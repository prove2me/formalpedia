-- Prove2me | solution 1 for MosonyiPetz.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-15T19:45:56.759172+00:00
-- url     : https://prove2.me/submissions/215042e4-9004-4f52-86fe-c62e45cf305e

import Mathlib
import Definitions.Def_MosonyiPetz_multiplicityProjection
import Definitions.Def_MosonyiPetz_blockDim
import Definitions.Def_MosonyiPetz_IsMinimalCentralProjection
import Definitions.Def_MosonyiPetz_multiplicity
import Definitions.Def_MosonyiPetz_dimensionProjection

section

/-!
# Unitaries normalizing a finite-dimensional *-subalgebra

Conjugation `x ↦ v* x v` by a unitary `v` with `v* A v ⊆ A` maps `A` onto `A`, so it is a
*-automorphism of `A`. It therefore permutes the minimal projections and the minimal central
projections of `A`, preserving rank, multiplicity and block dimension.
-/

open Matrix
open scoped Matrix

namespace MosonyiPetzNormalizer

open MosonyiPetz

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Conjugation `x ↦ star v * x * v`. -/
def conj (v : Matrix H H ℂ) : Matrix H H ℂ →+ Matrix H H ℂ :=
  (AddMonoidHom.mulRight v).comp (AddMonoidHom.mulLeft (star v))

theorem conj_apply (v x : Matrix H H ℂ) : conj v x = star v * x * v := rfl

variable {v : Matrix H H ℂ} (hv : v ∈ Matrix.unitaryGroup H ℂ)
include hv

theorem star_mul_self : star v * v = 1 := Matrix.mem_unitaryGroup_iff'.mp hv
theorem mul_star_self : v * star v = 1 := Matrix.mem_unitaryGroup_iff.mp hv

theorem conj_mul (x y : Matrix H H ℂ) : conj v (x * y) = conj v x * conj v y := by
  simp only [conj_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc v (star v), mul_star_self hv, Matrix.one_mul]

theorem conj_conjTranspose (x : Matrix H H ℂ) : conj v xᴴ = (conj v x)ᴴ := by
  simp only [conj_apply, ← Matrix.star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]

theorem conj_star_conj (x : Matrix H H ℂ) : conj (star v) (conj v x) = x := by
  simp only [conj_apply, star_star, ← Matrix.mul_assoc, mul_star_self hv, Matrix.one_mul]
  rw [Matrix.mul_assoc, mul_star_self hv, Matrix.mul_one]

theorem conj_conj_star (x : Matrix H H ℂ) : conj v (conj (star v) x) = x := by
  simp only [conj_apply, star_star, ← Matrix.mul_assoc, star_mul_self hv, Matrix.one_mul]
  rw [Matrix.mul_assoc, star_mul_self hv, Matrix.mul_one]

theorem conj_injective : Function.Injective (conj v) := fun x y h => by
  rw [← conj_star_conj hv x, h, conj_star_conj hv y]

theorem rank_conj (x : Matrix H H ℂ) : (conj v x).rank = x.rank := by
  have hu : IsUnit v := ⟨⟨v, star v, mul_star_self hv, star_mul_self hv⟩, rfl⟩
  have hs : IsUnit (star v) := ⟨⟨star v, v, star_mul_self hv, mul_star_self hv⟩, rfl⟩
  rw [conj_apply, Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det v).mp hu),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hs)]

theorem star_mem_unitaryGroup : star v ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_star]; exact star_mul_self hv

omit hv in
/-- In finite dimension, `v* A v ⊆ A` forces `v A v* ⊆ A`. -/
theorem conj_star_mem (A : StarSubalgebra ℂ (Matrix H H ℂ)) (hv : v ∈ Matrix.unitaryGroup H ℂ)
    (hinv : ∀ a ∈ A, star v * a * v ∈ A) : ∀ a ∈ A, conj (star v) a ∈ A := by
  set V := A.toSubalgebra.toSubmodule
  let f : V →ₗ[ℂ] V :=
    { toFun := fun a => ⟨star v * a * v, hinv a a.2⟩
      map_add' := fun a b => Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
      map_smul' := fun c a => Subtype.ext (by simp) }
  have hinj : Function.Injective f := fun a b h => Subtype.ext
    (conj_injective hv (congrArg Subtype.val h))
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro a ha
  obtain ⟨b, hb⟩ := hsurj ⟨a, ha⟩
  have hb' : conj v b = a := congrArg Subtype.val hb
  rw [← hb', conj_star_conj hv]
  exact b.2

end MosonyiPetzNormalizer

namespace MosonyiPetzNormalizer

open MosonyiPetz

variable {H : Type*} [Fintype H] [DecidableEq H] (A : StarSubalgebra ℂ (Matrix H H ℂ))
  {v : Matrix H H ℂ} (hv : v ∈ Matrix.unitaryGroup H ℂ)
  (hA : ∀ a ∈ A, conj v a ∈ A) (hA' : ∀ a ∈ A, conj (star v) a ∈ A)
include hv hA hA'

theorem isCentralProjection_conj {z : Matrix H H ℂ} (hz : IsCentralProjection A z) :
    IsCentralProjection A (conj v z) := by
  obtain ⟨hzA, hzc, hzz, hzh⟩ := hz
  refine ⟨hA z hzA, fun a ha => ?_, by rw [← conj_mul hv, hzz], by
    rw [← conj_conjTranspose hv, hzh]⟩
  have ha' := hA' a ha
  have := hzc (conj (star v) a) ha'
  rw [← conj_conj_star hv a, ← conj_mul hv, ← conj_mul hv, this]

theorem isMinimalCentralProjection_conj {z : Matrix H H ℂ}
    (hz : IsMinimalCentralProjection A z) : IsMinimalCentralProjection A (conj v z) := by
  obtain ⟨hzc, hz0, hmin⟩ := hz
  refine ⟨isCentralProjection_conj A hv hA hA' hzc, fun h => hz0 ?_, fun w hw hwz => ?_⟩
  · have := congrArg (conj (star v)) h
    rwa [conj_star_conj hv, map_zero] at this
  · have hw' := isCentralProjection_conj A (star_mem_unitaryGroup hv)
      (by simpa using hA') (by simpa [star_star] using hA) hw
    have hwz' : conj (star v) w * z = conj (star v) w := by
      have := congrArg (conj (star v)) hwz
      rwa [conj_mul (star_mem_unitaryGroup hv), conj_star_conj hv] at this
    rcases hmin _ hw' hwz' with h | h
    · left
      have := congrArg (conj v) h
      rwa [conj_conj_star hv, map_zero] at this
    · right
      rw [← h, conj_conj_star hv]

theorem isMinimalProjection_conj {q : Matrix H H ℂ} (hq : IsMinimalProjection A q) :
    IsMinimalProjection A (conj v q) := by
  obtain ⟨hqA, hqq, hqh, hq0, hmin⟩ := hq
  refine ⟨hA q hqA, by rw [← conj_mul hv, hqq], by rw [← conj_conjTranspose hv, hqh],
    fun h => hq0 ?_, fun w hwA hww hwh hwq => ?_⟩
  · have := congrArg (conj (star v)) h
    rwa [conj_star_conj hv, map_zero] at this
  · set w' := conj (star v) w
    have hsv := star_mem_unitaryGroup hv
    have h1 : w' * q = w' := by
      have := congrArg (conj (star v)) hwq
      rwa [conj_mul hsv, conj_star_conj hv] at this
    rcases hmin w' (hA' w hwA) (by rw [← conj_mul hsv, hww])
        (by rw [← conj_conjTranspose hsv, hwh]) h1 with h | h
    · left
      have := congrArg (conj v) h
      rwa [conj_conj_star hv, map_zero] at this
    · right
      rw [← h, conj_conj_star hv]

theorem multiplicity_conj_le (z : Matrix H H ℂ) :
    {n | ∃ q, IsMinimalProjection A q ∧ z * q = q ∧ q.rank = n} ⊆
      {n | ∃ q, IsMinimalProjection A q ∧ conj v z * q = q ∧ q.rank = n} := by
  rintro n ⟨q, hq, hzq, hr⟩
  exact ⟨conj v q, isMinimalProjection_conj A hv hA hA' hq,
    by rw [← conj_mul hv, hzq], by rw [rank_conj hv, hr]⟩

end MosonyiPetzNormalizer

namespace MosonyiPetzNormalizer

open MosonyiPetz

variable {H : Type*} [Fintype H] [DecidableEq H] (A : StarSubalgebra ℂ (Matrix H H ℂ))
  {u : Matrix H H ℂ} (hu : u ∈ Matrix.unitaryGroup H ℂ)
  (hinv : ∀ a ∈ A, star u * a * u ∈ A)
include hu hinv

theorem multiplicity_conj (z : Matrix H H ℂ) : MosonyiPetz.multiplicity A (conj u z) = MosonyiPetz.multiplicity A z := by
  have hA : ∀ a ∈ A, conj u a ∈ A := hinv
  have hA' := conj_star_mem A hu hinv
  have hsu := star_mem_unitaryGroup hu
  have hA'' : ∀ a ∈ A, conj (star (star u)) a ∈ A := by simpa using hA
  unfold MosonyiPetz.multiplicity
  congr 1
  apply Set.Subset.antisymm
  · have := multiplicity_conj_le A hsu hA' hA'' (conj u z)
    rwa [conj_star_conj hu] at this
  · exact multiplicity_conj_le A hu hA hA' z

theorem blockDim_conj (z : Matrix H H ℂ) : blockDim A (conj u z) = blockDim A z := by
  unfold blockDim
  rw [rank_conj hu, multiplicity_conj A hu hinv]

/-- Conjugation by `u` permutes any class of minimal central projections cut out by an invariant
of the conjugation, and so fixes the class's sum. -/
theorem conj_finsum_eq {S : Set (Matrix H H ℂ)}
    (hS : ∀ z, z ∈ S ↔ conj u z ∈ S) (hS0 : (0 : Matrix H H ℂ) ∉ S) :
    conj u (∑ᶠ z ∈ S, z) = ∑ᶠ z ∈ S, z := by
  have hbij : Set.BijOn (conj u) S S := by
    refine ⟨fun z hz => (hS z).mp hz, (conj_injective hu).injOn, fun w hw => ?_⟩
    refine ⟨conj (star u) w, (hS _).mpr (by rwa [conj_conj_star hu]), conj_conj_star hu w⟩
  have hsupp : S ∩ Function.support (fun z : Matrix H H ℂ => z) = S := by
    ext z; simp only [Set.mem_inter_iff, Function.mem_support, and_iff_left_iff_imp]
    exact fun hz h => hS0 (h ▸ hz)
  by_cases hfin : (S ∩ Function.support (fun z : Matrix H H ℂ => z)).Finite
  · rw [AddMonoidHom.map_finsum_mem' (conj u) hfin]
    exact finsum_mem_eq_of_bijOn (conj u) hbij fun _ _ => rfl
  · rw [finsum_mem_eq_zero_of_infinite (Set.not_finite.mp hfin), map_zero]

theorem commute_of_conj_eq {P : Matrix H H ℂ} (h : conj u P = P) : u * P = P * u := by
  have := congrArg (fun X => u * X) h
  simp only [conj_apply, ← Matrix.mul_assoc, mul_star_self hu, Matrix.one_mul] at this
  exact this.symm

theorem isMinimalCentralProjection_conj_iff (z : Matrix H H ℂ) :
    IsMinimalCentralProjection A z ↔ IsMinimalCentralProjection A (conj u z) := by
  have hA : ∀ a ∈ A, conj u a ∈ A := hinv
  have hA' := conj_star_mem A hu hinv
  have hsu := star_mem_unitaryGroup hu
  refine ⟨isMinimalCentralProjection_conj A hu hA hA', fun h => ?_⟩
  have := isMinimalCentralProjection_conj A hsu hA' (by simpa using hA) h
  rwa [conj_star_conj hu] at this

end MosonyiPetzNormalizer
end

section

/-!
# The minimal central projections of a finite-dimensional *-subalgebra

The minimal central projections of a unital *-subalgebra `A ⊆ B(H)` are pairwise orthogonal,
finite in number, and sum to `1`. Ranks of Hermitian idempotents are traces, so they add over
orthogonal decompositions; this gives minimal central projections below any nonzero central
projection.
-/

open Matrix
open scoped Matrix ComplexOrder

namespace MosonyiPetzNormalizer

open MosonyiPetz

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem trace_eq_rank_of_proj {P : Matrix H H ℂ} (hP : P.IsHermitian) (hPP : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  have hev : ∀ i, hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
    intro i
    set v : H → ℂ := ⇑(hP.eigenvectorBasis i)
    have h1 : P *ᵥ v = (hP.eigenvalues i) • v := hP.mulVec_eigenvectorBasis i
    have h2 : P *ᵥ (P *ᵥ v) = P *ᵥ v := by rw [Matrix.mulVec_mulVec, hPP]
    rw [h1, Matrix.mulVec_smul, h1, smul_smul] at h2
    have hv : v ≠ 0 := by
      intro h
      have := (hP.eigenvectorBasis).orthonormal.ne_zero i
      apply this
      ext j
      exact congrFun h j
    have h3 : (hP.eigenvalues i * hP.eigenvalues i - hP.eigenvalues i) • v = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · have : hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by linarith)
    · exact absurd h hv
  rw [hP.trace_eq_sum_eigenvalues, hP.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  push_cast
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hev i with h | h <;> simp [h]

theorem rank_eq_zero_of_proj {P : Matrix H H ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (h : P.rank = 0) : P = 0 := by
  have htr : (Pᴴ * P).trace = 0 := by
    rw [hP.eq, hPP, trace_eq_rank_of_proj hP hPP, h, Nat.cast_zero]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr

variable (A : StarSubalgebra ℂ (Matrix H H ℂ))

theorem isCentralProjection_mul {z w : Matrix H H ℂ} (hz : IsCentralProjection A z)
    (hw : IsCentralProjection A w) : IsCentralProjection A (z * w) := by
  obtain ⟨hzA, hzc, hzz, hzh⟩ := hz
  obtain ⟨hwA, hwc, hww, hwh⟩ := hw
  have hcomm : w * z = z * w := hzc w hwA
  refine ⟨A.mul_mem hzA hwA, fun a ha => ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, hzc a ha, Matrix.mul_assoc, hwc a ha, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc w z w, hcomm, Matrix.mul_assoc, hww,
      ← Matrix.mul_assoc, hzz]
  · rw [Matrix.conjTranspose_mul, hzh, hwh, hcomm]

theorem isCentralProjection_one_sub {z : Matrix H H ℂ} (hz : IsCentralProjection A z) :
    IsCentralProjection A (1 - z) := by
  obtain ⟨hzA, hzc, hzz, hzh⟩ := hz
  refine ⟨A.sub_mem A.one_mem hzA, fun a ha => ?_, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hzc a ha]
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hzz, sub_self, sub_zero]
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hzh]

theorem isCentralProjection_sub {z w : Matrix H H ℂ} (hz : IsCentralProjection A z)
    (hw : IsCentralProjection A w) (hwz : w * z = w) : IsCentralProjection A (z - w) := by
  have hzw : z * w = w := by rw [← hz.2.1 w hw.1, hwz]
  have := isCentralProjection_mul A hz (isCentralProjection_one_sub A hw)
  rwa [Matrix.mul_sub, Matrix.mul_one, hzw] at this

theorem minimal_orthogonal {z w : Matrix H H ℂ} (hz : IsMinimalCentralProjection A z)
    (hw : IsMinimalCentralProjection A w) (hne : z ≠ w) : z * w = 0 := by
  have hzw := isCentralProjection_mul A hz.1 hw.1
  have hcomm : w * z = z * w := hz.1.2.1 w hw.1.1
  have h1 : z * w * z = z * w := by
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hz.1.2.2.1]
  have h2 : z * w * w = z * w := by rw [Matrix.mul_assoc, hw.1.2.2.1]
  rcases hz.2.2 _ hzw h1 with h | h
  · exact h
  rcases hw.2.2 _ hzw h2 with h' | h'
  · exact h'
  exact absurd (h.symm.trans h') hne

theorem minimal_finite : {z | IsMinimalCentralProjection A z}.Finite := by
  apply LinearIndependent.setFinite (R := ℂ)
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hmul := congrArg (fun X => X * (i : Matrix H H ℂ)) hg
  simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.zero_mul] at hmul
  rw [Finset.sum_eq_single i] at hmul
  · rw [i.2.1.2.2.1] at hmul
    exact (smul_eq_zero.mp hmul).resolve_right i.2.2.1
  · intro j _ hji
    rw [minimal_orthogonal A j.2 i.2 (fun h => hji (Subtype.ext h)), smul_zero]
  · intro h; exact absurd hi h

theorem exists_minimal_le {e : Matrix H H ℂ} (he : IsCentralProjection A e) (he0 : e ≠ 0) :
    ∃ z, IsMinimalCentralProjection A z ∧ z * e = z := by
  classical
  have hex : ∃ n, ∃ w, IsCentralProjection A w ∧ w ≠ 0 ∧ w * e = w ∧ w.rank = n :=
    ⟨_, e, he, he0, he.2.2.1, rfl⟩
  obtain ⟨w, hw, hw0, hwe, hrank⟩ := Nat.find_spec hex
  refine ⟨w, ⟨hw, hw0, fun w' hw' hw'w => ?_⟩, hwe⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hw'0, hw'ne⟩ := hcon
  have hd := isCentralProjection_sub A hw hw' hw'w
  have hd0 : w - w' ≠ 0 := sub_ne_zero.mpr (Ne.symm hw'ne)
  have hw'e : w' * e = w' := by rw [← hw'w, Matrix.mul_assoc, hwe]
  have hmin := Nat.find_min' hex ⟨w', hw', hw'0, hw'e, rfl⟩
  have htr : w.trace = w'.trace + (w - w').trace := by rw [Matrix.trace_sub]; ring
  rw [trace_eq_rank_of_proj hw.2.2.2 hw.2.2.1, trace_eq_rank_of_proj hw'.2.2.2 hw'.2.2.1,
    trace_eq_rank_of_proj hd.2.2.2 hd.2.2.1] at htr
  have htr' : w.rank = w'.rank + (w - w').rank := by exact_mod_cast htr
  have hpos : 0 < (w - w').rank := Nat.pos_of_ne_zero fun h =>
    hd0 (rank_eq_zero_of_proj hd.2.2.2 hd.2.2.1 h)
  omega

/-- The minimal central projections sum to `1`. -/
theorem sum_minimal_eq_one :
    ∑ z ∈ (minimal_finite A).toFinset, z = 1 := by
  classical
  set Z := (minimal_finite A).toFinset
  set s := ∑ z ∈ Z, z
  have hmemZ : ∀ z, z ∈ Z ↔ IsMinimalCentralProjection A z := fun z => by
    simp [Z]
  have hzs : ∀ z ∈ Z, z * s = z := by
    intro z hz
    rw [Finset.mul_sum, Finset.sum_eq_single z]
    · exact ((hmemZ z).mp hz).1.2.2.1
    · intro w hw hwz
      exact minimal_orthogonal A ((hmemZ z).mp hz) ((hmemZ w).mp hw) (Ne.symm hwz)
    · intro h; exact absurd hz h
  have hscp : IsCentralProjection A s := by
    refine ⟨A.sum_mem fun z hz => ((hmemZ z).mp hz).1.1, fun a ha => ?_, ?_, ?_⟩
    · rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun z hz => ((hmemZ z).mp hz).1.2.1 a ha
    · rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun z hz => hzs z hz
    · rw [Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun z hz => ((hmemZ z).mp hz).1.2.2.2
  by_contra hne
  have he := isCentralProjection_one_sub A hscp
  have he0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨z, hz, hze⟩ := exists_minimal_le A he he0
  rw [Matrix.mul_sub, Matrix.mul_one, hzs z ((hmemZ z).mpr hz), sub_self] at hze
  exact hz.2.1 hze.symm

end MosonyiPetzNormalizer
end


open scoped Matrix

open MosonyiPetzNormalizer MosonyiPetz in
theorem solution {H : Type*} [Fintype H] [DecidableEq H]
    (A : StarSubalgebra ℂ (Matrix H H ℂ)) (m : ℕ)
    (hm : ∀ z, IsMinimalCentralProjection A z → MosonyiPetz.multiplicity A z = m)
    (u : Matrix H H ℂ) (hu : u ∈ Matrix.unitaryGroup H ℂ)
    (hinv : ∀ a ∈ A, star u * a * u ∈ A) :
    (∀ d : ℕ, u * dimensionProjection A d = dimensionProjection A d * u) ∧
    u = ∑ᶠ d : ℕ, dimensionProjection A d * u * dimensionProjection A d := by
  classical
  have hcomm : ∀ d : ℕ, u * dimensionProjection A d = dimensionProjection A d * u := by
    intro d
    apply commute_of_conj_eq A hu hinv
    unfold dimensionProjection
    refine conj_finsum_eq A hu hinv (fun z => ?_) (fun h => h.1.2.1 rfl)
    simp only [Set.mem_setOf_eq]
    rw [isMinimalCentralProjection_conj_iff A hu hinv z, blockDim_conj A hu hinv]
  refine ⟨hcomm, ?_⟩
  set Z := (minimal_finite A).toFinset
  have hmemZ : ∀ z, z ∈ Z ↔ IsMinimalCentralProjection A z := fun z => by simp [Z]
  -- each dimension projection is a finite sum over the minimal central projections
  have hP : ∀ d, dimensionProjection A d = ∑ z ∈ Z with blockDim A z = d, z := by
    intro d
    have hfin : {z | IsMinimalCentralProjection A z ∧ blockDim A z = d}.Finite :=
      (minimal_finite A).subset fun z hz => hz.1
    unfold dimensionProjection
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    congr 1
    ext z; simp [Z]
  have hidem : ∀ d, dimensionProjection A d * dimensionProjection A d =
      dimensionProjection A d := by
    intro d
    rw [hP d, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzZ := (hmemZ z).mp (Finset.mem_filter.mp hz).1
    rw [Finset.mul_sum, Finset.sum_eq_single z]
    · exact hzZ.1.2.2.1
    · intro w hw hwz
      exact minimal_orthogonal A hzZ ((hmemZ w).mp (Finset.mem_filter.mp hw).1) (Ne.symm hwz)
    · intro h; exact absurd hz h
  set D := Z.image (blockDim A)
  have hsupp : Function.support (fun d => dimensionProjection A d * u * dimensionProjection A d)
      ⊆ D := by
    intro d hd
    by_contra hdD
    apply hd
    have : dimensionProjection A d = 0 := by
      rw [hP d]
      refine Finset.sum_eq_zero fun z hz => absurd ?_ hdD
      obtain ⟨hzZ, hzd⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_image.mpr ⟨z, hzZ, hzd⟩
    simp [this]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hterm : ∀ d, dimensionProjection A d * u * dimensionProjection A d =
      u * dimensionProjection A d := by
    intro d
    rw [← hcomm d, Matrix.mul_assoc, hidem d]
  rw [Finset.sum_congr rfl fun d _ => hterm d, ← Finset.mul_sum]
  simp only [hP]
  rw [Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz),
    sum_minimal_eq_one A, Matrix.mul_one]