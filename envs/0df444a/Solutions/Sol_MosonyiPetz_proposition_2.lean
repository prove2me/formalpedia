-- Prove2me | solution 1 for MosonyiPetz.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-15T19:40:12.00521+00:00
-- url     : https://prove2.me/submissions/c4bd2d88-172d-467a-a8ff-e01410447758

import Mathlib
import Definitions.Def_MosonyiPetz_multiplicityProjection
import Definitions.Def_MosonyiPetz_blockDim

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


open scoped Matrix

open MosonyiPetzNormalizer MosonyiPetz in
theorem solution {H : Type*} [Fintype H] [DecidableEq H]
    (A : StarSubalgebra ℂ (Matrix H H ℂ)) (u : Matrix H H ℂ) (hu : u ∈ Matrix.unitaryGroup H ℂ)
    (hinv : ∀ a ∈ A, star u * a * u ∈ A) (m : ℕ) :
    u * multiplicityProjection A m = multiplicityProjection A m * u := by
  apply commute_of_conj_eq A hu hinv
  unfold multiplicityProjection
  refine conj_finsum_eq A hu hinv (fun z => ?_) (fun h => h.1.2.1 rfl)
  simp only [Set.mem_setOf_eq]
  rw [isMinimalCentralProjection_conj_iff A hu hinv z, MosonyiPetzNormalizer.multiplicity_conj A hu hinv]