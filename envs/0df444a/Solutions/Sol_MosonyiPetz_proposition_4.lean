-- Prove2me | solution 1 for MosonyiPetz.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-15T20:18:09.484204+00:00
-- url     : https://prove2.me/submissions/3e0466ba-a27f-46d7-a88d-94a60e89565f

import Mathlib
import Definitions.Def_MosonyiPetz_multiplicityProjection
import Definitions.Def_MosonyiPetz_blockDim
import Definitions.Def_MosonyiPetz_blockAlgebra

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
# Unitaries implementing an automorphism of `M_d ⊗ 1`

If a unitary `V` on `ℂ^ι ⊗ ℂ^μ` satisfies `V (A ⊗ 1) V* = θ(A) ⊗ 1` for every `A`, then
`V = v ⊗ w` for unitaries `v`, `w`. The proof makes `θ` an injective `*`-homomorphism, builds
`v` with `θ(A) = v A v*` from the matrix units (Skolem–Noether for `M_d`), and identifies
`(v ⊗ 1)* V` as an element of the commutant `1 ⊗ M_m` of `M_d ⊗ 1`.
-/

open Matrix
open scoped Matrix Kronecker ComplexOrder

namespace MosonyiPetzBlock

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

theorem kron_one_injective (m0 : μ) :
    Function.Injective (fun X : Matrix ι ι ℂ => X ⊗ₖ (1 : Matrix μ μ ℂ)) := by
  intro X Y h
  ext a a'
  have := congrFun (congrFun h (a, m0)) (a', m0)
  simpa [Matrix.kroneckerMap_apply] using this

theorem one_kron_injective (i0 : ι) :
    Function.Injective (fun X : Matrix μ μ ℂ => (1 : Matrix ι ι ℂ) ⊗ₖ X) := by
  intro X Y h
  ext b b'
  have := congrFun (congrFun h (i0, b)) (i0, b')
  simpa [Matrix.kroneckerMap_apply] using this

theorem kron_one_mul (X Y : Matrix ι ι ℂ) :
    (X ⊗ₖ (1 : Matrix μ μ ℂ)) * (Y ⊗ₖ (1 : Matrix μ μ ℂ)) = (X * Y) ⊗ₖ (1 : Matrix μ μ ℂ) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem single_mul_single' (i j k l : ι) :
    Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0 := by
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, mul_one]
  · simp [h]

theorem mul_single_kron_apply (W : Matrix (ι × μ) (ι × μ) ℂ) (i j x y : ι) (b b' : μ) :
    (W * (Matrix.single i j (1:ℂ) ⊗ₖ (1 : Matrix μ μ ℂ))) (x, b) (y, b') =
      if j = y then W (x, b) (i, b') else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply, ite_and,
    mul_ite, mul_one, mul_zero]
  simp

theorem single_kron_mul_apply (W : Matrix (ι × μ) (ι × μ) ℂ) (i j x y : ι) (b b' : μ) :
    ((Matrix.single i j (1:ℂ) ⊗ₖ (1 : Matrix μ μ ℂ)) * W) (x, b) (y, b') =
      if x = i then W (j, b) (y, b') else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply, ite_and,
    mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
  simp [eq_comm]

/-- The commutant of `M_d ⊗ 1` is `1 ⊗ M_m`. -/
theorem eq_one_kron_of_commute (i0 : ι) {W : Matrix (ι × μ) (ι × μ) ℂ}
    (hW : ∀ A : Matrix ι ι ℂ, W * (A ⊗ₖ (1 : Matrix μ μ ℂ)) = (A ⊗ₖ (1 : Matrix μ μ ℂ)) * W) :
    W = (1 : Matrix ι ι ℂ) ⊗ₖ (Matrix.of fun b b' => W (i0, b) (i0, b')) := by
  have key : ∀ (i j x y : ι) (b b' : μ),
      (if j = y then W (x, b) (i, b') else 0) = (if x = i then W (j, b) (y, b') else 0) := by
    intro i j x y b b'
    have := congrFun (congrFun (hW (Matrix.single i j 1)) (x, b)) (y, b')
    rwa [mul_single_kron_apply, single_kron_mul_apply] at this
  ext ⟨x, b⟩ ⟨y, b'⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    have := key x i0 x i0 b b'
    simp only [if_true] at this
    rw [if_pos rfl, one_mul, this]
  · have := key y y x y b b'
    simp only [if_true, if_neg hxy] at this
    rw [if_neg hxy, zero_mul, this]

section Skolem

variable (m0 : μ) {V : Matrix (ι × μ) (ι × μ) ℂ}
  (hV : V ∈ Matrix.unitaryGroup (ι × μ) ℂ) {θ : Matrix ι ι ℂ → Matrix ι ι ℂ}
  (hθ : ∀ A, V * (A ⊗ₖ (1 : Matrix μ μ ℂ)) * star V = θ A ⊗ₖ (1 : Matrix μ μ ℂ))
include m0 hV hθ

theorem theta_mul (A B : Matrix ι ι ℂ) : θ (A * B) = θ A * θ B := by
  apply kron_one_injective m0
  have hu := Matrix.mem_unitaryGroup_iff'.mp hV
  change θ (A * B) ⊗ₖ (1 : Matrix μ μ ℂ) = (θ A * θ B) ⊗ₖ (1 : Matrix μ μ ℂ)
  rw [← kron_one_mul, ← hθ, ← hθ, ← hθ, ← kron_one_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star V) V, hu, Matrix.one_mul]

theorem theta_conjTranspose (A : Matrix ι ι ℂ) : θ Aᴴ = (θ A)ᴴ := by
  apply kron_one_injective m0
  change θ Aᴴ ⊗ₖ (1 : Matrix μ μ ℂ) = (θ A)ᴴ ⊗ₖ (1 : Matrix μ μ ℂ)
  have h1 : (θ A)ᴴ ⊗ₖ (1 : Matrix μ μ ℂ) = (θ A ⊗ₖ (1 : Matrix μ μ ℂ))ᴴ := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have h2 : Aᴴ ⊗ₖ (1 : Matrix μ μ ℂ) = (A ⊗ₖ (1 : Matrix μ μ ℂ))ᴴ := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [h1, ← hθ, ← hθ, h2]
  simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem theta_add (A B : Matrix ι ι ℂ) : θ (A + B) = θ A + θ B := by
  apply kron_one_injective m0
  change θ (A + B) ⊗ₖ (1 : Matrix μ μ ℂ) = (θ A + θ B) ⊗ₖ (1 : Matrix μ μ ℂ)
  rw [Matrix.add_kronecker, ← hθ, ← hθ, ← hθ, Matrix.add_kronecker, Matrix.mul_add,
    Matrix.add_mul]

theorem theta_smul (c : ℂ) (A : Matrix ι ι ℂ) : θ (c • A) = c • θ A := by
  apply kron_one_injective m0
  change θ (c • A) ⊗ₖ (1 : Matrix μ μ ℂ) = (c • θ A) ⊗ₖ (1 : Matrix μ μ ℂ)
  rw [Matrix.smul_kronecker, ← hθ, ← hθ, Matrix.smul_kronecker, Matrix.mul_smul,
    Matrix.smul_mul]

theorem theta_zero : θ 0 = 0 := by
  have := theta_smul m0 hV hθ 0 0
  simpa using this

theorem theta_injective {A : Matrix ι ι ℂ} (h : θ A = 0) : A = 0 := by
  have hu := Matrix.mem_unitaryGroup_iff'.mp hV
  have e : A ⊗ₖ (1 : Matrix μ μ ℂ) = star V * (θ A ⊗ₖ (1 : Matrix μ μ ℂ)) * V := by
    rw [← hθ]
    simp only [← Matrix.mul_assoc, hu, Matrix.one_mul]
    rw [Matrix.mul_assoc, hu, Matrix.mul_one]
  rw [h, Matrix.zero_kronecker, Matrix.mul_zero, Matrix.zero_mul] at e
  apply kron_one_injective m0
  change A ⊗ₖ (1 : Matrix μ μ ℂ) = 0 ⊗ₖ (1 : Matrix μ μ ℂ)
  rw [e, Matrix.zero_kronecker]

theorem theta_sum (s : Finset ι) (f : ι → Matrix ι ι ℂ) :
    θ (∑ i ∈ s, f i) = ∑ i ∈ s, θ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact theta_zero m0 hV hθ
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, theta_add m0 hV hθ, ih]

theorem theta_eq_sum (A : Matrix ι ι ℂ) :
    θ A = ∑ i, ∑ j, A i j • θ (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [theta_sum m0 hV hθ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [theta_sum m0 hV hθ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← theta_smul m0 hV hθ, Matrix.smul_single, smul_eq_mul, mul_one]

/-- Skolem–Noether for `M_d`: `θ` is conjugation by a unitary. -/
theorem exists_unitary_theta (i0 : ι) :
    ∃ v ∈ Matrix.unitaryGroup ι ℂ, ∀ A, θ A = v * A * star v := by
  set E : ι → ι → Matrix ι ι ℂ := fun i j => Matrix.single i j (1 : ℂ) with hEdef
  set p := θ (E i0 i0)
  have hθE : ∀ i j k l, θ (E i j) * θ (E k l) = if j = k then θ (E i l) else 0 := by
    intro i j k l
    rw [← theta_mul m0 hV hθ, hEdef, single_mul_single']
    split_ifs
    · rfl
    · exact theta_zero m0 hV hθ
  have hθEh : ∀ i j, (θ (E i j))ᴴ = θ (E j i) := by
    intro i j
    rw [← theta_conjTranspose m0 hV hθ, hEdef, Matrix.conjTranspose_single, star_one]
  have hp0 : p ≠ 0 := fun h => by
    have := theta_injective m0 hV hθ h
    have h1 := congrFun (congrFun this i0) i0
    simp [E] at h1
  have hpp : pᴴ * p = p := by rw [hθEh, hθE, if_pos rfl]
  obtain ⟨b, hb⟩ : ∃ b, p b b ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hp0
    have htr : (pᴴ * p).trace = 0 := by
      rw [hpp, Matrix.trace]; exact Finset.sum_eq_zero fun i _ => hcon i
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr
  set r : ℝ := ∑ a, Complex.normSq (p a b)
  have hpbb : p b b = (r : ℂ) := by
    conv_lhs => rw [← hpp]
    rw [Matrix.mul_apply]
    simp only [r, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_apply, mul_comm, Complex.star_def, Complex.mul_conj]
  have hr : 0 < r := by
    by_contra hle
    have : r = 0 := le_antisymm (not_lt.mp hle)
      (Finset.sum_nonneg fun a _ => Complex.normSq_nonneg (p a b))
    apply hb; rw [hpbb, this, Complex.ofReal_zero]
  set c : ℂ := (((Real.sqrt r)⁻¹ : ℝ) : ℂ)
  have hcc : star c * c * p b b = 1 := by
    rw [hpbb]
    simp only [c, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
      show (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ * r = 1 by
        rw [← mul_inv, Real.mul_self_sqrt hr.le, inv_mul_cancel₀ hr.ne'],
      Complex.ofReal_one]
  set v : Matrix ι ι ℂ := ∑ k, c • (θ (E k i0) * E b k)
  have hEpE : ∀ k, E k b * p * E b k = p b b • E k k := by
    intro k
    rw [hEdef]
    simp only
    rw [Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, smul_eq_mul, mul_one]
  have hvv : star v * v = 1 := by
    have hEh : ∀ k, (E b k)ᴴ = E k b := fun k => by
      rw [hEdef]; simp only; rw [Matrix.conjTranspose_single, star_one]
    have hsv : star v = ∑ k, star c • (E k b * θ (E i0 k)) := by
      simp only [v, star_sum, star_smul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        hθEh, hEh]
    rw [hsv, Finset.sum_mul]
    have hterm : ∀ k, star c • (E k b * θ (E i0 k)) * v = E k k := by
      intro k
      rw [Finset.mul_sum, Finset.sum_eq_single k]
      · rw [smul_mul_assoc, mul_smul_comm, smul_smul,
          show E k b * θ (E i0 k) * (θ (E k i0) * E b k) =
            E k b * (θ (E i0 k) * θ (E k i0)) * E b k by simp only [Matrix.mul_assoc],
          hθE, if_pos rfl, hEpE, smul_smul, hcc, one_smul]
      · intro l _ hlk
        rw [smul_mul_assoc, mul_smul_comm,
          show E k b * θ (E i0 k) * (θ (E l i0) * E b l) =
            E k b * (θ (E i0 k) * θ (E l i0)) * E b l by simp only [Matrix.mul_assoc],
          hθE, if_neg (Ne.symm hlk), Matrix.mul_zero, Matrix.zero_mul, smul_zero, smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    simp only [hEdef]
    ext x y
    rw [Matrix.sum_apply, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp [Matrix.single_apply]
    · simp only [Matrix.single_apply, if_neg h]
      exact Finset.sum_eq_zero fun k _ => if_neg fun hk => h (hk.1.symm.trans hk.2)
  have hv : v ∈ Matrix.unitaryGroup ι ℂ := Matrix.mem_unitaryGroup_iff'.mpr hvv
  have hvv' : v * star v = 1 := Matrix.mem_unitaryGroup_iff.mp hv
  have hint : ∀ i j, θ (E i j) * v = v * E i j := by
    intro i j
    simp only [v, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, hθE, if_pos rfl, Matrix.mul_assoc, hEdef]
      simp only
      rw [single_mul_single', if_pos rfl]
    · intro k _ hki
      rw [Matrix.mul_assoc, hEdef]; simp only
      rw [single_mul_single', if_neg hki, Matrix.mul_zero, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
    · intro k _ hkj
      rw [← Matrix.mul_assoc, hθE, if_neg (Ne.symm hkj), Matrix.zero_mul, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  refine ⟨v, hv, fun A => ?_⟩
  have hA : θ A * v = v * A := by
    rw [theta_eq_sum m0 hV hθ A, Finset.sum_mul]
    conv_rhs => rw [Matrix.matrix_eq_sum_single A, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, hint, ← mul_smul_comm, Matrix.smul_single, smul_eq_mul, mul_one]
  calc θ A = θ A * v * star v := by rw [Matrix.mul_assoc, hvv', Matrix.mul_one]
    _ = v * A * star v := by rw [hA]

/-- `V (A ⊗ 1) V* = θ(A) ⊗ 1` for all `A` forces `V = v ⊗ w` with `v`, `w` unitary. -/
theorem eq_kron_of_conj (i0 : ι) :
    ∃ v ∈ Matrix.unitaryGroup ι ℂ, ∃ w ∈ Matrix.unitaryGroup μ ℂ, V = v ⊗ₖ w := by
  obtain ⟨v, hv, hθv⟩ := exists_unitary_theta m0 hV hθ i0
  have hvv : star v * v = 1 := Matrix.mem_unitaryGroup_iff'.mp hv
  have hvv' : v * star v = 1 := Matrix.mem_unitaryGroup_iff.mp hv
  have hVV : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  set W := (star v ⊗ₖ (1 : Matrix μ μ ℂ)) * V
  have hstarW : star W = star V * (v ⊗ₖ (1 : Matrix μ μ ℂ)) := by
    simp only [W, star_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose]
  have hWW : star W * W = 1 := by
    rw [hstarW]
    simp only [W, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (v ⊗ₖ 1), kron_one_mul, hvv', Matrix.one_kronecker_one, Matrix.one_mul,
      hVV]
  have hWW' : W * star W = 1 := mul_eq_one_comm.mp hWW
  have hconj : ∀ A : Matrix ι ι ℂ, W * (A ⊗ₖ (1 : Matrix μ μ ℂ)) * star W = A ⊗ₖ 1 := by
    intro A
    rw [hstarW]
    have e : W * (A ⊗ₖ (1 : Matrix μ μ ℂ)) * (star V * (v ⊗ₖ (1 : Matrix μ μ ℂ))) =
        (star v ⊗ₖ (1 : Matrix μ μ ℂ)) * (V * (A ⊗ₖ (1 : Matrix μ μ ℂ)) * star V) *
          (v ⊗ₖ (1 : Matrix μ μ ℂ)) := by
      simp only [W, Matrix.mul_assoc]
    rw [e, hθ, hθv, kron_one_mul, kron_one_mul]
    congr 1
    simp only [← Matrix.mul_assoc, hvv, Matrix.one_mul]
    rw [Matrix.mul_assoc, hvv, Matrix.mul_one]
  have hcomm : ∀ A : Matrix ι ι ℂ, W * (A ⊗ₖ (1 : Matrix μ μ ℂ)) = (A ⊗ₖ 1) * W := by
    intro A
    calc W * (A ⊗ₖ (1 : Matrix μ μ ℂ)) = W * (A ⊗ₖ 1) * (star W * W) := by
          rw [hWW, Matrix.mul_one]
      _ = W * (A ⊗ₖ 1) * star W * W := by simp only [Matrix.mul_assoc]
      _ = (A ⊗ₖ 1) * W := by rw [hconj]
  set w : Matrix μ μ ℂ := Matrix.of fun b b' => W (i0, b) (i0, b')
  have hW : W = (1 : Matrix ι ι ℂ) ⊗ₖ w := eq_one_kron_of_commute i0 hcomm
  have hw : w ∈ Matrix.unitaryGroup μ ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    apply one_kron_injective i0
    change (1 : Matrix ι ι ℂ) ⊗ₖ (w * star w) = (1 : Matrix ι ι ℂ) ⊗ₖ 1
    have := hWW'
    rw [hW, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose] at this
    rw [this, Matrix.one_kronecker_one]
  refine ⟨v, hv, w, hw, ?_⟩
  calc V = (v ⊗ₖ (1 : Matrix μ μ ℂ)) * W := by
        simp only [W, ← Matrix.mul_assoc]
        rw [kron_one_mul, hvv', Matrix.one_kronecker_one, Matrix.one_mul]
    _ = v ⊗ₖ w := by rw [hW, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

end Skolem

end MosonyiPetzBlock
end

section

/-!
# The block algebra `⊕_K M_d ⊗ 1_m`

`MosonyiPetzBlock.embed A = ∑ᵢ (Aᵢ ⊗ 1) ⊗ eᵢᵢ` is an injective unital `*`-homomorphism, so its
range `blockAlgebra d m K` is a `*`-subalgebra. Its central projections are the sums of the block
projections `Q i = embed (δᵢ · 1)`, and its minimal central projections are exactly the `Q i`.
-/

open Matrix
open scoped Matrix Kronecker

namespace MosonyiPetzBlock

variable {d m K : ℕ}

/-- `∑ᵢ (Aᵢ ⊗ 1) ⊗ eᵢᵢ`, the defining parametrization of `blockAlgebra d m K`. -/
noncomputable def embed (A : Fin K → Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ :=
  ∑ i, (A i ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) ⊗ₖ Matrix.single i i (1 : ℂ)

theorem embed_apply (A : Fin K → Matrix (Fin d) (Fin d) ℂ) (a a' : Fin d) (b b' : Fin m)
    (i i' : Fin K) :
    (embed (m := m) A) ((a, b), i) ((a', b'), i') =
      if i = i' then A i a a' * (if b = b' then 1 else 0) else 0 := by
  simp only [embed, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single_apply,
    Matrix.one_apply]
  by_cases h : i = i'
  · subst h; simp
  · simp only [if_neg h]
    exact Finset.sum_eq_zero fun l _ => by
      by_cases hl : l = i <;> simp_all [eq_comm]

theorem embed_mul (A B : Fin K → Matrix (Fin d) (Fin d) ℂ) :
    embed (m := m) A * embed B = embed (A * B) := by
  simp only [embed, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      single_mul_single', if_pos rfl, Pi.mul_apply]
  · intro j _ hji
    rw [← Matrix.mul_kronecker_mul, single_mul_single', if_neg hji, Matrix.kronecker_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem embed_add (A B : Fin K → Matrix (Fin d) (Fin d) ℂ) :
    embed (m := m) (A + B) = embed A + embed B := by
  simp only [embed, ← Finset.sum_add_distrib, Pi.add_apply, Matrix.add_kronecker]

theorem embed_smul (c : ℂ) (A : Fin K → Matrix (Fin d) (Fin d) ℂ) :
    embed (m := m) (c • A) = c • embed A := by
  simp only [embed, Finset.smul_sum, Pi.smul_apply, Matrix.smul_kronecker]

theorem embed_conjTranspose (A : Fin K → Matrix (Fin d) (Fin d) ℂ) :
    (embed (m := m) A)ᴴ = embed (fun i => (A i)ᴴ) := by
  simp only [embed, Matrix.conjTranspose_sum, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.conjTranspose_single, star_one]

theorem embed_one : embed (m := m) (1 : Fin K → Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext ⟨⟨a, b⟩, i⟩ ⟨⟨a', b'⟩, i'⟩
  rw [embed_apply, Matrix.one_apply]
  simp only [Pi.one_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases hi : i = i' <;> by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [hi, ha, hb]

theorem embed_zero : embed (m := m) (0 : Fin K → Matrix (Fin d) (Fin d) ℂ) = 0 := by
  have := embed_smul (m := m) 0 (0 : Fin K → Matrix (Fin d) (Fin d) ℂ)
  simpa using this

theorem embed_injective (m0 : Fin m) :
    Function.Injective (embed (m := m) (K := K) (d := d)) := by
  intro A B h
  funext i
  ext a a'
  have := congrFun (congrFun h ((a, m0), i)) ((a', m0), i)
  simpa [embed_apply] using this

/-- `blockAlgebra d m K` as a `*`-subalgebra. -/
noncomputable def blockStarAlg (d m K : ℕ) :
    StarSubalgebra ℂ (Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ) where
  carrier := MosonyiPetz.blockAlgebra d m K
  mul_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨A * B, embed_mul A B⟩
  add_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨A + B, (embed_add A B).symm⟩
  algebraMap_mem' := fun c => ⟨c • 1, by
    show _ = embed (c • 1)
    rw [embed_smul, embed_one, Algebra.algebraMap_eq_smul_one]⟩
  star_mem' := by
    rintro _ ⟨A, rfl⟩
    exact ⟨fun i => (A i)ᴴ, by rw [Matrix.star_eq_conjTranspose]; exact embed_conjTranspose A⟩

theorem mem_blockStarAlg {x : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ} :
    x ∈ blockStarAlg d m K ↔ ∃ A, x = embed A := Iff.rfl

/-- The block projections. -/
noncomputable def Q (i : Fin K) :
    Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ :=
  embed (fun j => if j = i then 1 else 0)

theorem scalar_of_commute (i0 : Fin d) {C : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ X, X * C = C * X) : C = C i0 i0 • 1 := by
  have hL : ∀ k l x y : Fin d, (Matrix.single k l (1:ℂ) * C) x y = if x = k then C l y else 0 := by
    intro k l x y; rw [Matrix.mul_apply]; simp [Matrix.single_apply, ite_and, eq_comm]
  have hR : ∀ k l x y : Fin d, (C * Matrix.single k l (1:ℂ)) x y = if l = y then C x k else 0 := by
    intro k l x y; rw [Matrix.mul_apply]; simp [Matrix.single_apply, ite_and, eq_comm]
  have key : ∀ k l x y : Fin d, (if x = k then C l y else 0) = (if l = y then C x k else 0) := by
    intro k l x y
    have := congrFun (congrFun (h (Matrix.single k l 1)) x) y
    rwa [hL, hR] at this
  ext x y
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    have := key x i0 x i0
    simp at this
    rw [if_pos rfl, mul_one, ← this]
  · have := key y y x y
    simp [hxy] at this
    rw [if_neg hxy, mul_zero, this]

section Central

open MosonyiPetz

variable (m0 : Fin m) (i0 : Fin d)

theorem Q_apply (l : Fin K) (x y : (Fin d × Fin m) × Fin K) :
    Q (m := m) l x y = if x = y then (if x.2 = l then 1 else 0) else 0 := by
  obtain ⟨⟨a, b⟩, i⟩ := x
  obtain ⟨⟨a', b'⟩, i'⟩ := y
  rw [Q, embed_apply]
  simp only [Prod.mk.injEq]
  by_cases hi : i = i' <;> by_cases hl : i = l
  · subst hi; subst hl; simp [Matrix.one_apply, ite_and]
    split_ifs <;> simp_all
  · subst hi; simp [hl]
  · simp [hi]
  · simp [hi]

theorem Q_mul_apply (l : Fin K) (X : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ)
    (x y : (Fin d × Fin m) × Fin K) : ((Q l : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ) * X) x y = if x.2 = l then X x y else 0 := by
  rw [Matrix.mul_apply]
  simp only [Q_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem mul_Q_apply (l : Fin K) (X : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ)
    (x y : (Fin d × Fin m) × Fin K) : (X * (Q l : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ)) x y = if y.2 = l then X x y else 0 := by
  rw [Matrix.mul_apply]
  simp only [Q_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

theorem idem_cases {c : ℂ} (h : c * c = c) : c = 0 ∨ c = 1 := by
  have : c * (c - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

include m0 i0

theorem central_form {z : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ}
    (hz : IsCentralProjection (blockStarAlg d m K) z) :
    ∃ c : Fin K → ℂ, (∀ j, c j * c j = c j) ∧ z = embed (fun j => c j • 1) := by
  obtain ⟨hzB, hc, hzz, -⟩ := hz
  obtain ⟨C, rfl⟩ := mem_blockStarAlg.mp hzB
  have hcomm : ∀ j X, X * C j = C j * X := by
    intro j X
    have h := (Set.mem_centralizer_iff.mp hc) (embed (fun l => if l = j then X else 0))
      (mem_blockStarAlg.mpr ⟨_, rfl⟩)
    rw [embed_mul, embed_mul] at h
    have := congrFun (embed_injective m0 h) j
    simpa using this
  have hscal : ∀ j, C j = C j i0 i0 • 1 := fun j => scalar_of_commute i0 (hcomm j)
  refine ⟨fun j => C j i0 i0, fun j => ?_, by congr 1; funext j; exact hscal j⟩
  rw [embed_mul] at hzz
  have h := congrFun (embed_injective m0 hzz) j
  have h2 := congrFun (congrFun h i0) i0
  rw [Pi.mul_apply, hscal j] at h2
  simpa [Matrix.smul_apply, Matrix.one_apply] using h2

omit i0 in
theorem Q_isCentral (l : Fin K) : IsCentralProjection (blockStarAlg d m K) (Q l) := by
  refine ⟨mem_blockStarAlg.mpr ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · rw [Set.mem_centralizer_iff]
    intro a ha
    obtain ⟨A, rfl⟩ := mem_blockStarAlg.mp ha
    rw [Q, embed_mul, embed_mul]
    congr 1; funext j
    simp only [Pi.mul_apply]
    split_ifs <;> simp
  · rw [Q, embed_mul]
    congr 1; funext j
    simp only [Pi.mul_apply]
    split_ifs <;> simp
  · rw [Q, embed_conjTranspose]
    congr 1; funext j
    split_ifs <;> simp

omit i0 in
theorem Q_entry_self (l : Fin K) (a : Fin d) : Q (m := m) l ((a, m0), l) ((a, m0), l) = 1 := by
  rw [Q_apply]; simp

theorem Q_ne_zero (l : Fin K) : Q (m := m) (d := d) l ≠ 0 := fun h => by
  have := Q_entry_self m0 l i0
  rw [h] at this
  simp at this

theorem Q_injective : Function.Injective (Q (m := m) (d := d) (K := K)) := fun l l' h => by
  have := Q_entry_self m0 l i0
  rw [h, Q_apply] at this
  by_contra hne
  simp [hne] at this

theorem Q_minimal (l : Fin K) : IsMinimalCentralProjection (blockStarAlg d m K) (Q l) := by
  refine ⟨Q_isCentral m0 l, Q_ne_zero m0 i0 l, fun w hw hwQ => ?_⟩
  obtain ⟨c, hc, rfl⟩ := central_form m0 i0 hw
  rw [Q, embed_mul] at hwQ
  have h := embed_injective m0 hwQ
  have hcj : ∀ j, j ≠ l → c j = 0 := by
    intro j hj
    have := congrFun (congrFun (congrFun h j) i0) i0
    simp [hj, Matrix.smul_apply] at this
    exact this.symm
  rcases idem_cases (hc l) with h0 | h1
  · left
    rw [← embed_zero]
    congr 1; funext j
    by_cases hj : j = l
    · subst hj; simp [h0]
    · simp [hcj j hj]
  · right
    rw [Q]
    congr 1; funext j
    by_cases hj : j = l
    · subst hj; simp [h1]
    · simp [hcj j hj, hj]

theorem minimal_eq_Q {z : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ}
    (hz : IsMinimalCentralProjection (blockStarAlg d m K) z) : ∃ l, z = Q l := by
  obtain ⟨c, hc, rfl⟩ := central_form m0 i0 hz.1
  obtain ⟨l, hl⟩ : ∃ l, c l ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hz.2.1
    rw [← embed_zero]
    congr 1; funext j; simp [hcon j]
  have hl1 : c l = 1 := (idem_cases (hc l)).resolve_left hl
  have hQz : Q l * embed (m := m) (fun j => c j • (1 : Matrix (Fin d) (Fin d) ℂ)) = Q l := by
    rw [Q, embed_mul]
    congr 1; funext j
    simp only [Pi.mul_apply]
    split_ifs with hj
    · subst hj; simp [hl1]
    · simp
  rcases hz.2.2 (Q l) (Q_isCentral m0 l) hQz with h | h
  · exact absurd h (Q_ne_zero m0 i0 l)
  · exact ⟨l, h.symm⟩

end Central

end MosonyiPetzBlock
end


open Matrix
open scoped Matrix Kronecker

namespace MosonyiPetzBlock

open MosonyiPetz MosonyiPetzNormalizer

theorem prop4_main {d m K : ℕ} (hd : 0 < d) (hm : 0 < m)
    (u : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ)
    (hu : u ∈ Matrix.unitaryGroup ((Fin d × Fin m) × Fin K) ℂ)
    (hinv : ∀ a ∈ blockAlgebra d m K, star u * a * u ∈ blockAlgebra d m K) :
    ∃ (σ : Equiv.Perm (Fin K)) (v : Fin K → Matrix.unitaryGroup (Fin d) ℂ)
      (w : Fin K → Matrix.unitaryGroup (Fin m) ℂ),
      u = ∑ i, ((v i : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (w i : Matrix (Fin m) (Fin m) ℂ)) ⊗ₖ
        Matrix.single (σ i) i (1 : ℂ) := by
  classical
  set i0 : Fin d := ⟨0, hd⟩
  set m0 : Fin m := ⟨0, hm⟩
  set B := blockStarAlg d m K
  have hinv' : ∀ a ∈ B, star u * a * u ∈ B := hinv
  have huu : star u * u = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have huu' : u * star u = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  have hsurj : ∀ a ∈ B, u * a * star u ∈ B := by
    intro a ha
    have := conj_star_mem B hu hinv' a ha
    rwa [conj_apply, star_star] at this
  -- the block permutation
  have hτ : ∀ i, ∃ j, conj u (Q i) = Q j := fun i =>
    minimal_eq_Q m0 i0 ((isMinimalCentralProjection_conj_iff B hu hinv' (Q i)).mp
      (Q_minimal m0 i0 i))
  choose τ hτ using hτ
  have hτinj : Function.Injective τ := fun i i' h => by
    apply Q_injective m0 i0 (K := K)
    apply conj_injective hu
    rw [hτ, hτ, h]
  set e := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  set σ : Equiv.Perm (Fin K) := e.symm
  have hcomm : ∀ j, (Q (σ j) : Matrix ((Fin d × Fin m) × Fin K) _ ℂ) * u = u * Q j := by
    intro j
    have h := hτ (σ j)
    have hτσ : τ (σ j) = j := e.apply_symm_apply j
    rw [hτσ, conj_apply] at h
    calc (Q (σ j) : Matrix ((Fin d × Fin m) × Fin K) _ ℂ) * u
        = u * (star u * Q (σ j) * u) := by
          simp only [← Matrix.mul_assoc, huu', Matrix.one_mul]
      _ = u * Q j := by rw [h]
  have hblock : ∀ p k p' j, k ≠ σ j → u (p, k) (p', j) = 0 := by
    intro p k p' j hk
    have := congrFun (congrFun (hcomm j) (p, k)) (p', j)
    rw [Q_mul_apply, mul_Q_apply, if_neg hk, if_pos rfl] at this
    exact this.symm
  -- the blocks
  set U : Fin K → Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
    fun j => Matrix.of fun p p' => u (p, σ j) (p', j)
  have hdecomp : u = ∑ l, U l ⊗ₖ Matrix.single (σ l) l (1 : ℂ) := by
    ext ⟨p, k⟩ ⟨p', j⟩
    rw [Matrix.sum_apply, Finset.sum_eq_single j]
    · simp only [Matrix.kroneckerMap_apply, Matrix.single_apply, U, Matrix.of_apply, and_true]
      by_cases hk : σ j = k
      · subst hk; simp
      · rw [if_neg hk, mul_zero]; exact hblock p k p' j (Ne.symm hk)
    · intro l _ hlj
      simp [Matrix.kroneckerMap_apply, hlj]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin d × Fin m) ℂ := by
    intro j
    rw [Matrix.mem_unitaryGroup_iff']
    ext p p'
    have h := congrFun (congrFun huu (p, j)) (p', j)
    rw [Matrix.mul_apply, Fintype.sum_prod_type] at h
    rw [Matrix.mul_apply]
    have hinner : ∀ q : Fin d × Fin m, ∑ k, star u (p, j) (q, k) * u (q, k) (p', j) =
        star (U j) p q * U j q p' := by
      intro q
      rw [Finset.sum_eq_single (σ j)]
      · simp [Matrix.star_apply, U]
      · intro k _ hk
        rw [hblock q k p' j hk, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [hinner] at h
    rw [h, Matrix.one_apply, Matrix.one_apply]
    simp [Prod.ext_iff]
  -- the induced automorphisms of `M_d`
  have hθ : ∀ j (A : Matrix (Fin d) (Fin d) ℂ),
      U j * (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * star (U j) =
        (Matrix.of fun a a' => (U j * (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * star (U j))
          (a, m0) (a', m0)) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro j A
    set X := embed (m := m) (fun l => if l = j then A else 0)
    have hXB : X ∈ B := mem_blockStarAlg.mpr ⟨_, rfl⟩
    obtain ⟨C, hC⟩ := mem_blockStarAlg.mp (hsurj X hXB)
    have hstaru : star u = ∑ l, star (U l) ⊗ₖ Matrix.single l (σ l) (1 : ℂ) := by
      conv_lhs => rw [hdecomp]
      simp only [star_sum, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_single, star_one]
    have hX : X = (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) ⊗ₖ Matrix.single j j (1 : ℂ) := by
      simp only [X, embed]
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hl; simp [hl]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hY : u * X * star u = (U j * (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * star (U j)) ⊗ₖ
        Matrix.single (σ j) (σ j) (1 : ℂ) := by
      have h1 : ∀ l', (U l' ⊗ₖ Matrix.single (σ l') l' (1 : ℂ)) *
          ((A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) ⊗ₖ Matrix.single j j (1 : ℂ)) =
          if l' = j then (U j * (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))) ⊗ₖ
            Matrix.single (σ j) j (1 : ℂ) else 0 := by
        intro l'
        rw [← Matrix.mul_kronecker_mul, single_mul_single']
        split_ifs with h
        · subst h; rfl
        · exact Matrix.kronecker_zero _
      have h2 : ∀ l, ((U j * (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))) ⊗ₖ
          Matrix.single (σ j) j (1 : ℂ)) * (star (U l) ⊗ₖ Matrix.single l (σ l) (1 : ℂ)) =
          if j = l then (U j * (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * star (U j)) ⊗ₖ
            Matrix.single (σ j) (σ j) (1 : ℂ) else 0 := by
        intro l
        rw [← Matrix.mul_kronecker_mul, single_mul_single']
        split_ifs with h
        · subst h; rfl
        · exact Matrix.kronecker_zero _
      rw [hstaru, hX, hdecomp, Finset.sum_mul]
      simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.mul_sum]
      simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hY] at hC
    ext ⟨a, b⟩ ⟨a', b'⟩
    have h1 := congrFun (congrFun hC ((a, b), σ j)) ((a', b'), σ j)
    have h2 := congrFun (congrFun hC ((a, m0), σ j)) ((a', m0), σ j)
    simp only [Matrix.kroneckerMap_apply, Matrix.single_apply, and_self, if_true, mul_one,
      embed_apply] at h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply]
    rw [h1, h2]
    try simp
  have hkron : ∀ j, ∃ v ∈ Matrix.unitaryGroup (Fin d) ℂ, ∃ w ∈ Matrix.unitaryGroup (Fin m) ℂ,
      U j = v ⊗ₖ w := fun j => eq_kron_of_conj m0 (hU j) (hθ j) i0
  choose v hv w hw hvw using hkron
  refine ⟨σ, fun i => ⟨v i, hv i⟩, fun i => ⟨w i, hw i⟩, ?_⟩
  rw [hdecomp]
  exact Finset.sum_congr rfl fun l _ => by rw [hvw l]

end MosonyiPetzBlock

open MosonyiPetzBlock MosonyiPetz in
theorem solution (d m K : ℕ)
    (u : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ)
    (hu : u ∈ Matrix.unitaryGroup ((Fin d × Fin m) × Fin K) ℂ)
    (hinv : ∀ a ∈ blockAlgebra d m K, star u * a * u ∈ blockAlgebra d m K) :
    ∃ (σ : Equiv.Perm (Fin K)) (v : Fin K → Matrix.unitaryGroup (Fin d) ℂ)
      (w : Fin K → Matrix.unitaryGroup (Fin m) ℂ),
      u = ∑ i, ((v i : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (w i : Matrix (Fin m) (Fin m) ℂ)) ⊗ₖ
        Matrix.single (σ i) i (1 : ℂ) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨1, fun _ => 1, fun _ => 1, ?_⟩
    ext x
    exact x.1.1.elim0
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨1, fun _ => 1, fun _ => 1, ?_⟩
    ext x
    exact x.1.2.elim0
  exact prop4_main hd hm u hu hinv