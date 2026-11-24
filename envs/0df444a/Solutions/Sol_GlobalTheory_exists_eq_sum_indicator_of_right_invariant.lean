-- Prove2me | solution 1 for GlobalTheory.exists_eq_sum_indicator_of_right_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:34.291965+00:00
-- url     : https://prove2.me/submissions/3fc66c1c-eb6e-404f-9dc9-b824053bdb90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_LatticeIndicator_exists_eq_sum_ite_integral
import Theorems.Thm_GlobalTheory_LatticeIndicator_forall_mem_range_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open LatticeIndicator
variable {O K m n R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]
namespace GlobalTheory
theorem _root_.solution {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL n O),
      φ (x * (k : Matrix n n O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    ∃ (r : ℕ) (h : Fin r → GL m K) (c : Fin r → R), ∀ x : Matrix m n K,
      φ x = ∑ l, c l * Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 ((((h l)⁻¹ : GL m K) : Matrix m m K) * x) := by
  classical
  set f := algebraMap O K with hf
  have hinj : Function.Injective f := IsFractionRing.injective O K
  have ha' : f a ≠ 0 := (map_ne_zero_iff f hinj).2 ha
  obtain ⟨r, h, c, hdet, hψ⟩ := exists_eq_sum_ite_integral (mul_ne_zero ha hb)
    (fun z : Matrix m n O => φ ((f a)⁻¹ • z.map f))
    (fun z k => by rw [Matrix.map_mul, ← Matrix.smul_mul, hinv])
    (fun z y => by
      have : (f a)⁻¹ • (z + (a * b) • y).map f = (f a)⁻¹ • z.map f + f b • y.map f := by
        ext i j
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply, smul_eq_mul, map_add,
          map_mul]
        field_simp
      rw [this, hper _ (y.map f) fun i j => ⟨y i j, rfl⟩])
  have hdet' : ∀ l, ((f a)⁻¹ • (h l).map f).det ≠ 0 := by
    intro l
    rw [Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha')) ?_
    have := RingHom.map_det f (h l)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero_iff f hinj).2 (hdet l)
  let H : Fin r → GL m K := fun l => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet' l)
  have hH : ∀ l, (H l : Matrix m m K) = (f a)⁻¹ • (h l).map f := fun l => rfl
  have hmem : ∀ l (x : Matrix m n K),
      ((((H l)⁻¹ : GL m K) : Matrix m m K) * x ∈
        {y : Matrix m n K | ∀ i j, y i j ∈ f.range}) ↔
      ∃ y : Matrix m n O, f a • x = (h l * y).map f := by
    intro l x
    rw [Set.mem_setOf_eq, hf, forall_mem_range_iff, ← hf]
    refine exists_congr fun y => ?_
    rw [Matrix.map_mul]
    have h1 : (h l).map f = f a • (H l : Matrix m m K) := by
      rw [hH, smul_smul, mul_inv_cancel₀ ha', one_smul]
    rw [h1, Matrix.smul_mul, (smul_right_injective _ ha').eq_iff]
    constructor
    · intro hy
      rw [hy, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    · intro hy
      rw [hy, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨r, H, c, fun x => ?_⟩
  by_cases hx : ∃ z : Matrix m n O, z.map f = f a • x
  · obtain ⟨z, hz⟩ := hx
    have h1 := hψ z
    simp only [hz, smul_smul, inv_mul_cancel₀ ha', one_smul] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Set.indicator_apply]
    have h2 : ∀ y : Matrix m n O, f a • x = (h l * y).map f ↔ z = h l * y := fun y => by
      rw [← hz]
      exact (Matrix.map_injective hinj).eq_iff
    simp only [hmem, h2, Pi.one_apply]
  · have h0 : φ x = 0 := by
      by_contra h0
      exact hx ((forall_mem_range_iff _).1 (hsupp x h0))
    rw [h0]
    refine (Finset.sum_eq_zero fun l _ => ?_).symm
    rw [Set.indicator_of_notMem, mul_zero]
    rw [hmem]
    rintro ⟨y, hy⟩
    exact hx ⟨_, hy.symm⟩
end GlobalTheory
