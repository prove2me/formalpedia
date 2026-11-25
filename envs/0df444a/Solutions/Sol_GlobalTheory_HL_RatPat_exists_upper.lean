-- Prove2me | solution 1 for GlobalTheory.HL.RatPat.exists_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:51.460192+00:00
-- url     : https://prove2.me/submissions/9ccd6052-87fc-4128-bd9a-a1889829f550

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliser
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatPat
namespace GlobalTheory.HL.RatPat
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (Z u : Matrix (Fin n) (Fin n) K) (ρ : Fin n → Fin n)
    (B : Fin n → Fin n → Prop) (hρ : Function.Involutive ρ) (hZ : ∀ a b, Z a b ≠ 0 ↔ b = ρ a)
    (hB : ∀ x y, x < y → B x y → ρ y < ρ x) (hu1 : ∀ a, u a a = 1)
    (hu0 : ∀ a b, a ≠ b → ¬ (b < a ∧ B b a) → u a b = 0) :
    ∃ s : Matrix (Fin n) (Fin n) K, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ u * Z * s = Z := by
  have hZd : ∀ a, Z a (ρ a) ≠ 0 := fun a => (hZ a _).2 rfl
  have hZd' : ∀ b, Z (ρ b) b ≠ 0 := fun b => (hZ _ _).2 (hρ b).symm
  let M : Matrix (Fin n) (Fin n) K := fun a b => u (ρ a) (ρ b) * Z (ρ b) b / Z (ρ a) a
  have hMup : M.BlockTriangular id := by
    intro i j hij
    simp only [id] at hij
    show u (ρ i) (ρ j) * Z (ρ j) j / Z (ρ i) i = 0
    rw [hu0 (ρ i) (ρ j) (fun h => (ne_of_gt hij) (hρ.injective h)) ?_]
    · simp
    · rintro ⟨h1, h2⟩
      have := hB _ _ h1 h2
      rw [hρ, hρ] at this
      exact absurd hij (not_lt.2 this.le)
  have hMd : ∀ i, M i i = 1 := by
    intro i
    show u (ρ i) (ρ i) * Z (ρ i) i / Z (ρ i) i = 1
    rw [hu1, one_mul, div_self (hZd' i)]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular hMup]
    simp [hMd]
  have hZM : Z * M = u * Z := by
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (ρ a), Finset.sum_eq_single (ρ b)]
    · show Z a (ρ a) * (u (ρ (ρ a)) (ρ b) * Z (ρ b) b / Z (ρ (ρ a)) (ρ a)) = u a (ρ b) * Z (ρ b) b
      rw [hρ a]
      field_simp [hZd a]
    · intro c _ hc
      have : Z c b = 0 := by
        by_contra h
        apply hc
        rw [(hZ c b).1 h, hρ]
      rw [this, mul_zero]
    · simp
    · intro c _ hc
      have : Z a c = 0 := by
        by_contra h
        exact hc ((hZ a c).1 h)
      rw [this, zero_mul]
    · simp
  haveI : Invertible M := Matrix.invertibleOfIsUnitDet M (by rw [hdet]; exact isUnit_one)
  refine ⟨M⁻¹, ⟨fun i j hij => Matrix.blockTriangular_inv_of_blockTriangular hMup hij, fun i => ?_⟩, ?_⟩
  · have h1 : (M⁻¹ * M) i i = 1 := by rw [Matrix.inv_mul_of_invertible]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rwa [hMd, mul_one] at h1
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [Matrix.blockTriangular_inv_of_blockTriangular hMup h, zero_mul]
      · rw [hMup h, mul_zero]
    · simp
  · rw [← hZM, Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
end GlobalTheory.HL.RatPat
