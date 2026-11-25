-- Prove2me | solution 1 for GlobalTheory.ThetaPoint.isSymm_and_eq_imInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:53.174565+00:00
-- url     : https://prove2.me/submissions/f4c65ad6-5f44-4863-8655-6a8c9163885f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHalfOfSqEqOne
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_single
import Theorems.Thm_GlobalTheory_SiegelNormalForm_siegel_of_relations
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.ThetaPoint
open CanTh
variable {g : ℕ}
namespace GlobalTheory.ThetaPoint
theorem _root_.solution {M τ : Matrix (Fin g) (Fin g) ℂ} (hH : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) (hτ : (τ.map Complex.im).PosDef)
    {s : ℝ} (hs : s = 1 ∨ s = -1)
    (h₁₁ : ∀ i j, (hermForm M (Pi.single i 1) (Pi.single j 1)).im = 0)
    (h₁₂ : ∀ i j, (hermForm M (Pi.single i 1) (τ *ᵥ Pi.single j 1)).im = if i = j then s else 0)
    (h₂₂ : ∀ i j, (hermForm M (τ *ᵥ Pi.single i 1) (τ *ᵥ Pi.single j 1)).im = 0) :
    τ.IsSymm ∧ M = imInv τ := by
  let Y : Matrix (Fin g) (Fin g) ℝ := M.map Complex.re
  have hY : M = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · have := h₁₁ i j
      rw [hermForm, SiegelNormalForm.form_single] at this
      simpa using this
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (hH.apply i j)
    simpa [Y] using this
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : (fun i => (a i : ℂ)) ≠ 0 := fun h0 =>
      ha (funext fun i => by simpa using congrFun h0 i)
    have := hpos _ hne
    rw [hY] at this
    simpa [hermForm, Matrix.mulVec, dotProduct] using this
  rw [hY] at h₁₂ h₂₂
  rcases hs with rfl | rfl
  · obtain ⟨-, h2, -⟩ := SiegelNormalForm.siegel_of_relations Y hYp (-τ)
      (fun i j => by
        have := h₁₂ i j
        rw [hermForm] at this
        rw [Matrix.neg_mulVec, star_neg, Matrix.mulVec_neg, dotProduct_neg, Complex.neg_im, this]
        split_ifs <;> simp)
      (fun i j => by
        have := h₂₂ i j
        rw [hermForm] at this
        rw [Matrix.neg_mulVec, Matrix.neg_mulVec, star_neg, Matrix.mulVec_neg, dotProduct_neg,
          neg_dotProduct, neg_neg, this])
    have hf : ∀ i : Fin g, False := fun i => by
      have e1 := h2.diag_pos (i := i)
      have e2 := hτ.diag_pos (i := i)
      simp only [Matrix.map_apply, Matrix.neg_apply, Complex.neg_im] at e1 e2
      linarith
    exact ⟨by ext i; exact (hf i).elim, by ext i; exact (hf i).elim⟩
  · obtain ⟨h1, -, h3⟩ := SiegelNormalForm.siegel_of_relations Y hYp τ h₁₂ h₂₂
    refine ⟨h1, ?_⟩
    rw [hY, imInv, Matrix.inv_eq_left_inv h3]
end GlobalTheory.ThetaPoint
