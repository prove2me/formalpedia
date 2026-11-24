-- Prove2me | solution 1 for GlobalTheory.RealWeil.toLp_dRho_omS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:50.179498+00:00
-- url     : https://prove2.me/submissions/1e04453c-e5a7-43d1-b52d-009f6404786f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_omS_dRho
import Theorems.Thm_GlobalTheory_RealWeil_dRho_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
variable {G : Type} [Group G] {pr : G →* Matrix.symplecticGroup l ℝ} {om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)}
  {omS : G →* (Sch l →L[ℂ] Sch l)}
namespace GlobalTheory.RealWeil
theorem _root_.solution
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume) (A : Sch l →L[ℂ] Sch l) (g : G)
    (w : l ⊕ l → ℝ) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (omS g f)) = ∑ a,
      (((-(Matrix.J l ℝ * (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * Matrix.J l ℝ)) *ᵥ w) a : ℂ) •
        schwartzToL2 l (A (omS g (dRho (Pi.single a 1) f))) := by
  have h1 : (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ
      ((-(Matrix.J l ℝ * (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * Matrix.J l ℝ)) *ᵥ w) = w := by
    rw [mulVec_mulVec, mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      SymplecticGroup.mem_iff.1 (pr g).2, J_squared, neg_neg, one_mulVec]
  rw [ContinuousLinearMap.mul_apply]
  conv_lhs => rw [← h1, ← omS_dRho h3 h4, dRho_eq_sum]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
end GlobalTheory.RealWeil
