-- Prove2me | solution 1 for GlobalTheory.RealWeil.omS_dRho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:44:29.33168+00:00
-- url     : https://prove2.me/submissions/91d18249-3dd8-4b0a-890a-1f3d9f191678

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_inner_rho

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
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume) (g : G) (w : l ⊕ l → ℝ) (f : Sch l) :
    omS g (dRho w f) = dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f) := by
  have key : ∀ φ : Sch l, inner ℂ (φ.toLp 2 volume) ((omS g (dRho w f)).toLp 2 volume) =
      inner ℂ (φ.toLp 2 volume) ((dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f)).toLp 2 volume) := fun φ => by
    have e : ∀ v : L2 l, inner ℂ ((omS g⁻¹ φ).toLp 2 volume) v = inner ℂ (φ.toLp 2 volume) (om g v) := fun v => by
      rw [← (om g).inner_map_map, h4, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        ContinuousLinearMap.one_apply]
    have d1 := hasDerivAt_inner_rho w (omS g⁻¹ φ) f
    have d2 := hasDerivAt_inner_rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) φ (omS g f)
    simp only [e, h3, h4, mulVec_smul] at d1
    exact d1.unique d2
  apply injective_toLp 2 volume
  have := key (omS g (dRho w f) - dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f))
  rw [← sub_eq_zero, ← inner_sub_right, ← toLpCLM_apply (𝕜 := ℂ), map_sub] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)
end GlobalTheory.RealWeil
