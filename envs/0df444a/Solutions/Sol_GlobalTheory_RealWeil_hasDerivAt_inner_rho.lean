-- Prove2me | solution 1 for GlobalTheory.RealWeil.hasDerivAt_inner_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:21.360837+00:00
-- url     : https://prove2.me/submissions/fad34587-23c1-4222-b191-298a7831906b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_rhoFun_at
import Theorems.Thm_GlobalTheory_RealWeil_inner_toLp_rho

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
omit [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (w : l ⊕ l → ℝ) (φ f : Sch l) :
    HasDerivAt (fun t : ℝ => inner ℂ (φ.toLp 2 volume) (rho (t • w) (f.toLp 2 volume)))
      (inner ℂ (φ.toLp 2 volume) ((dRho w f).toLp 2 volume)) 0 := by
  have hc : ∀ (u : l ⊕ l → ℝ) (g : Sch l), Continuous fun x => inner ℂ (φ x) (rhoFun u g x) := fun u g =>
    φ.continuous.inner ((continuous_phase u).mul (g.continuous.comp (continuous_add_const _)))
  have hb : ∀ (u : l ⊕ l → ℝ) (g : Sch l) (x), ‖inner ℂ (φ x) (rhoFun u g x)‖ ≤
      ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 g := fun u g x => by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [rhoFun, norm_mul, norm_phase, one_mul]
    exact norm_le_seminorm ℝ g _
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := Set.univ) (x₀ := (0 : ℝ))
    (F := fun t x => inner ℂ (φ x) (rhoFun (t • w) f x))
    (F' := fun t x => inner ℂ (φ x) (rhoFun (t • w) (dRho w f) x))
    (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 (dRho w f)) Filter.univ_mem
    (.of_forall fun t => (hc _ _).aestronglyMeasurable)
    ((φ.integrable.norm.mul_const _).mono' (hc _ _).aestronglyMeasurable (.of_forall (hb _ f)))
    (hc _ _).aestronglyMeasurable (.of_forall fun x t _ => hb _ _ x) (φ.integrable.norm.mul_const _)
    (.of_forall fun x t _ => ((innerSL ℂ (φ x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_rhoFun_at w f x t))).2
  simp only [inner_toLp_rho, inner_toL2_toL2_eq]
  simpa only [zero_smul, rhoFun_zero] using this
end GlobalTheory.RealWeil
