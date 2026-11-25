-- Prove2me | solution 1 for GlobalTheory.AnDim.injective_fderiv_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:35.128665+00:00
-- url     : https://prove2.me/submissions/7121f845-d71f-4d90-bac3-e9152dee4dcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution {a b c : ℕ} {F : (Fin a → ℂ) → Fin b → ℂ}
    {G : (Fin b → ℂ) → Fin c → ℂ} {H : (Fin a → ℂ) → Fin c → ℂ} {z : Fin a → ℂ}
    (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G (F z)) (h : G ∘ F =ᶠ[𝓝 z] H)
    (hH : Function.Injective (fderiv ℂ H z)) : Function.Injective (fderiv ℂ F z) := by
  rw [← h.fderiv_eq, fderiv_comp z hG hF] at hH
  exact Function.Injective.of_comp (f := fderiv ℂ G (F z)) hH
end GlobalTheory.AnDim
