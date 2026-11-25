-- Prove2me | solution 1 for GlobalTheory.InjHol.bijective_fderiv_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:09.533352+00:00
-- url     : https://prove2.me/submissions/f6de77fd-2790-46ba-bf77-dc34ca1bac66

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Theorems.Thm_GlobalTheory_InjHol_localStatement
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol
namespace GlobalTheory.InjHol
theorem _root_.solution :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → (Fin n → ℂ)), IsOpen U →
      DifferentiableOn ℂ f U → Set.InjOn f U → ∀ a ∈ U, Function.Bijective (fderiv ℂ f a) := by
  intro n U f hU hf hinj a ha
  have han : AnalyticAt ℂ f a := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n U (fun x => f x i) hU (differentiableOn_pi.mp hf i) a ha
  have hi := localStatement n _ _ (by simp) (by simp) f a han ⟨U, hU.mem_nhds ha, hinj⟩
  exact ⟨hi, LinearMap.injective_iff_surjective.mp
    (show Function.Injective (fderiv ℂ f a : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) from hi)⟩
end GlobalTheory.InjHol
