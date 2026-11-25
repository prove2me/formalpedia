-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.hodgeTate_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:51.013481+00:00
-- url     : https://prove2.me/submissions/5500cb4c-5034-4b2f-8672-fd37da0ae716

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
theorem _root_.solution [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    (∀ t, hodgeTate (mu p O) t = 0) ∧ hodgeTate (const p O) (constGen p O) ≠ 0 := by
  refine ⟨fun t => Subsingleton.elim _ _, fun h => dlogT_ne_zero p O hp ?_⟩
  rw [hodgeTate_eq_omegaMap, ← dualHom_constHom, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], dualHom_id,
    Category.id_comp] at h
  have h2 := LinearMap.congr_fun (omegaMap_comp (mu p O).bidual.hom (mu p O).bidual.inv) (dlogT p O)
  rw [Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h2
  rw [h2]
  exact (congrArg _ h).trans (map_zero _)
end GlobalTheory.PDivGroup.Test
