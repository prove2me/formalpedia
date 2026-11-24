-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.unimod_of_unimodFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:23.275668+00:00
-- url     : https://prove2.me/submissions/8b475e8e-59c8-4be2-9216-123bffbb008d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCosetSumUnimodularityOfFiniteIndex
import Theorems.Thm_GlobalTheory_SatakeWeyl_finsum_quotient_subgroupOf
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution : UnimodFin → Unimod := by
  intro H A _ Γ U V f _ _ hUi hVi hΓ hfV hfU
  have h := H Γ (U.subgroupOf Γ) (V.subgroupOf Γ) (fun a => f a) hUi hVi
    (fun v hv a => hfV _ (Subgroup.mem_subgroupOf.1 hv) _)
    (fun u hu a => hfU _ (Subgroup.mem_subgroupOf.1 hu) _)
  rw [finsum_quotient_subgroupOf Γ U f hΓ hfU,
    finsum_quotient_subgroupOf Γ V (fun a => f a⁻¹) (fun a ha => (inv_mem_iff.1 (hΓ _ ha)))
      (fun w hw a => by rw [mul_inv_rev, hfV _ (inv_mem hw)])]
  exact h
end GlobalTheory.SatakeWeyl
