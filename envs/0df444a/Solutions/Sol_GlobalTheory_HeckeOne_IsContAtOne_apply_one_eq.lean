-- Prove2me | solution 1 for GlobalTheory.HeckeOne.IsContAtOne.apply_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:54.772904+00:00
-- url     : https://prove2.me/submissions/2803a46a-9796-413b-b508-5173885389b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
import Theorems.Thm_GlobalTheory_CMVal_IsLatSum_unique
import Theorems.Thm_GlobalTheory_CMVal_IsToricSum_unique
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles eulerFactor IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.HeckeOne
namespace IsContAtOne
theorem _root_.solution {χ : HChar K} {Λ Λ' : ℂ → ℂ} (h : IsContAtOne χ Λ) (h' : IsContAtOne χ Λ') :
    Λ 1 = Λ' 1 := by
  have hc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique_of_eventuallyEq (h.1.continuousAt.tendsto.comp hc)
    (h'.1.continuousAt.tendsto.comp hc) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (h.2 x hx).unique (h'.2 x hx)
end IsContAtOne
end GlobalTheory.HeckeOne
