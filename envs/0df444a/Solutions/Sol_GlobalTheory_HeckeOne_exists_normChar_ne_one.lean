-- Prove2me | solution 1 for GlobalTheory.HeckeOne.exists_normChar_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:18.802805+00:00
-- url     : https://prove2.me/submissions/5a05fa9c-e18a-45b3-885c-f418ca97e204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Theorems.Thm_Formalism_L2_Host_unif_spec
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_exists_normPow_valueAt_eq_neg_one
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_normPow_isUnramifiedAt
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_valueAt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles eulerFactor IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.HeckeOne
theorem _root_.solution : ∃ t : ℝ, normChar K t ≠ 1 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩
  obtain ⟨t, ht⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.exists_normPow_valueAt_eq_neg_one v
  refine ⟨t, fun h => ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt_eq _
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_isUnramifiedAt t v) (Formalism.L2.Host.unif_spec v)] at ht
  have h2 : (((normChar K t).val v : ℂˣ) : ℂ) = -1 := ht
  rw [h] at h2
  have h3 : (1 : ℂ) = -1 := h2
  norm_num at h3
end GlobalTheory.HeckeOne
