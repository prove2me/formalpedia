-- Prove2me | solution 1 for GlobalTheory.HeckeOne.unrAt_normChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:26.937631+00:00
-- url     : https://prove2.me/submissions/7c8bf538-c770-454a-957c-dc268a69caa2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Theorems.Thm_GlobalTheory_HeckeOne_normChar_apply
import Theorems.Thm_GlobalTheory_HeckeOne_ideleNorm_localIdele
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_ideleNorm_localIdele
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
theorem _root_.solution (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) : (normChar K t).UnrAt v := fun u hu => by
  apply Units.ext
  change (((normChar K t).1 (Neutral.B1.localIdele K v u) : ℂˣ) : ℂ) = _
  rw [normChar_apply, ideleNorm_localIdele, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued hu]
  simp
end GlobalTheory.HeckeOne
