-- Prove2me | solution 1 for GlobalTheory.HeckeOne.isUnitary_normChar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:11.568509+00:00
-- url     : https://prove2.me/submissions/d03e2ddd-f38c-4986-9c68-9bfb517e41fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Theorems.Thm_GlobalTheory_HeckeOne_normChar_apply

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
theorem _root_.solution (t : ℝ) : (normChar K t).IsUnitary := fun x => by
  rw [normChar_apply]; exact Circle.norm_coe _
end GlobalTheory.HeckeOne
