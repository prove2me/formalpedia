-- Prove2me | solution 1 for GlobalTheory.HeckeOne.normChar_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:45.421079+00:00
-- url     : https://prove2.me/submissions/1715c11e-6b97-4782-a6c0-86b3f11b75be

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
theorem _root_.solution (s t : ℝ) : normChar K (s + t) = normChar K s * normChar K t :=
  Subtype.ext (MonoidHom.ext fun x => Units.ext (by
    change _ = (((normChar K s).1 x : ℂˣ) : ℂ) * (((normChar K t).1 x : ℂˣ) : ℂ)
    rw [normChar_apply, normChar_apply, normChar_apply, add_mul, Circle.exp_add, Circle.coe_mul]))
end GlobalTheory.HeckeOne
