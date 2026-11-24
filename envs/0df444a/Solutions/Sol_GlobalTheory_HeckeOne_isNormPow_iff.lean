-- Prove2me | solution 1 for GlobalTheory.HeckeOne.isNormPow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:58:31.36849+00:00
-- url     : https://prove2.me/submissions/34027d0c-0142-44be-a24f-c2184978ac08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Theorems.Thm_GlobalTheory_HeckeOne_cpow_eq_exp
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
theorem _root_.solution (χ : HChar K) (t : ℝ) : IsNormPow χ t ↔ χ = normChar K t := by
  constructor
  · intro h
    exact Subtype.ext (MonoidHom.ext fun x => Units.ext (by rw [h x, cpow_eq_exp, normChar_apply]))
  · rintro rfl x
    rw [cpow_eq_exp, normChar_apply]
end GlobalTheory.HeckeOne
