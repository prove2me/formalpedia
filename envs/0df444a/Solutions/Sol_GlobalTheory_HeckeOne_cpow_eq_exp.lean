-- Prove2me | solution 1 for GlobalTheory.HeckeOne.cpow_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:41:47.693347+00:00
-- url     : https://prove2.me/submissions/8c169cad-f7fb-463e-8607-088ca4919068

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Theorems.Thm_GlobalTheory_HeckeOne_ideleNorm_pos

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
theorem _root_.solution (x : Ideles K) (t : ℝ) :
    ((ideleNorm x : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
      ((Circle.exp (t * Real.log (ideleNorm x)) : Circle) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ideleNorm_pos x).ne'), Circle.coe_exp,
    ← Complex.ofReal_log (ideleNorm_pos x).le]
  congr 1
  push_cast
  ring
end GlobalTheory.HeckeOne
