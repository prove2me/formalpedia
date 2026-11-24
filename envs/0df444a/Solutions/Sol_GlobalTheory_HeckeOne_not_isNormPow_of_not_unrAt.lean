-- Prove2me | solution 1 for GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:14:18.39699+00:00
-- url     : https://prove2.me/submissions/c37ae8d3-51bc-4817-8008-3fe9fcfb82ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Theorems.Thm_GlobalTheory_HeckeOne_isNormPow_iff
import Theorems.Thm_GlobalTheory_HeckeOne_unrAt_normChar

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
theorem _root_.solution {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : ¬ χ.UnrAt v) :
    ¬ ∃ t : ℝ, IsNormPow χ t := fun ⟨t, ht⟩ => h ((isNormPow_iff χ t).1 ht ▸ unrAt_normChar t v)
end GlobalTheory.HeckeOne
