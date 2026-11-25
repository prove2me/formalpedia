-- Prove2me | solution 1 for GroundTheory.Global.coe_decomposition_smul_integerUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:37:05.121032+00:00
-- url     : https://prove2.me/submissions/da58ed66-35e4-4cb7-a887-4a3ddabbcdb7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
variable {w}
variable (w)
variable {w}
namespace GroundTheory.Global
theorem _root_.solution (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (u : (w.adicCompletionIntegers L)ˣ) :
    (((σ • u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L) :
      w.adicCompletion L) = σ • ((u : w.adicCompletionIntegers L) : w.adicCompletion L) :=
  rfl
end GroundTheory.Global
