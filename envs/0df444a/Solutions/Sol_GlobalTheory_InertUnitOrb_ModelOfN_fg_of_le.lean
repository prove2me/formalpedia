-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.fg_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:39.527801+00:00
-- url     : https://prove2.me/submissions/c8165fe1-222f-443c-8f68-46ce6983f128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
variable {K : UQ}
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K.O V] (L N : Submodule K.O V) (hfg : L.FG) (hle : N ≤ L) :
    N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian L hfg
  have h1 := (IsNoetherian.noetherian (N.comap L.subtype)).map L.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h1
end GlobalTheory.InertUnitOrb.ModelOfN
