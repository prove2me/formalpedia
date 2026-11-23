-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.away_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:01.22394+00:00
-- url     : https://prove2.me/submissions/2014343a-fe66-4110-9b20-e530b1531812

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution {R T : Type} [CommRing R] [CommRing T] (a : R) (φ ψ : Localization.Away a →+* T)
    (h : φ.comp (algebraMap R _) = ψ.comp (algebraMap R _)) : φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h
end GlobalTheory.SecGlue.Red
