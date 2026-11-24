-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.isIntegral_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:58:55.398095+00:00
-- url     : https://prove2.me/submissions/d66ace24-967b-4c89-b53e-f80839bdfd95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProductLatticePositionsAndTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.2 := hx.map (AlgHom.snd R A₁ A₂)
end GlobalTheory.UnitLemma.Desc
