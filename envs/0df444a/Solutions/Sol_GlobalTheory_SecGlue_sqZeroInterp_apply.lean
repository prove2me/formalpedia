-- Prove2me | solution 1 for GlobalTheory.SecGlue.sqZeroInterp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:53.885478+00:00
-- url     : https://prove2.me/submissions/bdf616f6-dcf1-48ba-96f1-d783db504713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPow

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
open GlobalTheory GlobalTheory.SecGlue
namespace GlobalTheory.SecGlue
theorem _root_.solution {R B S : Type} [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S)
    (h : ∀ x, β x - α x ∈ J) (c : S) (x : B) :
    sqZeroInterp J hJ α β h c x = α x + c * (β x - α x) := rfl
end GlobalTheory.SecGlue
