-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.redPsi_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:14.956867+00:00
-- url     : https://prove2.me/submissions/61786c36-ac69-4e1b-8e03-5dbcf9f55e69

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
variable {R R₀ : Type} [CommRing R] [CommRing R₀]
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S]
    [Algebra R S] : (redPsi π hπ S).comp π = (Ideal.Quotient.mk (redI π S)).comp (algebraMap R S) :=
  RingHom.liftOfRightInverse_comp _ _ _ _
end GlobalTheory.SecGlue.Red
