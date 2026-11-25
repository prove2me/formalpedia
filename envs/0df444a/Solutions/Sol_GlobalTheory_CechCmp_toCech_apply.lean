-- Prove2me | solution 1 for GlobalTheory.CechCmp.toCech_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:51:27.030401+00:00
-- url     : https://prove2.me/submissions/f951fc6f-ceb2-4015-bbdc-4c115c87a566

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechCmp
variable {I : Type} {X : Scheme.{0}}
variable {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))
namespace GlobalTheory.CechCmp
theorem _root_.solution (f : CatCoh.C1 (capF s U hU hinf)) (i j : I) :
    toCech s U hU hinf f i j =
      rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single i)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_left i j)).op))
        (U i ⊓ U j) -
      rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single j)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_right i j)).op))
        (U i ⊓ U j) := rfl
end GlobalTheory.CechCmp
