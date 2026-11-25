-- Prove2me | solution 1 for GlobalTheory.CechCmp.cv_toPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:01:04.390448+00:00
-- url     : https://prove2.me/submissions/180b90c2-4300-4d2a-817a-ab97555efc90

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
theorem _root_.solution (c : C1 U) {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') :
    cv s U hU hinf T' (toPos s U hU hinf c T T' a) = rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop) :=
  RingEquiv.apply_symm_apply _ _
end GlobalTheory.CechCmp
