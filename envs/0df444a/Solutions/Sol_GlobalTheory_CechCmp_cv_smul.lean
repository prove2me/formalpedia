-- Prove2me | solution 1 for GlobalTheory.CechCmp.cv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:32:34.745672+00:00
-- url     : https://prove2.me/submissions/c799ce0d-1cc8-4aa0-aef2-03729bfc47c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def


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
theorem _root_.solution {T : (NE I)ᵒᵖ} (r : R) (b : (capF s U hU hinf).obj T) :
    cv s U hU hinf T (r • b) = constFn s (cap U T.unop) r * cv s U hU hinf T b :=
  Algebra.smul_def r b
end GlobalTheory.CechCmp
