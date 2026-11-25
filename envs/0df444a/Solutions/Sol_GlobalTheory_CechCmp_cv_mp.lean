-- Prove2me | solution 1 for GlobalTheory.CechCmp.cv_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:04:28.35186+00:00
-- url     : https://prove2.me/submissions/1689ab82-76f2-4ae5-a8e3-c31b7d6baa3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Theorems.Thm_GlobalTheory_KS_rsT_of_le


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
theorem _root_.solution {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') (b : (capF s U hU hinf).obj T) :
    cv s U hU hinf T' (mp (capF s U hU hinf) a b) = rsT (cv s U hU hinf T b) (cap U T'.unop) :=
  (GlobalTheory.KS.rsT_of_le (O₀ := cap U T.unop) (cap_mono U (leOfHom a.unop)) b).symm
end GlobalTheory.CechCmp
