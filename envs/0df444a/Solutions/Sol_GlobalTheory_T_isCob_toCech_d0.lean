-- Prove2me | solution 1 for GlobalTheory.T.isCob_toCech_d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:18:37.3427+00:00
-- url     : https://prove2.me/submissions/741c125f-5aa6-461e-8c6d-3a93aa90d29b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosetOneCochainToCechCochainCoboundary
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosetOneCochainToCechCochainCoboundaryStatement
import Theorems.Thm_GlobalTheory_CechCmp_posetOneCochainToCechCochain_coboundary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  first | exact @GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | exact GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | (intros; apply GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary <;> assumption)
end _root_.GlobalTheory.T
