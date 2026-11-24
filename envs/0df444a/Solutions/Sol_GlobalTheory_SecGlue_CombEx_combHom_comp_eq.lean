-- Prove2me | solution 1 for GlobalTheory.SecGlue.CombEx.combHom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:23.246621+00:00
-- url     : https://prove2.me/submissions/cf08ad38-5b82-4edd-a460-6265ced8c9d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_combHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx
namespace GlobalTheory.SecGlue.CombEx
theorem _root_.solution {R A S T : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (θ : R →+* A) (hθ : ∀ i, (ψ i).comp θ = φ.comp θ) :
    (combHom q hsq φ ψ a hq).comp θ = φ.comp θ := by
  ext r
  have h : ∀ i, ψ i (θ r) = φ (θ r) := fun i => RingHom.congr_fun (hθ i) r
  simp only [RingHom.comp_apply, combHom_apply, h, sub_self, mul_zero, Finset.sum_const_zero, add_zero]
end GlobalTheory.SecGlue.CombEx
