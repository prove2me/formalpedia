-- Prove2me | solution 1 for GlobalTheory.SecGlue.CombEx.comp_combHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:24.233614+00:00
-- url     : https://prove2.me/submissions/30e9ba68-2593-4900-b74a-ec8cb4212f28

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
theorem _root_.solution {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) : q.comp (combHom q hsq φ ψ a hq) = q.comp φ := by
  ext x
  have hd : ∀ i, q (ψ i x - φ x) = 0 := fun i => by
    rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
  simp only [RingHom.comp_apply, combHom_apply, map_add, map_sum, map_mul, hd, mul_zero,
    Finset.sum_const_zero, add_zero]
end GlobalTheory.SecGlue.CombEx
