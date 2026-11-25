-- Prove2me | solution 1 for GroundTheory.Brauer.nonempty_algEquiv_of_isBrauerEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:36:32.410722+00:00
-- url     : https://prove2.me/submissions/c1a12698-757e-487b-9e70-67e8e4634262

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_iff_nonempty_algEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v
namespace GroundTheory.Brauer
theorem _root_.solution {K : Type u} [Field K] {A B : CSA.{u, v} K}
    (h : IsBrauerEquivalent A B) (hd : Module.finrank K A = Module.finrank K B) :
    Nonempty (A ≃ₐ[K] B) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨n, hn, D, _, _, _, ⟨eA⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  obtain ⟨m, hm, D', _, _, _, ⟨eB⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K B
  obtain ⟨φ⟩ := (isBrauerEquivalent_iff_nonempty_algEquiv eA eB).1 h
  have hdA := eA.toLinearEquiv.finrank_eq
  have hdB := eB.toLinearEquiv.finrank_eq
  rw [Module.finrank_matrix, Fintype.card_fin] at hdA hdB
  have hDD : Module.finrank K D = Module.finrank K D' := φ.toLinearEquiv.finrank_eq
  have hD0 : 0 < Module.finrank K D := Module.finrank_pos
  obtain rfl : n = m := by
    rw [hdA, hdB, ← hDD] at hd
    exact Nat.mul_self_inj.1 (Nat.eq_of_mul_eq_mul_right hD0 hd)
  exact ⟨eA.trans (φ.mapMatrix.trans eB.symm)⟩
end GroundTheory.Brauer
