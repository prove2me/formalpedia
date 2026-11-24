-- Prove2me | solution 1 for GlobalTheory.NearlyPrimitive.norm_natCast_eq_one_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:58.94906+00:00
-- url     : https://prove2.me/submissions/5ee9a233-139b-46b5-a821-4376ac7a3afe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.NearlyPrimitive
theorem _root_.solution {p m : ℕ} (hp : ‖(p : C)‖ < 1) (h : Nat.Coprime p m) :
    ‖(m : C)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one C m) ?_
  by_contra hlt
  push Not at hlt
  have hb : ((Nat.gcd p m : ℤ) : C) = ((p * Nat.gcdA p m + m * Nat.gcdB p m : ℤ) : C) := by
    rw [← Nat.gcd_eq_gcd_ab]
  rw [h.gcd_eq_one] at hb
  push_cast at hb
  have h1 : ‖(p : C) * ((Nat.gcdA p m : ℤ) : C)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one C _)) hp
  have h2 : ‖(m : C) * ((Nat.gcdB p m : ℤ) : C)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one C _)) hlt
  have h3 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  rw [← hb, norm_one] at h3
  exact lt_irrefl _ h3
end GlobalTheory.NearlyPrimitive
