-- Prove2me | solution 1 for IntermediateField.exists_uniformiser_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c5777e8a-0cc4-5ac7-b255-02649fcc9e45

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_uniformiser_padic

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField
open ExtCitation.LocalLevel
open ExtCitation.LocalLevel

theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] :
    ∃ π : K, 0 < ‖(π : PadicAlgCl q)‖ ∧ ‖(π : PadicAlgCl q)‖ < 1 ∧
      ∀ y : K, y ≠ 0 → ∃ i : ℤ, ‖(y : PadicAlgCl q)‖ = ‖(π : PadicAlgCl q)‖ ^ i := by
  classical
  haveI hDVR : IsDiscreteValuationRing (Rw q K) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q K
  have hmem : ∀ x : K, x ∈ Rw q K ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := fun x => by
    change ((x : PadicAlgCl q)) ∈ padicIntegers q ↔ _
    rw [mem_padicIntegers_iff]
    rfl
  have hcoe : ∀ r s : Rw q K, (((r * s : Rw q K) : K) : PadicAlgCl q) = ((r : K) : PadicAlgCl q) * ((s : K) : PadicAlgCl q) :=
    fun _ _ => rfl
  have hcoepow : ∀ (r : Rw q K) (n : ℕ), (((r ^ n : Rw q K) : K) : PadicAlgCl q) = (((r : K) : PadicAlgCl q)) ^ n := by
    intro r n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, hcoe, ih, pow_succ]

  have hunit : ∀ u : (Rw q K)ˣ, ‖(((u : Rw q K) : K) : PadicAlgCl q)‖ = 1 := fun u => by
    have ha : ‖(((u : Rw q K) : K) : PadicAlgCl q)‖ ≤ 1 := (hmem _).1 (u : Rw q K).2
    have hb : ‖((((u⁻¹ : (Rw q K)ˣ) : Rw q K) : K) : PadicAlgCl q)‖ ≤ 1 := (hmem _).1 ((u⁻¹ : (Rw q K)ˣ) : Rw q K).2
    have hmul : ‖(((u : Rw q K) : K) : PadicAlgCl q)‖ * ‖((((u⁻¹ : (Rw q K)ˣ) : Rw q K) : K) : PadicAlgCl q)‖ = 1 := by
      rw [← norm_mul, ← hcoe, u.mul_inv]
      exact norm_one
    apply le_antisymm ha
    calc (1 : ℝ) = _ := hmul.symm
      _ ≤ ‖(((u : Rw q K) : K) : PadicAlgCl q)‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := mul_one _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rw q K)
  have hϖ1 : ‖(((ϖ : Rw q K) : K) : PadicAlgCl q)‖ ≤ 1 := (hmem _).1 ϖ.2
  have hπ0 : ((ϖ : K) : PadicAlgCl q) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext (Subtype.ext h))
  have hπlt : ‖(((ϖ : Rw q K) : K) : PadicAlgCl q)‖ < 1 := by
    refine lt_of_le_of_ne hϖ1 fun heq => hϖ.not_isUnit ?_
    have hinv : ((ϖ : K)⁻¹) ∈ Rw q K := by
      rw [hmem]
      change ‖(((ϖ : K) : PadicAlgCl q))⁻¹‖ ≤ 1
      rw [norm_inv, heq, inv_one]
    refine ⟨⟨ϖ, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ?_), Subtype.ext (inv_mul_cancel₀ ?_)⟩, rfl⟩ <;>
      exact fun h => hπ0 (by rw [h]; rfl)
  refine ⟨(ϖ : K), norm_pos_iff.2 hπ0, hπlt, fun y hy => ?_⟩

  have hdec : ∀ z : K, z ≠ 0 → ‖(z : PadicAlgCl q)‖ ≤ 1 →
      ∃ n : ℕ, ‖(z : PadicAlgCl q)‖ = ‖(((ϖ : Rw q K) : K) : PadicAlgCl q)‖ ^ n := by
    intro z hz hz1
    have hr : (⟨z, (hmem z).2 hz1⟩ : Rw q K) ≠ 0 := fun h => hz (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    refine ⟨n, ?_⟩
    have := congrArg (fun r : Rw q K => ‖((r : K) : PadicAlgCl q)‖) hu
    simp only [hcoe, hcoepow, norm_mul, norm_pow, hunit, one_mul] at this
    exact this
  by_cases hy1 : ‖(y : PadicAlgCl q)‖ ≤ 1
  · obtain ⟨n, hn⟩ := hdec y hy hy1
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  · have hy0 : ((y : K) : PadicAlgCl q) ≠ 0 := fun h => hy (Subtype.ext h)
    have hyi : ‖((y⁻¹ : K) : PadicAlgCl q)‖ ≤ 1 := by
      change ‖((y : PadicAlgCl q))⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hy1))
    obtain ⟨n, hn⟩ := hdec y⁻¹ (inv_ne_zero hy) hyi
    refine ⟨-(n : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← hn]
    change _ = ‖((y : PadicAlgCl q))⁻¹‖⁻¹
    rw [norm_inv, inv_inv]

end S_IntermediateField_exists_uniformiser_padic
end P2MW
export P2MW.S_IntermediateField_exists_uniformiser_padic (solution)
