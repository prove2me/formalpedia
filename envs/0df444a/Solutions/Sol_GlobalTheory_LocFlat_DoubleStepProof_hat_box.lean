-- Prove2me | solution 1 for GlobalTheory.LocFlat.DoubleStepProof.hat_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:29.5828+00:00
-- url     : https://prove2.me/submissions/d5047fdb-a254-4fb3-b0a0-c5be0c7b6f37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_vol_box_pos
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_integral_box
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.DoubleStepProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace k] [BorelSpace k]
open Classical
namespace GlobalTheory.LocFlat.DoubleStepProof
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (c : kˣ) :
    ∃ V : ℝ, 0 < V ∧ ∀ u, hat ψ ν (-1) (fun y : n → k => if y ∈ box n c⁻¹ then (1 : ℂ) else 0) u =
      (V : ℂ) * (if u ∈ box n c then 1 else 0) := by
  have := secondCountable k
  have hc0 : valuation k (c : k) ≠ 0 := (Valuation.ne_zero_iff _).2 c.ne_zero
  refine ⟨_, vol_box_pos (n := n) ν c⁻¹, fun u => ?_⟩
  by_cases hu : u ∈ box n c
  · rw [if_pos hu, mul_one, ← integral_box (n := n) ν c⁻¹]
    unfold hat
    congr 1
    funext y
    dsimp only
    by_cases hy : y ∈ box n c⁻¹
    · rw [if_pos hy, one_mul]
      have hm : (-1 : k) * (u ⬝ᵥ y) ∈ cball (1 : kˣ) := by
        show valuation k _ ≤ valuation k ((1 : kˣ) : k)
        rw [map_mul, Valuation.map_neg, map_one, one_mul, Units.val_one, map_one]
        refine Valuation.map_sum_le _ fun i _ => ?_
        rw [map_mul]
        calc valuation k (u i) * valuation k (y i) ≤ valuation k (c : k) * valuation k ((c⁻¹ : kˣ) : k) :=
              mul_le_mul' (hu i) (hy i)
          _ = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ hc0]
      rw [hψ.eq_one hm]; simp
    · rw [if_neg hy, zero_mul]
  · rw [if_neg hu, mul_zero]
    obtain ⟨i, hi⟩ : ∃ i, valuation k (c : k) < valuation k (u i) := by
      by_contra hcon; push_neg at hcon; exact hu (mem_box.2 hcon)
    have hui : u i ≠ 0 := by rintro h0; simp [h0] at hi
    have hv0 : valuation k (u i) ≠ 0 := (Valuation.ne_zero_iff _).2 hui
    set x := u i * ((c⁻¹ : kˣ) : k) with hxdef
    have hx : ¬ valuation k x ≤ valuation k ((1 : kˣ) : k) := by
      intro hle
      rw [hxdef, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_one, map_one] at hle
      have : valuation k (u i) ≤ valuation k (c : k) := by
        have h2 := mul_le_mul' hle (le_refl (valuation k (c : k)))
        rwa [one_mul, mul_assoc, inv_mul_cancel₀ hc0, mul_one] at h2
      exact (not_le.2 hi) this
    obtain ⟨y, hy1, hy2⟩ : ∃ y, valuation k y ≤ valuation k x ∧ ψ y ≠ 1 := by
      by_contra hcon; push_neg at hcon; exact hx ((hψ x).1 hcon)
    set y₀ : n → k := Pi.single i (-(y / u i)) with hy₀def
    have hy₀ : y₀ ∈ box n c⁻¹ := by
      intro l
      by_cases hl : l = i
      · subst hl
        simp only [hy₀def, Pi.single_eq_same, map_neg, map_div₀]
        rw [Units.val_inv_eq_inv_val, map_inv₀]
        rw [hxdef, map_mul, Units.val_inv_eq_inv_val, map_inv₀] at hy1
        have h2 := mul_le_mul' hy1 (le_refl (valuation k (u l))⁻¹)
        rw [mul_comm (valuation k (u l)) _, mul_assoc, mul_inv_cancel₀ hv0, mul_one, ← div_eq_mul_inv] at h2
        rw [Valuation.map_neg, Valuation.map_div]; exact h2
      · simp [hy₀def, hl]
    have hχ : (-1 : k) * (u ⬝ᵥ y₀) = y := by
      rw [hy₀def, dotProduct_single]; field_simp
    set F : (n → k) → ℂ := fun y => (if y ∈ box n c⁻¹ then (1 : ℂ) else 0) * (ψ ((-1 : k) * (u ⬝ᵥ y)) : ℂ) with hF
    have hFt : ∀ z, F (y₀ + z) = (ψ y : ℂ) * F z := by
      intro z
      simp only [hF]
      rw [if_congr ((box n c⁻¹).add_mem_iff_right hy₀) rfl rfl, dotProduct_add, mul_add, AddChar.map_add_eq_mul,
        hχ, Circle.coe_mul]
      ring
    have hI := integral_add_left_eq_self (μ := Measure.pi fun _ : n => ν) F y₀
    simp_rw [hFt] at hI
    rw [integral_const_mul] at hI
    have hne : (ψ y : ℂ) ≠ 1 := fun h => hy2 (Circle.coe_inj.1 (by simpa using h))
    show ∫ z, F z ∂(Measure.pi fun _ : n => ν) = 0
    have h3 : ((ψ y : ℂ) - 1) * ∫ z, F z ∂(Measure.pi fun _ : n => ν) = 0 := by rw [sub_mul, hI]; ring
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
end GlobalTheory.LocFlat.DoubleStepProof
