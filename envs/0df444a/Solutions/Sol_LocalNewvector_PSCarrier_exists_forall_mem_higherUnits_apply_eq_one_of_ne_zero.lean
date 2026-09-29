-- Prove2me | solution 1 for LocalNewvector.PSCarrier.exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ed0d9a2f-5c5b-5fb9-a7ea-39dc0f262b07

import Mathlib
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero

set_option autoImplicit false

open LocalNewvector Topology

namespace PSCharCont

variable (p : ℕ) [Fact p.Prime]

theorem continuous_borelElem_left (g₀ : GL (Fin 2) ℚ_[p]) :
    Continuous fun u : ℚ_[p]ˣ => borelElem p u 1 0 * g₀ := by
  refine Continuous.mul ?_ continuous_const
  rw [Units.continuous_iff]
  constructor
  ·
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [coe_borelElem] <;> fun_prop
  · have hinv : Continuous fun u : ℚ_[p]ˣ => ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) := Units.continuous_coe_inv
    have hinv' : Continuous fun u : ℚ_[p]ˣ => ((u : ℚ_[p]ˣ) : ℚ_[p])⁻¹ := by
      simpa only [Units.val_inv_eq_inv_val] using hinv
    refine continuous_matrix fun i j => ?_
    simp only [borelElem_inv, coe_borelElem]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_borelElem_right (g₀ : GL (Fin 2) ℚ_[p]) :
    Continuous fun u : ℚ_[p]ˣ => borelElem p 1 u 0 * g₀ := by
  refine Continuous.mul ?_ continuous_const
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [coe_borelElem] <;> fun_prop
  · have hinv : Continuous fun u : ℚ_[p]ˣ => ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) := Units.continuous_coe_inv
    have hinv' : Continuous fun u : ℚ_[p]ˣ => ((u : ℚ_[p]ˣ) : ℚ_[p])⁻¹ := by
      simpa only [Units.val_inv_eq_inv_val] using hinv
    refine continuous_matrix fun i j => ?_
    simp only [borelElem_inv, coe_borelElem]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem exists_higherUnits_subset {V : Set ℚ_[p]ˣ} (hV : V ∈ 𝓝 (1 : ℚ_[p]ˣ)) :
    ∃ c : ℕ, higherUnits p c ⊆ V := by
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  rw [Units.val_one, Metric.mem_nhds_iff] at hW
  obtain ⟨ε, hε, hball⟩ := hW
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨k + 1, fun u hu => hWV ?_⟩
  obtain ⟨-, hu2⟩ := (mem_higherUnits_iff p).mp hu
  rcases hu2 with h0 | hle
  · omega
  · apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le
    calc ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := hle
      _ ≤ (p : ℝ) ^ (-(k : ℤ)) := zpow_le_zpow_right₀ hp1 (by push_cast; omega)
      _ < ε := hk

end PSCharCont

open PSCharCont in
theorem solution
    (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (F : LocalNewvector.PSCarrier p μ₁ μ₂)
    (hF : F ≠ 0) :
    ∃ c : ℕ, ∀ u ∈ LocalNewvector.higherUnits p c, μ₁ u = 1 ∧ μ₂ u = 1 := by
  classical
  set F₀ : GL (Fin 2) ℚ_[p] → ℂ := PSCarrier.toFn p μ₁ μ₂ F with hF₀
  have hmem : F₀ ∈ principalSeries p μ₁ μ₂ := PSCarrier.toFn_mem p μ₁ μ₂ F
  have hlc : IsLocallyConstant F₀ := isLocallyConstant_of_mem_principalSeries p hmem

  obtain ⟨g₀, hg₀⟩ : ∃ g₀, F₀ g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hF (PSCarrier.ext p μ₁ μ₂ (fun y => by rw [← hF₀, h y]; rfl))

  set U : Set (GL (Fin 2) ℚ_[p]) := F₀ ⁻¹' {F₀ g₀} with hU
  have hUopen : IsOpen U := hlc.isOpen_fiber _
  have hg₀U : g₀ ∈ U := rfl

  have hV₁ : (fun u : ℚ_[p]ˣ => borelElem p u 1 0 * g₀) ⁻¹' U ∈ 𝓝 (1 : ℚ_[p]ˣ) := by
    refine (hUopen.preimage (continuous_borelElem_left p g₀)).mem_nhds ?_
    show borelElem p 1 1 0 * g₀ ∈ U
    rw [borelElem_one, one_mul]
    exact hg₀U
  have hV₂ : (fun u : ℚ_[p]ˣ => borelElem p 1 u 0 * g₀) ⁻¹' U ∈ 𝓝 (1 : ℚ_[p]ˣ) := by
    refine (hUopen.preimage (continuous_borelElem_right p g₀)).mem_nhds ?_
    show borelElem p 1 1 0 * g₀ ∈ U
    rw [borelElem_one, one_mul]
    exact hg₀U
  obtain ⟨c₁, hc₁⟩ := exists_higherUnits_subset p hV₁
  obtain ⟨c₂, hc₂⟩ := exists_higherUnits_subset p hV₂
  refine ⟨max c₁ c₂, fun u hu => ?_⟩
  have hu1 : u ∈ higherUnits p c₁ := higherUnits_antitone p (le_max_left _ _) hu
  have hu2 : u ∈ higherUnits p c₂ := higherUnits_antitone p (le_max_right _ _) hu
  have hunorm : ‖(u : ℚ_[p])‖ = 1 := ((mem_higherUnits_iff p).mp hu).1
  have hhalf₁ : halfModulus p u 1 = 1 := halfModulus_eq_one_of_norm_eq_one p hunorm (by simp)
  have hhalf₂ : halfModulus p 1 u = 1 := halfModulus_eq_one_of_norm_eq_one p (by simp) hunorm
  constructor
  · have h1 : F₀ (borelElem p u 1 0 * g₀) = F₀ g₀ := hc₁ hu1
    rw [apply_borelElem_mul_of_mem_principalSeries p hmem, hhalf₁, map_one, Units.val_one, mul_one,
      mul_one] at h1

    have h2 : ((μ₁ u : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hg₀ (h1.trans (one_mul _).symm)
      exact this
    exact Units.ext h2
  · have h1 : F₀ (borelElem p 1 u 0 * g₀) = F₀ g₀ := hc₂ hu2
    rw [apply_borelElem_mul_of_mem_principalSeries p hmem, hhalf₂, map_one, Units.val_one, one_mul,
      mul_one] at h1
    have h2 : ((μ₂ u : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hg₀ (h1.trans (one_mul _).symm)
      exact this
    exact Units.ext h2

end S_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero
end P2MW
export P2MW.S_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero (solution)
