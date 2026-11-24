-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolPQ.lintegral_one_add_inv_pow_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:19:00.582272+00:00
-- url     : https://prove2.me/submissions/c7c8d109-8fa3-408b-a2f6-9e950749ae34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_OneAddHsInvPowLintegralLtTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset PI.UpqRep
open scoped InnerProductSpace ENNReal ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolPQ
namespace GlobalTheory.CompanionTheory.HolPQ
theorem _root_.solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (h : X → ℝ) (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) (d : ℕ) (C : ℝ)
    (hC : ∀ k : ℕ, μ {x | h x ≤ (4 : ℝ) ^ k} ≤ ENNReal.ofReal (C * ((4 : ℝ) ^ k) ^ d))
    (s : ℕ) (hs' : d + 1 ≤ s) :
    ∫⁻ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ∂μ < ⊤ := by
  set c : ℕ → ℝ := fun k => (4 : ℝ) ^ s * (((4 : ℝ) ^ k)⁻¹) ^ s with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by simp only [hc]; positivity
  set A : ℕ → Set X := fun k => {x | h x ≤ (4 : ℝ) ^ k} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k => measurableSet_le hm measurable_const
  have point : ∀ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ≤
      ∑' k, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x := by
    intro x
    have hex : ∃ k : ℕ, h x ≤ (4 : ℝ) ^ k := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (h x) (by norm_num : (1 : ℝ) < 4)
      exact ⟨k, hk.le⟩
    classical
    set k := Nat.find hex with hk
    have hxk : x ∈ A k := Nat.find_spec hex
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [Set.indicator_of_mem hxk]
    apply ENNReal.ofReal_le_ofReal
    have h4 : (4 : ℝ) ^ k ≤ 4 * (1 + h x) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0]; have := h0 x; norm_num; linarith
      · have hmin : ¬ h x ≤ (4 : ℝ) ^ (k - 1) := Nat.find_min hex (by omega)
        have e : (4 : ℝ) ^ k = 4 * 4 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [e]; push Not at hmin; linarith
    have hpos : 0 < 1 + h x := by have := h0 x; linarith
    have h5 : (1 + h x)⁻¹ ≤ 4 * ((4 : ℝ) ^ k)⁻¹ := by
      rw [inv_le_comm₀ hpos (by positivity), mul_inv, inv_inv]
      have : (0 : ℝ) < 4 ^ k := by positivity
      nlinarith
    calc ((1 + h x)⁻¹) ^ s ≤ (4 * ((4 : ℝ) ^ k)⁻¹) ^ s :=
          pow_le_pow_left₀ (by positivity) h5 s
      _ = c k := by simp only [hc]; rw [mul_pow]
  set C' : ℝ := max C 0 with hC'
  have hterm : ∀ k, ENNReal.ofReal (c k) * μ (A k) ≤
      ENNReal.ofReal ((4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k) := by
    intro k
    have h1 : μ (A k) ≤ ENNReal.ofReal (C' * ((4 : ℝ) ^ k) ^ d) :=
      (hC k).trans (ENNReal.ofReal_le_ofReal (by
        gcongr; exact le_max_left _ _))
    calc ENNReal.ofReal (c k) * μ (A k)
        ≤ ENNReal.ofReal (c k) * ENNReal.ofReal (C' * ((4 : ℝ) ^ k) ^ d) := by gcongr
      _ = ENNReal.ofReal (c k * (C' * ((4 : ℝ) ^ k) ^ d)) :=
          (ENNReal.ofReal_mul (hc0 k)).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hC0 : 0 ≤ C' := le_max_right _ _
          have hq : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
          have key : (((4 : ℝ) ^ k)⁻¹) ^ s * ((4 : ℝ) ^ k) ^ d ≤ ((4 : ℝ)⁻¹) ^ k := by
            obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs'
            have e : (((4 : ℝ) ^ k)⁻¹) ^ (d + 1 + t) * ((4 : ℝ) ^ k) ^ d =
                ((4 : ℝ) ^ k)⁻¹ * (((4 : ℝ) ^ k)⁻¹) ^ t := by
              have : ((4 : ℝ) ^ k) ≠ 0 := by positivity
              rw [pow_add, pow_succ, inv_pow]
              field_simp
            have h7 : ((4 : ℝ)⁻¹) ^ k = ((4 : ℝ) ^ k)⁻¹ := inv_pow _ _
            have h8 : (((4 : ℝ) ^ k)⁻¹) ^ t ≤ 1 :=
              pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hq)
            have h6 : (0 : ℝ) < ((4 : ℝ) ^ k)⁻¹ := by positivity
            rw [e, h7]
            exact mul_le_of_le_one_right h6.le h8
          simp only [hc]
          calc (4 : ℝ) ^ s * (((4 : ℝ) ^ k)⁻¹) ^ s * (C' * ((4 : ℝ) ^ k) ^ d)
              = (4 : ℝ) ^ s * C' * ((((4 : ℝ) ^ k)⁻¹) ^ s * ((4 : ℝ) ^ k) ^ d) := by ring
            _ ≤ _ := by gcongr
  have hsum : Summable fun k : ℕ => (4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∫⁻ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ∂μ
      ≤ ∫⁻ x, ∑' k, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x ∂μ :=
        lintegral_mono point
    _ = ∑' k, ∫⁻ x, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x ∂μ :=
        lintegral_tsum fun k => (measurable_const.indicator (hAm k)).aemeasurable
    _ = ∑' k, ENNReal.ofReal (c k) * μ (A k) := by
        congr 1; funext k
        rw [lintegral_indicator (hAm k), setLIntegral_const]
    _ ≤ ∑' k, ENNReal.ofReal ((4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k) :=
        ENNReal.tsum_le_tsum hterm
    _ < ⊤ := hsum.tsum_ofReal_lt_top
end GlobalTheory.CompanionTheory.HolPQ
