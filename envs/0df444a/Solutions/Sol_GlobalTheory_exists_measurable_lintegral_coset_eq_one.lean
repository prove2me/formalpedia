-- Prove2me | solution 1 for GlobalTheory.exists_measurable_lintegral_coset_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:18.970658+00:00
-- url     : https://prove2.me/submissions/d2361edc-1130-4d3b-9ef6-7550bc8d3c19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMeasurableLintegralCosetEqOneClosedSubgrou

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open MeasureTheory
open scoped ENNReal
open scoped Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution
    (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  let K := CompactExhaustion.choice G
  set a : ℕ → ℝ≥0∞ := fun n => ν (j ⁻¹' (K n * (K n)⁻¹)) with ha_def
  have ha : ∀ n, a n ≠ ∞ := fun n =>
    (hj.isCompact_preimage ((K.isCompact n).mul (K.isCompact n).inv)).measure_lt_top.ne
  set c : ℕ → ℝ≥0∞ := fun n => (2⁻¹ : ℝ≥0∞) ^ n / (a n + 1) with hc_def
  have hc_pos : ∀ n, c n ≠ 0 := fun n =>
    (ENNReal.div_pos (pow_ne_zero _ (by simp)) (by simp [ha n])).ne'
  have hc_le : ∀ n, c n ≤ 2⁻¹ ^ n := fun n =>
    ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' le_add_self)
  have hca : ∀ n, c n * a n ≤ 2⁻¹ ^ n := fun n => by
    calc c n * a n ≤ c n * (a n + 1) := by gcongr; exact le_self_add
      _ = 2⁻¹ ^ n := ENNReal.div_mul_cancel (by simp) (by simp [ha n])
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (K.isCompact n).isClosed.measurableSet
  set f : G → ℝ≥0∞ := fun y => ∑' n, (K n).indicator (fun _ => c n) y with hf_def
  have hf : Measurable f := Measurable.ennreal_tsum fun n => measurable_const.indicator (hKm n)
  have hf_pos : ∀ y, f y ≠ 0 := by
    intro y
    obtain ⟨n, hn⟩ := K.exists_mem y
    refine ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (hc_pos n)) ?_)
    calc c n = (K n).indicator (fun _ => c n) y := (Set.indicator_of_mem hn (fun _ => c n)).symm
      _ ≤ f y := ENNReal.le_tsum n
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  have hmeas : ∀ g, Measurable fun h => f (j h * g) := fun g => hf.comp (hjg g)
  set F : G → ℝ≥0∞ := fun g => ∫⁻ h, f (j h * g) ∂ν with hF_def
  have hF : Measurable F :=
    Measurable.lintegral_prod_right' (ν := ν) (f := fun p : G × H => f (j p.2 * p.1))
      (hf.comp ((hj.continuous.measurable.comp measurable_snd).mul measurable_fst))
  have hF_inv : ∀ h' g, F (j h' * g) = F g := by
    intro h' g
    have e : ∀ h, f (j h * (j h' * g)) = (fun k => f (j k * g)) (h * h') := by
      intro h; simp only [map_mul, mul_assoc]
    calc F (j h' * g) = ∫⁻ h, (fun k => f (j k * g)) (h * h') ∂ν := lintegral_congr e
      _ = F g := lintegral_mul_right_eq_self (μ := ν) (fun k => f (j k * g)) h'
  have hF0 : ∀ g, F g ≠ 0 := by
    intro g h0
    rw [hF_def, lintegral_eq_zero_iff (hmeas g), Filter.EventuallyEq, ae_iff] at h0
    have : ν Set.univ = 0 := by simpa [hf_pos] using h0
    exact NeZero.ne ν (Measure.measure_univ_eq_zero.1 this)
  have hFtop : ∀ g, F g ≠ ∞ := by
    intro g
    obtain ⟨m, hm⟩ := K.exists_mem g
    have hterm : ∀ n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
        ≤ (1 + a m) * 2⁻¹ ^ n := by
      intro n
      have hsub : (fun h => j h * g) ⁻¹' K n ⊆ j ⁻¹' (K (max n m) * (K (max n m))⁻¹) := by
        intro h hh
        have h1 : j h * g ∈ K (max n m) := K.subset (le_max_left n m) hh
        have h2 : g ∈ K (max n m) := K.subset (le_max_right n m) hm
        have e : j h = (j h * g) * g⁻¹ := by group
        rw [Set.mem_preimage, e]
        exact Set.mul_mem_mul h1 (Set.inv_mem_inv.2 h2)
      have hle : ν ((fun h => j h * g) ⁻¹' K n) ≤ a n + a m := by
        refine (measure_mono hsub).trans ?_
        rcases le_total n m with hnm | hnm
        · rw [max_eq_right hnm]; exact le_add_self
        · rw [max_eq_left hnm]; exact le_self_add
      calc ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
          = ∫⁻ h, ((fun h => j h * g) ⁻¹' K n).indicator (fun _ => c n) h ∂ν := rfl
        _ = c n * ν ((fun h => j h * g) ⁻¹' K n) :=
            lintegral_indicator_const (hjg g (hKm n)) _
        _ ≤ c n * (a n + a m) := by gcongr
        _ = c n * a n + c n * a m := mul_add _ _ _
        _ ≤ 2⁻¹ ^ n + 2⁻¹ ^ n * a m := by gcongr; exacts [hca n, hc_le n]
        _ = (1 + a m) * 2⁻¹ ^ n := by ring
    have hF_eq : F g = ∑' n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν :=
      lintegral_tsum fun n =>
        ((measurable_const.indicator (hKm n)).comp (hjg g)).aemeasurable
    rw [hF_eq]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (by simp [ha m]) (by simp)
  refine ⟨fun g => f g * (F g)⁻¹, hf.mul hF.inv, fun g => ?_⟩
  simp only [hF_inv]
  rw [lintegral_mul_const _ (hmeas g)]
  exact ENNReal.mul_inv_cancel (hF0 g) (hFtop g)
end _root_.GlobalTheory
end GlobalTheory
