-- Prove2me | solution 1 for GlobalTheory.exists_pos_finite_density_of_almost_translation_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:54.287672+00:00
-- url     : https://prove2.me/submissions/64ff838f-dda5-4817-afc8-e9d5fc290471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsPosFiniteDensityOfAlmostTranslationInvaria
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Filter Topology Metric Set
namespace GlobalTheory
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end
open MeasureTheory Filter Topology Metric Set in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem measurableSet_pairs_mem_ball_mem_ball (ρ s : ℝ) :
    MeasurableSet {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s} :=
  ((isOpen_ball.preimage continuous_fst).inter
    (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const)).measurableSet
open MeasureTheory Filter Topology Metric Set in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem measure_ball_mul_le_mul_of_forall_le_measure_ball (lam ν : Measure V) [lam.IsAddHaarMeasure]
    [IsFiniteMeasure ν] {ρ s : ℝ} {a : ENNReal} (ha : ∀ x ∈ ball (0 : V) ρ, a ≤ ν (ball x s)) :
    lam (ball 0 ρ) * a ≤ lam (ball 0 s) * ν (ball 0 (ρ + s)) := by
  have hS := measurableSet_pairs_mem_ball_mem_ball (V := V) ρ s
  calc lam (ball 0 ρ) * a = ∫⁻ x, (ball (0 : V) ρ).indicator (fun _ => a) x ∂lam := by
        rw [lintegral_indicator_const measurableSet_ball, mul_comm]
    _ ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s}) ∂lam :=
        lintegral_mono fun x => by
          by_cases hx : x ∈ ball (0 : V) ρ
          · rw [indicator_of_mem hx]
            exact (ha x hx).trans (measure_mono fun y hy => (⟨hx, hy⟩ : x ∈ ball (0 : V) ρ ∧ y ∈ ball x s))
          · rw [indicator_of_notMem hx]
            exact zero_le
    _ = lam.prod ν {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s} :=
        (Measure.prod_apply hS).symm
    _ = ∫⁻ y, lam ((fun x => (x, y)) ⁻¹' {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s}) ∂ν :=
        Measure.prod_apply_symm hS
    _ ≤ ∫⁻ y, (ball (0 : V) (ρ + s)).indicator (fun _ => lam (ball 0 s)) y ∂ν :=
        lintegral_mono fun y => by
          by_cases hy : y ∈ ball (0 : V) (ρ + s)
          · rw [indicator_of_mem hy, ← Measure.addHaar_ball_center lam y s]
            refine measure_mono fun x hx => ?_
            have hxy : dist y x < s := hx.2
            show dist x y < s
            rwa [dist_comm]
          · rw [indicator_of_notMem hy]
            have hempty : (fun x => (x, y)) ⁻¹'
                {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s} = ∅ := by
              refine eq_empty_of_forall_notMem fun x hx => hy ?_
              have h1 : dist x 0 < ρ := hx.1
              have h2 : dist y x < s := hx.2
              show dist y 0 < ρ + s
              linarith [dist_triangle y x 0]
            rw [hempty, measure_empty]
    _ = lam (ball 0 s) * ν (ball 0 (ρ + s)) := lintegral_indicator_const measurableSet_ball _
open MeasureTheory Filter Topology Metric Set in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem measure_ball_mul_le_mul_of_forall_measure_ball_le (lam ν : Measure V) [lam.IsAddHaarMeasure]
    [IsFiniteMeasure ν] {ρ s : ℝ} {b : ENNReal} (hb : ∀ x ∈ ball (0 : V) ρ, ν (ball x s) ≤ b) :
    lam (ball 0 s) * ν (ball 0 (ρ - s)) ≤ lam (ball 0 ρ) * b := by
  have hS := measurableSet_pairs_mem_ball_mem_ball (V := V) ρ s
  calc lam (ball 0 s) * ν (ball 0 (ρ - s))
        = ∫⁻ y, (ball (0 : V) (ρ - s)).indicator (fun _ => lam (ball 0 s)) y ∂ν :=
          (lintegral_indicator_const measurableSet_ball _).symm
    _ ≤ ∫⁻ y, lam ((fun x => (x, y)) ⁻¹' {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s}) ∂ν :=
        lintegral_mono fun y => by
          by_cases hy : y ∈ ball (0 : V) (ρ - s)
          · rw [indicator_of_mem hy, ← Measure.addHaar_ball_center lam y s]
            refine measure_mono fun x hx => ?_
            have h1 : dist x y < s := hx
            have h2 : dist y 0 < ρ - s := hy
            have h3 : dist x 0 < ρ := by linarith [dist_triangle x y 0]
            have h4 : dist y x < s := by rwa [dist_comm]
            exact (⟨h3, h4⟩ : x ∈ ball (0 : V) ρ ∧ y ∈ ball x s)
          · rw [indicator_of_notMem hy]
            exact zero_le
    _ = lam.prod ν {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s} :=
        (Measure.prod_apply_symm hS).symm
    _ = ∫⁻ x, ν (Prod.mk x ⁻¹' {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s}) ∂lam :=
        Measure.prod_apply hS
    _ ≤ ∫⁻ x, (ball (0 : V) ρ).indicator (fun _ => b) x ∂lam :=
        lintegral_mono fun x => by
          by_cases hx : x ∈ ball (0 : V) ρ
          · rw [indicator_of_mem hx]
            exact (measure_mono fun y hy => hy.2).trans (hb x hx)
          · rw [indicator_of_notMem hx]
            have hempty : Prod.mk x ⁻¹'
                {p : V × V | p.1 ∈ ball (0 : V) ρ ∧ p.2 ∈ ball p.1 s} = ∅ :=
              eq_empty_of_forall_notMem fun y hy => hx hy.1
            rw [hempty, measure_empty]
    _ = lam (ball 0 ρ) * b := by rw [lintegral_indicator_const measurableSet_ball, mul_comm]
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory Filter Topology Metric Set
open GlobalTheory
open MeasureTheory Filter Topology Metric Set
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (lam ν : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure ν], (∀ r : ℝ, 0 < r → ν (ball 0 r) ≠ 0) → (∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball (0 : V) δ, ∀ r ∈ Ioo (0 : ℝ) δ, ν (ball 0 r) ≤ ν (ball x (κ * r)) ∧ ν (ball x r) ≤ ν (ball 0 (κ * r))) → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ Tendsto (fun r : ℝ => ν (ball 0 r) / lam (ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  intro V _ _ _ _ _ lam ν _ _ hpos hinv
  obtain ⟨d, hd⟩ : ∃ d, d = Module.finrank ℝ V := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ → ℝ, ∀ r, M r = (ν (ball 0 r)).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ, ∀ r, L r = (lam (ball 0 r)).toReal := ⟨_, fun _ => rfl⟩
  have hc₁ : 0 < L 1 := by
    rw [hL]
    exact ENNReal.toReal_pos (measure_ball_pos lam 0 one_pos).ne' measure_ball_lt_top.ne
  have hLr : ∀ r, 0 < r → L r = r ^ d * L 1 := fun r hr => by
    rw [hL r, hL 1, Measure.addHaar_ball_of_pos lam 0 hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hd]
  have hMpos : ∀ r, 0 < r → 0 < M r := fun r hr => by
    rw [hM]
    exact ENNReal.toReal_pos (hpos r hr) (measure_ne_top ν _)
  have hLpos : ∀ r, 0 < r → 0 < L r := fun r hr => by
    rw [hLr r hr]
    exact mul_pos (pow_pos hr d) hc₁
  have hMmono : ∀ r r', r ≤ r' → M r ≤ M r' := fun r r' h => by
    rw [hM, hM]
    exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (ball_subset_ball h))
  have hUp : ∀ ρ s r, (∀ x ∈ ball (0 : V) ρ, ν (ball 0 r) ≤ ν (ball x s)) →
      L ρ * M r ≤ L s * M (ρ + s) := fun ρ s r h => by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top measure_ball_lt_top.ne (measure_ne_top ν _))
      (measure_ball_mul_le_mul_of_forall_le_measure_ball lam ν h)
    simpa only [ENNReal.toReal_mul, ← hL, ← hM] using this
  have hDown : ∀ ρ s b, (∀ x ∈ ball (0 : V) ρ, ν (ball x s) ≤ ν (ball 0 b)) →
      L s * M (ρ - s) ≤ L ρ * M b := fun ρ s b h => by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top measure_ball_lt_top.ne (measure_ne_top ν _))
      (measure_ball_mul_le_mul_of_forall_measure_ball_le lam ν h)
    simpa only [ENNReal.toReal_mul, ← hL, ← hM] using this
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ r, g r = M r / L r := ⟨_, fun _ => rfl⟩
  have hgpos : ∀ r, 0 < r → 0 < g r := fun r hr => by
    rw [hg]
    exact div_pos (hMpos r hr) (hLpos r hr)
  have hkey : ∀ ε, 0 < ε → ∃ t, 0 < t ∧ ∀ u ∈ Ioo 0 t, ∀ v ∈ Ioo 0 t, g u ≤ (1 + ε) * g v := by
    intro ε hε
    have hF : Tendsto (fun η : ℝ => ((1 + η) ^ d) ^ 3 / (1 - η) ^ d) (𝓝 0) (𝓝 1) := by
      have : ContinuousAt (fun η : ℝ => ((1 + η) ^ d) ^ 3 / (1 - η) ^ d) 0 :=
        (((continuous_const.add continuous_id).pow d).pow 3).continuousAt.div
          ((continuous_const.sub continuous_id).pow d).continuousAt (by simp)
      simpa using this.tendsto
    obtain ⟨η, hFη, hη⟩ := (((hF.mono_left nhdsWithin_le_nhds).eventually_lt_const
      (by linarith : (1 : ℝ) < 1 + ε)).and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))).exists
    obtain ⟨hη0, hη1⟩ := hη
    obtain ⟨δ, hδ, hδ'⟩ := hinv (1 + η) (by linarith)
    have hρ0 : 0 < δ / 2 := by linarith
    have hηρ0 : 0 < η * (δ / 2) := mul_pos hη0 hρ0
    have hηρ : η * (δ / 2) < δ / 2 := by nlinarith
    refine ⟨η * (δ / 2) / (1 + η), div_pos hηρ0 (by linarith), fun u hu v hv => ?_⟩
    have hu0 := hu.1
    have hv0 := hv.1
    have hku : (1 + η) * u < η * (δ / 2) := by
      have := (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + η)).1 hu.2
      linarith
    have hkv : (1 + η) * v < η * (δ / 2) := by
      have := (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + η)).1 hv.2
      linarith
    have hηu : 0 < η * u := mul_pos hη0 hu0
    have huδ : u < δ := by linarith

    have hU := hUp ((1 - η) * (δ / 2)) ((1 + η) * u) u fun x hx =>
      (hδ' x (ball_subset_ball (by linarith) hx) u ⟨hu0, huδ⟩).1
    have hU2 : L ((1 - η) * (δ / 2)) * M u ≤ L ((1 + η) * u) * M (δ / 2) :=
      hU.trans (mul_le_mul_of_nonneg_left (hMmono _ _ (by linarith))
        (hLpos _ (mul_pos (by linarith) hu0)).le)
    rw [hLr _ (mul_pos (by linarith) hρ0), hLr _ (mul_pos (by linarith) hu0), mul_pow,
      mul_pow] at hU2

    obtain ⟨w, hw⟩ : ∃ w, w = v / (1 + η) := ⟨_, rfl⟩
    have hw0 : 0 < w := hw ▸ div_pos hv0 (by linarith)
    have hvw : (1 + η) * w = v := by rw [hw]; field_simp
    have hηw : 0 < η * w := mul_pos hη0 hw0
    have hwv : w < v := by
      rw [← hvw]
      nlinarith [hηw]
    have hwδ : w < δ := by nlinarith [mul_pos hη0 hv0]
    have hD := hDown ((1 + η) * (δ / 2)) w v fun x hx => by
      have := (hδ' x (ball_subset_ball (by nlinarith) hx) w ⟨hw0, hwδ⟩).2
      rwa [hvw] at this
    have hD2 : L w * M (δ / 2) ≤ L ((1 + η) * (δ / 2)) * M v :=
      (mul_le_mul_of_nonneg_left (hMmono _ _ (by nlinarith)) (hLpos w hw0).le).trans hD
    rw [hLr w hw0, hLr _ (mul_pos (by linarith) hρ0), mul_pow] at hD2
    have hvd : v ^ d = (1 + η) ^ d * w ^ d := by rw [← hvw, mul_pow]
    have he : 0 < (1 + η) ^ d := pow_pos (by linarith) d
    have ha : 0 < (1 - η) ^ d := pow_pos (by linarith) d
    have hP : 0 < (δ / 2) ^ d := pow_pos hρ0 d
    have hUd : 0 < u ^ d := pow_pos hu0 d
    have hWd : 0 < w ^ d := pow_pos hw0 d
    have hMu := hMpos u hu0
    have hMv := hMpos v hv0
    have h1 : (1 - η) ^ d * (δ / 2) ^ d * M u ≤ (1 + η) ^ d * u ^ d * M (δ / 2) :=
      le_of_mul_le_mul_right (by linarith [hU2]) hc₁
    have h2 : w ^ d * M (δ / 2) ≤ (1 + η) ^ d * (δ / 2) ^ d * M v :=
      le_of_mul_le_mul_right (by linarith [hD2]) hc₁
    have h3 : (1 - η) ^ d * (δ / 2) ^ d * M u * w ^ d ≤ (1 + η) ^ d * u ^ d * M (δ / 2) * w ^ d :=
      mul_le_mul_of_nonneg_right h1 hWd.le
    have h4 : (1 + η) ^ d * u ^ d * (w ^ d * M (δ / 2)) ≤
        (1 + η) ^ d * u ^ d * ((1 + η) ^ d * (δ / 2) ^ d * M v) :=
      mul_le_mul_of_nonneg_left h2 (mul_pos he hUd).le
    have h5 : (1 - η) ^ d * M u * w ^ d * (δ / 2) ^ d ≤
        ((1 + η) ^ d) ^ 2 * u ^ d * M v * (δ / 2) ^ d := by
      nlinarith
    have h6 := le_of_mul_le_mul_right h5 hP
    have hne1 : u ^ d * L 1 ≠ 0 := (mul_pos hUd hc₁).ne'
    have hne2 : (1 + η) ^ d * w ^ d * L 1 ≠ 0 := (mul_pos (mul_pos he hWd) hc₁).ne'
    rw [hg, hg, hLr u hu0, hLr v hv0, hvd]
    calc M u / (u ^ d * L 1)
        ≤ ((1 + η) ^ d) ^ 3 / (1 - η) ^ d * (M v / ((1 + η) ^ d * w ^ d * L 1)) := by
          rw [div_le_iff₀ (mul_pos hUd hc₁)]
          have heq : ((1 + η) ^ d) ^ 3 / (1 - η) ^ d * (M v / ((1 + η) ^ d * w ^ d * L 1)) *
              (u ^ d * L 1) = ((1 + η) ^ d) ^ 2 * u ^ d * M v / ((1 - η) ^ d * w ^ d) := by
            field_simp
          rw [heq, le_div_iff₀ (mul_pos ha hWd)]
          linarith
      _ ≤ (1 + ε) * (M v / ((1 + η) ^ d * w ^ d * L 1)) :=
          mul_le_mul_of_nonneg_right hFη.le (div_pos hMv (mul_pos (mul_pos he hWd) hc₁)).le
  obtain ⟨t₁, ht₁, hkey₁⟩ := hkey 1 one_pos
  have hv₀ : t₁ / 2 ∈ Ioo 0 t₁ := ⟨by linarith, by linarith⟩
  have hg₀ := hgpos (t₁ / 2) hv₀.1
  have hupper : ∀ u ∈ Ioo 0 t₁, g u ≤ 2 * g (t₁ / 2) := fun u hu => by
    have := hkey₁ u hu _ hv₀
    linarith
  have hlower : ∀ u ∈ Ioo 0 t₁, g (t₁ / 2) ≤ 2 * g u := fun u hu => by
    have := hkey₁ _ hv₀ u hu
    linarith
  have hcau : Cauchy (map g (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hB : 0 < 2 * g (t₁ / 2) := by linarith
    obtain ⟨t, ht, hgt⟩ := hkey (ε / (2 * (2 * g (t₁ / 2)))) (div_pos hε (by linarith))
    refine ⟨g '' Ioo 0 (min t t₁), image_mem_map (Ioo_mem_nhdsGT (lt_min ht ht₁)), ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hu' : u ∈ Ioo 0 t := ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩
    have hv' : v ∈ Ioo 0 t := ⟨hv.1, hv.2.trans_le (min_le_left _ _)⟩
    have hu₁ : u ∈ Ioo 0 t₁ := ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩
    have hv₁ : v ∈ Ioo 0 t₁ := ⟨hv.1, hv.2.trans_le (min_le_right _ _)⟩
    have h1 := hgt u hu' v hv'
    have h2 := hgt v hv' u hu'
    have h3 : ε / (2 * (2 * g (t₁ / 2))) * g v ≤ ε / (2 * (2 * g (t₁ / 2))) * (2 * g (t₁ / 2)) :=
      mul_le_mul_of_nonneg_left (hupper v hv₁) (div_pos hε (by linarith)).le
    have h4 : ε / (2 * (2 * g (t₁ / 2))) * g u ≤ ε / (2 * (2 * g (t₁ / 2))) * (2 * g (t₁ / 2)) :=
      mul_le_mul_of_nonneg_left (hupper u hu₁) (div_pos hε (by linarith)).le
    have h5 : ε / (2 * (2 * g (t₁ / 2))) * (2 * g (t₁ / 2)) = ε / 2 := by
      field_simp
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> nlinarith
  obtain ⟨c, hc⟩ := CompleteSpace.complete hcau
  have hc0 : 0 < c := by
    have : g (t₁ / 2) / 2 ≤ c := ge_of_tendsto hc (by
      filter_upwards [Ioo_mem_nhdsGT ht₁] with u hu
      linarith [hlower u hu])
    linarith
  refine ⟨ENNReal.ofReal c, (ENNReal.ofReal_pos.2 hc0).ne', ENNReal.ofReal_ne_top, ?_⟩
  refine (ENNReal.tendsto_ofReal hc).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [hg, hM, hL, ← ENNReal.toReal_div, ENNReal.ofReal_toReal]
  exact (ENNReal.div_lt_top (measure_ne_top ν _) (measure_ball_pos lam 0 hr).ne').ne
end _root_.GlobalTheory
end GlobalTheory
