-- Prove2me | solution 1 for MultiItemRev.KSeparate.proposition_13_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:30:30.381508+00:00
-- url     : https://prove2.me/submissions/a62ee443-2dd0-454b-9b20-eaddd3841ea4

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model
import Theorems.Thm_MultiItemRev_KSeparate_myerson_one_good

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace KSepP13Aux
open MultiItemRev.Decomp

/-- Truncation `t ↦ t · 1{t < p}`. -/
noncomputable def Y (p : ℝ) (t : ℝ≥0) : ℝ := if (t : ℝ) < p then (t : ℝ) else 0

lemma Y_nonneg (p : ℝ) (t : ℝ≥0) : 0 ≤ Y p t := by
  unfold Y; split_ifs <;> simp

lemma Y_le (p : ℝ) (hp : 0 ≤ p) (t : ℝ≥0) : Y p t ≤ p := by
  unfold Y; split_ifs with h
  · exact h.le
  · exact hp

lemma measurable_Y (p : ℝ) : Measurable (Y p) := by
  unfold Y
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
    measurable_const

lemma dyadic (b : ℝ) (hb : 0 < b) : ∀ (L : ℕ) (t : ℝ), t < 2 ^ L * b →
    t < b ∨ ∃ l < L, 2 ^ l * b ≤ t ∧ t < 2 ^ (l + 1) * b
  | 0, t, h => Or.inl (by simpa using h)
  | L + 1, t, h => by
    by_cases h' : t < 2 ^ L * b
    · rcases dyadic b hb L t h' with h1 | ⟨l, hl, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨l, by omega, h2⟩
    · exact Or.inr ⟨L, by omega, le_of_not_gt h', h⟩

lemma Y_bound (p b : ℝ) (hb : 0 < b) (L : ℕ) (hL : p ≤ 2 ^ L * b) (t : ℝ≥0) :
    Y p t ≤ b ∨ ∃ l < L, 2 ^ l * b ≤ (t : ℝ) ∧ Y p t ≤ 2 ^ (l + 1) * b := by
  by_cases ht : (t : ℝ) < p
  · have hY : Y p t = t := if_pos ht
    rcases dyadic b hb L t (by linarith) with h | ⟨l, hl, h1, h2⟩
    · left; rw [hY]; exact h.le
    · right; exact ⟨l, hl, h1, by rw [hY]; exact h2.le⟩
  · left
    have : Y p t = 0 := if_neg ht
    rw [this]; exact hb.le

/-- The dyadic domination `g (Y t) ≤ g b + ∑_{l<L} g(2^{l+1} b) 1{t ≥ 2^l b}`. -/
lemma g_Y_le (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Ici 0)) (hg0 : ∀ v, 0 ≤ v → 0 ≤ g v)
    (p b : ℝ) (hb : 0 < b) (L : ℕ) (hL : p ≤ 2 ^ L * b) (t : ℝ≥0) :
    g (Y p t) ≤ g b + ∑ l ∈ Finset.range L,
      Set.indicator {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} (fun _ => g (2 ^ (l + 1) * b)) t := by
  have hterm : ∀ l ∈ Finset.range L, 0 ≤
      Set.indicator {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} (fun _ => g (2 ^ (l + 1) * b)) t := by
    intro l _
    exact Set.indicator_nonneg (fun _ _ => hg0 _ (by positivity)) _
  rcases Y_bound p b hb L hL t with h | ⟨l, hl, h1, h2⟩
  · have := hg (Y_nonneg p t) (Set.mem_Ici.mpr hb.le) h
    have := Finset.sum_nonneg hterm
    linarith
  · have h3 := hg (Y_nonneg p t) (Set.mem_Ici.mpr (by positivity)) h2
    have h4 := Finset.single_le_sum hterm (Finset.mem_range.mpr hl)
    rw [Set.indicator_of_mem (show t ∈ {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} from h1)] at h4
    have := hg0 b hb.le
    linarith

lemma integral_g_Y_le (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (ρ : ℝ)
    (htail : ∀ q : ℝ, 0 < q → ν.real {s : ℝ≥0 | q ≤ (s : ℝ)} * q ≤ ρ)
    (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Ici 0)) (hg0 : ∀ v, 0 ≤ v → 0 ≤ g v)
    (p b : ℝ) (hgi : Integrable (fun t => g (Y p t)) ν) (hb : 0 < b) (L : ℕ) (hL : p ≤ 2 ^ L * b) (C : ℕ → ℝ)
    (hC : ∀ l, g (2 ^ (l + 1) * b) ≤ C l * (2 ^ l * b)) (hC0 : ∀ l, 0 ≤ C l) :
    ∫ t, g (Y p t) ∂ν ≤ g b + ∑ l ∈ Finset.range L, C l * ρ := by
  have hms : ∀ l : ℕ, MeasurableSet {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} := fun l =>
    measurableSet_le measurable_const (by fun_prop)
  calc ∫ t, g (Y p t) ∂ν ≤ ∫ t, (g b + ∑ l ∈ Finset.range L,
        Set.indicator {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} (fun _ => g (2 ^ (l + 1) * b)) t) ∂ν := by
        refine integral_mono hgi ?_ (fun t => g_Y_le g hg hg0 p b hb L hL t)
        refine (integrable_const _).add (integrable_finsetSum _ fun l _ => ?_)
        exact (integrable_const _).indicator (hms l)
    _ = g b + ∑ l ∈ Finset.range L,
        ν.real {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} * g (2 ^ (l + 1) * b) := by
        rw [integral_add (integrable_const _) (integrable_finsetSum _ fun l _ =>
          (integrable_const _).indicator (hms l)), integral_finsetSum _ fun l _ =>
          (integrable_const _).indicator (hms l)]
        simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_indicator_const _ (hms l), smul_eq_mul]
    _ ≤ g b + ∑ l ∈ Finset.range L, C l * ρ := by
        refine add_le_add_right (Finset.sum_le_sum fun l _ => ?_) _
        calc ν.real {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} * g (2 ^ (l + 1) * b)
            ≤ ν.real {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} * (C l * (2 ^ l * b)) := by
              exact mul_le_mul_of_nonneg_left (hC l) measureReal_nonneg
          _ = C l * (ν.real {s : ℝ≥0 | 2 ^ l * b ≤ (s : ℝ)} * (2 ^ l * b)) := by ring
          _ ≤ C l * ρ := mul_le_mul_of_nonneg_left (htail _ (by positivity)) (hC0 l)

lemma geom_le (L : ℕ) : ∑ l ∈ Finset.range L, (2 : ℝ) ^ l ≤ 2 ^ L := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, pow_succ]; linarith


lemma key (k : ℕ) (hk : 2 ≤ k) (ν : Fin k → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (p : ℝ≥0) :
    (p : ℝ≥0∞) * (Measure.pi ν) {x | p ≤ ∑ i, x i} ≤
      ENNReal.ofReal (60 * Real.log k) * ∑ i, Rev1 (ν i) := by
  set μ := Measure.pi ν with hμ
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hlogk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk2
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hlogkpos : 0 < Real.log k := by linarith
  have htail : ∀ i (q : ℝ≥0), (q : ℝ≥0∞) * ν i {t | q ≤ t} ≤ Rev1 (ν i) := by
    intro i q
    rw [(MultiItemRev.KSeparate.myerson_one_good (ν i)).1]
    exact le_iSup (fun q : ℝ≥0 => (q : ℝ≥0∞) * ν i {t | q ≤ t}) q
  by_cases htop : ∃ i, Rev1 (ν i) = ⊤
  · obtain ⟨i, hi⟩ := htop
    have : ∑ i, Rev1 (ν i) = ⊤ := by
      rw [ENNReal.sum_eq_top]; exact ⟨i, Finset.mem_univ _, hi⟩
    rw [this, ENNReal.mul_top (by simp; linarith)]
    exact le_top
  push Not at htop
  set ρ : Fin k → ℝ := fun i => (Rev1 (ν i)).toReal with hρ
  set R : ℝ := ∑ i, ρ i with hR
  have hρ0 : ∀ i, 0 ≤ ρ i := fun i => ENNReal.toReal_nonneg
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => hρ0 i
  have hsumR : ∑ i, Rev1 (ν i) = ENNReal.ofReal R := by
    rw [hR, ENNReal.ofReal_sum_of_nonneg (fun i _ => hρ0 i)]
    exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_toReal (htop i)).symm
  have htailR : ∀ i (q : ℝ), 0 < q → (ν i).real {s : ℝ≥0 | q ≤ (s : ℝ)} * q ≤ ρ i := by
    intro i q hq
    have hset : {s : ℝ≥0 | q ≤ (s : ℝ)} = {s : ℝ≥0 | q.toNNReal ≤ s} := by
      ext s; simp [Real.toNNReal_le_iff_le_coe]
    have h := htail i q.toNNReal
    rw [← hset] at h
    have := ENNReal.toReal_mono (htop i) h
    rw [ENNReal.toReal_mul] at this
    simpa [Measure.real, Real.coe_toNNReal _ hq.le, mul_comm] using this
  have hmeval : ∀ i (q : ℝ≥0), μ {x | q ≤ x i} = ν i {t | q ≤ t} := by
    intro i q
    exact (measurePreserving_eval ν i).measure_preimage
      (measurableSet_le measurable_const measurable_id).nullMeasurableSet
  rw [hsumR, ← ENNReal.ofReal_mul (by positivity)]
  by_cases hp : (p : ℝ) ≤ 60 * Real.log k * R
  · calc (p : ℝ≥0∞) * μ {x | p ≤ ∑ i, x i} ≤ (p : ℝ≥0∞) * 1 := by gcongr; exact prob_le_one
      _ = ENNReal.ofReal p := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hp
  push Not at hp
  have hppos : 0 < (p : ℝ) := lt_of_le_of_lt (by positivity) hp
  by_cases hR0' : R = 0
  · have hρz : ∀ i, Rev1 (ν i) = 0 := by
      intro i
      have h0 : ρ i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hρ0 i)).mp hR0' i (Finset.mem_univ i)
      rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
      · exact h
      · exact absurd h (htop i)
    have hq : (p / k : ℝ≥0) ≠ 0 := by
      have : (0 : ℝ≥0) < p := by exact_mod_cast hppos
      positivity
    have hzero : ∀ i, ν i {t | p / k ≤ t} = 0 := by
      intro i
      have h := htail i (p / k)
      rw [hρz i, nonpos_iff_eq_zero, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd (by exact_mod_cast h) hq
      · exact h
    have hsub : {x : Fin k → ℝ≥0 | p ≤ ∑ i, x i} ⊆ ⋃ i, {x | p / k ≤ x i} := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hcon
      have hlt : ∑ i, x i < ∑ _i : Fin k, p / k :=
        Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun i _ => hcon i
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      rw [mul_div_cancel₀ _ hk0] at hlt
      exact absurd hx (not_le.mpr hlt)
    have hμ0 : μ {x | p ≤ ∑ i, x i} = 0 := by
      refine le_antisymm ?_ zero_le
      calc μ {x | p ≤ ∑ i, x i} ≤ μ (⋃ i, {x | p / k ≤ x i}) := measure_mono hsub
        _ ≤ ∑ i, μ {x | p / k ≤ x i} := measure_iUnion_fintype_le _ _
        _ = 0 := by simp [hmeval, hzero]
    rw [hμ0, mul_zero]
    exact zero_le
  -- main case
  have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hR0')
  set P : ℝ := (p : ℝ) with hPdef
  set b : ℝ := R / k with hbdef
  have hb : 0 < b := by positivity
  have hbR : b ≤ R := div_le_self hR0 (by linarith)
  have h60 : 1 ≤ 60 * Real.log k := by linarith
  have hbP : b < P := by nlinarith
  have hex : ∃ L : ℕ, P ≤ 2 ^ L * b := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (P / b) one_lt_two
    exact ⟨n, by rw [div_lt_iff₀ hb] at hn; linarith⟩
  classical
  set L := Nat.find hex with hLdef
  have hL : P ≤ 2 ^ L * b := Nat.find_spec hex
  have hL0 : L ≠ 0 := by
    intro h
    have := hL
    rw [h, pow_zero, one_mul] at this
    linarith
  have hLmin : ¬ P ≤ 2 ^ (L - 1) * b := Nat.find_min hex (by omega)
  push Not at hLmin
  have hpowL : (2 : ℝ) ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hL2 : 2 ^ L * b < 2 * P := by rw [hpowL]; nlinarith
  have hLlog : (L : ℝ) * Real.log 2 < Real.log 2 + Real.log k + Real.log (P / R) := by
    have h1 := Real.log_lt_log (by positivity) hLmin
    rw [Real.log_mul (by positivity) hb.ne', Real.log_pow, hbdef,
      Real.log_div hRpos.ne' hkpos.ne', Nat.cast_sub (by omega)] at h1
    rw [Real.log_div hppos.ne' hRpos.ne']
    push_cast at h1
    linarith
  have hlogx : Real.log (P / R) ≤ P / R / 16 + 2 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < P / R / 16 by positivity)
    rw [Real.log_div (by positivity) (by norm_num),
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hx : 60 * Real.log k < P / R := by rw [lt_div_iff₀ hRpos]; linarith
  have hLbound : 1 + 2 * (L : ℝ) ≤ P / R / 2 := by
    have hL0' : (0 : ℝ) ≤ L := by positivity
    have := mul_le_mul_of_nonneg_left hlog2.le hL0'
    linarith
  -- the truncated variables
  set Z : Fin k → (Fin k → ℝ≥0) → ℝ := fun i x => Y P (x i) with hZ
  have hZm : ∀ i, Measurable (Z i) := fun i => (measurable_Y P).comp (measurable_pi_apply i)
  have hZbd : ∀ i x, ‖Z i x‖ ≤ P := by
    intro i x
    rw [Real.norm_of_nonneg (Y_nonneg _ _)]
    exact Y_le P hppos.le _
  have hZL2 : ∀ i, MemLp (Z i) 2 μ := fun i =>
    MemLp.of_bound (hZm i).aestronglyMeasurable P (ae_of_all _ (hZbd i))
  have hint : ∀ i (f : ℝ → ℝ), Measurable f →
      ∫ x, f (Z i x) ∂μ = ∫ t, f (Y P t) ∂(ν i) := by
    intro i f hf
    conv_rhs => rw [← (measurePreserving_eval ν i).map_eq]
    rw [integral_map (measurable_pi_apply i).aemeasurable
      (hf.comp (measurable_Y P)).aestronglyMeasurable]
  have hYint : ∀ i (f : ℝ → ℝ), Measurable f → (∀ v, 0 ≤ v → v ≤ P → |f v| ≤ P ^ 2 + P) →
      Integrable (fun t => f (Y P t)) (ν i) := by
    intro i f hf hfb
    refine Integrable.of_bound (hf.comp (measurable_Y P)).aestronglyMeasurable (P ^ 2 + P)
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs]
    exact hfb _ (Y_nonneg _ _) (Y_le P hppos.le _)
  have hE : ∀ i, ∫ t, Y P t ∂(ν i) ≤ b + L * (2 * ρ i) := by
    intro i
    have h := integral_g_Y_le (ν i) (ρ i) (htailR i) (fun v => v) monotoneOn_id
      (fun v hv => hv) P b
      (hYint i (fun v => v) measurable_id (fun v hv hvP => by
        rw [abs_of_nonneg hv]; nlinarith))
      hb L hL (fun _ => 2) (fun l => le_of_eq (by ring)) (fun _ => by norm_num)
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  have hF : ∀ i, ∫ t, (Y P t) ^ 2 ∂(ν i) ≤ b ^ 2 + 4 * (2 ^ L * b) * ρ i := by
    intro i
    have h := integral_g_Y_le (ν i) (ρ i) (htailR i) (fun v => v ^ 2)
      (fun u hu v _ huv => pow_le_pow_left₀ hu huv 2) (fun v _ => sq_nonneg v) P b
      (hYint i (fun v => v ^ 2) (measurable_id.pow_const 2) (fun v hv hvP => by
        rw [abs_of_nonneg (sq_nonneg v)]; nlinarith))
      hb L hL (fun l => 4 * 2 ^ l * b) (fun l => le_of_eq (by ring)) (fun _ => by positivity)
    refine h.trans ?_
    beta_reduce
    have hg := geom_le L
    have : ∑ l ∈ Finset.range L, 4 * 2 ^ l * b * ρ i =
        4 * b * ρ i * ∑ l ∈ Finset.range L, (2 : ℝ) ^ l := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hb.le) (hρ0 i))
    have e : 4 * (2 ^ L * b) * ρ i = 4 * b * ρ i * 2 ^ L := by ring
    rw [e]
    linarith
  -- the sum of the truncated variables
  set S : (Fin k → ℝ≥0) → ℝ := ∑ i, Z i with hS
  have hSapp : ∀ x, S x = ∑ i, Z i x := fun x => by simp [hS, Finset.sum_apply]
  have hSL2 : MemLp S 2 μ := memLp_finsetSum' _ fun i _ => hZL2 i
  have hZint : ∀ i, Integrable (Z i) μ := fun i => (hZL2 i).integrable one_le_two
  have hmean : μ[S] ≤ P / 2 := by
    have h1 : μ[S] = ∑ i, ∫ t, Y P t ∂(ν i) := by
      rw [show S = fun x => ∑ i, Z i x from funext hSapp,
        integral_finsetSum _ fun i _ => hZint i]
      exact Finset.sum_congr rfl fun i _ => hint i (fun v => v) measurable_id
    have h2 : ∑ i, ∫ t, Y P t ∂(ν i) ≤ ∑ i : Fin k, (b + L * (2 * ρ i)) :=
      Finset.sum_le_sum fun i _ => hE i
    have h3 : ∑ i : Fin k, (b + L * (2 * ρ i)) = R + 2 * L * R := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, hbdef]
      field_simp
      ring
    have h4 : R + 2 * L * R ≤ P / 2 := by
      have := mul_le_mul_of_nonneg_left hLbound hR0
      rw [show R * (P / R / 2) = P / 2 by field_simp] at this
      linarith
    linarith
  have hvar : variance S μ ≤ 9 * R * P := by
    have hind := iIndepFun_pi (μ := ν) (X := fun _ => Y P)
      (fun i => (measurable_Y P).aemeasurable)
    have h1 : variance S μ = ∑ i, variance (Z i) μ :=
      IndepFun.variance_sum (fun i _ => hZL2 i) (fun i _ j _ hij => hind.indepFun hij)
    have h2 : ∀ i, variance (Z i) μ ≤ ∫ t, (Y P t) ^ 2 ∂(ν i) := by
      intro i
      refine (variance_le_expectation_sq (hZm i).aestronglyMeasurable).trans (le_of_eq ?_)
      exact hint i (fun v => v ^ 2) (measurable_id.pow_const 2)
    have h3 : ∑ i : Fin k, (b ^ 2 + 4 * (2 ^ L * b) * ρ i) = R * b + 4 * (2 ^ L * b) * R := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, ← hR, hbdef]
      field_simp
    rw [h1]
    calc ∑ i, variance (Z i) μ ≤ ∑ i : Fin k, (b ^ 2 + 4 * (2 ^ L * b) * ρ i) :=
          Finset.sum_le_sum fun i _ => (h2 i).trans (hF i)
      _ = R * b + 4 * (2 ^ L * b) * R := h3
      _ ≤ R * P + 4 * (2 * P) * R := by gcongr
      _ = 9 * R * P := by ring
  have hcheb := meas_ge_le_variance_div_sq hSL2 (c := P / 2) (by positivity)
  have hsub : {x : Fin k → ℝ≥0 | p ≤ ∑ i, x i} ⊆
      (⋃ i, {x : Fin k → ℝ≥0 | p ≤ x i}) ∪ {ω | P / 2 ≤ |S ω - μ[S]|} := by
    intro x hx
    by_cases h : ∃ i, p ≤ x i
    · left; exact Set.mem_iUnion.mpr h
    · right
      push Not at h
      have hSx : S x = ((∑ i, x i : ℝ≥0) : ℝ) := by
        rw [hSapp, NNReal.coe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        show Y P (x i) = x i
        exact if_pos (by exact_mod_cast h i)
      have hx' : P ≤ S x := by rw [hSx]; exact_mod_cast hx
      show P / 2 ≤ |S x - μ[S]|
      exact le_trans (by linarith) (le_abs_self _)
  have hU : μ (⋃ i, {x : Fin k → ℝ≥0 | p ≤ x i}) ≤ ∑ i, ν i {t | p ≤ t} := by
    refine (measure_iUnion_fintype_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => hmeval i p
  have hfin : P * (variance S μ / (P / 2) ^ 2) ≤ 36 * R := by
    have : variance S μ / (P / 2) ^ 2 ≤ 9 * R * P / (P / 2) ^ 2 :=
      div_le_div_of_nonneg_right hvar (by positivity)
    calc P * (variance S μ / (P / 2) ^ 2) ≤ P * (9 * R * P / (P / 2) ^ 2) := by gcongr
      _ = 36 * R := by field_simp; ring
  calc (p : ℝ≥0∞) * μ {x | p ≤ ∑ i, x i}
      ≤ (p : ℝ≥0∞) * (∑ i, ν i {t | p ≤ t} + ENNReal.ofReal (variance S μ / (P / 2) ^ 2)) := by
        gcongr
        exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hU hcheb))
    _ = ∑ i, (p : ℝ≥0∞) * ν i {t | p ≤ t} +
          ENNReal.ofReal (P * (variance S μ / (P / 2) ^ 2)) := by
        rw [mul_add, Finset.mul_sum, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hppos.le]
    _ ≤ ∑ i, Rev1 (ν i) + ENNReal.ofReal (36 * R) := by
        gcongr with i
        exact htail i p
    _ = ENNReal.ofReal (R + 36 * R) := by
        rw [hsumR, ENNReal.ofReal_add hR0 (by positivity)]
    _ ≤ ENNReal.ofReal (60 * Real.log k * R) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith

end KSepP13Aux

open KSepP13Aux MultiItemRev.Decomp in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ), 2 ≤ k →
      ∀ (ν : Fin k → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)],
        ENNReal.ofReal (c / Real.log (k : ℝ)) *
          MultiItemRev.Decomp.BRev (Measure.pi ν) ≤ MultiItemRev.Decomp.SRev (Measure.pi ν) := by
  refine ⟨1 / 60, by norm_num, fun k hk ν _ => ?_⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogkpos : 0 < Real.log k := Real.log_pos (by linarith)
  have hsrev : SRev (Measure.pi ν) = ∑ i, Rev1 (ν i) := by
    unfold SRev
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(measurePreserving_eval ν i).map_eq]
  have hmeas : Measurable (fun x : Fin k → ℝ≥0 => ∑ i, x i) := by fun_prop
  have : IsProbabilityMeasure ((Measure.pi ν).map (fun x => ∑ i, x i)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hbrev : BRev (Measure.pi ν) =
      ⨆ p : ℝ≥0, (p : ℝ≥0∞) * (Measure.pi ν) {x | p ≤ ∑ i, x i} := by
    unfold BRev
    rw [(MultiItemRev.KSeparate.myerson_one_good _).1]
    refine iSup_congr fun p => ?_
    rw [Measure.map_apply hmeas (measurableSet_le measurable_const measurable_id :
      MeasurableSet {t : ℝ≥0 | p ≤ t})]
    rfl
  rw [hbrev, hsrev, ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  calc ENNReal.ofReal (1 / 60 / Real.log k) * ((p : ℝ≥0∞) * (Measure.pi ν) {x | p ≤ ∑ i, x i})
      ≤ ENNReal.ofReal (1 / 60 / Real.log k) *
          (ENNReal.ofReal (60 * Real.log k) * ∑ i, Rev1 (ν i)) := by
        exact mul_le_mul_of_nonneg_left (key k hk ν p) zero_le
    _ = ∑ i, Rev1 (ν i) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show 1 / 60 / Real.log k * (60 * Real.log k) = 1 by field_simp, ENNReal.ofReal_one,
          one_mul]
