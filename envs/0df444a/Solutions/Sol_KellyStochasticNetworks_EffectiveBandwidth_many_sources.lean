-- Prove2me | solution 1 for KellyStochasticNetworks.EffectiveBandwidth.many_sources
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-31T04:53:05.859098+00:00
-- url     : https://prove2.me/submissions/d4be168d-2575-4bb7-b80a-71d908e533c2

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace ManySrcCE

/-- clipped tent profile on the unit circle, values in `[-1, 1]` -/
noncomputable def kk (θ : UnitAddCircle) : ℝ := max (min (8 * ‖θ‖ - 2) 1) (-1)

/-- the cumulative workload of one source on `[a,b]` with phase `θ`:
rate `8` plus the increment of the bounded periodic profile `kk`. -/
noncomputable def ff (a b : ℝ) (θ : UnitAddCircle) : ℝ :=
  8 * (b - a) + kk (θ + (b : UnitAddCircle)) - kk (θ + (a : UnitAddCircle))

lemma kk_le (θ : UnitAddCircle) : kk θ ≤ 1 := by
  unfold kk; exact max_le (min_le_right _ _) (by norm_num)

lemma le_kk (θ : UnitAddCircle) : -1 ≤ kk θ := by
  unfold kk; exact le_max_right _ _

lemma kk_lip (θ φ : UnitAddCircle) : |kk θ - kk φ| ≤ 8 * ‖θ - φ‖ := by
  unfold kk
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le ?_ (by positivity)
  have h1 := abs_norm_sub_norm_le θ φ
  calc |8 * ‖θ‖ - 2 - (8 * ‖φ‖ - 2)| = 8 * |‖θ‖ - ‖φ‖| := by
        rw [show 8 * ‖θ‖ - 2 - (8 * ‖φ‖ - 2) = 8 * (‖θ‖ - ‖φ‖) by ring, abs_mul]; norm_num
    _ ≤ 8 * ‖θ - φ‖ := by linarith

lemma kk_cont : Continuous kk := by
  unfold kk; fun_prop

lemma ff_cont (a b : ℝ) : Continuous (ff a b) := by
  unfold ff
  have := kk_cont
  fun_prop

lemma ff_meas (a b : ℝ) : Measurable (ff a b) := (ff_cont a b).measurable

lemma norm_coe_le (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  have := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1:ℝ)) (m := x)
  simpa [Real.norm_eq_abs] using this

lemma ff_nonneg (a b : ℝ) (hab : a ≤ b) (θ : UnitAddCircle) : 0 ≤ ff a b θ := by
  unfold ff
  have h := kk_lip (θ + (b : UnitAddCircle)) (θ + (a : UnitAddCircle))
  have h2 : θ + (b : UnitAddCircle) - (θ + (a : UnitAddCircle)) = ((b - a : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_sub]; abel
  rw [h2] at h
  have h3 := norm_coe_le (b - a)
  rw [abs_of_nonneg (by linarith)] at h3
  have h4 := neg_abs_le (kk (θ + (b : UnitAddCircle)) - kk (θ + (a : UnitAddCircle)))
  nlinarith

lemma ff_shift (a b : ℝ) (θ : UnitAddCircle) :
    ff a b θ = ff 0 (b - a) (θ + (a : UnitAddCircle)) := by
  unfold ff
  have : θ + (a : UnitAddCircle) + ((b - a : ℝ) : UnitAddCircle) = θ + (b : UnitAddCircle) := by
    rw [AddCircle.coe_sub]; abel
  rw [this]; simp

lemma ff_abs (t : ℝ) (θ : UnitAddCircle) : |ff 0 t θ| ≤ 8 * |t| + 2 := by
  unfold ff
  have := kk_le (θ + (t : UnitAddCircle)); have := le_kk (θ + (t : UnitAddCircle))
  have := kk_le (θ + ((0:ℝ) : UnitAddCircle)); have := le_kk (θ + ((0:ℝ) : UnitAddCircle))
  rw [abs_le]
  constructor <;> cases abs_cases t <;> nlinarith

lemma ff_neg_le (t : ℝ) (θ : UnitAddCircle) : ff (-t) 0 θ ≤ 8 * t + 2 := by
  unfold ff
  have := kk_le (θ + ((0:ℝ) : UnitAddCircle)); have := le_kk (θ + ((-t:ℝ) : UnitAddCircle))
  linarith

lemma ff_half (x : ℝ) (hx1 : -1/8 ≤ x) (hx2 : x ≤ 0) :
    ff 0 (1/2) (x : UnitAddCircle) = 6 := by
  unfold ff
  have e1 : ((x : ℝ) : UnitAddCircle) + ((1/2 : ℝ) : UnitAddCircle) = ((x + 1/2 : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add]
  have e2 : ((x : ℝ) : UnitAddCircle) + ((0 : ℝ) : UnitAddCircle) = ((x : ℝ) : UnitAddCircle) := by
    simp
  rw [e1, e2]
  have n1 : ‖((x + 1/2 : ℝ) : UnitAddCircle)‖ = x + 1/2 := by
    rw [(AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).2 (by
      rw [abs_of_nonneg (by linarith)]; norm_num; linarith)]
    exact abs_of_nonneg (by linarith)
  have n2 : ‖((x : ℝ) : UnitAddCircle)‖ = -x := by
    rw [(AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).2 (by
      rw [abs_of_nonpos hx2]; norm_num; linarith)]
    exact abs_of_nonpos hx2
  unfold kk
  rw [n1, n2]
  have a1 : min (8 * (x + 1/2) - 2) 1 = 1 := min_eq_right (by linarith)
  have a2 : min (8 * -x - 2) 1 = 8 * -x - 2 := min_eq_left (by linarith)
  rw [a1, a2, max_eq_left (by norm_num), max_eq_right (by linarith)]
  norm_num

instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

lemma vol_pos : 0 < (volume : Measure UnitAddCircle) {φ | 6 ≤ ff 0 (1/2) φ} := by
  have hS : MeasurableSet {φ : UnitAddCircle | 6 ≤ ff 0 (1/2) φ} :=
    (isClosed_le continuous_const (ff_cont 0 (1/2))).measurableSet
  have hmp := UnitAddCircle.measurePreserving_mk (-1/2)
  rw [← hmp.measure_preimage hS.nullMeasurableSet]
  have hsub : Set.Icc (-1/8 : ℝ) 0 ⊆ (QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹'
      {φ | 6 ≤ ff 0 (1/2) φ} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have := ff_half x hx.1 hx.2
    exact le_of_eq this.symm
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.restrict_apply measurableSet_Icc,
    Set.inter_eq_left.2 (Set.Icc_subset_Ioc (by norm_num) (by norm_num)), Real.volume_Icc]
  norm_num

end ManySrcCE

open ManySrcCE in
theorem solution : ¬ (∀ {Ω J : Type} [MeasurableSpace Ω] [Fintype J]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : J → ℕ → ℝ → ℝ → Ω → ℝ) (n : J → ℕ)
    (C B : ℝ) (hC : 0 < C) (hB : 0 < B)
    (hmeas : ∀ j i a b, Measurable (X j i a b))
    (hindep : iIndepFun
      (fun k : J × ℕ => fun ω => fun ab : ℝ × ℝ => X k.1 k.2 ab.1 ab.2 ω) P)
    (hident : ∀ j i, IdentDistrib
      (fun ω => fun ab : ℝ × ℝ => X j i ab.1 ab.2 ω)
      (fun ω => fun ab : ℝ × ℝ => X j 0 ab.1 ab.2 ω) P P)
    (hstationary : ∀ j i a b, a ≤ b →
      IdentDistrib (X j i a b) (X j i 0 (b - a)) P P)
    (hzero : ∀ j i a ω, X j i a a ω = 0)
    (hadd : ∀ j i a b d ω, a ≤ b → b ≤ d →
      X j i a d ω = X j i a b ω + X j i b d ω)
    (hnonneg : ∀ j i a b ω, a ≤ b → 0 ≤ X j i a b ω)
    (hlocal : ∀ j t, 0 ≤ t → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      Integrable (fun ω => Real.exp (s * X j 0 0 t ω)) P),
    let S : ℕ → ℝ → ℝ → Ω → ℝ := fun N a b ω =>
      ∑ j, ∑ i ∈ Finset.range (n j * N), X j i a b ω
    let Q : ℕ → Ω → EReal := fun N ω =>
      ⨆ t : {t : ℝ // 0 ≤ t}, ((S N (-t.val) 0 ω - (C * N) * t.val : ℝ) : EReal)
    (∀ N, Measurable (Q N)) →
    Tendsto
      (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : EReal) *
        ENNReal.log (P {ω | ((B * (N + 1) : ℝ) : EReal) < Q (N + 1) ω})))
      atTop (𝓝 (⨆ t : {t : ℝ // 0 ≤ t}, ⨅ s : {s : ℝ // 0 ≤ s},
        (∑ j, (n j : EReal) *
          ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (s.val * X j 0 0 t.val ω)) ∂P)) -
          ((s.val * (B + C * t.val) : ℝ) : EReal)))) := by
  intro h
  let Ω0 := ℕ → UnitAddCircle
  let μ0 : Measure Ω0 := Measure.infinitePi (fun _ => volume)
  let P : Measure (ULift Ω0) := μ0.map ULift.up
  have hP : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map measurable_up.aemeasurable
  let θ : ℕ → ULift Ω0 → UnitAddCircle := fun i ω => ω.down i
  have hθm : ∀ i, Measurable (θ i) := fun i => (measurable_pi_apply i).comp measurable_down
  have hlaw : ∀ i, P.map (θ i) = volume := by
    intro i
    rw [Measure.map_map (hθm i) measurable_up]
    exact Measure.infinitePi_map_eval _ i
  have hind : iIndepFun θ P := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hθm]
    simp_rw [hlaw]
    rw [Measure.map_map (measurable_pi_iff.2 hθm) measurable_up]
    exact Measure.map_id
  have hid : ∀ i, IdentDistrib (θ i) (θ 0) P P := fun i =>
    ⟨(hθm i).aemeasurable, (hθm 0).aemeasurable, by rw [hlaw, hlaw]⟩
  have hsh : ∀ i (a : ℝ), IdentDistrib (fun ω => θ i ω + (a : UnitAddCircle)) (θ i) P P := by
    intro i a
    refine ⟨((hθm i).add_const _).aemeasurable, (hθm i).aemeasurable, ?_⟩
    rw [show (fun ω => θ i ω + (a : UnitAddCircle)) = (fun φ => φ + (a : UnitAddCircle)) ∘ θ i
      from rfl, ← Measure.map_map (measurable_add_const _) (hθm i), hlaw]
    exact (measurePreserving_add_right volume (a : UnitAddCircle)).map_eq
  let X : PUnit → ℕ → ℝ → ℝ → ULift Ω0 → ℝ := fun _ i a b ω => ff a b (θ i ω)
  let Φ : UnitAddCircle → (ℝ × ℝ → ℝ) := fun φ ab => ff ab.1 ab.2 φ
  have hΦ : Measurable Φ := by
    refine measurable_pi_iff.2 fun ab => ff_meas ab.1 ab.2
  have h1 := @h (ULift Ω0) PUnit _ _ P hP X (fun _ => 1) 8 2 (by norm_num) (by norm_num)
    (fun j i a b => (ff_meas a b).comp (hθm i))
    (by
      have := (hind.precomp (g := fun k : PUnit × ℕ => k.2) (fun x y hxy => Prod.ext (Subsingleton.elim _ _) hxy)).comp (fun _ => Φ) (fun _ => hΦ)
      exact this)
    (fun j i => (hid i).comp hΦ)
    (fun j i a b _ => by
      have e : X j i a b = ff 0 (b - a) ∘ (fun ω => θ i ω + (a : UnitAddCircle)) := by
        funext ω; exact ff_shift a b (θ i ω)
      rw [e]
      exact (hsh i a).comp (ff_meas 0 (b - a)))
    (fun j i a ω => by simp [X, ff])
    (fun j i a b d ω _ _ => by simp only [X, ff]; ring)
    (fun j i a b ω hab => ff_nonneg a b hab _)
    (fun j t _ => ⟨1, one_pos, fun s _ => by
      refine Integrable.of_bound (C := Real.exp (|s| * (8 * |t| + 2))) ?_ ?_
      · exact (Real.continuous_exp.measurable.comp
          (((ff_meas 0 t).comp (hθm 0)).const_mul s)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun ω => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.2
        have h2 := ff_abs t (θ 0 ω)
        calc s * X j 0 0 t ω ≤ |s * X j 0 0 t ω| := le_abs_self _
          _ = |s| * |ff 0 t (θ 0 ω)| := abs_mul _ _
          _ ≤ |s| * (8 * |t| + 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)⟩)
  dsimp only at h1
  refine absurd (h1 ?_) ?_
  · intro N
    have hG : LowerSemicontinuous (fun v : Ω0 => ⨆ t : {t : ℝ // 0 ≤ t},
        ((∑ j : PUnit, ∑ i ∈ Finset.range (1 * N), ff (-t.val) 0 (v i) - 8 * (N:ℝ) * t.val : ℝ)
          : EReal)) := by
      refine lowerSemicontinuous_iSup fun t => ?_
      refine Continuous.lowerSemicontinuous ?_
      refine continuous_coe_real_ereal.comp ?_
      refine Continuous.sub ?_ continuous_const
      refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ => ?_
      exact (ff_cont _ _).comp (continuous_apply i)
    exact hG.measurable.comp measurable_down
  · intro hT
    have hempty : ∀ N : ℕ, {ω : ULift Ω0 | ((2 * ((N:ℝ) + 1) : ℝ) : EReal) <
        ⨆ t : {t : ℝ // 0 ≤ t}, ((∑ j : PUnit, ∑ i ∈ Finset.range (1 * (N + 1)),
          X j i (-t.val) 0 ω - 8 * ((N + 1 : ℕ) : ℝ) * t.val : ℝ) : EReal)} = ∅ := by
      intro N
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      refine iSup_le fun t => EReal.coe_le_coe_iff.2 ?_
      simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, X]
      have : ∑ i ∈ Finset.range (N+1), ff (-t.val) 0 (θ i ω) ≤
          ∑ i ∈ Finset.range (N+1), (8 * t.val + 2) :=
        Finset.sum_le_sum fun i _ => ff_neg_le _ _
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      push_cast at this ⊢
      nlinarith [t.2]
    have hT' := hT.congr (f₂ := fun _ : ℕ => (⊥ : EReal)) (fun N => by
      rw [hempty N, measure_empty, ENNReal.log_zero]
      exact EReal.coe_mul_bot_of_pos (x := (((N+1:ℕ):ℝ))⁻¹) (by positivity))
    have heq := tendsto_nhds_unique tendsto_const_nhds hT'
    have hSmeas : MeasurableSet {φ : UnitAddCircle | 6 ≤ ff 0 (1/2) φ} :=
      (isClosed_le continuous_const (ff_cont 0 (1/2))).measurableSet
    have hAm : MeasurableSet {ω : ULift Ω0 | 6 ≤ ff 0 (1/2) (θ 0 ω)} := (hθm 0) hSmeas
    have hA : 0 < P {ω | 6 ≤ ff 0 (1/2) (θ 0 ω)} := by
      have : P {ω | 6 ≤ ff 0 (1/2) (θ 0 ω)} = volume {φ | 6 ≤ ff 0 (1/2) φ} := by
        rw [← hlaw 0, Measure.map_apply (hθm 0) hSmeas]; rfl
      rw [this]; exact vol_pos
    set L := ENNReal.log (P {ω | 6 ≤ ff 0 (1/2) (θ 0 ω)}) with hLdef
    have hL : L ≠ ⊥ := by
      rw [hLdef, Ne, ENNReal.log_eq_bot_iff]; exact hA.ne'
    apply hL
    refine le_bot_iff.1 ?_
    rw [heq]
    refine le_iSup_of_le ⟨1/2, by norm_num⟩ (le_iInf fun s => ?_)
    simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, one_mul]
    have hint : ENNReal.ofReal (Real.exp (s.val * 6)) * P {ω | 6 ≤ ff 0 (1/2) (θ 0 ω)} ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (s.val * X default 0 0 (1/2) ω)) ∂P := by
      rw [← lintegral_indicator_const hAm]
      refine lintegral_mono fun ω => ?_
      by_cases hω : ω ∈ {ω : ULift Ω0 | 6 ≤ ff 0 (1/2) (θ 0 ω)}
      · rw [Set.indicator_of_mem hω]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω s.2))
      · rw [Set.indicator_of_notMem hω]; exact zero_le
    have hlog := ENNReal.log_monotone hint
    rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at hlog
    have e6 : (s.val * (2 + 8 * (1/2 : ℝ))) = s.val * 6 := by norm_num
    show L ≤ _ - ((s.val * (2 + 8 * (1/2 : ℝ)) : ℝ) : EReal)
    rw [e6]
    calc L = ((s.val * 6 : ℝ) : EReal) + L - ((s.val * 6 : ℝ) : EReal) :=
          EReal.add_sub_cancel_left.symm
      _ ≤ _ := EReal.sub_le_sub hlog le_rfl
