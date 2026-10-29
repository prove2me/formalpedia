-- Prove2me | solution 1 for NaiveLearn.OverMatch.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T22:58:16.423419+00:00
-- url     : https://prove2.me/submissions/58d16a56-0fa2-46e0-88a4-eef5204bcd52

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace Prove2NaiveLearnSubmission

open _root_.NaiveLearn.OverMatch

namespace NaiveLearn.OverMatch.Peer82L2

/-- The coins of the first `t` periods. -/
def past {m : ℕ} (t : ℕ) (U : Coins m) : Fin t → Fin m → unitInterval := fun s => U s

/-- A coin path whose first `t` periods are `v`; the later coins are set to `0`. -/
noncomputable def extend {m : ℕ} (t : ℕ) (v : Fin t → Fin m → unitInterval) : Coins m :=
  fun s => if h : s < t then v ⟨s, h⟩ else fun _ => 0

/-- One step of the belief recursion, coordinatewise. -/
theorem beliefAct_succ_apply {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U : Coins m) (t : ℕ) (i : Fin m) :
    beliefAct σ ε W x1 U (t + 1) i =
      (1 - ε) * beliefAct σ ε W x1 U t i +
        ε * ∑ j, W i j * actOf σ (U t j) (beliefAct σ ε W x1 U t j) :=
  rfl

theorem actOf_nonneg (σ : ℝ → ℝ) (u : unitInterval) (y : ℝ) : 0 ≤ actOf σ u y := by
  unfold actOf
  split_ifs <;> norm_num

theorem actOf_le_one (σ : ℝ → ℝ) (u : unitInterval) (y : ℝ) : actOf σ u y ≤ 1 := by
  unfold actOf
  split_ifs <;> norm_num

/-- With a row-stochastic `W`, `ε ∈ (0, 1]` and `x¹ ∈ [0, 1]^m`, every belief stays in `[0, 1]`. -/
theorem beliefAct_mem_Icc {m : ℕ} {W : Matrix (Fin m) (Fin m) ℝ} (hW : IsWeightMatrix W) {ε : ℝ}
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {x1 : Fin m → ℝ} (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1)
    (U : Coins m) (t : ℕ) : ∀ i, beliefAct id ε W x1 U t i ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hWnn, hWsum⟩ := Matrix.mem_rowStochastic_iff_sum.mp hW.1
  obtain ⟨hε0, hε1⟩ := hε
  induction t with
  | zero => exact hx1
  | succ t ih =>
      intro i
      rw [beliefAct_succ_apply]
      have hS0 : 0 ≤ ∑ j, W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hWnn i j) (actOf_nonneg _ _ _)
      have hS1 : ∑ j, W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) ≤ 1 :=
        calc ∑ j, W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) ≤ ∑ j, W i j :=
              Finset.sum_le_sum fun j _ =>
                mul_le_of_le_one_right (hWnn i j) (actOf_le_one _ _ _)
          _ = 1 := hWsum i
      obtain ⟨hx0, hx1'⟩ := ih i
      refine ⟨?_, ?_⟩
      · nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hx0, mul_nonneg hε0.le hS0]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hε1) (sub_nonneg.mpr hx1'),
          mul_nonneg hε0.le (sub_nonneg.mpr hS1)]

theorem measurable_coin {m : ℕ} (t : ℕ) (j : Fin m) : Measurable (fun U : Coins m => U t j) := by
  fun_prop

theorem measurable_actOf {α : Type*} [MeasurableSpace α] {f : α → unitInterval} {g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun a => actOf id (f a) (g a)) := by
  unfold actOf
  exact Measurable.ite (measurableSet_lt (measurable_subtype_coe.comp hf) hg)
    measurable_const measurable_const

theorem measurable_beliefAct {m : ℕ} (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (x1 : Fin m → ℝ)
    (t : ℕ) : ∀ i, Measurable (fun U : Coins m => beliefAct id ε W x1 U t i) := by
  induction t with
  | zero =>
      intro i
      show Measurable (fun _ : Coins m => x1 i)
      exact measurable_const
  | succ t ih =>
      intro i
      have hact : ∀ j, Measurable
          (fun U : Coins m => actOf id (U t j) (beliefAct id ε W x1 U t j)) :=
        fun j => measurable_actOf (measurable_coin t j) (ih j)
      simp only [beliefAct_succ_apply]
      exact ((ih i).const_mul (1 - ε)).add
        ((Finset.measurable_sum _ fun j _ => (hact j).const_mul (W i j)).const_mul ε)

/-- The beliefs at time `t` depend only on the coins of the first `t` periods. -/
theorem beliefAct_congr {m : ℕ} (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (x1 : Fin m → ℝ)
    (t : ℕ) : ∀ U U' : Coins m, (∀ s < t, U s = U' s) →
      beliefAct id ε W x1 U t = beliefAct id ε W x1 U' t := by
  induction t with
  | zero =>
      intro U U' _
      rfl
  | succ t ih =>
      intro U U' h
      have h1 : beliefAct id ε W x1 U t = beliefAct id ε W x1 U' t :=
        ih U U' fun s hs => h s (Nat.lt_succ_of_lt hs)
      have h2 : U t = U' t := h t (Nat.lt_succ_self t)
      funext i
      rw [beliefAct_succ_apply, beliefAct_succ_apply, h1, h2]

theorem extend_past {m : ℕ} (t : ℕ) (U : Coins m) (s : ℕ) (hs : s < t) :
    extend t (past t U) s = U s := by
  simp [extend, past, hs]

theorem measurable_past {m : ℕ} (t : ℕ) : Measurable (past (m := m) t) :=
  measurable_pi_lambda _ fun s => measurable_pi_apply (s : ℕ)

theorem measurable_extend {m : ℕ} (t : ℕ) : Measurable (extend (m := m) t) := by
  refine measurable_pi_lambda _ fun s => ?_
  by_cases hs : s < t
  · have h : (fun v : Fin t → Fin m → unitInterval => extend t v s) = fun v => v ⟨s, hs⟩ := by
      funext v
      simp [extend, hs]
    rw [h]
    exact measurable_pi_apply _
  · have h : (fun v : Fin t → Fin m → unitInterval => extend t v s) =
        fun _ => fun _ => (0 : unitInterval) := by
      funext v
      simp [extend, hs]
    rw [h]
    exact measurable_const

theorem beliefAct_eq_extend {m : ℕ} (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (x1 : Fin m → ℝ)
    (t : ℕ) (U : Coins m) :
    beliefAct id ε W x1 U t = beliefAct id ε W x1 (extend t (past t U)) t :=
  beliefAct_congr ε W x1 t U _ fun s hs => (extend_past t U s hs).symm

theorem measurable_beliefAct_extend {m : ℕ} (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (t : ℕ) (i : Fin m) :
    Measurable (fun v : Fin t → Fin m → unitInterval => beliefAct id ε W x1 (extend t v) t i) :=
  (measurable_beliefAct ε W x1 t i).comp (measurable_extend t)

/-- The beliefs at time `t` are measurable for the coin filtration at time `t`. -/
theorem measurable_beliefAct_filtration {m : ℕ} (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (t : ℕ) (i : Fin m) :
    Measurable[coinFiltration m t] (fun U : Coins m => beliefAct id ε W x1 U t i) := by
  have h : (fun U : Coins m => beliefAct id ε W x1 U t i) =
      (fun v => beliefAct id ε W x1 (extend t v) t i) ∘ past t := by
    funext U
    exact congrFun (beliefAct_eq_extend ε W x1 t U) i
  rw [h]
  exact (measurable_beliefAct_extend ε W x1 t i).comp (comap_measurable (past t))

theorem integrable_of_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (h : ∀ ω, f ω ∈ Set.Icc (0 : ℝ) 1) : Integrable f P :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h ω).1]
      exact (h ω).2)

theorem indicator_one_mem_Icc {α : Type*} (S : Set α) (a : α) :
    S.indicator (fun _ => (1 : ℝ)) a ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : a ∈ S
  · rw [Set.indicator_of_mem h]
    exact ⟨zero_le_one, le_rfl⟩
  · rw [Set.indicator_of_notMem h]
    exact ⟨le_rfl, zero_le_one⟩

theorem mul_mem_Icc01 {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    a * b ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg ha.1 hb.1, by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hb.2), ha.2]⟩

/-- Using `µ W = µ`: `⟨µ, x^{t+1}⟩ = (1 − ε) ⟨µ, x^t⟩ + ε Σ_j µ_j a_j^t`. -/
theorem drift {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hμ : Matrix.vecMul μ W = μ) (ε : ℝ) (x1 : Fin m → ℝ) (U : Coins m) (t : ℕ) :
    ∑ i, μ i * beliefAct id ε W x1 U (t + 1) i =
      (1 - ε) * ∑ i, μ i * beliefAct id ε W x1 U t i +
        ε * ∑ j, μ j * actOf id (U t j) (beliefAct id ε W x1 U t j) := by
  have hcol : ∀ j, ∑ i, μ i * W i j = μ j := fun j => congrFun hμ j
  have key : ∑ i, ∑ j, μ i * W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) =
      ∑ j, μ j * actOf id (U t j) (beliefAct id ε W x1 U t j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j]
  have expand : ∀ i, μ i * beliefAct id ε W x1 U (t + 1) i =
      (1 - ε) * (μ i * beliefAct id ε W x1 U t i) +
        ε * ∑ j, μ i * W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) := by
    intro i
    have hsum : ∑ j, μ i * W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) =
        μ i * ∑ j, W i j * actOf id (U t j) (beliefAct id ε W x1 U t j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    rw [beliefAct_succ_apply, hsum]
    ring
  rw [Finset.sum_congr rfl fun i _ => expand i, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, key]

/-- For a uniform coin, `∫ 1{u < r} du = r` when `r ∈ [0, 1]`. -/
theorem integral_actOf {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u : unitInterval, actOf id u r = r := by
  have h1 : (fun u : unitInterval => actOf id u r) =
      (Set.Iio (⟨r, hr⟩ : unitInterval)).indicator 1 := by
    funext u
    by_cases h : (u : ℝ) < r
    · have hu : u ∈ Set.Iio (⟨r, hr⟩ : unitInterval) := h
      rw [Set.indicator_of_mem hu]
      simp only [actOf, id_eq, if_pos h, Pi.one_apply]
    · have hu : u ∉ Set.Iio (⟨r, hr⟩ : unitInterval) := h
      rw [Set.indicator_of_notMem hu]
      simp only [actOf, id_eq, if_neg h]
  rw [h1, integral_indicator_one measurableSet_Iio, measureReal_def, unitInterval.volume_Iio]
  exact ENNReal.toReal_ofReal hr.1

/-- The freezing step. The coin `U t j` is independent of the first `t` periods and uniform, so
on every event of the coin filtration at time `t` the action `1{U t j < g}` integrates like `g`,
when `g ∈ [0, 1]` is a function of the first `t` periods. -/
theorem freeze {m : ℕ} (t : ℕ) (j : Fin m) {c : (Fin t → Fin m → unitInterval) → ℝ}
    (hc : Measurable c) (hc01 : ∀ v, c v ∈ Set.Icc (0 : ℝ) 1)
    {B : Set (Fin t → Fin m → unitInterval)} (hB : MeasurableSet B) {g : Coins m → ℝ}
    (hg : ∀ U, g U = c (past t U)) :
    ∫ U in past t ⁻¹' B, actOf id (U t j) (g U) ∂coinLaw m =
      ∫ U in past t ⁻¹' B, g U ∂coinLaw m := by
  let _ : IsProbabilityMeasure (coinLaw m) := by
    unfold coinLaw
    infer_instance
  have hpast : Measurable (past (m := m) t) := measurable_past t
  have hY : Measurable (fun U : Coins m => U t j) := measurable_coin t j
  have hind : IndepFun (past t) (fun U : Coins m => U t j) (coinLaw m) := by
    have h0 := (iIndepFun_infinitePi
      (P := fun _ : ℕ => Measure.pi fun _ : Fin m => (volume : Measure unitInterval))
      (X := fun _ (ω : Fin m → unitInterval) => ω) (fun _ => measurable_id)).indepFun_finset
      (Finset.range t) {t} (Finset.disjoint_singleton_right.mpr (by simp))
      (fun i => measurable_pi_apply i)
    exact h0.comp
      (measurable_pi_lambda (fun (w : ↥(Finset.range t) → Fin m → unitInterval) (s : Fin t) =>
        w ⟨s, Finset.mem_range.mpr s.2⟩) fun s => measurable_pi_apply _)
      ((measurable_pi_apply j).comp (measurable_pi_apply
        (⟨t, Finset.mem_singleton_self t⟩ : ↥({t} : Finset ℕ))))
  have hlawY : (coinLaw m).map (fun U : Coins m => U t j) = (volume : Measure unitInterval) := by
    have h1 : (coinLaw m).map (fun U : Coins m => U t) =
        Measure.pi fun _ : Fin m => (volume : Measure unitInterval) :=
      Measure.infinitePi_map_eval _ t
    have h2 : (fun U : Coins m => U t j) =
        (fun r : Fin m → unitInterval => r j) ∘ (fun U : Coins m => U t) := rfl
    rw [h2, ← Measure.map_map (g := fun r : Fin m → unitInterval => r j)
      (f := fun U : Coins m => U t) (measurable_pi_apply j) (measurable_pi_apply t), h1]
    exact (measurePreserving_eval (fun _ : Fin m => (volume : Measure unitInterval)) j).map_eq
  have hrestrict : ∀ f : Coins m → ℝ, ∫ U in past t ⁻¹' B, f U ∂coinLaw m =
      ∫ U, B.indicator (fun _ => (1 : ℝ)) (past t U) * f U ∂coinLaw m := by
    intro f
    rw [← integral_indicator (hB.preimage hpast)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    change (past t ⁻¹' B).indicator f U =
      B.indicator (fun _ => (1 : ℝ)) (past t U) * f U
    by_cases hU : past t U ∈ B
    · have hU' : U ∈ past t ⁻¹' B := hU
      rw [Set.indicator_of_mem hU', Set.indicator_of_mem hU, one_mul]
    · have hU' : U ∉ past t ⁻¹' B := hU
      rw [Set.indicator_of_notMem hU', Set.indicator_of_notMem hU, zero_mul]
  rw [hrestrict, hrestrict]
  simp only [hg]
  let F : (Fin t → Fin m → unitInterval) × unitInterval → ℝ :=
    fun p => B.indicator (fun _ => (1 : ℝ)) p.1 * actOf id p.2 (c p.1)
  have hFm : Measurable F :=
    ((measurable_const.indicator hB).comp measurable_fst).mul
      (measurable_actOf measurable_snd (hc.comp measurable_fst))
  have hFint : Integrable F (((coinLaw m).map (past t)).prod (volume : Measure unitInterval)) :=
    integrable_of_mem_Icc hFm fun p =>
      mul_mem_Icc01 (indicator_one_mem_Icc B p.1) ⟨actOf_nonneg _ _ _, actOf_le_one _ _ _⟩
  calc ∫ U, B.indicator (fun _ => (1 : ℝ)) (past t U) * actOf id (U t j) (c (past t U))
        ∂coinLaw m
      = ∫ U, F (past t U, U t j) ∂coinLaw m := rfl
    _ = ∫ p, F p ∂((coinLaw m).map fun U => (past t U, U t j)) :=
        (integral_map (hpast.prodMk hY).aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂(((coinLaw m).map (past t)).prod (volume : Measure unitInterval)) := by
        rw [hind.map_prod_eq_prod_map_map hpast.aemeasurable hY.aemeasurable, hlawY]
    _ = ∫ v, ∫ y, F (v, y) ∂(volume : Measure unitInterval) ∂((coinLaw m).map (past t)) :=
        integral_prod F hFint
    _ = ∫ v, B.indicator (fun _ => (1 : ℝ)) v * c v ∂((coinLaw m).map (past t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        show ∫ y, B.indicator (fun _ => (1 : ℝ)) v * actOf id y (c v) = _
        rw [integral_const_mul, integral_actOf (hc01 v)]
    _ = ∫ U, B.indicator (fun _ => (1 : ℝ)) (past t U) * c (past t U) ∂coinLaw m :=
        integral_map hpast.aemeasurable
          ((measurable_const.indicator hB).mul hc).aestronglyMeasurable

/-- `∫_S Σ_j µ_j f_j = Σ_j µ_j ∫_S f_j` for integrable `f_j`. -/
theorem setIntegral_wsum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : Set Ω} {m : ℕ}
    (μ : Fin m → ℝ) {f : Fin m → Ω → ℝ} (hf : ∀ j, Integrable (f j) P) :
    ∫ ω in S, ∑ j, μ j * f j ω ∂P = ∑ j, μ j * ∫ ω in S, f j ω ∂P := by
  rw [integral_finsetSum _ fun j _ => ((hf j).const_mul (μ j)).integrableOn]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul (μ j) _

end NaiveLearn.OverMatch.Peer82L2

namespace NaiveLearn.OverMatch

/-- Lemma 2, p. 19: for the `ε`-DeGroot process (probability matching, `σ = id`) the centrality-
weighted average belief `⟨µ^W, x^t⟩ = Σ_i µ_i x_i^t` is a martingale. The filtration is generated
by the coins `U_0, …, U_{t−1}`, which contains `σ(x^0, …, x^t)`. -/
theorem lemma_2 {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) :
    Martingale (fun t U => ∑ i, μ i * beliefAct id ε W x1 U t i) (coinFiltration m)
      (coinLaw m) := by
  let _ : IsProbabilityMeasure (coinLaw m) := by
    unfold coinLaw
    infer_instance
  have hxI : ∀ (U : Coins m) (t : ℕ) (i : Fin m), beliefAct id ε W x1 U t i ∈ Set.Icc (0 : ℝ) 1 :=
    fun U t => Peer82L2.beliefAct_mem_Icc hW hε hx1 U t
  obtain ⟨-, -, hμW⟩ := hμ
  have hx_int : ∀ t i, Integrable (fun U : Coins m => beliefAct id ε W x1 U t i) (coinLaw m) :=
    fun t i => Peer82L2.integrable_of_mem_Icc (Peer82L2.measurable_beliefAct ε W x1 t i)
      (fun U => hxI U t i)
  have ha_int : ∀ t j, Integrable
      (fun U : Coins m => actOf id (U t j) (beliefAct id ε W x1 U t j)) (coinLaw m) :=
    fun t j => Peer82L2.integrable_of_mem_Icc
      (Peer82L2.measurable_actOf (Peer82L2.measurable_coin t j)
        (Peer82L2.measurable_beliefAct ε W x1 t j))
      (fun _ => ⟨Peer82L2.actOf_nonneg _ _ _, Peer82L2.actOf_le_one _ _ _⟩)
  refine martingale_of_setIntegral_eq_succ ?_ ?_ ?_
  · intro t
    exact (Finset.measurable_sum _ fun i _ =>
      (Peer82L2.measurable_beliefAct_filtration ε W x1 t i).const_mul (μ i)).stronglyMeasurable
  · intro t
    exact integrable_finsetSum _ fun i _ => (hx_int t i).const_mul (μ i)
  · intro t s hs
    obtain ⟨B, hB, rfl⟩ := hs
    show ∫ U in Peer82L2.past t ⁻¹' B, ∑ i, μ i * beliefAct id ε W x1 U t i ∂coinLaw m =
      ∫ U in Peer82L2.past t ⁻¹' B, ∑ i, μ i * beliefAct id ε W x1 U (t + 1) i ∂coinLaw m
    have hfreeze : ∀ j, ∫ U in Peer82L2.past t ⁻¹' B,
        actOf id (U t j) (beliefAct id ε W x1 U t j) ∂coinLaw m =
          ∫ U in Peer82L2.past t ⁻¹' B, beliefAct id ε W x1 U t j ∂coinLaw m := fun j =>
      Peer82L2.freeze t j (Peer82L2.measurable_beliefAct_extend ε W x1 t j)
        (fun _ => hxI _ t j) hB (fun U => congrFun (Peer82L2.beliefAct_eq_extend ε W x1 t U) j)
    have hM_int : Integrable (fun U : Coins m => ∑ i, μ i * beliefAct id ε W x1 U t i)
        (coinLaw m) :=
      integrable_finsetSum _ fun i _ => (hx_int t i).const_mul (μ i)
    have hA_int : Integrable
        (fun U : Coins m => ∑ j, μ j * actOf id (U t j) (beliefAct id ε W x1 U t j))
        (coinLaw m) :=
      integrable_finsetSum _ fun j _ => (ha_int t j).const_mul (μ j)
    have hdrift : ∀ U : Coins m, ∑ i, μ i * beliefAct id ε W x1 U (t + 1) i =
        (1 - ε) * ∑ i, μ i * beliefAct id ε W x1 U t i +
          ε * ∑ j, μ j * actOf id (U t j) (beliefAct id ε W x1 U t j) :=
      fun U => Peer82L2.drift W μ hμW ε x1 U t
    have hstep : ∫ U in Peer82L2.past t ⁻¹' B,
        ∑ i, μ i * beliefAct id ε W x1 U (t + 1) i ∂coinLaw m =
          (1 - ε) * ∫ U in Peer82L2.past t ⁻¹' B,
              ∑ i, μ i * beliefAct id ε W x1 U t i ∂coinLaw m +
            ε * ∫ U in Peer82L2.past t ⁻¹' B,
              ∑ j, μ j * actOf id (U t j) (beliefAct id ε W x1 U t j) ∂coinLaw m := by
      simp_rw [hdrift]
      rw [integral_add (hM_int.const_mul (1 - ε)).integrableOn (hA_int.const_mul ε).integrableOn,
        integral_const_mul, integral_const_mul]
    rw [hstep, Peer82L2.setIntegral_wsum μ (ha_int t), Peer82L2.setIntegral_wsum μ (hx_int t)]
    simp only [hfreeze]
    ring

end NaiveLearn.OverMatch

end Prove2NaiveLearnSubmission

open _root_.NaiveLearn.OverMatch

theorem solution {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) :
    Martingale (fun t U => ∑ i, μ i * beliefAct id ε W x1 U t i) (coinFiltration m)
      (coinLaw m) := by
  exact _root_.Prove2NaiveLearnSubmission.NaiveLearn.OverMatch.lemma_2 W μ hW hμ ε hε x1 hx1
