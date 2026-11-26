-- Prove2me | solution 1 for ManyServerQED.Scheduling.poisson_path_laws_with_matched_time_scales
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:47:08.837248+00:00
-- url     : https://prove2.me/submissions/65a0bbf1-354a-4b0c-a03c-5c3ab80d87b4

import Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
import Definitions.Def_ManyServerQED_Scheduling_Model

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

private theorem count_increment_nat {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    (ω : Ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ j : ℕ, N ω t - N ω s = j := by
  obtain ⟨a, ha⟩ := hN.nat_valued ω s hs
  obtain ⟨b, hb⟩ := hN.nat_valued ω t (hs.trans hst)
  have hab : a ≤ b := by
    exact_mod_cast (show (a : ℝ) ≤ (b : ℝ) from ha ▸ hb ▸ hN.mono ω hs (hs.trans hst) hst)
  exact ⟨b - a, by rw [ha, hb, Nat.cast_sub hab]⟩

private theorem nat_floor_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    (ω : Ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (⌊N ω t - N ω s⌋₊ : ℝ) = N ω t - N ω s := by
  obtain ⟨j, hj⟩ := count_increment_nat hN ω hs hst
  rw [hj, Nat.floor_natCast]

private theorem map_floor_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Measure.map (fun ω => ⌊N ω t - N ω s⌋₊) P = poissonMeasure (rate * (t - s)).toNNReal := by
  apply Measure.ext_of_singleton
  intro j
  have hm : Measurable (fun ω => ⌊N ω t - N ω s⌋₊) := ((hN.meas t).sub (hN.meas s)).nat_floor
  rw [Measure.map_apply hm (measurableSet_singleton j)]
  convert hN.law s t hs hst j using 2
  ext ω
  change ⌊N ω t - N ω s⌋₊ = j ↔ N ω t - N ω s = j
  constructor
  · intro h
    rw [← nat_floor_increment hN ω hs hst, h]
  · intro h
    rw [h, Nat.floor_natCast]

open ManyServerQED.Scheduling

private theorem poisson_grid_telescopes
    {n : ℕ} {J : Finset ℝ≥0} (t : ℕ → ℝ≥0) (e : J → Fin n)
    (ht0 : t 0 = 0) (he : ∀ j : J, t ((e j).val+1) = j.val)
    {A : Type*} (Q : A → ℝ → ℝ) (h0 : ∀ ω, Q ω 0 = 0) (a : ℝ) (ω : A) (j : J) :
      (∑ i ∈ Finset.range ((e j).val+1), if h : i < n then
        Q ω (a * (t ((⟨i,h⟩ : Fin n).val+1):ℝ)) - Q ω (a * (t (⟨i,h⟩ : Fin n).val:ℝ))
        else 0) =
        Q ω (a * (j.val:ℝ≥0)) := by
  rw [show (∑ i ∈ Finset.range ((e j).val + 1),
        if h : i < n then Q ω (a * (t (i+1):ℝ)) - Q ω (a * (t i:ℝ)) else 0) =
          ∑ i ∈ Finset.range ((e j).val + 1),
            (Q ω (a * (t (i+1):ℝ)) - Q ω (a * (t i:ℝ))) from
      Finset.sum_congr rfl (fun i hi => if_pos
        ((Finset.mem_range.1 hi).trans_le (Nat.succ_le_of_lt (e j).2)))]
  rw [Finset.sum_range_sub (fun i => Q ω (a * (t i:ℝ))), ht0, he j]
  simp [h0]

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (N : Ω → ℝ → ℝ) (N' : Ω' → ℝ → ℝ) (a b c d : ℝ)
    (hN : IsPoissonProcess P N a) (hN' : IsPoissonProcess P' N' b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hMatch : a * c = b * d) :
    IdentDistrib (fun ω (t : ℝ≥0) => N ω (c*t)) (fun ω (t : ℝ≥0) => N' ω (d*t)) P P' := by
  classical
  let Y (ω : Ω) (t : ℝ≥0) := N ω (c*t)
  let Z (ω : Ω') (t : ℝ≥0) := N' ω (d*t)
  have hy : Measurable Y := measurable_pi_lambda _ (fun _ => hN.meas _)
  have hz : Measurable Z := measurable_pi_lambda _ (fun _ => hN'.meas _)
  refine ⟨hy.aemeasurable,hz.aemeasurable,?_⟩
  have hu : Measure.map Y P univ = Measure.map Z P' univ := by
    rw [Measure.map_apply hy MeasurableSet.univ, Measure.map_apply hz MeasurableSet.univ]
    simp
  refine ext_of_generate_finite (measurableCylinders _) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun C hC => ?_) hu
  obtain ⟨J, B, hB, rfl⟩ := (mem_measurableCylinders C).mp hC
  obtain ⟨n, t, e, ht, ht0, he⟩ := AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid J
  let Dy (i : Fin n) (ω : Ω) := N ω (c * (t (i.val + 1) : ℝ)) - N ω (c * (t i.val : ℝ))
  let Dz (i : Fin n) (ω : Ω') := N' ω (d * (t (i.val + 1) : ℝ)) - N' ω (d * (t i.val : ℝ))
  have hcM : Monotone (fun i : ℕ => c * (t i : ℝ)) :=
    fun _ _ hij => mul_le_mul_of_nonneg_left (by exact_mod_cast ht hij) hc
  have hdM : Monotone (fun i : ℕ => d * (t i : ℝ)) :=
    fun _ _ hij => mul_le_mul_of_nonneg_left (by exact_mod_cast ht hij) hd
  have hiY : iIndepFun Dy P := hN.indep_incr n (fun i => c * (t i.val : ℝ))
    (mul_nonneg hc (t 0).2) (fun i j h => hcM h)
  have hiZ : iIndepFun Dz P' := hN'.indep_incr n (fun i => d * (t i.val : ℝ))
    (mul_nonneg hd (t 0).2) (fun i j h => hdM h)
  have hDelta (i : Fin n) : IdentDistrib (Dy i) (Dz i) P P' := by
    have h₁ := mul_nonneg hc (t i.val).2
    have h₂ := mul_nonneg hd (t i.val).2
    have hs := hcM (Nat.le_succ i.val)
    have hs' := hdM (Nat.le_succ i.val)
    have hmap := (map_floor_increment hN h₁ hs).trans
      (Eq.trans ?h (map_floor_increment hN' h₂ hs').symm)
    case h =>
      congr 1
      congr 1
      rw [← mul_sub,← mul_sub,← mul_assoc,← mul_assoc,hMatch]
    have hDy : Measurable (Dy i) := (hN.meas _).sub (hN.meas _)
    have hDz : Measurable (Dz i) := (hN'.meas _).sub (hN'.meas _)
    have hId : IdentDistrib (fun ω => ⌊Dy i ω⌋₊) (fun ω => ⌊Dz i ω⌋₊) P P' :=
      ⟨hDy.nat_floor.aemeasurable,hDz.nat_floor.aemeasurable,hmap⟩
    have hCast := hId.comp (measurable_of_countable (fun z : ℕ => (z:ℝ)))
    refine ⟨hDy.aemeasurable,hDz.aemeasurable,?_⟩
    exact (Measure.map_congr (ae_of_all _ (fun ω => (nat_floor_increment hN ω h₁ hs).symm))).trans
      (hCast.map_eq.trans (Measure.map_congr (ae_of_all _ (fun ω => nat_floor_increment hN' ω h₂ hs'))))
  let proj (v : Fin n → ℝ) (j : J) :=
    ∑ i ∈ Finset.range ((e j).val+1), if h : i < n then v ⟨i,h⟩ else 0
  have hp : Measurable proj := by
    apply measurable_pi_lambda
    intro j
    apply Finset.measurable_sum
    intro i hi
    split_ifs with h
    · exact measurable_pi_apply (⟨i,h⟩ : Fin n)
    · exact measurable_const
  have hId := (IdentDistrib.pi hDelta hiY hiZ).comp hp
  have hYP : proj ∘ (fun ω i => Dy i ω) = fun ω => J.restrict (Y ω) :=
    funext fun ω => funext fun j => poisson_grid_telescopes t e ht0 he N hN.zero c ω j
  have hZP : proj ∘ (fun ω i => Dz i ω) = fun ω => J.restrict (Z ω) :=
    funext fun ω => funext fun j => poisson_grid_telescopes t e ht0 he N' hN'.zero d ω j
  rw [hYP,hZP] at hId
  rw [Measure.map_apply hy hB.cylinder,Measure.map_apply hz hB.cylinder]
  exact hId.measure_mem_eq hB
