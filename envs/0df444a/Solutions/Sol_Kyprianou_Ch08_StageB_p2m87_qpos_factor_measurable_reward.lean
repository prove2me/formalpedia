-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_factor_measurable_reward
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T06:01:50.611057+00:00
-- url     : https://prove2.me/submissions/e468bc2a-6185-4126-8a6b-ea44ab968b6d

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

namespace P2m87MeasurableRewardAux

/-- dyadic upper approximation of a time -/
noncomputable def dy (n : ℕ) (s : ℝ≥0) : ℝ≥0 := (⌈(2 : ℝ) ^ n * (s : ℝ)⌉₊ : ℝ≥0) / 2 ^ n

theorem dy_coe (n : ℕ) (s : ℝ≥0) :
    ((dy n s : ℝ≥0) : ℝ) = (⌈(2 : ℝ) ^ n * (s : ℝ)⌉₊ : ℝ) / 2 ^ n := by
  simp [dy]

theorem le_dy (n : ℕ) (s : ℝ≥0) : s ≤ dy n s := by
  rw [← NNReal.coe_le_coe, dy_coe, le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

theorem dy_le (n : ℕ) (s : ℝ≥0) : (dy n s : ℝ) ≤ s + 1 / 2 ^ n := by
  rw [dy_coe, div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity),
    mul_comm]
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem tendsto_dy (s : ℝ≥0) : Tendsto (fun n => dy n s) atTop (𝓝[≥] s) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => le_dy n s⟩
  rw [← NNReal.tendsto_coe]
  have h1 : Tendsto (fun n : ℕ => (s : ℝ) + 1 / 2 ^ n) atTop (𝓝 (s : ℝ)) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have he : (fun n : ℕ => (s : ℝ) + 1 / 2 ^ n) = fun n => (s : ℝ) + (1 / 2) ^ n := by
      funext n; rw [one_div_pow]
    rw [he]
    simpa using tendsto_const_nhds.add h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun n => NNReal.coe_le_coe.mpr (le_dy n s)) (fun n => dy_le n s)

theorem measurable_eval_dy (n : ℕ) :
    Measurable (fun p : (ℝ≥0 → ℝ) × ℝ≥0 => p.1 (dy n p.2)) := by
  have h1 : Measurable (fun q : (ℝ≥0 → ℝ) × ℕ => q.1 ((q.2 : ℝ≥0) / 2 ^ n)) :=
    measurable_from_prod_countable_left (fun k =>
      show Measurable fun x : ℝ≥0 → ℝ => x ((k : ℝ≥0) / 2 ^ n) from measurable_pi_apply _)
  have h2 : Measurable (fun p : (ℝ≥0 → ℝ) × ℝ≥0 => (p.1, ⌈(2 : ℝ) ^ n * (p.2 : ℝ)⌉₊)) :=
    measurable_fst.prodMk ((measurable_const.mul (measurable_coe_nnreal_real.comp
      measurable_snd)).nat_ceil)
  exact h1.comp h2

/-- measurable right-continuous regularisation of a path -/
noncomputable def Y (p : (ℝ≥0 → ℝ) × ℝ≥0) : ℝ := limsup (fun n => p.1 (dy n p.2)) atTop

theorem measurable_Y : Measurable Y := Measurable.limsup measurable_eval_dy

theorem Y_eq (y : ℝ≥0 → ℝ) (hy : ∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) (s : ℝ≥0) :
    Y (y, s) = y s :=
  ((hy s).tendsto.comp (tendsto_dy s)).limsup_eq

/-- countable description of "before the first passage below zero" -/
def B (a : ℝ) (p : (ℝ≥0 → ℝ) × ℝ≥0) : Prop :=
  ∃ r : ℚ, (p.2 : ℝ) < r ∧ ∀ u : ℚ, 0 < u → u < r → 0 ≤ a + p.1 (Real.toNNReal u)

theorem measurableSet_B (a : ℝ) : MeasurableSet {p | B a p} := by
  simp only [B, Set.setOf_exists]
  refine MeasurableSet.iUnion fun r => ?_
  rw [Set.setOf_and]
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt (measurable_coe_nnreal_real.comp measurable_snd) measurable_const
  · simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun u => ?_
    by_cases h : 0 < u ∧ u < r
    · simp only [h.1, h.2, Set.iInter_true]
      exact measurableSet_le measurable_const
        (measurable_const.add (show Measurable fun p : (ℝ≥0 → ℝ) × ℝ≥0 => p.1 (Real.toNNReal u) from
          (measurable_pi_apply _).comp measurable_fst))
    · have : ¬ (0 < u) ∨ ¬ (u < r) := not_and_or.mp h
      rcases this with h' | h'
      · simp [h']
      · simp [h']

theorem lt_tauMinus_iff (a : ℝ) (y : ℝ≥0 → ℝ)
    (hy : ∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) (s : ℝ≥0) :
    (s : WithTop ℝ≥0) < tauMinus (fun u (_ : PUnit) => a + y u) 0 () ↔ B a (y, s) := by
  unfold tauMinus
  constructor
  · intro h
    obtain ⟨c, hsc, hc⟩ := exists_between h
    have hcTop : c ≠ ⊤ := ne_top_of_lt hc
    lift c to ℝ≥0 using hcTop
    have hsc' : (s : ℝ) < c := by exact_mod_cast WithTop.coe_lt_coe.mp hsc
    obtain ⟨r, hsr, hrc⟩ := exists_rat_btwn hsc'
    refine ⟨r, hsr, fun u hu0 hur => ?_⟩
    by_contra hneg
    push_neg at hneg
    have hmem : ((Real.toNNReal u : ℝ≥0) : WithTop ℝ≥0) ∈ {t : WithTop ℝ≥0 | ∃ v : ℝ≥0,
        0 < v ∧ (v : WithTop ℝ≥0) = t ∧ a + y v < 0} :=
      ⟨Real.toNNReal u, by simpa using hu0, rfl, hneg⟩
    have h1 := (sInf_le hmem).trans_lt' hc
    have h2 : Real.toNNReal u < c := by
      rw [Real.toNNReal_lt_iff_lt_coe (by positivity : (0:ℝ) ≤ u)]
      exact (by exact_mod_cast hur : (u : ℝ) < r).trans hrc
    exact absurd (WithTop.coe_lt_coe.mp h1) (not_lt.mpr h2.le)
  · rintro ⟨r, hsr, hr⟩
    have hle : ((Real.toNNReal r : ℝ≥0) : WithTop ℝ≥0) ≤ sInf {t : WithTop ℝ≥0 | ∃ v : ℝ≥0,
        0 < v ∧ (v : WithTop ℝ≥0) = t ∧ a + y v < 0} := by
      refine le_sInf ?_
      rintro t ⟨v, hv0, rfl, hneg⟩
      rw [WithTop.coe_le_coe]
      by_contra hlt
      push_neg at hlt
      have hvr : (v : ℝ) < r := by
        have := (Real.lt_toNNReal_iff_coe_lt).mp hlt
        exact this
      have hev : ∀ᶠ w in 𝓝[≥] v, a + y w < 0 :=
        (hy v).eventually ((continuous_const.add continuous_id).continuousAt.eventually
          (gt_mem_nhds hneg)) |>.mono fun w hw => hw
      obtain ⟨w, hvw, hw⟩ := (mem_nhdsGE_iff_exists_Ico_subset.mp hev)
      have hvw' : (v : ℝ) < min (w : ℝ) r := lt_min (by exact_mod_cast hvw) hvr
      obtain ⟨u, hvu, hum⟩ := exists_rat_btwn hvw'
      have hu0 : (0 : ℝ) < u := (NNReal.coe_nonneg v).trans_lt hvu
      have hmem : Real.toNNReal u ∈ Set.Ico v w := by
        constructor
        · rw [Real.le_toNNReal_iff_coe_le hu0.le]; exact hvu.le
        · rw [Real.toNNReal_lt_iff_lt_coe hu0.le]; exact hum.trans_le (min_le_left _ _)
      have := hr u (by exact_mod_cast hu0) (by exact_mod_cast hum.trans_le (min_le_right _ _))
      exact absurd (hw hmem) (not_lt.mpr this)
    refine lt_of_lt_of_le ?_ hle
    rw [WithTop.coe_lt_coe]
    exact Real.lt_toNNReal_iff_coe_lt.mpr hsr

end P2m87MeasurableRewardAux

open P2m87MeasurableRewardAux in
theorem solution
    (q a : ℝ) (ha : 0 < a) (A : Set ℝ) (hA : MeasurableSet A) :
    ∃ reward : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable reward ∧
      ∀ (y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) →
        y 0 = 0 →
        reward y =
          (∫⁻ s : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
            (if (s : WithTop ℝ≥0) <
                  tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧
                a + y s ∈ A
             then (1 : ℝ≥0∞) else 0) ∂positiveTimeLebesgue) := by
  let F : (ℝ≥0 → ℝ) × ℝ≥0 → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-q * (p.2 : ℝ))) *
      (if B a p ∧ a + Y p ∈ A then (1 : ℝ≥0∞) else 0)
  have : SFinite positiveTimeLebesgue := by unfold positiveTimeLebesgue; infer_instance
  have hF : Measurable F := by
    refine Measurable.mul ?_ (Measurable.ite ?_ measurable_const measurable_const)
    · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (measurable_coe_nnreal_real.comp measurable_snd)))
    · rw [Set.setOf_and]
      exact (measurableSet_B a).inter ((measurable_const.add measurable_Y) hA)
  refine ⟨fun y => ∫⁻ s, F (y, s) ∂positiveTimeLebesgue, hF.lintegral_prod_right', ?_⟩
  intro y hy _
  refine lintegral_congr fun s => ?_
  simp only [F]
  congr 1
  exact if_congr (and_congr (lt_tauMinus_iff a y hy s).symm (by rw [Y_eq y hy s])) rfl rfl
