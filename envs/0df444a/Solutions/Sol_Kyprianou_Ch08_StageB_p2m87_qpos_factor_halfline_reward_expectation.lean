-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_factor_halfline_reward_expectation
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T06:05:24.403617+00:00
-- url     : https://prove2.me/submissions/88110f91-c4e8-40db-9b65-489948a06873

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

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


/-- jointly measurable integrand -/
noncomputable def Fint (q a : ℝ) (A : Set ℝ) (p : (ℝ≥0 → ℝ) × ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-q * (p.2 : ℝ))) *
    (if B a p ∧ a + Y p ∈ A then (1 : ℝ≥0∞) else 0)

theorem measurableSet_BY (a : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet {p : (ℝ≥0 → ℝ) × ℝ≥0 | B a p ∧ a + Y p ∈ A} := by
  rw [Set.setOf_and]
  exact (measurableSet_B a).inter ((measurable_const.add measurable_Y) hA)

theorem measurable_Fint (q a : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable (Fint q a A) := by
  refine Measurable.mul ?_ (Measurable.ite (measurableSet_BY a hA) measurable_const
    measurable_const)
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (measurable_coe_nnreal_real.comp measurable_snd)))

theorem Fint_eq (q a : ℝ) (A : Set ℝ) (y : ℝ≥0 → ℝ)
    (hy : ∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) (s : ℝ≥0) :
    Fint q a A (y, s) = ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
      (if (s : WithTop ℝ≥0) < tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧ a + y s ∈ A
        then (1 : ℝ≥0∞) else 0) := by
  simp only [Fint]
  congr 1
  exact if_congr (and_congr (lt_tauMinus_iff a y hy s).symm (by rw [Y_eq y hy s])) rfl rfl

end P2m87MeasurableRewardAux

open P2m87MeasurableRewardAux in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hreward : Measurable reward)
    (hreward_value : ∀ (y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) → y 0 = 0 →
        reward y =
          (∫⁻ s : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
            (if (s : WithTop ℝ≥0) <
                  tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧
                a + y s ∈ A
             then (1 : ℝ≥0∞) else 0) ∂positiveTimeLebesgue)) :
    (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) =
      ∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
          shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue := by
  have hSF : SFinite positiveTimeLebesgue := by unfold positiveTimeLebesgue; infer_instance
  let path : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hpathm : Measurable path :=
    measurable_pi_lambda _ (fun t => (X.adapted t).mono (F.le t) le_rfl)
  have hrc : ∀ ω, ∀ t : ℝ≥0, ContinuousWithinAt (path ω) (Set.Ici t) t :=
    fun ω t => X.rightCont ω t
  -- step 1: rewrite the reward with the measurable integrand
  have h1 : (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) =
      ∫⁻ ω, ∫⁻ s, Fint q a A (path ω, s) ∂positiveTimeLebesgue ∂P := by
    refine lintegral_congr fun ω => ?_
    rw [hreward_value (path ω) (hrc ω) (X.X_zero ω)]
    exact lintegral_congr fun s => (Fint_eq q a A (path ω) (hrc ω) s).symm
  -- step 2: Tonelli
  have hjoint : Measurable (Function.uncurry fun ω s => Fint q a A (path ω, s)) :=
    (measurable_Fint q a hA).comp ((hpathm.comp measurable_fst).prodMk measurable_snd)
  rw [h1, lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun s => ?_
  -- step 3: compute the inner integral
  let S : Set Ω := {ω | B a (path ω, s) ∧ a + Y (path ω, s) ∈ A}
  have hS : MeasurableSet S :=
    (hpathm.prodMk measurable_const) (measurableSet_BY a hA)
  have hin : (fun ω => Fint q a A (path ω, s)) =
      fun ω => ENNReal.ofReal (Real.exp (-q * (s : ℝ))) * S.indicator 1 ω := by
    funext ω
    simp only [Fint, Set.indicator_apply, S, Set.mem_setOf_eq, Pi.one_apply]
  rw [hin, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one hS]
  congr 1
  refine measure_congr ?_
  filter_upwards [hpath] with ω hω
  have hpe : path ω = fun t => D.X t ω := funext hω
  change (ω ∈ S) = (ω ∈ {ω | (s : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
      shifted D.X a s ω ∈ A})
  simp only [S, Set.mem_setOf_eq]
  rw [← lt_tauMinus_iff a (path ω) (hrc ω) s, Y_eq (path ω) (hrc ω) s, hpe]
  rfl
