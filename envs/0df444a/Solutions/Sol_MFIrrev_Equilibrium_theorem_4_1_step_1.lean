-- Prove2me | solution 1 for MFIrrev.Equilibrium.theorem_4_1_step_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:02:32.783958+00:00
-- url     : https://prove2.me/submissions/7a70636f-830d-4855-af93-f7019228744f

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_StoppingProblem

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrevStep1Aux
open MFIrrev.Equilibrium

/-- right grid point `(k+1)/(n+1)` -/
noncomputable def kk (n k : ℕ) : ℝ≥0 := Real.toNNReal (((k : ℝ) + 1) / ((n : ℝ) + 1))

/-- grid index of `t` -/
noncomputable def fl (n : ℕ) (t : ℝ) : ℕ := ⌊((n : ℝ) + 1) * t⌋₊

lemma kk_fl_bounds (n : ℕ) (t : ℝ) :
    ((t.toNNReal : ℝ≥0) : ℝ) < kk n (fl n t) ∧
      (kk n (fl n t) : ℝ) ≤ (t.toNNReal : ℝ) + 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfl : fl n t = ⌊((n : ℝ) + 1) * (t.toNNReal : ℝ)⌋₊ := by
    unfold fl
    rcases le_or_gt 0 t with ht | ht
    · rw [Real.coe_toNNReal _ ht]
    · rw [Real.toNNReal_of_nonpos ht.le, NNReal.coe_zero, mul_zero, Nat.floor_zero]
      exact Nat.floor_of_nonpos (by nlinarith)
  set u : ℝ := (t.toNNReal : ℝ) with hu
  have hu0 : 0 ≤ u := NNReal.coe_nonneg _
  have hpos : 0 ≤ (((fl n t : ℕ) : ℝ) + 1) / ((n : ℝ) + 1) := by positivity
  unfold kk
  rw [Real.coe_toNNReal _ hpos, hfl]
  have h1 := Nat.lt_floor_add_one (((n : ℝ) + 1) * u)
  have h2 := Nat.floor_le (mul_nonneg hn.le hu0)
  constructor
  · rw [lt_div_iff₀ hn]; linarith
  · rw [div_le_iff₀ hn]
    have : (u + 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * u + 1 := by
      field_simp
    rw [this]; linarith

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

lemma eps_eventually (S : Setting Ω)
    (hR : ∀ (ω : Ω) (t : ℝ≥0), ∃ h : ℝ≥0, 0 < h ∧ ∀ s, t ≤ s → s < t + h → S.ε s ω = S.ε t ω)
    (t : ℝ) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, S.ε (kk n (fl n t)) ω = S.ε t.toNNReal ω := by
  obtain ⟨h, hh, hc⟩ := hR ω t.toNNReal
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show (0 : ℝ) < h from hh)
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨b1, b2⟩ := kk_fl_bounds n t
  apply hc
  · exact le_of_lt (by exact_mod_cast b1)
  · have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have : (kk n (fl n t) : ℝ) < (t.toNNReal : ℝ) + (h : ℝ) := by linarith
    exact_mod_cast this

lemma epsG_meas (S : Setting Ω) (hA : ∀ t, Measurable[S.ℱ t] (S.ε t))
    (hR : ∀ (ω : Ω) (t : ℝ≥0), ∃ h : ℝ≥0, 0 < h ∧ ∀ s, t ≤ s → s < t + h → S.ε s ω = S.ε t ω)
    (g : Fin 2 → ℝ) : Measurable (fun p : ℝ × Ω => g (S.ε p.1.toNNReal p.2)) := by
  have hmeas : ∀ n : ℕ, Measurable (fun p : ℝ × Ω => g (S.ε (kk n (fl n p.1)) p.2)) := by
    intro n
    have h1 : Measurable (fun q : ℕ × Ω => g (S.ε (kk n q.1) q.2)) := by
      refine measurable_from_prod_countable_right
        (f := fun q : ℕ × Ω => g (S.ε (kk n q.1) q.2)) (fun k => ?_)
      have hk : Measurable (S.ε (kk n k)) := (hA (kk n k)).mono (S.ℱ.le (kk n k)) le_rfl
      exact (measurable_of_countable g).comp hk
    have h2 : Measurable (fun p : ℝ × Ω => (fl n p.1, p.2)) := by
      refine Measurable.prodMk ?_ measurable_snd
      unfold fl
      exact Nat.measurable_floor.comp ((measurable_const.mul measurable_id).comp measurable_fst)
    exact Measurable.comp (g := fun q : ℕ × Ω => g (S.ε (kk n q.1) q.2))
      (f := fun p : ℝ × Ω => (fl n p.1, p.2)) h1 h2
  refine measurable_of_tendsto_metrizable hmeas ?_
  rw [tendsto_pi_nhds]
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [eps_eventually S hR p.1 p.2] with n hn
  simp [hn]

lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hf.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x

lemma M_meas (m : Params) (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S) (t : ℝ≥0) :
    Measurable (S.M t) := by
  obtain ⟨hP, hcomp, hB, hchain, -, -, -, hito, -, -⟩ := hS
  have := hcomp
  obtain ⟨a, ha, -, -, hJ⟩ := hito.2 t
  have : AEMeasurable (S.M t) P := by
    refine hJ.aemeasurable (fun n => ?_)
    unfold EthierKurtz.itoStepSum
    refine Finset.aemeasurable_fun_sum _ (fun k hk => ?_)
    have hk' : k < 2 ^ n := Finset.mem_range.1 hk
    exact ((ha n k hk').mono (S.ℱ.le _) le_rfl).aemeasurable.mul
      ((hB.toIsPreBrownianReal.aemeasurable _).sub (hB.toIsPreBrownianReal.aemeasurable _))
  exact aemeasurable_iff_measurable.1 this


section Part2
variable (m : Params) (P : Measure Ω) (S : Setting Ω)

/-- bundled regularity facts extracted from `IsSetting` -/
structure Reg : Prop where
  adapt : ∀ t, Measurable[S.ℱ t] (S.ε t)
  rc : ∀ (ω : Ω) (t : ℝ≥0), ∃ h : ℝ≥0, 0 < h ∧ ∀ s, t ≤ s → s < t + h → S.ε s ω = S.ε t ω
  Mmeas : ∀ t, Measurable (S.M t)
  Mcont : ∀ ω, Continuous fun t => S.M t ω

lemma reg_of (hS : IsSetting m P S) : Reg S :=
  ⟨hS.2.2.2.1.1, hS.2.2.2.1.2.1, M_meas m P S hS, hS.2.2.2.2.2.2.2.2.1⟩

variable {S}

lemma epsG_path (hR : Reg S) (g : Fin 2 → ℝ) (ω : Ω) :
    Measurable (fun t : ℝ => g (S.ε t.toNNReal ω)) :=
  (epsG_meas S hR.adapt hR.rc g).comp (measurable_id.prodMk measurable_const)

lemma epsG_bdd (g : Fin 2 → ℝ) (j : Fin 2) : |g j| ≤ |g 0| + |g 1| := by
  fin_cases j <;> simp [abs_nonneg]

lemma sigSq_ii (hR : Reg S) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => m.σ (S.ε s.toNNReal ω) ^ 2) volume a b :=
  intervalIntegrable_of_bdd (epsG_path hR (fun j => m.σ j ^ 2) ω) _
    (fun x => epsG_bdd (fun j => m.σ j ^ 2) _) a b

lemma sigSqInt_cont (hR : Reg S) (ω : Ω) : Continuous fun t : ℝ≥0 => sigSqInt m S t ω := by
  unfold sigSqInt
  exact (intervalIntegral.continuous_primitive (sigSq_ii m hR ω) 0).comp NNReal.continuous_coe

lemma sigSqInt_meas (hR : Reg S) (t : ℝ≥0) : Measurable fun ω => sigSqInt m S t ω := by
  unfold sigSqInt
  simp_rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  have hsm : StronglyMeasurable (Function.uncurry fun (ω : Ω) (s : ℝ) => m.σ (S.ε s.toNNReal ω) ^ 2) :=
    ((epsG_meas S hR.adapt hR.rc (fun j => m.σ j ^ 2)).comp measurable_swap).stronglyMeasurable
  exact (hsm.integral_prod_right (ν := volume.restrict (Ioc (0 : ℝ) t))).measurable

lemma Xbar_cont (hR : Reg S) (x : ℝ) (ω : Ω) : Continuous fun t : ℝ≥0 => Xbar m S x t ω := by
  unfold Xbar
  have := sigSqInt_cont m hR ω
  have := hR.Mcont ω
  fun_prop

lemma Xbar_meas (hR : Reg S) (x : ℝ) : Measurable fun p : ℝ≥0 × Ω => Xbar m S x p.1 p.2 := by
  have h := measurable_uncurry_of_continuous_of_measurable (u := fun t ω => Xbar m S x t ω)
    (Xbar_cont m hR x) (fun t => by
      unfold Xbar
      have := sigSqInt_meas m hR t
      have := hR.Mmeas t
      fun_prop)
  exact h

lemma runCost_meas (hR : Reg S) (Q : Fin 2 → ℝ) (x : ℝ) :
    Measurable fun p : ℝ × Ω => runCost m S Q x p.1 p.2 := by
  unfold runCost
  have h1 := epsG_meas S hR.adapt hR.rc (eta m Q)
  have h2 := (Xbar_meas m hR x).comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
    (h1.sub (measurable_const.mul h2))

lemma runCost_path_meas (hR : Reg S) (Q : Fin 2 → ℝ) (x : ℝ) (ω : Ω) :
    Measurable fun t : ℝ => runCost m S Q x t ω :=
  (runCost_meas m hR Q x).comp (measurable_id.prodMk measurable_const)

lemma runCost_ii (hR : Reg S) (Q : Fin 2 → ℝ) (x : ℝ) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun t => runCost m S Q x t ω) volume a b := by
  unfold runCost
  have hc : Continuous fun t : ℝ => Xbar m S x t.toNNReal ω :=
    (Xbar_cont m hR x ω).comp continuous_real_toNNReal
  have h1 : IntervalIntegrable (fun t : ℝ => eta m Q (S.ε t.toNNReal ω)) volume a b :=
    intervalIntegrable_of_bdd (epsG_path hR (eta m Q) ω) _ (fun _ => epsG_bdd _ _) a b
  have h2 : IntervalIntegrable (fun t : ℝ => 2 * m.c * Xbar m S x t.toNNReal ω) volume a b :=
    (continuous_const.mul hc).intervalIntegrable a b
  exact (h1.sub h2).continuousOn_mul (by fun_prop)

end Part2

section Part3
variable (m : Params) {S : Setting Ω}

lemma runCost_sub (Q Q' : Fin 2 → ℝ) (x t : ℝ) (ω : Ω) :
    runCost m S Q x t ω - runCost m S Q' x t ω
      = Real.exp (-(m.ρ + m.δ) * t) * (eta m Q (S.ε t.toNNReal ω) - eta m Q' (S.ε t.toNNReal ω)) := by
  unfold runCost; ring

lemma path_bound (hR : Reg S) (Q Q' : Fin 2 → ℝ) (x : ℝ)
    (hD : ∀ j, 0 ≤ eta m Q j - eta m Q' j) (hc : 0 < m.ρ + m.δ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    stopPayoff m S Q' x τ ω ≤ stopPayoff m S Q x τ ω ∧
      stopPayoff m S Q x τ ω ≤ stopPayoff m S Q' x τ ω +
        (|eta m Q 0 - eta m Q' 0| + |eta m Q 1 - eta m Q' 1|) *
          ∫ t in Ioi (0 : ℝ), Real.exp (-(m.ρ + m.δ) * t) := by
  set Dg : Fin 2 → ℝ := fun j => eta m Q j - eta m Q' j with hDg
  set Dmax := |eta m Q 0 - eta m Q' 0| + |eta m Q 1 - eta m Q' 1| with hDmax
  set dd : ℝ → ℝ := fun t => Real.exp (-(m.ρ + m.δ) * t) * Dg (S.ε t.toNNReal ω) with hdd
  set E : ℝ → ℝ := fun t => Dmax * Real.exp (-(m.ρ + m.δ) * t) with hE
  have hdd_meas : Measurable dd :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul (epsG_path hR Dg ω)
  have hdd0 : ∀ t, 0 ≤ dd t := fun t => mul_nonneg (Real.exp_pos _).le (hD _)
  have hddE : ∀ t, dd t ≤ E t := by
    intro t
    have h1 : Dg (S.ε t.toNNReal ω) ≤ Dmax := by
      have := epsG_bdd Dg (S.ε t.toNNReal ω)
      have h2 := le_abs_self (Dg (S.ε t.toNNReal ω))
      simp only [hDg] at this h2 ⊢; linarith
    simp only [hdd, hE]
    rw [mul_comm Dmax]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hEint : IntegrableOn E (Ioi 0) := (exp_neg_integrableOn_Ioi 0 hc).const_mul Dmax
  have hddint : IntegrableOn dd (Ioi 0) := by
    refine Integrable.mono' hEint hdd_meas.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hdd0 t)]; exact hddE t
  have hEint_eq : ∫ t in Ioi (0 : ℝ), E t = Dmax * ∫ t in Ioi (0 : ℝ), Real.exp (-(m.ρ + m.δ) * t) :=
    integral_const_mul _ _
  have hE0 : ∀ t, 0 ≤ E t := fun t => le_trans (hdd0 t) (hddE t)
  have hIoi_le : ∫ t in Ioi (0 : ℝ), dd t ≤ ∫ t in Ioi (0 : ℝ), E t :=
    setIntegral_mono hddint hEint hddE
  have hIoi_nn : 0 ≤ ∫ t in Ioi (0 : ℝ), dd t := setIntegral_nonneg measurableSet_Ioi (fun t _ => hdd0 t)
  unfold stopPayoff
  cases hτ : τ ω with
  | top =>
    simp only
    by_cases hi : IntegrableOn (fun t => runCost m S Q x t ω) (Ioi 0)
    · have hi' : IntegrableOn (fun t => runCost m S Q' x t ω) (Ioi 0) := by
        refine (hi.sub hddint).congr_fun (fun t _ => ?_) measurableSet_Ioi
        have := runCost_sub m (S := S) Q Q' x t ω
        simp only [Pi.sub_apply, Pi.add_apply, hdd, hDg]; linarith
      have hsub : (∫ t in Ioi (0 : ℝ), runCost m S Q x t ω) - (∫ t in Ioi (0 : ℝ), runCost m S Q' x t ω)
          = ∫ t in Ioi (0 : ℝ), dd t := by
        rw [← integral_sub hi hi']
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        simp only [hdd, hDg]; rw [runCost_sub]
      constructor <;> linarith
    · have hi' : ¬ IntegrableOn (fun t => runCost m S Q' x t ω) (Ioi 0) := by
        intro hi'
        apply hi
        refine (hi'.add hddint).congr_fun (fun t _ => ?_) measurableSet_Ioi
        have := runCost_sub m (S := S) Q Q' x t ω
        simp only [Pi.sub_apply, Pi.add_apply, hdd, hDg]; linarith
      rw [integral_undef hi, integral_undef hi']
      have : 0 ≤ Dmax * ∫ t in Ioi (0 : ℝ), Real.exp (-(m.ρ + m.δ) * t) := by
        rw [← hEint_eq]; exact setIntegral_nonneg measurableSet_Ioi (fun t _ => hE0 t)
      constructor <;> linarith
  | coe s =>
    simp only
    have hsub : (∫ t in (0 : ℝ)..(s : ℝ), runCost m S Q x t ω)
        - ∫ t in (0 : ℝ)..(s : ℝ), runCost m S Q' x t ω = ∫ t in (0 : ℝ)..(s : ℝ), dd t := by
      rw [← intervalIntegral.integral_sub (runCost_ii m hR Q x ω 0 s) (runCost_ii m hR Q' x ω 0 s)]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp only [hdd, hDg]; rw [runCost_sub]
    have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..(s : ℝ), dd t :=
      intervalIntegral.integral_nonneg hs0 (fun t _ => hdd0 t)
    have hle : ∫ t in (0 : ℝ)..(s : ℝ), dd t ≤ ∫ t in Ioi (0 : ℝ), dd t := by
      rw [intervalIntegral.integral_of_le hs0]
      exact setIntegral_mono_set hddint (Eventually.of_forall fun t => hdd0 t)
        (Eventually.of_forall Ioc_subset_Ioi_self)
    constructor <;> linarith

lemma int_sandwich {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → ℝ} (hf : Measurable f)
    (hg : Measurable g) (K : ℝ) (hK : 0 ≤ K) (h1 : ∀ ω, f ω ≤ g ω) (h2 : ∀ ω, g ω ≤ f ω + K) :
    ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ ∧ ∫ ω, g ω ∂μ ≤ ∫ ω, f ω ∂μ + K * μ.real univ := by
  have bg : ∀ ω, ‖g ω‖ ≤ |f ω| + K := by
    intro ω; rw [Real.norm_eq_abs, abs_le]
    constructor <;> cases abs_cases (f ω) <;> linarith [h1 ω, h2 ω]
  have bf : ∀ ω, ‖f ω‖ ≤ |g ω| + K := by
    intro ω; rw [Real.norm_eq_abs, abs_le]
    constructor <;> cases abs_cases (g ω) <;> linarith [h1 ω, h2 ω]
  by_cases hfi : Integrable f μ
  · have hgi : Integrable g μ :=
      Integrable.mono' (hfi.abs.add (integrable_const K)) hg.aestronglyMeasurable
        (Eventually.of_forall bg)
    refine ⟨integral_mono hfi hgi h1, ?_⟩
    have h3 : ∫ ω, g ω ∂μ ≤ ∫ ω, (f ω + K) ∂μ := integral_mono hgi (hfi.add (integrable_const K)) h2
    have e : ∫ ω, (f ω + K) ∂μ = ∫ ω, f ω ∂μ + K * μ.real univ := by
      rw [integral_add hfi (integrable_const K), integral_const, smul_eq_mul, mul_comm]
    linarith
  · have hgi : ¬ Integrable g μ := by
      intro hgi
      exact hfi (Integrable.mono' (hgi.abs.add (integrable_const K)) hf.aestronglyMeasurable
        (Eventually.of_forall bf))
    rw [integral_undef hfi, integral_undef hgi]
    have : 0 ≤ K * μ.real univ := mul_nonneg hK measureReal_nonneg
    constructor <;> linarith

lemma iInf_sandwich {T : Type} [Nonempty T] (F G : T → ℝ) (K : ℝ) (h1 : ∀ τ, F τ ≤ G τ)
    (h2 : ∀ τ, G τ ≤ F τ + K) : ⨅ τ, F τ ≤ ⨅ τ, G τ := by
  by_cases hb : BddBelow (Set.range F)
  · exact ciInf_mono hb h1
  · have hb' : ¬ BddBelow (Set.range G) := by
      rintro ⟨b, hb2⟩
      apply hb
      refine ⟨b - K, ?_⟩
      rintro _ ⟨τ, rfl⟩
      have := hb2 ⟨τ, rfl⟩
      linarith [h2 τ]
    rw [Real.iInf_of_not_bddBelow hb, Real.iInf_of_not_bddBelow hb']

end Part3

section Part4
variable (m : Params) {S : Setting Ω}

lemma payoff_meas (hR : Reg S) (Q : Fin 2 → ℝ) (x : ℝ) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime S.ℱ τ) : Measurable (stopPayoff m S Q x τ) := by
  set A : Set Ω := {ω | τ ω = ⊤} with hA
  have hAeq : A = ⋂ n : ℕ, {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
    ext ω
    simp only [hA, mem_ofPred_eq, mem_iInter, mem_compl_iff]
    constructor
    · intro h n; rw [h]; exact not_le.2 (WithTop.coe_lt_top _)
    · intro h
      cases hω : τ ω with
      | top => rfl
      | coe s =>
        exfalso
        apply h ⌈s⌉₊
        rw [hω]
        exact_mod_cast Nat.le_ceil s
  have hAm : MeasurableSet A := by
    rw [hAeq]
    exact MeasurableSet.iInter fun n => (S.ℱ.le _ _ (hτ (n : ℝ≥0))).compl
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'
  have hτ'm : Measurable τ' := by
    refine measurable_of_Iic fun y => ?_
    have : τ' ⁻¹' Iic y = {ω | τ ω ≤ (y : WithTop ℝ≥0)} ∪ A := by
      ext ω
      simp only [hτ', hA, mem_preimage, mem_Iic, mem_union, mem_ofPred_eq]
      cases hω : τ ω with
      | top => simp
      | coe s => simp only [WithTop.untopD_coe, WithTop.coe_le_coe, WithTop.coe_ne_top, or_false]
    rw [this]
    exact (S.ℱ.le _ _ (hτ y)).union hAm
  -- the finite part
  set Ffin : ℝ≥0 → Ω → ℝ := fun s ω => (∫ t in (0 : ℝ)..(s : ℝ), runCost m S Q x t ω)
      + m.κ * Real.exp (-(m.ρ + m.δ) * (s : ℝ)) with hFfin
  have hrc_sm : StronglyMeasurable (Function.uncurry fun (ω : Ω) (t : ℝ) => runCost m S Q x t ω) :=
    ((runCost_meas m hR Q x).comp measurable_swap).stronglyMeasurable
  have hFfin_m : Measurable fun p : ℝ≥0 × Ω => Ffin p.1 p.2 := by
    refine measurable_uncurry_of_continuous_of_measurable (u := Ffin) (fun ω => ?_) (fun s => ?_)
    · simp only [hFfin]
      have := (intervalIntegral.continuous_primitive (runCost_ii m hR Q x ω) 0).comp
        NNReal.continuous_coe
      exact this.add (by fun_prop)
    · simp only [hFfin]
      refine Measurable.add ?_ measurable_const
      simp_rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg s)]
      exact (hrc_sm.integral_prod_right (ν := volume.restrict (Ioc (0 : ℝ) s))).measurable
  have hFtop_m : Measurable fun ω => ∫ t in Ioi (0 : ℝ), runCost m S Q x t ω :=
    (hrc_sm.integral_prod_right (ν := volume.restrict (Ioi (0 : ℝ)))).measurable
  have heq : stopPayoff m S Q x τ =
      A.piecewise (fun ω => ∫ t in Ioi (0 : ℝ), runCost m S Q x t ω) (fun ω => Ffin (τ' ω) ω) := by
    funext ω
    unfold stopPayoff
    by_cases hω : ω ∈ A
    · rw [Set.piecewise_eq_of_mem _ _ _ hω]
      simp only [hA, mem_ofPred_eq] at hω
      rw [hω]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hω]
      simp only [hA, mem_ofPred_eq] at hω
      cases hτω : τ ω with
      | top => exact absurd hτω hω
      | coe s => simp only [hFfin, hτ', hτω, WithTop.untopD_coe]
  rw [heq]
  exact Measurable.piecewise hAm hFtop_m (hFfin_m.comp (hτ'm.prodMk measurable_id))

end Part4

end MFIrrevStep1Aux

open MFIrrev.Equilibrium MFIrrevStep1Aux in
theorem solution (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    (hρ : 0 < m.ρ) (hc : 0 < m.c) (hκ : 0 < m.κ) (hφ : ∀ j, 0 < m.φ j) (hζ : ∀ j, 0 < m.ζ j)
    (hα0 : 0 < m.α) (hα1 : m.α < 1) (hφρδ : ∀ j, m.ρ + m.δ < m.φ j)
    (hA21 : 2 * max (m.σ 0 ^ 2) (m.σ 1 ^ 2) < m.ρ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (Q Q' : Fin 2 → ℝ) (hQ : ∀ j, 0 < Q j) (hQQ' : ∀ j, Q j ≤ Q' j) :
    (∀ x : ℝ, 0 < x → ∀ i : Fin 2, vStop m P S Q' x i ≤ vStop m P S Q x i) ∧
    ∀ a a' : Fin 2 → ℝ, (∀ j, 0 ≤ a j) → (∀ j, 0 ≤ a' j) →
      (∀ j, ∀ y : ℝ, 0 < y → (vStop m P S Q y j < m.κ ↔ a j < y)) →
      (∀ j, ∀ y : ℝ, 0 < y → (vStop m P S Q' y j < m.κ ↔ a' j < y)) →
      ∀ j, a' j ≤ a j := by
  have hR := reg_of m P S hS
  have hcc : 0 < m.ρ + m.δ := by linarith
  have hD : ∀ j, 0 ≤ eta m Q j - eta m Q' j := by
    intro j; unfold eta
    have h1 := Real.rpow_le_rpow_of_nonpos (hQ j) (hQQ' j) (by linarith : -m.α ≤ 0)
    have h2 := mul_le_mul_of_nonneg_left h1 (hζ j).le
    linarith
  have hmono : ∀ x : ℝ, 0 < x → ∀ i : Fin 2, vStop m P S Q' x i ≤ vStop m P S Q x i := by
    intro x _ i
    have hPi : IsProbabilityMeasure (Pcond P S i) := by
      have := hS.1
      exact cond_isProbabilityMeasure (hS.2.2.2.2.1 i).ne'
    set K := (|eta m Q 0 - eta m Q' 0| + |eta m Q 1 - eta m Q' 1|) *
          ∫ t in Ioi (0 : ℝ), Real.exp (-(m.ρ + m.δ) * t) with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_Ioi fun t _ => (Real.exp_pos _).le)
    have : Nonempty {τ : Ω → WithTop ℝ≥0 // IsStoppingTime S.ℱ τ} :=
      ⟨⟨fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0), isStoppingTime_const _ _⟩⟩
    unfold vStop
    apply iInf_sandwich _ _ (K * (Pcond P S i).real univ)
    · intro τ
      exact (int_sandwich (payoff_meas m hR Q' x τ.1 τ.2) (payoff_meas m hR Q x τ.1 τ.2) K hK0
        (fun ω => (path_bound m hR Q Q' x hD hcc τ.1 ω).1)
        (fun ω => (path_bound m hR Q Q' x hD hcc τ.1 ω).2)).1
    · intro τ
      exact (int_sandwich (payoff_meas m hR Q' x τ.1 τ.2) (payoff_meas m hR Q x τ.1 τ.2) K hK0
        (fun ω => (path_bound m hR Q Q' x hD hcc τ.1 ω).1)
        (fun ω => (path_bound m hR Q Q' x hD hcc τ.1 ω).2)).2
  refine ⟨hmono, ?_⟩
  intro a a' ha ha' hQa hQ'a j
  by_contra hlt
  push Not at hlt
  have hy : 0 < a' j := lt_of_le_of_lt (ha j) hlt
  have h1 : vStop m P S Q (a' j) j < m.κ := (hQa j (a' j) hy).2 hlt
  have h2 := (hQ'a j (a' j) hy).1 (lt_of_le_of_lt (hmono _ hy j) h1)
  exact lt_irrefl _ h2

