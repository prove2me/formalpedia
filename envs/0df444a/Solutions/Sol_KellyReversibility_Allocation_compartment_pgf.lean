-- Prove2me | solution 1 for KellyReversibility.Allocation.compartment_pgf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:17:00.850646+00:00
-- url     : https://prove2.me/submissions/4cf5a25e-556d-49ba-833b-1d0357a781be

import Mathlib
import Definitions.Def_KellyReversibility_Allocation_CompartmentModel

set_option autoImplicit false

open MeasureTheory

namespace P02b6938a

lemma measSum {J : ℕ} (w : Fin J ⊕ Unit → ℝ) : Measurable w := by
  have : w = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) := by
    funext x; cases x <;> rfl
  rw [this]
  exact (measurable_of_countable _).sumElim (measurable_of_countable _)

lemma prod_count {J : ℕ} (z : Fin J → ℝ) (m : ℕ) (L : ℕ → Fin J ⊕ Unit) :
    ∏ j, z j ^ ((Finset.range m).filter (fun r => L r = Sum.inl j)).card
      = ∏ r ∈ Finset.range m, Sum.elim z (fun _ => (1:ℝ)) (L r) := by
  have h1 : ∀ r, Sum.elim z (fun _ => (1:ℝ)) (L r)
      = ∏ j, (if L r = Sum.inl j then z j else 1) := by
    intro r
    cases h : L r with
    | inl j0 =>
      simp only [Sum.elim_inl, Sum.inl.injEq]
      rw [Finset.prod_ite_eq]
      simp
    | inr u => simp
  simp_rw [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← Finset.prod_filter, Finset.prod_const]

lemma w_eq {J : ℕ} (z : Fin J → ℝ) (x : Fin J ⊕ Unit) :
    Sum.elim z (fun _ => (1:ℝ)) x
      = 1 - ∑ j, (1 - z j) * (if x = Sum.inl j then 1 else 0) := by
  cases x with
  | inl j0 =>
    simp only [Sum.elim_inl, Sum.inl.injEq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  | inr u => simp

end P02b6938a

open MeasureTheory KellyReversibility.Allocation in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {J : ℕ}
    {ν t : ℝ} {p : Fin J → ℝ → ℝ} {M : Ω → ℕ} {T : ℕ → Ω → ℝ}
    {Loc : ℕ → Ω → Fin J ⊕ Unit} (hmodel : IsCompartmentModel P ν t p M T Loc)
    (z : Fin J → ℝ) (hz0 : ∀ j, 0 ≤ z j) (hz1 : ∀ j, z j ≤ 1) :
    ∫ ω, ∏ j, z j ^ compartmentCount M Loc j ω ∂P
      = ∏ j, Real.exp (-(1 - z j) * ν * alpha p j t) := by
  have hP := hmodel.isProb
  have hν := hmodel.rate_pos
  have ht := hmodel.time_pos
  set w : Fin J ⊕ Unit → ℝ := Sum.elim z (fun _ => (1:ℝ)) with hw_def
  have hw : Measurable w := P02b6938a.measSum w
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x; cases x <;> simp [w, hz0]
  have hw1 : ∀ x, w x ≤ 1 := by
    intro x; cases x <;> simp [w, hz1]
  have hLoc := hmodel.Loc_meas
  have hM := hmodel.M_meas
  -- H n ω
  set H : ℕ → Ω → ℝ := fun n ω => ∏ r ∈ Finset.range n, w (Loc r ω) with hH
  have hHm : ∀ n, Measurable (H n) := fun n =>
    Finset.measurable_prod _ (fun r _ => hw.comp (hLoc r))
  have hH0 : ∀ n ω, 0 ≤ H n ω := fun n ω => Finset.prod_nonneg (fun r _ => hw0 _)
  have hH1 : ∀ n ω, H n ω ≤ 1 := fun n ω =>
    Finset.prod_le_one (fun r _ => hw0 _) (fun r _ => hw1 _)
  have hf : ∀ ω, ∏ j, z j ^ compartmentCount M Loc j ω = H (M ω) ω := by
    intro ω
    exact P02b6938a.prod_count z (M ω) (fun r => Loc r ω)
  simp_rw [hf]
  have hfm : Measurable (fun ω => H (M ω) ω) := by
    have : Measurable (fun q : ℕ × Ω => H q.1 q.2) :=
      measurable_from_prod_countable_right (fun n => hHm n)
    exact this.comp (hM.prodMk measurable_id)
  have hfi : Integrable (fun ω => H (M ω) ω) P := by
    refine Integrable.of_bound hfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 _ _)]
    exact hH1 _ _
  -- decompose over M = n
  have hdecomp : ∫ ω, H (M ω) ω ∂P = ∑' n, ∫ ω in M ⁻¹' {n}, H (M ω) ω ∂P := by
    have hU : (⋃ n, M ⁻¹' {n}) = Set.univ := by
      ext ω; simp
    rw [← integral_iUnion (fun n => hM (measurableSet_singleton n))
      (fun a b hab => by
        simp only [Function.onFun]
        exact Set.disjoint_left.mpr (fun ω h1 h2 => hab (by simp at h1 h2; omega)))
      (by rw [hU]; exact hfi.integrableOn), hU, setIntegral_univ]
  -- single-location expectation
  set q : ℝ := 1 - ∑ j, (1 - z j) * (alpha p j t / t) with hq
  have hLocLaw : ∀ r j, P.real {ω | Loc r ω = Sum.inl j} = alpha p j t / t := by
    intro r j
    have h := hmodel.Loc_law r Set.univ MeasurableSet.univ j
    simp only [Set.mem_univ, true_and, Set.univ_inter] at h
    have hint : ∫ u in Set.Ioo 0 t, p j (t - u) = alpha p j t := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
        intervalIntegral.integral_comp_sub_left]
      simp [alpha]
    have hnn : 0 ≤ ∫ u in Set.Ioo 0 t, p j (t - u) :=
      setIntegral_nonneg measurableSet_Ioo
        (fun u hu => hmodel.p_nonneg j (t - u) (by linarith [hu.2]))
    rw [measureReal_def, h, ENNReal.toReal_ofReal (by positivity), hint]
    ring
  have hEw : ∀ r, ∫ ω, w (Loc r ω) ∂P = q := by
    intro r
    have : (fun ω => w (Loc r ω)) = fun ω =>
        1 - ∑ j, (1 - z j) * ({ω | Loc r ω = Sum.inl j}.indicator (1 : Ω → ℝ) ω) := by
      funext ω
      rw [hw_def, P02b6938a.w_eq]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      simp [Set.indicator]
    have hms : ∀ j, MeasurableSet {ω | Loc r ω = Sum.inl j} := fun j =>
      (P02b6938a.measSum (fun x => if x = Sum.inl j then (1:ℝ) else 0)).comp (hLoc r)
        (measurableSet_singleton (1:ℝ)) |> fun h => by
          convert h using 1
          ext ω; simp
    rw [this, integral_sub (integrable_const _), integral_const, integral_finsetSum]
    · have hu : P.real Set.univ = 1 := by simp [measureReal_def]
      simp only [hu, smul_eq_mul, mul_one]
      rw [hq]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_const_mul, integral_indicator_one (hms j), hLocLaw]
    · intro j _
      exact ((integrable_const (1:ℝ)).indicator (hms j)).const_mul _
    · exact integrable_finsetSum _ (fun j _ =>
        ((integrable_const (1:ℝ)).indicator (hms j)).const_mul _)
  -- independence
  have hX : Measurable (fun ω r => (T r ω, Loc r ω)) :=
    measurable_pi_lambda _ (fun r => (hmodel.T_meas r).prodMk (hLoc r))
  have hiW : ProbabilityTheory.iIndepFun (fun r ω => w (Loc r ω)) P := by
    have := hmodel.indep_pairs.comp (fun _ (x : ℝ × (Fin J ⊕ Unit)) => w x.2)
      (fun _ => hw.comp measurable_snd)
    exact this
  have hEH : ∀ n, ∫ ω, H n ω ∂P = q ^ n := by
    intro n
    have hi := hiW.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective
    have key : ∫ ω, ∏ i : Fin n, w (Loc i ω) ∂P = ∏ i : Fin n, ∫ ω, w (Loc i ω) ∂P :=
      hi.integral_fun_prod_eq_prod_integral
        (fun i => (hw.comp (hLoc _)).aestronglyMeasurable)
    calc ∫ ω, H n ω ∂P = ∫ ω, ∏ i : Fin n, w (Loc i ω) ∂P := by
          congr 1; funext ω; exact Finset.prod_range _
      _ = ∏ i : Fin n, ∫ ω, w (Loc i ω) ∂P := key
      _ = q ^ n := by simp [hEw]
  have hpiece : ∀ n, ∫ ω in M ⁻¹' {n}, H (M ω) ω ∂P
      = P.real (M ⁻¹' {n}) * q ^ n := by
    intro n
    set φ : ℕ → ℝ := fun k => if k = n then 1 else 0 with hφ
    rw [← integral_indicator (hM (measurableSet_singleton n))]
    have e1 : (M ⁻¹' {n}).indicator (fun ω => H (M ω) ω) = fun ω => φ (M ω) * H n ω := by
      funext ω
      by_cases h : M ω = n
      · simp [Set.indicator, φ, h]
      · simp [Set.indicator, φ, h]
    rw [e1]
    have hI := hmodel.indep_M.comp (φ := φ)
      (ψ := fun x : ℕ → ℝ × (Fin J ⊕ Unit) => ∏ r ∈ Finset.range n, w (x r).2)
      (measurable_of_countable _)
      (Finset.measurable_prod _ (fun r _ => hw.comp (measurable_snd.comp (measurable_pi_apply r))))
    have key : ∫ ω, φ (M ω) * H n ω ∂P = (∫ ω, φ (M ω) ∂P) * ∫ ω, H n ω ∂P :=
      hI.integral_fun_mul_eq_mul_integral
        ((measurable_of_countable φ).comp hM).aestronglyMeasurable
        (hHm n).aestronglyMeasurable
    rw [key, hEH]
    have e2 : (fun ω => φ (M ω)) = (M ⁻¹' {n}).indicator (1 : Ω → ℝ) := by
      funext ω
      by_cases h : M ω = n
      · simp [Set.indicator, φ, h]
      · simp [Set.indicator, φ, h]
    rw [e2, integral_indicator_one (hM (measurableSet_singleton n))]
  rw [hdecomp]
  simp_rw [hpiece]
  have hPn : ∀ n, P.real (M ⁻¹' {n})
      = Real.exp (-(ν * t)) * (ν * t) ^ n / (n.factorial : ℝ) := by
    intro n
    rw [measureReal_def]
    show (P {ω | M ω = n}).toReal = _
    rw [hmodel.M_poisson n, ENNReal.toReal_ofReal (by positivity)]
  simp_rw [hPn]
  have he : Real.exp (ν * t * q) = ∑' n : ℕ, (ν * t * q) ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hs : ∑' n : ℕ, Real.exp (-(ν * t)) * (ν * t) ^ n / (n.factorial : ℝ) * q ^ n
      = Real.exp (-(ν * t)) * Real.exp (ν * t * q) := by
    rw [he, ← tsum_mul_left]
    congr 1; funext n; rw [mul_pow]; ring
  have htne : t ≠ 0 := ht.ne'
  have hsum : ν * t * ∑ j, (1 - z j) * (alpha p j t / t)
      = ∑ j, (1 - z j) * ν * alpha p j t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show ν * t * ((1 - z j) * (alpha p j t / t))
        = (1 - z j) * ν * alpha p j t * (t / t) by ring, div_self htne, mul_one]
  rw [hs, ← Real.exp_add, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => show -(1 - z j) * ν * alpha p j t
      = -((1 - z j) * ν * alpha p j t) by ring), Finset.sum_neg_distrib, ← hsum, hq]
  ring
