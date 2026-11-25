-- Prove2me | solution 1 for ManyServerQED.Scheduling.independence_under_negligible_weak_limit_perturbations
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T21:10:13.598439+00:00
-- url     : https://prove2.me/submissions/271d592f-b17a-47b9-b94f-936998abc2a6

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal

private theorem charFunDual_tendsto_of_in_distribution
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {X : ℕ → Ω → E} {Y : Ω' → E}
    (h : TendstoInDistribution X atTop Y (fun _ => P) P') (L : StrongDual ℝ E) :
    Tendsto (fun n => charFunDual (P.map (X n)) L) atTop (𝓝 (charFunDual (P'.map Y) L)) := by
  let f (x : E) : ℂ := Complex.exp ((L x:ℂ)*Complex.I)
  have hf : Continuous f := by unfold f; fun_prop
  let g := BoundedContinuousFunction.mkOfBound ⟨f,hf⟩ 2 (by
    intro x y
    rw [dist_eq_norm]
    change ‖f x-f y‖ ≤ 2
    refine (norm_sub_le _ _).trans ?_
    norm_num [f,Complex.norm_exp,Complex.mul_re])
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h.tendsto g

theorem solution
    {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F]
    (X : ℕ → Ω → E) (Y V : ℕ → Ω → F) (x : Ω' → E) (y : Ω' → F)
    (h : TendstoInDistribution (fun n ω => (X n ω,Y n ω)) atTop
      (fun ω => (x ω,y ω)) (fun _ => P) P')
    (hV : ∀ n, AEMeasurable (V n) P)
    (herr : TendstoInMeasure P (fun n ω => V n ω - Y n ω) atTop (fun _ => 0))
    (hind : ∀ᶠ n in atTop, IndepFun (X n) (V n) P) :
    IndepFun x y P' := by
  let g (z : (E × F) × F) := (z.1.1,z.1.2 + z.2)
  have hg : Continuous g := by unfold g; fun_prop
  have hY (n : ℕ) : AEMeasurable (Y n) P := measurable_snd.comp_aemeasurable (h.forall_aemeasurable n)
  have hE (n : ℕ) : AEMeasurable (fun ω => V n ω - Y n ω) P := (hV n).sub (hY n)
  have h' := h.continuous_comp_prodMk_of_tendstoInMeasure_const hg herr hE
  have hp : TendstoInDistribution (fun n ω => (X n ω,V n ω)) atTop
      (fun ω => (x ω,y ω)) (fun _ => P) P' := by
    have he (a b : F) : a + (b-a) = b := by abel
    simpa [g,he] using h' 
  have hx' : TendstoInDistribution X atTop x (fun _ => P) P' :=
    hp.continuous_comp continuous_fst
  have hy' : TendstoInDistribution V atTop y (fun _ => P) P' :=
    hp.continuous_comp continuous_snd
  apply (indepFun_iff_charFunDual_prod hx'.aemeasurable_limit hy'.aemeasurable_limit).2
  intro L
  have ht := charFunDual_tendsto_of_in_distribution hp L
  have ht' := (charFunDual_tendsto_of_in_distribution hx' (L.comp (.inl ℝ E F))).mul
    (charFunDual_tendsto_of_in_distribution hy' (L.comp (.inr ℝ E F)))
  have hrel : ∀ᶠ n in atTop, charFunDual (P.map (fun ω => (X n ω,V n ω))) L =
       charFunDual (P.map (X n)) (L.comp (.inl ℝ E F)) *
         charFunDual (P.map (V n)) (L.comp (.inr ℝ E F)) := by
    filter_upwards [hind] with n hi
    exact (indepFun_iff_charFunDual_prod (hx'.forall_aemeasurable n) (hV n)).1 hi L
  exact tendsto_nhds_unique (ht.congr' hrel) ht'
