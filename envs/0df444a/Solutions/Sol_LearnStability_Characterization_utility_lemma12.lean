-- Prove2me | solution 1 for LearnStability.Characterization.utility_lemma12
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:32:55.977606+00:00
-- url     : https://prove2.me/submissions/3a353dbc-012b-4bbb-83fb-95cf059bba5f

import Definitions.Def_LearnStability_Characterization_Setting
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Finset
open LearnStability.Characterization
namespace CLearn

theorem abs_mean_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLp Y 2 P) :
    (∫ ω,|Y ω| ∂P) ≤ Real.sqrt (∫ ω,(Y ω)^2 ∂P) := by
  have hAbs : MemLp (fun ω=>|Y ω|) 2 P := by simpa only [Real.norm_eq_abs] using hY.norm
  have hv:=variance_nonneg (fun ω=>|Y ω|) P
  rw [variance_eq_sub hAbs] at hv
  change 0 ≤ (∫ ω,|Y ω|^2 ∂P)-(∫ ω,|Y ω| ∂P)^2 at hv
  simp_rw [sq_abs] at hv
  have hn : 0 ≤ ∫ ω,(Y ω)^2 ∂P := integral_nonneg (fun ω=>sq_nonneg _)
  have hs:=Real.sq_sqrt hn
  have hs0:=Real.sqrt_nonneg (∫ ω,(Y ω)^2 ∂P)
  nlinarith

theorem utility {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) [IsProbabilityMeasure D]
    (g : Z → ℝ) (B : ℝ) (hg : Measurable g) (hB : ∀ z, |g z| ≤ B)
    (m : ℕ) (hm : 1 ≤ m) :
    ∫ S, |(∑ i, g (S i)) / m - ∫ z, g z ∂D| ∂(sampleLaw D m) ≤ B / Real.sqrt m := by
  classical
  haveI : Nonempty Z := nonempty_of_isProbabilityMeasure D
  have hB0 : 0 ≤ B := (abs_nonneg (g (Classical.arbitrary Z))).trans (hB _)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn : (m : ℝ) ≠ 0 := ne_of_gt hm0
  haveI : IsProbabilityMeasure (sampleLaw D m) := by unfold sampleLaw;infer_instance
  have hg2 : MemLp g 2 D := MemLp.of_bound hg.aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun z=>by simpa only [Real.norm_eq_abs] using hB z))
  have hi2 (i : Fin m) : MemLp (fun S : Fin m → Z=>g (S i)) 2 (sampleLaw D m) := by
    exact MemLp.of_bound (hg.comp (measurable_pi_apply i)).aestronglyMeasurable B (Filter.Eventually.of_forall (fun S=>by simpa only [Real.norm_eq_abs] using hB (S i)))
  have hi (i : Fin m) : (∫ S,g (S i) ∂sampleLaw D m)=∫ z,g z ∂D := by
    have hp:=measurePreserving_eval (fun _ : Fin m=>D) i
    calc
      _=∫ z,g z ∂(Measure.map (Function.eval i) (Measure.pi fun _ : Fin m=>D)) :=
        (integral_map hp.measurable.aemeasurable hg.aestronglyMeasurable).symm
      _=_ := by rw [hp.map_eq]
  let X (S : Fin m → Z) := (∑ i,g (S i))/(m : ℝ)
  have hX2 : MemLp X 2 (sampleLaw D m) := by
    simpa only [X,div_eq_mul_inv] using (memLp_finsetSum univ (fun i _=>hi2 i)).mul_const ((m : ℝ)⁻¹)
  have hmean : (∫ S,X S ∂sampleLaw D m)=∫ z,g z ∂D := by
    change (∫ S,(∑ i,g (S i))/(m : ℝ) ∂sampleLaw D m)=_
    rw [integral_div,integral_finsetSum _ (fun i _=>(hi2 i).integrable (by norm_num))]
    simp_rw [hi]
    simp [hmn]
  have hsum : variance (fun S : Fin m → Z=>∑ i,g (S i)) (sampleLaw D m)=(m : ℝ)*variance g D := by
    have hv:=variance_sum_pi (ι:=Fin m) (μ:=fun _=>D) (X:=fun _=>g) (fun _=>hg2)
    have he : (∑ i : Fin m,fun S : Fin m → Z=>g (S i))=(fun S=>∑ i,g (S i)) := by ext S;simp
    rw [he] at hv
    simpa [sampleLaw] using hv
  have hvg : variance g D ≤ B^2 := by
    apply (variance_le_expectation_sq hg2.aestronglyMeasurable).trans
    calc
      (∫ z,g z^2 ∂D) ≤ ∫ _ : Z,B^2 ∂D := by
        apply integral_mono (hg2.integrable_sq) (integrable_const _)
        intro z
        nlinarith [hB z,sq_abs (g z),abs_nonneg (g z)]
      _=B^2 := by simp
  have hvX : variance X (sampleLaw D m) ≤ B^2/(m : ℝ) := by
    have he : X=(fun S=>(∑ i,g (S i))*(m : ℝ)⁻¹) := by funext S;rfl
    rw [he,variance_mul_const,hsum]
    calc
      (m : ℝ)*variance g D*((m : ℝ)⁻¹)^2 ≤ (m : ℝ)*B^2*((m : ℝ)⁻¹)^2 := by gcongr
      _=B^2/(m : ℝ) := by field_simp
  have hY2:=hX2.sub (memLp_const (∫ z,g z ∂D))
  have hsq : (∫ S,(X S-∫ z,g z ∂D)^2 ∂sampleLaw D m)=variance X (sampleLaw D m) := by
    rw [variance_eq_integral hX2.aemeasurable,hmean]
  calc
    _ ≤ Real.sqrt (∫ S,(X S-∫ z,g z ∂D)^2 ∂sampleLaw D m) := abs_mean_le_sqrt _ _ hY2
    _ ≤ Real.sqrt (B^2/(m : ℝ)) := by rw [hsq];exact Real.sqrt_le_sqrt hvX
    _=B/Real.sqrt m := by rw [Real.sqrt_div (sq_nonneg B),Real.sqrt_sq_eq_abs,abs_of_nonneg hB0]

end CLearn

theorem solution {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) [IsProbabilityMeasure D]
    (g : Z → ℝ) (B : ℝ) (hg : Measurable g) (hB : ∀ z, |g z| ≤ B)
    (m : ℕ) (hm : 1 ≤ m) :
    ∫ S, |(∑ i, g (S i)) / m - ∫ z, g z ∂D| ∂(sampleLaw D m) ≤ B / Real.sqrt m :=
  CLearn.utility D g B hg hB m hm
