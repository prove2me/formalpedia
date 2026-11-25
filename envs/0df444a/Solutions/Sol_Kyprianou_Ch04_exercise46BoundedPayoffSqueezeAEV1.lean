-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BoundedPayoffSqueezeAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:28:28.1338+00:00
-- url     : https://prove2.me/submissions/0b54fcd8-2cac-4139-8be1-cf611a2b081f

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Almost-everywhere equality from decreasing bounded payoff expectations. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Nat → Omega → Real) (g h : Omega → Real)
    (hF : ∀ n, AEMeasurable (F n) P) (hg : AEMeasurable g P)
    (hFBound : ∀ n w, 0 ≤ F n w ∧ F n w ≤ 1)
    (hgBound : ∀ w, 0 ≤ g w ∧ g w ≤ 1)
    (hSandwich : ∀ᵐ w ∂P, g w ≤ h w ∧ ∀ n, h w ≤ F n w)
    (hAnti : ∀ᵐ w ∂P, Antitone (fun n => F n w))
    (hLimit : Tendsto (fun n => ∫ w, F n w ∂P) atTop
      (nhds (∫ w, g w ∂P))) :
    h =ᵐ[P] g := by
  let l : Omega → Real := fun w => ⨅ n, F n w
  have hbelow (w : Omega) : BddBelow (range fun n => F n w) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hFBound n w).1⟩
  have hl : AEMeasurable l P := AEMeasurable.iInf hF
  have hlb (w : Omega) : 0 ≤ l w ∧ l w ≤ 1 :=
    ⟨le_ciInf fun n => (hFBound n w).1, (ciInf_le (hbelow w) 0).trans (hFBound 0 w).2⟩
  have hlim := tendsto_integral_of_dominated_convergence (μ := P) (f := l)
    (fun _ => (1 : Real)) (fun n => (hF n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun w => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hFBound n w).1] using (hFBound n w).2)
    (hAnti.mono fun w hw => tendsto_atTop_ciInf hw (hbelow w))
  have hgI := (integrable_const (1 : Real) (μ := P)).mono' hg.aestronglyMeasurable
    (Eventually.of_forall fun w => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hgBound w).1] using (hgBound w).2)
  have hlI := (integrable_const (1 : Real) (μ := P)).mono' hl.aestronglyMeasurable
    (Eventually.of_forall fun w => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hlb w).1] using (hlb w).2)
  have hgl : g ≤ᵐ[P] l := hSandwich.mono fun w hw => hw.1.trans (le_ciInf hw.2)
  have he := (integral_eq_iff_of_ae_le hgI hlI hgl).mp (tendsto_nhds_unique hLimit hlim)
  filter_upwards [hSandwich, he] with w hw heq
  exact le_antisymm ((le_ciInf hw.2).trans_eq heq.symm) hw.1
