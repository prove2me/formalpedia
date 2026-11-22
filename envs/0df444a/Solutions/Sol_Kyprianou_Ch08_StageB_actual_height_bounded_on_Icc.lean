-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_bounded_on_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:01:31.967803+00:00
-- url     : https://prove2.me/submissions/f18def49-843b-47e0-b352-f696028d33c8

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ h : ℝ, 0 < h → ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x → x ≤ 2 →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X x h ω}, Real.exp (Phi ψ q * x) * discountedAt q (tauPlus D.X x ω) ∂P) ≤ B := by
  intro h hh
  let C : ℝ := Real.exp (|Phi ψ q| * 2)
  refine ⟨(P Set.univ).toReal * C, ?_⟩
  intro x hx1 hx2
  let s : Set Ω := {ω | NoDrawdownBeforeUpcrossing D.X x h ω}
  let f : Ω → ℝ := fun ω =>
    Real.exp (Phi ψ q * x) * discountedAt q (tauPlus D.X x ω)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdisc : ∀ τ : WithTop ℝ≥0, 0 ≤ discountedAt q τ ∧ discountedAt q τ ≤ 1 := by
    intro τ
    cases τ using WithTop.recTopCoe with
    | top =>
        simp [discountedAt]
    | coe t =>
        simp only [discountedAt]
        constructor
        · positivity
        · rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (NNReal.coe_nonneg t)
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have harg : Phi ψ q * x ≤ |Phi ψ q| * 2 := by
    calc
      Phi ψ q * x ≤ |Phi ψ q| * x :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hx0
      _ ≤ |Phi ψ q| * 2 :=
        mul_le_mul_of_nonneg_left hx2 (abs_nonneg _)
  have hexp0 : 0 ≤ Real.exp (Phi ψ q * x) := (Real.exp_pos _).le
  have hexpC : Real.exp (Phi ψ q * x) ≤ C := by
    dsimp [C]
    exact Real.exp_le_exp.mpr harg
  have hf_bound : ∀ ω, 0 ≤ f ω ∧ f ω ≤ C := by
    intro ω
    have hd := hdisc (tauPlus D.X x ω)
    have hle : f ω ≤ Real.exp (Phi ψ q * x) := by
      dsimp [f]
      exact mul_le_of_le_one_right hexp0 hd.2
    exact ⟨by dsimp [f]; exact mul_nonneg hexp0 hd.1, hle.trans hexpC⟩
  change (∫ ω, f ω ∂(P.restrict s)) ≤ (P Set.univ).toReal * C
  by_cases hfi : Integrable f (P.restrict s)
  · have hci : Integrable (fun _ : Ω => C) (P.restrict s) := integrable_const C
    have hmono :
        (∫ ω, f ω ∂(P.restrict s)) ≤ ∫ _ : Ω, C ∂(P.restrict s) :=
      integral_mono_ae hfi hci (Filter.Eventually.of_forall (fun ω => (hf_bound ω).2))
    calc
      (∫ ω, f ω ∂(P.restrict s)) ≤ ∫ _ : Ω, C ∂(P.restrict s) := hmono
      _ = (P.restrict s Set.univ).toReal * C := by
        simp [MeasureTheory.integral_const, MeasureTheory.Measure.real]
      _ = (P s).toReal * C := by simp [MeasureTheory.Measure.real]
      _ ≤ (P Set.univ).toReal * C := by
        exact mul_le_mul_of_nonneg_right
          (ENNReal.toReal_mono (ne_of_lt (measure_lt_top P Set.univ))
            (measure_mono (Set.subset_univ s))) hC0
  · rw [integral_undef hfi]
    exact mul_nonneg ENNReal.toReal_nonneg hC0
