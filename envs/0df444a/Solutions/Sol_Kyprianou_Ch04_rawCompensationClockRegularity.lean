-- Prove2me | solution 1 for Kyprianou.Ch04.rawCompensationClockRegularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:15:24.454344+00:00
-- url     : https://prove2.me/submissions/231e7c0b-5268-46c6-92a9-482e7bca1613

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_pointwiseFiniteBandJointLIntegral
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04
/-- Raw nonnegative Poisson clock measurability and real conversion. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (t : NNReal)
    (hKernelPast : Measurable[(F t).prod inferInstance]
      (fun z : Omega × (Real × Real) =>
        if z.2.1 ∈ Set.Icc (0 : Real) (t : Real) then phi z.2.1 z.2.2 z.1 else 0))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hPast : ∀ B : Set (Real × Real), MeasurableSet B →
      B ⊆ Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ →
      Measurable[F t] (fun w => N.N w B))
    (hLocalFinite : ∀ n : Nat, ∀ w : Omega,
      N.N w (Set.Icc (0 : Real) (t : Real) ×ˢ spanningSets levyMeasure n) ≠ ⊤) :
    Measurable[F t] (fun w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)) ∧
    StronglyMeasurable[F t] (fun w => ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      phi z.1 z.2 w ∂(N.N w)) ∧
    (∀ w, (∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      phi z.1 z.2 w ∂(N.N w)) =
      (∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
        ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)).toReal) := by
  let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
  let B (n : Nat) := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets levyMeasure n
  let f (z : Omega × (ℝ × ℝ)) :=
    ENNReal.ofReal (if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then phi z.2.1 z.2.2 z.1 else 0)
  have hB (n : Nat) : MeasurableSet (B n) :=
    measurableSet_Icc.prod (measurableSet_spanningSets levyMeasure n)
  have hm : Monotone B := fun i j hij _ hz =>
    ⟨hz.1, monotone_spanningSets levyMeasure hij hz.2⟩
  have hu : (⋃ n, B n) = U := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact ⟨hn.1, Set.mem_univ _⟩
    · intro hz
      have hx : z.2 ∈ ⋃ n, spanningSets levyMeasure n := by
        rw [iUnion_spanningSets]
        exact Set.mem_univ _
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n, hz.1, hn⟩
  have hf : Measurable[(F t).prod inferInstance] f :=
    ENNReal.measurable_ofReal.comp hKernelPast
  have h := @pointwiseFiniteBandJointLIntegral Omega (ℝ × ℝ)
    (F t) inferInstance N.N U (measurableSet_Icc.prod MeasurableSet.univ)
    B hB hm hu hPast hLocalFinite f hf
  have he (w : Omega) : (∫⁻ z in U, f (w,z) ∂(N.N w)) =
      ∫⁻ z in U, ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    have hmem : z.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) := hz.1
    exact congrArg ENNReal.ofReal (if_pos hmem)
  simp_rw [he] at h
  have hr (w : Omega) : (∫ z in U, phi z.1 z.2 w ∂(N.N w)) =
      (∫⁻ z in U, ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)).toReal := by
    apply integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => hPhi.1 _ _ _)
    exact (hPhi.2.1.comp measurable_prodMk_right).aestronglyMeasurable
  refine ⟨h, ?_, hr⟩
  have heq : (fun w => ∫ z in U, phi z.1 z.2 w ∂(N.N w)) =
      fun w => (∫⁻ z in U, ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)).toReal :=
    funext hr
  change StronglyMeasurable[F t] (fun w => ∫ z in U, phi z.1 z.2 w ∂(N.N w))
  rw [heq]
  exact h.ennreal_toReal.stronglyMeasurable
