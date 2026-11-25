-- Prove2me | solution 1 for Kyprianou.Ch04.finiteENNCompensatedMartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:39:53.450858+00:00
-- url     : https://prove2.me/submissions/2e91503e-b5fa-401e-902e-7466ebc5689e

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- An adapted real clock difference is a martingale under eventwise balance. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R C : NNReal → Omega → ENNReal) (M : NNReal → Omega → Real)
    (hR : ∀ t, Measurable (R t)) (hC : ∀ t, Measurable (C t))
    (hRf : ∀ t, (∫⁻ w, R t w ∂P) ≠ ⊤)
    (hCf : ∀ t, (∫⁻ w, C t w ∂P) ≠ ⊤)
    (hAdapt : StronglyAdapted F M)
    (hM : ∀ t, M t =ᵐ[P] fun w => (R t w).toReal - (C t w).toReal)
    (hBalance : ∀ u t : NNReal, u ≤ t → ∀ A : Set Omega, MeasurableSet[F u] A →
      (∫⁻ w in A, R u w ∂P) + (∫⁻ w in A, C t w ∂P) =
      (∫⁻ w in A, R t w ∂P) + (∫⁻ w in A, C u w ∂P)) :
    Martingale M F P := by
  have aux (L : Omega → ENNReal) (hL : Measurable L)
      (hf : (∫⁻ w, L w ∂P) < ⊤) :
      Integrable (fun w => (L w).toReal) P ∧ ∀ A : Set Omega,
        (∫ w in A, (L w).toReal ∂P) = (∫⁻ w in A, L w ∂P).toReal := by
    have htop := ae_lt_top hL hf.ne
    have ht : (fun w => ENNReal.ofReal (L w).toReal) =ᵐ[P] L := by
      filter_upwards [htop] with w hw
      exact ENNReal.ofReal_toReal hw.ne
    have hi : Integrable (fun w => (L w).toReal) P := by
      refine ⟨hL.ennreal_toReal.aestronglyMeasurable, ?_⟩
      exact (hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).2
        (by rwa [lintegral_congr_ae ht])
    refine ⟨hi, fun A => ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      hi.integrableOn.aestronglyMeasurable,
      lintegral_congr_ae (ae_restrict_of_ae ht)]
  have hRi (t : NNReal) :=
    aux (R t) (hR t) (lt_top_iff_ne_top.mpr (hRf t))
  have hCi (t : NNReal) :=
    aux (C t) (hC t) (lt_top_iff_ne_top.mpr (hCf t))
  have hi (t : NNReal) : Integrable (M t) P :=
    (integrable_congr (hM t)).2 ((hRi t).1.sub (hCi t).1)
  refine ⟨hAdapt, fun u t hut => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le u) (hi t)
    (fun A _ _ => (hi u).integrableOn) (fun A hA _ => ?_)
    (hAdapt u).aestronglyMeasurable).symm
  have h := congrArg ENNReal.toReal (hBalance u t hut A hA)
  have hfr (r : NNReal) : (∫⁻ w in A, R r w ∂P) ≠ ⊤ :=
    ((calc
      (∫⁻ w in A, R r w ∂P) ≤ ∫⁻ w in Set.univ, R r w ∂P :=
        lintegral_mono_set (Set.subset_univ A)
      _ = ∫⁻ w, R r w ∂P := by rw [Measure.restrict_univ]).trans_lt
        (lt_top_iff_ne_top.mpr (hRf r))).ne
  have hfc (r : NNReal) : (∫⁻ w in A, C r w ∂P) ≠ ⊤ :=
    ((calc
      (∫⁻ w in A, C r w ∂P) ≤ ∫⁻ w in Set.univ, C r w ∂P :=
        lintegral_mono_set (Set.subset_univ A)
      _ = ∫⁻ w, C r w ∂P := by rw [Measure.restrict_univ]).trans_lt
        (lt_top_iff_ne_top.mpr (hCf r))).ne
  rw [ENNReal.toReal_add (hfr u) (hfc t),
    ENNReal.toReal_add (hfr t) (hfc u)] at h
  change (∫ w in A, M u w ∂P) = ∫ w in A, M t w ∂P
  rw [integral_congr_ae (ae_restrict_of_ae (hM u)),
    integral_congr_ae (ae_restrict_of_ae (hM t)),
    integral_sub (hRi u).1.integrableOn (hCi u).1.integrableOn,
    integral_sub (hRi t).1.integrableOn (hCi t).1.integrableOn,
    (hRi u).2 A, (hCi u).2 A, (hRi t).2 A, (hCi t).2 A]
  linarith
