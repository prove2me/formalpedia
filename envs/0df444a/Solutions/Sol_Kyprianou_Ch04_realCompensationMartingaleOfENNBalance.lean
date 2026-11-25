-- Prove2me | solution 1 for Kyprianou.Ch04.realCompensationMartingaleOfENNBalance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:21:48.734326+00:00
-- url     : https://prove2.me/submissions/6c088833-bb2f-42d8-83f6-ac6dc95afcf0

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Martingale from finite compensated extended clock balance. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (J C : NNReal → Omega → ENNReal)
    (j c : NNReal → Omega → Real)
    (hj : StronglyAdapted F j) (hc : StronglyAdapted F c)
    (hJ : ∀ t, Measurable (J t)) (hC : ∀ t, Measurable (C t))
    (hfinJ : ∀ t, (∫⁻ w, J t w ∂P) < ⊤)
    (hfinC : ∀ t, (∫⁻ w, C t w ∂P) < ⊤)
    (heJ : ∀ t, j t =ᵐ[P] fun w => (J t w).toReal)
    (heC : ∀ t, c t =ᵐ[P] fun w => (C t w).toReal)
    (hbal : ∀ u t : NNReal, u ≤ t → ∀ A : Set Omega, MeasurableSet[F u] A →
      (∫⁻ w in A, J t w ∂P) + (∫⁻ w in A, C u w ∂P) =
      (∫⁻ w in A, J u w ∂P) + (∫⁻ w in A, C t w ∂P)) :
    Martingale (fun t w => j t w - c t w) F P := by
  have aux (L : Omega → ENNReal) (hL : Measurable L)
      (hf : (∫⁻ w, L w ∂P) < ⊤) (r : Omega → Real)
      (he : r =ᵐ[P] fun w => (L w).toReal) :
      Integrable r P ∧ ∀ A : Set Omega,
        (∫ w in A, r w ∂P) = (∫⁻ w in A, L w ∂P).toReal := by
    have htop := ae_lt_top hL hf.ne
    have ht : (fun w => ENNReal.ofReal (L w).toReal) =ᵐ[P] L := by
      filter_upwards [htop] with w hw
      exact ENNReal.ofReal_toReal hw.ne
    have hi : Integrable (fun w => (L w).toReal) P := by
      refine ⟨hL.ennreal_toReal.aestronglyMeasurable, ?_⟩
      exact (hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).2
        (by rwa [lintegral_congr_ae ht])
    refine ⟨(integrable_congr he).2 hi, fun A => ?_⟩
    rw [integral_congr_ae (ae_restrict_of_ae he),
      integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        hi.integrableOn.aestronglyMeasurable,
      lintegral_congr_ae (ae_restrict_of_ae ht)]
  have hji (t : NNReal) := aux (J t) (hJ t) (hfinJ t) (j t) (heJ t)
  have hci (t : NNReal) := aux (C t) (hC t) (hfinC t) (c t) (heC t)
  have had : StronglyAdapted F (fun t w => j t w - c t w) :=
    fun t => (hj t).sub (hc t)
  have hi (t : NNReal) := (hji t).1.sub (hci t).1
  refine ⟨had, fun u t hut => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le u) (hi t)
    (fun A _ _ => (hi u).integrableOn) (fun A hA _ => ?_)
    (had u).aestronglyMeasurable).symm
  have h := congrArg ENNReal.toReal (hbal u t hut A hA)
  have hfj (r : NNReal) : (∫⁻ w in A, J r w ∂P) ≠ ⊤ :=
    ((calc
      (∫⁻ w in A, J r w ∂P) ≤ ∫⁻ w in Set.univ, J r w ∂P :=
        lintegral_mono_set (Set.subset_univ A)
      _ = ∫⁻ w, J r w ∂P := by rw [Measure.restrict_univ]).trans_lt (hfinJ r)).ne
  have hfc (r : NNReal) : (∫⁻ w in A, C r w ∂P) ≠ ⊤ :=
    ((calc
      (∫⁻ w in A, C r w ∂P) ≤ ∫⁻ w in Set.univ, C r w ∂P :=
        lintegral_mono_set (Set.subset_univ A)
      _ = ∫⁻ w, C r w ∂P := by rw [Measure.restrict_univ]).trans_lt (hfinC r)).ne
  rw [ENNReal.toReal_add (hfj t) (hfc u),
    ENNReal.toReal_add (hfj u) (hfc t)] at h
  change (∫ w in A, j u w - c u w ∂P) = ∫ w in A, j t w - c t w ∂P
  rw [integral_sub (hji u).1.integrableOn (hci u).1.integrableOn,
    integral_sub (hji t).1.integrableOn (hci t).1.integrableOn,
    (hji u).2 A, (hci u).2 A, (hji t).2 A, (hci t).2 A]
  linarith
