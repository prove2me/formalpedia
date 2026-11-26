-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstServiceMarkLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:40:44.685188+00:00
-- url     : https://prove2.me/submissions/64e9ffc9-feab-4bcc-a69a-e96917b78abb

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstMarkTruncatedCompensationV1
import Theorems.Thm_Kyprianou_Ch04_exercise46MarkLawFromTruncatedProportionsV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FiniteArrivalIntensityV1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hFirst : ∀ᵐ w ∂P, A w = ((A w).untopD 0 : NNReal) ∧
      0 < (A w).untopD 0 ∧
      L.X ((A w).untopD 0) w <
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0) ∧
      ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν = ENNReal.ofReal lambda • service.map (fun x : Real => -x)) :
    let J : Omega → Real := fun w =>
      -(L.X ((A w).untopD 0) w -
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0))
    Measurable J ∧ P.map J = service := by
  classical
  dsimp only
  let j : Omega → Real := fun w => L.X ((A w).untopD 0) w -
    Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0)
  let J : Omega → Real := fun w => -j w
  have hAm : Measurable A := hA.measurable'
  have hj : Measurable j :=
    (avram_wave4_04a_actual_levy_jumpmark_joint_measurable L).comp
      (((WithTop.measurable_untopD (0 : NNReal)).comp hAm).prodMk measurable_id)
  have hJ : Measurable J := hj.neg
  refine ⟨hJ, ?_⟩
  let D : Nat → Set Omega := fun n => {w | A w ≤ ((n : NNReal) : WithTop NNReal)}
  have hD : Monotone D := by
    intro n m hnm w hw
    change A w ≤ ((n : NNReal) : WithTop NNReal) at hw
    change A w ≤ ((m : NNReal) : WithTop NNReal)
    have hn : (n : NNReal) ≤ (m : NNReal) := Nat.cast_le.mpr hnm
    exact hw.trans (WithTop.coe_le_coe.mpr hn)
  have hFull : (⋃ n, D n) =ᵐ[P] (univ : Set Omega) := by
    filter_upwards [hFirst] with w hw
    apply propext
    change w ∈ (⋃ n, D n) ↔ w ∈ (univ : Set Omega)
    refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_ge ((A w).untopD 0)
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change A w ≤ ((n : NNReal) : WithTop NNReal)
    rw [hw.1]
    exact WithTop.coe_le_coe.mpr hn
  have hs : ∀ᵐ y ∂service, y ∈ Ioi (0 : Real) := by
    rw [ae_iff]
    change service (Ioi (0 : Real))ᶜ = 0
    rw [measure_compl measurableSet_Ioi (by rw [hServicePositive]; exact ENNReal.one_ne_top),
      hServicePositive, measure_univ, tsub_self]
  have hrate := Kyprianou.Ch04.exercise46FiniteArrivalIntensityV1
    P G L lambda hlambda service hServicePositive hInputLaw
  apply Kyprianou.Ch04.exercise46MarkLawFromTruncatedProportionsV1
    P service J hJ.aemeasurable D hD hFull
  intro n C hC
  let B : Set Real := (fun x : Real => -x) ⁻¹' C ∩ Iio 0
  have hB : MeasurableSet B := (hC.preimage measurable_neg).inter measurableSet_Iio
  have hν : L.ν B = ENNReal.ofReal lambda * service C := by
    rw [hInputLaw, Measure.smul_apply, Measure.map_apply measurable_neg hB]
    change ENNReal.ofReal lambda * service ((fun x : Real => -x) ⁻¹' B) = _
    congr 1
    apply measure_congr
    filter_upwards [hs] with y hy
    apply propext
    change (-(-y) ∈ C ∧ -y < 0) ↔ y ∈ C
    have hypos : 0 < y := mem_Ioi.mp hy
    rw [neg_neg]
    exact ⟨And.left, fun h => ⟨h, neg_lt_zero.mpr hypos⟩⟩
  have h0 := Kyprianou.Ch04.exercise46FirstMarkTruncatedCompensationV1
    P G L A hA hAm hFirst (n : NNReal) (Iio 0) measurableSet_Iio (Subset.rfl)
  have h1 := Kyprianou.Ch04.exercise46FirstMarkTruncatedCompensationV1
    P G L A hA hAm hFirst (n : NNReal) B hB (inter_subset_right)
  dsimp only at h0 h1
  rw [hrate] at h0
  rw [hν] at h1
  have e0 : D n =ᵐ[P] {w | A w ≤ ((n : NNReal) : WithTop NNReal) ∧ j w ∈ Iio 0} := by
    filter_upwards [hFirst] with w hw
    apply propext
    change A w ≤ _ ↔ A w ≤ _ ∧ j w < 0
    exact ⟨fun h => ⟨h, sub_neg.mpr hw.2.2.1⟩, And.left⟩
  have e1 : (D n ∩ J ⁻¹' C : Set Omega) =ᵐ[P]
      {w | A w ≤ ((n : NNReal) : WithTop NNReal) ∧ j w ∈ B} := by
    filter_upwards [hFirst] with w hw
    apply propext
    change (A w ≤ _ ∧ -j w ∈ C) ↔ A w ≤ _ ∧ (-j w ∈ C ∧ j w < 0)
    have hjn : j w < 0 := sub_neg.mpr hw.2.2.1
    tauto
  rw [measure_congr e1]
  change P {w | A w ≤ ((n : NNReal) : WithTop NNReal) ∧ j w ∈ B} = _
  rw [h1, ← mul_assoc, ← h0, measure_congr e0]
