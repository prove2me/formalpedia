-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46NullPredictableNoJumpsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:21:41.937305+00:00
-- url     : https://prove2.me/submissions/7e18d8e4-4ca0-44ff-9216-5a7b3e2714b9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46PredictableMarkedCountMeanV1
import Theorems.Thm_Kyprianou_Ch04_exercise46MeasurableJumpSubsetCountV1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal m) (L : SpectrallyNegativeLevy P G)
    (T : NNReal) (E : Set (NNReal × Omega))
    (hE : MeasurableSet[G.rightCont.predictable] E)
    (hAmb : MeasurableSet E) (hT : ∀ p ∈ E, p.1 ≤ T)
    (hNull : ((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E = 0) :
    ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → (t,w) ∈ E →
      ¬ L.X t w < Function.leftLim (fun v : NNReal => L.X v w) t := by
  let j : NNReal → Omega → Real := fun t w =>
    L.X t w - Function.leftLim (fun v : NNReal => L.X v w) t
  let S : Set (Omega × NNReal) := {p | 0 < p.2 ∧ (p.2,p.1) ∈ E ∧ j p.2 p.1 < 0}
  have hj : Measurable (fun p : NNReal × Omega => j p.1 p.2) :=
    avram_wave4_04a_actual_levy_jumpmark_joint_measurable L
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      ((measurable_swap hAmb).inter
        (measurableSet_lt (hj.comp measurable_swap) measurable_const))
  let Q : Omega → ENNReal := fun w => (({t : NNReal | (w,t) ∈ S}).encard : ENNReal)
  have hQ : Measurable Q :=
    Kyprianou.Ch04.exercise46MeasurableJumpSubsetCountV1 P G L S hS
      (fun w t ht => ⟨ht.1,ne_of_lt ht.2.2⟩)
  have hc := Kyprianou.Ch04.exercise46PredictableMarkedCountMeanV1 P G L T E hE hT
    (Iio (0 : Real)) measurableSet_Iio (fun _ h => h)
  dsimp only at hc
  rw [hNull,zero_mul] at hc
  have he (w : Omega) :
      ((Measure.count.restrict {u : NNReal | 0 < u ∧ j u w ≠ 0}).map
        (fun u => (u,j u w))) {p | (p.1,w) ∈ E ∧ p.2 ∈ Iio (0 : Real)} = Q w := by
    have hm : Measurable (fun u : NNReal => (u,j u w)) :=
      measurable_id.prodMk (hj.comp (measurable_id.prodMk measurable_const))
    have hs : MeasurableSet {p : NNReal × Real | (p.1,w) ∈ E ∧ p.2 ∈ Iio (0 : Real)} :=
      (hAmb.preimage (measurable_fst.prodMk measurable_const)).inter
        (measurable_snd measurableSet_Iio)
    rw [Measure.map_apply hm hs,Measure.restrict_apply (hs.preimage hm)]
    have hset : ((fun u : NNReal => (u,j u w)) ⁻¹'
          {p | (p.1,w) ∈ E ∧ p.2 ∈ Iio (0 : Real)}) ∩
          {u | 0 < u ∧ j u w ≠ 0} = {t | (w,t) ∈ S} := by
      ext u
      constructor
      · intro h
        exact ⟨h.2.1,h.1.1,h.1.2⟩
      · intro h
        exact ⟨⟨h.2.1,h.2.2⟩,h.1,ne_of_lt h.2.2⟩
    rw [hset]
    exact Measure.count_apply (hS.preimage measurable_prodMk_left)
  have hi : ∫⁻ w, Q w ∂P = 0 := by
    calc
      _ = _ := lintegral_congr (fun w => (he w).symm)
      _ = 0 := hc
  filter_upwards [(lintegral_eq_zero_iff hQ).mp hi] with w hw
  intro t ht hEw hneg
  have htS : (w,t) ∈ S := ⟨ht,hEw,sub_neg.mpr hneg⟩
  have hp : 0 < ({t : NNReal | (w,t) ∈ S}).encard := Set.encard_pos.mpr ⟨t,htS⟩
  have hpos : 0 < Q w := by
    change 0 < (({t : NNReal | (w,t) ∈ S}).encard : ENNReal)
    exact_mod_cast hp
  exact (ne_of_gt hpos) hw
