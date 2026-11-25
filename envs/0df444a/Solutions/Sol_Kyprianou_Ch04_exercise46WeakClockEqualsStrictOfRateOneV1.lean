-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46WeakClockEqualsStrictOfRateOneV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:49:48.916642+00:00
-- url     : https://prove2.me/submissions/add4b01a-c3c4-456c-969a-1aa28c238c39

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46LowerHeightSequenceV2
import Theorems.Thm_Kyprianou_Ch04_exercise46LowerHeightLaplaceLimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RandomStrictPassageTransformV1
import Theorems.Thm_Kyprianou_Ch04_exercise46KilledDiscountPropertiesV1
import Theorems.Thm_Kyprianou_Ch04_exercise46WeakPassageSandwichV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BoundedPayoffSqueezeAEV1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (J : Omega → Real) (hJ : AEMeasurable J P)
    (hJPositive : ∀ᵐ w ∂P, 0 < J w)
    (hInd : IndepFun J (fun w : Omega => fun t : NNReal => L.X t w) P)
    (phi : Real) (hp : 0 ≤ phi)
    (hStrict : ∀ x : Real, 0 < x →
      (∫ w, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w = ⊤
        then (0 : Real) else Real.exp (-1 *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0 : NNReal) : Real)) ∂P)
        = Real.exp (-phi * x)) :
    (fun w : Omega =>
      sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ J w ≤ L.X t w}) =ᵐ[P]
      (fun w => Kyprianou.Ch03.firstHittingTime L.X (Ioi (J w)) w) := by
  obtain ⟨a, ha, hapos⟩ := Kyprianou.Ch04.exercise46LowerHeightSequenceV2
  let A : Nat → Omega → Real := fun n w => a n (J w)
  let S : Real → Omega → WithTop NNReal := fun y w =>
    Kyprianou.Ch03.firstHittingTime L.X (Ioi y) w
  let T : Omega → WithTop NNReal := fun w => S (J w) w
  let Tn : Nat → Omega → WithTop NNReal := fun n w => S (A n w) w
  let B : Omega → WithTop NNReal := fun w =>
    sInf {v : WithTop NNReal | ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ J w ≤ L.X t w}
  let d : WithTop NNReal → Real := fun z =>
    if z = ⊤ then 0 else Real.exp (-1 * (((z.untopD 0 : NNReal) : Real)))
  obtain ⟨hd, hbd, hanti⟩ := Kyprianou.Ch04.exercise46KilledDiscountPropertiesV1 1 (by norm_num)
  have hda : StrictAnti d := hanti (by norm_num)
  have hAm n : AEMeasurable (A n) P := (ha n).comp_aemeasurable hJ
  have hAp n : ∀ᵐ w ∂P, 0 < A n w :=
    hJPositive.mono fun w hw => ((hapos (J w) hw).1 n).1
  have hAi n : IndepFun (A n) (fun w : Omega => fun t : NNReal => L.X t w) P :=
    hInd.comp (ha n) measurable_id
  have hT := Kyprianou.Ch04.exercise46RandomStrictPassageTransformV1
    P G L J hJ hJPositive hInd 1 phi (by norm_num) hStrict
  have hn n := Kyprianou.Ch04.exercise46RandomStrictPassageTransformV1
    P G L (A n) (hAm n) (hAp n) (hAi n) 1 phi (by norm_num) hStrict
  have hSand : ∀ᵐ w ∂P, d (T w) ≤ d (B w) ∧ ∀ n, d (B w) ≤ d (Tn n w) := by
    filter_upwards [hJPositive] with w hw
    have hs n := Kyprianou.Ch04.exercise46WeakPassageSandwichV1
      P G L (A n w) (J w) ((hapos (J w) hw).1 n).2 w
    exact ⟨hda.antitone (hs 0).2, fun n => hda.antitone (hs n).1⟩
  have hMon : ∀ᵐ w ∂P, Antitone (fun n => d (Tn n w)) := by
    filter_upwards [hJPositive] with w hw
    intro m n hmn
    apply hda.antitone
    change S (A m w) w ≤ S (A n w) w
    unfold S Kyprianou.Ch03.firstHittingTime
    apply sInf_le_sInf
    rintro v ⟨t, ⟨ht, hcross⟩, rfl⟩
    exact ⟨t, ⟨ht, lt_of_le_of_lt ((hapos (J w) hw).2.1 hmn) hcross⟩, rfl⟩
  have hlim := Kyprianou.Ch04.exercise46LowerHeightLaplaceLimitV1 P A J phi hp hAm hAp
    (hJPositive.mono fun w hw => (hapos (J w) hw).2.2)
  have hL : Tendsto (fun n => ∫ w, d (Tn n w) ∂P) atTop
      (nhds (∫ w, d (T w) ∂P)) := by
    rw [show (∫ w, d (T w) ∂P) = ∫ w, Real.exp (-phi * J w) ∂P from hT.2]
    exact hlim.congr (fun n => (hn n).2.symm)
  have hEq := Kyprianou.Ch04.exercise46BoundedPayoffSqueezeAEV1 P
    (fun n w => d (Tn n w)) (fun w => d (T w)) (fun w => d (B w))
    (fun n => hd.comp_aemeasurable (hn n).1) (hd.comp_aemeasurable hT.1)
    (fun n w => hbd _) (fun w => hbd _) hSand hMon hL
  exact hEq.mono fun w hw => hda.injective hw
