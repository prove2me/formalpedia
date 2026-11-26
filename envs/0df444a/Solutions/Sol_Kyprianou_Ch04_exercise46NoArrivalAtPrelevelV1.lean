-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46NoArrivalAtPrelevelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:19:26.590411+00:00
-- url     : https://prove2.me/submissions/8f52b748-57d1-4614-9101-5fbfe0a1963a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46JumpFreeLeftAffineV1
import Theorems.Thm_Kyprianou_Ch04_exercise46PrelevelLeftIsolatedV1
import Theorems.Thm_Kyprianou_Ch04_exercise46PredictablePrelevelEventV1
import Theorems.Thm_Kyprianou_Ch04_exercise46PrelevelContactNullV1
import Theorems.Thm_Kyprianou_Ch04_exercise46NullPredictableNoJumpsV1
import Theorems.Thm_AvramDividend_Classical_ripple_predictable_le_ambient_product
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A) :
    ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → A w < (t : WithTop NNReal) →
      Function.leftLim (fun u : NNReal => L.X u w) t =
        (((A w).untopD 0 : NNReal) : Real) →
      ¬ L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t := by
  letI : IsProbabilityMeasure P := L.isProbability
  have hLocal := Kyprianou.Ch04.exercise46JumpFreeLeftAffineV1 P G L hBV hDrift hFinite
  have hHorizon (T : NNReal) : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → t ≤ T →
      A w < (t : WithTop NNReal) →
      Function.leftLim (fun u : NNReal => L.X u w) t =
        (((A w).untopD 0 : NNReal) : Real) →
      ¬ L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t := by
    let E : Set (NNReal × Omega) := {p | A p.2 < (p.1 : WithTop NNReal) ∧
      p.1 ≤ T ∧ Function.leftLim (fun u : NNReal => L.X u p.2) p.1 =
        (((A p.2).untopD 0 : NNReal) : Real)}
    have hE : MeasurableSet[G.rightCont.predictable] E :=
      Kyprianou.Ch04.exercise46PredictablePrelevelEventV1 P G L A hA T
    have hAmb : MeasurableSet E := ripple_predictable_le_ambient_product G.rightCont E hE
    have hCount : ∀ᵐ w ∂P, {t : NNReal | (t,w) ∈ E}.Countable := by
      filter_upwards [hLocal] with w hw
      apply (Kyprianou.Ch04.exercise46PrelevelLeftIsolatedV1
        (fun u => L.X u w) (((A w).untopD 0 : NNReal) : Real) hw).mono
      intro t ht
      exact ⟨WithTop.coe_lt_coe.mp ((show (0 : WithTop NNReal) ≤ A w from
        bot_le).trans_lt ht.1),ht.2.2⟩
    have hNull := Kyprianou.Ch04.exercise46PrelevelContactNullV1 P T E hAmb hCount
    have hNo := Kyprianou.Ch04.exercise46NullPredictableNoJumpsV1
      P G L T E hE hAmb (fun p hp => hp.2.1) hNull
    filter_upwards [hNo] with w hw
    intro t ht hcap ha he
    exact hw t ht ⟨ha,hcap,he⟩
  have hAll := ae_all_iff.mpr (fun n : Nat => hHorizon ((n+1 : Nat) : NNReal))
  filter_upwards [hAll] with w hw
  intro t ht ha he
  obtain ⟨n,hn⟩ := exists_nat_gt t
  exact hw n t ht (hn.le.trans (by exact_mod_cast Nat.le_succ n)) ha he
