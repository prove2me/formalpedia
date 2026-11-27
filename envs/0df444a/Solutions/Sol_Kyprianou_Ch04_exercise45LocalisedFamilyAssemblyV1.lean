-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45LocalisedFamilyAssemblyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:39:50.232975+00:00
-- url     : https://prove2.me/submissions/9b03ea56-e8a9-4221-9d82-4d2fed6d547d

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_exercise45UCPPrefixConsistencyV1
import Theorems.Thm_Kyprianou_Ch04_gluedLocalMartingaleStoppedEqV1
import Theorems.Thm_Kyprianou_Ch04_exercise45CofinalGoodProbabilityV1
import Theorems.Thm_Kyprianou_Ch04_exercise45LocalisedGridTransferV1
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Consistency and UCP for a glued family of local integral witnesses. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X H D R : NNReal → Ω → ℝ)
    (Hn Dn Rn Mn : ℕ → NNReal → Ω → ℝ) (τ : ℕ → Ω → NNReal)
    (hMeas : ∀ n T, MeasurableSet {w | τ n w ≤ T})
    (hMono : ∀ w, Monotone (fun n => τ n w))
    (hCof : ∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤))
    (hPrefix : ∀ᵐ w ∂P, ∀ n t, t ≤ τ n w → Hn n t w = H t w ∧ Dn n t w = D t w)
    (hResidual : ∀ᵐ w ∂P, ∀ n t, t < τ n w → Rn n t w = R t w)
    (hUCP : ∀ n, IsStochasticIntegralInProbabilityV2 P X (Hn n) (fun t w => Dn n t w + Mn n t w))
    (hIto : ∀ n, ∀ᵐ w ∂P, ∀ t, Rn n t w = Dn n t w + Mn n t w) :
    let M : NNReal → Ω → ℝ := fun t w =>
      if h : ∃ k : ℕ, t ≤ τ k w then Mn (Nat.find h) t w else 0
    (∀ᵐ w ∂P, ∀ n m : ℕ, n ≤ m → ∀ t,
      Mn m (min t (τ n w)) w = Mn n (min t (τ n w)) w) ∧
    IsStochasticIntegralInProbabilityV2 P X H (fun t w => D t w + M t w) ∧
    (∀ᵐ w ∂P, ∀ t, R t w = D t w + M t w) := by
  intro M
  have hpair (n m : ℕ) (hnm : n ≤ m) : ∀ᵐ w ∂P, ∀ t ≤ τ n w, Mn m t w = Mn n t w := by
    have hH : ∀ᵐ w ∂P, ∀ t ≤ τ n w, Hn n t w = Hn m t w :=
      hPrefix.mono fun w hw t ht =>
        (hw n t ht).1.trans (hw m t (ht.trans (hMono w hnm))).1.symm
    have hI := exercise45UCPPrefixConsistencyV1 P X (Hn n) (Hn m)
      (fun t w => Dn n t w + Mn n t w) (fun t w => Dn m t w + Mn m t w)
      (τ n) (hUCP n) (hUCP m) hH
    filter_upwards [hI,hPrefix] with w hw hp
    intro t ht
    linarith only [hw t ht,(hp n t ht).2,(hp m t (ht.trans (hMono w hnm))).2]
  have hcons : ∀ᵐ w ∂P, ∀ n m : ℕ, n ≤ m → ∀ t,
      Mn m (min t (τ n w)) w = Mn n (min t (τ n w)) w := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro m
    by_cases hnm : n ≤ m
    · exact (hpair n m hnm).mono fun w hw _ t => hw _ (min_le_right _ _)
    · exact Eventually.of_forall fun _ h => (hnm h).elim
  have hGlue := gluedLocalMartingaleStoppedEqV1 P Mn τ (Eventually.of_forall hMono) hcons
  let G (w : Ω) := ∀ n t, t ≤ τ n w →
    Hn n t w = H t w ∧ Dn n t w = D t w ∧ M t w = Mn n t w
  have hG : ∀ᵐ w ∂P, G w := by
    filter_upwards [hPrefix,hGlue] with w hp hg
    intro n t ht
    exact ⟨(hp n t ht).1,(hp n t ht).2,by
      simpa only [min_eq_left ht] using hg n t⟩
  let B (T : NNReal) (n : ℕ) := {w | ¬ G w ∨ τ n w ≤ T}
  refine ⟨hcons,?_,?_⟩
  · apply exercise45LocalisedGridTransferV1 P X H (fun t w => D t w + M t w) Hn
      (fun n t w => Dn n t w + Mn n t w) B
      (exercise45CofinalGoodProbabilityV1 P τ hMeas hMono hCof G hG) hUCP
    intro T n w hw t ht
    have h : ¬ (¬ G w ∨ τ n w ≤ T) := hw
    have hg := (not_or.mp h).1
    have hclock := ht.trans (le_of_lt (lt_of_not_ge (not_or.mp h).2))
    obtain ⟨hh,hd,hm⟩ := (not_not.mp hg) n t hclock
    exact ⟨hh.symm,by rw [hd,hm]⟩
  · have hall := ae_all_iff.mpr hIto
    filter_upwards [hG,hResidual,hall,hCof] with w hg hr hi hc
    intro t
    rw [WithTop.tendsto_nhds_top_iff] at hc
    obtain ⟨n,hn⟩ := (hc t).exists
    have ht := WithTop.coe_lt_coe.mp hn
    rw [← hr n t ht,hi n t,(hg n t ht.le).2.1,← (hg n t ht.le).2.2]
