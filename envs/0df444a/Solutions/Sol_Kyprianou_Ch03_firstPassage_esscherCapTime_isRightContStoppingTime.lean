-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassage_esscherCapTime_isRightContStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:00:04.657789+00:00
-- url     : https://prove2.me/submissions/bdfe8f4a-4992-4346-b2a9-ff2f788e409f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassage_firstHittingIoi_isRightContStoppingTime

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Capped first-passage time `τ_x^+ ∧ T` is an `F.rightCont`-stopping time.

Reduction: import that `τ_x^+` itself is an `F₊`-stopping time, identify the
capped selector expression with `min τ T` via `hfin`, then apply
`IsStoppingTime.min_const`. The pathwise bound `σ ≤ T` is immediate.
-/

namespace Kyprianou.Ch03

private lemma cap_eq_min_firstHitting
    {Omega : Type} [MeasurableSpace Omega]
    (X : NNReal → Omega → Real)
    (x : Real)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime X (Set.Ioi x) omega != ⊤ →
        firstHittingTime X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal))
    (T : NNReal) (omega : Omega) :
    ((if firstHittingTime X (Set.Ioi x) omega ≠ ⊤ ∧
        finiteTime omega ≤ T
      then finiteTime omega
      else T) : WithTop NNReal) =
      min (firstHittingTime X (Set.Ioi x) omega) (T : WithTop NNReal) := by
  by_cases htop : firstHittingTime X (Set.Ioi x) omega = ⊤
  · -- Both sides equal `↑T`.
    have hcond : ¬ (firstHittingTime X (Set.Ioi x) omega ≠ ⊤ ∧ finiteTime omega ≤ T) := by
      intro h; exact h.1 htop
    rw [if_neg hcond, htop, min_eq_right le_top]
  · have hbne : firstHittingTime X (Set.Ioi x) omega != ⊤ := by
      simpa [bne_iff_ne] using htop
    have hft : firstHittingTime X (Set.Ioi x) omega =
        (finiteTime omega : WithTop NNReal) := hfin omega hbne
    cases hτ : firstHittingTime X (Set.Ioi x) omega with
    | top => exact absurd hτ htop
    | coe t =>
      have ht_eq : finiteTime omega = t := by
        have : (finiteTime omega : WithTop NNReal) = (t : WithTop NNReal) := by
          rw [← hft, hτ]
        exact WithTop.coe_injective this
      -- After `cases`, LHS already has `↑t` in the ≠⊤ conjunct; RHS is `min ↑t ↑T`.
      rw [ht_eq]
      have hcoe_ne : (t : WithTop NNReal) ≠ ⊤ := WithTop.coe_ne_top
      by_cases hle : t ≤ T
      · have hcond : (t : WithTop NNReal) ≠ ⊤ ∧ t ≤ T := ⟨hcoe_ne, hle⟩
        rw [if_pos hcond, min_eq_left (WithTop.coe_le_coe.mpr hle)]
      · have hcond : ¬ ((t : WithTop NNReal) ≠ ⊤ ∧ t ≤ T) := by
          intro h; exact hle h.2
        have hle' : (T : WithTop NNReal) ≤ (t : WithTop NNReal) :=
          WithTop.coe_le_coe.mpr (le_of_lt (lt_of_not_ge hle))
        rw [if_neg hcond, min_eq_right hle']

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 < x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal))
    (T : NNReal) :
    IsStoppingTime F.rightCont
      (fun omega =>
        ((if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
            finiteTime omega ≤ T
          then finiteTime omega
          else T) : WithTop NNReal)) ∧
    (∀ omega,
      (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
          finiteTime omega ≤ T
        then finiteTime omega
        else T) ≤ T) := by
  refine ⟨?_, ?_⟩
  · have hτstop :
        IsStoppingTime F.rightCont
          (fun omega => firstHittingTime L.X (Set.Ioi x) omega) :=
      firstPassage_firstHittingIoi_isRightContStoppingTime P F L x hx
    have heq :
        (fun omega =>
          ((if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
              finiteTime omega ≤ T
            then finiteTime omega
            else T) : WithTop NNReal)) =
          (fun omega =>
            min (firstHittingTime L.X (Set.Ioi x) omega) (T : WithTop NNReal)) :=
      funext fun omega =>
        cap_eq_min_firstHitting L.X x finiteTime hfin T omega
    rw [heq]
    exact hτstop.min_const T
  · intro omega
    split_ifs with h
    · exact h.2
    · exact le_rfl
