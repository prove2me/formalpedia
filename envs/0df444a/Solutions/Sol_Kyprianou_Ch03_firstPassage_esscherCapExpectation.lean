-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassage_esscherCapExpectation
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:28:33.112325+00:00
-- url     : https://prove2.me/submissions/1cd4db17-fecc-4015-9c78-149c02f25002

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassage_creepingOnFiniteHit
import Theorems.Thm_Kyprianou_Ch03_firstPassage_esscherCap_trueStoppedMeanOne

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Reduction of the capped Esscher identity (with creeping rewrite $X_τ = x$) to:
1. the Proved pathwise creeping lemma `firstPassage_creepingOnFiniteHit`;
2. the optional-sampling child `firstPassage_esscherCap_trueStoppedMeanOne`
   (true stopped position $X_{τ∧T}$, mean one).
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : Real) (hq : 0 < q)
    (phi : Real)
    (hRoot : 0 ≤ phi ∧ L.ψ phi = q ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = q → theta ≤ phi))
    (x : Real) (hx : 0 < x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal))
    (T : NNReal) :
    (∫ omega,
      (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
          finiteTime omega ≤ T
        then Real.exp (phi * x - q * (finiteTime omega : Real))
        else Real.exp (phi * L.X T omega - q * (T : Real))) ∂P) = 1 := by
  -- Retain source-exact unused hypothesis.
  have _ := hNotDecreasing
  have hCreep :
      ∀ᵐ omega ∂P,
        firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ →
          L.X (finiteTime omega) omega = x :=
    firstPassage_creepingOnFiniteHit P F L x hx.le finiteTime hfin
  have hTrue :
      (∫ omega,
        Real.exp (phi *
            (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
                finiteTime omega ≤ T
              then L.X (finiteTime omega) omega
              else L.X T omega)
          - q *
            (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
                finiteTime omega ≤ T
              then (finiteTime omega : Real)
              else (T : Real))) ∂P) = 1 :=
    firstPassage_esscherCap_trueStoppedMeanOne P F L hNotDecreasing q hq phi hRoot x hx
      finiteTime hfin T
  have hae :
      (fun omega =>
        if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧ finiteTime omega ≤ T
        then Real.exp (phi * x - q * (finiteTime omega : Real))
        else Real.exp (phi * L.X T omega - q * (T : Real))) =ᵐ[P]
      (fun omega =>
        Real.exp (phi *
            (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
                finiteTime omega ≤ T
              then L.X (finiteTime omega) omega
              else L.X T omega)
          - q *
            (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
                finiteTime omega ≤ T
              then (finiteTime omega : Real)
              else (T : Real)))) := by
    filter_upwards [hCreep] with ω hω
    by_cases hcap :
      firstHittingTime L.X (Set.Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ T
    · have hX : L.X (finiteTime ω) ω = x := hω hcap.1
      simp [hcap, hX]
    · simp [hcap]
  rw [integral_congr_ae hae, hTrue]
