-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassage_esscherCap_meanOne_of_rightContStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:50:58.445899+00:00
-- url     : https://prove2.me/submissions/32400142-9efb-41ea-abb7-d220ed90c8c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Esscher mean-one at the capped first-passage time, given an `F.rightCont` stopping-time
hypothesis. Splices the Proved
`avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one`
and rewrites with `L.ψ phi = q`.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
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
    (T : NNReal)
    (hstop : IsStoppingTime F.rightCont
      (fun omega =>
        ((if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
            finiteTime omega ≤ T
          then finiteTime omega
          else T) : WithTop NNReal)))
    (hbound : ∀ omega,
      (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
          finiteTime omega ≤ T
        then finiteTime omega
        else T) ≤ T) :
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
            else (T : Real))) ∂P) = 1 := by
  have _ := hq
  have _ := hx
  have _ := hfin
  have hψ : L.ψ phi = q := hRoot.2.1
  let cap : Omega → NNReal := fun omega =>
    if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧ finiteTime omega ≤ T
    then finiteTime omega else T
  have hcoe_cap :
      ∀ omega,
        (cap omega : WithTop NNReal) =
          (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧ finiteTime omega ≤ T
            then (finiteTime omega : WithTop NNReal)
            else (T : WithTop NNReal)) := by
    intro omega
    dsimp only [cap]
    rw [apply_ite (fun t : NNReal => (t : WithTop NNReal))]
  have hstop' : IsStoppingTime F.rightCont (fun omega => (cap omega : WithTop NNReal)) := by
    have heq :
        (fun omega => (cap omega : WithTop NNReal)) =
          (fun omega =>
            if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧ finiteTime omega ≤ T
            then (finiteTime omega : WithTop NNReal)
            else (T : WithTop NNReal)) :=
      funext hcoe_cap
    rwa [heq]
  have hbound' : ∀ omega, cap omega ≤ T := hbound
  have hmean :
      (∫ omega, Real.exp (phi * L.X (cap omega) omega -
        (cap omega : Real) * L.ψ phi) ∂P) = 1 :=
    AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
      L phi hRoot.1 cap hstop' T hbound'
  have hmean' :
      (∫ omega, Real.exp (phi * L.X (cap omega) omega -
        q * (cap omega : Real)) ∂P) = 1 := by
    rw [← hmean]
    congr 1
    funext omega
    rw [hψ, mul_comm (cap omega : Real) q]
  have hintegrand :
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
              else (T : Real)))) =
      (fun omega =>
        Real.exp (phi * L.X (cap omega) omega - q * (cap omega : Real))) := by
    funext omega
    dsimp only [cap]
    split_ifs <;> rfl
  rw [hintegrand, hmean']
