-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovDyadicFiniteFibresV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:14:46.798907+00:00
-- url     : https://prove2.me/submissions/5f05b74c-a0fc-4fb5-b91f-4d428f2564fe

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDyadicSublevelV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovGridCellsMeasV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (n : ℕ) (s : NNReal) :
    MeasurableSet[F s] ({w : Omega | tau w ≠ ⊤} ∩ {w | (fun w : Omega => if tau w = ⊤ then (0 : NNReal) else
      (Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) : NNReal) / (2 : NNReal)^n) w = s}) := by
  classical
  let g : ℕ → NNReal := fun j => (j : NNReal) / (2 : NNReal)^n
  let k : Omega → ℕ := fun w => Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n)
  have hg : StrictMono g := by
    intro i j hij
    exact (div_lt_div_iff_of_pos_right (by positivity)).2 (by exact_mod_cast hij)
  have hs := Kyprianou.Ch03.strongMarkovGridCellsMeasV1 F tau hTau g hg k
    (fun j w => Kyprianou.Ch03.strongMarkovDyadicSublevelV1 tau finiteTime hFiniteTime n j w) s
  convert hs using 1
  ext w
  change (tau w ≠ ⊤ ∧ (if tau w = ⊤ then 0 else g (k w)) = s) ↔
    (tau w ≠ ⊤ ∧ g (k w) = s)
  by_cases hw : tau w = ⊤ <;> simp [hw]
