-- Prove2me | solution 1 for MooreLateJobs.MaxDeferral.bounded_exists_feasible_level
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:06:04.083992+00:00
-- url     : https://prove2.me/submissions/c908b839-990e-4bb5-8a16-ffd775d6213d

import Definitions.Def_MooreLateJobs_MaxDeferral_NoLateAt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
open MooreLateJobs.MaxDeferral
open scoped BigOperators

theorem solution {ι : Type*} [DecidableEq ι] (J : Finset ι) (t : ι → ℝ)
    (P : ι → ℝ → ℝ) (ht : ∀ i ∈ J, 0 ≤ t i)
    (hcont : ∀ i ∈ J, Continuous (P i)) (hbdd : ∀ i ∈ J, ∃ M, ∀ s, |P i s| ≤ M)
    (hmono : ∀ i ∈ J, Monotone (P i)) (SD : ℝ → List ι)
    (hSD : ∀ y, 0 < y →
      MooreLateJobs.Shared.IsSchedule J (SD y) ∧ (SD y).Pairwise (fun a b => Pstar (P a) y ≤ Pstar (P b) y)) :
    ∃ y, 0 < y ∧ NoLateAt t P y (SD y) := by
  classical
  let M : ι → ℝ := fun i => if hi : i∈J then (hbdd i hi).choose else 0
  let y := 1+∑ i∈J, |M i|
  have hy : 0 < y := by dsimp [y]; positivity
  have hb (i : ι) (hi : i∈J) (s : ℝ) : P i s < y := by
    have h1 : |P i s| ≤ M i := by simp only [M,dif_pos hi]; exact (hbdd i hi).choose_spec s
    have h2 : |M i| ≤ ∑ j∈J, |M j| := Finset.single_le_sum (fun j hj => abs_nonneg (M j)) hi
    have h3 := le_abs_self (P i s)
    have h4 := le_abs_self (M i)
    dsimp [y]
    linarith
  have hp (i : ι) (hi : i∈J) : Pstar (P i) y=⊤ := by
    have hn : ¬∃ s, 0 ≤ s ∧ P i s=y := by rintro ⟨s,hs,he⟩; have hh := hb i hi s; linarith
    have hn' : ¬∀ s, 0 ≤ s → y < P i s := by intro hh; have h := hh 0 le_rfl; linarith [hb i hi 0]
    simp only [Pstar,if_neg hn,if_neg hn']
  refine ⟨y,hy,?_⟩
  intro j hj
  have hjJ := (hSD y hy).1.2 j |>.mp hj
  simp [IsLate,dueDates,hp j hjJ]

