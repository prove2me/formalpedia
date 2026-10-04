-- Prove2me | solution 1 for MDPFinance.Bellman.structure_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:55:19.888965+00:00
-- url     : https://prove2.me/submissions/a7e7ec2d-72f8-4006-b7f1-51107c9cd1f4

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_MDPFinance_Bellman_StructureAssumption

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace StructureCex

/-- Horizon `N = 0`, one state, no actions. -/
noncomputable def M0 : MarkovDecisionModel Unit Empty 0 where
  D := fun _ => ∅
  hD_meas := fun n hn => absurd hn (Nat.not_lt_zero n)
  hD_sel := fun n hn => absurd hn (Nat.not_lt_zero n)
  Q := fun _ => 0
  hQ_prob := fun n hn => absurd hn (Nat.not_lt_zero n)
  r := fun _ _ => 0
  hr_meas := fun _ _ => measurable_const
  g := fun _ => 0
  hg_meas := measurable_const

theorem policy_empty (π : Policy M0) : False := (π.1 0 ()).elim

theorem V_eq_bot (n : ℕ) (x : Unit) : V M0 n x = ⊥ := by
  unfold V
  have : IsEmpty (Policy M0) := ⟨policy_empty⟩
  exact iSup_of_empty _

end StructureCex

open StructureCex in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A))
    (hSAN : StructureAssumption M IMs Deltas),
    (∀ n ≤ N, V M n ∈ IMs n) ∧
    (V M N = fun x => (M.g x : EReal)) ∧
    (∀ n < N, ∀ x, V M n x = ⨆ a ∈ M.Dx n x, (M.r n (x, a) : EReal) + erealIntegral
        (M.Q n (x, a)) (V M (n + 1))) ∧
    (∀ n ≤ N, V M n = TChain M (N - n) n (fun x => (M.g x : EReal))) ∧
    (∀ n < N, ∃ f ∈ Deltas n, IsMaximizer M n (V M (n + 1)) f) ∧
    (∀ fstar : Policy M, (∀ n < N, IsMaximizer M n (V M (n + 1)) (fstar.1 n)) →
        Vpi M fstar 0 = V M 0)) := by
  intro h
  have hAN : IntegrabilityAssumption M0 := by
    intro n _ x
    unfold deltaN
    have : IsEmpty (Policy M0) := ⟨policy_empty⟩
    rw [iSup_of_empty]
    exact bot_lt_top
  have hSAN : StructureAssumption M0 (fun _ => IM Unit) (fun _ => ∅) := by
    refine ⟨fun _ => le_rfl, fun n hn => absurd hn (Nat.not_lt_zero n), ?_,
      fun n hn => absurd hn (Nat.not_lt_zero n), fun n hn => absurd hn (Nat.not_lt_zero n)⟩
    exact ⟨(measurable_const : Measurable fun _ : Unit => ((0:ℝ) : EReal)), fun _ => EReal.coe_ne_top _⟩
  have h2 := (h M0 hAN _ _ hSAN).2.1
  have := congrFun h2 ()
  rw [V_eq_bot] at this
  exact EReal.bot_ne_coe _ this

#print axioms solution
