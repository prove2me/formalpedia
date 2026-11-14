-- Prove2me | solution 1 for KSATSingleFlip.Connect.degree_append_one
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:44:47.673086+00:00
-- url     : https://prove2.me/submissions/67b432b2-378e-495e-9729-87863870f928

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

lemma audit_degree_eq_filter {n : ℕ} (Φ : GFormula (Fin n)) (u : Fin n) :
    degree Φ u = (Φ.filter (fun C => (C u).isSome)).length := by
  induction Φ with
  | nil => simp [degree]
  | cons C Φ ih =>
    unfold degree at ih ⊢
    simp only [List.length_cons] at *
    rw [Fin.card_filter_univ_succ]
    simp only [List.get_cons_zero, List.filter_cons, apply_ite, List.length_cons]
    simp [List.get_eq_getElem] at ih ⊢
    rw [ih]
    split_ifs <;> simp_all


/-- Inserting one clause changes exactly the degrees of its variables. -/
theorem audit_degree_append {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (u : Fin n) :
    degree (Φ ++ [C]) u = degree Φ u + if u ∈ vbl C then 1 else 0 := by
  simp [audit_degree_eq_filter, vbl, List.filter_append]
  split_ifs <;> simp_all

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect
theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (u : Fin n) :
    degree (Φ ++ [C]) u = degree Φ u + if u ∈ vbl C then 1 else 0 := by
  exact audit_degree_append Φ C u

#print axioms solution
