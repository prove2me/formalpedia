-- Prove2me | solution 1 for KSATSingleFlip.Connect.append_ballVars_mono
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:45:24.469232+00:00
-- url     : https://prove2.me/submissions/6e6f0ffd-62ab-4c77-9ab4-94c1bc87c1e4

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

lemma audit_adj_var_clause {n : ℕ} (Φ : GFormula (Fin n)) (v : Fin n) (c : Fin Φ.length) :
    (factorGraph Φ).Adj (Sum.inl v) (Sum.inr c) ↔ v ∈ vbl (Φ.get c) := by
  simp [factorGraph, SimpleGraph.fromRel_adj, vbl]

def audit_oldNode {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) :
    (Fin n ⊕ Fin Φ.length) → (Fin n ⊕ Fin (Φ ++ [C]).length) :=
  Sum.map id (Fin.castLE (by simp))

lemma audit_get_append {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (c : Fin Φ.length) :
    (Φ ++ [C]).get (Fin.castLE (by simp) c) = Φ.get c := by
  simp [List.get_eq_getElem]

lemma audit_oldNode_inj {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) :
    Function.Injective (audit_oldNode Φ C) := by
  intro x y h
  cases x <;> cases y <;> simp_all [audit_oldNode, Fin.ext_iff]

def audit_oldHom {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) :
    factorGraph Φ →g factorGraph (Φ ++ [C]) where
  toFun := audit_oldNode Φ C
  map_rel' := by
    intro x y h
    simp only [factorGraph, SimpleGraph.fromRel_adj] at h ⊢
    refine ⟨fun e => h.1 (audit_oldNode_inj Φ C e), ?_⟩
    rcases h.2 with hxy | hyx
    · left
      obtain ⟨v,c,rfl,rfl,hc⟩ := hxy
      exact ⟨v, Fin.castLE (by simp) c, rfl, rfl, by simpa [audit_get_append] using hc⟩
    · right
      obtain ⟨v,c,rfl,rfl,hc⟩ := hyx
      exact ⟨v, Fin.castLE (by simp) c, rfl, rfl, by simpa [audit_get_append] using hc⟩

theorem audit_append_ballVars_mono {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (v : Fin n) (r : ℕ) : ballVars Φ v r ⊆ ballVars (Φ ++ [C]) v r := by
  intro u hu
  have hdist : withinDist Φ (Sum.inl v) (Sum.inl u) (2*r) := by simpa [ballVars] using hu
  obtain ⟨p,hp⟩ := hdist.1.exists_walk_length_eq_dist
  have hlen : p.length ≤ 2*r := by simpa [hp] using hdist.2
  let p' := p.map (audit_oldHom Φ C)
  have h' : withinDist (Φ ++ [C]) (Sum.inl v) (Sum.inl u) (2*r) := by
    refine ⟨p'.reachable, ?_⟩
    exact le_trans (SimpleGraph.dist_le p') (by simpa [p'] using hlen)
  simpa [ballVars] using h'
end KSATSingleFlip.Connect

open KSATSingleFlip.Connect
theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n))
    (v : Fin n) (r : ℕ) : ballVars Φ v r ⊆ ballVars (Φ ++ [C]) v r := by
  exact audit_append_ballVars_mono Φ C v r

#print axioms solution
