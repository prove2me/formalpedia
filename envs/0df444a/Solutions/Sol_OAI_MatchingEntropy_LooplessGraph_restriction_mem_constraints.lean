-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.restriction_mem_constraints
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:51:45.532355+00:00
-- url     : https://prove2.me/submissions/5259174a-cae2-4f63-9e8d-a860f60b38ac

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Contraction.lean:L404-L427
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.restriction_mem_constraints. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction

-- ---- from OAI.Combinatorics.PerfectMatching.Coupling ----
namespace OAI

/-!
Finite pushforwards and couplings with a prescribed common marginal.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

theorem sum_subtype_supported {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P]
    (w : A → ℝ) (hsupp : ∀ a, ¬P a → w a = 0) :
    (∑ a : {a // P a}, w a.val) = ∑ a, w a := by
  have hh : (∑ a : {a // ¬P a}, w a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hsupp a.val a.property
  simpa only [hh, add_zero] using (Fintype.sum_subtype_add_sum_subtype P w)

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
Contraction of tight odd cuts and gluing of perfect matchings and their laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

theorem liftVertices_card (S : Finset V) (T : Finset (Option {v // v ∈ S}))
    (hn : none ∉ T) : (liftVertices S T).card = T.card := by
  apply Finset.card_bij (fun v _ => sideMap S v)
  · intro v hv
    exact (mem_liftVertices S T v).mp hv
  · intro v hv w hw he
    have hvS : v ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T v).mp hv
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    have hwS : w ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T w).mp hw
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    simp only [sideMap, hvS, hwS, ↓reduceDIte, Option.some.injEq] at he
    exact congrArg Subtype.val he
  · intro t ht
    cases t with
    | none => exact (hn ht).elim
    | some v => exact ⟨v.val, by simpa only [mem_liftVertices, sideMap_some] using ht, sideMap_some S v⟩

omit [Fintype E] [DecidableEq E] in
theorem onSide_cut_crosses (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Crosses T e ↔ G.Crosses (liftVertices S T) e.val := by
  simp only [Crosses, mem_liftVertices]
  rfl

omit [Fintype E] [DecidableEq E] in
theorem crosses_lift_kept (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : E)
    (he : G.Crosses (liftVertices S T) e) : G.left e ∈ S ∨ G.right e ∈ S := by
  by_contra h
  simp only [not_or] at h
  simp only [Crosses, mem_liftVertices, sideMap, h.1, h.2, ↓reduceDIte] at he
  tauto

omit [DecidableEq E] in
theorem onSide_cutMass (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (T : Finset (Option {v // v ∈ S})) :
    (G.onSide S).cutMass (fun e => x e.val) T = G.cutMass x (liftVertices S T) := by
  simp only [cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_cut_crosses S T]
  exact sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses (liftVertices S T) e then x e else 0)
    (by intro e he; rw [ite_eq_right (fun hc => he (G.crosses_lift_kept S T e hc))])

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_some (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (v : {v // v ∈ S}) :
    (G.onSide S).degree (fun e => x e.val) (some v) = G.degree x v.val := by
  simp only [degree]
  simp_rw [G.onSide_incident_some S v]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Incident v.val e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl (h.symm ▸ v.property))
  · exact he (Or.inr (h.symm ▸ v.property))

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_none (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ) :
    (G.onSide S).degree (fun e => x e.val) none = G.cutMass x S := by
  simp only [degree, cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_incident_none S]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses S e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl h.1)
  · exact he (Or.inr h.2)

theorem odd_compl_of_even {W : Type*} [Fintype W] [DecidableEq W]
    (hn : Even (Fintype.card W)) {T : Finset W} (hT : Odd T.card) : Odd Tᶜ.card := by
  rcases hn with ⟨k,hk⟩
  rcases hT with ⟨l,hl⟩
  have hle := Finset.card_le_univ T
  rw [Finset.card_compl]
  refine ⟨k-l-1, ?_⟩
  omega

omit [DecidableEq E] in
/-- Exact inheritance of the odd-cut system under contraction of a tight odd cut. -/
theorem restriction_mem_constraints (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (S : Finset V) (hS : Odd S.card)
    (htight : G.cutMass x S = 1) :
    (fun e : {e // G.left e ∈ S ∨ G.right e ∈ S} => x e.val) ∈
      (G.onSide S).constraintPolytope := by
  refine ⟨fun e => hx.1 e.val, ?_, ?_⟩
  · intro v
    cases v with
    | none => exact (G.onSide_degree_none S x).trans htight
    | some v => exact (G.onSide_degree_some S x v).trans (hx.2.1 v.val)
  · intro T hT
    by_cases hn : none ∈ T
    · have hn' : none ∉ Tᶜ := by simpa using hn
      have hnEven : Even (Fintype.card (Option {v // v ∈ S})) := by
        simp only [Fintype.card_option, Fintype.card_coe]
        exact hS.add_odd odd_one
      have hTc := odd_compl_of_even hnEven hT
      have hh := hx.2.2 (liftVertices S Tᶜ) (by rwa [liftVertices_card S Tᶜ hn'])
      rw [← G.onSide_cutMass S x Tᶜ] at hh
      simpa only [cutMass, cut_compl] using hh
    · rw [G.onSide_cutMass S x T]
      exact hx.2.2 _ (by rwa [liftVertices_card S T hn])

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem solution (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (S : Finset V) (hS : Odd S.card)
    (htight : G.cutMass x S = 1) :
    (fun e : {e // G.left e ∈ S ∨ G.right e ∈ S} => x e.val) ∈
      (G.onSide S).constraintPolytope := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.restriction_mem_constraints G hx S hS htight
    | exact OAI.MatchingEntropy.LooplessGraph.restriction_mem_constraints
    | (apply OAI.MatchingEntropy.LooplessGraph.restriction_mem_constraints <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.restriction_mem_constraints <;> assumption)
