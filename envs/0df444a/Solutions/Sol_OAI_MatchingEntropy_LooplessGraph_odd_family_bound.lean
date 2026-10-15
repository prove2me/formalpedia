-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.odd_family_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:56:18.795029+00:00
-- url     : https://prove2.me/submissions/6c6fc5b1-72ce-40f7-9c4e-09f60ed24e12

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Polytope.lean:L50-L137
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.odd_family_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope

-- ---- from OAI.Combinatorics.PerfectMatching.Polytope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
Tutte's criterion and Edmonds' perfect matching polytope theorem for multigraphs.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

theorem sum_pred_le_one {C : Type*} [Fintype C] (P : C → Prop) [DecidablePred P]
    (huniq : ∀ a b, P a → P b → a=b) : (∑ c, if P c then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ a, P a
  · obtain ⟨a,ha⟩ := h
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      rw [ite_eq_right]
      intro hPb
      exact hb (huniq b a hPb ha)
    · simp
  · simp only [not_exists] at h
    simp [h]

omit [Fintype V] [DecidableEq E] in
/-- The weighted cut-counting argument in Tutte's criterion. -/
theorem odd_family_bound (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {C : Type*} [Fintype C] [DecidableEq C]
    (U : Finset V) (T : C → Finset V)
    (hodd : ∀ c, Odd (T c).card)
    (hdisj : ∀ c v, v ∈ T c → v ∉ U)
    (huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b)
    (hclosed : ∀ e, 0 < x e → G.left e ∉ U → G.right e ∉ U →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c) :
    Fintype.card C ≤ U.card := by
  have hcuts : (Fintype.card C : ℝ) ≤ ∑ c, G.cutMass x (T c) := by
    calc
      _ = ∑ c : C, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ => hx.2.2 (T c) (hodd c)
  have hedges : ∀ e, (∑ c, if G.Crosses (T c) e then x e else 0) ≤
      (if G.left e ∈ U then x e else 0) + (if G.right e ∈ U then x e else 0) := by
    intro e
    by_cases hz : x e=0
    · simp [hz]
    have hp : 0 < x e := lt_of_le_of_ne (hx.1 e) (Ne.symm hz)
    by_cases hl : G.left e ∈ U <;> by_cases hr : G.right e ∈ U
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        rcases hc with h | h
        · exact hdisj c _ h.1 hl
        · exact hdisj c _ h.2 hr
      simp [hzero, hl, hr, hx.1 e]
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.right e ∈ T c := by
        intro c
        have hn : G.left e ∉ T c := fun h => hdisj c _ h hl
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.right e ∈ T c)
        (fun a b => huniq a b (G.right e))
      have heq' : (∑ c, if G.right e ∈ T c then x e else 0) =
          (∑ c, if G.right e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.left e ∈ T c := by
        intro c
        have hn : G.right e ∉ T c := fun h => hdisj c _ h hr
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.left e ∈ T c)
        (fun a b => huniq a b (G.left e))
      have heq' : (∑ c, if G.left e ∈ T c then x e else 0) =
          (∑ c, if G.left e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        have hiff := hclosed e hp hl hr c
        unfold Crosses at hc
        tauto
      simp [hzero, hl, hr]
  have hdegree : ∑ v ∈ U, G.degree x v = (U.card : ℝ) := by
    simp_rw [hx.2.1]
    simp
  have hsum : (∑ e : E, ((if G.left e ∈ U then x e else 0) +
      (if G.right e ∈ U then x e else 0))) = ∑ v ∈ U, G.degree x v := by
    simp only [degree]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have hf : ∀ v, (if G.Incident v e then x e else 0) =
        (if G.left e = v then x e else 0) + (if G.right e = v then x e else 0) := by
      intro v
      by_cases hl : G.left e=v <;> by_cases hr : G.right e=v
      · exact (G.loopless e (hl.trans hr.symm)).elim
      all_goals simp [Incident, hl, hr]
    simp_rw [hf]
    rw [Finset.sum_add_distrib]
    simp
  have hbound := (Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hedges e))
  rw [hsum, hdegree] at hbound
  have hcutEq : (∑ c, G.cutMass x (T c)) = ∑ e, ∑ c, if G.Crosses (T c) e then x e else 0 := by
    simp only [cutMass, cut, Finset.sum_filter]
    exact Finset.sum_comm
  exact_mod_cast hcuts.trans (hcutEq ▸ hbound)

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq E] in
theorem solution (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {C : Type*} [Fintype C] [DecidableEq C]
    (U : Finset V) (T : C → Finset V)
    (hodd : ∀ c, Odd (T c).card)
    (hdisj : ∀ c v, v ∈ T c → v ∉ U)
    (huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b)
    (hclosed : ∀ e, 0 < x e → G.left e ∉ U → G.right e ∉ U →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c) :
    Fintype.card C ≤ U.card := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.odd_family_bound G hx U T hodd hdisj huniq hclosed
    | exact OAI.MatchingEntropy.LooplessGraph.odd_family_bound
    | (apply OAI.MatchingEntropy.LooplessGraph.odd_family_bound <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.odd_family_bound <;> assumption)
