-- Prove2me | solution 1 for OAI.MatchingEntropy.LooplessGraph.faceCodimension_strong_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:08:30.431477+00:00
-- url     : https://prove2.me/submissions/189d7e94-539f-4cf0-b3a8-919c46740778

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Face.lean:L191-L234
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.LooplessGraph.faceCodimension_strong_aux. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_faceSpace_of_side_spaces
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_restriction_mem_constraints
import Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_trivial_tight_cut_preserved
import Theorems.Thm_OAI_MatchingEntropy_quotient_finrank_le_pair

-- ---- from OAI.Combinatorics.PerfectMatching.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem odd_compl_of_even {W : Type*} [Fintype W] [DecidableEq W]
    (hn : Even (Fintype.card W)) {T : Finset W} (hT : Odd T.card) : Odd Tᶜ.card := by
  rcases hn with ⟨k,hk⟩
  rcases hT with ⟨l,hl⟩
  have hle := Finset.card_le_univ T
  rw [Finset.card_compl]
  refine ⟨k-l-1, ?_⟩
  omega

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Polyhedron ----
namespace OAI

/-!
Finite polyhedra, local perturbations, and quotient dimension bounds.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

section PolyhedralPrelude
variable {I J : Type*} [Fintype I] [Fintype J]

section LinearHelper
open Module
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_le_of_ker_le (U : Submodule ℝ A) (f : A →ₗ[ℝ] B)
    (h : f.ker ≤ U) : finrank ℝ (A ⧸ U) ≤ finrank ℝ B := by
  have h1 := U.finrank_quotient_add_finrank
  have h2 := f.finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_mono h
  have h4 : finrank ℝ f.range ≤ finrank ℝ B := Submodule.finrank_le _
  omega

end LinearHelper
end PolyhedralPrelude

end MatchingEntropy

end

end OAI

-- ---- from OAI.Combinatorics.PerfectMatching.Face ----
namespace OAI

/-!
Active face spaces, their codimension bounds, and local radial extension.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [DecidableEq E] in
 theorem faceCodimension_no_tight (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    G.faceCodimension x ≤ Fintype.card V := by
  classical
  let F := G.degreeLinear.comp (positiveExtension x)
  have hk : F.ker ≤ G.faceSpace x := by
    intro u hu
    have hd : G.degreeLinear (positiveExtension x u)=0 := hu
    refine ⟨hd,?_⟩
    exact G.trivial_tight_cut_preserved heven hnt _ (congrFun hd)
  simpa [faceCodimension] using quotient_finrank_le_of_ker_le (G.faceSpace x) F hk

 theorem faceCodimension_le_sides (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1) :
    G.faceCodimension x ≤ (G.onSide S).faceCodimension (G.sideMarginal x S) +
      (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) := by
  classical
  exact quotient_finrank_le_pair (G.faceSpace x) ((G.onSide S).faceSpace (G.sideMarginal x S))
    ((G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ))
    (G.sideRestriction x S) (G.sideRestriction x Sᶜ)
    (fun _ => G.faceSpace_of_side_spaces heven hx S hS ht)

/-- Strong face-codimension induction for even orders at least four. -/
theorem faceCodimension_strong_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, G.faceCodimension x ≤ 2*(n-2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven hfour x hx
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
    · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
      have hc := odd_compl_of_even heven' hS
      have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        omega
      have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        have hle := Finset.card_le_univ S
        omega
      have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
      have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
      have hn1 : 4≤Fintype.card (Option {v // v ∈ S}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hn2 : 4≤Fintype.card (Option {v // v ∈ Sᶜ}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hx1 := G.restriction_mem_constraints hx S hS ht
      have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
      have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
      have hb1 := ih _ hlt1 (G.onSide S) rfl hv1 hn1 _ hx1
      have hb2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 hn2 _ hx2
      have hb := G.faceCodimension_le_sides heven' hx S hS ht
      have hsum : Fintype.card (Option {v // v ∈ S}) + Fintype.card (Option {v // v ∈ Sᶜ})=n+2 := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hh := Finset.card_compl_add_card S
        omega
      change (G.onSide S).faceCodimension (G.sideMarginal x S) ≤ _ at hb1
      change (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) ≤ _ at hb2
      omega
    · have hb := G.faceCodimension_no_tight heven' hcut
      omega

end LooplessGraph

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, G.faceCodimension x ≤ 2*(n-2) := by
  first
    | exact OAI.MatchingEntropy.LooplessGraph.faceCodimension_strong_aux n
    | exact OAI.MatchingEntropy.LooplessGraph.faceCodimension_strong_aux
    | (apply OAI.MatchingEntropy.LooplessGraph.faceCodimension_strong_aux <;> assumption)
    | (intros; apply OAI.MatchingEntropy.LooplessGraph.faceCodimension_strong_aux <;> assumption)
