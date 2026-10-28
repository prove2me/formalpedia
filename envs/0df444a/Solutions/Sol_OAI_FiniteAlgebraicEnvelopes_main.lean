-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T15:49:17.610991+00:00
-- url     : https://prove2.me/submissions/e576f0dc-da1b-4f54-9321-d2f555355c1b

import Mathlib
import Definitions.Def_BooneHigman
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem
import Theorems.Thm_WordProblem_re_eq_one_of_isFinitelyPresented
import Theorems.Thm_WordProblem_re_ne_one_of_isFinitelyPresented_simple
import Theorems.Thm_WordProblem_computablePred_of_hasDecidableWordProblem

open OAI.FiniteAlgebraicEnvelopes

namespace OAI

namespace FiniteAlgebraicEnvelopes

universe u

/-- `evalWord` of a composed tuple is the image of `evalWord` under the homomorphism:
elementary, proved outright. -/
theorem evalWord_comp {G H : Type u} [Group G] [Group H] (φ : G →* H) {n : ℕ}
    (tuple : Fin n → G) (word : Word n) :
    evalWord (φ ∘ tuple) word = φ (evalWord tuple word) := by
  classical
  unfold evalWord
  rw [map_list_prod]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro letter _
  by_cases h : letter.2 <;> simp [h, Function.comp_apply]

/-- A finitely presented simple group has decidable word problem (w.r.t. its own
presentation-derived generating tuple). Assembled from the two imported `WordProblem`
r.e./co-r.e. facts via Post's theorem (`ComputablePred.computable_iff_re_compl_re'`). -/
theorem hasDecidableWordProblem_of_finitelyPresented_simple
    (H : Type u) [Group H] [Group.IsFinitelyPresented H] [IsSimpleGroup H] :
    HasDecidableWordProblem H := by
  classical
  obtain ⟨n, π, hπsurj, -⟩ := ‹Group.IsFinitelyPresented H›.out
  set p : Fin n → H := fun i => π (FreeGroup.of i) with hp_def
  have hp : Subgroup.closure (Set.range p) = ⊤ := by
    have h1 : Subgroup.closure (Set.range (FreeGroup.of (α := Fin n))) = ⊤ :=
      FreeGroup.closure_range_of (Fin n)
    have h2 : (Subgroup.closure (Set.range (FreeGroup.of (α := Fin n)))).map π
        = Subgroup.closure (Set.range p) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_range, hp_def]
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨FreeGroup.of i, ⟨i, rfl⟩, rfl⟩
    rw [h1] at h2
    rw [← h2, Subgroup.map_top_of_surjective π hπsurj]
  exact ⟨n, p, hp, ComputablePred.computable_iff_re_compl_re'.2
    ⟨WordProblem.re_eq_one_of_isFinitelyPresented p hp,
     WordProblem.re_ne_one_of_isFinitelyPresented_simple p hp⟩⟩

end FiniteAlgebraicEnvelopes

end OAI

universe u

open OAI.FiniteAlgebraicEnvelopes in
theorem solution (GroupType : Type u) [Group GroupType] [Group.FG GroupType] :
    HasDecidableWordProblem GroupType ↔ EmbedsInFinitelyPresentedSimpleGroup GroupType := by
  classical
  constructor
  · exact embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem GroupType
  · intro h
    obtain ⟨TargetGroup, _, hfp, hsimple, φ, hφinj⟩ := h
    obtain ⟨n, g, hcard, hgclosure⟩ := Group.fg_iff'.1 ‹Group.FG GroupType›
    let e : Fin n ≃ g := (Fintype.equivFinOfCardEq (α := g) (by simpa using hcard)).symm
    let gTuple : Fin n → GroupType := fun i => ((e i : g) : GroupType)
    have hgTuple : Subgroup.closure (Set.range gTuple) = ⊤ := by
      have : Set.range gTuple = (g : Set GroupType) := by
        apply Set.eq_of_subset_of_subset
        · rintro _ ⟨i, rfl⟩; exact (e i).2
        · rintro x hx
          exact ⟨e.symm ⟨x, hx⟩, by simp [gTuple]⟩
      rw [this, hgclosure]
    have hTarget : HasDecidableWordProblem TargetGroup :=
      @OAI.FiniteAlgebraicEnvelopes.hasDecidableWordProblem_of_finitelyPresented_simple
        TargetGroup ‹_› hfp hsimple
    have hComp : ComputablePred (fun word : Word n => evalWord (φ ∘ gTuple) word = 1) :=
      WordProblem.computablePred_of_hasDecidableWordProblem hTarget (φ ∘ gTuple)
    refine ⟨n, gTuple, hgTuple, hComp.of_eq (fun word => ?_)⟩
    rw [OAI.FiniteAlgebraicEnvelopes.evalWord_comp φ gTuple word, map_eq_one_iff φ hφinj]
