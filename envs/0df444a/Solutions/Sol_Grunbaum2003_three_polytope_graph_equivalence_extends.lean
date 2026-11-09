-- Prove2me | solution 1 for Grunbaum2003.three_polytope_graph_equivalence_extends
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T23:42:32.539178+00:00
-- url     : https://prove2.me/submissions/a8cd6417-c528-4684-9a1a-6b737f68e994

import Theorems.Thm_Grunbaum2003_three_polytope_facet_is_induced_nonseparating_cycle
import Theorems.Thm_Grunbaum2003_three_polytope_facet_of_induced_nonseparating_cycle
import Theorems.Thm_Grunbaum2003_skeleton_orderIso_extends_of_downSet_image
import Theorems.Thm_Grunbaum2003_polytopeFace_trichotomy_codim_two
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003ThreePolySketch
open Grunbaum2003

theorem isBot_map_iff {P Q : Set (Fin 3 → ℝ)} (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1)
    (B : SkeletonFace P 1) :
    (∀ Y : SkeletonFace Q 1, φ B ≤ Y) ↔ (∀ X : SkeletonFace P 1, B ≤ X) := by
  refine ⟨fun h X => (φ.le_iff_le).1 (h (φ X)), fun h Y => ?_⟩
  have h1 := (φ.le_iff_le).2 (h (φ.symm Y))
  simpa using h1

theorem isAtom_map_iff {P Q : Set (Fin 3 → ℝ)} (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1)
    (A : SkeletonFace P 1) :
    (¬ (∀ Y : SkeletonFace Q 1, φ A ≤ Y) ∧
      ∀ Y : SkeletonFace Q 1, Y < φ A → ∀ Z : SkeletonFace Q 1, Y ≤ Z) ↔
    (¬ (∀ X : SkeletonFace P 1, A ≤ X) ∧
      ∀ X : SkeletonFace P 1, X < A → ∀ Z : SkeletonFace P 1, X ≤ Z) := by
  rw [isBot_map_iff φ A]
  refine and_congr_right (fun _ => ⟨fun h X hXA => ?_, fun h Y hYA => ?_⟩)
  · have hφ : φ X < φ A := (φ.lt_iff_lt).2 hXA
    exact (isBot_map_iff φ X).1 (h (φ X) hφ)
  · have hsymm : φ.symm Y < A := (φ.symm_apply_lt).2 hYA
    have hbotP := h (φ.symm Y) hsymm
    have hbotQ := (isBot_map_iff φ (φ.symm Y)).2 hbotP
    simpa using hbotQ

theorem isEdge_map_iff {P Q : Set (Fin 3 → ℝ)} (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1)
    (E : SkeletonFace P 1) :
    (∀ Y : SkeletonFace Q 1, φ E ≤ Y → Y = φ E) ↔
    (∀ X : SkeletonFace P 1, E ≤ X → X = E) := by
  refine ⟨fun h X hEX => ?_, fun h Y hEY => ?_⟩
  · have heq := h (φ X) ((φ.le_iff_le).2 hEX)
    exact φ.injective heq
  · have hle : E ≤ φ.symm Y := (φ.le_symm_apply).2 hEY
    have heq := h (φ.symm Y) hle
    exact (φ.symm_apply_eq).1 heq

theorem facet_downSet_image_three (P Q : Set (Fin 3 → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q 1, T.val ≤ G ↔ (φ.symm T).val ≤ F := by
  obtain ⟨hInducedP, ⟨⟨A₀P, hA₀P_atom, hA₀P_mem⟩, hTwoRegP⟩, hConnP, ⟨W₀P, hW₀P_atom, hW₀P_not⟩, hNonsepP⟩ :=
    three_polytope_facet_is_induced_nonseparating_cycle P hP F hF
  let C_Q : Set (SkeletonFace Q 1) := {T : SkeletonFace Q 1 | (φ.symm T).val ≤ F}
  have hInducedQ : ∀ T : SkeletonFace Q 1,
      T ∈ C_Q ↔ (∀ B : SkeletonFace Q 1,
        (¬ (∀ Y : SkeletonFace Q 1, B ≤ Y) ∧
          ∀ Y : SkeletonFace Q 1, Y < B → ∀ Z : SkeletonFace Q 1, Y ≤ Z) →
        B ≤ T → B ∈ C_Q) := by
    intro T
    change φ.symm T ∈ {S : SkeletonFace P 1 | S.val ≤ F} ↔ _
    rw [hInducedP (φ.symm T)]
    refine ⟨fun h B hB_atom hBT => ?_, fun h A hA_atom hAT => ?_⟩
    · have hsymm_atom : ¬ (∀ X : SkeletonFace P 1, φ.symm B ≤ X) ∧
          ∀ X : SkeletonFace P 1, X < φ.symm B → ∀ Z : SkeletonFace P 1, X ≤ Z := by
        have h1 : φ (φ.symm B) = B := φ.apply_symm_apply B
        have hB' := hB_atom
        rw [← h1] at hB'
        exact (isAtom_map_iff φ (φ.symm B)).1 hB'
      exact h (φ.symm B) hsymm_atom ((φ.symm.le_iff_le).2 hBT)
    · have hφA_atom : ¬ (∀ Y : SkeletonFace Q 1, φ A ≤ Y) ∧
          ∀ Y : SkeletonFace Q 1, Y < φ A → ∀ Z : SkeletonFace Q 1, Y ≤ Z :=
        (isAtom_map_iff φ A).2 hA_atom
      have hle : φ A ≤ T := (φ.le_symm_apply).1 hAT
      have hmem := h (φ A) hφA_atom hle
      change (φ.symm (φ A)).val ≤ F at hmem
      simpa using hmem
  have hTwoRegQ :
      (∃ B : SkeletonFace Q 1,
        (¬ (∀ Y : SkeletonFace Q 1, B ≤ Y) ∧
          ∀ Y : SkeletonFace Q 1, Y < B → ∀ Z : SkeletonFace Q 1, Y ≤ Z) ∧ B ∈ C_Q) ∧
      ∀ B : SkeletonFace Q 1,
        (¬ (∀ Y : SkeletonFace Q 1, B ≤ Y) ∧
          ∀ Y : SkeletonFace Q 1, Y < B → ∀ Z : SkeletonFace Q 1, Y ≤ Z) →
        B ∈ C_Q →
        ∃ E₁ E₂ : SkeletonFace Q 1,
          (∀ Y : SkeletonFace Q 1, E₁ ≤ Y → Y = E₁) ∧
          (∀ Y : SkeletonFace Q 1, E₂ ≤ Y → Y = E₂) ∧
          E₁ ∈ C_Q ∧ E₂ ∈ C_Q ∧ E₁ ≠ E₂ ∧ B ≤ E₁ ∧ B ≤ E₂ ∧
          ∀ E : SkeletonFace Q 1,
            (∀ Y : SkeletonFace Q 1, E ≤ Y → Y = E) → E ∈ C_Q → B ≤ E → E = E₁ ∨ E = E₂ := by
    refine ⟨⟨φ A₀P, (isAtom_map_iff φ A₀P).2 hA₀P_atom, by
      change (φ.symm (φ A₀P)).val ≤ F
      simpa using hA₀P_mem⟩, ?_⟩
    intro B hB_atom hB_mem
    have hsymm_atom : ¬ (∀ X : SkeletonFace P 1, φ.symm B ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < φ.symm B → ∀ Z : SkeletonFace P 1, X ≤ Z := by
      have h1 : φ (φ.symm B) = B := φ.apply_symm_apply B
      have hB' := hB_atom
      rw [← h1] at hB'
      exact (isAtom_map_iff φ (φ.symm B)).1 hB'
    obtain ⟨E₁P, E₂P, hE₁P_edge, hE₂P_edge, hE₁P_mem, hE₂P_mem, hE₁₂_ne, hBE₁, hBE₂, hE_uniq⟩ :=
      hTwoRegP (φ.symm B) hsymm_atom hB_mem
    refine ⟨φ E₁P, φ E₂P, (isEdge_map_iff φ E₁P).2 hE₁P_edge, (isEdge_map_iff φ E₂P).2 hE₂P_edge,
      by change (φ.symm (φ E₁P)).val ≤ F; simpa using hE₁P_mem,
      by change (φ.symm (φ E₂P)).val ≤ F; simpa using hE₂P_mem,
      fun hEq => hE₁₂_ne (φ.injective hEq),
      (φ.symm_apply_le).1 hBE₁, (φ.symm_apply_le).1 hBE₂, ?_⟩
    intro E hE_edge hE_mem hBE
    have hsymm_edge : ∀ X : SkeletonFace P 1, φ.symm E ≤ X → X = φ.symm E := by
      have h1 : φ (φ.symm E) = E := φ.apply_symm_apply E
      have hE' := hE_edge
      rw [← h1] at hE'
      exact (isEdge_map_iff φ (φ.symm E)).1 hE'
    rcases hE_uniq (φ.symm E) hsymm_edge hE_mem ((φ.symm.le_iff_le).2 hBE) with h1 | h2
    · exact Or.inl ((φ.symm_apply_eq).1 h1)
    · exact Or.inr ((φ.symm_apply_eq).1 h2)
  have hConnQ :
      ∀ (Good : SkeletonFace Q 1 → Prop),
        (∃ B₀ : SkeletonFace Q 1,
          (¬ (∀ Y : SkeletonFace Q 1, B₀ ≤ Y) ∧
            ∀ Y : SkeletonFace Q 1, Y < B₀ → ∀ Z : SkeletonFace Q 1, Y ≤ Z) ∧
          B₀ ∈ C_Q ∧ Good B₀) →
        (∀ A B E : SkeletonFace Q 1,
          (¬ (∀ Y : SkeletonFace Q 1, A ≤ Y) ∧
            ∀ Y : SkeletonFace Q 1, Y < A → ∀ Z : SkeletonFace Q 1, Y ≤ Z) →
          (¬ (∀ Y : SkeletonFace Q 1, B ≤ Y) ∧
            ∀ Y : SkeletonFace Q 1, Y < B → ∀ Z : SkeletonFace Q 1, Y ≤ Z) →
          (∀ Y : SkeletonFace Q 1, E ≤ Y → Y = E) →
          A ∈ C_Q → B ∈ C_Q → E ∈ C_Q → A ≤ E → B ≤ E → Good A → Good B) →
        ∀ B : SkeletonFace Q 1,
          (¬ (∀ Y : SkeletonFace Q 1, B ≤ Y) ∧
            ∀ Y : SkeletonFace Q 1, Y < B → ∀ Z : SkeletonFace Q 1, Y ≤ Z) →
          B ∈ C_Q → Good B := by
    intro Good ⟨B₀, hB₀_atom, hB₀_mem, hB₀_good⟩ hStep B hB_atom hB_mem
    have hB₀P_atom : ¬ (∀ X : SkeletonFace P 1, φ.symm B₀ ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < φ.symm B₀ → ∀ Z : SkeletonFace P 1, X ≤ Z := by
      have h1 : φ (φ.symm B₀) = B₀ := φ.apply_symm_apply B₀
      have h' := hB₀_atom; rw [← h1] at h'
      exact (isAtom_map_iff φ (φ.symm B₀)).1 h'
    have hBP_atom : ¬ (∀ X : SkeletonFace P 1, φ.symm B ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < φ.symm B → ∀ Z : SkeletonFace P 1, X ≤ Z := by
      have h1 : φ (φ.symm B) = B := φ.apply_symm_apply B
      have h' := hB_atom; rw [← h1] at h'
      exact (isAtom_map_iff φ (φ.symm B)).1 h'
    have hRes := hConnP (fun A => Good (φ A))
      ⟨φ.symm B₀, hB₀P_atom, hB₀_mem, by simpa using hB₀_good⟩
      (fun A₁ A₂ E hA₁ hA₂ hE hA₁C hA₂C hEC hA₁E hA₂E hGoodA₁ =>
        hStep (φ A₁) (φ A₂) (φ E)
          ((isAtom_map_iff φ A₁).2 hA₁)
          ((isAtom_map_iff φ A₂).2 hA₂)
          ((isEdge_map_iff φ E).2 hE)
          (by change (φ.symm (φ A₁)).val ≤ F; simpa using hA₁C)
          (by change (φ.symm (φ A₂)).val ≤ F; simpa using hA₂C)
          (by change (φ.symm (φ E)).val ≤ F; simpa using hEC)
          ((φ.le_iff_le).2 hA₁E)
          ((φ.le_iff_le).2 hA₂E)
          hGoodA₁)
      (φ.symm B) hBP_atom hB_mem
    simpa using hRes
  have hNonsepQ :
      (∃ W : SkeletonFace Q 1,
        (¬ (∀ Y : SkeletonFace Q 1, W ≤ Y) ∧
          ∀ Y : SkeletonFace Q 1, Y < W → ∀ Z : SkeletonFace Q 1, Y ≤ Z) ∧ W ∉ C_Q) ∧
      ∀ (Good : SkeletonFace Q 1 → Prop),
        (∃ W₀ : SkeletonFace Q 1,
          (¬ (∀ Y : SkeletonFace Q 1, W₀ ≤ Y) ∧
            ∀ Y : SkeletonFace Q 1, Y < W₀ → ∀ Z : SkeletonFace Q 1, Y ≤ Z) ∧
          W₀ ∉ C_Q ∧ Good W₀) →
        (∀ U V E : SkeletonFace Q 1,
          (¬ (∀ Y : SkeletonFace Q 1, U ≤ Y) ∧
            ∀ Y : SkeletonFace Q 1, Y < U → ∀ Z : SkeletonFace Q 1, Y ≤ Z) →
          (¬ (∀ Y : SkeletonFace Q 1, V ≤ Y) ∧
            ∀ Y : SkeletonFace Q 1, Y < V → ∀ Z : SkeletonFace Q 1, Y ≤ Z) →
          (∀ Y : SkeletonFace Q 1, E ≤ Y → Y = E) →
          U ∉ C_Q → V ∉ C_Q → U ≤ E → V ≤ E → Good U → Good V) →
        ∀ W : SkeletonFace Q 1,
          (¬ (∀ Y : SkeletonFace Q 1, W ≤ Y) ∧
            ∀ Y : SkeletonFace Q 1, Y < W → ∀ Z : SkeletonFace Q 1, Y ≤ Z) →
          W ∉ C_Q → Good W := by
    refine ⟨⟨φ W₀P, (isAtom_map_iff φ W₀P).2 hW₀P_atom, by
      change ¬ (φ.symm (φ W₀P)).val ≤ F
      simpa using hW₀P_not⟩, ?_⟩
    intro Good ⟨W₀, hW₀_atom, hW₀_not, hW₀_good⟩ hStep W hW_atom hW_not
    have hW₀P_atom' : ¬ (∀ X : SkeletonFace P 1, φ.symm W₀ ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < φ.symm W₀ → ∀ Z : SkeletonFace P 1, X ≤ Z := by
      have h1 : φ (φ.symm W₀) = W₀ := φ.apply_symm_apply W₀
      have h' := hW₀_atom; rw [← h1] at h'
      exact (isAtom_map_iff φ (φ.symm W₀)).1 h'
    have hWP_atom' : ¬ (∀ X : SkeletonFace P 1, φ.symm W ≤ X) ∧
        ∀ X : SkeletonFace P 1, X < φ.symm W → ∀ Z : SkeletonFace P 1, X ≤ Z := by
      have h1 : φ (φ.symm W) = W := φ.apply_symm_apply W
      have h' := hW_atom; rw [← h1] at h'
      exact (isAtom_map_iff φ (φ.symm W)).1 h'
    have hRes := hNonsepP (fun U => Good (φ U))
      ⟨φ.symm W₀, hW₀P_atom', hW₀_not, by simpa using hW₀_good⟩
      (fun U₁ V₁ E hU₁ hV₁ hE hU₁_not hV₁_not hU₁E hV₁E hGoodU₁ =>
        hStep (φ U₁) (φ V₁) (φ E)
          ((isAtom_map_iff φ U₁).2 hU₁)
          ((isAtom_map_iff φ V₁).2 hV₁)
          ((isEdge_map_iff φ E).2 hE)
          (by change ¬ (φ.symm (φ U₁)).val ≤ F; simpa using hU₁_not)
          (by change ¬ (φ.symm (φ V₁)).val ≤ F; simpa using hV₁_not)
          ((φ.le_iff_le).2 hU₁E)
          ((φ.le_iff_le).2 hV₁E)
          hGoodU₁)
      (φ.symm W) hWP_atom' hW_not
    simpa using hRes
  exact three_polytope_facet_of_induced_nonseparating_cycle Q hQ C_Q
    hInducedQ hTwoRegQ hConnQ hNonsepQ

theorem fwd_all_three (P Q : Set (Fin 3 → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1)
    (F : PolytopeFace P) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q 1, T.val ≤ G ↔ (φ.symm T).val ≤ F := by
  rcases polytopeFace_trichotomy_codim_two 3 (by omega) P F with hS | hTop | hFacet
  · let S : SkeletonFace P 1 := ⟨F, hS⟩
    refine ⟨(φ S).val, fun T => ?_⟩
    change T ≤ φ S ↔ φ.symm T ≤ S
    exact (OrderIso.symm_apply_le φ).symm
  · refine ⟨⟨Q, IsExposed.refl Q⟩, fun T => ?_⟩
    constructor
    · intro _
      change (φ.symm T).val.val ⊆ F.val
      rw [hTop]
      exact (φ.symm T).val.property.subset
    · intro _
      change T.val.val ⊆ Q
      exact T.val.property.subset
  · exact facet_downSet_image_three P Q hP hQ φ F hFacet

end Grunbaum2003ThreePolySketch

open Grunbaum2003 Grunbaum2003ThreePolySketch in
theorem solution
    (P Q : Set (Fin 3 → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P 1, Φ F.val = (φ F).val := by
  refine skeleton_orderIso_extends_of_downSet_image 3 3 1 P Q hP hQ φ
    (fun F => fwd_all_three P Q hP hQ φ F) (fun G => ?_)
  obtain ⟨F, hF⟩ := fwd_all_three Q P hQ hP φ.symm G
  exact ⟨F, fun S => hF S⟩
