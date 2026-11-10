-- Prove2me | solution 1 for Grunbaum2003.exists_stellar_subdivision_simplicial_polytope
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:24:06.468586+00:00
-- url     : https://prove2.me/submissions/0f465134-45a8-4d2c-8c25-5029a8264f0d

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_polytope_kFaces_finite_and_stellar_subdivision_card
import Theorems.Thm_Grunbaum2003_exists_stellar_subdivision_face_finset_bijection
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped Classical

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P) :
    ∃ P' : Set (Fin d → ℝ), IsSimplicialDPolytope P' ∧
      (∀ j : Fin d, j.val + 1 < d → faceCount P' j.val = faceCount P j.val + Nat.choose d j.val) ∧
      faceCount P' (d - 1) = faceCount P (d - 1) + (d - 1) := by
  have hd1 : 1 ≤ d := by omega
  have hCardLem := Grunbaum2003.polytope_kFaces_finite_and_stellar_subdivision_card d hd1
  choose ℱ hℱ using hCardLem.1 hP.1
  obtain ⟨P', F₀, ℱ', ℱ_new, hP', hF₀, hℱ', hLow, hTop⟩ :=
    Grunbaum2003.exists_stellar_subdivision_face_finset_bijection d hd P hP ℱ hℱ
  have hCounts := hCardLem.2 ℱ ℱ' ℱ_new (fun k => (hℱ k).2) (fun k => (hℱ' k).2) hLow F₀ hF₀ hTop
  exact ⟨P', hP', hCounts.1, hCounts.2⟩
