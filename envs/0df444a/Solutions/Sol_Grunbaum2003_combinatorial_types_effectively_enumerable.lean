-- Prove2me | solution 1 for Grunbaum2003.combinatorial_types_effectively_enumerable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:28:41.06121+00:00
-- url     : https://prove2.me/submissions/40f49725-cab6-485e-b490-b96df13d7399

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Theorems.Thm_Grunbaum2003_exists_scheme_realizing_dpolytope
import Theorems.Thm_Grunbaum2003_exists_computable_realizable_scheme_representatives
import Mathlib.Computability.Partrec

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), Theorem 5.5.2 (p. 91): the combinatorial types of `d`-polytopes
with `k` vertices are effectively enumerable via realizable vertex-face schemes. -/
theorem combinatorial_types_effectively_enumerable_sol :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ∧
        (∀ P : Set (Fin d → ℝ), IsDPolytope P → faceCount P 0 = k →
          ∃ S ∈ E d k, SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length,
          ∀ P Q : Set (Fin d → ℝ),
            SchemeRealizes k ((E d k).get i) P →
            SchemeRealizes k ((E d k).get j) Q →
            Nonempty (PolytopeFace P ≃o PolytopeFace Q) → i = j) := by
  obtain ⟨E, hComp, hProps⟩ := exists_computable_realizable_scheme_representatives
  refine ⟨E, hComp, ?_⟩
  intro d k
  obtain ⟨hSound, hComplete, hUnique⟩ := hProps d k
  refine ⟨hSound, ?_, hUnique⟩
  intro P hP hk
  obtain ⟨S₀, hS₀⟩ := exists_scheme_realizing_dpolytope d k P hP hk
  obtain ⟨S, hSMem, hSImp⟩ := hComplete S₀ ⟨P, hS₀⟩
  exact ⟨S, hSMem, hSImp P hS₀⟩

end Grunbaum2003

theorem solution :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S P) ∧
        (∀ P : Set (Fin d → ℝ), Grunbaum2003.IsDPolytope P → Grunbaum2003.faceCount P 0 = k →
          ∃ S ∈ E d k, Grunbaum2003.SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length,
          ∀ P Q : Set (Fin d → ℝ),
            Grunbaum2003.SchemeRealizes k ((E d k).get i) P →
            Grunbaum2003.SchemeRealizes k ((E d k).get j) Q →
            Nonempty (Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q) → i = j) :=
  Grunbaum2003.combinatorial_types_effectively_enumerable_sol
