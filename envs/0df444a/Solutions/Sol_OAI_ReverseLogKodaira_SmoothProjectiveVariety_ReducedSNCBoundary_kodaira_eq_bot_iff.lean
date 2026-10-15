-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.kodaira_eq_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:17:53.648987+00:00
-- url     : https://prove2.me/submissions/d1507767-2b73-4f9e-80fc-384e9390ee9d

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/Basic.lean:L344-L361
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.kodaira_eq_bot_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic

-- ---- from OAI.AlgebraicGeometry.LogKodaira.Basic ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira

attribute [local instance] MvPolynomial.gradedAlgebra

 
attribute [instance] SmoothProjectiveVariety.integral SmoothProjectiveVariety.smooth

namespace SmoothProjectiveVariety

 
 
 
 

 

 
 
 
 
 

 

 
 

namespace ReducedSNCBoundary

 
 
 
 

 

 

 

 
lemma hasImageDimensionAtLeast_zero_iff {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) :
    E.HasImageDimensionAtLeast 0 ↔ ∃ (m : ℕ), 0 < m ∧
      ∃ s : X.RationalPluriform m, s ∈ E.sections m ∧ s ≠ 0 := by
  constructor
  · rintro ⟨m, hm, s, hs, hn, r, hr, h⟩
    exact ⟨m, hm, s, hs, hn⟩
  · rintro ⟨m, hm, s, hs, hn⟩
    exact ⟨m, hm, s, hs, hn, Fin.elim0, algebraicIndependent_empty_type, fun i => i.elim0⟩

 
theorem kodaira_eq_bot_iff {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) :
    E.kodaira = ⊥ ↔ ∀ (m : ℕ), 0 < m →
      ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0 := by
  constructor
  · intro h m hm s hs
    by_contra hn
    have hzero := E.hasImageDimensionAtLeast_zero_iff.mpr ⟨m, hm, s, hs, hn⟩
    have hle : ((0 : ℕ∞) : WithBot ℕ∞) ≤ E.kodaira :=
      le_iSup_of_le 0 (le_iSup_of_le hzero le_rfl)
    rw [h] at hle
    exact WithBot.coe_ne_bot (le_bot_iff.mp hle)
  · intro h
    apply le_bot_iff.mp
    apply iSup_le
    intro k
    apply iSup_le
    rintro ⟨m, hm, s, hs, hn, r, hr, hmem⟩
    exact (hn (h m hm s hs)).elim

end ReducedSNCBoundary

 
 
 
 
 

 

 

 

end SmoothProjectiveVariety

open SmoothProjectiveVariety

 

 

 
 

end ReverseLogKodaira

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

 
 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

end
end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) :
    E.kodaira = ⊥ ↔ ∀ (m : ℕ), 0 < m →
      ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0 := by
  first
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.kodaira_eq_bot_iff E
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.kodaira_eq_bot_iff
    | (apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.kodaira_eq_bot_iff <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.kodaira_eq_bot_iff <;> assumption)
