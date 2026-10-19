-- Prove2me | solution 1 for OAI.FiniteCircle.recursive_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:49:27.894091+00:00
-- url     : https://prove2.me/submissions/760d7591-6584-4bf8-9e85-52de7ca1e226

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Parameters.lean:L60-L76
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.recursive_length_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion

-- ---- from OAI.Combinatorics.FiniteCircle.Parameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem recursive_length_bound (h M : ℕ) (P T L : ℕ → ℕ) (hh : 3≤h)
    (h0 : L 0=M) (hs : ∀ l, L (l+1)=(h^(2*h)*P (l+1))*(T (l+1)*L l))
    (hP : ∀ l, 1≤l → l≤h → P l≤h^(4*h))
    (hT : ∀ l, 1≤l → l≤h → T l≤h^5) :
    ∀ l, l≤h → L l ≤ M*h^(8*h*l) := by
  intro l
  induction l with
  | zero => intro _; simp [h0]
  | succ l ih =>
    intro hl
    rw [hs]
    calc
      _ ≤ (h^(2*h)*h^(4*h))*(h^5*(M*h^(8*h*l))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (hP _ (by omega) hl))
          (Nat.mul_le_mul (hT _ (by omega) hl) (ih (by omega)))
      _ = M*h^(2*h+4*h+5+8*h*l) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by nlinarith))

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.recursive_length_bound := @_root_.OAI.FiniteCircle.recursive_length_bound
