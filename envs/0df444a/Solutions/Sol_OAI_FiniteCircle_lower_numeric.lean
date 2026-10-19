-- Prove2me | solution 1 for OAI.FiniteCircle.lower_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:57:06.942013+00:00
-- url     : https://prove2.me/submissions/c7720c56-3b41-4109-ab53-02ea3c33e80a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Parameters.lean:L274-L290
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.lower_numeric. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_lower_coefficient_budget

-- ---- from OAI.Combinatorics.FiniteCircle.Parameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem lower_numeric {n k M : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : Nat.log 2 M+1≤n^13) {w : ℕ} (hw : 0<w) (t : ℝ)
    (ht : (1/268435456)*(w:ℝ)/(n:ℝ)^(3*n^4) ≤ t*w*
      (4*(n^4:ℕ)/((n^4:ℕ):ℝ)^(2*n^4)+2*(Nat.log 2 M+1:ℕ)/(((n^4:ℕ):ℝ)/2)^(n^4))) :
    (n:ℝ)^k ≤ t := by
  let q : ℝ := 4*(n^4:ℕ)/((n^4:ℕ):ℝ)^(2*n^4)+2*(Nat.log 2 M+1:ℕ)/(((n^4:ℕ):ℝ)/2)^(n^4)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hq : 0<q := by dsimp [q]; positivity
  have hwq : 0<(w:ℝ)*q := mul_pos (by exact_mod_cast hw) hq
  apply (mul_le_mul_iff_left₀ hwq).mp
  calc
    _ = w*((n:ℝ)^k*q) := by ring
    _ ≤ w*((1/268435456)/(n:ℝ)^(3*n^4)) :=
      mul_le_mul_of_nonneg_left (lower_coefficient_budget hn hk hJ) (by positivity)
    _ = (1/268435456)*w/(n:ℝ)^(3*n^4) := by ring
    _ ≤ t*w*q := ht
    _ = _ := by ring

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.lower_numeric := @_root_.OAI.FiniteCircle.lower_numeric
