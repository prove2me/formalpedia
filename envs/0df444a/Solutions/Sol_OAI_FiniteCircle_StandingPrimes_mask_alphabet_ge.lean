-- Prove2me | solution 1 for OAI.FiniteCircle.StandingPrimes.mask_alphabet_ge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:54:01.821885+00:00
-- url     : https://prove2.me/submissions/c63d501c-72d9-4a8e-9c59-4c0b938df1c0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Parameters.lean:L135-L148
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.StandingPrimes.mask_alphabet_ge. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.Primes ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace StandingPrimes
variable {h : ℕ} {p : ℕ → ℕ → ℕ} (hp : StandingPrimes h p)
include hp

 theorem atLevel (l : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h) (k : Fin h) :
    Nat.Prime (p l k) ∧ h^3 < p l k ∧ p l k ≤ 2*h^3 := by
  have ht := hp.inside ⟨l-1,by omega⟩ k
  simpa only [show l-1+1=l by omega] using ht

 theorem positive (l : ℕ) (k : Fin h) : 0 < p l k := by
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · exact (hp.atLevel l hl.1 hl.2 k).1.pos
  · rw [hp.outside l k (by omega)]
    norm_num

end StandingPrimes

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Parameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem StandingPrimes.mask_alphabet_ge {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) (l : ℕ) : 2≤Fintype.card (MaskAlphabet h p l) := by
  have hT (l : ℕ) : 1≤Fintype.card (MaskTag h p l) := by
    have ht : h≤∑ k : Fin h, p l k := by
      calc
        _ = ∑ _k : Fin h, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun k _ => hp.positive l k)
    simpa only [MaskTag,Fintype.card_sigma,Fintype.card_fin] using hh.trans ht
  induction l with
  | zero => change 2≤Fintype.card Bool; norm_num
  | succ l ih =>
    change 2≤Fintype.card (MaskTag h p (l+1) × MaskAlphabet h p l)
    rw [Fintype.card_prod]
    nlinarith [hT (l+1)]

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.StandingPrimes.mask_alphabet_ge := @_root_.OAI.FiniteCircle.StandingPrimes.mask_alphabet_ge
