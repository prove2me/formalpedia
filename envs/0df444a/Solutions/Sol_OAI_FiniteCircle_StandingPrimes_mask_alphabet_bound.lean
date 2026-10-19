-- Prove2me | solution 1 for OAI.FiniteCircle.StandingPrimes.mask_alphabet_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:51:07.513107+00:00
-- url     : https://prove2.me/submissions/88c5a906-332a-4c20-aea7-cc32ba3d229e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Parameters.lean:L101-L118
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.StandingPrimes.mask_alphabet_bound. The node keeps its source
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

end StandingPrimes

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Parameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem StandingPrimes.small_prime {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) (k : Fin h) :
    p l k ≤ h^4 := by
  apply (hp.atLevel l hl hlh k).2.2.trans
  calc
    2*h^3 ≤ h*h^3 := Nat.mul_le_mul_right _ hh
    _ = h^4 := by ring

 theorem StandingPrimes.tags_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    (maskTags h p l).length ≤ h^5 := by
  rw [length_maskTags]
  calc
    _ ≤ ∑ _k : Fin h, h^4 := Finset.sum_le_sum (fun k _ => hp.small_prime hh l hl hlh k)
    _ = _ := by simp; ring

 theorem StandingPrimes.tag_card_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    Fintype.card (MaskTag h p l) ≤ h^5 := by
  simpa [Fintype.card_sigma, MaskTag, length_maskTags] using hp.tags_bound hh l hl hlh

 theorem StandingPrimes.mask_alphabet_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2≤h) :
    Fintype.card (MaskAlphabet h p h) ≤ h^(6*h^2) := by
  have hc : ∀ l, l≤h → Fintype.card (MaskAlphabet h p l) ≤ 2*h^(5*l) := by
    intro l
    induction l with
    | zero => intro _; change Fintype.card Bool ≤ 2*h^(5*0); norm_num
    | succ l ih =>
      intro hl
      calc
        _ = Fintype.card (MaskTag h p (l+1))*Fintype.card (MaskAlphabet h p l) := Fintype.card_prod _ _
        _ ≤ h^5*(2*h^(5*l)) := Nat.mul_le_mul (hp.tag_card_bound hh _ (by omega) hl) (ih (by omega))
        _ = _ := by ring
  calc
    _ ≤ 2*h^(5*h) := hc h (le_refl _)
    _ ≤ h*h^(5*h) := Nat.mul_le_mul_right _ hh
    _ = h^(5*h+1) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.StandingPrimes.mask_alphabet_bound := @_root_.OAI.FiniteCircle.StandingPrimes.mask_alphabet_bound
