-- Prove2me | solution 1 for OAI.FiniteCircle.StandingPrimes.excluded_alphabet_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:52:33.038928+00:00
-- url     : https://prove2.me/submissions/5dacb77d-0f2f-40a4-874e-3cd115992abf

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Parameters.lean:L120-L133
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.StandingPrimes.excluded_alphabet_bound. The node keeps its source
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

 theorem StandingPrimes.period_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    period h p l ≤ h^(4*h) := by
  calc
    _ ≤ ∏ _k : Fin h, h^4 := Finset.prod_le_prod' (fun k _ => hp.small_prime hh l hl hlh k)
    _ = _ := by simp [← pow_mul]

 theorem StandingPrimes.circle_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) : circleSize h p ≤ h^(5*h^2) := by
  calc
    _ ≤ h*(∏ _l : Fin h, h^(4*h)) := Nat.mul_le_mul hh
      (Finset.prod_le_prod' (fun l _ => hp.period_bound hh (l.val+1) (by omega) (by omega)))
    _ = h^(4*h^2+1) := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

 theorem StandingPrimes.excluded_alphabet_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2≤h) :
    Fintype.card (ExcludedAlphabet h (circleSize h p) h) ≤ h^(6*h^2) := by
  have hc : ∀ l, Fintype.card (ExcludedAlphabet h (circleSize h p) l) = h^l*(circleSize h p*2) := by
    intro l
    induction l with
    | zero => change Fintype.card (Fin (circleSize h p) × Bool) = 1*(circleSize h p*2); simp
    | succ l ih => change Fintype.card (Fin h × ExcludedAlphabet h (circleSize h p) l) = _
                   rw [Fintype.card_prod,Fintype.card_fin,ih]; ring
  rw [hc]
  calc
    _ ≤ h^h*(h^(5*h^2)*h) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (hp.circle_bound hh) hh)
    _ = h^(5*h^2+h+1) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.StandingPrimes.excluded_alphabet_bound := @_root_.OAI.FiniteCircle.StandingPrimes.excluded_alphabet_bound
