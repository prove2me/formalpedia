-- Prove2me | solution 1 for OAI.FiniteCircle.excluded_long_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:24:15.364698+00:00
-- url     : https://prove2.me/submissions/6f624383-609f-42c1-b54d-f965ddf6e250

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/DeficitLower.lean:L79-L119
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.excluded_long_deficit. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_excluded_denominator_descent
import Theorems.Thm_OAI_FiniteCircle_excluded_descent_numeric
import Theorems.Thm_OAI_FiniteCircle_excluded_separation

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

 theorem level_injective (l : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h) :
    Function.Injective (fun k : Fin h => p l k) := by
  intro i j he
  have hi := hp.inj (a₁ := (⟨l-1,by omega⟩,i)) (a₂ := (⟨l-1,by omega⟩,j))
    (by simpa only [show l-1+1=l by omega] using he)
  exact congrArg Prod.snd hi

 theorem level_distinct (l r : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h)
    (hr : 1 ≤ r) (hrh : r ≤ h) (hlr : l ≠ r) (i j : Fin h) : p l i ≠ p r j := by
  intro he
  have hi := hp.inj (a₁ := (⟨l-1,by omega⟩,i)) (a₂ := (⟨r-1,by omega⟩,j))
    (by simpa only [show l-1+1=l by omega, show r-1+1=r by omega] using he)
  have hh := congrArg (fun z : Fin h × Fin h => z.1.val) hi
  apply hlr
  dsimp only at hh
  omega

 theorem period_pos (l : ℕ) : 0 < period h p l :=
  Finset.prod_pos (fun k _ => hp.positive l k)

 theorem circle_pos : 0 < circleSize h p := by
  apply Nat.mul_pos (by norm_num)
  exact Finset.prod_pos (fun l _ => hp.period_pos (l.val+1))

 omit hp in
 theorem circle_even : circleSize h p = 2*(circleSize h p/2) := by
  unfold circleSize
  omega

 theorem divides_circle (l : ℕ) (k : Fin h) : p l k ∣ circleSize h p := by
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · have hk : p l k ∣ period h p l := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    have hd : period h p l ∣ ∏ r : Fin h, period h p (r.val+1) := by
      have hh := Finset.dvd_prod_of_mem (fun r : Fin h => period h p (r.val+1))
        (Finset.mem_univ (⟨l-1,by omega⟩ : Fin h))
      simpa only [show l-1+1=l by omega] using hh
    exact hk.trans (hd.trans (dvd_mul_left _ _))
  · rw [hp.outside l k (by omega)]
    exact one_dvd _

 theorem excludedPrimes (hh : 2 ≤ h) : ExcludedPrimes h p := by
  refine ⟨fun l k => (hp.inside l k).1, hp.inj, fun l k => ⟨(hp.inside l k).2.1, ?_⟩⟩
  apply (hp.inside l k).2.2.trans
  have hh2 : 2 ≤ h^2 := by nlinarith
  calc
    2*h^3 ≤ h^2*h^3 := Nat.mul_le_mul_right _ hh2
    _ = h^5 := by ring

end StandingPrimes

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.DeficitLower ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem halfturn_ne_zero {M : ℕ} [NeZero M] (he : M=2*(M/2)) :
    ((M/2:ℕ) : ZMod M) ≠ 0 := by
  intro hz
  have hd := (CharP.cast_eq_zero_iff (ZMod M) M (M/2)).mp hz
  have hm := NeZero.pos M
  have hh : 0 < M/2 := by omega
  have hw := Nat.le_of_dvd hh hd
  omega

 theorem halfturn_supported {M : ℕ} (he : M=2*(M/2)) :
    PhaseSupported {2} ((M/2:ℕ) : ZMod M) := by
  simp only [PhaseSupported, Finset.prod_singleton, nsmul_eq_mul]
  rw [← Nat.cast_mul, ← he]
  simp

 theorem StandingPrimes.half_fresh {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : l ≤ h) : LowerFresh h p l {2} := by
  intro j hj hjl k hk
  have ht := (hp.atLevel j hj (hjl.trans hl) k).2.1
  have hh3 := Nat.pow_le_pow_left hh 3
  simp only [Finset.mem_singleton] at hk
  omega

 theorem excluded_long_deficit {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2))
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {R : ℕ} (hR : 0<R)
    (v : ExcludedState (n^4) (circleSize (n^4) p) (n^4)) :
    (excludedLength (n^4) p R (circleSize (n^4) p) (n^4):ℝ)/(n:ℝ)^(3*n^4) ≤
      (deficit (excludedWord (n^4) p R (circleSize (n^4) p) (n^4) v)
        (excludedWord (n^4) p R (circleSize (n^4) p) (n^4)
          (shiftExcludedState (n^4) (circleSize (n^4) p) (n^4) v ((circleSize (n^4) p/2 : ℕ) : ZMod (circleSize (n^4) p)))) : ℝ) := by
  let h := n^4
  let M := circleSize h p
  let : NeZero M := ⟨hp.circle_pos.ne'⟩
  have hh : 1000000 ≤ h := hn.trans (le_self_pow₀ (by omega) (by norm_num))
  have ht : 2 ≤ n^3 := by nlinarith [Nat.pow_le_pow_left (show 2≤n by omega) 3]
  have htt : h ≤ n^3*n := by dsimp [h]; ring_nf; rfl
  have hsmall : 2*n^3 ≤ h := by
    have ht := Nat.mul_le_mul_right (n^3) (show 2≤n by omega)
    dsimp [h]; nlinarith [show n*n^3=n^4 by ring]
  have hbound := excluded_denominator_descent ht (by omega : 1≤n) (le_refl (n^4)) htt hsmall
    (by omega : 3≤h/100) hp.divides_circle hp.positive
    (fun j hj hjh k => (hp.atLevel j hj hjh k).1)
    (fun j hj hjh k => by
      have ht := ((hp.excludedPrimes (by omega)).2.2 ⟨j-1,by omega⟩ k).2
      simpa only [show j-1+1=j by omega] using ht) hp.level_injective hp.level_distinct
    h (le_refl _) {2} ((M/2:ℕ) : ZMod M) (by simp; omega)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; subst q
        exact ⟨Nat.prime_two, (show 2≤h by omega).trans (le_self_pow₀ (by omega) (by norm_num))⟩)
    (hp.half_fresh (by omega) h (le_refl _))
    (halfturn_ne_zero (StandingPrimes.circle_even (h:=h) (p:=p)))
    (halfturn_supported (StandingPrimes.circle_even (h:=h) (p:=p)))
  simp only [Finset.card_singleton] at hbound
  have hsep := excluded_separation (StandingPrimes.circle_even (h:=h) (p:=p)) (by omega : 0<h)
    hR hp.divides_circle hp.positive (fun _ => by simp; omega) h v ((M/2:ℕ) : ZMod M)
  have hnum := excluded_descent_numeric hn he
  have hL : (0:ℝ) ≤ excludedLength h p R M h := by positivity
  have hc : (0:ℝ) ≤ 1/((2:ℝ)^h*4) := by positivity
  calc
    _ = (excludedLength h p R M h:ℝ)*(1/(n:ℝ)^(3*h)) := by dsimp [h,M]; ring
    _ ≤ (excludedLength h p R M h:ℝ)*((1/((2:ℝ)^h*4))*pairDescentBound h (h/100) (n^3) n 1 h) :=
      mul_le_mul_of_nonneg_left hnum hL
    _ ≤ (1/((2:ℝ)^h*4))*(excludedLength h p R M h)*excludedCost h p M hp.divides_circle hp.positive h ((M/2:ℕ) : ZMod M) := by
      nlinarith [mul_le_mul_of_nonneg_left hbound (mul_nonneg hL hc)]
    _ ≤ _ := hsep

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.excluded_long_deficit := @_root_.OAI.FiniteCircle.excluded_long_deficit
