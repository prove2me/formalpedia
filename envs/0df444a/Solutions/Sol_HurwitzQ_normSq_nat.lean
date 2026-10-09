-- Prove2me | solution 1 for HurwitzQ.normSq_nat
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-18T18:10:11.025897+00:00
-- url     : https://prove2.me/submissions/debcecff-f62c-49a5-8035-80dd21c5ab44

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Natural-valued squared norm

For a rational quaternion $q=a+bi+cj+dk$, put
$N(q)=a^2+b^2+c^2+d^2$. Every Hurwitz integer has $N(q)\in\mathbb{N}$,
and $q\ne0$ implies $N(q)\ge1$.

For integral coordinates this is a sum of integer squares. For half-integral
coordinates, writing each coordinate as an odd integer divided by two and using
odd squares modulo eight shows that the squared norm is an integer.
Multiplicativity is already provided by Mathlib's `Quaternion.normSq.map_mul`.

Reference: John H. Conway and Derek A. Smith, *On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry*, A K Peters, 2003, §5.1, "The Hurwitz Integral Quaternions".
-/

open Quaternion

open HurwitzQ

/-- Every odd square is congruent to one modulo eight. Writing `a = 2t` gives
`(2a+1)² = 8(2t²+t)+1`; writing `a = 2t+1` gives `8(2t²+3t+1)+1`. -/
private theorem odd_sq_eq_eight_mul_add_one (a : ℤ) : ∃ k : ℤ, (2 * a + 1) ^ 2 = 8 * k + 1 := by
  rcases Int.even_or_odd a with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨2 * t ^ 2 + t, by ring⟩
  · exact ⟨2 * t ^ 2 + 3 * t + 1, by ring⟩


theorem solution (q : ℍ[ℚ]) (hq : q ∈ hurwitzIntegersQ) : ∃ n : ℕ, normSq q = n := by
  rcases hq with ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩ | ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩
  · have hn : normSq q = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℤ) : ℚ) := by
      rw [normSq_def']
      simp only [hqa, hqi, hqj, hqk]
      push_cast
      ring
    refine ⟨Int.toNat (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2), hn.trans ?_⟩
    have hs : 0 ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℤ) := by positivity
    exact congrArg (fun x : ℤ => (x : ℚ)) (Int.toNat_of_nonneg hs) |>.symm
  · obtain ⟨k₁, hk₁⟩ := odd_sq_eq_eight_mul_add_one a
    obtain ⟨k₂, hk₂⟩ := odd_sq_eq_eight_mul_add_one b
    obtain ⟨k₃, hk₃⟩ := odd_sq_eq_eight_mul_add_one c
    obtain ⟨k₄, hk₄⟩ := odd_sq_eq_eight_mul_add_one d
    -- each half-integral coordinate squares to `2k + 1/4` with `8k + 1` the odd square;
    -- the four quarter terms add up to `1`.
    have ea : ((a : ℚ) + 1 / 2) ^ 2 = 2 * (k₁ : ℚ) + 1 / 4 := by
      have h : ((2 : ℚ) * ↑a + 1) ^ 2 = (8 : ℚ) * ↑k₁ + 1 := by exact_mod_cast hk₁
      have ha : ((a : ℚ) + 1 / 2) = ((2 : ℚ) * ↑a + 1) / 2 := by ring
      rw [ha, div_pow, h]
      ring
    have eb : ((b : ℚ) + 1 / 2) ^ 2 = 2 * (k₂ : ℚ) + 1 / 4 := by
      have h : ((2 : ℚ) * ↑b + 1) ^ 2 = (8 : ℚ) * ↑k₂ + 1 := by exact_mod_cast hk₂
      have hb : ((b : ℚ) + 1 / 2) = ((2 : ℚ) * ↑b + 1) / 2 := by ring
      rw [hb, div_pow, h]
      ring
    have ec : ((c : ℚ) + 1 / 2) ^ 2 = 2 * (k₃ : ℚ) + 1 / 4 := by
      have h : ((2 : ℚ) * ↑c + 1) ^ 2 = (8 : ℚ) * ↑k₃ + 1 := by exact_mod_cast hk₃
      have hc : ((c : ℚ) + 1 / 2) = ((2 : ℚ) * ↑c + 1) / 2 := by ring
      rw [hc, div_pow, h]
      ring
    have ed : ((d : ℚ) + 1 / 2) ^ 2 = 2 * (k₄ : ℚ) + 1 / 4 := by
      have h : ((2 : ℚ) * ↑d + 1) ^ 2 = (8 : ℚ) * ↑k₄ + 1 := by exact_mod_cast hk₄
      have hd : ((d : ℚ) + 1 / 2) = ((2 : ℚ) * ↑d + 1) / 2 := by ring
      rw [hd, div_pow, h]
      ring
    refine ⟨Int.toNat (2 * (k₁ + k₂ + k₃ + k₄) + 1), ?_⟩
    have hn : normSq q = ((2 * (k₁ + k₂ + k₃ + k₄) + 1 : ℤ) : ℚ) := by
      rw [normSq_def']
      simp only [hqa, hqi, hqj, hqk]
      rw [ea, eb, ec, ed]
      push_cast
      ring
    have hs : 0 ≤ (2 * (k₁ + k₂ + k₃ + k₄) + 1 : ℤ) := by
      have hpos : 0 ≤ normSq q := normSq_nonneg
      rw [hn] at hpos
      exact_mod_cast hpos
    rw [hn]
    exact congrArg (fun x : ℤ => (x : ℚ)) (Int.toNat_of_nonneg hs) |>.symm




