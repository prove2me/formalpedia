-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.pb_eq_qa_minus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:30.544601+00:00
-- url     : https://prove2.me/submissions/89f488c7-2626-4f47-81e1-f85aa15834a8

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n) (hd : r + k * b ^ n ≠ 0) :
    p n k b r s * b = q n k b r s * (a n k b r s) - r * s^(n-1) := by
  simp only [p, q, a]
  have hd' : (r + k * b^n : ℚ) ≠ 0 := by exact_mod_cast hd
  field_simp
  push_cast
  -- Goal: (s^n * r + k * a^n) * b
  --     = (s^{n-1} * r + k * b * a^{n-1}) * a - r * s^{n-1} * (r + k * b^n)
  -- where a = k * b^n + s * b + r
  set a' := k * b ^ n + s * b + r with ha'_def
  -- Key: s * s^(n-1) = s^n and a^(n-1) * a = a^n
  have h1 : s * s^(n-1) = s^n := by
    cases n with | zero => omega | succ m => simp [pow_succ]; ring
  have h2 : a'^(n-1) * a' = a'^n := by
    cases n with
    | zero => omega
    | succ m => simp only [Nat.add_sub_cancel, pow_succ]
  -- Algebraic proof
  have key : (s^n * r + k * a'^n) * b =
      (s^(n-1) * r + k * b * a'^(n-1)) * a' - r * s^(n-1) * (r + k * b^n) := by
    have h3 : k * a'^n * b = k * b * a'^(n-1) * a' := by
      calc k * a'^n * b = k * (a'^(n-1) * a') * b := by rw [← h2]
        _ = k * b * a'^(n-1) * a' := by ring
    calc (s^n * r + k * a'^n) * b
        = s^n * r * b + k * a'^n * b := by ring
      _ = s * s^(n-1) * r * b + k * b * a'^(n-1) * a' := by rw [← h1, h3]
      _ = s^(n-1) * r * (s * b) + k * b * a'^(n-1) * a' := by ring
      _ = s^(n-1) * r * a' - s^(n-1) * r * (k * b^n + r) + k * b * a'^(n-1) * a' := by
          rw [ha'_def]; ring
      _ = (s^(n-1) * r + k * b * a'^(n-1)) * a' - r * s^(n-1) * (r + k * b^n) := by ring
  have key_q : (((s^n * r + k * a'^n) * b : ℤ) : ℚ)
             = ((s^(n-1) * r + k * b * a'^(n-1)) * a' - r * s^(n-1) * (r + k * b^n) : ℚ) := by
    exact_mod_cast key
  have ha'_q : (a' : ℚ) = k * b^n + s * b + r := by simp only [ha'_def]; push_cast; ring
  calc ((s^n * r + k * (k * b^n + s * b + r)^n) * b : ℚ)
      = (s^n * r + k * a'^n) * b := by rw [← ha'_q]
    _ = (s^(n-1) * r + k * b * a'^(n-1)) * a' - r * s^(n-1) * (r + k * b^n) := by exact_mod_cast key
    _ = (s^(n-1) * r + k * b * (k * b^n + s * b + r)^(n-1)) * (k * b^n + s * b + r) -
        r * s^(n-1) * (r + k * b^n) := by rw [ha'_q]
    _ = (r * s^(n-1) + k * b * (k * b^n + s * b + r)^(n-1)) * (k * b^n + s * b + r) -
        r * (r + k * b^n) * s^(n-1) := by ring
end GroupTheoreticShannonCapacity.Construction
