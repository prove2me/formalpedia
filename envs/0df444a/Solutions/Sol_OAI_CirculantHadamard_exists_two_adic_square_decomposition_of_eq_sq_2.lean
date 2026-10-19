-- Prove2me | solution 2 for OAI.CirculantHadamard.exists_two_adic_square_decomposition_of_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:16:30.617438+00:00
-- url     : https://prove2.me/submissions/30aab6de-df50-48b1-8146-bb713823e8f0

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/TwoAdicDecomposition.lean:L16-L32
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.exists_two_adic_square_decomposition_of_eq_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm

-- ---- from OAI.LinearAlgebra.CirculantHadamard.TwoAdicDecomposition ----
namespace OAI

/-!
# The two-adic form of a positive even square

Extract the power of two from an actual positive square root. Evenness of the
square forces a positive exponent in that root, so squaring gives the precise
form used at the start of the circulant Hadamard order reduction.
-/

namespace CirculantHadamard

/-- Extract the two-adic part from a specified positive square root. -/
theorem exists_two_adic_square_decomposition_of_eq_sq {n m : ℕ}
    (hm : 0 < m) (hnm : n = m ^ 2) (heven : Even n) :
    ∃ s u : ℕ, 1 ≤ s ∧ 0 < u ∧ Odd u ∧ n = 2 ^ (2 * s) * u ^ 2 := by
  obtain ⟨s, u, hu, hroot⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  have hmEven : Even m := (Nat.even_pow.mp (hnm ▸ heven)).1
  have hs : s ≠ 0 := by
    intro hs0
    have hmu : m = u := by simpa only [hs0, pow_zero, one_mul] using hroot
    exact (Nat.not_even_iff_odd.mpr hu) (hmu ▸ hmEven)
  have huPos : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro hu0
    have hm0 : m = 0 := by simpa only [hu0, mul_zero] using hroot
    exact hm.ne' hm0
  refine ⟨s, u, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs), huPos, hu, ?_⟩
  rw [hnm, hroot, mul_pow, ← pow_mul, Nat.mul_comm s 2]

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard


theorem solution : type_of% @_root_.OAI.CirculantHadamard.exists_two_adic_square_decomposition_of_eq_sq := @_root_.OAI.CirculantHadamard.exists_two_adic_square_decomposition_of_eq_sq
