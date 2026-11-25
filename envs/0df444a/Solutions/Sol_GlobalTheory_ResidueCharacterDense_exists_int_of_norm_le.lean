-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.exists_int_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:36:34.151404+00:00
-- url     : https://prove2.me/submissions/eeea1029-9a86-44b1-8df5-261077d8cc51

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution {l : ℕ} [Fact l.Prime] (q : ℚ) (n : ℕ) (m : ℤ)
    (h : q * (l : ℚ) ^ n = m) (hq : ‖(q : ℚ_[l])‖ ≤ 1) : ∃ c : ℤ, q = c := by
  have hl : (l : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h1 : ‖(m : ℚ_[l])‖ ≤ (l : ℝ) ^ (-n : ℤ) := by
    have : (m : ℚ_[l]) = (q : ℚ_[l]) * (l : ℚ_[l]) ^ n := by exact_mod_cast h.symm
    rw [this, norm_mul, Padic.norm_p_pow]
    calc _ ≤ 1 * (l : ℝ) ^ (-n : ℤ) := by gcongr
      _ = _ := one_mul _
  obtain ⟨c, hc⟩ := (Padic.norm_int_le_pow_iff_dvd m n).mp h1
  refine ⟨c, ?_⟩
  rw [hc] at h
  push_cast at h
  have : (l : ℚ) ^ n ≠ 0 := pow_ne_zero _ hl
  apply mul_right_cancel₀ this
  rw [h]; ring
end GlobalTheory.ResidueCharacterDense
