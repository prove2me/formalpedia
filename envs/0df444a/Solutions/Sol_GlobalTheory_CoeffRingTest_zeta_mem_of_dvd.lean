-- Prove2me | solution 1 for GlobalTheory.CoeffRingTest.zeta_mem_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:52.588745+00:00
-- url     : https://prove2.me/submissions/7bd832e0-f09a-4043-9e43-31fa457d1bc4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_FullIffBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffRingTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace GlobalTheory.CoeffRingTest
theorem _root_.solution {F : IntermediateField ℚ ℂ} {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) (h : zeta n ∈ F) :
    zeta m ∈ F := by
  obtain ⟨k, rfl⟩ := hmn
  have hm : m ≠ 0 := left_ne_zero_of_mul hn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  have : zeta m = zeta (m * k) ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
    have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    push_cast
    field_simp
  rw [this]
  exact pow_mem h k
end GlobalTheory.CoeffRingTest
