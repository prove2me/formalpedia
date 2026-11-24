-- Prove2me | solution 1 for GlobalTheory.BK.smodEq_l_pow_S_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:23:13.902802+00:00
-- url     : https://prove2.me/submissions/72f23e35-18db-4ff4-8313-ad8417f001f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Theorems.Thm_GlobalTheory_BK_mem_span_l_pow_S_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BK PowerSeries Filter Topology
open GlobalTheory GlobalTheory.BK
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
namespace GlobalTheory.BK
theorem _root_.solution (n : ℕ) (f g : S O K e) :
    f ≡ g [SMOD (Ideal.span {(l : S O K e)} ^ n • ⊤ : Submodule (S O K e) (S O K e))] ↔
      ∀ m, ‖coeff m (f : K⟦X⟧) - coeff m (g : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_l_pow_S_iff]
  simp
end GlobalTheory.BK
