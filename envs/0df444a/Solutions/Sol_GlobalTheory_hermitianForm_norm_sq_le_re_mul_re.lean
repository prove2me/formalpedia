-- Prove2me | solution 1 for GlobalTheory.hermitianForm_norm_sq_le_re_mul_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:12.369392+00:00
-- url     : https://prove2.me/submissions/4a77ccdc-9973-487f-88ad-a3659b2b4ae8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulRe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  intro V _ _ Bf hsymm hpos v w
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf y x
      conj_inner_symm := fun x y => by
        show starRingEnd ℂ (Bf x y) = Bf y x
        rw [hsymm x y]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (Bf x x)
        by_cases hx : x = 0
        · subst hx; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show Bf z (x + y) = Bf z x + Bf z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show Bf y (r • x) = starRingEnd ℂ r * Bf y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul] }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c v w
  change ‖Bf w v‖ * ‖Bf v w‖ ≤ RCLike.re (Bf v v) * RCLike.re (Bf w w) at h
  rw [hsymm v w, RCLike.norm_conj] at h
  rw [sq]
  exact h
end GlobalTheory
