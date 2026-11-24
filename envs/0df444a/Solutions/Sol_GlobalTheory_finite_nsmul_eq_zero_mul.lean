-- Prove2me | solution 1 for GlobalTheory.finite_nsmul_eq_zero_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:05.443052+00:00
-- url     : https://prove2.me/submissions/9f89aadd-f0cf-4995-a048-c7f6b50c9b68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory
theorem _root_.solution {G : Type*} [AddCommGroup G] {m n : ℕ}
    (hm : {x : G | m • x = 0}.Finite) (hn : {x : G | n • x = 0}.Finite) :
    {x : G | (m * n) • x = 0}.Finite := by
  refine Set.Finite.of_finite_fibers (fun x => m • x) (hn.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    simpa [mul_nsmul] using hx
  · rintro _ ⟨x, -, rfl⟩
    refine (hm.image (· + x)).subset fun y hy => ⟨y - x, ?_, sub_add_cancel _ _⟩
    have : m • y = m • x := hy.2
    simp [smul_sub, this]
end GlobalTheory
