-- Prove2me | solution 1 for LinearMap.smallSetExpandingAtRelativeRadius_mono_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:56.544201+00:00
-- url     : https://prove2.me/submissions/d52ee973-033f-4f7e-b8f9-711e86d21e34

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion

set_option autoImplicit false
open LinearMap
open QEC.Coding
universe u v w
namespace LinearMap
theorem _root_.solution
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    {f : Word F ι →ₗ[F] Word F κ}
    {smallNumerator largeNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hNumerator : smallNumerator ≤ largeNumerator)
    (hExpansion : f.SmallSetExpandingAtRelativeRadius
      largeNumerator radiusDenominator
      expansionNumerator expansionDenominator) :
    f.SmallSetExpandingAtRelativeRadius
      smallNumerator radiusDenominator
      expansionNumerator expansionDenominator := by
  refine ⟨hExpansion.1, hExpansion.2.1, ?_⟩
  intro x hx
  apply hExpansion.2.2 x
  exact hx.trans (Nat.mul_le_mul_right (Fintype.card ι) hNumerator)
end LinearMap
