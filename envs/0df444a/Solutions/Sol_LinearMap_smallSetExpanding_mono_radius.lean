-- Prove2me | solution 1 for LinearMap.smallSetExpanding_mono_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:53.07742+00:00
-- url     : https://prove2.me/submissions/b4bfe90d-fea7-40c6-8e44-d4aa7c890f46

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
    {smallRadius largeRadius expansionNumerator expansionDenominator : Nat}
    (hRadius : smallRadius ≤ largeRadius)
    (hExpansion : f.SmallSetExpanding
      largeRadius expansionNumerator expansionDenominator) :
    f.SmallSetExpanding
      smallRadius expansionNumerator expansionDenominator := by
  refine ⟨hExpansion.1, ?_⟩
  intro x hx
  exact hExpansion.2 x (hx.trans hRadius)
end LinearMap
