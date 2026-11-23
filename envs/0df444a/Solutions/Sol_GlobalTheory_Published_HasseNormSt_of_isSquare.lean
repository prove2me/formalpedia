-- Prove2me | solution 1 for GlobalTheory.Published.HasseNormSt.of_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:37.988102+00:00
-- url     : https://prove2.me/submissions/50508361-c6d8-49e3-9edd-0094ffa1ac5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.HasseNormSt
open scoped TensorProduct
namespace GlobalTheory.Published.HasseNormSt
theorem _root_.solution {F : Type*} [Field F] [CharZero F] {δ : F} (h0 : δ ≠ 0) (hδ : _root_.IsSquare δ) (x : F) :
    ∃ a b : F, x = a ^ 2 - δ * b ^ 2 := by
  obtain ⟨r, rfl⟩ := hδ
  have hr : r ≠ 0 := fun hr => h0 (by rw [hr, mul_zero])
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  refine ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring
end GlobalTheory.Published.HasseNormSt
