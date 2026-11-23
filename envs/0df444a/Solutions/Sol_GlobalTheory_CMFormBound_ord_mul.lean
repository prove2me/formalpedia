-- Prove2me | solution 1 for GlobalTheory.CMFormBound.ord_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:35.538805+00:00
-- url     : https://prove2.me/submissions/becf8a44-5bd0-4321-9e75-dc6414a22d9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
namespace GlobalTheory.CMFormBound
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ord_vw O (x * y) = ord_vw O x + ord_vw O y := by
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation K x ≠ 0 := by simpa using hx
  have hy' : (IsDiscreteValuationRing.maximalIdeal O).valuation K y ≠ 0 := by simpa using hy
  unfold ord_vw
  rw [map_mul, WithZero.log_mul hx' hy']
  ring
end GlobalTheory.CMFormBound
