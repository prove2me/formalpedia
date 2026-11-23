-- Prove2me | solution 1 for GlobalTheory.HermSign.realMap_realAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:02.11752+00:00
-- url     : https://prove2.me/submissions/c22a60a7-02a3-454a-93f5-ce7b7815f01a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_HermSign_realMap_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {r : ℕ}
  (Φ : CMType E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
namespace GlobalTheory.HermSign
theorem _root_.solution (a : 𝓞 E) (x : ℝ ⊗[ℤ] D.La) :
    realMap D Φ φ (realAct D a x) = (fun τ : Φ => τ.1 (a : E)) • realMap D Φ φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul t x =>
    funext τ i
    simp only [realAct, LinearMap.baseChange_tmul, DistribSMul.toLinearMap_apply, realMap_tmul,
      map_smul, Pi.smul_apply', Pi.smul_apply, smul_eq_mul, Algebra.smul_def (A := E), map_mul]
    ring
end GlobalTheory.HermSign
