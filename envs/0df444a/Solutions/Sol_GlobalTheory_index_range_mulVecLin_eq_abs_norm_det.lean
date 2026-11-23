-- Prove2me | solution 1 for GlobalTheory.index_range_mulVecLin_eq_abs_norm_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:01.98181+00:00
-- url     : https://prove2.me/submissions/6177b1cf-77fb-4da9-a8a4-2823a498abef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IndexRangeMulVecLinEqAbsNormDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (𝓞 E)), A.det ≠ 0 →
      (((LinearMap.range A.mulVecLin).toAddSubgroup.index : ℕ) : ℚ) =
        |Algebra.norm ℚ ((A.det : 𝓞 E) : E)|) := by
  intro ι _ _ A hA
  classical
  set f := A.mulVecLin with hf
  have hinj : Function.Injective f := by
    intro u v huv
    have h : A.mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hA h)
  let b := Module.Free.chooseBasis ℤ (ι → 𝓞 E)
  let fZ : (ι → 𝓞 E) →ₗ[ℤ] (ι → 𝓞 E) := f.restrictScalars ℤ
  have hinjZ : Function.Injective fZ := hinj
  let e := LinearEquiv.ofInjective fZ hinjZ
  have key := AddSubgroup.index_eq_natAbs_det b (LinearMap.range f).toAddSubgroup (b.map e)
  rw [key]
  have hdet : (b.det fun i ↦ ((b.map e i : LinearMap.range fZ) : ι → 𝓞 E)) = LinearMap.det fZ := by
    rw [Module.Basis.det_apply, ← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply, e]
  have h2 : (((b.det fun i ↦ ((b.map e i : LinearMap.range fZ) : ι → 𝓞 E)).natAbs : ℕ) : ℚ) =
      |Algebra.norm ℚ ((A.det : 𝓞 E) : E)| := by
    rw [hdet, LinearMap.det_restrictScalars, hf, ← Matrix.toLin'_apply', LinearMap.det_toLin',
      Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
  exact h2
end _root_.GlobalTheory
end GlobalTheory
