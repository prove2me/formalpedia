-- Prove2me | solution 1 for GlobalTheory.SW.Dict.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:53.57106+00:00
-- url     : https://prove2.me/submissions/992a4016-ba82-436b-9e71-94850bb1861a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution {K ι : Type} [Field K] [NumberField K]
    [Finite ι] (x : ι → K) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, IsIntegral ℤ (D • x i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image x)
  have hy' : ∀ i, IsIntegral ℤ (y • x i) := fun i => by
    simpa [Algebra.smul_def] using h (x i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun i => ?_⟩
  rcases Int.natAbs_eq y with hyn | hyn
  · have := hy' i
    rw [hyn] at this
    simpa [natCast_zsmul] using this
  · have := (hy' i).neg
    rw [hyn, neg_smul, neg_neg] at this
    simpa [natCast_zsmul] using this
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
