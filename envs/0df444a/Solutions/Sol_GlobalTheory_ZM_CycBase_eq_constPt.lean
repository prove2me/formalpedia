-- Prove2me | solution 1 for GlobalTheory.ZM.CycBase.eq_constPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:53.207845+00:00
-- url     : https://prove2.me/submissions/2e4b9206-d128-4458-ae06-37bae3de977d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCyclotomicBaseRingInvertingPrime
import Theorems.Thm_GlobalTheory_ZM_CycBase_snd_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.CycBase
namespace GlobalTheory.ZM.CycBase
theorem _root_.solution {p k : ℕ} (hk : k ≠ 0) (hkp : k.Coprime p) (hp : p.Prime) {K : Type} [Field K]
    (y : Sp (DualNumber K) ⟶ Sp (ZP p k)) : y = constPt y := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective y
  simp only [constPt, spMap, ← Spec.map_comp]
  congr 1
  ext x
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [snd_eq_zero hk hkp hp f.hom x, TrivSqZeroExt.algebraMap_eq_inl]
end GlobalTheory.ZM.CycBase
