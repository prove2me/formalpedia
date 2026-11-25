-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.isTensorLat_curry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:25:40.258797+00:00
-- url     : https://prove2.me/submissions/1bca7be8-d3e0-4c21-90dc-b65274fcf1bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
namespace GlobalTheory.Cmp.WachMonoidal
theorem _root_.solution {T T' T'' : LocLat G Qp LL O} (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T)
    (hm : UnitDualParts.IsTensorLat m) :
    TensorProduct.lift (TensorProduct.curry m.toLinearMap) = m.toLinearMap ∧
      TensorLatticeUnitPart.IsTensorLat (TensorProduct.curry m.toLinearMap) := by
  have h : TensorProduct.lift (TensorProduct.curry m.toLinearMap) = m.toLinearMap := by
    ext x y; simp
  refine ⟨h, ?_, fun g x y => hm g x y⟩
  rw [h]
  exact m.bijective
end GlobalTheory.Cmp.WachMonoidal
