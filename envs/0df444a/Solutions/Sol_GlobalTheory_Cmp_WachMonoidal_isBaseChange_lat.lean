-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.isBaseChange_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:25:38.828815+00:00
-- url     : https://prove2.me/submissions/341500b4-5814-484e-bd9f-8ec2424ad3d4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_HasTriangularWeight_smul
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
theorem _root_.solution [IsFractionRing O LL] (T : LocLat G Qp LL O) :
    IsBaseChange LL T.L.T.subtype := by
  rw [← isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) LL]
  refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩
  · have := (IsLocalization.map_units LL s).map (algebraMap LL (Module.End LL T.V))
    rw [Module.End.isUnit_iff] at this ⊢
    convert this using 1
    ext x
    simp
  · have hy : y ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
    have : ∃ s : nonZeroDivisors O, (s : O) • y ∈ T.L.T := by
      induction hy using Submodule.span_induction with
      | mem x hx => exact ⟨1, by simpa using hx⟩
      | zero => exact ⟨1, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        refine ⟨s * t, ?_⟩
        rw [smul_add, Submonoid.coe_mul]
        refine T.L.T.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact T.L.T.smul_mem _ hs
        · rw [mul_smul]; exact T.L.T.smul_mem _ ht
      | smul c x _ hx =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨⟨a, t⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors O) c
        refine ⟨s * t, ?_⟩
        have : ((s * t : nonZeroDivisors O) : O) • c • x = a • (s : O) • x := by
          rw [← algebraMap_smul LL a, ← algebraMap_smul LL (s : O),
            ← algebraMap_smul LL ((s * t : nonZeroDivisors O) : O), smul_smul, smul_smul,
            Submonoid.coe_mul, map_mul]
          simp only at hc
          rw [← hc]
          congr 1
          ring
        rw [this]
        exact T.L.T.smul_mem _ hs
    obtain ⟨s, hs⟩ := this
    exact ⟨(⟨_, hs⟩, s), rfl⟩
end GlobalTheory.Cmp.WachMonoidal
