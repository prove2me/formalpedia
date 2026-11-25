-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.dualLatCrys_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:57:23.685802+00:00
-- url     : https://prove2.me/submissions/fc727ae8-47cf-4c47-b9c5-dd6171fcdaf9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_isCrys_of_equiv
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
theorem _root_.solution (h : CrystallineSubrepresentation.DualCrys PD LL) : DualLatCrys PD LL O := by
  rintro T T' Pr hT ⟨hG, -, h2, hr, -⟩
  have hinj : Function.Injective Pr.flip := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y fun x => LinearMap.congr_fun hy x
  have hbij : Function.Bijective Pr.flip :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [← hr]; exact (Subspace.dual_finrank_eq (K := LL) (V := T.V)).symm)).mp hinj⟩
  let e : T'.V ≃ₗ[LL] Module.Dual LL T.V := LinearEquiv.ofBijective Pr.flip hbij
  refine isCrys_of_equiv PD e.symm (fun g f => ?_) (h T.V T.ρ hT)
  obtain ⟨y, rfl⟩ := e.surjective f
  apply e.injective
  rw [e.apply_symm_apply, e.symm_apply_apply]
  ext x
  change Pr (T.ρ g⁻¹ x) y = Pr x (T'.ρ g y)
  rw [← hG g]
  simp
end GlobalTheory.Cmp.WachMonoidal
