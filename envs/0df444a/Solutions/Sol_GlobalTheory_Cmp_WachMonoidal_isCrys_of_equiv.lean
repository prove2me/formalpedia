-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:10.947251+00:00
-- url     : https://prove2.me/submissions/ad8a97e9-3a25-438c-9eb9-21d2a42672ab

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensorB_comp
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensorB_id
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_coe_DcrisMap
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
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
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
namespace GlobalTheory.Cmp.WachMonoidal
theorem _root_.solution {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have h1 : CrystallineSubrepresentation.IsEquivariant ρ ρ' e.toLinearMap := he
  have h2 : CrystallineSubrepresentation.IsEquivariant ρ' ρ e.symm.toLinearMap := fun g x => by
    apply e.injective
    simp [he]
  let E : ↥(Dcris PD ρ) ≃ₗ[LL] ↥(Dcris PD ρ') :=
    LinearEquiv.ofLinear (CrystallineSubrepresentation.DcrisMap PD h1) (CrystallineSubrepresentation.DcrisMap PD h2)
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
  unfold IsCrys at h ⊢
  rw [← E.finrank_eq, ← e.finrank_eq, h]
end GlobalTheory.Cmp.WachMonoidal
