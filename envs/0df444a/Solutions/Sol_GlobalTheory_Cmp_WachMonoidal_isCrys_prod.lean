-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.isCrys_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:58:30.179305+00:00
-- url     : https://prove2.me/submissions/b11cd495-a007-4426-aeba-88a7fe36de87

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensorB_comp
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensorB_id
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensorB_zero
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_tensorB_add
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_coe_DcrisMap
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_finite_Dcris
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
theorem _root_.solution [FiniteDimensional LL V] [FiniteDimensional LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (h : IsCrys PD ρ) (h' : IsCrys PD ρ') : IsCrys PD (ρ.prod ρ') := by
  have := finite_Dcris PD h
  have := finite_Dcris PD h'
  have e1 : CrystallineSubrepresentation.IsEquivariant ρ (ρ.prod ρ') (LinearMap.inl LL V V') := fun g x => by
    simp [Representation.prod]
  have e2 : CrystallineSubrepresentation.IsEquivariant ρ' (ρ.prod ρ') (LinearMap.inr LL V V') := fun g x => by
    simp [Representation.prod]
  have p1 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ (LinearMap.fst LL V V') := fun g x => by
    simp [Representation.prod]
  have p2 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ' (LinearMap.snd LL V V') := fun g x => by
    simp [Representation.prod]
  let E : (↥(Dcris PD ρ) × ↥(Dcris PD ρ')) ≃ₗ[LL] ↥(Dcris PD (ρ.prod ρ')) :=
    LinearEquiv.ofLinear ((CrystallineSubrepresentation.DcrisMap PD e1).coprod (CrystallineSubrepresentation.DcrisMap PD e2))
      ((CrystallineSubrepresentation.DcrisMap PD p1).prod (CrystallineSubrepresentation.DcrisMap PD p2))
      (by
        refine LinearMap.ext fun x => Subtype.ext ?_
        simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
          Submodule.coe_add, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [← tensorB_add, show (LinearMap.inl LL V V').comp (LinearMap.fst LL V V') +
          (LinearMap.inr LL V V').comp (LinearMap.snd LL V V') = LinearMap.id by ext <;> simp,
          tensorB_id])
      (by
        refine LinearMap.ext fun x => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, tensorB_id, tensorB_zero, add_zero]
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, tensorB_id, tensorB_zero, zero_add])
  unfold IsCrys at h h' ⊢
  rw [← E.finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]
end GlobalTheory.Cmp.WachMonoidal
