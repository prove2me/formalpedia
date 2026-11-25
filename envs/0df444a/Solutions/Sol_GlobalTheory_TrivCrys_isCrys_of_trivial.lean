-- Prove2me | solution 1 for GlobalTheory.TrivCrys.isCrys_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:36.521323+00:00
-- url     : https://prove2.me/submissions/7e4c8fbd-1e1c-48a5-9665-c2c38c60fd51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_KernelDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_NonGaloisSurvey_CrystallineCyclotomic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCrysLatOfTrivial
import Theorems.Thm_GlobalTheory_TrivCrys_dcris_of_trivial
import Theorems.Thm_GlobalTheory_Survey_CrystallineCyclotomic_nontrivial_B


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB
open GlobalTheory GlobalTheory.TrivCrys
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
open PowerSeries
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
namespace GlobalTheory.TrivCrys
namespace _root_.GlobalTheory.TrivCrys
theorem _root_.solution {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) : _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys PD ρ := by
  haveI := _root_.GlobalTheory.Survey.CrystallineCyclotomic.nontrivial_B PD
  have key : ⇑(AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) =
      ⇑(LinearMap.lTensor V (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [AlgebraTensorModule.map_tmul]
    | add u w hu hw => simp only [map_add, hu, hw]
  have hinj : Function.Injective (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
    rw [key]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (fun a c h => (algebraMap K₀ B).injective h)
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys
  rw [_root_.GlobalTheory.TrivCrys.dcris_of_trivial PD ρ hρ, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_tensorProduct, mul_comm]
end _root_.GlobalTheory.TrivCrys
end GlobalTheory.TrivCrys
