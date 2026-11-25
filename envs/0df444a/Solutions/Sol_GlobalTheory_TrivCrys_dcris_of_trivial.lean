-- Prove2me | solution 1 for GlobalTheory.TrivCrys.dcris_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:34.112165+00:00
-- url     : https://prove2.me/submissions/3928ecaa-dcf6-473e-af08-12cae625a770

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_KernelDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_NonGaloisSurvey_CrystallineCyclotomic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCrysLatOfTrivial
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineSubrepresentation_invariantsEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB
namespace GlobalTheory.TrivCrys
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
private theorem lid_rTensor_map_id_eq {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] (f : V →ₗ[Qp] Qp) (σ : B →ₗ[Qp] B) (x : V ⊗[Qp] B) :
    TensorProduct.lid Qp B (LinearMap.rTensor B f
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) σ x)) =
      σ (TensorProduct.lid Qp B (LinearMap.rTensor B f x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [AlgebraTensorModule.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
open PowerSeries in
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] in
private theorem eq_sum_basis_tmul_coord {V : Type} [AddCommGroup V] [Module Qp V] {ι : Type}
    [Fintype ι] (b : Basis ι Qp V) (x : V ⊗[Qp] B) :
    x = ∑ i, b i ⊗ₜ[Qp] TensorProduct.lid Qp B (LinearMap.rTensor B (b.coord i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
    simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
end GlobalTheory.TrivCrys
end
end

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module Qp V]
    [Module LL V] [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  have hid : ∀ g, ρ g = LinearMap.id := fun g => LinearMap.ext (hρ g)
  ext x
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris, LinearMap.mem_range]
  constructor
  · intro hx
    let b := Module.finBasis Qp V
    have hc : ∀ i, ∃ k : K₀, algebraMap K₀ B k =
        TensorProduct.lid Qp B (LinearMap.rTensor B (b.coord i) x) := by
      intro i
      refine (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.invariantsEq PD _).mp fun g => ?_
      have h := hx g
      unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVB at h
      rw [hid g] at h
      conv_rhs => rw [← h]
      rw [lid_rTensor_map_id_eq]
      rfl
    choose k hk using hc
    refine ⟨∑ i, b i ⊗ₜ[Qp] k i, ?_⟩
    rw [map_sum, eq_sum_basis_tmul_coord b x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraTensorModule.map_tmul, ← hk i]
    rfl
  · rintro ⟨y, rfl⟩ g
    unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVB
    rw [hid g]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [AlgebraTensorModule.map_tmul]
    | add y z hy hz => simp only [map_add, hy, hz]
end _root_.GlobalTheory.TrivCrys
end GlobalTheory.TrivCrys
