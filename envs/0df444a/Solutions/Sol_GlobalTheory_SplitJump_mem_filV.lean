-- Prove2me | solution 1 for GlobalTheory.SplitJump.mem_filV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:53.079662+00:00
-- url     : https://prove2.me/submissions/d67473ab-d4eb-4b91-bcc6-fcdc47e5e000

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.SplitJump
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V) in
omit [Field LL] [Algebra Qp LL] [Module LL V] [IsScalarTower Qp LL V] in
private lemma coord_tmul_eq_repr_mul (v : V) (b : BdR) (i : Fin n) :
    _root_.GlobalTheory.SplitJump.coord e BdR (v ⊗ₜ b) i = algebraMap Qp BdR (e.repr v i) * b := by
  simp [_root_.GlobalTheory.SplitJump.coord, Algebra.TensorProduct.basis_repr_tmul, mul_comm]
open Module TensorProduct in
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) in
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V) in
omit [Field LL] [Algebra Qp LL] [Module LL V] [IsScalarTower Qp LL V] in
private lemma sum_basis_tmul_coord_eq (y : V ⊗[Qp] BdR) :
    ∑ i, e i ⊗ₜ[Qp] _root_.GlobalTheory.SplitJump.coord e BdR y i = y := by
  apply (_root_.GlobalTheory.SplitJump.coord e BdR).injective
  ext j
  simp [map_sum, coord_tmul_eq_repr_mul, Finsupp.single_apply, Pi.single_apply]
end GlobalTheory.SplitJump
end
end

set_option autoImplicit false
noncomputable section
open Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.SplitJump
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
namespace GlobalTheory.SplitJump
namespace _root_.GlobalTheory.SplitJump
theorem _root_.solution (a : ℤ) (y : V ⊗[Qp] BdR) :
    y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a ↔ ∀ i, _root_.GlobalTheory.SplitJump.coord e BdR y i ∈ PD.Fil a := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.FilV
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨z, rfl⟩ i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      rw [AlgebraTensorModule.map_tmul, LinearMap.id_apply, coord_tmul_eq_repr_mul]
      rw [IsScalarTower.algebraMap_apply Qp K BdR, ← Algebra.smul_def]
      exact (PD.Fil a).smul_mem _ f.2
    | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact (PD.Fil a).add_mem h₁ h₂
  · intro h
    refine ⟨∑ i, e i ⊗ₜ[Qp]
      (⟨_root_.GlobalTheory.SplitJump.coord e BdR y i, h i⟩ : (PD.Fil a).restrictScalars Qp), ?_⟩
    rw [map_sum]
    conv_rhs => rw [← sum_basis_tmul_coord_eq e y]
    rfl
end _root_.GlobalTheory.SplitJump
end GlobalTheory.SplitJump
