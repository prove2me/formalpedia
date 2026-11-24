-- Prove2me | solution 1 for GlobalTheory.SplitJump.coord_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:55:00.894724+00:00
-- url     : https://prove2.me/submissions/48ac7d48-be7a-4820-be57-f027551cd7b3

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
theorem _root_.solution (g : G) (x : V ⊗[Qp] BdR) :
    _root_.GlobalTheory.SplitJump.coord e BdR (_root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g x) =
      (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)).mulVec
        fun i => PD.actdR g (_root_.GlobalTheory.SplitJump.coord e BdR x i) := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR
  induction x using TensorProduct.induction_on with
  | zero => ext i; simp [Matrix.mulVec, dotProduct]
  | tmul v b =>
    ext i
    have hv : ρ g v = ∑ j, e.repr v j • ρ g (e j) := by
      conv_lhs => rw [← e.sum_repr v]
      rw [map_sum]
      simp [LinearMap.map_smul_of_tower]
    have hσ : ∀ r : Qp, PD.actdR g (algebraMap Qp BdR r) = algebraMap Qp BdR r := by
      intro r
      rw [IsScalarTower.algebraMap_apply Qp K BdR, AlgEquiv.commutes]
    simp only [AlgebraTensorModule.map_tmul, coord_tmul_eq_repr_mul, Matrix.mulVec, dotProduct,
      Matrix.of_apply]
    rw [hv, map_sum, Finset.sum_apply', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hσ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
    change _ * PD.actdR g b = _
    ring
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, ← Matrix.mulVec_add]
    congr 1
    ext i
    simp
end _root_.GlobalTheory.SplitJump
end GlobalTheory.SplitJump
