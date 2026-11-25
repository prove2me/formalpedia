-- Prove2me | solution 1 for GlobalTheory.CoeffExt.lenOl_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:13.876466+00:00
-- url     : https://prove2.me/submissions/8861560e-2fbe-418d-9f26-7a671cc92b4e

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_funCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CoeffExt.funCoord_apply
section
noncomputable section
namespace GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
section Linear
variable {R : Type} [Ring R] {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module R W]
  [Module R W'] {ι : Type}
end Linear
section Length
variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {W W' : Type} [AddCommGroup W]
  [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W'] [IsScalarTower O O' W'] {ι : Type}
  [Fintype ι]
end Length
section Tensor
variable {Qp : Type} [Field Qp] {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
  [Algebra Qp LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  [Module LL' V'] [IsScalarTower Qp LL' V']
  {ι : Type} [Fintype ι] [DecidableEq ι] (E : V' ≃ₗ[LL] (ι → V))
end Tensor
section Period
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}
end Period
section Cochains
variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  {V V' : Type} [AddCommGroup V] [AddCommGroup V'] [Module LL V] [Module LL V'] [Module O V]
  [Module O V'] [IsScalarTower O LL V] [IsScalarTower O LL V'] {ι : Type}
end Cochains
section Lat
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
    {O O' : Type} [CommRing O] [CommRing O'] [Algebra O LL] [Algebra O' LL']
    {ι : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace G]
section One
variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [Module O V'] [IsScalarTower O LL V']
    [Module O' V'] [IsScalarTower O' LL' V']
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {E : V' ≃ₗ[LL] (ι → V)} {L : Lattice (O := O) ρ} {L' : Lattice (O := O') ρ'}
end One
section Two
variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [Module O V₁] [IsScalarTower O LL V₁]
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul LL V₁]
    {V₁' : Type} [AddCommGroup V₁'] [Module LL V₁'] [Module Qp V₁'] [IsScalarTower Qp LL V₁']
    [Module LL' V₁'] [IsScalarTower Qp LL' V₁'] [Module O V₁'] [IsScalarTower O LL V₁']
    [Module O' V₁'] [IsScalarTower O' LL' V₁']
    [TopologicalSpace V₁'] [ContinuousAdd V₁'] [ContinuousConstSMul LL' V₁']
    {ρ₁ : Representation LL G V₁} {ρ₁' : Representation LL' G V₁'}
    {E₁ : V₁' ≃ₗ[LL] (ι → V₁)} {L₁ : Lattice (O := O) ρ₁} {L₁' : Lattice (O := O') ρ₁'}
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [Module O V₂] [IsScalarTower O LL V₂]
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul LL V₂]
    {V₂' : Type} [AddCommGroup V₂'] [Module LL V₂'] [Module Qp V₂'] [IsScalarTower Qp LL V₂']
    [Module LL' V₂'] [IsScalarTower Qp LL' V₂'] [Module O V₂'] [IsScalarTower O LL V₂']
    [Module O' V₂'] [IsScalarTower O' LL' V₂']
    [TopologicalSpace V₂'] [ContinuousAdd V₂'] [ContinuousConstSMul LL' V₂']
    {ρ₂ : Representation LL G V₂} {ρ₂' : Representation LL' G V₂'}
    {E₂ : V₂' ≃ₗ[LL] (ι → V₂)} {L₂ : Lattice (O := O) ρ₂} {L₂' : Lattice (O := O') ρ₂'}
    (F : LatHom L₁ L₂) (F' : LatHom L₁' L₂')
end Two
private theorem length_quotient_eq_card_mul_of_pi_equiv {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module R W] [Module R W'] [Module R' W']
    [IsScalarTower R R' W'] {ι : Type} [Fintype ι] (E : W' ≃ₗ[R] (ι → W))
    (N' : Submodule R' W') (N : Submodule R W) (hN : ∀ x, x ∈ N' ↔ ∀ i, E x i ∈ N) :
    Module.length R (W' ⧸ N') = Fintype.card ι * Module.length R (W ⧸ N) := by
  classical
  let Φ : W' →ₗ[R] (ι → W ⧸ N) := LinearMap.pi fun i => N.mkQ ∘ₗ (LinearMap.proj i ∘ₗ E.toLinearMap)
  have hsurj : Function.Surjective Φ := by
    intro y
    choose s hs using fun i => Submodule.Quotient.mk_surjective _ (y i)
    refine ⟨E.symm s, ?_⟩
    funext i
    simp [Φ, ← hs i]
  have hker : LinearMap.ker Φ = N'.restrictScalars R := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, hN, funext_iff]
    simp [Φ, Submodule.Quotient.mk_eq_zero]
  let e : (W' ⧸ N') ≃ₗ[R] (ι → W ⧸ N) :=
    (Submodule.Quotient.restrictScalarsEquiv R N').symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ Φ.quotKerEquivOfSurjective hsurj
  rw [e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]
end Lat
end GlobalTheory.CoeffExt
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
    {O O' : Type} [CommRing O] [CommRing O'] [Algebra O LL] [Algebra O' LL']
    {ι : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace G]
omit [TopologicalSpace G] [DecidableEq ι]
namespace GlobalTheory.CoeffExt
theorem _root_.solution [Algebra O O'] [IsLocalRing O] [IsLocalRing O'] [IsLocalHom (algebraMap O O')]
    (b : Basis ι O O') :
    lenOl PD (O := O') * Module.length (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') =
      Fintype.card ι * lenOl PD (O := O) := by
  unfold lenOl
  rw [← IsLocalRing.length_restrictScalars O O']
  rw [length_quotient_eq_card_mul_of_pi_equiv b.equivFun (Ideal.span {((PD.p : ℕ) : O')}) (Ideal.span {((PD.p : ℕ) : O)})]
  intro x
  have hcast : ∀ y : O', ((PD.p : ℕ) : O') * y = ((PD.p : ℕ) : O) • y := fun y => by
    rw [Algebra.smul_def, map_natCast]
  simp only [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    refine ⟨b.equivFun y i, ?_⟩
    rw [hcast, map_smul, Pi.smul_apply, smul_eq_mul]
  · intro H
    choose a ha using H
    refine ⟨b.equivFun.symm a, ?_⟩
    apply b.equivFun.injective
    rw [hcast, map_smul, LinearEquiv.apply_symm_apply]
    funext i
    rw [ha i, Pi.smul_apply, smul_eq_mul]
end GlobalTheory.CoeffExt
