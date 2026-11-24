-- Prove2me | solution 1 for GlobalTheory.CoeffExt.mem_ImF_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:14.361168+00:00
-- url     : https://prove2.me/submissions/7101c212-910d-4171-b2bc-b3cd6ea6855f

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_funCoord_apply
import Theorems.Thm_GlobalTheory_CoeffExt_mem_Z1fT_iff
import Theorems.Thm_GlobalTheory_CoeffExt_mem_B1T_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CoeffExt.funCoord_apply

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
namespace GlobalTheory.CoeffExt
theorem _root_.solution (hE₁ : ∀ g x i, E₁ (ρ₁' g x) i = ρ₁ g (E₁ x i)) (hc₁ : Continuous E₁)
    (hs₁ : Continuous E₁.symm) (hL₁ : ∀ x, x ∈ L₁'.T ↔ ∀ i, E₁ x i ∈ L₁.T)
    (hE₂ : ∀ g x i, E₂ (ρ₂' g x) i = ρ₂ g (E₂ x i))
    (hL₂ : ∀ x, x ∈ L₂'.T ↔ ∀ i, E₂ x i ∈ L₂.T)
    (hF : ∀ x i, E₂ (F'.f x) i = F.f (E₁ x i)) (c : G → V₂') :
    c ∈ F'.ImF PD ↔ ∀ i, funCoord O G E₂ c i ∈ F.ImF PD := by
  have post_coord : ∀ (x : G → V₁') i,
      funCoord O G E₂ (F'.post x) i = F.post (funCoord O G E₁ x i) := by
    intro x i
    funext g
    simp [LatHom.post, hF]
  unfold LatHom.ImF
  constructor
  · intro hc i
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hc
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_sup.2 ⟨F.post (funCoord O G E₁ x i),
      Submodule.mem_map_of_mem ((mem_Z1fT_iff PD hE₁ hc₁ hs₁ hL₁ x).1 hx i),
      funCoord O G E₂ z i, (mem_B1T_iff hE₂ hL₂ z).1 hz i, ?_⟩
    rw [map_add, Pi.add_apply, post_coord]
  · intro H
    choose y hy z hz hyz using fun i => Submodule.mem_sup.1 (H i)
    choose x hx hxy using fun i => Submodule.mem_map.1 (hy i)
    refine Submodule.mem_sup.2 ⟨F'.post ((funCoord O G E₁).symm x),
      Submodule.mem_map_of_mem ((mem_Z1fT_iff PD hE₁ hc₁ hs₁ hL₁ _).2 (by simpa using hx)),
      (funCoord O G E₂).symm z, (mem_B1T_iff hE₂ hL₂ _).2 (by simpa using hz), ?_⟩
    apply (funCoord O G E₂).injective
    funext i
    rw [map_add, Pi.add_apply, post_coord, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, hxy i, hyz i]
end GlobalTheory.CoeffExt
