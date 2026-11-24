-- Prove2me | solution 1 for GlobalTheory.CoeffExt.mem_B1T_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:33.035814+00:00
-- url     : https://prove2.me/submissions/58b5c087-51b3-492c-b932-79eae53de80f

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
variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [Module O V'] [IsScalarTower O LL V']
    [Module O' V'] [IsScalarTower O' LL' V']
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {E : V' ≃ₗ[LL] (ι → V)} {L : Lattice (O := O) ρ} {L' : Lattice (O := O') ρ'}
omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
  [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V'] [Fintype ι]
  [DecidableEq ι]
namespace GlobalTheory.CoeffExt
theorem _root_.solution (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hL : ∀ x, x ∈ L'.T ↔ ∀ i, E x i ∈ L.T) (c : G → V') :
    c ∈ latticeCoboundaries L' ↔ ∀ i, funCoord O G E c i ∈ latticeCoboundaries L := by
  simp only [latticeCoboundaries, Submodule.mem_map, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    refine ⟨E x i, (hL x).1 hx i, ?_⟩
    funext g
    simp [cob, hE]
  · intro H
    choose x hx hcx using H
    refine ⟨E.symm x, (hL _).2 (by simpa using hx), ?_⟩
    funext g
    apply E.injective
    funext i
    have h1 := congrFun (hcx i) g
    simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, funCoord_apply]
      at h1 ⊢
    rw [map_sub, Pi.sub_apply, hE, LinearEquiv.apply_symm_apply, h1]
end GlobalTheory.CoeffExt
