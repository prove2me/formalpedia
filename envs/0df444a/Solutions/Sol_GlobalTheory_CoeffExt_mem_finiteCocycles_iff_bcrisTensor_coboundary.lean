-- Prove2me | solution 1 for GlobalTheory.CoeffExt.mem_finiteCocycles_iff_bcrisTensor_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:33.886167+00:00
-- url     : https://prove2.me/submissions/ac61c54f-aa12-48da-975a-bb9e985f0909

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_tensCoord_actVB
import Theorems.Thm_GlobalTheory_CoeffExt_funCoord_apply
import Theorems.Thm_GlobalTheory_CoeffExt_mem_continuous_cocycles_iff_coords
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
namespace GlobalTheory.CoeffExt
theorem _root_.solution (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (hc : Continuous E)
    (hs : Continuous E.symm) (c : G → V') :
    c ∈ finiteCocycles PD ρ' ↔ ∀ i, funCoord O G E c i ∈ finiteCocycles PD ρ := by
  change (c ∈ continuousCocycles ρ' ∧ ∃ x : V' ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ' g x - x) ↔
    ∀ i, (funCoord O G E c i ∈ continuousCocycles ρ ∧
      ∃ x : V ⊗[Qp] B, ∀ g, funCoord O G E c i g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x)
  rw [mem_continuous_cocycles_iff_coords (O := O) hE hc hs]
  simp only [funCoord_apply]
  constructor
  · rintro ⟨hz, x, hx⟩ i
    refine ⟨hz i, tensCoord E B x i, fun g => ?_⟩
    rw [← tensCoord_tmul E (c g) (1 : B) i, hx g, map_sub, Pi.sub_apply, tensCoord_actVB PD hE]
  · intro H
    have hz : ∀ i, funCoord O G E c i ∈ continuousCocycles ρ := fun i => (H i).1
    choose x hx using fun i => (H i).2
    refine ⟨hz, (tensCoord E B).symm x, fun g => ?_⟩
    apply (tensCoord E B).injective
    funext i
    rw [tensCoord_tmul, map_sub, Pi.sub_apply, tensCoord_actVB PD hE, LinearEquiv.apply_symm_apply,
      hx i g]
end GlobalTheory.CoeffExt
