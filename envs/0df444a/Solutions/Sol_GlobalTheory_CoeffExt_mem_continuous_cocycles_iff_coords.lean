-- Prove2me | solution 1 for GlobalTheory.CoeffExt.mem_continuous_cocycles_iff_coords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:02.032726+00:00
-- url     : https://prove2.me/submissions/cd1f4293-185c-4fb4-85bc-a73713b809f3

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
namespace GlobalTheory.CoeffExt
theorem _root_.solution (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (hc : Continuous E)
    (hs : Continuous E.symm) (c : G → V') :
    c ∈ continuousCocycles ρ' ↔ ∀ i, funCoord O G E c i ∈ continuousCocycles ρ := by
  change (Continuous c ∧ ∀ g h, c (g * h) = c g + ρ' g (c h)) ↔
    ∀ i, (Continuous (funCoord O G E c i) ∧ ∀ g h, funCoord O G E c i (g * h) =
      funCoord O G E c i g + ρ g (funCoord O G E c i h))
  simp only [funCoord_apply]
  constructor
  · rintro ⟨hcont, hcoc⟩ i
    refine ⟨(continuous_apply i).comp (hc.comp hcont), fun g h => ?_⟩
    rw [hcoc, map_add, Pi.add_apply, hE]
  · intro H
    refine ⟨?_, fun g h => ?_⟩
    · have hcont : Continuous fun g => E.symm (fun i => E (c g) i) :=
        hs.comp (continuous_pi fun i => (H i).1)
      simpa using hcont
    · apply E.injective
      funext i
      rw [map_add, Pi.add_apply, (H i).2 g h, hE]
end GlobalTheory.CoeffExt
