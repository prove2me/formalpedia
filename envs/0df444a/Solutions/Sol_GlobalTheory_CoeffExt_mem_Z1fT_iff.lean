-- Prove2me | solution 1 for GlobalTheory.CoeffExt.mem_Z1fT_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:29:54.258406+00:00
-- url     : https://prove2.me/submissions/45160d55-f3f7-4d6f-83dc-5ee92ed41eca

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_funCoord_apply
import Theorems.Thm_GlobalTheory_CoeffExt_mem_continuous_cocycles_iff_coords
import Theorems.Thm_GlobalTheory_CoeffExt_mem_finiteCocycles_iff_bcrisTensor_coboundary
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
    (hs : Continuous E.symm) (hL : ∀ x, x ∈ L'.T ↔ ∀ i, E x i ∈ L.T) (c : G → V') :
    c ∈ latticeFiniteCocycles PD L' ↔ ∀ i, funCoord O G E c i ∈ latticeFiniteCocycles PD L := by
  simp only [latticeFiniteCocycles, latticeCocycles, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_pi,
    Set.mem_univ, true_implies]
  rw [mem_continuous_cocycles_iff_coords (O := O) hE hc hs, mem_finiteCocycles_iff_bcrisTensor_coboundary (O := O) PD hE hc hs]
  simp only [hL, funCoord_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ i
    exact ⟨⟨h1 i, fun g => h2 g i⟩, h3 i⟩
  · intro H
    exact ⟨⟨fun i => (H i).1.1, fun g i => (H i).1.2 g⟩, fun i => (H i).2⟩
end GlobalTheory.CoeffExt
