-- Prove2me | solution 1 for GlobalTheory.CoeffExt.tensCoord_actVB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:13.219216+00:00
-- url     : https://prove2.me/submissions/95e9345a-ebae-4d73-ba7b-526ceaecb4d1

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_tensCoord_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}
omit [Algebra LL LL'] [IsScalarTower LL LL' V']
namespace GlobalTheory.CoeffExt
theorem _root_.solution (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (g : G) (x : V' ⊗[Qp] B)
    (i : ι) : tensCoord E B (actVB PD ρ' g x) i = actVB PD ρ g (tensCoord E B x i) := by
  unfold actVB
  exact tensCoord_map E (ρ' g) (ρ g) (hE g) _ x i
end GlobalTheory.CoeffExt
