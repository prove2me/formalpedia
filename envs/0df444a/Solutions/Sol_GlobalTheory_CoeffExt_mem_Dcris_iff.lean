-- Prove2me | solution 1 for GlobalTheory.CoeffExt.mem_Dcris_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:41:52.745002+00:00
-- url     : https://prove2.me/submissions/a7082434-0cb8-4dc3-88ab-d763d089903f

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_tensCoord_actVB

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
theorem _root_.solution (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (x : V' ⊗[Qp] B) :
    x ∈ Dcris PD ρ' ↔ ∀ i, tensCoord E B x i ∈ Dcris PD ρ := by
  have key : ∀ {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
      (r : Representation LL G W) (y : W ⊗[Qp] B), y ∈ Dcris PD r ↔ ∀ g, actVB PD r g y = y := by
    intro W _ _ _ _ r y
    simp [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
  have key' : x ∈ Dcris PD ρ' ↔ ∀ g, actVB PD ρ' g x = x := by
    simp [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
  rw [key']
  constructor
  · intro hx i
    rw [key]
    intro g
    rw [← tensCoord_actVB PD hE g x i, hx g]
  · intro hx g
    apply (tensCoord E B).injective
    funext i
    rw [tensCoord_actVB PD hE]
    exact (key _ _).1 (hx i) g
end GlobalTheory.CoeffExt
