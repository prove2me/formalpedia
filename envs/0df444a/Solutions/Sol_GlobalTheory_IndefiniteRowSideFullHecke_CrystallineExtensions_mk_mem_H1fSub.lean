-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.mk_mem_H1fSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:35:06.98737+00:00
-- url     : https://prove2.me/submissions/446ab1cf-cd5e-4d05-a8d7-7a54e9405b00

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineExtensions
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
theorem _root_.solution {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL G V)
    (c : ↥(continuousCocycles ρ)) : (Submodule.Quotient.mk c : H1V ρ) ∈ H1fSubmodule PD ρ ↔ (c : G → V) ∈ finiteCocycles PD ρ := by
  refine ⟨?_, fun h => ⟨c, h, rfl⟩⟩
  rintro ⟨c', ⟨-, x, hx⟩, h⟩
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq _).mp h
  refine ⟨c.2, x - b ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  have h1 : ρ g b - b = (c' : G → V) g - (c : G → V) g := congrFun hb g
  have h2 : (c : G → V) g = (c' : G → V) g - (ρ g b - b) := by rw [h1]; abel
  have h3 : actVB PD ρ g (b ⊗ₜ[Qp] (1 : B)) = ρ g b ⊗ₜ[Qp] (1 : B) := by simp [actVB]
  have h4 : (c' : G → V) g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x := hx g
  rw [h2, sub_tmul, sub_tmul, h4, map_sub, h3]
  abel
end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
