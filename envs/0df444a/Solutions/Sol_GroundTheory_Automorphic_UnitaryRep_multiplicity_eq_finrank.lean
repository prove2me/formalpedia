-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.multiplicity_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:37.49186+00:00
-- url     : https://prove2.me/submissions/7e71ce9e-4929-4f30-9346-a5345c12f0d8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_finrank_intertwiners_eq_card
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_isIrreducible_iff
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isIrreducible_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
variable (hirr : ∀ j, (π.restrict (V j) (hinv j)).IsIrreducible)
include hsum hirr
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite)
    (c : Quotient (restrictSetoid π hinv)) {σ : UnitaryRep G K}
    (hσ : (π.restrict (V c.out) (hinv c.out)).IsEquivalent σ) :
    FiniteDimensional ℂ (σ.intertwiners π) ∧
      multiplicity π hinv c = Module.finrank ℂ (σ.intertwiners π) := by
  have hσirr : σ.IsIrreducible := hσ.isIrreducible_iff.1 (hirr c.out)
  have hiff : ∀ j, (π.restrict (V j) (hinv j)).IsEquivalent σ ↔
      Quotient.mk (restrictSetoid π hinv) j = c := by
    intro j
    rw [← Quotient.out_eq c, Quotient.eq]
    exact ⟨fun h => h.trans hσ.symm, fun h => h.trans hσ⟩
  have hW : {j | (π.restrict (V j) (hinv j)).IsEquivalent σ}.Finite :=
    (hfin c.out).subset fun j hj => hj.trans hσ.symm
  obtain ⟨hfd, hrank⟩ := finrank_intertwiners_eq_card hinv hsum hirr hσirr hW
  refine ⟨hfd, ?_⟩
  rw [hrank, multiplicity]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun j => (hiff j).symm)
end GroundTheory.Automorphic.UnitaryRep
