-- Prove2me | solution 1 for GlobalTheory.ThetaInter.discrete_of_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:23.211445+00:00
-- url     : https://prove2.me/submissions/b447a40a-38dd-4b02-b135-f7eb953253e2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
namespace GlobalTheory.ThetaInter
theorem _root_.solution (hH : IsHerm H) {A : AddSubgroup W} (hd : IsSelfDual H A) (hfg : A.FG) :
    DiscreteTopology A := by
  obtain ⟨s, hs⟩ := hfg
  have hfg' : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 ⟨s, hs⟩
  have : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.2 hfg'
  have hc : Countable A := Finsupp.Countable.of_moduleFinite (R := ℤ)
  refine discreteTopology_iff_isOpen_singleton_zero.2 ⟨⋂ y ∈ s, {x | |altE H x y| < 1}, ?_, ?_⟩
  · exact isOpen_biInter_finset fun y _ =>
      isOpen_lt (altL H y).continuous_of_finiteDimensional.abs continuous_const
  · ext x
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have h0 : ∀ y ∈ A, altE H x y = 0 := by
        intro y hy
        rw [← hs] at hy
        induction hy using AddSubgroup.closure_induction with
        | mem y hy =>
          obtain ⟨m, hm⟩ := hd.ge x.2 y (hs ▸ AddSubgroup.subset_closure hy)
          have := h y hy
          rw [hm] at this ⊢
          have : |m| < 1 := by exact_mod_cast this
          exact_mod_cast Int.abs_lt_one_iff.1 this
        | zero => simp [altE]
        | add a b _ _ ha hb => simp only [altE, map_add, add_im] at ha hb ⊢; rw [ha, hb, add_zero]
        | neg a _ ha => simp only [altE, map_neg, neg_im] at ha ⊢; rw [ha, neg_zero]
      by_contra hx
      have hx' : (x : W) ≠ 0 := fun h => hx (Subtype.ext h)
      have hm : ∀ t : ℝ, t • (x : W) ∈ A := fun t => hd.le fun y hy =>
        ⟨0, by rw [altE_real_smul_left, h0 y hy]; simp⟩
      have : Function.Injective fun t : ℝ => (⟨t • (x : W), hm t⟩ : A) := fun a b hab =>
        smul_left_injective ℝ hx' (congrArg Subtype.val hab)
      exact not_countable this.countable
    · rintro rfl y _
      simp [altE]
end GlobalTheory.ThetaInter
