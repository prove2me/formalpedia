-- Prove2me | solution 1 for GlobalTheory.FinTyp.rank_le_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:27.50315+00:00
-- url     : https://prove2.me/submissions/4532dd14-c9b4-4752-9566-d0ae879820ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Theorems.Thm_GlobalTheory_FinTypCount_rt_mul
import Theorems.Thm_GlobalTheory_FinTypCount_countable_range_rt
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.FinTypCount
namespace GlobalTheory
namespace FinTyp
theorem _root_.solution : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by
  intro L _ _ _ n π
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
  obtain ⟨N, hN, hfix⟩ := π.smooth f hfS
  let T := Submodule.span ℂ (Set.range fun h : GAf L n => rt L n h f)
  have hle : T ≤ π.S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact π.stable h f hfS
  have hst : ∀ h, ∀ u ∈ T, rt L n h u ∈ T := by
    intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h', rfl⟩ := hx
      exact Submodule.subset_span ⟨h * h', rt_mul h h' f⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hfT : f ∈ T := Submodule.subset_span ⟨1, by funext x; simp [rt]⟩
  have hT : T = π.S := by
    rcases π.irr T hle hst with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hfT)) hf0
    · exact h
  rw [← hT]
  exact (rank_span_le _).trans (Cardinal.le_aleph0_iff_set_countable.2 (countable_range_rt hN hfix))
end FinTyp
end GlobalTheory
