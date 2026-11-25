-- Prove2me | solution 1 for GlobalTheory.HL.QuadricShare.sum_char_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:47:50.727725+00:00
-- url     : https://prove2.me/submissions/ea5d8198-7259-4b69-aada-5aae8125e495

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProperIdealsOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsTraceChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpandByConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TwoGeometricSumsIndexBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFinite
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QuadricShare
open GlobalTheory.HL.GaussSummand
namespace GlobalTheory.HL.QuadricShare
theorem _root_.solution {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E}
    (UU : Submodule O V) (p : E) (R : Finset V) (hRU : ∀ u ∈ R, u ∈ UU)
    (hR : ∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = p • y) (χ : AddChar V ℂ)
    (hχ : ∀ u ∈ UU, χ (p • u) = 1) (u₀ : V) (hu₀ : u₀ ∈ R) (hne : χ u₀ ≠ 1) :
    ∑ u ∈ R, χ u = 0 := by
  have hex : ∀ w ∈ R, ∃ w', w' ∈ R ∧ ∃ y ∈ UU, (w + u₀) - w' = p • y := fun w hw =>
    (hR _ (UU.add_mem (hRU w hw) (hRU u₀ hu₀))).exists
  choose! σ hσR hσ using hex
  have hinj : Set.InjOn σ R := by
    intro w hw w' hw' h
    obtain ⟨y, hy, e⟩ := hσ w hw
    obtain ⟨y', hy', e'⟩ := hσ w' hw'
    refine (hR w (hRU w hw)).unique ⟨hw, 0, UU.zero_mem, by simp⟩ ⟨hw', y - y', UU.sub_mem hy hy', ?_⟩
    rw [smul_sub, ← e, ← e', h]; abel
  have himg : R.image σ = R := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      exact hσR w hw
    · rw [Finset.card_image_of_injOn hinj]
  have h1 : ∑ u ∈ R, χ u = ∑ u ∈ R, χ u * χ u₀ := by
    conv_lhs => rw [← himg, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨y, hy, e⟩ := hσ w hw
    have : w + u₀ = σ w + p • y := by rw [← e]; abel
    rw [← AddChar.map_add_eq_mul, this, AddChar.map_add_eq_mul, hχ y hy, mul_one]
  rw [← Finset.sum_mul] at h1
  have h2 : (∑ u ∈ R, χ u) * (1 - χ u₀) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hne.symm)
end GlobalTheory.HL.QuadricShare
