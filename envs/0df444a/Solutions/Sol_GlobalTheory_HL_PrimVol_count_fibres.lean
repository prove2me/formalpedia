-- Prove2me | solution 1 for GlobalTheory.HL.PrimVol.count_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:18.051133+00:00
-- url     : https://prove2.me/submissions/0f2c9195-861d-4552-a1ab-650318f94700

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContent
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimVol
namespace GlobalTheory.HL.PrimVol
theorem _root_.solution {W W' : Type} [AddCommGroup W] [AddCommGroup W'] (T : AddSubgroup W)
    (H : AddSubgroup W') (Pr : W → Prop) (g : W → W') (B : Set W') (Q : ℝ)
    (hB : ∀ x ∈ B, ∀ a ∈ H, x + a ∈ B)
    (hfin : ((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).Finite)
    (hg : ∀ z z', Pr z → Pr z' → z - z' ∈ T → g z - g z' ∈ H)
    (hfib : ∀ G ∈ B, ((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).Finite ∧
      Q ≤ 2 * (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).ncard : ℝ) ∧
      (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).ncard : ℝ) ≤ 2 * Q) :
    ((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).Finite ∧
      (((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).ncard : ℝ) * Q ≤
        2 * (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).ncard : ℝ) ∧
      (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).ncard : ℝ) ≤
        2 * ((((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).ncard : ℝ) * Q) := by
  set Fb : W' ⧸ H → Set (W ⧸ T) := fun c =>
    (QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ (QuotientAddGroup.mk (g z) : W' ⧸ H) = c} with hFb
  have hF : ∀ c ∈ hfin.toFinset, (Fb c).Finite ∧ Q ≤ 2 * ((Fb c).ncard : ℝ) ∧
      ((Fb c).ncard : ℝ) ≤ 2 * Q := by
    intro c hc
    obtain ⟨G, hG, rfl⟩ := (Set.Finite.mem_toFinset _).1 hc
    have := hfib G hG
    simp only [hFb, QuotientAddGroup.eq_iff_sub_mem]
    exact this
  have hU : (QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B} = ⋃ c ∈ hfin.toFinset, Fb c := by
    ext q
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, hFb]
    constructor
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨_, ⟨_, h2, rfl⟩, z, ⟨h1, rfl⟩, rfl⟩
    · rintro ⟨c, ⟨G, hG, rfl⟩, z, ⟨h1, h2⟩, rfl⟩
      refine ⟨z, ⟨h1, ?_⟩, rfl⟩
      have := hB G hG _ (QuotientAddGroup.eq_iff_sub_mem.1 h2)
      simpa using this
  have hD : (hfin.toFinset : Set (W' ⧸ H)).PairwiseDisjoint Fb := by
    intro c _ c' _ hne
    refine Set.disjoint_left.2 ?_
    rintro q ⟨z, ⟨h1, rfl⟩, rfl⟩ ⟨z', ⟨h1', rfl⟩, h3⟩
    exact hne (QuotientAddGroup.eq_iff_sub_mem.2
      (hg z z' h1 h1' (QuotientAddGroup.eq_iff_sub_mem.1 h3.symm)))
  have hC : (⋃ c ∈ hfin.toFinset, Fb c).ncard = ∑ c ∈ hfin.toFinset, (Fb c).ncard := by
    have := Set.Finite.ncard_biUnion (hfin.toFinset.finite_toSet) (fun c hc => (hF c hc).1) hD
    rw [finsum_mem_coe_finset] at this
    exact this
  rw [hU, hC, Set.ncard_eq_toFinset_card _ hfin]
  refine ⟨Set.Finite.biUnion hfin.toFinset.finite_toSet (fun c hc => (hF c hc).1), ?_, ?_⟩
  · push_cast
    rw [Finset.mul_sum]
    have := Finset.card_nsmul_le_sum hfin.toFinset (fun c => 2 * ((Fb c).ncard : ℝ)) Q
      (fun c hc => (hF c hc).2.1)
    simpa using this
  · push_cast
    have := Finset.sum_le_card_nsmul hfin.toFinset (fun c => ((Fb c).ncard : ℝ)) (2 * Q)
      (fun c hc => (hF c hc).2.2)
    rw [nsmul_eq_mul] at this
    linarith
end GlobalTheory.HL.PrimVol
