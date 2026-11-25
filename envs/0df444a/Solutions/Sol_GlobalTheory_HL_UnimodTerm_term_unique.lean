-- Prove2me | solution 1 for GlobalTheory.HL.UnimodTerm.term_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:17.688117+00:00
-- url     : https://prove2.me/submissions/c3b71188-6a25-41a3-9a3d-f39e4794aa64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralOfMulVec
import Theorems.Thm_GlobalTheory_HL_UnimodTerm_proj_mem
import Theorems.Thm_GlobalTheory_HL_UnimodTerm_le_of_M_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameGram_main
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.UnimodTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma mem_frameCls_self (g h : Fin (r + 1) → S.V) : (g, h) ∈ S.frameCls g h := by
  unfold _root_.GlobalTheory.HL.Frames.frameCls
  have hint : _root_.GlobalTheory.HL.IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := by
    unfold _root_.GlobalTheory.HL.IsIntM
    intro i j
    by_cases hij : i = j
    · subst hij; simp [L.O.one_mem]
    · simp [Matrix.one_apply_ne hij, L.O.zero_mem]
  refine ⟨1, 1, hint, hint, fun i j hji => ⟨Matrix.one_apply_ne (ne_of_gt hji), Matrix.one_apply_ne (ne_of_gt hji)⟩,
    fun i => ⟨Matrix.one_apply_eq i, Matrix.one_apply_eq i⟩, fun i j => ⟨0, L.O.zero_mem, by simp⟩, ?_, ?_⟩
  · intro j; simp [Matrix.one_apply]
  · intro j; simp [Matrix.one_apply]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma Mof_le_of_mem_frameCls {g h g' h' : Fin (r + 1) → S.V}
    (hP : (g', h') ∈ S.frameCls g h) : S.Mof g' h' ≤ S.Mof g h := by
  obtain ⟨A, A', hA, hA', -, -, hdiff, h1, h2⟩ := hP
  dsimp only at h1 h2
  obtain ⟨-, -, -, -, -, hth0, -, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hθ : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth0, map_one]
  choose c hc hcdef using hdiff
  unfold _root_.GlobalTheory.HL.Frames.Mof
  rw [Submodule.span_le]
  rintro v (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [h1 j]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (⟨A i j, hA i j⟩ : L.O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
  · have hsplit : algebraMap F E S.th⁻¹ • (h' j - g' j) =
        ∑ i, A' i j • (algebraMap F E S.th⁻¹ • (h i - g i)) + ∑ i, c i j • g i := by
      rw [h1 j, h2 j, ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hci : c i j = algebraMap F E S.th⁻¹ * (A' i j - A i j) := by
        rw [hcdef, ← mul_assoc, hθ, one_mul]
      rw [hci]
      module
    show algebraMap F E S.th⁻¹ • (h' j - g' j) ∈ _
    rw [hsplit]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)
    · exact Submodule.smul_mem _ (⟨A' i j, hA' i j⟩ : L.O) (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
    · exact Submodule.smul_mem _ (⟨c i j, hc i j⟩ : L.O) (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
end GlobalTheory.HL.UnimodTerm
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UnimodTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k)
namespace GlobalTheory.HL.UnimodTerm
namespace _root_.GlobalTheory.HL.UnimodTerm
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → S.BBzero d Λ ∧ ∀ Λ', S.IsTerm d Λ' → S.Fr d Λ' = S.Fr d Λ → Λ' = Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha
  obtain ⟨-, -, hMs, -, -, -, -, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  refine ⟨?_, fun Λ' hT' hFr => ?_⟩
  · unfold _root_.GlobalTheory.HL.Frames.BBzero
    refine le_antisymm hMs fun x hx => ?_
    have hx' : x ∈ Λ ⊓ Submodule.restrictScalars L.O S.ME := hx
    exact _root_.GlobalTheory.HL.UnimodTerm.proj_mem S hT ha (Submodule.mem_inf.mp hx').1
      (Submodule.mem_inf.mp hx').2 (by simp)
  · have hM : S.M d Λ' = S.M d Λ := by
      unfold _root_.GlobalTheory.HL.Frames.Fr at hFr
      unfold _root_.GlobalTheory.HL.Frames.M
      apply le_antisymm
      · have hmem := mem_frameCls_self S (S.fr d Λ') (S.fr' d Λ')
        rw [hFr] at hmem
        exact Mof_le_of_mem_frameCls S hmem
      · have hmem := mem_frameCls_self S (S.fr d Λ) (S.fr' d Λ)
        rw [← hFr] at hmem
        exact Mof_le_of_mem_frameCls S hmem
    exact le_antisymm (_root_.GlobalTheory.HL.UnimodTerm.le_of_M_eq S hT hT' ha hM)
      (_root_.GlobalTheory.HL.UnimodTerm.le_of_M_eq S hT' hT ha hM.symm)
end _root_.GlobalTheory.HL.UnimodTerm
end GlobalTheory.HL.UnimodTerm
