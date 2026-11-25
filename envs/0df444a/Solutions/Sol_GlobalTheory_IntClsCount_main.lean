-- Prove2me | solution 1 for GlobalTheory.IntClsCount.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:18:40.283989+00:00
-- url     : https://prove2.me/submissions/f400940a-0a48-453e-8998-501a0c6ecad4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RmulMul
import Theorems.Thm_GlobalTheory_IntClsCount_uni_mul
import Theorems.Thm_GlobalTheory_IntClsCount_int_mul
import Theorems.Thm_GlobalTheory_IntClsCount_exists_inv
import Theorems.Thm_GlobalTheory_IntClsCount_exists_reps
import Theorems.Thm_GlobalTheory_IntClsCount_rmul_mul
import Theorems.Thm_GlobalTheory_IntClsCount_pairing
import Theorems.Thm_GlobalTheory_IntClsCount_exists_section
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameClass_exists_inv
import Theorems.Thm_GlobalTheory_HL_FrameClass_frame_classes
import Theorems.Thm_GlobalTheory_HL_encard_uniCosets_le
import Theorems.Thm_GlobalTheory_T_leadingMinors_prod_denominator_unitriangular_factors
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
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
open GlobalTheory GlobalTheory.IntClsCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.IntClsCount
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 0 ≤ S.vD → ({C : Set S.FrP | S.IsIntCls C ∧ ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ IsUni u' ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ C = S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i}.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (r * (r + 1) * (S.vth + S.vD).toNat) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hvD
  obtain ⟨-, -, -, -, -, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hth : S.th = (S.ϖ : F) ^ S.vth.toNat := by
    unfold Frames.th Frames.vth; split_ifs <;> simp
  have hv0 : 0 ≤ S.vth := by unfold Frames.vth; split_ifs <;> simp
  obtain ⟨R, hR, hRu, hRs⟩ := exists_reps L (algebraMap F E S.th) (resQ S.ϖ ^ (2 * S.vth.toNat))
    (pow_ne_zero _ (by omega)) (by rw [hth]; exact hcard _) (r + 1)
  obtain ⟨s, hs⟩ := exists_section L (r + 1)
  set T := {C : Set S.FrP | S.IsIntCls C ∧ ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ IsUni u' ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ C = S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i} with hT
  rcases T.eq_empty_or_nonempty with h0 | ⟨C₀, hC₀⟩
  · rw [h0]; simp
  set Δ : E := ∏ l : Fin (r + 2), (if S.D l ≠ 0 then S.D l else 1) with hΔ
  have hden : ∀ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u → IsUni u' →
      (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) →
      S.IsIntCls (S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i) →
      Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD ∧
        ∀ i j, L.cj Δ * u i j ∈ L.O ∧ Δ * u' i j ∈ L.O := by
    intro u u' hu hu' hb hint
    refine GlobalTheory.T.leadingMinors_prod_denominator_unitriangular_factors L r k S u u' hu hu' hb (fun a b => ?_) Δ hΔ
    rw [pairing]
    exact hint.2 _ (GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).1 a b
  obtain ⟨hΔO, hΔu, hΔv⟩ : Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD := by
    obtain ⟨hi, u, u', hu, hu', hb, rfl⟩ := hC₀
    obtain ⟨a, b, c, -⟩ := hden u u' hu hu' hb hi
    exact ⟨a, b, c⟩
  have hcjO : L.cj Δ ∈ L.O := ((GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.1 Δ hΔO).1
  have c1 := GlobalTheory.HL.encard_uniCosets_le L S.ϖ S.ϖ_irr (L.cj Δ) hcjO (hΔu.map L.cj) (r + 1)
  have c2 := GlobalTheory.HL.encard_uniCosets_le L S.ϖ S.ϖ_irr Δ hΔO hΔu (r + 1)
  rw [L.cj_cj, mul_comm (L.cj Δ) Δ, hΔv] at c1
  rw [hΔv] at c2
  set S₁ := {C : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) | ∃ u, IsUni u ∧ (∀ i j, L.cj Δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}} with hS₁
  set S₂ := {C : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) | ∃ u, IsUni u ∧ (∀ i j, Δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}} with hS₂
  have hsub : T ⊆ (fun p => S.frameCls (fun j => ∑ i, s p.1 i j • S.f i)
      fun j => ∑ i, (s p.2.1 * p.2.2) i j • S.f' i) '' (S₁ ×ˢ S₂ ×ˢ R) := by
    rintro C ⟨hi, u, u', hu, hu', hb, rfl⟩
    obtain ⟨-, -, -, hd⟩ := hden u u' hu hu' hb hi
    obtain ⟨A, hA, hAI, eA⟩ := hs u
    obtain ⟨A', hA', hAI', eA'⟩ := hs u'
    obtain ⟨Ai, hAi, hAiI, -, e2⟩ := exists_inv L hA hAI
    obtain ⟨B₀, hB₀, hcong⟩ := hRs (A' * Ai) (uni_mul hA' hAi) (int_mul L hAI' hAiI)
    obtain ⟨Bi, hBi, hBiI, e3, e4⟩ := exists_inv L (hRu B₀ hB₀).1 (hRu B₀ hB₀).2
    refine ⟨(coset L u, coset L u', B₀), ⟨⟨u, hu, fun i j => (hd i j).1, rfl⟩,
      ⟨u', hu', fun i j => (hd i j).2, rfl⟩, hB₀⟩, ?_⟩
    refine (((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1
      (fun j => ∑ i, u i j • S.f i, fun j => ∑ i, u' i j • S.f' i) ?_).1).symm
    have hBA := uni_mul hBi hA'
    refine ⟨A, Bi * A', hAI, int_mul L hBiI hAI', fun i j h => ⟨hA.1 i j h, hBA.1 i j h⟩,
      fun i => ⟨hA.2 i, hBA.2 i⟩, ?_, fun j => ?_, fun j => ?_⟩
    · choose c hc ec using hcong
      have e5 : A' * Ai - B₀ = algebraMap F E S.th • Matrix.of c := by
        ext i j; simp [ec]
      have e6 : Bi * A' - A = algebraMap F E S.th • (Bi * Matrix.of c * A) := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← e5, Matrix.mul_sub, Matrix.sub_mul, e4,
          Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, e2, Matrix.mul_one]
      intro i j
      exact ⟨(Bi * Matrix.of c * A) i j, int_mul L (int_mul L hBiI hc) hAI i j,
        congrFun (congrFun e6 i) j⟩
    · dsimp only
      rw [← rmul_mul, ← eA]
    · dsimp only
      rw [← rmul_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B₀, e3, Matrix.one_mul, ← eA']
  have h1 : T.encard ≤ S₁.encard * (S₂.encard * R.encard) := by
    refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
    rw [Set.encard_prod, Set.encard_prod]
  have h2 : (T.encard : ℝ≥0∞) ≤ (S₁.encard : ℝ≥0∞) * ((S₂.encard : ℝ≥0∞) * (R.encard : ℝ≥0∞)) := by
    rw [← ENat.toENNReal_mul, ← ENat.toENNReal_mul]
    exact ENat.toENNReal_le.2 h1
  have h3 : (R.encard : ℝ≥0∞) ≤
      (resQ S.ϖ : ℝ≥0∞) ^ (2 * S.vth.toNat * ((r + 1) * (r + 1 - 1) / 2)) := by
    refine (ENat.toENNReal_le.2 hR).trans (le_of_eq ?_)
    rw [ENat.toENNReal_coe, ← pow_mul, Nat.cast_pow]
  refine h2.trans ((mul_le_mul' c1 (mul_le_mul' c2 h3)).trans (le_of_eq ?_))
  rw [← pow_add, ← pow_add, Frames.q, Int.toNat_add hv0 hvD]
  congr 1
  have h4 : (r + 1) * (r + 1 - 1) / 2 * 2 = r * (r + 1) := by
    rw [Nat.add_sub_cancel, mul_comm (r + 1) r]
    exact Nat.div_mul_cancel (Nat.even_mul_succ_self r).two_dvd
  rw [← h4]; ring
end GlobalTheory.IntClsCount
