-- Prove2me | solution 1 for GlobalTheory.HL.SmallImage.small_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:15.467796+00:00
-- url     : https://prove2.me/submissions/7e03078a-0f8f-4381-a89d-e27ef5ce4a94

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GluingImageCardPowLeDefectGroupCard
import Theorems.Thm_GlobalTheory_HL_SmallImage_resQ_pos
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FiniteModuleOrder_card_eq_pow_and_index_ge
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_HL_Defect_exponents_and_defect
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_le_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_LevelRep_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_HL_TypeRep_main
import Theorems.Thm_GlobalTheory_HL_TypeRep_spanTo_mono
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
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
namespace GlobalTheory.HL.SmallImage
section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
end
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma hf_sub_left_flag_measures {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H (x - x') y = _root_.GlobalTheory.HL.hf L H x y - _root_.GlobalTheory.HL.hf L H x' y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma hf_sub_right_flag_measures {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H x (y - y') = _root_.GlobalTheory.HL.hf L H x y - _root_.GlobalTheory.HL.hf L H x y' := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma hf_add_left_flag_measures'' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H (x + x') y = _root_.GlobalTheory.HL.hf L H x y + _root_.GlobalTheory.HL.hf L H x' y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma hf_algebraMap_smul_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : F) :
    _root_.GlobalTheory.HL.hf L H x (algebraMap F E c • y) = algebraMap F E c * _root_.GlobalTheory.HL.hf L H x y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.HL.SmallImage
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SmallImage
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SmallImage
namespace _root_.GlobalTheory.HL.SmallImage
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∃ i : ℕ, S.cardI d Λ = S.q ^ i) ∧ S.cardI d Λ ≤ S.be d Λ ∧ (¬ S.BBzero d Λ → ¬ S.TypeBe d Λ → S.q * S.cardI d Λ ≤ S.be d Λ) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have hbasic := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hMsat : S.M d Λ ≤ S.sat Λ := hbasic.2.2.1
  have hth : S.th ≠ 0 := by
    unfold _root_.GlobalTheory.HL.Frames.th
    split_ifs
    · exact_mod_cast S.ϖ_irr.ne_zero
    · exact one_ne_zero
  have hX : S.X ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.X _root_.GlobalTheory.HL.Frames.ME
    exact (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f (Nat.le_succ r)).trans le_sup_left
  have hX' : S.X' ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.X' _root_.GlobalTheory.HL.Frames.ME
    exact (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f' (Nat.le_succ r)).trans le_sup_right
  have hIsat : S.Ihat d Λ ≤ S.sat Λ := by
    unfold _root_.GlobalTheory.HL.Frames.Ihat
    refine sup_le hMsat (Submodule.span_le.mpr ?_)
    rintro y ⟨w, hw, la, hla, la', hla', h1, h2, ⟨y1, hy1, hy1e⟩, h4⟩
    have hy1' : (algebraMap F E) S.th⁻¹ • (la' - la) = y1 := by
      rw [hy1e, smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
    have hME : y1 ∈ S.ME := by
      rw [← hy1']
      apply Submodule.smul_mem
      exact Submodule.sub_mem _ (hX' hla') (hX hla)
    have hy1sat : y1 ∈ S.sat Λ := by
      unfold _root_.GlobalTheory.HL.Frames.sat
      exact Submodule.mem_inf.mpr ⟨hy1, (Submodule.restrictScalars_mem _ _ _).mpr hME⟩
    have hsum : y = (y - (algebraMap F E) S.th⁻¹ • (la' - la)) + y1 := by
      rw [hy1']; abel
    rw [SetLike.mem_coe, hsum]
    exact Submodule.add_mem _ (hMsat h4) hy1sat
  have hMI : S.M d Λ ≤ S.Ihat d Λ := by
    unfold _root_.GlobalTheory.HL.Frames.Ihat; exact le_sup_left
  have hq : 0 < S.q :=
    _root_.GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr
  obtain ⟨j, -, hbe⟩ := (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.1
  have hprod := AddSubgroup.relIndex_mul_relIndex (S.M d Λ).toAddSubgroup (S.Ihat d Λ).toAddSubgroup
    (S.sat Λ).toAddSubgroup (fun x hx => hMI hx) (fun x hx => hIsat hx)
  unfold _root_.GlobalTheory.HL.Frames.cardI _root_.GlobalTheory.HL.Frames.be
    at *
  have hbe0 : (S.M d Λ).toAddSubgroup.relIndex (S.sat Λ).toAddSubgroup ≠ 0 := by
    rw [hbe]; positivity
  rw [← hprod] at hbe0 ⊢
  have hI0 := left_ne_zero_of_mul hbe0
  have hJ0 := right_ne_zero_of_mul hbe0
  refine ⟨?_, ?_, ?_⟩
  · have hfin : Finite (↥(S.Ihat d Λ) ⧸ (S.M d Λ).comap (S.Ihat d Λ).subtype) :=
      Nat.finite_of_card_ne_zero hI0
    obtain ⟨i, hi⟩ := (_root_.GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ
      S.ϖ_irr (↥(S.Ihat d Λ) ⧸ (S.M d Λ).comap (S.Ihat d Λ).subtype)).1
    exact ⟨i, hi⟩
  · exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hJ0)
  · intro hB hTB
    have hne : S.Ihat d Λ ≠ S.sat Λ := by
      intro heq
      apply hTB
      have hcancel : ∀ v : S.V,
          algebraMap F E S.th • (algebraMap F E S.th⁻¹ • v) = v := by
        intro v; rw [smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul]
      have hcancel' : ∀ v : S.V,
          algebraMap F E S.th⁻¹ • (algebraMap F E S.th • v) = v := by
        intro v; rw [smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
      refine _root_.GlobalTheory.HL.TypeRep.main L r k S d Λ hT hB
        (_root_.GlobalTheory.HL.SmallImage.reps S Λ) ?_ ?_ ?_
      · rintro y ⟨hyΛ, w, hw, la, hla, la', hla', h1, h2⟩
        refine ⟨hyΛ, ?_⟩
        rw [← hcancel' y, ← h2]
        exact Submodule.smul_mem _ _
          (Submodule.sub_mem _ (Submodule.mem_sup_right hla') (Submodule.mem_sup_left hla))
      · intro y hy
        rw [← heq] at hy
        have hle : S.Ihat d Λ ≤ S.M d Λ ⊔ _root_.GlobalTheory.HL.SmallImage.reps S Λ := by
          unfold _root_.GlobalTheory.HL.Frames.Ihat
          refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
          rintro z ⟨w, hw, la, hla, la', hla', h1, h2, ⟨y1, hy1, hy1e⟩, h4⟩
          have hy1' : (algebraMap F E) S.th⁻¹ • (la' - la) = y1 := by
            rw [hy1e, hcancel']
          have hrep : y1 ∈ _root_.GlobalTheory.HL.SmallImage.reps S Λ :=
            ⟨hy1, w, hw.1, la, hla, la', hla', h1, hy1e⟩
          have hsum : z = (z - (algebraMap F E) S.th⁻¹ • (la' - la)) + y1 := by
            rw [hy1']; abel
          rw [SetLike.mem_coe, hsum]
          exact Submodule.add_mem _ (Submodule.mem_sup_left h4) (Submodule.mem_sup_right hrep)
        obtain ⟨m, hm, y₀, hy₀, hmy⟩ := Submodule.mem_sup.mp (hle hy)
        refine ⟨y₀, hy₀, ?_⟩
        rw [← hmy, add_sub_cancel_right]
        exact hm
      · intro x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' hy₁ hy₂
        obtain ⟨hΛ1, w₁, hw₁, la₁, hla₁, la₁', hla₁', hwl₁, he₁⟩ := hy₁
        obtain ⟨hΛ2, w₂, hw₂, la₂, hla₂, la₂', hla₂', hwl₂, he₂⟩ := hy₂
        rw [hcancel] at he₁ he₂
        have isoX : ∀ a ∈ S.X, ∀ b ∈ S.X,
            _root_.GlobalTheory.HL.hf L S.Hm a b = 0 := fun a ha b hb =>
          _root_.GlobalTheory.HL.FrameOnto.spanTo_le_perp S S.f _ S.gram ha b hb
        have isoX' : ∀ a ∈ S.X', ∀ b ∈ S.X',
            _root_.GlobalTheory.HL.hf L S.Hm a b = 0 := fun a ha b hb =>
          _root_.GlobalTheory.HL.FrameOnto.spanTo_le_perp S S.f' _ S.gram' ha b hb
        have hperp : ∀ w ∈ S.W0, ∀ m ∈ S.ME,
            _root_.GlobalTheory.HL.hf L S.Hm w m = 0 := fun w hw m hm => hw m hm
        have hz₁ : x₁ + la₁ = la₁' - x₁' := by
          rw [sub_eq_iff_eq_add] at he₁; rw [he₁]; abel
        have hz₂ : x₂ + la₂ = la₂' - x₂' := by
          rw [sub_eq_iff_eq_add] at he₂; rw [he₂]; abel
        have hz₁X' : x₁ + la₁ ∈ S.X' := by
          rw [hz₁]; exact Submodule.sub_mem _ hla₁' hx₁'
        have hz₂X : x₂ + la₂ ∈ S.X := Submodule.add_mem _ hx₂ hla₂
        have hz₂X' : x₂ + la₂ ∈ S.X' := by
          rw [hz₂]; exact Submodule.sub_mem _ hla₂' hx₂'
        have e1 : x₁ = (x₁ + la₁) - la₁ := by abel
        have e2 : x₂' = la₂' - (x₂ + la₂) := by rw [hz₂]; abel
        have hmain : _root_.GlobalTheory.HL.hf L S.Hm x₁ x₂'
            = -_root_.GlobalTheory.HL.hf L S.Hm la₁ la₂' := by
          rw [e1, e2, hf_sub_left_flag_measures, hf_sub_right_flag_measures, hf_sub_right_flag_measures, isoX' _ hz₁X' _ hla₂',
            isoX' _ hz₁X' _ hz₂X', isoX _ hla₁ _ hz₂X]
          ring
        have hkey : _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁) (la₂' - la₂)
            = _root_.GlobalTheory.HL.hf L S.Hm la₁ la₂' := by
          rw [hf_add_left_flag_measures'', hf_sub_right_flag_measures, hf_sub_right_flag_measures, hperp w₁ hw₁ la₂' (hX' hla₂'),
            hperp w₁ hw₁ la₂ (hX hla₂), isoX la₁ hla₁ la₂ hla₂]
          ring
        have hsm : _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁) (la₂' - la₂)
            = algebraMap F E S.th * _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁)
              (algebraMap F E S.th⁻¹ • (x₂ + x₂')) := by
          rw [← hf_algebraMap_smul_right, hcancel, he₂]
        have hdual := hbasic.1
        unfold _root_.GlobalTheory.HL.IsSD at hdual
        refine ⟨-_root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁)
          (algebraMap F E S.th⁻¹ • (x₂ + x₂')), ?_, ?_⟩
        · exact L.O.neg_mem ((hdual.2 _).mpr hΛ2 _ hwl₁)
        · show _root_.GlobalTheory.HL.hf L S.Hm x₁ x₂' = _
          rw [hmain, ← hkey, hsm]
          ring
    have hfin : Finite (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype) :=
      Nat.finite_of_card_ne_zero hJ0
    have hbot : (⊥ : Submodule L.O (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)) ≠ ⊤ := by
      intro hbt
      apply hne
      refine le_antisymm hIsat (fun x hx => ?_)
      have hmem : Submodule.Quotient.mk (p := (S.Ihat d Λ).comap (S.sat Λ).subtype) ⟨x, hx⟩ ∈
          (⊥ : Submodule L.O (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)) := by
        rw [hbt]; trivial
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
      exact hmem
    have hle := (_root_.GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ
      S.ϖ_irr (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)).2 ⊥ hbot
    rw [Nat.card_unique, mul_one] at hle
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hle
end _root_.GlobalTheory.HL.SmallImage
end GlobalTheory.HL.SmallImage
