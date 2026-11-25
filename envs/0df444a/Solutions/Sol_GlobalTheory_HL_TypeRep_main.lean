-- Prove2me | solution 1 for GlobalTheory.HL.TypeRep.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:35.372003+00:00
-- url     : https://prove2.me/submissions/3532872c-1284-4648-ba60-97c2f171493f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentatives
import Theorems.Thm_GlobalTheory_HL_TypeRep_h_add_left
import Theorems.Thm_GlobalTheory_HL_TypeRep_h_add_right
import Theorems.Thm_GlobalTheory_HL_TypeRep_h_smul_left
import Theorems.Thm_GlobalTheory_HL_TypeRep_h_smul_right
import Theorems.Thm_GlobalTheory_HL_TypeRep_iso_of
import Theorems.Thm_GlobalTheory_HL_TypeRep_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TypeRep_disj
import Theorems.Thm_GlobalTheory_HL_TypeRep_frame_split
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_LevelRep_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_T_termLevel_zero_and_bounded_representatives

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.TypeRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
private theorem algebraMap_mem_O_of_mem_valuationInteger (L : LocE F E) {x : F} (hx : x ∈ 𝒪[F]) : algebraMap F E x ∈ L.O := by
  rw [L.O_def]
  have := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨x, hx⟩)
  convert this using 1
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
  rfl
end GlobalTheory.HL.TypeRep
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TypeRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.TypeRep
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ¬ S.BBzero d Λ → ∀ B₀ : Set S.V, (∀ y ∈ B₀, y ∈ Λ ∧ y ∈ S.X ⊔ S.X') → (∀ y ∈ S.sat Λ, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ) → (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', algebraMap F E S.th⁻¹ • (x₁ + x₁') ∈ B₀ → algebraMap F E S.th⁻¹ • (x₂ + x₂') ∈ B₀ → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) → S.TypeBe d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB B₀ hB₀ hrep hpair
  obtain ⟨hli, -, -, -, -, h0, hthF, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hSD, -, hMsat, hfr, hfr', -, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hlev := (GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ hT).2.1
  have hthO : algebraMap F E S.th ∈ L.O := algebraMap_mem_O_of_mem_valuationInteger L hthF
  have hcj : L.cj (algebraMap F E S.th) = algebraMap F E S.th := L.cj.commutes S.th
  have hinv : ∀ v : S.V, algebraMap F E S.th⁻¹ • algebraMap F E S.th • v = v := by
    intro v
    rw [smul_smul, ← map_mul, inv_mul_cancel₀ h0, map_one, one_smul]
  have hint : ∀ v ∈ Λ, ∀ w ∈ Λ, S.h v w ∈ L.O := fun v hv w hw => (hSD.2 w).2 hw v hv
  have hXX : ∀ v ∈ S.X, ∀ w ∈ S.X, S.h v w = 0 := fun v hv w hw =>
    iso_of S S.f (-algebraMap F E S.T) S.gram hv hw
  have hXX' : ∀ v ∈ S.X', ∀ w ∈ S.X', S.h v w = 0 := fun v hv w hw =>
    iso_of S S.f' (-algebraMap F E S.T') S.gram' hv hw
  have hXME : S.X ≤ S.ME := (spanTo_mono S S.f).trans le_sup_left
  have hX'ME : S.X' ≤ S.ME := (spanTo_mono S S.f').trans le_sup_right
  have hsatΛ : S.sat Λ ≤ Λ := inf_le_left
  have hg : ∀ b, S.fr d Λ b ∈ S.spanTo S.f (r + 1) := fun b =>
    ((hfr (r + 1) le_rfl _).2 (Submodule.subset_span (Set.mem_image_of_mem _ b.2))).2
  have hg' : ∀ b, S.fr' d Λ b ∈ Λ ∧ S.fr' d Λ b ∈ S.spanTo S.f' (r + 1) := fun b =>
    (hfr' (r + 1) le_rfl _).2 (Submodule.subset_span (Set.mem_image_of_mem _ b.2))
  have hdisj := Submodule.disjoint_def.1 (disj S hli)
  have key : ∀ x ∈ S.X, ∀ x' ∈ S.X', S.InTh Λ (x + x') → ∃ u ∈ S.X, ∃ u' ∈ S.X',
      u + u' ∈ B₀ ∧ u + u' ∈ Λ ∧ x' - algebraMap F E S.th • u' ∈ Λ ∧
      ∃ m ∈ Λ, (x - algebraMap F E S.th • u) + (x' - algebraMap F E S.th • u') =
        algebraMap F E S.th • m := by
    rintro x hx x' hx' ⟨y, hyΛ, hxy⟩
    have hyME : y ∈ S.ME := by
      rw [← hinv y, ← hxy]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hXME hx) (hX'ME hx'))
    have hysat : y ∈ S.sat Λ := Submodule.mem_inf.2 ⟨hyΛ, hyME⟩
    obtain ⟨y₀, hy₀, hmM⟩ := hrep y hysat
    obtain ⟨hy₀Λ, hy₀X⟩ := hB₀ y₀ hy₀
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy₀X
    have hmΛ : y - (u + u') ∈ Λ := hsatΛ (hMsat hmM)
    obtain ⟨b, hb, b', hb', hb'Λ, hbb⟩ := frame_split S Λ _ _ h0 hg hg' hmM
    have hsum : (x - algebraMap F E S.th • u) + (x' - algebraMap F E S.th • u') =
        algebraMap F E S.th • (y - (u + u')) := by
      rw [smul_sub, ← hxy, smul_add]
      abel
    have hdiff : b' - (x' - algebraMap F E S.th • u') = 0 := by
      apply hdisj
      · have he : b' - (x' - algebraMap F E S.th • u') = (x - algebraMap F E S.th • u) - b := by
          have h2 := hsum.trans hbb
          linear_combination -h2
        rw [he]
        exact Submodule.sub_mem _
          (spanTo_mono S S.f (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hu))) hb
      · exact Submodule.sub_mem _ hb'
          (spanTo_mono S S.f' (Submodule.sub_mem _ hx' (Submodule.smul_mem _ _ hu')))
    have ha' : x' - algebraMap F E S.th • u' = b' := (sub_eq_zero.1 hdiff).symm
    exact ⟨u, hu, u', hu', hy₀, hy₀Λ, by rw [ha']; exact hb'Λ, y - (u + u'), hmΛ, hsum⟩
  refine ⟨hB, ?_, ?_⟩
  · intro y hy
    obtain ⟨y₀, hy₀, hm⟩ := hrep y hy
    exact (hlev y hy r).2 ⟨y₀, (hB₀ y₀ hy₀).2, hm⟩
  · intro x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' h1 h2
    obtain ⟨u₁, hu₁, u₁', hu₁', hB1, hy1, ha1', m₁, hm₁, he1⟩ := key x₁ hx₁ x₁' hx₁' h1
    obtain ⟨u₂, hu₂, u₂', hu₂', hB2, hy2, ha2', m₂, hm₂, he2⟩ := key x₂ hx₂ x₂' hx₂' h2
    generalize ht : algebraMap F E S.th = t at *
    set a₁ := x₁ - t • u₁ with ha₁
    set a₁' := x₁' - t • u₁' with ha₁d
    set a₂' := x₂' - t • u₂' with ha₂d
    have ha₁X : a₁ ∈ S.X := Submodule.sub_mem _ hx₁ (Submodule.smul_mem _ _ hu₁)
    have ha₁'X : a₁' ∈ S.X' := Submodule.sub_mem _ hx₁' (Submodule.smul_mem _ _ hu₁')
    have ha₂'X : a₂' ∈ S.X' := Submodule.sub_mem _ hx₂' (Submodule.smul_mem _ _ hu₂')
    have hB1' : algebraMap F E S.th⁻¹ • (t • u₁ + t • u₁') ∈ B₀ := by rw [← smul_add, hinv]; exact hB1
    have hB2' : algebraMap F E S.th⁻¹ • (t • u₂ + t • u₂') ∈ B₀ := by rw [← smul_add, hinv]; exact hB2
    obtain ⟨c₀, hc₀, hc₀e⟩ := hpair (t • u₁) (Submodule.smul_mem _ _ hu₁) (t • u₁')
      (Submodule.smul_mem _ _ hu₁') (t • u₂) (Submodule.smul_mem _ _ hu₂) (t • u₂')
      (Submodule.smul_mem _ _ hu₂') hB1' hB2'
    have ex₁ : x₁ = t • u₁ + a₁ := by rw [ha₁]; abel
    have ex₂' : x₂' = t • u₂' + a₂' := by rw [ha₂d]; abel
    have eA : S.h x₁ x₂' = S.h (t • u₁) (t • u₂') + S.h (t • u₁) a₂' + S.h a₁ (t • u₂') +
        S.h a₁ a₂' := by
      rw [ex₁, ex₂', h_add_left, h_add_right, h_add_right]
      ring
    have eB : S.h (t • u₁) a₂' = t * S.h u₁ a₂' := h_smul_left S _ _ _
    have eC : S.h (u₁ + u₁') a₂' = S.h u₁ a₂' + S.h u₁' a₂' := h_add_left S _ _ _
    have eD : S.h u₁' a₂' = 0 := hXX' _ hu₁' _ ha₂'X
    have eE : S.h a₁ (t • u₂') = t * S.h a₁ u₂' := by rw [h_smul_right, hcj]
    have eF : S.h a₁ (u₂ + u₂') = S.h a₁ u₂ + S.h a₁ u₂' := h_add_right S _ _ _
    have eG : S.h a₁ u₂ = 0 := hXX _ ha₁X _ hu₂
    have eH : S.h (a₁ + a₁') a₂' = S.h a₁ a₂' + S.h a₁' a₂' := h_add_left S _ _ _
    have eI : S.h (t • m₁) a₂' = t * S.h m₁ a₂' := h_smul_left S _ _ _
    have eJ : S.h a₁' a₂' = 0 := hXX' _ ha₁'X _ ha₂'X
    have eK : S.h (t • m₁) (u₂ + u₂') = t * S.h m₁ (u₂ + u₂') := h_smul_left S _ _ _
    have eL : S.h (a₁ + a₁') (u₂ + u₂') = S.h a₁ (u₂ + u₂') + S.h a₁' (u₂ + u₂') :=
      h_add_left S _ _ _
    rw [he1] at eH eL
    have hO1 : S.h (u₁ + u₁') a₂' ∈ L.O := hint _ hy1 _ ha2'
    have hO2 : S.h m₁ (u₂ + u₂') ∈ L.O := hint _ hm₁ _ hy2
    have hO3 : S.h a₁' (u₂ + u₂') ∈ L.O := hint _ ha1' _ hy2
    have hO4 : S.h m₁ a₂' ∈ L.O := hint _ hm₁ _ ha2'
    refine ⟨c₀ + S.h (u₁ + u₁') a₂' + (t * S.h m₁ (u₂ + u₂') - S.h a₁' (u₂ + u₂')) + S.h m₁ a₂',
      ?_, ?_⟩
    · exact L.O.add_mem (L.O.add_mem (L.O.add_mem hc₀ hO1)
        (L.O.sub_mem (L.O.mul_mem hthO hO2) hO3)) hO4
    · rw [eA, hc₀e]
      linear_combination eB - t * eC - t * eD + eE - t * eF - t * eG - eH + eI - eJ + t * eK - t * eL
end GlobalTheory.HL.TypeRep
