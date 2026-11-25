-- Prove2me | solution 1 for GlobalTheory.FrameAct.stabiliser_acts_on_terms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:07.573561+00:00
-- url     : https://prove2.me/submissions/f1d837f4-3816-4c86-8ac6-ac9f2b8bdd6e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Theorems.Thm_GlobalTheory_FrameAct_mem_smul_iff
import Theorems.Thm_GlobalTheory_FrameAct_relIndex_smul
import Theorems.Thm_GlobalTheory_FrameAct_inTh_iff
import Theorems.Thm_GlobalTheory_FrameAct_mof_smul
import Theorems.Thm_GlobalTheory_FrameAct_frameCls_smul
import Theorems.Thm_GlobalTheory_FrameAct_lev_smul
import Theorems.Thm_GlobalTheory_FrameAct_spanTo_iff
import Theorems.Thm_P2M_GlobalTheory_FrameAct_spanTo_iff__721488b8eec6
import Theorems.Thm_GlobalTheory_FrameAct_sup_iff
import Theorems.Thm_GlobalTheory_FrameAct_isom
import Theorems.Thm_GlobalTheory_FrameAct_perp_iff
import Theorems.Thm_GlobalTheory_FrameAct_sat_smul
import Theorems.Thm_GlobalTheory_FrameAct_isTermW_smul
import Theorems.Thm_GlobalTheory_FrameAct_ihat_smul
import Theorems.Thm_GlobalTheory_FrameAct_forall_sat
import Theorems.Thm_GlobalTheory_FrameAct_exists_sat
import Theorems.Thm_GlobalTheory_FrameAct_nLev_smul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FramePsi_psi_unitary_character
import Theorems.Thm_GlobalTheory_T_frames_characters_agree_commonStabiliser
import Theorems.Thm_GlobalTheory_T_term_invariants_independent_of_witnesses
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
open GlobalTheory GlobalTheory.FrameAct
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FrameAct
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) ∧ S.om d (h • Λ) = S.om d Λ ∧ S.M d (h • Λ) = h • S.M d Λ ∧ S.sat (h • Λ) = h • S.sat Λ ∧ S.Fr d (h • Λ) = h • S.Fr d Λ ∧ S.be d (h • Λ) = S.be d Λ ∧ S.cardI d (h • Λ) = S.cardI d Λ ∧ (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) ∧ (S.TypeBe d (h • Λ) ↔ S.TypeBe d Λ) ∧ (∀ β J βJ, S.InFF β J βJ d (h • Λ) ↔ S.InFF β J βJ d Λ) ∧ ∀ J x x' u s, S.IsMove J d Λ x x' u s ↔ S.IsMove J d (h • Λ) (h x) (h x') (h u) s := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT h hh
  obtain ⟨⟨n, n'⟩, W⟩ := hT
  have W0 : S.IsTermW d Λ n n' := W
  have W2 := isTermW_smul S h hh d Λ n n' W0
  have hn : n ∈ S.N := W0.2.2.1
  have hn' : n' ∈ S.N' := W0.2.2.2.1
  have hN : h ∈ S.N := (Subgroup.mem_inf.mp hh).1
  have hN' : h ∈ S.N' := (Subgroup.mem_inf.mp hh).2
  obtain ⟨omA, MA, FrA, levA, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d Λ n n' W0
  obtain ⟨omB, MB, FrB, levB, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d (h • Λ) (h * n) (h * n') W2
  obtain ⟨pm, pm', pn, -⟩ := GlobalTheory.FramePsi.psi_unitary_character L r k S
  have hpp : S.psi h = S.psi' h := GlobalTheory.T.frames_characters_agree_commonStabiliser L r k S h hh
  have hM : S.M d (h • Λ) = h • S.M d Λ := by
    rw [MB, MA]
    exact mof_smul S h _ _
  have hsat := sat_smul S h hh Λ
  have hlev : ∀ y, S.levC d (h • Λ) (h y) = S.levC d Λ y := by
    intro y
    unfold Frames.levC
    rw [levB, levA]
    have e : algebraMap F E S.th • h y = h (algebraMap F E S.th • y) :=
      (LinearEquiv.map_smul h _ y).symm
    rw [e]
    exact lev_smul S h _ _ _
  have hom : S.om d (h • Λ) = S.om d Λ := by
    rw [omB, omA, pm h hN n hn, pm' h hN' n' hn', hpp]
    have hne : S.psi' h ≠ 0 := by
      intro e
      have h1 := (pn h).2
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have key : ∀ a b c : ℂ, a ≠ 0 → a * b * (a * c)⁻¹ = b * c⁻¹ := by
      intro a b c ha
      calc a * b * (a * c)⁻¹ = (a * a⁻¹) * (b * c⁻¹) := by ring
        _ = b * c⁻¹ := by rw [mul_inv_cancel₀ ha, one_mul]
    exact key _ _ _ hne
  have hFr : S.Fr d (h • Λ) = h • S.Fr d Λ := by
    rw [FrB, FrA]
    exact frameCls_smul S h _ _
  have hbe : S.be d (h • Λ) = S.be d Λ := by
    unfold Frames.be
    rw [hM, hsat]
    exact relIndex_smul S h _ _
  have hcard : S.cardI d (h • Λ) = S.cardI d Λ := by
    unfold Frames.cardI
    rw [hM, ihat_smul S h hh d Λ hM]
    exact relIndex_smul S h _ _
  have hBB : S.BBzero d (h • Λ) ↔ S.BBzero d Λ := by
    unfold Frames.BBzero
    rw [hM, hsat]
    exact (MulAction.injective h).eq_iff
  have hall : ∀ J, (∀ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y ≤ J) ↔
      ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J := by
    intro J
    exact (forall_sat S h hh Λ (fun y => S.levC d (h • Λ) y ≤ J)).trans (by simp only [hlev])
  have hex : ∀ J, (∃ y ∈ S.sat (h • Λ), S.levC d (h • Λ) y = J) ↔
      ∃ y ∈ S.sat Λ, S.levC d Λ y = J := by
    intro J
    exact (exists_sat S h hh Λ (fun y => S.levC d (h • Λ) y = J)).trans (by simp only [hlev])
  have hX : ∀ v, h v ∈ S.X ↔ v ∈ S.X := fun v => spanTo_iff S h hh r v
  have hX' : ∀ v, h v ∈ S.X' ↔ v ∈ S.X' := fun v => spanTo_iff' S h hh r v
  have e : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
  have third : (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', S.InTh (h • Λ) (x₁ + x₁') →
        S.InTh (h • Λ) (x₂ + x₂') → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) ↔
      (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', S.InTh Λ (x₁ + x₁') →
        S.InTh Λ (x₂ + x₂') → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) := by
    constructor
    · intro H x₁ h1 x₁' h1' x₂ h2 x₂' h2' t1 t2
      have t1' := (inTh_iff S h Λ (x₁ + x₁')).2 t1
      have t2' := (inTh_iff S h Λ (x₂ + x₂')).2 t2
      rw [map_add] at t1' t2'
      have h3 := H (h x₁) ((hX _).2 h1) (h x₁') ((hX' _).2 h1') (h x₂) ((hX _).2 h2)
        (h x₂') ((hX' _).2 h2') t1' t2'
      unfold Frames.h at h3 ⊢
      rwa [isom S h hh] at h3
    · intro H x₁ h1 x₁' h1' x₂ h2 x₂' h2' t1 t2
      have t1' : S.InTh (h • Λ) (h (h⁻¹ x₁ + h⁻¹ x₁')) := by
        rw [map_add, e, e]
        exact t1
      have t2' : S.InTh (h • Λ) (h (h⁻¹ x₂ + h⁻¹ x₂')) := by
        rw [map_add, e, e]
        exact t2
      have h3 := H (h⁻¹ x₁) ((hX _).1 (by rw [e]; exact h1)) (h⁻¹ x₁') ((hX' _).1 (by rw [e]; exact h1'))
        (h⁻¹ x₂) ((hX _).1 (by rw [e]; exact h2)) (h⁻¹ x₂') ((hX' _).1 (by rw [e]; exact h2'))
        ((inTh_iff S h Λ _).1 t1') ((inTh_iff S h Λ _).1 t2')
      unfold Frames.h at h3 ⊢
      rwa [← isom S h hh, e, e] at h3
  have hTB : S.TypeBe d (h • Λ) ↔ S.TypeBe d Λ := by
    unfold Frames.TypeBe
    exact and_congr (not_congr hBB) (and_congr (hall r) third)
  have hFF : ∀ β J βJ, S.InFF β J βJ d (h • Λ) ↔ S.InFF β J βJ d Λ := by
    intro β J βJ
    unfold Frames.InFF
    rw [hbe, nLev_smul S h hh d Λ hM hlev J]
    exact and_congr hTB (and_congr Iff.rfl (and_congr (hall J) (and_congr (hex J) Iff.rfl)))
  have hmove : ∀ J x x' u s, S.IsMove J d Λ x x' u s ↔
      S.IsMove J d (h • Λ) (h x) (h x') (h u) s := by
    intro J x x' u s
    have ha : h x + h x' = h (x + x') := (map_add h x x').symm
    have hl : S.lev (S.fr d (h • Λ)) (S.fr' d (h • Λ)) (h x + h x') =
        S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') := by
      rw [levB, levA, ha]
      exact lev_smul S h _ _ _
    have hin : S.InTh (h • Λ) (h x + h x') ↔ S.InTh Λ (x + x') := by
      rw [ha]
      exact inTh_iff S h Λ _
    have hu : h u ∈ h • Λ ↔ u ∈ Λ := mem_smul_iff S h Λ u
    have hp : h u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) ↔
        u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) :=
      perp_iff S h hh _ (sup_iff S h hh J) u
    have hs : S.h (h u) (h u) = S.h u u := isom S h hh u u
    unfold Frames.IsMove
    rw [spanTo_iff S h hh J x, spanTo_iff' S h hh J x', hin, hl, hu, hp, hs]
  exact ⟨⟨(h * n, h * n'), W2⟩, hom, hM, hsat, hFr, hbe, hcard, hBB, hTB, hFF, hmove⟩
end GlobalTheory.FrameAct
