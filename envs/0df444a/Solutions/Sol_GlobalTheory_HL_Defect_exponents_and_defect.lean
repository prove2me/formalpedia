-- Prove2me | solution 1 for GlobalTheory.HL.Defect.exponents_and_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:45.320471+00:00
-- url     : https://prove2.me/submissions/04c63c3f-e5b9-4e61-a085-dc7e34fda32e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Theorems.Thm_GlobalTheory_HL_Defect_defect
import Theorems.Thm_GlobalTheory_HL_Defect_spanTo_eq
import Theorems.Thm_GlobalTheory_HL_Defect_Mof_eq
import Theorems.Thm_GlobalTheory_HL_Defect_lead_translate
import Theorems.Thm_GlobalTheory_HL_Defect_det_gens
import Theorems.Thm_GlobalTheory_HL_Defect_det_mem
import Theorems.Thm_GlobalTheory_HL_Defect_vE_pow_mul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_matrix
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
import Theorems.Thm_GlobalTheory_T_hermitianDoubleCosetFrames_level_le_iff_congr_flagSteps
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_exists_norm
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.Defect
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 ≤ S.a ∧ 0 ≤ S.vD ∧ (∀ l, S.D l ∈ L.O) ∧ (S.q : ℝ) ^ S.a ≤ S.Hp ∧ 1 ≤ S.Hp ∧ (∃ i : ℕ, (i : ℤ) ≤ S.a ∧ S.be d Λ = S.q ^ i) ∧ (S.BBzero d Λ ↔ S.be d Λ = 1) ∧ (¬ S.BBzero d Λ → (S.q : ℝ) ≤ S.Hp) ∧ (∀ y ∈ S.sat Λ, algebraMap F E ((S.ϖ : F) ^ S.a) • y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ S.spanTo S.f j ⊔ S.spanTo S.f' j, y - y₁ ∈ S.M d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨hSD, hW, hM, -, hfr', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, hDu, hth0, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hv, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hn : (S.wit d Λ).1 ∈ S.N := hW.2.2.1
  have hn' : (S.wit d Λ).2 ∈ S.N' := hW.2.2.2.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hSD.2 y).2 hy x hx
  have hMe : S.M d Λ = Submodule.span L.O (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) := Mof_eq S _ _
  have hg : ∀ i, gens S (S.fr d Λ) (S.fr' d Λ) i ∈ Λ := fun i =>
    (hM (hMe ▸ Submodule.subset_span ⟨i, rfl⟩)).1
  have hf1 : ∀ b, S.fr d Λ b ∈ Λ := fun b => hg (Sum.inl b)
  have hf2 : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    ((hfr' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hD : ∀ l, S.D l ∈ L.O := fun l => by
    rw [← lead_translate S hn hn' l]
    exact det_mem _ fun i j => hint _ (hf2 _) _ (hf1 _)
  have hsp : ∀ j, S.spanTo (S.fr d Λ) j = S.spanTo S.f j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f S.T S.gram _ hn
    exact spanTo_eq S _ _ s hs h
  have hsp' : ∀ j, S.spanTo (S.fr' d Λ) j = S.spanTo S.f' j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hn'
    exact spanTo_eq S _ _ s hs h
  have hdet : (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i)
      (gens S (S.fr d Λ) (S.fr' d Λ) j)).det =
      algebraMap F E ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c) := by
    refine (det_gens S hn hn').trans ?_
    rw [hc]; simp only [map_mul, map_pow, map_neg, map_one]
  have hc' : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ≠ 0 := by
    simp [hc0, hth0]
  have hmem : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ∈ 𝒪[F] := by
    rw [← algebraMap_mem_iff L, ← hdet]
    exact det_mem _ fun i j => hint _ (hg i) _ (hg j)
  obtain ⟨u, hu⟩ := hvu _ hc'
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((hv _ hc').2 hmem)
  rw [hm, zpow_natCast] at hu
  have ha : S.a = m := by
    have e1 : c = S.th ^ (2 * (r + 1)) * ((S.ϖ : F) ^ m *
        ((((-1) ^ (r + 1) * u : (𝒪[F])ˣ) : 𝒪[F]) : F)) := by
      have e2 : ((((-1) ^ (r + 1) * u : (𝒪[F])ˣ) : 𝒪[F]) : F) = (-1) ^ (r + 1) * ((u : 𝒪[F]) : F) := by
        simp
      rw [e2, mul_left_comm ((S.ϖ : F) ^ m), ← hu, ← mul_assoc ((-1 : F) ^ _), ← mul_assoc ((-1 : F) ^ _),
        ← mul_pow, inv_pow]
      field_simp
      simp
    unfold Frames.a Frames.vth
    unfold Frames.th at e1
    rw [hc, e1]
    split_ifs
    · rw [← mul_assoc, ← pow_add, vE_pow_mul _ S.ϖ_irr]; push_cast; ring
    · rw [one_pow, one_mul, vE_pow_mul _ S.ϖ_irr]; ring
  have hvD : 0 ≤ S.vD := by
    refine Finset.sum_nonneg fun l _ => ?_
    split_ifs with h
    · obtain ⟨e, he⟩ := exists_norm L (hD l)
      rw [he]
      refine (hv _ fun h0 => ?_).2 e.2
      rw [h0, map_zero] at he
      apply h.2
      rw [← L.cj_cj (S.D l), (hDu l h.2).mul_right_eq_zero.1 he, map_zero]
    · exact le_rfl
  have hq : 2 ≤ S.q := (order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ S.q := by exact_mod_cast (by omega : 1 ≤ S.q)
  have hvth : 0 ≤ S.vth := by unfold Frames.vth; split_ifs <;> norm_num
  have hHp : (S.q : ℝ) ^ S.a ≤ S.Hp := zpow_le_zpow_right₀ hq1 (by omega)
  have hsat : ∀ y ∈ S.sat Λ, y ∈ S.spanTo (S.fr d Λ) (r + 1) ⊔ S.spanTo (S.fr' d Λ) (r + 1) :=
    fun y hy => by rw [hsp, hsp']; exact hy.2
  obtain ⟨hk, i, hi, hbe⟩ := defect L S.ϖ S.ϖ_irr S.Hm (gens S (S.fr d Λ) (S.fr' d Λ)) m u
    (hdet.trans (congrArg _ hu)) (S.sat Λ) (hMe ▸ hM)
    (fun y hy => by
      have h1 : ∀ b, S.fr d Λ b ∈ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) :=
        fun b => Submodule.subset_span ⟨Sum.inl b, rfl⟩
      refine (sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) :
        _ ≤ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ)))) (hsat y hy)
      · rintro _ ⟨b, -, rfl⟩
        exact h1 b
      · rintro _ ⟨b, -, rfl⟩
        have h2 : S.fr' d Λ b = S.fr d Λ b +
            algebraMap F E S.th • gens S (S.fr d Λ) (S.fr' d Λ) (Sum.inr b) := by
          simp only [gens, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ hth0, map_one, one_smul]
          abel
        rw [h2]
        exact Submodule.add_mem _ (h1 b)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)))
    (fun x hx y hy => hint x hx.1 y hy.1)
  rw [← hMe] at hk hbe
  have hbe' : S.be d Λ = S.q ^ i := hbe
  have hBB : S.BBzero d Λ ↔ S.be d Λ = 1 := by
    unfold Frames.BBzero Frames.be
    rw [AddSubgroup.relIndex_eq_one]
    exact ⟨fun h => by rw [h], fun h => le_antisymm hM h⟩
  have hlev : ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔
      ∃ y₁ ∈ S.spanTo S.f j ⊔ S.spanTo S.f' j, y - y₁ ∈ S.M d Λ := fun y hy j => by
    rw [← hsp, ← hsp']
    exact GlobalTheory.T.hermitianDoubleCosetFrames_level_le_iff_congr_flagSteps L r k S _ _ y (hsat y hy) j
  refine ⟨by omega, hvD, hD, hHp, le_trans (one_le_zpow₀ hq1 (by omega)) hHp,
    ⟨i, by omega, hbe'⟩, hBB, fun h => ?_, fun y hy => ?_, fun y hy => ?_, hlev⟩
  · have hi0 : i ≠ 0 := by
      rintro rfl
      exact h (hBB.2 (by simpa using hbe'))
    refine le_trans ?_ hHp
    simpa using zpow_le_zpow_right₀ hq1 (show (1 : ℤ) ≤ S.a by omega)
  · rw [ha, zpow_natCast]; exact hk y hy
  · rw [← Nat.le_zero, hlev y hy 0]
    simp [Frames.spanTo]
end GlobalTheory.HL.Defect
