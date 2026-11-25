-- Prove2me | solution 1 for GlobalTheory.HL.MoveFacts.move_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:57.314751+00:00
-- url     : https://prove2.me/submissions/66aee82a-34ae-4f0d-a820-bea9856b844c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMoveProperties
import Theorems.Thm_GlobalTheory_HL_MoveFacts_conj_form
import Theorems.Thm_GlobalTheory_HL_MoveFacts_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_MoveFacts_iso_spanTo
import Theorems.Thm_GlobalTheory_HL_MoveFacts_mem_span_frame
import Theorems.Thm_GlobalTheory_HL_MoveFacts_parts_of_mem_Mof
import Theorems.Thm_GlobalTheory_FrameBasic_frames_basic
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_T_term_exponents_nonneg_and_defect_group_bound
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveFacts
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveFacts
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hx, hx', hin, -, -, huperp, ⟨c, hcO, hs⟩, -⟩ := hM
  obtain ⟨y, hyΛ, hxy⟩ := id hin
  obtain ⟨⟨-, -, hint⟩, -⟩ := hF
  have hj : (j : ℕ) + 1 ≤ r := Nat.succ_le_of_lt j.2
  have hxX : x ∈ S.X := spanTo_mono S S.f hj hx
  have hx'X : x' ∈ S.X' := spanTo_mono S S.f' hj hx'
  have hH : IsHerm L S.Hm := S.herm.1
  have hxx : S.h x x = 0 := iso_spanTo S S.f _ S.gram x hxX
  have hx'x' : S.h x' x' = 0 := iso_spanTo S S.f' _ S.gram' x' hx'X
  have hperp : ∀ z ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1), hf L S.Hm u z = 0 := huperp
  have hux : S.h u x = 0 := hperp x (Submodule.mem_sup_left hx)
  have hux' : S.h u x' = 0 := hperp x' (Submodule.mem_sup_right hx')
  obtain ⟨c0, hc0, he⟩ := hint x hxX x' hx'X x hxX x' hx'X hin hin
  have he' : hf L S.Hm x x' = algebraMap F E S.th * c0 := he
  have hcross : S.h x' x = algebraMap F E S.th * L.cj c0 := by
    show hf L S.Hm x' x = _
    rw [conj_form hH x x', he', map_mul, AlgEquiv.commutes]
  obtain ⟨-, hW, -, hfrL, hfr'L, hli, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -⟩ := hW
  obtain ⟨-, -, -, -, -, hth, hthO, -⟩ := GlobalTheory.FrameBasic.frames_basic L r k S
  obtain ⟨-, -, -, -, -, -, -, -, hMa, -, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hthE : algebraMap F E S.th ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr hthO
  have hinv : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth, map_one]
  have hsum : x + x' ∈ S.ME :=
    add_mem (Submodule.mem_sup_left (spanTo_mono S S.f (by omega) hx))
      (Submodule.mem_sup_right (spanTo_mono S S.f' (by omega) hx'))
  have hyeq : y = algebraMap F E S.th⁻¹ • (x + x') := by
    rw [hxy, smul_smul, hinv, one_smul]
  have hyME : y ∈ S.ME := by rw [hyeq]; exact Submodule.smul_mem _ _ hsum
  have hysat : y ∈ S.sat Λ := Submodule.mem_inf.mpr ⟨hyΛ, hyME⟩
  obtain ⟨ξ, hξ, ξ', hξ', hsplit⟩ :=
    parts_of_mem_Mof S hth hthE (S.fr d Λ) (S.fr' d Λ) _ (hMa y hysat)
  set P := algebraMap F E ((S.ϖ : F) ^ S.a) with hP
  have hsplit' : P • x + P • x' = ξ + ξ' := by
    rw [← smul_add, hxy, smul_comm]; exact hsplit
  have hxfr : x ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    mem_span_frame S S.f (S.wit d Λ).1 hn j x hx
  have hx'fr : x' ∈ Submodule.span E (Set.range (S.fr' d Λ)) :=
    mem_span_frame S S.f' (S.wit d Λ).2 hn' j x' hx'
  have hdis := (linearIndependent_sum.mp hli).2.2
  have hw1 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hxfr)
      (Submodule.span_le_restrictScalars L.O E _ hξ)
  have hw2 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr' d Λ)) := by
    have e : P • x - ξ = ξ' - P • x' := by
      rw [sub_eq_sub_iff_add_eq_add, hsplit', add_comm]
    rw [e]
    exact Submodule.sub_mem _ (Submodule.span_le_restrictScalars L.O E _ hξ')
      (Submodule.smul_mem _ _ hx'fr)
  have hPx : P • x = ξ := sub_eq_zero.mp ((Submodule.disjoint_def.mp hdis) _ hw1 hw2)
  have hPx' : P • x' = ξ' := by rw [hPx] at hsplit'; exact add_left_cancel hsplit'
  have hfrΛ : ∀ b, S.fr d Λ b ∈ Λ := fun b =>
    ((hfrL (r + 1) le_rfl (S.fr d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hfr'Λ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    ((hfr'L (r + 1) le_rfl (S.fr' d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hξΛ : ξ ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfrΛ b) hξ
  have hξ'Λ : ξ' ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfr'Λ b) hξ'
  have key : ∀ z, P • z ∈ Λ → s • z ∈ Λ ∧ L.cj s • z ∈ Λ := by
    intro z hz
    have hc' : L.cj c ∈ L.O := GlobalTheory.UnramOrder.cj_mem L hcO
    have h1 : s • z = (⟨c, hcO⟩ : L.O) • (P • z) := by
      rw [hs]; show (P * c) • z = c • (P • z); rw [smul_smul, mul_comm c P]
    have h2 : L.cj s • z = (⟨L.cj c, hc'⟩ : L.O) • (P • z) := by
      rw [hs, map_mul, AlgEquiv.commutes]; show (P * L.cj c) • z = L.cj c • (P • z)
      rw [smul_smul, mul_comm (L.cj c) P]
    exact ⟨h1 ▸ Λ.smul_mem _ hz, h2 ▸ Λ.smul_mem _ hz⟩
  have kx := key x (hPx ▸ hξΛ)
  have kx' := key x' (hPx' ▸ hξ'Λ)
  exact ⟨kx.1, kx.2, kx'.1, kx'.2, ⟨L.cj c0, GlobalTheory.UnramOrder.cj_mem L hc0, hcross⟩, hxx, hx'x',
    hux, hux', hxX, hx'X⟩
end GlobalTheory.HL.MoveFacts
