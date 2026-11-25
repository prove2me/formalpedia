-- Prove2me | solution 1 for GlobalTheory.MoveFine.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:06.820751+00:00
-- url     : https://prove2.me/submissions/40415cfd-ddbf-4e4e-82d5-169fdfce143c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_mem_scl
import Theorems.Thm_GlobalTheory_MoveFine_finite_image_mk
import Theorems.Thm_GlobalTheory_MoveFine_iso_span
import Theorems.Thm_GlobalTheory_MoveFine_relIndex_inf_scl
import Theorems.Thm_GlobalTheory_MoveFine_smul_memO
import Theorems.Thm_GlobalTheory_MoveFine_algO
import Theorems.Thm_GlobalTheory_MoveFine_bound
import Theorems.Thm_GlobalTheory_MoveFine_noLeak_add
import Theorems.Thm_GlobalTheory_MoveFine_half_int
import Theorems.Thm_GlobalTheory_MoveFine_scl_index
import Theorems.Thm_GlobalTheory_MoveFine_mem_intP
import Theorems.Thm_GlobalTheory_MoveFine_intP_fg
import Theorems.Thm_GlobalTheory_MoveFine_mem_refA
import Theorems.Thm_GlobalTheory_MoveFine_Mv_lin
import Theorems.Thm_GlobalTheory_MoveFine_sOf_diff
import Theorems.Thm_GlobalTheory_MoveFine_p_unit
import Theorems.Thm_GlobalTheory_MoveFine_inTh_pow
import Theorems.Thm_GlobalTheory_MoveFine_Mv_add
import Theorems.Thm_GlobalTheory_MoveFine_chi_add
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_T_eichlerLattice_locally_constant_data
import Theorems.Thm_GlobalTheory_T_hermitian_double_coset_term_basic_facts
import Theorems.Thm_GlobalTheory_T_term_exponents_nonneg_and_defect_group_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
namespace GlobalTheory.MoveFine
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∃ B : AddSubgroup S.MW, Fine (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) B ∧ ∀ w, S.Mv (j + 1) d Λ w → ∀ b ∈ B, S.moved Λ (w + b).1.1 (w + b).2.1 (S.sOf (w + b)) = S.moved Λ w.1.1 w.2.1 (S.sOf w) ∧ S.chiM j d Λ (w + b).1 (w + b).2.1 = S.chiM j d Λ w.1 w.2.1 ∧ (S.NoLeak Λ (w + b).2.1 ↔ S.NoLeak Λ w.2.1) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT _
  have hΛ := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1
  obtain ⟨A, hA0⟩ := Int.eq_ofNat_of_zero_le (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).1
  have hA : algebraMap F E ((S.ϖ : F) ^ S.a) = algebraMap F E S.ϖ ^ A := by rw [hA0, zpow_natCast, map_pow]
  obtain ⟨v, hv⟩ := half_int S
  obtain ⟨n, hn⟩ := GlobalTheory.T.eichlerLattice_locally_constant_data L r k S Λ hΛ A
  have hJ0 : (j : ℕ) + 1 ≤ r := j.2
  have hJ : (j : ℕ) + 1 ≤ r + 1 := by omega
  have hp := fun n => L.O.pow_mem (algO S S.ϖ) n
  have hi : ∀ x ∈ Λ, ∀ y ∈ Λ, S.h x y ∈ L.O := fun x hx y hy => (hΛ.2 y).2 hy x hx
  let B := lin S (j + 1) ⊓ scl (intP S Λ).toAddSubgroup (algebraMap F E S.ϖ ^ (n + A + 1 + v))
  have hB : ∀ b ∈ B, ∃ y ∈ intP S Λ, b = algebraMap F E S.ϖ ^ (n + A + 1 + v) • y ∧ b ∈ lin S (j + 1) :=
    fun b hb => let ⟨y, hy, e⟩ := mem_scl.1 hb.2; ⟨y, hy, e, hb.1⟩
  have hadd : ∀ w, S.Mv (j + 1) d Λ w → ∀ b ∈ B, S.Mv (j + 1) d Λ (w + b) := fun w hw b hb => by
    obtain ⟨y, hy, rfl, hl⟩ := hB b hb
    exact Mv_add S hJ hT A hA n v hv w y hw hy hl
  have hidx : ∀ G ≤ lin S (j + 1), (∀ w ∈ G, algebraMap F E S.ϖ ^ (A + v) • w ∈ intP S Λ) → B.relIndex G ≠ 0 :=
    fun G hG hGP => relIndex_inf_scl _ _ _ _ (p_unit S (A + v))
      (by rw [← pow_add]; exact scl_index S _ (intP_fg S hΛ.1.1) _) G hG hGP
  have hbd : ∀ w ∈ lin S (j + 1), S.InTh Λ (w.1.1 + w.1.2) → w.2.1 ∈ Λ → algebraMap F E S.ϖ ^ v * w.2.2 ∈ L.O →
      algebraMap F E S.ϖ ^ (A + v) • w ∈ intP S Λ := fun w hw h1 h2 h3 => by
    obtain ⟨b1, b2⟩ := bound S d Λ hT _ hJ _ _ hw.1.1 hw.1.2 h1
    rw [hA] at b1 b2
    refine (mem_intP S).2 ⟨⟨?_, ?_⟩, smul_memO S (hp _) h2, ?_⟩
    · simpa only [Prod.smul_fst, ← mul_smul, ← pow_add, add_comm] using smul_memO S (hp v) b1
    · simpa only [Prod.smul_fst, Prod.smul_snd, ← mul_smul, ← pow_add, add_comm] using smul_memO S (hp v) b2
    · simpa only [Prod.smul_snd, pow_add, smul_eq_mul, mul_assoc] using L.O.mul_mem (hp A) h3
  refine ⟨B, ⟨fun b hb => ?_, hidx _ (fun w hw => ((mem_refA S).1 hw).1) fun w hw => ?_, fun w b hb => ?_, ?_⟩,
    fun w hw b hb => ?_⟩
  · obtain ⟨y, hy, rfl, hl⟩ := hB b hb
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (mem_intP S).1 hy
    refine (mem_refA S).2 ⟨hl, ?_, smul_memO S (hp _) h3, algebraMap F E S.ϖ ^ (n + 1 + v) * y.2.2,
      L.O.mul_mem (hp _) h4, ?_⟩
    · have := inTh_pow S (n + A + v) (Λ.add_mem h1 h2)
      rwa [smul_add, show n + A + v + 1 = n + A + 1 + v by ring] at this
    · rw [hA]; simp only [Prod.smul_snd, smul_eq_mul]; ring
  · obtain ⟨h1, h2, h3, c, hc, e⟩ := (mem_refA S).1 hw
    exact hbd w h1 h2 h3 (by rw [e, hA]; exact L.O.mul_mem (hp _) (L.O.mul_mem (hp _) hc))
  · have : S.Mv (j + 1) d Λ (w + b) ↔ S.Mv (j + 1) d Λ w :=
      ⟨fun h => by simpa using hadd _ h _ (B.neg_mem hb), fun h => hadd _ h _ hb⟩
    simp only [ind, this]
  · let G := lin S (j + 1) ⊓ (intP S Λ).toAddSubgroup.comap
      (algebraMap F E S.ϖ ^ (A + v) • (LinearMap.id : S.MW →ₗ[E] S.MW)).toAddMonoidHom
    refine finite_image_mk B G (hidx G inf_le_left fun w hw => hw.2) _ fun w hw => ?_
    have hw' : S.Mv (j + 1) d Λ w := by
      by_contra h
      exact hw (if_neg h)
    refine ⟨Mv_lin S hw', hbd w (Mv_lin S hw') hw'.2.2.1 hw'.2.2.2.2.1 ?_⟩
    obtain ⟨-, -, -, -, hu, -, ⟨c, hc, e⟩, -⟩ := hw'
    have : algebraMap F E S.ϖ ^ v * w.2.2 = algebraMap F E S.ϖ ^ v * (algebraMap F E S.ϖ ^ A * c) -
        algebraMap F E S.ϖ ^ v * algebraMap F E 2⁻¹ * S.h w.2.1 w.2.1 := by
      rw [← hA, ← e, Frames.sOf]; ring
    rw [this]
    exact L.O.sub_mem (L.O.mul_mem (hp _) (L.O.mul_mem (hp _) hc)) (L.O.mul_mem hv (hi _ hu _ hu))
  · have hw1 := hadd w hw b hb
    obtain ⟨y, hy, rfl, hl⟩ := hB b hb
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (mem_intP S).1 hy
    have hu := hw.2.2.2.2.1
    refine ⟨hn _ _ _ _ _ _ (iso_span S _ hJ0 _ hw.1) (hw.2.2.2.2.2.1 _ (Submodule.mem_sup_left hw.1))
      hw.2.2.2.2.2.2.2 (iso_span S _ hJ0 _ hw1.1) (hw1.2.2.2.2.2.1 _ (Submodule.mem_sup_left hw1.1))
      hw1.2.2.2.2.2.2.2 ?_ hu ?_ ⟨_, smul_memO S (hp (A + 1 + v)) h1, ?_⟩ ⟨_, smul_memO S (hp (A + 1 + v)) h3, ?_⟩ ?_,
      ?_, ?_⟩
    · rw [map_pow, ← hA]; exact (bound S d Λ hT _ hJ _ _ hw.1 hw.2.1 hw.2.2.1).1
    · obtain ⟨c, hc, e⟩ := hw.2.2.2.2.2.2.1
      rw [e, hA]; exact L.O.mul_mem (hp _) hc
    · simp only [Prod.fst_add, Prod.smul_fst, add_sub_cancel_left, map_pow, ← mul_smul, ← pow_add, add_assoc]
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, add_sub_cancel_left, map_pow,
        ← mul_smul, ← pow_add, add_assoc]
    · obtain ⟨z, hz, e⟩ := sOf_diff S hΛ (n + A + 1) v hv w y hu hy
      exact ⟨_, L.O.mul_mem (hp (A + 1)) hz, by rw [e, map_pow]; ring⟩
    · have hN : n + A + 1 + v = n + v + A + 1 := by ring
      rw [hN] at hl ⊢
      exact chi_add S j hT A hA _ w y hw hy hl
    · have hb' := smul_memO S (hp (n + A + v)) h3
      have e : (w + algebraMap F E S.ϖ ^ (n + A + 1 + v) • y).2.1 =
          w.2.1 + algebraMap F E S.ϖ • algebraMap F E S.ϖ ^ (n + A + v) • y.2.1 := by
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, ← mul_smul]
        congr 2; ring
      rw [e]
      refine ⟨fun h => ?_, noLeak_add S Λ hΛ _ _ hb'⟩
      simpa only [smul_neg, add_neg_cancel_right] using noLeak_add S Λ hΛ _ _ (Λ.neg_mem hb') h
end GlobalTheory.MoveFine
