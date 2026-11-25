-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.exists_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:45.369515+00:00
-- url     : https://prove2.me/submissions/89e8ea7d-3ec6-499a-8820-38fdf2079659

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Theorems.Thm_GlobalTheory_HL_OrthCompl_hf_eq_zero_symm
import Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_norm_one_orth_triple
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution (h : IsHerm L Hm) (M : Submodule L.O (Fin n → E)) {e0 e1 e2 : Fin n → E}
    (m0 : e0 ∈ M) (m1 : e1 ∈ M) (m2 : e2 ∈ M)
    (h00 : hf L Hm e0 e0 = 1) (h11 : hf L Hm e1 e1 = 1) (h22 : hf L Hm e2 e2 = 1)
    (h01 : hf L Hm e0 e1 = 0) (h02 : hf L Hm e0 e2 = 0) (h12 : hf L Hm e1 e2 = 0)
    (y : Fin n → E) :
    ∃ u ∈ M, ∃ t ∈ M, ∃ s ∈ M, hf L Hm u u = 1 ∧ hf L Hm t t = 1 ∧ hf L Hm s s = 1 ∧
      hf L Hm t u = 0 ∧ hf L Hm s u = 0 ∧ hf L Hm s t = 0 ∧ hf L Hm u y = 0 := by
  have h10 := hf_eq_zero_symm L h h01
  have h20 := hf_eq_zero_symm L h h02
  have h21 := hf_eq_zero_symm L h h12
  have hM : ∀ a ∈ L.O, ∀ b ∈ L.O, ∀ c ∈ L.O, a • e0 + b • e1 + c • e2 ∈ M :=
    fun a ha b hb c hc => M.add_mem (M.add_mem (M.smul_mem ⟨a, ha⟩ m0) (M.smul_mem ⟨b, hb⟩ m1))
      (M.smul_mem ⟨c, hc⟩ m2)
  have hB : ∀ a b c a' b' c' : E, hf L Hm (a • e0 + b • e1 + c • e2) (a' • e0 + b' • e1 + c' • e2)
      = a * L.cj a' + b * L.cj b' + c * L.cj c' := fun a b c a' b' c' => by
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, h00, h11, h22, h01, h02, h12, h10, h20,
      h21]
    ring
  obtain ⟨u0, hu0, u1, hu1, u2, hu2, k1, k2⟩ :=
    exists_norm_one_orth_triple L (hf L Hm e0 y) (hf L Hm e1 y) (hf L Hm e2 y)
  obtain ⟨t0, ht0, t1, ht1, t2, ht2, l1, l2⟩ :=
    exists_norm_one_orth_triple L (L.cj u0) (L.cj u1) (L.cj u2)
  have l3 := congrArg L.cj l2
  simp only [map_add, map_mul, map_zero, L.cj_cj] at l3
  refine ⟨_, hM u0 hu0 u1 hu1 u2 hu2, _, hM t0 ht0 t1 ht1 t2 ht2, _,
    hM (L.cj (u1 * t2 - u2 * t1)) (cj_mem L ?_) (L.cj (u2 * t0 - u0 * t2)) (cj_mem L ?_)
      (L.cj (u0 * t1 - u1 * t0)) (cj_mem L ?_), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact L.O.sub_mem (L.O.mul_mem hu1 ht2) (L.O.mul_mem hu2 ht1)
  · exact L.O.sub_mem (L.O.mul_mem hu2 ht0) (L.O.mul_mem hu0 ht2)
  · exact L.O.sub_mem (L.O.mul_mem hu0 ht1) (L.O.mul_mem hu1 ht0)
  · rw [hB, k1]
  · rw [hB, l1]
  · rw [hB]
    simp only [map_sub, map_mul, L.cj_cj]
    linear_combination (t0 * L.cj t0 + t1 * L.cj t1 + t2 * L.cj t2) * k1 + l1
      - (L.cj t0 * u0 + L.cj t1 * u1 + L.cj t2 * u2) * l2
  · rw [hB, l2]
  · rw [hB]
    simp only [map_sub, map_mul]
    ring
  · rw [hB]
    simp only [map_sub, map_mul]
    ring
  · simp only [hf_add_l, hf_smul_l]
    exact k2
end GlobalTheory.HL.OrthCompl
