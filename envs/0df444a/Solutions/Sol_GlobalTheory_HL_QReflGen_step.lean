-- Prove2me | solution 1 for GlobalTheory.HL.QReflGen.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:52.411793+00:00
-- url     : https://prove2.me/submissions/1d53bac9-6e18-4ec8-80af-4675f353b686

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_add_l
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_smul_l
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_add_r
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_smul_r
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_cj
import Theorems.Thm_GlobalTheory_HL_QReflGen_exists_qrefl
import Theorems.Thm_GlobalTheory_HL_QReflGen_exists_norm_one
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.QReflGen
theorem _root_.solution [CharZero F] (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) (hx : IsUnit (hf L Hm x x)) (hxy : hf L Hm y y = hf L Hm x x) :
    ∃ (u : E) (σ ρ : (Fin n → E) ≃ₗ[E] (Fin n → E)),
      IsQRefl L Hm (x + (-u) • y) σ ∧ IsQRefl L Hm y ρ ∧ σ x = ρ y := by
  obtain ⟨u, huu, hb, hbb⟩ := exists_norm_one L (hf L Hm x x) (hf L Hm x y) hx (hf_cj L h x x)
  have haa : hf L Hm (x + (-u) • y) (x + (-u) • y) =
      (hf L Hm x x - L.cj u * hf L Hm x y) + L.cj (hf L Hm x x - L.cj u * hf L Hm x y) := by
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_mul, map_sub, map_neg, hf_cj L h,
      L.cj_cj, hxy]
    linear_combination hf L Hm x x * huu
  have hxa : hf L Hm x (x + (-u) • y) = hf L Hm x x - L.cj u * hf L Hm x y := by
    simp only [hf_add_r, hf_smul_r, map_neg]; ring
  obtain ⟨b, hb1⟩ := hb.exists_left_inv
  obtain ⟨t, ht1⟩ := hx.exists_left_inv
  have hb2 := congrArg L.cj hb1
  have ht2 := congrArg L.cj ht1
  rw [map_mul, map_one] at hb2 ht2
  rw [hf_cj L h] at ht2
  have htt : L.cj t = t := by linear_combination t * ht2 - L.cj t * ht1
  obtain ⟨σ, hσ, hσ'⟩ := exists_qrefl L h (x + (-u) • y) (haa ▸ hbb) (-b) (by
    rw [haa, map_neg]
    linear_combination L.cj b * hb1 + b * hb2)
  obtain ⟨ρ, hρ, hρ'⟩ := exists_qrefl L h y (hxy ▸ hx) ((u - 1) * t) (by
    rw [hxy, map_mul, map_sub, map_one, htt]
    linear_combination (u - 1) * (L.cj u - 1) * t * ht1 + t * huu)
  refine ⟨u, σ, ρ, hσ, hρ, ?_⟩
  rw [hσ', hρ', hxa, hxy, neg_mul, hb1, mul_assoc, ht1]
  module
end GlobalTheory.HL.QReflGen
