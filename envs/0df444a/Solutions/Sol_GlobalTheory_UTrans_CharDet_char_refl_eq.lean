-- Prove2me | solution 1 for GlobalTheory.UTrans.CharDet.char_refl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:47:27.521943+00:00
-- url     : https://prove2.me/submissions/80ecc958-6d8b-49ff-acce-5d3a686d9cb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWittStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfDetEqOne
import Theorems.Thm_GlobalTheory_UTrans_CharDet_isU_refl
import Theorems.Thm_GlobalTheory_T_unitaryCharacter_kills_unitaryTransvections
import Theorems.Thm_GlobalTheory_T_unitary_generated_by_quasiReflections_and_witt
import Theorems.Thm_GlobalTheory_UTrans_Calc_conj_tv
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_smul_left
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_smul_right
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_smul
import Theorems.Thm_GlobalTheory_UTrans_PlaneRefl_hf_smul_left
import Theorems.Thm_GlobalTheory_UTrans_PlaneRefl_hf_smul_right
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_isU_refl
import Theorems.Thm_GlobalTheory_UTrans_quasiReflection_eq_tvGen_mul
import Theorems.Thm_GlobalTheory_UTrans_tvGen_normal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.CharDet
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
variable [CharZero E] {A : Type} [CommGroup A] {X : Matrix (Fin n) (Fin n) E → A}
namespace GlobalTheory.UTrans.CharDet
theorem _root_.solution (hG : IsHerm σ G)
    (h : (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) ∨ ∀ x y : Fin n → E, hf σ G x x ≠ 0 → hf σ G y y ≠ 0 →
      ∃ a : E, hf σ G y y = σ a * a * hf σ G x x)
    (hX : ∀ a b, IsU σ G a → IsU σ G b → X (a * b) = X a * X b)
    {x y : Fin n → E} {u : E} (hx : hf σ G x x ≠ 0) (hy : hf σ G y y ≠ 0) (hu : u * σ u = 1) :
    X (tv σ G x ((u - 1) / hf σ G x x)) = X (tv σ G y ((u - 1) / hf σ G y y)) := by
  rcases h with h | h
  · obtain ⟨m, hm, e⟩ := quasiReflection_eq_tvGen_mul E n σ G hG h x y u hx hy hu
    rw [e, hX _ _ ((tvGen_normal E n σ G hG).2 m hm).1 (isU_refl hG hy hu),
      GlobalTheory.T.unitaryCharacter_kills_unitaryTransvections E n σ G hG A X hX m hm, one_mul]
  · obtain ⟨a, ha⟩ := h x y hx hy
    have h1 : hf σ G (a • x) (a • x) = hf σ G y y := by
      rw [Calc.hf_smul_left, Calc.hf_smul_right, ha]; ring
    obtain ⟨γ, hγ, e⟩ := (GlobalTheory.T.unitary_generated_by_quasiReflections_and_witt E n σ G hG).2 y (a • x) hy h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
      exact hy ha
    have ha1 : σ a ≠ 0 := (map_ne_zero σ).2 ha0
    have h2 : tv σ G x ((u - 1) / hf σ G x x) = tv σ G (a • x) ((u - 1) / hf σ G y y) := by
      rw [Calc.tv_smul, ha]
      congr 1
      field_simp
    have h3 : γ * tv σ G x ((u - 1) / hf σ G x x) = tv σ G y ((u - 1) / hf σ G y y) * γ := by
      rw [h2, Calc.conj_tv σ G γ _ _ hγ, e]
    have h4 := congrArg X h3
    rw [hX _ _ hγ (isU_refl hG hx hu), hX _ _ (isU_refl hG hy hu) hγ, mul_comm] at h4
    exact mul_right_cancel h4
end GlobalTheory.UTrans.CharDet
