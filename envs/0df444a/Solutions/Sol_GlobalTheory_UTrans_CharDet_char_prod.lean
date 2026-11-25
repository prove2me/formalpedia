-- Prove2me | solution 1 for GlobalTheory.UTrans.CharDet.char_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:14:03.960428+00:00
-- url     : https://prove2.me/submissions/6d7ac719-99f5-4e77-b8dd-926b766df994

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWittStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfDetEqOne
import Theorems.Thm_GlobalTheory_UTrans_CharDet_isU_one
import Theorems.Thm_GlobalTheory_UTrans_CharDet_isU_refl
import Theorems.Thm_GlobalTheory_UTrans_CharDet_refl_mul
import Theorems.Thm_GlobalTheory_UTrans_CharDet_refl_det
import Theorems.Thm_GlobalTheory_UTrans_CharDet_refl_one
import Theorems.Thm_GlobalTheory_UTrans_CharDet_char_refl_eq
import Theorems.Thm_GlobalTheory_UTrans_Calc_isU_mul
import Theorems.Thm_GlobalTheory_UTrans_IsU_det_mul_conj_det
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_isU_refl


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
    {x : Fin n → E} (hx : hf σ G x x ≠ 0) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    IsU σ G (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod ∧
      X (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod =
        X (tv σ G x (((l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod.det - 1) / hf σ G x x)) := by
  induction l with
  | nil => exact ⟨isU_one, by simp only [List.map_nil, List.prod_nil, Matrix.det_one, refl_one]⟩
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨hp, hv⟩ := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons]
    refine ⟨Calc.isU_mul σ G _ _ (isU_refl hG hp hv) h1, ?_⟩
    rw [hX _ _ (isU_refl hG hp hv) h1, h2, char_refl_eq hG h hX hp hx hv, Matrix.det_mul, refl_det _ hp,
      ← refl_mul _ _ hx, hX _ _ (isU_refl hG hx hv) (isU_refl hG hx (h1.det_mul_conj_det hG.det_ne))]
end GlobalTheory.UTrans.CharDet
