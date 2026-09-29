-- Prove2me | solution 1 for ModularCurve.redRes_modularEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2e030f1e-9d41-572d-9663-ba75e87c1f83

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_redRes_modularEval

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_redRes_modularEval.ModularCurve ModularCurve.NodeLocalized ModularCurve.CharPReduction"

namespace ModularCurve
p2m_export "ModularCurve" "NodeLocalized.modularEval CharPReduction.redRes CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_eq_map_intCast qExpand_coeff_mul qExpand_coeff_of_not_dvd"
p2m_open "ModularCurve"
namespace RedEval
p2m_open "ModularCurve.CharPReduction"

section Eval
variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem modularEval_mem_modularRing (p : MvPolynomial (Fin 2) A) :
    modularEval N A p ∈ modularRing N A := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [modularEval, MvPolynomial.eval₂Hom_C]
    exact constSeries_mem_modularRing N A c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [modularEval, MvPolynomial.eval₂Hom_X']
    fin_cases i
    · exact jqModC_mem_modularRing N A
    · exact jqNModC_mem_modularRing N A

noncomputable def modularEvalRing : MvPolynomial (Fin 2) A →+* modularRing N A :=
  (modularEval N A).codRestrict _ (modularEval_mem_modularRing N A)

@[scoped simp] theorem coe_modularEvalRing (p : MvPolynomial (Fin 2) A) :
    (modularEvalRing N A p : LaurentSeries L) = modularEval N A p := rfl

noncomputable def modularEvalRed : MvPolynomial (Fin 2) A →+* LaurentSeries k :=
  MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![jqModC k, jqNModC k N]

theorem red_mk_eq {x : L} (hx : x ∈ A) (y : A) (h : x = (y : L)) : red ⟨x, hx⟩ = red y := by
  subst h; rfl

theorem coeffRed_constSeries (c : A) :
    coeffRed A red ⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ = algebraMap k (LaurentSeries k) (red c) := by
  have hc : ∀ n : ℤ, (constSeries A c).coeff n = if n = 0 then (c : L) else 0 := fun n => by
    show ((algebraMap L (LaurentSeries L)) (c : L)).coeff n = _
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
    split_ifs <;> rfl
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  by_cases h : n = 0
  · subst h
    rw [if_pos rfl]
    exact red_mk_eq A red _ c (by rw [show (↑(⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ : integralCoeffs A) : LaurentSeries L) = constSeries A c from rfl, hc, if_pos rfl])
  · rw [if_neg h]
    rw [red_mk_eq A red _ 0 (by rw [show (↑(⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ : integralCoeffs A) : LaurentSeries L) = constSeries A c from rfl, hc, if_neg h, ZeroMemClass.coe_zero])]
    exact map_zero red

theorem coeffRed_jqModC :
    coeffRed A red ⟨jqModC L, jqModC_mem_integralCoeffs A⟩ = jqModC k := by
  ext n
  rw [coeffRed_coeff]
  rw [red_mk_eq A red _ (((jqModC ℤ).coeff n : ℤ) : A) (by
      show (jqModC L).coeff n = (((((jqModC ℤ).coeff n : ℤ) : A)) : L)
      rw [jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]; simp)]
  rw [map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
  simp

theorem coeffRed_jqNModC :
    coeffRed A red ⟨jqNModC L N, jqNModC_mem_integralCoeffs N A⟩ = jqNModC k N := by
  ext n
  rw [coeffRed_coeff]
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [red_mk_eq A red _ (((jqModC ℤ).coeff m : ℤ) : A) (by
        show (jqNModC L N).coeff (N * m) = (((((jqModC ℤ).coeff m : ℤ) : A)) : L)
        rw [jqNModC, qExpand_coeff_mul, jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]; simp)]
    rw [map_intCast, jqNModC, qExpand_coeff_mul, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
    simp
  · rw [red_mk_eq A red _ 0 (by
        show (jqNModC L N).coeff n = ((0 : A) : L)
        rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h, ZeroMemClass.coe_zero])]
    rw [map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem redRes_modularEvalRing (p : MvPolynomial (Fin 2) A) :
    redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) (modularEvalRing N A p)
      = modularEvalRed N A red p := by
  have key : (redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A)).comp (modularEvalRing N A)
      = modularEvalRed N A red := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, redRes_apply, modularEvalRed, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        ← coeffRed_constSeries A red c]
      exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_C]))
    · rw [RingHom.comp_apply, redRes_apply, modularEvalRed, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · rw [← coeffRed_jqModC A red (L := L)]
        exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_X']; rfl))
      · rw [← coeffRed_jqNModC N A red (L := L)]
        exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_X']; rfl))
  exact RingHom.congr_fun key p

end Eval
end RedEval
p2m_reactivate "P2MW.S_ModularCurve_redRes_modularEval.ModularCurve.RedEval"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_redRes_modularEval.ModularCurve.RedEval P2MW.S_ModularCurve_redRes_modularEval.ModularCurve"

theorem solution (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (p : MvPolynomial (Fin 2) A)
    (hp : NodeLocalized.modularEval N A p ∈ CharPReduction.modularRing N A) :
    CharPReduction.redRes A red (CharPReduction.modularRing N A) (CharPReduction.modularRing_le_integralCoeffs N A)
        ⟨NodeLocalized.modularEval N A p, hp⟩
      = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![jqModC k, jqNModC k N] p := by
  have h := ModularCurve.RedEval.redRes_modularEvalRing N A red p
  have e : (⟨NodeLocalized.modularEval N A p, hp⟩ : ↥(CharPReduction.modularRing N A)) = ModularCurve.RedEval.modularEvalRing N A p :=
    Subtype.ext rfl
  rw [e, h]
  rfl

end S_ModularCurve_redRes_modularEval
end P2MW
export P2MW.S_ModularCurve_redRes_modularEval (solution)
