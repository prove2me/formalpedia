-- Prove2me | solution 1 for ModularCurve.heckeAlphaCIntegral_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0011003a-6814-5426-8e6f-8127f6fc31e1

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeAlphaCIntegral_unconditional
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "charLDegeneracyRoof modularFunctionFieldC_le_charLDegeneracyRoof heckeAlphaC HeckeAlphaCIntegral jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem ModularPolynomialData nonempty_modularPolynomialData"
namespace IntegralLegs
p2m_open "ModularCurve"

section Generic

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

private def integralField (B : IntermediateField k L) : IntermediateField k L :=
  ((integralClosure B L).restrictScalars k).toIntermediateField fun x hx => by
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hx ⊢
    exact hx.inv

private theorem mem_integralField {B : IntermediateField k L} {x : L} : x ∈ integralField B ↔ IsIntegral B x := by
  change x ∈ (integralClosure B L).restrictScalars k ↔ _
  rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]

private theorem le_integralField (B : IntermediateField k L) : B ≤ integralField B :=
  fun x hx => mem_integralField.mpr (isIntegral_algebraMap (A := L) (x := (⟨x, hx⟩ : B)))

private theorem adjoin_le_integralField (B : IntermediateField k L) (S : Set L) (hS : ∀ s ∈ S, IsIntegral B s) :
    adjoin k S ≤ integralField B :=
  adjoin_le_iff.mpr fun s hs => mem_integralField.mpr (hS s hs)

private theorem isIntegral_of_mem (B : IntermediateField k L) {x : L} (hx : x ∈ B) : IsIntegral B x :=
  mem_integralField.mp (le_integralField B hx)

private theorem isIntegral_of_eval₂_eq_zero (B : IntermediateField k L) (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    {algZ : Algebra ℤ L} {x y : L} (hx : x ∈ B) (h : Φ.eval₂ (aeval (R := ℤ) x).toRingHom y = 0) :
    IsIntegral B y := by
  refine ⟨Φ.map (aeval (R := ℤ) (⟨x, hx⟩ : B)).toRingHom, hΦ.map _, ?_⟩
  rw [eval₂_map]
  have hcomp : (algebraMap B L).comp (aeval (R := ℤ) (⟨x, hx⟩ : B)).toRingHom = (aeval (R := ℤ) x).toRingHom := by
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · simp
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
      rfl
  rw [hcomp]
  exact h

private theorem isIntegral_inclusion {A R : IntermediateField k L} (hAR : A ≤ R) (hint : ∀ r : R, IsIntegral A (r : L)) :
    (IntermediateField.inclusion hAR).toRingHom.IsIntegral := by
  intro r
  obtain ⟨p, hp, hr⟩ := hint r
  refine ⟨p, hp, ?_⟩
  apply Subtype.val_injective
  change algebraMap R L (p.eval₂ (IntermediateField.inclusion hAR).toRingHom r) = ((0 : R) : L)
  have hcomp : (algebraMap R L).comp (IntermediateField.inclusion hAR).toRingHom = algebraMap A L :=
    RingHom.ext fun _ => rfl
  rw [hom_eval₂, ZeroMemClass.coe_zero, hcomp]
  exact hr

end Generic

section Modular

variable (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]

omit [NeZero N] [NeZero q] in
private theorem jqNModC_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) : jqNModC k a = jqNModC k b := by
  subst h; rfl

private def Φq : ModularPolynomialData q := (nonempty_modularPolynomialData q).some

private theorem eval_one : (Φq q).Φ.eval₂ (aeval (R := ℤ) (jqModC k)).toRingHom (jqNModC k q) = 0 := by
  have h := (Φq q).eval_jqNModC_mul_eq_zero k 1
  rwa [jqNModC_one, jqNModC_congr k (one_mul q)] at h

private theorem eval_N : (Φq q).Φ.eval₂ (aeval (R := ℤ) (jqNModC k N)).toRingHom (jqNModC k (N * q)) = 0 :=
  (Φq q).eval_jqNModC_mul_eq_zero k N

private theorem heckeAlphaCIntegral : HeckeAlphaCIntegral k N q := by
  have hR : charLDegeneracyRoof k N q ≤ integralField (modularFunctionFieldC k N) := by
    refine adjoin_le_integralField _ _ ?_
    rintro s (rfl | rfl | rfl | rfl)
    · exact isIntegral_of_mem _ (jqModC_mem k N)
    · exact isIntegral_of_mem _ (jqNModC_mem k N)
    · exact isIntegral_of_eval₂_eq_zero _ _ (Φq q).monic (jqModC_mem k N) (eval_one k q)
    · exact isIntegral_of_eval₂_eq_zero _ _ (Φq q).monic (jqNModC_mem k N) (eval_N k N q)
  unfold HeckeAlphaCIntegral heckeAlphaC
  exact isIntegral_inclusion (modularFunctionFieldC_le_charLDegeneracyRoof k N q) fun r => mem_integralField.mp (hR r.2)

end Modular

end ModularCurve.IntegralLegs

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_heckeAlphaCIntegral_unconditional.ModularCurve in
theorem solution (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q] :
    HeckeAlphaCIntegral k N q :=
  ModularCurve.IntegralLegs.heckeAlphaCIntegral k N q

end S_ModularCurve_heckeAlphaCIntegral_unconditional
end P2MW
export P2MW.S_ModularCurve_heckeAlphaCIntegral_unconditional (solution)
