-- Prove2me | solution 1 for ModularCurve.heckeBetaCIntegral_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/24352ebd-8791-5c40-82ca-45945634ac72

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeBetaCIntegral_unconditional
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "charLDegeneracyRoof heckeBetaC HeckeBetaCIntegral qExpandAlgC jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_qExpand ModularPolynomialData nonempty_modularPolynomialData ModularPolynomialData.evalSymm_of_one_lt swapInner swapBivar swapBivar_X swapBivar_eq_of_evalSymm"
namespace IntegralLegs
p2m_open "ModularCurve"

private theorem eval₂_swapBivar {S : Type*} [CommRing S] {algZ : Algebra ℤ S} (Φ : Polynomial (Polynomial ℤ)) (x y : S) :
    (swapBivar Φ).eval₂ (aeval (R := ℤ) x).toRingHom y = Φ.eval₂ (aeval (R := ℤ) y).toRingHom x := by

  have hin : (eval₂RingHom (aeval (R := ℤ) x).toRingHom y).comp swapInner = (aeval (R := ℤ) y).toRingHom := by
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · rw [RingHom.comp_apply, coe_eval₂RingHom, show swapInner (C n) = C (C n) by simp [swapInner], eval₂_C]
      simp
    · rw [RingHom.comp_apply, coe_eval₂RingHom, show swapInner X = X by simp [swapInner], eval₂_X]
      simp
  have h : (eval₂RingHom (aeval (R := ℤ) x).toRingHom y).comp swapBivar = eval₂RingHom (aeval (R := ℤ) y).toRingHom x := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, eval₂_C,
        show swapBivar (C c) = swapInner c from Polynomial.eval₂_C _ _]
      rw [← hin, RingHom.comp_apply, coe_eval₂RingHom]
    · rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, swapBivar_X, eval₂_C, eval₂_X]
      simp
  exact DFunLike.congr_fun h Φ

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

private theorem isIntegral_of_coe_eq {A R : IntermediateField k L} (φ : L →ₐ[k] L) (f : A →ₐ[k] R)
    (hf : ∀ a : A, ((f a : R) : L) = φ a) (hint : ∀ r : R, IsIntegral (A.map φ) (r : L)) :
    f.toRingHom.IsIntegral := by
  intro r
  obtain ⟨p, hp, hr⟩ := hint r
  let e : A ≃ₐ[k] A.map φ := equivMap A φ
  refine ⟨p.map (e.symm : A.map φ →+* A), hp.map _, ?_⟩
  apply Subtype.val_injective
  change algebraMap R L (eval₂ f.toRingHom r (p.map (e.symm : A.map φ →+* A))) = ((0 : R) : L)
  rw [hom_eval₂, eval₂_map, ZeroMemClass.coe_zero]
  have hcomp : ((algebraMap R L).comp f.toRingHom).comp (e.symm : A.map φ →+* A) = algebraMap (A.map φ) L := by
    refine RingHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply]
    change ((f a : R) : L) = φ a
    exact hf a
  rw [hcomp]
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

private theorem eval_one' (hq : 1 < q) : (Φq q).Φ.eval₂ (aeval (R := ℤ) (jqNModC k q)).toRingHom (jqModC k) = 0 := by
  have hs : swapBivar (Φq q).Φ = (Φq q).Φ := swapBivar_eq_of_evalSymm (ModularPolynomialData.evalSymm_of_one_lt q hq _)
  rw [← eval₂_swapBivar, hs]
  exact eval_one k q

private theorem eval_N' (hq : 1 < q) : (Φq q).Φ.eval₂ (aeval (R := ℤ) (jqNModC k (N * q))).toRingHom (jqNModC k N) = 0 := by
  have hs : swapBivar (Φq q).Φ = (Φq q).Φ := swapBivar_eq_of_evalSymm (ModularPolynomialData.evalSymm_of_one_lt q hq _)
  rw [← eval₂_swapBivar, hs]
  exact eval_N k N q

private theorem heckeBetaCIntegral : HeckeBetaCIntegral k N q := by
  let B : IntermediateField k (LaurentSeries k) := (modularFunctionFieldC k N).map (qExpandAlgC k q)
  have hjq : jqNModC k q ∈ B := ⟨jqModC k, jqModC_mem k N, rfl⟩
  have hjNq : jqNModC k (N * q) ∈ B := by
    refine ⟨jqNModC k N, jqNModC_mem k N, ?_⟩
    show qExpand k q (jqNModC k N) = jqNModC k (N * q)
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm q N]
  have hR : charLDegeneracyRoof k N q ≤ integralField B := by
    refine adjoin_le_integralField _ _ ?_
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) with hq | hq
    ·
      have h1 : jqModC k = jqNModC k q := by rw [← jqNModC_congr k hq, jqNModC_one]
      have hN : jqNModC k N = jqNModC k (N * q) := jqNModC_congr k (by rw [← hq, mul_one])
      rintro s (rfl | rfl | rfl | rfl)
      · exact isIntegral_of_mem _ (h1 ▸ hjq)
      · exact isIntegral_of_mem _ (hN ▸ hjNq)
      · exact isIntegral_of_mem _ hjq
      · exact isIntegral_of_mem _ hjNq
    · rintro s (rfl | rfl | rfl | rfl)
      · exact isIntegral_of_eval₂_eq_zero _ _ (Φq q).monic hjq (eval_one' k q hq)
      · exact isIntegral_of_eval₂_eq_zero _ _ (Φq q).monic hjNq (eval_N' k N q hq)
      · exact isIntegral_of_mem _ hjq
      · exact isIntegral_of_mem _ hjNq
  unfold HeckeBetaCIntegral
  exact isIntegral_of_coe_eq (qExpandAlgC k q) (heckeBetaC k N q) (fun _ => rfl) fun r => mem_integralField.mp (hR r.2)

end Modular

end ModularCurve.IntegralLegs

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_heckeBetaCIntegral_unconditional.ModularCurve in
theorem solution (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q] :
    HeckeBetaCIntegral k N q :=
  ModularCurve.IntegralLegs.heckeBetaCIntegral k N q

end S_ModularCurve_heckeBetaCIntegral_unconditional
end P2MW
export P2MW.S_ModularCurve_heckeBetaCIntegral_unconditional (solution)
