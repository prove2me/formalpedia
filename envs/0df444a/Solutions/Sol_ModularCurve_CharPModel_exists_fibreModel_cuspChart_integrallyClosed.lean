-- Prove2me | solution 1 for ModularCurve.CharPModel.exists_fibreModel_cuspChart_integrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fa3c907b-5b3f-551a-b09f-8eafd65dad38

import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.BigOperators.Fin
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero
import Theorems.Thm_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero
import Theorems.Thm_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

namespace CharpS10bB

section Organs

open Polynomial
open scoped Polynomial.Bivariate

theorem exists_mul_eq_of_forall_mem_closure_range {L B : Type*} [Field L] [CommRing B]
    (π : B →+* L) (hgen : ∀ x : L, x ∈ Subfield.closure (π.range : Set L)) :
    ∀ x : L, ∃ b c : B, π c ≠ 0 ∧ x * π c = π b := by
  intro x
  obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.mp (hgen x)
  rw [Subring.closure_eq] at hy hz
  obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hy
  obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hz
  by_cases hc : π c = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [← hyz, hc, div_zero, map_one, map_zero, zero_mul]
  · exact ⟨b, c, hc, ((div_eq_iff hc).mp hyz).symm⟩

theorem forall_mem_closure_range_of_adjoin {F E : Type*} [Field F] [Field E] [Algebra F E]
    (S : Set E) {B : Type*} [CommRing B] (π : B →+* IntermediateField.adjoin F S)
    (hconst : ∀ c : F, algebraMap F (IntermediateField.adjoin F S) c ∈
      Subfield.closure (π.range : Set (IntermediateField.adjoin F S)))
    (hgen : ∀ (s : E) (hs : s ∈ S),
      (⟨s, IntermediateField.subset_adjoin F S hs⟩ : IntermediateField.adjoin F S) ∈
        Subfield.closure (π.range : Set (IntermediateField.adjoin F S))) :
    ∀ x : IntermediateField.adjoin F S,
      x ∈ Subfield.closure (π.range : Set (IntermediateField.adjoin F S)) := by
  intro x
  set T := Subfield.closure (π.range : Set (IntermediateField.adjoin F S)) with hT
  let T' : Subfield E := T.map (algebraMap (IntermediateField.adjoin F S) E)
  have hle : Subfield.closure (Set.range (algebraMap F E) ∪ S) ≤ T' := by
    rw [Subfield.closure_le]
    rintro e (⟨c, rfl⟩ | he)
    · exact ⟨_, hconst c, rfl⟩
    · exact ⟨_, hgen e he, rfl⟩
  have hxE : (x : E) ∈ Subfield.closure (Set.range (algebraMap F E) ∪ S) := x.2
  obtain ⟨t, ht, htx⟩ := Subfield.mem_map.mp (hle hxE)
  have htx' : t = x := Subtype.ext htx
  exact htx' ▸ ht

theorem exists_mul_eq_of_adjoin {F E : Type*} [Field F] [Field E] [Algebra F E]
    (S : Set E) {B : Type*} [CommRing B] (π : B →+* IntermediateField.adjoin F S)
    (hconst : ∀ c : F, algebraMap F (IntermediateField.adjoin F S) c ∈
      Subfield.closure (π.range : Set (IntermediateField.adjoin F S)))
    (hgen : ∀ (s : E) (hs : s ∈ S),
      (⟨s, IntermediateField.subset_adjoin F S hs⟩ : IntermediateField.adjoin F S) ∈
        Subfield.closure (π.range : Set (IntermediateField.adjoin F S))) :
    ∀ x : IntermediateField.adjoin F S, ∃ b c : B, π c ≠ 0 ∧ x * π c = π b :=
  exists_mul_eq_of_forall_mem_closure_range π (forall_mem_closure_range_of_adjoin S π hconst hgen)

end Organs

namespace Model

p2m_open "ModularCurve~coeffMap_qExpand ModularCurve.CharPModel ModularCurve.CharPReduction Polynomial"

abbrev FF (N : ℕ) [NeZero N] : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)

variable (N : ℕ) [NeZero N]

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_apply_eq_single, algebraMap_laurentSeries_eq_single]
  exact coeffMap_single _ _ _

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L :=
  map_jqModC (algebraMap ℚ L)

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext j
  by_cases hj : (n : ℤ) ∣ j
  · obtain ⟨m, rfl⟩ := hj
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hj, qExpand_coeff_of_not_dvd n _ hj,
      map_zero]

theorem coeffEmb_qExpand_jq (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L (qExpand ℚ N jq) = jqNModC L N := by
  show coeffMap (algebraMap ℚ L) (qExpand ℚ N jq) = qExpand L N (jqModC L)
  rw [coeffMap_qExpand, ← coeffEmb_jq]
  rfl

theorem modularFunctionFieldFull_le : modularFunctionFieldFull N ≤ modularFunctionField N := by
  rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd, hdvd, rfl⟩
  exact functionFieldGeneration N d hdvd hd

theorem ff_le_modularFunctionFieldC :
    (FF N : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
      ≤ modularFunctionFieldC (AlgebraicClosure ℚ) N := by
  rw [FF, laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hxN : x ∈ modularFunctionField N := modularFunctionFieldFull_le N hx

  have key : (modularFunctionField N).toSubfield ≤
      (modularFunctionFieldC (AlgebraicClosure ℚ) N).toSubfield.comap
        (coeffEmb (AlgebraicClosure ℚ)) := by
    show Subfield.closure _ ≤ _
    rw [Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | rfl | rfl) <;>
      rw [SetLike.mem_coe, Subfield.mem_comap, IntermediateField.mem_toSubfield]
    · rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · rw [coeffEmb_jq]
      exact jqModC_mem _ N
    · rw [coeffEmb_qExpand_jq]
      exact jqNModC_mem _ N
  exact key hxN

theorem coe_mem_modularFunctionFieldC (x : FF N) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldC (AlgebraicClosure ℚ) N :=
  ff_le_modularFunctionFieldC N x.2

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem coe_jBar : ((jBar N : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
  coeffEmb_jq _

theorem coe_jNBar : ((jNBar N : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) N :=
  coeffEmb_qExpand_jq N _

omit [NeZero N] in
theorem coe_constantsHom (a : A) :
    ((constantsHom N A a : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = constSeries A.toSubring ⟨a, a.2⟩ :=
  rfl

theorem coe_mem_modularRing_of_mem_affineBaseFin {x : FF N} (hx : x ∈ affineBaseFin N A) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularRing N A.toSubring := by
  have : affineBaseFin N A ≤ (modularRing N A.toSubring).comap
      (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))) := by
    rw [affineBaseFin, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl) <;> rw [SetLike.mem_coe, Subring.mem_comap]
    · show ((constantsHom N A a : FF N) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ modularRing N A.toSubring
      rw [coe_constantsHom]
      exact constSeries_mem_modularRing N A.toSubring _
    · show ((jBar N : FF N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularRing N A.toSubring
      rw [coe_jBar]
      exact jqModC_mem_modularRing N A.toSubring
  exact this hx

private def _root_.CharpS10bB.Model.BFin : Subring (FF N) := (integralClosure (affineBaseFin N A) (FF N)).toSubring

p2m_export "CharpS10bB.Model" "BFin"

private def _root_.CharpS10bB.Model.BInf : Subring (FF N) := (integralClosure (affineBaseInf N A) (FF N)).toSubring

p2m_export "CharpS10bB.Model" "BInf"
section ICWitness
variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']

theorem isIntegrallyClosed_integralClosure_in_field :
    IsIntegrallyClosed (integralClosure R' K') := by
  have hinj : Function.Injective (algebraMap (integralClosure R' K') K') :=
    Subtype.val_injective
  let φ : FractionRing (integralClosure R' K') →+* K' := IsFractionRing.lift hinj
  have hφinj : Function.Injective φ := φ.injective
  have hφcomp : φ.comp (algebraMap (integralClosure R' K') (FractionRing (integralClosure R' K')))
      = algebraMap (integralClosure R' K') K' :=
    RingHom.ext (IsFractionRing.lift_algebraMap hinj)
  refine (isIntegrallyClosed_iff (FractionRing (integralClosure R' K'))).mpr fun {x} hx => ?_
  have hφx : IsIntegral (integralClosure R' K') (φ x) :=
    hx.map_of_comp_eq (RingHom.id _) φ (by rw [RingHom.comp_id]; exact hφcomp.symm)
  have hmem : (φ x : K') ∈ integralClosure R' K' := isIntegral_trans (φ x) hφx
  refine ⟨⟨φ x, hmem⟩, hφinj ?_⟩
  rw [← RingHom.comp_apply, hφcomp]
  rfl

end ICWitness

scoped instance instIsIntegrallyClosed_BFin : IsIntegrallyClosed (BFin N A) :=
  isIntegrallyClosed_integralClosure_in_field (R' := affineBaseFin N A) (K' := FF N)

scoped instance instIsIntegrallyClosed_BInf : IsIntegrallyClosed (BInf N A) :=
  isIntegrallyClosed_integralClosure_in_field (R' := affineBaseInf N A) (K' := FF N)

theorem mem_BFin_iff {x : FF N} :
    x ∈ BFin N A ↔ ∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype x p = 0 :=
  Iff.rfl

theorem mem_BInf_iff {x : FF N} :
    x ∈ BInf N A ↔ ∃ p : Polynomial (affineBaseInf N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseInf N A).subtype x p = 0 :=
  Iff.rfl

theorem affineBaseFin_le_BFin : affineBaseFin N A ≤ BFin N A := fun x hx =>
  (mem_BFin_iff N A).2 ⟨X - C ⟨x, hx⟩, monic_X_sub_C _, by simp⟩

theorem affineBaseInf_le_BInf : affineBaseInf N A ≤ BInf N A := fun x hx =>
  (mem_BInf_iff N A).2 ⟨X - C ⟨x, hx⟩, monic_X_sub_C _, by simp⟩

theorem constFin_mem (a : A) : constantsHom N A a ∈ BFin N A :=
  affineBaseFin_le_BFin N A (Subring.subset_closure (Or.inl ⟨a, rfl⟩))

theorem constInf_mem (a : A) : constantsHom N A a ∈ BInf N A :=
  affineBaseInf_le_BInf N A (Subring.subset_closure (Or.inl ⟨a, rfl⟩))

theorem jBar_mem_affineBaseFin : jBar N ∈ affineBaseFin N A :=
  Subring.subset_closure (Or.inr rfl)

theorem jBar_mem : jBar N ∈ BFin N A :=
  affineBaseFin_le_BFin N A (jBar_mem_affineBaseFin N A)

theorem jInvBar_mem_affineBaseInf : (jBar N)⁻¹ ∈ affineBaseInf N A :=
  Subring.subset_closure (Or.inr rfl)

theorem jInvBar_mem : (jBar N)⁻¹ ∈ BInf N A :=
  affineBaseInf_le_BInf N A (jInvBar_mem_affineBaseInf N A)

theorem integralFin (b : BFin N A) : ∃ p : Polynomial (affineBaseFin N A),
    p.Monic ∧ Polynomial.eval₂ (affineBaseFin N A).subtype (b : FF N) p = 0 :=
  b.2

theorem integralInf (b : BInf N A) : ∃ p : Polynomial (affineBaseInf N A),
    p.Monic ∧ Polynomial.eval₂ (affineBaseInf N A).subtype (b : FF N) p = 0 :=
  b.2

theorem eval₂_Phi_jqModC (data : ModularPolynomialData N) :
    data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
      (jqModC (AlgebraicClosure ℚ))) (jqNModC (AlgebraicClosure ℚ) N) = 0 := by
  have h := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
  rw [map_zero, hom_eval₂] at h
  have hring : (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ
      = eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
          (jqModC (AlgebraicClosure ℚ)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [evalAtJ_def]
    · rw [RingHom.comp_apply, evalAtJ_def, coe_eval₂RingHom, eval₂_X]
      show coeffEmb (AlgebraicClosure ℚ) ((Polynomial.aeval (R := ℤ) jq) X) = _
      rw [aeval_X, coeffEmb_jq]
  have hjN : coeffEmb (AlgebraicClosure ℚ) (jqN N) = jqNModC (AlgebraicClosure ℚ) N :=
    coeffEmb_qExpand_jq N _
  rwa [hring, hjN] at h

def intPolyToFin : Polynomial ℤ →+* affineBaseFin N A :=
  eval₂RingHom (Int.castRingHom _) ⟨jBar N, jBar_mem_affineBaseFin N A⟩

theorem algebraMap_comp_subtype_comp_intPolyToFin :
    ((algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp (affineBaseFin N A).subtype).comp
        (intPolyToFin N A)
      = eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
          (jqModC (AlgebraicClosure ℚ)) := by
  refine Polynomial.ringHom_ext (fun a => by simp [intPolyToFin]) ?_
  simp only [RingHom.comp_apply, intPolyToFin, coe_eval₂RingHom, eval₂_X]
  exact coe_jBar N

theorem jNBar_mem (data : ModularPolynomialData N) : jNBar N ∈ BFin N A := by
  refine (mem_BFin_iff N A).2 ⟨data.Φ.map (intPolyToFin N A), data.monic.map _, ?_⟩
  apply (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).injective
  rw [map_zero, hom_eval₂, eval₂_map, algebraMap_comp_subtype_comp_intPolyToFin]
  show data.Φ.eval₂ _ ((jNBar N : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = 0
  rw [coe_jNBar]
  exact eval₂_Phi_jqModC N data

section Generic

variable {L : Type*} [Field L] (A' : Subring L) {k : Type*} [Field k] (red' : A' →+* k)

theorem red_eq_intCast_of_coe_eq {y : A'} {m : ℤ} (h : (y : L) = m) : red' y = m := by
  have hy : y = (m : A') := Subtype.ext (by rw [h]; rfl)
  rw [hy, map_intCast]

theorem red_eq_zero_of_coe_eq {y : A'} (h : (y : L) = 0) : red' y = 0 := by
  have hy : y = 0 := Subtype.ext h
  rw [hy, map_zero]

theorem coeffRed_constSeries (x : A') :
    coeffRed A' red' ⟨constSeries A' x, constSeries_mem_integralCoeffs A' x⟩
      = algebraMap k (LaurentSeries k) (red' x) := by
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  have hc : ∀ m : ℤ, (constSeries A' x).coeff m = (HahnSeries.single 0 (x : L)).coeff m := by
    intro m
    show (algebraMap L (LaurentSeries L) (x : L)).coeff m = _
    rw [algebraMap_laurentSeries_eq_single]
  split_ifs with h0
  · congr 1
    apply Subtype.ext
    show (constSeries A' x).coeff n = x
    rw [hc, h0, HahnSeries.coeff_single_same]
  · apply red_eq_zero_of_coe_eq A' red'
    show (constSeries A' x).coeff n = 0
    rw [hc, HahnSeries.coeff_single_of_ne h0]

theorem coeffRed_jqModC :
    coeffRed A' red' ⟨jqModC L, jqModC_mem_integralCoeffs A'⟩ = jqModC k := by
  ext n
  rw [coeffRed_coeff]
  have hL : (jqModC L).coeff n = (((jqModC ℤ).coeff n : ℤ) : L) := by
    rw [jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]
    rfl
  have hk : (jqModC k).coeff n = (((jqModC ℤ).coeff n : ℤ) : k) := by
    rw [jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
    rfl
  rw [hk]
  exact red_eq_intCast_of_coe_eq A' red' hL

theorem coeffRed_jqNModC :
    coeffRed A' red' ⟨jqNModC L N, jqNModC_mem_integralCoeffs N A'⟩ = jqNModC k N := by
  ext n
  rw [coeffRed_coeff]
  by_cases hn : ((N : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    have hL : (jqNModC L N).coeff ((N : ℤ) * m) = (((jqModC ℤ).coeff m : ℤ) : L) := by
      show (qExpand L N (jqModC L)).coeff ((N : ℤ) * m) = _
      rw [qExpand_coeff_mul, jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]
      rfl
    have hk : (jqNModC k N).coeff ((N : ℤ) * m) = (((jqModC ℤ).coeff m : ℤ) : k) := by
      show (qExpand k N (jqModC k)).coeff ((N : ℤ) * m) = _
      rw [qExpand_coeff_mul, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
      rfl
    rw [hk]
    exact red_eq_intCast_of_coe_eq A' red' hL
  · have hk : (jqNModC k N).coeff n = 0 := qExpand_coeff_of_not_dvd _ _ hn
    rw [hk]
    exact red_eq_zero_of_coe_eq A' red'
      (show (jqNModC L N).coeff n = 0 from qExpand_coeff_of_not_dvd _ _ hn)

theorem jqModC_coeff_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have h : (jqModC K).coeff (-1) = (((jqModC ℤ).coeff (-1) : ℤ) : K) := by
    rw [jqModC_eq_map_intCast (K := K), HahnSeries.map_coeff]
    rfl
  have hQ : (jqModC ℚ).coeff (-1) = (((jqModC ℤ).coeff (-1) : ℤ) : ℚ) := by
    rw [jqModC_eq_map_intCast (K := ℚ), HahnSeries.map_coeff]
    rfl
  have hZ : (jqModC ℤ).coeff (-1) = 1 := by
    have := coeff_jq_neg_one
    rw [← jqModC_rat, hQ] at this
    exact_mod_cast this
  rw [h, hZ, Int.cast_one]

theorem jqModC_ne_zero (K : Type*) [CommRing K] [Nontrivial K] : jqModC K ≠ 0 := fun h => by
  simpa [h] using jqModC_coeff_neg_one K

end Generic

variable {k : Type*} [Field k] (red : A →+* k)

abbrev redS : A.toSubring →+* k := red

abbrev O : Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  modularLocalized N A.toSubring (redS A red)

abbrev π₀ : O N A red →+* LaurentSeries k :=
  modularRedLocHom N A.toSubring (redS A red)

theorem mem_O_of_mem_modularRing {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ modularRing N A.toSubring) : x ∈ O N A red :=
  subring_le_localizedAtKer _ _ _ _ hx

theorem pi0_congr {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ O N A red)
    (hy : y ∈ O N A red) (h : x = y) : π₀ N A red ⟨x, hx⟩ = π₀ N A red ⟨y, hy⟩ := by
  subst h
  rfl

theorem pi0_of_mem_modularRing {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ modularRing N A.toSubring) (hxO : x ∈ O N A red) :
    π₀ N A red ⟨x, hxO⟩
      = coeffRed A.toSubring (redS A red) ⟨x, modularRing_le_integralCoeffs N A.toSubring hx⟩ :=
  redLoc_coe (A := A.toSubring) (red := redS A red) (R := modularRing N A.toSubring)
    (hR := modularRing_le_integralCoeffs N A.toSubring) ⟨x, hx⟩

theorem pi0_constSeries (a : A) (hO : constSeries A.toSubring ⟨a, a.2⟩ ∈ O N A red) :
    π₀ N A red ⟨constSeries A.toSubring ⟨a, a.2⟩, hO⟩ = algebraMap k (LaurentSeries k) (red a) := by
  rw [pi0_of_mem_modularRing N A red (constSeries_mem_modularRing N A.toSubring ⟨a, a.2⟩),
    coeffRed_constSeries]
  rfl

theorem pi0_jqModC (hO : jqModC (AlgebraicClosure ℚ) ∈ O N A red) :
    π₀ N A red ⟨jqModC (AlgebraicClosure ℚ), hO⟩ = jqModC k := by
  rw [pi0_of_mem_modularRing N A red (jqModC_mem_modularRing N A.toSubring), coeffRed_jqModC]

theorem pi0_jqNModC (hO : jqNModC (AlgebraicClosure ℚ) N ∈ O N A red) :
    π₀ N A red ⟨jqNModC (AlgebraicClosure ℚ) N, hO⟩ = jqNModC k N := by
  rw [pi0_of_mem_modularRing N A red (jqNModC_mem_modularRing N A.toSubring), coeffRed_jqNModC]

theorem jqModC_inv_mem_O : (jqModC (AlgebraicClosure ℚ))⁻¹ ∈ O N A red := by
  refine (mem_localizedAtKer _ _ _ _).2
    ⟨1, ⟨jqModC _, jqModC_mem_modularRing N A.toSubring⟩, ?_, ?_⟩
  · rw [notMem_redKer_iff, redRes_apply]
    show coeffRed A.toSubring (redS A red) ⟨jqModC _, _⟩ ≠ 0
    rw [coeffRed_jqModC]
    exact jqModC_ne_zero k
  · show (jqModC (AlgebraicClosure ℚ))⁻¹ * jqModC (AlgebraicClosure ℚ) = ((1 : modularRing N A.toSubring) : LaurentSeries _)
    rw [inv_mul_cancel₀ (jqModC_ne_zero _), OneMemClass.coe_one]

theorem pi0_jqModC_inv :
    π₀ N A red ⟨(jqModC (AlgebraicClosure ℚ))⁻¹, jqModC_inv_mem_O N A red⟩ = (jqModC k)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pi0_jqModC N A red (mem_O_of_mem_modularRing N A red (jqModC_mem_modularRing N A.toSubring)),
    ← map_mul]
  convert (π₀ N A red).map_one
  apply Subtype.ext
  show (jqModC (AlgebraicClosure ℚ))⁻¹ * jqModC (AlgebraicClosure ℚ) = 1
  exact inv_mul_cancel₀ (jqModC_ne_zero _)

variable (B : Subring (FF N))

def toSeries : B →+* LaurentSeries (AlgebraicClosure ℚ) :=
  (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp B.subtype

theorem toSeries_apply (b : B) :
    toSeries N B b = ((b : FF N) : LaurentSeries (AlgebraicClosure ℚ)) := rfl

theorem pi0_mem (f : O N A red) : π₀ N A red f ∈ modularFunctionFieldC k N :=
  modularRedLocHom_mem A.toSubring (redS A red) N f

variable (hBO : ∀ b : B, toSeries N B b ∈ O N A red)

def piChart : B →+* modularFunctionFieldC k N :=
  ((π₀ N A red).codRestrict (modularFunctionFieldC k N) (pi0_mem N A red)).comp
    ((toSeries N B).codRestrict (O N A red) hBO)

theorem coe_piChart_apply (b : B) :
    ((piChart N A red B hBO b : modularFunctionFieldC k N) : LaurentSeries k)
      = π₀ N A red ⟨toSeries N B b, hBO b⟩ := rfl

theorem piChart_constantsHom (hc : ∀ a : A, constantsHom N A a ∈ B) (a : A) :
    piChart N A red B hBO ⟨constantsHom N A a, hc a⟩
      = algebraMap k (modularFunctionFieldC k N) (red a) := by
  apply Subtype.ext
  rw [coe_piChart_apply]
  exact pi0_constSeries N A red a _

theorem piChart_constantsHom_eq_zero (hc : ∀ a : A, constantsHom N A a ∈ B) {a : A}
    (ha : red a = 0) : piChart N A red B hBO ⟨constantsHom N A a, hc a⟩ = 0 := by
  rw [piChart_constantsHom, ha, map_zero]

theorem piChart_jBar (hj : jBar N ∈ B) :
    piChart N A red B hBO ⟨jBar N, hj⟩ = ⟨jqModC k, jqModC_mem k N⟩ := by
  apply Subtype.ext
  rw [coe_piChart_apply, pi0_congr N A red (hBO ⟨jBar N, hj⟩)
    (mem_O_of_mem_modularRing N A red (jqModC_mem_modularRing N A.toSubring))
    (show toSeries N B ⟨jBar N, hj⟩ = jqModC (AlgebraicClosure ℚ) from coe_jBar N)]
  exact pi0_jqModC N A red _

theorem piChart_jNBar (hjN : jNBar N ∈ B) :
    piChart N A red B hBO ⟨jNBar N, hjN⟩ = ⟨jqNModC k N, jqNModC_mem k N⟩ := by
  apply Subtype.ext
  rw [coe_piChart_apply, pi0_congr N A red (hBO ⟨jNBar N, hjN⟩)
    (mem_O_of_mem_modularRing N A red (jqNModC_mem_modularRing N A.toSubring))
    (show toSeries N B ⟨jNBar N, hjN⟩ = jqNModC (AlgebraicClosure ℚ) N from coe_jNBar N)]
  exact pi0_jqNModC N A red _

theorem coe_jBar_inv : (((jBar N)⁻¹ : FF N) : LaurentSeries (AlgebraicClosure ℚ))
    = (jqModC (AlgebraicClosure ℚ))⁻¹ := by
  rw [IntermediateField.coe_inv, coe_jBar]

theorem piChart_jBar_inv (hj : (jBar N)⁻¹ ∈ B) :
    piChart N A red B hBO ⟨(jBar N)⁻¹, hj⟩
      = (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹ := by
  apply Subtype.ext
  rw [coe_piChart_apply, pi0_congr N A red (hBO ⟨(jBar N)⁻¹, hj⟩) (jqModC_inv_mem_O N A red)
    (show toSeries N B ⟨(jBar N)⁻¹, hj⟩ = (jqModC (AlgebraicClosure ℚ))⁻¹ from coe_jBar_inv N),
    IntermediateField.coe_inv]
  exact pi0_jqModC_inv N A red

section WithData

variable (data : ModularPolynomialData N)
variable (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
  (modularFunctionFieldC k N) = dedekindPsi N)

def finToO : affineBaseFin N A →+* O N A red :=
  (toSeries N (affineBaseFin N A)).codRestrict (O N A red) fun x =>
    mem_O_of_mem_modularRing N A red (coe_mem_modularRing_of_mem_affineBaseFin N A x.2)

theorem coe_mem_O_of_mem_affineBaseInf {x : FF N} (hx : x ∈ affineBaseInf N A) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ O N A red := by
  have : affineBaseInf N A ≤ (O N A red).comap
      (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))) := by
    rw [affineBaseInf, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl) <;> rw [SetLike.mem_coe, Subring.mem_comap]
    · show ((constantsHom N A a : FF N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ O N A red
      rw [coe_constantsHom]
      exact mem_O_of_mem_modularRing N A red (constSeries_mem_modularRing N A.toSubring _)
    · show (((jBar N)⁻¹ : FF N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ O N A red
      rw [coe_jBar_inv]
      exact jqModC_inv_mem_O N A red
  exact this hx

def infToO : affineBaseInf N A →+* O N A red :=
  (toSeries N (affineBaseInf N A)).codRestrict (O N A red) fun x =>
    coe_mem_O_of_mem_affineBaseInf N A red x.2

include data hdeg in

theorem hBO_Fin (b : BFin N A) : toSeries N (BFin N A) b ∈ O N A red := by
  obtain ⟨p, hp, hev⟩ := b.2
  refine mem_modularLocalized_of_eval2_monic A (redS A red) N data hdeg
    (coe_mem_modularFunctionFieldC N (b : FF N)) (hp.map (finToO N A red)) ?_
  rw [eval₂_map]
  have : (O N A red).subtype.comp (finToO N A red)
      = (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp (affineBaseFin N A).subtype :=
    RingHom.ext fun _ => rfl
  have hev' : eval₂ (affineBaseFin N A).subtype ((b : BFin N A) : FF N) p = 0 := hev
  rw [this, toSeries_apply, show (((b : BFin N A) : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ)) (b : FF N) from rfl,
    ← hom_eval₂, hev', map_zero]

include data hdeg in

theorem hBO_Inf (b : BInf N A) : toSeries N (BInf N A) b ∈ O N A red := by
  obtain ⟨p, hp, hev⟩ := b.2
  refine mem_modularLocalized_of_eval2_monic A (redS A red) N data hdeg
    (coe_mem_modularFunctionFieldC N (b : FF N)) (hp.map (infToO N A red)) ?_
  rw [eval₂_map]
  have : (O N A red).subtype.comp (infToO N A red)
      = (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp (affineBaseInf N A).subtype :=
    RingHom.ext fun _ => rfl
  have hev' : eval₂ (affineBaseInf N A).subtype ((b : BInf N A) : FF N) p = 0 := hev
  rw [this, toSeries_apply, show (((b : BInf N A) : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ)) (b : FF N) from rfl,
    ← hom_eval₂, hev', map_zero]

abbrev piFin : BFin N A →+* modularFunctionFieldC k N :=
  piChart N A red (BFin N A) (hBO_Fin N A red data hdeg)

abbrev piInf : BInf N A →+* modularFunctionFieldC k N :=
  piChart N A red (BInf N A) (hBO_Inf N A red data hdeg)

end WithData

theorem coe_tBar :
    ((jNBar N * ((jBar N)⁻¹) ^ N : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      = jqNModC (AlgebraicClosure ℚ) N * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ N := by
  rw [IntermediateField.coe_mul, IntermediateField.coe_pow, coe_jBar_inv, coe_jNBar]

def intPolyToInf : Polynomial ℤ →+* affineBaseInf N A :=
  eval₂RingHom (Int.castRingHom _) ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩

theorem algebraMap_comp_subtype_comp_intPolyToInf :
    ((algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp (affineBaseInf N A).subtype).comp
        (intPolyToInf N A)
      = eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
          (jqModC (AlgebraicClosure ℚ))⁻¹ := by
  refine Polynomial.ringHom_ext (fun a => by simp [intPolyToInf]) ?_
  simp only [RingHom.comp_apply, intPolyToInf, coe_eval₂RingHom, eval₂_X]
  exact coe_jBar_inv N

theorem tBar_mem (data : ModularPolynomialData N)
    (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i)) :
    jNBar N * ((jBar N)⁻¹) ^ N ∈ BInf N A := by
  obtain ⟨Q, hQ, -, hroot⟩ := ModularCurve.CharPModel.exists_monic_eval2_inv_mul_inv_pow_eq_zero
    (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) data.Φ data.monic N
    (fun i _ => by rw [data.natDegree_eq]; exact hdegX i) (jqModC_ne_zero _)
    (jqNModC (AlgebraicClosure ℚ) N) (eval₂_Phi_jqModC N data)
  refine (mem_BInf_iff N A).2 ⟨Q.map (intPolyToInf N A), hQ.map _, ?_⟩
  apply (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).injective
  rw [map_zero, hom_eval₂, eval₂_map, algebraMap_comp_subtype_comp_intPolyToInf]
  show Q.eval₂ _ ((jNBar N * ((jBar N)⁻¹) ^ N : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = 0
  rw [coe_tBar]
  exact hroot

theorem piChart_tBar (ht : jNBar N * ((jBar N)⁻¹) ^ N ∈ B) :
    piChart N A red B hBO ⟨jNBar N * ((jBar N)⁻¹) ^ N, ht⟩
      = (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) *
          ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹ ^ N := by
  have hmemN : jqNModC (AlgebraicClosure ℚ) N ∈ O N A red :=
    mem_O_of_mem_modularRing N A red (jqNModC_mem_modularRing N A.toSubring)
  have hmemI := jqModC_inv_mem_O N A red
  have helt : (⟨toSeries N B ⟨_, ht⟩, hBO ⟨_, ht⟩⟩ : O N A red)
      = ⟨jqNModC (AlgebraicClosure ℚ) N, hmemN⟩ * ⟨(jqModC (AlgebraicClosure ℚ))⁻¹, hmemI⟩ ^ N := by
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_pow]
    exact coe_tBar N
  apply Subtype.ext
  rw [coe_piChart_apply, helt, map_mul, map_pow, pi0_jqNModC, pi0_jqModC_inv,
    IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_inv]

section Frac

variable (hred : Function.Surjective red) (data : ModularPolynomialData N)
variable (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
  (modularFunctionFieldC k N) = dedekindPsi N)

include hred in
theorem algebraMap_mem_closure_range (hc : ∀ a : A, constantsHom N A a ∈ B) (c : k) :
    algebraMap k (modularFunctionFieldC k N) c
      ∈ Subfield.closure ((piChart N A red B hBO).range : Set (modularFunctionFieldC k N)) := by
  obtain ⟨a, rfl⟩ := hred c
  exact Subfield.subset_closure ⟨⟨constantsHom N A a, hc a⟩, piChart_constantsHom N A red B hBO hc a⟩

include hred in

theorem frac_Fin : ∀ x : modularFunctionFieldC k N, ∃ b c : BFin N A,
    piFin N A red data hdeg c ≠ 0 ∧ x * piFin N A red data hdeg c = piFin N A red data hdeg b := by
  refine CharpS10bB.exists_mul_eq_of_adjoin {jqModC k, jqNModC k N} (piFin N A red data hdeg)
    (algebraMap_mem_closure_range N A red _ _ hred (constFin_mem N A)) ?_
  rintro s (rfl | rfl)
  · exact Subfield.subset_closure
      ⟨⟨jBar N, jBar_mem N A⟩, piChart_jBar N A red _ _ (jBar_mem N A)⟩
  · exact Subfield.subset_closure
      ⟨⟨jNBar N, jNBar_mem N A data⟩, piChart_jNBar N A red _ _ (jNBar_mem N A data)⟩

include hred in

theorem frac_Inf (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i)) :
    ∀ x : modularFunctionFieldC k N, ∃ b c : BInf N A,
    piInf N A red data hdeg c ≠ 0 ∧ x * piInf N A red data hdeg c = piInf N A red data hdeg b := by
  refine CharpS10bB.exists_mul_eq_of_forall_mem_closure_range (piInf N A red data hdeg)
    (CharpS10bB.forall_mem_closure_range_of_adjoin {jqModC k, jqNModC k N} (piInf N A red data hdeg)
      (algebraMap_mem_closure_range N A red _ _ hred (constInf_mem N A)) ?_)
  set T := Subfield.closure ((piInf N A red data hdeg).range : Set (modularFunctionFieldC k N)) with hT
  have hjinv : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹ ∈ T :=
    Subfield.subset_closure ⟨⟨(jBar N)⁻¹, jInvBar_mem N A⟩, piChart_jBar_inv N A red _ _ (jInvBar_mem N A)⟩
  have hj : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ T := by
    rw [← inv_inv (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)]
    exact T.inv_mem hjinv
  have ht : (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) *
      ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹ ^ N ∈ T :=
    Subfield.subset_closure ⟨⟨_, tBar_mem N A data hdegX⟩, piChart_tBar N A red _ _ (tBar_mem N A data hdegX)⟩
  have hjne : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ≠ 0 := fun h =>
    jqModC_ne_zero k (congrArg Subtype.val h)
  have hjN : (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ∈ T := by
    have : (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)
        = (⟨jqNModC k N, jqNModC_mem k N⟩ * (⟨jqModC k, jqModC_mem k N⟩)⁻¹ ^ N) *
            (⟨jqModC k, jqModC_mem k N⟩) ^ N := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hjne, one_pow, mul_one]
    rw [this]
    exact T.mul_mem ht (T.pow_mem hj N)
  rintro s (rfl | rfl)
  · exact hj
  · exact hjN

end Frac

section Down

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem exists_bivariate_of_isIntegral_subring (R' : Subring E) (g : E)
    (hconst : ∀ c : K, algebraMap K E c ∈ R') (hg : g ∈ R')
    (hR' : ∀ r : R', IsIntegral (Algebra.adjoin K ({g} : Set E)) (r : E))
    {x : E} (hx : ∃ p : Polynomial R', p.Monic ∧ Polynomial.eval₂ R'.subtype x p = 0) :
    ∃ P : Polynomial (Polynomial K), P.Monic ∧
      Polynomial.eval₂ (eval₂RingHom (algebraMap K E) g) x P = 0 := by
  set T : Subalgebra K E := Algebra.adjoin K ({g} : Set E) with hTdef
  have hTR : ∀ t : T, (t : E) ∈ R' := fun t => by
    have ht : (t : E) ∈ Subring.closure (Set.range (algebraMap K E) ∪ {g}) :=
      Algebra.mem_adjoin_iff.1 t.2
    refine (Subring.closure_le.2 ?_) ht
    rintro _ (⟨c, rfl⟩ | rfl)
    · exact hconst c
    · exact hg
  letI : Algebra T R' := ((T.val : T →+* E).codRestrict R' hTR).toAlgebra
  haveI : IsScalarTower T R' E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral T R' := ⟨fun r =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom T R' E) Subtype.val_injective).1 (hR' r)⟩
  have hxR : IsIntegral R' x := hx
  obtain ⟨p', hp'm, hp'e⟩ := (isIntegral_trans x hxR : IsIntegral T x)

  let gT : T := ⟨g, Algebra.subset_adjoin rfl⟩
  let f : Polynomial K →+* T := (Polynomial.aeval gT).toRingHom
  have hfE : (algebraMap T E).comp f = eval₂RingHom (algebraMap K E) g := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp [f]
    · simp [f, gT]
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨q, hq⟩ : (t : E) ∈ (Polynomial.aeval (R := K) g).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact t.2
    refine ⟨q, Subtype.ext ?_⟩
    show (algebraMap T E).comp f q = t
    rw [hfE]
    exact hq
  obtain ⟨P, hPmap, -, hPmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective f hf p')) hp'm
  refine ⟨P, hPmonic, ?_⟩
  rw [← hfE, ← eval₂_map, hPmap]
  exact hp'e

end Down

section IntClosed

variable (data : ModularPolynomialData N)
variable (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
  (modularFunctionFieldC k N) = dedekindPsi N)

theorem exists_coe_eq_of_mem_O {f : LaurentSeries (AlgebraicClosure ℚ)} (hf : f ∈ O N A red) :
    ∃ b : FF N, (b : LaurentSeries (AlgebraicClosure ℚ)) = f := by
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).1 hf
  have hR : modularRing N A.toSubring ≤ (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).range := by
    rw [modularRing, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl | rfl)
    · exact ⟨constantsHom N A ⟨a, a.2⟩, coe_constantsHom N A _⟩
    · exact ⟨jBar N, coe_jBar N⟩
    · exact ⟨jNBar N, coe_jNBar N⟩
  obtain ⟨r', hr'⟩ := hR r.2
  obtain ⟨s', hs'⟩ := hR s.2
  have hs0 : (s : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply (notMem_redKer_iff _ _ _ _).1 hs
    have : s = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hr'' : ((r' : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = r := hr'
  have hs'' : ((s' : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = s := hs'
  refine ⟨r' / s', ?_⟩
  rw [IntermediateField.coe_div, hr'', hs'']
  exact ((eq_div_iff hs0).2 hfs).symm

def basePoly (base : Subring (FF N)) (hc : ∀ a : A, constantsHom N A a ∈ base) (g : base) :
    Polynomial A →+* base :=
  eval₂RingHom ((constantsHom N A).codRestrict base hc) g

theorem algebraMap_comp_subtype_comp_basePoly (base : Subring (FF N))
    (hc : ∀ a : A, constantsHom N A a ∈ base) (g : base) :
    ((algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp base.subtype).comp
        (basePoly N A base hc g)
      = eval₂RingHom ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          ((g : FF N) : LaurentSeries (AlgebraicClosure ℚ)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, basePoly, coe_eval₂RingHom, eval₂_C]
    rfl
  · simp only [RingHom.comp_apply, basePoly, coe_eval₂RingHom, eval₂_X]
    rfl

theorem exists_mem_of_lift (base B : Subring (FF N)) (hbase : ∀ x : FF N, x ∈ B ↔
      ∃ p : Polynomial base, p.Monic ∧ Polynomial.eval₂ base.subtype x p = 0)
    (hc : ∀ a : A, constantsHom N A a ∈ base) (g : base)
    {f : LaurentSeries (AlgebraicClosure ℚ)} (hfO : f ∈ O N A red)
    (hP : ∃ P : Polynomial (Polynomial A), P.Monic ∧
      Polynomial.eval₂ (eval₂RingHom
        ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
        ((g : FF N) : LaurentSeries (AlgebraicClosure ℚ))) f P = 0) :
    ∃ b : B, ((b : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = f := by
  obtain ⟨b, hb⟩ := exists_coe_eq_of_mem_O N A red hfO
  obtain ⟨P, hPm, hPe⟩ := hP
  refine ⟨⟨b, (hbase b).2 ⟨P.map (basePoly N A base hc g), hPm.map _, ?_⟩⟩, hb⟩
  apply (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).injective
  rw [map_zero, hom_eval₂, eval₂_map, algebraMap_comp_subtype_comp_basePoly]
  show P.eval₂ _ ((b : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = 0
  rw [hb]
  exact hPe

theorem isIntegral_adjoin_of_mem_range (base B : Subring (FF N)) (hbB : base ≤ B)
    (hB : ∀ b : B, ∃ p : Polynomial base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : FF N) p = 0)
    (hc : ∀ a : A, constantsHom N A a ∈ base) (g : base)
    (hgen : base ≤ Subring.closure (Set.range (constantsHom N A) ∪ {(g : FF N)}))
    (hBO : ∀ b : B, toSeries N B b ∈ O N A red) (r : (piChart N A red B hBO).range) :
    IsIntegral (Algebra.adjoin k ({(piChart N A red B hBO ⟨g, hbB g.2⟩ : modularFunctionFieldC k N)} :
      Set (modularFunctionFieldC k N))) (r : modularFunctionFieldC k N) := by
  obtain ⟨b, hb⟩ := RingHom.mem_range.1 r.2
  rw [← hb]
  set π := piChart N A red B hBO with hπ
  set gk : modularFunctionFieldC k N := π ⟨g, hbB g.2⟩ with hgk
  set T : Subalgebra k (modularFunctionFieldC k N) := Algebra.adjoin k ({gk} : Set _) with hT
  obtain ⟨p, hpm, hpe⟩ := hB b

  have hbaseT : ∀ x : base, π ⟨x, hbB x.2⟩ ∈ T := by
    intro x
    have hx : (x : FF N) ∈ Subring.closure (Set.range (constantsHom N A) ∪ {(g : FF N)}) := hgen x.2
    have key : Subring.closure (Set.range (constantsHom N A) ∪ {(g : FF N)})
        ≤ (T.toSubring.comap π).map B.subtype := by
      rw [Subring.closure_le]
      rintro y (⟨a, rfl⟩ | rfl)
      · refine ⟨⟨constantsHom N A a, hbB (hc a)⟩, ?_, rfl⟩
        show π ⟨constantsHom N A a, hbB (hc a)⟩ ∈ T
        rw [hπ, piChart_constantsHom N A red B hBO (fun a => hbB (hc a)) a]
        exact T.algebraMap_mem _
      · exact ⟨⟨g, hbB g.2⟩, Algebra.subset_adjoin rfl, rfl⟩
    obtain ⟨x', hx', hxx⟩ := key hx
    have : x' = ⟨x, hbB x.2⟩ := Subtype.ext hxx
    rw [← this]
    exact hx'
  let φ : base →+* T := (π.comp (Subring.inclusion hbB)).codRestrict T.toSubring
    (fun x => by
      show π ⟨x, hbB x.2⟩ ∈ T
      exact hbaseT x)
  refine ⟨p.map φ, hpm.map φ, ?_⟩
  rw [eval₂_map]
  have hcomp : (algebraMap T (modularFunctionFieldC k N)).comp φ = π.comp (Subring.inclusion hbB) :=
    RingHom.ext fun _ => rfl
  rw [hcomp]
  show Polynomial.eval₂ (π.comp (Subring.inclusion hbB)) (π b) p = 0
  rw [← hom_eval₂]
  have hev : Polynomial.eval₂ (Subring.inclusion hbB) b p = 0 := by
    apply Subtype.val_injective
    show ((Polynomial.eval₂ (Subring.inclusion hbB) b p : B) : FF N) = ((0 : B) : FF N)
    rw [show ((Polynomial.eval₂ (Subring.inclusion hbB) b p : B) : FF N)
        = B.subtype (Polynomial.eval₂ (Subring.inclusion hbB) b p) from rfl, hom_eval₂]
    exact hpe
  rw [hev, map_zero]

theorem intClosed_chart (base B : Subring (FF N)) (hbB : base ≤ B)
    (hbase : ∀ x : FF N, x ∈ B ↔
      ∃ p : Polynomial base, p.Monic ∧ Polynomial.eval₂ base.subtype x p = 0)
    (hc : ∀ a : A, constantsHom N A a ∈ base) (g : base)
    (hgen : base ≤ Subring.closure (Set.range (constantsHom N A) ∪ {(g : FF N)}))
    (hBO : ∀ b : B, toSeries N B b ∈ O N A red) (hred : Function.Surjective red)
    (y₀ : LaurentSeries k)
    (hy₀ : ((piChart N A red B hBO ⟨g, hbB g.2⟩ : modularFunctionFieldC k N) : LaurentSeries k) = y₀)
    (g₀ : LaurentSeries (AlgebraicClosure ℚ)) (hg₀ : ((g : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = g₀)
    (hlift : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) y₀) y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            g₀) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y) :
    ∀ x : modularFunctionFieldC k N,
      (∃ p : Polynomial (piChart N A red B hBO).range, p.Monic ∧
        Polynomial.eval₂ (piChart N A red B hBO).range.subtype x p = 0) →
      x ∈ (piChart N A red B hBO).range := by
  subst hg₀
  intro x hx
  set π := piChart N A red B hBO with hπ

  obtain ⟨P, hPm, hPe⟩ := exists_bivariate_of_isIntegral_subring (K := k) π.range (π ⟨g, hbB g.2⟩)
    (fun c => by
      obtain ⟨a, rfl⟩ := hred c
      exact ⟨⟨constantsHom N A a, hbB (hc a)⟩, piChart_constantsHom N A red B hBO (fun a => hbB (hc a)) a⟩)
    ⟨_, rfl⟩
    (isIntegral_adjoin_of_mem_range N A red base B hbB (fun b => (hbase b).1 b.2) hc g hgen hBO) hx
  have hPe' : Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) y₀)
      (x : LaurentSeries k) P = 0 := by
    have h := congrArg (algebraMap (modularFunctionFieldC k N) (LaurentSeries k)) hPe
    rw [map_zero, hom_eval₂] at h
    have hring : (algebraMap (modularFunctionFieldC k N) (LaurentSeries k)).comp
          (eval₂RingHom (algebraMap k (modularFunctionFieldC k N)) (π ⟨g, hbB g.2⟩))
        = Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) y₀ := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · simp
      · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
        exact hy₀
    rwa [hring] at h

  obtain ⟨f, hfP, hfy⟩ := hlift (x : LaurentSeries k) x.2 ⟨P, hPm, hPe'⟩

  obtain ⟨b, hb⟩ := exists_mem_of_lift N A red base B hbase hc g f.2 hfP
  refine ⟨b, Subtype.ext ?_⟩
  rw [hπ, coe_piChart_apply, pi0_congr N A red (hBO b) f.2 hb]
  exact hfy

end IntClosed

section Assembly

variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
variable (data : ModularPolynomialData N)
variable (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
  (modularFunctionFieldC k N) = dedekindPsi N)

theorem affineBaseFin_le_closure_jBar :
    affineBaseFin N A ≤ Subring.closure (Set.range (constantsHom N A) ∪
      {((⟨jBar N, jBar_mem_affineBaseFin N A⟩ : affineBaseFin N A) : FF N)}) :=
  le_rfl

theorem affineBaseInf_le_closure_jBar_inv :
    affineBaseInf N A ≤ Subring.closure (Set.range (constantsHom N A) ∪
      {((⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ : affineBaseInf N A) : FF N)}) :=
  le_rfl

theorem exists_fibreModel_cuspChart_of_ker (hred : Function.Surjective red)
    (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
    (hliftFin : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k))
          y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y)
    (hliftInf : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k)⁻¹)
          y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y)
    (hkerFin : RingHom.ker (piFin N A red data hdeg) =
      Ideal.span ((fun a : A => (⟨constantsHom N A a, constFin_mem N A a⟩ : BFin N A)) ''
        (IsLocalRing.maximalIdeal A : Set A)))
    (hkerInf : RingHom.ker (piInf N A red data hdeg) =
      Ideal.span ((fun a : A => (⟨constantsHom N A a, constInf_mem N A a⟩ : BInf N A)) ''
        (IsLocalRing.maximalIdeal A : Set A))) :
    ∃ fm : FibreModel N A ℓ k red, fm.CuspChart ∧ IsIntegrallyClosed fm.BFin ∧ IsIntegrallyClosed fm.BInf := by
  exact ⟨{
    BFin := BFin N A
    BInf := BInf N A
    constFin_mem := constFin_mem N A
    constInf_mem := constInf_mem N A
    jBar_mem := jBar_mem N A
    jNBar_mem := jNBar_mem N A data
    jInvBar_mem := jInvBar_mem N A
    integralFin := integralFin N A
    integralInf := integralInf N A
    piFin := piFin N A red data hdeg
    piInf := piInf N A red data hdeg
    piFin_const := piChart_constantsHom N A red _ _ (constFin_mem N A)
    piInf_const := piChart_constantsHom N A red _ _ (constInf_mem N A)
    piFin_j := piChart_jBar N A red _ _ (jBar_mem N A)
    piFin_jN := piChart_jNBar N A red _ _ (jNBar_mem N A data)
    piInf_jInv := piChart_jBar_inv N A red _ _ (jInvBar_mem N A)
    ker_piFin := hkerFin
    ker_piInf := hkerInf
    intClosed_piFin := intClosed_chart N A red (affineBaseFin N A) (BFin N A)
      (affineBaseFin_le_BFin N A) (fun x => mem_BFin_iff N A)
      (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩)) ⟨jBar N, jBar_mem_affineBaseFin N A⟩
      (affineBaseFin_le_closure_jBar N A) (hBO_Fin N A red data hdeg) hred (jqModC k)
      (congrArg Subtype.val (piChart_jBar N A red _ _ (jBar_mem N A)))
      (jqModC (AlgebraicClosure ℚ)) (coe_jBar N) hliftFin
    intClosed_piInf := intClosed_chart N A red (affineBaseInf N A) (BInf N A)
      (affineBaseInf_le_BInf N A) (fun x => mem_BInf_iff N A)
      (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩)) ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩
      (affineBaseInf_le_closure_jBar_inv N A) (hBO_Inf N A red data hdeg) hred (jqModC k)⁻¹
      ((congrArg Subtype.val (piChart_jBar_inv N A red _ _ (jInvBar_mem N A))).trans
        (IntermediateField.coe_inv _ _))
      (jqModC (AlgebraicClosure ℚ))⁻¹ (coe_jBar_inv N) hliftInf
    frac_piFin := frac_Fin N A red hred data hdeg
    frac_piInf := frac_Inf N A red hred data hdeg hdegX },
    { tBar_mem := tBar_mem N A data hdegX
      piInf_t := piChart_tBar N A red _ _ (tBar_mem N A data hdegX) },
    instIsIntegrallyClosed_BFin N A, instIsIntegrallyClosed_BInf N A⟩

end Assembly

end Model
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB.Model"

namespace Model

p2m_open "ModularCurve~coeffMap_qExpand ModularCurve.CharPModel ModularCurve.CharPReduction Polynomial"

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k]
  (red : A →+* k)

theorem valuationRing_toSubring (A' : ValuationSubring (AlgebraicClosure ℚ)) :
    ValuationRing A'.toSubring := by
  change ValuationRing A'
  infer_instance

attribute [local instance] valuationRing_toSubring

section KerChart

theorem const_mem_affineBaseFin (a : A) : constantsHom N A a ∈ affineBaseFin N A :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem const_mem_affineBaseInf (a : A) : constantsHom N A a ∈ affineBaseInf N A :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

def constO : A →+* O N A red :=
  ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype).codRestrict
    (O N A red) fun a => mem_O_of_mem_modularRing N A red (constSeries_mem_modularRing N A.toSubring ⟨a, a.2⟩)

theorem pi0_constO (a : A) : π₀ N A red (constO N A red a) = algebraMap k (LaurentSeries k) (red a) :=
  pi0_constSeries N A red a _

theorem basePoly_surjective (base : Subring (FF N)) (hc : ∀ a : A, constantsHom N A a ∈ base) (g : base)
    (hgen : base ≤ Subring.closure (Set.range (constantsHom N A) ∪ {(g : FF N)})) :
    Function.Surjective (basePoly N A base hc g) := by
  intro x
  have hx : (x : FF N) ∈ ((basePoly N A base hc g).range).map base.subtype := by
    refine (show Subring.closure (Set.range (constantsHom N A) ∪ {(g : FF N)}) ≤ _ from ?_) (hgen x.2)
    rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    · refine ⟨basePoly N A base hc g (C a), ⟨C a, rfl⟩, ?_⟩
      show ((Polynomial.eval₂ _ _ (C a) : base) : FF N) = constantsHom N A a
      rw [eval₂_C]; rfl
    · refine ⟨basePoly N A base hc g X, ⟨X, rfl⟩, ?_⟩
      show ((Polynomial.eval₂ _ _ X : base) : FF N) = (g : FF N)
      rw [eval₂_X]
  obtain ⟨y, ⟨p, rfl⟩, hy⟩ := hx
  exact ⟨p, Subtype.ext hy⟩

theorem coe_basePoly (base : Subring (FF N)) (hc : ∀ a : A, constantsHom N A a ∈ base) (g : base)
    (p : Polynomial A) :
    (((basePoly N A base hc g p : base) : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      = p.eval₂ ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          ((g : FF N) : LaurentSeries (AlgebraicClosure ℚ)) := by
  have h := congrArg (fun f : Polynomial A →+* LaurentSeries (AlgebraicClosure ℚ) => f p)
    (algebraMap_comp_subtype_comp_basePoly N A base hc g)
  simpa using h

theorem basePoly_toO (base : Subring (FF N)) (hc : ∀ a : A, constantsHom N A a ∈ base) (g : base)
    (gO : O N A red) (hg : ((g : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = gO)
    (p : Polynomial A)
    (hbO : (((basePoly N A base hc g p : base) : FF N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ O N A red) :
    (⟨_, hbO⟩ : O N A red) = Polynomial.eval₂ (constO N A red) gO p := by
  apply Subtype.ext
  rw [show ((Polynomial.eval₂ (constO N A red) gO p : O N A red) : LaurentSeries (AlgebraicClosure ℚ))
      = (O N A red).subtype (Polynomial.eval₂ (constO N A red) gO p) from rfl, hom_eval₂]
  show (((basePoly N A base hc g p : base) : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = _
  rw [coe_basePoly, hg]
  rfl

end KerChart
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB.Model"

theorem toSeries_BFin_injective : Function.Injective (toSeries N (BFin N A)) := fun _ _ h =>
  Subtype.ext ((algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).injective h)

theorem toSeries_BInf_injective : Function.Injective (toSeries N (BInf N A)) := fun _ _ h =>
  Subtype.ext ((algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).injective h)

section SplitGlue

variable (data : ModularPolynomialData N)
variable (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
variable (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
  (modularFunctionFieldC k N) = dedekindPsi N)

theorem exists_bivariate_of_mem_BFin (b : BFin N A) :
    (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))) (toSeries N (BFin N A) b : LaurentSeries (AlgebraicClosure ℚ)) P = 0) := by
  obtain ⟨p, hpm, hpe⟩ := (mem_BFin_iff N A).1 b.2
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective _
      (basePoly_surjective N A (affineBaseFin N A) (const_mem_affineBaseFin N A)
        ⟨jBar N, jBar_mem_affineBaseFin N A⟩ le_rfl) p)) hpm
  refine ⟨P, hPm, ?_⟩
  have h := congrArg (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))) hpe
  rw [map_zero, hom_eval₂, ← hPmap, eval₂_map, algebraMap_comp_subtype_comp_basePoly,
    show (((⟨jBar N, jBar_mem_affineBaseFin N A⟩ : affineBaseFin N A) : FF N) :
      LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) from coe_jBar N] at h
  exact h

theorem exists_bivariate_of_mem_BInf (b : BInf N A) :
    (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (toSeries N (BInf N A) b : LaurentSeries (AlgebraicClosure ℚ)) P = 0) := by
  obtain ⟨p, hpm, hpe⟩ := (mem_BInf_iff N A).1 b.2
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective _
      (basePoly_surjective N A (affineBaseInf N A) (const_mem_affineBaseInf N A)
        ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ le_rfl) p)) hpm
  refine ⟨P, hPm, ?_⟩
  have h := congrArg (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))) hpe
  rw [map_zero, hom_eval₂, ← hPmap, eval₂_map, algebraMap_comp_subtype_comp_basePoly,
    show ((((⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ : affineBaseInf N A) : FF N)) :
      LaurentSeries (AlgebraicClosure ℚ)) = (jqModC (AlgebraicClosure ℚ))⁻¹ from coe_jBar_inv N] at h
  exact h

include hdeg in

theorem ker_piFin_eq_span_of_K (hred : Function.Surjective red)
    (HK : ∀ f : O N A red,
      (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) →
      modularRedLocHom N A.toSubring (redS A red) f = 0 →
      ∃ m : A, red m = 0 ∧ ∃ f' : O N A red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))) (f' : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ))
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (m : AlgebraicClosure ℚ)
            * (f' : LaurentSeries (AlgebraicClosure ℚ))) :
    RingHom.ker (piFin N A red data hdeg) =
      Ideal.span ((fun a : A => (⟨constantsHom N A a, constFin_mem N A a⟩ : BFin N A)) ''
        (IsLocalRing.maximalIdeal A : Set A)) := by
  have hkerA : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  apply le_antisymm
  · intro b hb
    have hb0 : piFin N A red data hdeg b = 0 := hb
    obtain ⟨m, hm, f', hf'int, hff'⟩ := HK ⟨toSeries N (BFin N A) b, hBO_Fin N A red data hdeg b⟩
      (exists_bivariate_of_mem_BFin N A b)
      (by
        have h := congrArg (fun y : modularFunctionFieldC k N => (y : LaurentSeries k)) hb0
        first | exact h | simpa only [ZeroMemClass.coe_zero] using h)
    obtain ⟨b', hb'⟩ := exists_mem_of_lift N A red (affineBaseFin N A) (BFin N A)
      (fun x => mem_BFin_iff N A) (const_mem_affineBaseFin N A) ⟨jBar N, jBar_mem_affineBaseFin N A⟩ f'.2
      (by
        obtain ⟨P, hPm, hPe⟩ := hf'int
        exact ⟨P, hPm, by
          rw [show (((⟨jBar N, jBar_mem_affineBaseFin N A⟩ : affineBaseFin N A) : FF N) :
            LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) from coe_jBar N]
          exact hPe⟩)
    have hbb : b = ⟨constantsHom N A m, constFin_mem N A m⟩ * b' := by
      apply toSeries_BFin_injective N A
      rw [map_mul]
      show toSeries N (BFin N A) b = ((constantsHom N A m : FF N) : LaurentSeries (AlgebraicClosure ℚ))
        * (((b' : BFin N A) : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      rw [coe_constantsHom, hb']
      exact hff'
    rw [hbb]
    refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨m, ?_, rfl⟩)
    show m ∈ IsLocalRing.maximalIdeal A
    rw [← hkerA]
    exact hm
  · rw [Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha0 : red a = 0 := by
      have : a ∈ RingHom.ker red := by rw [hkerA]; exact ha
      exact this
    show piFin N A red data hdeg ⟨constantsHom N A a, constFin_mem N A a⟩ = 0
    rw [piChart_constantsHom N A red _ _ (constFin_mem N A), ha0, map_zero]

include hdeg in

theorem ker_piInf_eq_span_of_K (hred : Function.Surjective red)
    (HK : ∀ f : O N A red,
      (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) →
      modularRedLocHom N A.toSubring (redS A red) f = 0 →
      ∃ m : A, red m = 0 ∧ ∃ f' : O N A red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (f' : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ))
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (m : AlgebraicClosure ℚ)
            * (f' : LaurentSeries (AlgebraicClosure ℚ))) :
    RingHom.ker (piInf N A red data hdeg) =
      Ideal.span ((fun a : A => (⟨constantsHom N A a, constInf_mem N A a⟩ : BInf N A)) ''
        (IsLocalRing.maximalIdeal A : Set A)) := by
  have hkerA : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  apply le_antisymm
  · intro b hb
    have hb0 : piInf N A red data hdeg b = 0 := hb
    obtain ⟨m, hm, f', hf'int, hff'⟩ := HK ⟨toSeries N (BInf N A) b, hBO_Inf N A red data hdeg b⟩
      (exists_bivariate_of_mem_BInf N A b)
      (by
        have h := congrArg (fun y : modularFunctionFieldC k N => (y : LaurentSeries k)) hb0
        first | exact h | simpa only [ZeroMemClass.coe_zero] using h)
    obtain ⟨b', hb'⟩ := exists_mem_of_lift N A red (affineBaseInf N A) (BInf N A)
      (fun x => mem_BInf_iff N A) (const_mem_affineBaseInf N A) ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ f'.2
      (by
        obtain ⟨P, hPm, hPe⟩ := hf'int
        exact ⟨P, hPm, by
          rw [show ((((⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ : affineBaseInf N A) : FF N)) :
            LaurentSeries (AlgebraicClosure ℚ)) = (jqModC (AlgebraicClosure ℚ))⁻¹ from coe_jBar_inv N]
          exact hPe⟩)
    have hbb : b = ⟨constantsHom N A m, constInf_mem N A m⟩ * b' := by
      apply toSeries_BInf_injective N A
      rw [map_mul]
      show toSeries N (BInf N A) b = ((constantsHom N A m : FF N) : LaurentSeries (AlgebraicClosure ℚ))
        * (((b' : BInf N A) : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      rw [coe_constantsHom, hb']
      exact hff'
    rw [hbb]
    refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨m, ?_, rfl⟩)
    show m ∈ IsLocalRing.maximalIdeal A
    rw [← hkerA]
    exact hm
  · rw [Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha0 : red a = 0 := by
      have : a ∈ RingHom.ker red := by rw [hkerA]; exact ha
      exact this
    show piInf N A red data hdeg ⟨constantsHom N A a, constInf_mem N A a⟩ = 0
    rw [piChart_constantsHom N A red _ _ (constInf_mem N A), ha0, map_zero]

end SplitGlue
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB.Model"

theorem exists_fibreModel_cuspChart_of_K (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hred : Function.Surjective red)
    (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
    (hliftFin : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k))
          y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y)
    (hliftInf : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k)⁻¹)
          y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y)
    (HKFin : ∀ f : O N A red,
      (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) →
      modularRedLocHom N A.toSubring (redS A red) f = 0 →
      ∃ m : A, red m = 0 ∧ ∃ f' : O N A red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))) (f' : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ))
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (m : AlgebraicClosure ℚ)
            * (f' : LaurentSeries (AlgebraicClosure ℚ)))
    (HKInf : ∀ f : O N A red,
      (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) →
      modularRedLocHom N A.toSubring (redS A red) f = 0 →
      ∃ m : A, red m = 0 ∧ ∃ f' : O N A red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (f' : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ))
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (m : AlgebraicClosure ℚ)
            * (f' : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ fm : FibreModel N A ℓ k red, fm.CuspChart ∧ IsIntegrallyClosed fm.BFin ∧ IsIntegrallyClosed fm.BInf :=
  exists_fibreModel_cuspChart_of_ker N A red ℓ data hdeg hred hdegX hliftFin hliftInf
    (ker_piFin_eq_span_of_K N A red data hdeg hred HKFin)
    (ker_piInf_eq_span_of_K N A red data hdeg hred HKInf)

end Model
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB.Model"
end CharpS10bB
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB.Model P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB.Model P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed.CharpS10bB"

p2m_open "ModularCurve~coeffMap_qExpand" in open  ModularCurve.CharPModel ModularCurve.CharPReduction in

theorem solution
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hred : Function.Surjective red)
    (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
    (hliftFin : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k))
          y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y)
    (hliftInf : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k)⁻¹)
          y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y) :
    ∃ fm : FibreModel N A ℓ k red, fm.CuspChart ∧ IsIntegrallyClosed fm.BFin ∧ IsIntegrallyClosed fm.BInf :=
  CharpS10bB.Model.exists_fibreModel_cuspChart_of_K N A red ℓ hred data hdeg hdegX hliftFin hliftInf
    (fun f hint hker =>
      ModularCurve.CharPModel.exists_eq_const_mul_of_modularRedLocHom_eq_zero N A k red data hdeg f
        hint hker)
    (fun f hint hker =>
      ModularCurve.CharPModel.exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv N A k red data hdeg
        hdegX f hint hker)

end S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed
end P2MW
export P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed (solution)
