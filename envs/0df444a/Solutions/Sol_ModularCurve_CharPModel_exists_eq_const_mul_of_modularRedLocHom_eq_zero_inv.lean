-- Prove2me | solution 1 for ModularCurve.CharPModel.exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c3d63c78-9fb7-5943-a58d-0bd2ffa0971a

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
import Theorems.Thm_ModularCurve_CharPModel_exists_eq_const_mul_of_redHom_eq_zero
import Theorems.Thm_ModularCurve_CharPModel_ker_eq_map_of_hasGoingDown
import Theorems.Thm_ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

namespace CharpS10bB

namespace SD2r

section Scaling

variable {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]

theorem exists_dvd_forall {ι : Type*} (c : ι → A) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ j ∈ s, c i ∣ c j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨a, Finset.mem_insert_self _ _, fun j hj => ?_⟩
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_rfl
      · exact absurd hj (Finset.notMem_empty _)
    · obtain ⟨i, hi, hmin⟩ := ih hne
      rcases ValuationRing.dvd_total (c a) (c i) with h | h
      · refine ⟨a, Finset.mem_insert_self _ _, fun j hj => ?_⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact dvd_rfl
        · exact h.trans (hmin j hj)
      · refine ⟨i, Finset.mem_insert_of_mem hi, fun j hj => ?_⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact h
        · exact hmin j hj

end Scaling

end SD2r

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

def BFin : Subring (FF N) := (integralClosure (affineBaseFin N A) (FF N)).toSubring

def BInf : Subring (FF N) := (integralClosure (affineBaseInf N A) (FF N)).toSubring

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

end IntClosed

end Model

namespace KerAbs

open Ideal Polynomial

section Radical

variable {A' : Type*} [CommRing A'] [IsDomain A'] [ValuationRing A']
variable {k' : Type*} [CommRing k'] (red' : A' →+* k')
variable {B : Type*} [CommRing B] (alg : Polynomial A' →+* B)

theorem mem_map_ker_iff (x : B) :
    x ∈ (RingHom.ker (mapRingHom red')).map alg ↔
      ∃ m : A', red' m = 0 ∧ ∃ b' : B, x = alg (C m) * b' := by
  constructor
  · intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨p, hp, rfl⟩
      have hp'' : ∀ i, red' (p.coeff i) = 0 := fun i => by
        have := congrArg (fun q => Polynomial.coeff q i) (RingHom.mem_ker.1 (show p ∈ RingHom.ker (mapRingHom red') from hp))
        simpa [coeff_map] using this
      classical
      by_cases hs : p.support.Nonempty
      · obtain ⟨i₀, -, hmin⟩ := SD2r.exists_dvd_forall (fun i => p.coeff i) p.support hs
        have hdvd : C (p.coeff i₀) ∣ p := by
          rw [C_dvd_iff_dvd_coeff]
          intro i
          by_cases hi : i ∈ p.support
          · exact hmin i hi
          · rw [Polynomial.notMem_support_iff.1 hi]; exact dvd_zero _
        obtain ⟨p', hp'⟩ := hdvd
        exact ⟨p.coeff i₀, hp'' i₀, alg p', by rw [← map_mul, ← hp']⟩
      · rw [Finset.not_nonempty_iff_eq_empty, Polynomial.support_eq_empty] at hs
        exact ⟨0, by rw [map_zero], 0, by rw [hs, map_zero, mul_zero]⟩
    · exact ⟨0, by rw [map_zero], 0, by rw [mul_zero]⟩
    · rintro x y - - ⟨m₁, hm₁, b₁, rfl⟩ ⟨m₂, hm₂, b₂, rfl⟩
      rcases ValuationRing.dvd_total m₁ m₂ with ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact ⟨m₁, hm₁, b₁ + alg (C d) * b₂, by rw [map_mul, map_mul]; ring⟩
      · exact ⟨m₂, hm₂, alg (C d) * b₁ + b₂, by rw [map_mul, map_mul]; ring⟩
    · rintro r x - ⟨m, hm, b', rfl⟩
      exact ⟨m, hm, r * b', by rw [smul_eq_mul]; ring⟩
  · rintro ⟨m, hm, b', rfl⟩
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, coe_mapRingHom, map_C, hm, C_0]

end Radical

end KerAbs

namespace Model

p2m_open "ModularCurve~coeffMap_qExpand ModularCurve.CharPModel ModularCurve.CharPReduction Polynomial"

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k]
  (red : A →+* k)

theorem valuationRing_toSubring (A' : ValuationSubring (AlgebraicClosure ℚ)) :
    ValuationRing A'.toSubring := by
  change ValuationRing A'
  infer_instance

attribute [local instance] valuationRing_toSubring

section ModularSite

theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  rw [dedekindPsi]
  refine Finset.sum_pos' (fun d _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  · simpa using Nat.pos_of_ne_zero (NeZero.ne N)

end ModularSite

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

section KerFin

theorem rad_chart (base : Subring (FF N)) (alg : Polynomial A →+* (integralClosure base (FF N)).toSubring)
    (halgC : ∀ m : A, ((alg (C m) : (integralClosure base (FF N)).toSubring) : FF N) = constantsHom N A m)
    (b : (integralClosure base (FF N)).toSubring) (n : ℕ) (hn : 0 < n)
    (h : b ^ n ∈ (RingHom.ker (Polynomial.mapRingHom red)).map alg) :
    b ∈ (RingHom.ker (Polynomial.mapRingHom red)).map alg := by
  obtain ⟨m, hm, b', hb'⟩ := (KerAbs.mem_map_ker_iff red alg _).1 h
  have hn0 : n ≠ 0 := by omega
  by_cases hm0 : m = 0
  · subst hm0
    have : b ^ n = 0 := by rw [hb', C_0, map_zero, zero_mul]
    rw [pow_eq_zero_iff hn0] at this
    rw [this]
    exact Ideal.zero_mem _
  have hm0' : (m : AlgebraicClosure ℚ) ≠ 0 := fun h => hm0 (Subtype.ext h)
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq (m : AlgebraicClosure ℚ) hn
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    apply hm0'
    rw [← hc₀, zero_pow hn0]
  have hc₀A : c₀ ∈ A := by
    rcases ValuationSubring.mem_or_inv_mem A c₀ with h | h
    · exact h
    · exfalso
      have key : m * (⟨c₀⁻¹, h⟩ : A) ^ n = 1 := by
        apply Subtype.ext
        show (m : AlgebraicClosure ℚ) * (c₀⁻¹) ^ n = 1
        rw [← hc₀, ← mul_pow, mul_inv_cancel₀ hc₀0, one_pow]
      have := congrArg red key
      rw [map_mul, hm, zero_mul, map_one] at this
      exact zero_ne_one this
  set c : A := ⟨c₀, hc₀A⟩ with hc
  have hcn : c ^ n = m := Subtype.ext (by rw [hc]; push_cast; exact hc₀)
  have hredc : red c = 0 := by
    have : red c ^ n = 0 := by rw [← map_pow, hcn, hm]
    exact (pow_eq_zero_iff hn0).1 this
  set cF : FF N := constantsHom N A c with hcF
  have hcF0 : cF ≠ 0 := by
    rw [hcF]
    show (algebraMap (AlgebraicClosure ℚ) (FF N)) c₀ ≠ 0
    exact (_root_.map_ne_zero _).2 hc₀0
  have hcFn : cF ^ n = constantsHom N A m := by rw [hcF, ← map_pow, hcn]
  have hconst_m : constantsHom N A m ≠ 0 := by rw [← hcFn]; exact pow_ne_zero _ hcF0
  have hy : ((b : FF N) / cF) ^ n = (b' : FF N) := by
    have := congrArg (fun z : (integralClosure base (FF N)).toSubring => (z : FF N)) hb'
    simp only [Subring.coe_pow, Subring.coe_mul] at this
    rw [div_pow, hcFn, this, halgC, mul_div_cancel_left₀ _ hconst_m]
  obtain ⟨y, hyb⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
    (R := (integralClosure base (FF N)).toSubring) hn (x := (b : FF N) / cF)
    (by rw [hy]; exact isIntegral_algebraMap)
  refine (KerAbs.mem_map_ker_iff red alg _).2 ⟨c, hredc, y, Subtype.ext ?_⟩
  have hyb' : ((y : (integralClosure base (FF N)).toSubring) : FF N) = (b : FF N) / cF := hyb
  rw [Subring.coe_mul, halgC, hyb', ← hcF, mul_div_cancel₀ _ hcF0]

end KerFin

section PoleSite

def poleRing : Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subring.closure (Set.range (constSeries A.toSubring) ∪
    {(jqModC (AlgebraicClosure ℚ))⁻¹,
      jqNModC (AlgebraicClosure ℚ) N * (jqModC (AlgebraicClosure ℚ))⁻¹ ^ N})

theorem const_mem_poleRing (a : A.toSubring) : constSeries A.toSubring a ∈ poleRing N A :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem inv_mem_poleRing : (jqModC (AlgebraicClosure ℚ))⁻¹ ∈ poleRing N A :=
  Subring.subset_closure (Or.inr (Or.inl rfl))

theorem t_mem_poleRing :
    jqNModC (AlgebraicClosure ℚ) N * (jqModC (AlgebraicClosure ℚ))⁻¹ ^ N ∈ poleRing N A :=
  Subring.subset_closure (Or.inr (Or.inr rfl))

theorem poleRing_le_O : poleRing N A ≤ O N A red := by
  rw [poleRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact mem_O_of_mem_modularRing N A red (constSeries_mem_modularRing N A.toSubring a)
  · exact jqModC_inv_mem_O N A red
  · exact Subring.mul_mem _
      (mem_O_of_mem_modularRing N A red (jqNModC_mem_modularRing N A.toSubring))
      (Subring.pow_mem _ (jqModC_inv_mem_O N A red) N)

def redPole : poleRing N A →+* LaurentSeries k :=
  (π₀ N A red).comp (Subring.inclusion (poleRing_le_O N A red))

theorem redPole_apply (r : poleRing N A) :
    redPole N A red r = π₀ N A red ⟨r, poleRing_le_O N A red r.2⟩ := rfl

def constToPole : A.toSubring →+* poleRing N A :=
  (constSeries A.toSubring).codRestrict _ (const_mem_poleRing N A)

@[scoped simp] theorem coe_constToPole (a : A.toSubring) :
    ((constToPole N A a : poleRing N A) : LaurentSeries (AlgebraicClosure ℚ)) = constSeries A.toSubring a := rfl

def sR : poleRing N A := ⟨_, inv_mem_poleRing N A⟩

def tR : poleRing N A := ⟨_, t_mem_poleRing N A⟩

@[scoped simp] theorem coe_sR : ((sR N A : poleRing N A) : LaurentSeries (AlgebraicClosure ℚ))
    = (jqModC (AlgebraicClosure ℚ))⁻¹ := rfl

@[scoped simp] theorem coe_tR : ((tR N A : poleRing N A) : LaurentSeries (AlgebraicClosure ℚ))
    = jqNModC (AlgebraicClosure ℚ) N * (jqModC (AlgebraicClosure ℚ))⁻¹ ^ N := rfl

theorem redPole_constToPole (a : A.toSubring) :
    redPole N A red (constToPole N A a) = algebraMap k (LaurentSeries k) (red a) :=
  pi0_constSeries N A red ⟨a, a.2⟩ _

theorem redPole_sR : redPole N A red (sR N A) = (jqModC k)⁻¹ :=
  pi0_jqModC_inv N A red

theorem redPole_tR : redPole N A red (tR N A) = jqNModC k N * (jqModC k)⁻¹ ^ N := by
  rw [redPole_apply]
  have : (⟨(tR N A : LaurentSeries (AlgebraicClosure ℚ)), poleRing_le_O N A red (tR N A).2⟩ : O N A red)
      = ⟨jqNModC (AlgebraicClosure ℚ) N,
          mem_O_of_mem_modularRing N A red (jqNModC_mem_modularRing N A.toSubring)⟩ *
        ⟨(jqModC (AlgebraicClosure ℚ))⁻¹, jqModC_inv_mem_O N A red⟩ ^ N :=
    Subtype.ext (by rw [Subring.coe_mul, Subring.coe_pow]; rfl)
  rw [this, map_mul, map_pow, pi0_jqNModC, pi0_jqModC_inv]

theorem exists_pole_relation (data : ModularPolynomialData N)
    (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i)) :
    ∃ Q : Polynomial (Polynomial A.toSubring), Q.Monic ∧ Q.natDegree = dedekindPsi N ∧
      Q.eval₂ (eval₂RingHom (constSeries A.toSubring) (jqModC (AlgebraicClosure ℚ))⁻¹)
        (jqNModC (AlgebraicClosure ℚ) N * (jqModC (AlgebraicClosure ℚ))⁻¹ ^ N) = 0 := by
  obtain ⟨Q, hQ, hQdeg, hroot⟩ := ModularCurve.CharPModel.exists_monic_eval2_inv_mul_inv_pow_eq_zero
    (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) data.Φ data.monic N
    (fun i _ => by rw [data.natDegree_eq]; exact hdegX i) (jqModC_ne_zero _)
    (jqNModC (AlgebraicClosure ℚ) N) (eval₂_Phi_jqModC N data)
  refine ⟨Q.map (Polynomial.mapRingHom (Int.castRingHom A.toSubring)), hQ.map _,
    by rw [hQ.natDegree_map, hQdeg, data.natDegree_eq], ?_⟩
  rw [eval₂_map]
  have : (eval₂RingHom (constSeries A.toSubring) (jqModC (AlgebraicClosure ℚ))⁻¹).comp
      (Polynomial.mapRingHom (Int.castRingHom A.toSubring))
      = eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ))⁻¹ :=
    Polynomial.ringHom_ext (fun n => by simp) (by simp)
  rw [this]
  exact hroot

theorem adjoin_inv_eq :
    IntermediateField.adjoin k {(jqModC k)⁻¹} = IntermediateField.adjoin k {(jqModC k : LaurentSeries k)} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k _)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k (jqModC k)⁻¹)
    rwa [inv_inv] at this

theorem adjoin_pole_eq :
    IntermediateField.adjoin k {(jqModC k)⁻¹, jqNModC k N * (jqModC k)⁻¹ ^ N}
      = IntermediateField.adjoin k {jqModC k, jqNModC k N} := by
  have hjL : jqModC k ∈ IntermediateField.adjoin k {(jqModC k)⁻¹, jqNModC k N * (jqModC k)⁻¹ ^ N} := by
    have := inv_mem (IntermediateField.subset_adjoin k
      ({(jqModC k)⁻¹, jqNModC k N * (jqModC k)⁻¹ ^ N} : Set (LaurentSeries k)) (Set.mem_insert _ _))
    rwa [inv_inv] at this
  have htL : jqNModC k N * (jqModC k)⁻¹ ^ N
      ∈ IntermediateField.adjoin k {(jqModC k)⁻¹, jqNModC k N * (jqModC k)⁻¹ ^ N} :=
    IntermediateField.subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)
  have hjR : jqModC k ∈ IntermediateField.adjoin k {jqModC k, jqNModC k N} :=
    IntermediateField.subset_adjoin k _ (Set.mem_insert _ _)
  have hjNR : jqNModC k N ∈ IntermediateField.adjoin k {jqModC k, jqNModC k N} :=
    IntermediateField.subset_adjoin k _ (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm <;> rw [IntermediateField.adjoin_le_iff]
  · rintro x (rfl | rfl)
    · exact inv_mem hjR
    · exact mul_mem hjNR (pow_mem (inv_mem hjR) N)
  · rintro x (rfl | rfl)
    · exact hjL
    · have key := mul_mem htL (pow_mem hjL N)
      rwa [mul_assoc, ← mul_pow, inv_mul_cancel₀ (jqModC_ne_zero k), one_pow, mul_one] at key

theorem transcendental_jqModC_inv (K : Type*) [Field K] : Transcendental K (jqModC K)⁻¹ :=
  fun h => transcendental_jqModC K (IsAlgebraic.inv_iff.1 h)

variable (data : ModularPolynomialData N)
variable (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
variable (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
  (modularFunctionFieldC k N) = dedekindPsi N)

include data hdegX hdeg in

theorem exists_eq_const_mul_of_redPole_eq_zero (r : poleRing N A) (hr : redPole N A red r = 0) :
    ∃ m : A.toSubring, red m = 0 ∧ ∃ r' : poleRing N A, r = constToPole N A m * r' := by
  obtain ⟨Q, hQ, hQdeg, hrel⟩ := exists_pole_relation N A data hdegX
  exact ModularCurve.CharPModel.exists_eq_const_mul_of_redHom_eq_zero (redS A red) (constSeries A.toSubring)
    (jqModC (AlgebraicClosure ℚ))⁻¹ (jqNModC (AlgebraicClosure ℚ) N * (jqModC (AlgebraicClosure ℚ))⁻¹ ^ N)
    Q hQ (by rw [hQdeg]; exact dedekindPsi_pos N) hrel
    (poleRing N A) (const_mem_poleRing N A) (inv_mem_poleRing N A) (t_mem_poleRing N A) (le_of_eq rfl)
    (redPole N A red) (redPole_constToPole N A red)
    (by
      show Transcendental k (redPole N A red (sR N A))
      rw [redPole_sR]
      exact transcendental_jqModC_inv k)
    (by
      show (IntermediateField.adjoin k {redPole N A red (sR N A)}).relfinrank
        (IntermediateField.adjoin k {redPole N A red (sR N A), redPole N A red (tR N A)}) = _
      rw [redPole_sR, redPole_tR, adjoin_inv_eq, adjoin_pole_eq, hQdeg]
      exact hdeg)
    r hr

theorem exists_pow_mul_mem_poleRing {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ modularRing N A.toSubring) :
    ∃ M : ℕ, ∀ M' : ℕ, M ≤ M' → (jqModC (AlgebraicClosure ℚ))⁻¹ ^ M' * x ∈ poleRing N A := by
  rw [modularRing] at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | rfl | rfl
    · exact ⟨0, fun M' _ => Subring.mul_mem _ (Subring.pow_mem _ (inv_mem_poleRing N A) M')
        (const_mem_poleRing N A a)⟩
    · refine ⟨1, fun M' hM' => ?_⟩
      obtain ⟨M'', rfl⟩ := Nat.exists_eq_add_of_le hM'
      have : (jqModC (AlgebraicClosure ℚ))⁻¹ ^ (1 + M'') * jqModC (AlgebraicClosure ℚ)
          = (jqModC (AlgebraicClosure ℚ))⁻¹ ^ M'' := by
        rw [pow_add, pow_one, mul_comm ((jqModC (AlgebraicClosure ℚ))⁻¹) _, mul_assoc,
          inv_mul_cancel₀ (jqModC_ne_zero _), mul_one]
      rw [this]
      exact Subring.pow_mem _ (inv_mem_poleRing N A) _
    · refine ⟨N, fun M' hM' => ?_⟩
      obtain ⟨M'', rfl⟩ := Nat.exists_eq_add_of_le hM'
      have : (jqModC (AlgebraicClosure ℚ))⁻¹ ^ (N + M'') * jqNModC (AlgebraicClosure ℚ) N
          = (jqModC (AlgebraicClosure ℚ))⁻¹ ^ M'' *
              (jqNModC (AlgebraicClosure ℚ) N * (jqModC (AlgebraicClosure ℚ))⁻¹ ^ N) := by ring
      rw [this]
      exact Subring.mul_mem _ (Subring.pow_mem _ (inv_mem_poleRing N A) _) (t_mem_poleRing N A)
  | zero => exact ⟨0, fun M' _ => by rw [mul_zero]; exact Subring.zero_mem _⟩
  | one => exact ⟨0, fun M' _ => by rw [mul_one]; exact Subring.pow_mem _ (inv_mem_poleRing N A) _⟩
  | add x y _ _ hx hy =>
    obtain ⟨M₁, h₁⟩ := hx
    obtain ⟨M₂, h₂⟩ := hy
    exact ⟨max M₁ M₂, fun M' hM' => by
      rw [mul_add]
      exact Subring.add_mem _ (h₁ M' (le_of_max_le_left hM')) (h₂ M' (le_of_max_le_right hM'))⟩
  | neg x _ hx =>
    obtain ⟨M, h⟩ := hx
    exact ⟨M, fun M' hM' => by rw [mul_neg]; exact Subring.neg_mem _ (h M' hM')⟩
  | mul x y _ _ hx hy =>
    obtain ⟨M₁, h₁⟩ := hx
    obtain ⟨M₂, h₂⟩ := hy
    refine ⟨M₁ + M₂, fun M' hM' => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM'
    have : (jqModC (AlgebraicClosure ℚ))⁻¹ ^ (M₁ + M₂ + d) * (x * y)
        = ((jqModC (AlgebraicClosure ℚ))⁻¹ ^ M₁ * x) * ((jqModC (AlgebraicClosure ℚ))⁻¹ ^ (M₂ + d) * y) := by
      ring
    rw [this]
    exact Subring.mul_mem _ (h₁ M₁ le_rfl) (h₂ (M₂ + d) (Nat.le_add_right _ _))

end PoleSite

section KerInf

def algInf : Polynomial A →+* BInf N A :=
  (Subring.inclusion (affineBaseInf_le_BInf N A)).comp
    (basePoly N A (affineBaseInf N A) (const_mem_affineBaseInf N A)
      ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩)

theorem coe_algInf (p : Polynomial A) :
    (((algInf N A p : BInf N A) : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      = p.eval₂ ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹ := by
  rw [← coe_jBar_inv N]
  exact coe_basePoly N A (affineBaseInf N A) (const_mem_affineBaseInf N A)
    ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ p

theorem coe_algInf_mem_affineBaseInf (p : Polynomial A) :
    ((algInf N A p : BInf N A) : FF N) ∈ affineBaseInf N A :=
  (basePoly N A (affineBaseInf N A) (const_mem_affineBaseInf N A) ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ p).2

theorem toSeries_algInf (p : Polynomial A) :
    toSeries N (BInf N A) (algInf N A p)
      = p.eval₂ ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹ :=
  coe_algInf N A p

theorem algInf_injective : Function.Injective (algInf N A) := by
  refine (injective_iff_map_eq_zero (algInf N A)).2 fun p hp => ?_
  have h1 : p.eval₂ ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
      (jqModC (AlgebraicClosure ℚ))⁻¹ = 0 := by
    rw [← coe_algInf N A, hp]; rfl
  have h2 : Polynomial.aeval (jqModC (AlgebraicClosure ℚ))⁻¹ (p.map A.subtype) = 0 := by
    rw [aeval_def, eval₂_map]; exact h1
  have h3 : p.map A.subtype = 0 :=
    transcendental_iff_injective.1 (transcendental_jqModC_inv (AlgebraicClosure ℚ)) (by rw [h2, map_zero])
  exact Polynomial.map_injective _ Subtype.val_injective (by rw [h3, Polynomial.map_zero])

abbrev algInfAlgebra : Algebra (Polynomial A) (BInf N A) := (algInf N A).toAlgebra

attribute [local instance] algInfAlgebra

theorem algebraMap_BInf_eq : algebraMap (Polynomial A) (BInf N A) = algInf N A := rfl

theorem isIntegral_BInf : Algebra.IsIntegral (Polynomial A) (BInf N A) := by
  refine ⟨fun b => ?_⟩
  obtain ⟨p, hpm, hpe⟩ := b.2
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective _
      (basePoly_surjective N A (affineBaseInf N A) (const_mem_affineBaseInf N A)
        ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ le_rfl) p)) hpm
  refine ⟨P, hPm, ?_⟩
  apply Subtype.ext
  rw [show ((Polynomial.eval₂ (algebraMap (Polynomial A) (BInf N A)) b P : BInf N A) : FF N)
      = (BInf N A).subtype (Polynomial.eval₂ (algebraMap (Polynomial A) (BInf N A)) b P) from rfl,
    hom_eval₂, algebraMap_BInf_eq,
    show (BInf N A).subtype.comp (algInf N A) = (affineBaseInf N A).subtype.comp
      (basePoly N A (affineBaseInf N A) (const_mem_affineBaseInf N A) ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩)
      from RingHom.ext fun _ => rfl,
    ← eval₂_map, hPmap]
  exact hpe

theorem faithfulSMul_BInf : FaithfulSMul (Polynomial A) (BInf N A) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 (algInf_injective N A)

theorem hasGoingDown_BInf : Algebra.HasGoingDown (Polynomial A) (BInf N A) := by
  haveI := faithfulSMul_BInf N A
  haveI := isIntegral_BInf N A
  infer_instance

variable (data : ModularPolynomialData N)
variable (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
variable (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
  (modularFunctionFieldC k N) = dedekindPsi N)

theorem coe_piInf_algInf (p : Polynomial A) :
    ((piInf N A red data hdeg (algInf N A p) : modularFunctionFieldC k N) : LaurentSeries k)
      = (p.map red).eval₂ (algebraMap k (LaurentSeries k)) (jqModC k)⁻¹ := by
  have hO := hBO_Inf N A red data hdeg (algInf N A p)
  have h1 : ((piInf N A red data hdeg (algInf N A p) : modularFunctionFieldC k N) : LaurentSeries k)
      = π₀ N A red ⟨toSeries N (BInf N A) (algInf N A p), hO⟩ := rfl
  have h2 : (⟨toSeries N (BInf N A) (algInf N A p), hO⟩ : O N A red)
      = Polynomial.eval₂ (constO N A red) ⟨_, jqModC_inv_mem_O N A red⟩ p :=
    basePoly_toO N A red (affineBaseInf N A) (const_mem_affineBaseInf N A)
      ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ ⟨_, jqModC_inv_mem_O N A red⟩ (coe_jBar_inv N) p hO
  rw [h1, h2, hom_eval₂, eval₂_map]
  congr 1
  · exact RingHom.ext fun a => pi0_constO N A red a
  · exact pi0_jqModC_inv N A red

include data hdeg in
theorem comap_ker_piInf : (RingHom.ker (piInf N A red data hdeg)).comap (algInf N A)
    = RingHom.ker (Polynomial.mapRingHom red) := by
  ext p
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, coe_mapRingHom]
  constructor
  · intro h
    have h1 : (p.map red).eval₂ (algebraMap k (LaurentSeries k)) (jqModC k)⁻¹ = 0 := by
      rw [← coe_piInf_algInf N A red data hdeg, h]; rfl
    have h2 : Polynomial.aeval (jqModC k)⁻¹ (p.map red) = 0 := by rw [aeval_def]; exact h1
    exact transcendental_iff_injective.1 (transcendental_jqModC_inv k) (by rw [h2, map_zero])
  · intro h
    apply Subtype.ext
    rw [coe_piInf_algInf, h, eval₂_zero]
    rfl

def tB : BInf N A := ⟨jNBar N * ((jBar N)⁻¹) ^ N, tBar_mem N A data hdegX⟩

theorem toSeries_tB : toSeries N (BInf N A) (tB N A data hdegX)
    = jqNModC (AlgebraicClosure ℚ) N * (jqModC (AlgebraicClosure ℚ))⁻¹ ^ N :=
  coe_tBar N

def RInf : Subring (BInf N A) :=
  Subring.closure (Set.range (algInf N A) ∪ {tB N A data hdegX})

theorem coe_mem_poleRing_of_mem_affineBaseInf {x : FF N} (hx : x ∈ affineBaseInf N A) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ poleRing N A := by
  have : affineBaseInf N A ≤ (poleRing N A).comap
      (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))) := by
    rw [affineBaseInf, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl) <;> rw [SetLike.mem_coe, Subring.mem_comap]
    · show ((constantsHom N A a : FF N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ poleRing N A
      rw [coe_constantsHom]
      exact const_mem_poleRing N A _
    · show (((jBar N)⁻¹ : FF N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ poleRing N A
      rw [coe_jBar_inv]
      exact inv_mem_poleRing N A
  exact this hx

theorem RInf_le_comap : RInf N A data hdegX ≤ (poleRing N A).comap (toSeries N (BInf N A)) := by
  rw [RInf, Subring.closure_le]
  rintro x (⟨p, rfl⟩ | rfl) <;> rw [SetLike.mem_coe, Subring.mem_comap]
  · exact coe_mem_poleRing_of_mem_affineBaseInf N A (coe_algInf_mem_affineBaseInf N A p)
  · rw [toSeries_tB]
    exact t_mem_poleRing N A

theorem poleRing_le_map_RInf :
    poleRing N A ≤ (RInf N A data hdegX).map (toSeries N (BInf N A)) := by
  rw [poleRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · refine ⟨algInf N A (C ⟨a, a.2⟩), Subring.subset_closure (Or.inl ⟨C ⟨a, a.2⟩, rfl⟩), ?_⟩
    rw [toSeries_algInf, eval₂_C]
    rfl
  · refine ⟨algInf N A X, Subring.subset_closure (Or.inl ⟨X, rfl⟩), ?_⟩
    rw [toSeries_algInf, eval₂_X]
  · exact ⟨tB N A data hdegX, Subring.subset_closure (Or.inr rfl), toSeries_tB N A data hdegX⟩

theorem toSeries_BInf_injective : Function.Injective (toSeries N (BInf N A)) := fun _ _ h =>
  Subtype.ext ((algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).injective h)

include hdeg hdegX in
theorem hpres_Inf (b : BInf N A) : ∃ r ∈ RInf N A data hdegX, ∃ s ∈ RInf N A data hdegX,
    piInf N A red data hdeg s ≠ 0 ∧ b * s = r := by
  obtain ⟨r₀, s₀, hs₀, hbs⟩ := (mem_localizedAtKer _ _ _ _).1 (hBO_Inf N A red data hdeg b)
  obtain ⟨M₁, hM₁⟩ := exists_pow_mul_mem_poleRing N A r₀.2
  obtain ⟨M₂, hM₂⟩ := exists_pow_mul_mem_poleRing N A s₀.2
  have hr₁ := hM₁ (max M₁ M₂) (le_max_left _ _)
  have hs₁ := hM₂ (max M₁ M₂) (le_max_right _ _)
  obtain ⟨r, hr, hrr⟩ := poleRing_le_map_RInf N A data hdegX hr₁
  obtain ⟨s, hs, hss⟩ := poleRing_le_map_RInf N A data hdegX hs₁
  refine ⟨r, hr, s, hs, ?_, ?_⟩
  · intro h0
    apply (notMem_redKer_iff _ _ _ _).1 hs₀
    have h1 : ((piInf N A red data hdeg s : modularFunctionFieldC k N) : LaurentSeries k) = 0 := by
      rw [h0]; rfl
    have h2 : ((piInf N A red data hdeg s : modularFunctionFieldC k N) : LaurentSeries k)
        = π₀ N A red ⟨toSeries N (BInf N A) s, hBO_Inf N A red data hdeg s⟩ := rfl
    have hsO : (jqModC (AlgebraicClosure ℚ))⁻¹ ^ max M₁ M₂ * (s₀ : LaurentSeries (AlgebraicClosure ℚ))
        ∈ O N A red :=
      Subring.mul_mem _ (Subring.pow_mem _ (jqModC_inv_mem_O N A red) _)
        (mem_O_of_mem_modularRing N A red s₀.2)
    rw [h2, pi0_congr N A red _ hsO hss] at h1
    have h3 : (⟨_, hsO⟩ : O N A red)
        = ⟨(jqModC (AlgebraicClosure ℚ))⁻¹, jqModC_inv_mem_O N A red⟩ ^ max M₁ M₂ *
          ⟨(s₀ : LaurentSeries (AlgebraicClosure ℚ)), mem_O_of_mem_modularRing N A red s₀.2⟩ :=
      Subtype.ext (by rw [Subring.coe_mul, Subring.coe_pow])
    rw [h3, map_mul, map_pow, pi0_jqModC_inv, pi0_of_mem_modularRing N A red s₀.2] at h1
    have h4 := (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (inv_ne_zero (jqModC_ne_zero k)))
    rw [redRes_apply]
    exact h4
  · apply toSeries_BInf_injective N A
    rw [map_mul, hrr, hss, mul_left_comm, hbs]

include hdeg in
theorem hfree_Inf (r : BInf N A) (hr : r ∈ RInf N A data hdegX) (h0 : piInf N A red data hdeg r = 0) :
    ∃ c ∈ RingHom.ker (Polynomial.mapRingHom red), ∃ r' ∈ RInf N A data hdegX,
      r = algInf N A c * r' := by
  set r₀ : poleRing N A := ⟨toSeries N (BInf N A) r, RInf_le_comap N A data hdegX hr⟩ with hr₀
  have hrK : redPole N A red r₀ = 0 := by
    have h1 : ((piInf N A red data hdeg r : modularFunctionFieldC k N) : LaurentSeries k) = 0 := by
      rw [h0]; rfl
    exact h1
  obtain ⟨m, hm, r', hrm⟩ := exists_eq_const_mul_of_redPole_eq_zero N A red data hdegX hdeg r₀ hrK
  obtain ⟨r'', hr'', hrr''⟩ := poleRing_le_map_RInf N A data hdegX r'.2
  refine ⟨C ⟨m, m.2⟩, ?_, r'', hr'', ?_⟩
  · rw [RingHom.mem_ker, coe_mapRingHom, map_C, show red ⟨m, m.2⟩ = 0 from hm, C_0]
  · apply toSeries_BInf_injective N A
    rw [map_mul, hrr'', toSeries_algInf, eval₂_C]
    exact congrArg Subtype.val hrm

end KerInf

section SplitGlue

attribute [local instance] algInfAlgebra

variable (data : ModularPolynomialData N)
variable (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
variable (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
  (modularFunctionFieldC k N) = dedekindPsi N)

include hdeg hdegX in

theorem ker_piInf_eq_map :
    RingHom.ker (piInf N A red data hdeg) =
      (RingHom.ker (Polynomial.mapRingHom red)).map (algebraMap (Polynomial A) (BInf N A)) := by
  haveI := hasGoingDown_BInf N A
  haveI := isIntegral_BInf N A
  haveI h𝔭 : (RingHom.ker (Polynomial.mapRingHom red)).IsPrime := RingHom.ker_isPrime _
  exact ModularCurve.CharPModel.ker_eq_map_of_hasGoingDown (piInf N A red data hdeg)
    (RingHom.ker (Polynomial.mapRingHom red)) (comap_ker_piInf N A red data hdeg)
    (RInf N A data hdegX) (fun p => Subring.subset_closure (Or.inl ⟨p, rfl⟩))
    (hpres_Inf N A red data hdegX hdeg) (fun r hr h0 => hfree_Inf N A red data hdegX hdeg r hr h0)
    (fun b n hn hb => rad_chart N A red (affineBaseInf N A) (algInf N A) (fun m => by
        apply (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).injective
        show toSeries N (BInf N A) (algInf N A (C m)) = _
        rw [toSeries_algInf, eval₂_C]; rfl) b n hn hb)

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

include data hdegX hdeg in

theorem kerInf_series (f : O N A red)
    (hint : (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0))
    (hker : modularRedLocHom N A.toSubring (redS A red) f = 0) :
    ∃ m : A, red m = 0 ∧ ∃ f' : O N A red,
      (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (f' : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
      (f : LaurentSeries (AlgebraicClosure ℚ))
        = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (m : AlgebraicClosure ℚ)
          * (f' : LaurentSeries (AlgebraicClosure ℚ)) := by
  obtain ⟨b, hb⟩ := exists_mem_of_lift N A red (affineBaseInf N A) (BInf N A) (fun x => mem_BInf_iff N A)
    (const_mem_affineBaseInf N A) ⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ f.2
    (by
      obtain ⟨P, hPm, hPe⟩ := hint
      exact ⟨P, hPm, by
        rw [show ((((⟨(jBar N)⁻¹, jInvBar_mem_affineBaseInf N A⟩ : affineBaseInf N A) : FF N)) :
          LaurentSeries (AlgebraicClosure ℚ)) = (jqModC (AlgebraicClosure ℚ))⁻¹ from coe_jBar_inv N]
        exact hPe⟩)
  have hfb : (⟨toSeries N (BInf N A) b, hBO_Inf N A red data hdeg b⟩ : O N A red) = f := Subtype.ext hb
  have hb0 : piInf N A red data hdeg b = 0 := by
    apply Subtype.ext
    rw [coe_piChart_apply, hfb, ZeroMemClass.coe_zero]
    exact hker
  have hbker : b ∈ (RingHom.ker (Polynomial.mapRingHom red)).map (algInf N A) := by
    rw [← algebraMap_BInf_eq, ← ker_piInf_eq_map N A red data hdegX hdeg]
    exact hb0
  obtain ⟨m, hm, b', hbm⟩ := (KerAbs.mem_map_ker_iff red (algInf N A) b).1 hbker
  refine ⟨m, hm, ⟨toSeries N (BInf N A) b', hBO_Inf N A red data hdeg b'⟩,
    exists_bivariate_of_mem_BInf N A b', ?_⟩
  rw [← hb]
  have h := congrArg (toSeries N (BInf N A)) hbm
  rw [map_mul, toSeries_algInf, eval₂_C] at h
  exact h

end SplitGlue

end Model
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv.CharpS10bB.Model"
end CharpS10bB
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv.CharpS10bB.Model P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv.CharpS10bB"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv.CharpS10bB.Model P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv.CharpS10bB"

p2m_open "ModularCurve~coeffMap_qExpand" in open  ModularCurve.CharPModel ModularCurve.CharPReduction in

theorem solution (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (k : Type*) [Field k] (red : A →+* k)
    (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
    (f : CharPReduction.modularLocalized N A.toSubring red)
    (hint : ∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0)
    (hker : CharPReduction.modularRedLocHom N A.toSubring red f = 0) :
    ∃ m : A, red m = 0 ∧ ∃ f' : CharPReduction.modularLocalized N A.toSubring red,
      (∃ P : Polynomial (Polynomial A), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ))⁻¹) (f' : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
      (f : LaurentSeries (AlgebraicClosure ℚ))
        = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (m : AlgebraicClosure ℚ)
          * (f' : LaurentSeries (AlgebraicClosure ℚ)) :=
  CharpS10bB.Model.kerInf_series N A red data hdegX hdeg f hint hker

end S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv
end P2MW
export P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv (solution)
