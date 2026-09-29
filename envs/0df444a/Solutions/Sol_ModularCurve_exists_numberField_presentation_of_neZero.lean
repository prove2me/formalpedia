-- Prove2me | solution 1 for ModularCurve.exists_numberField_presentation_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/db12f23f-f3dd-589d-b473-871b28d3afb1

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_laurentBaseChange_le_of_divisor_generators_mem
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_numberField_presentation_of_neZero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

namespace DescAux

noncomputable section

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))

def Pres (x : LaurentSeries (AlgebraicClosure ℚ)) : Prop :=
  ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (P Q : MvPolynomial (Fin 2) (coeffSubring A K)),
      modularEval N (coeffSubring A K) Q ≠ 0 ∧
      x * modularEval N (coeffSubring A K) Q = modularEval N (coeffSubring A K) P

variable {A} in
theorem coeffSubring_mono {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    coeffSubring A K ≤ coeffSubring A K' :=
  inf_le_inf_left _ (fun _ hx => h hx)

variable {N A} in

theorem modularEval_map_inclusion {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K')
    (P : MvPolynomial (Fin 2) (coeffSubring A K)) :
    modularEval N (coeffSubring A K') (MvPolynomial.map (Subring.inclusion (coeffSubring_mono h)) P)
      = modularEval N (coeffSubring A K) P := by
  unfold modularEval
  rw [MvPolynomial.eval₂Hom_map_hom]
  congr 1

variable {N A} in

theorem Pres.enlarge {x : LaurentSeries (AlgebraicClosure ℚ)}
    {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (P Q : MvPolynomial (Fin 2) (coeffSubring A K))
    (hQ : modularEval N (coeffSubring A K) Q ≠ 0)
    (hx : x * modularEval N (coeffSubring A K) Q = modularEval N (coeffSubring A K) P)
    {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    ∃ P' Q' : MvPolynomial (Fin 2) (coeffSubring A K'),
      modularEval N (coeffSubring A K') Q' ≠ 0 ∧
      x * modularEval N (coeffSubring A K') Q' = modularEval N (coeffSubring A K') P' :=
  ⟨MvPolynomial.map (Subring.inclusion (coeffSubring_mono h)) P,
    MvPolynomial.map (Subring.inclusion (coeffSubring_mono h)) Q,
    by rwa [modularEval_map_inclusion h], by rwa [modularEval_map_inclusion h, modularEval_map_inclusion h]⟩

theorem pres_zero : Pres N A 0 :=
  ⟨⊥, inferInstance, 0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, map_zero, zero_mul]⟩

theorem pres_one : Pres N A 1 :=
  ⟨⊥, inferInstance, 1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]⟩

variable {N A} in
theorem pres_add {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : Pres N A x) (hy : Pres N A y) :
    Pres N A (x + y) := by
  obtain ⟨K₁, hK₁, P₁, Q₁, hQ₁, h₁⟩ := hx
  obtain ⟨K₂, hK₂, P₂, Q₂, hQ₂, h₂⟩ := hy
  haveI := hK₁; haveI := hK₂
  obtain ⟨P, Q, hQ, h⟩ := Pres.enlarge P₁ Q₁ hQ₁ h₁ (le_sup_left : K₁ ≤ K₁ ⊔ K₂)
  obtain ⟨P', Q', hQ', h'⟩ := Pres.enlarge P₂ Q₂ hQ₂ h₂ (le_sup_right : K₂ ≤ K₁ ⊔ K₂)
  refine ⟨K₁ ⊔ K₂, inferInstance, P * Q' + P' * Q, Q * Q', ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hQ hQ'
  · rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']; ring

variable {N A} in
theorem pres_neg {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : Pres N A x) : Pres N A (-x) := by
  obtain ⟨K, hK, P, Q, hQ, h⟩ := hx
  exact ⟨K, hK, -P, Q, hQ, by rw [map_neg, neg_mul, h]⟩

variable {N A} in
theorem pres_mul {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : Pres N A x) (hy : Pres N A y) :
    Pres N A (x * y) := by
  obtain ⟨K₁, hK₁, P₁, Q₁, hQ₁, h₁⟩ := hx
  obtain ⟨K₂, hK₂, P₂, Q₂, hQ₂, h₂⟩ := hy
  haveI := hK₁; haveI := hK₂
  obtain ⟨P, Q, hQ, h⟩ := Pres.enlarge P₁ Q₁ hQ₁ h₁ (le_sup_left : K₁ ≤ K₁ ⊔ K₂)
  obtain ⟨P', Q', hQ', h'⟩ := Pres.enlarge P₂ Q₂ hQ₂ h₂ (le_sup_right : K₂ ≤ K₁ ⊔ K₂)
  refine ⟨K₁ ⊔ K₂, inferInstance, P * P', Q * Q', ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hQ hQ'
  · rw [map_mul, map_mul, ← h, ← h']; ring

variable {N A} in
theorem pres_inv {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : Pres N A x) : Pres N A x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [inv_zero]; exact pres_zero N A
  obtain ⟨K, hK, P, Q, hQ, h⟩ := hx
  refine ⟨K, hK, Q, P, ?_, ?_⟩
  · rw [← h]; exact mul_ne_zero hx0 hQ
  · rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

theorem modularEval_C (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (a : coeffSubring A K) :
    modularEval N (coeffSubring A K) (MvPolynomial.C a)
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) := by
  unfold modularEval
  rw [MvPolynomial.eval₂Hom_C]
  rfl

theorem pres_algebraMap (c : AlgebraicClosure ℚ) :
    Pres N A (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [map_zero]; exact pres_zero N A
  have hcK : c ∈ IntermediateField.adjoin ℚ {c} := IntermediateField.mem_adjoin_simple_self ℚ c

  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) :=
    IntermediateField.adjoin.finiteDimensional (halg.isAlgebraic c).isIntegral
  have hinj : Function.Injective
      (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) :=
    (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective
  rcases A.mem_or_inv_mem c with hcA | hcA
  · refine ⟨IntermediateField.adjoin ℚ {c}, inferInstance, MvPolynomial.C ⟨c, hcA, hcK⟩, 1,
      by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [map_one, mul_one, modularEval_C]
  · refine ⟨IntermediateField.adjoin ℚ {c}, inferInstance, 1,
      MvPolynomial.C ⟨c⁻¹, hcA, (IntermediateField.adjoin ℚ {c}).inv_mem hcK⟩, ?_, ?_⟩
    · rw [modularEval_C]
      exact (map_ne_zero_iff _ hinj).mpr (inv_ne_zero hc0)
    · rw [modularEval_C, map_one]
      change _ * algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]

def presField : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subfield.toIntermediateField
    { carrier := {x | Pres N A x}
      mul_mem' := fun hx hy => pres_mul hx hy
      one_mem' := pres_one N A
      add_mem' := fun hx hy => pres_add hx hy
      zero_mem' := pres_zero N A
      neg_mem' := fun hx => pres_neg hx
      inv_mem' := fun _ hx => pres_inv hx }
    (pres_algebraMap N A)

theorem mem_presField {x : LaurentSeries (AlgebraicClosure ℚ)} : x ∈ presField N A ↔ Pres N A x :=
  Iff.rfl

theorem pres_jqModC : Pres N A (jqModC (AlgebraicClosure ℚ)) := by
  refine ⟨⊥, inferInstance, MvPolynomial.X 0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [map_one, mul_one]
  unfold modularEval
  rw [MvPolynomial.eval₂Hom_X']
  rfl

theorem pres_jqNModC : Pres N A (jqNModC (AlgebraicClosure ℚ) N) := by
  refine ⟨⊥, inferInstance, MvPolynomial.X 1, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
  rw [map_one, mul_one]
  unfold modularEval
  rw [MvPolynomial.eval₂Hom_X']
  rfl

end

end DescAux

open DescAux in
theorem solution
    {N : ℕ} [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (f : ↥(modularFunctionFieldBar N)) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (P Q : MvPolynomial (Fin 2) (coeffSubring A K)),
      modularEval N (coeffSubring A K) Q ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval N (coeffSubring A K) Q
        = modularEval N (coeffSubring A K) P := by
  suffices hle : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      ≤ presField N A from (mem_presField N A).mp (hle f.2)

  have hC : modularFunctionFieldC (AlgebraicClosure ℚ) N ≤ presField N A := by
    rw [modularFunctionFieldC, IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact pres_jqModC N A
    · exact pres_jqNModC N A

  have hfull : modularFunctionFieldC (AlgebraicClosure ℚ) N
      = modularFunctionFieldFullC (AlgebraicClosure ℚ) N :=
    ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (AlgebraicClosure ℚ) 0 N
      (fun h => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd h))
  refine ModularCurve.laurentBaseChange_le_of_divisor_generators_mem (AlgebraicClosure ℚ) N
    (presField N A) ?_
  intro d hd hdvd
  rw [ModularCurve.coeffEmb_qExpand, ModularCurve.coeffEmb_jq]
  apply hC
  rw [hfull]
  exact jqModCd_mem_full (AlgebraicClosure ℚ) N hdvd

end S_ModularCurve_exists_numberField_presentation_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_numberField_presentation_of_neZero (solution)
