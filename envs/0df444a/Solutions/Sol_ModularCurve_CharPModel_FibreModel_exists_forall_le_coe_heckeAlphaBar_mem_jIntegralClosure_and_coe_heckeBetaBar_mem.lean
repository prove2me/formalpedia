-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0b388981-91f7-59bb-9fca-3199cd80b925

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_numberField_presentation_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem.ModularCurve.NodeLocalized ModularCurve.CharPModel"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_congr qExpand_qExpand algebraMap_apply_eq_single jq evalAtJ_X ModularPolynomialData coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff jqModC jqNModC map_jqModC heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar CharPReduction.constSeries CharPModel.jBar CharPModel.affineBaseFin CharPModel.FibreModel functionFieldGeneration nonempty_modularPolynomialData exists_numberField_presentation_of_neZero"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval"
p2m_open "ModularCurve.NodeLocalized ModularCurve"

section Basics

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem c4_mem_coeffSubring_iff {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := by
  simp only [coeffSubring, Subring.mem_inf]
  exact Iff.rfl

theorem c4_constSeries_coeffSubring_apply (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) := rfl

theorem c4_algebraMap_mem_fieldOver (M : ℕ) [NeZero M] {x : AlgebraicClosure ℚ} (hx : x ∈ K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem c4_jqModC_mem_fieldOver (M : ℕ) [NeZero M] : jqModC (AlgebraicClosure ℚ) ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem c4_jqNModC_mem_fieldOver (M : ℕ) [NeZero M] : jqNModC (AlgebraicClosure ℚ) M ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem c4_jqModC_mem_jRing : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

theorem c4_constSeries_mem_jRing (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem c4_jRing_le_fieldOver (M : ℕ) [NeZero M] : jRing A K ≤ (fieldOver M K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact c4_algebraMap_mem_fieldOver K M ((c4_mem_coeffSubring_iff A K).mp a.2).2
  · exact c4_jqModC_mem_fieldOver K M

variable {A K} in
theorem c4_coeffSubring_mono {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    coeffSubring A K ≤ coeffSubring A K' :=
  inf_le_inf_left _ (fun _ hx => h hx)

variable {A K} in
theorem c4_jRing_mono {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') : jRing A K ≤ jRing A K' := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact c4_constSeries_mem_jRing A K' ⟨a, c4_coeffSubring_mono h a.2⟩
  · exact c4_jqModC_mem_jRing A K'

variable {K} in
theorem c4_fieldOver_mono (M : ℕ) [NeZero M] {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    fieldOver M K ≤ fieldOver M K' := by
  rw [fieldOver, Subfield.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨a, h a.2⟩, rfl⟩)
  · exact Subfield.subset_closure (Or.inr hx)

variable {A K} in

theorem c4_jIntegralClosure_mono (M : ℕ) [NeZero M] {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K')
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ jIntegralClosure M A K) : x ∈ jIntegralClosure M A K' := by
  refine ⟨c4_fieldOver_mono M h hx.1, ?_⟩
  obtain ⟨p, hp, hpx⟩ := hx.2
  refine ⟨p.map (Subring.inclusion (c4_jRing_mono h)), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx

end Basics

end ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_congr qExpand_qExpand algebraMap_apply_eq_single jq evalAtJ_X ModularPolynomialData coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff jqModC jqNModC map_jqModC heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar CharPReduction.constSeries CharPModel.jBar CharPModel.affineBaseFin CharPModel.FibreModel functionFieldGeneration nonempty_modularPolynomialData exists_numberField_presentation_of_neZero"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval"
p2m_open "ModularCurve.NodeLocalized ModularCurve"

section FieldBookkeeping

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem c4_constSeries_mem_jRing_adjoin (a : A) :
    CharPReduction.constSeries A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩
      ∈ jRing A (IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)}) :=
  Subring.subset_closure (Or.inl ⟨⟨(a : AlgebraicClosure ℚ), ⟨a.2, IntermediateField.mem_adjoin_simple_self ℚ _⟩⟩, rfl⟩)

theorem c4_finiteDimensional_adjoin (a : AlgebraicClosure ℚ) :
    FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {a}) := by
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  exact IntermediateField.adjoin.finiteDimensional (halg.isAlgebraic a).isIntegral

variable {A} in
theorem c4_jRing_mono' {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') : jRing A K ≤ jRing A K' := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact Subring.subset_closure (Or.inl ⟨⟨a, a.2.1, h a.2.2⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inr rfl)

theorem c4_exists_fd_coe_mem_jRing (M : ℕ) [NeZero M] {y : modularFunctionFieldBar M}
    (hy : y ∈ CharPModel.affineBaseFin M A) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ jRing A K := by
  induction hy using Subring.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | rfl
      · exact ⟨_, c4_finiteDimensional_adjoin (a : AlgebraicClosure ℚ), c4_constSeries_mem_jRing_adjoin A a⟩
      · refine ⟨⊥, inferInstance, ?_⟩
        have : ((CharPModel.jBar M : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
          map_jqModC _
        rw [this]
        exact Subring.subset_closure (Or.inr rfl)
  | zero => exact ⟨⊥, inferInstance, by rw [ZeroMemClass.coe_zero]; exact zero_mem _⟩
  | one => exact ⟨⊥, inferInstance, by rw [OneMemClass.coe_one]; exact one_mem _⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨K₁, hK₁, h₁⟩ := ihx; obtain ⟨K₂, hK₂, h₂⟩ := ihy
      haveI := hK₁; haveI := hK₂
      exact ⟨K₁ ⊔ K₂, inferInstance, by rw [AddMemClass.coe_add]; exact add_mem (c4_jRing_mono' le_sup_left h₁) (c4_jRing_mono' le_sup_right h₂)⟩
  | neg x _ ihx =>
      obtain ⟨K₁, hK₁, h₁⟩ := ihx
      exact ⟨K₁, hK₁, by rw [NegMemClass.coe_neg]; exact neg_mem h₁⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨K₁, hK₁, h₁⟩ := ihx; obtain ⟨K₂, hK₂, h₂⟩ := ihy
      haveI := hK₁; haveI := hK₂
      exact ⟨K₁ ⊔ K₂, inferInstance, by rw [MulMemClass.coe_mul]; exact mul_mem (c4_jRing_mono' le_sup_left h₁) (c4_jRing_mono' le_sup_right h₂)⟩

theorem c4_exists_fd_forall_coeff_mem_jRing (M : ℕ) [NeZero M] (p : Polynomial ↥(CharPModel.affineBaseFin M A)) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      ∀ i, (((p.coeff i : ↥(CharPModel.affineBaseFin M A)) : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ jRing A K := by
  classical
  choose Kf hKf hmem using fun (y : ↥(CharPModel.affineBaseFin M A)) => c4_exists_fd_coe_mem_jRing A M y.2
  refine ⟨p.support.sup (fun i => Kf (p.coeff i)), ?_, ?_⟩
  · refine Finset.sup_induction (p := fun K : IntermediateField ℚ (AlgebraicClosure ℚ) => FiniteDimensional ℚ K)
      (inferInstance : FiniteDimensional ℚ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ))) ?_ ?_
    · intro K₁ hK₁ K₂ hK₂
      haveI := hK₁; haveI := hK₂
      exact IntermediateField.finiteDimensional_sup K₁ K₂
    · intro i _; exact hKf _
  · intro i
    by_cases hi : i ∈ p.support
    · exact c4_jRing_mono' (Finset.le_sup (f := fun i => Kf (p.coeff i)) hi) (hmem _)
    · rw [Polynomial.notMem_support_iff.mp hi]
      rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
      exact zero_mem _

theorem c4_isIntegral_jRing_of_monic (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (p : Polynomial ↥(CharPModel.affineBaseFin M A)) (hp : p.Monic)
    (hK : ∀ i, (((p.coeff i : ↥(CharPModel.affineBaseFin M A)) : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ jRing A K)
    (b : modularFunctionFieldBar M) (hpb : Polynomial.eval₂ (CharPModel.affineBaseFin M A).subtype b p = 0) :
    IsIntegral ↥(jRing A K) (b : LaurentSeries (AlgebraicClosure ℚ)) := by

  set P : Polynomial (LaurentSeries (AlgebraicClosure ℚ)) :=
    p.map ((modularFunctionFieldBar M).val.toRingHom.comp (CharPModel.affineBaseFin M A).subtype) with hP
  have hPm : P.Monic := hp.map _
  have hPl : P ∈ Polynomial.lifts (algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [hP, Polynomial.coeff_map]
    exact ⟨⟨_, hK i⟩, rfl⟩
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hPl hPm
  refine ⟨Q, hQm, ?_⟩
  rw [← Polynomial.eval_map, hQ, hP, Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ p (CharPModel.affineBaseFin M A).subtype (modularFunctionFieldBar M).val.toRingHom b
  rw [hpb, map_zero] at h
  exact h.symm

end FieldBookkeeping

end ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_congr qExpand_qExpand algebraMap_apply_eq_single jq evalAtJ_X ModularPolynomialData coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff jqModC jqNModC map_jqModC heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar CharPReduction.constSeries CharPModel.jBar CharPModel.affineBaseFin CharPModel.FibreModel functionFieldGeneration nonempty_modularPolynomialData exists_numberField_presentation_of_neZero"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval"
p2m_open "ModularCurve.NodeLocalized ModularCurve"

section FieldOverTransport

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem c4_coeffEmb_qExpand' (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n x) = qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) x) := by
  ext m
  by_cases hm : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := hm
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hm, qExpand_coeff_of_not_dvd n _ hm, map_zero]

theorem c4_coeffEmb_jq' : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
  exact map_jqModC _

theorem c4_jqNModC_mem_fieldOver_of_dvd (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (hd : d ∣ M) :
    jqNModC (AlgebraicClosure ℚ) d ∈ fieldOver M K := by
  have hgen := ModularCurve.functionFieldGeneration M d hd inferInstance

  have hle : (IntermediateField.adjoin ℚ ({jq, qExpand ℚ M jq} : Set (LaurentSeries ℚ))).toSubfield.map
      (coeffEmb (AlgebraicClosure ℚ)) ≤ fieldOver M K := by
    change (Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ {jq, qExpand ℚ M jq})).map _ ≤ _
    rw [RingHom.map_field_closure, Subfield.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨r, rfl⟩ | rfl | rfl
    · have : coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) r)
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) r) := by
        rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single, algebraMap_laurentSeries_eq_single]
      rw [this]
      exact Subfield.subset_closure (Or.inl ⟨⟨_, K.algebraMap_mem r⟩, rfl⟩)
    · rw [c4_coeffEmb_jq']
      exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
    · rw [c4_coeffEmb_qExpand', c4_coeffEmb_jq']
      exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  have h := hle ⟨_, hgen, rfl⟩
  rw [c4_coeffEmb_qExpand', c4_coeffEmb_jq'] at h
  exact h

theorem c4_fieldOver_le_fieldOver_mul (N q : ℕ) [NeZero N] [NeZero q] : fieldOver N K ≤ fieldOver (N * q) K := by
  rw [fieldOver, Subfield.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
  · exact c4_jqNModC_mem_fieldOver_of_dvd K (N * q) N (dvd_mul_right N q)

theorem c4_qExpand_mem_fieldOver_mul (N q : ℕ) [NeZero N] [NeZero q] {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ fieldOver N K) : qExpand (AlgebraicClosure ℚ) q x ∈ fieldOver (N * q) K := by
  have hle : (fieldOver N K).map (qExpand (AlgebraicClosure ℚ) q) ≤ fieldOver (N * q) K := by
    rw [fieldOver, RingHom.map_field_closure, Subfield.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨a, rfl⟩ | rfl | rfl
    · have : qExpand (AlgebraicClosure ℚ) q (CharPReduction.constSeries K.toSubalgebra.toSubring a)
          = CharPReduction.constSeries K.toSubalgebra.toSubring a := by
        show qExpand _ q (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ)) = _
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
        exact (algebraMap_laurentSeries_eq_single (AlgebraicClosure ℚ) (a : AlgebraicClosure ℚ)).symm
      rw [this]
      exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · exact c4_jqNModC_mem_fieldOver_of_dvd K (N * q) q (dvd_mul_left q N)
    · have : qExpand (AlgebraicClosure ℚ) q (jqNModC (AlgebraicClosure ℚ) N) = jqNModC (AlgebraicClosure ℚ) (N * q) := by
        rw [jqNModC, jqNModC, qExpand_qExpand, qExpand_congr (mul_comm q N)]
      rw [this]
      exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  exact hle ⟨x, hx, rfl⟩

include A in

theorem c4_exists_fd_coe_mem_fieldOver (M : ℕ) [NeZero M] (f : modularFunctionFieldBar M) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver M K := by
  obtain ⟨K, hK, P, Q, hQ, hPQ⟩ := ModularCurve.exists_numberField_presentation_of_neZero A f
  refine ⟨K, hK, ?_⟩
  have hev : ∀ R : MvPolynomial (Fin 2) (coeffSubring A K), modularEval M (coeffSubring A K) R ∈ fieldOver M K := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
        rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        exact Subfield.subset_closure (Or.inl ⟨⟨a, a.2.2⟩, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
        rw [map_mul]
        refine mul_mem hp ?_
        rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        fin_cases i
        · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
        · exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  have hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = modularEval M (coeffSubring A K) P / modularEval M (coeffSubring A K) Q := by
    rw [eq_div_iff hQ, hPQ]
  rw [hf]
  exact div_mem (hev P) (hev Q)

end FieldOverTransport

section IntegralityTransport

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem c4_isIntegral_jRing_jqNModC (q : ℕ) [NeZero q] (dq : ModularPolynomialData q) :
    IsIntegral ↥(jRing A K) (jqNModC (AlgebraicClosure ℚ) q) := by
  let jR : ↥(jRing A K) := ⟨jqModC (AlgebraicClosure ℚ), Subring.subset_closure (Or.inr rfl)⟩
  let f₀ : Polynomial ℤ →+* ↥(jRing A K) := Polynomial.eval₂RingHom (Int.castRingHom _) jR
  refine ⟨dq.Φ.map f₀, dq.monic.map f₀, ?_⟩
  rw [Polynomial.eval₂_map]
  have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) dq.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h0
  convert h0 using 2 <;> try rfl
  all_goals first
    | (refine Polynomial.ringHom_ext' ?_ ?_
       · exact RingHom.ext_int _ _
       · have hX : f₀ Polynomial.X = jR := Polynomial.eval₂_X _ _
         rw [RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X, c4_coeffEmb_jq', hX]
         rfl)
    | (show jqNModC (AlgebraicClosure ℚ) q = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
       rw [c4_coeffEmb_qExpand', c4_coeffEmb_jq']
       rfl)

theorem c4_isIntegral_jRing_qExpand_of_mem (q : ℕ) [NeZero q] :
    ∀ y ∈ jRing A K, IsIntegral ↥(jRing A K) (qExpand (AlgebraicClosure ℚ) q y) := by
  obtain ⟨dq⟩ := ModularCurve.nonempty_modularPolynomialData q
  let IC := integralClosure ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ))
  have hgen : Set.range (CharPReduction.constSeries (coeffSubring A K)) ∪ {jqModC (AlgebraicClosure ℚ)}
      ⊆ (IC.toSubring.comap (qExpand (AlgebraicClosure ℚ) q) : Set (LaurentSeries (AlgebraicClosure ℚ))) := by
    rintro y (⟨a, rfl⟩ | rfl)
    · show qExpand _ q _ ∈ IC
      have hc : qExpand (AlgebraicClosure ℚ) q (CharPReduction.constSeries (coeffSubring A K) a)
          = CharPReduction.constSeries (coeffSubring A K) a := by
        show qExpand _ q (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ)) = _
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
        exact (algebraMap_laurentSeries_eq_single (AlgebraicClosure ℚ) (a : AlgebraicClosure ℚ)).symm
      rw [hc, mem_integralClosure_iff]
      exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩)
    · show qExpand _ q (jqModC _) ∈ IC
      rw [mem_integralClosure_iff]
      exact c4_isIntegral_jRing_jqNModC A K q dq
  intro y hy
  exact (mem_integralClosure_iff _ _).mp ((Subring.closure_le.mpr hgen) hy)

theorem c4_isIntegral_jRing_qExpand (q : ℕ) [NeZero q] {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : IsIntegral ↥(jRing A K) x) : IsIntegral ↥(jRing A K) (qExpand (AlgebraicClosure ℚ) q x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  let S := jRing A K
  let IC := integralClosure ↥S (LaurentSeries (AlgebraicClosure ℚ))
  let W : LaurentSeries (AlgebraicClosure ℚ) →+* LaurentSeries (AlgebraicClosure ℚ) := qExpand (AlgebraicClosure ℚ) q
  have hW : ∀ y : ↥S, (W.comp S.subtype) y ∈ IC.toSubring := fun y =>
    (mem_integralClosure_iff _ _).mpr (c4_isIntegral_jRing_qExpand_of_mem A K q y y.2)
  let ψ : ↥S →+* ↥IC := (W.comp S.subtype).codRestrict IC.toSubring hW
  have hint : IsIntegral ↥IC (W x) := by
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap ↥IC (LaurentSeries (AlgebraicClosure ℚ))).comp ψ = W.comp S.subtype := RingHom.ext fun _ => rfl
    rw [hc, ← Polynomial.hom_eval₂]
    have : Polynomial.eval₂ S.subtype x p = 0 := hpx
    rw [this, map_zero]
  exact isIntegral_trans (W x) hint

theorem c4_coe_degeneracies_mem_jIntegralClosure (N q : ℕ) [NeZero N] [NeZero q]
    (b : modularFunctionFieldBar N) (hbK : (b : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver N K)
    (hbi : IsIntegral ↥(jRing A K) (b : LaurentSeries (AlgebraicClosure ℚ))) :
    ((heckeAlphaBar (AlgebraicClosure ℚ) N q b : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ jIntegralClosure (N * q) A K ∧
    ((heckeBetaBar (AlgebraicClosure ℚ) N q b : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ jIntegralClosure (N * q) A K := by
  constructor
  · rw [coe_heckeAlphaBar]
    exact ⟨c4_fieldOver_le_fieldOver_mul K N q hbK, hbi⟩
  · rw [coe_heckeBetaBar]
    exact ⟨c4_qExpand_mem_fieldOver_mul K N q hbK, c4_isIntegral_jRing_qExpand A K q hbi⟩

end IntegralityTransport

end ModularCurve.NodeLocalized

open _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem.ModularCurve.NodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    (fm : CharPModel.FibreModel N A q k red) (b : fm.BFin) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₀),
      ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), K₀ ≤ K →
        ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : ↥(modularFunctionFieldBar N)) : ↥(modularFunctionFieldBar (N * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K ∧
        ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : ↥(modularFunctionFieldBar N)) : ↥(modularFunctionFieldBar (N * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K := by
  obtain ⟨p, hp, hpb⟩ := fm.integralFin b
  obtain ⟨K₁, hK₁, hcoef⟩ := c4_exists_fd_forall_coeff_mem_jRing A N p
  obtain ⟨K₂, hK₂, hbK⟩ := c4_exists_fd_coe_mem_fieldOver A N (b : modularFunctionFieldBar N)
  haveI := hK₁; haveI := hK₂
  refine ⟨K₁ ⊔ K₂, inferInstance, fun K'' hle => ?_⟩
  have hbi : IsIntegral ↥(jRing A K'') ((b : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) :=
    c4_isIntegral_jRing_of_monic A N K'' p hp (fun i => c4_jRing_mono' (le_sup_left.trans hle) (hcoef i)) _ hpb
  have hbK' : ((b : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver N K'' :=
    c4_fieldOver_mono N (le_sup_right.trans hle) hbK
  exact c4_coe_degeneracies_mem_jIntegralClosure A K'' N q _ hbK' hbi

end

end S_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_exists_forall_le_coe_heckeAlphaBar_mem_jIntegralClosure_and_coe_heckeBetaBar_mem (solution)
