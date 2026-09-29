-- Prove2me | solution 1 for ModularCurve.exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c389e9e1-9da2-5e27-b3f3-20df075fee9d

import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_exists_numberField_presentation_level
import Theorems.Thm_ModularCurve_modularRing_eq_range_modularEval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
p2m_open "ModularCurve~coeffMap_jqModC ModularCurve.NodeLocalized ModularCurve.CharPModel"
open scoped IntermediateField

theorem solution
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (f : ↥(modularFunctionFieldBar (N * q)))
    (hf : ∃ p : Polynomial ↥(affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin (N * q) A).subtype f p = 0)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
      ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ K'' → K' ≤ K'' →
        ((f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ jIntegralClosure (N * q) A K'' := by
  classical

  let ι : ↥(modularFunctionFieldBar (N * q)) →+* (LaurentSeries (AlgebraicClosure ℚ)) := (modularFunctionFieldBar (N * q)).val.toRingHom
  have hι : ∀ x : ↥(modularFunctionFieldBar (N * q)), ι x = (x : (LaurentSeries (AlgebraicClosure ℚ))) := fun x => rfl

  obtain ⟨K₁, hK₁, P, Q, hQ, hPQ⟩ := ModularCurve.exists_numberField_presentation_level (q := q) (N := N) A f
  have hev : ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), K₁ ≤ K'' → ∀ X : MvPolynomial (Fin 2) (coeffSubring A K₁),
      modularEval (N * q) (coeffSubring A K₁) X ∈ fieldOver (N * q) K'' := by
    intro K'' hle X
    have hX : modularEval (N * q) (coeffSubring A K₁) X ∈ (modularEval (N * q) (coeffSubring A K₁)).range := ⟨X, rfl⟩
    rw [← ModularCurve.modularRing_eq_range_modularEval] at hX
    refine (Subring.closure_le (t := (fieldOver (N * q) K'').toSubring)).mpr ?_ hX
    rintro x (⟨a, rfl⟩ | hx)
    ·
      refine Subfield.subset_closure (Or.inl ⟨⟨(a : AlgebraicClosure ℚ), hle a.2.2⟩, rfl⟩)
    · rcases hx with rfl | rfl
      · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
      · exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  have hfield : ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), K₁ ≤ K'' → (f : (LaurentSeries (AlgebraicClosure ℚ))) ∈ fieldOver (N * q) K'' := by
    intro K'' hle
    have hfeq : (f : (LaurentSeries (AlgebraicClosure ℚ))) = modularEval (N * q) (coeffSubring A K₁) P / modularEval (N * q) (coeffSubring A K₁) Q :=
      (eq_div_iff hQ).mpr hPQ
    rw [hfeq]
    exact div_mem (hev K'' hle P) (hev K'' hle Q)

  obtain ⟨p, hpm, hp0⟩ := hf
  let pL : Polynomial (LaurentSeries (AlgebraicClosure ℚ)) := p.map (ι.comp (affineBaseFin (N * q) A).subtype)
  have hpLm : pL.Monic := hpm.map _
  have hpL0 : Polynomial.eval (f : (LaurentSeries (AlgebraicClosure ℚ))) pL = 0 := by
    rw [Polynomial.eval_map, ← hι f, ← Polynomial.hom_eval₂, hp0, map_zero]

  have hgood : ∀ x : (LaurentSeries (AlgebraicClosure ℚ)), x ∈ (affineBaseFin (N * q) A).map (ι : ↥(modularFunctionFieldBar (N * q)) →+* (LaurentSeries (AlgebraicClosure ℚ))) →
      ∃ K₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K₀ ∧
        ∀ K'' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K'' → K₀ ≤ K'' → x ∈ jRing A K'' := by
    intro x hx
    rw [affineBaseFin, RingHom.map_closure] at hx
    induction hx using Subring.closure_induction with
    | mem y hy =>
        rcases hy with ⟨z, hz, rfl⟩
        rcases hz with ⟨a, rfl⟩ | hz
        ·
          have ha : IsIntegral ℚ (a : AlgebraicClosure ℚ) := Algebra.IsIntegral.isIntegral _
          haveI : FiniteDimensional ℚ ℚ⟮(a : AlgebraicClosure ℚ)⟯ := IntermediateField.adjoin.finiteDimensional ha
          refine ⟨ℚ⟮(a : AlgebraicClosure ℚ)⟯, inferInstance, fun K'' _ hle => ?_⟩
          have haK : (a : AlgebraicClosure ℚ) ∈ K'' := hle (IntermediateField.mem_adjoin_simple_self ℚ (a : AlgebraicClosure ℚ))
          have : ι (constantsHom (N * q) A a) = CharPReduction.constSeries (coeffSubring A K'') ⟨a, a.2, haK⟩ := rfl
          rw [this]
          exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
        · rw [Set.mem_singleton_iff] at hz
          subst hz
          refine ⟨⊥, inferInstance, fun K'' _ _ => ?_⟩
          have : ι (jBar (N * q)) = jqModC (AlgebraicClosure ℚ) := by
            show coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ)
            rw [← jqModC_rat]
            exact coeffSemilinearAut.coeffMap_jqModC _
          rw [this]
          exact Subring.subset_closure (Or.inr rfl)
    | zero => exact ⟨⊥, inferInstance, fun K'' _ _ => zero_mem _⟩
    | one => exact ⟨⊥, inferInstance, fun K'' _ _ => one_mem _⟩
    | add x y _ _ hx hy =>
        obtain ⟨K₁', h1, h1'⟩ := hx
        obtain ⟨K₂', h2, h2'⟩ := hy
        haveI := h1; haveI := h2
        exact ⟨K₁' ⊔ K₂', inferInstance, fun K'' hK hle =>
          add_mem (h1' K'' hK (le_sup_left.trans hle)) (h2' K'' hK (le_sup_right.trans hle))⟩
    | neg x _ hx =>
        obtain ⟨K₁', h1, h1'⟩ := hx
        exact ⟨K₁', h1, fun K'' hK hle => neg_mem (h1' K'' hK hle)⟩
    | mul x y _ _ hx hy =>
        obtain ⟨K₁', h1, h1'⟩ := hx
        obtain ⟨K₂', h2, h2'⟩ := hy
        haveI := h1; haveI := h2
        exact ⟨K₁' ⊔ K₂', inferInstance, fun K'' hK hle =>
          mul_mem (h1' K'' hK (le_sup_left.trans hle)) (h2' K'' hK (le_sup_right.trans hle))⟩
  have hcoeff : ∀ i : ℕ, ∃ K₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K₀ ∧
      ∀ K'' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K'' → K₀ ≤ K'' → pL.coeff i ∈ jRing A K'' := by
    intro i
    apply hgood
    rw [Polynomial.coeff_map]
    exact ⟨p.coeff i, (p.coeff i).2, rfl⟩
  choose K₀ hK₀fd hK₀ using hcoeff
  let K₂ : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ i : Fin (pL.natDegree + 1), K₀ i
  haveI : ∀ i : Fin (pL.natDegree + 1), FiniteDimensional ℚ (K₀ i) := fun i => hK₀fd i
  haveI hK₂fd : FiniteDimensional ℚ K₂ := IntermediateField.finiteDimensional_iSup_of_finite
  have hint : ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ K'' → K₂ ≤ K'' →
      IsIntegral (jRing A K'') (f : (LaurentSeries (AlgebraicClosure ℚ))) := by
    intro K'' hK hle
    have hlift : pL ∈ Polynomial.lifts (algebraMap (jRing A K'') (LaurentSeries (AlgebraicClosure ℚ))) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : n ≤ pL.natDegree
      · have hmem := hK₀ n K'' hK ((le_iSup (fun i : Fin (pL.natDegree + 1) => K₀ i) ⟨n, Nat.lt_succ_of_le hn⟩).trans hle)
        exact ⟨⟨pL.coeff n, hmem⟩, rfl⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hn)]
        exact ⟨0, map_zero _⟩
    obtain ⟨pR, hpR, -, hpRm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hpLm
    refine ⟨pR, hpRm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hpR, hpL0]

  haveI := hK₁
  refine ⟨K ⊔ K₁ ⊔ K₂, inferInstance, le_sup_left.trans le_sup_left, fun K'' hK hle => ?_⟩
  exact ⟨hfield K'' (le_sup_right.trans (le_sup_left.trans hle)), hint K'' hK (le_sup_right.trans hle)⟩

end S_ModularCurve_exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin
end P2MW
export P2MW.S_ModularCurve_exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin (solution)
