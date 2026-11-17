-- Prove2me | solution 1 for N25.GlobalKummer.exists_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:15.861511+00:00
-- url     : https://prove2.me/submissions/2a5af453-1b84-4ccc-964a-b67847185766

import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC

noncomputable section

namespace N25.GlobalKummer

/-- Every geometric divisor class is fixed over a finite extension, without a torsion assumption. -/
theorem _root_.solution (x : J) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : Gal, σ ∈ L.fixingSubgroup → σ • x = x := by
  classical
  obtain ⟨D, rfl⟩ := AlgebraicCurve.Pic0.mk_surjective x
  letI : (CohCarrier.GammaH 25 H25).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH 25 H25)
  have hfg := ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
    (CohCarrier.GammaH 25 H25) (ModularCurve.translation_mem_GammaH 25 H25)
  have hdiv : ∀ E : AlgebraicCurve.Divisor (AlgebraicClosure ℚ)
      (ModularCurve.xHFunctionFieldBar 25 H25),
      ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
        ∀ σ : Gal, σ ∈ L.fixingSubgroup →
          ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField 25 H25) σ • E = E := by
    intro E
    induction E using Finsupp.induction with
    | zero =>
      exact ⟨⊥, inferInstance, fun σ _ => smul_zero _⟩
    | @single_add v n E hv hn ih =>
      obtain ⟨L, hL, hfix⟩ := ih
      obtain ⟨K, hK, hvfix⟩ :=
        ModularCurve.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
          (ModularCurve.xHFunctionField 25 H25) hfg v
      letI := hL
      letI := hK
      refine ⟨L ⊔ K, L.finiteDimensional_sup K, ?_⟩
      intro σ hσ
      rw [smul_add, AlgebraicCurve.SemilinearAut.smul_single,
        hvfix σ (IntermediateField.fixingSubgroup_antitone le_sup_right hσ),
        hfix σ (IntermediateField.fixingSubgroup_antitone le_sup_left hσ)]
  obtain ⟨L, hL, hfix⟩ := hdiv D.val
  refine ⟨L, hL, ?_⟩
  intro σ hσ
  change ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField 25 H25) σ •
    AlgebraicCurve.Pic0.mk D = AlgebraicCurve.Pic0.mk D
  rw [AlgebraicCurve.SemilinearAut.pic0_smul_mk]
  apply congrArg AlgebraicCurve.Pic0.mk
  apply Subtype.ext
  exact hfix σ hσ

end N25.GlobalKummer
