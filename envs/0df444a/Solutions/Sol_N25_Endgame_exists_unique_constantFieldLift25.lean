-- Prove2me | solution 1 for N25.Endgame.exists_unique_constantFieldLift25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:52.971196+00:00
-- url     : https://prove2.me/submissions/7d7b741c-050b-47e4-8e9c-e7fbebd3149a

import Mathlib
import Definitions.Def_N25_ConstantFieldLift
import Theorems.Thm_N25_Endgame_rational_geometric_constant_extension25
import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_N25_GammaH25_finiteIndex
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic

set_option autoImplicit false

open ModularCurve AlgebraicCurve

namespace N25.Endgame

theorem _root_.solution (P : QPlace) (hP : P.deg = 1) :
    ∃ P' : GPlace, IsConstantFieldLift25 P P' ∧
      ∀ Q' : GPlace, Q'.toValuationSubring.comap emb25.toRingHom =
        P.toValuationSubring → Q' = P' := by
  let : Algebra FQ FG := emb25.toRingHom.toAlgebra
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  have he := rational_geometric_constant_extension25
  let : IsScalarTower ℚ FQ FG := he.1
  let : Γ25.FiniteIndex := N25.GammaH25_finiteIndex
  obtain ⟨x, hx, hfd⟩ := JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
    Γ25 (translation_mem_GammaH 25 N25.H25)
  let : IsCurveOver ℚ FQ := isCurveOver_of_transcendental_of_perfectField hx hfd
  have hfg : ∃ x : FQ, Transcendental ℚ x ∧
      FiniteDimensional (IntermediateField.adjoin ℚ ({x} : Set FQ)) FQ := ⟨x,hx,hfd⟩
  have hfg' : ∃ x : FG, Transcendental Qbar x ∧
      FiniteDimensional (IntermediateField.adjoin Qbar ({x} : Set FG)) FG :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange Qbar Γ25
      (translation_mem_GammaH 25 N25.H25)
  have hgen : IntermediateField.adjoin Qbar (Set.range (algebraMap FQ FG)) = ⊤ := by
    let S := IntermediateField.adjoin Qbar (Set.range (algebraMap FQ FG))
    let T : Subalgebra FQ FG :=
      { carrier := S
        zero_mem' := S.zero_mem
        one_mem' := S.one_mem
        add_mem' := S.add_mem
        mul_mem' := S.mul_mem
        algebraMap_mem' := fun f => IntermediateField.subset_adjoin _ _ ⟨f,rfl⟩ }
    have hle : Algebra.adjoin FQ (Set.range (algebraMap Qbar FG)) ≤ T := by
      apply Algebra.adjoin_le
      rintro _ ⟨c,rfl⟩
      exact S.algebraMap_mem c
    rw [he.2.2] at hle
    apply top_unique
    intro y hy
    exact hle (show y ∈ (⊤ : Subalgebra FQ FG) from trivial)
  obtain ⟨P', hc, ho, hu⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
      ℚ FQ Qbar FG hfg hfg' (constantsAreBase_of_deg_eq_one P hP) hgen P hP
  exact ⟨P', ⟨hc,ho⟩, hu⟩

end N25.Endgame
