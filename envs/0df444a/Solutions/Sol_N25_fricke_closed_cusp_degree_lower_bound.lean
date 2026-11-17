-- Prove2me | solution 1 for N25.fricke_closed_cusp_degree_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:59.828091+00:00
-- url     : https://prove2.me/submissions/ba15a85b-1113-4ac6-b672-a2a825160e02

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_AlgebraicCurve_Place_not_mem_iff_ord_neg
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_N25_fricke_cusp_five_orbit
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
import Theorems.Thm_ModularCurve_coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
import Theorems.Thm_N25_cusp_galois_contraction
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_N25_Endgame_cusp_constant_fibre_degree25
import Theorems.Thm_N25_Endgame_rational_geometric_constant_extension25
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_N25_Endgame_rational_algebraic_constants25
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ModularCurve AlgebraicCurve

open scoped MatrixGroups Pointwise

namespace N25

open Endgame

/-- The transitive five-point Fricke orbit lies over a closed cusp of degree
at least five, whose normalized j-pole order is twenty-five. -/
theorem _root_.solution (ι : Qbar →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0]) :
    ∃ Q : QPlace, IsCusp j25 Q ∧ Q.ord j25 = -25 ∧ 5 ≤ Q.deg := by
  classical
  let : Algebra FQ FG := emb25.toRingHom.toAlgebra
  have he := rational_geometric_constant_extension25
  let : IsScalarTower ℚ FQ FG := he.1
  let : Algebra.IsIntegral FQ FG := he.2.1
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  obtain ⟨w, hw, hi, _, _, ht⟩ := fricke_cusp_five_orbit ι W hW
  let V (i : Fin 5) : GPlace := SemilinearAut.ofAlgAut w.symm • pG25 i
  let Q : QPlace := Place.restrictConstants FQ (V 0)
  have hc (i : Fin 5) :
      (V i).toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring := by
    obtain ⟨σ, hσ⟩ := ht.1 0 i
    have h := cusp_galois_contraction σ (V 0)
    change arithmeticGalois FQ σ • V 0 = V i at hσ
    rw [hσ] at h
    exact h
  have horder : Q.ord j25 = -25 := by
    have ho := Place.ord_restrictConstants (K := ℚ) (V 0) j25
    have hr := Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
      (K := ℚ) (K' := Qbar) (F := FQ) (F' := FG)
      he.2.2 rational_algebraic_constants25 (V 0)
    simp only [hr, Nat.cast_one, one_mul] at ho
    exact ho.symm.trans (hw 0)
  refine ⟨Q, ?_, horder, ?_⟩
  · exact (Place.not_mem_iff_ord_neg Q j25).mpr (by rw [horder]; norm_num)
  · let f : Fin 5 → {P : GPlace |
        P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring} :=
      fun i => ⟨V i, hc i⟩
    have hf : Function.Injective f := fun i j h => hi (congrArg Subtype.val h)
    have hdegree := cusp_constant_fibre_degree25 Q
    let : Finite {P : GPlace |
        P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring} := hdegree.1.to_subtype
    have hcard := Nat.card_le_card_of_injective f hf
    rw [hdegree.2] at hcard
    simpa only [Nat.card_fin] using hcard

end N25
