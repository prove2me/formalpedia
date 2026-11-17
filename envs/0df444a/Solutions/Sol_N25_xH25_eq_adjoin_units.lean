-- Prove2me | solution 1 for N25.xH25_eq_adjoin_units
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:09.449071+00:00
-- url     : https://prove2.me/submissions/6e2c2e44-f17a-49c1-a96e-63fb509713bf

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_Endgame_pQ25_degree
import Theorems.Thm_N25_Endgame_xH25C_isCurveOver
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_N25_Endgame_xH25C_essFiniteType
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_N25_Endgame_adjoin_pair_eq_top_of_coprime_finrank
import Theorems.Thm_N25_U25_orders_rational
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_N25_U25C_ne_zero
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType

set_option autoImplicit false

noncomputable section

open AlgebraicCurve N25.Endgame

namespace N25

/-- A complete list of the orders computes the degree over the simple subfield. -/
private theorem finrank_eq_sum_poles
    [IsCurveOver ℚ FQ] [FiniteDimensional ℚ (LSpace (0 : Divisor ℚ FQ))]
    (f : FQ) (hf : Transcendental ℚ f)
    [FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set FQ)) FQ]
    (a : Fin 5 → ℤ) (ha : ∀ i, (pQ25 i).ord f = a i)
    (hs : ∀ P : QPlace, (∀ i, P ≠ pQ25 i) → P.ord f = 0) :
    (Module.finrank (IntermediateField.adjoin ℚ ({f} : Set FQ)) FQ : ℤ) =
      ∑ i : Fin 5, max 0 (-a i) := by
  classical
  let D : Divisor ℚ FQ := ∑ i : Fin 5, Finsupp.single (pQ25 i) (max 0 (-a i))
  have hinj : Function.Injective pQ25 := cuspChoice25_spec.2.1
  have hD (P : QPlace) : D P = max 0 (-P.ord f) := by
    by_cases hP : ∃ i : Fin 5, P = pQ25 i
    · obtain ⟨i, rfl⟩ := hP
      simp [D, Finset.sum_apply, Finsupp.single_apply, hinj.eq_iff, eq_comm, ha]
    · have hn (i : Fin 5) : pQ25 i ≠ P := by
        intro h
        exact hP ⟨i, h.symm⟩
      have hz : P.ord f = 0 := hs P (fun i h => hP ⟨i, h⟩)
      simp [D, Finset.sum_apply, hn, hz]
  calc
    _ = Divisor.degree D :=
      (Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord f hf D hD).symm
    _ = _ := by simp [D, map_sum, Divisor.degree_single, pQ25_degree]

/-- The complete rational unit divisors have coprime pole degrees four and seven. -/
theorem _root_.solution :
    IntermediateField.adjoin ℚ
      ({U25 0, U25 0 / U25 1} : Set FQ) = ⊤ := by
  have hA : FBaseAlgebra25 ℚ = (inferInstance : Algebra ℚ FQ) :=
    Subsingleton.elim _ _
  have : IsCurveOver ℚ FQ := by
    have h := xH25C_isCurveOver ℚ
    rwa [hA] at h
  have : Algebra.EssFiniteType ℚ FQ := by
    have h := xH25C_essFiniteType ℚ
    rwa [hA] at h
  have hC := constantsAreBase_of_deg_eq_one (pQ25 0) (pQ25_degree 0)
  have : FiniteDimensional ℚ (LSpace (0 : Divisor ℚ FQ)) := by
    rw [hC]
    infer_instance
  have hu : U25 0 ≠ 0 := U25C_ne_zero ℚ 0
  have hv : U25 1 ≠ 0 := U25C_ne_zero ℚ 1
  have hord (P : QPlace) :
      P.ord (U25 0 / U25 1) = P.ord (U25 0) - P.ord (U25 1) := by
    rw [div_eq_mul_inv, P.ord_mul hu (inv_ne_zero hv), P.ord_inv]
    rfl
  have huT : Transcendental ℚ (U25 0) := by
    apply (pQ25 0).transcendental_of_ord_ne_zero
    rw [(U25_orders_rational 0).1 0]
    norm_num [unitOrders25]
  have hvT : Transcendental ℚ (U25 0 / U25 1) := by
    apply (pQ25 1).transcendental_of_ord_ne_zero
    rw [hord, (U25_orders_rational 0).1 1, (U25_orders_rational 1).1 1]
    norm_num [unitOrders25]
  have : FiniteDimensional (IntermediateField.adjoin ℚ ({U25 0} : Set FQ)) FQ :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType huT
  have : FiniteDimensional
      (IntermediateField.adjoin ℚ ({U25 0 / U25 1} : Set FQ)) FQ :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hvT
  have hfour : Module.finrank (IntermediateField.adjoin ℚ ({U25 0} : Set FQ)) FQ = 4 := by
    have h := finrank_eq_sum_poles (U25 0) huT (unitOrders25 0)
      (U25_orders_rational 0).1 (U25_orders_rational 0).2
    norm_num [Fin.sum_univ_succ, unitOrders25] at h
    exact_mod_cast h
  have hseven :
      Module.finrank (IntermediateField.adjoin ℚ ({U25 0 / U25 1} : Set FQ)) FQ = 7 := by
    have h := finrank_eq_sum_poles (U25 0 / U25 1) hvT
      (fun i => unitOrders25 0 i - unitOrders25 1 i)
      (fun i => by rw [hord, (U25_orders_rational 0).1 i, (U25_orders_rational 1).1 i])
      (fun P hP => by
        rw [hord, (U25_orders_rational 0).2 P hP, (U25_orders_rational 1).2 P hP]
        exact sub_self 0)
    norm_num [Fin.sum_univ_succ, unitOrders25] at h
    exact_mod_cast h
  apply adjoin_pair_eq_top_of_coprime_finrank
  rw [hfour, hseven]
  norm_num

end N25
