-- Prove2me | solution 1 for N25.Endgame.U25_orders_special_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:13.517842+00:00
-- url     : https://prove2.me/submissions/bdce7361-12da-4e71-903e-0cbba9294179

import Mathlib
import Theorems.Thm_N25_coe_U25C
import Definitions.Def_N25_Units
import Theorems.Thm_N25_unitSeries25_mem
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Theorems.Thm_N25_U25_orders_geometric
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_N25_unitSeries25_coeffEmb
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
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Theorems.Thm_N25_unitSeries25_leadingCoeff
import Theorems.Thm_N25_unitSeries25_normalization
import Theorems.Thm_N25_Endgame_cusp_reductions_injective_good
import Definitions.Def_N25_PointDifference
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators

open ModularCurve HahnSeries AlgebraicCurve

namespace N25.Endgame

private theorem coeffMap_powerSeries
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R s) =
      HahnSeries.ofPowerSeries ℤ S (s.map f) := by
  ext n
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · simp only [coeffMap_coeff, ofPowerSeries_coeff_of_neg _ hn, map_zero]

/-- The integral numerator and the inverse eta unit give a Laurent series over ℤ
whose image is the specified unpowered unit in every coefficient field. -/
private theorem unitSeries_integral_lift (i : Fin 5) :
    ∃ s : LaurentSeries ℤ, ∀ (K : Type*) [Field K],
      coeffMap (Int.castRingHom K) s = N25.unitSeries25 K i := by
  let s : LaurentSeries ℤ :=
    HahnSeries.single (-3) 1 *
      HahnSeries.ofPowerSeries ℤ ℤ (N25.unitNumeratorSeries25 i) *
      HahnSeries.ofPowerSeries ℤ ℤ (dedekindEtaUnitInv ^ 3)
  refine ⟨s, ?_⟩
  intro K instK
  have hmap : coeffMap (Int.castRingHom K) s =
      HahnSeries.single (-3) 1 * intSeriesC K (N25.unitNumeratorSeries25 i) *
        intSeriesC K (dedekindEtaUnitInv ^ 3) := by
    simp only [s, map_mul, coeffMap_single, map_one, coeffMap_powerSeries, intSeriesC]
  rw [hmap, N25.unitSeries25]
  apply (eq_div_iff (N25.unitSeries25_normalization K).1).mpr
  have hinv : intSeriesC K (dedekindEtaUnitInv ^ 3) *
      intSeriesC K (dedekindEtaUnit ^ 3) = 1 := by
    rw [← intSeriesC_mul, ← mul_pow, mul_comm dedekindEtaUnitInv,
      dedekindEtaUnit_mul_inv, one_pow, intSeriesC_one]
  have hden : intSeriesC K N25.unitDenominatorSeries25 =
      HahnSeries.single (3 : ℤ) 1 * intSeriesC K (dedekindEtaUnit ^ 3) := by
    simp [N25.unitDenominatorSeries25, mul_pow, intSeriesC, map_mul, map_pow]
  rw [hden]
  calc
    _ = intSeriesC K (N25.unitNumeratorSeries25 i) *
        ((HahnSeries.single (-3) 1 * HahnSeries.single (3 : ℤ) 1) *
          (intSeriesC K (dedekindEtaUnitInv ^ 3) *
            intSeriesC K (dedekindEtaUnit ^ 3))) := by ring
    _ = intSeriesC K (N25.unitNumeratorSeries25 i) := by
      simp [hinv, HahnSeries.single_mul_single]

/-- Specialization preserves the complete divisor of each unpowered unit:
separation prevents collisions between the five cusp multiplicities. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (D : RedDatum25 p) (i : Fin 5) :
    (∀ j : Fin 5,
      (redPlace25 D (pG25 j)).ord (N25.U25C (κ D.A) i) =
        N25.unitOrders25 i j) ∧
    ∀ P : SpecialPlace D.A,
      (∀ j : Fin 5, P ≠ redPlace25 D (pG25 j)) →
        P.ord (N25.U25C (κ D.A) i) = 0 := by
  classical
  let : Algebra (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25).algebra
  have hsep := cusp_reductions_injective_good p hp D
  have hinj : Function.Injective pG25 := fun a b h => hsep (congrArg (redPlace25 D) h)
  obtain ⟨s, hs⟩ := unitSeries_integral_lift i
  let y : LaurentSeries D.A := coeffMap (Int.castRingHom D.A) s
  have hgeneric : coeffMap D.A.subtype y =
      (emb25 (N25.U25 i) : LaurentSeries Qbar) := by
    rw [coe_emb25, show (N25.U25 i).1 = N25.unitSeries25 ℚ i from N25.coe_U25C ℚ i]
    change coeffMap D.A.subtype y = coeffEmb Qbar (N25.unitSeries25 ℚ i)
    rw [N25.unitSeries25_coeffEmb]
    dsimp only [y]
    rw [coeffMap_coeffMap]
    exact (coeffMap_congr (Subsingleton.elim _ _) s).trans (hs Qbar)
  have hspecial : coeffMap (IsLocalRing.residue D.A) y =
      N25.unitSeries25 (κ D.A) i := by
    dsimp only [y]
    rw [coeffMap_coeffMap]
    exact (coeffMap_congr (Subsingleton.elim _ _) s).trans (hs (κ D.A))
  have hy : coeffMap D.A.subtype y ∈ FG := by
    rw [hgeneric]
    exact (emb25 (N25.U25 i)).property
  have hyk : coeffMap (IsLocalRing.residue D.A) y ∈ FSpecial D.A := by
    rw [hspecial]
    exact N25.unitSeries25_mem (κ D.A) i
  have hne : coeffMap (IsLocalRing.residue D.A) y ≠ 0 := by
    rw [hspecial]
    intro hzero
    have hc := N25.unitSeries25_leadingCoeff (κ D.A) i
    rw [hzero] at hc
    exact zero_ne_one hc
  let E : Divisor Qbar FG :=
    ∑ j : Fin 5, Finsupp.single (pG25 j) (N25.unitOrders25 i j)
  have hE : ∀ P : GPlace,
      E P = P.ord (⟨coeffMap D.A.subtype y, hy⟩ : FG) := by
    have heq : (⟨coeffMap D.A.subtype y, hy⟩ : FG) =
        emb25 (N25.U25 i) := Subtype.ext hgeneric
    rw [heq]
    intro P
    by_cases hP : ∃ j, pG25 j = P
    · obtain ⟨j, rfl⟩ := hP
      rw [(N25.U25_orders_geometric i).1]
      simp [E, Finset.sum_apply, Finsupp.single_apply, hinj.eq_iff]
    · have hn : ∀ j, P ≠ pG25 j := fun j h => hP ⟨j, h.symm⟩
      rw [(N25.U25_orders_geometric i).2 P hn]
      simp [E, Finset.sum_apply, fun j => (hn j).symm]
  have hred := (isPlaceReductionQExpModL_placeReductionQExpModL D.hred).2
    y hy hyk hne E hE
  have hspec : (⟨coeffMap (IsLocalRing.residue D.A) y, hyk⟩ : FSpecial D.A) =
      N25.U25C (κ D.A) i := Subtype.ext (hspecial.trans (N25.coe_U25C (κ D.A) i).symm)
  have hmap : Finsupp.mapDomain (redPlace25 D) E =
      ∑ j : Fin 5,
        Finsupp.single (redPlace25 D (pG25 j)) (N25.unitOrders25 i j) := by
    change (Finsupp.mapDomain.addMonoidHom (redPlace25 D))
      (∑ j : Fin 5, Finsupp.single (pG25 j) (N25.unitOrders25 i j)) = _
    simp only [map_sum, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
  have hpoint (P : SpecialPlace D.A) :
      (Finsupp.mapDomain (redPlace25 D) E) P =
        P.ord (⟨coeffMap (IsLocalRing.residue D.A) y, hyk⟩ : FSpecial D.A) := by
    exact hred P
  refine ⟨?_, ?_⟩
  · intro j
    rw [← hspec]
    exact (hpoint (redPlace25 D (pG25 j))).symm.trans (by
      rw [hmap]
      simp [Finset.sum_apply, Finsupp.single_apply, hsep.eq_iff])
  · intro P hP
    rw [← hspec]
    exact (hpoint P).symm.trans (by
      rw [hmap]
      simp [Finset.sum_apply, fun j => (hP j).symm])

end N25.Endgame
