-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_ord_jqModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5ca11ebe-34c3-578d-b78f-54d397a73793

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_ord_sub_pow_sq_eq_one_of_ord_jqModC
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace JBranchRegularity

private theorem jGeomGen_mem_of_disj {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]
    [DecidableEq k] (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k)
    {u : Place k (modularFunctionFieldC k N)}
    (hu : u = w ∨ frobOnPlacesGeomLevel k N data hKr u = w ∨ u = frobOnPlacesGeomLevel k N data hKr w) :
    (⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ∈ u.toValuationSubring := by
  have hjw : (⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring := hw.2.1.1
  rcases hu with rfl | hφ | rfl
  · exact hjw
  ·
    rw [← hφ, mem_frobOnPlacesGeomLevel_iff, frobeniusGeomLevel_jq] at hjw
    exact (mem_valuationSubring_iff_pow_mem (ℓ := q) u.toValuationSubring _).mpr hjw
  · rw [mem_frobOnPlacesGeomLevel_iff, frobeniusGeomLevel_jq]
    exact pow_mem hjw q

end JBranchRegularity

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hj : w.ord ((⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N))
        - (⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ^ (q ^ 2)) = 1)
    (hjφ : (arithFrobC q k N • w).ord ((⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N))
        - (⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ^ (q ^ 2)) = 1) :
    ∃ (g₀ : LaurentSeries ℚ) (y : LaurentSeries ↥A) (g : ↥(modularFunctionFieldBar N))
      (gbar : ↥(modularFunctionFieldC k N)),
      g₀ ∈ modularFunctionFieldFull N ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g₀ ∧
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g₀ ∧
      (gbar : LaurentSeries k) = coeffMap red y ∧
      w.ord (gbar - gbar ^ (q ^ 2)) = 1 ∧ (arithFrobC q k N • w).ord (gbar - gbar ^ (q ^ 2)) = 1 ∧
      ∀ U : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        (P.sp U = w ∨ frobOnPlacesGeomLevel k N data hKr (P.sp U) = w ∨
            P.sp U = frobOnPlacesGeomLevel k N data hKr w) →
          g ∈ U.toValuationSubring := by
  have _ := hqN
  refine ⟨jq, jqModC ↥A,
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩,
    ⟨jqModC k, jqModC_mem k N⟩, modularFunctionField_le_full N (jq_mem N), rfl, ?_, ?_, hj, hjφ, ?_⟩
  ·
    rw [coeffMap_jqModC]
    show jqModC (AlgebraicClosure ℚ) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq
    rw [← jqModC_rat, coeffMap_jqModC]
  · show jqModC k = coeffMap red (jqModC ↥A)
    rw [coeffMap_jqModC]
  · intro U hU
    by_contra hg

    have hle : ∀ a : A,
        U.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : ↥(modularFunctionFieldBar N))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
      intro a
      have hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ U.toValuationSubring := U.algebraMap_mem' _
      have hnot : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : ↥(modularFunctionFieldBar N))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
            ∉ U.toValuationSubring := by
        intro h
        apply hg
        have h' := add_mem h hc
        rwa [sub_add_cancel] at h'
      have hne : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : ↥(modularFunctionFieldBar N))
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0
        apply hnot
        rw [h0]
        exact zero_mem _
      by_contra hpos
      push Not at hpos
      exact hnot ((Place.mem_iff_ord_nonneg U hne).mpr hpos.le)
    have hlt := P.d0_j_pole U hle

    have hmem : (⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ∈ (P.sp U).toValuationSubring :=
      JBranchRegularity.jGeomGen_mem_of_disj data hKr hw hU
    have h0 := Place.ord_nonneg_of_mem (P.sp U) hmem
    exact absurd hlt (not_lt.mpr h0)

end

end S_ModularCurve_PlaceSpecialization_exists_ord_sub_pow_sq_eq_one_of_ord_jqModC
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_ord_sub_pow_sq_eq_one_of_ord_jqModC (solution)
