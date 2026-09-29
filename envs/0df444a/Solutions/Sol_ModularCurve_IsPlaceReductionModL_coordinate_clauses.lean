-- Prove2me | solution 1 for ModularCurve.IsPlaceReductionModL.coordinate_clauses
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2d138d66-5555-5585-91c9-e30bb466285f

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsPlaceReductionModL_coordinate_clauses
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "IsPlaceReductionModL modularFunctionFieldBar qExpand qExpand_one_apply jq dedekindPsi jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange coeffMap_jqModC coeffMap_jqNModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full jqModC jqNModC jqNModC_mem jBar jpBar transcendental_jqModC transcendental_jqNModC dedekindPsi_pos finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi CompEq.finrank_adjoin_jBar_eq_dedekindPsi finiteDimensional_adjoin_coeffEmb_jq_full deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional exists_frickeAlgEquiv_modularFunctionFieldBar"
namespace IsPlaceReductionModL
namespace CoordinateClausesAux
p2m_open "ModularCurve"

open Classical in
theorem mapDomain_apply_eq_sum {α β : Type*} (r : α → β) (D : α →₀ ℤ) (Q : β) :
    Finsupp.mapDomain r D Q = ∑ a ∈ D.support with r a = Q, D a := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : r a = Q
  · rw [if_pos h, h, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_apply, if_neg h]

theorem mapDomain_nonneg {α β : Type*} (r : α → β) {D : α →₀ ℤ} (hD : ∀ a, 0 ≤ D a)
    (Q : β) : 0 ≤ Finsupp.mapDomain r D Q := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_nonneg fun a _ => hD a

theorem le_mapDomain_apply {α β : Type*} (r : α → β) {D : α →₀ ℤ} (hD : ∀ a, 0 ≤ D a)
    (w : α) : D w ≤ Finsupp.mapDomain r D (r w) := by
  classical
  rw [mapDomain_apply_eq_sum]
  by_cases hw : w ∈ D.support
  · exact Finset.single_le_sum (f := fun a => D a) (fun a _ => hD a)
      (Finset.mem_filter.mpr ⟨hw, rfl⟩)
  · rw [Finsupp.notMem_support_iff.mp hw]
    exact Finset.sum_nonneg fun a _ => hD a

section Divisors

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum, AddMonoidHom.mulRight_apply]

theorem eq_zero_of_nonneg_of_degree_nonpos {D : Divisor K F} (hD : ∀ v, 0 ≤ D v)
    (hdeg : ∀ v : Place K F, 0 < v.deg) (hD0 : Divisor.degree D ≤ 0) : D = 0 := by
  ext v
  by_contra hv
  have hpos : 0 < D v := lt_of_le_of_ne (hD v) (Ne.symm hv)
  have hmem : v ∈ D.support := Finsupp.mem_support_iff.mpr hv
  have h1 : D v * (v.deg : ℤ) ≤ Divisor.degree D := by
    rw [degree_eq_sum]
    exact Finset.single_le_sum (f := fun v => D v * (v.deg : ℤ))
      (fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)) hmem
  have h2 : 0 < D v * (v.deg : ℤ) := mul_pos hpos (by exact_mod_cast hdeg v)
  omega

theorem degree_mapDomain {k Fb : Type*} [Field k] [Field Fb] [Algebra k Fb]
    (r : Place K F → Place k Fb) (hdeg : ∀ P, (r P).deg = P.deg) (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, hdeg]

theorem min_ord_zero_le_ord_add_algebraMap (v : Place K F) {f : F} (hf : f ≠ 0) (c : K)
    (hfc : f + algebraMap K F c ≠ 0) : min (v.ord f) 0 ≤ v.ord (f + algebraMap K F c) := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, add_zero]
    exact min_le_left _ _
  · have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
    have := Place.min_ord_le_ord_add v hf hc' hfc
    rwa [Place.ord_algebraMap] at this

theorem ne_zero_of_ne_algebraMap {x : F} (hx : ∀ c : K, x ≠ algebraMap K F c) : x ≠ 0 :=
  fun h => hx 0 (by rw [h, map_zero])

theorem sub_algebraMap_ne_zero {x : F} (hx : ∀ c : K, x ≠ algebraMap K F c) (c : K) :
    x - algebraMap K F c ≠ 0 :=
  fun h => hx c (sub_eq_zero.mp h)

theorem max_neg_ord_sub_algebraMap (v : Place K F) {x : F} (hx : ∀ c : K, x ≠ algebraMap K F c)
    (c : K) : max 0 (-v.ord (x - algebraMap K F c)) = max 0 (-v.ord x) := by
  have hx0 : x ≠ 0 := ne_zero_of_ne_algebraMap hx
  have hxc : x - algebraMap K F c ≠ 0 := sub_algebraMap_ne_zero hx c
  have h1 : min (v.ord x) 0 ≤ v.ord (x - algebraMap K F c) := by
    have := min_ord_zero_le_ord_add_algebraMap v hx0 (-c)
      (by rw [map_neg, ← sub_eq_add_neg]; exact hxc)
    rwa [map_neg, ← sub_eq_add_neg] at this
  have h2 : min (v.ord (x - algebraMap K F c)) 0 ≤ v.ord x := by
    have := min_ord_zero_le_ord_add_algebraMap v hxc c (by rw [sub_add_cancel]; exact hx0)
    rwa [sub_add_cancel] at this
  omega

theorem core {k Fb : Type*} [Field k] [Field Fb] [Algebra k Fb] {ι : Type*}
    (r : Place K F → Place k Fb)
    (hdeg : ∀ P, (r P).deg = P.deg)
    (hdegb : ∀ Q : Place k Fb, 0 < Q.deg)
    (hdiv : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F, ∀ v, D v = v.ord f)
    (x : F) (xb : Fb) (hx : ∀ c : K, x ≠ algebraMap K F c)
    (hxb : ∀ c : k, xb ≠ algebraMap k Fb c)
    (hrat : ∀ w : Place K F, x ∈ w.toValuationSubring →
      ∃ c : K, 0 < w.ord (x - algebraMap K F c))
    (Px : Divisor K F) (hPx : ∀ v, Px v = max 0 (-v.ord x))
    (Pxb : Divisor k Fb) (hPxb : ∀ w, Pxb w = max 0 (-w.ord xb))
    (hle : Divisor.degree Px ≤ Divisor.degree Pxb)
    (emb : ι → K) (red : ι → k) (i₀ : ι)
    (hS1 : ∀ (i : ι) (D : Divisor K F), (∀ v, D v = v.ord (x - algebraMap K F (emb i))) →
      ∀ Q, Finsupp.mapDomain r D Q = Q.ord (xb - algebraMap k Fb (red i)))
    (hS2 : ∀ b : K, (∀ i, emb i ≠ b) → ∀ D : Divisor K F,
      (∀ v, D v = v.ord (x - algebraMap K F b)) → Finsupp.mapDomain r D = 0) :
    (∀ (w : Place K F) (i : ι), 0 < w.ord (x - algebraMap K F (emb i)) →
        0 < (r w).ord (xb - algebraMap k Fb (red i))) ∧
    (∀ w : Place K F, (∀ i : ι, w.ord (x - algebraMap K F (emb i)) ≤ 0) →
        (r w).ord xb < 0) := by
  classical
  have hxc : ∀ c : K, x - algebraMap K F c ≠ 0 := sub_algebraMap_ne_zero hx

  choose Dc hDc using fun c : K => hdiv _ (hxc c)

  have hZ : ∀ c v, (Dc c + Px) v = max 0 (v.ord (x - algebraMap K F c)) := by
    intro c v
    rw [Finsupp.add_apply, hDc, hPx, ← max_neg_ord_sub_algebraMap v hx c]
    omega
  have hZnn : ∀ c v, 0 ≤ (Dc c + Px) v := fun c v => by rw [hZ]; exact le_max_left _ _
  have hPxnn : ∀ v, 0 ≤ Px v := fun v => by rw [hPx]; exact le_max_left _ _

  have hRPx : Finsupp.mapDomain r Px = Pxb := by
    have hΔnn : ∀ Q, 0 ≤ (Finsupp.mapDomain r Px - Pxb) Q := by
      intro Q
      rw [Finsupp.sub_apply, hPxb, ← max_neg_ord_sub_algebraMap Q hxb (red i₀)]
      have h1 : 0 ≤ Finsupp.mapDomain r Px Q := mapDomain_nonneg r hPxnn Q
      have h2 : 0 ≤ Finsupp.mapDomain r (Dc (emb i₀) + Px) Q := mapDomain_nonneg r (hZnn _) Q
      have h3 : Finsupp.mapDomain r (Dc (emb i₀) + Px) Q =
          Q.ord (xb - algebraMap k Fb (red i₀)) + Finsupp.mapDomain r Px Q := by
        rw [Finsupp.mapDomain_add, Finsupp.add_apply, hS1 i₀ (Dc (emb i₀)) (hDc _)]
      omega
    have hΔdeg : Divisor.degree (Finsupp.mapDomain r Px - Pxb) ≤ 0 := by
      rw [map_sub, degree_mapDomain r hdeg]
      omega
    exact sub_eq_zero.mp (eq_zero_of_nonneg_of_degree_nonpos hΔnn hdegb hΔdeg)

  have hRZ : ∀ i Q, Finsupp.mapDomain r (Dc (emb i) + Px) Q =
      max 0 (Q.ord (xb - algebraMap k Fb (red i))) := by
    intro i Q
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, hS1 i (Dc (emb i)) (hDc _), hRPx, hPxb,
      ← max_neg_ord_sub_algebraMap Q hxb (red i)]
    omega
  have hRZ' : ∀ b, (∀ i, emb i ≠ b) → Finsupp.mapDomain r (Dc b + Px) = Pxb := by
    intro b hb
    rw [Finsupp.mapDomain_add, hS2 b hb (Dc b) (hDc _), zero_add, hRPx]
  refine ⟨fun w i hi => ?_, fun w hw => ?_⟩
  · have h1 : (Dc (emb i) + Px) w ≤ Finsupp.mapDomain r (Dc (emb i) + Px) (r w) :=
      le_mapDomain_apply r (hZnn _) w
    rw [hRZ, hZ] at h1
    have h2 : 0 < max 0 (w.ord (x - algebraMap K F (emb i))) := lt_max_of_lt_right hi
    have h3 := lt_of_lt_of_le h2 h1
    omega
  · suffices h : 0 < Pxb (r w) by
      rw [hPxb] at h
      omega
    rcases lt_or_ge (w.ord x) 0 with hpole | hint
    · have h1 : Px w ≤ Finsupp.mapDomain r Px (r w) := le_mapDomain_apply r hPxnn w
      rw [hRPx] at h1
      have h2 : 0 < Px w := by rw [hPx]; omega
      omega
    · have hx0 : x ≠ 0 := ne_zero_of_ne_algebraMap hx
      have hmem : x ∈ w.toValuationSubring := (Place.mem_iff_ord_nonneg w hx0).mpr hint
      obtain ⟨c, hc⟩ := hrat w hmem
      have hcS : ∀ i, emb i ≠ c := by
        intro i h
        have := hw i
        rw [h] at this
        omega
      have h1 : (Dc c + Px) w ≤ Finsupp.mapDomain r (Dc c + Px) (r w) :=
        le_mapDomain_apply r (hZnn _) w
      rw [hRZ' c hcS, hZ] at h1
      have h2 : 0 < max 0 (w.ord (x - algebraMap K F c)) := lt_max_of_lt_right hc
      omega

theorem ne_algebraMap_of_transcendental {x : F} (hx : Transcendental K x) (c : K) :
    x ≠ algebraMap K F c := fun h => hx (by rw [h]; exact isAlgebraic_algebraMap c)

theorem transcendental_of_coe {L : Type*} [Field L] [Algebra K L] {S : IntermediateField K L}
    {x : S} (h : Transcendental K (x : L)) : Transcendental K x :=
  fun hx => h (IntermediateField.isAlgebraic_iff.mp hx)

theorem ord_one_sub_algebraMap_inv_mul (v : Place K F) {x : F}
    (hx : ∀ c : K, x ≠ algebraMap K F c) {b : K} (hb : b ≠ 0) :
    v.ord (1 - algebraMap K F b⁻¹ * x) = v.ord (x - algebraMap K F b) := by
  have hfac : (1 - algebraMap K F b⁻¹ * x) = algebraMap K F (-b⁻¹) * (x - algebraMap K F b) := by
    rw [map_neg, neg_mul, mul_sub, ← map_mul, inv_mul_cancel₀ hb, map_one]
    ring
  have hne : algebraMap K F (-b⁻¹) ≠ 0 := (map_ne_zero _).mpr (neg_ne_zero.mpr (inv_ne_zero hb))
  rw [hfac, Place.ord_mul v hne (sub_algebraMap_ne_zero hx b), Place.ord_algebraMap, zero_add]

theorem exists_ord_sub_algebraMap_pos (w : Place K F) (hw : w.IsRational) {x : F}
    (hx : ∀ c : K, x ≠ algebraMap K F c) (hmem : x ∈ w.toValuationSubring) :
    ∃ c : K, 0 < w.ord (x - algebraMap K F c) := by
  refine ⟨w.evalAt x, ?_⟩
  have hcmem : algebraMap K F (w.evalAt x) ∈ w.toValuationSubring := w.algebraMap_mem' _
  have hmem' : x - algebraMap K F (w.evalAt x) ∈ w.toValuationSubring := sub_mem hmem hcmem
  have hmax : (⟨x - algebraMap K F (w.evalAt x), hmem'⟩ : w.toValuationSubring) ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have hsplit : (⟨x - algebraMap K F (w.evalAt x), hmem'⟩ : w.toValuationSubring) =
        ⟨x, hmem⟩ - ⟨algebraMap K F (w.evalAt x), hcmem⟩ := rfl
    rw [hsplit, map_sub, ← w.algebraMap_evalAt hw hmem, ← w.algebraMap_evalAt hw hcmem,
      Place.evalAt_algebraMap, sub_self]
  rcases (Place.mk_mem_maximalIdeal_iff w hmem').mp hmax with h | h
  · exact absurd h (sub_algebraMap_ne_zero hx _)
  · exact h

end Divisors

section Application

p2m_open "ModularCurve P2MW.S_ModularCurve_IsPlaceReductionModL_coordinate_clauses.ModularCurve IsLocalRing HahnSeries"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

theorem transfer (N : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N))
    (hr : IsPlaceReductionModL A N r) (y : LaurentSeries A)
    (e : modularFunctionFieldBar N) (eb : modularFunctionFieldFullC (ResidueField A) N)
    (he : coeffMap A.subtype y = (e : LaurentSeries (AlgebraicClosure ℚ)))
    (heb : coeffMap (residue A) y = (eb : LaurentSeries (ResidueField A)))
    (hne : eb ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ P, D P = P.ord e) :
    ∀ Q, Finsupp.mapDomain r D Q = Q.ord eb := by
  have hy : coeffMap A.subtype y ∈
      laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) := by
    rw [he]; exact e.2
  have hyk : coeffMap (residue A) y ∈ modularFunctionFieldFullC (ResidueField A) N := by
    rw [heb]; exact eb.2
  have h1 : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) = e := Subtype.ext he
  have h2 : (⟨coeffMap (residue A) y, hyk⟩ : modularFunctionFieldFullC (ResidueField A) N) = eb :=
    Subtype.ext heb
  have hne' : coeffMap (residue A) y ≠ 0 := by
    rw [heb]
    exact fun h => hne (ZeroMemClass.coe_eq_zero.mp h)
  intro Q
  have := hr.2 y hy hyk hne' D (fun P => by rw [h1]; exact hD P) Q
  rwa [h2] at this

theorem spec_integral (N : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N))
    (hr : IsPlaceReductionModL A N r) (z : LaurentSeries A)
    (x : modularFunctionFieldBar N) (xb : modularFunctionFieldFullC (ResidueField A) N)
    (hzx : coeffMap A.subtype z = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hzxb : coeffMap (residue A) z = (xb : LaurentSeries (ResidueField A)))
    (hxb : ∀ c, xb ≠ algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) c)
    (a : A) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ v, D v = v.ord (x - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a : AlgebraicClosure ℚ))) (Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)) :
    Finsupp.mapDomain r D Q = Q.ord (xb - algebraMap (ResidueField A)
      (modularFunctionFieldFullC (ResidueField A) N) (residue A a)) := by
  refine transfer N A r hr (z - single 0 a) _ _ ?_ ?_ (sub_algebraMap_ne_zero hxb _) D hD Q
  · rw [map_sub, coeffMap_single, hzx]
    change _ = (x : LaurentSeries (AlgebraicClosure ℚ)) -
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ)
    rw [algebraMap_laurentSeries_eq_single]
    rfl
  · rw [map_sub, coeffMap_single, hzxb]
    change _ = (xb : LaurentSeries (ResidueField A)) -
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (residue A a)
    rw [algebraMap_laurentSeries_eq_single]

theorem residue_inv_eq_zero (A : ValuationSubring (AlgebraicClosure ℚ)) {b : AlgebraicClosure ℚ}
    (hbA : b ∉ A) (hbinv : b⁻¹ ∈ A) : residue A ⟨b⁻¹, hbinv⟩ = 0 := by
  have hb0 : b ≠ 0 := fun h => hbA (h ▸ A.zero_mem)
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  apply hbA
  have h := u.inv_mul
  rw [hu] at h
  have h' : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) * b⁻¹ = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  rw [mul_inv_eq_one₀ hb0] at h'
  rw [← h']
  exact ((u⁻¹ : Aˣ) : A).2

theorem spec_nonintegral (N : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N))
    (hr : IsPlaceReductionModL A N r) (z : LaurentSeries A)
    (x : modularFunctionFieldBar N)
    (hzx : coeffMap A.subtype z = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hx : ∀ c, x ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
    (b : AlgebraicClosure ℚ) (hb : ∀ a : A, (a : AlgebraicClosure ℚ) ≠ b)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ v, D v = v.ord (x - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) b)) :
    Finsupp.mapDomain r D = 0 := by
  have hbA : b ∉ A := fun h => hb ⟨b, h⟩ rfl
  have hb0 : b ≠ 0 := fun h => hbA (h ▸ A.zero_mem)
  have hbinv : b⁻¹ ∈ A := (A.mem_or_inv_mem b).resolve_left hbA
  have hres : residue A ⟨b⁻¹, hbinv⟩ = 0 := residue_inv_eq_zero A hbA hbinv
  have hD' : ∀ P, D P = P.ord (1 - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) b⁻¹ * x
      : modularFunctionFieldBar N) := fun P => by
    rw [hD, ord_one_sub_algebraMap_inv_mul P hx hb0]
  have key := transfer N A r hr (1 - single 0 (⟨b⁻¹, hbinv⟩ : A) * z) _ 1 ?_ ?_ one_ne_zero D hD'
  · ext Q
    rw [key Q, Place.ord_one, Finsupp.coe_zero, Pi.zero_apply]
  · rw [map_sub, map_one, map_mul, coeffMap_single, hzx]
    change _ = 1 - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) b⁻¹ *
      (x : LaurentSeries (AlgebraicClosure ℚ))
    rw [algebraMap_laurentSeries_eq_single]
    rfl
  · rw [map_sub, map_one, map_mul, coeffMap_single, hres, single_eq_zero, zero_mul, sub_zero]
    rfl

theorem clauses_of (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    [IsAlgClosed (ResidueField A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N))
    (hr : IsPlaceReductionModL A N r) (z : LaurentSeries A)
    (x : modularFunctionFieldBar N) (xb : modularFunctionFieldFullC (ResidueField A) N)
    (hzx : coeffMap A.subtype z = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hzxb : coeffMap (residue A) z = (xb : LaurentSeries (ResidueField A)))
    (hxt : Transcendental (AlgebraicClosure ℚ) x) (hxbt : Transcendental (ResidueField A) xb)
    (Px : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hPx : ∀ v, Px v = max 0 (-v.ord x)) (hPxdeg : Divisor.degree Px = dedekindPsi N)
    (hfin : Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({xb} : Set (modularFunctionFieldFullC (ResidueField A) N)))
        (modularFunctionFieldFullC (ResidueField A) N) = dedekindPsi N) :
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
        0 < w.ord (x - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) →
        0 < (r w).ord (xb - algebraMap (ResidueField A)
          (modularFunctionFieldFullC (ResidueField A) N) (residue A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A, w.ord (x - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) ≤ 0) → (r w).ord xb < 0) := by
  have hx : ∀ c, x ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c :=
    ne_algebraMap_of_transcendental hxt
  have hxb : ∀ c, xb ≠ algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) c :=
    ne_algebraMap_of_transcendental hxbt
  haveI : FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({xb} : Set (modularFunctionFieldFullC (ResidueField A) N)))
      (modularFunctionFieldFullC (ResidueField A) N) :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact dedekindPsi_pos N (NeZero.ne N))
  have hdegb : ∀ Q : Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N),
      0 < Q.deg := fun Q =>
    Nat.pos_of_ne_zero (Place.deg_ne_zero_of_finiteDimensional_adjoin xb hxbt Q)
  have hdiv : ∀ f : modularFunctionFieldBar N, f ≠ 0 →
      ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ v, D v = v.ord f := by
    intro f hf
    obtain ⟨D, hD, -⟩ :=
      (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor f hf
    exact ⟨D, hD⟩
  have hrat : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      x ∈ w.toValuationSubring →
      ∃ c : AlgebraicClosure ℚ,
        0 < w.ord (x - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) :=
    fun w hmem => exists_ord_sub_algebraMap_pos w
      ((Place.isRational_iff_deg_eq_one w).mpr (deg_eq_one_modularFunctionFieldBar N w)) hx hmem
  obtain ⟨Pxb, hPxb⟩ := exists_poleDivisor_of_transcendental xb hxbt
  have hle : Divisor.degree Px ≤ Divisor.degree Pxb := by
    rw [hPxdeg, degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental xb hxbt Pxb hPxb,
      hfin]
  exact core r hr.1 hdegb hdiv x xb hx hxb hrat Px hPx Pxb hPxb hle
    (fun a : A => (a : AlgebraicClosure ℚ)) (fun a : A => residue A a) 0
    (spec_integral N A r hr z x xb hzx hzxb hxb) (spec_nonintegral N A r hr z x hzx hx)

theorem exists_poleDivisor_jBar (N : ℕ) [NeZero N] :
    ∃ P : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, P v = max 0 (-v.ord (jBar N))) ∧ Divisor.degree P = dedekindPsi N := by
  have hcoe : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) :=
    coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have hjt : Transcendental (AlgebraicClosure ℚ) (jBar N) :=
    transcendental_of_coe (by rw [hcoe]; exact transcendental_jqModC _)
  haveI := finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
  obtain ⟨P, hP⟩ := exists_poleDivisor_of_transcendental (jBar N) hjt
  refine ⟨P, hP, ?_⟩
  rw [degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental (jBar N) hjt P hP,
    CompEq.finrank_adjoin_jBar_eq_dedekindPsi N]

theorem exists_poleDivisor_jpBar (N : ℕ) [NeZero N] :
    ∃ P : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, P v = max 0 (-v.ord (jpBar N))) ∧ Divisor.degree P = dedekindPsi N := by
  obtain ⟨Pj, hPj, hdeg⟩ := exists_poleDivisor_jBar N
  obtain ⟨σ, hσ⟩ := exists_frickeAlgEquiv_modularFunctionFieldBar N
  have hσj : σ (jBar N) = jpBar N := by
    apply Subtype.ext
    exact hσ 1 N (one_mul N) (jBar N) (by rw [qExpand_one_apply])
  refine ⟨σ • Pj, fun v => ?_, by rw [Divisor.degree_smul, hdeg]⟩
  rw [Divisor.smul_apply, hPj]
  have := Place.ord_smul σ (σ⁻¹ • v) (jBar N)
  rw [smul_inv_smul, hσj] at this
  rw [this]

theorem clauses_j (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField A) ℓ] [IsAlgClosed (ResidueField A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N))
    (hr : IsPlaceReductionModL A N r) :
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
        0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) →
        0 < (r w).ord ((⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩
            : modularFunctionFieldFullC (ResidueField A) N) -
          algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) (residue A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A, w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r w).ord (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩
        : modularFunctionFieldFullC (ResidueField A) N) < 0) := by
  have hN : (N : ResidueField A) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff _ ℓ N).mp h)
  obtain ⟨Px, hPx, hPxdeg⟩ := exists_poleDivisor_jBar N
  have hcoe : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) :=
    coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  refine clauses_of N A r hr (jqModC A) (jBar N) ⟨jqModC (ResidueField A), jqModC_mem_full _ N⟩
    (by rw [hcoe, coeffMap_jqModC]) (coeffMap_jqModC _)
    (transcendental_of_coe (by rw [hcoe]; exact transcendental_jqModC _))
    (transcendental_of_coe (transcendental_jqModC _)) Px hPx hPxdeg
    (finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi _ N hN)

theorem clauses_jN (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField A) ℓ] [IsAlgClosed (ResidueField A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N))
    (hr : IsPlaceReductionModL A N r) :
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
        0 < w.ord (jpBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) →
        0 < (r w).ord ((⟨jqNModC (ResidueField A) N,
            modularFunctionFieldC_le_full (ResidueField A) N (jqNModC_mem (ResidueField A) N)⟩
            : modularFunctionFieldFullC (ResidueField A) N) -
          algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) (residue A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A, w.ord (jpBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r w).ord (⟨jqNModC (ResidueField A) N,
          modularFunctionFieldC_le_full (ResidueField A) N (jqNModC_mem (ResidueField A) N)⟩
        : modularFunctionFieldFullC (ResidueField A) N) < 0) := by
  have hN : (N : ResidueField A) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff _ ℓ N).mp h)
  obtain ⟨Px, hPx, hPxdeg⟩ := exists_poleDivisor_jpBar N
  have hcoe : ((jpBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqNModC (AlgebraicClosure ℚ) N :=
    coeffMap_jqNModC (algebraMap ℚ (AlgebraicClosure ℚ)) N
  refine clauses_of N A r hr (jqNModC A N) (jpBar N)
    ⟨jqNModC (ResidueField A) N, modularFunctionFieldC_le_full _ N (jqNModC_mem _ N)⟩
    (by rw [hcoe, coeffMap_jqNModC]) (coeffMap_jqNModC _ N)
    (transcendental_of_coe (by rw [hcoe]; exact transcendental_jqNModC _ N))
    (transcendental_of_coe (transcendental_jqNModC _ N)) Px hPx hPxdeg
    (finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi _ N hN)

end Application

end ModularCurve.IsPlaceReductionModL.CoordinateClausesAux

p2m_open "ModularCurve P2MW.S_ModularCurve_IsPlaceReductionModL_coordinate_clauses.ModularCurve AlgebraicCurve IsLocalRing"
open ModularCurve.IsPlaceReductionModL.CoordinateClausesAux

set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r) :
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r w).ord
          (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r w).ord (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0) ∧
    (∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a : A),
      0 < w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) →
      0 < (r w).ord
          (⟨jqNModC (ResidueField ↥A) N,
              modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
            - algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
                (IsLocalRing.residue ↥A a))) ∧
    (∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ a : A,
        w.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (a : AlgebraicClosure ℚ)) ≤ 0) →
      (r w).ord (⟨jqNModC (ResidueField ↥A) N,
          modularFunctionFieldC_le_full (ResidueField ↥A) N (jqNModC_mem (ResidueField ↥A) N)⟩
        : modularFunctionFieldFullC (ResidueField ↥A) N) < 0) := by
  obtain ⟨h1, h2⟩ := clauses_j N ℓ hℓN A r hr
  obtain ⟨h3, h4⟩ := clauses_jN N ℓ hℓN A r hr
  exact ⟨h1, h2, h3, h4⟩

end S_ModularCurve_IsPlaceReductionModL_coordinate_clauses
end P2MW
export P2MW.S_ModularCurve_IsPlaceReductionModL_coordinate_clauses (solution)
