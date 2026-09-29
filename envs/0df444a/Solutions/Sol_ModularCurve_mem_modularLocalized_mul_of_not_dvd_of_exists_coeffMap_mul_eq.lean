-- Prove2me | solution 1 for ModularCurve.mem_modularLocalized_mul_of_not_dvd_of_exists_coeffMap_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/496d92dc-a624-51a3-ba62-fedf538c2122

import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_existsUnique_kroneckerRemainder
import Theorems.Thm_ModularCurve_jqNModC_mul_eq_pow
import Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
import Theorems.Thm_ModularCurve_jqNModC_mem_modularLocalized_mul_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_modularLocalized_mul_of_not_dvd_of_exists_coeffMap_mul_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_mem_modularLocalized_mul_of_not_dvd_of_exists_coeffMap_mul_eq.ModularCurve ModularCurve.CharPReduction ModularCurve.NodeLocalized"

private theorem hvc_modularRing_mono_of_le (M : ℕ) [NeZero M] {S T : Subring (AlgebraicClosure ℚ)} (hST : S ≤ T) :
    modularRing M S ≤ modularRing M T := by
  rw [modularRing, Subring.closure_le]
  rintro y (⟨a, rfl⟩ | rfl | rfl)
  · exact constSeries_mem_modularRing M T ⟨a, hST a.2⟩
  · exact jqModC_mem_modularRing M T
  · exact jqNModC_mem_modularRing M T

private theorem hvc_coeffSubring_mono (A : ValuationSubring (AlgebraicClosure ℚ)) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hKK' : K ≤ K') : coeffSubring A K ≤ coeffSubring A K' :=
  fun _ hx => ⟨hx.1, hKK' hx.2⟩

private theorem hvc_const_mem_fieldOver (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {c : AlgebraicClosure ℚ}
    (hc : c ∈ K) : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inl ⟨⟨c, hc⟩, rfl⟩)

private theorem hvc_jqModC_mem_fieldOver (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jqModC (AlgebraicClosure ℚ) ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

private theorem hvc_jqNModC_mem_fieldOver (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jqNModC (AlgebraicClosure ℚ) M ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

private theorem hvc_finiteDimensional_adjoin (c : AlgebraicClosure ℚ) : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c).isIntegral

private theorem hvc_modularRing_mono (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') :
    modularRing M (coeffSubring A K) ≤ modularRing M (coeffSubring A K') := by
  exact hvc_modularRing_mono_of_le M (hvc_coeffSubring_mono A hKK')

private theorem hvc_fieldOver_mono (M : ℕ) [NeZero M] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') :
    fieldOver M K ≤ fieldOver M K' := by
  rw [fieldOver, Subfield.closure_le]
  rintro y (⟨a, rfl⟩ | rfl | rfl)
  · exact hvc_const_mem_fieldOver M K' (hKK' a.2)
  · exact hvc_jqModC_mem_fieldOver M K'
  · exact hvc_jqNModC_mem_fieldOver M K'

private theorem hvc_exists_fieldOver (M : ℕ) [NeZero M] (f : modularFunctionFieldBar M) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver M K := by
  have hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) M} :=
    (SetLike.ext_iff.mp (modularFunctionFieldBar_eq_modularFunctionFieldC M) _).mp f.2
  suffices key : ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) M} →
      ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧ x ∈ fieldOver M K from key _ hf
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      refine ⟨⊥, inferInstance, ?_⟩
      rcases hx with rfl | rfl
      · exact hvc_jqModC_mem_fieldOver M ⊥
      · exact hvc_jqNModC_mem_fieldOver M ⊥
  | algebraMap c =>
      exact ⟨IntermediateField.adjoin ℚ {c}, hvc_finiteDimensional_adjoin c,
        hvc_const_mem_fieldOver M _ (IntermediateField.subset_adjoin ℚ {c} rfl)⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨K₁, hK₁, hx⟩ := ihx
      obtain ⟨K₂, hK₂, hy⟩ := ihy
      haveI := hK₁
      haveI := hK₂
      exact ⟨K₁ ⊔ K₂, inferInstance, add_mem (hvc_fieldOver_mono M le_sup_left hx) (hvc_fieldOver_mono M le_sup_right hy)⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨K₁, hK₁, hx⟩ := ihx
      obtain ⟨K₂, hK₂, hy⟩ := ihy
      haveI := hK₁
      haveI := hK₂
      exact ⟨K₁ ⊔ K₂, inferInstance, mul_mem (hvc_fieldOver_mono M le_sup_left hx) (hvc_fieldOver_mono M le_sup_right hy)⟩
  | inv x _ ihx =>
      obtain ⟨K₁, hK₁, hx⟩ := ihx
      exact ⟨K₁, hK₁, inv_mem hx⟩

private theorem hvc_exists_mem_modularRing_coeffSubring (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    (r : modularRing M A.toSubring) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧
      (r : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularRing M (coeffSubring A K) := by
  have hr : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈ Subring.closure (Set.range (constSeries A.toSubring) ∪
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) M}) := r.2
  suffices key : ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ Subring.closure (Set.range (constSeries A.toSubring) ∪
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) M}) →
      ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧ x ∈ modularRing M (coeffSubring A K) from key _ hr
  intro x hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | rfl | rfl
      · refine ⟨IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)}, hvc_finiteDimensional_adjoin _, ?_⟩
        have ha : (a : AlgebraicClosure ℚ) ∈ coeffSubring A (IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)}) :=
          ⟨a.2, IntermediateField.subset_adjoin ℚ _ rfl⟩
        have heq : constSeries A.toSubring a =
            constSeries (coeffSubring A (IntermediateField.adjoin ℚ {(a : AlgebraicClosure ℚ)})) ⟨a, ha⟩ := by
          simp [constSeries]
        rw [heq]
        exact constSeries_mem_modularRing M _ _
      · exact ⟨⊥, inferInstance, jqModC_mem_modularRing M _⟩
      · exact ⟨⊥, inferInstance, jqNModC_mem_modularRing M _⟩
  | zero => exact ⟨⊥, inferInstance, zero_mem _⟩
  | one => exact ⟨⊥, inferInstance, one_mem _⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨K₁, hK₁, hx⟩ := ihx
      obtain ⟨K₂, hK₂, hy⟩ := ihy
      haveI := hK₁
      haveI := hK₂
      exact ⟨K₁ ⊔ K₂, inferInstance, add_mem (hvc_modularRing_mono M A le_sup_left hx) (hvc_modularRing_mono M A le_sup_right hy)⟩
  | neg x _ ihx =>
      obtain ⟨K₁, hK₁, hx⟩ := ihx
      exact ⟨K₁, hK₁, neg_mem hx⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨K₁, hK₁, hx⟩ := ihx
      obtain ⟨K₂, hK₂, hy⟩ := ihy
      haveI := hK₁
      haveI := hK₂
      exact ⟨K₁ ⊔ K₂, inferInstance, mul_mem (hvc_modularRing_mono M A le_sup_left hx) (hvc_modularRing_mono M A le_sup_right hy)⟩

private theorem hvc_exists_fraction (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ fieldOver M K) :
    ∃ P Q : modularRing M (coeffSubring A K), (Q : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 ∧
      x * (Q : LaurentSeries (AlgebraicClosure ℚ)) = P := by
  have hx' : x ∈ Subfield.closure (Set.range (constSeries K.toSubalgebra.toSubring) ∪
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) M}) := hx
  clear hx
  induction hx' using Subfield.closure_induction with
  | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | rfl | rfl
      · by_cases hc0 : (c : AlgebraicClosure ℚ) = 0
        · refine ⟨0, 1, by simp, ?_⟩
          have h0 : constSeries K.toSubalgebra.toSubring c = 0 := by
            rw [show c = 0 from Subtype.ext hc0, map_zero]
          rw [h0]
          simp
        · rcases A.mem_or_inv_mem (c : AlgebraicClosure ℚ) with hcA | hcA
          · refine ⟨⟨constSeries (coeffSubring A K) ⟨c, hcA, c.2⟩, constSeries_mem_modularRing M (coeffSubring A K) _⟩, 1,
              by simp, ?_⟩
            simp only [OneMemClass.coe_one, mul_one]
            rfl
          · have hcK : (c : AlgebraicClosure ℚ)⁻¹ ∈ K := K.inv_mem c.2
            refine ⟨1, ⟨constSeries (coeffSubring A K) ⟨(c : AlgebraicClosure ℚ)⁻¹, hcA, hcK⟩,
              constSeries_mem_modularRing M (coeffSubring A K) _⟩, ?_, ?_⟩
            · show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)⁻¹ ≠ 0
              exact (map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective).mpr
                (inv_ne_zero hc0)
            · show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) *
                algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)⁻¹ =
                  ((1 : modularRing M (coeffSubring A K)) : LaurentSeries (AlgebraicClosure ℚ))
              rw [← map_mul, mul_inv_cancel₀ hc0, map_one, OneMemClass.coe_one]
      · exact ⟨⟨_, jqModC_mem_modularRing M (coeffSubring A K)⟩, 1, by simp, by simp⟩
      · exact ⟨⟨_, jqNModC_mem_modularRing M (coeffSubring A K)⟩, 1, by simp, by simp⟩
  | one => exact ⟨1, 1, by simp, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨r, s, hs, hr⟩ := ihx
      obtain ⟨u, t, ht, hu⟩ := ihy
      refine ⟨r * t + u * s, s * t, by push_cast; exact mul_ne_zero hs ht, ?_⟩
      push_cast
      calc (x + y) * ((s : LaurentSeries (AlgebraicClosure ℚ)) * t) = x * s * t + y * t * s := by ring
        _ = (r : LaurentSeries (AlgebraicClosure ℚ)) * t + (u : LaurentSeries (AlgebraicClosure ℚ)) * s := by rw [hr, hu]
  | neg x _ ihx =>
      obtain ⟨r, s, hs, hr⟩ := ihx
      refine ⟨-r, s, hs, ?_⟩
      push_cast
      rw [neg_mul, hr]
  | inv x _ ihx =>
      obtain ⟨r, s, hs, hr⟩ := ihx
      by_cases hx0 : x = 0
      · exact ⟨0, 1, by simp, by simp [hx0]⟩
      · have hr0 : (r : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
          rw [← hr]
          exact mul_ne_zero hx0 hs
        refine ⟨s, r, hr0, ?_⟩
        rw [← hr, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x y _ _ ihx ihy =>
      obtain ⟨r, s, hs, hr⟩ := ihx
      obtain ⟨u, t, ht, hu⟩ := ihy
      refine ⟨r * u, s * t, by push_cast; exact mul_ne_zero hs ht, ?_⟩
      push_cast
      calc x * y * ((s : LaurentSeries (AlgebraicClosure ℚ)) * t) = (x * s) * (y * t) := by ring
        _ = (r : LaurentSeries (AlgebraicClosure ℚ)) * u := by rw [hr, hu]

private theorem hvc_modularLocalized_le (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) ≤
      modularLocalized M A.toSubring (IsLocalRing.residue A) := by
  have hle : coeffSubring A K ≤ A.toSubring := inf_le_left
  rintro x ⟨r, s, hs, hxs⟩
  refine ⟨⟨r, hvc_modularRing_mono_of_le M hle r.2⟩, ⟨s, hvc_modularRing_mono_of_le M hle s.2⟩, ?_, hxs⟩
  intro hsker
  apply hs
  have h1 : redRes A.toSubring (IsLocalRing.residue A) (modularRing M A.toSubring) (modularRing_le_integralCoeffs M A.toSubring)
      ⟨s, hvc_modularRing_mono_of_le M hle s.2⟩ = 0 := RingHom.mem_ker.mp hsker
  have h2 : redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing M (coeffSubring A K))
      (modularRing_le_integralCoeffs M (coeffSubring A K)) s =
      redRes A.toSubring (IsLocalRing.residue A) (modularRing M A.toSubring) (modularRing_le_integralCoeffs M A.toSubring)
        ⟨s, hvc_modularRing_mono_of_le M hle s.2⟩ := by
    ext n
    rfl
  exact RingHom.mem_ker.mpr (h2.trans h1)

private theorem hvc_mem_modularLocalized_coeffSubring (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (r s : modularRing M A.toSubring)
    (hs : s ∉ redKer A.toSubring (IsLocalRing.residue A) (modularRing M A.toSubring) (modularRing_le_integralCoeffs M A.toSubring))
    (hxs : x * s = r) (hr : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularRing M (coeffSubring A K))
    (hs' : (s : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularRing M (coeffSubring A K)) :
    x ∈ modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := by
  refine ⟨⟨r, hr⟩, ⟨s, hs'⟩, ?_, hxs⟩
  intro hsker
  apply hs
  have h1 : redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing M (coeffSubring A K))
      (modularRing_le_integralCoeffs M (coeffSubring A K)) ⟨s, hs'⟩ = 0 := RingHom.mem_ker.mp hsker
  have h2 : redRes A.toSubring (IsLocalRing.residue A) (modularRing M A.toSubring) (modularRing_le_integralCoeffs M A.toSubring) s =
      redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing M (coeffSubring A K))
        (modularRing_le_integralCoeffs M (coeffSubring A K)) ⟨s, hs'⟩ := by
    ext n
    rfl
  exact RingHom.mem_ker.mpr (h2.trans h1)

private theorem hvc_charP {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) :
    CharP (IsLocalRing.ResidueField A) q := by
  rw [CharP.charP_iff_prime_eq_zero Fact.out]
  have hq : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have h := (ValuationSubring.mem_nonunits_iff (A := A)).mp hA
    simpa using h
  rw [← map_natCast (IsLocalRing.residue A)]
  exact (IsLocalRing.residue_eq_zero_iff (q : A)).mpr hq

private theorem hvc_exists_uniformizer {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime q) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsDiscreteValuationRing (coeffSubring A K) ∧ ∃ ϖ : coeffSubring A K,
      redRestrict (IsLocalRing.residue A) K ϖ = 0 ∧ (ϖ : AlgebraicClosure ℚ) ≠ 0 ∧
        ∀ c : coeffSubring A K, redRestrict (IsLocalRing.residue A) K c = 0 ↔ ∃ d : coeffSubring A K, c = ϖ * d := by
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hqinv : (q : AlgebraicClosure ℚ)⁻¹ ∉ A := by
    rcases (ValuationSubring.mem_nonunits_iff_or (A := A) (x := (q : AlgebraicClosure ℚ))).mp hA with h | h
    · exact absurd h hq0
    · exact h
  have hdvr : IsDiscreteValuationRing (coeffSubring A K) := by
    rcases coeffSubring_eq_or_isDiscreteValuationRing A K with htop | hdvr
    · exfalso
      apply hqinv
      have hmem : (q : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
        rw [htop]
        exact K.inv_mem (K.natCast_mem q)
      exact hmem.1
    · exact hdvr
  refine ⟨hdvr, ?_⟩

  have hker : ∀ c : coeffSubring A K, redRestrict (IsLocalRing.residue A) K c = 0 ↔ c ∈ IsLocalRing.maximalIdeal (coeffSubring A K) := by
    intro c
    rw [redRestrict, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hcA hcu
      apply hcA
      obtain ⟨c', hcc'⟩ := isUnit_iff_exists_inv.mp hcu
      refine isUnit_iff_exists_inv.mpr ⟨Subring.inclusion inf_le_left c', ?_⟩
      have hm := map_mul (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) c c'
      simp only [hcc', map_one] at hm
      exact hm.symm
    · intro hcu hcA
      apply hcu
      obtain ⟨a', ha'⟩ := isUnit_iff_exists_inv.mp hcA
      have ha'' : ((Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) c : A) : AlgebraicClosure ℚ) * (a' : AlgebraicClosure ℚ) = 1 := by
        exact_mod_cast congrArg Subtype.val ha'
      have hcK : (c : AlgebraicClosure ℚ) ∈ K := c.2.2
      have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0
        simp [h0] at ha''
      have ha'K : (a' : AlgebraicClosure ℚ) ∈ K := by
        have : (a' : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right ha''
        rw [this]
        exact K.inv_mem hcK
      refine isUnit_iff_exists_inv.mpr ⟨⟨(a' : AlgebraicClosure ℚ), a'.2, ha'K⟩, ?_⟩
      apply Subtype.ext
      exact ha''
  haveI := hdvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (coeffSubring A K)
  refine ⟨ϖ, ?_, ?_, ?_⟩
  · rw [hker, hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  · exact_mod_cast hϖ.ne_zero
  · intro c
    rw [hker, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    rfl

open IsLocalRing

namespace HVC_SD2

variable {F : Type*} [Field F]

section LocSubring

variable (R : Subring F) (𝔭 : Ideal R)

private theorem ne_zero_of_notMem_prime {s : R} (hs : s ∉ 𝔭) : (s : F) ≠ 0 := by
  intro h
  apply hs
  have : s = 0 := Subtype.ext h
  rw [this]
  exact Ideal.zero_mem _

variable [𝔭.IsPrime]

private theorem one_notMem_prime : (1 : R) ∉ 𝔭 := fun h =>
  Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr h)

private theorem mul_notMem_prime {s t : R} (hs : s ∉ 𝔭) (ht : t ∉ 𝔭) : s * t ∉ 𝔭 := fun h =>
  (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht

private def locSubring : Subring F where
  carrier := {x | ∃ r s : R, s ∉ 𝔭 ∧ x * s = r}
  mul_mem' := by
    rintro x y ⟨r, s, hs, hx⟩ ⟨r', s', hs', hy⟩
    refine ⟨r * r', s * s', mul_notMem_prime R 𝔭 hs hs', ?_⟩
    rw [Subring.coe_mul, Subring.coe_mul, ← hx, ← hy]; ring
  one_mem' := ⟨1, 1, one_notMem_prime R 𝔭, by simp⟩
  add_mem' := by
    rintro x y ⟨r, s, hs, hx⟩ ⟨r', s', hs', hy⟩
    refine ⟨r * s' + r' * s, s * s', mul_notMem_prime R 𝔭 hs hs', ?_⟩
    rw [Subring.coe_mul, Subring.coe_add, Subring.coe_mul, Subring.coe_mul, ← hx, ← hy]; ring
  zero_mem' := ⟨0, 1, one_notMem_prime R 𝔭, by simp⟩
  neg_mem' := by
    rintro x ⟨r, s, hs, hx⟩
    exact ⟨-r, s, hs, by rw [Subring.coe_neg, ← hx]; ring⟩

private theorem mem_locSubring_iff {x : F} :
    x ∈ locSubring R 𝔭 ↔ ∃ r s : R, s ∉ 𝔭 ∧ x * s = r := Iff.rfl

private theorem le_locSubring : R ≤ locSubring R 𝔭 := fun x hx =>
  ⟨⟨x, hx⟩, 1, one_notMem_prime R 𝔭, by simp⟩

private theorem inv_mem_locSubring {x : F} {r s : R} (hr : r ∉ 𝔭) (hx : x * s = r) :
    x⁻¹ ∈ locSubring R 𝔭 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact ne_zero_of_notMem_prime R 𝔭 hr (by rw [← hx, zero_mul])
  exact ⟨s, r, hr, by rw [← hx, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]⟩

private theorem notMem_of_inv_mem_locSubring {x : F} (hx0 : x ≠ 0) {r s : R} (hs : s ∉ 𝔭)
    (hx : x * s = r) (hinv : x⁻¹ ∈ locSubring R 𝔭) : r ∉ 𝔭 := by
  obtain ⟨r', s', hs', hx'⟩ := hinv
  intro hr
  have hss : s * s' = r * r' := by
    apply Subtype.ext
    change (s : F) * s' = r * r'
    rw [← hx, ← hx']
    calc (s : F) * s' = (x * x⁻¹) * s * s' := by rw [mul_inv_cancel₀ hx0, one_mul]
      _ = x * s * (x⁻¹ * s') := by ring
  exact mul_notMem_prime R 𝔭 hs hs' (hss ▸ Ideal.mul_mem_right _ _ hr)

private theorem inv_mem_locSubring_iff {x : F} (hx0 : x ≠ 0) {r s : R} (hs : s ∉ 𝔭)
    (hx : x * s = r) : x⁻¹ ∈ locSubring R 𝔭 ↔ r ∉ 𝔭 :=
  ⟨notMem_of_inv_mem_locSubring R 𝔭 hx0 hs hx, fun hr => inv_mem_locSubring R 𝔭 hr hx⟩

end LocSubring

section Scaling

variable {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]

private theorem exists_dvd_forall {ι : Type*} (c : ι → A) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ j ∈ s, c i ∣ c j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨a, Finset.mem_insert_self _ _, fun j hj => ?_⟩
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_rfl
      · exact absurd hj (Finset.notMem_empty _)
    · obtain ⟨i, hi, hmin⟩ := ih hne
      rcases ValuationRing.dvd_total (c a) (c i) with h | h
      · refine ⟨a, Finset.mem_insert_self _ _, fun j hj => ?_⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact dvd_rfl
        · exact h.trans (hmin j hj)
      · refine ⟨i, Finset.mem_insert_of_mem hi, fun j hj => ?_⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact h
        · exact hmin j hj

variable {R : Type*} [CommRing R] (𝔭 : Ideal R) (φ : A →+* R) {ι : Type*} (b : ι → R)

private def IndepModPrime : Prop :=
  ∀ (s : Finset ι) (c : ι → A), (∑ i ∈ s, φ (c i) * b i) ∈ 𝔭 → ∀ i ∈ s, c i ∈ maximalIdeal A

private theorem exists_eq_mul_notMem
    (hspan : ∀ r : R, ∃ (s : Finset ι) (c : ι → A), r = ∑ i ∈ s, φ (c i) * b i)
    (hind : IndepModPrime 𝔭 φ b) {r : R} (hr : r ≠ 0) :
    ∃ (c : A) (r' : R), r' ∉ 𝔭 ∧ r = φ c * r' := by
  classical
  obtain ⟨s, c, rfl⟩ := hspan r

  set s' := s.filter (fun i => c i ≠ 0) with hs'
  have hsum : ∑ i ∈ s, φ (c i) * b i = ∑ i ∈ s', φ (c i) * b i := by
    rw [hs', Finset.sum_filter_of_ne]
    intro i _ hne hci
    apply hne
    rw [hci, map_zero, zero_mul]
  have hne : s'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hr
    rw [hsum, he, Finset.sum_empty]
  obtain ⟨i₀, hi₀, hmin⟩ := exists_dvd_forall c s' hne
  have hci₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  choose! d hd using hmin
  refine ⟨c i₀, ∑ j ∈ s', φ (d j) * b j, ?_, ?_⟩
  · intro hmem
    have h1 : d i₀ ∈ maximalIdeal A := hind s' d hmem i₀ hi₀
    have hd1 : d i₀ = 1 := by
      apply mul_left_cancel₀ hci₀
      rw [mul_one]
      exact (hd i₀ hi₀).symm
    rw [hd1] at h1
    exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hd j hj, map_mul, mul_assoc]

end Scaling

section Valuation

variable {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
variable (R : Subring F) (𝔭 : Ideal R) [𝔭.IsPrime] (φ : A →+* R) {ι : Type*} (b : ι → R)
variable (hspan : ∀ r : R, ∃ (s : Finset ι) (c : ι → A), r = ∑ i ∈ s, φ (c i) * b i)
variable (hind : IndepModPrime 𝔭 φ b)

include hspan hind

private theorem mem_or_inv_mem_of_fraction {x : F} {r s : R} (hs : (s : F) ≠ 0)
    (hx : x * s = r) : x ∈ locSubring R 𝔭 ∨ x⁻¹ ∈ locSubring R 𝔭 := by
  by_cases hr0 : r = 0
  · left
    have hx0 : x = 0 := by
      rw [hr0, Subring.coe_zero] at hx
      exact (mul_eq_zero.mp hx).resolve_right hs
    rw [hx0]
    exact Subring.zero_mem _
  have hs0 : s ≠ 0 := fun h => hs (by rw [h]; rfl)
  obtain ⟨c, r', hr', hr⟩ := exists_eq_mul_notMem 𝔭 φ b hspan hind hr0
  obtain ⟨d, s', hs', hs''⟩ := exists_eq_mul_notMem 𝔭 φ b hspan hind hs0
  have hxF : x * ((φ d : R) : F) * s' = (φ c : R) * r' := by
    rw [mul_assoc, ← Subring.coe_mul, ← hs'', hx, hr, Subring.coe_mul]
  rcases ValuationRing.dvd_total c d with ⟨e, rfl⟩ | ⟨e, rfl⟩
  ·
    right
    have hc0 : ((φ c : R) : F) ≠ 0 := by
      intro h0
      apply hr0
      apply Subtype.ext
      change (r : F) = 0
      rw [hr, Subring.coe_mul, h0, zero_mul]
    have hx' : x * ((φ e : R) * s' : R) = r' := by
      apply mul_left_cancel₀ hc0
      rw [← hxF, map_mul, Subring.coe_mul, Subring.coe_mul]
      ring
    exact inv_mem_locSubring R 𝔭 hr' hx'
  ·
    left
    have hd0 : ((φ d : R) : F) ≠ 0 := by
      intro h0
      apply hs
      rw [hs'', Subring.coe_mul, h0, zero_mul]
    have hx' : x * s' = ((φ e : R) * r' : R) := by
      apply mul_left_cancel₀ hd0
      rw [← mul_assoc, mul_comm _ x, hxF, map_mul, Subring.coe_mul, Subring.coe_mul]
      ring
    exact ⟨_, s', hs', hx'⟩

private def locValuationSubring (hfrac : ∀ x : F, ∃ r s : R, (s : F) ≠ 0 ∧ x * s = r) :
    ValuationSubring F :=
  { locSubring R 𝔭 with
    mem_or_inv_mem' := fun x => by
      obtain ⟨r, s, hs, hx⟩ := hfrac x
      exact mem_or_inv_mem_of_fraction R 𝔭 φ b hspan hind hs hx }

private theorem mem_locValuationSubring_iff (hfrac : ∀ x : F, ∃ r s : R, (s : F) ≠ 0 ∧ x * s = r)
    {x : F} : x ∈ locValuationSubring R 𝔭 φ b hspan hind hfrac ↔
      ∃ r s : R, s ∉ 𝔭 ∧ x * s = r := Iff.rfl

private theorem exists_eq_mul_of_numerator_mem {x : F} {r s : R} (hs : s ∉ 𝔭) (hx : x * s = r)
    (hr : r ∈ 𝔭) :
    ∃ m ∈ maximalIdeal A, ∃ y ∈ locSubring R 𝔭, x = ((φ m : R) : F) * y := by
  by_cases hr0 : r = 0
  · refine ⟨0, Ideal.zero_mem _, 0, Subring.zero_mem _, ?_⟩
    have : x = 0 := by
      rw [hr0, Subring.coe_zero] at hx
      exact (mul_eq_zero.mp hx).resolve_right (ne_zero_of_notMem_prime R 𝔭 hs)
    rw [this, mul_zero]
  obtain ⟨c, r', hr', hr⟩ := exists_eq_mul_notMem 𝔭 φ b hspan hind hr0
  have hc : c ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hr'
    have : r' = φ (hu.unit⁻¹ : Aˣ) * r := by
      rw [hr, ← mul_assoc, ← map_mul, hu.val_inv_mul, map_one, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ ‹r ∈ 𝔭›
  refine ⟨c, hc, r' / s, ⟨r', s, hs, ?_⟩, ?_⟩
  · rw [div_mul_cancel₀ _ (ne_zero_of_notMem_prime R 𝔭 hs)]
  · rw [mul_div_assoc', ← Subring.coe_mul, ← hr, ← hx,
      mul_div_cancel_right₀ _ (ne_zero_of_notMem_prime R 𝔭 hs)]

omit hspan hind in

private theorem dvd_of_fraction_mem (hφ : Function.Injective φ)
    (h𝔪 : ∀ m ∈ maximalIdeal A, φ m ∈ 𝔭) {a d : A} {x : F}
    (hx : x * (φ d : R) = (φ a : R)) (hd : d ≠ 0) (hmem : x ∈ locSubring R 𝔭) : d ∣ a := by
  by_cases ha : a = 0
  · rw [ha]; exact dvd_zero _
  rcases ValuationRing.dvd_total d a with h | ⟨e, rfl⟩
  · exact h

  by_cases he : IsUnit e
  · exact ⟨(he.unit⁻¹ : Aˣ), by rw [mul_assoc, he.mul_val_inv, mul_one]⟩
  exfalso
  obtain ⟨r, s, hs, hxs⟩ := hmem
  have hφa : ((φ a : R) : F) ≠ 0 := by
    intro h0
    apply ha
    apply hφ
    rw [map_zero]
    exact Subtype.ext h0
  have hφd : ((φ (a * e) : R) : F) ≠ 0 := by
    intro h0
    apply hd
    apply hφ
    rw [map_zero]
    exact Subtype.ext h0

  have hkey : s = φ e * r := by
    apply Subtype.ext
    change (s : F) = ((φ e * r : R) : F)
    apply mul_left_cancel₀ hφa
    calc ((φ a : R) : F) * s = x * ((φ (a * e) : R) : F) * s := by rw [hx]
      _ = (x * s) * ((φ (a * e) : R) : F) := by ring
      _ = (r : F) * (((φ a : R) * (φ e : R) : R) : F) := by rw [hxs, map_mul]
      _ = ((φ a : R) : F) * ((φ e * r : R) : F) := by rw [Subring.coe_mul, Subring.coe_mul]; ring
  apply hs
  rw [hkey]
  exact Ideal.mul_mem_right _ _ (h𝔪 e (by rwa [mem_maximalIdeal, mem_nonunits_iff]))

end Valuation

section Local

variable (R : Subring F) (𝔭 : Ideal R) [𝔭.IsPrime]

private theorem isUnit_locSubring_iff {x : F} (hx : x ∈ locSubring R 𝔭) {r s : R} (hs : s ∉ 𝔭)
    (hxs : x * s = r) : IsUnit (⟨x, hx⟩ : locSubring R 𝔭) ↔ r ∉ 𝔭 := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : x * (((u⁻¹ : (locSubring R 𝔭)ˣ) : locSubring R 𝔭) : F) = 1 := by
      have := congrArg (fun y : locSubring R 𝔭 => (y : F)) u.mul_inv
      simpa [hu] using this
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h1
      exact zero_ne_one h1
    have hinv : x⁻¹ ∈ locSubring R 𝔭 := by
      rw [inv_eq_of_mul_eq_one_right h1]
      exact SetLike.coe_mem _
    exact notMem_of_inv_mem_locSubring R 𝔭 hx0 hs hxs hinv
  · intro hr
    have hinv := inv_mem_locSubring R 𝔭 hr hxs
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact ne_zero_of_notMem_prime R 𝔭 hr (by rw [← hxs, zero_mul])
    exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0),
      Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

private theorem locSubring_isLocalRing : IsLocalRing (locSubring R 𝔭) := by
  apply IsLocalRing.of_nonunits_add
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hna hnb
  obtain ⟨r, s, hs, has⟩ := ha
  obtain ⟨r', s', hs', hbs⟩ := hb
  have hr : r ∈ 𝔭 := by
    by_contra h
    exact hna ((isUnit_locSubring_iff R 𝔭 ⟨r, s, hs, has⟩ hs has).mpr h)
  have hr' : r' ∈ 𝔭 := by
    by_contra h
    exact hnb ((isUnit_locSubring_iff R 𝔭 ⟨r', s', hs', hbs⟩ hs' hbs).mpr h)
  have hab : a + b ∈ locSubring R 𝔭 := Subring.add_mem _ ⟨r, s, hs, has⟩ ⟨r', s', hs', hbs⟩
  have hsum : (a + b) * ((s * s' : R) : F) = ((r * s' + r' * s : R) : F) := by
    rw [Subring.coe_mul, Subring.coe_add, Subring.coe_mul, Subring.coe_mul, ← has, ← hbs]
    ring
  intro hu
  have := (isUnit_locSubring_iff R 𝔭 hab (mul_notMem_prime R 𝔭 hs hs') hsum).mp hu
  exact this (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hr) (Ideal.mul_mem_right _ _ hr'))

private theorem mem_maximalIdeal_locSubring_iff {x : F} (hx : x ∈ locSubring R 𝔭) {r s : R}
    (hs : s ∉ 𝔭) (hxs : x * s = r) :
    haveI := locSubring_isLocalRing R 𝔭
    (⟨x, hx⟩ : locSubring R 𝔭) ∈ maximalIdeal (locSubring R 𝔭) ↔ r ∈ 𝔭 := by
  haveI := locSubring_isLocalRing R 𝔭
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_locSubring_iff R 𝔭 hx hs hxs, not_not]

end Local

end HVC_SD2

open IsLocalRing IntermediateField

namespace HVC_SD2

section H1

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {R : Type*} [CommRing R] {k : Type*} [Field k] {S : Type*} [CommRing S] [Algebra k S]
variable (φ : A →+* R) (red : A →+* k) (red₀ : R →+* S)

private theorem mem_maximalIdeal_of_map_eq_zero {a : A} (ha : red a = 0) : a ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact (hu.map red).ne_zero ha

private theorem indepModKer_of_linearIndependent {ι : Type*} (b : ι → R)
    (hcompat : ∀ a, red₀ (φ a) = algebraMap k S (red a))
    (hli : LinearIndependent k (fun i => red₀ (b i))) :
    ∀ (s : Finset ι) (c : ι → A), (∑ i ∈ s, φ (c i) * b i) ∈ RingHom.ker red₀ →
      ∀ i ∈ s, c i ∈ maximalIdeal A := by
  intro s c hmem i hi
  apply mem_maximalIdeal_of_map_eq_zero red
  rw [RingHom.mem_ker, map_sum] at hmem
  have hsum : ∑ j ∈ s, red (c j) • red₀ (b j) = 0 := by
    rw [← hmem]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hcompat, Algebra.smul_def]
  exact linearIndependent_iff'.mp hli s (fun j => red (c j)) hsum i hi

end H1

section H2

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

private theorem linearIndependent_pow_of_transcendental {x : E} (hx : Transcendental k x) :
    LinearIndependent k (fun a : ℕ => x ^ a) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hinj := transcendental_iff_injective.mp hx
  set p : Polynomial k := ∑ a ∈ s, Polynomial.monomial a (g a) with hp
  have hp0 : Polynomial.aeval x p = 0 := by
    rw [hp, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Polynomial.aeval_monomial, Algebra.smul_def]
  have hpz : p = 0 := hinj (by rw [hp0, map_zero])
  have hc : p.coeff i = g i := by
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' s i g, if_pos hi]
  rw [hpz, Polynomial.coeff_zero] at hc
  exact hc.symm

private theorem linearIndependent_pow_fin_of_relfinrank (x y : E) {n : ℕ} (hn : 0 < n)
    (hdeg : relfinrank k⟮x⟯ (adjoin k {x, y}) = n) :
    LinearIndependent k⟮x⟯ (fun i : Fin n => y ^ (i : ℕ)) := by
  have hle : k⟮x⟯ ≤ adjoin k {x, y} := adjoin.mono k _ _ (by simp)
  have hKy : extendScalars hle = k⟮x⟯⟮y⟯ := by
    rw [extendScalars_adjoin hle]
    apply le_antisymm
    · rw [adjoin_le_iff]
      intro z hz
      rcases hz with rfl | hz
      · have := IntermediateField.algebraMap_mem k⟮z⟯⟮y⟯ (AdjoinSimple.gen k z)
        rwa [AdjoinSimple.algebraMap_gen] at this
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact mem_adjoin_simple_self _ z
    · exact adjoin.mono _ _ _ (by simp)
  have hfin : Module.finrank k⟮x⟯ k⟮x⟯⟮y⟯ = n := by
    rw [← hdeg, relfinrank_eq_finrank_of_le hle, hKy]
  haveI : FiniteDimensional k⟮x⟯ k⟮x⟯⟮y⟯ := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral k⟮x⟯ y := by
    have h1 : IsIntegral k⟮x⟯ (AdjoinSimple.gen k⟮x⟯ y) := Algebra.IsIntegral.isIntegral _
    have h2 := isIntegral_iff.mp h1
    rwa [AdjoinSimple.coe_gen] at h2
  have hnat : (minpoly k⟮x⟯ y).natDegree = n := by
    rw [← adjoin.finrank hint, hfin]
  set pb := adjoin.powerBasis hint with hpb
  have hdim : pb.dim = n := by rw [hpb, adjoin.powerBasis_dim, hnat]
  have hli : LinearIndependent k⟮x⟯ (fun i : Fin pb.dim => y ^ (i : ℕ)) := by
    have h0 : LinearIndependent k⟮x⟯ pb.basis := pb.basis.linearIndependent
    have h1 := h0.map' (k⟮x⟯⟮y⟯.val).toLinearMap
      (LinearMap.ker_eq_bot.mpr (k⟮x⟯⟮y⟯.val).toRingHom.injective)
    convert h1 using 1 <;> first | rfl | exact Subsingleton.elim _ _ |
      (ext i
       simp only [Function.comp_apply, AlgHom.toLinearMap_apply, PowerBasis.basis_eq_pow, hpb,
         adjoin.powerBasis_gen, map_pow]
       rfl)
  subst hdim
  exact hli

private theorem linearIndependent_monomial_of_relfinrank (x y : E) {n : ℕ} (hn : 0 < n)
    (hx : Transcendental k x) (hdeg : relfinrank k⟮x⟯ (adjoin k {x, y}) = n) :
    LinearIndependent k (fun p : ℕ × Fin n => x ^ p.1 * y ^ (p.2 : ℕ)) := by
  have hb : LinearIndependent k (fun a : ℕ => (AdjoinSimple.gen k x) ^ a) := by
    apply LinearIndependent.of_comp (k⟮x⟯.val).toLinearMap
    convert linearIndependent_pow_of_transcendental hx using 1 <;> first | rfl | exact Subsingleton.elim _ _ | skip
  have hc := linearIndependent_pow_fin_of_relfinrank x y hn hdeg
  convert linearIndependent_smul hb hc using 1 <;> first | rfl | exact Subsingleton.elim _ _ | skip

end H2

section Dock

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {R : Type*} [CommRing R] {k E : Type*} [Field k] [Field E] [Algebra k E]
variable (φ : A →+* R) (red : A →+* k) (red₀ : R →+* E)

private theorem indepModKer_monomial (hcompat : ∀ a, red₀ (φ a) = algebraMap k E (red a))
    (X Y : R) {n : ℕ} (hn : 0 < n) (hx : Transcendental k (red₀ X))
    (hdeg : relfinrank k⟮red₀ X⟯ (adjoin k {red₀ X, red₀ Y}) = n) :
    ∀ (s : Finset (ℕ × Fin n)) (c : ℕ × Fin n → A),
      (∑ p ∈ s, φ (c p) * (X ^ p.1 * Y ^ (p.2 : ℕ))) ∈ RingHom.ker red₀ →
        ∀ p ∈ s, c p ∈ maximalIdeal A := by
  apply indepModKer_of_linearIndependent φ red red₀ (fun p : ℕ × Fin n => X ^ p.1 * Y ^ (p.2 : ℕ))
    hcompat
  convert linearIndependent_monomial_of_relfinrank (red₀ X) (red₀ Y) hn hx hdeg using 1
  ext p
  simp only [map_mul, map_pow]

end Dock

end HVC_SD2

namespace HVC_SD2

private theorem exists_sum_monomial_of_mem_closure {A E : Type*} [CommRing A] [CommRing E]
    (φ : A →+* E) (X Y : E) {P : Polynomial (Polynomial A)} (hP : P.Monic)
    (hrel : P.eval₂ (Polynomial.eval₂RingHom φ X) Y = 0)
    {r : E} (hr : r ∈ Subring.closure (Set.range φ ∪ {X, Y})) :
    ∃ (s : Finset (ℕ × Fin P.natDegree)) (c : ℕ × Fin P.natDegree → A),
      r = ∑ p ∈ s, φ (c p) * (X ^ p.1 * Y ^ (p.2 : ℕ)) := by
  classical
  set f : Polynomial A →+* E := Polynomial.eval₂RingHom φ X with hf
  set Ψ : Polynomial (Polynomial A) →+* E := Polynomial.eval₂RingHom f Y with hΨ

  have hle : Subring.closure (Set.range φ ∪ {X, Y}) ≤ Ψ.range := by
    rw [Subring.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · exact ⟨Polynomial.C (Polynomial.C a), by simp [hΨ, hf]⟩
    · rcases hz with rfl | hz
      · exact ⟨Polynomial.C Polynomial.X, by simp [hΨ, hf]⟩
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨Polynomial.X, by simp [hΨ]⟩
  obtain ⟨G, rfl⟩ := hle hr
  by_cases hP1 : P = 1
  ·
    have h10 : (1 : E) = 0 := by
      have : Ψ P = 0 := hrel
      rwa [hP1, map_one] at this
    refine ⟨∅, fun _ => 0, ?_⟩
    rw [Finset.sum_empty, ← mul_one (Ψ G), h10, mul_zero]
  have hΨP : Ψ P = 0 := hrel
  set Rm := G %ₘ P with hRm
  have hG : Ψ G = Ψ Rm := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div G P]
    rw [map_add, map_mul, hΨP, zero_mul, add_zero]
  have hdeg : Rm.natDegree < P.natDegree := Polynomial.natDegree_modByMonic_lt G hP hP1
  set n := P.natDegree with hn
  set D := (Finset.range n).sup (fun i => (Rm.coeff i).natDegree) + 1 with hD
  have hDi : ∀ i ∈ Finset.range n, (Rm.coeff i).natDegree < D := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (Rm.coeff i).natDegree) hi)
  refine ⟨(Finset.range D) ×ˢ (Finset.univ : Finset (Fin n)),
    fun p => (Rm.coeff (p.2 : ℕ)).coeff p.1, ?_⟩
  rw [hG, Finset.sum_product, Finset.sum_comm]
  rw [show Ψ Rm = Rm.eval₂ f Y from rfl, Polynomial.eval₂_eq_sum_range' f hdeg Y,
    ← Fin.sum_univ_eq_sum_range (fun i => f (Rm.coeff i) * Y ^ i) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show f (Rm.coeff i) = (Rm.coeff i).eval₂ φ X from rfl,
    Polynomial.eval₂_eq_sum_range' φ (hDi i (by simp)) X, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end HVC_SD2

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.modularLocalized coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single jqModC jqNModC jqNModC_one jqModC_eq_map_intCast modularFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_injective qExpand_congr dedekindPsi ModularPolynomialData modularFunctionFieldBar transcendental_jqModC nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi exists_kroneckerCongruence_of_prime existsUnique_kroneckerRemainder jqNModC_mul_eq_pow modularFunctionFieldBar_eq_modularFunctionFieldC jqNModC_mem_modularLocalized_mul_of_not_dvd"
p2m_open "ModularCurve"
namespace HVC_Charp

section Modular

variable (N : ℕ) [NeZero N]
variable {L : Type*} [Field L]
variable (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

private theorem constSeries_apply (a : A) :
    constSeries A a = HahnSeries.single 0 (a : L) := by
  show algebraMap L (LaurentSeries L) (a : L) = HahnSeries.single 0 (a : L)
  ext m
  rw [HahnSeries.algebraMap_apply', show algebraMap L (PowerSeries L) (a : L)
    = PowerSeries.C (a : L) from by simp, HahnSeries.ofPowerSeries_C]
  rfl

private theorem coeffRed_jqModC :
    coeffRed A red ⟨jqModC L, jqModC_mem_integralCoeffs A⟩ = jqModC k := by
  ext n
  rw [coeffRed_coeff]
  have hL : (⟨(jqModC L).coeff n, jqModC_mem_integralCoeffs A n⟩ : A)
      = (((jqModC ℤ).coeff n : ℤ) : A) := by
    ext
    push_cast
    rw [jqModC_eq_map_intCast, HahnSeries.map_coeff]
    rfl
  rw [hL, map_intCast]
  conv_rhs => rw [jqModC_eq_map_intCast]
  rw [HahnSeries.map_coeff]
  rfl

private theorem coeffRed_jqNModC :
    coeffRed A red ⟨jqNModC L N, jqNModC_mem_integralCoeffs N A⟩ = jqNModC k N := by
  have hqk : ∀ m : ℤ, (jqNModC k N).coeff ((N : ℤ) * m) = (jqModC k).coeff m := fun m => by
    rw [jqNModC, qExpand_coeff_mul]
  have hqk0 : ∀ {n : ℤ}, ¬ ((N : ℕ) : ℤ) ∣ n → (jqNModC k N).coeff n = 0 := fun h => by
    rw [jqNModC]
    exact qExpand_coeff_of_not_dvd _ _ h
  have hqL : ∀ m : ℤ, (jqNModC L N).coeff ((N : ℤ) * m) = (jqModC L).coeff m := fun m => by
    rw [jqNModC, qExpand_coeff_mul]
  have hqL0 : ∀ {n : ℤ}, ¬ ((N : ℕ) : ℤ) ∣ n → (jqNModC L N).coeff n = 0 := fun h => by
    rw [jqNModC]
    exact qExpand_coeff_of_not_dvd _ _ h
  ext n
  rw [coeffRed_coeff]
  by_cases h : ((N : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hL : (⟨(jqNModC L N).coeff ((N : ℤ) * m), jqNModC_mem_integralCoeffs N A _⟩ : A)
        = (((jqModC ℤ).coeff m : ℤ) : A) := by
      ext
      push_cast
      rw [hqL, jqModC_eq_map_intCast, HahnSeries.map_coeff]
      rfl
    rw [hL, map_intCast, hqk]
    conv_rhs => rw [jqModC_eq_map_intCast]
    rw [HahnSeries.map_coeff]
    rfl
  · have hL : (⟨(jqNModC L N).coeff n, jqNModC_mem_integralCoeffs N A n⟩ : A) = 0 := by
      ext
      push_cast
      exact hqL0 h
    rw [hL, map_zero, hqk0 h]

private theorem coeffRed_constSeries (a : A) :
    coeffRed A red ⟨constSeries A a, constSeries_mem_integralCoeffs A a⟩
      = algebraMap k (LaurentSeries k) (red a) := by
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  by_cases h : n = 0
  · subst h
    have hL : (⟨(constSeries A a).coeff 0, constSeries_mem_integralCoeffs A a 0⟩ : A) = a := by
      ext
      push_cast
      rw [constSeries_apply, HahnSeries.coeff_single]
      simp
    rw [hL, if_pos rfl]
  · have hL : (⟨(constSeries A a).coeff n, constSeries_mem_integralCoeffs A a n⟩ : A) = 0 := by
      ext
      push_cast
      rw [constSeries_apply, HahnSeries.coeff_single]
      simp [h]
    rw [hL, map_zero, if_neg h]

end Modular

end HVC_Charp
end ModularCurve

end

section HvcInst

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem hvc_dedekindPsi_pos : 0 < dedekindPsi N := by
  rw [dedekindPsi]
  refine Finset.sum_pos' (fun d _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  · simpa using Nat.pos_of_ne_zero (NeZero.ne N)

private noncomputable def hvc_const : coeffSubring A K →+* modularRing N (coeffSubring A K) :=
  (constSeries (coeffSubring A K)).codRestrict (modularRing N (coeffSubring A K))
    (constSeries_mem_modularRing N (coeffSubring A K))

private theorem hvc_coe_const (a : coeffSubring A K) :
    ((hvc_const N A K a : modularRing N (coeffSubring A K)) : LaurentSeries (AlgebraicClosure ℚ)) =
      constSeries (coeffSubring A K) a :=
  rfl

private noncomputable def hvc_jR : modularRing N (coeffSubring A K) :=
  ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_modularRing N (coeffSubring A K)⟩

private noncomputable def hvc_jNR : modularRing N (coeffSubring A K) :=
  ⟨jqNModC (AlgebraicClosure ℚ) N, jqNModC_mem_modularRing N (coeffSubring A K)⟩

private theorem hvc_redRes_const (a : coeffSubring A K) :
    redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing N (coeffSubring A K))
        (modularRing_le_integralCoeffs N (coeffSubring A K)) (hvc_const N A K a) =
      algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
        (redRestrict (IsLocalRing.residue A) K a) :=
  HVC_Charp.coeffRed_constSeries (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) a

private theorem hvc_redRes_jR :
    redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing N (coeffSubring A K))
        (modularRing_le_integralCoeffs N (coeffSubring A K)) (hvc_jR N A K) = jqModC (IsLocalRing.ResidueField A) :=
  HVC_Charp.coeffRed_jqModC (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)

private theorem hvc_redRes_jNR :
    redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing N (coeffSubring A K))
        (modularRing_le_integralCoeffs N (coeffSubring A K)) (hvc_jNR N A K) = jqNModC (IsLocalRing.ResidueField A) N :=
  HVC_Charp.coeffRed_jqNModC N (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)

private theorem hvc_rel (data : ModularPolynomialData N) :
    (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (coeffSubring A K)))).eval₂
      (Polynomial.eval₂RingHom (constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)))
      (jqNModC (AlgebraicClosure ℚ) N) = 0 := by
  have h := data.eval_jqNModC_mul_eq_zero (AlgebraicClosure ℚ) 1
  simp only [jqNModC_one, one_mul] at h
  rw [Polynomial.eval₂_map]
  convert h using 2 <;> try rfl
  apply Polynomial.ringHom_ext
  · intro a
    simp [constSeries]
  · simp

private theorem hvc_natDegree_map (data : ModularPolynomialData N) :
    (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (coeffSubring A K)))).natDegree = dedekindPsi N := by
  rw [data.monic.natDegree_map, data.natDegree_eq]

private theorem hvc_span (data : ModularPolynomialData N) :
    ∀ r : modularRing N (coeffSubring A K),
      ∃ (s : Finset (ℕ × Fin (dedekindPsi N))) (c : ℕ × Fin (dedekindPsi N) → coeffSubring A K),
        r = ∑ p ∈ s, hvc_const N A K (c p) * (hvc_jR N A K ^ p.1 * hvc_jNR N A K ^ (p.2 : ℕ)) := by
  intro r
  have h := HVC_SD2.exists_sum_monomial_of_mem_closure (constSeries (coeffSubring A K))
    (jqModC (AlgebraicClosure ℚ)) (jqNModC (AlgebraicClosure ℚ) N) (data.monic.map _) (hvc_rel N A K data) r.2
  rw [hvc_natDegree_map] at h
  obtain ⟨s, c, hc⟩ := h
  refine ⟨s, c, Subtype.ext ?_⟩
  rw [hc]
  push_cast
  rfl

private theorem hvc_ind [ValuationRing (coeffSubring A K)]
    (hdeg : (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        {(jqModC (IsLocalRing.ResidueField A) : LaurentSeries (IsLocalRing.ResidueField A))}).relfinrank
      (modularFunctionFieldC (IsLocalRing.ResidueField A) N) = dedekindPsi N) :
    HVC_SD2.IndepModPrime
      (redKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing N (coeffSubring A K))
        (modularRing_le_integralCoeffs N (coeffSubring A K)))
      (hvc_const N A K)
      (fun p : ℕ × Fin (dedekindPsi N) => hvc_jR N A K ^ p.1 * hvc_jNR N A K ^ (p.2 : ℕ)) := by
  intro s c hmem
  refine HVC_SD2.indepModKer_monomial (hvc_const N A K) (redRestrict (IsLocalRing.residue A) K)
    (redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing N (coeffSubring A K))
      (modularRing_le_integralCoeffs N (coeffSubring A K)))
    (hvc_redRes_const N A K) (hvc_jR N A K) (hvc_jNR N A K) (hvc_dedekindPsi_pos N) ?_ ?_ s c hmem
  · rw [hvc_redRes_jR]
    exact transcendental_jqModC (IsLocalRing.ResidueField A)
  · rw [hvc_redRes_jR, hvc_redRes_jNR]
    exact hdeg

end HvcInst

private theorem hvc_scale {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hdvr : IsDiscreteValuationRing (coeffSubring A K)) (r : modularRing N (coeffSubring A K)) (hr : r ≠ 0) :
    ∃ (c : coeffSubring A K) (r' : modularRing N (coeffSubring A K)),
      r' ∉ redKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing N (coeffSubring A K))
          (modularRing_le_integralCoeffs N (coeffSubring A K)) ∧
        (r : LaurentSeries (AlgebraicClosure ℚ)) = constSeries (coeffSubring A K) c * (r' : LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI : IsDiscreteValuationRing (coeffSubring A K) := hdvr
  haveI : CharP (IsLocalRing.ResidueField A) q := hvc_charP hA
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hdeg := relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi (IsLocalRing.ResidueField A) N q hqN
  obtain ⟨c, r', hr', hrr'⟩ := HVC_SD2.exists_eq_mul_notMem _ (hvc_const N A K) _ (hvc_span N A K data) (hvc_ind N A K hdeg) hr
  refine ⟨c, r', hr', ?_⟩
  rw [hrr']
  push_cast
  rw [hvc_coe_const]

section HvcLoc

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem hvc_modularRing_N_le
    (hjN : jqNModC (AlgebraicClosure ℚ) N ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) :
    modularRing N (coeffSubring A K) ≤
      (modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) : Subring (LaurentSeries (AlgebraicClosure ℚ))) := by
  rw [modularRing, Subring.closure_le]
  rintro y (⟨a, rfl⟩ | rfl | rfl)
  · exact subring_le_localizedAtKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing (N * q) (coeffSubring A K))
      (modularRing_le_integralCoeffs (N * q) (coeffSubring A K)) (constSeries_mem_modularRing (N * q) (coeffSubring A K) a)
  · exact subring_le_localizedAtKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing (N * q) (coeffSubring A K))
      (modularRing_le_integralCoeffs (N * q) (coeffSubring A K)) (jqModC_mem_modularRing (N * q) (coeffSubring A K))
  · exact hjN

variable (M : ℕ) [NeZero M]

private theorem hvc_inv_mem {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K))
    (hred : redLoc (⟨x, hx⟩ : modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) ≠ 0) :
    x⁻¹ ∈ modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := by
  obtain ⟨r, s, hs, hxs⟩ := id hx
  have hspec := redLoc_spec (⟨x, hx⟩ : modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) hxs
  have hsne := redRes_ne_zero_of_notMem hs
  have hr : r ∉ redKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing M (coeffSubring A K))
      (modularRing_le_integralCoeffs M (coeffSubring A K)) := by
    rw [notMem_redKer_iff, ← hspec]
    exact mul_ne_zero hred hsne
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hr
    have h0 : r = 0 := by
      apply Subtype.ext
      rw [← hxs]
      simp
    rw [h0]
    exact Ideal.zero_mem _
  exact ⟨s, r, hr, by rw [← hxs, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]⟩

private theorem hvc_redLoc_eq_coeffRed {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K))
    (hx' : x ∈ integralCoeffs (coeffSubring A K)) :
    redLoc (⟨x, hx⟩ : modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) =
      coeffRed (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) ⟨x, hx'⟩ := by
  obtain ⟨r, s, hs, hxs⟩ := id hx
  have hspec := redLoc_spec (⟨x, hx⟩ : modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) hxs
  have hsne := redRes_ne_zero_of_notMem hs
  rw [redRes_apply] at hsne
  rw [redRes_apply, redRes_apply] at hspec
  apply mul_right_cancel₀ hsne
  rw [hspec, ← map_mul]
  congr 1
  exact Subtype.ext hxs.symm

private theorem hvc_redLoc_const (a : coeffSubring A K) :
    redLoc (⟨constSeries (coeffSubring A K) a, subring_le_localizedAtKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)
        (modularRing M (coeffSubring A K)) (modularRing_le_integralCoeffs M (coeffSubring A K))
        (constSeries_mem_modularRing M (coeffSubring A K) a)⟩ :
      modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) =
      algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (redRestrict (IsLocalRing.residue A) K a) := by
  rw [hvc_redLoc_eq_coeffRed K M _ (constSeries_mem_integralCoeffs (coeffSubring A K) a)]
  exact HVC_Charp.coeffRed_constSeries (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) a

end HvcLoc

section HvcOrd

variable (k : Type*) [Field k]

private theorem hvc_l2_aeval_j_nzd :
    nonZeroDivisors (Polynomial k)
      ≤ Submonoid.comap (Polynomial.aeval (R := k) (jqModC k) : Polynomial k →ₐ[k] LaurentSeries k)
          (nonZeroDivisors (LaurentSeries k)) := by
  intro p hp
  rw [Submonoid.mem_comap]
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => nonZeroDivisors.ne_zero hp ?_
  exact (transcendental_iff_injective.mp (transcendental_jqModC k)) (by rw [h0, map_zero])

private noncomputable def hvc_l2lift : RatFunc k →ₐ[k] LaurentSeries k :=
  RatFunc.liftAlgHom (Polynomial.aeval (R := k) (jqModC k)) (hvc_l2_aeval_j_nzd k)

private theorem hvc_l2lift_algebraMap (p : Polynomial k) :
    hvc_l2lift k (algebraMap (Polynomial k) (RatFunc k) p) = Polynomial.aeval (jqModC k) p := by
  have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval (R := k) (jqModC k)) (hvc_l2_aeval_j_nzd k) p 1
  rwa [map_one, div_one, map_one, div_one] at h

private theorem hvc_l2lift_X : hvc_l2lift k RatFunc.X = jqModC k := by
  rw [← RatFunc.algebraMap_X, hvc_l2lift_algebraMap, Polynomial.aeval_X]

private theorem hvc_l2lift_comp :
    ((hvc_l2lift k).toRingHom.comp (algebraMap (Polynomial k) (RatFunc k))).comp
        (Polynomial.mapRingHom (Int.castRingHom k))
      = (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp [hvc_l2lift_X]

private noncomputable abbrev hvc_l2ratAlg : Algebra (RatFunc k) (LaurentSeries k) := (hvc_l2lift k).toRingHom.toAlgebra

variable {k}

private theorem hvc_l2_twist {q : ℕ} [Fact q.Prime] [CharP k q] {M : ℕ} [NeZero M] (data : ModularPolynomialData M)
    {x y : LaurentSeries k} (h : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (x ^ q)).toRingHom (y ^ q) = 0 := by
  haveI : CharP (LaurentSeries k) q := charP_of_injective_ringHom HahnSeries.C_injective q
  haveI : ExpChar (LaurentSeries k) q := ExpChar.prime Fact.out
  have h' := congrArg (frobenius (LaurentSeries k) q) h
  rw [Polynomial.hom_eval₂, map_zero, frobenius_def] at h'
  convert h' using 2
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp [frobenius_def]

private theorem hvc_l2_aeval_ratPoly {M : ℕ} [NeZero M] (data : ModularPolynomialData M) (y : LaurentSeries k) :
    @Polynomial.aeval (RatFunc k) (LaurentSeries k) _ _ (hvc_l2ratAlg k) y
        ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k)))
      = data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom y := by
  letI := hvc_l2ratAlg k
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map, ← hvc_l2lift_comp k]
  rfl

private theorem hvc_l2_aeval_ratPoly_twist {q : ℕ} (M : ℕ) [NeZero M] (data : ModularPolynomialData M)
    (y : LaurentSeries k) :
    @Polynomial.aeval (RatFunc k) (LaurentSeries k) _ _ (hvc_l2ratAlg k) y
        (((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (Polynomial.expand k (q * q)).toRingHom).map
          (algebraMap (Polynomial k) (RatFunc k)))
      = data.Φ.eval₂ (Polynomial.aeval (R := ℤ) ((jqModC k ^ q) ^ q)).toRingHom y := by
  letI := hvc_l2ratAlg k
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map, Polynomial.eval₂_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [RingHom.algebraMap_toAlgebra]
  · simp [RingHom.algebraMap_toAlgebra, hvc_l2lift_X, pow_mul]

variable (k)

private theorem hvc_ord_transcendental_jqNModC (N : ℕ) [NeZero N] : Transcendental k (jqNModC k N) := by
  refine transcendental_iff.mpr fun p hp => ?_
  refine transcendental_iff.mp (transcendental_jqModC k) p ?_
  refine qExpand_injective N ?_
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂]
  have hc : (qExpand k N).comp (algebraMap k (LaurentSeries k)) = algebraMap k (LaurentSeries k) := by
    ext a
    have ha : algebraMap k (LaurentSeries k) a = HahnSeries.C a := by
      show HahnSeries.ofPowerSeries ℤ k (PowerSeries.C a) = HahnSeries.C a
      exact HahnSeries.ofPowerSeries_C a
    simp only [RingHom.comp_apply, ha, qExpand_C]
  rw [hc]
  exact (Polynomial.aeval_def (jqNModC k N) p).symm.trans hp

private theorem phiN_eval_pow_pow_ne_zero {q : ℕ} [Fact q.Prime] [CharP k q] {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N)
    (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom ((jqNModC k N ^ q) ^ q) ≠ 0 := by
  intro h0
  have hN : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)

  have hrel : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom (jqNModC k N) = 0 := by
    have h := data.eval_jqNModC_mul_eq_zero k 1
    have e : jqNModC k (1 * N) = jqNModC k N := qExpand_congr (one_mul N) _
    rwa [jqNModC_one, e] at h
  have htw := hvc_l2_twist data (hvc_l2_twist data hrel)
  letI := hvc_l2ratAlg k
  set Φk : Polynomial (Polynomial k) := data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)) with hΦk
  set ΦR : Polynomial (RatFunc k) := Φk.map (algebraMap (Polynomial k) (RatFunc k)) with hΦR
  set ΦR' : Polynomial (RatFunc k) :=
    (Φk.map (Polynomial.expand k (q * q)).toRingHom).map (algebraMap (Polynomial k) (RatFunc k)) with hΦR'
  have hΦkm : Φk.Monic := data.monic.map _
  have hRm : ΦR.Monic := hΦkm.map _
  have hR'm : ΦR'.Monic := (hΦkm.map _).map _
  have hirr : Irreducible ΦR := data.irreducible_map_ratFunc_of_natCast_ne_zero k N hN
  have hR0 : Polynomial.aeval ((jqNModC k N ^ q) ^ q) ΦR = 0 := by
    rw [hΦR, hΦk, hvc_l2_aeval_ratPoly]; exact h0
  have hR'0 : Polynomial.aeval ((jqNModC k N ^ q) ^ q) ΦR' = 0 := by
    rw [hΦR', hΦk, hvc_l2_aeval_ratPoly_twist]; exact htw
  have hmin : ΦR = minpoly (RatFunc k) ((jqNModC k N ^ q) ^ q) := minpoly.eq_of_irreducible_of_monic hirr hR0 hRm
  have hdvd : ΦR ∣ ΦR' := by
    rw [hmin]
    exact minpoly.dvd (RatFunc k) _ hR'0
  have hdeg : ΦR'.natDegree ≤ ΦR.natDegree := by
    rw [hΦR', hΦR, (hΦkm.map _).natDegree_map, hΦkm.natDegree_map, hΦkm.natDegree_map]
  have heq : ΦR' = ΦR := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hRm hR'm hdvd hdeg

  have hconst : ∀ i, (Φk.coeff i).natDegree = 0 := by
    intro i
    have hc := congrArg (fun p => Polynomial.coeff p i) heq
    simp only [hΦR', hΦR, Polynomial.coeff_map] at hc
    have hc' : Polynomial.expand k (q * q) (Φk.coeff i) = Φk.coeff i :=
      IsFractionRing.injective (Polynomial k) (RatFunc k) hc
    have hdeg' := congrArg Polynomial.natDegree hc'
    rw [Polynomial.natDegree_expand] at hdeg'
    have hq2 : 2 ≤ q * q := by nlinarith [(Fact.out : q.Prime).two_le]
    by_contra hne
    have hpos : 0 < (Φk.coeff i).natDegree := Nat.pos_of_ne_zero hne
    nlinarith

  set Q : Polynomial k := Φk.map Polynomial.constantCoeff with hQ
  have hQm : Q.Monic := hΦkm.map _
  have hQ0 : Polynomial.aeval (jqNModC k N) Q = 0 := by
    have hrel' : Φk.eval₂ (Polynomial.aeval (R := k) (jqModC k)).toRingHom (jqNModC k N) = 0 := by
      rw [hΦk, Polynomial.eval₂_map, ← hrel]
      congr 1
      apply Polynomial.ringHom_ext <;> simp
    rw [Polynomial.aeval_def, hQ, Polynomial.eval₂_map, ← hrel', Polynomial.eval₂_eq_sum_range,
      Polynomial.eval₂_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [Polynomial.eq_C_of_natDegree_eq_zero (hconst i)]
    simp
  exact hvc_ord_transcendental_jqNModC k N ⟨Q, hQm.ne_zero, hQ0⟩

end HvcOrd

private theorem hvc_jqN_ne_pow_pow (k : Type*) [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] {N : ℕ} [NeZero N]
    (hqN : ¬ q ∣ N) : jqNModC k N ≠ (jqNModC k N ^ q) ^ q := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  intro h
  apply phiN_eval_pow_pow_ne_zero k hqN data
  have hrel := data.eval_jqNModC_mul_eq_zero k 1
  simp only [jqNModC_one, one_mul] at hrel
  rw [← h]
  exact hrel

private theorem hvc_jqN_mul_sub_pow {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (ϖ : coeffSubring A K)
    (hϖ : ∀ c : coeffSubring A K, redRestrict (IsLocalRing.residue A) K c = 0 ↔ ∃ d : coeffSubring A K, c = ϖ * d)
    (hjN : jqNModC (AlgebraicClosure ℚ) N ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) :
    ∃ b ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K),
      jqNModC (AlgebraicClosure ℚ) (N * q) = jqNModC (AlgebraicClosure ℚ) N ^ q + constSeries (coeffSubring A K) ϖ * b := by
  haveI : CharP (IsLocalRing.ResidueField A) q := hvc_charP hA
  have hjNq : jqNModC (AlgebraicClosure ℚ) (N * q) ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) :=
    subring_le_localizedAtKer _ _ _ _ (jqNModC_mem_modularRing (N * q) (coeffSubring A K))

  obtain ⟨data, hK⟩ := exists_kroneckerCongruence_of_prime q
  obtain ⟨Rm, hRm, -⟩ := existsUnique_kroneckerRemainder q data hK
  have hrel := data.eval_jqNModC_mul_eq_zero (AlgebraicClosure ℚ) N
  rw [hRm] at hrel
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X, eq_intCast, Int.cast_natCast] at hrel

  set Rv : LaurentSeries (AlgebraicClosure ℚ) := Rm.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC (AlgebraicClosure ℚ) N) : Polynomial ℤ →+* LaurentSeries (AlgebraicClosure ℚ)) (jqNModC (AlgebraicClosure ℚ) (N * q)) with hRv_def

  have hRv : Rv ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := by
    have hcomp : (modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)).subtype.comp (Polynomial.aeval (R := ℤ) (⟨_, hjN⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) : Polynomial ℤ →+* modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = (Polynomial.aeval (R := ℤ) (jqNModC (AlgebraicClosure ℚ) N) : Polynomial ℤ →+* LaurentSeries (AlgebraicClosure ℚ)) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    have h := Polynomial.hom_eval₂ Rm (Polynomial.aeval (R := ℤ) (⟨_, hjN⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) : Polynomial ℤ →+* modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) (modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)).subtype (⟨_, hjNq⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K))
    rw [hcomp] at h
    have h' : Rv = (modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)).subtype (Rm.eval₂ (Polynomial.aeval (R := ℤ) (⟨_, hjN⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) : Polynomial ℤ →+* modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) ⟨_, hjNq⟩) := by
      rw [h]
      rfl
    rw [h']
    exact Subtype.mem _
  have h1 : redLoc (⟨_, hjN⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = jqNModC (IsLocalRing.ResidueField A) N := by
    rw [hvc_redLoc_eq_coeffRed K (N * q) hjN (jqNModC_mem_integralCoeffs N (coeffSubring A K))]
    exact HVC_Charp.coeffRed_jqNModC N (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)
  have h2 : redLoc (⟨_, hjNq⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = jqNModC (IsLocalRing.ResidueField A) N ^ q := by
    rw [hvc_redLoc_eq_coeffRed K (N * q) hjNq (jqNModC_mem_integralCoeffs (N * q) (coeffSubring A K)),
      HVC_Charp.coeffRed_jqNModC (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)]
    exact jqNModC_mul_eq_pow (IsLocalRing.ResidueField A) N
  set aB : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := ⟨_, hjN⟩ with haB
  set bB : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := ⟨_, hjNq⟩ with hbB
  have h1' : redLoc aB = jqNModC (IsLocalRing.ResidueField A) N := h1
  have h2' : redLoc bB = jqNModC (IsLocalRing.ResidueField A) N ^ q := h2

  have hredu : redLoc (aB - bB ^ q) ≠ 0 := by
    have e : redLoc (aB - bB ^ q) = redLoc aB - redLoc bB ^ q :=
      (map_sub (redLocHom (A := coeffSubring A K) (red := redRestrict (IsLocalRing.residue A) K)
      (R := modularRing (N * q) (coeffSubring A K)) (hR := modularRing_le_integralCoeffs (N * q) (coeffSubring A K))) aB (bB ^ q)).trans (congrArg (fun t => redLoc aB - t) (map_pow (redLocHom (A := coeffSubring A K) (red := redRestrict (IsLocalRing.residue A) K)
      (R := modularRing (N * q) (coeffSubring A K)) (hR := modularRing_le_integralCoeffs (N * q) (coeffSubring A K))) bB q))
    rw [e, h1', h2']
    exact sub_ne_zero.mpr (hvc_jqN_ne_pow_pow (IsLocalRing.ResidueField A) hqN)
  have huinv : (jqNModC (AlgebraicClosure ℚ) N - jqNModC (AlgebraicClosure ℚ) (N * q) ^ q)⁻¹ ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) :=
    hvc_inv_mem K (N * q) (aB - bB ^ q).2 hredu
  have hu0 : jqNModC (AlgebraicClosure ℚ) N - jqNModC (AlgebraicClosure ℚ) (N * q) ^ q ≠ 0 := by
    intro h0
    apply hredu
    have heq : aB - bB ^ q = 0 := Subtype.ext h0
    rw [heq]
    exact map_zero (redLocHom (A := coeffSubring A K) (red := redRestrict (IsLocalRing.residue A) K)
      (R := modularRing (N * q) (coeffSubring A K)) (hR := modularRing_le_integralCoeffs (N * q) (coeffSubring A K)))

  have hq0 : redRestrict (IsLocalRing.residue A) K (q : coeffSubring A K) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero (IsLocalRing.ResidueField A) q
  obtain ⟨d, hd⟩ := (hϖ _).mp hq0
  have hqL : ((q : ℕ) : LaurentSeries (AlgebraicClosure ℚ)) = constSeries (coeffSubring A K) ϖ * constSeries (coeffSubring A K) d := by
    rw [← map_mul, ← hd, map_natCast]

  refine ⟨constSeries (coeffSubring A K) d * Rv * (jqNModC (AlgebraicClosure ℚ) N - jqNModC (AlgebraicClosure ℚ) (N * q) ^ q)⁻¹,
    mul_mem (mul_mem (subring_le_localizedAtKer _ _ _ _ (constSeries_mem_modularRing (N * q) (coeffSubring A K) d)) hRv) huinv, ?_⟩

  have hrel' : (jqNModC (AlgebraicClosure ℚ) N ^ q - jqNModC (AlgebraicClosure ℚ) (N * q)) *
      (jqNModC (AlgebraicClosure ℚ) N - jqNModC (AlgebraicClosure ℚ) (N * q) ^ q) +
        ((q : ℕ) : LaurentSeries (AlgebraicClosure ℚ)) * Rv = 0 := by
    convert hrel using 3 <;> first | rfl | simp
  have hq2 : ((q : ℕ) : LaurentSeries (AlgebraicClosure ℚ)) * Rv =
      (jqNModC (AlgebraicClosure ℚ) (N * q) - jqNModC (AlgebraicClosure ℚ) N ^ q) *
        (jqNModC (AlgebraicClosure ℚ) N - jqNModC (AlgebraicClosure ℚ) (N * q) ^ q) := by
    linear_combination hrel'
  have h3 : constSeries (coeffSubring A K) ϖ * (constSeries (coeffSubring A K) d * Rv *
      (jqNModC (AlgebraicClosure ℚ) N - jqNModC (AlgebraicClosure ℚ) (N * q) ^ q)⁻¹) =
      jqNModC (AlgebraicClosure ℚ) (N * q) - jqNModC (AlgebraicClosure ℚ) N ^ q := by
    rw [show constSeries (coeffSubring A K) ϖ * (constSeries (coeffSubring A K) d * Rv *
        (jqNModC (AlgebraicClosure ℚ) N - jqNModC (AlgebraicClosure ℚ) (N * q) ^ q)⁻¹) =
        (constSeries (coeffSubring A K) ϖ * constSeries (coeffSubring A K) d) * Rv *
          (jqNModC (AlgebraicClosure ℚ) N - jqNModC (AlgebraicClosure ℚ) (N * q) ^ q)⁻¹ by ring,
      ← hqL, hq2, mul_inv_cancel_right₀ hu0]
  rw [h3]
  ring

private theorem hvc_kernel {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hdvr : IsDiscreteValuationRing (coeffSubring A K)) (ϖ : coeffSubring A K)
    (hϖ : ∀ c : coeffSubring A K, redRestrict (IsLocalRing.residue A) K c = 0 ↔ ∃ d : coeffSubring A K, c = ϖ * d)
    (hjN : jqNModC (AlgebraicClosure ℚ) N ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K))
    (z : modularRing (N * q) (coeffSubring A K))
    (hz : z ∈ redKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing (N * q) (coeffSubring A K))
      (modularRing_le_integralCoeffs (N * q) (coeffSubring A K))) :
    ∃ b ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K),
      (z : LaurentSeries (AlgebraicClosure ℚ)) = constSeries (coeffSubring A K) ϖ * b := by

  have hRN := hvc_modularRing_N_le K hjN
  have hB : ∀ {y : LaurentSeries (AlgebraicClosure ℚ)}, y ∈ modularRing N (coeffSubring A K) →
      y ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := fun hy => hRN hy
  have hϖB : constSeries (coeffSubring A K) ϖ ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) :=
    hB (constSeries_mem_modularRing N (coeffSubring A K) ϖ)
  obtain ⟨b₁, hb₁, hjq⟩ := hvc_jqN_mul_sub_pow hA hqN K ϖ hϖ hjN

  have key : ∀ y ∈ modularRing (N * q) (coeffSubring A K), ∃ (y₀ : modularRing N (coeffSubring A K))
      (c : LaurentSeries (AlgebraicClosure ℚ)), c ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) ∧
        y = (y₀ : LaurentSeries (AlgebraicClosure ℚ)) + constSeries (coeffSubring A K) ϖ * c := by
    intro y hy
    have hy' : y ∈ Subring.closure (Set.range (constSeries (coeffSubring A K)) ∪
        {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (N * q)}) := hy
    clear hy
    induction hy' using Subring.closure_induction with
    | mem x hx =>
        rcases hx with ⟨a, rfl⟩ | rfl | rfl
        · exact ⟨⟨_, constSeries_mem_modularRing N (coeffSubring A K) a⟩, 0, zero_mem _, by simp⟩
        · exact ⟨⟨_, jqModC_mem_modularRing N (coeffSubring A K)⟩, 0, zero_mem _, by simp⟩
        · exact ⟨⟨_, pow_mem (jqNModC_mem_modularRing N (coeffSubring A K)) q⟩, b₁, hb₁, by rw [hjq]⟩
    | zero => exact ⟨0, 0, zero_mem _, by simp⟩
    | one => exact ⟨1, 0, zero_mem _, by simp⟩
    | add x y _ _ ihx ihy =>
        obtain ⟨x₀, c, hc, rfl⟩ := ihx
        obtain ⟨y₀, d, hd, rfl⟩ := ihy
        exact ⟨x₀ + y₀, c + d, add_mem hc hd, by push_cast; ring⟩
    | neg x _ ihx =>
        obtain ⟨x₀, c, hc, rfl⟩ := ihx
        exact ⟨-x₀, -c, neg_mem hc, by push_cast; ring⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨x₀, c, hc, rfl⟩ := ihx
        obtain ⟨y₀, d, hd, rfl⟩ := ihy
        refine ⟨x₀ * y₀, (x₀ : LaurentSeries (AlgebraicClosure ℚ)) * d + c * (y₀ : LaurentSeries (AlgebraicClosure ℚ)) +
          constSeries (coeffSubring A K) ϖ * (c * d), ?_, by push_cast; ring⟩
        exact add_mem (add_mem (mul_mem (hB x₀.2) hd) (mul_mem hc (hB y₀.2))) (mul_mem hϖB (mul_mem hc hd))

  obtain ⟨z₀, c, hc, hzc⟩ := key z z.2
  have hz₀B := hB z₀.2

  have hzB : (z : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) :=
    subring_le_localizedAtKer _ _ _ _ z.2
  have hred_z : redLoc (⟨(z : LaurentSeries (AlgebraicClosure ℚ)), hzB⟩ :
      modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = 0 := by
    have h1 := RingHom.mem_ker.mp hz
    rw [redRes_apply] at h1
    rw [hvc_redLoc_eq_coeffRed K (N * q) hzB (modularRing_le_integralCoeffs (N * q) (coeffSubring A K) z.2)]
    exact h1
  have hred_ϖ : redLoc (⟨constSeries (coeffSubring A K) ϖ, hϖB⟩ :
      modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = 0 := by
    rw [hvc_redLoc_eq_coeffRed K (N * q) _ (constSeries_mem_integralCoeffs (coeffSubring A K) ϖ),
      HVC_Charp.coeffRed_constSeries, (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩, map_zero]
  have hred_z₀ : redLoc (⟨(z₀ : LaurentSeries (AlgebraicClosure ℚ)), hz₀B⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = 0 := by
    set zB : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := ⟨(z : LaurentSeries (AlgebraicClosure ℚ)), hzB⟩ with hzBdef
    set z₀B : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := ⟨(z₀ : LaurentSeries (AlgebraicClosure ℚ)), hz₀B⟩ with hz₀Bdef
    set ϖB : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := ⟨constSeries (coeffSubring A K) ϖ, hϖB⟩ with hϖBdef
    set cB : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := ⟨c, hc⟩ with hcBdef
    have hsum : zB = z₀B + ϖB * cB := Subtype.ext hzc
    have e : redLoc zB = redLoc z₀B + redLoc ϖB * redLoc cB := by
      rw [hsum]
      exact (map_add (redLocHom (A := coeffSubring A K) (red := redRestrict (IsLocalRing.residue A) K)
      (R := modularRing (N * q) (coeffSubring A K)) (hR := modularRing_le_integralCoeffs (N * q) (coeffSubring A K))) z₀B (ϖB * cB)).trans (congrArg (fun t => redLoc z₀B + t) (map_mul (redLocHom (A := coeffSubring A K) (red := redRestrict (IsLocalRing.residue A) K)
      (R := modularRing (N * q) (coeffSubring A K)) (hR := modularRing_le_integralCoeffs (N * q) (coeffSubring A K))) ϖB cB))
    have hz' : redLoc zB = 0 := hred_z
    have hϖ' : redLoc ϖB = 0 := hred_ϖ
    rw [hz', hϖ', zero_mul, add_zero] at e
    exact e.symm

  have hz₀ker : z₀ ∈ redKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing N (coeffSubring A K))
      (modularRing_le_integralCoeffs N (coeffSubring A K)) := by
    rw [redKer, RingHom.mem_ker, redRes_apply, ← hvc_redLoc_eq_coeffRed K (N * q) hz₀B]
    exact hred_z₀
  by_cases hz₀0 : z₀ = 0
  · refine ⟨c, hc, ?_⟩
    rw [hzc, hz₀0]
    simp
  obtain ⟨a, r', hr', hz₀⟩ := hvc_scale hA hqN K hdvr z₀ hz₀0

  have ha : redRestrict (IsLocalRing.residue A) K a = 0 := by
    have h1 : redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing N (coeffSubring A K))
        (modularRing_le_integralCoeffs N (coeffSubring A K)) z₀ = 0 := RingHom.mem_ker.mp hz₀ker
    have h2 : z₀ = hvc_const N A K a * r' := Subtype.ext (by rw [hz₀]; rfl)
    rw [h2, map_mul, hvc_redRes_const] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact (map_eq_zero_iff _ (algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))).injective).mp h
    · exact absurd h (redRes_ne_zero_of_notMem hr')
  obtain ⟨d, rfl⟩ := (hϖ a).mp ha
  refine ⟨constSeries (coeffSubring A K) d * (r' : LaurentSeries (AlgebraicClosure ℚ)) + c, add_mem (mul_mem (hB (constSeries_mem_modularRing N _ d)) (hB r'.2)) hc, ?_⟩
  rw [hzc, hz₀, map_mul]
  ring

private def hvc_HasPres {A : ValuationSubring (AlgebraicClosure ℚ)} (ϖ : AlgebraicClosure ℚ) (m : ℕ)
    (y : LaurentSeries (AlgebraicClosure ℚ)) : Prop :=
  ∃ x' y' : LaurentSeries A, coeffMap (IsLocalRing.residue A) y' ≠ 0 ∧
    y * coeffMap A.subtype y' = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ ^ m) *
      coeffMap A.subtype x'

open HahnSeries in
private theorem hvc_bound_algebraMap_eq_C (c : AlgebraicClosure ℚ) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c = C c := by
  show HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (PowerSeries.C c) = C c
  exact HahnSeries.ofPowerSeries_C c

open HahnSeries in

private theorem hvc_bound_C_mul_mem {A : ValuationSubring (AlgebraicClosure ℚ)} {ϖ : AlgebraicClosure ℚ} (hϖA : ϖ ∈ A)
    {z : LaurentSeries (AlgebraicClosure ℚ)} (hz : z ∈ integralCoeffs A.toSubring) :
    C ϖ * z ∈ integralCoeffs A.toSubring := by
  intro n
  rw [C_mul_eq_smul, coeff_smul, smul_eq_mul]
  exact A.toSubring.mul_mem hϖA (hz n)

open HahnSeries in
private theorem hvc_bound_C_pow_mul_mem {A : ValuationSubring (AlgebraicClosure ℚ)} {ϖ : AlgebraicClosure ℚ} (hϖA : ϖ ∈ A)
    (m : ℕ) {z : LaurentSeries (AlgebraicClosure ℚ)} (hz : z ∈ integralCoeffs A.toSubring) :
    C ϖ ^ m * z ∈ integralCoeffs A.toSubring := by
  induction m with
  | zero => simpa using hz
  | succ m ih =>
    rw [pow_succ', mul_assoc]
    exact hvc_bound_C_mul_mem hϖA ih

private theorem hvc_bound_coeffMap_mem {A : ValuationSubring (AlgebraicClosure ℚ)} (x : LaurentSeries A) :
    coeffMap A.subtype x ∈ integralCoeffs A.toSubring := by
  intro n
  rw [coeffMap_coeff]
  exact (x.coeff n).2

open HahnSeries in
private theorem hvc_bound_coeffRed_C_mul {A : ValuationSubring (AlgebraicClosure ℚ)} {ϖ : AlgebraicClosure ℚ} (hϖA : ϖ ∈ A)
    (hres : IsLocalRing.residue A ⟨ϖ, hϖA⟩ = 0)
    {z : LaurentSeries (AlgebraicClosure ℚ)} (hz : z ∈ integralCoeffs A.toSubring) :
    coeffRed A.toSubring (IsLocalRing.residue A) ⟨C ϖ * z, hvc_bound_C_mul_mem hϖA hz⟩ = 0 := by
  ext n
  rw [coeffRed_coeff, coeff_zero]
  have hcoef : (⟨(C ϖ * z).coeff n, hvc_bound_C_mul_mem hϖA hz n⟩ : A) = ⟨ϖ, hϖA⟩ * ⟨z.coeff n, hz n⟩ :=
    Subtype.ext (by
      show (C ϖ * z).coeff n = ϖ * z.coeff n
      rw [C_mul_eq_smul, coeff_smul, smul_eq_mul])
  rw [hcoef, map_mul, hres, zero_mul]

private theorem hvc_bound_coeffRed_coeffMap {A : ValuationSubring (AlgebraicClosure ℚ)} (x : LaurentSeries A) :
    coeffRed A.toSubring (IsLocalRing.residue A) ⟨coeffMap A.subtype x, hvc_bound_coeffMap_mem x⟩ =
      coeffMap (IsLocalRing.residue A) x := by
  ext n
  rfl

open HahnSeries in

private theorem hvc_bound_div {A : ValuationSubring (AlgebraicClosure ℚ)} (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ϖ : coeffSubring A K) (hϖne : (ϖ : AlgebraicClosure ℚ) ≠ 0)
    (hres : IsLocalRing.residue A ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0)
    (hϖ : ∀ c : coeffSubring A K, redRestrict (IsLocalRing.residue A) K c = 0 ↔ ∃ d : coeffSubring A K, c = ϖ * d) :
    ∀ (m : ℕ) (y : LaurentSeries (AlgebraicClosure ℚ)), y ∈ integralCoeffs (coeffSubring A K) →
      hvc_HasPres (A := A) (ϖ : AlgebraicClosure ℚ) m y →
      ∀ n : ℤ, ∃ d : coeffSubring A K, y.coeff n = (ϖ : AlgebraicClosure ℚ) ^ m * d := by
  intro m
  induction m with
  | zero =>
    intro y hy _ n
    exact ⟨⟨y.coeff n, hy n⟩, by simp⟩
  | succ m ih =>
    intro y hy hpres n
    obtain ⟨x', y', hy'ne, hid⟩ := hpres
    rw [hvc_bound_algebraMap_eq_C, map_pow] at hid
    have hϖA : (ϖ : AlgebraicClosure ℚ) ∈ A := ϖ.2.1
    have hyA : y ∈ integralCoeffs A.toSubring := fun i => (inf_le_left : coeffSubring A K ≤ A.toSubring) (hy i)

    have hW := hvc_bound_C_pow_mul_mem hϖA m (hvc_bound_coeffMap_mem x')
    have hS : (⟨y, hyA⟩ : integralCoeffs A.toSubring) * ⟨coeffMap A.subtype y', hvc_bound_coeffMap_mem y'⟩ =
        ⟨C (ϖ : AlgebraicClosure ℚ) * (C (ϖ : AlgebraicClosure ℚ) ^ m * coeffMap A.subtype x'),
          hvc_bound_C_mul_mem hϖA hW⟩ := by
      apply Subtype.ext
      push_cast
      rw [hid, pow_succ', mul_assoc]
    have hred := congrArg (coeffRed A.toSubring (IsLocalRing.residue A)) hS
    rw [map_mul, hvc_bound_coeffRed_coeffMap, hvc_bound_coeffRed_C_mul hϖA hres hW] at hred
    have hy0 : coeffRed A.toSubring (IsLocalRing.residue A) ⟨y, hyA⟩ = 0 :=
      (mul_eq_zero.mp hred).resolve_right hy'ne

    have hstep : ∀ i : ℤ, ∃ e : coeffSubring A K, y.coeff i = (ϖ : AlgebraicClosure ℚ) * e := by
      intro i
      have h1 : IsLocalRing.residue A ⟨y.coeff i, hyA i⟩ = 0 := by
        have := congrArg (fun z : LaurentSeries (IsLocalRing.ResidueField A) => z.coeff i) hy0
        simpa only [coeffRed_coeff, coeff_zero] using this
      have h2 : redRestrict (IsLocalRing.residue A) K ⟨y.coeff i, hy i⟩ = 0 := h1
      obtain ⟨e, he⟩ := (hϖ _).mp h2
      exact ⟨e, congrArg Subtype.val he⟩

    set y₁ : LaurentSeries (AlgebraicClosure ℚ) := C (ϖ : AlgebraicClosure ℚ)⁻¹ * y with hy₁
    have hy₁coeff : ∀ i : ℤ, y₁.coeff i = (ϖ : AlgebraicClosure ℚ)⁻¹ * y.coeff i := by
      intro i
      rw [hy₁, C_mul_eq_smul, coeff_smul, smul_eq_mul]
    have hy₁mem : y₁ ∈ integralCoeffs (coeffSubring A K) := by
      intro i
      obtain ⟨e, he⟩ := hstep i
      rw [hy₁coeff, he, inv_mul_cancel_left₀ hϖne]
      exact e.2
    have hC : C (ϖ : AlgebraicClosure ℚ)⁻¹ * C (ϖ : AlgebraicClosure ℚ) = (1 : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [← map_mul, inv_mul_cancel₀ hϖne, map_one]
    have hy₁pres : hvc_HasPres (A := A) (ϖ : AlgebraicClosure ℚ) m y₁ := by
      refine ⟨x', y', hy'ne, ?_⟩
      rw [hvc_bound_algebraMap_eq_C, map_pow, hy₁]
      linear_combination (C (ϖ : AlgebraicClosure ℚ)⁻¹) * hid +
        (C (ϖ : AlgebraicClosure ℚ) ^ m * coeffMap A.subtype x') * hC
    obtain ⟨d, hd⟩ := ih y₁ hy₁mem hy₁pres n
    refine ⟨d, ?_⟩
    have hyn : y.coeff n = (ϖ : AlgebraicClosure ℚ) * y₁.coeff n := by
      rw [hy₁coeff, mul_inv_cancel_left₀ hϖne]
    rw [hyn, hd, pow_succ', mul_assoc]

private theorem hvc_bound {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (ϖ : coeffSubring A K)
    (hϖ0 : redRestrict (IsLocalRing.residue A) K ϖ = 0) (hϖne : (ϖ : AlgebraicClosure ℚ) ≠ 0)
    (hϖ : ∀ c : coeffSubring A K, redRestrict (IsLocalRing.residue A) K c = 0 ↔ ∃ d : coeffSubring A K, c = ϖ * d)
    {y : LaurentSeries (AlgebraicClosure ℚ)} (hy : y ∈ integralCoeffs (coeffSubring A K)) (hy0 : y ≠ 0) :
    ∃ B : ℕ, ∀ m : ℕ, hvc_HasPres (A := A) (ϖ : AlgebraicClosure ℚ) m y → m ≤ B := by

  obtain ⟨n₀, hn₀⟩ : ∃ n : ℤ, y.coeff n ≠ 0 := by
    by_contra h
    push Not at h
    exact hy0 (HahnSeries.ext (funext h))
  have hϖA : (ϖ : AlgebraicClosure ℚ) ∈ A := ϖ.2.1
  set ϖA : A := ⟨(ϖ : AlgebraicClosure ℚ), hϖA⟩ with hϖA_def
  have hres : IsLocalRing.residue A ϖA = 0 := hϖ0
  have hϖmem : ϖA ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.residue_eq_zero_iff ϖA).mp hres
  have hϖAne : ϖA ≠ 0 := fun h => hϖne (congrArg Subtype.val h)
  have hϖunit : ¬ IsUnit ϖA := hϖmem
  set c₀ : A := ⟨y.coeff n₀, (inf_le_left : coeffSubring A K ≤ A.toSubring) (hy n₀)⟩ with hc₀_def
  have hc₀ : c₀ ≠ 0 := fun h => hn₀ (congrArg Subtype.val h)
  obtain ⟨M, hM⟩ := ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal A hA c₀ hc₀ ϖA hϖmem hϖAne
  refine ⟨M, fun m hm => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨d, hd⟩ := hvc_bound_div K ϖ hϖne hres hϖ m y hy hm n₀
  have hdiv : ϖA ^ (M + 1) ∣ c₀ := by
    have hc₀eq : c₀ = ϖA ^ m * ⟨(d : AlgebraicClosure ℚ), d.2.1⟩ := by
      apply Subtype.ext
      push_cast
      exact hd
    rw [hc₀eq]
    exact Dvd.dvd.mul_right (pow_dvd_pow ϖA hlt) _
  have : M + 1 ≤ M := (pow_dvd_pow_iff hϖAne hϖunit).mp (hdiv.trans hM)
  omega

private noncomputable def hvc_pack {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ integralCoeffs A.toSubring) : LaurentSeries A where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (fun _ hn h => hn (Subtype.ext h))

private theorem hvc_coeffMap_pack {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ integralCoeffs A.toSubring) :
    coeffMap A.subtype (hvc_pack x hx) = x := by
  ext n
  rfl

private theorem hvc_integralCoeffs_le (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    integralCoeffs (coeffSubring A K) ≤ integralCoeffs A.toSubring :=
  fun _ hx n => (hx n).1

section HvcGauss

variable {A : ValuationSubring (AlgebraicClosure ℚ)} (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]

private theorem hvc_coeffMap_residue_pack (r : modularRing M (coeffSubring A K)) :
    coeffMap (IsLocalRing.residue A) (hvc_pack (r : LaurentSeries (AlgebraicClosure ℚ))
        (hvc_integralCoeffs_le A K (modularRing_le_integralCoeffs M (coeffSubring A K) r.2))) =
      redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing M (coeffSubring A K))
        (modularRing_le_integralCoeffs M (coeffSubring A K)) r := by
  ext n
  rfl

private theorem hvc_redRes_eq_coeffRed (r : modularRing M (coeffSubring A K)) :
    redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing M (coeffSubring A K))
        (modularRing_le_integralCoeffs M (coeffSubring A K)) r =
      coeffRed A.toSubring (IsLocalRing.residue A)
        ⟨r, hvc_integralCoeffs_le A K (modularRing_le_integralCoeffs M (coeffSubring A K) r.2)⟩ := by
  ext n
  rfl

private theorem hvc_hasPres_zero_of_mem (ϖ : AlgebraicClosure ℚ) {b : LaurentSeries (AlgebraicClosure ℚ)}
    (hb : b ∈ modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) :
    hvc_HasPres (A := A) ϖ 0 b := by
  obtain ⟨r, s, hs, hbs⟩ := id hb
  refine ⟨hvc_pack r (hvc_integralCoeffs_le A K (modularRing_le_integralCoeffs M (coeffSubring A K) r.2)),
    hvc_pack s (hvc_integralCoeffs_le A K (modularRing_le_integralCoeffs M (coeffSubring A K) s.2)), ?_, ?_⟩
  · rw [hvc_coeffMap_residue_pack]
    exact redRes_ne_zero_of_notMem hs
  · rw [hvc_coeffMap_pack, hvc_coeffMap_pack, pow_zero, map_one, one_mul]
    exact hbs

private theorem hvc_hasPres_zero_mul (ϖ : AlgebraicClosure ℚ) {x y : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : hvc_HasPres (A := A) ϖ 0 x) (hy : hvc_HasPres (A := A) ϖ 0 y) : hvc_HasPres (A := A) ϖ 0 (x * y) := by
  obtain ⟨x₁, y₁, h₁, e₁⟩ := hx
  obtain ⟨x₂, y₂, h₂, e₂⟩ := hy
  rw [pow_zero, map_one, one_mul] at e₁ e₂
  refine ⟨x₁ * x₂, y₁ * y₂, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero h₁ h₂
  · rw [map_mul, map_mul, pow_zero, map_one, one_mul]
    linear_combination (y * coeffMap A.subtype y₂) * e₁ + (coeffMap A.subtype x₁) * e₂

private theorem hvc_redLoc_eq_zero_of_eq_mul (ϖ : coeffSubring A K)
    (hres : IsLocalRing.residue A ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0)
    {b : LaurentSeries (AlgebraicClosure ℚ)} (hb : b ∈ modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K))
    {g : LaurentSeries (AlgebraicClosure ℚ)} (hg : hvc_HasPres (A := A) (ϖ : AlgebraicClosure ℚ) 0 g)
    (hbg : b = constSeries (coeffSubring A K) ϖ * g) :
    redLoc (⟨b, hb⟩ : modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = 0 := by
  obtain ⟨r, s, hs, hbs⟩ := id hb
  have hspec := redLoc_spec (⟨b, hb⟩ : modularLocalized M (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) hbs
  have hsne := redRes_ne_zero_of_notMem hs
  suffices hr : redRes (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing M (coeffSubring A K))
      (modularRing_le_integralCoeffs M (coeffSubring A K)) r = 0 by
    rw [hr] at hspec
    exact (mul_eq_zero.mp hspec).resolve_right hsne
  obtain ⟨X, Y, hY, hgY⟩ := hg
  rw [pow_zero, map_one, one_mul] at hgY
  have hrA : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring :=
    hvc_integralCoeffs_le A K (modularRing_le_integralCoeffs M (coeffSubring A K) r.2)
  have hXs : coeffMap A.subtype X * (s : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring :=
    mul_mem (hvc_bound_coeffMap_mem X) (hvc_integralCoeffs_le A K (modularRing_le_integralCoeffs M (coeffSubring A K) s.2))

  have hid : (r : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype Y =
      HahnSeries.C (ϖ : AlgebraicClosure ℚ) * (coeffMap A.subtype X * (s : LaurentSeries (AlgebraicClosure ℚ))) := by
    have hc : constSeries (coeffSubring A K) ϖ = HahnSeries.C (ϖ : AlgebraicClosure ℚ) := hvc_bound_algebraMap_eq_C _
    rw [← hbs, hbg, hc]
    linear_combination (HahnSeries.C (ϖ : AlgebraicClosure ℚ) * (s : LaurentSeries (AlgebraicClosure ℚ))) * hgY

  have hprod := map_mul (coeffRed A.toSubring (IsLocalRing.residue A)) (⟨r, hrA⟩ : integralCoeffs A.toSubring)
    ⟨coeffMap A.subtype Y, hvc_bound_coeffMap_mem Y⟩
  have hzero : coeffRed A.toSubring (IsLocalRing.residue A)
      ((⟨r, hrA⟩ : integralCoeffs A.toSubring) * ⟨coeffMap A.subtype Y, hvc_bound_coeffMap_mem Y⟩) = 0 := by
    have h := hvc_bound_coeffRed_C_mul ϖ.2.1 hres hXs
    rw [← h]
    congr 1
    exact Subtype.ext hid
  have h1 : coeffRed A.toSubring (IsLocalRing.residue A) ⟨r, hrA⟩ * coeffMap (IsLocalRing.residue A) Y = 0 := by
    rw [← hvc_bound_coeffRed_coeffMap]
    exact hprod.symm.trans hzero
  rw [hvc_redRes_eq_coeffRed]
  exact (mul_eq_zero.mp h1).resolve_right hY

end HvcGauss

private theorem hvc_strip {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hdvr : IsDiscreteValuationRing (coeffSubring A K)) (ϖ : coeffSubring A K)
    (hϖ : ∀ c : coeffSubring A K, redRestrict (IsLocalRing.residue A) K c = 0 ↔ ∃ d : coeffSubring A K, c = ϖ * d)
    (hjN : jqNModC (AlgebraicClosure ℚ) N ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K))
    {b : LaurentSeries (AlgebraicClosure ℚ)} (hb : b ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K))
    (hred : redLoc (⟨b, hb⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = 0) :
    ∃ b' ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K),
      b = constSeries (coeffSubring A K) ϖ * b' := by
  obtain ⟨r, s, hs, hbs⟩ := id hb
  have hspec := redLoc_spec (⟨b, hb⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) hbs
  rw [hred, zero_mul] at hspec
  have hr : r ∈ redKer (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) (modularRing (N * q) (coeffSubring A K))
      (modularRing_le_integralCoeffs (N * q) (coeffSubring A K)) := RingHom.mem_ker.mpr hspec.symm
  obtain ⟨b', hb', hrb'⟩ := hvc_kernel hA hqN K hdvr ϖ hϖ hjN r hr
  have hs0 : (s : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply hs
    rw [show s = 0 from Subtype.ext h0]
    exact Ideal.zero_mem _
  have hsinv : (s : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈
      modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) :=
    ⟨1, s, hs, by rw [inv_mul_cancel₀ hs0]; simp⟩
  refine ⟨b' * (s : LaurentSeries (AlgebraicClosure ℚ))⁻¹, mul_mem hb' hsinv, ?_⟩
  rw [show b = (r : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ))⁻¹ by
    rw [← hbs, mul_inv_cancel_right₀ hs0], hrb']
  ring

private theorem hvc_mem_of_fraction {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hdvr : IsDiscreteValuationRing (coeffSubring A K)) (ϖ : coeffSubring A K)
    (hϖ0 : redRestrict (IsLocalRing.residue A) K ϖ = 0) (hϖne : (ϖ : AlgebraicClosure ℚ) ≠ 0)
    (hϖ : ∀ c : coeffSubring A K, redRestrict (IsLocalRing.residue A) K c = 0 ↔ ∃ d : coeffSubring A K, c = ϖ * d)
    (hjN : jqNModC (AlgebraicClosure ℚ) N ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K))
    {f : LaurentSeries (AlgebraicClosure ℚ)} (hf : hvc_HasPres (A := A) (ϖ : AlgebraicClosure ℚ) 0 f)
    (P Q : modularRing (N * q) (coeffSubring A K)) (hQ : (Q : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0)
    (hfQ : f * (Q : LaurentSeries (AlgebraicClosure ℚ)) = P) :
    f ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := by
  have hres : IsLocalRing.residue A ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0 := hϖ0
  have hc : constSeries (coeffSubring A K) ϖ = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ) := rfl
  have hϖc0 : constSeries (coeffSubring A K) ϖ ≠ 0 := by
    rw [hc]
    exact (map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective).mpr hϖne
  by_cases hP0 : (P : LaurentSeries (AlgebraicClosure ℚ)) = 0
  · have hf0 : f = 0 := by
      have h0 : f * (Q : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [hfQ, hP0]
      exact (mul_eq_zero.mp h0).resolve_right hQ
    rw [hf0]
    exact zero_mem _
  obtain ⟨Bd, hBd⟩ := hvc_bound hA K ϖ hϖ0 hϖne hϖ (modularRing_le_integralCoeffs (N * q) (coeffSubring A K) P.2) hP0

  have main : ∀ n i : ℕ, Bd + 1 ≤ i + n → ∀ bP bQ : LaurentSeries (AlgebraicClosure ℚ), bP ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) → bQ ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) →
      (P : LaurentSeries (AlgebraicClosure ℚ)) = constSeries (coeffSubring A K) ϖ ^ i * bP →
      (Q : LaurentSeries (AlgebraicClosure ℚ)) = constSeries (coeffSubring A K) ϖ ^ i * bQ → f ∈ modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K) := by
    intro n
    induction n with
    | zero =>
        intro i hi bP _ hbP _ hP _
        exfalso
        have hpres : hvc_HasPres (A := A) (ϖ : AlgebraicClosure ℚ) i P := by
          obtain ⟨X, Y, hY, hXY⟩ := hvc_hasPres_zero_of_mem K (N * q) (ϖ : AlgebraicClosure ℚ) hbP
          rw [pow_zero, map_one, one_mul] at hXY
          refine ⟨X, Y, hY, ?_⟩
          rw [hP, map_pow, ← hc, mul_assoc, hXY]
        have := hBd i hpres
        omega
    | succ n ih =>
        intro i hi bP bQ hbP hbQ hP hQ'
        have hbQ0 : bQ ≠ 0 := by
          rintro rfl
          apply hQ
          rw [hQ', mul_zero]
        have hfb : f * bQ = bP := by
          have h := hfQ
          rw [hP, hQ'] at h
          apply mul_left_cancel₀ (pow_ne_zero i hϖc0)
          linear_combination h
        by_cases hred : redLoc (⟨bQ, hbQ⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = 0
        · obtain ⟨bQ', hbQ', hbQeq⟩ := hvc_strip hA hqN K hdvr ϖ hϖ hjN hbQ hred
          have hbPeq : bP = constSeries (coeffSubring A K) ϖ * (f * bQ') := by
            rw [← hfb, hbQeq]
            ring
          have hredP : redLoc (⟨bP, hbP⟩ : modularLocalized (N * q) (coeffSubring A K) (redRestrict (IsLocalRing.residue A) K)) = 0 :=
            hvc_redLoc_eq_zero_of_eq_mul K (N * q) ϖ hres hbP
              (hvc_hasPres_zero_mul (ϖ : AlgebraicClosure ℚ) hf (hvc_hasPres_zero_of_mem K (N * q) (ϖ : AlgebraicClosure ℚ) hbQ')) hbPeq
          obtain ⟨bP', hbP', hbPeq'⟩ := hvc_strip hA hqN K hdvr ϖ hϖ hjN hbP hredP
          refine ih (i + 1) (by omega) bP' bQ' hbP' hbQ' ?_ ?_
          · rw [hP, hbPeq', pow_succ]
            ring
          · rw [hQ', hbQeq, pow_succ]
            ring
        · have hinv := hvc_inv_mem K (N * q) hbQ hred
          have hfeq : f = bP * bQ⁻¹ := by
            rw [← hfb, mul_inv_cancel_right₀ hbQ0]
          rw [hfeq]
          exact mul_mem hbP hinv
  exact main (Bd + 1) 0 (by omega) P Q (subring_le_localizedAtKer _ _ _ _ P.2) (subring_le_localizedAtKer _ _ _ _ Q.2)
    (by rw [pow_zero, one_mul]) (by rw [pow_zero, one_mul])

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (f : ↥(modularFunctionFieldBar (N * q))) :
    (∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y
          = ModularCurve.coeffMap A.subtype x) →
      (f : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring (IsLocalRing.residue A) := by
  intro hf
  obtain ⟨K₁, hK₁, hf₁⟩ := hvc_exists_fieldOver (N * q) f
  obtain ⟨r, s, hs, hjs⟩ := id (ModularCurve.jqNModC_mem_modularLocalized_mul_of_not_dvd hA hqN)
  obtain ⟨K₂, hK₂, hr₂⟩ := hvc_exists_mem_modularRing_coeffSubring (N * q) A r
  obtain ⟨K₃, hK₃, hs₃⟩ := hvc_exists_mem_modularRing_coeffSubring (N * q) A s
  haveI := hK₁
  haveI := hK₂
  haveI := hK₃

  have hle₁ : K₁ ≤ K₁ ⊔ K₂ ⊔ K₃ := le_sup_left.trans le_sup_left
  have hle₂ : K₂ ≤ K₁ ⊔ K₂ ⊔ K₃ := le_sup_right.trans le_sup_left
  have hle₃ : K₃ ≤ K₁ ⊔ K₂ ⊔ K₃ := le_sup_right
  have hf' : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) (K₁ ⊔ K₂ ⊔ K₃) := hvc_fieldOver_mono (N * q) hle₁ hf₁
  have hjN : jqNModC (AlgebraicClosure ℚ) N ∈ modularLocalized (N * q) (coeffSubring A (K₁ ⊔ K₂ ⊔ K₃))
      (redRestrict (IsLocalRing.residue A) (K₁ ⊔ K₂ ⊔ K₃)) :=
    hvc_mem_modularLocalized_coeffSubring (N * q) A (K₁ ⊔ K₂ ⊔ K₃) r s hs hjs
      (hvc_modularRing_mono (N * q) A hle₂ hr₂) (hvc_modularRing_mono (N * q) A hle₃ hs₃)
  obtain ⟨hdvr, ϖ, hϖ0, hϖne, hϖ⟩ := hvc_exists_uniformizer hA (K₁ ⊔ K₂ ⊔ K₃)
  obtain ⟨P, Q, hQ, hfQ⟩ := hvc_exists_fraction (N * q) A (K₁ ⊔ K₂ ⊔ K₃) hf'
  have hfV : hvc_HasPres (A := A) (ϖ : AlgebraicClosure ℚ) 0 (f : LaurentSeries (AlgebraicClosure ℚ)) := by
    obtain ⟨x, y, hy, hxy⟩ := hf
    exact ⟨x, y, hy, by rw [pow_zero, map_one, one_mul]; exact hxy⟩
  exact hvc_modularLocalized_le (N * q) A (K₁ ⊔ K₂ ⊔ K₃)
    (hvc_mem_of_fraction hA hqN (K₁ ⊔ K₂ ⊔ K₃) hdvr ϖ hϖ0 hϖne hϖ hjN hfV P Q hQ hfQ)

end S_ModularCurve_mem_modularLocalized_mul_of_not_dvd_of_exists_coeffMap_mul_eq
end P2MW
export P2MW.S_ModularCurve_mem_modularLocalized_mul_of_not_dvd_of_exists_coeffMap_mul_eq (solution)
