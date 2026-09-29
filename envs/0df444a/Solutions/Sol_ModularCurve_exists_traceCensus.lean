-- Prove2me | solution 1 for ModularCurve.exists_traceCensus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4727a6b0-44a5-548c-9c94-e5717d3d42f3

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
import Theorems.Thm_ModularCurve_coeffMap_injective
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_full_eq_adjoin_full_div_prime
import Theorems.Thm_ModularCurve_exists_phiIrreducible
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_qExpand_mem_laurentBaseChange
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_traceCensus
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full P2MW.S_ModularCurve_exists_traceCensus.ModularCurve ModularCurve.PhiGen"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full full_degeneracy_map_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqNModC map_jqModC heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot dedekindPsi_prime dedekindPsi_pos dedekindPsi_mul_of_coprime finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full minpoly_jqN_map_eq_prod_slots full_eq_adjoin_full_div_prime exists_phiIrreducible relfinrank_laurentBaseChange relfinrank_full_eq_dedekindPsi transcendental_jq laurentBaseChange_adjoin_pair qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full"

variable {K : Type*} [Field K] [Algebra ℚ K]

def TS (K : Type*) [Field K] [Algebra ℚ K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K :=
  qExpand K e (qTwist u (coeffEmb K jq))

theorem TS_coeff_mul (e : ℕ) [NeZero e] (u : Kˣ) (n : ℤ) :
    (TS K e u).coeff ((e : ℤ) * n) = ((u ^ n : Kˣ) : K) * algebraMap ℚ K (jq.coeff n) := by
  rw [TS, qExpand_coeff_mul, qTwist_coeff, coeffEmb_coeff]

theorem TS_coeff_of_not_dvd (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : ¬ (e : ℤ) ∣ k) :
    (TS K e u).coeff k = 0 := by
  exact qExpand_coeff_of_not_dvd (R := K) (N := e) _ hk

theorem TS_coeff_neg (e : ℕ) [NeZero e] (u : Kˣ) : (TS K e u).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := TS_coeff_mul (K := K) e u (-1)
  rw [mul_neg_one] at h
  rw [h, coeff_jq_neg_one, map_one, mul_one, zpow_neg_one]

theorem TS_coeff_of_lt (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : k < -(e : ℤ)) : (TS K e u).coeff k = 0 := by
  by_cases hd : (e : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hd
    have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
    have hn : n < -1 := by
      by_contra hcon
      push Not at hcon
      have : -(e : ℤ) ≤ (e : ℤ) * n := by nlinarith
      exact absurd hk (not_lt.mpr this)
    rw [TS_coeff_mul, coeff_jq_of_lt hn, map_zero, mul_zero]
  · exact TS_coeff_of_not_dvd e u hd

theorem TS_ne_zero (e : ℕ) [NeZero e] (u : Kˣ) : TS K e u ≠ 0 := by
  intro h
  have := TS_coeff_neg (K := K) e u
  rw [h, HahnSeries.coeff_zero] at this
  exact (u⁻¹).ne_zero this.symm

theorem TS_injective {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ} (h : TS K e u = TS K e' u') :
    e = e' ∧ u = u' := by
  have key : ∀ {a a' : ℕ} [NeZero a] [NeZero a'] {v v' : Kˣ}, TS K a v = TS K a' v' → a ≤ a' := by
    intro a a' _ _ v v' hh
    by_contra hlt
    push Not at hlt
    have h1 := TS_coeff_neg (K := K) a v
    have hlt' : (-(a : ℤ)) < -(a' : ℤ) := by
      have : (a' : ℤ) < a := by exact_mod_cast hlt
      omega
    have h2 : (TS K a' v').coeff (-(a : ℤ)) = 0 := TS_coeff_of_lt a' v' hlt'
    rw [← hh, h1] at h2
    exact (v⁻¹).ne_zero h2
  have hee : e = e' := le_antisymm (key h) (key h.symm)
  subst hee
  refine ⟨rfl, ?_⟩
  have h1 := TS_coeff_neg (K := K) e u
  rw [h, TS_coeff_neg] at h1
  exact (inv_injective (Units.val_injective h1)).symm

theorem qTwist_TS (v : Kˣ) (e : ℕ) [NeZero e] (u : Kˣ) : qTwist v (TS K e u) = TS K e (v ^ (e : ℤ) * u) := by
  rw [TS, qTwist_qExpand, qTwist_qTwist]; rfl

theorem qExpand_TS (m e : ℕ) [NeZero m] [NeZero e] (u : Kˣ) : qExpand K m (TS K e u) = TS K (m * e) u := by
  rw [TS, qExpand_qExpand]; rfl

theorem TS_congr {e e' : ℕ} [NeZero e] [NeZero e'] (h : e = e') (u : Kˣ) : TS K e u = TS K e' u := by
  subst h; rfl

theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb K (qExpand ℚ n x) = qExpand K n (coeffEmb K x) :=
  coeffMap_qExpand (algebraMap ℚ K) n x

theorem iota_jqN (N d : ℕ) [NeZero N] [NeZero d] :
    coeffEmb K (qExpand ℚ N (jqN d)) = TS K (N * d) 1 := by
  rw [jqN, coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand, TS, qTwist_one_apply]

theorem iota_jq (N : ℕ) [NeZero N] : coeffEmb K (qExpand ℚ N jq) = TS K N 1 := by
  rw [coeffEmb_qExpand, TS, qTwist_one_apply]

theorem conj_zero_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) : conj p ζ (0 : Fin (p + 1)) = TS K (p * p) 1 := by
  rw [conj_zero, TS, qTwist_one_apply]

theorem conj_succ_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (b : Fin p) : conj p ζ b.succ = TS K 1 (ζ ^ (b : ℕ)) := by
  rw [conj_succ, TS, qExpand_one_apply]

theorem qTwist_iota_of_pow_eq_one (N : ℕ) [NeZero N] (v : Kˣ) (hv : v ^ N = 1) (x : LaurentSeries ℚ) :
    qTwist v (coeffEmb K (qExpand ℚ N x)) = coeffEmb K (qExpand ℚ N x) := by
  rw [coeffEmb_qExpand, qTwist_qExpand]
  have : v ^ (N : ℤ) = 1 := by exact_mod_cast hv
  rw [this, qTwist_one_apply]

end ModularCurve.W1

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full full_degeneracy_map_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqNModC map_jqModC heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot dedekindPsi_prime dedekindPsi_pos dedekindPsi_mul_of_coprime finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full minpoly_jqN_map_eq_prod_slots full_eq_adjoin_full_div_prime exists_phiIrreducible relfinrank_laurentBaseChange relfinrank_full_eq_dedekindPsi transcendental_jq laurentBaseChange_adjoin_pair qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full"

variable {K : Type*} [Field K] [Algebra ℚ K]

def qTwistEquiv (u : Kˣ) : LaurentSeries K ≃+* LaurentSeries K where
  toFun := qTwist u
  invFun := qTwist u⁻¹
  left_inv := fun f => by
    show qTwist u⁻¹ (qTwist u f) = f
    rw [qTwist_qTwist, inv_mul_cancel, qTwist_one_apply]
  right_inv := fun f => by
    show qTwist u (qTwist u⁻¹ f) = f
    rw [qTwist_qTwist, mul_inv_cancel, qTwist_one_apply]
  map_mul' := map_mul _
  map_add' := map_add _

omit [Algebra ℚ K] in
@[scoped simp] theorem qTwistEquiv_apply (u : Kˣ) (f : LaurentSeries K) : qTwistEquiv u f = qTwist u f := rfl

omit [Algebra ℚ K] in
theorem coe_qTwistEquiv (u : Kˣ) : ((qTwistEquiv u : LaurentSeries K ≃+* LaurentSeries K) : LaurentSeries K →+* LaurentSeries K) = qTwist u :=
  RingHom.ext fun _ => rfl

theorem qTwist_TS_one_cycle (ζ : Kˣ) {p : ℕ} (hζp : ζ ^ p = 1) (b : ℕ) :
    qTwist ζ (TS K 1 (ζ ^ b)) = TS K 1 (ζ ^ ((b + 1) % p)) := by
  rw [qTwist_TS]
  congr 1
  have : ζ ^ ((1 : ℕ) : ℤ) * ζ ^ b = ζ ^ (b + 1) := by rw [zpow_natCast, pow_one, pow_succ']
  rw [this]
  conv_lhs => rw [← Nat.mod_add_div (b + 1) p, pow_add, pow_mul, hζp, one_pow, mul_one]

theorem phiProd_conj_eq (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    phiProd p (conj p ζ) = (Polynomial.X - Polynomial.C (TS K (p * p) 1)) *
      ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) := by
  rw [phiProd, Fin.prod_univ_succ, conj_zero_eq]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun b => Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) p]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [conj_succ_eq]

theorem roots_phiProd_conj (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    (phiProd p (conj p ζ)).roots = TS K (p * p) 1 ::ₘ (Multiset.range p).map (fun b => TS K 1 (ζ ^ b)) := by
  classical
  rw [phiProd_conj_eq]
  have h1 : (Polynomial.X - Polynomial.C (TS K (p * p) 1) : Polynomial (LaurentSeries K)) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have h2 : (∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b _ => Polynomial.X_sub_C_ne_zero _
  rw [Polynomial.roots_mul (mul_ne_zero h1 h2), Polynomial.roots_X_sub_C, Finset.prod_eq_multiset_prod,
    Finset.range_val]
  have hm : (Multiset.map (fun b => Polynomial.X - Polynomial.C (TS K 1 (ζ ^ b))) (Multiset.range p)) =
      ((Multiset.range p).map (fun b => TS K 1 (ζ ^ b))).map (fun a => Polynomial.X - Polynomial.C a) := by
    rw [Multiset.map_map]; rfl
  rw [hm, Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

theorem roots_phiProd_conj_nodup (p : ℕ) [hp : Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    (TS K (p * p) 1 ::ₘ (Multiset.range p).map (fun b => TS K 1 (ζ ^ b))).Nodup := by
  refine Multiset.nodup_cons.mpr ⟨?_, ?_⟩
  · intro hmem
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hmem
    have := (TS_injective hb).1
    have h2 := hp.out.two_le
    nlinarith
  · refine (Multiset.nodup_range p).map_on fun b hb b' hb' hbb' => ?_
    rw [Multiset.mem_range] at hb hb'
    have hu := (TS_injective hbb').2
    have hζu : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.mp hζ
    exact hζu.pow_inj hb hb' hu

theorem exists_isPrimitiveRoot_cyclotomicField (N : ℕ) [NeZero N] :
    ∃ z : CyclotomicField N ℚ, IsPrimitiveRoot z N := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  exact IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ) (Set.mem_singleton N) (NeZero.ne N)

def cycUnit (N : ℕ) [NeZero N] : (CyclotomicField N ℚ)ˣ :=
  ((exists_isPrimitiveRoot_cyclotomicField N).choose_spec.isUnit (NeZero.ne N)).unit

theorem cycUnit_spec (N : ℕ) [NeZero N] :
    IsPrimitiveRoot ((cycUnit N : (CyclotomicField N ℚ)ˣ) : CyclotomicField N ℚ) N := by
  rw [cycUnit, IsUnit.unit_spec]
  exact (exists_isPrimitiveRoot_cyclotomicField N).choose_spec

theorem cycUnit_pow (N : ℕ) [NeZero N] : cycUnit N ^ N = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, (cycUnit_spec N).pow_eq_one, Units.val_one])

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full full_degeneracy_map_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqNModC map_jqModC heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot dedekindPsi_prime dedekindPsi_pos dedekindPsi_mul_of_coprime finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full minpoly_jqN_map_eq_prod_slots full_eq_adjoin_full_div_prime exists_phiIrreducible relfinrank_laurentBaseChange relfinrank_full_eq_dedekindPsi transcendental_jq laurentBaseChange_adjoin_pair qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full"

variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in

theorem isPrimitiveRoot_pow_div {N : ℕ} [NeZero N] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N)
    {p : ℕ} (hpN : p ∣ N) : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := by
  have hN : N ≠ 0 := NeZero.ne N
  have hd0 : N / p ≠ 0 := by
    intro h0
    have hc := Nat.div_mul_cancel hpN
    rw [h0, zero_mul] at hc
    exact hN hc.symm
  have h := hζ.pow_of_dvd hd0 (Nat.div_dvd_of_dvd hpN)
  rw [Nat.div_div_self hpN hN] at h
  rwa [← Units.val_pow_eq_pow_val] at h

theorem qExpand_qTwist_TS (e : ℕ) [NeZero e] (u : Kˣ) (m : ℕ) [NeZero m] (w : Kˣ) :
    qExpand K e (qTwist u (TS K m w)) = TS K (e * m) (u ^ (m : ℤ) * w) := by
  rw [qTwist_TS, qExpand_TS]

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full full_degeneracy_map_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqNModC map_jqModC heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot dedekindPsi_prime dedekindPsi_pos dedekindPsi_mul_of_coprime finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full minpoly_jqN_map_eq_prod_slots full_eq_adjoin_full_div_prime exists_phiIrreducible relfinrank_laurentBaseChange relfinrank_full_eq_dedekindPsi transcendental_jq laurentBaseChange_adjoin_pair qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full"

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem prod_form_ne_zero (N : ℕ) (ζ : Kˣ) (p : ℕ) [NeZero p] (e : ℕ) [NeZero e]
    (u : Kˣ) :
    (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)))) *
        ∏ b ∈ Finset.range p,
          (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))) ≠ 0 :=
  mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero

theorem roots_prime_at_slot (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq))))).roots
      = (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq))) ::ₘ
          (Multiset.range p).map
            (fun b => qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq))) := by
  rw [ModularCurve.PhiGen.splits_prime_at_slot N ζ hζ p hpN data e u,
    Polynomial.roots_mul (prod_form_ne_zero N ζ p e u), Polynomial.roots_X_sub_C,
    Finset.prod_eq_multiset_prod, Finset.range_val,
    show (Multiset.range p).map
          (fun b => Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq))))
        = ((Multiset.range p).map
            (fun b => qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))).map
            (fun a => Polynomial.X - Polynomial.C a) from
      (Multiset.map_map (fun a => Polynomial.X - Polynomial.C a)
        (fun b => qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))
        (Multiset.range p)).symm,
    Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

theorem roots_prime_at_slot_nodup (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (e : ℕ) [NeZero e] (u : Kˣ) :
    ((qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq))) ::ₘ
        (Multiset.range p).map
          (fun b => qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)))).Nodup := by
  have hζp : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := isPrimitiveRoot_pow_div hζ hpN
  rw [Multiset.nodup_cons]
  constructor
  ·
    intro hmem
    obtain ⟨b, hb, heq⟩ := Multiset.mem_map.mp hmem
    have h := (TS_injective (K := K) (e := e) (e' := p * (p * e))
      (u := u * ζ ^ (b * (N / p))) (u' := u ^ (p * p)) heq).1
    have hp2 : 2 ≤ p := hp.out.two_le
    have he1 : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
    have hmono : 2 * (2 * e) ≤ p * (p * e) := Nat.mul_le_mul hp2 (Nat.mul_le_mul hp2 le_rfl)
    rw [← h] at hmono
    omega
  ·
    refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range p)
    intro b hb b' hb' heq
    rw [Multiset.mem_range] at hb hb'
    have h := (TS_injective (K := K) (e := e) (e' := e)
      (u := u * ζ ^ (b * (N / p))) (u' := u * ζ ^ (b' * (N / p))) heq).2
    have h2 : ζ ^ (b * (N / p)) = ζ ^ (b' * (N / p)) := mul_left_cancel h
    have h3 : (ζ ^ (N / p)) ^ b = (ζ ^ (N / p)) ^ b' := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (N / p) b, Nat.mul_comm (N / p) b']
      exact h2
    have h4 : ((ζ ^ (N / p) : Kˣ) : K) ^ b = ((ζ ^ (N / p) : Kˣ) : K) ^ b' := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h3]
    exact hζp.pow_inj hb hb' h4

theorem roots_prime_at_slot_roots_nodup (N : ℕ) [NeZero N] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) N) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq))))).roots.Nodup := by
  rw [roots_prime_at_slot N ζ hζ p hpN data e u]
  exact roots_prime_at_slot_nodup N ζ hζ p hpN e u

theorem isRoot_prime_at_slot_iff (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpN : p ∣ N) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) (y : LaurentSeries K) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq))))).IsRoot y ↔
      y = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (coeffEmb K jq)) ∨
        ∃ b < p, y = qExpand K e (qTwist (u * ζ ^ (b * (N / p))) (coeffEmb K jq)) := by
  have hne : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (coeffEmb K jq)))) ≠ 0 := by
    rw [ModularCurve.PhiGen.splits_prime_at_slot N ζ hζ p hpN data e u]
    exact prod_form_ne_zero N ζ p e u
  rw [← Polynomial.mem_roots hne, roots_prime_at_slot N ζ hζ p hpN data e u,
    Multiset.mem_cons, Multiset.mem_map]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mp hb, rfl⟩
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mpr hb, rfl⟩

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full full_degeneracy_map_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqNModC map_jqModC heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot dedekindPsi_prime dedekindPsi_pos dedekindPsi_mul_of_coprime finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full minpoly_jqN_map_eq_prod_slots full_eq_adjoin_full_div_prime exists_phiIrreducible relfinrank_laurentBaseChange relfinrank_full_eq_dedekindPsi transcendental_jq laurentBaseChange_adjoin_pair qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full"

def phiAtSeed {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (data : ModularPolynomialData n) (x : R) :
    Polynomial R :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)

theorem phiAtSeed_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) (f : R →+* S) :
    (phiAtSeed data x).map f = phiAtSeed data (f x) := by
  rw [phiAtSeed, phiAtSeed, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp

theorem phiAtSeed_monic {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).Monic :=
  data.monic.map _

theorem phiAtSeed_natDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x : R) : (phiAtSeed data x).natDegree = dedekindPsi n := by
  rw [phiAtSeed, data.monic.natDegree_map, data.natDegree_eq]

theorem phiAtSeed_jq_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) :
    (phiAtSeed data jq).eval (jqN n) = 0 := by
  have h := data.eval_eq_zero
  rw [phiAtSeed, Polynomial.eval_map]
  convert h using 2 <;> try rfl
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evalAtJ_X]

theorem phiAtSeed_eval_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} [NeZero n]
    (data : ModularPolynomialData n) (x y : R) (f : R →+* S) (h : (phiAtSeed data x).eval y = 0) :
    (phiAtSeed data (f x)).eval (f y) = 0 := by
  rw [← phiAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom, h, map_zero]

theorem phiAtSeed_jqN_eval (n : ℕ) [NeZero n] (data : ModularPolynomialData n) (M : ℕ) [NeZero M] :
    (phiAtSeed data (jqN M)).eval (jqN (M * n)) = 0 := by
  have h := phiAtSeed_eval_map data jq (jqN n) (qExpand ℚ M) (phiAtSeed_jq_eval n data)
  rwa [jqN, qExpand_qExpand] at h

theorem phiAtSeed_iota_eval {K : Type*} [Field K] [Algebra ℚ K] (A : ℕ) [NeZero A] (n : ℕ) [NeZero n]
    (data : ModularPolynomialData n) (M : ℕ) [NeZero M] :
    (phiAtSeed data (coeffEmb K (qExpand ℚ A (jqN M)))).eval (coeffEmb K (qExpand ℚ A (jqN (M * n)))) = 0 :=
  phiAtSeed_eval_map data _ _ ((coeffEmb K).comp (qExpand ℚ A)) (phiAtSeed_jqN_eval n data M)

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full full_degeneracy_map_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqNModC map_jqModC heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot dedekindPsi_prime dedekindPsi_pos dedekindPsi_mul_of_coprime finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full minpoly_jqN_map_eq_prod_slots full_eq_adjoin_full_div_prime exists_phiIrreducible relfinrank_laurentBaseChange relfinrank_full_eq_dedekindPsi transcendental_jq laurentBaseChange_adjoin_pair qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full"

private theorem jqN_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) : jqN n = jqN m := by
  subst h; rfl

private theorem full_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    modularFunctionFieldFull n = modularFunctionFieldFull m := by
  subst h; rfl

private theorem hallAll (M : ℕ) [NeZero M] : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
      ∧ modularFunctionField d = modularFunctionFieldFull d := by
  intro d _ _
  exact ⟨ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi d,
    ModularCurve.modularFunctionField_eq_full d⟩

private theorem jq_mem_full (M : ℕ) [NeZero M] : jq ∈ modularFunctionFieldFull M :=
  modularFunctionField_le_full M (jq_mem M)

private theorem adjoin_simple_algHom_ext {F₀ L T : Type*} [Field F₀] [Field L] [Field T]
    [Algebra F₀ L] [Algebra F₀ T] {x : L}
    {σ₁ σ₂ : (IntermediateField.adjoin F₀ ({x} : Set L)) →ₐ[F₀] T}
    (h : σ₁ (IntermediateField.AdjoinSimple.gen F₀ x)
      = σ₂ (IntermediateField.AdjoinSimple.gen F₀ x)) : σ₁ = σ₂ := by
  apply AlgHom.ext
  rintro ⟨v, hv⟩
  induction hv using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact h
  | algebraMap f =>
    have h₁ : (⟨algebraMap F₀ L f, by exact IntermediateField.algebraMap_mem _ f⟩ :
        IntermediateField.adjoin F₀ ({x} : Set L))
        = algebraMap F₀ (IntermediateField.adjoin F₀ ({x} : Set L)) f := rfl
    rw [h₁, AlgHom.commutes, AlgHom.commutes]
  | add w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
    have h₁ : (⟨w₁ + w₂, by exact add_mem hw₁ hw₂⟩ :
        IntermediateField.adjoin F₀ ({x} : Set L))
        = ⟨w₁, hw₁⟩ + ⟨w₂, hw₂⟩ := rfl
    rw [h₁, map_add, map_add, ih₁, ih₂]
  | inv w hw ih =>
    have h₁ : (⟨w⁻¹, by exact inv_mem hw⟩ :
        IntermediateField.adjoin F₀ ({x} : Set L)) = (⟨w, hw⟩)⁻¹ := rfl
    rw [h₁, map_inv₀, map_inv₀, ih]
  | mul w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
    have h₁ : (⟨w₁ * w₂, by exact mul_mem hw₁ hw₂⟩ :
        IntermediateField.adjoin F₀ ({x} : Set L))
        = ⟨w₁, hw₁⟩ * ⟨w₂, hw₂⟩ := rfl
    rw [h₁, map_mul, map_mul, ih₁, ih₂]

private theorem phiAtSeed_eval_of_injective {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    [NeZero n] (data : ModularPolynomialData n) (x y : R) (f : R →+* S)
    (hf : Function.Injective f) (h : (phiAtSeed data (f x)).eval (f y) = 0) :
    (phiAtSeed data x).eval y = 0 := by
  rw [← phiAtSeed_map, Polynomial.eval_map, Polynomial.eval₂_hom] at h
  exact (injective_iff_map_eq_zero f).mp hf _ h

section BarSetup

variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem jqModC_eq_coeffEmb : jqModC L = coeffEmb L jq :=
  (map_jqModC (algebraMap ℚ L)).symm

omit [Algebra ℚ L] in

private theorem qExpand_algebraMap' (n : ℕ) [NeZero n] (c : L) :
    qExpand L n (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) c := by
  rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

private theorem full_mul_eq_adjoin (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)]
    (hN : ¬ ℓ ∣ N) :
    modularFunctionFieldFull (N * ℓ) = IntermediateField.adjoin ℚ
      (insert (jqN ℓ) (modularFunctionFieldFull N : Set (LaurentSeries ℚ))) := by
  have h := ModularCurve.full_eq_adjoin_full_div_prime N ℓ 0 hN
  rw [full_congr (show N * ℓ ^ (0 + 1) = N * ℓ by norm_num),
    full_congr (show N * ℓ ^ 0 = N by norm_num),
    jqN_congr (show ℓ ^ (0 + 1) = ℓ by norm_num)] at h
  exact h

private theorem ffgAll (M : ℕ) [NeZero M] : FunctionFieldGeneration M := by
  intro d hd hne
  show qExpand ℚ d jq ∈ modularFunctionField M
  rw [ModularCurve.modularFunctionField_eq_full M]
  exact jqd_mem_full M hd

variable (L) in

private theorem bar_extendScalars_eq_adjoin (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)]
    (hN : ¬ ℓ ∣ N)
    (hle : laurentBaseChange L (modularFunctionFieldFull N)
      ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
    IntermediateField.extendScalars hle
      = IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
      (IntermediateField.mem_extendScalars hle).mp hx
    clear hx
    rw [laurentBaseChange] at hx'
    induction hx' using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [full_mul_eq_adjoin N ℓ hN] at hy
      induction hy using IntermediateField.adjoin_induction with
      | mem z hz =>
        rcases hz with rfl | hz
        · exact IntermediateField.subset_adjoin _ _ rfl
        · exact (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
            ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))).algebraMap_mem
            ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L hz⟩
      | algebraMap q =>
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) q, map_ratCast]
        exact SubfieldClass.ratCast_mem _ q
      | add z₁ z₂ _ _ ih₁ ih₂ => rw [map_add]; exact add_mem ih₁ ih₂
      | inv z _ ih => rw [map_inv₀]; exact inv_mem ih
      | mul z₁ z₂ _ _ ih₁ ih₂ => rw [map_mul]; exact mul_mem ih₁ ih₂
    | algebraMap c =>
      exact (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
        ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))).algebraMap_mem
        ⟨algebraMap L (LaurentSeries L) c,
          (laurentBaseChange L (modularFunctionFieldFull N)).algebraMap_mem c⟩
    | add w₁ w₂ _ _ ih₁ ih₂ => exact add_mem ih₁ ih₂
    | inv w _ ih => exact inv_mem ih
    | mul w₁ w₂ _ _ ih₁ ih₂ => exact mul_mem ih₁ ih₂
  · rw [IntermediateField.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (IntermediateField.mem_extendScalars hle).mpr
      (coeffEmb_mem_laurentBaseChange L (jqd_mem_full (N * ℓ) (dvd_mul_left ℓ N)))

variable (L) in

private theorem bar_finrank_adjoin_gen (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)]
    (hN : ¬ ℓ ∣ N)
    (hle : laurentBaseChange L (modularFunctionFieldFull N)
      ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
    Module.finrank (laurentBaseChange L (modularFunctionFieldFull N))
      (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
        ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) = ℓ + 1 := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hA_le_B : IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))
      ≤ laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact coeffEmb_mem_laurentBaseChange L (jq_mem_full N)
  have hAB : IntermediateField.relfinrank
      (IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)))
      (laurentBaseChange L (modularFunctionFieldFull N)) = dedekindPsi N := by
    rw [ModularCurve.relfinrank_laurentBaseChange L (modularFunctionFieldFull N) jq
      (jq_mem_full N) ModularCurve.transcendental_jq]
    exact ModularCurve.relfinrank_full_eq_dedekindPsi N
  have hAC : IntermediateField.relfinrank
      (IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) = dedekindPsi N * (ℓ + 1) := by
    rw [ModularCurve.relfinrank_laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) jq
      (jq_mem_full (N * ℓ)) ModularCurve.transcendental_jq,
      ModularCurve.relfinrank_full_eq_dedekindPsi (N * ℓ),
      ModularCurve.dedekindPsi_mul_of_coprime N ℓ
        ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr hN).symm,
      ModularCurve.dedekindPsi_prime hl.out]
  have hchain := IntermediateField.relfinrank_mul_relfinrank hA_le_B hle
  rw [hAB, hAC] at hchain
  have hBC : IntermediateField.relfinrank
      (laurentBaseChange L (modularFunctionFieldFull N))
      (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) = ℓ + 1 :=
    Nat.eq_of_mul_eq_mul_left (ModularCurve.dedekindPsi_pos N (NeZero.ne N)) hchain
  rw [← bar_extendScalars_eq_adjoin L N ℓ hN hle,
    ← IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact hBC

end BarSetup
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full full_degeneracy_map_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqNModC map_jqModC heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot dedekindPsi_prime dedekindPsi_pos dedekindPsi_mul_of_coprime finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full minpoly_jqN_map_eq_prod_slots full_eq_adjoin_full_div_prime exists_phiIrreducible relfinrank_laurentBaseChange relfinrank_full_eq_dedekindPsi transcendental_jq laurentBaseChange_adjoin_pair qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full"

private theorem bigEmb_coeffEmb {L K' : Type*} [Field L] [Algebra ℚ L] [Field K']
    [Algebra ℚ K'] [Algebra L K'] [IsScalarTower ℚ L K'] (x : LaurentSeries ℚ) :
    coeffMap (algebraMap L K') (coeffEmb L x) = coeffEmb K' x := by
  show coeffMap (algebraMap L K') (coeffMap (algebraMap ℚ L) x) = _
  rw [coeffMap_coeffMap, ← IsScalarTower.algebraMap_eq]
  rfl

private theorem coeffMap_self_apply {L : Type*} [Field L] [Algebra ℚ L] (x : LaurentSeries L) :
    coeffMap (algebraMap L L) x = x := by
  ext k
  rw [coeffMap_coeff, Algebra.algebraMap_self, RingHom.id_apply]

private theorem coeffMap_algebraMap {L K' : Type*} [Field L] [Field K'] [Algebra L K'] (c : L) :
    coeffMap (algebraMap L K') (algebraMap L (LaurentSeries L) c)
      = algebraMap K' (LaurentSeries K') (algebraMap L K' c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]

private theorem aeval_intermediateField_eq_zero {F₀ L : Type*} [Field F₀] [Field L]
    [Algebra F₀ L] {E : IntermediateField F₀ L} {P : Polynomial F₀} {x : E}
    (h : Polynomial.aeval (E.val x) P = 0) : Polynomial.aeval x P = 0 := by
  have h1 := Polynomial.aeval_algHom_apply E.val x P
  rw [h] at h1
  have h2 : E.val (Polynomial.aeval x P) = E.val 0 := by rw [← h1, map_zero]
  exact RingHom.injective (E.val : E →+* L) h2

private theorem bigEmb_jqModC {L K' : Type*} [Field L] [Algebra ℚ L] [Field K']
    [Algebra ℚ K'] [Algebra L K'] [IsScalarTower ℚ L K'] :
    coeffMap (algebraMap L K') (jqModC L) = coeffEmb K' jq := by
  rw [jqModC_eq_coeffEmb, bigEmb_coeffEmb]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem beta_eval_of_compat (L : Type*) [Field L] [Algebra ℚ L]
    (K' : Type*) [Field K'] [Algebra ℚ K'] [Algebra L K'] [IsScalarTower ℚ L K']
    (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N)
    (ζ ξ : K'ˣ) (hζ : IsPrimitiveRoot (ζ : K') ℓ) (hξ : IsPrimitiveRoot (ξ : K') (N * ℓ))
    (hξN : ξ ^ N = ζ)
    (hle : laurentBaseChange L (modularFunctionFieldFull N)
      ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))
    (b : ℕ)
    (ψ : (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) →+* LaurentSeries K')
    (hψ : ∀ x : laurentBaseChange L (modularFunctionFieldFull N),
      ψ (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) _ x)
        = qExpand K' (N * ℓ) (coeffMap (algebraMap L K') (x : LaurentSeries L)))
    (hψgen : ψ (IntermediateField.AdjoinSimple.gen (laurentBaseChange L (modularFunctionFieldFull N))
        (coeffEmb L (jqN ℓ)))
      = qExpand K' N (qTwist (ζ ^ b) (coeffEmb K' jq)))
    (f : laurentBaseChange L (modularFunctionFieldFull N))
    (hf : qExpand L ℓ (f : LaurentSeries L) ∈ IntermediateField.adjoin
      (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) :
    ψ ⟨qExpand L ℓ (f : LaurentSeries L), hf⟩
      = qExpand K' N (qTwist (ζ ^ b) (coeffMap (algebraMap L K') (f : LaurentSeries L))) := by
  classical
  obtain ⟨dl, -⟩ := ModularCurve.exists_phiIrreducible ℓ
  obtain ⟨dN, -⟩ := ModularCurve.exists_phiIrreducible N
  have hl2 : 2 ≤ ℓ := hl.out.two_le
  have hlpos : 0 < ℓ := hl.out.pos
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hζN : IsPrimitiveRoot ((ξ ^ ℓ : K'ˣ) : K') N := by
    have h := isPrimitiveRoot_pow_div (K := K') hξ (dvd_mul_right N ℓ)
    rwa [Nat.mul_div_cancel_left ℓ hNpos] at h

  have hEeq := bar_extendScalars_eq_adjoin L N ℓ hN hle
  have hĵF : jqModC L ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [jqModC_eq_coeffEmb]
    exact coeffEmb_mem_laurentBaseChange L (jq_mem_full N)

  have hĵ_coe : (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L))
      (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N)) = jqModC L := rfl
  have hambient : (phiAtSeed dl (jqModC L)).eval (coeffEmb L (jqN ℓ)) = 0 := by
    rw [jqModC_eq_coeffEmb]
    exact phiAtSeed_eval_map dl jq (jqN ℓ) (coeffEmb L) (phiAtSeed_jq_eval ℓ dl)
  have haev : Polynomial.aeval (coeffEmb L (jqN ℓ))
      (phiAtSeed dl (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N))) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, phiAtSeed_map, hĵ_coe]
    exact hambient
  have hint : IsIntegral (laurentBaseChange L (modularFunctionFieldFull N))
      (coeffEmb L (jqN ℓ)) :=
    ⟨phiAtSeed dl (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N)),
      phiAtSeed_monic dl _, by rw [← Polynomial.aeval_def]; exact haev⟩
  have hmindeg : (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
      (coeffEmb L (jqN ℓ))).natDegree = ℓ + 1 := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact bar_finrank_adjoin_gen L N ℓ hN hle
  have hPdeg : (phiAtSeed dl
      (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N))).natDegree
      = ℓ + 1 := by
    rw [phiAtSeed_natDegree, ModularCurve.dedekindPsi_prime hl.out]
  have hmin_eq : phiAtSeed dl
      (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N))
      = minpoly (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ)) := by
    apply minpoly.unique_of_degree_le_degree_minpoly _ _ (phiAtSeed_monic dl _) haev
    rw [Polynomial.degree_eq_natDegree (phiAtSeed_monic dl
        (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N))).ne_zero,
      Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hPdeg, hmindeg]

  letI : Algebra (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries K') :=
    (((qExpand K' (N * ℓ)).comp (coeffMap (algebraMap L K'))).comp
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull N))
        (LaurentSeries L))).toAlgebra
  have halg : algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries K')
      = ((qExpand K' (N * ℓ)).comp (coeffMap (algebraMap L K'))).comp
        (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L)) :=
    RingHom.algebraMap_toAlgebra _

  have hseed : ((qExpand K' (N * ℓ)).comp (coeffMap (algebraMap L K') : _ →+* LaurentSeries K'))
      (jqModC L) = qExpand K' (ℓ * N) (qTwist ((1 : K'ˣ) ^ ℓ) (coeffEmb K' jq)) := by
    show qExpand K' (N * ℓ) (coeffMap (algebraMap L K') (jqModC L)) = _
    rw [bigEmb_jqModC, one_pow, qTwist_one_apply]
    exact qExpand_congr (Nat.mul_comm N ℓ) _
  have hmap_min : (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
      (coeffEmb L (jqN ℓ))).map
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries K'))
      = dl.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K'))
          (qExpand K' (ℓ * N) (qTwist ((1 : K'ˣ) ^ ℓ) (coeffEmb K' jq)))) := by
    rw [← hmin_eq, halg, ← Polynomial.map_map, phiAtSeed_map, hĵ_coe, phiAtSeed_map, hseed]
    rfl

  have hgen_aroots : ∀ b : ℕ, b < ℓ →
      qExpand K' N (qTwist ((1 : K'ˣ) * ζ ^ (b * (ℓ / ℓ))) (coeffEmb K' jq))
        ∈ (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
            (coeffEmb L (jqN ℓ))).aroots (LaurentSeries K') := by
    intro b hb
    rw [Polynomial.aroots_def, hmap_min, roots_prime_at_slot ℓ ζ hζ ℓ dvd_rfl dl N 1]
    exact Multiset.mem_cons_of_mem
      (Multiset.mem_map.mpr ⟨b, Multiset.mem_range.mpr hb, rfl⟩)

  obtain ⟨σ0, hσ0⟩ : ∃ σ : (IntermediateField.adjoin
      (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
        →ₐ[laurentBaseChange L (modularFunctionFieldFull N)] LaurentSeries K',
      σ (IntermediateField.AdjoinSimple.gen (laurentBaseChange L (modularFunctionFieldFull N))
          (coeffEmb L (jqN ℓ)))
        = qExpand K' N (qTwist ((1 : K'ˣ) * ζ ^ (0 * (ℓ / ℓ))) (coeffEmb K' jq)) :=
    ⟨(IntermediateField.algHomAdjoinIntegralEquiv _ hint).symm ⟨_, hgen_aroots 0 hlpos⟩,
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen _ hint _⟩
  have hσ0gen : σ0 (IntermediateField.AdjoinSimple.gen
      (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ)))
      = qExpand K' N (coeffEmb K' jq) := by
    rw [hσ0, Nat.zero_mul, pow_zero, mul_one, qTwist_one_apply]

  have hξpow : ∀ b : ℕ, (ξ ^ b) ^ (N * ℓ) = 1 := by
    intro b
    have h1 : ξ ^ (N * ℓ) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hξ.pow_eq_one, Units.val_one]
    rw [← pow_mul, Nat.mul_comm b (N * ℓ), pow_mul, h1, one_pow]
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ →
      (LaurentSeries K' →ₐ[laurentBaseChange L (modularFunctionFieldFull N)] LaurentSeries K'),
      ∀ b w, τ b w = qTwist (ξ ^ b) w :=
    ⟨fun b =>
      { toRingHom := qTwist (ξ ^ b)
        commutes' := fun f => by
          rw [halg]
          show qTwist (ξ ^ b) (qExpand K' (N * ℓ) _) = qExpand K' (N * ℓ) _
          rw [qTwist_qExpand, show ((ξ ^ b) ^ ((N * ℓ : ℕ) : ℤ)) = (1 : K'ˣ) from by
            rw [zpow_natCast]; exact hξpow b, qTwist_one_apply] },
     fun b w => rfl⟩
  have hτσ0gen : ∀ b : ℕ,
      (τ b) (σ0 (IntermediateField.AdjoinSimple.gen
        (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ))))
        = qExpand K' N (qTwist ((1 : K'ˣ) * ζ ^ (b * (ℓ / ℓ))) (coeffEmb K' jq)) := by
    intro b
    have hu : ((ξ ^ b) ^ ((N : ℕ) : ℤ) : K'ˣ) = (1 : K'ˣ) * ζ ^ (b * (ℓ / ℓ)) := by
      rw [Nat.div_self hlpos, Nat.mul_one, one_mul, zpow_natCast, ← pow_mul,
        Nat.mul_comm b N, pow_mul, hξN]
    rw [hτ, hσ0gen, qTwist_qExpand, hu]

  have hmemNL : coeffEmb L (jqN (N * ℓ)) ∈ IntermediateField.adjoin
      (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)) := by
    rw [← hEeq]
    exact (IntermediateField.mem_extendScalars hle).mpr
      (coeffEmb_mem_laurentBaseChange L (jqd_mem_full (N * ℓ) dvd_rfl))
  have hmemN : coeffEmb L (jqN N) ∈ IntermediateField.adjoin
      (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)) := by
    rw [← hEeq]
    exact (IntermediateField.mem_extendScalars hle).mpr
      (hle (coeffEmb_mem_laurentBaseChange L (jqd_mem_full N dvd_rfl)))

  have hx_pin : σ0 ⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩
      = qExpand K' (N * N) (qTwist (1 : K'ˣ) (coeffEmb K' jq)) := by

    have hrel2 : (phiAtSeed dl (jqN N)).eval (jqN (N * ℓ)) = 0 := phiAtSeed_jqN_eval ℓ dl N
    have hrel2L : (phiAtSeed dl (coeffEmb L (jqN N))).eval (coeffEmb L (jqN (N * ℓ))) = 0 :=
      phiAtSeed_eval_map dl _ _ (coeffEmb L) hrel2
    have hrel2E : (phiAtSeed dl (⟨coeffEmb L (jqN N), hmemN⟩ : IntermediateField.adjoin
          (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))).eval
        (⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩ : IntermediateField.adjoin
          (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) = 0 :=
      phiAtSeed_eval_of_injective dl _ _
        ((IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))).val : _ →+* LaurentSeries L)
        Subtype.val_injective hrel2L
    have hrel2Ω : (phiAtSeed dl (σ0 ⟨coeffEmb L (jqN N), hmemN⟩)).eval
        (σ0 ⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩) = 0 :=
      phiAtSeed_eval_map dl _ _ (σ0 : _ →+* LaurentSeries K') hrel2E

    have hσ0N : σ0 ⟨coeffEmb L (jqN N), hmemN⟩
        = qExpand K' (ℓ * (N * N)) (qTwist ((1 : K'ˣ) ^ ℓ) (coeffEmb K' jq)) := by
      have h1 : (⟨coeffEmb L (jqN N), hmemN⟩ : IntermediateField.adjoin
            (laurentBaseChange L (modularFunctionFieldFull N))
            ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
          = algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) _
              (⟨coeffEmb L (jqN N),
                coeffEmb_mem_laurentBaseChange L (jqd_mem_full N dvd_rfl)⟩ :
                laurentBaseChange L (modularFunctionFieldFull N)) := Subtype.ext rfl
      rw [h1, AlgHom.commutes, halg]
      show qExpand K' (N * ℓ) (coeffMap (algebraMap L K') (coeffEmb L (jqN N))) = _
      rw [bigEmb_coeffEmb, show jqN N = qExpand ℚ N jq from rfl, coeffEmb_qExpand,
        qExpand_qExpand, one_pow, qTwist_one_apply]
      exact qExpand_congr (by ring) _
    rw [hσ0N, phiAtSeed] at hrel2Ω
    have hcases := (isRoot_prime_at_slot_iff ℓ ζ hζ ℓ dvd_rfl dl (N * N) 1
      (σ0 ⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩)).mp hrel2Ω

    have hrel1 : (phiAtSeed dN (jqN ℓ)).eval (jqN (N * ℓ)) = 0 := by
      have h := phiAtSeed_jqN_eval N dN ℓ
      rwa [jqN_congr (Nat.mul_comm ℓ N)] at h
    have hrel1L : (phiAtSeed dN (coeffEmb L (jqN ℓ))).eval (coeffEmb L (jqN (N * ℓ))) = 0 :=
      phiAtSeed_eval_map dN _ _ (coeffEmb L) hrel1
    have hrel1E : (phiAtSeed dN
          (IntermediateField.AdjoinSimple.gen (laurentBaseChange L (modularFunctionFieldFull N))
            (coeffEmb L (jqN ℓ)))).eval
        (⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩ : IntermediateField.adjoin
          (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) = 0 :=
      phiAtSeed_eval_of_injective dN _ _
        ((IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))).val : _ →+* LaurentSeries L)
        Subtype.val_injective hrel1L
    have hrel1Ω : (phiAtSeed dN (σ0 (IntermediateField.AdjoinSimple.gen
          (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ))))).eval
        (σ0 ⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩) = 0 :=
      phiAtSeed_eval_map dN _ _ (σ0 : _ →+* LaurentSeries K') hrel1E
    rw [hσ0gen] at hrel1Ω

    have hjqF0 : jq ∈ IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) :=
      IntermediateField.subset_adjoin ℚ _ rfl
    have hjq_coe0 : (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (LaurentSeries ℚ)) (⟨jq, hjqF0⟩ : _) = jq := rfl
    have haevN : Polynomial.aeval (jqN N) (phiAtSeed dN
        (⟨jq, hjqF0⟩ : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))) = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, phiAtSeed_map, hjq_coe0]
      exact phiAtSeed_jq_eval N dN
    have hintN : IsIntegral (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (jqN N) :=
      ⟨phiAtSeed dN (⟨jq, hjqF0⟩ : _), phiAtSeed_monic dN _, by
        rw [← Polynomial.aeval_def]; exact haevN⟩
    have hmindegN : (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (jqN N)).natDegree = dedekindPsi N := by
      rw [← IntermediateField.adjoin.finrank hintN]
      exact ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi N
    have hminN_eq : phiAtSeed dN (⟨jq, hjqF0⟩ : _)
        = minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N) := by
      apply minpoly.unique_of_degree_le_degree_minpoly _ _ (phiAtSeed_monic dN _) haevN
      rw [Polynomial.degree_eq_natDegree (phiAtSeed_monic dN
          (⟨jq, hjqF0⟩ : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))).ne_zero,
        Polynomial.degree_eq_natDegree (minpoly.ne_zero hintN), phiAtSeed_natDegree, hmindegN]
    have hRV := ModularCurve.minpoly_jqN_map_eq_prod_slots (K := K') N (ξ ^ ℓ) hζN (hallAll N)
    have hmapN : (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (jqN N)).map (((coeffEmb K').comp (qExpand ℚ N)).comp
          (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            (LaurentSeries ℚ)))
        = phiAtSeed dN (qExpand K' N (coeffEmb K' jq)) := by
      rw [← hminN_eq, ← Polynomial.map_map, phiAtSeed_map, hjq_coe0, phiAtSeed_map]
      congr 1
      show coeffEmb K' (qExpand ℚ N jq) = _
      rw [coeffEmb_qExpand]
    have hx_slot : ∃ a ∈ N.divisors, ∃ b ∈ (Finset.range (N / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
        σ0 ⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩ = (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩;
          qExpand K' (a * a) (qTwist ((ξ ^ ℓ) ^ (b * a)) (coeffEmb K' jq))) := by
      have h1 : Polynomial.eval (σ0 ⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩)
          ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            (jqN N)).map (((coeffEmb K').comp (qExpand ℚ N)).comp
              (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
                (LaurentSeries ℚ)))) = 0 := by
        rw [hmapN]
        exact hrel1Ω
      rw [hRV, Polynomial.eval_prod] at h1
      obtain ⟨a, ha, h2⟩ := Finset.prod_eq_zero_iff.mp h1
      rw [Polynomial.eval_prod] at h2
      obtain ⟨b, hb, h3⟩ := Finset.prod_eq_zero_iff.mp h2
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h3
      exact ⟨a, ha, b, hb, h3⟩

    obtain ⟨a, ha, b', hb', hx⟩ := hx_slot
    rw [Nat.mem_divisors] at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact NeZero.ne N (Nat.eq_zero_of_zero_dvd ha.1)
    rw [dif_neg ha0] at hx
    haveI : NeZero a := ⟨ha0⟩
    have haN : a ≤ N := Nat.le_of_dvd hNpos ha.1
    rcases hcases with hsp | ⟨b, hb, htw⟩
    ·
      exfalso
      have hTS := (TS_injective (K := K') (e := ℓ * (ℓ * (N * N))) (e' := a * a)
        (u := (1 : K'ˣ) ^ (ℓ * ℓ)) (u' := (ξ ^ ℓ) ^ (b' * a)) (hsp.symm.trans hx)).1
      have h1 : a * a ≤ N * N := Nat.mul_le_mul haN haN
      have h2 : 2 * (2 * (N * N)) ≤ ℓ * (ℓ * (N * N)) :=
        Nat.mul_le_mul hl2 (Nat.mul_le_mul hl2 le_rfl)
      have h3 : 0 < N * N := Nat.mul_pos hNpos hNpos
      omega
    ·
      have hTS := TS_injective (K := K') (e := N * N) (e' := a * a)
        (u := (1 : K'ˣ) * ζ ^ (b * (ℓ / ℓ))) (u' := (ξ ^ ℓ) ^ (b' * a)) (htw.symm.trans hx)
      have haeq : a = N := by
        have h1 := hTS.1
        have h2 : N * N ≤ N * a := by
          calc N * N = a * a := h1
          _ ≤ N * a := Nat.mul_le_mul_right a haN
        have h3 : N ≤ a := Nat.le_of_mul_le_mul_left h2 hNpos
        exact le_antisymm haN h3
      subst haeq
      have hb'0 : b' = 0 := by
        have h1 := (Finset.mem_filter.mp hb').1
        rw [Finset.mem_range, Nat.div_self hNpos] at h1
        omega
      subst hb'0
      have hunit := hTS.2
      rw [Nat.zero_mul, pow_zero, Nat.div_self hlpos, Nat.mul_one, one_mul] at hunit
      have hbz : b = 0 := by
        have h1 : ((ζ : K')) ^ b = 1 := by
          have h2 := congrArg (Units.val) hunit
          rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
        have h3 : ℓ ∣ b := hζ.dvd_of_pow_eq_one b h1
        exact Nat.eq_zero_of_dvd_of_lt h3 hb
      rw [htw, hbz, Nat.zero_mul, pow_zero, mul_one, qTwist_one_apply]

  have hβmem : ∀ x : LaurentSeries L, x ∈ laurentBaseChange L (modularFunctionFieldFull N) →
      qExpand L ℓ x ∈ IntermediateField.adjoin
        (laurentBaseChange L (modularFunctionFieldFull N))
        ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)) := by
    intro x hx
    rw [← hEeq]
    exact (IntermediateField.mem_extendScalars hle).mpr
      (ModularCurve.qExpand_mem_laurentBaseChange ℓ
        (fun y hy => full_degeneracy_map_le (N := N) ℓ ⟨y, hy, rfl⟩) hx)

  have hβ0 : ∀ (x : LaurentSeries L)
      (hxF : x ∈ laurentBaseChange L (modularFunctionFieldFull N))
      (hxE : qExpand L ℓ x ∈ IntermediateField.adjoin
        (laurentBaseChange L (modularFunctionFieldFull N))
        ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))),
      σ0 ⟨qExpand L ℓ x, hxE⟩ = qExpand K' N (coeffMap (algebraMap L K') x) := by
    intro x hxF
    have hxF' : x ∈ IntermediateField.adjoin L {jqModC L, jqNModC L N} := by
      rw [← ModularCurve.laurentBaseChange_adjoin_pair L N (ffgAll N)]
      exact hxF
    clear hxF
    induction hxF' using IntermediateField.adjoin_induction with
    | mem w hw =>
      intro hxE
      rcases hw with rfl | hw
      ·
        have h1 : (⟨qExpand L ℓ (jqModC L), hxE⟩ : IntermediateField.adjoin
            (laurentBaseChange L (modularFunctionFieldFull N))
            ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
            = IntermediateField.AdjoinSimple.gen
                (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ)) := by
          apply Subtype.ext
          show qExpand L ℓ (jqModC L) = coeffEmb L (jqN ℓ)
          rw [jqModC_eq_coeffEmb, show jqN ℓ = qExpand ℚ ℓ jq from rfl, coeffEmb_qExpand]
        rw [h1, hσ0gen, bigEmb_jqModC]
      ·
        rw [Set.mem_singleton_iff] at hw
        subst hw
        have h1 : (⟨qExpand L ℓ (jqNModC L N), hxE⟩ : IntermediateField.adjoin
            (laurentBaseChange L (modularFunctionFieldFull N))
            ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
            = ⟨coeffEmb L (jqN (N * ℓ)), hmemNL⟩ := by
          apply Subtype.ext
          show qExpand L ℓ (qExpand L N (jqModC L)) = coeffEmb L (jqN (N * ℓ))
          rw [jqModC_eq_coeffEmb, show jqN (N * ℓ) = qExpand ℚ (N * ℓ) jq from rfl,
            coeffEmb_qExpand, qExpand_qExpand]
          exact qExpand_congr (by ring) _
        rw [h1, hx_pin, qTwist_one_apply]
        show qExpand K' (N * N) (coeffEmb K' jq)
          = qExpand K' N (coeffMap (algebraMap L K') (qExpand L N (jqModC L)))
        rw [coeffMap_qExpand, bigEmb_jqModC, qExpand_qExpand]
    | algebraMap c =>
      intro hxE
      have h1 : (⟨qExpand L ℓ (algebraMap L (LaurentSeries L) c), hxE⟩ :
          IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
            ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
          = algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) _
              (⟨algebraMap L (LaurentSeries L) c,
                (laurentBaseChange L (modularFunctionFieldFull N)).algebraMap_mem c⟩ :
                laurentBaseChange L (modularFunctionFieldFull N)) :=
        Subtype.ext (qExpand_algebraMap' ℓ c)
      rw [h1, AlgHom.commutes, halg]
      show qExpand K' (N * ℓ) (coeffMap (algebraMap L K') (algebraMap L (LaurentSeries L) c))
        = qExpand K' N (coeffMap (algebraMap L K') (algebraMap L (LaurentSeries L) c))
      rw [coeffMap_algebraMap, qExpand_algebraMap', qExpand_algebraMap']
    | add w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
      intro hxE
      have hm₁ : w₁ ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
        rw [ModularCurve.laurentBaseChange_adjoin_pair L N (ffgAll N)]
        exact hw₁
      have hm₂ : w₂ ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
        rw [ModularCurve.laurentBaseChange_adjoin_pair L N (ffgAll N)]
        exact hw₂
      have h1 : (⟨qExpand L ℓ (w₁ + w₂), hxE⟩ : IntermediateField.adjoin
          (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
          = ⟨qExpand L ℓ w₁, hβmem w₁ hm₁⟩ + ⟨qExpand L ℓ w₂, hβmem w₂ hm₂⟩ := by
        apply Subtype.ext
        show qExpand L ℓ (w₁ + w₂) = qExpand L ℓ w₁ + qExpand L ℓ w₂
        exact map_add _ _ _
      rw [h1, map_add, ih₁ (hβmem w₁ hm₁), ih₂ (hβmem w₂ hm₂), map_add, map_add]
    | inv w hw ih =>
      intro hxE
      have hm : w ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
        rw [ModularCurve.laurentBaseChange_adjoin_pair L N (ffgAll N)]
        exact hw
      have h1 : (⟨qExpand L ℓ w⁻¹, hxE⟩ : IntermediateField.adjoin
          (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
          = (⟨qExpand L ℓ w, hβmem w hm⟩ : IntermediateField.adjoin
              (laurentBaseChange L (modularFunctionFieldFull N))
              ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))⁻¹ := by
        apply Subtype.ext
        show qExpand L ℓ w⁻¹ = (qExpand L ℓ w)⁻¹
        exact map_inv₀ _ _
      rw [h1, map_inv₀, ih (hβmem w hm), map_inv₀, map_inv₀]
    | mul w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
      intro hxE
      have hm₁ : w₁ ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
        rw [ModularCurve.laurentBaseChange_adjoin_pair L N (ffgAll N)]
        exact hw₁
      have hm₂ : w₂ ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
        rw [ModularCurve.laurentBaseChange_adjoin_pair L N (ffgAll N)]
        exact hw₂
      have h1 : (⟨qExpand L ℓ (w₁ * w₂), hxE⟩ : IntermediateField.adjoin
          (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
          = ⟨qExpand L ℓ w₁, hβmem w₁ hm₁⟩ * ⟨qExpand L ℓ w₂, hβmem w₂ hm₂⟩ := by
        apply Subtype.ext
        show qExpand L ℓ (w₁ * w₂) = qExpand L ℓ w₁ * qExpand L ℓ w₂
        exact map_mul _ _ _
      rw [h1, map_mul, ih₁ (hβmem w₁ hm₁), ih₂ (hβmem w₂ hm₂), map_mul, map_mul]

  let ψA : (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
        →ₐ[laurentBaseChange L (modularFunctionFieldFull N)] LaurentSeries K' :=
    { toRingHom := ψ
      commutes' := fun x => by rw [halg]; exact hψ x }
  have hψA : ψA = (τ b).comp σ0 := by
    apply adjoin_simple_algHom_ext
    show ψ _ = (τ b) (σ0 _)
    rw [hψgen, hτσ0gen b, Nat.div_self hlpos, Nat.mul_one, one_mul]
  have h1 : ψ ⟨qExpand L ℓ (f : LaurentSeries L), hf⟩
      = (τ b) (σ0 ⟨qExpand L ℓ (f : LaurentSeries L), hf⟩) :=
    congrArg (fun φ : (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
        →ₐ[laurentBaseChange L (modularFunctionFieldFull N)] LaurentSeries K' =>
      φ ⟨qExpand L ℓ (f : LaurentSeries L), hf⟩) hψA
  have hu : ((ξ ^ b) ^ ((N : ℕ) : ℤ) : K'ˣ) = ζ ^ b := by
    rw [zpow_natCast, ← pow_mul, Nat.mul_comm b N, pow_mul, hξN]
  rw [h1, hβ0 _ f.2 hf, hτ, qTwist_qExpand, hu]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_family (L : Type*) [Field L] [Algebra ℚ L]
    (K' : Type*) [Field K'] [Algebra ℚ K'] [Algebra L K'] [IsScalarTower ℚ L K']
    (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N)
    (ζ ξ : K'ˣ) (hζ : IsPrimitiveRoot (ζ : K') ℓ) (hξ : IsPrimitiveRoot (ξ : K') (N * ℓ))
    (hξN : ξ ^ N = ζ)
    (hle : laurentBaseChange L (modularFunctionFieldFull N)
      ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
    ∃ σ : Fin (ℓ + 1) → ((IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
        ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) →+* LaurentSeries K'),
      (∀ (b : Fin (ℓ + 1)) (x : laurentBaseChange L (modularFunctionFieldFull N)),
        σ b (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) _ x)
          = qExpand K' ℓ (coeffMap (algebraMap L K') (x : LaurentSeries L))) ∧
      (∀ (g : laurentBaseChange L (modularFunctionFieldFull N))
        (hg : qExpand L ℓ (g : LaurentSeries L) ∈ IntermediateField.adjoin
          (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))),
        σ 0 ⟨qExpand L ℓ (g : LaurentSeries L), hg⟩
          = qExpand K' (ℓ * ℓ) (coeffMap (algebraMap L K') (g : LaurentSeries L))) ∧
      (∀ (b : Fin ℓ) (g : laurentBaseChange L (modularFunctionFieldFull N))
        (hg : qExpand L ℓ (g : LaurentSeries L) ∈ IntermediateField.adjoin
          (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))),
        σ b.succ ⟨qExpand L ℓ (g : LaurentSeries L), hg⟩
          = qTwist (ζ ^ (b : ℕ)) (coeffMap (algebraMap L K') (g : LaurentSeries L))) ∧
      (∀ y : IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
          ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)),
        qExpand K' ℓ (coeffMap (algebraMap L K')
          ((Algebra.trace (laurentBaseChange L (modularFunctionFieldFull N))
            (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
              ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) y : LaurentSeries L)))
          = ∑ b, σ b y) := by
  classical
  obtain ⟨dl, -⟩ := ModularCurve.exists_phiIrreducible ℓ
  have hl2 : 2 ≤ ℓ := hl.out.two_le
  have hlpos : 0 < ℓ := hl.out.pos
  have hĵF : jqModC L ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [jqModC_eq_coeffEmb]
    exact coeffEmb_mem_laurentBaseChange L (jq_mem_full N)

  have hĵ_coe : (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L))
      (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N)) = jqModC L := rfl
  have hambient : (phiAtSeed dl (jqModC L)).eval (coeffEmb L (jqN ℓ)) = 0 := by
    rw [jqModC_eq_coeffEmb]
    exact phiAtSeed_eval_map dl jq (jqN ℓ) (coeffEmb L) (phiAtSeed_jq_eval ℓ dl)
  have haev : Polynomial.aeval (coeffEmb L (jqN ℓ))
      (phiAtSeed dl (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N))) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, phiAtSeed_map, hĵ_coe]
    exact hambient
  have hint : IsIntegral (laurentBaseChange L (modularFunctionFieldFull N))
      (coeffEmb L (jqN ℓ)) :=
    ⟨phiAtSeed dl (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N)),
      phiAtSeed_monic dl _, by rw [← Polynomial.aeval_def]; exact haev⟩
  have hmindeg : (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
      (coeffEmb L (jqN ℓ))).natDegree = ℓ + 1 := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact bar_finrank_adjoin_gen L N ℓ hN hle
  have hPdeg : (phiAtSeed dl
      (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N))).natDegree
      = ℓ + 1 := by
    rw [phiAtSeed_natDegree, ModularCurve.dedekindPsi_prime hl.out]
  have hmin_eq : phiAtSeed dl
      (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N))
      = minpoly (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ)) := by
    apply minpoly.unique_of_degree_le_degree_minpoly _ _ (phiAtSeed_monic dl _) haev
    rw [Polynomial.degree_eq_natDegree (phiAtSeed_monic dl
        (⟨jqModC L, hĵF⟩ : laurentBaseChange L (modularFunctionFieldFull N))).ne_zero,
      Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hPdeg, hmindeg]

  letI : Algebra (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries K') :=
    (((qExpand K' ℓ).comp (coeffMap (algebraMap L K'))).comp
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull N))
        (LaurentSeries L))).toAlgebra
  have halg : algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries K')
      = ((qExpand K' ℓ).comp (coeffMap (algebraMap L K'))).comp
        (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L)) :=
    RingHom.algebraMap_toAlgebra _

  have hseed : ((qExpand K' ℓ).comp (coeffMap (algebraMap L K') : _ →+* LaurentSeries K'))
      (jqModC L) = qExpand K' (ℓ * 1) (qTwist ((1 : K'ˣ) ^ ℓ) (coeffEmb K' jq)) := by
    show qExpand K' ℓ (coeffMap (algebraMap L K') (jqModC L)) = _
    rw [bigEmb_jqModC, one_pow, qTwist_one_apply]
    exact qExpand_congr (Nat.mul_one ℓ).symm _
  have hmap_min : (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
      (coeffEmb L (jqN ℓ))).map
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries K'))
      = dl.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K'))
          (qExpand K' (ℓ * 1) (qTwist ((1 : K'ˣ) ^ ℓ) (coeffEmb K' jq)))) := by
    rw [← hmin_eq, halg, ← Polynomial.map_map, phiAtSeed_map, hĵ_coe, phiAtSeed_map, hseed]
    rfl

  have hsp_raw : qExpand K' (ℓ * (ℓ * 1)) (qTwist ((1 : K'ˣ) ^ (ℓ * ℓ)) (coeffEmb K' jq))
      = qExpand K' (ℓ * ℓ) (qTwist (1 : K'ˣ) (coeffEmb K' jq)) := by
    rw [one_pow]
    exact qExpand_congr (by ring) _
  have htw_raw : ∀ c : ℕ, qExpand K' 1 (qTwist ((1 : K'ˣ) * ζ ^ (c * (ℓ / ℓ))) (coeffEmb K' jq))
      = qExpand K' 1 (qTwist (ζ ^ c) (coeffEmb K' jq)) := by
    intro c
    rw [Nat.div_self hlpos, Nat.mul_one, one_mul]
  have hsp_aroots : qExpand K' (ℓ * ℓ) (qTwist (1 : K'ˣ) (coeffEmb K' jq))
      ∈ (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
          (coeffEmb L (jqN ℓ))).aroots (LaurentSeries K') := by
    rw [Polynomial.aroots_def, hmap_min, roots_prime_at_slot ℓ ζ hζ ℓ dvd_rfl dl 1 1]
    exact Multiset.mem_cons.mpr (Or.inl hsp_raw.symm)
  have htw_aroots : ∀ c : ℕ, c < ℓ → qExpand K' 1 (qTwist (ζ ^ c) (coeffEmb K' jq))
      ∈ (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
          (coeffEmb L (jqN ℓ))).aroots (LaurentSeries K') := by
    intro c hc
    rw [Polynomial.aroots_def, hmap_min, roots_prime_at_slot ℓ ζ hζ ℓ dvd_rfl dl 1 1]
    exact Multiset.mem_cons_of_mem
      (Multiset.mem_map.mpr ⟨c, Multiset.mem_range.mpr hc, htw_raw c⟩)
  obtain ⟨root, hroot0, hrootS⟩ : ∃ root : Fin (ℓ + 1) → LaurentSeries K',
      root 0 = qExpand K' (ℓ * ℓ) (qTwist (1 : K'ˣ) (coeffEmb K' jq)) ∧
      ∀ b : Fin ℓ, root b.succ = qExpand K' 1 (qTwist (ζ ^ (b : ℕ)) (coeffEmb K' jq)) :=
    ⟨fun b => Fin.cases (motive := fun _ => LaurentSeries K')
        (qExpand K' (ℓ * ℓ) (qTwist (1 : K'ˣ) (coeffEmb K' jq)))
        (fun b : Fin ℓ => qExpand K' 1 (qTwist (ζ ^ (b : ℕ)) (coeffEmb K' jq))) b,
      Fin.cases_zero, fun b => Fin.cases_succ b⟩
  have hroot_aroots : ∀ b : Fin (ℓ + 1), root b
      ∈ (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
          (coeffEmb L (jqN ℓ))).aroots (LaurentSeries K') := by
    intro b
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨c, rfl⟩
    · rw [hroot0]; exact hsp_aroots
    · rw [hrootS]; exact htw_aroots c c.2
  have hroot_inj : ∀ b b' : Fin (ℓ + 1), root b = root b' → b = b' := by
    intro b b' h
    have h22 : 2 * 2 ≤ ℓ * ℓ := Nat.mul_le_mul hl2 hl2
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨c, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ b' with rfl | ⟨c', rfl⟩
    · rfl
    · exfalso
      rw [hroot0, hrootS] at h
      have h2 := (TS_injective (K := K') (e := ℓ * ℓ) (e' := 1) (u := (1 : K'ˣ))
        (u' := ζ ^ (c' : ℕ)) h).1
      omega
    · exfalso
      rw [hrootS, hroot0] at h
      have h2 := (TS_injective (K := K') (e := 1) (e' := ℓ * ℓ) (u := ζ ^ (c : ℕ))
        (u' := (1 : K'ˣ)) h).1
      omega
    · rw [hrootS, hrootS] at h
      have h2 := (TS_injective (K := K') (e := 1) (e' := 1) (u := ζ ^ (c : ℕ))
        (u' := ζ ^ (c' : ℕ)) h).2
      have h3 : ((ζ : K')) ^ (c : ℕ) = ((ζ : K')) ^ (c' : ℕ) := by
        have h4 := congrArg Units.val h2
        rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h4
      exact congrArg Fin.succ (Fin.ext (hζ.pow_inj c.2 c'.2 h3))

  obtain ⟨σA, hσgen⟩ : ∃ σA : Fin (ℓ + 1) → ((IntermediateField.adjoin
      (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
        →ₐ[laurentBaseChange L (modularFunctionFieldFull N)] LaurentSeries K'),
      ∀ b, σA b (IntermediateField.AdjoinSimple.gen
        (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ))) = root b :=
    ⟨fun b => (IntermediateField.algHomAdjoinIntegralEquiv _ hint).symm ⟨root b, hroot_aroots b⟩,
      fun b => IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen _ hint _⟩

  obtain ⟨σinf, hσinf⟩ : ∃ σ : (IntermediateField.adjoin
      (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
        →ₐ[laurentBaseChange L (modularFunctionFieldFull N)] LaurentSeries K',
      ∀ v, σ v = qExpand K' ℓ (coeffMap (algebraMap L K') (v : LaurentSeries L)) :=
    ⟨{ toRingHom := ((qExpand K' ℓ).comp (coeffMap (algebraMap L K'))).comp
          ((IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
            ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))).val : _ →+* LaurentSeries L)
       commutes' := fun f => by rw [halg]; rfl },
     fun v => rfl⟩
  have hσ0_inf : σA 0 = σinf := by
    apply adjoin_simple_algHom_ext
    rw [hσgen, hroot0, hσinf, qTwist_one_apply]
    show _ = qExpand K' ℓ (coeffMap (algebraMap L K') (coeffEmb L (jqN ℓ)))
    rw [bigEmb_coeffEmb, show jqN ℓ = qExpand ℚ ℓ jq from rfl, coeffEmb_qExpand, qExpand_qExpand]

  letI : Algebra (laurentBaseChange L (modularFunctionFieldFull N))
      (AlgebraicClosure (LaurentSeries K')) :=
    ((algebraMap (LaurentSeries K') (AlgebraicClosure (LaurentSeries K'))).comp
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull N))
        (LaurentSeries K'))).toAlgebra
  have halgbar : algebraMap (laurentBaseChange L (modularFunctionFieldFull N))
      (AlgebraicClosure (LaurentSeries K'))
      = ((algebraMap (LaurentSeries K') (AlgebraicClosure (LaurentSeries K'))).comp
        (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries K'))) :=
    RingHom.algebraMap_toAlgebra _
  obtain ⟨jA, hjA⟩ : ∃ jA : LaurentSeries K'
      →ₐ[laurentBaseChange L (modularFunctionFieldFull N)]
        AlgebraicClosure (LaurentSeries K'),
      ∀ w, jA w = algebraMap (LaurentSeries K') (AlgebraicClosure (LaurentSeries K')) w :=
    ⟨{ toRingHom := algebraMap (LaurentSeries K') (AlgebraicClosure (LaurentSeries K'))
       commutes' := fun f => by rw [halgbar]; rfl },
     fun w => rfl⟩
  haveI : CharZero (laurentBaseChange L (modularFunctionFieldFull N)) := by
    letI : Algebra ℚ (laurentBaseChange L (modularFunctionFieldFull N)) :=
      ((algebraMap L (laurentBaseChange L (modularFunctionFieldFull N))).comp
        (algebraMap ℚ L)).toAlgebra
    exact charZero_of_injective_algebraMap
      (algebraMap ℚ (laurentBaseChange L (modularFunctionFieldFull N))).injective
  haveI : FiniteDimensional (laurentBaseChange L (modularFunctionFieldFull N))
      (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
        ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hjinj : Function.Injective
      (algebraMap (LaurentSeries K') (AlgebraicClosure (LaurentSeries K'))) :=
    RingHom.injective _

  have hclass : ∀ σb : (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
        →ₐ[laurentBaseChange L (modularFunctionFieldFull N)] AlgebraicClosure (LaurentSeries K'),
      ∃ b : Fin (ℓ + 1), σb = jA.comp (σA b) := by
    intro σb
    have h0 : Polynomial.aeval (IntermediateField.AdjoinSimple.gen
        (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ)))
        (minpoly (laurentBaseChange L (modularFunctionFieldFull N))
          (coeffEmb L (jqN ℓ))) = 0 := by
      apply aeval_intermediateField_eq_zero
      exact minpoly.aeval _ _
    have h1 : Polynomial.eval
        (σb (IntermediateField.AdjoinSimple.gen
          (laurentBaseChange L (modularFunctionFieldFull N)) (coeffEmb L (jqN ℓ))))
        ((minpoly (laurentBaseChange L (modularFunctionFieldFull N))
          (coeffEmb L (jqN ℓ))).map
          (algebraMap (laurentBaseChange L (modularFunctionFieldFull N))
            (AlgebraicClosure (LaurentSeries K')))) = 0 := by
      rw [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, h0,
        map_zero]
    rw [halgbar, ← Polynomial.map_map, hmap_min,
      ModularCurve.PhiGen.splits_prime_at_slot ℓ ζ hζ ℓ dvd_rfl dl 1 1] at h1
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_prod, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, Finset.prod_eq_zero_iff,
      sub_eq_zero] at h1
    rcases h1 with h1 | ⟨c, hcm, h1⟩
    · refine ⟨0, adjoin_simple_algHom_ext ?_⟩
      rw [h1, AlgHom.comp_apply, hjA, hσgen, hroot0, hsp_raw]
    · refine ⟨(⟨c, Finset.mem_range.mp hcm⟩ : Fin ℓ).succ, adjoin_simple_algHom_ext ?_⟩
      rw [h1, AlgHom.comp_apply, hjA, hσgen, hrootS, htw_raw c]
  have hinj : ∀ b b' : Fin (ℓ + 1), jA.comp (σA b) = jA.comp (σA b') → b = b' := by
    intro b b' h
    apply hroot_inj
    have h1 := congrArg (fun φ : (IntermediateField.adjoin
        (laurentBaseChange L (modularFunctionFieldFull N))
        ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
          →ₐ[laurentBaseChange L (modularFunctionFieldFull N)]
            AlgebraicClosure (LaurentSeries K') =>
      φ (IntermediateField.AdjoinSimple.gen (laurentBaseChange L (modularFunctionFieldFull N))
        (coeffEmb L (jqN ℓ)))) h
    simp only [AlgHom.comp_apply] at h1
    rw [hjA, hjA, hσgen, hσgen] at h1
    exact hjinj h1
  have huniv : (Finset.univ : Finset ((IntermediateField.adjoin
      (laurentBaseChange L (modularFunctionFieldFull N))
      ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
        →ₐ[laurentBaseChange L (modularFunctionFieldFull N)]
          AlgebraicClosure (LaurentSeries K')))
      = Finset.univ.image (fun b : Fin (ℓ + 1) => jA.comp (σA b)) := by
    apply Finset.ext
    intro σb
    simp only [Finset.mem_univ, true_iff, Finset.mem_image, true_and]
    obtain ⟨b, hb⟩ := hclass σb
    exact ⟨b, hb.symm⟩
  have hinjon : Set.InjOn (fun b : Fin (ℓ + 1) => jA.comp (σA b))
      ↑(Finset.univ : Finset (Fin (ℓ + 1))) := by
    intro b _ b' _ h
    exact hinj b b' h

  refine ⟨fun b => (σA b).toRingHom, ?_, ?_, ?_, ?_⟩
  ·
    intro b x
    show σA b (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) _ x) = _
    rw [(σA b).commutes x, halg]
    rfl
  ·
    intro g hg
    show σA 0 ⟨qExpand L ℓ (g : LaurentSeries L), hg⟩ = _
    rw [hσ0_inf, hσinf]
    show qExpand K' ℓ (coeffMap (algebraMap L K') (qExpand L ℓ (g : LaurentSeries L))) = _
    rw [coeffMap_qExpand, qExpand_qExpand]
  ·
    intro b g hg
    have hψ : ∀ x : laurentBaseChange L (modularFunctionFieldFull N),
        ((qExpand K' N).comp (σA b.succ).toRingHom)
            (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) _ x)
          = qExpand K' (N * ℓ) (coeffMap (algebraMap L K') (x : LaurentSeries L)) := by
      intro x
      show qExpand K' N (σA b.succ (algebraMap (laurentBaseChange L (modularFunctionFieldFull N))
        _ x)) = _
      rw [(σA b.succ).commutes x, halg]
      show qExpand K' N (qExpand K' ℓ (coeffMap (algebraMap L K') (x : LaurentSeries L))) = _
      rw [qExpand_qExpand]
    have hψgen : ((qExpand K' N).comp (σA b.succ).toRingHom)
        (IntermediateField.AdjoinSimple.gen (laurentBaseChange L (modularFunctionFieldFull N))
          (coeffEmb L (jqN ℓ)))
        = qExpand K' N (qTwist (ζ ^ (b : ℕ)) (coeffEmb K' jq)) := by
      show qExpand K' N (σA b.succ _) = _
      rw [hσgen, hrootS, qExpand_one_apply]
    have h := beta_eval_of_compat L K' N ℓ hN ζ ξ hζ hξ hξN hle (b : ℕ)
      ((qExpand K' N).comp (σA b.succ).toRingHom) hψ hψgen g hg
    show σA b.succ ⟨qExpand L ℓ (g : LaurentSeries L), hg⟩ = _
    apply qExpand_injective (R := K') (N := N)
    exact h
  ·
    intro y
    show _ = ∑ b, σA b y
    have htr := trace_eq_sum_embeddings
      (K := ↥(laurentBaseChange L (modularFunctionFieldFull N)))
      (E := AlgebraicClosure (LaurentSeries K')) (x := y)
    rw [huniv, Finset.sum_image hinjon] at htr
    have hsum : ∑ b ∈ (Finset.univ : Finset (Fin (ℓ + 1))), (jA.comp (σA b)) y
        = algebraMap (LaurentSeries K') (AlgebraicClosure (LaurentSeries K')) (∑ b, σA b y) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun b _ => by rw [AlgHom.comp_apply, hjA])
    rw [hsum, halgbar] at htr
    have htr2 : algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries K')
        (Algebra.trace (laurentBaseChange L (modularFunctionFieldFull N))
          (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N))
            ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L))) y)
        = ∑ b, σA b y := hjinj htr
    rw [halg] at htr2
    exact htr2

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"

namespace ModularCurve p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData FunctionFieldGeneration modularFunctionField jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full full_degeneracy_map_le coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffMap_algebraMap coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand jqModC jqNModC map_jqModC heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot dedekindPsi_prime dedekindPsi_pos dedekindPsi_mul_of_coprime finrank_adjoin_jqN_eq_dedekindPsi modularFunctionField_eq_full minpoly_jqN_map_eq_prod_slots full_eq_adjoin_full_div_prime exists_phiIrreducible relfinrank_laurentBaseChange relfinrank_full_eq_dedekindPsi transcendental_jq laurentBaseChange_adjoin_pair qExpand_mem_laurentBaseChange" end ModularCurve
p2m_open_scoped "ModularCurve" in
set_option synthInstance.maxHeartbeats 240000 in

private theorem ModularCurve.exists_traceCensus (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N) (ζ : Lˣ) (ξ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ) (hξ : IsPrimitiveRoot (ξ : L) (N * ℓ)) (hξN : ξ ^ N = ζ) (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
    ∃ σ : Fin (ℓ + 1) → (IntermediateField.extendScalars hle →ₐ[L] LaurentSeries L),
      (∀ (b : Fin (ℓ + 1)) (x : laurentBaseChange L (modularFunctionFieldFull N)), σ b (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) x) = qExpand L ℓ (x : LaurentSeries L)) ∧
      (∀ g : laurentBaseChange L (modularFunctionFieldFull N), σ 0 ⟨(heckeBetaBar L N ℓ g : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mpr (heckeBetaBar L N ℓ g).2⟩ = qExpand L (ℓ * ℓ) (g : LaurentSeries L)) ∧
      (∀ (b : Fin ℓ) (g : laurentBaseChange L (modularFunctionFieldFull N)), σ b.succ ⟨(heckeBetaBar L N ℓ g : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mpr (heckeBetaBar L N ℓ g).2⟩ = qTwist (ζ ^ (b : ℕ)) (g : LaurentSeries L)) ∧
      (∀ y : IntermediateField.extendScalars hle, qExpand L ℓ ((Algebra.trace (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) y : LaurentSeries L)) = ∑ b, σ b y) := by
  obtain ⟨σ', ha, hb, hc, hd⟩ := ModularCurve.W1.exists_family L L N ℓ hN ζ ξ hζ hξ hξN hle
  simp only [ModularCurve.W1.coeffMap_self_apply] at ha hb hc hd
  have hEeq := ModularCurve.W1.bar_extendScalars_eq_adjoin L N ℓ hN hle

  have hβ : ∀ g : laurentBaseChange L (modularFunctionFieldFull N),
      IntermediateField.inclusion hEeq.le ⟨(heckeBetaBar L N ℓ g : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mpr (heckeBetaBar L N ℓ g).2⟩
        = ⟨qExpand L ℓ (g : LaurentSeries L),
            hEeq.le ((IntermediateField.mem_extendScalars hle).mpr (heckeBetaBar L N ℓ g).2)⟩ :=
    fun g => Subtype.ext rfl
  refine ⟨fun b =>
    { toRingHom := (σ' b).comp (IntermediateField.inclusion hEeq.le : _ →+* _)
      commutes' := fun c => by
        show σ' b (IntermediateField.inclusion hEeq.le (algebraMap L _ c)) = _
        rw [IsScalarTower.algebraMap_apply L (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) c,
          (IntermediateField.inclusion hEeq.le).commutes, ha]
        exact ModularCurve.W1.qExpand_algebraMap' ℓ c }, ?_, ?_, ?_, ?_⟩
  ·
    intro b x
    show σ' b (IntermediateField.inclusion hEeq.le (algebraMap _ _ x)) = _
    rw [(IntermediateField.inclusion hEeq.le).commutes x]
    exact ha b x
  ·
    intro g
    show σ' 0 (IntermediateField.inclusion hEeq.le _) = _
    rw [hβ g]
    exact hb g _
  ·
    intro b g
    show σ' b.succ (IntermediateField.inclusion hEeq.le _) = _
    rw [hβ g]
    exact hc b g _
  ·
    intro y
    show qExpand L ℓ _ = ∑ b, σ' b (IntermediateField.inclusion hEeq.le y)
    have htreq : Algebra.trace (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) y
        = Algebra.trace (laurentBaseChange L (modularFunctionFieldFull N))
            (IntermediateField.adjoin (laurentBaseChange L (modularFunctionFieldFull N)) ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)))
            (IntermediateField.inclusion hEeq.le y) := by
      have h := Algebra.trace_eq_of_algEquiv (IntermediateField.equivOfEq hEeq) y
      rw [← h]
      rfl
    rw [htreq]
    exact hd _

p2m_open_scoped "ModularCurve" in
set_option synthInstance.maxHeartbeats 240000 in

theorem ModularCurve.qExpand_trace_heckeBetaBar_of_traceCensus (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N) (ζ : Lˣ) (ξ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ) (hξ : IsPrimitiveRoot (ξ : L) (N * ℓ)) (hξN : ξ ^ N = ζ) (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) (g : laurentBaseChange L (modularFunctionFieldFull N)) : qExpand L ℓ ((Algebra.trace (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) ⟨(heckeBetaBar L N ℓ g : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mpr (heckeBetaBar L N ℓ g).2⟩ : LaurentSeries L)) = qExpand L (ℓ * ℓ) (g : LaurentSeries L) + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) (g : LaurentSeries L) := by
  obtain ⟨σ, -, hb, hc, hd⟩ := ModularCurve.exists_traceCensus L N ℓ hN ζ ξ hζ hξ hξN hle
  rw [hd, Fin.sum_univ_succ, hb g]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun b => qTwist (ζ ^ b) (g : LaurentSeries L)) ℓ]
  exact Finset.sum_congr rfl (fun b _ => hc b g)

end
p2m_reactivate "P2MW.S_ModularCurve_exists_traceCensus.ModularCurve P2MW.S_ModularCurve_exists_traceCensus.ModularCurve.W1"

p2m_open "ModularCurve~coeffEmb_qExpand~jq_mem_full" in open _root_.P2MW.S_ModularCurve_exists_traceCensus.ModularCurve ModularCurve.PhiGen in

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] (hN : ¬ ℓ ∣ N) (ζ : Lˣ) (ξ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) ℓ) (hξ : IsPrimitiveRoot (ξ : L) (N * ℓ)) (hξN : ξ ^ N = ζ) (hle : laurentBaseChange L (modularFunctionFieldFull N) ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) : ∃ σ : Fin (ℓ + 1) → (IntermediateField.extendScalars hle →ₐ[L] LaurentSeries L), (∀ (b : Fin (ℓ + 1)) (x : laurentBaseChange L (modularFunctionFieldFull N)), σ b (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) x) = qExpand L ℓ (x : LaurentSeries L)) ∧ (∀ g : laurentBaseChange L (modularFunctionFieldFull N), σ 0 ⟨(heckeBetaBar L N ℓ g : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mpr (heckeBetaBar L N ℓ g).2⟩ = qExpand L (ℓ * ℓ) (g : LaurentSeries L)) ∧ (∀ (b : Fin ℓ) (g : laurentBaseChange L (modularFunctionFieldFull N)), σ b.succ ⟨(heckeBetaBar L N ℓ g : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mpr (heckeBetaBar L N ℓ g).2⟩ = qTwist (ζ ^ (b : ℕ)) (g : LaurentSeries L)) ∧ (∀ y : IntermediateField.extendScalars hle, qExpand L ℓ ((Algebra.trace (laurentBaseChange L (modularFunctionFieldFull N)) (IntermediateField.extendScalars hle) y : LaurentSeries L)) = ∑ b, σ b y) :=
  ModularCurve.exists_traceCensus L N ℓ hN ζ ξ hζ hξ hξN hle

#print axioms solution

end S_ModularCurve_exists_traceCensus
end P2MW
export P2MW.S_ModularCurve_exists_traceCensus (solution)
