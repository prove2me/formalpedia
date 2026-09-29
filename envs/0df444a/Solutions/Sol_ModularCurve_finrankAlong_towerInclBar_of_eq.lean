-- Prove2me | solution 1 for ModularCurve.finrankAlong_towerInclBar_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/718da366-46a9-5d4e-ba1d-5f6736cc2ed1

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
import Theorems.Thm_ModularCurve_relfinrank_qExpand_full
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_jqN
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_laurentBaseChange_mono
import Theorems.Thm_ModularCurve_qExpand_mem_laurentBaseChange
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option Elab.async false

noncomputable section

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve ModularCurve.PhiGen"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand towerInclBar towerInclBar_self towerSubstBar dvd_of_eq_roof heckeAlphaBar heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot relfinrank_qExpand_full relfinrank_full_eq_dedekindPsi relfinrank_laurentBaseChange transcendental_jqN laurentBaseChange_adjoin laurentBaseChange_mono qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

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
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand towerInclBar towerInclBar_self towerSubstBar dvd_of_eq_roof heckeAlphaBar heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot relfinrank_qExpand_full relfinrank_full_eq_dedekindPsi relfinrank_laurentBaseChange transcendental_jqN laurentBaseChange_adjoin laurentBaseChange_mono qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

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
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand towerInclBar towerInclBar_self towerSubstBar dvd_of_eq_roof heckeAlphaBar heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot relfinrank_qExpand_full relfinrank_full_eq_dedekindPsi relfinrank_laurentBaseChange transcendental_jqN laurentBaseChange_adjoin laurentBaseChange_mono qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

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
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand towerInclBar towerInclBar_self towerSubstBar dvd_of_eq_roof heckeAlphaBar heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot relfinrank_qExpand_full relfinrank_full_eq_dedekindPsi relfinrank_laurentBaseChange transcendental_jqN laurentBaseChange_adjoin laurentBaseChange_mono qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

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
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand towerInclBar towerInclBar_self towerSubstBar dvd_of_eq_roof heckeAlphaBar heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot relfinrank_qExpand_full relfinrank_full_eq_dedekindPsi relfinrank_laurentBaseChange transcendental_jqN laurentBaseChange_adjoin laurentBaseChange_mono qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

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
  refine Polynomial.ringHom_ext' ?_ ?_
  · exact RingHom.ext_int _ _
  · simp [evalAtJ_X]

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
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "algebraAlong finrankAlong" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in
private theorem AlgebraicCurve.finrankAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') : AlgebraicCurve.finrankAlong K (χ.comp φ) = AlgebraicCurve.finrankAlong K φ * AlgebraicCurve.finrankAlong K χ := by
  letI : Algebra F F' := AlgebraicCurve.algebraAlong φ
  letI : Algebra F' F'' := AlgebraicCurve.algebraAlong χ
  letI : Algebra F F'' := AlgebraicCurve.algebraAlong (χ.comp φ)
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  show Module.finrank F F'' = Module.finrank F F' * Module.finrank F' F''
  exact (Module.finrank_mul_finrank F F' F'').symm

p2m_open_scoped "AlgebraicCurve" in

private theorem AlgebraicCurve.finrankAlong_id {K F : Type*} [Field K] [Field F] [Algebra K F] : AlgebraicCurve.finrankAlong K (AlgHom.id K F) = 1 := by
  letI : Algebra F F := AlgebraicCurve.algebraAlong (AlgHom.id K F)
  show Module.finrank F F = 1
  exact Module.finrank_self F

p2m_open_scoped "AlgebraicCurve" in
private theorem AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange {K E : Type*} [Field K] [Field E] [Algebra K E] (A B : IntermediateField K E) (φ : A →ₐ[K] B) : AlgebraicCurve.finrankAlong K φ = IntermediateField.relfinrank ((B.val.comp φ).fieldRange) B := by
  have hRB : (B.val.comp φ).fieldRange ≤ B := by
    rintro x ⟨a, rfl⟩
    exact (φ a).2
  rw [IntermediateField.relfinrank_eq_finrank_of_le hRB]
  letI : Algebra A B := AlgebraicCurve.algebraAlong φ
  let i : A ≃+* ((B.val.comp φ).fieldRange) :=
    (AlgEquiv.ofInjectiveField (B.val.comp φ)).toRingEquiv
  let j : B ≃+* (IntermediateField.extendScalars hRB) := RingEquiv.refl _
  exact Algebra.finrank_eq_of_equiv_equiv i j (by
    refine RingHom.ext fun a => Subtype.ext ?_
    rfl)

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand towerInclBar towerInclBar_self towerSubstBar dvd_of_eq_roof heckeAlphaBar heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot relfinrank_qExpand_full relfinrank_full_eq_dedekindPsi relfinrank_laurentBaseChange transcendental_jqN laurentBaseChange_adjoin laurentBaseChange_mono qExpand_mem_laurentBaseChange"
namespace W1
p2m_open "ModularCurve~coeffEmb_qExpand"

private theorem full_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    modularFunctionFieldFull a = modularFunctionFieldFull b := by
  subst h; rfl

private theorem dedekindPsi_pos' (A : ℕ) [NeZero A] : 0 < dedekindPsi A := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ A.divisors.filter (fun d => Squarefree d) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd A, NeZero.ne A⟩, squarefree_one⟩
  calc 0 < A / 1 := by
        rw [Nat.div_one]
        exact Nat.pos_of_ne_zero (NeZero.ne A)
  _ ≤ ∑ d ∈ A.divisors with Squarefree d, A / d := Finset.single_le_sum (fun _ _ => Nat.zero_le _) h1

private theorem fieldRange_heckeBetaBar (L : Type*) [Field L] [Algebra ℚ L] (A : ℕ) [NeZero A]
    (ℓ : ℕ) [NeZero ℓ] :
    (((laurentBaseChange L (modularFunctionFieldFull (A * ℓ))).val.comp
        (heckeBetaBar L A ℓ)).fieldRange)
      = laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨a, rfl⟩
    show qExpand L ℓ (a : LaurentSeries L) ∈ _
    refine ModularCurve.qExpand_mem_laurentBaseChange ℓ (fun y hy => ?_) a.2
    rw [IntermediateField.mem_map]
    exact ⟨y, hy, rfl⟩
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    show coeffEmb L (qExpand ℚ ℓ y) ∈ _
    rw [coeffEmb_qExpand]
    exact ⟨⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩, rfl⟩

end ModularCurve.W1
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"

namespace ModularCurve p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_qExpand qExpandₐ qExpandₐ_apply jq coeff_jq_neg_one coeff_jq_of_lt jqN dedekindPsi evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_map_le coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand towerInclBar towerInclBar_self towerSubstBar dvd_of_eq_roof heckeAlphaBar heckeBetaBar coeffMap_qExpand PhiGen.splits_prime_at_slot relfinrank_qExpand_full relfinrank_full_eq_dedekindPsi relfinrank_laurentBaseChange transcendental_jqN laurentBaseChange_adjoin laurentBaseChange_mono qExpand_mem_laurentBaseChange" end ModularCurve
p2m_open_scoped "ModularCurve" in
open ModularCurve.W1 in
private theorem ModularCurve.finrankAlong_heckeBetaBar (L : Type*) [Field L] [Algebra ℚ L] (A : ℕ) [NeZero A] (ℓ : ℕ) [hl : Fact (Nat.Prime ℓ)] : AlgebraicCurve.finrankAlong L (heckeBetaBar L A ℓ) = if ℓ ∣ A then ℓ else ℓ + 1 := by
  classical
  have hB2 := AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange _ _ (heckeBetaBar L A ℓ)
  have hcong : IntermediateField.relfinrank
      (((laurentBaseChange L (modularFunctionFieldFull (A * ℓ))).val.comp
        (heckeBetaBar L A ℓ)).fieldRange)
      (laurentBaseChange L (modularFunctionFieldFull (A * ℓ)))
      = IntermediateField.relfinrank
          (laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)))
          (laurentBaseChange L (modularFunctionFieldFull (A * ℓ))) :=
    congrArg (fun X : IntermediateField L (LaurentSeries L) =>
      IntermediateField.relfinrank X (laurentBaseChange L (modularFunctionFieldFull (A * ℓ))))
      (fieldRange_heckeBetaBar L A ℓ)
  refine (hB2.trans hcong).trans ?_

  have hmemJ : jqN ℓ ∈ (modularFunctionFieldFull A).map (qExpandₐ ℓ) := by
    rw [IntermediateField.mem_map]
    refine ⟨jq, ?_, by rw [qExpandₐ_apply, jqN]⟩
    have h := jqd_mem_full A (one_dvd A)
    rwa [qExpand_one_apply] at h
  have hanchor_le : IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ))
      ≤ (modularFunctionFieldFull A).map (qExpandₐ ℓ) := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x rfl
    exact hmemJ
  have hmap_le : (modularFunctionFieldFull A).map (qExpandₐ ℓ) ≤ modularFunctionFieldFull (A * ℓ) :=
    full_degeneracy_map_le A ℓ
  have hmemJ2 : jqN ℓ ∈ modularFunctionFieldFull (A * ℓ) := hmap_le hmemJ

  have hXeq : laurentBaseChange L (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
      = IntermediateField.adjoin L ({coeffEmb L (jqN ℓ)} : Set (LaurentSeries L)) := by
    rw [ModularCurve.laurentBaseChange_adjoin, Set.image_singleton]
  have hXR : laurentBaseChange L (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
      ≤ laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)) :=
    ModularCurve.laurentBaseChange_mono L hanchor_le
  have hRB : laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ))
      ≤ laurentBaseChange L (modularFunctionFieldFull (A * ℓ)) :=
    ModularCurve.laurentBaseChange_mono L hmap_le

  have hTR1a := ModularCurve.relfinrank_laurentBaseChange L
    ((modularFunctionFieldFull A).map (qExpandₐ ℓ)) (jqN ℓ) hmemJ (transcendental_jqN ℓ)
  have hTR1b := ModularCurve.relfinrank_laurentBaseChange L
    (modularFunctionFieldFull (A * ℓ)) (jqN ℓ) hmemJ2 (transcendental_jqN ℓ)

  have hanchor_val : IntermediateField.relfinrank
      (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
      ((modularFunctionFieldFull A).map (qExpandₐ ℓ)) = dedekindPsi A := by
    have hmapmap := IntermediateField.relfinrank_map_map
      (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionFieldFull A)
      (qExpandₐ ℓ)
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hmapmap
    rw [show qExpandₐ ℓ jq = jqN ℓ from by rw [qExpandₐ_apply, jqN]] at hmapmap
    rw [hmapmap]
    exact ModularCurve.relfinrank_full_eq_dedekindPsi A
  have hQside : IntermediateField.relfinrank
      (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ)))
      (modularFunctionFieldFull (A * ℓ))
      = dedekindPsi A * (if ℓ ∣ A then ℓ else ℓ + 1) := by
    rw [← IntermediateField.relfinrank_mul_relfinrank hanchor_le hmap_le, hanchor_val,
      ModularCurve.relfinrank_qExpand_full A ℓ]

  have hbar : IntermediateField.relfinrank
      (laurentBaseChange L (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ))))
      (laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)))
      * IntermediateField.relfinrank
        (laurentBaseChange L ((modularFunctionFieldFull A).map (qExpandₐ ℓ)))
        (laurentBaseChange L (modularFunctionFieldFull (A * ℓ)))
      = IntermediateField.relfinrank
          (laurentBaseChange L (IntermediateField.adjoin ℚ ({jqN ℓ} : Set (LaurentSeries ℚ))))
          (laurentBaseChange L (modularFunctionFieldFull (A * ℓ))) :=
    IntermediateField.relfinrank_mul_relfinrank hXR hRB
  rw [hXeq] at hbar
  rw [hTR1a, hanchor_val] at hbar
  rw [hTR1b, hQside] at hbar

  exact Nat.eq_of_mul_eq_mul_left (dedekindPsi_pos' A) hbar

p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 3200000 in
open ModularCurve.W1 in

private theorem ModularCurve.finrankAlong_towerInclBar_of_eq (L : Type*) [Field L] [Algebra ℚ L] (A B : ℕ) [NeZero A] [NeZero B] (hAB : A = B) (h : A ∣ B) : AlgebraicCurve.finrankAlong L (towerInclBar (N := A) (M := B) L h) = 1 := by
  subst hAB
  have hid : towerInclBar (N := A) (M := A) L h = AlgHom.id L
      (laurentBaseChange L (modularFunctionFieldFull A)) :=
    AlgHom.ext fun x => towerInclBar_self L h x
  exact (congrArg (fun φ => AlgebraicCurve.finrankAlong L φ) hid).trans
    AlgebraicCurve.finrankAlong_id

p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 3200000 in
open ModularCurve.W1 in

private theorem ModularCurve.finrankAlong_towerSubstBar_roof (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ ℓ' M : ℕ) [hl : Fact (Nat.Prime ℓ)] [hl' : Fact (Nat.Prime ℓ')] [NeZero M] (hM : M = N * ℓ * ℓ') (hne : ℓ ≠ ℓ') : AlgebraicCurve.finrankAlong L (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2) = AlgebraicCurve.finrankAlong L (heckeBetaBar L N ℓ) := by
  classical
  have hsubst_eq : towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2
      = (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp (heckeBetaBar L (N * ℓ') ℓ) := rfl
  refine Eq.trans (congrArg (fun φ => AlgebraicCurve.finrankAlong L φ) hsubst_eq) ?_
  refine Eq.trans (AlgebraicCurve.finrankAlong_comp (heckeBetaBar L (N * ℓ') ℓ)
    (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).2)) ?_
  have hlev : N * ℓ' * ℓ = M := by rw [hM]; ring
  rw [ModularCurve.finrankAlong_towerInclBar_of_eq L (N * ℓ' * ℓ) M hlev
    (dvd_of_eq_roof N ℓ ℓ' M hM).2, mul_one]
  refine (ModularCurve.finrankAlong_heckeBetaBar L (N * ℓ') ℓ).trans
    (Eq.trans ?_ (ModularCurve.finrankAlong_heckeBetaBar L N ℓ).symm)
  have hiff : ℓ ∣ N * ℓ' ↔ ℓ ∣ N := by
    constructor
    · intro h
      exact (Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.coprime_primes hl.out hl'.out).mpr hne) h)
    · intro h
      exact h.mul_right ℓ'
  by_cases hd : ℓ ∣ N
  · rw [if_pos hd, if_pos (hiff.mpr hd)]
  · rw [if_neg hd, if_neg (fun h => hd (hiff.mp h))]

p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 3200000 in
open ModularCurve.W1 in
private theorem ModularCurve.finrankAlong_towerSubstBar_comp_heckeAlphaBar (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (ℓ ℓ' M : ℕ) [hl : Fact (Nat.Prime ℓ)] [hl' : Fact (Nat.Prime ℓ')] [NeZero M] (hM : M = N * ℓ * ℓ') (hne : ℓ ≠ ℓ') : AlgebraicCurve.finrankAlong L ((towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).comp (heckeAlphaBar L N ℓ')) = AlgebraicCurve.finrankAlong L (heckeAlphaBar L N ℓ') * AlgebraicCurve.finrankAlong L (heckeBetaBar L N ℓ) := by
  refine Eq.trans (AlgebraicCurve.finrankAlong_comp (heckeAlphaBar L N ℓ')
    (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2)) ?_
  exact congrArg
    (fun t => AlgebraicCurve.finrankAlong L (heckeAlphaBar L N ℓ') * t)
    (ModularCurve.finrankAlong_towerSubstBar_roof L N ℓ ℓ' M hM hne)

end
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve.W1"

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq.ModularCurve in

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (A B : ℕ) [NeZero A] [NeZero B] (hAB : A = B) (h : A ∣ B) : AlgebraicCurve.finrankAlong L (towerInclBar (N := A) (M := B) L h) = 1 :=
  ModularCurve.finrankAlong_towerInclBar_of_eq L A B hAB h

#print axioms solution

end S_ModularCurve_finrankAlong_towerInclBar_of_eq
end P2MW
export P2MW.S_ModularCurve_finrankAlong_towerInclBar_of_eq (solution)
