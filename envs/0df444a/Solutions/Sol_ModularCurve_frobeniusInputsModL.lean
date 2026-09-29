-- Prove2me | solution 1 for ModularCurve.frobeniusInputsModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7c895759-895c-56fe-a81b-8cdd40ee089b

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobeniusInputsModL
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option linter.unusedSectionVars false

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace W4FA

section Criterion

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p]

theorem frobenius_image_range_algebraMap :
    (frobenius L p) '' Set.range (algebraMap K L) = Set.range (algebraMap K L) := by
  ext u
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a ^ p, by rw [map_pow, frobenius_def]⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := surjective_frobenius K p a
    exact ⟨algebraMap K L b, ⟨b, rfl⟩, by rw [frobenius_def, frobenius_def, map_pow]⟩

theorem map_frobenius_adjoin_toSubfield (S : Set L) :
    (adjoin K S).toSubfield.map (frobenius L p) = (adjoin K ((frobenius L p) '' S)).toSubfield := by
  rw [adjoin_toSubfield, adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    frobenius_image_range_algebraMap]

omit [CharP K p] [PerfectRing K p] in

theorem map_frobenius_adjoin_toSubfield_le (S : Set L) :
    (adjoin K S).toSubfield.map (frobenius L p) ≤ (adjoin K ((frobenius L p) '' S)).toSubfield := by
  rw [adjoin_toSubfield, RingHom.map_field_closure, Subfield.closure_le, Set.image_union]
  rintro u (⟨_, ⟨a, rfl⟩, rfl⟩ | hu)
  · exact pow_mem ((adjoin K _).algebraMap_mem a) p
  · exact IntermediateField.subset_adjoin K _ hu

omit [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p] in

theorem relfinrank_adjoin_simple (F : IntermediateField K L) {a : L} (ha : IsIntegral F a) :
    IntermediateField.relfinrank F (restrictScalars K F⟮a⟯) = (minpoly F a).natDegree := by
  have hle : F ≤ restrictScalars K F⟮a⟯ := fun u hu => (algebraMap F F⟮a⟯ ⟨u, hu⟩).2
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  have hext : extendScalars hle = F⟮a⟯ :=
    IntermediateField.restrictScalars_injective K (extendScalars_restrictScalars hle)
  rw [hext, IntermediateField.adjoin.finrank ha]

omit [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p] in
theorem le_restrictScalars_adjoin (F : IntermediateField K L) (S : Set L) :
    F ≤ restrictScalars K (adjoin F S) := fun u hu => (algebraMap F (adjoin F S) ⟨u, hu⟩).2

include p in

theorem isSeparable_of_forall_pow_ne {x : L} (hx : ∀ u : L, u ^ p ≠ x)
    {y : L} (hy : IsIntegral K⟮x⟯ y) : IsSeparable K⟮x⟯ y := by
  classical
  by_contra hsep
  set E : IntermediateField K L := K⟮x⟯ with hE
  have hp : p.Prime := Fact.out

  have hirr : Irreducible (minpoly E y) := minpoly.irreducible hy
  obtain hs | ⟨-, g, hg, hgm⟩ := Polynomial.separable_or p hirr
  · exact hsep hs
  set z : L := y ^ p with hz
  have hgz : aeval z g = 0 := by
    rw [hz, ← expand_aeval p g y, hgm, minpoly.aeval]
  have hgmonic : g.Monic := by
    have h := minpoly.monic hy
    rw [← hgm] at h
    exact (monic_expand_iff hp.pos).mp h
  have hgmin : g = minpoly E z := minpoly.eq_of_irreducible_of_monic hg hgz hgmonic
  have hzint : IsIntegral E z := hy.pow p
  set r : ℕ := g.natDegree with hr
  have hrpos : 0 < r := by rw [hr, hgmin]; exact minpoly.natDegree_pos hzint
  have hdegm : (minpoly E y).natDegree = r * p := by rw [← hgm, natDegree_expand]

  let φ : L →+* L := frobenius L p
  set SE : Subfield L := E.toSubfield with hSE
  set SM : Subfield L := (restrictScalars K E⟮y⟯).toSubfield with hSM
  set SM₁ : Subfield L := (restrictScalars K E⟮z⟯).toSubfield with hSM₁
  set SE' : Subfield L := SE.map φ with hSE'
  set SM' : Subfield L := SM.map φ with hSM'

  have h1 : SE.relfinrank SM = r * p := by
    change IntermediateField.relfinrank E (restrictScalars K E⟮y⟯) = r * p
    rw [relfinrank_adjoin_simple E hy, hdegm]

  have h2 : SE.relfinrank SM₁ = r := by
    change IntermediateField.relfinrank E (restrictScalars K E⟮z⟯) = r
    rw [relfinrank_adjoin_simple E hzint, ← hgmin]

  have h3 : SE'.relfinrank SM' = r * p := by
    rw [hSE', hSM', Subfield.relfinrank_map_map, h1]

  have hE' : SE' = (K⟮x ^ p⟯).toSubfield := by
    rw [hSE', hSE, hE, map_frobenius_adjoin_toSubfield p, Set.image_singleton, frobenius_def]
  have hxpE : IsIntegral K⟮x ^ p⟯ x := by
    refine ⟨X ^ p - C (AdjoinSimple.gen K (x ^ p)), monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
    simp
  have hEeq : restrictScalars K (K⟮x ^ p⟯)⟮x⟯ = E := by
    rw [adjoin_simple_adjoin_simple, hE]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro u (rfl | rfl)
      · exact pow_mem (mem_adjoin_simple_self K x) p
      · exact mem_adjoin_simple_self K u
    · exact adjoin.mono K _ _ (Set.subset_insert _ _)
  have h4 : SE'.relfinrank SE ≤ p := by
    rw [hE', hSE, ← hEeq]
    change IntermediateField.relfinrank K⟮x ^ p⟯ (restrictScalars K (K⟮x ^ p⟯)⟮x⟯) ≤ p
    rw [relfinrank_adjoin_simple _ hxpE]
    have hdvd : minpoly K⟮x ^ p⟯ x ∣ X ^ p - C (AdjoinSimple.gen K (x ^ p)) :=
      minpoly.dvd _ _ (by simp)
    calc (minpoly K⟮x ^ p⟯ x).natDegree
        ≤ (X ^ p - C (AdjoinSimple.gen K (x ^ p))).natDegree :=
          natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero hp.pos _)
      _ = p := natDegree_X_pow_sub_C
  have h4' : 0 < SE'.relfinrank SE := by
    rw [hE', hSE, ← hEeq]
    change 0 < IntermediateField.relfinrank K⟮x ^ p⟯ (restrictScalars K (K⟮x ^ p⟯)⟮x⟯)
    rw [relfinrank_adjoin_simple _ hxpE]
    exact minpoly.natDegree_pos hxpE

  have hE'E : SE' ≤ SE := by
    rw [hSE']
    rintro _ ⟨u, hu, rfl⟩
    exact pow_mem hu p
  have hEM₁ : SE ≤ SM₁ := le_restrictScalars_adjoin E {z}
  have hEM : SE ≤ SM := le_restrictScalars_adjoin E {y}
  have hM'M₁ : SM' ≤ SM₁ := by
    rw [hSM', hSM]
    have hM : restrictScalars K E⟮y⟯ = adjoin K {x, y} := by
      rw [hE, adjoin_simple_adjoin_simple]
    rw [hM]
    refine (map_frobenius_adjoin_toSubfield_le p _).trans ?_
    change adjoin K (frobenius L p '' {x, y}) ≤ restrictScalars K E⟮z⟯
    rw [adjoin_le_iff]
    rintro u ⟨v, hv, rfl⟩
    rcases hv with rfl | rfl
    · exact pow_mem (le_restrictScalars_adjoin E {z} (mem_adjoin_simple_self K v)) p
    · change frobenius L p _ ∈ E⟮z⟯
      rw [frobenius_def, ← hz]
      exact mem_adjoin_simple_self E z
  have hE'M' : SE' ≤ SM' := by
    rw [hSE', hSM']
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hEM hu, rfl⟩

  have h5 : SE'.relfinrank SM₁ = SE'.relfinrank SE * r := by
    rw [← Subfield.relfinrank_mul_relfinrank hE'E hEM₁, h2]
  have h6 : SE'.relfinrank SM₁ = r * p * SM'.relfinrank SM₁ := by
    rw [← Subfield.relfinrank_mul_relfinrank hE'M' hM'M₁, h3]
  have hne : SE'.relfinrank SM₁ ≠ 0 := by
    rw [h5]; exact Nat.mul_ne_zero h4'.ne' hrpos.ne'
  have hone : SM'.relfinrank SM₁ = 1 := by
    have hle : SE'.relfinrank SE * r ≤ p * r := Nat.mul_le_mul_right r h4
    rw [← h5, h6] at hle
    have hk : SM'.relfinrank SM₁ ≠ 0 := fun h => hne (by rw [h6, h]; ring)
    have hk1 : SM'.relfinrank SM₁ ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have : r * p * 2 ≤ r * p * SM'.relfinrank SM₁ := Nat.mul_le_mul_left _ hcon
      have hrp : 0 < r * p := Nat.mul_pos hrpos hp.pos
      nlinarith
    omega

  have hxM' : x ∈ SM' := by
    have hM₁M' : SM₁ ≤ SM' := Subfield.relfinrank_eq_one_iff.mp hone
    exact hM₁M' (le_restrictScalars_adjoin E {z} (mem_adjoin_simple_self K x))
  rw [hSM'] at hxM'
  obtain ⟨u, -, hu⟩ := hxM'
  exact hx u hu

end Criterion

end W4FA

end

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "Polynomial IntermediateField HahnSeries ModularCurve~coeffMap_injective"

namespace W4FA

section JBar

variable (K : Type*) [Field K]

theorem eq_zero_of_aeval_jqModC_eq_zero {p : K[X]} (hp : aeval (jqModC K) p = 0) : p = 0 := by
  by_contra hp0
  set n := p.natDegree with hn
  have hcoeff : (aeval (jqModC K) p).coeff (-(n : ℤ)) = p.coeff n := by
    rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single n]
    · rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        coeff_jqModC_pow_self, mul_one]
    · intro i hi hin
      have hilt : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        coeff_jqModC_pow_of_lt K (by omega), mul_zero]
    · intro hn'
      exact absurd (Finset.self_mem_range_succ n) hn'
  rw [hp, HahnSeries.coeff_zero] at hcoeff
  exact hp0 (leadingCoeff_eq_zero.mp hcoeff.symm)

theorem transcendental_jqModC : Transcendental K (jqModC K) :=
  transcendental_iff.mpr fun _ hp => eq_zero_of_aeval_jqModC_eq_zero K hp

theorem pow_ne_jqModC (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (u : LaurentSeries K) : u ^ ℓ ≠ jqModC K := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
  simp only [coeff_jqModC_neg_one] at h1
  rw [pow_char_eq_coeffMap_frobenius_qExpand ℓ u, coeffMap_coeff,
    qExpand_coeff_of_not_dvd ℓ u ?_, map_zero] at h1
  · exact zero_ne_one h1
  · intro hdvd
    have h2 : (ℓ : ℤ) ∣ 1 := (Int.dvd_neg).mp hdvd
    have h3 : ℓ = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h2
    exact (Fact.out : ℓ.Prime).one_lt.ne' h3

end JBar

section ModularPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

variable (R) in

def evalAtJC : ℤ[X] →+* LaurentSeries R := eval₂RingHom (Int.castRingHom _) (jqModC R)

@[scoped simp]
theorem evalAtJC_X : evalAtJC R X = jqModC R := by simp [evalAtJC]

theorem coeffMap_comp_evalAtJC (f : R →+* S) : (coeffMap f).comp (evalAtJC R) = evalAtJC S :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [coeffMap_jqModC])

theorem coeffMap_eval₂_evalAtJC (f : R →+* S) (Φ : Polynomial (Polynomial ℤ)) (N : ℕ) [NeZero N] :
    coeffMap f (Φ.eval₂ (evalAtJC R) (jqNModC R N)) = Φ.eval₂ (evalAtJC S) (jqNModC S N) := by
  rw [hom_eval₂, coeffMap_comp_evalAtJC, coeffMap_jqNModC]

theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem evalAtJ_eq : evalAtJ = evalAtJC ℚ := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [evalAtJ_X, evalAtJC_X, jqModC_rat]

theorem modularPolynomial_eval₂_eq_zero {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (R : Type*) [CommRing R] : data.Φ.eval₂ (evalAtJC R) (jqNModC R N) = 0 := by
  have hQ : data.Φ.eval₂ (evalAtJC ℚ) (jqNModC ℚ N) = 0 := by
    rw [← evalAtJ_eq, jqNModC_rat]; exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (evalAtJC ℤ) (jqNModC ℤ N) = 0 := by
    apply coeffMap_injective (f := Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [coeffMap_eval₂_evalAtJC, hQ, map_zero]
  rw [← coeffMap_eval₂_evalAtJC (Int.castRingHom R), hZ, map_zero]

end ModularPolynomial

section FunctionField

variable (K : Type*) [Field K] (N : ℕ)

def jGen : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

@[scoped simp] theorem coe_jGen : (jGen K N : LaurentSeries K) = jqModC K := rfl

def jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) : modularFunctionFieldFullC K N :=
  ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩

@[scoped simp] theorem coe_jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (jGenD K N d hd : LaurentSeries K) = qExpand K d (jqModC K) := rfl

theorem transcendental_jGen : Transcendental K (jGen K N) := by
  rw [← transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (modularFunctionFieldFullC K N) (LaurentSeries K))]
  exact transcendental_jqModC K

def gensC : Set (modularFunctionFieldFullC K N) := Subtype.val ⁻¹' divisorExpansionsC K N

theorem image_gensC : Subtype.val '' gensC K N = divisorExpansionsC K N := by
  rw [gensC, Set.image_preimage_eq_iff]
  rintro x ⟨d, hne, hd, rfl⟩
  exact ⟨⟨_, @jqModCd_mem_full K _ N d hne hd⟩, rfl⟩

theorem gensC_finite [NeZero N] : (gensC K N).Finite := by
  classical
  let g : N.divisors → modularFunctionFieldFullC K N := fun d =>
    haveI : NeZero (d : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pos_of_mem_divisors d.2)⟩
    ⟨qExpand K d (jqModC K), jqModCd_mem_full K N (Nat.dvd_of_mem_divisors d.2)⟩
  refine (Set.finite_range g).subset ?_
  rintro ⟨x, hx⟩ ⟨d, hne, hd, rfl⟩
  refine ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, NeZero.ne N⟩⟩, Subtype.ext ?_⟩
  exact qExpand_congr rfl _

theorem adjoin_gensC_eq_top : adjoin K (gensC K N) = ⊤ := by
  apply lift_injective
  have h1 := IntermediateField.lift_adjoin K (modularFunctionFieldFullC K N) (gensC K N)
  have h2 := IntermediateField.lift_top K (modularFunctionFieldFullC K N)
  rw [image_gensC] at h1
  exact h1.trans h2.symm

theorem adjoin_adjoin_gensC_eq_top : adjoin K⟮jGen K N⟯ (gensC K N) = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [restrictScalars_adjoin, restrictScalars_top]
  refine le_antisymm le_top ?_
  rw [← adjoin_gensC_eq_top]
  exact adjoin.mono K _ _ Set.subset_union_right

theorem isIntegral_jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) : IsIntegral K⟮jGen K N⟯ (jGenD K N d hd) := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData d
  let e : ℤ[X] →+* K⟮jGen K N⟯ := eval₂RingHom (Int.castRingHom _) (AdjoinSimple.gen K (jGen K N))
  refine ⟨data.Φ.map e, data.monic.map e, ?_⟩
  rw [eval₂_map]
  apply FaithfulSMul.algebraMap_injective (modularFunctionFieldFullC K N) (LaurentSeries K)
  rw [map_zero, hom_eval₂]
  have hcomp : ((algebraMap (modularFunctionFieldFullC K N) (LaurentSeries K)).comp
      ((algebraMap K⟮jGen K N⟯ (modularFunctionFieldFullC K N)).comp e)) = evalAtJC K := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [e, evalAtJC]
  rw [hcomp]
  exact modularPolynomial_eval₂_eq_zero data K

theorem isIntegral_of_mem_gensC {y : modularFunctionFieldFullC K N} (hy : y ∈ gensC K N) :
    IsIntegral K⟮jGen K N⟯ y := by
  obtain ⟨d, hne, hd, hyd⟩ := hy
  have : y = jGenD K N d hd := Subtype.ext hyd
  rw [this]
  exact isIntegral_jGenD K N d hd

theorem finiteDimensional_adjoin_jGen [NeZero N] :
    FiniteDimensional K⟮jGen K N⟯ (modularFunctionFieldFullC K N) := by
  haveI : Finite (gensC K N) := (gensC_finite K N).to_subtype
  haveI : FiniteDimensional K⟮jGen K N⟯ (adjoin K⟮jGen K N⟯ (gensC K N)) :=
    finiteDimensional_adjoin fun y hy => isIntegral_of_mem_gensC K N hy
  rw [adjoin_adjoin_gensC_eq_top] at this
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := K⟮jGen K N⟯) (E := modularFunctionFieldFullC K N)).toLinearEquiv

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

omit [PerfectRing K ℓ] in

theorem pow_ne_jGen (u : modularFunctionFieldFullC K N) : u ^ ℓ ≠ jGen K N := fun h =>
  pow_ne_jqModC K ℓ (u : LaurentSeries K) (by rw [← coe_jGen K N, ← h]; rfl)

omit [PerfectRing K ℓ] [Fact ℓ.Prime] in
theorem charP_full : CharP (modularFunctionFieldFullC K N) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (modularFunctionFieldFullC K N)).injective ℓ

include ℓ in

theorem isSeparable_adjoin_jGen :
    Algebra.IsSeparable K⟮jGen K N⟯ (modularFunctionFieldFullC K N) := by
  haveI := charP_full K N (ℓ := ℓ)
  haveI : Algebra.IsSeparable K⟮jGen K N⟯ (adjoin K⟮jGen K N⟯ (gensC K N)) := by
    rw [isSeparable_adjoin_iff_isSeparable]
    intro y hy
    exact isSeparable_of_forall_pow_ne ℓ (pow_ne_jGen K N) (isIntegral_of_mem_gensC K N hy)
  rw [adjoin_adjoin_gensC_eq_top] at this
  exact Algebra.IsSeparable.of_algHom _ _
    (IntermediateField.topEquiv (F := K⟮jGen K N⟯) (E := modularFunctionFieldFullC K N)).symm.toAlgHom

end FunctionField

end W4FA
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

end
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "Polynomial IntermediateField HahnSeries ModularCurve~coeffMap_injective AlgebraicCurve"

namespace W4FA

section Sigma

variable (K : Type*) [Field K] (N : ℕ) {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

abbrev FF : Type _ := modularFunctionFieldFullC K N

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in

theorem coeffMap_mem_full (g : K →+* K) {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldFullC K N) :
    coeffMap g x ∈ modularFunctionFieldFullC K N := by
  have hx' : x ∈ (modularFunctionFieldFullC K N).toSubfield := hx
  rw [modularFunctionFieldFullC, adjoin_toSubfield] at hx'
  have key : (Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ divisorExpansionsC K N)).map
      (coeffMap g) ≤ (modularFunctionFieldFullC K N).toSubfield := by
    rw [RingHom.map_field_closure, Subfield.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨d, hne, hd, rfl⟩
    · rw [coeffMap_algebraMap]
      exact (modularFunctionFieldFullC K N).algebraMap_mem _
    · haveI := hne
      change coeffMap g (qExpand K d (jqModC K)) ∈ modularFunctionFieldFullC K N
      rw [coeffMap_qExpand, coeffMap_jqModC]
      exact jqModCd_mem_full K N hd
  exact key ⟨x, hx', rfl⟩

variable (ℓ)

def sigmaRingHom : FF K N →+* FF K N where
  toFun x := ⟨coeffMap (frobenius K ℓ) x, coeffMap_mem_full K N _ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def sigmaInvRingHom : FF K N →+* FF K N where
  toFun x := ⟨coeffMap ((frobeniusEquiv K ℓ).symm : K →+* K) x, coeffMap_mem_full K N _ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_sigmaRingHom (x : FF K N) :
    (sigmaRingHom K N ℓ x : LaurentSeries K) = coeffMap (frobenius K ℓ) x := rfl

@[scoped simp] theorem coe_sigmaInvRingHom (x : FF K N) :
    (sigmaInvRingHom K N ℓ x : LaurentSeries K) = coeffMap ((frobeniusEquiv K ℓ).symm : K →+* K) x := rfl

def sigma : FF K N ≃+* FF K N :=
  { sigmaRingHom K N ℓ with
    invFun := sigmaInvRingHom K N ℓ
    left_inv := fun x => Subtype.ext <| by
      change coeffMap _ (coeffMap _ (x : LaurentSeries K)) = (x : LaurentSeries K)
      rw [coeffMap_coeffMap]
      convert coeffMap_id (x : LaurentSeries K)
      ext a; exact (frobeniusEquiv K ℓ).symm_apply_apply a
    right_inv := fun x => Subtype.ext <| by
      change coeffMap _ (coeffMap _ (x : LaurentSeries K)) = (x : LaurentSeries K)
      rw [coeffMap_coeffMap]
      convert coeffMap_id (x : LaurentSeries K)
      ext a; exact (frobeniusEquiv K ℓ).apply_symm_apply a }

@[scoped simp] theorem coe_sigma (x : FF K N) : (sigma K N ℓ x : LaurentSeries K) = coeffMap (frobenius K ℓ) x := rfl

theorem frobeniusModL_sigma (x : FF K N) : frobeniusModL K N ℓ (sigma K N ℓ x) = x ^ ℓ := by
  apply Subtype.ext
  rw [coe_frobeniusModL, coe_sigma, ← coeffMap_qExpand]
  push_cast
  exact (pow_char_eq_coeffMap_frobenius_qExpand ℓ (x : LaurentSeries K)).symm

theorem frobeniusModL_eq_pow (y : FF K N) : frobeniusModL K N ℓ y = ((sigma K N ℓ).symm y) ^ ℓ := by
  conv_lhs => rw [← (sigma K N ℓ).apply_symm_apply y]
  exact frobeniusModL_sigma K N ℓ _

theorem mem_range_frobeniusModL_iff (y : FF K N) :
    y ∈ Set.range (frobeniusModL K N ℓ) ↔ ∃ u : FF K N, u ^ ℓ = y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(sigma K N ℓ).symm x, (frobeniusModL_eq_pow K N ℓ x).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨sigma K N ℓ u, frobeniusModL_sigma K N ℓ u⟩

theorem sigma_algebraMap (a : K) : sigma K N ℓ (algebraMap K (FF K N) a) = algebraMap K (FF K N) (a ^ ℓ) := by
  apply Subtype.ext
  change coeffMap (frobenius K ℓ) (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) (a ^ ℓ)
  rw [coeffMap_algebraMap, frobenius_def]

def sigmaSL : SemilinearAut K (FF K N) :=
  ⟨(sigma K N ℓ, frobeniusEquiv K ℓ), fun a => by
    change sigma K N ℓ (algebraMap K (FF K N) a) = algebraMap K (FF K N) (frobeniusEquiv K ℓ a)
    rw [sigma_algebraMap, frobeniusEquiv_apply, frobenius_def]⟩

@[scoped simp] theorem sigmaSL_smul (x : FF K N) : sigmaSL K N ℓ • x = sigma K N ℓ x := rfl

theorem sigmaSL_inv_smul (x : FF K N) : (sigmaSL K N ℓ)⁻¹ • x = (sigma K N ℓ).symm x := rfl

end Sigma
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

section Places

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

theorem pow_mem_valuationSubring_iff {F : Type*} [Field F] (O : ValuationSubring F) {n : ℕ} (hn : n ≠ 0)
    (u : F) : u ^ n ∈ O ↔ u ∈ O := by
  rw [← O.valuation_le_one_iff, ← O.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hn

theorem frobeniusPlaceModL_eq_smul (w : Place K (FF K N)) :
    frobeniusPlaceModL K N ℓ w = sigmaSL K N ℓ • w := by
  apply Place.ext
  ext x
  rw [mem_frobeniusPlaceModL_iff, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, sigmaSL_inv_smul, frobeniusModL_eq_pow]
  exact pow_mem_valuationSubring_iff _ (Fact.out : ℓ.Prime).ne_zero _

theorem restrictAlong_frobenius_eq_smul (w : Place K (FF K N)) :
    w.restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) = sigmaSL K N ℓ • w :=
  frobeniusPlaceModL_eq_smul K N ℓ w

theorem ord_frobeniusModL (w : Place K (FF K N)) (f : FF K N) :
    w.ord (frobeniusModL K N ℓ f) = ℓ * w.ord ((sigma K N ℓ).symm f) := by
  rw [frobeniusModL_eq_pow, ← zpow_natCast, Place.ord_zpow]

theorem ramificationIndexAlong_frobenius (w : Place K (FF K N)) :
    Place.ramificationIndexAlong (frobeniusModL K N ℓ) w = ℓ := by
  letI := algebraAlong (frobeniusModL K N ℓ)
  haveI := isIntegral_along (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
  have hℓ : ℓ.Prime := Fact.out
  change w.ramificationIndex (FF K N) = ℓ
  have halg : ∀ f : FF K N, algebraMap (FF K N) (FF K N) f = frobeniusModL K N ℓ f := fun _ => rfl
  apply le_antisymm
  ·
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    have hπ1 : w.ord (π : FF K N) = 1 := w.ord_coe_irreducible hπ
    have hπ0 : (π : FF K N) ≠ 0 := fun h => by simp [h] at hπ1
    have hσπ0 : sigma K N ℓ π ≠ 0 := (map_ne_zero_iff _ (sigma K N ℓ).injective).mpr hπ0
    have hord : w.ord (algebraMap (FF K N) (FF K N) (sigma K N ℓ π)) = ℓ := by
      rw [halg, ord_frobeniusModL, RingEquiv.symm_apply_apply, hπ1, mul_one]
    have h := Place.ramificationIndex_le_ord (F := FF K N) w hσπ0 (by rw [hord]; exact_mod_cast hℓ.pos)
    rw [hord] at h
    exact_mod_cast h
  ·
    obtain ⟨f, hf0, hfe⟩ := Place.exists_ord_eq_ramificationIndex (F := FF K N) w
    have hpos := Place.ramificationIndex_pos (F := FF K N) w
    rw [halg, ord_frobeniusModL] at hfe
    have hk : 0 < w.ord ((sigma K N ℓ).symm f) := by
      by_contra hk
      push Not at hk
      have : (ℓ : ℤ) * w.ord ((sigma K N ℓ).symm f) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hk
      omega
    have : (ℓ : ℤ) * 1 ≤ (ℓ : ℤ) * w.ord ((sigma K N ℓ).symm f) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    omega

variable [hP : HasPrincipalDivisors K (FF K N)]

theorem fiberAlong_frobenius (v : Place K (FF K N)) :
    Place.fiberAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) v = {(sigmaSL K N ℓ)⁻¹ • v} := by
  ext W
  rw [Place.mem_fiberAlong, Finset.mem_singleton, restrictAlong_frobenius_eq_smul, smul_eq_iff_eq_inv_smul]

end Places
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

section Degree

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

abbrev PP : IntermediateField K (FF K N) := (frobeniusModL K N ℓ).fieldRange

theorem mem_PP_iff (y : FF K N) : y ∈ PP K N ℓ ↔ ∃ u : FF K N, u ^ ℓ = y := by
  rw [AlgHom.mem_fieldRange, ← mem_range_frobeniusModL_iff, Set.mem_range]

def isoPP : FF K N ≃+* PP K N ℓ :=
  RingEquiv.ofBijective
    ((frobeniusModL K N ℓ).toRingHom.codRestrict (PP K N ℓ).toSubring
      fun x => AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    ⟨fun x y h => frobeniusModL_injective K N ℓ (congrArg Subtype.val h),
     fun ⟨y, hy⟩ => by
       obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
       exact ⟨x, rfl⟩⟩

@[scoped simp] theorem coe_isoPP (x : FF K N) : (isoPP K N ℓ x : FF K N) = frobeniusModL K N ℓ x := rfl

omit [NeZero N] in
theorem charP_FF : CharP (FF K N) ℓ := charP_full K N

theorem jGen_not_mem_PP : jGen K N ∉ PP K N ℓ := fun h => by
  obtain ⟨u, hu⟩ := (mem_PP_iff K N ℓ _).mp h
  exact pow_ne_jGen K N u hu

def jPowP : PP K N ℓ := ⟨jGen K N ^ ℓ, (mem_PP_iff K N ℓ _).mpr ⟨_, rfl⟩⟩

@[scoped simp] theorem coe_jPowP : (jPowP K N ℓ : FF K N) = jGen K N ^ ℓ := rfl

theorem minpoly_PP_jGen :
    minpoly (PP K N ℓ) (jGen K N) = X ^ ℓ - Polynomial.C (jPowP K N ℓ) := by
  haveI := charP_FF K N ℓ
  have hℓ : ℓ.Prime := Fact.out
  symm
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ (monic_X_pow_sub_C _ hℓ.ne_zero)
  · refine X_pow_sub_C_irreducible_of_prime hℓ fun b hb => ?_
    apply jGen_not_mem_PP K N ℓ
    have hb' : (b : FF K N) ^ ℓ = jGen K N ^ ℓ := by
      have h := congrArg Subtype.val hb
      simpa using h
    have : (b : FF K N) = jGen K N := by
      have h := sub_pow_char (b : FF K N) (jGen K N) (p := ℓ)
      rw [hb', sub_self] at h
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h.symm.symm)
    rw [← this]; exact b.2
  · simp

theorem isIntegral_PP_jGen : IsIntegral (PP K N ℓ) (jGen K N) :=
  ⟨X ^ ℓ - Polynomial.C (jPowP K N ℓ),
    monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero, by simp⟩

theorem finrank_PP_adjoin_jGen : Module.finrank (PP K N ℓ) (PP K N ℓ)⟮jGen K N⟯ = ℓ := by
  rw [adjoin.finrank (isIntegral_PP_jGen K N ℓ), minpoly_PP_jGen, natDegree_X_pow_sub_C]

def MM : IntermediateField K (FF K N) := restrictScalars K (PP K N ℓ)⟮jGen K N⟯

theorem mem_MM_iff (y : FF K N) : y ∈ MM K N ℓ ↔ y ∈ (PP K N ℓ)⟮jGen K N⟯ := Iff.rfl

theorem PP_le_MM : PP K N ℓ ≤ MM K N ℓ := fun p hp =>
  (mem_MM_iff K N ℓ p).mpr ((PP K N ℓ)⟮jGen K N⟯.algebraMap_mem ⟨p, hp⟩)

theorem jGen_mem_MM : jGen K N ∈ MM K N ℓ :=
  (mem_MM_iff K N ℓ _).mpr (mem_adjoin_simple_self _ _)

theorem mem_MM_of_mem_gensC {y : FF K N} (hy : y ∈ gensC K N) : y ∈ MM K N ℓ := by
  haveI := charP_FF K N ℓ
  haveI : CharP (MM K N ℓ) ℓ := IntermediateField.charP _ ℓ
  haveI : ExpChar (MM K N ℓ) ℓ := ExpChar.prime Fact.out

  have hsepK : IsSeparable K⟮jGen K N⟯ y := by
    haveI := isSeparable_adjoin_jGen K N (ℓ := ℓ)
    exact Algebra.IsSeparable.isSeparable _ y
  have hle : K⟮jGen K N⟯ ≤ MM K N ℓ := adjoin_simple_le_iff.mpr (jGen_mem_MM K N ℓ)
  let incl : K⟮jGen K N⟯ →+* MM K N ℓ := (IntermediateField.inclusion hle).toRingHom
  have hsep2 : IsSeparable (MM K N ℓ) y := by
    have hm : (minpoly K⟮jGen K N⟯ y).Separable := hsepK
    have hroot : aeval y ((minpoly K⟮jGen K N⟯ y).map incl) = 0 := by
      rw [aeval_def, eval₂_map, ← minpoly.aeval K⟮jGen K N⟯ y, aeval_def]
      rfl
    exact (hm.map (f := incl)).of_dvd (minpoly.dvd _ _ hroot)

  have hperf : y ∈ perfectClosure (MM K N ℓ) (FF K N) := by
    rw [mem_perfectClosure_iff_pow_mem ℓ]
    refine ⟨1, ⟨y ^ ℓ, PP_le_MM K N ℓ ((mem_PP_iff K N ℓ _).mpr ⟨y, rfl⟩)⟩, ?_⟩
    rw [pow_one]; rfl
  have hsc : y ∈ separableClosure (MM K N ℓ) (FF K N) := mem_separableClosure_iff.mpr hsep2
  have hbot : y ∈ (⊥ : IntermediateField (MM K N ℓ) (FF K N)) := by
    rw [← separableClosure_inf_perfectClosure]; exact ⟨hsc, hperf⟩
  rw [IntermediateField.mem_bot] at hbot
  obtain ⟨⟨z, hz⟩, rfl⟩ := hbot
  exact hz

theorem PP_adjoin_jGen_eq_top : (PP K N ℓ)⟮jGen K N⟯ = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [restrictScalars_top]
  refine le_antisymm le_top ?_
  rw [← adjoin_gensC_eq_top, adjoin_le_iff]
  exact fun y hy => mem_MM_of_mem_gensC K N ℓ hy

theorem finrank_PP : Module.finrank (PP K N ℓ) (FF K N) = ℓ := by
  rw [← finrank_top', ← PP_adjoin_jGen_eq_top, finrank_PP_adjoin_jGen]

scoped instance finite_PP : Module.Finite (PP K N ℓ) (FF K N) :=
  Module.finite_of_finrank_pos (by rw [finrank_PP]; exact (Fact.out : ℓ.Prime).pos)

theorem isoPP_compat :
    (algebraMap (PP K N ℓ) (FF K N)).comp (isoPP K N ℓ).toRingHom =
      (RingEquiv.refl (FF K N)).toRingHom.comp
        (@algebraMap (FF K N) (FF K N) _ _ (algebraAlong (frobeniusModL K N ℓ))) :=
  RingHom.ext fun _ => rfl

theorem finrankAlong_frobenius : finrankAlong K (frobeniusModL K N ℓ) = ℓ := by
  refine Eq.trans ?_ (finrank_PP K N ℓ)
  exact @Algebra.finrank_eq_of_equiv_equiv (FF K N) (FF K N) _ _ (algebraAlong (frobeniusModL K N ℓ))
    (PP K N ℓ) (FF K N) _ _ _ (isoPP K N ℓ) (RingEquiv.refl _) (isoPP_compat K N ℓ)

theorem finiteAlong_frobenius : FiniteAlong K (frobeniusModL K N ℓ) :=
  @Module.Finite.of_equiv_equiv (PP K N ℓ) (FF K N) (FF K N) (FF K N) _ _ _ _ _
    (algebraAlong (frobeniusModL K N ℓ)) (isoPP K N ℓ).symm (RingEquiv.refl _)
    (by
      apply RingHom.ext; intro x
      obtain ⟨y, rfl⟩ := (isoPP K N ℓ).surjective x
      change (frobeniusModL K N ℓ) ((isoPP K N ℓ).symm (isoPP K N ℓ y)) = (isoPP K N ℓ y : FF K N)
      rw [RingEquiv.symm_apply_apply]; rfl)
    (finite_PP K N ℓ)

end Degree
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

end W4FA
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

end
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "Polynomial IntermediateField HahnSeries ModularCurve~coeffMap_injective AlgebraicCurve"

namespace W4FA

section Norm

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

theorem minpoly_PP_of_not_mem {f : FF K N} (hf : f ∉ PP K N ℓ) :
    minpoly (PP K N ℓ) f =
      X ^ ℓ - Polynomial.C (⟨f ^ ℓ, (mem_PP_iff K N ℓ _).mpr ⟨f, rfl⟩⟩ : PP K N ℓ) := by
  haveI := charP_FF K N ℓ
  have hℓ : ℓ.Prime := Fact.out
  symm
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ (monic_X_pow_sub_C _ hℓ.ne_zero)
  · refine X_pow_sub_C_irreducible_of_prime hℓ fun b hb => ?_
    apply hf
    have hb' : (b : FF K N) ^ ℓ = f ^ ℓ := by
      have h := congrArg Subtype.val hb
      simpa using h
    have : (b : FF K N) = f := by
      have h := sub_pow_char (b : FF K N) f (p := ℓ)
      rw [hb', sub_self] at h
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h.symm.symm)
    rw [← this]; exact b.2
  · simp

theorem coe_norm_PP (f : FF K N) : ((Algebra.norm (PP K N ℓ) f : PP K N ℓ) : FF K N) = f ^ ℓ := by
  haveI := charP_FF K N ℓ
  haveI : CharP (PP K N ℓ) ℓ := IntermediateField.charP _ ℓ
  have hℓ : ℓ.Prime := Fact.out
  by_cases hf : f ∈ PP K N ℓ
  ·
    have hfp : algebraMap (PP K N ℓ) (FF K N) ⟨f, hf⟩ = f := IntermediateField.algebraMap_apply _ _
    have h := Algebra.norm_algebraMap (S := FF K N) (⟨f, hf⟩ : PP K N ℓ)
    rw [hfp, finrank_PP] at h
    rw [h]
    exact SubmonoidClass.coe_pow _ _
  ·
    have hint : IsIntegral (PP K N ℓ) f := IsIntegral.of_finite _ f
    have hdeg : (minpoly (PP K N ℓ) f).natDegree = ℓ := by
      rw [minpoly_PP_of_not_mem K N ℓ hf, natDegree_X_pow_sub_C]
    have h1 : Module.finrank (PP K N ℓ) (PP K N ℓ)⟮f⟯ = ℓ := by
      rw [adjoin.finrank hint, hdeg]
    have htop : (PP K N ℓ)⟮f⟯ = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [h1, finrank_top', finrank_PP])
    have h2 : Module.finrank (PP K N ℓ)⟮f⟯ (FF K N) = 1 := finrank_eq_one_iff_eq_top.mpr htop
    rw [Algebra.norm_eq_norm_adjoin, h2, pow_one]
    have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hint)
    have hgen : (adjoin.powerBasis hint).gen = AdjoinSimple.gen (PP K N ℓ) f := adjoin.powerBasis_gen hint
    have hdim : (adjoin.powerBasis hint).dim = ℓ := by rw [adjoin.powerBasis_dim, hdeg]
    have hmin : minpoly (PP K N ℓ) (AdjoinSimple.gen (PP K N ℓ) f) = minpoly (PP K N ℓ) f := minpoly_gen _ f
    rw [hgen, hdim, hmin, minpoly_PP_of_not_mem K N ℓ hf] at hpb
    rw [hpb, neg_one_pow_char, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_zero,
      if_neg (Ne.symm hℓ.ne_zero), zero_sub, neg_mul_neg, one_mul]

theorem frobeniusModL_normAlong (f : FF K N) :
    frobeniusModL K N ℓ (@Algebra.norm (FF K N) (FF K N) _ _ (algebraAlong (frobeniusModL K N ℓ)) f) =
      f ^ ℓ := by
  have h := @Algebra.norm_eq_of_equiv_equiv (FF K N) (FF K N) (PP K N ℓ) (FF K N) _ _ _ _
    (algebraAlong (frobeniusModL K N ℓ)) _ (isoPP K N ℓ) (RingEquiv.refl _) (isoPP_compat K N ℓ) f
  rw [h]
  change ((isoPP K N ℓ) ((isoPP K N ℓ).symm _) : FF K N) = f ^ ℓ
  rw [RingEquiv.apply_symm_apply]
  exact coe_norm_PP K N ℓ f

end Norm
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

section Inputs

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
variable [hC : IsCurveOver K (FF K N)]

scoped instance perfectRing_of_isAlgClosed : PerfectRing K ℓ :=
  haveI := IsAlgClosed.perfectField K
  PerfectField.toPerfectRing ℓ

theorem deg_eq_one (w : Place K (FF K N)) : w.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed w

theorem inertiaDegAlong_frobenius (w : Place K (FF K N)) :
    Place.inertiaDegAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) w = 1 := by
  letI := algebraAlong (frobeniusModL K N ℓ)
  haveI := isScalarTower_along (frobeniusModL K N ℓ)
  haveI := isIntegral_along (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
  have h := Place.deg_restrict_mul_inertiaDeg (F := FF K N) w
  rw [deg_eq_one, deg_eq_one, one_mul] at h
  exact h

theorem fundamentalIdentityAlong_frobenius :
    FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) := by
  letI := algebraAlong (frobeniusModL K N ℓ)
  haveI := isScalarTower_along (frobeniusModL K N ℓ)
  haveI := isIntegral_along (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
  refine ⟨fun v => ?_⟩
  change ∑ w ∈ Place.fiberAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) v,
      (Place.ramificationIndexAlong (frobeniusModL K N ℓ) w : ℤ) * (w.deg : ℤ) =
    (finrankAlong K (frobeniusModL K N ℓ) : ℤ) * (v.deg : ℤ)
  rw [fiberAlong_frobenius, Finset.sum_singleton, ramificationIndexAlong_frobenius, deg_eq_one, deg_eq_one,
    finrankAlong_frobenius]

theorem normFormulaAlong_frobenius :
    NormFormulaAlong K (frobeniusModL K N ℓ) (finiteAlong_frobenius K N ℓ) := by
  classical
  letI := algebraAlong (frobeniusModL K N ℓ)
  haveI := isScalarTower_along (frobeniusModL K N ℓ)
  haveI := isIntegral_along (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
  intro f hf D hD v
  have hℓ : ℓ.Prime := Fact.out
  set w₀ : Place K (FF K N) := (sigmaSL K N ℓ)⁻¹ • v with hw₀

  have hres : ∀ w : Place K (FF K N), w.restrict (FF K N) = v ↔ w = w₀ := fun w => by
    change w.restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) = v ↔ _
    rw [restrictAlong_frobenius_eq_smul, smul_eq_iff_eq_inv_smul]
  have hLHS : Divisor.pushforward (FF K N) D v = w₀.ord f := by
    rw [Divisor.pushforward_apply]
    have : ∀ w ∈ D.support, (if w.restrict (FF K N) = v then D w * (w.inertiaDeg (FF K N) : ℤ) else 0) =
        (if w₀ = w then D w else 0) := fun w _ => by
      have hf1 : w.inertiaDeg (FF K N) = 1 := inertiaDegAlong_frobenius K N ℓ w
      simp only [hres w, hf1, Nat.cast_one, mul_one, eq_comm]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    split_ifs with hmem
    · exact hD w₀
    · rw [Finsupp.mem_support_iff, not_not] at hmem
      rw [← hD w₀, hmem]

  have hw₀res : w₀.restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) = v := by
    rw [restrictAlong_frobenius_eq_smul, hw₀, smul_inv_smul]
  have hRHS : (ℓ : ℤ) * v.ord (Algebra.norm (FF K N) f) = ℓ * w₀.ord f := by
    have h := Place.ord_restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) w₀
      (Algebra.norm (FF K N) f)
    rw [hw₀res, ramificationIndexAlong_frobenius, frobeniusModL_normAlong, ← zpow_natCast,
      Place.ord_zpow] at h
    exact h.symm
  rw [hLHS]
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  exact (mul_left_cancel₀ hℓ0 hRHS).symm

end Inputs
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

end W4FA
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

end
p2m_reactivate "P2MW.S_ModularCurve_frobeniusInputsModL.W4FA"

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (N : ℕ) [NeZero N] :
    ModularCurve.FrobeniusInputsModL K N ℓ := by
  haveI : AlgebraicCurve.IsCurveOver K (W4FA.FF K N) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K (W4FA.FF K N) (W4FA.jGen K N)
      (W4FA.transcendental_jGen K N) (W4FA.finiteDimensional_adjoin_jGen K N)
      (W4FA.isSeparable_adjoin_jGen K N (ℓ := ℓ))
  haveI : AlgebraicCurve.HasPrincipalDivisors K (ModularCurve.modularFunctionFieldFullC K N) :=
    AlgebraicCurve.IsCurveOver.hasPrincipalDivisors
  exact ModularCurve.frobeniusInputsModL_intro (W4FA.finiteAlong_frobenius K N ℓ)
    (W4FA.fundamentalIdentityAlong_frobenius K N ℓ) (W4FA.normFormulaAlong_frobenius K N ℓ)

end S_ModularCurve_frobeniusInputsModL
end P2MW
export P2MW.S_ModularCurve_frobeniusInputsModL (solution)
