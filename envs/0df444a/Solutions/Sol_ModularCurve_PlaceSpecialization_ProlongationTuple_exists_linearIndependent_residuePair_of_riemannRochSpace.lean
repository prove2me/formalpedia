-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_linearIndependent_residuePair_of_riemannRochSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8f436d32-bbc1-57f3-a5db-850c260def65

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_linearIndependent_residuePair_of_riemannRochSpace
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace MovN

section AlphaGeneric

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem Alpha.ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf

private theorem Alpha.mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

private theorem Alpha.ord_neg_of_ord_sub_neg (v : Place K F) {f g : F} (hg : g ∈ v.toValuationSubring)
    (h : v.ord (f - g) < 0) : v.ord f < 0 := by
  rw [← Place.not_adicValuation_le_one_iff] at h ⊢
  intro hf
  apply h
  calc v.adicValuation (f - g) ≤ max (v.adicValuation f) (v.adicValuation g) := Valuation.map_sub _ _ _
    _ ≤ 1 := max_le hf (v.adicValuation_le_one_of_mem hg)

private theorem Alpha.ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (Place.hasValue_algebraMap v c).ord_eq_zero hc

private theorem Alpha.ord_smul_const (v : Place K F) {c : K} (hc : c ≠ 0) (f : F) : v.ord (c • f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, Alpha.ord_algebraMap, zero_add]

private theorem Alpha.ord_pow (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have h := v.ord_zpow f n
  rwa [zpow_natCast] at h

private theorem Alpha.ord_sub_pos_of_hasValue (v : Place K F) {g : F} {c : K} (h : v.HasValue g c)
    (hne : g ≠ algebraMap K F c) : 0 < v.ord (g - algebraMap K F c) := by
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem h.mem (v.algebraMap_mem' c)
  have hne0 : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hne
  have h0 : 0 ≤ v.ord (g - algebraMap K F c) := Alpha.ord_nonneg_of_mem v hne0 hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hne0 heq.symm
    have e : (⟨g - algebraMap K F c, hm⟩ : v.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K v.toValuationSubring c := Subtype.ext rfl
    have hres : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hm⟩ = 0 := by
      rw [e, map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

private theorem Alpha.exists_hasValue_of_deg_eq_one (v : Place K F) (hdeg : v.deg = 1) {g : F}
    (hg : g ∈ v.toValuationSubring) : ∃ a : K, v.HasValue g a := by
  have h1 : (1 : v.ResidueField) ≠ 0 := one_ne_zero
  have hsurj : Function.Surjective (algebraMap K v.ResidueField) := by
    intro x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) h1).mp hdeg x
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hsurj hg
  exact ⟨a, ha⟩

private theorem Alpha.inv_mem_of_isUnit {S : ValuationSubring F} {x : F} (hx : x ∈ S)
    (hu : IsUnit (⟨x, hx⟩ : S)) : x⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : F) = x := by rw [hu]
  have h1 : x * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  have hinv : (((u⁻¹ : Sˣ) : S) : F) = x⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  exact hinv ▸ SetLike.coe_mem _

private theorem Alpha.coe_unit_inv {S : ValuationSubring F} (u : Sˣ) :
    (((u⁻¹ : Sˣ) : S) : F) = ((u : S) : F)⁻¹ := by
  have h1 : ((u : S) : F) * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  exact (inv_eq_of_mul_eq_one_right h1).symm

private theorem Alpha.exists_coeffMap_subtype_eq {L : Type*} [Field L] (A : ValuationSubring L)
    (x : LaurentSeries L) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq]
    rw [← ZeroMemClass.coe_eq_zero]
  · ext n
    rfl

private theorem Alpha.coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) :=
  HahnSeries.map_C r f

private theorem Alpha.coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

end AlphaGeneric

section AlphaLevel

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]

local notation "F" => modularFunctionFieldBar (N * q)
local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "w" => ProlongationTuple.atkinLehnerBar N q
local notation "J" => ProlongationTuple.jFun N q
local notation "JQ" => ProlongationTuple.jQFun N q

private theorem Alpha.neZero : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩

private theorem Alpha.w_jFun_and_w_jQFun (hqN : ¬ q ∣ N) : w J = JQ ∧ w JQ = J := by
  have hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨hleg1, hleg2⟩ :=
    geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q (atkinLehnerInvolutionFull N q) hAL
  let jN : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
  have hαj : heckeAlphaBar (AlgebraicClosure ℚ) N q jN = J :=
    Subtype.ext (coe_heckeAlphaBar N q jN)
  have hβj : heckeBetaBar (AlgebraicClosure ℚ) N q jN = JQ :=
    Subtype.ext (coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq).symm
  refine ⟨?_, ?_⟩
  · rw [← hαj, ← hβj]; exact DFunLike.congr_fun hleg1 jN
  · rw [← hαj, ← hβj]; exact DFunLike.congr_fun hleg2 jN

private theorem Alpha.w_jFun (hqN : ¬ q ∣ N) : w J = JQ := (Alpha.w_jFun_and_w_jQFun hqN).1
private theorem Alpha.w_jQFun (hqN : ¬ q ∣ N) : w JQ = J := (Alpha.w_jFun_and_w_jQFun hqN).2
private theorem Alpha.winv_jFun (hqN : ¬ q ∣ N) : w⁻¹ J = JQ := by
  have h := Alpha.w_jQFun (N := N) hqN
  conv_lhs => rw [← h]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

private theorem Alpha.winv_jQFun (hqN : ¬ q ∣ N) : w⁻¹ JQ = J := by
  have h := Alpha.w_jFun (N := N) hqN
  conv_lhs => rw [← h]
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

private theorem Alpha.ord_w (W : Place ℚ̄ F) (g : F) : W.ord (w g) = (w⁻¹ • W).ord g := by
  conv_lhs => rw [← smul_inv_smul w W]
  rw [Place.ord_smul]

private theorem Alpha.ord_winv (W : Place ℚ̄ F) (g : F) : W.ord (w⁻¹ g) = (w • W).ord g := by
  conv_lhs => rw [← inv_smul_smul w W]
  rw [Place.ord_smul]

private theorem Alpha.coe_jFun : ((J : F) : LaurentSeries ℚ̄) = jqModC ℚ̄ := by
  show coeffMap (algebraMap ℚ ℚ̄) jq = _
  rw [← jqModC_rat]
  exact Alpha.coeffMap_jqModC _

private theorem Alpha.coe_jQFun : ((JQ : F) : LaurentSeries ℚ̄) = qExpand ℚ̄ q (jqModC ℚ̄) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  show coeffMap (algebraMap ℚ ℚ̄) (qExpand ℚ q jq) = _
  rw [coeffMap_qExpand, ← jqModC_rat, Alpha.coeffMap_jqModC]

private theorem Alpha.coe_algebraMap (c : ℚ̄) :
    ((algebraMap ℚ̄ F c : F) : LaurentSeries ℚ̄) = HahnSeries.single 0 c := by
  rw [show ((algebraMap ℚ̄ F c : F) : LaurentSeries ℚ̄) = algebraMap ℚ̄ (LaurentSeries ℚ̄) c from rfl,
    algebraMap_laurentSeries_eq_single]

private theorem Alpha.jFun_ne_algebraMap (c : ℚ̄) : (J : F) ≠ algebraMap ℚ̄ F c := by
  intro h
  have h1 := congrArg (fun x : F => (x : LaurentSeries ℚ̄).coeff (-1)) h
  simp only [Alpha.coe_jFun, Alpha.coe_algebraMap] at h1
  rw [HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by decide), coeff_jqModC_neg_one] at h1
  exact one_ne_zero h1

private theorem Alpha.jQFun_ne_algebraMap (c : ℚ̄) : (JQ : F) ≠ algebraMap ℚ̄ F c := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  intro h
  have h1 := congrArg (fun x : F => (x : LaurentSeries ℚ̄).coeff ((q : ℤ) * (-1))) h
  simp only [Alpha.coe_jQFun, Alpha.coe_algebraMap] at h1
  rw [qExpand_coeff_mul, HahnSeries.coeff_single_of_ne, coeff_jqModC_neg_one] at h1
  · exact one_ne_zero h1
  · have : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    omega

private theorem Alpha.jFun_ne_zero : (J : F) ≠ 0 := by simpa using Alpha.jFun_ne_algebraMap (N := N) (q := q) 0
private theorem Alpha.jQFun_ne_zero : (JQ : F) ≠ 0 := by simpa using Alpha.jQFun_ne_algebraMap (N := N) (q := q) 0

private theorem Alpha.eval₂_modularPolynomial (data : ModularPolynomialData q) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) J)).eval JQ = 0 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have key := eval_int_eq_zero_geom ℚ̄ (N := q) data
  set θ : F →+* LaurentSeries ℚ̄ := (modularFunctionFieldBar (N * q)).toSubalgebra.val.toRingHom with hθ
  have hθ' : ∀ x : F, θ x = (x : LaurentSeries ℚ̄) := fun x => rfl
  have hcomp : θ.comp (Polynomial.eval₂RingHom (Int.castRingHom F) J) = evalAtJGeom ℚ̄ := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [evalAtJGeom]
    · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJGeom_X, hθ',
        Alpha.coe_jFun]
  have hJQ : θ JQ = jqNModC (AlgebraicClosure ℚ) q := by
    rw [hθ']
    exact Alpha.coe_jQFun (N := N) (q := q)
  apply Subtype.val_injective
  rw [ZeroMemClass.coe_zero, ← hθ', Polynomial.eval_map, Polynomial.hom_eval₂, hcomp, hJQ]
  exact key

private theorem Alpha.mem_of_eval₂_modularPolynomial (data : ModularPolynomialData q) (W : Place ℚ̄ F) {x y : F}
    (hx : x ∈ W.toValuationSubring)
    (hxy : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x)).eval y = 0) :
    y ∈ W.toValuationSubring := by
  set p : Polynomial W.toValuationSubring :=
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom W.toValuationSubring) ⟨x, hx⟩) with hp
  have hmonic : p.Monic := data.monic.map _
  have hmap : p.map (algebraMap W.toValuationSubring F) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x) := by
    rw [hp, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp
  have hint : IsIntegral W.toValuationSubring y := by
    refine ⟨p, hmonic, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hmap]
    exact hxy
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hz ▸ z.2

private def Alpha.IsCusp (W : Place ℚ̄ F) : Prop := W.ord (J : F) < 0

private theorem Alpha.jQFun_mem_of_jFun_mem (data : ModularPolynomialData q) (W : Place ℚ̄ F)
    (h : (J : F) ∈ W.toValuationSubring) : (JQ : F) ∈ W.toValuationSubring :=
  Alpha.mem_of_eval₂_modularPolynomial data W h (Alpha.eval₂_modularPolynomial data)

private theorem Alpha.eval₂_modularPolynomial' (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) JQ)).eval J = 0 := by
  have h := congrArg (w : F → F) (Alpha.eval₂_modularPolynomial (N := N) data)
  simp only [map_zero] at h
  rw [Polynomial.eval_map, ← AlgEquiv.coe_ringEquiv, ← RingEquiv.coe_toRingHom, Polynomial.hom_eval₂] at h
  rw [Polynomial.eval_map]
  convert h using 2
  all_goals try rfl
  · refine Polynomial.ringHom_ext (fun a => by simp) ?_
    simp [Alpha.w_jFun hqN]
  · simp [Alpha.w_jQFun hqN]

private theorem Alpha.jFun_mem_of_jQFun_mem (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F)
    (h : (JQ : F) ∈ W.toValuationSubring) : (J : F) ∈ W.toValuationSubring :=
  Alpha.mem_of_eval₂_modularPolynomial data W h (Alpha.eval₂_modularPolynomial' hqN data)

private theorem Alpha.ord_jQFun_neg_iff (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F) :
    W.ord (JQ : F) < 0 ↔ Alpha.IsCusp W := by
  unfold Alpha.IsCusp
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have hm := Alpha.jQFun_mem_of_jFun_mem data W (Alpha.mem_of_ord_nonneg W Alpha.jFun_ne_zero h')
    exact absurd (Alpha.ord_nonneg_of_mem W Alpha.jQFun_ne_zero hm) (not_le.mpr h)
  · intro h
    by_contra h'
    push Not at h'
    have hm := Alpha.jFun_mem_of_jQFun_mem hqN data W (Alpha.mem_of_ord_nonneg W Alpha.jQFun_ne_zero h')
    exact absurd (Alpha.ord_nonneg_of_mem W Alpha.jFun_ne_zero hm) (not_le.mpr h)

private theorem Alpha.isCusp_smul_iff (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F) :
    Alpha.IsCusp (w • W) ↔ Alpha.IsCusp W := by
  show (w • W).ord J < 0 ↔ _
  rw [← Alpha.ord_winv, Alpha.winv_jFun hqN]
  exact Alpha.ord_jQFun_neg_iff hqN data W

private theorem Alpha.isCusp_winv_smul_iff (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F) :
    Alpha.IsCusp (w⁻¹ • W) ↔ Alpha.IsCusp W := by
  show (w⁻¹ • W).ord J < 0 ↔ _
  rw [← Alpha.ord_w, Alpha.w_jFun hqN]
  exact Alpha.ord_jQFun_neg_iff hqN data W

private noncomputable def Alpha.uJ (b : A) : F :=
  algebraMap ℚ̄ F (b : ℚ̄) * J - 1

private noncomputable def Alpha.uJq (b : A) : F :=
  algebraMap ℚ̄ F (b : ℚ̄) * JQ - 1

private theorem Alpha.w_uJ (hqN : ¬ q ∣ N) (b : A) : w (Alpha.uJ (N := N) (q := q) b) = Alpha.uJq b := by
  unfold Alpha.uJ Alpha.uJq
  rw [map_sub, map_mul, map_one, AlgEquiv.commutes, Alpha.w_jFun hqN]

private theorem Alpha.w_uJq (hqN : ¬ q ∣ N) (b : A) : w (Alpha.uJq (N := N) (q := q) b) = Alpha.uJ b := by
  unfold Alpha.uJ Alpha.uJq
  rw [map_sub, map_mul, map_one, AlgEquiv.commutes, Alpha.w_jQFun hqN]

private theorem Alpha.coe_uJ (b : A) :
    ((Alpha.uJ (N := N) (q := q) b : F) : LaurentSeries ℚ̄) = coeffMap A.subtype (HahnSeries.C b * jqModC A - 1) := by
  rw [map_sub, map_mul, map_one, Alpha.coeffMap_C, Alpha.coeffMap_jqModC]
  unfold Alpha.uJ
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, Alpha.coe_jFun, Alpha.coe_algebraMap,
    HahnSeries.C_apply]
  rfl

private theorem Alpha.coe_uJq (b : A) :
    ((Alpha.uJq (N := N) (q := q) b : F) : LaurentSeries ℚ̄) =
      coeffMap A.subtype (HahnSeries.C b * qExpand A q (jqModC A) - 1) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [map_sub, map_mul, map_one, Alpha.coeffMap_C, coeffMap_qExpand, Alpha.coeffMap_jqModC]
  unfold Alpha.uJq
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, Alpha.coe_jQFun, Alpha.coe_algebraMap,
    HahnSeries.C_apply]
  rfl

private theorem Alpha.coeffMap_residue_yJ (b : A) (hb : b ∈ maximalIdeal A) :
    coeffMap (IsLocalRing.residue A) (HahnSeries.C b * jqModC A - 1) = -1 := by
  rw [map_sub, map_mul, map_one, Alpha.coeffMap_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb,
    map_zero, zero_mul, zero_sub]

private theorem Alpha.coeffMap_residue_yJq (b : A) (hb : b ∈ maximalIdeal A) :
    coeffMap (IsLocalRing.residue A) (HahnSeries.C b * qExpand A q (jqModC A) - 1) = -1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [map_sub, map_mul, map_one, Alpha.coeffMap_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb,
    map_zero, zero_mul, zero_sub]

private theorem Alpha.isCusp_of_ord_uJ_neg (b : A) (W : Place ℚ̄ F) (h : W.ord (Alpha.uJ (N := N) (q := q) b) < 0) :
    Alpha.IsCusp W := by
  have h1 : W.ord (algebraMap ℚ̄ F (b : ℚ̄) * J) < 0 := Alpha.ord_neg_of_ord_sub_neg W (one_mem _) h
  have hb : (b : ℚ̄) ≠ 0 := by
    intro hb; rw [hb, map_zero, zero_mul, Place.ord_zero] at h1; exact lt_irrefl _ h1
  rw [W.ord_mul ((map_ne_zero _).mpr hb) Alpha.jFun_ne_zero, Alpha.ord_algebraMap, zero_add] at h1
  exact h1

private theorem Alpha.isCusp_of_ord_uJq_neg (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (b : A) (W : Place ℚ̄ F)
    (h : W.ord (Alpha.uJq (N := N) (q := q) b) < 0) : Alpha.IsCusp W := by
  have h1 : W.ord (algebraMap ℚ̄ F (b : ℚ̄) * JQ) < 0 := Alpha.ord_neg_of_ord_sub_neg W (one_mem _) h
  have hb : (b : ℚ̄) ≠ 0 := by
    intro hb; rw [hb, map_zero, zero_mul, Place.ord_zero] at h1; exact lt_irrefl _ h1
  rw [W.ord_mul ((map_ne_zero _).mpr hb) Alpha.jQFun_ne_zero, Alpha.ord_algebraMap, zero_add] at h1
  exact (Alpha.ord_jQFun_neg_iff hqN data W).mp h1

private theorem Alpha.uJ_ne_zero (b : A) : Alpha.uJ (N := N) (q := q) b ≠ 0 := by
  intro h
  have h' : algebraMap ℚ̄ F (b : ℚ̄) * J = 1 := sub_eq_zero.mp h
  rcases eq_or_ne (b : ℚ̄) 0 with hb | hb
  · rw [hb, map_zero, zero_mul] at h'; exact zero_ne_one h'
  · apply Alpha.jFun_ne_algebraMap (N := N) (q := q) ((b : ℚ̄)⁻¹)
    rw [← mul_right_inj' ((map_ne_zero (algebraMap ℚ̄ F)).mpr hb), h', ← map_mul, mul_inv_cancel₀ hb, map_one]

private theorem Alpha.uJq_ne_zero (b : A) : Alpha.uJq (N := N) (q := q) b ≠ 0 := by
  intro h
  have h' : algebraMap ℚ̄ F (b : ℚ̄) * JQ = 1 := sub_eq_zero.mp h
  rcases eq_or_ne (b : ℚ̄) 0 with hb | hb
  · rw [hb, map_zero, zero_mul] at h'; exact zero_ne_one h'
  · apply Alpha.jQFun_ne_algebraMap (N := N) (q := q) ((b : ℚ̄)⁻¹)
    rw [← mul_right_inj' ((map_ne_zero (algebraMap ℚ̄ F)).mpr hb), h', ← map_mul, mul_inv_cancel₀ hb, map_one]

private theorem Alpha.uJ_mem_place (b : A) {W : Place ℚ̄ F} (hW : ¬ Alpha.IsCusp W) :
    Alpha.uJ (N := N) (q := q) b ∈ W.toValuationSubring :=
  Alpha.mem_of_ord_nonneg W (Alpha.uJ_ne_zero b) (not_lt.mp fun h => hW (Alpha.isCusp_of_ord_uJ_neg b W h))

private theorem Alpha.uJq_mem_place (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (b : A) {W : Place ℚ̄ F}
    (hW : ¬ Alpha.IsCusp W) : Alpha.uJq (N := N) (q := q) b ∈ W.toValuationSubring :=
  Alpha.mem_of_ord_nonneg W (Alpha.uJq_ne_zero b)
    (not_lt.mp fun h => hW (Alpha.isCusp_of_ord_uJq_neg hqN data b W h))

private theorem Alpha.exists_uJ_of_tate (W : Place ℚ̄ F) (hW : ¬ Alpha.IsCusp W)
    (hcusp : ∀ a : A, W.ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄)) ≤ 0) :
    ∃ b : A, b ∈ maximalIdeal A ∧ 0 < W.ord (Alpha.uJ (N := N) (q := q) b) := by
  haveI : NeZero (N * q) := Alpha.neZero
  have hj0 : 0 ≤ W.ord (J : F) := not_lt.mp hW
  have hmem : (J : F) ∈ W.toValuationSubring := Alpha.mem_of_ord_nonneg W Alpha.jFun_ne_zero hj0
  obtain ⟨c, hc⟩ := Alpha.exists_hasValue_of_deg_eq_one W (deg_eq_one_modularFunctionFieldBar (N * q) W) hmem
  have hpos : 0 < W.ord ((J : F) - algebraMap _ _ c) :=
    Alpha.ord_sub_pos_of_hasValue W hc (Alpha.jFun_ne_algebraMap c)
  have hcA : c ∉ A := fun hcA => absurd (hcusp ⟨c, hcA⟩) (not_le.mpr hpos)
  have hc0 : c ≠ 0 := fun h => hcA (h ▸ A.zero_mem)
  have hbA : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  refine ⟨⟨c⁻¹, hbA⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hcA
    have h2 := Alpha.inv_mem_of_isUnit hbA hu
    rwa [inv_inv] at h2
  · have e : Alpha.uJ (N := N) (q := q) ⟨c⁻¹, hbA⟩ = algebraMap _ _ (c⁻¹ : ℚ̄) * ((J : F) - algebraMap _ _ c) := by
      unfold Alpha.uJ
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hc0, map_one]
    rw [e, W.ord_mul ((map_ne_zero _).mpr (inv_ne_zero hc0)) (sub_ne_zero.mpr (Alpha.jFun_ne_algebraMap c)),
      Alpha.ord_algebraMap, zero_add]
    exact hpos

private theorem Alpha.exists_uJq_of_tate (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (W : Place ℚ̄ F)
    (hW : ¬ Alpha.IsCusp W)
    (hcusp : ∀ a : A, W.ord ((JQ : F) - algebraMap ℚ̄ F (a : ℚ̄)) ≤ 0) :
    ∃ b : A, b ∈ maximalIdeal A ∧ 0 < W.ord (Alpha.uJq (N := N) (q := q) b) := by

  have h' : ∀ a : A, (w⁻¹ • W).ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄)) ≤ 0 := by
    intro a
    have e : w ((J : F) - algebraMap _ _ (a : ℚ̄)) = (JQ : F) - algebraMap _ _ (a : ℚ̄) := by
      rw [map_sub, Alpha.w_jFun hqN, AlgEquiv.commutes]
    rw [← Alpha.ord_w, e]
    exact hcusp a
  have hW' : ¬ Alpha.IsCusp (w⁻¹ • W) := by rwa [Alpha.isCusp_winv_smul_iff hqN data]
  obtain ⟨b, hb, hpos⟩ := Alpha.exists_uJ_of_tate (N := N) (q := q) _ hW' h'
  refine ⟨b, hb, ?_⟩
  rw [← Alpha.w_uJ hqN, Alpha.ord_w]
  exact hpos

private theorem Alpha.exists_coeffMap_eq_smul_of_poles (f : F) (hf : f ≠ 0)
    (hpole : ∀ W : Place ℚ̄ F, W.ord f < 0 →
      (∃ a : A, 0 < W.ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Alpha.IsCusp W) :
    ∃ (c : ℚ̄) (y : LaurentSeries A), c ≠ 0 ∧ coeffMap A.subtype y = c • (f : LaurentSeries ℚ̄) := by
  classical
  haveI : NeZero (N * q) := Alpha.neZero
  have hPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hPD) f hf
  set M : ℕ := ∑ W ∈ D.support, (-(D W)).toNat with hM
  have hMb : ∀ W : Place ℚ̄ F, -(W.ord f) ≤ M := by
    intro W
    by_cases hW : W ∈ D.support
    · have h1 : (-(D W)).toNat ≤ M :=
        Finset.single_le_sum (f := fun W' => (-(D W')).toNat) (fun _ _ => Nat.zero_le _) hW
      have h2 : -(D W) ≤ ((-(D W)).toNat : ℤ) := Int.self_le_toNat _
      rw [← hD]; omega
    · have : D W = 0 := Finsupp.notMem_support_iff.mp hW
      rw [← hD, this]; omega
  have hJ0 : (J : F)⁻¹ ^ M ≠ 0 := pow_ne_zero _ (inv_ne_zero Alpha.jFun_ne_zero)
  have hg0 : f * (J : F)⁻¹ ^ M ≠ 0 := mul_ne_zero hf hJ0
  have hordg : ∀ W : Place ℚ̄ F, W.ord (f * (J : F)⁻¹ ^ M) = W.ord f - M * W.ord (J : F) := fun W => by
    rw [W.ord_mul hf hJ0, Alpha.ord_pow, W.ord_inv]; ring
  obtain ⟨c, hc0, hc⟩ := exists_forall_coeff_smul_mem_of_forall_ord_neg A (N * q) _ hg0 (by
    intro W hW
    rw [hordg] at hW
    rcases lt_trichotomy (W.ord (J : F)) 0 with hj | hj | hj
    · exfalso
      have h1 := hMb W
      have h2 : (M : ℤ) * W.ord (J : F) ≤ (M : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg M)
      omega
    · rw [hj, mul_zero, sub_zero] at hW
      rcases hpole W hW with h | h
      · exact h
      · exact absurd h (by unfold Alpha.IsCusp; omega)
    · refine ⟨0, ?_⟩
      rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
      exact hj)
  obtain ⟨yg, hyg⟩ := Alpha.exists_coeffMap_subtype_eq A _ hc
  have hJne : jqModC ℚ̄ ≠ 0 := by
    rw [← Alpha.coe_jFun (N := N) (q := q)]
    exact fun h => Alpha.jFun_ne_zero (N := N) (q := q) ((ZeroMemClass.coe_eq_zero).mp h)
  have hJJ : ((jqModC ℚ̄)⁻¹) ^ M * (jqModC ℚ̄) ^ M = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hJne, one_pow]
  refine ⟨c, yg * (jqModC A) ^ M, hc0, ?_⟩
  rw [map_mul, map_pow, hyg, Alpha.coeffMap_jqModC, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
    IntermediateField.coe_inv, Alpha.coe_jFun, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
    mul_assoc, mul_assoc, hJJ, mul_one]

private theorem Alpha.poles_mul (E : Divisor ℚ̄ F) (U : F) (hU0 : U ≠ 0)
    (hUint : ∀ W : Place ℚ̄ F, ¬ Alpha.IsCusp W → U ∈ W.toValuationSubring)
    (T : Place ℚ̄ F → Prop)
    (hUT : ∀ W : Place ℚ̄ F, ¬ Alpha.IsCusp W → 0 < E W → T W → E W ≤ W.ord U)
    (f : F) (hf : f ∈ riemannRochSpace E) (hf0 : f ≠ 0)
    (W : Place ℚ̄ F) (hW : W.ord (U * f) < 0) :
    ¬ T W ∨ Alpha.IsCusp W := by
  by_cases hc : Alpha.IsCusp W
  · exact Or.inr hc
  left
  intro hT
  have hU : 0 ≤ W.ord U := Alpha.ord_nonneg_of_mem W hU0 (hUint W hc)
  rw [W.ord_mul hU0 hf0] at hW
  rcases (mem_riemannRochSpace_iff.mp hf) W with h | h
  · exact hf0 h
  · have hEW : 0 < E W := by omega
    have h2 := hUT W hc hEW hT
    omega

end AlphaLevel

section AlphaPair

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

local notation "F" => modularFunctionFieldBar (N * q)
local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "w" => ProlongationTuple.atkinLehnerBar N q
local notation "J" => ProlongationTuple.jFun N q
local notation "JQ" => ProlongationTuple.jQFun N q

private theorem Alpha.uJ_mem₁ (R : ProlongationTuple P) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Alpha.uJ (N := N) (q := q) b ∈ R.R₁.integers, R.R₁.residue ⟨Alpha.uJ b, h⟩ = -1 := by
  have hy : coeffMap A.subtype (HahnSeries.C b * jqModC A - 1) ∈ F := by
    rw [← Alpha.coe_uJ (N := N) (q := q)]; exact (Alpha.uJ (N := N) (q := q) b).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap _ hy
  have e : (⟨coeffMap A.subtype (HahnSeries.C b * jqModC A - 1), hy⟩ : F) = Alpha.uJ b :=
    Subtype.ext (Alpha.coe_uJ b).symm
  have h' : Alpha.uJ (N := N) (q := q) b ∈ R.R₁.integers := by rw [← e]; exact h
  refine ⟨h', ?_⟩
  have e2 : (⟨Alpha.uJ b, h'⟩ : R.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [e2]
  apply Subtype.ext
  rw [hres, Alpha.coeffMap_residue_yJ b hb, NegMemClass.coe_neg, OneMemClass.coe_one]

private theorem Alpha.uJq_mem₁ (R : ProlongationTuple P) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Alpha.uJq (N := N) (q := q) b ∈ R.R₁.integers, R.R₁.residue ⟨Alpha.uJq b, h⟩ = -1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hy : coeffMap A.subtype (HahnSeries.C b * qExpand A q (jqModC A) - 1) ∈ F := by
    rw [← Alpha.coe_uJq (N := N) (q := q)]; exact (Alpha.uJq (N := N) (q := q) b).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap _ hy
  have e : (⟨coeffMap A.subtype (HahnSeries.C b * qExpand A q (jqModC A) - 1), hy⟩ : F) = Alpha.uJq b :=
    Subtype.ext (Alpha.coe_uJq b).symm
  have h' : Alpha.uJq (N := N) (q := q) b ∈ R.R₁.integers := by rw [← e]; exact h
  refine ⟨h', ?_⟩
  have e2 : (⟨Alpha.uJq b, h'⟩ : R.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [e2]
  apply Subtype.ext
  rw [hres, Alpha.coeffMap_residue_yJq b hb, NegMemClass.coe_neg, OneMemClass.coe_one]

private theorem Alpha.uJ_mem₂ (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Alpha.uJ (N := N) (q := q) b ∈ R.R₂.integers, R.R₂.residue ⟨Alpha.uJ b, h⟩ = -1 := by
  obtain ⟨h1, hres⟩ := Alpha.uJq_mem₁ R b hb
  have h1' : w (Alpha.uJ (N := N) (q := q) b) ∈ R.R₁.integers := by
    rw [Alpha.w_uJ hqN]; exact h1
  have h2 : Alpha.uJ (N := N) (q := q) b ∈ R.R₂.integers := (R.mem_integers₂_iff _).mpr h1'
  refine ⟨h2, ?_⟩
  rw [R.residue₂_eq]
  have e : (⟨w (Alpha.uJ b), (R.mem_integers₂_iff _).mp h2⟩ : R.R₁.integers) = ⟨Alpha.uJq b, h1⟩ :=
    Subtype.ext (Alpha.w_uJ hqN b)
  rw [e, hres]

private theorem Alpha.uJq_mem₂ (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Alpha.uJq (N := N) (q := q) b ∈ R.R₂.integers, R.R₂.residue ⟨Alpha.uJq b, h⟩ = -1 := by
  obtain ⟨h1, hres⟩ := Alpha.uJ_mem₁ R b hb
  have h1' : w (Alpha.uJq (N := N) (q := q) b) ∈ R.R₁.integers := by
    rw [Alpha.w_uJq hqN]; exact h1
  have h2 : Alpha.uJq (N := N) (q := q) b ∈ R.R₂.integers := (R.mem_integers₂_iff _).mpr h1'
  refine ⟨h2, ?_⟩
  rw [R.residue₂_eq]
  have e : (⟨w (Alpha.uJq b), (R.mem_integers₂_iff _).mp h2⟩ : R.R₁.integers) = ⟨Alpha.uJ b, h1⟩ :=
    Subtype.ext (Alpha.w_uJq hqN b)
  rw [e, hres]

private noncomputable def Alpha.bigU (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A) :
    F :=
  (∏ W ∈ E.support, Alpha.uJ (N := N) (q := q) (bJ W) ^ (E W).toNat) *
    ∏ W ∈ E.support, Alpha.uJq (N := N) (q := q) (bJq W) ^ (E W).toNat

private theorem Alpha.bigU_ne_zero (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A) :
    Alpha.bigU (N := N) (q := q) E bJ bJq ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (Alpha.uJ_ne_zero _))
    (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (Alpha.uJq_ne_zero _))

private theorem Alpha.bigU_mem_place (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (W : Place ℚ̄ F)
    (hWc : ¬ Alpha.IsCusp W) :
    Alpha.bigU (N := N) (q := q) E bJ bJq ∈ W.toValuationSubring :=
  mul_mem (prod_mem fun W' _ => pow_mem (Alpha.uJ_mem_place _ hWc) _)
    (prod_mem fun W' _ => pow_mem (Alpha.uJq_mem_place hqN data _ hWc) _)

private theorem Alpha.le_ord_bigU_of_pos (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (W : Place ℚ̄ F)
    (hWc : ¬ Alpha.IsCusp W) (hEW : 0 < E W)
    (hpos : 0 < W.ord (Alpha.uJ (N := N) (q := q) (bJ W))) :
    E W ≤ W.ord (Alpha.bigU (N := N) (q := q) E bJ bJq) := by
  classical
  have hWS : W ∈ E.support := Finsupp.mem_support_iff.mpr hEW.ne'
  have hsplit := Finset.mul_prod_erase E.support (fun W' => Alpha.uJ (N := N) (q := q) (bJ W') ^ (E W').toNat) hWS
  unfold Alpha.bigU
  rw [← hsplit]
  have hne1 : Alpha.uJ (N := N) (q := q) (bJ W) ^ (E W).toNat ≠ 0 := pow_ne_zero _ (Alpha.uJ_ne_zero _)
  have hne2 : ∏ x ∈ E.support.erase W, Alpha.uJ (N := N) (q := q) (bJ x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Alpha.uJ_ne_zero _)
  have hne3 : ∏ x ∈ E.support, Alpha.uJq (N := N) (q := q) (bJq x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Alpha.uJq_ne_zero _)
  rw [W.ord_mul (mul_ne_zero hne1 hne2) hne3, W.ord_mul hne1 hne2, Alpha.ord_pow]
  have h2 : 0 ≤ W.ord (∏ x ∈ E.support.erase W, Alpha.uJ (N := N) (q := q) (bJ x) ^ (E x).toNat) :=
    Alpha.ord_nonneg_of_mem W hne2 (prod_mem fun W' _ => pow_mem (Alpha.uJ_mem_place _ hWc) _)
  have h3 : 0 ≤ W.ord (∏ x ∈ E.support, Alpha.uJq (N := N) (q := q) (bJq x) ^ (E x).toNat) :=
    Alpha.ord_nonneg_of_mem W hne3 (prod_mem fun W' _ => pow_mem (Alpha.uJq_mem_place hqN data _ hWc) _)
  have h4 : ((E W).toNat : ℤ) = E W := Int.toNat_of_nonneg hEW.le
  have h5 : ((E W).toNat : ℤ) * 1 ≤ ((E W).toNat : ℤ) * W.ord (Alpha.uJ (N := N) (q := q) (bJ W)) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
  linarith

private theorem Alpha.le_ord_bigU_of_pos' (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (W : Place ℚ̄ F)
    (hWc : ¬ Alpha.IsCusp W) (hEW : 0 < E W)
    (hpos : 0 < W.ord (Alpha.uJq (N := N) (q := q) (bJq W))) :
    E W ≤ W.ord (Alpha.bigU (N := N) (q := q) E bJ bJq) := by
  classical
  have hWS : W ∈ E.support := Finsupp.mem_support_iff.mpr hEW.ne'
  have hsplit := Finset.mul_prod_erase E.support (fun W' => Alpha.uJq (N := N) (q := q) (bJq W') ^ (E W').toNat) hWS
  unfold Alpha.bigU
  rw [← hsplit]
  have hne1 : Alpha.uJq (N := N) (q := q) (bJq W) ^ (E W).toNat ≠ 0 := pow_ne_zero _ (Alpha.uJq_ne_zero _)
  have hne2 : ∏ x ∈ E.support.erase W, Alpha.uJq (N := N) (q := q) (bJq x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Alpha.uJq_ne_zero _)
  have hne3 : ∏ x ∈ E.support, Alpha.uJ (N := N) (q := q) (bJ x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Alpha.uJ_ne_zero _)
  rw [W.ord_mul hne3 (mul_ne_zero hne1 hne2), W.ord_mul hne1 hne2, Alpha.ord_pow]
  have h2 : 0 ≤ W.ord (∏ x ∈ E.support.erase W, Alpha.uJq (N := N) (q := q) (bJq x) ^ (E x).toNat) :=
    Alpha.ord_nonneg_of_mem W hne2 (prod_mem fun W' _ => pow_mem (Alpha.uJq_mem_place hqN data _ hWc) _)
  have h3 : 0 ≤ W.ord (∏ x ∈ E.support, Alpha.uJ (N := N) (q := q) (bJ x) ^ (E x).toNat) :=
    Alpha.ord_nonneg_of_mem W hne3 (prod_mem fun W' _ => pow_mem (Alpha.uJ_mem_place _ hWc) _)
  have h4 : ((E W).toNat : ℤ) = E W := Int.toNat_of_nonneg hEW.le
  have h5 : ((E W).toNat : ℤ) * 1 ≤ ((E W).toNat : ℤ) * W.ord (Alpha.uJq (N := N) (q := q) (bJq W)) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
  linarith

private theorem Alpha.bigU_isUnit₁ (R : ProlongationTuple P)
    (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (hbJ : ∀ W, bJ W ∈ maximalIdeal A) (hbJq : ∀ W, bJq W ∈ maximalIdeal A) :
    ∃ h : Alpha.bigU (N := N) (q := q) E bJ bJq ∈ R.R₁.integers, IsUnit (⟨Alpha.bigU E bJ bJq, h⟩ : R.R₁.integers) := by
  classical
  have m1 : ∀ W, Alpha.uJ (N := N) (q := q) (bJ W) ∈ R.R₁.integers := fun W => (Alpha.uJ_mem₁ R (bJ W) (hbJ W)).1
  have m2 : ∀ W, Alpha.uJq (N := N) (q := q) (bJq W) ∈ R.R₁.integers := fun W => (Alpha.uJq_mem₁ R (bJq W) (hbJq W)).1
  have r1 : ∀ W, R.R₁.residue ⟨Alpha.uJ (N := N) (q := q) (bJ W), m1 W⟩ = -1 := fun W => (Alpha.uJ_mem₁ R (bJ W) (hbJ W)).2
  have r2 : ∀ W, R.R₁.residue ⟨Alpha.uJq (N := N) (q := q) (bJq W), m2 W⟩ = -1 := fun W => (Alpha.uJq_mem₁ R (bJq W) (hbJq W)).2
  set y1 : Place ℚ̄ F → R.R₁.integers :=
    fun W => ⟨Alpha.uJ (N := N) (q := q) (bJ W), m1 W⟩ with hy1
  set y2 : Place ℚ̄ F → R.R₁.integers :=
    fun W => ⟨Alpha.uJq (N := N) (q := q) (bJq W), m2 W⟩ with hy2
  set x : R.R₁.integers := (∏ W ∈ E.support, y1 W ^ (E W).toNat) * ∏ W ∈ E.support, y2 W ^ (E W).toNat with hx
  have e1 : ((∏ W ∈ E.support, y1 W ^ (E W).toNat : R.R₁.integers) : F)
      = ∏ W ∈ E.support, ((y1 W ^ (E W).toNat : R.R₁.integers) : F) :=
    SubmonoidClass.coe_finsetProd _ _
  have e2 : ((∏ W ∈ E.support, y2 W ^ (E W).toNat : R.R₁.integers) : F)
      = ∏ W ∈ E.support, ((y2 W ^ (E W).toNat : R.R₁.integers) : F) :=
    SubmonoidClass.coe_finsetProd _ _
  have hxU : (x : F) = Alpha.bigU E bJ bJq := by
    rw [hx, MulMemClass.coe_mul, e1, e2]
    unfold Alpha.bigU
    congr 1 <;> first | rfl | exact Finset.prod_congr rfl fun W _ => (by rw [SubmonoidClass.coe_pow])
  have hmem : Alpha.bigU (N := N) (q := q) E bJ bJq ∈ R.R₁.integers := by rw [← hxU]; exact x.2
  refine ⟨hmem, ?_⟩
  have ex : (⟨Alpha.bigU E bJ bJq, hmem⟩ : R.R₁.integers) = x := Subtype.ext hxU.symm
  rw [ex]
  apply R.R₁.isUnit_of_residue_ne_zero
  rw [hx, map_mul, map_prod, map_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => ?_) (Finset.prod_ne_zero_iff.mpr fun W _ => ?_)
  · rw [map_pow, r1]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · rw [map_pow, r2]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

private theorem Alpha.bigU_isUnit₂ (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (E : Divisor ℚ̄ F)
    (bJ bJq : Place ℚ̄ F → A)
    (hbJ : ∀ W, bJ W ∈ maximalIdeal A) (hbJq : ∀ W, bJq W ∈ maximalIdeal A) :
    ∃ h : Alpha.bigU (N := N) (q := q) E bJ bJq ∈ R.R₂.integers, IsUnit (⟨Alpha.bigU E bJ bJq, h⟩ : R.R₂.integers) := by
  classical
  have m1 : ∀ W, Alpha.uJ (N := N) (q := q) (bJ W) ∈ R.R₂.integers := fun W => (Alpha.uJ_mem₂ hqN R (bJ W) (hbJ W)).1
  have m2 : ∀ W, Alpha.uJq (N := N) (q := q) (bJq W) ∈ R.R₂.integers := fun W => (Alpha.uJq_mem₂ hqN R (bJq W) (hbJq W)).1
  have r1 : ∀ W, R.R₂.residue ⟨Alpha.uJ (N := N) (q := q) (bJ W), m1 W⟩ = -1 := fun W => (Alpha.uJ_mem₂ hqN R (bJ W) (hbJ W)).2
  have r2 : ∀ W, R.R₂.residue ⟨Alpha.uJq (N := N) (q := q) (bJq W), m2 W⟩ = -1 := fun W => (Alpha.uJq_mem₂ hqN R (bJq W) (hbJq W)).2
  set y1 : Place ℚ̄ F → R.R₂.integers :=
    fun W => ⟨Alpha.uJ (N := N) (q := q) (bJ W), m1 W⟩ with hy1
  set y2 : Place ℚ̄ F → R.R₂.integers :=
    fun W => ⟨Alpha.uJq (N := N) (q := q) (bJq W), m2 W⟩ with hy2
  set x : R.R₂.integers := (∏ W ∈ E.support, y1 W ^ (E W).toNat) * ∏ W ∈ E.support, y2 W ^ (E W).toNat with hx
  have e1 : ((∏ W ∈ E.support, y1 W ^ (E W).toNat : R.R₂.integers) : F)
      = ∏ W ∈ E.support, ((y1 W ^ (E W).toNat : R.R₂.integers) : F) :=
    SubmonoidClass.coe_finsetProd _ _
  have e2 : ((∏ W ∈ E.support, y2 W ^ (E W).toNat : R.R₂.integers) : F)
      = ∏ W ∈ E.support, ((y2 W ^ (E W).toNat : R.R₂.integers) : F) :=
    SubmonoidClass.coe_finsetProd _ _
  have hxU : (x : F) = Alpha.bigU E bJ bJq := by
    rw [hx, MulMemClass.coe_mul, e1, e2]
    unfold Alpha.bigU
    congr 1 <;> first | rfl | exact Finset.prod_congr rfl fun W _ => (by rw [SubmonoidClass.coe_pow])
  have hmem : Alpha.bigU (N := N) (q := q) E bJ bJq ∈ R.R₂.integers := by rw [← hxU]; exact x.2
  refine ⟨hmem, ?_⟩
  have ex : (⟨Alpha.bigU E bJ bJq, hmem⟩ : R.R₂.integers) = x := Subtype.ext hxU.symm
  rw [ex]
  apply R.R₂.isUnit_of_residue_ne_zero
  rw [hx, map_mul, map_prod, map_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => ?_) (Finset.prod_ne_zero_iff.mpr fun W _ => ?_)
  · rw [map_pow, r1]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · rw [map_pow, r2]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

private theorem Alpha.exists_bigU (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (E : Divisor ℚ̄ F) :
    ∃ U : F,
      (∃ h₁ : U ∈ R.R₁.integers, IsUnit (⟨U, h₁⟩ : R.R₁.integers)) ∧
      (∃ h₂ : U ∈ R.R₂.integers, IsUnit (⟨U, h₂⟩ : R.R₂.integers)) ∧
      (∀ f ∈ riemannRochSpace E, f ≠ 0 →
        ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
          (∃ a : A, 0 < W.ord ((J : F)
            - algebraMap (AlgebraicClosure ℚ) (F) (a : AlgebraicClosure ℚ)))
          ∨ Alpha.IsCusp W) ∧
      (∀ f ∈ riemannRochSpace E, f ≠ 0 →
        ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
          (∃ a : A, 0 < W.ord ((JQ : F)
            - algebraMap (AlgebraicClosure ℚ) (F) (a : AlgebraicClosure ℚ)))
          ∨ Alpha.IsCusp W) := by
  classical

  have hJ : ∀ W : Place ℚ̄ F, ∃ b : A, b ∈ maximalIdeal A ∧
      (¬ Alpha.IsCusp W →
        (∀ a : A, W.ord ((J : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0) → 0 < W.ord (Alpha.uJ (N := N) (q := q) b)) := by
    intro W
    by_cases h : ¬ Alpha.IsCusp W ∧
        ∀ a : A, W.ord ((J : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0
    · obtain ⟨b, hb, hpos⟩ := Alpha.exists_uJ_of_tate W h.1 h.2
      exact ⟨b, hb, fun _ _ => hpos⟩
    · exact ⟨0, Ideal.zero_mem _, fun h1 h3 => absurd ⟨h1, h3⟩ h⟩
  have hJq : ∀ W : Place ℚ̄ F, ∃ b : A, b ∈ maximalIdeal A ∧
      (¬ Alpha.IsCusp W →
        (∀ a : A, W.ord ((JQ : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0) → 0 < W.ord (Alpha.uJq (N := N) (q := q) b)) := by
    intro W
    by_cases h : ¬ Alpha.IsCusp W ∧
        ∀ a : A, W.ord ((JQ : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0
    · obtain ⟨b, hb, hpos⟩ := Alpha.exists_uJq_of_tate hqN data W h.1 h.2
      exact ⟨b, hb, fun _ _ => hpos⟩
    · exact ⟨0, Ideal.zero_mem _, fun h1 h3 => absurd ⟨h1, h3⟩ h⟩
  choose bJ hbJm hbJpos using hJ
  choose bJq hbJqm hbJqpos using hJq
  refine ⟨Alpha.bigU E bJ bJq, Alpha.bigU_isUnit₁ R E bJ bJq hbJm hbJqm,
    Alpha.bigU_isUnit₂ hqN R E bJ bJq hbJm hbJqm, ?_, ?_⟩
  · intro f hf hf0 W hW
    rcases Alpha.poles_mul E _ (Alpha.bigU_ne_zero E bJ bJq) (Alpha.bigU_mem_place hqN data E bJ bJq)
      (fun W => ∀ a : A, W.ord ((J : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0)
      (fun W hWc hEW hT => Alpha.le_ord_bigU_of_pos hqN data E bJ bJq W hWc hEW (hbJpos W hWc hT))
      f hf hf0 W hW with h | h
    · left; simpa only [not_forall, not_le] using h
    · exact Or.inr h
  · intro f hf hf0 W hW
    rcases Alpha.poles_mul E _ (Alpha.bigU_ne_zero E bJ bJq) (Alpha.bigU_mem_place hqN data E bJ bJq)
      (fun W => ∀ a : A, W.ord ((JQ : F) - algebraMap (AlgebraicClosure ℚ) (F)
          (a : AlgebraicClosure ℚ)) ≤ 0)
      (fun W hWc hEW hT => Alpha.le_ord_bigU_of_pos' hqN data E bJ bJq W hWc hEW (hbJqpos W hWc hT))
      f hf hf0 W hW with h | h
    · left; simpa only [not_forall, not_le] using h
    · exact Or.inr h

private theorem Alpha.linearIndependent_mul_units {k₀ L : Type*} [Field k₀] [Field L] [Algebra k₀ L]
    {ι : Type*} {r : ι → L × L} (hr : LinearIndependent k₀ r) {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent k₀ (fun i => (a * (r i).1, b * (r i).2)) := by
  let φ : L × L →ₗ[k₀] L × L := (LinearMap.mulLeft k₀ a).prodMap (LinearMap.mulLeft k₀ b)
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    simp only [φ, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ ha h.1) (mul_left_cancel₀ hb h.2)
  have h := hr.map' φ hφ
  exact h

private theorem Alpha.hint (hqN : ¬ q ∣ N) (data : ModularPolynomialData q) (E : Divisor ℚ̄ F) (U : F) (hU0 : U ≠ 0)
    (hpJ : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Alpha.IsCusp W)
    (hpJq : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord ((JQ : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Alpha.IsCusp W)
    (V : Submodule ℚ̄ F) (hV : V = (riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U))
    [FiniteDimensional ℚ̄ V] :
    ∃ b : Fin (Module.finrank ℚ̄ V) → F,
      (∀ i, b i ∈ V) ∧ LinearIndependent ℚ̄ b ∧
      ∀ i, (∃ (c : ℚ̄) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : F) : LaurentSeries ℚ̄)) ∧
           (∃ (c : ℚ̄) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((w (b i) : F) : LaurentSeries ℚ̄)) := by
  classical
  have B : Module.Basis (Fin (Module.finrank ℚ̄ V)) ℚ̄ V := Module.finBasis ℚ̄ V
  have hbli : LinearIndependent ℚ̄ (V.subtype ∘ B) := B.linearIndependent.map' _ (Submodule.ker_subtype _)
  have hmem : ∀ i, ∃ f, f ∈ riemannRochSpace E ∧ f ≠ 0 ∧ (V.subtype ∘ B) i = U * f := fun i => by
    have hi : ((V.subtype ∘ B) i) ∈ (riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U) := hV.le (B i).2
    rw [Submodule.mem_map] at hi
    obtain ⟨f, hf, hfe⟩ := hi
    rw [LinearMap.mulLeft_apply] at hfe
    refine ⟨f, hf, ?_, hfe.symm⟩
    rintro rfl
    apply B.ne_zero i
    apply Subtype.ext
    rw [mul_zero] at hfe
    exact hfe.symm
  refine ⟨V.subtype ∘ B, fun i => (B i).2, hbli, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf, hf0, hfe⟩ := hmem i
    have hne : (V.subtype ∘ B) i ≠ 0 := by rw [hfe]; exact mul_ne_zero hU0 hf0
    exact Alpha.exists_coeffMap_eq_smul_of_poles _ hne (fun W hW => hpJ f hf hf0 W (by rw [← hfe]; exact hW))
  · obtain ⟨f, hf, hf0, hfe⟩ := hmem i
    have hne : (V.subtype ∘ B) i ≠ 0 := by rw [hfe]; exact mul_ne_zero hU0 hf0
    have hwne : w ((V.subtype ∘ B) i) ≠ 0 := (map_ne_zero _).mpr hne
    refine Alpha.exists_coeffMap_eq_smul_of_poles _ hwne (fun W hW => ?_)
    rw [Alpha.ord_w, hfe] at hW
    rcases hpJq f hf hf0 _ hW with ⟨a, ha⟩ | h
    · left
      refine ⟨a, ?_⟩
      rw [← Alpha.ord_w, map_sub, Alpha.w_jQFun hqN, AlgEquiv.commutes] at ha
      exact ha
    · right
      exact (Alpha.isCusp_winv_smul_iff hqN data W).mp h

set_option maxHeartbeats 6400000 in

private theorem Alpha.main_of_unit (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (E : Divisor ℚ̄ F)
    [FiniteDimensional ℚ̄ ↥(riemannRochSpace E)]
    (U : F)
    (hU₁ : U ∈ R.R₁.integers) (hU₁u : IsUnit (⟨U, hU₁⟩ : R.R₁.integers))
    (hU₂ : U ∈ R.R₂.integers) (hU₂u : IsUnit (⟨U, hU₂⟩ : R.R₂.integers))
    (hpJ : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord ((J : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Alpha.IsCusp W)
    (hpJq : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place ℚ̄ F, W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord ((JQ : F) - algebraMap ℚ̄ F (a : ℚ̄))) ∨ Alpha.IsCusp W) :
    ∃ (Gf : Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) → F)
      (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers),
      (∀ j, Gf j ∈ riemannRochSpace E) ∧
      LinearIndependent k (fun j =>
        ((R.residue₁ ⟨Gf j, hG₁ j⟩ : modularFunctionFieldC k N), (R.residue₂ ⟨Gf j, hG₂ j⟩ : modularFunctionFieldC k N))) := by
  classical
  have hU0 : U ≠ 0 := fun h => hU₁u.ne_zero (Subtype.ext h)
  have hinj : Function.Injective (LinearMap.mulLeft ℚ̄ U) := by
    intro x y h
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at h
    exact mul_left_cancel₀ hU0 h
  have hn : Module.finrank ℚ̄ ↥((riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U))
      = Module.finrank ℚ̄ ↥(riemannRochSpace E) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (riemannRochSpace E))).symm
  obtain ⟨b, hbV, hbli, hbint⟩ := Alpha.hint hqN data E U hU0 hpJ hpJq
    ((riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U)) rfl
  obtain ⟨G, hG₁, hG₂, hGV, hGli⟩ :=
    ProlongationTuple.exists_mem_integers_linearIndependent_residue_pair_of_finiteDimensional R
      ((riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U)) ⟨b, hbV, hbli, hbint⟩

  obtain ⟨u₁, hu₁⟩ := hU₁u
  obtain ⟨u₂, hu₂⟩ := hU₂u
  have hinv₁ : (((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) : F) = U⁻¹ := by
    rw [Alpha.coe_unit_inv, hu₁]
  have hinv₂ : (((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : F) = U⁻¹ := by
    rw [Alpha.coe_unit_inv, hu₂]

  let e : Fin (Module.finrank ℚ̄ ↥((riemannRochSpace E).map (LinearMap.mulLeft ℚ̄ U))) ≃
      Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) := finCongr hn
  set Gf : Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) → F := fun j => U⁻¹ * G (e.symm j) with hGf
  have hGf₁ : ∀ j, Gf j ∈ R.R₁.integers := fun j => by
    rw [hGf, ← hinv₁]; exact mul_mem (SetLike.coe_mem _) (hG₁ _)
  have hGf₂ : ∀ j, Gf j ∈ R.R₂.integers := fun j => by
    rw [hGf, ← hinv₂]; exact mul_mem (SetLike.coe_mem _) (hG₂ _)
  have hGfV : ∀ j, Gf j ∈ riemannRochSpace E := fun j => by
    obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.mp (hGV (e.symm j))
    rw [LinearMap.mulLeft_apply] at hfe
    have : Gf j = f := by
      rw [hGf]
      show U⁻¹ * G (e.symm j) = f
      rw [← hfe, ← mul_assoc, inv_mul_cancel₀ hU0, one_mul f]
    rw [this]; exact hf

  have ha₁ : R.residue₁ ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) ≠ 0 := by
    rw [ProlongationTuple.residue₁_apply]
    exact (map_ne_zero_iff R.ι R.ι.injective).mpr (R.R₁.residue_ne_zero_of_isUnit (Units.isUnit _))
  have ha₂ : R.residue₂ ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) ≠ 0 := by
    rw [ProlongationTuple.residue₂_apply]
    exact (map_ne_zero_iff R.ι R.ι.injective).mpr (R.R₂.residue_ne_zero_of_isUnit (Units.isUnit _))
  have hres₁ : ∀ j, R.residue₁ ⟨Gf j, hGf₁ j⟩
      = R.residue₁ ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) * R.residue₁ ⟨G (e.symm j), hG₁ _⟩ := by
    intro j
    have ex : (⟨Gf j, hGf₁ j⟩ : R.R₁.integers)
        = ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) * ⟨G (e.symm j), hG₁ _⟩ := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hinv₁]
    rw [ex, map_mul]
  have hres₂ : ∀ j, R.residue₂ ⟨Gf j, hGf₂ j⟩
      = R.residue₂ ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) * R.residue₂ ⟨G (e.symm j), hG₂ _⟩ := by
    intro j
    have ex : (⟨Gf j, hGf₂ j⟩ : R.R₂.integers)
        = ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) * ⟨G (e.symm j), hG₂ _⟩ := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hinv₂]
    rw [ex, map_mul]
  refine ⟨Gf, hGf₁, hGf₂, hGfV, ?_⟩
  have hfun : (fun j => ((R.residue₁ ⟨Gf j, hGf₁ j⟩ : modularFunctionFieldC k N),
        (R.residue₂ ⟨Gf j, hGf₂ j⟩ : modularFunctionFieldC k N)))
      = fun j => ((R.residue₁ ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) : modularFunctionFieldC k N)
          * ((fun i => ((R.residue₁ ⟨G i, hG₁ i⟩ : modularFunctionFieldC k N),
              (R.residue₂ ⟨G i, hG₂ i⟩ : modularFunctionFieldC k N))) (e.symm j)).1,
        (R.residue₂ ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : modularFunctionFieldC k N)
          * ((fun i => ((R.residue₁ ⟨G i, hG₁ i⟩ : modularFunctionFieldC k N),
              (R.residue₂ ⟨G i, hG₂ i⟩ : modularFunctionFieldC k N))) (e.symm j)).2) :=
    funext fun j => Prod.ext (hres₁ j) (hres₂ j)
  rw [hfun]
  exact Alpha.linearIndependent_mul_units (hGli.comp e.symm e.symm.injective) ha₁ ha₂

private theorem Alpha.exists_linearIndependent_residuePair (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (E : Divisor ℚ̄ F)
    [FiniteDimensional ℚ̄ ↥(riemannRochSpace E)] :
    ∃ (Gf : Fin (Module.finrank ℚ̄ ↥(riemannRochSpace E)) → F)
      (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers),
      (∀ j, Gf j ∈ riemannRochSpace E) ∧
      LinearIndependent k (fun j =>
        ((R.residue₁ ⟨Gf j, hG₁ j⟩ : modularFunctionFieldC k N), (R.residue₂ ⟨Gf j, hG₂ j⟩ : modularFunctionFieldC k N))) := by
  obtain ⟨U, ⟨hU₁, hU₁u⟩, ⟨hU₂, hU₂u⟩, hpJ, hpJq⟩ := Alpha.exists_bigU hqN R E
  exact Alpha.main_of_unit hqN R E U hU₁ hU₁u hU₂ hU₂u hpJ hpJq

end AlphaPair

end MovN

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)] :
    ∃ (G : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → ↥(modularFunctionFieldBar (N * q)))
      (hG₁ : ∀ i, G i ∈ R.R₁.integers) (hG₂ : ∀ i, G i ∈ R.R₂.integers),
      (∀ i, G i ∈ riemannRochSpace E) ∧
      LinearIndependent k (fun i =>
        ((R.residue₁ ⟨G i, hG₁ i⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨G i, hG₂ i⟩ : ↥(modularFunctionFieldC k N)))) :=
  MovN.Alpha.exists_linearIndependent_residuePair hqN R E

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_linearIndependent_residuePair_of_riemannRochSpace
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_linearIndependent_residuePair_of_riemannRochSpace (solution)
