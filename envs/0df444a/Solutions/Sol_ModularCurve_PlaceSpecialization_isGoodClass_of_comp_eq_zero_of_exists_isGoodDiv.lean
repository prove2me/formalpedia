-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7b806e57-41cb-5854-8026-7e47cae04868

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace GoodClassDescent

private theorem degree_eq_sum_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    D.degree = D.sum (fun _ c => c) := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  exact Finset.sum_congr rfl fun v _ => by
    simp only [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one]

private theorem sum_mapDomain {α β M : Type*} [AddCommMonoid M] (f : α → β) (D : α →₀ M) :
    (Finsupp.mapDomain f D).sum (fun _ c => c) = D.sum (fun _ c => c) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

private theorem degree_mapDomain_of_deg_eq_one {K F K' F' : Type*} [Field K] [Field F]
    [Algebra K F] [Field K'] [Field F'] [Algebra K' F'] (hup : ∀ V : Place K F, V.deg = 1)
    (hdn : ∀ w : Place K' F', w.deg = 1) (f : Place K F → Place K' F') (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain f D) = Divisor.degree D := by
  rw [degree_eq_sum_of_deg_eq_one hdn, degree_eq_sum_of_deg_eq_one hup, sum_mapDomain]

private theorem mapDomain_apply_eq_zero {α β : Type*} (f : α → β) (v : α →₀ ℤ) (y : β)
    (h : ∀ a ∈ v.support, f a ≠ y) : Finsupp.mapDomain f v y = 0 := by
  classical
  by_contra h0
  obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp
    (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr h0))
  exact h a ha hfa

private theorem smul_eq_zero_of_comp {H Φ : Type*} [AddCommGroup H] [AddCommGroup Φ]
    (comp : H →+ Φ) {y x : H} {d : ℤ} {g : Φ} (hyx : y = x) (hlaw : comp y = d • g)
    (hx : comp x = 0) : d • g = 0 := by
  subst hyx
  rw [hlaw] at hx
  exact hx

section ORD

variable {ι : Type*} [Fintype ι]

theorem single_sub_single_mem_characterLattice [DecidableEq ι] (x y : ι) :
    (Pi.single x 1 - Pi.single y 1 : ι → ℤ) ∈ characterLattice ι := by
  rw [ModularCurve.mem_characterLattice]
  simp [Pi.single_apply, Finset.sum_sub_distrib]

theorem sum_mul_single_sub_single [DecidableEq ι] (a : ι → ℤ) (x y : ι) :
    ∑ j, a j * (Pi.single x 1 - Pi.single y 1 : ι → ℤ) j = a x - a y := by
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, mul_ite]

theorem nsmul_smul_proj_comp_subtype_apply (n : ℕ) (a : ℤ) (s₀ : ι)
    (D : characterLattice ι) :
    (n • (a • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) D =
      (n : ℤ) * (a * (D : ι → ℤ) s₀) := by
  simp

theorem gramMap_apply' (e : ι → ℕ) (ξ D : characterLattice ι) :
    gramMap e ξ D = ∑ x, (e x : ℤ) * (ξ : ι → ℤ) x * (D : ι → ℤ) x := by
  rw [ModularCurve.gramMap_apply]
  exact Finset.sum_congr rfl fun x _ => (mul_assoc _ _ _).symm

theorem componentGroupProj_eq_zero_iff (e : ι → ℕ) (φ : Module.Dual ℤ (characterLattice ι)) :
    componentGroupProj e φ = 0 ↔ φ ∈ LinearMap.range (gramMap e) :=
  Submodule.Quotient.mk_eq_zero _

theorem nsmul_smul_coord_mem_range_gramMap_iff (e : ι → ℕ) (he : ∀ s, 0 < e s) (s₀ : ι) (n : ℕ) :
    n • ((e s₀ : ℤ) • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype) ∈
        LinearMap.range (gramMap e) ↔
      (∑ s : ι, Finset.univ.lcm e / e s) ∣ n := by
  haveI : DecidableEq ι := Classical.decEq ι
  have hdvd : ∀ s, e s ∣ Finset.univ.lcm e := fun s => Finset.dvd_lcm (Finset.mem_univ s)
  have hmul : ∀ s, (e s : ℤ) * ((Finset.univ.lcm e / e s : ℕ) : ℤ) = ((Finset.univ.lcm e : ℕ) : ℤ) :=
    fun s => by exact_mod_cast Nat.mul_div_cancel' (hdvd s)
  have he0 : ∀ s, (e s : ℤ) ≠ 0 := fun s => by exact_mod_cast (he s).ne'
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ξ, hξ⟩

    have hev : ∀ D : characterLattice ι,
        ∑ x, (e x : ℤ) * (ξ : ι → ℤ) x * (D : ι → ℤ) x = (n : ℤ) * ((e s₀ : ℤ) * (D : ι → ℤ) s₀) := by
      intro D
      rw [← gramMap_apply', hξ, nsmul_smul_proj_comp_subtype_apply]

    have hκ : ∀ x, x ≠ s₀ →
        (e x : ℤ) * (ξ : ι → ℤ) x = (e s₀ : ℤ) * (ξ : ι → ℤ) s₀ - (n : ℤ) * (e s₀ : ℤ) := by
      intro x hx
      have h1 : ∑ j, (e j : ℤ) * (ξ : ι → ℤ) j * (Pi.single x 1 - Pi.single s₀ 1 : ι → ℤ) j =
          (n : ℤ) * ((e s₀ : ℤ) * (Pi.single x 1 - Pi.single s₀ 1 : ι → ℤ) s₀) :=
        hev ⟨_, single_sub_single_mem_characterLattice x s₀⟩
      rw [sum_mul_single_sub_single (fun j => (e j : ℤ) * (ξ : ι → ℤ) j) x s₀, Pi.sub_apply,
        Pi.single_eq_of_ne (Ne.symm hx), Pi.single_eq_same] at h1
      linarith

    have hdivκ : ∀ x, (e x : ℤ) ∣ (e s₀ : ℤ) * (ξ : ι → ℤ) s₀ - (n : ℤ) * (e s₀ : ℤ) := by
      intro x
      by_cases hx : x = s₀
      · subst hx
        exact ⟨(ξ : ι → ℤ) x - n, by ring⟩
      · exact ⟨(ξ : ι → ℤ) x, (hκ x hx).symm⟩
    have hL : ((Finset.univ.lcm e : ℕ) : ℤ) ∣ (e s₀ : ℤ) * (ξ : ι → ℤ) s₀ - (n : ℤ) * (e s₀ : ℤ) := by
      rw [Int.natCast_dvd]
      exact Finset.lcm_dvd fun x _ => Int.natCast_dvd.mp (hdivκ x)
    obtain ⟨t, ht⟩ := hL

    have hcoord : ∀ x, (ξ : ι → ℤ) x =
        ((Finset.univ.lcm e / e x : ℕ) : ℤ) * t + if x = s₀ then (n : ℤ) else 0 := by
      intro x
      by_cases hx : x = s₀
      · subst hx
        rw [if_pos rfl]
        apply mul_left_cancel₀ (he0 x)
        rw [mul_add, ← mul_assoc, hmul]
        linarith
      · rw [if_neg hx, add_zero]
        apply mul_left_cancel₀ (he0 x)
        rw [← mul_assoc, hmul, hκ x hx]
        exact ht

    have hsum : ∑ x, (ξ : ι → ℤ) x = 0 := ModularCurve.mem_characterLattice.mp ξ.2
    have hsum' : ∑ x, (ξ : ι → ℤ) x = (∑ x, ((Finset.univ.lcm e / e x : ℕ) : ℤ)) * t + n := by
      rw [Finset.sum_congr rfl fun x _ => hcoord x, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    rw [← Int.natCast_dvd_natCast, Nat.cast_sum]
    exact ⟨-t, by linarith⟩
  · rintro ⟨t, ht⟩
    have ht' : (n : ℤ) = (∑ x, ((Finset.univ.lcm e / e x : ℕ) : ℤ)) * (t : ℤ) := by
      rw [ht, Nat.cast_mul, Nat.cast_sum]
    refine ⟨⟨fun x => -(((Finset.univ.lcm e / e x : ℕ) : ℤ) * (t : ℤ)) +
      (if x = s₀ then (n : ℤ) else 0), ?_⟩, ?_⟩
    · rw [ModularCurve.mem_characterLattice]
      show ∑ x, (-(((Finset.univ.lcm e / e x : ℕ) : ℤ) * (t : ℤ)) +
        (if x = s₀ then (n : ℤ) else 0)) = 0
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← ht', neg_add_cancel]
    · refine LinearMap.ext fun D => ?_
      have hD : ∑ x, (D : ι → ℤ) x = 0 := ModularCurve.mem_characterLattice.mp D.2
      rw [gramMap_apply', nsmul_smul_proj_comp_subtype_apply]
      show ∑ x, (e x : ℤ) * (-(((Finset.univ.lcm e / e x : ℕ) : ℤ) * (t : ℤ)) +
          (if x = s₀ then (n : ℤ) else 0)) * (D : ι → ℤ) x = (n : ℤ) * ((e s₀ : ℤ) * (D : ι → ℤ) s₀)
      have hpt : ∀ x, (e x : ℤ) * (-(((Finset.univ.lcm e / e x : ℕ) : ℤ) * (t : ℤ)) +
          (if x = s₀ then (n : ℤ) else 0)) * (D : ι → ℤ) x =
          -((((Finset.univ.lcm e : ℕ) : ℤ) * (t : ℤ)) * (D : ι → ℤ) x) +
          (if x = s₀ then (e s₀ : ℤ) * (n : ℤ) * (D : ι → ℤ) x else 0) := by
        intro x
        by_cases hx : x = s₀
        · subst hx
          rw [if_pos rfl, if_pos rfl, mul_add, add_mul, mul_neg, ← mul_assoc, hmul, neg_mul]
        · rw [if_neg hx, if_neg hx, add_zero, add_zero, mul_neg, ← mul_assoc, hmul, neg_mul]
      rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, hD, mul_zero, neg_zero, zero_add, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _)]
      ring

theorem addOrderOf_componentGroupProj_smul_coord {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (he : ∀ s, 0 < e s) (s₀ : ι) :
    addOrderOf (componentGroupProj e ((e s₀ : ℤ) •
      (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) =
      ∑ s : ι, Finset.univ.lcm e / e s := by
  have key : ∀ n : ℕ, addOrderOf (componentGroupProj e ((e s₀ : ℤ) •
      (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) ∣ n ↔
      (∑ s : ι, Finset.univ.lcm e / e s) ∣ n := by
    intro n
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul, componentGroupProj_eq_zero_iff]
    exact nsmul_smul_coord_mem_range_gramMap_iff e he s₀ n
  exact Nat.dvd_antisymm ((key _).mpr dvd_rfl) ((key _).mp dvd_rfl)

end ORD

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem not_isStrictFst_and_isStrictSnd
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    ¬ (P.IsStrictFst V ∧ P.IsStrictSnd V) := by
  rintro ⟨⟨h1, h2⟩, h3, -⟩
  exact h2 ((congrArg (frobOnPlacesGeomLevel k N data hKr) h1).trans h3.symm)

private theorem fstDiv_add_sndDiv
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hD : P.IsGoodDiv D) :
    P.fstDiv D + P.sndDiv D = D := by
  classical
  ext V
  rw [Finsupp.add_apply]
  simp only [PlaceSpecialization.fstDiv, PlaceSpecialization.sndDiv, Finsupp.filter_apply]
  by_cases hV : V ∈ D.support
  · rcases hD V hV with h | h
    · rw [if_pos h, if_neg fun h' => not_isStrictFst_and_isStrictSnd P V ⟨h, h'⟩, add_zero]
    · rw [if_neg fun h' => not_isStrictFst_and_isStrictSnd P V ⟨h', h⟩, if_pos h, zero_add]
  · have h0 : D V = 0 := by
      by_contra hne
      exact hV (Finsupp.mem_support_iff.mpr hne)
    rw [h0]
    simp

private theorem fstDiv_add
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.fstDiv (D + D') = P.fstDiv D + P.fstDiv D' := by
  classical
  simp only [PlaceSpecialization.fstDiv]
  exact Finsupp.filter_add

private theorem sndDiv_add
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.sndDiv (D + D') = P.sndDiv D + P.sndDiv D' := by
  classical
  simp only [PlaceSpecialization.sndDiv]
  exact Finsupp.filter_add

private theorem fstDiv_zsmul
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (t : ℤ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.fstDiv (t • D) = t • P.fstDiv D := by
  classical
  ext V
  simp only [PlaceSpecialization.fstDiv, Finsupp.filter_apply, Finsupp.smul_apply]
  split_ifs
  · rfl
  · exact (smul_zero t).symm

private theorem sndDiv_zsmul
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (t : ℤ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.sndDiv (t • D) = t • P.sndDiv D := by
  classical
  ext V
  simp only [PlaceSpecialization.sndDiv, Finsupp.filter_apply, Finsupp.smul_apply]
  split_ifs
  · rfl
  · exact (smul_zero t).symm

private theorem isGoodDiv_add
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hD : P.IsGoodDiv D) (hD' : P.IsGoodDiv D') : P.IsGoodDiv (D + D') := by
  classical
  intro V hV
  rcases Finset.mem_union.mp (Finsupp.support_add hV) with h | h
  · exact hD V h
  · exact hD' V h

private theorem isGoodDiv_zsmul
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (t : ℤ) {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hD : P.IsGoodDiv D) : P.IsGoodDiv (t • D) := by
  intro V hV
  refine hD V ?_
  rw [Finsupp.mem_support_iff] at hV ⊢
  intro h0
  exact hV (by rw [Finsupp.smul_apply, h0, smul_zero])

private theorem mapDomain_fstDiv_apply_eq_zero [IsAlgClosed k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hfix : ∀ w ∈ W, arithFrobC q k N • (arithFrobC q k N • w) = w)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)}
    (hs : s ∈ nodePairsOfPlaces (arithFrobC q k N) W) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv D) s.1 = 0 := by
  classical
  have hfixφ : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr s.1)
      = s.1 := by
    rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel, ← arithFrobC_smul_eq_frobOnPlacesGeomLevel]
    exact hfix s.1 (fst_mem_of_mem_nodePairsOfPlaces hs)
  refine mapDomain_apply_eq_zero _ _ _ fun V hV hEq => ?_
  have hVs : P.IsStrictFst V := by
    by_contra hcon
    refine Finsupp.mem_support_iff.mp hV ?_
    simp only [PlaceSpecialization.fstDiv, Finsupp.filter_apply]
    exact if_neg hcon
  exact hVs.2 (by rw [hEq]; exact hfixφ)

private theorem mapDomain_sndDiv_apply_eq_zero [IsAlgClosed k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hfix : ∀ w ∈ W, arithFrobC q k N • (arithFrobC q k N • w) = w)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)}
    (hs : s ∈ nodePairsOfPlaces (arithFrobC q k N) W) :
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D) s.2 = 0 := by
  classical
  have hfixφ1 : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr s.1)
      = s.1 := by
    rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel, ← arithFrobC_smul_eq_frobOnPlacesGeomLevel]
    exact hfix s.1 (fst_mem_of_mem_nodePairsOfPlaces hs)
  have hfixφ2 : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr s.2)
      = s.2 := by
    rw [snd_eq_of_mem_nodePairsOfPlaces hs, arithFrobC_smul_eq_frobOnPlacesGeomLevel]
    exact congrArg (frobOnPlacesGeomLevel k N data hKr) hfixφ1
  refine mapDomain_apply_eq_zero _ _ _ fun V hV hEq => ?_
  have hVs : P.IsStrictSnd V := by
    by_contra hcon
    refine Finsupp.mem_support_iff.mp hV ?_
    simp only [PlaceSpecialization.sndDiv, Finsupp.filter_apply]
    exact if_neg hcon
  exact hVs.2 (by rw [hEq]; exact hfixφ2)

theorem isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv [IsAlgClosed k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hfix : ∀ w ∈ W, arithFrobC q k N • (arithFrobC q k N • w) = w)
    (hW0 : W.Nonempty)
    (e : Place k (modularFunctionFieldC k N) → ℕ) (hpos : ∀ w ∈ W, 0 < e w)
    (comp : ↥(inertiaInvariants A (N * q)) →+
      componentGroup (widthOfPlaces (arithFrobC q k N) W e))
    (hlaw : ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
          (F := ↥(modularFunctionFieldBar (N * q)))))
        (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
        P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
        ∀ s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
          comp ⟨Pic0.mk D, hH⟩ =
            (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).degree •
              componentGroupProj (widthOfPlaces (arithFrobC q k N) W e)
                ((widthOfPlaces (arithFrobC q k N) W e s₀ : ℤ) •
                  (LinearMap.proj s₀ : (↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℤ) →ₗ[ℤ] ℤ).comp
                    (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)).subtype))
    (hG : ∃ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        Divisor.IsPrincipal G ∧ P.IsGoodDiv G ∧
          (P.fstDiv G).degree = ((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) ∧
          (P.sndDiv G).degree = -((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ))
    (x : ↥(inertiaInvariants A (N * q)))
    (hrep : ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
            Pic0.mk D = (x : JZero (N * q)))
    (hx : comp x = 0) :
    P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (x : JZero (N * q)) := by
  classical
  obtain ⟨D, hgD, hmD⟩ := hrep
  obtain ⟨G, hGprin, hGgood, hGfst, hGsnd⟩ := hG
  have hH : Pic0.mk D ∈ inertiaInvariants A (N * q) := hmD ▸ x.2
  have hxD : (⟨Pic0.mk D, hH⟩ : ↥(inertiaInvariants A (N * q))) = x := Subtype.ext hmD
  obtain ⟨w0, hw0⟩ := hW0
  have hup := deg_eq_one_modularFunctionFieldBar (N * q)
  have hdn := place_deg_eq_one_of_isAlgClosed k N
  have hord := addOrderOf_componentGroupProj_smul_coord
    (widthOfPlaces (arithFrobC q k N) W e)
    (fun s => hpos _ (fst_mem_of_mem_nodePairsOfPlaces s.2))
    ⟨smulNodePair (arithFrobC q k N) w0, smulNodePair_mem_nodePairsOfPlaces _ hw0⟩
  have hdvd : ((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
        Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) /
          widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) ∣
      Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)))) := by
    rw [← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr
      (smul_eq_zero_of_comp comp hxD
        (hlaw D hH hgD ⟨smulNodePair (arithFrobC q k N) w0,
          smulNodePair_mem_nodePairsOfPlaces _ hw0⟩) hx)
  obtain ⟨t, ht⟩ := hdvd
  have hsum : Divisor.degree (P.fstDiv (D : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)))) +
      Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)))) = 0 := by
    rw [← map_add, fstDiv_add_sndDiv P hgD]
    exact Divisor.mem_degZero.mp D.2
  have hfst : Divisor.degree (P.fstDiv (D : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)))) =
      -Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)))) :=
    eq_neg_of_add_eq_zero_left hsum
  have hGdeg0 : G ∈ Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, ← fstDiv_add_sndDiv P hGgood, map_add, hGfst, hGsnd]
    ring
  have hGz0 : Pic0.mk (⟨G, hGdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ↥(modularFunctionFieldBar (N * q))))) = 0 := by
    have h1 := Pic0.zsmul_mk_eq_zero_of_isPrincipal
      (⟨G, hGdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q))))) 1 (by rw [one_smul]; exact hGprin)
    rwa [one_smul] at h1
  refine ⟨D + t • ⟨G, hGdeg0⟩, ?_, ?_, ?_⟩
  · show P.IsGoodDiv ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      + t • G)
    exact isGoodDiv_add P hgD (isGoodDiv_zsmul P t hGgood)
  · show P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
        ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + t • G)
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W)
    refine (GluingData.mem_admissible _).mpr
      ⟨?_, ?_, fun s hs => ⟨mapDomain_fstDiv_apply_eq_zero P W hfix _ hs,
        mapDomain_sndDiv_apply_eq_zero P W hfix _ hs⟩⟩
    · show Finsupp.mapDomain P.reduceFst (P.fstDiv
          ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + t • G))
        ∈ Divisor.degZero (K := k) (F := ↥(modularFunctionFieldC k N))
      rw [Divisor.mem_degZero, degree_mapDomain_of_deg_eq_one hup hdn, fstDiv_add P,
        fstDiv_zsmul P, map_add, map_zsmul, hGfst, hfst, ht]
      simp only [zsmul_eq_mul, Int.cast_id]
      ring
    · show Finsupp.mapDomain P.reduceSnd (P.sndDiv
          ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + t • G))
        ∈ Divisor.degZero (K := k) (F := ↥(modularFunctionFieldC k N))
      rw [Divisor.mem_degZero, degree_mapDomain_of_deg_eq_one hup hdn, sndDiv_add P,
        sndDiv_zsmul P, map_add, map_zsmul, hGsnd, ht]
      simp only [zsmul_eq_mul, Int.cast_id]
      ring
  · have hzs : Pic0.mk (t • (⟨G, hGdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q)))))) =
        t • Pic0.mk (⟨G, hGdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q))))) :=
      map_zsmul (AddMonoidHom.mk' (Pic0.mk (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q)))) fun a b => Pic0.mk_add a b) t _
    rw [Pic0.mk_add, hzs, hGz0, smul_zero, add_zero]
    exact hmD

end GoodClassDescent

theorem solution (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hfix : ∀ w ∈ W, arithFrobC q k N • (arithFrobC q k N • w) = w)
    (hW0 : W.Nonempty)
    (e : Place k (modularFunctionFieldC k N) → ℕ) (hpos : ∀ w ∈ W, 0 < e w)
    (comp : ↥(inertiaInvariants A (N * q)) →+
      componentGroup (widthOfPlaces (arithFrobC q k N) W e))
    (hlaw : ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
          (F := ↥(modularFunctionFieldBar (N * q)))))
        (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
        P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
        ∀ s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
          comp ⟨Pic0.mk D, hH⟩ =
            (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).degree •
              componentGroupProj (widthOfPlaces (arithFrobC q k N) W e)
                ((widthOfPlaces (arithFrobC q k N) W e s₀ : ℤ) •
                  (LinearMap.proj s₀ : (↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℤ) →ₗ[ℤ] ℤ).comp
                    (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)).subtype))
    (hG : ∃ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        Divisor.IsPrincipal G ∧ P.IsGoodDiv G ∧
          (P.fstDiv G).degree = ((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) ∧
          (P.sndDiv G).degree = -((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ))
    (x : ↥(inertiaInvariants A (N * q)))
    (hrep : ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
            Pic0.mk D = (x : JZero (N * q)))
    (hx : comp x = 0) :
    P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (x : JZero (N * q)) :=
  GoodClassDescent.isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv P W hfix hW0 e hpos comp
    hlaw hG x hrep hx

end

end S_ModularCurve_PlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv (solution)
