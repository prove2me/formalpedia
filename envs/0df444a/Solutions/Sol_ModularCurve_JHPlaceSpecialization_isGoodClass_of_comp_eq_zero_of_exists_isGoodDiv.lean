-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0491589d-3750-58d1-8695-9f85751811a0

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Pic0_zsmul_mk_eq_zero_of_isPrincipal
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace GoodClassDescentH

theorem degree_eq_sum_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    D.degree = D.sum (fun _ c => c) := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  exact Finset.sum_congr rfl fun v _ => by
    simp only [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one]

theorem sum_mapDomain {α β M : Type*} [AddCommMonoid M] (f : α → β) (D : α →₀ M) :
    (Finsupp.mapDomain f D).sum (fun _ c => c) = D.sum (fun _ c => c) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem degree_mapDomain_of_deg_eq_one {K F K' F' : Type*} [Field K] [Field F]
    [Algebra K F] [Field K'] [Field F'] [Algebra K' F'] (hup : ∀ V : Place K F, V.deg = 1)
    (hdn : ∀ w : Place K' F', w.deg = 1) (f : Place K F → Place K' F') (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain f D) = Divisor.degree D := by
  rw [degree_eq_sum_of_deg_eq_one hdn, degree_eq_sum_of_deg_eq_one hup, sum_mapDomain]

theorem mapDomain_apply_eq_zero {α β : Type*} (f : α → β) (v : α →₀ ℤ) (y : β)
    (h : ∀ a ∈ v.support, f a ≠ y) : Finsupp.mapDomain f v y = 0 := by
  classical
  by_contra h0
  obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp
    (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr h0))
  exact h a ha hfa

theorem smul_eq_zero_of_comp {H Φ : Type*} [AddCommGroup H] [AddCommGroup Φ]
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

section Floors

scoped instance finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem deg_eq_one_up (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 := by
  obtain ⟨x, htr, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  exact IsCurveOver.forall_deg_eq_one_of_isAlgClosed

theorem deg_eq_one_down (p M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] :
    ∀ w : Place κ (JHNeronObjectAtP.Fbar p M H hpM κ), w.deg = 1 := by
  haveI : (JHNeronObjectAtP.ΓN p M H hpM).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  haveI : IsCurveOver κ (JHNeronObjectAtP.Fbar p M H hpM κ) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed κ (JHNeronObjectAtP.ΓN p M H hpM)
      (ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM))
  exact IsCurveOver.forall_deg_eq_one_of_isAlgClosed

end Floors

section Kit

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

variable (P : JHPlaceSpecialization p M H hpM A) (α β : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

theorem not_isStrictFst_and_isStrictSnd (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    ¬ (P.IsStrictFst α β hα hβ δ V ∧ P.IsStrictSnd α β hα hβ δ V) := by
  rintro ⟨⟨h1, h2⟩, h3, -⟩
  apply h2
  show qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
      (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (P.reduceFst α hα V))) = P.reduceFst α hα V
  rw [h1]
  exact h3.symm

theorem fstDiv_add_sndDiv {D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hD : P.IsGoodDiv α β hα hβ δ D) :
    P.fstDiv α β hα hβ δ D + P.sndDiv α β hα hβ δ D = D := by
  classical
  ext V
  rw [Finsupp.add_apply]
  simp only [JHPlaceSpecialization.fstDiv, JHPlaceSpecialization.sndDiv, Finsupp.filter_apply]
  by_cases hV : V ∈ D.support
  · rcases hD V hV with h | h
    · rw [if_pos h, if_neg fun h' => not_isStrictFst_and_isStrictSnd P α β hα hβ δ V ⟨h, h'⟩, add_zero]
    · rw [if_neg fun h' => not_isStrictFst_and_isStrictSnd P α β hα hβ δ V ⟨h', h⟩, if_pos h, zero_add]
  · have h0 : D V = 0 := by
      by_contra hne
      exact hV (Finsupp.mem_support_iff.mpr hne)
    rw [h0]
    simp

theorem fstDiv_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    P.fstDiv α β hα hβ δ (D + D') = P.fstDiv α β hα hβ δ D + P.fstDiv α β hα hβ δ D' := by
  classical
  simp only [JHPlaceSpecialization.fstDiv]
  exact Finsupp.filter_add

theorem sndDiv_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    P.sndDiv α β hα hβ δ (D + D') = P.sndDiv α β hα hβ δ D + P.sndDiv α β hα hβ δ D' := by
  classical
  simp only [JHPlaceSpecialization.sndDiv]
  exact Finsupp.filter_add

theorem fstDiv_zsmul (t : ℤ) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    P.fstDiv α β hα hβ δ (t • D) = t • P.fstDiv α β hα hβ δ D := by
  classical
  ext V
  simp only [JHPlaceSpecialization.fstDiv, Finsupp.filter_apply, Finsupp.smul_apply]
  split_ifs
  · rfl
  · exact (smul_zero t).symm

theorem sndDiv_zsmul (t : ℤ) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    P.sndDiv α β hα hβ δ (t • D) = t • P.sndDiv α β hα hβ δ D := by
  classical
  ext V
  simp only [JHPlaceSpecialization.sndDiv, Finsupp.filter_apply, Finsupp.smul_apply]
  split_ifs
  · rfl
  · exact (smul_zero t).symm

theorem isGoodDiv_add {D D' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)}
    (hD : P.IsGoodDiv α β hα hβ δ D) (hD' : P.IsGoodDiv α β hα hβ δ D') : P.IsGoodDiv α β hα hβ δ (D + D') := by
  classical
  intro V hV
  rcases Finset.mem_union.mp (Finsupp.support_add hV) with h | h
  · exact hD V h
  · exact hD' V h

theorem isGoodDiv_zsmul (t : ℤ) {D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)}
    (hD : P.IsGoodDiv α β hα hβ δ D) : P.IsGoodDiv α β hα hβ δ (t • D) := by
  intro V hV
  refine hD V ?_
  rw [Finsupp.mem_support_iff] at hV ⊢
  intro h0
  exact hV (by rw [Finsupp.smul_apply, h0, smul_zero])

theorem mapDomain_fstDiv_apply_eq_zero
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hfix : ∀ s ∈ SS, JHPlaceSpecialization.Fixed p M H hpM A δ s.1 ∧ JHPlaceSpecialization.Fixed p M H hpM A δ s.2)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) {s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))} (hs : s ∈ SS) :
    Finsupp.mapDomain (P.reduceFst α hα) (P.fstDiv α β hα hβ δ D) s.1 = 0 := by
  classical
  refine mapDomain_apply_eq_zero _ _ _ fun V hV hEq => ?_
  have hVs : P.IsStrictFst α β hα hβ δ V := by
    by_contra hcon
    refine Finsupp.mem_support_iff.mp hV ?_
    simp only [JHPlaceSpecialization.fstDiv, Finsupp.filter_apply]
    exact if_neg hcon
  exact hVs.2 (by rw [hEq]; exact (hfix s hs).1)

theorem mapDomain_sndDiv_apply_eq_zero
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hfix : ∀ s ∈ SS, JHPlaceSpecialization.Fixed p M H hpM A δ s.1 ∧ JHPlaceSpecialization.Fixed p M H hpM A δ s.2)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) {s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))} (hs : s ∈ SS) :
    Finsupp.mapDomain (P.reduceSnd β hβ δ) (P.sndDiv α β hα hβ δ D) s.2 = 0 := by
  classical
  refine mapDomain_apply_eq_zero _ _ _ fun V hV hEq => ?_
  have hVs : P.IsStrictSnd α β hα hβ δ V := by
    by_contra hcon
    refine Finsupp.mem_support_iff.mp hV ?_
    simp only [JHPlaceSpecialization.sndDiv, Finsupp.filter_apply]
    exact if_neg hcon
  exact hVs.2 (by rw [hEq]; exact (hfix s hs).2)

end Kit

end GoodClassDescentH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv.GoodClassDescentH"

end
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv.GoodClassDescentH"

open GoodClassDescentH in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hfix : ∀ s ∈ SS, JHPlaceSpecialization.Fixed p M H hpM A δ s.1 ∧ JHPlaceSpecialization.Fixed p M H hpM A δ s.2)
    (hSS0 : SS.Nonempty)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (e : ↥SS → ℕ) (hpos : ∀ s, 0 < e s)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e)
    (hlaw : ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
        (hI : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A),
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        ∀ s₀ : ↥SS,
          comp ⟨Pic0.mk D, hI⟩ =
            (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).degree •
              componentGroupProj e ((e s₀ : ℤ) • (LinearMap.proj s₀ : (↥SS → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ↥SS).subtype))
    (hG : ∃ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Divisor.IsPrincipal G ∧ Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G ∧
          (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = ((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) ∧
          (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = -((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ))
    (x : ↥(JHPlaceSpecialization.inertiaInvariants M H A))
    (hrep : ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧ Pic0.mk D = (x : JH M H))
    (hx : comp x = 0) :
    Psp.IsGoodClass α (θ.toAlgHom.comp α) hα hβ δ SS (x : JH M H) := by
  classical
  obtain ⟨D, hgD, hmD⟩ := hrep
  obtain ⟨G, hGprin, hGgood, hGfst, hGsnd⟩ := hG
  have hH' : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A := hmD ▸ x.2
  have hxD : (⟨Pic0.mk D, hH'⟩ : ↥(JHPlaceSpecialization.inertiaInvariants M H A)) = x := Subtype.ext hmD
  obtain ⟨s0, hs0⟩ := hSS0
  have hup := GoodClassDescentH.deg_eq_one_up M H
  have hdn := GoodClassDescentH.deg_eq_one_down p M H hpM (ResidueField ↥A)
  have hord := GoodClassDescentH.addOrderOf_componentGroupProj_smul_coord e hpos ⟨s0, hs0⟩
  have hdvd : ((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) ∣
      Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) := by
    rw [← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr
      (GoodClassDescentH.smul_eq_zero_of_comp comp hxD (hlaw D hH' hgD ⟨s0, hs0⟩) hx)
  obtain ⟨t, ht⟩ := hdvd
  have hsum : Divisor.degree (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) +
      Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) = 0 := by
    rw [← map_add, GoodClassDescentH.fstDiv_add_sndDiv Psp _ _ hα hβ δ hgD]
    exact Divisor.mem_degZero.mp D.2
  have hfst : Divisor.degree (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) =
      -Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) :=
    eq_neg_of_add_eq_zero_left hsum
  have hGdeg0 : G ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
    rw [Divisor.mem_degZero, ← GoodClassDescentH.fstDiv_add_sndDiv Psp _ _ hα hβ δ hGgood, map_add, hGfst, hGsnd]
    ring
  have hGz0 : Pic0.mk (⟨G, hGdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))) = 0 := by
    have h1 := Pic0.zsmul_mk_eq_zero_of_isPrincipal
      (⟨G, hGdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))) 1 (by rw [one_smul]; exact hGprin)
    rwa [one_smul] at h1
  refine ⟨D + t • ⟨G, hGdeg0⟩, ?_, ?_, ?_⟩
  · show Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ ((D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + t • G)
    exact GoodClassDescentH.isGoodDiv_add Psp _ _ hα hβ δ hgD (GoodClassDescentH.isGoodDiv_zsmul Psp _ _ hα hβ δ t hGgood)
  · show Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS ((D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + t • G)
      ∈ GluingData.admissible SS
    refine (GluingData.mem_admissible _).mpr
      ⟨?_, ?_, fun s hs => ⟨GoodClassDescentH.mapDomain_fstDiv_apply_eq_zero Psp _ _ hα hβ δ SS hfix _ hs,
        GoodClassDescentH.mapDomain_sndDiv_apply_eq_zero Psp _ _ hα hβ δ SS hfix _ hs⟩⟩
    · show Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ
          ((D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + t • G))
        ∈ Divisor.degZero (K := ResidueField ↥A) (F := JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
      rw [Divisor.mem_degZero, GoodClassDescentH.degree_mapDomain_of_deg_eq_one hup hdn, GoodClassDescentH.fstDiv_add Psp,
        GoodClassDescentH.fstDiv_zsmul Psp, map_add, map_zsmul, hGfst, hfst, ht]
      simp only [zsmul_eq_mul, Int.cast_id]
      ring
    · show Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ
          ((D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + t • G))
        ∈ Divisor.degZero (K := ResidueField ↥A) (F := JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
      rw [Divisor.mem_degZero, GoodClassDescentH.degree_mapDomain_of_deg_eq_one hup hdn, GoodClassDescentH.sndDiv_add Psp,
        GoodClassDescentH.sndDiv_zsmul Psp, map_add, map_zsmul, hGsnd, ht]
      simp only [zsmul_eq_mul, Int.cast_id]
      ring
  · have hzs : Pic0.mk (t • (⟨G, hGdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))) =
        t • Pic0.mk (⟨G, hGdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))) :=
      map_zsmul (AddMonoidHom.mk' (Pic0.mk (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) fun a b => Pic0.mk_add a b) t _
    rw [Pic0.mk_add, hzs, hGz0, smul_zero, add_zero]
    exact hmD

end S_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv (solution)
