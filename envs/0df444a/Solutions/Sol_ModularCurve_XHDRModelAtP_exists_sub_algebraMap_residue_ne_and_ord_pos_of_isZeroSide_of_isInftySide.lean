-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_sub_algebraMap_residue_ne_and_ord_pos_of_isZeroSide_of_isInftySide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/927c78f2-88e3-5938-8492-d13e75d9829e

import Theorems.Thm_ModularCurve_XHDRLevel_exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_sub_algebraMap_residue_ne_and_ord_pos_of_isZeroSide_of_isInftySide
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws47
namespace D3b

open AlgebraicCurve

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem isUnit_iff_ord_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

theorem hasValue_iff_eq_or_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {g : F}
    (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm
  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [isUnit_iff_ord_eq_zero v hsub h0]
    have hnn := ord_nonneg_of_mem v hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

theorem hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (n : ℕ) : u.HasValue (g ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact u.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem exists_hasValue (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) {g : ↥(xHFunctionFieldBar M H)}
    (hg : g ∈ W.toValuationSubring) : ∃ c : AlgebraicClosure ℚ, W.HasValue g c := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  have h1 : Module.finrank (AlgebraicClosure ℚ) W.ResidueField = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed W
  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) := by
    intro x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : W.ResidueField) one_ne_zero).mp h1 x
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨c, hc, -⟩ := W.exists_hasValue_of_surjective hsurj hg
  exact ⟨c, hc⟩

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (g : LaurentSeries R) : coeffMap f (qExpand R N g) = qExpand S N (coeffMap f g) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd (N := N) g hk, qExpand_coeff_of_not_dvd (N := N) (coeffMap f g) hk, map_zero]

end Ws47.D3b

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : ∃ c, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceFst α hα) c = v)
    (ft : ↥(xHFunctionFieldBar M H))
    (hft : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((ft : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W) (hWv : Psp.reduceFst α hα W = v) :
    ∃ (a : ↥A) (h₁ : ft - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers),
      ¬ v.HasValue (Rpd.R₁.residue ⟨_, h₁⟩) (0 : ResidueField ↥A) ∧
      0 < W.ord (ft - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨hc', x, x', hx, hx', τ, hτ1, hτ⟩ := hW
  have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have : τ = 0 := Subtype.ext h0
    rw [this, map_zero] at hτ1
    exact zero_ne_one hτ1
  have hτunit : IsUnit τ := by
    by_contra h
    have hm : τ ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal τ).mpr (mem_nonunits_iff.mpr h)
    rw [(IsLocalRing.residue_eq_zero_iff τ).mpr hm] at hτ1
    exact zero_ne_one hτ1
  have hτinvA : ((τ : AlgebraicClosure ℚ))⁻¹ ∈ A := by
    obtain ⟨u, hu⟩ := hτunit
    have h1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * (τ : AlgebraicClosure ℚ) = 1 := by
      rw [← hu]; exact_mod_cast congrArg (fun t : ↥A => (t : AlgebraicClosure ℚ)) u.inv_mul
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact ((u⁻¹ : (↥A)ˣ) : ↥A).2

  have hq0 : x / x' ^ p ≠ 0 := hτ.ne_zero hτ0
  have hx0 : x ≠ 0 := fun h => hq0 (by rw [h, zero_div])
  have hx'0 : x' ≠ 0 := fun h => hq0 (by rw [h, zero_pow (NeZero.ne p), div_zero])

  have hx'nc : ∀ c : AlgebraicClosure ℚ, x' ≠ algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c := by
    intro c h
    have h1 : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff ((p : ℤ) * (-1)) = 1 := by
      rw [hx', qExpand_coeff_mul, ModularCurve.coeff_jqModC_neg_one]
    have h2 : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff ((p : ℤ) * (-1)) = 0 := by
      rw [h]
      show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c).coeff ((p : ℤ) * (-1)) = 0
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne]
      have : (p : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
      omega
    rw [h1] at h2
    exact one_ne_zero h2

  have hx'inv_mem : x'⁻¹ ∈ W.toValuationSubring := by
    refine Ws47.D3b.mem_of_ord_nonneg W (inv_ne_zero hx'0) ?_
    rw [W.ord_inv]
    have h := hc' x' hx' 0
    simp only [ZeroMemClass.coe_zero, map_zero, sub_zero] at h
    omega
  obtain ⟨d, hd⟩ := Ws47.D3b.exists_hasValue M H W hx'inv_mem
  have hdkey : d ∈ A ∧ ∀ hdA : d ∈ A, IsLocalRing.residue ↥A ⟨d, hdA⟩ = 0 := by

    have hnot : ¬ (d ≠ 0 ∧ d⁻¹ ∈ A) := by
      rintro ⟨hd0, hdinv⟩
      have hval : W.HasValue x' d⁻¹ := by
        have h := hd.inv hd0
        rwa [inv_inv] at h
      rcases (Ws47.D3b.hasValue_iff_eq_or_ord_sub_pos W hval.mem _).mp hval with heq | hpos
      · exact hx'nc _ heq
      · have h := hc' x' hx' ⟨d⁻¹, hdinv⟩
        exact absurd h (not_le.mpr hpos)
    have hdA : d ∈ A := by
      rcases A.mem_or_inv_mem d with h | h
      · exact h
      · by_cases hd0 : d = 0
        · rw [hd0]; exact zero_mem _
        · exact absurd ⟨hd0, h⟩ hnot
    refine ⟨hdA, fun hdA' => ?_⟩
    by_cases hd0 : d = 0
    · have : (⟨d, hdA'⟩ : ↥A) = 0 := Subtype.ext hd0
      rw [this, map_zero]
    · rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hnot
      refine ⟨hd0, ?_⟩
      obtain ⟨u, hu⟩ := hu
      have h1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * d = 1 := by
        have := congrArg (fun t : ↥A => (t : AlgebraicClosure ℚ)) u.inv_mul
        rw [hu] at this
        first | simpa using this | exact_mod_cast this
      rw [← eq_inv_of_mul_eq_one_left h1]
      exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  obtain ⟨hdA, hdres⟩ := hdkey

  obtain ⟨e, he⟩ : ∃ e : ℕ, e + 1 = p * p :=
    ⟨p * p - 1, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne p)))⟩
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, zero_add] at he
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    nlinarith
  have hftid : ft = (x / x' ^ p)⁻¹ ^ p * x'⁻¹ ^ e := by
    apply Subtype.ext
    have hxx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
      simpa using (Subtype.coe_injective.ne hx0 : (x : LaurentSeries (AlgebraicClosure ℚ)) ≠ ((0 : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))
    have hxx' : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
      simpa using (Subtype.coe_injective.ne hx'0 : (x' : LaurentSeries (AlgebraicClosure ℚ)) ≠ ((0 : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))
    rw [hft, ← hx', ← hx]
    push_cast
    rw [inv_div, div_pow, ← pow_mul, ← he, pow_succ]
    field_simp
    rw [← mul_pow, ← mul_pow, one_div_mul_cancel hxx, mul_one_div_cancel hxx', one_pow, one_pow]
  set c : AlgebraicClosure ℚ := ((τ : AlgebraicClosure ℚ))⁻¹ ^ p * d ^ e with hcdef
  have hcval : W.HasValue ft c := by
    rw [hftid]
    exact (Ws47.D3b.hasValue_pow W (hτ.inv hτ0) p).mul (Ws47.D3b.hasValue_pow W hd e)
  have hcA : c ∈ A := mul_mem (pow_mem hτinvA p) (pow_mem hdA e)
  have hcres : IsLocalRing.residue ↥A ⟨c, hcA⟩ = 0 := by
    have : (⟨c, hcA⟩ : ↥A) = ⟨_, hτinvA⟩ ^ p * ⟨d, hdA⟩ ^ e := Subtype.ext (by push_cast; rfl)
    rw [this, map_mul, map_pow, map_pow, hdres hdA, zero_pow he0, mul_zero]

  obtain ⟨t, y, z, ht, hy, hyz⟩ :=
    ModularCurve.XHDRLevel.exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add p M H hpM hj
  have hRQ : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap (R p) ℚ) = A.subtype.comp ρ := by
    rw [hρ]; exact (IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)).symm
  have hY : coeffMap A.subtype (coeffMap ρ y) = ((ft : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coeffMap_coeffMap, ← hRQ, ← coeffMap_coeffMap, hy, ht, map_mul, map_pow, map_inv₀,
      Ws47.D3b.coeffMap_qExpand, hft]
    have hj' : coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
    rw [hj']
  have hYmem : coeffMap A.subtype (coeffMap ρ y) ∈ xHFunctionFieldBar M H := by rw [hY]; exact ft.2
  obtain ⟨h1, hres1⟩ := Rpd.residue₁_coeffMap (coeffMap ρ y) hYmem
  have eel : (⟨coeffMap A.subtype (coeffMap ρ y), hYmem⟩ : ↥(xHFunctionFieldBar M H)) = ft := Subtype.ext hY
  have hftR : ft ∈ Rpd.R₁.integers := eel ▸ h1
  have hres_ft : Rpd.R₁.residue ⟨ft, hftR⟩ = 1 := by
    have eint : (⟨ft, hftR⟩ : Rpd.R₁.integers) = ⟨_, h1⟩ := Subtype.ext eel.symm
    apply Subtype.ext
    rw [eint, hres1, coeffMap_coeffMap, hyz, map_add, map_one]
    have hsm : coeffMap ((IsLocalRing.residue ↥A).comp ρ) (((p : ℕ) : R p) • z) = 0 := by
      ext k
      rw [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
      rfl
    rw [hsm, add_zero]
    rfl

  have hcmem : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c ∈ Rpd.R₁.integers :=
    (Rpd.R₁.algebraMap_mem_iff c).mpr hcA
  have hres_c : Rpd.R₁.residue ⟨_, hcmem⟩ = 0 := by
    have h := Rpd.R₁.residue_algebraMap ⟨c, hcA⟩
    simp only at h
    rw [h, hcres, map_zero]
  refine ⟨⟨c, hcA⟩, sub_mem hftR hcmem, ?_, ?_⟩
  ·
    have hsub : (⟨ft - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((⟨c, hcA⟩ : ↥A) : AlgebraicClosure ℚ),
        sub_mem hftR hcmem⟩ : Rpd.R₁.integers) = ⟨ft, hftR⟩ - ⟨_, hcmem⟩ := rfl
    rw [hsub, map_sub, hres_ft, hres_c, sub_zero]
    intro h0
    exact one_ne_zero ((v.hasValue_one).unique h0)
  ·
    rcases (Ws47.D3b.hasValue_iff_eq_or_ord_sub_pos W hcval.mem c).mp hcval with heq | hpos
    · exfalso
      have : (⟨ft, hftR⟩ : Rpd.R₁.integers) = ⟨_, hcmem⟩ := Subtype.ext heq
      have h := hres_ft
      rw [this, hres_c] at h
      exact zero_ne_one h
    · exact hpos

end S_ModularCurve_XHDRModelAtP_exists_sub_algebraMap_residue_ne_and_ord_pos_of_isZeroSide_of_isInftySide
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_sub_algebraMap_residue_ne_and_ord_pos_of_isZeroSide_of_isInftySide (solution)
