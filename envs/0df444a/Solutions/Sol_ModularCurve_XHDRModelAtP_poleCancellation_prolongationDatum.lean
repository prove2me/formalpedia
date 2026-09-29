-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.poleCancellation_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ed473f74-a68b-521c-975a-2c4738b6766b

import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_poleCancellation_prolongationDatum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

noncomputable section

namespace Ws49
namespace PoleCanc

section RR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open Classical in

theorem exists_ord_bounds [IsAlgClosed K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (t₀ : Place K F) (T : Finset (Place K F)) (B : ℕ) :
    ∃ x : F, x ≠ 0 ∧ (∀ t, t ≠ t₀ → 0 ≤ t.ord x) ∧ ∀ t ∈ T, t ≠ t₀ → (B : ℤ) ≤ t.ord x := by
  obtain ⟨Kc, g, hRR⟩ := AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch K F
  have hdeg1 : ∀ w : Place K F, (w.deg : ℤ) = 1 := fun w => by
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed w, Nat.cast_one]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (Divisor.degree Kc).toNat + g + B * T.card + 1 := ⟨_, rfl⟩
  have hKn : Divisor.degree Kc ≤ (Divisor.degree Kc).toNat := Int.self_le_toNat _
  obtain ⟨E, hE⟩ : ∃ E : Divisor K F,
      E = Finsupp.single t₀ (n : ℤ) - ∑ t ∈ T, Finsupp.single t (B : ℤ) := ⟨_, rfl⟩
  have hdegE : Divisor.degree E = n - B * T.card := by
    rw [hE, map_sub, map_sum]
    simp only [Divisor.degree_single, hdeg1, mul_one, Finset.sum_const, nsmul_eq_mul]
    ring
  have hneg : Divisor.degree (Kc - E) < 0 := by
    rw [map_sub, hdegE, hn]
    push_cast
    linarith
  have hell0 : ell (Kc - E) = 0 := by
    show Module.finrank _ (LSpace _) = 0
    rw [AlgebraicCurve.lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
  have h := hRR E
  rw [hell0, hdegE, hn] at h
  have hpos : 0 < ell E := by
    push_cast at h
    have : (0 : ℤ) < ell E := by linarith
    exact_mod_cast this
  have hbot : LSpace E ≠ ⊥ := by
    intro hb
    have : ell E = 0 := by
      show Module.finrank _ (LSpace E) = 0
      rw [hb, finrank_bot]
    omega
  obtain ⟨x, hxE, hx0⟩ := (Submodule.ne_bot_iff (LSpace E)).mp hbot
  have hord : ∀ v : Place K F, -E v ≤ v.ord x := (mem_lSpace_iff_ord.mp hxE).resolve_left hx0
  have hE_out : ∀ t, t ∉ T → t ≠ t₀ → E t = 0 := by
    intro t htT ht
    rw [hE]
    simp [Finsupp.single_apply, Ne.symm ht, htT]
  have hE_in : ∀ t, t ∈ T → t ≠ t₀ → E t = -(B : ℤ) := by
    intro t htT ht
    rw [hE]
    simp [Finsupp.single_apply, Ne.symm ht, htT]
  refine ⟨x, hx0, ?_, ?_⟩
  · intro t ht
    by_cases htT : t ∈ T
    · have h1 := hE_in t htT ht
      have h2 := hord t
      omega
    · have h1 := hE_out t htT ht
      have h2 := hord t
      omega
  · intro t htT ht
    have h1 := hE_in t htT ht
    have h2 := hord t
    omega

end RR

section Balanced

variable {L F' F Fb : Type*} [Field L] [Field F'] [Field F] [Field Fb] [Algebra L F'] [Algebra L F]
  {A : ValuationSubring L} [Algebra (ResidueField ↥A) Fb]

theorem ne_zero_of_residue_ne_zero (R : RegularProlongation A F Fb) {z : F} (h : z ∈ R.integers)
    (hr : R.residue ⟨z, h⟩ ≠ 0) : z ≠ 0 := by
  rintro rfl
  exact hr (map_zero R.residue)

theorem inv_mem_and_residue_ne_zero (R : RegularProlongation A F Fb) {z : F} (h : z ∈ R.integers)
    (hr : R.residue ⟨z, h⟩ ≠ 0) : ∃ h' : z⁻¹ ∈ R.integers, R.residue ⟨z⁻¹, h'⟩ ≠ 0 := by
  have hz0 : z ≠ 0 := ne_zero_of_residue_ne_zero R h hr
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (R.isUnit_of_residue_ne_zero hr)
  have hbval : (b : F) = z⁻¹ := by
    have h1 : z * (b : F) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    exact eq_inv_of_mul_eq_one_right h1
  have hmem : z⁻¹ ∈ R.integers := hbval ▸ b.2
  refine ⟨hmem, ?_⟩
  apply R.residue_ne_zero_of_isUnit
  refine IsUnit.of_mul_eq_one ⟨z, h⟩ ?_
  apply Subtype.ext
  simp [inv_mul_cancel₀ hz0]

theorem mem_and_residue_ne_zero_of_residue_eq (R₁ R₂ : RegularProlongation A F Fb) (α : F' →ₐ[L] F)
    (φ : Fb → Fb) (hφ : ∀ y, φ y = 0 → y = 0)
    (hres : ∀ (v : F') (h₁ : α v ∈ R₁.integers) (h₂ : α v ∈ R₂.integers),
      R₂.residue ⟨α v, h₂⟩ = φ (R₁.residue ⟨α v, h₁⟩))
    (v : F') (h₁ : α v ∈ R₁.integers) (hr₁ : R₁.residue ⟨α v, h₁⟩ ≠ 0) :
    ∃ h₂ : α v ∈ R₂.integers, R₂.residue ⟨α v, h₂⟩ ≠ 0 := by
  by_cases h₂ : α v ∈ R₂.integers
  · refine ⟨h₂, ?_⟩
    rw [hres v h₁ h₂]
    exact fun h => hr₁ (hφ _ h)
  · exfalso

    have hinv₂ : (α v)⁻¹ ∈ R₂.integers := (R₂.integers.mem_or_inv_mem (α v)).resolve_left h₂
    obtain ⟨hinv₁, hrinv₁⟩ := inv_mem_and_residue_ne_zero R₁ h₁ hr₁
    have hαinv : α v⁻¹ = (α v)⁻¹ := map_inv₀ α v
    have k₁ : α v⁻¹ ∈ R₁.integers := by rw [hαinv]; exact hinv₁
    have k₂ : α v⁻¹ ∈ R₂.integers := by rw [hαinv]; exact hinv₂
    have hr₁' : R₁.residue ⟨α v⁻¹, k₁⟩ ≠ 0 := by
      have : (⟨α v⁻¹, k₁⟩ : ↥R₁.integers) = ⟨(α v)⁻¹, hinv₁⟩ := Subtype.ext hαinv
      rw [this]
      exact hrinv₁

    have hr₂' : R₂.residue ⟨α v⁻¹, k₂⟩ ≠ 0 := by
      rw [hres v⁻¹ k₁ k₂]
      exact fun h => hr₁' (hφ _ h)
    obtain ⟨hmem, -⟩ := inv_mem_and_residue_ne_zero R₂ k₂ hr₂'
    apply h₂
    have : (α v⁻¹)⁻¹ = α v := by rw [hαinv, inv_inv]
    rw [← this]
    exact hmem

theorem exists_smul_commonUnit (R₁ R₂ : RegularProlongation A F Fb) (α : F' →ₐ[L] F)
    (φ : Fb → Fb) (hφ : ∀ y, φ y = 0 → y = 0)
    (hres : ∀ (v : F') (h₁ : α v ∈ R₁.integers) (h₂ : α v ∈ R₂.integers),
      R₂.residue ⟨α v, h₂⟩ = φ (R₁.residue ⟨α v, h₁⟩))
    (x : F') (hx : x ≠ 0) :
    ∃ (c : L) (h₁ : c • α x ∈ R₁.integers) (h₂ : c • α x ∈ R₂.integers),
      R₁.residue ⟨_, h₁⟩ ≠ 0 ∧ R₂.residue ⟨_, h₂⟩ ≠ 0 := by
  have hαx : α x ≠ 0 := (map_ne_zero α).mpr hx
  obtain ⟨c, h₁, hr₁⟩ := R₁.exists_smul_mem (α x) hαx
  have e : α (c • x) = c • α x := map_smul α c x
  have h₁' : α (c • x) ∈ R₁.integers := by rw [e]; exact h₁
  have hr₁' : R₁.residue ⟨α (c • x), h₁'⟩ ≠ 0 := by
    have : (⟨α (c • x), h₁'⟩ : ↥R₁.integers) = ⟨c • α x, h₁⟩ := Subtype.ext e
    rw [this]
    exact hr₁
  obtain ⟨h₂', hr₂'⟩ := mem_and_residue_ne_zero_of_residue_eq R₁ R₂ α φ hφ hres (c • x) h₁' hr₁'
  have h₂ : c • α x ∈ R₂.integers := by rw [← e]; exact h₂'
  refine ⟨c, h₁, h₂, hr₁, ?_⟩
  have : (⟨c • α x, h₂⟩ : ↥R₂.integers) = ⟨α (c • x), h₂'⟩ := Subtype.ext e.symm
  rw [this]
  exact hr₂'

end Balanced

end Ws49.PoleCanc

end

open Ws49.PoleCanc

set_option synthInstance.maxHeartbeats 1600000 in
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
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩)) :
    (∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
        ∃ (h : ↥(xHFunctionFieldBar M H)) (hh₁ : h ∈ Rpd.R₁.integers) (hh₂ : h ∈ Rpd.R₂.integers),
          Rpd.R₁.residue ⟨h, hh₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨h, hh₂⟩ ≠ 0 ∧
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u → 0 ≤ W.ord h) ∧
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ W.ord h) ∧
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u → 0 ≤ W.ord (f * h)) ∧
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ W.ord (f * h))) := by
  classical
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (M / p)
      (infSubgroup p M H hpM)).1
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (M / p)
      (infSubgroup p M H hpM)).2
  intro f h₁ h₂ hr₁ hr₂ u

  have hφ : ∀ y : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A),
      qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p y = 0 → y = 0 := fun y hy =>
    (map_eq_zero_iff _ (qExpFrobeniusModL_injective (ResidueField ↥A) (ΓN p M H hpM) p)).mp hy
  by_cases havoid : ∃ t₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      Psp.sp t₀ ≠ qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u
  swap
  ·

    push Not at havoid
    have hsub : ∀ v w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v = w := by
      intro v w
      obtain ⟨tv, rfl⟩ := Psp.d4 v
      obtain ⟨tw, rfl⟩ := Psp.d4 w
      rw [havoid tv, havoid tw]
    have hfix : ∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v :=
      fun v => hsub _ _
    have hone₁ : Rpd.R₁.residue 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hone₂ : Rpd.R₂.residue 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
    refine ⟨1, one_mem _, one_mem _, hone₁, hone₂, ?_, ?_, ?_, ?_⟩
    · intro W hW _
      exact absurd (hfix _) hW.2
    · intro W hW _
      exact absurd (hfix _) hW.2
    · intro W hW _
      exact absurd (hfix _) hW.2
    · intro W hW _
      exact absurd (hfix _) hW.2
  obtain ⟨t₀, ht₀⟩ := havoid
  have hf0 : f ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ h₁ hr₁
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf0
  obtain ⟨S, hS⟩ : ∃ S : Finset (Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      S = D.support.filter (fun W => Psp.reduceFst α hα W =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      T = S.image (fun W => W.restrictAlong α hα) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = S.sup (fun W => (-D W).toNat) := ⟨_, rfl⟩
  obtain ⟨x, hx0, hx₁, hx₂⟩ := exists_ord_bounds t₀ T B
  obtain ⟨c, hc₁, hc₂, hres₁, hres₂⟩ := exists_smul_commonUnit Rpd.R₁ Rpd.R₂ α
    (qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p) hφ hres₂α x hx0
  have h0 : c • α x ≠ 0 := ne_zero_of_residue_ne_zero Rpd.R₁ hc₁ hres₁
  have hc0 : c ≠ 0 := Rpd.R₁.smul_const_ne_zero hc₁ hres₁
  have hαx0 : α x ≠ 0 := (map_ne_zero α).mpr hx0

  have hordc : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (c • α x) = W.ord (α x) := by
    intro W
    rw [Algebra.smul_def, W.ord_mul ((map_ne_zero _).mpr hc0) hαx0, ConstantReduction.ord_algebraMap W hc0,
      zero_add]

  have key : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ∃ e : ℕ, 0 < e ∧
      W.ord (α x) = (e : ℤ) * (W.restrictAlong α hα).ord x := by
    intro W
    refine ⟨Place.ramificationIndexAlong α W, ?_, Place.ord_restrictAlong α hα W x⟩
    letI := algebraAlong α
    haveI := isScalarTower_along α
    haveI := isIntegral_along α hα
    exact W.ramificationIndex_pos (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))

  have hnot : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u →
        W.restrictAlong α hα ≠ t₀ := by
    intro W hW h
    apply ht₀
    rw [← h]
    exact hW

  have hfree : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u →
        0 ≤ W.ord (α x) := by
    intro W hW
    obtain ⟨e, he, heq⟩ := key W
    rw [heq]
    exact mul_nonneg (by omega) (hx₁ _ (hnot W hW))
  have hcancel : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u →
        0 ≤ W.ord f + W.ord (α x) := by
    intro W hW
    have hWt₀ := hnot W hW
    obtain ⟨e, he, heq⟩ := key W
    have hordf : W.ord f = D W := (hD W).symm
    have hxnn : 0 ≤ (W.restrictAlong α hα).ord x := hx₁ _ hWt₀
    have hex : (W.restrictAlong α hα).ord x ≤ (e : ℤ) * (W.restrictAlong α hα).ord x :=
      le_mul_of_one_le_left hxnn (by omega)
    rw [heq]
    by_cases hpole : D W < 0
    · have hWS : W ∈ S := by
        rw [hS]
        exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by omega), hW⟩
      have hWT : W.restrictAlong α hα ∈ T := by
        rw [hT]
        exact Finset.mem_image_of_mem _ hWS
      have hBW : (-D W).toNat ≤ B := by
        rw [hB]
        exact Finset.le_sup (f := fun W => (-D W).toNat) hWS
      have hxW := hx₂ _ hWT hWt₀
      omega
    · have := mul_nonneg (by omega : (0 : ℤ) ≤ e) hxnn
      omega

  have hsnd : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u →
        Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u := by
    intro W hW hWu
    rw [hW.1, hWu]
  refine ⟨c • α x, hc₁, hc₂, hres₁, hres₂, ?_, ?_, ?_, ?_⟩
  · intro W _ hW
    rw [hordc]
    exact hfree W hW
  · intro W hWs hWu
    rw [hordc]
    exact hfree W (hsnd W hWs hWu)
  · intro W _ hW
    rw [W.ord_mul hf0 h0, hordc]
    exact hcancel W hW
  · intro W hWs hWu
    rw [W.ord_mul hf0 h0, hordc]
    exact hcancel W (hsnd W hWs hWu)

end S_ModularCurve_XHDRModelAtP_poleCancellation_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_poleCancellation_prolongationDatum (solution)
