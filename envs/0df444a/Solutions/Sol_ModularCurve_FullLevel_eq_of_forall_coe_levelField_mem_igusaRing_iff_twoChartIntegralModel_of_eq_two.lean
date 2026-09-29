-- Prove2me | solution 1 for ModularCurve.FullLevel.eq_of_forall_coe_levelField_mem_igusaRing_iff_twoChartIntegralModel_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/94cd645b-57a5-53a7-bc15-439636366874

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

import Theorems.Thm_ValuationSubring_eq_of_constantsTower_of_forall_mem_iff
import Theorems.Thm_ValuationSubring_isIntegral_and_exists_totallyRamified_layers_of_henselian
import Theorems.Thm_ModularCurve_FullLevel_exists_smul_mem_and_inv_mem_gauss_levelField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_eq_of_forall_coe_levelField_mem_igusaRing_iff_twoChartIntegralModel_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace TraceInjAux

open IsLocalRing

theorem isDiscreteValuationRing_and_maximalIdeal_eq_of_forall_exists_mul_mem
    {K T : Type*} [Field K] [Field T] [Algebra K T]
    (W₀ : ValuationSubring T) (O : ValuationSubring K) [IsDiscreteValuationRing ↥O]
    (hO : ∀ x : K, algebraMap K T x ∈ W₀ ↔ x ∈ O) (π : ↥O) (hπ : Irreducible π)
    (hreg : ∀ f : T, f ≠ 0 → ∃ c : K, c ≠ 0 ∧ algebraMap K T c * f ∈ W₀ ∧ (algebraMap K T c * f)⁻¹ ∈ W₀) :
    IsDiscreteValuationRing ↥W₀ ∧
      maximalIdeal ↥W₀ = Ideal.span {(⟨algebraMap K T (π : K), (hO _).mpr π.2⟩ : ↥W₀)} := by
  classical
  set P : ↥W₀ := ⟨algebraMap K T (π : K), (hO _).mpr π.2⟩ with hP
  have hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hPT0 : algebraMap K T (π : K) ≠ 0 := (map_ne_zero _).mpr hπ0
  have hP0 : P ≠ 0 := fun h => hPT0 (congrArg Subtype.val h)
  have hPval : (P : T) = algebraMap K T (π : K) := rfl

  have unitOf : ∀ (y : T) (hy : y ∈ W₀), y⁻¹ ∈ W₀ → y ≠ 0 → IsUnit (⟨y, hy⟩ : ↥W₀) := fun y hy hy' hy0 =>
    IsUnit.of_mul_eq_one ⟨y⁻¹, hy'⟩ (Subtype.ext (mul_inv_cancel₀ hy0))

  have hOmem : ∀ v : ↥O, algebraMap K T (v : K) ∈ W₀ := fun v => (hO _).mpr v.2
  have hOunit : ∀ v : (↥O)ˣ, IsUnit (⟨algebraMap K T ((v : ↥O) : K), hOmem v⟩ : ↥W₀) := by
    intro v
    have hv0 : ((v : ↥O) : K) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
    refine unitOf _ _ ?_ ((map_ne_zero _).mpr hv0)
    rw [← map_inv₀, hO]
    have h1 : ((v : ↥O) : K) * (((v⁻¹ : (↥O)ˣ) : ↥O) : K) = 1 := by
      rw [← MulMemClass.coe_mul, show ((v : ↥O) * ((v⁻¹ : (↥O)ˣ) : ↥O)) = 1 from v.mul_inv, OneMemClass.coe_one]
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact ((v⁻¹ : (↥O)ˣ) : ↥O).2

  have hPnu : ¬ IsUnit P := by
    intro hu
    apply hπ.not_isUnit
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hbT : ((b : ↥W₀) : T) = (algebraMap K T (π : K))⁻¹ :=
      eq_inv_of_mul_eq_one_right (by simpa using congrArg Subtype.val hb)
    have hinv : (π : K)⁻¹ ∈ O := by rw [← hO, map_inv₀, ← hbT]; exact b.2
    exact IsUnit.of_mul_eq_one ⟨(π : K)⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hπ0))
  have hPinv_nmem : ∀ m : ℕ, 1 ≤ m → (algebraMap K T (π : K))⁻¹ ^ m ∉ W₀ := by
    intro m hm hmem
    apply hPnu
    have h1 : (algebraMap K T (π : K))⁻¹ = (algebraMap K T (π : K))⁻¹ ^ m * (algebraMap K T (π : K)) ^ (m - 1) := by
      rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hPT0]
      rw [show (-(m : ℤ) + ((m - 1 : ℕ) : ℤ)) = -1 from by push_cast [hm]; ring, zpow_neg, zpow_one]
    have hmem' : (algebraMap K T (π : K))⁻¹ ∈ W₀ := by
      rw [h1]; exact mul_mem hmem (pow_mem ((hO _).mpr π.2) _)
    exact unitOf _ ((hO _).mpr π.2) hmem' hPT0

  have key : ∀ x : ↥W₀, x ≠ 0 → ∃ (n : ℕ) (w : ↥W₀), IsUnit w ∧ x = w * P ^ n := by
    intro x hx
    have hx0 : (x : T) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨c, hc0, hcW, hcW'⟩ := hreg (x : T) hx0
    have hcf0 : algebraMap K T c * (x : T) ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hc0) hx0
    have hw₁ : IsUnit (⟨_, hcW⟩ : ↥W₀) := unitOf _ hcW hcW' hcf0
    rcases O.mem_or_inv_mem c with hc | hc
    ·
      have hc0' : (⟨c, hc⟩ : ↥O) ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
      obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0' hπ
      have hcK : c = ((v : ↥O) : K) * (π : K) ^ m := by
        have := congrArg Subtype.val hv; simpa using this
      rcases Nat.eq_zero_or_pos m with hm | hm
      ·
        refine ⟨0, x, ?_, by simp⟩
        have hcunit : IsUnit (⟨algebraMap K T c, (hO c).mpr hc⟩ : ↥W₀) := by
          have : (⟨algebraMap K T c, (hO c).mpr hc⟩ : ↥W₀) = ⟨algebraMap K T ((v : ↥O) : K), hOmem v⟩ :=
            Subtype.ext (by show algebraMap K T c = algebraMap K T _; rw [hcK, hm, pow_zero, mul_one])
          rw [this]; exact hOunit v
        have : (⟨_, hcW⟩ : ↥W₀) = ⟨algebraMap K T c, (hO c).mpr hc⟩ * x := Subtype.ext rfl
        rw [this] at hw₁
        exact isUnit_of_mul_isUnit_right hw₁
      · exfalso
        apply hPinv_nmem m hm

        have : (algebraMap K T (π : K))⁻¹ ^ m =
            (algebraMap K T c * (x : T))⁻¹ * (algebraMap K T ((v : ↥O) : K) * (x : T)) := by
          rw [hcK, map_mul, map_pow]
          field_simp
          rw [one_div, ← mul_pow, inv_mul_cancel₀ hPT0, one_pow]
        rw [this]
        exact mul_mem hcW' (mul_mem (hOmem v) x.2)
    ·
      have hc0' : (⟨c⁻¹, hc⟩ : ↥O) ≠ 0 := fun h => (inv_ne_zero hc0) (congrArg Subtype.val h)
      obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0' hπ
      have hcK : c⁻¹ = ((v : ↥O) : K) * (π : K) ^ m := by
        have := congrArg Subtype.val hv; simpa using this
      refine ⟨m, ⟨_, hcW⟩ * ⟨algebraMap K T ((v : ↥O) : K), hOmem v⟩, hw₁.mul (hOunit v), ?_⟩
      have hcT0 : algebraMap K T c ≠ 0 := (map_ne_zero _).mpr hc0
      apply Subtype.ext
      show (x : T) = algebraMap K T c * (x : T) * algebraMap K T ((v : ↥O) : K) * (algebraMap K T (π : K)) ^ m
      rw [mul_assoc (algebraMap K T c * (x : T)), ← map_pow, ← map_mul, ← hcK, map_inv₀,
        mul_comm (algebraMap K T c) (x : T), mul_inv_cancel_right₀ hcT0]

  have hirr : Irreducible P := by
    refine ⟨hPnu, fun a b hab => ?_⟩
    have ha0 : a ≠ 0 := fun h => hP0 (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hP0 (by rw [hab, h, mul_zero])
    obtain ⟨na, wa, hwa, ha⟩ := key a ha0
    obtain ⟨nb, wb, hwb, hb⟩ := key b hb0
    rcases Nat.eq_zero_or_pos na with hna | hna
    · left; rw [ha, hna, pow_zero, mul_one]; exact hwa
    rcases Nat.eq_zero_or_pos nb with hnb | hnb
    · right; rw [hb, hnb, pow_zero, mul_one]; exact hwb
    exfalso
    apply hPnu
    have h1 : P * 1 = P * (wa * wb * P ^ (na + nb - 1)) := by
      rw [mul_one]
      conv_lhs => rw [hab, ha, hb]
      rw [show na + nb - 1 = (na - 1) + nb from by omega, pow_add,
        show P ^ na = P * P ^ (na - 1) from by rw [← pow_succ', Nat.sub_add_cancel hna]]
      ring
    have h2 := mul_left_cancel₀ hP0 h1
    have h3 : IsUnit (wa * wb * P ^ (na + nb - 1)) := by rw [← h2]; exact isUnit_one
    have h4 : IsUnit (P ^ (na + nb - 1)) := isUnit_of_mul_isUnit_right h3
    exact (isUnit_pow_iff (by omega)).mp h4
  have hfac : IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization ↥W₀ :=
    ⟨P, hirr, fun {x} hx => by
      obtain ⟨n, w, hw, e⟩ := key x hx
      exact ⟨n, hw.unit, by rw [IsUnit.unit_spec, e, mul_comm]⟩⟩
  haveI hDVR : IsDiscreteValuationRing ↥W₀ := IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization hfac
  exact ⟨hDVR, hirr.maximalIdeal_eq⟩

end TraceInjAux

open TraceInjAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 51200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    let OffBranch : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      ∀ ℓ : CuspidalType.ProjLine q, ℓ ≠ lineInfty q →
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal) ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal)

    ∀ ℓ ℓ' : CuspidalType.ProjLine q,
      (∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), (f : ↥(fieldBar q M')) ∈ OIg ℓ ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ') → ℓ = ℓ' := by
  intro F₀ hK1 hStab hLD hRAT instA₁T hconst j₁ hj₁ instFact
  intro InStalk InMax Centred GoodPt Reads OffBranch ℓ ℓ' htrace
  classical

  have constInf : ∀ a : (AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a ∈ OIg (lineInfty q) ↔ a ∈ A := by
    intro a
    rw [hIg_inf]
    constructor
    · rintro ⟨x, y, hy, e⟩

      have : ∃ i : ℤ, IsLocalRing.residue ↥A (y.coeff i) ≠ 0 := by
        by_contra hall
        push_neg at hall
        apply hy
        ext i
        rw [coeffMap_coeff, hall i, HahnSeries.coeff_zero]
      obtain ⟨i, hi⟩ := this
      have hyi : IsUnit (y.coeff i) := by
        by_contra hnu
        exact hi ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
      have hci := congrArg (fun s => HahnSeries.coeff s i) e
      simp only [coeffMap_coeff] at hci
      rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a from rfl,
        algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul] at hci

      obtain ⟨u, hu⟩ := hyi
      have hyi0 : ((y.coeff i : ↥A) : (AlgebraicClosure ℚ)) ≠ 0 := fun h => by
        apply hi; rw [show y.coeff i = 0 from Subtype.ext h, map_zero]
      have hinv : (((u⁻¹ : (↥A)ˣ) : ↥A) : (AlgebraicClosure ℚ)) = (((y.coeff i : ↥A) : (AlgebraicClosure ℚ)))⁻¹ := by
        rw [← hu]
        exact eq_inv_of_mul_eq_one_right (by rw [← MulMemClass.coe_mul, show ((u : ↥A) * ((u⁻¹ : (↥A)ˣ) : ↥A)) = 1 from u.mul_inv]; rfl)
      have hci' : a * ((y.coeff i : ↥A) : (AlgebraicClosure ℚ)) = ((x.coeff i : ↥A) : (AlgebraicClosure ℚ)) := hci
      have : a = ((x.coeff i : ↥A) : (AlgebraicClosure ℚ)) * (((y.coeff i : ↥A) : (AlgebraicClosure ℚ)))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hyi0).mpr hci'
      rw [this, ← hinv]; exact mul_mem (x.coeff i).2 ((u⁻¹ : (↥A)ˣ) : ↥A).2
    · intro ha
      refine ⟨HahnSeries.single 0 ⟨a, ha⟩, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      rw [map_one, mul_one, coeffMap_single]
      show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a = _
      rw [algebraMap_laurentSeries_eq_single]
      rfl

  have constIg : ∀ (l : CuspidalType.ProjLine q) (a : (AlgebraicClosure ℚ)), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a ∈ OIg l ↔ a ∈ A := by
    intro l a
    obtain ⟨γ, -, -, hγ⟩ := hIg l
    rw [hγ, ValuationSubring.mem_comap]
    show (levelAutBar q M' ζ γ) (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a) ∈ OIg (lineInfty q) ↔ a ∈ A
    rw [AlgEquiv.commutes, constInf]

  haveI isk₀ : IsScalarTower ↥k₀ (AlgebraicClosure ℚ) ↥(fieldBar q M') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have stabT1 : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → (levelAutBar q M' ζ γ) f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := by
    intro γ hγ f hf
    let σ : ↥(fieldBar q M') →ₐ[↥k₀] ↥(fieldBar q M') := ((levelAutBar q M' ζ γ).restrictScalars ↥k₀).toAlgHom
    have hσ : ∀ x, σ x = (levelAutBar q M' ζ γ) x := fun _ => rfl
    have hmem : σ f ∈ ((IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).map σ := ⟨f, hf, rfl⟩
    rw [← hσ]
    refine (?_ : ((IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).map σ ≤ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) hmem
    rw [IntermediateField.map_sup, IntermediateField.adjoin_map]
    refine sup_le ?_ ?_
    · refine le_trans (IntermediateField.adjoin.mono _ _ _ ?_) le_sup_left
      rintro x ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by rw [hσ, AlgEquiv.commutes]⟩
    · rintro x ⟨y, hy, rfl⟩
      exact le_sup_right (α := IntermediateField ↥k₀ ↥(fieldBar q M')) (hStab ζ γ hγ y hy)

  obtain ⟨hLR, -⟩ := ModularCurve.FullLevel.exists_smul_mem_and_inv_mem_gauss_levelField q M' A k₀ K₁ hK₁ A₁ hA₁
    F₀ hK1 (hLD K₁ hK₁) hRAT (OIg (lineInfty q)) hIg_inf
  have hregIg : ∀ (l : CuspidalType.ProjLine q) (f : ↥(fieldBar q M')), f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → f ≠ 0 →
      ∃ c : ↥K₁, c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : (AlgebraicClosure ℚ)) * f ∈ OIg l ∧ (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : (AlgebraicClosure ℚ)) * f)⁻¹ ∈ OIg l := by
    intro l f hf hf0
    obtain ⟨γ, hγ, -, hOl⟩ := hIg l
    have hgf : (levelAutBar q M' ζ γ) f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := stabT1 γ hγ f hf
    have hgf0 : (⟨(levelAutBar q M' ζ γ) f, hgf⟩ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ≠ 0 := fun h =>
      hf0 (by have := congrArg Subtype.val h; simpa using this)
    obtain ⟨c, hc0, hc1, hc2⟩ := hLR ⟨_, hgf⟩ hgf0
    refine ⟨c, hc0, ?_, ?_⟩
    · rw [hOl, ValuationSubring.mem_comap]
      show (levelAutBar q M' ζ γ) (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : (AlgebraicClosure ℚ)) * f) ∈ OIg (lineInfty q)
      rw [map_mul, AlgEquiv.commutes]; exact hc1
    · rw [hOl, ValuationSubring.mem_comap]
      show (levelAutBar q M' ζ γ) (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : (AlgebraicClosure ℚ)) * f)⁻¹ ∈ OIg (lineInfty q)
      rw [map_inv₀, map_mul, AlgEquiv.commutes]; exact hc2

  obtain ⟨π₁, hπ₁irr⟩ := IsDiscreteValuationRing.exists_irreducible ↥A₁
  have hunif₁ : maximalIdeal ↥A₁ = Ideal.span {π₁} := hπ₁irr.maximalIdeal_eq
  have hresA₁ : IsAlgClosed (ResidueField ↥A₁) := by
    let Ak := A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))
    have hAkmem : ∀ a : ↥k₀, a ∈ Ak ↔ (a : (AlgebraicClosure ℚ)) ∈ A := fun _ => Iff.rfl
    let ψ : ↥Ak →+* ↥A₁ :=
      { toFun := fun a => ⟨algebraMap ↥k₀ ↥K₁ (a : ↥k₀), (hA₁ _).mpr ((hAkmem _).mp a.2)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp) }
    have hψ : ∀ a : ↥Ak, ((ψ a : ↥A₁) : ↥K₁) = algebraMap ↥k₀ ↥K₁ (a : ↥k₀) := fun _ => rfl
    have hψQ : ∀ a : ↥Ak, (((ψ a : ↥A₁) : ↥K₁) : (AlgebraicClosure ℚ)) = ((a : ↥k₀) : (AlgebraicClosure ℚ)) := fun _ => rfl
    haveI : IsLocalHom ψ := by
      refine ⟨fun a hu => ?_⟩
      have ha0 : ((a : ↥k₀) : (AlgebraicClosure ℚ)) ≠ 0 := by
        intro h0; apply hu.ne_zero; exact Subtype.ext (Subtype.ext (by rw [hψQ, h0]; rfl))
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hbQ : (((b : ↥A₁) : ↥K₁) : (AlgebraicClosure ℚ)) = (((a : ↥k₀) : (AlgebraicClosure ℚ)))⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        have := congrArg (fun z : ↥A₁ => ((z : ↥K₁) : (AlgebraicClosure ℚ))) hb
        simpa [hψQ] using this
      have hinv : ((a : ↥k₀) : (AlgebraicClosure ℚ))⁻¹ ∈ A := by rw [← hbQ]; exact (hA₁ _).mp b.2
      have hinv' : (a : ↥k₀)⁻¹ ∈ Ak := by
        show ((a : ↥k₀)⁻¹ : (AlgebraicClosure ℚ)) ∈ A
        simpa using hinv
      exact IsUnit.of_mul_eq_one ⟨(a : ↥k₀)⁻¹, hinv'⟩ (Subtype.ext (mul_inv_cancel₀ (fun h => ha0 (by rw [h]; rfl))))
    let ψr : ResidueField ↥Ak →+* ResidueField ↥A₁ := IsLocalRing.ResidueField.map ψ
    have hsurj : Function.Surjective ψr := by
      intro r
      obtain ⟨a₁, rfl⟩ := IsLocalRing.residue_surjective r
      obtain ⟨c, hcA, h, hm⟩ := hκ ((a₁ : ↥K₁) : (AlgebraicClosure ℚ)) ((hA₁ _).mp a₁.2)
      refine ⟨IsLocalRing.residue ↥Ak ⟨c, hcA⟩, ?_⟩
      show Ideal.Quotient.mk _ (ψ ⟨c, hcA⟩) = Ideal.Quotient.mk _ a₁
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hm
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hbQ := congrArg (fun z : ↥A₁ => ((z : ↥K₁) : (AlgebraicClosure ℚ))) hb
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at hbQ
      have hdiff : (((ψ ⟨c, hcA⟩ - a₁ : ↥A₁) : ↥K₁) : (AlgebraicClosure ℚ)) = (c : (AlgebraicClosure ℚ)) - ((a₁ : ↥K₁) : (AlgebraicClosure ℚ)) := by
        rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, hψQ]
      rw [hdiff] at hbQ
      refine IsUnit.of_mul_eq_one ⟨-(((b : ↥A₁) : ↥K₁) : (AlgebraicClosure ℚ)), neg_mem ((hA₁ _).mp b.2)⟩ (Subtype.ext ?_)
      show (((a₁ : ↥K₁) : (AlgebraicClosure ℚ)) - c) * -(((b : ↥A₁) : ↥K₁) : (AlgebraicClosure ℚ)) = 1
      linear_combination hbQ
    have hbij : Function.Bijective ψr := ⟨ψr.injective, hsurj⟩
    exact IsAlgClosed.of_ringEquiv (ResidueField ↥Ak) (ResidueField ↥A₁) (RingEquiv.ofBijective ψr hbij)

  haveI : IsScalarTower ↥k₀ ↥K₁ ↥(fieldBar q M') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hK₁F : ∀ c : ↥K₁, algebraMap ↥K₁ ↥(fieldBar q M') c = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : (AlgebraicClosure ℚ)) := fun _ => rfl
  let φ : (AlgebraicClosure ℚ) →ₐ[↥K₁] ↥(fieldBar q M') := IsScalarTower.toAlgHom ↥K₁ (AlgebraicClosure ℚ) ↥(fieldBar q M')
  let L : IntermediateField ↥K₁ ↥(fieldBar q M') := φ.fieldRange
  have hLmem : ∀ x : ↥(fieldBar q M'), x ∈ L ↔ ∃ a : (AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a = x := fun x => AlgHom.mem_fieldRange
  have hQalg : ∀ a : (AlgebraicClosure ℚ), IsAlgebraic ↥K₁ a := by
    intro a
    obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic a
    refine ⟨p.map (algebraMap ℚ ↥K₁), (Polynomial.map_ne_zero_iff (algebraMap ℚ ↥K₁).injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hp
    convert hp using 2
    rfl
    rfl
  haveI : Algebra.IsAlgebraic ↥K₁ ↥L := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, ha⟩ := (hLmem x).mp x.2
    rw [IntermediateField.isAlgebraic_iff, ← ha]
    exact (hQalg a).algHom φ
  let F₀' : IntermediateField ↥K₁ ↥(fieldBar q M') := ((IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).toSubfield.toIntermediateField (fun c => by
    show algebraMap ↥K₁ ↥(fieldBar q M') c ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)
    rw [hK₁F]
    exact (le_sup_left : IntermediateField.adjoin ↥k₀ _ ≤ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (IntermediateField.subset_adjoin _ _ ⟨c, c.2, rfl⟩))
  have hF₀'mem : ∀ f : ↥(fieldBar q M'), f ∈ F₀' ↔ f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := fun _ => Iff.rfl
  have hgen : L ⊔ F₀' = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hf := hK1.ge (IntermediateField.mem_top (x := f))
    rw [← IntermediateField.mem_toSubfield, IntermediateField.sup_toSubfield, IntermediateField.adjoin_toSubfield] at hf
    rw [← IntermediateField.mem_toSubfield, IntermediateField.sup_toSubfield]
    refine (sup_le_sup ?_ ?_ : _ ≤ L.toSubfield ⊔ F₀'.toSubfield) hf
    · rw [Subfield.closure_le]
      rintro x (⟨c, rfl⟩ | ⟨a, rfl⟩)
      · exact (hLmem _).mpr ⟨(c : (AlgebraicClosure ℚ)), rfl⟩
      · exact (hLmem _).mpr ⟨a, rfl⟩
    · intro x hx
      exact (le_sup_right : F₀ ≤ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) hx

  let AL : ValuationSubring ↥L := (OIg ℓ).comap (algebraMap ↥L ↥(fieldBar q M'))
  have hALmem : ∀ x : ↥L, x ∈ AL ↔ (x : ↥(fieldBar q M')) ∈ OIg ℓ := fun _ => Iff.rfl
  have hA₀ : AL.comap (algebraMap ↥K₁ ↥L) = A₁ := by
    ext x
    rw [ValuationSubring.mem_comap, hALmem, hA₁, ← constIg ℓ]
    show algebraMap ↥L ↥(fieldBar q M') (algebraMap ↥K₁ ↥L x) ∈ OIg ℓ ↔ _
    rw [← IsScalarTower.algebraMap_apply, hK₁F]
  have hπ₀ : (π₁ : ↥K₁) ∈ AL.comap (algebraMap ↥K₁ ↥L) := by rw [hA₀]; exact π₁.2
  have hdvr₀ : IsDiscreteValuationRing ↥(AL.comap (algebraMap ↥K₁ ↥L)) := by rw [hA₀]; infer_instance
  have hhens₀ : HenselianLocalRing ↥(AL.comap (algebraMap ↥K₁ ↥L)) := by rw [hA₀]; infer_instance
  have hres₀ : IsAlgClosed (ResidueField ↥(AL.comap (algebraMap ↥K₁ ↥L))) := by rw [hA₀]; exact hresA₁
  have hunif₀ : maximalIdeal ↥(AL.comap (algebraMap ↥K₁ ↥L)) =
      Ideal.span {(⟨(π₁ : ↥K₁), hπ₀⟩ : ↥(AL.comap (algebraMap ↥K₁ ↥L)))} := by
    have key : ∀ (S : ValuationSubring ↥K₁) (hS : S = A₁) (h : (π₁ : ↥K₁) ∈ S),
        maximalIdeal ↥S = Ideal.span {(⟨(π₁ : ↥K₁), h⟩ : ↥S)} := by
      intro S hS h; subst hS; exact hunif₁
    exact key _ hA₀ hπ₀
  obtain ⟨hint, htower⟩ := ValuationSubring.isIntegral_and_exists_totallyRamified_layers_of_henselian ↥K₁ ↥(fieldBar q M') L AL
    (π₁ : ↥K₁) hπ₀ hdvr₀ hunif₀ hhens₀ hres₀

  let W₀ : ValuationSubring ↥F₀' := (OIg ℓ).comap (algebraMap ↥F₀' ↥(fieldBar q M'))
  have hW₀mem : ∀ f : ↥F₀', f ∈ W₀ ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ := fun _ => Iff.rfl
  have hK₁F₀' : ∀ c : ↥K₁, ((algebraMap ↥K₁ ↥F₀' c : ↥F₀') : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : (AlgebraicClosure ℚ)) := fun _ => rfl
  have hO : ∀ x : ↥K₁, algebraMap ↥K₁ ↥F₀' x ∈ W₀ ↔ x ∈ A₁ := by
    intro x; rw [hW₀mem, hK₁F₀', constIg, hA₁]
  have hregW : ∀ f : ↥F₀', f ≠ 0 → ∃ c : ↥K₁, c ≠ 0 ∧ algebraMap ↥K₁ ↥F₀' c * f ∈ W₀ ∧ (algebraMap ↥K₁ ↥F₀' c * f)⁻¹ ∈ W₀ := by
    intro f hf0
    have hf0' : (f : ↥(fieldBar q M')) ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨c, hc0, h1, h2⟩ := hregIg ℓ (f : ↥(fieldBar q M')) f.2 hf0'
    refine ⟨c, hc0, ?_, ?_⟩
    · rw [hW₀mem, MulMemClass.coe_mul, hK₁F₀']; exact h1
    · rw [hW₀mem]
      show (((algebraMap ↥K₁ ↥F₀' c * f : ↥F₀') : ↥(fieldBar q M')))⁻¹ ∈ OIg ℓ
      rw [MulMemClass.coe_mul, hK₁F₀']; exact h2
  obtain ⟨hdvrW, hunifW⟩ := isDiscreteValuationRing_and_maximalIdeal_eq_of_forall_exists_mul_mem
    (K := ↥K₁) (T := ↥F₀') W₀ A₁ hO π₁ hπ₁irr hregW
  have hagree : ∀ x : ↥K₁, algebraMap ↥K₁ ↥L x ∈ AL ↔ algebraMap ↥K₁ ↥F₀' x ∈ W₀ := by
    intro x
    rw [hALmem, hW₀mem, hK₁F₀']
    show algebraMap ↥L ↥(fieldBar q M') (algebraMap ↥K₁ ↥L x) ∈ OIg ℓ ↔ _
    rw [← IsScalarTower.algebraMap_apply, hK₁F]

  have hEq : OIg ℓ = OIg ℓ' :=
    ValuationSubring.eq_of_constantsTower_of_forall_mem_iff ↥K₁ ↥(fieldBar q M') L F₀' hgen AL W₀ hagree hdvrW (π₁ : ↥K₁)
      ((hO _).mpr π₁.2) hunifW hint htower (OIg ℓ) (OIg ℓ') (fun f => (hW₀mem f).symm)
      (fun f => (htrace ⟨(f : ↥(fieldBar q M')), f.2⟩).symm.trans (hW₀mem f).symm)
  exact hIg_inj hEq

end S_ModularCurve_FullLevel_eq_of_forall_coe_levelField_mem_igusaRing_iff_twoChartIntegralModel_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_eq_of_forall_coe_levelField_mem_igusaRing_iff_twoChartIntegralModel_of_eq_two (solution)
