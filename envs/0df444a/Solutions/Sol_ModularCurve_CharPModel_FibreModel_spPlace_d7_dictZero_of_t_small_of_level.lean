-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d59d1f87-cddd-56d1-a528-da22e603ea52

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_eq_ord_coeffMap_of_surjective
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN_pole
import Theorems.Thm_ModularCurve_exists_slot_of_isCusp
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small_of_level
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve~coeffMap_qExpand~coeffMap_injective ModularCurve.CharPModel"

noncomputable section

namespace SolD7DictZeroSmallLevel

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem placeOrdNonnegOfMem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
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

theorem placeMemOfOrdNonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_pow' (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem ord_algebraMap' (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]; exact v.algebraMap_mem' _
  have h1 := placeOrdNonnegOfMem v hmem
  have h2 := placeOrdNonnegOfMem v hmem'
  rw [v.ord_inv] at h2
  omega

end PlaceFacts

section Orders

variable {L : Type*} [Field L]

theorem order_eq_of_coeff (x : LaurentSeries L) (m : ℤ) (hm : x.coeff m ≠ 0)
    (hlt : ∀ k < m, x.coeff k = 0) : x.order = m := by
  have hx : x ≠ 0 := fun h => hm (by rw [h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hm) ?_
  by_contra h
  push Not at h
  exact (HahnSeries.coeff_order_eq_zero.not.mpr hx) (hlt _ h)

theorem order_qExpand_of_coeff (M : ℕ) [NeZero M] (f : LaurentSeries L) (h1 : f.coeff (-1) ≠ 0)
    (hlt : ∀ k < -1, f.coeff k = 0) : (qExpand L M f).order = -(M : ℤ) := by
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  refine order_eq_of_coeff _ _ ?_ ?_
  · rw [show (-(M : ℤ)) = (M : ℤ) * (-1) by ring, qExpand_coeff_mul]
    exact h1
  · intro k hk
    by_cases hd : (M : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hd
      rw [qExpand_coeff_mul]
      refine hlt m ?_
      by_contra hm
      push Not at hm
      have : (M : ℤ) * (-1) ≤ (M : ℤ) * m := mul_le_mul_of_nonneg_left hm hM.le
      omega
    · exact qExpand_coeff_of_not_dvd M f hd

variable [Algebra ℚ L]

theorem coeffEmb_jq_coeff_neg_one : (coeffEmb L jq).coeff (-1) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

theorem coeffEmb_jq_coeff_of_lt {k : ℤ} (hk : k < -1) : (coeffEmb L jq).coeff k = 0 := by
  rw [coeffEmb_coeff, coeff_jq_of_lt hk, map_zero]

theorem order_qExpand_coeffEmb_jq (M : ℕ) [NeZero M] :
    (qExpand L M (coeffEmb L jq)).order = -(M : ℤ) :=
  order_qExpand_of_coeff M _ (by rw [coeffEmb_jq_coeff_neg_one]; exact one_ne_zero)
    fun _ hk => coeffEmb_jq_coeff_of_lt hk

theorem order_qExpand_qTwist_coeffEmb_jq (M : ℕ) [NeZero M] (u : Lˣ) :
    (qExpand L M (qTwist u (coeffEmb L jq))).order = -(M : ℤ) := by
  refine order_qExpand_of_coeff M _ ?_ ?_
  · rw [qTwist_coeff, coeffEmb_jq_coeff_neg_one, mul_one]
    exact Units.ne_zero _
  · intro k hk
    rw [qTwist_coeff, coeffEmb_jq_coeff_of_lt hk, mul_zero]

end Orders

section CuspIneq

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N]

def jB : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

def jNB : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

theorem coe_jB : ((jB N : modularFunctionFieldBar N) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ jq := rfl

theorem coe_jNB :
    ((jNB N : modularFunctionFieldBar N) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ (qExpand ℚ N jq) := rfl

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (M : ℕ) [NeZero M]
    (x : LaurentSeries R) : coeffMap f (qExpand R M x) = qExpand S M (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (M : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd M x hk, qExpand_coeff_of_not_dvd M _ hk, map_zero]

theorem coe_jNB' :
    ((jNB N : modularFunctionFieldBar N) : LaurentSeries ℚ̄) = qExpand ℚ̄ N (coeffEmb ℚ̄ jq) := by
  rw [coe_jNB, coeffEmb, coeffMap_qExpand]

theorem jB_ne_zero : jB N ≠ 0 := by
  intro h
  have h' := congrArg (fun x : modularFunctionFieldBar N => (x : LaurentSeries ℚ̄).coeff (-1)) h
  simp only [coe_jB, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h'
  rw [coeffEmb_jq_coeff_neg_one] at h'
  exact one_ne_zero h'

theorem jNB_ne_zero : jNB N ≠ 0 := by
  intro h
  have h' := congrArg (fun x : modularFunctionFieldBar N => (x : LaurentSeries ℚ̄).coeff
    ((N : ℤ) * (-1))) h
  simp only [coe_jNB', ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h'
  rw [qExpand_coeff_mul, coeffEmb_jq_coeff_neg_one] at h'
  exact one_ne_zero h'

theorem cusp_ineq (P : Place ℚ̄ (modularFunctionFieldBar N)) (hP : P.ord (jB N) < 0) :
    (N : ℤ) * P.ord (jNB N) ≤ P.ord (jB N) := by
  have hN0 : (N : ℕ) ≠ 0 := NeZero.ne N
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  have hζunit : IsUnit ζ := hζ.isUnit hN0
  set ζu : (AlgebraicClosure ℚ)ˣ := hζunit.unit with hζu
  have hζ' : IsPrimitiveRoot (ζu : ℚ̄) N := by
    rw [hζu, IsUnit.unit_spec]; exact hζ
  have hcusp : IsCusp (⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (jq_mem_full N)⟩ :
      laurentBaseChange ℚ̄ (modularFunctionFieldFull N)) P := by
    rw [isCusp_iff]
    intro hmem
    have h0 := placeOrdNonnegOfMem P hmem
    have : P.ord (jB N) = P.ord (⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (jq_mem_full N)⟩ :
      laurentBaseChange ℚ̄ (modularFunctionFieldFull N)) := rfl
    omega
  obtain ⟨a, b, haN, -, -, hne, ι, hιj, hιjN, hord⟩ :=
    ModularCurve.exists_slot_of_isCusp ℚ̄ N ζu hζ' P hcusp
  have ha0 : a ≠ 0 := hne.ne

  have hg : (0 : ℤ) < ((a * Nat.gcd a (N / a) : ℕ) : ℤ) := by
    have : 0 < a * Nat.gcd a (N / a) :=
      Nat.mul_pos (Nat.pos_of_ne_zero ha0) (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha0))
    exact_mod_cast this
  have h1 : P.ord (jB N) * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) = -(N : ℤ) := by
    have h := hord (jB N)
    rw [show jB N = (⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (jq_mem_full N)⟩ :
      laurentBaseChange ℚ̄ (modularFunctionFieldFull N)) from rfl, hιj,
      order_qExpand_coeffEmb_jq] at h
    exact h
  have h2 : P.ord (jNB N) * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) = -((a * a : ℕ) : ℤ) := by
    have h := hord (jNB N)
    rw [show jNB N = (⟨coeffEmb ℚ̄ (jqN N),
        coeffEmb_mem_laurentBaseChange ℚ̄ (jqd_mem_full N (dvd_refl N))⟩ :
      laurentBaseChange ℚ̄ (modularFunctionFieldFull N)) from rfl, hιjN,
      order_qExpand_qTwist_coeffEmb_jq] at h
    exact h

  have ha1 : (1 : ℤ) ≤ ((a * a : ℕ) : ℤ) := by
    have : 1 ≤ a * a := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ha0 ha0)
    exact_mod_cast this
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have key : (N : ℤ) * P.ord (jNB N) * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) ≤
      P.ord (jB N) * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) := by
    rw [mul_assoc, h2, h1]
    nlinarith
  exact le_of_mul_le_mul_right key hg

end CuspIneq

section QExp

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N] (A : ValuationSubring ℚ̄)

theorem coeffMap_subtype_jqModC :
    coeffMap A.subtype (jqModC A) = ((jB N : modularFunctionFieldBar N) : LaurentSeries ℚ̄) := by
  rw [coe_jB]
  show (jqModC A).map _ = (jqModC ℚ).map _
  rw [map_jqModC, map_jqModC]

theorem coeffMap_subtype_jqNModC :
    coeffMap A.subtype (jqNModC A N) = ((jNB N : modularFunctionFieldBar N) : LaurentSeries ℚ̄) := by
  rw [coe_jNB', jqNModC, coeffMap_qExpand]
  congr 1
  show (jqModC A).map _ = (jqModC ℚ).map _
  rw [map_jqModC, map_jqModC]

variable {k : Type*} [Field k] (red : A →+* k)

theorem coeffMap_red_jqModC : coeffMap red (jqModC A) = jqModC k := map_jqModC red

theorem coeffMap_red_jqNModC : coeffMap red (jqNModC A N) = jqNModC k N := by
  rw [jqNModC, coeffMap_qExpand, coeffMap_red_jqModC]; rfl

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext m
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff m) h
  simpa using this

end QExp

section Main

local notation "ℚ̄" => AlgebraicClosure ℚ

def jt (k : Type*) [Field k] (N : ℕ) [NeZero N] : modularFunctionFieldC k N :=
  ⟨jqModC k, jqModC_mem k N⟩

def jNt (k : Type*) [Field k] (N : ℕ) [NeZero N] : modularFunctionFieldC k N :=
  ⟨jqNModC k N, jqNModC_mem k N⟩

theorem main' (A : ValuationSubring ℚ̄) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart)
    (w : Place ℚ̄ (modularFunctionFieldBar N)) (τ : A)
    (ht : jB N / jNB N ^ N ∈ w.toValuationSubring)
    (hpole : ∀ a : A, w.ord (jNB N - algebraMap ℚ̄ (modularFunctionFieldBar N) (a : ℚ̄)) ≤ 0)
    (hres : IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap ℚ̄ w.ResidueField (τ : ℚ̄)) :
    jt k N / jNt k N ^ N - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (jt k N / jNt k N ^ N - algebraMap k (modularFunctionFieldC k N) (red τ)) := by
  classical

  generalize hsp : fm.spPlace hred dataAll hsep = sp
  set c : modularFunctionFieldC k N := algebraMap k (modularFunctionFieldC k N) (red τ) with hc
  set τ' : modularFunctionFieldBar N := algebraMap ℚ̄ (modularFunctionFieldBar N) (τ : ℚ̄) with hτ'
  by_cases hzero : jt k N / jNt k N ^ N - c = 0
  · exact Or.inl hzero
  refine Or.inr ?_

  have hjNt_neg : (sp w).ord (jNt k N) < 0 := by
    have h := ModularCurve.CharPModel.FibreModel.spPlace_d0_jN_pole N A ℓ k red fm hred dataAll
      hsep hsym w hpole
    rwa [hsp] at h
  have hjNt0 : jNt k N ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hjNt_neg; exact lt_irrefl _ hjNt_neg
  have hjNtN0 : jNt k N ^ N ≠ 0 := pow_ne_zero _ hjNt0
  have hg₁_eq : jt k N - c * jNt k N ^ N = jNt k N ^ N * (jt k N / jNt k N ^ N - c) := by
    field_simp
  have hg₁0 : jt k N - c * jNt k N ^ N ≠ 0 := by
    rw [hg₁_eq]; exact mul_ne_zero hjNtN0 hzero

  have hjB0 := jB_ne_zero N
  have hjNB0 := jNB_ne_zero N
  have hjNBN0 : jNB N ^ N ≠ 0 := pow_ne_zero _ hjNB0
  have hu0 : jB N / jNB N ^ N ≠ 0 := div_ne_zero hjB0 hjNBN0
  have hf₁_eq : jB N - τ' * jNB N ^ N = jNB N ^ N * (jB N / jNB N ^ N - τ') := by
    field_simp

  set yA₁ : LaurentSeries A := jqModC A - HahnSeries.single 0 τ * jqNModC A N ^ N with hyA₁
  set yA₂ : LaurentSeries A := jqNModC A N with hyA₂
  have e₁ : coeffMap A.subtype yA₁ =
      ((jB N - τ' * jNB N ^ N : modularFunctionFieldBar N) : LaurentSeries ℚ̄) := by
    rw [hyA₁, map_sub, map_mul, map_pow, coeffMap_single, coeffMap_subtype_jqModC N A,
      coeffMap_subtype_jqNModC N A, hτ']
    push_cast
    rw [← algebraMap_laurentSeries_eq_single]
    rfl
  have e₁k : coeffMap red yA₁ =
      ((jt k N - c * jNt k N ^ N : modularFunctionFieldC k N) : LaurentSeries k) := by
    rw [hyA₁, map_sub, map_mul, map_pow, coeffMap_single, coeffMap_red_jqModC A red,
      coeffMap_red_jqNModC N A red, hc]
    push_cast
    rw [← algebraMap_laurentSeries_eq_single]
    rfl
  have e₂ : coeffMap A.subtype yA₂ = ((jNB N : modularFunctionFieldBar N) : LaurentSeries ℚ̄) := by
    rw [hyA₂, coeffMap_subtype_jqNModC N A]
  have e₂k : coeffMap red yA₂ = ((jNt k N : modularFunctionFieldC k N) : LaurentSeries k) := by
    rw [hyA₂, coeffMap_red_jqNModC N A red]; rfl
  have hy₁ : coeffMap A.subtype yA₁ ∈ modularFunctionFieldBar N := by
    rw [e₁]; exact SetLike.coe_mem _
  have hyk₁ : coeffMap red yA₁ ∈ modularFunctionFieldC k N := by
    rw [e₁k]; exact SetLike.coe_mem _
  have hy₂ : coeffMap A.subtype yA₂ ∈ modularFunctionFieldBar N := by
    rw [e₂]; exact SetLike.coe_mem _
  have hyk₂ : coeffMap red yA₂ ∈ modularFunctionFieldC k N := by
    rw [e₂k]; exact SetLike.coe_mem _
  have hsub₁ : (⟨coeffMap A.subtype yA₁, hy₁⟩ : modularFunctionFieldBar N) =
      jB N - τ' * jNB N ^ N := Subtype.ext e₁
  have hsub₁k : (⟨coeffMap red yA₁, hyk₁⟩ : modularFunctionFieldC k N) =
      jt k N - c * jNt k N ^ N := Subtype.ext e₁k
  have hsub₂ : (⟨coeffMap A.subtype yA₂, hy₂⟩ : modularFunctionFieldBar N) = jNB N :=
    Subtype.ext e₂
  have hsub₂k : (⟨coeffMap red yA₂, hyk₂⟩ : modularFunctionFieldC k N) = jNt k N :=
    Subtype.ext e₂k
  have hne₁ : coeffMap red yA₁ ≠ 0 := by
    rw [e₁k]; exact fun h => hg₁0 (by exact_mod_cast h)
  have hne₂ : coeffMap red yA₂ ≠ 0 := by
    rw [e₂k]; exact fun h => hjNt0 (by exact_mod_cast h)
  have hf₁0 : jB N - τ' * jNB N ^ N ≠ 0 := by
    intro h
    apply hne₁
    have hy0 : yA₁ = 0 := by
      apply coeffMap_injective (f := A.subtype) Subtype.val_injective
      rw [e₁, h, map_zero]; rfl
    rw [hy0, map_zero]
  have huτ0 : jB N / jNB N ^ N - τ' ≠ 0 := by
    intro h; apply hf₁0; rw [hf₁_eq, h, mul_zero]

  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D₁, hD₁, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := ℚ̄) (jB N - τ' * jNB N ^ N) hf₁0
  obtain ⟨D₂, hD₂, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℚ̄) (jNB N) hjNB0
  have T₁ := ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap_of_surjective
    N ℓ A k red hred hlN fm cc dataAll hsep yA₁ hy₁ hyk₁ hne₁ D₁
    (fun P => by rw [hD₁ P, hsub₁]) (sp w)
  have T₂ := ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap_of_surjective
    N ℓ A k red hred hlN fm cc dataAll hsep yA₂ hy₂ hyk₂ hne₂ D₂
    (fun P => by rw [hD₂ P, hsub₂]) (sp w)
  rw [hsp, hsub₁k] at T₁
  rw [hsp, hsub₂k] at T₂

  set D : Divisor ℚ̄ (modularFunctionFieldBar N) := D₁ - N • D₂ with hDdef
  have hD : ∀ P, D P = P.ord (jB N / jNB N ^ N - τ') := by
    intro P
    rw [hDdef, Finsupp.sub_apply, Finsupp.smul_apply, hD₁ P, hD₂ P, hf₁_eq,
      P.ord_mul hjNBN0 huτ0, ord_pow', nsmul_eq_mul]
    ring
  have hmapD : Finsupp.mapDomain sp D (sp w) = (sp w).ord (jt k N / jNt k N ^ N - c) := by
    rw [hDdef, Finsupp.mapDomain_sub, Finsupp.mapDomain_smul, Finsupp.sub_apply,
      Finsupp.smul_apply, T₁, T₂, hg₁_eq, (sp w).ord_mul hjNtN0 hzero, ord_pow', nsmul_eq_mul]
    ring
  have hsum : Finsupp.mapDomain sp D (sp w) = ∑ P ∈ D.support with sp P = sp w, D P := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.single_apply]

  have hDw : 0 < D w := by
    rw [hD w]
    have hmemO : jB N / jNB N ^ N - τ' ∈ w.toValuationSubring := sub_mem ht (w.algebraMap_mem' _)
    have hmax : (⟨jB N / jNB N ^ N - τ', hmemO⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring := by
      have h := hres
      rw [IsScalarTower.algebraMap_apply ℚ̄ w.toValuationSubring w.ResidueField] at h
      have h' := Ideal.Quotient.eq.mp h
      have hval : (⟨jB N / jNB N ^ N - τ', hmemO⟩ : w.toValuationSubring) =
          ⟨jB N / jNB N ^ N, ht⟩ - algebraMap ℚ̄ w.toValuationSubring (τ : ℚ̄) :=
        Subtype.ext (by simp [hτ'])
      rw [hval]
      exact h'
    exact (w.mem_maximalIdeal_iff_ord_pos huτ0 hmemO).mp hmax
  have hw_in : w ∈ D.support.filter (fun P => sp P = sp w) := by
    simp [Finsupp.mem_support_iff, hDw.ne']

  have hnonneg : ∀ P ∈ D.support.filter (fun P => sp P = sp w), 0 ≤ D P := by
    intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨-, hPw⟩ := hP
    rw [hD P]
    by_contra hneg
    push Not at hneg
    have hu_neg : P.ord (jB N / jNB N ^ N) < 0 := by
      by_contra h'
      push Not at h'
      have hmem : jB N / jNB N ^ N ∈ P.toValuationSubring := placeMemOfOrdNonneg P hu0 h'
      have h2 : 0 ≤ P.ord (jB N / jNB N ^ N - τ') :=
        placeOrdNonnegOfMem P (sub_mem hmem (P.algebraMap_mem' (τ : ℚ̄)))
      omega
    have hu_ord : P.ord (jB N / jNB N ^ N) = P.ord (jB N) - N * P.ord (jNB N) := by
      rw [div_eq_mul_inv, P.ord_mul hjB0 (inv_ne_zero hjNBN0), P.ord_inv, ord_pow']
      ring
    rcases lt_or_ge (P.ord (jB N)) 0 with hcusp | hfin
    · have := cusp_ineq N P hcusp
      omega
    · have hNnn : (0 : ℤ) ≤ N := Int.natCast_nonneg N
      have hjNpos : 0 < P.ord (jNB N) := by
        by_contra h0
        push Not at h0
        have : (N : ℤ) * P.ord (jNB N) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNnn h0
        omega
      have h0 : 0 < P.ord (jNB N - algebraMap ℚ̄ (modularFunctionFieldBar N) ((0 : A) : ℚ̄)) := by
        simpa using hjNpos
      have hspP := ModularCurve.CharPModel.FibreModel.spPlace_d0_jN N A ℓ k red fm hred dataAll
        hsep hsym P 0 h0
      rw [hsp, map_zero, map_zero, sub_zero, hPw] at hspP
      exact absurd hspP (not_lt.mpr hjNt_neg.le)

  rw [← hmapD, hsum]
  exact lt_of_lt_of_le hDw (Finset.single_le_sum hnonneg hw_in)

end Main

end SolD7DictZeroSmallLevel

open SolD7DictZeroSmallLevel in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart) :
    ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N) ^ N ∈
                  w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
    (∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
      ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
          ∈ w.toValuationSubring.nonunits) →
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) :=
  fun w τ ht hpole hres _ =>
    main' A ℓ N hlN k red hred dataAll hsym hsep fm cc w τ ht hpole hres

end
end S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small_of_level
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small_of_level (solution)
