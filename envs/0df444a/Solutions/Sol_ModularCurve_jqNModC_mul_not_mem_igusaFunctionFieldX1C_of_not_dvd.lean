-- Prove2me | solution 1 for ModularCurve.jqNModC_mul_not_mem_igusaFunctionFieldX1C_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/10f5f10f-a830-5024-8665-231d6b224eee

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_isKummerGenerator_hasseRootFn_x1FunctionFieldC
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jqNModC_mul_not_mem_igusaFunctionFieldX1C_of_not_dvd
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Polynomial IntermediateField

namespace IgusaNonMemMl

section Kummer

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

theorem isGalois_adjoin_of_pow_eq {n : ℕ} (hn : 0 < n) (hnF : ((n : ℕ) : F) ≠ 0)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) {a : Ω} {c : F} (hc : c ≠ 0)
    (hac : a ^ n = algebraMap F Ω c) :
    IsGalois F (IntermediateField.adjoin F ({a} : Set Ω)) ∧
      FiniteDimensional F (IntermediateField.adjoin F ({a} : Set Ω)) := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  set f : Polynomial F := X ^ n - C c with hf
  have hf0 : f ≠ 0 := X_pow_sub_C_ne_zero hn c
  have hsep : f.Separable := separable_X_pow_sub_C c hnF hc
  have hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) n := hζ.map_of_injective (algebraMap F Ω).injective
  have hmapf : f.map (algebraMap F Ω) = X ^ n - C (algebraMap F Ω c) := by
    simp [hf, Polynomial.map_sub, Polynomial.map_pow]
  have hsplits : (f.map (algebraMap F Ω)).Splits := by
    rw [hmapf]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot hζΩ hac
  haveI hSF : IsSplittingField F (IntermediateField.adjoin F (f.rootSet Ω)) f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplits
  have hGal : IsGalois F (IntermediateField.adjoin F (f.rootSet Ω)) :=
    IsGalois.of_separable_splitting_field hsep
  have ha0 : a ≠ 0 := by
    intro h
    apply hc
    have : algebraMap F Ω c = 0 := by rw [← hac, h, zero_pow hn.ne']
    exact (map_eq_zero _).mp this

  have hroots_eq : IntermediateField.adjoin F (f.rootSet Ω) =
      IntermediateField.adjoin F ({a} : Set Ω) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      rw [Polynomial.mem_rootSet] at hy
      obtain ⟨-, hy⟩ := hy
      have hyn : y ^ n = a ^ n := by
        rw [hac]
        simpa [hf, sub_eq_zero] using hy
      have hya : (y / a) ^ n = 1 := by
        rw [div_pow, hyn, div_self (pow_ne_zero _ ha0)]
      obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one hya
      have hy' : y = algebraMap F Ω (ζ ^ i) * a := by
        rw [map_pow, hi, div_mul_cancel₀ y ha0]
      rw [hy']
      refine mul_mem ?_ (IntermediateField.subset_adjoin F _ (Set.mem_singleton a))
      exact IntermediateField.algebraMap_mem _ _
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      refine IntermediateField.subset_adjoin F _ ?_
      rw [Polynomial.mem_rootSet]
      refine ⟨hf0, ?_⟩
      simp [hf, hac]
  refine ⟨?_, ?_⟩
  · exact IsGalois.of_algEquiv (IntermediateField.equivOfEq hroots_eq)
  · have hint : IsIntegral F a := by
      refine IsIntegral.of_pow hn ?_
      rw [hac]
      exact isIntegral_algebraMap
    exact IntermediateField.adjoin.finiteDimensional hint

theorem mem_range_algebraMap_of_unique_root {n : ℕ} (hn : 0 < n) (hnF : ((n : ℕ) : F) ≠ 0)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) {a : Ω} {c : F} (hc : c ≠ 0)
    (hac : a ^ n = algebraMap F Ω c)
    (P : Polynomial F) {x : Ω} (hxa : x ∈ IntermediateField.adjoin F ({a} : Set Ω))
    (hx : aeval x P = 0) (huniq : ∀ y : Ω, aeval y P = 0 → y = x) :
    x ∈ Set.range (algebraMap F Ω) := by
  obtain ⟨hGal, hfd⟩ := isGalois_adjoin_of_pow_eq hn hnF hζ hc hac
  set L := IntermediateField.adjoin F ({a} : Set Ω) with hL
  haveI := hGal
  haveI := hfd
  set xL : L := ⟨x, hxa⟩ with hxL
  have hcoe : ∀ z : L, algebraMap L Ω z = (z : Ω) := fun z => rfl
  have hxL0 : aeval xL P = 0 := by
    apply (algebraMap L Ω).injective
    rw [← Polynomial.aeval_algebraMap_apply Ω xL P, map_zero, hcoe]
    exact hx
  have hfix : ∀ σ : L ≃ₐ[F] L, σ xL = xL := by
    intro σ
    apply Subtype.ext
    apply huniq

    have h1 : aeval ((σ xL : L) : Ω) P = algebraMap L Ω (aeval (σ xL) P) := by
      rw [← hcoe, Polynomial.aeval_algebraMap_apply Ω (σ xL) P]
    rw [h1, Polynomial.aeval_algHom_apply σ xL P, hxL0, map_zero, map_zero]
  obtain ⟨e, he⟩ := (IsGalois.mem_range_algebraMap_iff_fixed xL).mpr hfix
  refine ⟨e, ?_⟩
  have h2 := congrArg (fun z : L => (z : Ω)) he
  simpa using h2

end Kummer

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_injective~coeffMap_jqModC~coeffMap_jqNModC HahnSeries"

section CoeffMap

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem coeffMap_qExpand (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem coeffMap_intSeriesC {K L : Type*} [Field K] [Field L] (g : K →+* L) (p : PowerSeries ℤ) :
    coeffMap g (intSeriesC K p) = intSeriesC L p := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [intSeriesC, intSeriesC, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map]
    simp
  · rw [intSeriesC, intSeriesC, ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_jqModC : coeffMap f (jqModC R) = jqModC S := map_jqModC f

theorem coeffMap_jqNModC (N : ℕ) [NeZero N] : coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC, jqNModC]

theorem coeffMap_injective (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z => HahnSeries.coeff z k) h
  simpa using this

theorem coeffMap_algebraMap₂ {K L : Type*} [Field K] [Field L] (g : K →+* L) (r : K) :
    coeffMap g (algebraMap K (LaurentSeries K) r) = algebraMap L (LaurentSeries L) (g r) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

end CoeffMap

section LeadingCoeff

variable (K : Type*) [CommRing K]

theorem jqModC_coeff_neg_one : (jqModC K).coeff (-1) = 1 := by
  have h : ((HahnSeries.single (-1 : ℤ) (1 : K)) *
      HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))).coeff (0 + (-1)) = 1 := by
    have h0 := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (jNum.map (Int.castRingHom K)) 0
    simp only [Nat.cast_zero] at h0
    rw [HahnSeries.coeff_single_mul_add, one_mul, h0, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]
  rw [jqModC]
  simpa using h

theorem jqNModC_coeff_neg (N : ℕ) [NeZero N] : (jqNModC K N).coeff (-(N : ℤ)) = 1 := by
  rw [jqNModC, show (-(N : ℤ)) = (N : ℤ) * (-1) by ring, qExpand_coeff_mul, jqModC_coeff_neg_one]

end LeadingCoeff

section PhiEval

noncomputable def jEval {S : Type*} [CommRing S] (x : S) : Polynomial ℤ →+* S :=
  Polynomial.eval₂RingHom (Int.castRingHom S) x

@[scoped simp] theorem jEval_X {S : Type*} [CommRing S] (x : S) : jEval x Polynomial.X = x := by
  simp [jEval]

@[scoped simp] theorem jEval_C {S : Type*} [CommRing S] (x : S) (a : ℤ) : jEval x (Polynomial.C a) = a := by
  simp [jEval]

theorem comp_jEval {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T) (x : S) :
    g.comp (jEval x) = jEval (g x) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

theorem aeval_toRingHom_eq_jEval {S : Type*} [CommRing S] [Algebra ℤ S] (x : S) :
    (Polynomial.aeval (R := ℤ) x).toRingHom = jEval x := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

noncomputable def phiEval {S : Type*} [CommRing S] (Φ : Polynomial (Polynomial ℤ)) (x y : S) : S :=
  Φ.eval₂ (jEval x) y

theorem map_phiEval {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T)
    (Φ : Polynomial (Polynomial ℤ)) (x y : S) :
    g (phiEval Φ x y) = phiEval Φ (g x) (g y) := by
  rw [phiEval, Polynomial.hom_eval₂, comp_jEval, phiEval]

theorem eval_map_jEval {S : Type*} [CommRing S] (Φ : Polynomial (Polynomial ℤ)) (x y : S) :
    (Φ.map (jEval x)).eval y = phiEval Φ x y := by
  rw [Polynomial.eval_map, phiEval]

theorem map_map_jEval {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T)
    (Φ : Polynomial (Polynomial ℤ)) (x : S) :
    (Φ.map (jEval x)).map g = Φ.map (jEval (g x)) := by
  rw [Polynomial.map_map, comp_jEval]

theorem eval₂_aeval_eq_phiEval {S : Type*} [CommRing S] [Algebra ℤ S]
    (Φ : Polynomial (Polynomial ℤ)) (x y : S) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = phiEval Φ x y := by
  rw [aeval_toRingHom_eq_jEval, phiEval]

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem phiEval_int_eq_zero (data : ModularPolynomialData ℓ) (hsymm : EvalSymm data.Φ) :
    phiEval data.Φ (jqModC ℤ) (qExpand ℤ ℓ (jqModC ℤ)) = 0 ∧
      phiEval data.Φ (qExpand ℤ ℓ (jqModC ℤ)) (jqModC ℤ) = 0 := by
  have hinj : Function.Injective (coeffMap (Int.castRingHom ℚ)) :=
    coeffMap_injective _ Int.cast_injective
  have hQ : phiEval data.Φ (jqModC ℚ) (qExpand ℚ ℓ (jqModC ℚ)) = 0 := by
    have := data.eval_eq_zero
    rw [evalAtJ_def, eval₂_aeval_eq_phiEval] at this
    exact this
  have hQ' : phiEval data.Φ (qExpand ℚ ℓ (jqModC ℚ)) (jqModC ℚ) = 0 := by
    have := hsymm (jqModC ℚ) (qExpand ℚ ℓ (jqModC ℚ))
    rw [eval₂_aeval_eq_phiEval, eval₂_aeval_eq_phiEval] at this
    rw [← this]
    exact hQ
  refine ⟨hinj ?_, hinj ?_⟩
  · rw [map_phiEval, map_zero, coeffMap_qExpand, coeffMap_jqModC]
    exact hQ
  · rw [map_phiEval, map_zero, coeffMap_qExpand, coeffMap_jqModC]
    exact hQ'

variable (K : Type*) [CommRing K]

theorem phiEval_jqNModC_eq_zero (data : ModularPolynomialData ℓ) (hsymm : EvalSymm data.Φ)
    (M : ℕ) [NeZero M] [NeZero (M * ℓ)] :
    phiEval data.Φ (jqNModC K M) (jqNModC K (M * ℓ)) = 0 ∧
      phiEval data.Φ (jqNModC K (M * ℓ)) (jqNModC K M) = 0 := by
  obtain ⟨h1, h2⟩ := phiEval_int_eq_zero ℓ data hsymm
  have g1 := congrArg (coeffMap (Int.castRingHom K)) h1
  have g2 := congrArg (coeffMap (Int.castRingHom K)) h2
  rw [map_phiEval, map_zero, coeffMap_qExpand, coeffMap_jqModC] at g1 g2
  have e1 := congrArg (qExpand K M) g1
  have e2 := congrArg (qExpand K M) g2
  rw [map_phiEval, map_zero, qExpand_qExpand] at e1 e2
  exact ⟨e1, e2⟩

end PhiEval

section UniqueRoot

variable {K : Type*} [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] [NeZero (M * ℓ)]

theorem dedekindPsi_prime' : dedekindPsi ℓ = ℓ + 1 := by
  have hℓ : ℓ.Prime := Fact.out
  rw [dedekindPsi, Nat.Prime.divisors hℓ]
  have h1 : (1 : ℕ) ≠ ℓ := hℓ.one_lt.ne
  rw [Finset.filter_insert, if_pos squarefree_one, Finset.filter_singleton,
    if_pos hℓ.squarefree, Finset.sum_insert (by simpa using h1), Finset.sum_singleton,
    Nat.div_one, Nat.div_self hℓ.pos, add_comm]

theorem qTwist_apply_qExpand_of_pow_eq_one (v : Kˣ) (hv : v ^ ℓ = 1) (f : LaurentSeries K) :
    qTwist v (qExpand K ℓ f) = qExpand K ℓ f := by
  rw [qTwist_qExpand, zpow_natCast, hv, qTwist_one_apply]

theorem eq_of_phiEval_eq_zero (data : ModularPolynomialData ℓ) (hsymm : EvalSymm data.Φ)
    (hℓM : ¬ ℓ ∣ M) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    (y : LaurentSeries K) (hy : phiEval data.Φ (jqNModC K M) y = 0) :
    y = jqNModC K (M * ℓ) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  set A : LaurentSeries K := jqNModC K M with hA
  set x : LaurentSeries K := jqNModC K (M * ℓ) with hx
  set ι : LaurentSeries K →+* LaurentSeries K := qExpand K ℓ with hι
  by_contra hne

  have hιA : ι A = x := by
    rw [hι, hA, hx, jqNModC, jqNModC, qExpand_qExpand, qExpand_congr (Nat.mul_comm ℓ M)]
  set Q : Polynomial (LaurentSeries K) := data.Φ.map (jEval x) with hQ
  have hQmonic : Q.Monic := data.monic.map _
  have hQdeg : Q.natDegree = ℓ + 1 := by
    rw [hQ, data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime']
  have hQ0 : Q ≠ 0 := hQmonic.ne_zero
  have hQeval : ∀ z, Q.eval z = phiEval data.Φ x z := fun z => eval_map_jEval _ _ _
  obtain ⟨hroot, hroot'⟩ := phiEval_jqNModC_eq_zero ℓ K data hsymm M

  have hιroot : ∀ z, phiEval data.Φ A z = 0 → Q.eval (ι z) = 0 := by
    intro z hz
    rw [hQeval, ← hιA, ← map_phiEval, hz, map_zero]

  have hζ0 : ζ ≠ 0 := hζ.ne_zero hℓ.ne_zero
  set u : Kˣ := Units.mk0 ζ hζ0 with hu
  have huℓ : u ^ ℓ = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, hζ.pow_eq_one, Units.val_one]
  have hfixι : ∀ (b : ℕ) (f : LaurentSeries K), qTwist (u ^ b) (ι f) = ι f := by
    intro b f
    apply qTwist_apply_qExpand_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul, huℓ, one_pow]
  have hxfix : ∀ b : ℕ, qTwist (u ^ b) x = x := by
    intro b
    rw [← hιA]
    exact hfixι b A
  set s : ℕ → LaurentSeries K := fun b => qTwist (u ^ b) A with hs
  have hsroot : ∀ b, Q.eval (s b) = 0 := by
    intro b
    have h1 : Q.map (qTwist (u ^ b)) = Q := by
      rw [hQ, map_map_jEval, hxfix]
    have h2 : (Q.map (qTwist (u ^ b))).eval (qTwist (u ^ b) A) = qTwist (u ^ b) (Q.eval A) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_hom _ _
    rw [h1] at h2
    show Q.eval (qTwist (u ^ b) A) = 0
    rw [h2, hQeval, hroot', map_zero]

  have hMℓ : ¬ (ℓ : ℤ) ∣ (-(M : ℤ)) := by
    rw [Int.dvd_neg]
    exact_mod_cast hℓM
  have hιcoeff : ∀ f : LaurentSeries K, (ι f).coeff (-(M : ℤ)) = 0 := fun f =>
    qExpand_coeff_of_not_dvd ℓ f hMℓ
  have hscoeff : ∀ b, (s b).coeff (-(M : ℤ)) = ((u ^ b) ^ (-(M : ℤ)) : Kˣ) := by
    intro b
    show (qTwist (u ^ b) A).coeff (-(M : ℤ)) = _
    rw [qTwist_coeff, hA, jqNModC_coeff_neg, mul_one]
  have hs_ne_ι : ∀ b f, s b ≠ ι f := by
    intro b f h
    have := congrArg (fun g => HahnSeries.coeff g (-(M : ℤ))) h
    simp only [hscoeff, hιcoeff] at this
    exact ((u ^ b) ^ (-(M : ℤ))).ne_zero this

  have hsinj : ∀ b b' : ℕ, b < ℓ → b' < ℓ → s b = s b' → b = b' := by
    intro b b' hb hb' h
    have hc := congrArg (fun g => HahnSeries.coeff g (-(M : ℤ))) h
    simp only [hscoeff] at hc
    have hc' : (u ^ b) ^ (-(M : ℤ)) = (u ^ b') ^ (-(M : ℤ)) := Units.ext hc
    rw [zpow_neg, zpow_neg, inv_inj, zpow_natCast, zpow_natCast, ← pow_mul, ← pow_mul] at hc'
    have hu' : IsPrimitiveRoot u ℓ := IsPrimitiveRoot.coe_units_iff.mp (by simpa [hu] using hζ)
    rw [pow_eq_pow_iff_modEq, ← hu'.eq_orderOf] at hc'
    have hcop : Nat.gcd ℓ M = 1 := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM
    have hmod : b ≡ b' [MOD ℓ] := Nat.ModEq.cancel_right_of_coprime hcop hc'
    exact Nat.ModEq.eq_of_lt_of_lt hmod hb hb'

  have hyroot : Q.eval (ι y) = 0 := hιroot y hy
  have hxroot : Q.eval (ι x) = 0 := hιroot x hroot
  have hιinj : Function.Injective ι := qExpand_injective ℓ
  set S : Finset (LaurentSeries K) :=
    insert (ι x) (insert (ι y) ((Finset.range ℓ).image s)) with hS
  have hSsub : S ⊆ Q.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def]
    rw [hS, Finset.mem_insert, Finset.mem_insert, Finset.mem_image] at hz
    rcases hz with rfl | rfl | ⟨b, -, rfl⟩
    · exact hxroot
    · exact hyroot
    · exact hsroot b
  have hScard : S.card = ℓ + 2 := by
    have himg : ((Finset.range ℓ).image s).card = ℓ := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro b hb b' hb' h
      exact hsinj b b' (Finset.mem_range.mp hb) (Finset.mem_range.mp hb') h
    have hy_notin : ι y ∉ (Finset.range ℓ).image s := by
      rw [Finset.mem_image]
      rintro ⟨b, -, hb⟩
      exact hs_ne_ι b y hb
    have hx_notin : ι x ∉ insert (ι y) ((Finset.range ℓ).image s) := by
      rw [Finset.mem_insert, Finset.mem_image]
      rintro (h | ⟨b, -, hb⟩)
      · exact hne (hιinj h).symm
      · exact hs_ne_ι b x hb
    rw [hS, Finset.card_insert_of_notMem hx_notin, Finset.card_insert_of_notMem hy_notin, himg]
  have h1 : S.card ≤ Q.roots.toFinset.card := Finset.card_le_card hSsub
  have h2 : Q.roots.toFinset.card ≤ Q.roots.card := Multiset.toFinset_card_le _
  have h3 : Q.roots.card ≤ Q.natDegree := Polynomial.card_roots' Q
  rw [hScard] at h1
  rw [hQdeg] at h3
  omega

end UniqueRoot

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_injective~coeffMap_jqModC~coeffMap_jqNModC HahnSeries CongruenceSubgroup"
open scoped MatrixGroups

section BaseChange

variable {κ k : Type*} [Field κ] [Field k] (g : κ →+* k)

theorem image_intFormRatiosC_subset (Γ : Subgroup SL(2, ℤ)) :
    coeffMap g '' intFormRatiosC κ Γ ⊆ intFormRatiosC k Γ := by
  rintro _ ⟨x, ⟨kk, f, f', pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
  refine ⟨kk, f, f', pf, pg, hf, hg, ?_, ?_⟩
  · intro h
    apply hg0
    apply coeffMap_injective g g.injective
    rw [coeffMap_intSeriesC, h, map_zero]
  · rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem coeffMap_mem_of_mem_adjoin {S : Set (LaurentSeries κ)} {T : IntermediateField k (LaurentSeries k)}
    (hST : coeffMap g '' S ⊆ T) {x : LaurentSeries κ} (hx : x ∈ IntermediateField.adjoin κ S) :
    coeffMap g x ∈ T := by
  have hle : (IntermediateField.adjoin κ S).toSubfield ≤ T.toSubfield.comap (coeffMap g) := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro y (⟨r, rfl⟩ | hy)
    · show coeffMap g (algebraMap κ _ r) ∈ T
      rw [coeffMap_algebraMap₂]
      exact T.algebraMap_mem _
    · exact hST ⟨y, hy, rfl⟩
  exact hle hx

theorem coeffMap_mem_x1FunctionFieldC (M : ℕ) {x : LaurentSeries κ} (hx : x ∈ x1FunctionFieldC κ M) :
    coeffMap g x ∈ x1FunctionFieldC k M :=
  coeffMap_mem_of_mem_adjoin g (T := x1FunctionFieldC k M)
    ((image_intFormRatiosC_subset g _).trans (intFormRatiosC_subset k _)) hx

variable (M : ℕ)

noncomputable def baseChangeForm (w : IntegralWeightOneForm κ M) : IntegralWeightOneForm k M where
  form := w.form
  series := w.series
  isIntegralQExp := w.isIntegralQExp
  intSeriesC_ne_zero := fun h => w.intSeriesC_ne_zero
    (coeffMap_injective g g.injective (by rw [coeffMap_intSeriesC, h, map_zero]))

theorem coeffMap_hasseRootFn (w : IntegralWeightOneForm κ M) :
    coeffMap g w.hasseRootFn = (baseChangeForm g M w).hasseRootFn := by
  show coeffMap g (intSeriesC κ w.series)⁻¹ = (intSeriesC k w.series)⁻¹
  rw [map_inv₀, coeffMap_intSeriesC]

theorem coeffMap_mem_igusaFunctionFieldX1C (w : IntegralWeightOneForm κ M) {x : LaurentSeries κ}
    (hx : x ∈ igusaFunctionFieldX1C κ M w) :
    coeffMap g x ∈ igusaFunctionFieldX1C k M (baseChangeForm g M w) := by
  refine coeffMap_mem_of_mem_adjoin g ?_ hx
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with hy | hy
  · exact x1FunctionFieldC_le_igusaFunctionFieldX1C k M _ (coeffMap_mem_x1FunctionFieldC g M hy)
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [coeffMap_hasseRootFn]
    exact hasseRootFn_mem_igusaFunctionFieldX1C k M _

end BaseChange

section Assembly

theorem gamma1_conj_mem_top (M : ℕ) [NeZero M] :
    ∀ γ ∈ Gamma1 M, ∃ γ₁ ∈ (⊤ : Subgroup SL(2, ℤ)),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (M : ℤ) * γ 0 1 ∧ (M : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  rw [Gamma1_mem] at hγ
  obtain ⟨-, -, h10⟩ := hγ
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp h10
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  refine ⟨⟨!![γ 0 0, (M : ℤ) * γ 0 1; c, γ 1 1], ?_⟩, Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    rw [hc] at hdet
    linear_combination hdet
  · rfl
  · rfl
  · show (M : ℤ) * c = γ 1 0
    rw [hc]
  · rfl

theorem jqNModC_mem_x1FunctionFieldC (k : Type*) [Field k] (M : ℕ) [NeZero M] :
    jqNModC k M ∈ x1FunctionFieldC k M := by
  have h1 : jqModC k ∈ intFormRatiosC k (⊤ : Subgroup SL(2, ℤ)) := ModularCurve.jqModC_mem_intFormRatiosC k ⊤
  have h2 := ModularCurve.qExpand_image_intFormRatiosC_subset k (Γ := ⊤) (Γ' := Gamma1 M)
    (Subgroup.mem_top _) M (gamma1_conj_mem_top M)
  exact intFormRatiosC_subset k _ (h2 ⟨_, h1, rfl⟩)

theorem not_mem_of_isAlgClosed (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M) (w : IntegralWeightOneForm k M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hℓM : ¬ ℓ ∣ M) [NeZero (M * ℓ)]
    (hx : jqNModC k (M * ℓ) ∈ igusaFunctionFieldX1C k M w) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  set E : IntermediateField k (LaurentSeries k) := x1FunctionFieldC k M with hE
  set a : LaurentSeries k := w.hasseRootFn with ha
  set A : LaurentSeries k := jqNModC k M with hAdef
  set x : LaurentSeries k := jqNModC k (M * ℓ) with hxdef

  obtain ⟨hnpos, ha0, hapow⟩ := ModularCurve.isKummerGenerator_hasseRootFn_x1FunctionFieldC p M hM hpM k w
  have hn_ne : ((p - 1 : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    intro h
    have h1 := Nat.le_of_dvd hnpos h
    have h2 := hp.one_lt
    omega
  haveI : NeZero (((p - 1 : ℕ)) : k) := ⟨hn_ne⟩
  obtain ⟨ζk, hζk⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k (p - 1)
  have hζE : IsPrimitiveRoot (algebraMap k E ζk) (p - 1) :=
    hζk.map_of_injective (algebraMap k E).injective
  have hinjE : Function.Injective (algebraMap E (LaurentSeries k)) := (algebraMap E (LaurentSeries k)).injective
  have hnE : ((p - 1 : ℕ) : E) ≠ 0 := by
    intro h
    apply hn_ne
    have h1 : ((p - 1 : ℕ) : LaurentSeries k) = 0 := by
      have := congrArg (algebraMap E (LaurentSeries k)) h
      rwa [map_natCast, map_zero] at this
    apply (algebraMap k (LaurentSeries k)).injective
    rw [map_natCast, map_zero]
    exact h1
  set c : E := ⟨a ^ (p - 1), hapow⟩ with hcdef
  have hc : c ≠ 0 := by
    intro h
    apply pow_ne_zero (p - 1) ha0
    have := congrArg (fun z : E => (z : LaurentSeries k)) h
    simpa [hcdef] using this
  have hac : a ^ (p - 1) = algebraMap E (LaurentSeries k) c := rfl

  have hxa : x ∈ IntermediateField.adjoin E ({a} : Set (LaurentSeries k)) := by
    have hle : igusaFunctionFieldX1C k M w ≤
        (IntermediateField.adjoin E ({a} : Set (LaurentSeries k))).restrictScalars k := by
      show IntermediateField.adjoin k ((E : Set (LaurentSeries k)) ∪ {a}) ≤ _
      rw [IntermediateField.adjoin_le_iff]
      rintro y (hy | hy)
      · show y ∈ IntermediateField.adjoin E ({a} : Set (LaurentSeries k))
        have : y = algebraMap E (LaurentSeries k) ⟨y, hy⟩ := rfl
        rw [this]
        exact IntermediateField.algebraMap_mem _ _
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact IntermediateField.mem_adjoin_simple_self E a
    exact (IntermediateField.mem_restrictScalars k).mp (hle hx)

  obtain ⟨data, hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm ℓ
  have hAE : A ∈ E := jqNModC_mem_x1FunctionFieldC k M
  set AE : E := ⟨A, hAE⟩ with hAEdef
  set P : Polynomial E := data.Φ.map (jEval AE) with hP
  have hPeval : ∀ y : LaurentSeries k, aeval y P = phiEval data.Φ A y := by
    intro y
    rw [Polynomial.aeval_def, hP, Polynomial.eval₂_map, comp_jEval]
    rfl

  have hℓk : ((ℓ : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    intro h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm
  haveI : NeZero ((ℓ : ℕ) : k) := ⟨hℓk⟩
  obtain ⟨ζℓ, hζℓ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k ℓ
  have hxroot : aeval x P = 0 := by
    rw [hPeval]
    exact (phiEval_jqNModC_eq_zero ℓ k data hsymm M).1
  have huniq : ∀ y : LaurentSeries k, aeval y P = 0 → y = x := by
    intro y hy
    rw [hPeval] at hy
    exact eq_of_phiEval_eq_zero ℓ M data hsymm hℓM hζℓ y hy

  obtain ⟨e, he⟩ := mem_range_algebraMap_of_unique_root hnpos hnE hζE hc hac P hxa hxroot huniq
  have hxE : x ∈ E := by
    rw [← he]
    exact e.2

  have hMk : ((M : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    exact hpM
  have hMℓk : ((M * ℓ : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_mul]
    exact mul_ne_zero hMk hℓk
  have hnd : ¬ (M * ℓ ∣ M) := by
    intro h
    have h1 := Nat.le_of_dvd (NeZero.pos M) h
    have h2 := hℓ.two_le
    have h3 := NeZero.pos M
    nlinarith
  have hnon := ModularCurve.qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_of_not_dvd k M ⊥ hMk
    (M * ℓ) hnd hMℓk
  rw [ModularCurve.GammaH_bot] at hnon
  exact hnon hxE

theorem not_mem (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M) (w : IntegralWeightOneForm κ M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hℓM : ¬ ℓ ∣ M) [NeZero (M * ℓ)] :
    jqNModC κ (M * ℓ) ∉ igusaFunctionFieldX1C κ M w := by
  intro hx
  let k : Type := AlgebraicClosure κ
  let g : κ →+* k := algebraMap κ k
  have hxk : jqNModC k (M * ℓ) ∈ igusaFunctionFieldX1C k M (baseChangeForm g M w) := by
    have := coeffMap_mem_igusaFunctionFieldX1C g M w hx
    rwa [coeffMap_jqNModC] at this
  exact not_mem_of_isAlgClosed p k M hM hpM (baseChangeForm g M w) ℓ hℓp hℓM hxk

end Assembly

end IgusaNonMemMl
p2m_reactivate "P2MW.S_ModularCurve_jqNModC_mul_not_mem_igusaFunctionFieldX1C_of_not_dvd.IgusaNonMemMl"

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hℓM : ¬ ℓ ∣ M) :
    haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : ℓ.Prime).ne_zero⟩
    ModularCurve.jqNModC κ (M * ℓ) ∉ ModularCurve.igusaFunctionFieldX1C κ M w :=
  IgusaNonMemMl.not_mem p κ M hM hpM w ℓ hℓp hℓM

end S_ModularCurve_jqNModC_mul_not_mem_igusaFunctionFieldX1C_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_jqNModC_mul_not_mem_igusaFunctionFieldX1C_of_not_dvd (solution)
