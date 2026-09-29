-- Prove2me | solution 1 for ModularCurve.eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ea192257-f1ce-530e-8909-987deaacb9ba

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_HeckeOperatorModL
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_heckeInputsFibre_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_AlgebraicCurve_traceDiff_apply
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_apply_eq_inv_smul_D
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_smul_D_jqModC_ne_zero
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_frobeniusInputsModL
import Theorems.Thm_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero
import Theorems.Thm_ModularCurve_coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq
import Theorems.Thm_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order
import Theorems.Thm_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow
import Theorems.Thm_ModularCurve_coeff_inv_mul_thetaL_mul_level_eq_of_heckePic0Fibre_self_eq_of_smul_eq_neg
import Theorems.Thm_LinearMap_finrank_iInf_eigenspace_le_one_of_coeff_hecke_law
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg.ModularCurve AlgebraicCurve IntermediateField HahnSeries KaehlerDifferential"

namespace ModularCurve
p2m_export "ModularCurve" "charLDegeneracyRoof heckeAlphaC heckeBetaC heckeDivFibre heckePic0Fibre heckePic0Fibre_eq jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem dedekindPsi heckeOperatorModL heckeOperatorModL_apply frobeniusPushforwardModL modularFunctionFieldFullC coeffMap_coeff coeff_jqModC_neg_one thetaL thetaL_apply qExpansionDiffAlong qInftyPlaceMod ord_qInftyPlaceMod heckeInputsFibre_of_prime finiteAlong_heckeAlphaC separableAlong_heckeAlphaC_heckeBetaC coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC qExpansionDiffAlong_smul qExpansionDiffAlong_D qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero theta_coeff transcendental_jqModC smul_D_jqModC_ne_zero relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi dedekindPsi_pos frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order coeff_inv_mul_thetaL_mul_char_eq_pow coeff_inv_mul_thetaL_mul_level_eq_of_heckePic0Fibre_self_eq_of_smul_eq_neg"
p2m_open "ModularCurve"

namespace RankOneFibreW

section PrimeField

variable {k : Type*} [Field k] (q : ℕ) [hq : Fact q.Prime] [CharP k q]

theorem exists_natCast_eq_of_pow_eq {c : k} (hc : c ^ q = c) : ∃ m : ℕ, (m : k) = c := by
  classical

  set P : Polynomial k := Polynomial.X ^ q - Polynomial.X with hP
  have hq1 : 1 < q := hq.out.one_lt
  have hPne : P ≠ 0 := by
    intro h
    have := congrArg (fun Q : Polynomial k => Q.coeff q) h
    simp only [hP, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_true, Polynomial.coeff_X,
      Polynomial.coeff_zero] at this
    rw [if_neg (by omega)] at this
    norm_num at this
  have hdeg : P.natDegree = q := by
    rw [hP]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq1]

  set S : Finset k := (Finset.range q).image (fun m : ℕ => (m : k)) with hS
  have hroot : ∀ x : k, x ^ q = x → x ∈ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot, hP]
    simp [hx]
  have hSsub : S ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hx
    apply hroot
    have h := map_natCast (frobenius k q) m
    rwa [frobenius_def] at h
  have hScard : S.card = q := by
    rw [hS, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h := (CharP.natCast_eq_natCast (R := k) q).mp hab
    exact (Nat.ModEq.eq_of_lt_of_lt h ha hb)
  have hcard : P.roots.toFinset.card ≤ q := by
    calc P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = q := hdeg
  have hSeq : S = P.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hcard)
  have hcS : c ∈ S := by rw [hSeq]; exact hroot c hc
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hcS
  exact ⟨m, hm⟩

end PrimeField

section Setting

variable (k : Type*) [Field k] (p : ℕ) [hpp : Fact p.Prime]

abbrev FF : Type _ := ↥(modularFunctionFieldC k p)

abbrev jF : FF k p := ⟨jqModC k, jqModC_mem k p⟩

abbrev qexp : Ω[FF k p⁄k] →ₗ[k] LaurentSeries k :=
  qExpansionDiffAlong (modularFunctionFieldC k p).val

variable {k p}

theorem hqp (q : ℕ) [CharP k q] (hp : (p : k) ≠ 0) : q ≠ p := by
  rintro rfl
  exact hp (CharP.cast_eq_zero k q)

theorem not_char_dvd (q : ℕ) [CharP k q] (hp : (p : k) ≠ 0) : ¬ q ∣ p := fun h =>
  hp ((CharP.cast_eq_zero_iff k q p).mpr h)

theorem transcendental_jF : Transcendental k (jF k p) := by
  intro halg
  apply transcendental_jqModC k
  exact (isAlgebraic_algHom_iff (modularFunctionFieldC k p).val Subtype.val_injective).mpr halg

theorem finiteDimensional_adjoin_jF (q : ℕ) [Fact q.Prime] [CharP k q] (hp : (p : k) ≠ 0) :
    FiniteDimensional (IntermediateField.adjoin k ({jF k p} : Set (FF k p))) (FF k p) := by
  have hrel := relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k p q (not_char_dvd q hp)

  have hle : IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) ≤ modularFunctionFieldC k p :=
    adjoin_simple_le_iff.mpr (jqModC_mem k p)
  rw [relfinrank_eq_finrank_of_le hle] at hrel
  set A' : IntermediateField k (FF k p) := IntermediateField.adjoin k ({jF k p} : Set (FF k p))
  have hlift : lift A' = IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) :=
    IntermediateField.lift_adjoin_simple k (modularFunctionFieldC k p) (jF k p)
  let i : A' ≃+* IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) :=
    ((liftAlgEquiv A').trans (equivOfEq hlift)).toRingEquiv
  let jj : FF k p ≃+* extendScalars hle :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hfr : Module.finrank A' (FF k p) = dedekindPsi p := by
    rw [← hrel]
    refine Algebra.finrank_eq_of_equiv_equiv i jj ?_
    refine RingHom.ext fun a => Subtype.ext ?_
    rfl
  have hpos : 0 < Module.finrank A' (FF k p) := by
    rw [hfr]
    exact dedekindPsi_pos p hpp.out.ne_zero
  exact Module.finite_of_finrank_pos hpos

theorem thetaL_jqModC_ne_zero : thetaL k (jqModC k) ≠ 0 := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries k => s.coeff (-1)) h
  beta_reduce at h1
  rw [thetaL_apply, theta_coeff, coeff_jqModC_neg_one, HahnSeries.coeff_zero] at h1
  norm_num at h1

theorem qexp_injective : Function.Injective (qexp k p) :=
  qExpansionDiffAlong_modularFunctionFieldC_injective_of_thetaL_ne_zero k p
    (modularFunctionFieldC k p).val thetaL_jqModC_ne_zero

theorem D_jF_ne_zero (q : ℕ) [Fact q.Prime] [CharP k q] [PerfectField k] (hp : (p : k) ≠ 0) :
    KaehlerDifferential.D k (FF k p) (jF k p) ≠ 0 := by
  haveI := finiteDimensional_adjoin_jF (k := k) (p := p) q hp
  have h := smul_D_jqModC_ne_zero (K := k) (ℓ := p) (jF k p) (z := (1 : FF k p)) one_ne_zero
  rwa [one_smul] at h

theorem exists_dlog [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q] (hp : (p : k) ≠ 0) :
    ∃ δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k], Function.Injective δ ∧
      ∀ (x : Pic0.torsion k (FF k p) q) (E : Divisor.degZero (K := k) (F := FF k p)) (g : FF k p),
        Pic0.mk E = (x : Pic0 k (FF k p)) → g ≠ 0 →
        (∀ v : Place k (FF k p), (q : ℤ) * (E : Divisor k (FF k p)) v = v.ord g) →
        δ x = g⁻¹ • KaehlerDifferential.D k (FF k p) g := by
  haveI := finiteDimensional_adjoin_jF (k := k) (p := p) q hp
  obtain ⟨t, ht, hfin, hsep⟩ := exists_separating_transcendental_of_perfectField (K := k)
    (F := FF k p) (x := jF k p) transcendental_jF (finiteDimensional_adjoin_jF q hp)
  haveI := hfin

  have hdt : KaehlerDifferential.D k (FF k p) t ≠ 0 := by
    intro hdt
    set E : IntermediateField k (FF k p) := IntermediateField.adjoin k ({t} : Set (FF k p)) with hE
    haveI : Algebra.IsSeparable E (FF k p) := hsep
    haveI : Algebra.FormallyEtale E (FF k p) := Algebra.FormallyEtale.of_isSeparable E (FF k p)

    have hkill : ∀ e : FF k p, e ∈ E → KaehlerDifferential.D k (FF k p) e = 0 := by
      intro e he
      change e ∈ Subfield.closure (Set.range (algebraMap k (FF k p)) ∪ {t}) at he
      induction he using Subfield.closure_induction with
      | mem y hy =>
          rcases hy with ⟨a, rfl⟩ | hy
          · exact (KaehlerDifferential.D k (FF k p)).map_algebraMap a
          · rw [Set.mem_singleton_iff] at hy; subst hy; exact hdt
      | one => exact Derivation.map_one_eq_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | neg x _ hx => rw [map_neg, hx, neg_zero]
      | inv x _ hx =>
          rcases eq_or_ne x 0 with rfl | hx0
          · rw [inv_zero, Derivation.map_zero]
          · simp [Derivation.leibniz_inv, hx]
      | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

    have hall : ∀ ω : Ω[FF k p⁄k], ω = 0 := by
      intro ω
      obtain ⟨τ, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale k E (FF k p)).surjective ω
      induction τ using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => rw [map_add, hx, hy, add_zero]
      | tmul u η =>
          rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
          suffices h : KaehlerDifferential.map k k E (FF k p) η = 0 by rw [h, smul_zero]
          have hη : η ∈ Submodule.span E (Set.range (KaehlerDifferential.D k E)) := by
            rw [KaehlerDifferential.span_range_derivation]; trivial
          induction hη using Submodule.span_induction with
          | mem x hx =>
              obtain ⟨e, rfl⟩ := hx
              rw [KaehlerDifferential.map_D]
              exact hkill e e.2
          | zero => rw [map_zero]
          | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
          | smul a x _ hx => rw [LinearMap.map_smul, hx]; exact smul_zero _
    exact D_jF_ne_zero q hp (hall _)
  exact Pic0.exists_injective_addMonoidHom_torsion_apply_eq_inv_smul_D k (FF k p) q t ht hsep hdt

end Setting

section Laws

variable {k : Type*} [Field k] {p : ℕ} [hpp : Fact p.Prime]

theorem exists_rep {q : ℕ} {x : Pic0 k (FF k p)} (hx : (q : ℤ) • x = 0) :
    ∃ (E : Divisor.degZero (K := k) (F := FF k p)) (g : FF k p), Pic0.mk E = x ∧ g ≠ 0 ∧
      ∀ v : Place k (FF k p), (q : ℤ) * (E : Divisor k (FF k p)) v = v.ord g := by
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective x
  have hmk : (Pic0.mk ((q : ℤ) • E) : Pic0 k (FF k p)) = 0 := by
    rw [Pic0.mk, QuotientAddGroup.mk_zsmul]; exact hx
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hmk
  obtain ⟨g, hg, hEg⟩ := hmk
  refine ⟨E, g, rfl, hg, fun v => ?_⟩
  rw [← hEg v]
  rfl

theorem qexp_dlog (g : FF k p) :
    qexp k p (g⁻¹ • KaehlerDifferential.D k (FF k p) g) =
      ((g : LaurentSeries k))⁻¹ * thetaL k (g : LaurentSeries k) := by
  rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_D, map_inv₀]
  rfl

theorem ord_cusp (g : FF k p) :
    (qInftyPlaceMod k (jqModC_mem k p)).ord g = ((g : LaurentSeries k)).order :=
  ord_qInftyPlaceMod k (jqModC_mem k p) g

variable {q : ℕ} [hq : Fact q.Prime] [CharP k q]

theorem coeff_dlog_eq_zero_of_nonpos {E : Divisor k (FF k p)} {g : FF k p} (hg : g ≠ 0)
    (hE : ∀ v : Place k (FF k p), (q : ℤ) * E v = v.ord g) (n : ℤ) (hn : n ≤ 0) :
    (((g : LaurentSeries k))⁻¹ * thetaL k (g : LaurentSeries k)).coeff n = 0 := by
  have hg' : (g : LaurentSeries k) ≠ 0 := fun h => hg (Subtype.ext h)
  obtain ⟨hneg, hzero⟩ := coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order k (g : LaurentSeries k) hg'
  rcases lt_or_eq_of_le hn with hn | rfl
  · exact hneg n hn
  · rw [hzero, ← ord_cusp, ← hE]
    push_cast
    rw [CharP.cast_eq_zero k q, zero_mul]

theorem traceAlong_apply_eq_traceDiff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ)
    (ω' : Ω[F'⁄K]) :
    Differential.traceAlong ψ ω' =
      (letI := algebraAlong ψ; haveI := isScalarTower_along ψ; traceDiff K F F' ω') := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Algebra.IsSeparable F F' := hsep
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale K F F').surjective ω'
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul u ω =>
      have htm : tensorKaehlerEquivOfFormallyEtale K F F' (u ⊗ₜ ω) =
          u • Differential.pullbackAlong ψ ω := by
        rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
        rfl
      rw [htm, Differential.traceAlong_smul_pullbackAlong ψ hsep]
      exact (AlgebraicCurve.traceDiff_apply K F F' u ω).symm

theorem dlog_heckePic0Fibre [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k])
    (hδ : ∀ (x : Pic0.torsion k (FF k p) q) (E : Divisor.degZero (K := k) (F := FF k p)) (g : FF k p),
        Pic0.mk E = (x : Pic0 k (FF k p)) → g ≠ 0 →
        (∀ v : Place k (FF k p), (q : ℤ) * (E : Divisor k (FF k p)) v = v.ord g) →
        δ x = g⁻¹ • KaehlerDifferential.D k (FF k p) g)
    (ℓ : Nat.Primes) (hℓk : ((ℓ : ℕ) : k) ≠ 0)
    (x y : Pic0.torsion k (FF k p) q)
    (hxy : (y : Pic0 k (FF k p)) =
      (letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckePic0Fibre k p ℓ (x : Pic0 k (FF k p)))) :
    letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    δ y = Differential.traceAlong (heckeAlphaC k p ℓ) (Differential.pullbackAlong (heckeBetaC k p ℓ) (δ x)) := by
  letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (Nat.Prime (ℓ : ℕ)) := ⟨ℓ.2⟩
  have hℓq : ¬ q ∣ p * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq.out).mp h with h | h
    · exact not_char_dvd q hp h
    · exact hℓk ((CharP.cast_eq_zero_iff k q _).mpr h)
  obtain ⟨hP, hβ, hα, hdesc⟩ := heckeInputsFibre_of_prime k p ℓ hp hℓk
  have hfin : FiniteAlong k (heckeAlphaC k p ℓ) := finiteAlong_heckeAlphaC k p ℓ
  have hsep : SeparableAlong k (heckeAlphaC k p ℓ) := (separableAlong_heckeAlphaC_heckeBetaC k p ℓ hℓq).1
  have hN : NormFormulaAlong k (heckeAlphaC k p ℓ) hfin :=
    normFormulaAlong_of_separableAlong (heckeAlphaC k p ℓ) hfin hsep
  obtain ⟨E, g, hEx, hg, hEg⟩ := exists_rep (k := k) (p := p) (Pic0.mem_torsion.mp x.2)
  obtain ⟨g', -, hg'0, hg', hdlog⟩ :=
    AlgebraicCurve.Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong k (FF k p)
      (charLDegeneracyRoof k p ℓ) (heckeBetaC k p ℓ) (heckeAlphaC k p ℓ) hβ hα hfin hN hsep
      (q : ℤ) (E : Divisor k (FF k p)) g hg hEg
  rw [hδ x E g hEx hg hEg, ← hdlog]
  refine hδ y (Divisor.degZeroEnd (heckeDivFibre k p ℓ hβ hα) hdesc E) g' ?_ hg'0 ?_
  · rw [hxy, ← hEx, heckePic0Fibre_eq k p ℓ hβ hα hdesc, AddMonoidHom.coe_toIntLinearMap,
      Divisor.toPic0End_mk]
  · intro v
    rw [Divisor.coe_degZeroEnd]
    exact hg' v

end Laws

section MemberLaws

variable {k : Type*} [Field k] [IsAlgClosed k] {q : ℕ} [hq : Fact q.Prime] [CharP k q]
variable {p : ℕ} [hpp : Fact p.Prime]

def IsDlogRecipe (q : ℕ) (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) : Prop :=
  ∀ (x : Pic0.torsion k (FF k p) q) (E : Divisor.degZero (K := k) (F := FF k p)) (g : FF k p),
    Pic0.mk E = (x : Pic0 k (FF k p)) → g ≠ 0 →
    (∀ v : Place k (FF k p), (q : ℤ) * (E : Divisor k (FF k p)) v = v.ord g) →
    δ x = g⁻¹ • KaehlerDifferential.D k (FF k p) g

theorem coeff_law_hecke (hp : (p : k) ≠ 0)
    (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (hδ : IsDlogRecipe q δ)
    (ℓ : Nat.Primes) (hℓp : (ℓ : ℕ) ≠ p) (hℓk : ((ℓ : ℕ) : k) ≠ 0)
    (x : Pic0.torsion k (FF k p) q)
    (hTx : (letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckePic0Fibre k p ℓ (x : Pic0 k (FF k p)))
      = (((ℓ : ℕ) + 1 : ℕ) : ℤ) • (x : Pic0 k (FF k p))) (n : ℤ) :
    (qexp k p (δ x)).coeff ((ℓ : ℤ) * n)
      + (if ((ℓ : ℕ) : ℤ) ∣ n then ((ℓ : ℕ) : k) * (qexp k p (δ x)).coeff (n / (ℓ : ℕ)) else 0)
      = (((ℓ : ℕ) : k) + 1) * (qexp k p (δ x)).coeff n := by
  letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (Nat.Prime (ℓ : ℕ)) := ⟨ℓ.2⟩

  set y : Pic0.torsion k (FF k p) q := (((ℓ : ℕ) + 1 : ℕ) : ℤ) • x with hy
  have hxy : (y : Pic0 k (FF k p)) = heckePic0Fibre k p ℓ (x : Pic0 k (FF k p)) := by
    rw [hTx, hy]; rfl
  have h1 := dlog_heckePic0Fibre (q := q) hp δ hδ ℓ hℓk x y hxy
  have h2 : δ y = ((((ℓ : ℕ) + 1 : ℕ) : ℤ) : k) • δ x := by
    rw [hy, map_zsmul, Int.cast_smul_eq_zsmul]

  have hℓq : ¬ q ∣ p * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq.out).mp h with h | h
    · exact not_char_dvd q hp h
    · exact hℓk ((CharP.cast_eq_zero_iff k q _).mpr h)
  have hsep : SeparableAlong k (heckeAlphaC k p ℓ) := (separableAlong_heckeAlphaC_heckeBetaC k p ℓ hℓq).1
  haveI : NeZero (((ℓ : ℕ) : k)) := ⟨hℓk⟩
  obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k (ℓ : ℕ)
  have hζu : IsUnit ζ' := hζ'.isUnit ℓ.2.ne_zero
  have hζ2 : IsPrimitiveRoot ((hζu.unit : kˣ) : k) (ℓ : ℕ) := by rw [IsUnit.unit_spec]; exact hζ'
  have hℓp' : ¬ (ℓ : ℕ) ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq ℓ.2 hpp.out).mp h)

  have hHQ := coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC k p ℓ hp hℓp' hζu.unit hζ2 (δ x) n
  have hbridge : Differential.traceAlong (heckeAlphaC k p ℓ)
      (Differential.pullbackAlong (heckeBetaC k p ℓ) (δ x)) =
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaC k p ℓ)
       haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC k p ℓ)
       traceDiff k (FF k p) (charLDegeneracyRoof k p ℓ) (pullbackDiff (heckeBetaC k p ℓ) (δ x))) := by
    rw [traceAlong_apply_eq_traceDiff (heckeAlphaC k p ℓ) hsep]
    rfl
  have h3 : qexp k p (δ y) = ((((ℓ : ℕ) + 1 : ℕ) : ℤ) : k) • qexp k p (δ x) := by
    rw [h2]; exact LinearMap.map_smul _ _ _
  rw [← hbridge, ← h1] at hHQ
  change (qexp k p (δ y)).coeff n = _ at hHQ
  rw [h3, HahnSeries.coeff_smul, smul_eq_mul] at hHQ
  change _ = (qexp k p (δ x)).coeff ((ℓ : ℤ) * n)
      + (if ((ℓ : ℕ) : ℤ) ∣ n then ((ℓ : ℕ) : k) * (qexp k p (δ x)).coeff (n / (ℓ : ℕ)) else 0) at hHQ
  rw [← hHQ]
  push_cast
  ring

theorem coeff_law_level (hp : (p : k) ≠ 0)
    (τ : FF k p ≃ₐ[k] FF k p)
    (hτ₁ : τ ⟨jqModC k, jqModC_mem k p⟩ = ⟨jqNModC k p, jqNModC_mem k p⟩)
    (hτ₂ : τ ⟨jqNModC k p, jqNModC_mem k p⟩ = ⟨jqModC k, jqModC_mem k p⟩)
    (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (hδ : IsDlogRecipe q δ)
    (x : Pic0.torsion k (FF k p) q)
    (hUx : heckePic0Fibre k p p (x : Pic0 k (FF k p)) = (x : Pic0 k (FF k p)))
    (hWx : τ • (x : Pic0 k (FF k p)) = -(x : Pic0 k (FF k p))) (n : ℤ) :
    (qexp k p (δ x)).coeff (n * p) = (qexp k p (δ x)).coeff n := by
  obtain ⟨E, g, hEx, hg, hEg⟩ := exists_rep (k := k) (p := p) (Pic0.mem_torsion.mp x.2)
  rw [hδ x E g hEx hg hEg, qexp_dlog]
  have hE' : (⟨(E : Divisor k (FF k p)), E.2⟩ : Divisor.degZero (K := k) (F := FF k p)) = E := rfl
  refine coeff_inv_mul_thetaL_mul_level_eq_of_heckePic0Fibre_self_eq_of_smul_eq_neg k q p hp τ hτ₁ hτ₂
    (E : Divisor k (FF k p)) E.2 g hg hEg ?_ ?_ n
  · rw [hE', hEx]
    exact hUx
  · rw [hE', hEx]
    exact hWx

theorem congr_mk {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (E : Divisor.degZero (K := K) (F := F)) :
    Pic0.congr e he (Pic0.mk E) = Pic0.mk (Pic0.degZeroCongr e he E) := rfl

theorem coeff_pow_char_eq (hp : (p : k) ≠ 0)
    (hE : modularFunctionFieldC k p = modularFunctionFieldFullC k p)
    (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (hδ : IsDlogRecipe q δ)
    (x : Pic0.torsion k (FF k p) q)
    (hFx : heckeOperatorModL k p q
        (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p))) =
      Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p))) (n : ℤ) :
    ((qexp k p (δ x)).coeff n) ^ q = (qexp k p (δ x)).coeff n := by
  obtain ⟨E, g, hEx, hg, hEg⟩ := exists_rep (k := k) (p := p) (Pic0.mem_torsion.mp x.2)

  have htor : (q : ℤ) • Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
      (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p)) = 0 := by
    rw [← map_zsmul]
    erw [Pic0.mem_torsion.mp x.2]
    exact map_zero _
  have hpull := frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero k q p _ htor
  have hpush : frobeniusPushforwardModL k p q
      (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p))) =
      Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p)) := by
    have h := hFx
    rw [heckeOperatorModL_apply, hpull, add_zero] at h
    exact h

  set E' : Divisor.degZero (K := k) (F := modularFunctionFieldFullC k p) :=
    Pic0.degZeroCongr (IntermediateField.equivOfEq hE).toRingEquiv
      (fun a => (IntermediateField.equivOfEq hE).commutes a) E with hE'def
  have hcgx : Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p)) =
      Pic0.mk ⟨(E' : Divisor k (modularFunctionFieldFullC k p)), E'.2⟩ := by
    rw [← hEx]
    exact congr_mk _ _ E
  have hg' : (IntermediateField.equivOfEq hE).toRingEquiv g ≠ 0 :=
    (map_ne_zero (IntermediateField.equivOfEq hE).toRingEquiv).mpr hg
  have hEg' : ∀ w : Place k (modularFunctionFieldFullC k p),
      (q : ℤ) * (E' : Divisor k (modularFunctionFieldFullC k p)) w =
        w.ord ((IntermediateField.equivOfEq hE).toRingEquiv g) := by
    intro w
    obtain ⟨v, rfl⟩ := (Place.congrEquiv (IntermediateField.equivOfEq hE).toRingEquiv
      (fun a => (IntermediateField.equivOfEq hE).commutes a)).surjective w
    change (q : ℤ) * Divisor.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a) (E : Divisor k (FF k p))
        (Place.congrRingEquiv (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) v) =
      (Place.congrRingEquiv (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a) v).ord
        ((IntermediateField.equivOfEq hE).toRingEquiv g)
    rw [Divisor.congr_apply_place_congr, Place.ord_congrRingEquiv]
    exact hEg v
  rw [hcgx] at hpush
  have key := coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq k q p _ _
    ((IntermediateField.equivOfEq hE).toRingEquiv g) hg' hEg' hpush
  have hcoe : (((IntermediateField.equivOfEq hE).toRingEquiv g : modularFunctionFieldFullC k p) :
      LaurentSeries k) = (g : LaurentSeries k) := rfl
  rw [hcoe] at key
  rw [hδ x E g hEx hg hEg, qexp_dlog]
  have := congrArg (fun s : LaurentSeries k => s.coeff n) key
  simpa only [coeffMap_coeff, frobenius_def] using this

theorem coeff_law_char (hp : (p : k) ≠ 0)
    (hE : modularFunctionFieldC k p = modularFunctionFieldFullC k p)
    (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (hδ : IsDlogRecipe q δ)
    (x : Pic0.torsion k (FF k p) q)
    (hFx : heckeOperatorModL k p q
        (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p))) =
      Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p))) (n : ℤ) :
    (qexp k p (δ x)).coeff (n * q) = (qexp k p (δ x)).coeff n := by
  rw [← coeff_pow_char_eq hp hE δ hδ x hFx n]
  obtain ⟨E, g, hEx, hg, hEg⟩ := exists_rep (k := k) (p := p) (Pic0.mem_torsion.mp x.2)
  rw [hδ x E g hEx hg hEg, qexp_dlog]
  have hg' : (g : LaurentSeries k) ≠ 0 := fun h => hg (Subtype.ext h)
  exact coeff_inv_mul_thetaL_mul_char_eq_pow k q (g : LaurentSeries k) hg' n

theorem coeff_eq_zero_of_nonpos
    (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (hδ : IsDlogRecipe q δ)
    (x : Pic0.torsion k (FF k p) q) (n : ℤ) (hn : n ≤ 0) :
    (qexp k p (δ x)).coeff n = 0 := by
  obtain ⟨E, g, hEx, hg, hEg⟩ := exists_rep (k := k) (p := p) (Pic0.mem_torsion.mp x.2)
  rw [hδ x E g hEx hg hEg, qexp_dlog]
  exact coeff_dlog_eq_zero_of_nonpos (q := q) hg hEg n hn

end MemberLaws

section Formal

variable (k : Type*) [Field k]

def seqV : Submodule k (ℕ → k) := LinearMap.ker (LinearMap.proj 0 : (ℕ → k) →ₗ[k] k)

theorem mem_seqV {v : ℕ → k} : v ∈ seqV k ↔ v 0 = 0 := LinearMap.mem_ker

def coefA (n : ℕ) : seqV k →ₗ[k] k := (LinearMap.proj n : (ℕ → k) →ₗ[k] k).comp (seqV k).subtype

@[scoped simp] theorem coefA_apply (n : ℕ) (v : seqV k) : coefA k n v = (v : ℕ → k) n := rfl

def heckeFun (c : k) (ℓ : ℕ) : (ℕ → k) →ₗ[k] (ℕ → k) where
  toFun v n := if n = 0 then 0 else v (n * ℓ) + (if ℓ ∣ n then c * v (n / ℓ) else 0)
  map_add' v w := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a v := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem heckeFun_apply (c : k) (ℓ : ℕ) (v : ℕ → k) (n : ℕ) :
    heckeFun k c ℓ v n = if n = 0 then 0 else v (n * ℓ) + (if ℓ ∣ n then c * v (n / ℓ) else 0) := rfl

def heckeT (c : k) (ℓ : ℕ) : seqV k →ₗ[k] seqV k :=
  ((heckeFun k c ℓ).comp (seqV k).subtype).codRestrict (seqV k) (fun v => by
    rw [mem_seqV, LinearMap.comp_apply, heckeFun_apply, if_pos rfl])

theorem coe_heckeT (c : k) (ℓ : ℕ) (v : seqV k) :
    (heckeT k c ℓ v : ℕ → k) = heckeFun k c ℓ (v : ℕ → k) := rfl

theorem coefA_heckeT (c : ℕ → k) (ℓ : ℕ) (n : ℕ) (hn : 1 ≤ n) (v : seqV k) :
    coefA k n (heckeT k (c ℓ) ℓ v) = coefA k (n * ℓ) v + (if ℓ ∣ n then c ℓ * coefA k (n / ℓ) v else 0) := by
  rw [coefA_apply, coe_heckeT, heckeFun_apply, if_neg (by omega)]
  rfl

theorem eq_zero_of_coefA (v : seqV k) (h : ∀ n : ℕ, 1 ≤ n → coefA k n v = 0) : v = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (mem_seqV k).mp v.2
  · exact h n hn

end Formal

section Main

variable {k : Type*} [Field k] [IsAlgClosed k] {q : ℕ} [hq : Fact q.Prime] [CharP k q]
variable {p : ℕ} [hpp : Fact p.Prime]

def vec (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (x : Pic0.torsion k (FF k p) q) : seqV k :=
  ⟨fun n => if n = 0 then 0 else (qexp k p (δ x)).coeff (n : ℤ), by rw [mem_seqV, if_pos rfl]⟩

theorem coe_vec (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (x : Pic0.torsion k (FF k p) q) (n : ℕ) :
    (vec δ x : ℕ → k) n = if n = 0 then 0 else (qexp k p (δ x)).coeff (n : ℤ) := rfl

theorem coe_vec_of_pos (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (x : Pic0.torsion k (FF k p) q)
    {n : ℕ} (hn : 1 ≤ n) : (vec δ x : ℕ → k) n = (qexp k p (δ x)).coeff (n : ℤ) := by
  rw [coe_vec, if_neg (by omega)]

def vecHom (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) : Pic0.torsion k (FF k p) q →+ seqV k where
  toFun := vec δ
  map_zero' := by
    refine Subtype.ext (funext fun n => ?_)
    rw [coe_vec, map_zero, map_zero, HahnSeries.coeff_zero, ite_self]
    rfl
  map_add' x y := by
    refine Subtype.ext (funext fun n => ?_)
    change (vec δ (x + y) : ℕ → k) n = (vec δ x : ℕ → k) n + (vec δ y : ℕ → k) n
    simp only [coe_vec, map_add, HahnSeries.coeff_add]
    split_ifs <;> ring

theorem eq_zero_of_vec_eq_zero (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (hδ : IsDlogRecipe q δ)
    (hinj : Function.Injective δ) (x : Pic0.torsion k (FF k p) q) (hx : vec δ x = 0) : x = 0 := by
  apply hinj
  rw [map_zero]
  apply qexp_injective
  rw [map_zero]
  ext n
  rw [HahnSeries.coeff_zero]
  rcases le_or_gt n 0 with hn | hn
  · exact coeff_eq_zero_of_nonpos (q := q) δ hδ x n hn
  · have hv := congrArg (fun v : seqV k => (v : ℕ → k) n.toNat) hx
    beta_reduce at hv
    rw [coe_vec_of_pos δ x (by omega), Int.toNat_of_nonneg hn.le] at hv
    exact hv

def muSys (k : Type*) [Field k] (p : ℕ) (ℓ : ℕ) : k := if ℓ = p then 1 else (ℓ : k) + 1

def cSys (k : Type*) [Field k] (p : ℕ) (ℓ : ℕ) : k := if ℓ = p then 0 else (ℓ : k)

theorem vec_mem_iInf (hp : (p : k) ≠ 0)
    (hE : modularFunctionFieldC k p = modularFunctionFieldFullC k p)
    (τ : FF k p ≃ₐ[k] FF k p)
    (hτ₁ : τ ⟨jqModC k, jqModC_mem k p⟩ = ⟨jqNModC k p, jqNModC_mem k p⟩)
    (hτ₂ : τ ⟨jqNModC k p, jqNModC_mem k p⟩ = ⟨jqModC k, jqModC_mem k p⟩)
    (δ : Pic0.torsion k (FF k p) q →+ Ω[FF k p⁄k]) (hδ : IsDlogRecipe q δ)
    (x : Pic0.torsion k (FF k p) q)
    (hTx : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → ((ℓ : ℕ) : k) ≠ 0 →
      (letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckePic0Fibre k p ℓ (x : Pic0 k (FF k p)))
        = (((ℓ : ℕ) + 1 : ℕ) : ℤ) • (x : Pic0 k (FF k p)))
    (hUx : heckePic0Fibre k p p (x : Pic0 k (FF k p)) = (x : Pic0 k (FF k p)))
    (hWx : τ • (x : Pic0 k (FF k p)) = -(x : Pic0 k (FF k p)))
    (hFx : heckeOperatorModL k p q
        (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p))) =
      Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 k (FF k p))) :
    vec δ x ∈ ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (heckeT k (cSys k p ℓ) ℓ) (muSys k p ℓ) := by
  simp only [Submodule.mem_iInf]
  intro ℓ hℓ
  rw [Module.End.mem_eigenspace_iff]
  refine Subtype.ext (funext fun n => ?_)
  rw [coe_heckeT, heckeFun_apply]
  change _ = ((muSys k p ℓ) • (vec δ x : ℕ → k)) n
  rw [Pi.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos rfl, coe_vec, if_pos rfl, mul_zero]
  rw [if_neg (by omega), coe_vec_of_pos δ x hn,
    coe_vec_of_pos δ x (Nat.mul_pos hn hℓ.pos : 1 ≤ n * ℓ)]
  by_cases hℓp : ℓ = p
  ·
    subst hℓp
    rw [cSys, if_pos rfl, muSys, if_pos rfl, one_mul, zero_mul, ite_self, add_zero]
    push_cast
    exact coeff_law_level (q := q) hp τ hτ₁ hτ₂ δ hδ x hUx hWx n
  rw [cSys, if_neg hℓp, muSys, if_neg hℓp]
  by_cases hℓk : ((ℓ : ℕ) : k) = 0
  ·
    have hℓq : ℓ = q := by
      have h := (CharP.cast_eq_zero_iff k q ℓ).mp hℓk
      exact ((Nat.prime_dvd_prime_iff_eq hq.out hℓ).mp h).symm
    subst hℓq
    rw [hℓk, zero_mul, ite_self, add_zero, zero_add, one_mul]
    push_cast
    exact coeff_law_char hp hE δ hδ x hFx n
  ·
    have h := coeff_law_hecke (q := q) hp δ hδ ⟨ℓ, hℓ⟩ hℓp hℓk x (hTx ⟨ℓ, hℓ⟩ hℓp hℓk) n
    simp only at h
    rw [mul_comm ((ℓ : ℕ) : ℤ) (n : ℤ)] at h
    push_cast at h ⊢
    rw [← h]
    congr 1
    by_cases hdvd : ℓ ∣ n
    · rw [if_pos hdvd, if_pos (Int.natCast_dvd_natCast.mpr hdvd),
        coe_vec_of_pos δ x (Nat.div_pos (Nat.le_of_dvd hn hdvd) hℓ.pos), Int.natCast_div]
    · rw [if_neg hdvd, if_neg (fun h => hdvd (Int.natCast_dvd_natCast.mp h))]

theorem main (hp : (p : k) ≠ 0)
    (hE : modularFunctionFieldC k p = modularFunctionFieldFullC k p)
    (τ : modularFunctionFieldC k p ≃ₐ[k] modularFunctionFieldC k p)
    (hτ₁ : τ ⟨jqModC k, jqModC_mem k p⟩ = ⟨jqNModC k p, jqNModC_mem k p⟩)
    (hτ₂ : τ ⟨jqNModC k p, jqNModC_mem k p⟩ = ⟨jqModC k, jqModC_mem k p⟩)
    (Z : AddSubgroup (Pic0 k (modularFunctionFieldC k p)))
    (hqZ : ∀ z ∈ Z, (q : ℤ) • z = 0)
    (hT : ∀ z ∈ Z, ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → ((ℓ : ℕ) : k) ≠ 0 →
      (letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckePic0Fibre k p ℓ z) = (((ℓ : ℕ) + 1 : ℕ) : ℤ) • z)
    (hU : ∀ z ∈ Z, heckePic0Fibre k p p z = z)
    (hW : ∀ z ∈ Z, τ • z = -z)
    (hF : ∀ z ∈ Z,
      heckeOperatorModL k p q
          (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
            (fun a => (IntermediateField.equivOfEq hE).commutes a) z) =
        Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) z) :
    ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ = 0 ∨ ∃ m : ℕ, z₂ = m • z₁ := by
  classical
  intro z₁ hz₁ z₂ hz₂
  obtain ⟨δ, hinj, hδ⟩ := exists_dlog (k := k) (p := p) q hp
  have hδ' : IsDlogRecipe q δ := hδ

  let tors : ∀ z ∈ Z, Pic0.torsion k (FF k p) q := fun z hz => ⟨z, Pic0.mem_torsion.mpr (hqZ z hz)⟩
  have hmem : ∀ z (hz : z ∈ Z), vec δ (tors z hz) ∈
      ⨅ (ℓ : ℕ) (_ : ℓ.Prime), Module.End.eigenspace (heckeT k (cSys k p ℓ) ℓ) (muSys k p ℓ) :=
    fun z hz => vec_mem_iInf hp hE τ hτ₁ hτ₂ δ hδ' (tors z hz) (hT z hz) (hU z hz) (hW z hz) (hF z hz)

  have hM1 := (LinearMap.finrank_iInf_eigenspace_le_one_of_coeff_hecke_law (coefA k)
    (eq_zero_of_coefA k) (fun ℓ => heckeT k (cSys k p ℓ) ℓ) (cSys k p)
    (fun ℓ _ n hn v => coefA_heckeT k (cSys k p) ℓ n hn v) (muSys k p)).1
  by_cases h0 : z₁ = 0
  · exact Or.inl h0
  right

  set a₁ : k := coefA k 1 (vec δ (tors z₁ hz₁)) with ha₁
  set a₂ : k := coefA k 1 (vec δ (tors z₂ hz₂)) with ha₂
  have ha₁ne : a₁ ≠ 0 := by
    intro h
    apply h0
    have hv := hM1 _ (hmem z₁ hz₁) h
    have := eq_zero_of_vec_eq_zero δ hδ' hinj (tors z₁ hz₁) hv
    exact congrArg Subtype.val this

  have hfix : ∀ z (hz : z ∈ Z), (coefA k 1 (vec δ (tors z hz))) ^ q = coefA k 1 (vec δ (tors z hz)) := by
    intro z hz
    rw [coefA_apply, coe_vec_of_pos δ _ le_rfl]
    exact coeff_pow_char_eq hp hE δ hδ' (tors z hz) (hF z hz) 1
  have hratio : (a₂ / a₁) ^ q = a₂ / a₁ := by rw [div_pow, hfix z₁ hz₁, hfix z₂ hz₂]
  obtain ⟨m, hm⟩ := exists_natCast_eq_of_pow_eq q hratio
  refine ⟨m, ?_⟩

  have hsub : z₂ - m • z₁ ∈ Z := Z.sub_mem hz₂ (Z.nsmul_mem hz₁ m)
  have htors : tors (z₂ - m • z₁) hsub = tors z₂ hz₂ - m • tors z₁ hz₁ := Subtype.ext rfl
  have hvec : vec δ (tors (z₂ - m • z₁) hsub) = vec δ (tors z₂ hz₂) - m • vec δ (tors z₁ hz₁) := by
    rw [htors]
    exact (map_sub (vecHom δ) _ _).trans (by rw [map_nsmul]; rfl)
  have ha : coefA k 1 (vec δ (tors (z₂ - m • z₁) hsub)) = 0 := by
    rw [hvec, map_sub, map_nsmul, ← ha₁, ← ha₂, nsmul_eq_mul, hm, div_mul_cancel₀ _ ha₁ne, sub_self]
  have hv := hM1 _ (hmem _ hsub) ha
  have := eq_zero_of_vec_eq_zero δ hδ' hinj _ hv
  have h' : z₂ - m • z₁ = 0 := congrArg Subtype.val this
  rwa [sub_eq_zero] at h'

end Main

end RankOneFibreW
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg.ModularCurve.RankOneFibreW"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg.ModularCurve.RankOneFibreW P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg.ModularCurve.RankOneFibreW P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg.ModularCurve AlgebraicCurve in
theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    (hE : modularFunctionFieldC k p = modularFunctionFieldFullC k p)
    (τ : modularFunctionFieldC k p ≃ₐ[k] modularFunctionFieldC k p)
    (hτ₁ : τ ⟨jqModC k, jqModC_mem k p⟩ = ⟨jqNModC k p, jqNModC_mem k p⟩)
    (hτ₂ : τ ⟨jqNModC k p, jqNModC_mem k p⟩ = ⟨jqModC k, jqModC_mem k p⟩)
    (Z : AddSubgroup (Pic0 k (modularFunctionFieldC k p)))
    (hq : ∀ z ∈ Z, (q : ℤ) • z = 0)
    (hT : ∀ z ∈ Z, ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → ((ℓ : ℕ) : k) ≠ 0 →
      (letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckePic0Fibre k p ℓ z) = (((ℓ : ℕ) + 1 : ℕ) : ℤ) • z)
    (hU : ∀ z ∈ Z, heckePic0Fibre k p p z = z)
    (hW : ∀ z ∈ Z, τ • z = -z)
    (hF : ∀ z ∈ Z,
      heckeOperatorModL k p q
          (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
            (fun a => (IntermediateField.equivOfEq hE).commutes a) z) =
        Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) z) :
    ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ = 0 ∨ ∃ m : ℕ, z₂ = m • z₁ :=
  ModularCurve.RankOneFibreW.main hp hE τ hτ₁ hτ₂ Z hq hT hU hW hF

end S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg
end P2MW
export P2MW.S_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg (solution)
