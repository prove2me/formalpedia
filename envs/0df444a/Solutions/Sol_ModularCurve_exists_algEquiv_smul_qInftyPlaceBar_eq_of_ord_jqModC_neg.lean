-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e3d082ef-f658-5ae3-80a4-64216d155f08

import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

noncomputable section

open ModularCurve AlgebraicCurve

namespace CharpS10bB
namespace SigDev

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

private def GenPerm (σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N) : Prop :=
  ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), ∃ (d' : ℕ) (_ : NeZero d') (hd' : d' ∣ N),
    σ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩
      = ⟨qExpand K d' (jqModC K), jqModCd_mem_full K N hd'⟩

omit [NeZero N] in
private theorem genPerm_refl : GenPerm K N (AlgEquiv.refl) :=
  fun d hne hd => ⟨d, hne, hd, rfl⟩

omit [NeZero N] in
private theorem genPerm_trans {σ τ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N}
    (hσ : GenPerm K N σ) (hτ : GenPerm K N τ) : GenPerm K N (σ.trans τ) := by
  intro d hne hd
  obtain ⟨d', hne', hd', he'⟩ := hσ d hne hd
  obtain ⟨d'', hne'', hd'', he''⟩ := hτ d' hne' hd'
  exact ⟨d'', hne'', hd'', by rw [AlgEquiv.trans_apply, he', he'']⟩

omit [NeZero N] in

private theorem qExpand_jqModC_congr {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) :
    qExpand K m (jqModC K) = qExpand K n (jqModC K) := by
  subst h; rfl

omit [NeZero N] in

private theorem eq_of_qExpand_eq {d d' : ℕ} [NeZero d] [NeZero d']
    (h : qExpand K d (jqModC K) = qExpand K d' (jqModC K)) : d = d' := by
  have hord : (-d : ℤ) = (-d' : ℤ) := by
    have := congrArg HahnSeries.order h
    rwa [order_qExpandC K d (jqModC_ne_zero_def K), order_qExpandC K d' (jqModC_ne_zero_def K),
      order_jqModC_def, mul_neg_one, mul_neg_one] at this
  exact_mod_cast neg_injective hord

private theorem genPerm_symm {σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N}
    (hσ : GenPerm K N σ) : GenPerm K N σ.symm := by
  intro d hne hd
  classical

  have hN0 : N ≠ 0 := NeZero.ne N
  let φ : {e // e ∈ N.divisors} → {e // e ∈ N.divisors} := fun e =>
    haveI : NeZero (e : ℕ) := ⟨(Nat.pos_of_mem_divisors e.2).ne'⟩
    ⟨(hσ e.1 inferInstance (Nat.mem_divisors.mp e.2).1).choose,
     Nat.mem_divisors.mpr ⟨(hσ e.1 inferInstance (Nat.mem_divisors.mp e.2).1).choose_spec.2.1,
       hN0⟩⟩
  have hφinj : Function.Injective φ := by
    intro e e' heq
    haveI : NeZero (e : ℕ) := ⟨(Nat.pos_of_mem_divisors e.2).ne'⟩
    haveI : NeZero (e' : ℕ) := ⟨(Nat.pos_of_mem_divisors e'.2).ne'⟩
    obtain ⟨_, _, he⟩ := (hσ e.1 inferInstance (Nat.mem_divisors.mp e.2).1).choose_spec
    obtain ⟨_, _, he'⟩ := (hσ e'.1 inferInstance (Nat.mem_divisors.mp e'.2).1).choose_spec
    have hveq : σ ⟨qExpand K e.1 (jqModC K), jqModCd_mem_full K N (Nat.mem_divisors.mp e.2).1⟩
        = σ ⟨qExpand K e'.1 (jqModC K), jqModCd_mem_full K N (Nat.mem_divisors.mp e'.2).1⟩ := by
      rw [he, he']
      exact Subtype.ext (qExpand_jqModC_congr K (congrArg Subtype.val heq))
    exact Subtype.ext (eq_of_qExpand_eq K (Subtype.ext_iff.mp (σ.injective hveq)))
  have hφsurj : Function.Surjective φ := Finite.surjective_of_injective hφinj
  obtain ⟨⟨e, he⟩, hφe⟩ := hφsurj ⟨d, Nat.mem_divisors.mpr ⟨hd, hN0⟩⟩
  haveI : NeZero e := ⟨(Nat.pos_of_mem_divisors he).ne'⟩
  obtain ⟨_, _, hσe⟩ := (hσ e inferInstance (Nat.mem_divisors.mp he).1).choose_spec
  refine ⟨e, inferInstance, (Nat.mem_divisors.mp he).1, ?_⟩
  rw [show (⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ : modularFunctionFieldFullC K N)
      = σ ⟨qExpand K e (jqModC K), jqModCd_mem_full K N (Nat.mem_divisors.mp he).1⟩ from ?_,
    σ.symm_apply_apply]
  rw [hσe]
  exact Subtype.ext (qExpand_jqModC_congr K (congrArg Subtype.val hφe).symm)

private abbrev KJ : IntermediateField K (modularFunctionFieldFullC K N) :=
  IntermediateField.adjoin K
    ({⟨jqModC K, jqModC_mem_full K N⟩} : Set (modularFunctionFieldFullC K N))

set_option synthInstance.maxHeartbeats 1600000 in

private scoped instance algKJ : Algebra K ↥(KJ K N) := inferInstance

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance stKJ : IsScalarTower K ↥(KJ K N) ↥(modularFunctionFieldFullC K N) := inferInstance

private def divGen : Set (modularFunctionFieldFullC K N) :=
  {x | (x : LaurentSeries K) ∈ divisorExpansionsC K N}

omit [NeZero N] in

private theorem adjoin_divGen_eq_top :
    IntermediateField.adjoin K (divGen K N) = (⊤ : IntermediateField K (modularFunctionFieldFullC K N)) := by
  refine eq_top_iff.mpr fun x _ => ?_

  have himg : (modularFunctionFieldFullC K N).val '' (divGen K N) = divisorExpansionsC K N := by
    ext y; constructor
    · rintro ⟨⟨z, hz⟩, hzS, rfl⟩; exact hzS
    · intro hy
      exact ⟨⟨y, IntermediateField.subset_adjoin K _ hy⟩, hy, rfl⟩
  have hmap : (IntermediateField.adjoin K (divGen K N)).map (modularFunctionFieldFullC K N).val
      = modularFunctionFieldFullC K N :=
    (IntermediateField.adjoin_map (F := K) (E := ↥(modularFunctionFieldFullC K N))
        (S := divGen K N) (modularFunctionFieldFullC K N).val).trans (by rw [himg]; rfl)
  have hx : (x : LaurentSeries K)
      ∈ (IntermediateField.adjoin K (divGen K N)).map (modularFunctionFieldFullC K N).val :=
    hmap.ge x.2
  obtain ⟨y, hy, hyval⟩ := hx
  rwa [show x = y from Subtype.val_injective hyval.symm]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem finDim (hNK : (N : K) ≠ 0) : FiniteDimensional (KJ K N) (modularFunctionFieldFullC K N) := by
  have hψ : 0 < dedekindPsi N := by
    unfold dedekindPsi
    refine Finset.sum_pos (fun d hd => ?_) ⟨1, by simp [NeZero.ne N]⟩
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.2) hd.1.1)
      (Nat.pos_of_ne_zero fun h => hd.1.2 (by simpa [h] using hd.1.1))
  exact Module.finite_of_finrank_pos
    ((finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hNK).symm ▸ hψ)

private theorem toggle_of_prime (hsq : Squarefree N) (hNK : (N : K) ≠ 0)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    ∃ τ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
      GenPerm K N τ ∧
      ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N) (_ : ¬ p ∣ d) (_ : NeZero (d * p)) (hdp : d * p ∣ N),
        τ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩
          = ⟨qExpand K (d * p) (jqModC K), jqModCd_mem_full K N hdp⟩ := by
  have hpne : (p : K) ≠ 0 := fun h => hNK (by
    obtain ⟨m, rfl⟩ := hpN; push_cast; exact mul_eq_zero_of_left h _)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨M, hMp⟩ : ∃ M, M * p = N := ⟨N / p, Nat.div_mul_cancel hpN⟩
  subst hMp
  haveI : NeZero M := ⟨fun hM0 => NeZero.ne (M * p) (by rw [hM0, zero_mul])⟩
  have hpM : ¬ p ∣ M := fun ⟨k, hk⟩ =>
    hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p ⟨k, by rw [hk]; ring⟩))
  have hMK : (M : K) ≠ 0 := fun h => hNK (by push_cast; exact mul_eq_zero_of_left h _)

  obtain ⟨τ, hτ⟩ :=
    ModularCurve.exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd K M p hp hpM hMK hpne
  refine ⟨τ, ?_, ?_⟩
  ·
    intro e hne he
    by_cases hpe : p ∣ e
    · obtain ⟨e', he'⟩ := hpe
      haveI : NeZero e' := ⟨fun h => hne.out (by rw [he', h, mul_zero])⟩
      have hcomm : e = e' * p := by rw [he', mul_comm]
      have he'M : e' ∣ M := by
        have : e' * p ∣ M * p := hcomm ▸ he
        exact (Nat.mul_dvd_mul_iff_right hp.pos).mp this
      haveI : NeZero (e' * p) := ⟨Nat.mul_ne_zero (NeZero.ne e') hp.ne_zero⟩
      refine ⟨e', inferInstance, Dvd.dvd.mul_right he'M p, ?_⟩
      rw [show (⟨qExpand K e (jqModC K), jqModCd_mem_full K (M * p) he⟩ : modularFunctionFieldFullC K (M * p))
          = ⟨qExpand K (e' * p) (jqModC K), jqModCd_mem_full K (M * p) (Nat.mul_dvd_mul_right he'M p)⟩ from
        Subtype.ext (qExpand_jqModC_congr K hcomm), (hτ e' inferInstance he'M).2]
    · have heM : e ∣ M := Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr hpe)) he
      haveI : NeZero (e * p) := ⟨Nat.mul_ne_zero hne.out hp.ne_zero⟩
      refine ⟨e * p, inferInstance, Nat.mul_dvd_mul_right heM p, ?_⟩
      rw [show (⟨qExpand K e (jqModC K), jqModCd_mem_full K (M * p) he⟩ : modularFunctionFieldFullC K (M * p))
          = ⟨qExpand K e (jqModC K), jqModCd_mem_full K (M * p) (Dvd.dvd.mul_right heM p)⟩ from
        Subtype.ext rfl, (hτ e hne heM).1]
  · intro d hne hd hpd hnedp hdp
    have hdM : d ∣ M := Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr hpd)) hd
    rw [show (⟨qExpand K d (jqModC K), jqModCd_mem_full K (M * p) hd⟩ : modularFunctionFieldFullC K (M * p))
        = ⟨qExpand K d (jqModC K), jqModCd_mem_full K (M * p) (Dvd.dvd.mul_right hdM p)⟩ from
      Subtype.ext rfl, (hτ d hne hdM).1]

private theorem exists_genPerm_apply_J_eq (hsq : Squarefree N) (hNK : (N : K) ≠ 0) :
    ∀ (d : ℕ) (hd : d ∣ N),
      haveI : NeZero d := ⟨fun h0 => (NeZero.ne N) (zero_dvd_iff.mp (h0 ▸ hd))⟩
      ∃ σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
        GenPerm K N σ
          ∧ σ ⟨jqModC K, jqModC_mem_full K N⟩ = ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd
  haveI hdne : NeZero d := ⟨fun h0 => (NeZero.ne N) (zero_dvd_iff.mp (h0 ▸ hd))⟩
  rcases eq_or_ne d 1 with rfl | hd1
  · exact ⟨AlgEquiv.refl, genPerm_refl K N, Subtype.ext (qExpand_one_apply _).symm⟩
  ·
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    have hpN : p ∣ N := hpd.trans hd

    set d' := d / p with hd'def
    have hd'p : d' * p = d := Nat.div_mul_cancel hpd
    haveI : NeZero d' := ⟨fun h => hdne.out (by rw [← hd'p, h, zero_mul])⟩
    have hd'lt : d' < d := by
      have : d' * 1 < d' * p := (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero (NeZero.ne d'))).mpr hp.one_lt
      omega
    have hd'N : d' ∣ N := (Dvd.intro_left p (by rw [mul_comm]; exact hd'p)).trans hd
    have hpd' : ¬ p ∣ d' := fun ⟨k, hk⟩ =>
      hp.one_lt.ne' (Nat.isUnit_iff.mp ((hsq.squarefree_of_dvd hd) p ⟨k, by rw [← hd'p, hk]; ring⟩))

    obtain ⟨σ', hσ'perm, hσ'J⟩ := ih d' hd'lt hd'N

    obtain ⟨τ, hτperm, hτtog⟩ := toggle_of_prime K N hsq hNK p hp hpN
    refine ⟨σ'.trans τ, genPerm_trans K N hσ'perm hτperm, ?_⟩
    haveI : NeZero (d' * p) := ⟨Nat.mul_ne_zero (NeZero.ne d') hp.ne_zero⟩
    rw [AlgEquiv.trans_apply, hσ'J,
      hτtog d' inferInstance hd'N hpd' inferInstance (hd'p ▸ hd)]
    exact Subtype.ext (qExpand_jqModC_congr K hd'p)

omit [NeZero N] in

private theorem order_Jd (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (qSeriesBar K (modularFunctionFieldFullC K N)
      (⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ : modularFunctionFieldFullC K N)).order
      = -(d : ℤ) := by

  show (qExpand K d (jqModC K)).order = -(d : ℤ)
  rw [order_qExpandC K d (jqModC_ne_zero_def K), order_jqModC_def]
  ring

set_option synthInstance.maxHeartbeats 1600000 in

private theorem congrRingEquiv_injective {F F' : Type*} [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    {v v' : Place K F} (h : Place.congrRingEquiv e he v = Place.congrRingEquiv e he v') :
    v = v' := by
  have hVS : v.toValuationSubring = v'.toValuationSubring := by
    have := congrArg (·.toValuationSubring) h
    simp only [Place.congrRingEquiv_toValuationSubring] at this
    ext x
    have := SetLike.ext_iff.mp this (e x)
    simpa [ValuationSubring.mem_comap] using this
  exact Place.ext hVS

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem transcendental_jFullC :
    Transcendental K (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) :=
  fun halg => transcendental_jqModC K (by
    have := halg.algHom (modularFunctionFieldFullC K N).val
    simpa using this)

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

private theorem isSep_gen (hNK : (N : K) ≠ 0) (d : ℕ) [NeZero d] (hd : d ∣ N) :
    IsSeparable (KJ K N) (⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ : modularFunctionFieldFullC K N) := by
  classical
  have hdK : (d : K) ≠ 0 := fun h0 => hNK (by
    obtain ⟨c, hc⟩ := hd; rw [hc, Nat.cast_mul, h0, zero_mul])
  obtain ⟨data⟩ := nonempty_modularPolynomialData d

  set jF : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩ with hjF
  let gKJ := IntermediateField.AdjoinSimple.gen K jF
  let q : Polynomial (KJ K N) :=
    data.Φ.map (Polynomial.aeval (R := ℤ) gKJ).toRingHom

  have hfact : (Polynomial.aeval (R := ℤ) gKJ).toRingHom
      = (Polynomial.aeval (R := K) gKJ).toRingHom.comp
          (Polynomial.mapRingHom (Int.castRingHom K)) := by
    refine RingHom.ext fun p => ?_
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
      Polynomial.coe_mapRingHom]
    exact (Polynomial.aeval_map_algebraMap K gKJ p).symm

  have hsep : q.Separable := by
    have hRF := ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero
      K d data hdK
    have htrans : Transcendental K jF := transcendental_jFullC K N
    let e : RatFunc K ≃ₐ[K] ↥(KJ K N) := RatFunc.algEquivOfTranscendental jF htrans

    have heq : (e : RatFunc K →+* ↥(KJ K N)).comp (algebraMap (Polynomial K) (RatFunc K))
        = (Polynomial.aeval (R := K) gKJ).toRingHom :=
      RingHom.ext fun g => RatFunc.algEquivOfTranscendental_algebraMap jF htrans g
    have hqeq : q = ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
        (algebraMap (Polynomial K) (RatFunc K))).map (e : RatFunc K →+* ↥(KJ K N)) := by
      simp only [Polynomial.map_map]
      rw [show q = data.Φ.map (Polynomial.aeval (R := ℤ) gKJ).toRingHom from rfl, hfact]
      congr 1
      rw [← RingHom.comp_assoc, heq]
    rw [hqeq]; exact hRF.map

  have hroot : (Polynomial.aeval
      (⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ : modularFunctionFieldFullC K N)) q = 0 := by
    have h0 := data.eval_jqNModC_mul_eq_zero K 1
    simp only [jqNModC_one, one_mul] at h0
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero]

    have key : (((Polynomial.aeval
        (⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ : modularFunctionFieldFullC K N)) q
          : modularFunctionFieldFullC K N) : LaurentSeries K)
        = Polynomial.eval₂ (Polynomial.aeval (R := ℤ) (jqModC K)).toRingHom (jqNModC K d) data.Φ := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      have hval := Polynomial.hom_eval₂ data.Φ
        ((algebraMap ↥(KJ K N) ↥(modularFunctionFieldFullC K N)).comp
          (Polynomial.aeval (R := ℤ) gKJ).toRingHom)
        (modularFunctionFieldFullC K N).val.toRingHom
        (⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ : modularFunctionFieldFullC K N)
      refine Eq.trans ?_ (hval.trans ?_)
      · rfl
      · refine Polynomial.eval₂_congr ?_ rfl rfl

        refine Polynomial.ringHom_ext (fun n => ?_) ?_
        · rw [eq_intCast Polynomial.C n]
          exact (map_intCast _ n).trans (map_intCast _ n).symm
        · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
            RingHom.coe_coe, Polynomial.aeval_X, IntermediateField.coe_val]
          rw [IntermediateField.AdjoinSimple.algebraMap_gen]
    exact key.trans h0
  exact hsep.of_dvd (minpoly.dvd _ _ hroot)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isSep (hNK : (N : K) ≠ 0) :
    Algebra.IsSeparable (KJ K N) (modularFunctionFieldFullC K N) := by
  have hadj : IntermediateField.adjoin (↥(KJ K N)) (divGen K N)
      = (⊤ : IntermediateField (KJ K N) (modularFunctionFieldFullC K N)) :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top K (adjoin_divGen_eq_top K N)
  have hsepTop : Algebra.IsSeparable ↥(KJ K N)
      ↥(⊤ : IntermediateField (KJ K N) (modularFunctionFieldFullC K N)) := by
    rw [← hadj]
    refine (IntermediateField.isSeparable_adjoin_iff_isSeparable ↥(KJ K N)
      ↥(modularFunctionFieldFullC K N)).mpr ?_
    rintro ⟨x, hxmem⟩ hxS
    obtain ⟨d, hne, hdN, heq⟩ := hxS
    have hxeq : (⟨x, hxmem⟩ : modularFunctionFieldFullC K N)
        = ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hdN⟩ := Subtype.ext heq
    rw [hxeq]
    exact isSep_gen K N hNK d hdN
  exact AlgEquiv.Algebra.isSeparable (F := ↥(KJ K N))
    (IntermediateField.topEquiv : _ ≃ₐ[↥(KJ K N)] ↥(modularFunctionFieldFullC K N))

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem restrict_eq_of_ord_J_neg [FiniteDimensional (KJ K N) (modularFunctionFieldFullC K N)]
    (w w' : Place K (modularFunctionFieldFullC K N))
    (hw : w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) < 0)
    (hw' : w'.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) < 0) :
    w.restrict (KJ K N) = w'.restrict (KJ K N) := by
  classical

  set jF : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩ with hjF
  have htrans : Transcendental K jF := transcendental_jFullC K N
  let e : ↥(KJ K N) ≃ₐ[K] RatFunc K := (RatFunc.algEquivOfTranscendental jF htrans).symm
  have he : ∀ a : K, e.toRingEquiv (algebraMap K (KJ K N) a) = algebraMap K (RatFunc K) a :=
    fun a => e.commutes a

  have key : ∀ v : Place K (modularFunctionFieldFullC K N),
      v.ord jF < 0 →
      Place.congrRingEquiv e.toRingEquiv he (v.restrict (KJ K N))
        = RationalFunctionField.placeInfty K := by
    intro v hv
    refine RationalFunctionField.eq_placeInfty_of_ord_X_neg _ ?_

    have hX : (e.toRingEquiv : ↥(KJ K N) → RatFunc K) (IntermediateField.AdjoinSimple.gen K jF)
        = (RatFunc.X : RatFunc K) := by
      show e (IntermediateField.AdjoinSimple.gen K jF) = RatFunc.X
      exact RatFunc.algEquivOfTranscendental_symm_gen jF htrans
    rw [← hX, Place.ord_congrRingEquiv]

    have hrest := v.ord_restrict (F := KJ K N) (IntermediateField.AdjoinSimple.gen K jF)
    rw [IntermediateField.AdjoinSimple.algebraMap_gen] at hrest
    have hepos : (0 : ℤ) < v.ramificationIndex (F := KJ K N) := by
      exact_mod_cast v.ramificationIndex_pos (F := KJ K N)
    have : v.ord jF = (v.ramificationIndex (F := KJ K N) : ℤ)
        * (v.restrict (KJ K N)).ord (IntermediateField.AdjoinSimple.gen K jF) := hrest
    by_contra hle
    rw [not_lt] at hle
    have : (0 : ℤ) ≤ v.ord jF := by
      rw [this]; exact mul_nonneg hepos.le hle
    omega
  exact congrRingEquiv_injective K e.toRingEquiv he ((key w hw).trans (key w' hw').symm)

omit [NeZero N] in

private theorem sum_divisors_eq_dedekindPsi (hsq : Squarefree N) :
    ∑ d ∈ N.divisors, d = dedekindPsi N := by
  unfold dedekindPsi
  rw [Finset.filter_true_of_mem fun d hd =>
    Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hsq]
  exact (Nat.sum_div_divisors N id).symm

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem classify (hsq : Squarefree N) (hNK : (N : K) ≠ 0)
    (h : ∃ j : modularFunctionFieldFullC K N,
      (qSeriesBar K (modularFunctionFieldFullC K N) j).order = -1)
    (P : Place K (modularFunctionFieldFullC K N))
    (hpole : P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) < 0) :
    ∃ (σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N),
      GenPerm K N σ ∧ P = σ • qInftyPlaceBar K (modularFunctionFieldFullC K N) h := by
  classical
  haveI := finDim K N hNK
  haveI := isSep K N hNK
  set jF : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩ with hjF
  set wInf := qInftyPlaceBar K (modularFunctionFieldFullC K N) h with hwInf

  have hordInf : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
      wInf.ord ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ = -(d : ℤ) := by
    intro d hne hd
    rw [ord_qInftyPlaceBar K h]; exact order_Jd K N d hd
  have hordInfJ : wInf.ord jF = -1 := by
    have := hordInf 1 inferInstance (one_dvd N)
    simpa [hjF, Subtype.ext_iff, qExpand_one_apply] using this

  set v₀ := wInf.restrict (KJ K N) with hv0
  have hv0gen : v₀.ord (IntermediateField.AdjoinSimple.gen K jF) = -1 := by
    have hrest := wInf.ord_restrict (F := KJ K N) (IntermediateField.AdjoinSimple.gen K jF)
    rw [IntermediateField.AdjoinSimple.algebraMap_gen, hordInfJ] at hrest
    have hepos : (0 : ℤ) < wInf.ramificationIndex (F := KJ K N) := by
      exact_mod_cast wInf.ramificationIndex_pos (F := KJ K N)

    have hneg : v₀.ord (IntermediateField.AdjoinSimple.gen K jF) < 0 := by
      by_contra hle; rw [not_lt] at hle
      have h0 : (0 : ℤ) ≤ -1 := hrest ▸ mul_nonneg hepos.le hle; omega
    nlinarith [hrest, hepos, hneg,
      mul_le_mul_of_nonneg_left (show v₀.ord (IntermediateField.AdjoinSimple.gen K jF) ≤ -1 by omega)
        hepos.le]

  have hN0 : N ≠ 0 := NeZero.ne N
  let sig : {d // d ∈ N.divisors} → (modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N) :=
    fun d => (exists_genPerm_apply_J_eq K N hsq hNK d.1 (Nat.mem_divisors.mp d.2).1).choose
  let wfn : {d // d ∈ N.divisors} → Place K (modularFunctionFieldFullC K N) :=
    fun d => (sig d).symm • wInf

  have hwdord : ∀ d : {d // d ∈ N.divisors}, (wfn d).ord jF = -(d.1 : ℤ) := by
    intro ⟨d, hd⟩
    haveI : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
    have hσJ := (exists_genPerm_apply_J_eq K N hsq hNK d (Nat.mem_divisors.mp hd).1).choose_spec.2
    have hsmul := Place.ord_smul (K := K) (sig ⟨d, hd⟩).symm wInf ((sig ⟨d, hd⟩) jF)
    simp only [AlgEquiv.symm_apply_apply] at hsmul
    show ((sig ⟨d, hd⟩).symm • wInf).ord jF = -(d : ℤ)
    rw [hsmul,
      show (sig ⟨d, hd⟩) jF = ⟨qExpand K d (jqModC K), jqModCd_mem_full K N (Nat.mem_divisors.mp hd).1⟩ from hσJ,
      hordInf d inferInstance (Nat.mem_divisors.mp hd).1]

  have hwfninj : Function.Injective wfn := fun d d' heq => by
    have := (hwdord d).symm.trans (heq ▸ hwdord d')
    exact Subtype.ext (by exact_mod_cast neg_injective this)

  have hrestP : P.restrict (KJ K N) = v₀ :=
    restrict_eq_of_ord_J_neg K N P wInf hpole (by rw [hordInfJ]; omega)
  have hrestW : ∀ d, (wfn d).restrict (KJ K N) = v₀ := fun d =>
    restrict_eq_of_ord_J_neg K N (wfn d) wInf
      (by rw [hwdord d]; simp only [neg_neg_iff_pos, Int.natCast_pos];
          exact Nat.pos_of_mem_divisors d.2)
      (by rw [hordInfJ]; omega)

  have hewd : ∀ d, ((wfn d).ramificationIndex (F := KJ K N) : ℤ) = d.1 := by
    intro d
    have hrest := (wfn d).ord_restrict (F := KJ K N) (IntermediateField.AdjoinSimple.gen K jF)
    rw [IntermediateField.AdjoinSimple.algebraMap_gen, hwdord d, hrestW d, hv0gen] at hrest
    omega

  have hfwd : ∀ d, 1 ≤ ((wfn d).inertiaDeg (F := KJ K N) : ℤ) := fun d => by
    exact_mod_cast (wfn d).inertiaDeg_pos_of_finiteDimensional (F := KJ K N)

  let S : Finset (Place K (modularFunctionFieldFullC K N)) :=
    N.divisors.attach.image wfn
  have hcardS : S.card = N.divisors.card :=
    (Finset.card_image_of_injective _ hwfninj).trans Finset.card_attach
  by_contra hP
  push Not at hP

  have hPnotS : P ∉ S := by
    intro hPS
    obtain ⟨d, _, heq⟩ := Finset.mem_image.mp hPS
    exact (hP (sig d).symm (genPerm_symm K N
      (exists_genPerm_apply_J_eq K N hsq hNK d.1 (Nat.mem_divisors.mp d.2).1).choose_spec.1)
      heq.symm)
  have hSrest : ∀ w ∈ insert P S, w.restrict (KJ K N) = v₀ := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwS
    · exact hrestP
    · obtain ⟨d, _, heq⟩ := Finset.mem_image.mp hwS
      exact heq ▸ hrestW d
  have hupper := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank
    (F := KJ K N) v₀ (insert P S) hSrest
  rw [finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hNK,
    ← sum_divisors_eq_dedekindPsi N hsq] at hupper
  have hlower : (∑ d ∈ N.divisors, (d : ℤ)) + 1
      ≤ ∑ w ∈ insert P S, (w.ramificationIndex (F := KJ K N) : ℤ) * (w.inertiaDeg (F := KJ K N) : ℤ) := by
    rw [Finset.sum_insert hPnotS]
    have hSsum : (∑ d ∈ N.divisors, (d : ℤ))
        ≤ ∑ w ∈ S, (w.ramificationIndex (F := KJ K N) : ℤ) * (w.inertiaDeg (F := KJ K N) : ℤ) := by
      rw [show S = N.divisors.attach.image wfn from rfl,
        Finset.sum_image (fun d _ d' _ h => hwfninj h)]
      calc (∑ d ∈ N.divisors, (d : ℤ))
          = ∑ d ∈ N.divisors.attach, (d.1 : ℤ) := (Finset.sum_attach _ _).symm
        _ ≤ ∑ d ∈ N.divisors.attach,
              ((wfn d).ramificationIndex (F := KJ K N) : ℤ) * ((wfn d).inertiaDeg (F := KJ K N) : ℤ) :=
            Finset.sum_le_sum fun d _ => by
              rw [hewd d]; exact le_mul_of_one_le_right (Int.natCast_nonneg _) (hfwd d)
    have hPterm : (1 : ℤ)
        ≤ (P.ramificationIndex (F := KJ K N) : ℤ) * (P.inertiaDeg (F := KJ K N) : ℤ) := by
      have he := P.ramificationIndex_pos (F := KJ K N)
      have hf := P.inertiaDeg_pos_of_finiteDimensional (F := KJ K N)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he.ne' hf.ne')
    omega
  have : (∑ d ∈ N.divisors, (d : ℤ)) + 1 ≤ (∑ d ∈ N.divisors, (d : ℤ)) := by
    calc (∑ d ∈ N.divisors, (d : ℤ)) + 1 ≤ _ := hlower
      _ ≤ (∑ d ∈ N.divisors, (d : ℤ)) := by push_cast at hupper; exact hupper
  omega

end CharpS10bB.SigDev
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg.CharpS10bB P2MW.S_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg.CharpS10bB.SigDev"
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg.CharpS10bB"

open CharpS10bB.SigDev ModularCurve AlgebraicCurve in

theorem solution (K : Type*) [Field K]
    (N : ℕ) [NeZero N] (hsq : Squarefree N) (hNK : (N : K) ≠ 0)
    (h : ∃ j : modularFunctionFieldFullC K N, (qSeriesBar K (modularFunctionFieldFullC K N) j).order = -1)
    (P : Place K (modularFunctionFieldFullC K N))
    (hpole : P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) < 0) :
    ∃ σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
      (∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), ∃ (d' : ℕ) (_ : NeZero d') (hd' : d' ∣ N),
          σ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ = ⟨qExpand K d' (jqModC K), jqModCd_mem_full K N hd'⟩)
        ∧ P = σ • qInftyPlaceBar K (modularFunctionFieldFullC K N) h := by
  obtain ⟨σ, hperm, hP⟩ := classify K N hsq hNK h P hpole
  exact ⟨σ, hperm, hP⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg.CharpS10bB P2MW.S_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg.CharpS10bB.SigDev"

end S_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg (solution)
