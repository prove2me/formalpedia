-- Prove2me | solution 1 for ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ad6b6f32-cdb1-5efd-985d-a2a9458ab362

import Theorems.Thm_ModularCurve_exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_qInftyPlaceBar
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve

namespace CuspFrobeniusFixedAux

variable (k : Type*) [Field k] (N : ℕ) [NeZero N]
  {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

omit [Fact ℓ.Prime] in

private theorem jd_mem (hlN : ¬ ℓ ∣ N) {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand k d (jqModC k) ∈ modularFunctionFieldC k N := by
  rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k ℓ N hlN]
  exact jqModCd_mem_full k N hd

private theorem frob_jd_eq_pow (hlN : ¬ ℓ ∣ N) {d : ℕ} [NeZero d] (hd : d ∣ N) :
    frobeniusGeomLevel k N data hKr ⟨qExpand k d (jqModC k), jd_mem k N hlN hd⟩
      = (⟨qExpand k d (jqModC k), jd_mem k N hlN hd⟩ : modularFunctionFieldC k N) ^ ℓ := by
  refine Subtype.ext ?_
  rw [frobeniusGeomLevel_apply_coe]
  push_cast
  haveI : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (Fact.out (p := ℓ.Prime)).ne_zero (NeZero.ne d)⟩
  haveI : NeZero (d * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne d) (Fact.out (p := ℓ.Prime)).ne_zero⟩
  rw [qExpand_qExpand, qExpand_congr (mul_comm ℓ d), ← qExpand_qExpand,
    qExpand_jqModC_eq_pow k data hKr, map_pow]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem mffC_algHom_ext {A : Type*} [Field A] [Algebra k A]
    {f g : modularFunctionFieldC k N →ₐ[k] A}
    (hj : f ⟨jqModC k, jqModC_mem k N⟩ = g ⟨jqModC k, jqModC_mem k N⟩)
    (hjN : f ⟨jqNModC k N, jqNModC_mem k N⟩ = g ⟨jqNModC k N, jqNModC_mem k N⟩) :
    f = g := by
  refine AlgHom.ext fun x => ?_
  obtain ⟨y, hy⟩ := x
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz =>
      rcases hz with rfl | hz
      · exact hj
      · rw [Set.mem_singleton_iff] at hz; subst hz; exact hjN
  | algebraMap c =>
      exact (f.commutes c).trans (g.commutes c).symm
  | add z w hz hw ihz ihw =>
      show f (⟨z, hz⟩ + ⟨w, hw⟩) = g (⟨z, hz⟩ + ⟨w, hw⟩)
      rw [map_add, map_add, ihz, ihw]
  | inv z hz ihz =>
      show f (⟨z, hz⟩)⁻¹ = g (⟨z, hz⟩)⁻¹
      rw [map_inv₀, map_inv₀, ihz]
  | mul z w hz hw ihz ihw =>
      show f (⟨z, hz⟩ * ⟨w, hw⟩) = g (⟨z, hz⟩ * ⟨w, hw⟩)
      rw [map_mul, map_mul, ihz, ihw]

private def GenPermC (hlN : ¬ ℓ ∣ N)
    (σ : modularFunctionFieldC k N ≃ₐ[k] modularFunctionFieldC k N) : Prop :=
  ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), ∃ (d' : ℕ) (_ : NeZero d') (hd' : d' ∣ N),
    σ ⟨qExpand k d (jqModC k), jd_mem k N hlN hd⟩ = ⟨qExpand k d' (jqModC k), jd_mem k N hlN hd'⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem frob_comm_genPerm (hlN : ¬ ℓ ∣ N)
    (σ : modularFunctionFieldC k N ≃ₐ[k] modularFunctionFieldC k N)
    (hgp : GenPermC k N hlN σ) (x : modularFunctionFieldC k N) :
    frobeniusGeomLevel k N data hKr (σ x) = σ (frobeniusGeomLevel k N data hKr x) := by

  have haux : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
      frobeniusGeomLevel k N data hKr (σ ⟨qExpand k d (jqModC k), jd_mem k N hlN hd⟩)
        = σ (frobeniusGeomLevel k N data hKr ⟨qExpand k d (jqModC k), jd_mem k N hlN hd⟩) := by
    intro d _ hd
    obtain ⟨d', _, hd', hσ⟩ := hgp d ‹_› hd
    rw [hσ, frob_jd_eq_pow k N data hKr hlN hd', frob_jd_eq_pow k N data hKr hlN hd,
      map_pow, hσ]
  have key : (frobeniusGeomLevel k N data hKr).comp σ.toAlgHom
      = σ.toAlgHom.comp (frobeniusGeomLevel k N data hKr) := by
    have h1 : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        = ⟨qExpand k 1 (jqModC k), jd_mem k N hlN (one_dvd N)⟩ :=
      Subtype.ext (qExpand_one_apply (jqModC k)).symm
    have hN : (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)
        = ⟨qExpand k N (jqModC k), jd_mem k N hlN (dvd_refl N)⟩ :=
      Subtype.ext rfl
    refine mffC_algHom_ext k N ?_ ?_ <;>
      simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
    · rw [h1]; exact haux 1 inferInstance (one_dvd N)
    · rw [hN]; exact haux N inferInstance (dvd_refl N)
  exact DFunLike.congr_fun key x

private theorem frobOnPlaces_smul_comm
    (σ : modularFunctionFieldC k N ≃ₐ[k] modularFunctionFieldC k N)
    (hcomm : ∀ x, frobeniusGeomLevel k N data hKr (σ x) = σ (frobeniusGeomLevel k N data hKr x))
    (w : Place k (modularFunctionFieldC k N)) :
    frobOnPlacesGeomLevel k N data hKr (σ • w) = σ • frobOnPlacesGeomLevel k N data hKr w := by

  have hcomm' : ∀ x, σ⁻¹ • frobeniusGeomLevel k N data hKr x
      = frobeniusGeomLevel k N data hKr (σ⁻¹ • x) := by
    intro x
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def]
    apply σ.injective
    rw [← hcomm, show σ (σ⁻¹ x) = x from σ.apply_symm_apply x,
      show σ (σ⁻¹ (frobeniusGeomLevel k N data hKr x)) = frobeniusGeomLevel k N data hKr x from
        σ.apply_symm_apply _]
  apply Place.ext
  ext x
  rw [mem_frobOnPlacesGeomLevel_iff, Place.smul_toValuationSubring, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    mem_frobOnPlacesGeomLevel_iff, hcomm']

private theorem hOrd : ∃ j : modularFunctionFieldC k N,
    (qSeriesBar k (modularFunctionFieldC k N) j).order = -1 :=
  ⟨⟨jqModC k, jqModC_mem k N⟩, order_jqModC_def k⟩

omit [Fact ℓ.Prime] in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

private theorem exists_genPermC_smul_qInftyPlaceBar_eq (hsq : Squarefree N) (hlN : ¬ ℓ ∣ N)
    (P : Place k (modularFunctionFieldC k N))
    (hpole : P.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    ∃ σ : modularFunctionFieldC k N ≃ₐ[k] modularFunctionFieldC k N, GenPermC k N hlN σ
      ∧ P = σ • qInftyPlaceBar k (modularFunctionFieldC k N) (hOrd k N) := by
  have he := modularFunctionFieldC_eq_modularFunctionFieldFullC k ℓ N hlN
  have hNK : (N : k) ≠ 0 := fun h => hlN ((CharP.cast_eq_zero_iff k ℓ N).mp h)
  set eFC : ↥(modularFunctionFieldC k N) ≃ₐ[k] ↥(modularFunctionFieldFullC k N) :=
    IntermediateField.equivOfEq he with heFC

  have heFC_val : ∀ x, ((eFC x : modularFunctionFieldFullC k N) : LaurentSeries k)
      = (x : LaurentSeries k) := fun x => by
    rw [heFC]; exact congrArg Subtype.val (IntermediateField.equivOfEq_apply he x)
  have heFC_symm_val : ∀ x, ((eFC.symm x : modularFunctionFieldC k N) : LaurentSeries k)
      = (x : LaurentSeries k) := fun x => by
    conv_rhs => rw [← eFC.apply_symm_apply x]
    exact (heFC_val (eFC.symm x)).symm
  have hceFC : ∀ a, eFC.toRingEquiv (algebraMap k _ a) = algebraMap k _ a := eFC.commutes
  let PE := Place.congrEquiv (K := k) eFC.toRingEquiv hceFC

  have hjeq : eFC.toRingEquiv ⟨jqModC k, jqModC_mem k N⟩
      = (⟨jqModC k, jqModC_mem_full k N⟩ : modularFunctionFieldFullC k N) :=
    Subtype.ext (heFC_val _)
  have hpoleF : (PE P).ord (⟨jqModC k, jqModC_mem_full k N⟩ : modularFunctionFieldFullC k N) < 0 := by
    rw [show PE P = Place.congrRingEquiv eFC.toRingEquiv hceFC P from rfl, ← hjeq,
      Place.ord_congrRingEquiv]
    exact hpole

  have hOrdF : ∃ j : modularFunctionFieldFullC k N,
      (qSeriesBar k (modularFunctionFieldFullC k N) j).order = -1 :=
    ⟨⟨jqModC k, jqModC_mem_full k N⟩, order_jqModC_def k⟩

  obtain ⟨τ, hτgp, hτP⟩ := exists_algEquiv_smul_qInftyPlaceBar_eq_of_ord_jqModC_neg
    k N hsq hNK hOrdF (PE P) hpoleF
  refine ⟨(eFC.trans τ).trans eFC.symm, ?_, ?_⟩
  ·
    intro d _ hd
    obtain ⟨d', _, hd', hτ⟩ := hτgp d ‹_› hd
    refine ⟨d', ‹_›, hd', eFC.injective ?_⟩
    have hd_eq : eFC ⟨qExpand k d (jqModC k), jd_mem k N hlN hd⟩
        = (⟨qExpand k d (jqModC k), jqModCd_mem_full k N hd⟩ : modularFunctionFieldFullC k N) :=
      Subtype.ext (heFC_val _)
    have hd'_eq : eFC ⟨qExpand k d' (jqModC k), jd_mem k N hlN hd'⟩
        = (⟨qExpand k d' (jqModC k), jqModCd_mem_full k N hd'⟩ : modularFunctionFieldFullC k N) :=
      Subtype.ext (heFC_val _)
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, eFC.apply_symm_apply, hd_eq, hτ, hd'_eq]
  ·

    have hconj : ∀ z, eFC (((eFC.trans τ).trans eFC.symm)⁻¹ z) = τ⁻¹ (eFC z) := fun z => by
      rw [AlgEquiv.aut_inv, AlgEquiv.aut_inv, AlgEquiv.symm_trans_apply,
        AlgEquiv.symm_symm, AlgEquiv.symm_trans_apply, eFC.apply_symm_apply]
    apply PE.injective
    rw [hτP]
    apply Place.ext
    refine SetLike.ext fun x => ?_
    rw [show (PE (((eFC.trans τ).trans eFC.symm)
            • qInftyPlaceBar k (modularFunctionFieldC k N) (hOrd k N))).toValuationSubring
          = (((eFC.trans τ).trans eFC.symm)
              • qInftyPlaceBar k (modularFunctionFieldC k N)
                  (hOrd k N)).toValuationSubring.comap
            (eFC.toRingEquiv.symm : ↥(modularFunctionFieldFullC k N) →+* _) from rfl,
      Place.smul_toValuationSubring, Place.smul_toValuationSubring,
      ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      qInftyPlaceBar_toValuationSubring, qInftyPlaceBar_toValuationSubring,
      mem_qIntegersBar_iff, mem_qIntegersBar_iff]

    rw [AlgEquiv.smul_def, AlgEquiv.smul_def]
    have hrepl : ((((eFC.trans τ).trans eFC.symm)⁻¹ (eFC.toRingEquiv.symm x)
          : modularFunctionFieldC k N) : LaurentSeries k)
        = ((τ⁻¹ x : modularFunctionFieldFullC k N) : LaurentSeries k) := by
      rw [← heFC_val (((eFC.trans τ).trans eFC.symm)⁻¹ (eFC.toRingEquiv.symm x)),
        hconj (eFC.toRingEquiv.symm x),
        show eFC (eFC.toRingEquiv.symm x) = x from eFC.apply_symm_apply x]
    show 0 ≤ ((((eFC.trans τ).trans eFC.symm)⁻¹ (eFC.toRingEquiv.symm x)
          : modularFunctionFieldC k N) : LaurentSeries k).order
        ↔ 0 ≤ ((τ⁻¹ x : modularFunctionFieldFullC k N) : LaurentSeries k).order
    rw [hrepl]

end CuspFrobeniusFixedAux

open CuspFrobeniusFixedAux in

theorem solution
    (k : Type*) [Field k] (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hsq : Squarefree N) (hlN : ¬ ℓ ∣ N)
    (P : Place k (modularFunctionFieldC k N))
    (hpole : P.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    frobOnPlacesGeomLevel k N data hKr P = P := by
  obtain ⟨σ, hgp, hP⟩ :=
    exists_genPermC_smul_qInftyPlaceBar_eq k N (ℓ := ℓ) hsq hlN P hpole
  rw [hP, frobOnPlaces_smul_comm k N data hKr σ (frob_comm_genPerm k N data hKr hlN σ hgp),
    ModularCurve.frobOnPlacesGeomLevel_qInftyPlaceBar k N data hKr (hOrd k N)]

end

end S_ModularCurve_CharPModel_frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg
end P2MW
export P2MW.S_ModularCurve_CharPModel_frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg (solution)
