-- Prove2me | solution 1 for ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/45482822-65a4-50b8-9f2a-24d6ae37fb30

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_MapPoint
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_ZeroComponentReduction
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
import Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_TatePoint_fullKernelDiscAt_univ
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
import Theorems.Thm_ModularCurve_monic_fibrePoly
import Theorems.Thm_ModularCurve_natDegree_fibrePoly
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq
import Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo
import Theorems.Thm_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j
import Theorems.Thm_WeierstrassCurve_finite_stabilizer_variableChange
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_eq_veluQuotient_of_odd
import Theorems.Thm_WeierstrassCurve_map_veluQuotientOfSums
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ
p2m_attr_erase "instance" "ModularCurve.B3.instIsElliptic_goodModel ModularCurve.Gamma0Pair.isElliptic ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"

set_option autoImplicit false

noncomputable section

section SigmaSpinePart

universe u

p2m_open "AlgebraicCurve ModularCurve~map_vcYInv~map_vcXInv~CycSub P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine"
open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace SigmaSpine
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

private abbrev genCurve (K : Type u) [Field K] {M : Type u} [Field M] [Algebra K M] [DecidableEq M] (t : M) :
    WeierstrassCurve K⟮t⟯ :=
  WeierstrassCurve.ofJ (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)

section Contracts

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
  (N : ℕ) (E₀ : WeierstrassCurve K) [E₀.IsElliptic]

private def FrobContract (M : Type u) [Field M] [Algebra K M] (t : M) : Prop :=
  ∀ W₀ : Place K M, 0 < W₀.ord (t - algebraMap K M E₀.j) →
    ∃ frM : SemilinearAut K M,
      (∀ a : K, frM • (algebraMap K M a) = algebraMap K M (a ^ q)) ∧ frM • t = t ∧ frM • W₀ = W₀

private def DescentContract : Prop :=
  ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
    (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M),
    Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
    (∃ m : ℕ, (m : K) ≠ 0 ∧ (q = 2 → m = 3) ∧
      Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // m • P = 0} = m ^ 2 ∧
      ∀ A : ValuationSubring M, IsUnit ((m : ℕ) : A) → t ∈ A →
        ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
          κ • (genCurve K t).baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
          ∀ (σ : M ≃ₐ[K⟮t⟯] M) (hσ : σ ∈ A.decompositionSubgroup K⟮t⟯),
            (⟨σ, hσ⟩ : A.decompositionSubgroup K⟮t⟯) ∈ A.inertiaSubgroup K⟮t⟯ →
            (∀ (n : ℕ), (n : K) ≠ 0 → ∀ P : ((genCurve K t).baseChange M).toAffine.Point, n • P = 0 →
              WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P = P) →
            (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
              g.map (IsLocalRing.residue A) = 1) →
            σ = 1) ∧
    FrobContract K q E₀ M t

end Contracts

section Furniture

private theorem map_ofJNe0Or1728 {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) (j : R) :
    (ofJNe0Or1728 j).map f = ofJNe0Or1728 (f j) := by
  ext <;> simp [ofJNe0Or1728, map_ofNat]

variable {K M : Type u} [Field K] [Field M] [Algebra K M] [DecidableEq M] {t : M}

private theorem genCurve_eq (ht : Transcendental K t) :
    genCurve K t = ofJNe0Or1728 (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯) := by
  apply ofJ_ne_0_ne_1728
  · intro h
    have h' : t = 0 := congrArg Subtype.val h
    exact ht (h' ▸ isAlgebraic_zero)
  · intro h
    have h' : t = (1728 : M) := congrArg Subtype.val h
    apply ht
    rw [h', ← map_ofNat (algebraMap K M) 1728]
    exact isAlgebraic_algebraMap _

private theorem baseChange_genCurve (ht : Transcendental K t) :
    (genCurve K t).baseChange M = ofJNe0Or1728 t := by
  rw [genCurve_eq ht, WeierstrassCurve.baseChange, map_ofJNe0Or1728]; rfl

private theorem map_baseChange_genCurve (ht : Transcendental K t) (ψ : M →+* M) (hψ : ψ t = t) :
    ((genCurve K t).baseChange M).map ψ = (genCurve K t).baseChange M := by
  rw [baseChange_genCurve ht, map_ofJNe0Or1728, hψ]

private def _root_.ModularCurve.SigmaSpine.castPt {k : Type u} [Field k] {V V' : WeierstrassCurve k} (h : V' = V) :
    V'.toAffine.Point → V.toAffine.Point := by
  subst h; exact id

p2m_export "ModularCurve.SigmaSpine" "castPt"
private def castAddHom {k : Type u} [Field k] [DecidableEq k] {V V' : WeierstrassCurve k} (h : V' = V) :
    V'.toAffine.Point →+ V.toAffine.Point := by
  subst h; exact AddMonoidHom.id _

private noncomputable def vcInvAddHom {k : Type u} [Field k] [DecidableEq k] (C : VariableChange k)
    (V : WeierstrassCurve k) : V.toAffine.Point →+ (C • V).toAffine.Point :=
  AddMonoidHom.mk' (Point.vcInvFun C V.toAffine) (Point.vcInvFun_add C V.toAffine)

private noncomputable def semilinearPt (ht : Transcendental K t) (σ : SemilinearAut K M) (hσt : σ • t = t)
    (P : ((genCurve K t).baseChange M).toAffine.Point) : ((genCurve K t).baseChange M).toAffine.Point :=
  castPt (map_baseChange_genCurve ht (SemilinearAut.toRingAut σ : M →+* M) hσt)
    (mapPoint (SemilinearAut.toRingAut σ : M →+* M) P)

variable (W₀ : Place K M)

private noncomputable def stabRingEquiv (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) :
    W₀.toValuationSubring ≃+* W₀.toValuationSubring where
  toFun x := ⟨σ • (x : M), by
    have h := ValuationSubring.smul_mem_pointwise_smul σ (x : M) W₀.toValuationSubring x.2
    rwa [← SemilinearAut.smul_toValuationSubring, hσ] at h⟩
  invFun x := ⟨σ⁻¹ • (x : M), by
    have hinv : σ⁻¹ • W₀ = W₀ := by rw [inv_smul_eq_iff, hσ]
    have h := ValuationSubring.smul_mem_pointwise_smul σ⁻¹ (x : M) W₀.toValuationSubring x.2
    rwa [← SemilinearAut.smul_toValuationSubring, hinv] at h⟩
  left_inv x := Subtype.ext (inv_smul_smul σ (x : M))
  right_inv x := Subtype.ext (smul_inv_smul σ (x : M))
  map_mul' x y := Subtype.ext (smul_mul' σ (x : M) (y : M))
  map_add' x y := Subtype.ext (smul_add σ (x : M) (y : M))

private noncomputable def residueAut (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) :
    IsLocalRing.ResidueField W₀.toValuationSubring ≃+* IsLocalRing.ResidueField W₀.toValuationSubring :=
  IsLocalRing.ResidueField.mapEquiv (stabRingEquiv W₀ σ hσ)

omit [DecidableEq M] in

private theorem reducedΔ_ne_zero {W : WeierstrassCurve W₀.toValuationSubring} (hΔ : IsUnit W.Δ) :
    (W.map (IsLocalRing.residue W₀.toValuationSubring)).Δ ≠ 0 := by
  rw [WeierstrassCurve.map_Δ]; exact (hΔ.map _).ne_zero

private noncomputable def reduceAlongHom [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)]
    (W : WeierstrassCurve W₀.toValuationSubring) (κ : VariableChange M)
    (hκ : κ • (genCurve K t).baseChange M = W.map W₀.toValuationSubring.subtype) (hΔ : IsUnit W.Δ) :
    ((genCurve K t).baseChange M).toAffine.Point →+
      (W.map (IsLocalRing.residue W₀.toValuationSubring)).toAffine.Point :=
  (WeierstrassCurve.reduceHom (reducedΔ_ne_zero W₀ hΔ)).comp
    ((castAddHom hκ).comp (vcInvAddHom κ ((genCurve K t).baseChange M)))

end Furniture

section Contracts

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
  (N : ℕ) (E₀ : WeierstrassCurve K) [E₀.IsElliptic]

private def ReductionContract : Prop :=
  ∀ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M) (ht : Transcendental K t)
    (_ : FiniteDimensional K⟮t⟯ M)
    (W₀ : Place K M) (_ : 0 < W₀.ord (t - algebraMap K M E₀.j))
    (_ : DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring))
    (W : WeierstrassCurve W₀.toValuationSubring) (κ : VariableChange M)
    (hκ : κ • (genCurve K t).baseChange M = W.map W₀.toValuationSubring.subtype) (hΔ : IsUnit W.Δ),
    (∀ (n : ℕ) (P : ((genCurve K t).baseChange M).toAffine.Point),
        (n : IsLocalRing.ResidueField W₀.toValuationSubring) ≠ 0 → n • P = 0 →
          reduceAlongHom W₀ W κ hκ hΔ P = 0 → P = 0) ∧
    ∃ g : SemilinearAut K M → VariableChange W₀.toValuationSubring,
      (∀ (σ : SemilinearAut K M) (hσt : σ • t = t) (hσ : σ • W₀ = W₀),
        (g σ).map W₀.toValuationSubring.subtype = κ * (κ.map (SemilinearAut.toRingAut σ : M →+* M))⁻¹ ∧
        (g σ).map (IsLocalRing.residue W₀.toValuationSubring) •
            (W.map (IsLocalRing.residue W₀.toValuationSubring)).map (residueAut W₀ σ hσ).toRingHom =
          W.map (IsLocalRing.residue W₀.toValuationSubring) ∧
        ∀ P : ((genCurve K t).baseChange M).toAffine.Point,
          HEq (Point.vcInvFun ((g σ).map (IsLocalRing.residue W₀.toValuationSubring))
                ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map
                  (residueAut W₀ σ hσ).toRingHom).toAffine
                (mapPoint (residueAut W₀ σ hσ).toRingHom (reduceAlongHom W₀ W κ hκ hΔ P)))
            (reduceAlongHom W₀ W κ hκ hΔ (semilinearPt ht σ hσt P))) ∧
      (∀ (σ τ : SemilinearAut K M) (_ : σ • t = t) (hσ : σ • W₀ = W₀) (_ : τ • t = t) (_ : τ • W₀ = W₀),
        (g (σ * τ)).map (IsLocalRing.residue W₀.toValuationSubring) =
          (g σ).map (IsLocalRing.residue W₀.toValuationSubring) *
            ((g τ).map (IsLocalRing.residue W₀.toValuationSubring)).map (residueAut W₀ σ hσ).toRingHom) ∧
      (∀ (σ : M ≃ₐ[K⟮t⟯] M) (hσ : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀)
          (r : IsLocalRing.ResidueField W₀.toValuationSubring),
        residueAut W₀ (SemilinearAut.ofAlgAut (σ.restrictScalars K)) hσ r = r)

private def DictionaryContract (_hN : (N : K) ≠ 0) : Prop :=
  ∀ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
    (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M)
    (_ : Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // N • P = 0} = N ^ 2)
    (frM : SemilinearAut K M) (_ : ∀ a : K, frM • (algebraMap K M a) = algebraMap K M (a ^ q))
    (_ : frM • t = t)
    (frE : ((genCurve K t).baseChange M).toAffine.Point →+ ((genCurve K t).baseChange M).toAffine.Point)
    (_ : ∀ (x y : M) (h : ((genCurve K t).baseChange M).toAffine.Nonsingular x y),
      ∃ h', frE (.some x y h) = .some (frM • x) (frM • y) h'),
    ∃ Φ : {H : AddSubgroup ((genCurve K t).baseChange M).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
          {ψ : modularFunctionFieldFullC K N →ₐ[K] M // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t},
      (∀ (σ : M ≃ₐ[K⟮t⟯] M) (H H' : {H : AddSubgroup ((genCurve K t).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M)) →
          ((Φ H').1 : modularFunctionFieldFullC K N →ₐ[K] M) =
            ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp (Φ H).1) ∧
      (∀ (H H' : {H : AddSubgroup ((genCurve K t).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map frE →
          ∀ (d : ℕ) [NeZero d] (hd : d ∣ N),
            (Φ H').1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ =
              frM • ((Φ H).1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩))

end Contracts

section ResidueOverlap
open IsLocalRing

noncomputable section

section Residue

variable {K : Type*} [Field K] [IsAlgClosed K] {M : Type*} [Field M] [Algebra K M]
  (W₀ : Place K M)

private lemma bijective_algebraMap_residueField (hdeg : W₀.deg ≠ 0) :
    Function.Bijective (algebraMap K W₀.ResidueField) := by
  haveI : Module.Finite K W₀.ResidueField :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  haveI : Algebra.IsIntegral K W₀.ResidueField := Algebra.IsIntegral.of_finite K _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

private def resK (hdeg : W₀.deg ≠ 0) : W₀.ResidueField ≃+* K :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).symm

private lemma resK_algebraMap (hdeg : W₀.deg ≠ 0) (c : K) :
    resK W₀ hdeg (algebraMap K W₀.ResidueField c) = c :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).symm_apply_apply c

private lemma algebraMap_resK (hdeg : W₀.deg ≠ 0) (r : W₀.ResidueField) :
    algebraMap K W₀.ResidueField (resK W₀ hdeg r) = r :=
  (RingEquiv.ofBijective (algebraMap K W₀.ResidueField)
    (bijective_algebraMap_residueField W₀ hdeg)).apply_symm_apply r

private def toK (hdeg : W₀.deg ≠ 0) : W₀.toValuationSubring →+* K :=
  (resK W₀ hdeg).toRingHom.comp (residue W₀.toValuationSubring)

private lemma toK_apply (hdeg : W₀.deg ≠ 0) (a : W₀.toValuationSubring) :
    toK W₀ hdeg a = resK W₀ hdeg (residue _ a) := rfl

private lemma toK_algebraMap (hdeg : W₀.deg ≠ 0) (c : K) :
    toK W₀ hdeg (algebraMap K W₀.toValuationSubring c) = c := by
  rw [toK_apply]
  exact resK_algebraMap W₀ hdeg c

private lemma toK_eq_toK_of_sub_mem (hdeg : W₀.deg ≠ 0) {a b : W₀.toValuationSubring}
    (h : a - b ∈ IsLocalRing.maximalIdeal W₀.toValuationSubring) : toK W₀ hdeg a = toK W₀ hdeg b := by
  rw [toK_apply, toK_apply]
  congr 1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact h

omit [IsAlgClosed K] in

private lemma _root_.ModularCurve.SigmaSpine.mem_maximalIdeal_of_ord_pos {f : M} (hf : 0 < W₀.ord f) :
    ∃ hfA : f ∈ W₀.toValuationSubring, (⟨f, hfA⟩ : W₀.toValuationSubring) ∈
      IsLocalRing.maximalIdeal W₀.toValuationSubring := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W₀.toValuationSubring
  obtain ⟨u, hu⟩ := W₀.exists_unit_mul_zpow hf0 hπ
  have hn : W₀.ord f = (((W₀.ord f).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hf.le).symm
  have hn0 : (W₀.ord f).toNat ≠ 0 := by omega
  set a : W₀.toValuationSubring := (u : W₀.toValuationSubring) * π ^ (W₀.ord f).toNat with ha
  have hfa : f = (a : M) := by
    rw [hu, hn, zpow_natCast, ha]; push_cast; rfl
  refine ⟨hfa ▸ a.2, ?_⟩
  have : (⟨f, hfa ▸ a.2⟩ : W₀.toValuationSubring) = a := Subtype.ext hfa
  rw [this, ha]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (hπ.maximalIdeal_eq ▸
    Ideal.mem_span_singleton_self π) _ (Nat.pos_of_ne_zero hn0))

p2m_export "ModularCurve.SigmaSpine" "mem_maximalIdeal_of_ord_pos"
omit [IsAlgClosed K] in
private lemma _root_.ModularCurve.SigmaSpine.ord_eq_zero_of_isUnit {a : W₀.toValuationSubring} (ha : IsUnit a) : W₀.ord (a : M) = 0 :=
  W₀.ord_coe_unit ha.unit

p2m_export "ModularCurve.SigmaSpine" "ord_eq_zero_of_isUnit"
private lemma mem_inertia_of_mem_decomposition (hdeg : W₀.deg ≠ 0) {E : Type*} [Field E] [Algebra K E]
    [Algebra E M] [IsScalarTower K E M] {σ : M ≃ₐ[E] M}
    (hσ : σ ∈ W₀.toValuationSubring.decompositionSubgroup E) :
    (⟨σ, hσ⟩ : W₀.toValuationSubring.decompositionSubgroup E) ∈
      W₀.toValuationSubring.inertiaSubgroup E := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  show (⟨σ, hσ⟩ : W₀.toValuationSubring.decompositionSubgroup E) • r = r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hc⟩ := (bijective_algebraMap_residueField W₀ hdeg).2 (residue _ a)
  have hc' : residue _ a = residue _ (algebraMap K W₀.toValuationSubring c) := hc.symm
  rw [hc', ← IsLocalRing.ResidueField.residue_smul]
  congr 1
  apply Subtype.ext
  show σ (algebraMap K M c) = algebraMap K M c
  rw [IsScalarTower.algebraMap_apply K E M, σ.commutes]

end Residue

end

end ResidueOverlap

section CoordStabOverlap
open IsLocalRing
open scoped Pointwise

section Coord

variable {K : Type*} [Field K]

private lemma _root_.ModularCurve.SigmaSpine.vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

p2m_export "ModularCurve.SigmaSpine" "vcXInv_mul"
private lemma _root_.ModularCurve.SigmaSpine.vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

p2m_export "ModularCurve.SigmaSpine" "vcYInv_mul"
@[scoped simp] private lemma vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  simp [vcXInv, VariableChange.one_def]

@[scoped simp] private lemma vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  simp [vcYInv, VariableChange.one_def]

variable {K' : Type*} [Field K'] (φ : K →+* K')

private lemma map_vcXInv (C : VariableChange K) (x : K) :
    φ (vcXInv C x) = vcXInv (C.map φ) (φ x) := by
  simp only [vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

private lemma map_vcYInv (C : VariableChange K) (x y : K) :
    φ (vcYInv C x y) = vcYInv (C.map φ) (φ x) (φ y) := by
  simp only [vcYInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

private def _root_.ModularCurve.SigmaSpine.negC (W : WeierstrassCurve K) : VariableChange K := ⟨-1, 0, -W.a₁, -W.a₃⟩

p2m_export "ModularCurve.SigmaSpine" "negC"
private lemma _root_.ModularCurve.SigmaSpine.negC_smul (W : WeierstrassCurve K) : negC W • W = W := by
  ext <;> simp [negC, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆] <;> ring

p2m_export "ModularCurve.SigmaSpine" "negC_smul"
private lemma _root_.ModularCurve.SigmaSpine.negC_ne_one (W : WeierstrassCurve K) [W.IsElliptic] : negC W ≠ 1 := by
  intro h
  have hu : ((-1 : Kˣ) : K) = 1 := by
    have := congrArg (fun C : VariableChange K => (C.u : K)) h
    first | simpa [negC] using this | simpa [negC, WeierstrassCurve.VariableChange.one_u] using this | (simp [negC] at this; exact this)
  have hs : -W.a₁ = 0 := by
    have := congrArg VariableChange.s h; simpa [negC, VariableChange.one_def] using this
  have ht : -W.a₃ = 0 := by
    have := congrArg VariableChange.t h; simpa [negC, VariableChange.one_def] using this
  have h2 : (2 : K) = 0 := by
    have : (-1 : K) = 1 := by simpa using hu
    linear_combination -this
  have ha₁ : W.a₁ = 0 := by linear_combination -hs
  have ha₃ : W.a₃ = 0 := by linear_combination -ht
  apply W.isUnit_Δ.ne_zero
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, ha₁, ha₃]
  linear_combination (-8 * W.a₂ ^ 2 * (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) - 32 * W.a₄ ^ 3
    - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2

p2m_export "ModularCurve.SigmaSpine" "negC_ne_one"
private lemma _root_.ModularCurve.SigmaSpine.vcXInv_negC (W : WeierstrassCurve K) (x : K) : vcXInv (negC W) x = x := by
  simp [vcXInv, negC]

p2m_export "ModularCurve.SigmaSpine" "vcXInv_negC"
private lemma _root_.ModularCurve.SigmaSpine.vcYInv_negC (W : WeierstrassCurve K) (x y : K) :
    vcYInv (negC W) x y = W.toAffine.negY x y := by
  simp only [vcYInv, negC, Affine.negY, inv_neg, inv_one, Units.val_neg, Units.val_one]
  simp; ring

p2m_export "ModularCurve.SigmaSpine" "vcYInv_negC"
end Coord

section Stab

variable {K : Type*} [Field K] {M : Type*} [Field M] [Algebra K M] {E : Type*} [Field E]
  [Algebra K E] [Algebra E M] [IsScalarTower K E M]

private lemma _root_.ModularCurve.SigmaSpine.smul_place_eq_iff (σ : M ≃ₐ[E] M) (W₀ : Place K M) :
    SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ↔
      σ ∈ W₀.toValuationSubring.decompositionSubgroup E := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff, Place.ext_iff,
    SemilinearAut.smul_toValuationSubring]
  have key : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀.toValuationSubring =
      σ • W₀.toValuationSubring := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, SemilinearAut.ofAlgAut_smul]
    rfl
  rw [key]

p2m_export "ModularCurve.SigmaSpine" "smul_place_eq_iff"
private lemma _root_.ModularCurve.SigmaSpine.isIntegral_of_apply_gen_eq (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : K⟮t⟯ →ₐ[K] M)
    (hψ : ψ ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ = t) : ψ.toRingHom.IsIntegral := by
  have hψ' : ψ = IntermediateField.val K⟮t⟯ := by
    apply IntermediateField.adjoin_algHom_ext K
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hψ
  rw [hψ']
  intro x
  exact Algebra.IsIntegral.isIntegral (R := K⟮t⟯) x

p2m_export "ModularCurve.SigmaSpine" "isIntegral_of_apply_gen_eq"
end Stab

section PointLemmasOverlap
open WeierstrassCurve.Affine.Point

variable {M : Type*} [Field M]

private lemma VariableChange.map_mul' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (C C' : VariableChange R) : (C * C').map φ = C.map φ * C'.map φ :=
  (VariableChange.mapHom φ).map_mul C C'

private lemma VariableChange.map_inv' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (C : VariableChange R) : C⁻¹.map φ = (C.map φ)⁻¹ :=
  (VariableChange.mapHom φ).map_inv C

private lemma j_congr {R : Type*} [CommRing R] {V₁ V₂ : WeierstrassCurve R} [V₁.IsElliptic] [V₂.IsElliptic]
    (h : V₁ = V₂) : V₁.j = V₂.j := by subst h; rfl

end PointLemmasOverlap

end CoordStabOverlap

section BodyFurniture

section CastOverlap

variable {k : Type u} [Field k]

private theorem _root_.ModularCurve.SigmaSpine.castPt_zero {V V' : WeierstrassCurve k} (h : V' = V) : castPt h (0 : V'.toAffine.Point) = 0 := by
  subst h; rfl

p2m_export "ModularCurve.SigmaSpine" "castPt_zero"
private theorem _root_.ModularCurve.SigmaSpine.castPt_some {V V' : WeierstrassCurve k} (h : V' = V) {x y : k} (hns : V'.toAffine.Nonsingular x y) :
    castPt h (.some x y hns) = .some x y (h ▸ hns) := by
  subst h; rfl

p2m_export "ModularCurve.SigmaSpine" "castPt_some"
private theorem _root_.ModularCurve.SigmaSpine.eq_castPt_of_heq {V V' : WeierstrassCurve k} (h : V' = V) {P : V'.toAffine.Point} {Q : V.toAffine.Point}
    (hPQ : HEq P Q) : Q = castPt h P := by
  subst h; exact (eq_of_heq hPQ).symm

p2m_export "ModularCurve.SigmaSpine" "eq_castPt_of_heq"
private theorem _root_.ModularCurve.SigmaSpine.heq_some_of_eq {V V' : WeierstrassCurve k} (hV : V' = V) {x₁ x₂ y₁ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h₁ : V'.toAffine.Nonsingular x₁ y₁) (h₂ : V.toAffine.Nonsingular x₂ y₂) :
    HEq (Point.some x₁ y₁ h₁ : V'.toAffine.Point) (Point.some x₂ y₂ h₂ : V.toAffine.Point) := by
  subst hV; subst hx; subst hy; rfl

p2m_export "ModularCurve.SigmaSpine" "heq_some_of_eq"
private theorem _root_.ModularCurve.SigmaSpine.heq_zero_of_eq {V V' : WeierstrassCurve k} (hV : V' = V) :
    HEq (0 : V'.toAffine.Point) (0 : V.toAffine.Point) := by
  subst hV; rfl

p2m_export "ModularCurve.SigmaSpine" "heq_zero_of_eq"
private theorem castAddHom_apply [DecidableEq k] {V V' : WeierstrassCurve k} (h : V' = V) (P : V'.toAffine.Point) :
    castAddHom h P = castPt h P := by
  subst h; rfl

private theorem _root_.ModularCurve.SigmaSpine.vcInvFun_some [DecidableEq k] (C : VariableChange k) (V : WeierstrassCurve.Affine k) {x y : k}
    (h : V.Nonsingular x y) :
    Point.vcInvFun C V (.some x y h) = .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

p2m_export "ModularCurve.SigmaSpine" "vcInvFun_some"
end CastOverlap

variable {K M : Type u} [Field K] [Field M] [Algebra K M] [DecidableEq M] {t : M}

private theorem semilinearPt_ofAlgAut (ht : Transcendental K t) (σ : M ≃ₐ[K⟮t⟯] M)
    (hσt : SemilinearAut.ofAlgAut (σ.restrictScalars K) • t = t) (P : ((genCurve K t).baseChange M).toAffine.Point) :
    semilinearPt ht (SemilinearAut.ofAlgAut (σ.restrictScalars K)) hσt P =
      WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P := by
  rcases P with _ | ⟨x, y, h⟩
  · show castPt _ (mapPoint _ 0) = _
    rw [mapPoint_zero, castPt_zero]
    rfl
  · show castPt _ (mapPoint _ (.some x y h)) = _
    rw [mapPoint_some, castPt_some, WeierstrassCurve.Affine.Point.map_some]
    rfl

omit [DecidableEq M] in

private theorem ofAlgAut_smul_t (σ : M ≃ₐ[K⟮t⟯] M) : SemilinearAut.ofAlgAut (σ.restrictScalars K) • t = t := by
  rw [SemilinearAut.ofAlgAut_smul]
  exact σ.commutes (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)

variable (W₀ : Place K M) [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)]
  (W : WeierstrassCurve W₀.toValuationSubring) (κ : VariableChange M)
  (hκ : κ • (genCurve K t).baseChange M = W.map W₀.toValuationSubring.subtype) (hΔ : IsUnit W.Δ)

private theorem reduceAlongHom_semilinearPt_some (ht : Transcendental K t) (σ : SemilinearAut K M) (hσt : σ • t = t)
    (hσ : σ • W₀ = W₀) (gb : VariableChange (IsLocalRing.ResidueField W₀.toValuationSubring))
    (hfix : gb • (W.map (IsLocalRing.residue W₀.toValuationSubring)).map (residueAut W₀ σ hσ).toRingHom =
      W.map (IsLocalRing.residue W₀.toValuationSubring))
    (hheq : ∀ P : ((genCurve K t).baseChange M).toAffine.Point,
      HEq (Point.vcInvFun gb ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map
              (residueAut W₀ σ hσ).toRingHom).toAffine
            (mapPoint (residueAut W₀ σ hσ).toRingHom (reduceAlongHom W₀ W κ hκ hΔ P)))
        (reduceAlongHom W₀ W κ hκ hΔ (semilinearPt ht σ hσt P)))
    (P : ((genCurve K t).baseChange M).toAffine.Point) {x y : IsLocalRing.ResidueField W₀.toValuationSubring}
    (h : (W.map (IsLocalRing.residue W₀.toValuationSubring)).toAffine.Nonsingular x y)
    (hP : reduceAlongHom W₀ W κ hκ hΔ P = .some x y h) :
    ∃ h', reduceAlongHom W₀ W κ hκ hΔ (semilinearPt ht σ hσt P) =
      .some (vcXInv gb (residueAut W₀ σ hσ x)) (vcYInv gb (residueAut W₀ σ hσ x) (residueAut W₀ σ hσ y)) h' := by
  have hE := eq_castPt_of_heq hfix (hheq P)
  rw [hE, hP, mapPoint_some, vcInvFun_some, castPt_some]
  exact ⟨_, rfl⟩

private theorem reduceAlongHom_semilinearPt_zero (ht : Transcendental K t) (σ : SemilinearAut K M) (hσt : σ • t = t)
    (hσ : σ • W₀ = W₀) (gb : VariableChange (IsLocalRing.ResidueField W₀.toValuationSubring))
    (hfix : gb • (W.map (IsLocalRing.residue W₀.toValuationSubring)).map (residueAut W₀ σ hσ).toRingHom =
      W.map (IsLocalRing.residue W₀.toValuationSubring))
    (hheq : ∀ P : ((genCurve K t).baseChange M).toAffine.Point,
      HEq (Point.vcInvFun gb ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map
              (residueAut W₀ σ hσ).toRingHom).toAffine
            (mapPoint (residueAut W₀ σ hσ).toRingHom (reduceAlongHom W₀ W κ hκ hΔ P)))
        (reduceAlongHom W₀ W κ hκ hΔ (semilinearPt ht σ hσt P)))
    (P : ((genCurve K t).baseChange M).toAffine.Point) (hP : reduceAlongHom W₀ W κ hκ hΔ P = 0) :
    reduceAlongHom W₀ W κ hκ hΔ (semilinearPt ht σ hσt P) = 0 := by
  have hE := eq_castPt_of_heq hfix (hheq P)
  rw [hE, hP, mapPoint_zero, Point.vcInvFun_zero, castPt_zero]

end BodyFurniture

section Cast

variable {k : Type u} [Field k]

private lemma castPt_rfl {V : WeierstrassCurve k} (P : V.toAffine.Point) : castPt rfl P = P := rfl

variable [DecidableEq k]

private lemma castPt_add {V V' : WeierstrassCurve k} (h : V' = V) (P Q : V'.toAffine.Point) :
    castPt h (P + Q) = castPt h P + castPt h Q := by
  subst h; rfl

private lemma _root_.ModularCurve.SigmaSpine.castPt_nsmul {V V' : WeierstrassCurve k} (h : V' = V) (n : ℕ) (P : V'.toAffine.Point) :
    castPt h (n • P) = n • castPt h P := by
  subst h; rfl

p2m_export "ModularCurve.SigmaSpine" "castPt_nsmul"
end Cast

section PlaceOver

variable (K : Type u) [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in

private lemma adjoin_toSubring_eq_closure {M : Type u} [Field M] [Algebra K M] (t : M) :
    (Algebra.adjoin K ({t} : Set M)).toSubring =
      Subring.closure (Set.range ((algebraMap K M).comp (⊤ : ValuationSubring K).subtype) ∪ {t}) := by
  have hr : Set.range ((algebraMap K M).comp (⊤ : ValuationSubring K).subtype) =
      Set.range (algebraMap K M) := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨⟨a, ValuationSubring.mem_top a⟩, rfl⟩
  rw [hr]
  ext x
  rw [Subalgebra.mem_toSubring, Algebra.mem_adjoin_iff]

private theorem exists_place_over (M : Type u) [Field M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M] (j₀ : K) :
    ∃ W₀ : Place K M, 0 < W₀.ord (t - algebraMap K M j₀) := by
  have htr : Transcendental K t := ht
  let A : ValuationSubring K := ⊤
  let B : Subring M := (Algebra.adjoin K ({t} : Set M)).toSubring
  have hconst : ∀ a : A, algebraMap K M a ∈ B := fun a =>
    (Algebra.adjoin K ({t} : Set M)).algebraMap_mem a
  have htB : t ∈ B := Algebra.self_mem_adjoin_singleton K t
  have hint : ∀ b : B, IsIntegral
      (Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t})) (b : M) := by
    intro b
    have hb : (b : M) ∈ Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t}) := by
      rw [← adjoin_toSubring_eq_closure]; exact b.2
    exact isIntegral_algebraMap (A := M)
      (x := (⟨(b : M), hb⟩ : Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t})))

  let g : B := ⟨t, htB⟩ - ⟨algebraMap K M j₀, hconst ⟨j₀, ValuationSubring.mem_top j₀⟩⟩
  have hg : ¬ IsUnit g := by
    intro hu
    let e := Polynomial.algEquivOfTranscendental K t htr
    have hge : e (Polynomial.X - Polynomial.C j₀) = g := by
      apply Subtype.ext
      simp [e, g, Polynomial.algEquivOfTranscendental_apply]
    have : IsUnit (Polynomial.X - Polynomial.C j₀ : Polynomial K) := by
      rw [← hge] at hu
      exact (MulEquiv.isUnit_map e).mp hu
    exact Polynomial.not_isUnit_X_sub_C j₀ this
  obtain ⟨𝔮, h𝔮max, hg𝔮⟩ := Ideal.exists_le_maximal (Ideal.span {g}) (Ideal.span_singleton_ne_top hg)
  haveI : 𝔮.IsPrime := h𝔮max.isPrime
  have h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A →
      (⟨algebraMap K M a, hconst a⟩ : B) ∈ 𝔮 := by
    intro a ha
    have ha0 : a = 0 := by
      by_contra hne
      apply (IsLocalRing.mem_maximalIdeal _).mp ha
      have hne' : (a : K) ≠ 0 := fun h => hne (Subtype.ext h)
      exact ⟨⟨a, ⟨(a : K)⁻¹, ValuationSubring.mem_top _⟩,
        Subtype.ext (mul_inv_cancel₀ hne'), Subtype.ext (inv_mul_cancel₀ hne')⟩, rfl⟩
    have : (⟨algebraMap K M a, hconst a⟩ : B) = 0 := by
      apply Subtype.ext; simp [ha0]
    rw [this]; exact 𝔮.zero_mem
  have hja : (⟨t, htB⟩ : B) - ⟨algebraMap K M ((⟨j₀, ValuationSubring.mem_top j₀⟩ : A) : K),
      hconst _⟩ ∈ 𝔮 := hg𝔮 (Ideal.mem_span_singleton_self g)
  obtain ⟨w, hw, -⟩ := AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring A htr hconst htB
    hint 𝔮 h𝔮A ⟨j₀, ValuationSubring.mem_top j₀⟩ hja
  exact ⟨w, hw⟩

end PlaceOver

namespace RealisationAux

open WeierstrassCurve.Affine.Point IsLocalRing ValuationSubring
open scoped Pointwise

section Cast

variable {R : Type u} [CommRing R]

private def _root_.ModularCurve.SigmaSpine.RealisationAux.castPt {V₁ V₂ : Affine R} (h : V₁ = V₂) : V₁.Point → V₂.Point
  | .zero => .zero
  | .some x y hns => .some x y (h ▸ hns)

p2m_export "ModularCurve.SigmaSpine.RealisationAux" "castPt"
@[scoped simp] private lemma castPt_zero {V₁ V₂ : Affine R} (h : V₁ = V₂) :
    castPt h (0 : V₁.Point) = 0 := rfl

private lemma castPt_some {V₁ V₂ : Affine R} (h : V₁ = V₂) {x y : R} (hns : V₁.Nonsingular x y) :
    castPt h (.some x y hns) = .some x y (h ▸ hns) := rfl

private lemma castPt_rfl {V : Affine R} (P : V.Point) : castPt rfl P = P := by
  cases P <;> rfl

private lemma eq_castPt_of_heq {V₁ V₂ : Affine R} (h : V₁ = V₂) {P : V₁.Point} {Q : V₂.Point}
    (hPQ : HEq P Q) : Q = castPt h P := by
  subst h; rw [castPt_rfl]; exact (eq_of_heq hPQ).symm

private lemma heq_some_of_eq {V₁ V₂ : Affine R} (hV : V₁ = V₂) {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V₁.Nonsingular x₁ y₁) (h₂ : V₂.Nonsingular x₂ y₂) :
    HEq (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂) := by
  subst hV; subst hx; subst hy; rfl

private lemma heq_zero_of_eq {V₁ V₂ : Affine R} (hV : V₁ = V₂) :
    HEq (0 : V₁.Point) (0 : V₂.Point) := by
  subst hV; rfl

variable {F' : Type u} [Field F'] [DecidableEq F']

private lemma castPt_add {V₁ V₂ : Affine F'} (h : V₁ = V₂) (P Q : V₁.Point) :
    castPt h (P + Q) = castPt h P + castPt h Q := by
  subst h; simp only [castPt_rfl]

private def _root_.ModularCurve.SigmaSpine.RealisationAux.castAddHom {V₁ V₂ : Affine F'} (h : V₁ = V₂) : V₁.Point →+ V₂.Point where
  toFun := castPt h
  map_zero' := castPt_zero h
  map_add' := castPt_add h

p2m_export "ModularCurve.SigmaSpine.RealisationAux" "castAddHom"
@[scoped simp] private lemma castAddHom_apply {V₁ V₂ : Affine F'} (h : V₁ = V₂) (P : V₁.Point) :
    castAddHom h P = castPt h P := rfl

private lemma castPt_nsmul {V₁ V₂ : Affine F'} (h : V₁ = V₂) (n : ℕ) (P : V₁.Point) :
    castPt h (n • P) = n • castPt h P :=
  map_nsmul (castAddHom h) n P

end Cast

section Coord

variable {K : Type u} [Field K]

private lemma vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have _hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have _hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

private lemma vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have _hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have _hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

@[scoped simp] private lemma vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  simp [vcXInv, VariableChange.one_def]

@[scoped simp] private lemma vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  simp [vcYInv, VariableChange.one_def]

variable {K' : Type u} [Field K'] (φ : K →+* K')

private lemma map_vcXInv (C : VariableChange K) (x : K) :
    φ (vcXInv C x) = vcXInv (C.map φ) (φ x) := by
  simp only [vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

private lemma map_vcYInv (C : VariableChange K) (x y : K) :
    φ (vcYInv C x y) = vcYInv (C.map φ) (φ x) (φ y) := by
  simp only [vcYInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

private def negC (W : WeierstrassCurve K) : VariableChange K := ⟨-1, 0, -W.a₁, -W.a₃⟩

private lemma negC_smul (W : WeierstrassCurve K) : negC W • W = W := by
  ext <;> simp [negC, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆] <;> ring

private lemma negC_ne_one (W : WeierstrassCurve K) [W.IsElliptic] : negC W ≠ 1 := by
  intro h
  have hu : ((-1 : Kˣ) : K) = 1 := by
    have := congrArg (fun C : VariableChange K => (C.u : K)) h
    first | simpa [negC] using this | simpa [negC, WeierstrassCurve.VariableChange.one_u] using this | (simp [negC] at this; exact this)
  have hs : -W.a₁ = 0 := by
    have := congrArg VariableChange.s h; simpa [negC, VariableChange.one_def] using this
  have ht : -W.a₃ = 0 := by
    have := congrArg VariableChange.t h; simpa [negC, VariableChange.one_def] using this
  have h2 : (2 : K) = 0 := by
    have : (-1 : K) = 1 := by simpa using hu
    linear_combination -this
  have ha₁ : W.a₁ = 0 := by linear_combination -hs
  have ha₃ : W.a₃ = 0 := by linear_combination -ht
  apply W.isUnit_Δ.ne_zero
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, ha₁, ha₃]
  linear_combination (-8 * W.a₂ ^ 2 * (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) - 32 * W.a₄ ^ 3
    - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2

private lemma vcXInv_negC (W : WeierstrassCurve K) (x : K) : vcXInv (negC W) x = x := by
  simp [vcXInv, negC]

private lemma vcYInv_negC (W : WeierstrassCurve K) (x y : K) :
    vcYInv (negC W) x y = W.toAffine.negY x y := by
  simp only [vcYInv, negC, Affine.negY, inv_neg, inv_one, Units.val_neg, Units.val_one]
  simp; ring

end Coord

section Residue

variable {K : Type u} [Field K] {M : Type u} [Field M] [Algebra K M]
  (W₀ : Place K M)

private lemma mem_maximalIdeal_of_ord_pos {f : M} (hf : 0 < W₀.ord f) :
    ∃ hfA : f ∈ W₀.toValuationSubring, (⟨f, hfA⟩ : W₀.toValuationSubring) ∈
      IsLocalRing.maximalIdeal W₀.toValuationSubring := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W₀.toValuationSubring
  obtain ⟨u, hu⟩ := W₀.exists_unit_mul_zpow hf0 hπ
  have hn : W₀.ord f = (((W₀.ord f).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hf.le).symm
  have hn0 : (W₀.ord f).toNat ≠ 0 := by omega
  set a : W₀.toValuationSubring := (u : W₀.toValuationSubring) * π ^ (W₀.ord f).toNat with ha
  have hfa : f = (a : M) := by
    rw [hu, hn, zpow_natCast, ha]; push_cast; rfl
  refine ⟨hfa ▸ a.2, ?_⟩
  have : (⟨f, hfa ▸ a.2⟩ : W₀.toValuationSubring) = a := Subtype.ext hfa
  rw [this, ha]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (hπ.maximalIdeal_eq ▸
    Ideal.mem_span_singleton_self π) _ (Nat.pos_of_ne_zero hn0))

private lemma ord_eq_zero_of_isUnit {a : W₀.toValuationSubring} (ha : IsUnit a) : W₀.ord (a : M) = 0 :=
  W₀.ord_coe_unit ha.unit

end Residue

section Stab

variable {K : Type u} [Field K] {M : Type u} [Field M] [Algebra K M] {E : Type u} [Field E]
  [Algebra K E] [Algebra E M] [IsScalarTower K E M]

private lemma smul_place_eq_iff (σ : M ≃ₐ[E] M) (W₀ : Place K M) :
    SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ↔
      σ ∈ W₀.toValuationSubring.decompositionSubgroup E := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff, Place.ext_iff,
    SemilinearAut.smul_toValuationSubring]
  have key : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀.toValuationSubring =
      σ • W₀.toValuationSubring := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, SemilinearAut.ofAlgAut_smul]
    rfl
  rw [key]

private lemma isIntegral_of_apply_gen_eq (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : K⟮t⟯ →ₐ[K] M)
    (hψ : ψ ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ = t) : ψ.toRingHom.IsIntegral := by
  have hψ' : ψ = IntermediateField.val K⟮t⟯ := by
    apply IntermediateField.adjoin_algHom_ext K
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hψ
  rw [hψ']
  intro x
  exact Algebra.IsIntegral.isIntegral (R := K⟮t⟯) x

end Stab

section PointLemmas

variable {M : Type u} [Field M] [DecidableEq M]

omit [DecidableEq M] in
private lemma vcInvFun_some (C : VariableChange M) (V : Affine M) {x y : M} (h : V.Nonsingular x y) :
    vcInvFun C V (.some x y h) = .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

end PointLemmas

end RealisationAux
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux"

section Body

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
  (N : ℕ) (E₀ : WeierstrassCurve K) [E₀.IsElliptic]

private theorem castAddHom_some {k : Type u} [Field k] [DecidableEq k] {V V' : WeierstrassCurve k} (e : V' = V)
    {x y : k} (h : V'.toAffine.Nonsingular x y) :
    castAddHom e (.some x y h) = .some x y (e ▸ h) := by
  subst e; rfl

private noncomputable def frobPt (hfr : E₀.map (frobenius K q) = E₀) : E₀.toAffine.Point →+ E₀.toAffine.Point :=
  (castAddHom hfr).comp (mapPointHom (frobenius K q))

omit [IsAlgClosed K] [E₀.IsElliptic] in
private theorem frobPt_some (hfr : E₀.map (frobenius K q) = E₀) (x y : K) (h : E₀.toAffine.Nonsingular x y) :
    ∃ h', frobPt K q E₀ hfr (.some x y h) = .some (x ^ q) (y ^ q) h' := by
  have h1 : (E₀.map (frobenius K q)).toAffine.Nonsingular (frobenius K q x) (frobenius K q y) :=
    (E₀.toAffine.map_nonsingular (frobenius K q).injective x y).mpr h
  have h2 : E₀.toAffine.Nonsingular (x ^ q) (y ^ q) := by
    rw [← frobenius_def, ← frobenius_def]
    rw [hfr] at h1
    exact h1
  refine ⟨h2, ?_⟩
  show castAddHom hfr (mapPointHom (frobenius K q) (.some x y h)) = _
  rw [mapPointHom_apply, mapPoint_some, castAddHom_some]
  exact Point.some_congr' (frobenius_def ..) (frobenius_def ..) _ _

omit [IsAlgClosed K] [DecidableEq K] in

private theorem exists_frobPt (M : Type u) [Field M] [DecidableEq M] [Algebra K M] (t : M) (ht : Transcendental K t)
    (frM : SemilinearAut K M) (hfrt : frM • t = t) :
    ∃ frE : ((genCurve K t).baseChange M).toAffine.Point →+ ((genCurve K t).baseChange M).toAffine.Point,
      ∀ (x y : M) (h : ((genCurve K t).baseChange M).toAffine.Nonsingular x y),
        ∃ h', frE (.some x y h) = .some (frM • x) (frM • y) h' := by
  have hψ : (SemilinearAut.toRingAut frM : M →+* M) t = t := hfrt
  have hE := map_baseChange_genCurve ht (SemilinearAut.toRingAut frM : M →+* M) hψ
  refine ⟨(castAddHom hE).comp (mapPointHom (SemilinearAut.toRingAut frM : M →+* M)), fun x y h => ?_⟩
  have h1 : (((genCurve K t).baseChange M).map (SemilinearAut.toRingAut frM : M →+* M)).toAffine.Nonsingular
      ((SemilinearAut.toRingAut frM : M →+* M) x) ((SemilinearAut.toRingAut frM : M →+* M) y) :=
    (((genCurve K t).baseChange M).toAffine.map_nonsingular (SemilinearAut.toRingAut frM : M →+* M).injective x y).mpr h
  have h2 : ((genCurve K t).baseChange M).toAffine.Nonsingular (frM • x) (frM • y) := by
    rw [hE] at h1
    exact h1
  refine ⟨h2, ?_⟩
  show castAddHom hE (mapPointHom _ (.some x y h)) = _
  rw [mapPointHom_apply, mapPoint_some, castAddHom_some]
  rfl

private theorem exists_theta_rho (hfr : E₀.map (frobenius K q) = E₀)
    (M : Type u) [Field M] [DecidableEq M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
    (W₀ : Place K M) (hW₀ : 0 < W₀.ord (t - algebraMap K M E₀.j))
    {m : ℕ} (hmK : (m : K) ≠ 0)
    (hmodel :
        ∀ A : ValuationSubring M, IsUnit ((m : ℕ) : A) → t ∈ A →
            ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
              κ • (genCurve K t).baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
              ∀ (σ : M ≃ₐ[K⟮t⟯] M) (hσ : σ ∈ A.decompositionSubgroup K⟮t⟯),
                (⟨σ, hσ⟩ : A.decompositionSubgroup K⟮t⟯) ∈ A.inertiaSubgroup K⟮t⟯ →
                (∀ (n : ℕ), (n : K) ≠ 0 → ∀ P : ((genCurve K t).baseChange M).toAffine.Point, n • P = 0 →
                  WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P = P) →
                (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
                  g.map (IsLocalRing.residue A) = 1) →
                σ = 1)
    (hred : ReductionContract K E₀) :
    ∃ (θ : ((genCurve K t).baseChange M).toAffine.Point →+ E₀.toAffine.Point)
      (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K),
      (∀ (n : ℕ) (P : ((genCurve K t).baseChange M).toAffine.Point), ¬ q ∣ n → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ → ρ σ • E₀ = E₀) ∧
      (∀ σ τ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          SemilinearAut.ofAlgAut (τ.restrictScalars K) • W₀ = W₀ → ρ (σ * τ) = ρ σ * ρ τ) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ → ρ σ = 1 → σ = 1) ∧
      (∀ (frM : SemilinearAut K M), (∀ a : K, frM • (algebraMap K M a) = algebraMap K M (a ^ q)) →
        frM • t = t → frM • W₀ = W₀ →
        ∀ frE : ((genCurve K t).baseChange M).toAffine.Point →+ ((genCurve K t).baseChange M).toAffine.Point,
          (∀ (x y : M) (h : ((genCurve K t).baseChange M).toAffine.Nonsingular x y),
            ∃ h', frE (.some x y h) = .some (frM • x) (frM • y) h') →
          ∀ fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point,
            (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y), ∃ h', fr₀ (.some x y h) = .some (x ^ q) (y ^ q) h') →
            ∃ α : VariableChange K, α • E₀ = E₀ ∧
              ∀ P, HEq (Point.vcInvFun α E₀.toAffine (fr₀ (θ P))) (θ (frE P))) := by

  have hdeg : W₀.deg ≠ 0 := Place.deg_ne_zero_of_finiteDimensional_adjoin t ht W₀
  obtain ⟨htjA, htj𝔪⟩ := mem_maximalIdeal_of_ord_pos W₀ hW₀
  have htA : t ∈ W₀.toValuationSubring := by
    have := add_mem htjA (W₀.algebraMap_mem' E₀.j)
    rwa [sub_add_cancel] at this
  have hmA : IsUnit ((m : ℕ) : W₀.toValuationSubring) := by
    have h1 : ((m : ℕ) : W₀.toValuationSubring) = algebraMap K W₀.toValuationSubring m := by simp
    rw [h1]
    exact (IsUnit.mk0 _ hmK).map _
  obtain ⟨W, κ, hκ, hΔ, hfaith⟩ := hmodel W₀.toValuationSubring hmA htA
  letI hdec : DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring) := Classical.decEq _
  obtain ⟨hinj, g, hg, hmul, hres⟩ :=
    hred M inferInstance inferInstance inferInstance t ht inferInstance W₀ hW₀ hdec W κ hκ hΔ

  have hD : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      ∃ hσ : σ ∈ W₀.toValuationSubring.decompositionSubgroup K⟮t⟯,
        (⟨σ, hσ⟩ : W₀.toValuationSubring.decompositionSubgroup K⟮t⟯) ∈
          W₀.toValuationSubring.inertiaSubgroup K⟮t⟯ := fun σ h =>
    ⟨(smul_place_eq_iff σ W₀).mp h, mem_inertia_of_mem_decomposition W₀ hdeg _⟩
  have hresHom : ∀ (σ : M ≃ₐ[K⟮t⟯] M) (hσ : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀),
      (residueAut W₀ (SemilinearAut.ofAlgAut (σ.restrictScalars K)) hσ).toRingHom = RingHom.id _ :=
    fun σ hσ => RingHom.ext fun r => hres σ hσ r
  have hfixG : ∀ (σ : M ≃ₐ[K⟮t⟯] M) (hσ : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀),
      (g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map (IsLocalRing.residue W₀.toValuationSubring) •
          W.map (IsLocalRing.residue W₀.toValuationSubring) = W.map (IsLocalRing.residue W₀.toValuationSubring) := by
    intro σ hσ
    obtain ⟨-, hfix, -⟩ := hg _ (ofAlgAut_smul_t σ) hσ
    rwa [hresHom σ hσ, WeierstrassCurve.map_id] at hfix

  haveI hWell : W.IsElliptic := ⟨hΔ⟩
  haveI hgen : (genCurve K t).IsElliptic := by unfold genCurve; infer_instance
  haveI hgenM : ((genCurve K t).baseChange M).IsElliptic := instIsEllipticMap (genCurve K t) _
  have hjW : W.j = ⟨t, htA⟩ := by
    apply Subtype.ext
    have h1 : ((W.j : W₀.toValuationSubring) : M) = (W.map W₀.toValuationSubring.subtype).j :=
      (W.map_j W₀.toValuationSubring.subtype).symm
    rw [h1, j_congr hκ.symm, variableChange_j]
    show ((genCurve K t).map (algebraMap K⟮t⟯ M)).j = t
    rw [(genCurve K t).map_j, ofJ_j]
    rfl
  have hjWK : ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom).j = E₀.j := by
    rw [WeierstrassCurve.map_j, WeierstrassCurve.map_j]
    change toK W₀ hdeg W.j = E₀.j
    rw [hjW, toK_eq_toK_of_sub_mem W₀ hdeg (a := ⟨t, htA⟩) (b := algebraMap K W₀.toValuationSubring E₀.j) htj𝔪,
      toK_algebraMap]
  obtain ⟨γ₀, hγ₀⟩ := exists_variableChange_of_j_eq _ E₀ hjWK

  let θ : ((genCurve K t).baseChange M).toAffine.Point →+ E₀.toAffine.Point :=
    (castAddHom hγ₀).comp ((vcInvAddHom γ₀ ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom)).comp
      ((mapPointHom (resK W₀ hdeg).toRingHom).comp (reduceAlongHom W₀ W κ hκ hΔ)))
  have hθeq : ∀ P, θ P = castAddHom hγ₀ (Point.vcInvFun γ₀ _
      (mapPoint (resK W₀ hdeg).toRingHom (reduceAlongHom W₀ W κ hκ hΔ P))) := fun P => rfl
  have hθsome : ∀ (P : ((genCurve K t).baseChange M).toAffine.Point)
      {x y : IsLocalRing.ResidueField W₀.toValuationSubring}
      (h : (W.map (IsLocalRing.residue W₀.toValuationSubring)).toAffine.Nonsingular x y),
      reduceAlongHom W₀ W κ hκ hΔ P = .some x y h →
        ∃ h', θ P = .some (vcXInv γ₀ (resK W₀ hdeg x)) (vcYInv γ₀ (resK W₀ hdeg x) (resK W₀ hdeg y)) h' := by
    intro P x y h hP
    rw [hθeq, hP, mapPoint_some, vcInvFun_some, castAddHom_apply, castPt_some]
    exact ⟨_, rfl⟩
  have hθzero : ∀ P : ((genCurve K t).baseChange M).toAffine.Point,
      reduceAlongHom W₀ W κ hκ hΔ P = 0 → θ P = 0 := by
    intro P hP
    rw [hθeq, hP, mapPoint_zero, Point.vcInvFun_zero, map_zero]
  let gK : (M ≃ₐ[K⟮t⟯] M) → VariableChange K := fun σ =>
    ((g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map (IsLocalRing.residue W₀.toValuationSubring)).map
      (resK W₀ hdeg).toRingHom
  have hgKfix : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      gK σ • ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom) = ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom) := by
    intro σ hσ
    show (((g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map (IsLocalRing.residue W₀.toValuationSubring)).map
      (resK W₀ hdeg).toRingHom) • ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom) = ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom)
    rw [WeierstrassCurve.map_variableChange, hfixG σ hσ]
  let ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K := fun σ => γ₀ * gK σ * γ₀⁻¹

  haveI hcharR : CharP (IsLocalRing.ResidueField W₀.toValuationSubring) q :=
    charP_of_injective_ringHom (algebraMap K W₀.ResidueField).injective q
  have hc2 : ∀ (n : ℕ) (P : ((genCurve K t).baseChange M).toAffine.Point),
      ¬ q ∣ n → n • P = 0 → θ P = 0 → P = 0 := by
    intro n P hqn hnP hθP
    have hn : (n : IsLocalRing.ResidueField W₀.toValuationSubring) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField W₀.toValuationSubring) q n]
      exact hqn
    apply hinj n P hn hnP
    rcases hQ : reduceAlongHom W₀ W κ hκ hΔ P with _ | ⟨x, y, h⟩
    · rfl
    · exfalso
      obtain ⟨h', hθP'⟩ := hθsome P h hQ
      rw [hθP'] at hθP
      exact Point.some_ne_zero _ hθP

  have hc3 : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ → ρ σ • E₀ = E₀ := by
    intro σ hσ
    show (γ₀ * gK σ * γ₀⁻¹) • E₀ = E₀
    rw [mul_smul, mul_smul, ← hγ₀, inv_smul_smul, hgKfix σ hσ]

  have hofMul : ∀ σ τ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut ((σ * τ).restrictScalars K) =
      SemilinearAut.ofAlgAut (σ.restrictScalars K) * SemilinearAut.ofAlgAut (τ.restrictScalars K) := by
    intro σ τ
    rw [← map_mul]
    rfl
  have hc4 : ∀ σ τ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      SemilinearAut.ofAlgAut (τ.restrictScalars K) • W₀ = W₀ → ρ (σ * τ) = ρ σ * ρ τ := by
    intro σ τ hσ hτ
    have h1 : gK (σ * τ) = gK σ * gK τ := by
      show ((g (SemilinearAut.ofAlgAut ((σ * τ).restrictScalars K))).map
          (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom = _
      rw [hofMul, hmul _ _ (ofAlgAut_smul_t σ) hσ (ofAlgAut_smul_t τ) hτ, hresHom σ hσ, VariableChange.map_id,
        VariableChange.map_mul']
    show γ₀ * gK (σ * τ) * γ₀⁻¹ = (γ₀ * gK σ * γ₀⁻¹) * (γ₀ * gK τ * γ₀⁻¹)
    rw [h1]
    group

  have hc5 : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
        (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P)) := by
    intro σ hσ P
    obtain ⟨-, hfix, hheq⟩ := hg _ (ofAlgAut_smul_t σ) hσ
    have hx : ∀ x, resK W₀ hdeg (vcXInv ((g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map
        (IsLocalRing.residue W₀.toValuationSubring)) x) = vcXInv (gK σ) (resK W₀ hdeg x) :=
      fun x => map_vcXInv (resK W₀ hdeg).toRingHom _ x
    have hy : ∀ x y, resK W₀ hdeg (vcYInv ((g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map
        (IsLocalRing.residue W₀.toValuationSubring)) x y) = vcYInv (gK σ) (resK W₀ hdeg x) (resK W₀ hdeg y) :=
      fun x y => map_vcYInv (resK W₀ hdeg).toRingHom _ x y
    rcases hQ : reduceAlongHom W₀ W κ hκ hΔ P with _ | ⟨x, y, h⟩
    · have h1 : θ P = 0 := hθzero P hQ
      have h2 : θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P) = 0 := by
        apply hθzero
        rw [← semilinearPt_ofAlgAut ht σ (ofAlgAut_smul_t σ)]
        exact reduceAlongHom_semilinearPt_zero W₀ W κ hκ hΔ ht _ _ hσ _ hfix hheq P hQ
      rw [h1, h2, Point.vcInvFun_zero]
      exact heq_zero_of_eq (hc3 σ hσ)
    · obtain ⟨h₁, hθP⟩ := hθsome P h hQ
      obtain ⟨h₂, hQ'⟩ := reduceAlongHom_semilinearPt_some W₀ W κ hκ hΔ ht _ _ hσ _ hfix hheq P h hQ
      rw [semilinearPt_ofAlgAut ht σ (ofAlgAut_smul_t σ)] at hQ'
      simp only [hres σ hσ] at hQ'
      obtain ⟨h₃, hθσP⟩ := hθsome _ _ hQ'
      rw [hθP, hθσP, vcInvFun_some]
      apply heq_some_of_eq (hc3 σ hσ)
      · show vcXInv (γ₀ * gK σ * γ₀⁻¹) (vcXInv γ₀ (resK W₀ hdeg x)) = _
        rw [vcXInv_mul, vcXInv_mul, ← vcXInv_mul γ₀⁻¹ γ₀, inv_mul_cancel, vcXInv_one, hx]
      · show vcYInv (γ₀ * gK σ * γ₀⁻¹) (vcXInv γ₀ (resK W₀ hdeg x))
            (vcYInv γ₀ (resK W₀ hdeg x) (resK W₀ hdeg y)) = _
        rw [vcYInv_mul, vcYInv_mul, ← vcYInv_mul γ₀⁻¹ γ₀, ← vcXInv_mul γ₀⁻¹ γ₀, inv_mul_cancel, vcXInv_one,
          vcYInv_one, hx, hy]

  have hc7 : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ → ρ σ = 1 → σ = 1 := by
    intro σ hσ hρ
    obtain ⟨hσD, hσI⟩ := hD σ hσ
    obtain ⟨hcoc, -, -⟩ := hg _ (ofAlgAut_smul_t σ) hσ
    have hgK1 : gK σ = 1 := by
      have h1 : γ₀ * gK σ * γ₀⁻¹ = 1 := hρ
      calc gK σ = γ₀⁻¹ * (γ₀ * gK σ * γ₀⁻¹) * γ₀ := by group
        _ = 1 := by rw [h1]; group
    have hg1 : (g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map (IsLocalRing.residue W₀.toValuationSubring) = 1 := by
      have h1 : ((g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map
          (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom = 1 := hgK1
      have h2 : (g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map (IsLocalRing.residue W₀.toValuationSubring) =
          (((g (SemilinearAut.ofAlgAut (σ.restrictScalars K))).map (IsLocalRing.residue W₀.toValuationSubring)).map
            (resK W₀ hdeg).toRingHom).map (resK W₀ hdeg).symm.toRingHom := by
        rw [VariableChange.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, VariableChange.map_id]
      rw [h2, h1]
      exact (VariableChange.mapHom _).map_one
    have htors : ∀ (n : ℕ), (n : K) ≠ 0 → ∀ P : ((genCurve K t).baseChange M).toAffine.Point, n • P = 0 →
        WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P = P := by
      intro n hn P hP
      have hqn : ¬ q ∣ n := fun hd => hn ((CharP.cast_eq_zero_iff K q n).mpr hd)
      have h1 := hc5 σ hσ P
      rw [hρ] at h1
      have h2 : θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P) = θ P := by
        rw [eq_castPt_of_heq (one_smul (VariableChange K) E₀) h1]
        rcases θ P with _ | ⟨x, y, h⟩
        · exact castPt_zero _
        · rw [vcInvFun_some, castPt_some]
          exact Point.some_congr' (vcXInv_one x) (vcYInv_one x y) _ _
      have h4 : θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P - P) = 0 := by
        rw [map_sub, h2, sub_self]
      have h5 : n • (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P - P) = 0 := by
        rw [nsmul_sub, ← map_nsmul, hP, map_zero, sub_zero]
      exact sub_eq_zero.mp (hc2 n _ hqn h5 h4)
    have hhom : (SemilinearAut.toRingAut (SemilinearAut.ofAlgAut (σ.restrictScalars K)) : M →+* M) = (σ : M →+* M) :=
      RingHom.ext fun _ => rfl
    refine hfaith σ hσD hσI htors ⟨g (SemilinearAut.ofAlgAut (σ.restrictScalars K)), ?_, hg1⟩
    rw [hcoc, hhom]

  have hdefect : ∀ (frM : SemilinearAut K M), (∀ a : K, frM • (algebraMap K M a) = algebraMap K M (a ^ q)) →
      frM • t = t → frM • W₀ = W₀ →
      ∀ frE : ((genCurve K t).baseChange M).toAffine.Point →+ ((genCurve K t).baseChange M).toAffine.Point,
        (∀ (x y : M) (h : ((genCurve K t).baseChange M).toAffine.Nonsingular x y),
          ∃ h', frE (.some x y h) = .some (frM • x) (frM • y) h') →
        ∀ fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point,
          (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y), ∃ h', fr₀ (.some x y h) = .some (x ^ q) (y ^ q) h') →
          ∃ α : VariableChange K, α • E₀ = E₀ ∧
            ∀ P, HEq (Point.vcInvFun α E₀.toAffine (fr₀ (θ P))) (θ (frE P)) := by
    intro frM hfrK hfrt hfrW frE hfrE fr₀ hfr₀
    obtain ⟨-, hfixF, hheqF⟩ := hg frM hfrt hfrW

    have hfrE' : ∀ P, frE P = semilinearPt ht frM hfrt P := by
      intro P
      rcases P with _ | ⟨x, y, h⟩
      · show frE 0 = castPt _ (mapPoint _ 0)
        rw [map_zero, mapPoint_zero, castPt_zero]
      · obtain ⟨h', hP⟩ := hfrE x y h
        rw [hP]
        show _ = castPt _ (mapPoint _ (.some x y h))
        rw [mapPoint_some, castPt_some]
        rfl

    have hresF : ∀ r, resK W₀ hdeg (residueAut W₀ frM hfrW r) = resK W₀ hdeg r ^ q := by
      intro r
      have hr : r = IsLocalRing.residue W₀.toValuationSubring
          (algebraMap K W₀.toValuationSubring (resK W₀ hdeg r)) := (algebraMap_resK W₀ hdeg r).symm
      have h1 : residueAut W₀ frM hfrW (IsLocalRing.residue W₀.toValuationSubring
            (algebraMap K W₀.toValuationSubring (resK W₀ hdeg r))) =
          IsLocalRing.residue W₀.toValuationSubring (algebraMap K W₀.toValuationSubring (resK W₀ hdeg r ^ q)) := by
        show IsLocalRing.residue W₀.toValuationSubring (stabRingEquiv W₀ frM hfrW _) = _
        congr 1
        apply Subtype.ext
        show frM • algebraMap K M (resK W₀ hdeg r) = algebraMap K M (resK W₀ hdeg r ^ q)
        exact hfrK _
      conv_lhs => rw [hr, h1]
      exact toK_algebraMap W₀ hdeg _
    have hresHomF : (resK W₀ hdeg).toRingHom.comp (residueAut W₀ frM hfrW).toRingHom = (frobenius K q).comp (resK W₀ hdeg).toRingHom :=
      RingHom.ext fun r => by
        show resK W₀ hdeg (residueAut W₀ frM hfrW r) = frobenius K q (resK W₀ hdeg r)
        rw [hresF, frobenius_def]

    have hWKF : ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (residueAut W₀ frM hfrW).toRingHom).map (resK W₀ hdeg).toRingHom = ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom).map (frobenius K q) := by
      rw [WeierstrassCurve.map_map, hresHomF, ← WeierstrassCurve.map_map]
    have hfixK : (((g frM).map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom) • ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom).map (frobenius K q) =
        ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom) := by
      rw [← hWKF, WeierstrassCurve.map_variableChange, hfixF]
    have hE₀F : γ₀.map (frobenius K q) • ((W.map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom).map (frobenius K q) = E₀ := by
      rw [WeierstrassCurve.map_variableChange, hγ₀, hfr]
    have hαE : (γ₀ * ((g frM).map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom *
        (γ₀.map (frobenius K q))⁻¹) • E₀ = E₀ := by
      conv_lhs => rw [← hE₀F]
      rw [mul_smul, mul_smul, inv_smul_smul, hfixK, hγ₀]
    have hαmul : γ₀ * ((g frM).map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom *
        (γ₀.map (frobenius K q))⁻¹ * γ₀.map (frobenius K q) =
        γ₀ * ((g frM).map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom := inv_mul_cancel_right _ _
    have hx : ∀ x, resK W₀ hdeg (vcXInv ((g frM).map (IsLocalRing.residue W₀.toValuationSubring)) x) =
        vcXInv (((g frM).map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom) (resK W₀ hdeg x) :=
      fun x => map_vcXInv (resK W₀ hdeg).toRingHom _ x
    have hy : ∀ x y, resK W₀ hdeg (vcYInv ((g frM).map (IsLocalRing.residue W₀.toValuationSubring)) x y) =
        vcYInv (((g frM).map (IsLocalRing.residue W₀.toValuationSubring)).map (resK W₀ hdeg).toRingHom) (resK W₀ hdeg x)
          (resK W₀ hdeg y) :=
      fun x y => map_vcYInv (resK W₀ hdeg).toRingHom _ x y
    refine ⟨_, hαE, fun P => ?_⟩
    rw [hfrE' P]
    rcases hQ : reduceAlongHom W₀ W κ hκ hΔ P with _ | ⟨x, y, h⟩
    · rw [hθzero P hQ, hθzero _ (reduceAlongHom_semilinearPt_zero W₀ W κ hκ hΔ ht frM hfrt hfrW _ hfixF hheqF P hQ),
        map_zero, Point.vcInvFun_zero]
      exact heq_zero_of_eq hαE
    · obtain ⟨h₁, hθP⟩ := hθsome P h hQ
      obtain ⟨h₂, hQ'⟩ := reduceAlongHom_semilinearPt_some W₀ W κ hκ hΔ ht frM hfrt hfrW _ hfixF hheqF P h hQ
      obtain ⟨h₃, hθF⟩ := hθsome _ _ hQ'
      obtain ⟨h₄, hfr₀P⟩ := hfr₀ _ _ h₁
      rw [hθP, hfr₀P, hθF, vcInvFun_some]
      apply heq_some_of_eq hαE
      · rw [← frobenius_def, map_vcXInv (frobenius K q), frobenius_def, ← vcXInv_mul, hαmul, vcXInv_mul, hx, hresF]
      · rw [← frobenius_def, ← frobenius_def, map_vcXInv (frobenius K q), map_vcYInv (frobenius K q), frobenius_def,
          frobenius_def, ← vcYInv_mul, hαmul, vcYInv_mul, hx, hy, hresF, hresF]
  exact ⟨θ, ρ, hc2, hc3, hc4, hc5, hc7, hdefect⟩

private theorem realisation (M : Type u) [Field M] [DecidableEq M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
    (W₀ : Place K M) (hW₀ : 0 < W₀.ord (t - algebraMap K M E₀.j))
    {m : ℕ} (hmK : (m : K) ≠ 0) (hm3 : q = 2 → m = 3)
    (hmcard : Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // m • P = 0} = m ^ 2)
    (hmodel :
        ∀ A : ValuationSubring M, IsUnit ((m : ℕ) : A) → t ∈ A →
            ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
              κ • (genCurve K t).baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
              ∀ (σ : M ≃ₐ[K⟮t⟯] M) (hσ : σ ∈ A.decompositionSubgroup K⟮t⟯),
                (⟨σ, hσ⟩ : A.decompositionSubgroup K⟮t⟯) ∈ A.inertiaSubgroup K⟮t⟯ →
                (∀ (n : ℕ), (n : K) ≠ 0 → ∀ P : ((genCurve K t).baseChange M).toAffine.Point, n • P = 0 →
                  WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P = P) →
                (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
                  g.map (IsLocalRing.residue A) = 1) →
                σ = 1)
    (θ : ((genCurve K t).baseChange M).toAffine.Point →+ E₀.toAffine.Point)
    (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K)
    (hc2 : ∀ (n : ℕ) (P : ((genCurve K t).baseChange M).toAffine.Point), ¬ q ∣ n → n • P = 0 → θ P = 0 → P = 0)
    (hc3 : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ → ρ σ • E₀ = E₀)
    (hc4 : ∀ σ τ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      SemilinearAut.ofAlgAut (τ.restrictScalars K) • W₀ = W₀ → ρ (σ * τ) = ρ σ * ρ τ)
    (hc5 : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
        (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P)))
    (hc7 : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ → ρ σ = 1 → σ = 1) :
    ∀ γ : VariableChange K, γ • E₀ = E₀ →
      ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
        ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
         (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
            (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P)))) := by

  intro γ hγ
  have _ := hc2
  obtain ⟨j₀, hE₀⟩ : ∃ j₀ : K, E₀.j = j₀ := ⟨_, rfl⟩
  rw [hE₀] at hW₀
  have htr : Transcendental K t := ht

  let A : ValuationSubring M := W₀.toValuationSubring
  obtain ⟨htjA, htj𝔪⟩ := RealisationAux.mem_maximalIdeal_of_ord_pos W₀ hW₀
  have htA : t ∈ A := by
    have := add_mem htjA (W₀.algebraMap_mem' j₀)
    rwa [sub_add_cancel] at this
  have hmA : IsUnit ((m : ℕ) : A) := by
    have h1 : ((m : ℕ) : A) = algebraMap K A m := by simp
    rw [h1]
    exact (IsUnit.mk0 _ hmK).map _
  obtain ⟨W, κ, hκ, hΔ, -⟩ := hmodel A hmA htA

  have hvt : (IntermediateField.val K⟮t⟯) (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯) = t :=
    rfl
  have hB := Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K (F := K⟮t⟯) (M := M)
    (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯) t j₀ (IntermediateField.val K⟮t⟯) hvt
    inferInstance inferInstance (RealisationAux.isIntegral_of_apply_gen_eq t) W₀ hW₀
  obtain ⟨e, he_def⟩ : ∃ e : ℕ, Nat.card {σ : M ≃ₐ[K⟮t⟯] M //
    SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀} = e := ⟨_, rfl⟩
  have hcardD : W₀.ord (t - algebraMap K M j₀) = e := by rw [← he_def]; exact hB.1
  clear hB
  have hepos : 0 < e := by
    have : (0 : ℤ) < e := hcardD ▸ hW₀
    exact_mod_cast this

  haveI : Finite (MulAction.stabilizer (VariableChange K) E₀) :=
    WeierstrassCurve.finite_stabilizer_variableChange K E₀
  have h1D : SemilinearAut.ofAlgAut ((1 : M ≃ₐ[K⟮t⟯] M).restrictScalars K) • W₀ = W₀ :=
    (RealisationAux.smul_place_eq_iff (1 : M ≃ₐ[K⟮t⟯] M) W₀).mpr (one_mem _)
  have hρ1 : ρ 1 = 1 := by
    have h := hc4 1 1 h1D h1D
    rw [mul_one] at h
    exact mul_eq_left.mp h.symm
  have hc3' : ∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
      (ρ σ • E₀).toAffine = E₀.toAffine := fun σ h => hc3 σ h

  let fD : {σ : M ≃ₐ[K⟮t⟯] M // SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀} →
      MulAction.stabilizer (VariableChange K) E₀ := fun σ => ⟨ρ σ.1, hc3 σ.1 σ.2⟩
  have hfD : Function.Injective fD := by
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
    have h' : ρ σ = ρ τ := congrArg (fun x : MulAction.stabilizer (VariableChange K) E₀ =>
      (x : VariableChange K)) h
    have hσ' := (RealisationAux.smul_place_eq_iff σ W₀).mp hσ
    have hτ' := (RealisationAux.smul_place_eq_iff τ W₀).mp hτ
    have hτinv : SemilinearAut.ofAlgAut ((τ⁻¹ : M ≃ₐ[K⟮t⟯] M).restrictScalars K) • W₀ = W₀ :=
      (RealisationAux.smul_place_eq_iff _ W₀).mpr (inv_mem hτ')
    have hστ : SemilinearAut.ofAlgAut ((σ * τ⁻¹ : M ≃ₐ[K⟮t⟯] M).restrictScalars K) • W₀ = W₀ :=
      (RealisationAux.smul_place_eq_iff _ W₀).mpr (mul_mem hσ' (inv_mem hτ'))
    have h1 : ρ (σ * τ⁻¹) = 1 := by
      rw [hc4 σ τ⁻¹ hσ hτinv, h', ← hc4 τ τ⁻¹ hτ hτinv, mul_inv_cancel, hρ1]
    have h2 := hc7 _ hστ h1
    exact Subtype.ext (mul_inv_eq_one.mp h2)

  have hHEqneg : ∀ (σ : M ≃ₐ[K⟮t⟯] M)
      (hσ : SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀) (P),
      HEq (Point.vcInvFun (RealisationAux.negC E₀ * ρ σ) E₀.toAffine (θ P))
        (-θ (Point.map (σ : M →ₐ[K⟮t⟯] M) P)) := by
    intro σ hσ P
    have hcurve : ((RealisationAux.negC E₀ * ρ σ) • E₀).toAffine = E₀.toAffine := by
      show (RealisationAux.negC E₀ * ρ σ) • E₀ = E₀
      rw [mul_smul, hc3 σ hσ, RealisationAux.negC_smul]
    have h5 := hc5 σ hσ P
    have hR : θ (Point.map (σ : M →ₐ[K⟮t⟯] M) P) =
        RealisationAux.castPt (hc3' σ hσ) (Point.vcInvFun (ρ σ) E₀.toAffine (θ P)) := RealisationAux.eq_castPt_of_heq _ h5
    rw [hR]
    rcases θ P with _ | ⟨_X, _Y, _hXY⟩
    · show HEq (0 : ((RealisationAux.negC E₀ * ρ σ) • E₀).toAffine.Point) (-(0 : E₀.toAffine.Point))
      rw [_root_.neg_zero]
      exact RealisationAux.heq_zero_of_eq hcurve
    · rw [RealisationAux.vcInvFun_some, RealisationAux.vcInvFun_some, RealisationAux.castPt_some, Affine.Point.neg_some]
      apply RealisationAux.heq_some_of_eq hcurve
      · rw [RealisationAux.vcXInv_mul, RealisationAux.vcXInv_negC]
      · rw [RealisationAux.vcYInv_mul, RealisationAux.vcYInv_negC]

  have key : Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ e ∨
      Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ 2 := by

    have ht0 : t ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
    have ht1728 : (t : M) - 1728 ≠ 0 := by
      intro h; apply htr
      rw [sub_eq_zero.mp h, show (1728 : M) = algebraMap K M 1728 from (map_ofNat _ 1728).symm]
      exact isAlgebraic_algebraMap _
    have hΔE : ((genCurve K t).baseChange M).Δ = t ^ 2 * (t - 1728) ^ 9 := by
      rw [baseChange_genCurve ht, ofJNe0Or1728_Δ]
    have h12 : (12 : ℤ) ∣ (2 * W₀.ord t + 9 * W₀.ord (t - 1728)) := by
      have h1 := congrArg WeierstrassCurve.Δ hκ
      rw [variableChange_Δ, map_Δ, hΔE] at h1
      have h2 := congrArg W₀.ord h1
      rw [W₀.ord_mul (pow_ne_zero _ (Units.ne_zero _))
        (mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ ht1728)),
        W₀.ord_mul (pow_ne_zero _ ht0) (pow_ne_zero _ ht1728)] at h2
      simp only [← zpow_natCast, Place.ord_zpow] at h2
      rw [show W₀.ord ((A.subtype) W.Δ) = 0 from RealisationAux.ord_eq_zero_of_isUnit W₀ hΔ] at h2
      push_cast at h2
      rw [W₀.ord_inv] at h2
      exact ⟨W₀.ord ((κ.u : Mˣ) : M), by linarith⟩

    have hunitK : ∀ (a : A) (c : K), c ≠ 0 →
        a - algebraMap K A c ∈ IsLocalRing.maximalIdeal A → IsUnit a := by
      intro a c hc hm
      by_contra hna
      have ha : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hna
      have h1 : algebraMap K A c ∈ IsLocalRing.maximalIdeal A := by
        have := Ideal.sub_mem _ ha hm; rwa [sub_sub_cancel] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp h1 ((IsUnit.mk0 c hc).map _)
    have hcoe1728 : ((algebraMap K A 1728 : A) : M) = 1728 := by
      rw [show algebraMap K A 1728 = (1728 : A) from map_ofNat _ 1728]; rfl
    by_cases h6 : (6 : K) = 0
    ·
      have hp23 : q = 2 ∨ q = 3 := by
        have h6' : q ∣ 2 * 3 := (CharP.cast_eq_zero_iff K q 6).mp (by exact_mod_cast h6)
        have hp : q.Prime := Fact.out
        rcases (Nat.Prime.dvd_mul hp).mp h6' with h | h
        · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
        · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
      have h1728K : (1728 : K) = 0 := by
        rw [show (1728 : K) = 6 * 288 by norm_num, h6, zero_mul]
      have h1728M : (1728 : M) = 0 := by
        rw [show (1728 : M) = algebraMap K M 1728 from (map_ofNat _ 1728).symm, h1728K,
          _root_.map_zero]
      by_cases hj0 : j₀ = 0
      · left
        have hcardD' : W₀.ord t = e := by rw [← hcardD, hj0, _root_.map_zero, sub_zero]
        have h12e : 12 ∣ e := by
          rw [h1728M, sub_zero, hcardD'] at h12
          omega
        rcases hp23 with hp2 | hp3
        ·
          obtain ⟨-, h24⟩ := (WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j E₀).2.2.2
            (by rw [← hp2]; exact ringChar.eq K q) (hE₀.trans hj0)
          have h8e : 8 ∣ e := by
            have hm : m = 3 := hm3 hp2
            haveI : CharP M 2 := by
              have hK : CharP K q := inferInstance
              rw [hp2] at hK
              exact charP_of_injective_ringHom (algebraMap K M).injective 2

            have h9 : 1 < Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // m • P = 0} := by
              rw [hmcard, hm]; norm_num
            haveI : Finite {P : ((genCurve K t).baseChange M).toAffine.Point // m • P = 0} :=
              Nat.finite_of_card_ne_zero (by omega)
            haveI := Finite.one_lt_card_iff_nontrivial.mp h9
            obtain ⟨⟨P₃, hP₃⟩, hne⟩ := exists_ne
              (⟨0, by rw [smul_zero]⟩ : {P : ((genCurve K t).baseChange M).toAffine.Point // m • P = 0})
            have hP₃ne : P₃ ≠ 0 := fun h => hne (Subtype.ext h)
            have hQ3 : (3 : ℕ) • P₃ = 0 := by rw [← hm]; exact hP₃

            have h2M : (2 : M) = 0 := CharTwo.two_eq_zero
            have h36 : (36 : M) = 0 := by
              rw [show (36 : M) = 2 * 18 by norm_num, h2M, zero_mul]
            have hEV0 : (genCurve K t).baseChange M = (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M) := by
              rw [baseChange_genCurve ht]
              simp only [ofJNe0Or1728, h1728M, sub_zero, h36, CharTwo.neg_eq]
              ext <;> simp
            have hEV : ((genCurve K t).baseChange M).toAffine =
                (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine := hEV0
            rcases hQdef : P₃ with _ | ⟨x₀, y₀, hxy⟩
            · exact absurd hQdef hP₃ne
            · have hns : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀ :=
                hEV ▸ hxy
              have h3P : (3 : ℕ) • (Point.some x₀ y₀ hns) = 0 := by
                have h1 : RealisationAux.castPt hEV P₃ = Point.some x₀ y₀ hns := by
                  rw [hQdef, RealisationAux.castPt_some]
                rw [← h1, ← RealisationAux.castPt_nsmul, hQ3, RealisationAux.castPt_zero]
              have htu : ¬ IsUnit (⟨t, htA⟩ : A) := by
                intro hu
                apply (IsLocalRing.mem_maximalIdeal _).mp _ hu
                have h1 : (⟨t, htA⟩ : A) = ⟨t - algebraMap K M j₀, htjA⟩ :=
                  Subtype.ext (by simp [hj0])
                rw [h1]; exact htj𝔪
              obtain ⟨μ, u, hu, htμ⟩ :=
                WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo A htA htu ht0 hns h3P
              have hu0 : ((u : A) : M) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
              have hμ0 : μ ≠ 0 := by
                rintro rfl; apply ht0; rw [htμ]; simp
              have h8 : (e : ℤ) = 8 * W₀.ord μ := by
                rw [← hcardD', htμ, W₀.ord_mul hu0 (pow_ne_zero _ hμ0), RealisationAux.ord_eq_zero_of_isUnit W₀ hu,
                  zero_add, ← zpow_natCast, W₀.ord_zpow]
                push_cast; ring
              have : ((8 : ℕ) : ℤ) ∣ (e : ℤ) := ⟨W₀.ord μ, by rw [h8]; push_cast; ring⟩
              exact Int.natCast_dvd_natCast.mp this
          have h24e : 24 ∣ e := by omega
          exact h24.trans (Nat.le_of_dvd hepos h24e)
        · obtain ⟨-, h12le⟩ := (WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j E₀).2.2.1
            (by rw [← hp3]; exact ringChar.eq K q) (hE₀.trans hj0)
          exact h12le.trans (Nat.le_of_dvd hepos h12e)
      · right
        have hchar : ringChar K = 2 ∨ ringChar K = 3 := by
          rcases hp23 with hp2 | hp3
          · left; rw [← hp2]; exact ringChar.eq K q
          · right; rw [← hp3]; exact ringChar.eq K q
        have hj : E₀.j ≠ 0 := by rw [hE₀]; exact hj0
        exact (WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
          hchar E₀ hj).le
    ·
      have h2 : (2 : K) ≠ 0 := fun h => h6 (by linear_combination 3 * h)
      have h3 : (3 : K) ≠ 0 := fun h => h6 (by linear_combination 2 * h)
      have h1728K : (1728 : K) ≠ 0 := by
        rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
        exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
      by_cases hj0 : j₀ = 0
      · left
        have hcardD' : W₀.ord t = e := by rw [← hcardD, hj0, _root_.map_zero, sub_zero]
        have hu : IsUnit (⟨t, htA⟩ - algebraMap K A 1728 : A) := by
          apply hunitK _ (-1728) (neg_ne_zero.mpr h1728K)
          have h1 : (⟨t, htA⟩ - algebraMap K A 1728 : A) - algebraMap K A (-1728) =
              ⟨t - algebraMap K M j₀, htjA⟩ := by
            apply Subtype.ext
            push_cast
            rw [hcoe1728, hj0, _root_.map_zero, sub_zero]
            ring
          rw [h1]; exact htj𝔪
        have hord0 : W₀.ord (t - 1728) = 0 := by
          have h1 := RealisationAux.ord_eq_zero_of_isUnit W₀ hu
          have h2 : ((⟨t, htA⟩ - algebraMap K A 1728 : A) : M) = t - 1728 := by
            push_cast; rw [hcoe1728]
          rwa [h2] at h1
        have h6e : 6 ∣ e := by
          rw [hord0, mul_zero, add_zero, hcardD'] at h12
          omega
        obtain ⟨-, h6le⟩ := (WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j E₀).1 h6
          (hE₀.trans hj0)
        exact h6le.trans (Nat.le_of_dvd hepos h6e)
      · by_cases hj1728 : j₀ = 1728
        · left
          have hcardD' : W₀.ord (t - 1728) = e := by rw [← hcardD, hj1728, map_ofNat]
          have hu : IsUnit (⟨t, htA⟩ : A) := by
            apply hunitK _ 1728 h1728K
            have h1 : (⟨t, htA⟩ : A) - algebraMap K A 1728 = ⟨t - algebraMap K M j₀, htjA⟩ := by
              apply Subtype.ext
              push_cast
              rw [hcoe1728, hj1728, map_ofNat]
            rw [h1]; exact htj𝔪
          have hord0 : W₀.ord t = 0 := RealisationAux.ord_eq_zero_of_isUnit W₀ hu
          have h4e : 4 ∣ e := by
            rw [hord0, mul_zero, zero_add, hcardD'] at h12
            omega
          obtain ⟨-, h4le⟩ := (WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j E₀).2.1 h6
            (hE₀.trans hj1728)
          exact h4le.trans (Nat.le_of_dvd hepos h4e)
        · right
          have hj0' : E₀.j ≠ 0 := by rw [hE₀]; exact hj0
          have hj1728' : E₀.j ≠ 1728 := by rw [hE₀]; exact hj1728
          exact (WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
            h2 h3 E₀ hj0' hj1728').le

  rcases key with hle | hle2
  · have hbij := hfD.bijective_of_nat_card_le (he_def ▸ hle)
    obtain ⟨⟨σ, hσ⟩, hσγ⟩ := hbij.2 ⟨γ, hγ⟩
    have hργ : ρ σ = γ := congrArg Subtype.val hσγ
    exact ⟨σ, hσ, Or.inl fun P => by rw [← hργ]; exact hc5 σ hσ P⟩
  · have hγ' : γ = 1 ∨ γ = RealisationAux.negC E₀ := by
      by_contra hcon
      push Not at hcon
      haveI := Fintype.ofFinite (MulAction.stabilizer (VariableChange K) E₀)
      have h3 : 2 < Nat.card (MulAction.stabilizer (VariableChange K) E₀) := by
        rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
        exact ⟨⟨1, one_mem _⟩, ⟨RealisationAux.negC E₀, RealisationAux.negC_smul E₀⟩, ⟨γ, hγ⟩,
          fun h => RealisationAux.negC_ne_one E₀ (congrArg Subtype.val h).symm,
          fun h => hcon.1 (congrArg Subtype.val h).symm,
          fun h => hcon.2 (congrArg Subtype.val h).symm⟩
      omega
    rcases hγ' with rfl | rfl
    · exact ⟨1, h1D, Or.inl fun P => by rw [← hρ1]; exact hc5 1 h1D P⟩
    · refine ⟨1, h1D, Or.inr fun P => ?_⟩
      have h := hHEqneg 1 h1D P
      rwa [hρ1, mul_one] at h

omit [IsAlgClosed K] [Fact q.Prime] [CharP K q] [E₀.IsElliptic] in

private theorem correct_frobenius (M : Type u) [Field M] [DecidableEq M] [Algebra K M] (t : M)
    (W₀ : Place K M)
    (θ : ((genCurve K t).baseChange M).toAffine.Point →+ E₀.toAffine.Point)
    (h6 : ∀ γ : VariableChange K, γ • E₀ = E₀ →
      ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
        ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
         (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
            (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P)))))
    (fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point)
    (frM : SemilinearAut K M) (hfrK : ∀ a : K, frM • (algebraMap K M a) = algebraMap K M (a ^ q))
    (hfrt : frM • t = t) (hfrW : frM • W₀ = W₀)
    (frE : ((genCurve K t).baseChange M).toAffine.Point →+ ((genCurve K t).baseChange M).toAffine.Point)
    (hfrE : ∀ (x y : M) (h : ((genCurve K t).baseChange M).toAffine.Nonsingular x y),
      ∃ h', frE (.some x y h) = .some (frM • x) (frM • y) h')
    (α : VariableChange K) (hα : α • E₀ = E₀)
    (hαθ : ∀ P, HEq (Point.vcInvFun α E₀.toAffine (fr₀ (θ P))) (θ (frE P))) :
    ∃ (frM' : SemilinearAut K M)
      (frE' : ((genCurve K t).baseChange M).toAffine.Point →+ ((genCurve K t).baseChange M).toAffine.Point) (ε : ℤ),
      (∀ a : K, frM' • (algebraMap K M a) = algebraMap K M (a ^ q)) ∧ frM' • t = t ∧ frM' • W₀ = W₀ ∧
      (∀ (x y : M) (h : ((genCurve K t).baseChange M).toAffine.Nonsingular x y),
        ∃ h', frE' (.some x y h) = .some (frM' • x) (frM' • y) h') ∧
      (ε = 1 ∨ ε = -1) ∧
      (∀ P : ((genCurve K t).baseChange M).toAffine.Point, N • P = 0 → θ (frE' P) = ε • fr₀ (θ P)) := by
  have hαinv : α⁻¹ • E₀ = E₀ := inv_smul_eq_iff.mpr hα.symm
  obtain ⟨σ₁, hσ₁W, hσ₁⟩ := h6 α⁻¹ hαinv

  have hK' : ∀ a : K, (SemilinearAut.ofAlgAut (σ₁.restrictScalars K) * frM) • algebraMap K M a =
      algebraMap K M (a ^ q) := by
    intro a
    rw [mul_smul, hfrK, SemilinearAut.ofAlgAut_smul]
    exact (σ₁.restrictScalars K).commutes _
  have ht' : (SemilinearAut.ofAlgAut (σ₁.restrictScalars K) * frM) • t = t := by
    rw [mul_smul, hfrt]
    exact ofAlgAut_smul_t σ₁
  have hW' : (SemilinearAut.ofAlgAut (σ₁.restrictScalars K) * frM) • W₀ = W₀ := by
    rw [mul_smul, hfrW, hσ₁W]
  have hE' : ∀ (x y : M) (h : ((genCurve K t).baseChange M).toAffine.Nonsingular x y),
      ∃ h', (WeierstrassCurve.Affine.Point.map (σ₁ : M →ₐ[K⟮t⟯] M)).comp frE (.some x y h) =
        .some ((SemilinearAut.ofAlgAut (σ₁.restrictScalars K) * frM) • x)
          ((SemilinearAut.ofAlgAut (σ₁.restrictScalars K) * frM) • y) h' := by
    intro x y h
    obtain ⟨h', hP⟩ := hfrE x y h
    rw [AddMonoidHom.comp_apply, hP, WeierstrassCurve.Affine.Point.map_some]
    exact ⟨_, rfl⟩

  have hcancel : ∀ X : E₀.toAffine.Point,
      castPt hαinv (Point.vcInvFun α⁻¹ E₀.toAffine (castPt hα (Point.vcInvFun α E₀.toAffine X))) = X := by
    intro X
    rcases X with _ | ⟨x, y, h⟩
    · show castPt hαinv (Point.vcInvFun α⁻¹ E₀.toAffine (castPt hα 0)) = 0
      rw [castPt_zero, Point.vcInvFun_zero, castPt_zero]
    · rw [vcInvFun_some, castPt_some, vcInvFun_some, castPt_some]
      refine Point.some_congr' ?_ ?_ _ _
      · rw [← vcXInv_mul, inv_mul_cancel, vcXInv_one]
      · rw [← vcYInv_mul, inv_mul_cancel, vcYInv_one]
  have hθfrE : ∀ P, θ (frE P) = castPt hα (Point.vcInvFun α E₀.toAffine (fr₀ (θ P))) :=
    fun P => eq_castPt_of_heq hα (hαθ P)
  rcases hσ₁ with h | h
  · refine ⟨_, _, 1, hK', ht', hW', hE', Or.inl rfl, fun P _ => ?_⟩
    rw [AddMonoidHom.comp_apply, eq_castPt_of_heq hαinv (h (frE P)), hθfrE, hcancel, one_zsmul]
  · refine ⟨_, _, -1, hK', ht', hW', hE', Or.inr rfl, fun P _ => ?_⟩
    have h1 := eq_castPt_of_heq hαinv (h (frE P))
    rw [AddMonoidHom.comp_apply, neg_eq_iff_eq_neg.mp h1, hθfrE, hcancel, neg_one_zsmul]

end Body
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux"

end ModularCurve.SigmaSpine
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData" namespace SigmaSpine end ModularCurve.SigmaSpine
p2m_open_scoped "ModularCurve" in
open ModularCurve.SigmaSpine in

private theorem ModularCurve.SigmaSpine.spine
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
    (N : ℕ) (hN : (N : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hfr : E₀.map (frobenius K q) = E₀)
    (hdesc : DescentContract K q N E₀)
    (hred : ReductionContract K E₀)
    (hdict : DictionaryContract K q N hN) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M)
      (W₀ : Place K M) (_ : 0 < W₀.ord (t - algebraMap K M E₀.j))
      (θ : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ E₀.toAffine.Point)
      (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K)
      (Φ : {H : AddSubgroup ((WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
              IsAddCyclic H ∧ Nat.card H = N} ≃
            {ψ : modularFunctionFieldFullC K N →ₐ[K] M // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t})
      (frM : SemilinearAut K M)
      (frE : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point)
      (fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point) (ε : ℤ),
      Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2 ∧
      (∀ (n : ℕ) (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          ¬ q ∣ n → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ • E₀ = E₀) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∧
      (∀ γ : VariableChange K, γ • E₀ = E₀ →
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
             (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))))) ∧
      (∀ (σ : M ≃ₐ[K⟮t⟯] M) (H H' : {H : AddSubgroup ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M)) →
          ((Φ H').1 : modularFunctionFieldFullC K N →ₐ[K] M) =
            ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp (Φ H).1) ∧
      (∀ a : K, frM • (algebraMap K M a) = algebraMap K M (a ^ q)) ∧
      frM • t = t ∧
      frM • W₀ = W₀ ∧
      (∀ (x y : M) (h : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Nonsingular x y),
        ∃ h', frE (.some x y h) = .some (frM • x) (frM • y) h') ∧
      (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y), ∃ h', fr₀ (.some x y h) = .some (x ^ q) (y ^ q) h') ∧
      (ε = 1 ∨ ε = -1) ∧
      (∀ P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point,
        N • P = 0 → θ (frE P) = ε • fr₀ (θ P)) ∧
      (∀ (H H' : {H : AddSubgroup ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map frE →
          ∀ (d : ℕ) [NeZero d] (hd : d ∣ N),
            (Φ H').1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ =
              frM • ((Φ H).1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩)) := by
  obtain ⟨M, _, _, _, t, ht, hfd, hgal, hcardN, ⟨m, hmK, hm3, hmcard, hmodel⟩, hfrob⟩ := hdesc
  obtain ⟨W₀, hW₀⟩ := exists_place_over K M t ht E₀.j
  obtain ⟨θ, ρ, hc2, hc3, hc4, hc5, hc7, hdefect⟩ := exists_theta_rho K q E₀ hfr M t ht W₀ hW₀ hmK hmodel hred
  have h6 := realisation K q E₀ M t ht W₀ hW₀ hmK hm3 hmcard hmodel θ ρ hc2 hc3 hc4 hc5 hc7
  obtain ⟨frM₀, hfrK₀, hfrt₀, hfrW₀⟩ := hfrob W₀ hW₀
  obtain ⟨frE₀, hfrE₀⟩ := exists_frobPt K M t ht frM₀ hfrt₀
  obtain ⟨α, hα, hαθ⟩ := hdefect frM₀ hfrK₀ hfrt₀ hfrW₀ frE₀ hfrE₀ (frobPt K q E₀ hfr) (frobPt_some K q E₀ hfr)
  obtain ⟨frM, frE, ε, hfrK, hfrt, hfrW, hfrE, hε, hF4⟩ :=
    correct_frobenius K q N E₀ M t W₀ θ h6 (frobPt K q E₀ hfr) frM₀ hfrK₀ hfrt₀ hfrW₀ frE₀ hfrE₀ α hα hαθ
  obtain ⟨Φ, hΦA, hΦF5⟩ := hdict M _ _ _ t ht hfd hgal hcardN frM hfrK hfrt frE hfrE
  exact ⟨M, _, _, _, t, ht, hfd, hgal, W₀, hW₀, θ, ρ, Φ, frM, frE, frobPt K q E₀ hfr, ε, hcardN, hc2, hc3, hc5, h6,
    hΦA, hfrK, hfrt, hfrW, hfrE, frobPt_some K q E₀ hfr, hε, hF4, hΦF5⟩

end SigmaSpinePart
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

section SigmaDescentPart

universe u

open ModularCurve.SigmaSpine (genCurve FrobContract baseChange_genCurve)

p2m_open "AlgebraicCurve WeierstrassCurve~map_veluGy~map_veluGx"
open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace SigmaDescent
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

noncomputable section

section Frame

variable (K : Type u) [Field K]

private abbrev Ω : Type u := AlgebraicClosure (RatFunc K)

private noncomputable abbrev xΩ : Ω K := algebraMap (RatFunc K) (Ω K) RatFunc.X

private abbrev F₀ : Subfield (Ω K) := Subfield.closure {xΩ K}

private noncomputable def x₀ : F₀ K := ⟨xΩ K, Subfield.subset_closure rfl⟩

private noncomputable abbrev Ω₀ : IntermediateField (F₀ K) (Ω K) := algebraicClosure (F₀ K) (Ω K)

private scoped instance : IsAlgClosed (Ω₀ K) := IsAlgClosure.isAlgClosed (F₀ K)

open scoped Classical in

private noncomputable abbrev Ebase : WeierstrassCurve (F₀ K) := ofJ (x₀ K)

open scoped Classical in

private noncomputable abbrev EF : WeierstrassCurve (RatFunc K) := ofJ RatFunc.X

private theorem map_ofJNe0Or1728 {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) (j : R) :
    (ofJNe0Or1728 j).map f = ofJNe0Or1728 (f j) := by
  ext <;> simp [ofJNe0Or1728, map_ofNat]

private theorem ratFuncX_ne_1728 [Nontrivial K] : (RatFunc.X : RatFunc K) ≠ 1728 := by
  intro h
  rw [← RatFunc.algebraMap_X, ← map_ofNat (algebraMap (Polynomial K) (RatFunc K)) 1728] at h
  have h' := RatFunc.algebraMap_injective K h
  have hdeg := congrArg Polynomial.natDegree h'
  simp at hdeg

private theorem xΩ_ne_zero : xΩ K ≠ 0 := (map_ne_zero _).mpr RatFunc.X_ne_zero

private theorem xΩ_ne_1728 : xΩ K ≠ 1728 := by
  intro h
  rw [xΩ, ← map_ofNat (algebraMap (RatFunc K) (Ω K)) 1728] at h
  exact ratFuncX_ne_1728 K ((algebraMap (RatFunc K) (Ω K)).injective h)

private theorem x₀_ne_zero : x₀ K ≠ 0 := fun h => xΩ_ne_zero K (congrArg Subtype.val h)

private theorem x₀_ne_1728 : x₀ K ≠ 1728 := fun h => xΩ_ne_1728 K (congrArg Subtype.val h)

open scoped Classical in
private theorem Ebase_eq : Ebase K = ofJNe0Or1728 (x₀ K) := ofJ_ne_0_ne_1728 _ (x₀_ne_zero K) (x₀_ne_1728 K)

open scoped Classical in
private theorem EF_eq : EF K = ofJNe0Or1728 (RatFunc.X : RatFunc K) :=
  ofJ_ne_0_ne_1728 _ RatFunc.X_ne_zero (ratFuncX_ne_1728 K)

private noncomputable def _root_.ModularCurve.SigmaDescent.lift (L₀ : IntermediateField (F₀ K) (Ω₀ K)) : IntermediateField (RatFunc K) (Ω K) :=
  IntermediateField.adjoin (RatFunc K) ((fun z : Ω₀ K => (z : Ω K)) '' (L₀ : Set (Ω₀ K)))

p2m_export "ModularCurve.SigmaDescent" "lift"
private theorem mem_lift_of_mem (L₀ : IntermediateField (F₀ K) (Ω₀ K)) {z : Ω₀ K} (hz : z ∈ L₀) :
    (z : Ω K) ∈ lift K L₀ :=
  IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩

private noncomputable def toLift (L₀ : IntermediateField (F₀ K) (Ω₀ K)) : L₀ →+* lift K L₀ where
  toFun z := ⟨((z : Ω₀ K) : Ω K), mem_lift_of_mem K L₀ z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem toLift_injective (L₀ : IntermediateField (F₀ K) (Ω₀ K)) : Function.Injective (toLift K L₀) :=
  (toLift K L₀).injective

end Frame
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

section Transfers

variable (K : Type u) [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in

private theorem F₀_le_fieldRange : F₀ K ≤ (algebraMap (RatFunc K) (Ω K)).fieldRange :=
  Subfield.closure_le.mpr (by
    rintro _ rfl
    exact ⟨RatFunc.X, rfl⟩)

private def pieceEmb (L₀ : IntermediateField (F₀ K) (Ω₀ K)) : L₀ →ₐ[F₀ K] Ω K :=
  (Ω₀ K).val.comp L₀.val

omit [IsAlgClosed K] in
private theorem lift_generators_eq_range (L₀ : IntermediateField (F₀ K) (Ω₀ K)) :
    (fun z : Ω₀ K => (z : Ω K)) '' (L₀ : Set (Ω₀ K)) = Set.range (pieceEmb K L₀) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.2, rfl⟩

omit [IsAlgClosed K] in

private theorem exists_lift_eq_adjoin_rootSet (L₀ : IntermediateField (F₀ K) (Ω₀ K)) [FiniteDimensional (F₀ K) L₀]
    [IsGalois (F₀ K) L₀] :
    ∃ qq : Polynomial (RatFunc K), qq.Separable ∧ (qq.map (algebraMap (RatFunc K) (Ω K))).Splits ∧
      lift K L₀ = IntermediateField.adjoin (RatFunc K) (qq.rootSet (Ω K)) := by
  obtain ⟨pp, hpsep, hpsplit⟩ := IsGalois.is_separable_splitting_field (F₀ K) L₀
  haveI : Polynomial.IsSplittingField (F₀ K) L₀ pp := hpsplit

  have hlifts : pp.map (algebraMap (F₀ K) (Ω K)) ∈ Polynomial.lifts (algebraMap (RatFunc K) (Ω K)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    have hmem : ((pp.coeff n : F₀ K) : Ω K) ∈ (algebraMap (RatFunc K) (Ω K)).fieldRange :=
      F₀_le_fieldRange K (pp.coeff n).2
    obtain ⟨f, hf⟩ := RingHom.mem_fieldRange.mp hmem
    exact ⟨f, hf⟩
  obtain ⟨qq, hqq⟩ := (Polynomial.mem_lifts _).mp hlifts
  have hroot : qq.rootSet (Ω K) = pp.rootSet (Ω K) := by
    ext a
    simp only [Polynomial.mem_rootSet', Polynomial.aeval_def, ← Polynomial.eval_map, hqq]
  refine ⟨qq, ?_, ?_, ?_⟩
  ·
    have hsep' : (qq.map (algebraMap (RatFunc K) (Ω K))).Separable := by
      rw [hqq]
      exact hpsep.map
    exact (Polynomial.separable_map _).mp hsep'
  ·
    rw [hqq]
    have h1 : pp.map (algebraMap (F₀ K) (Ω K)) =
        (pp.map (algebraMap (F₀ K) L₀)).map (pieceEmb K L₀ : L₀ →+* Ω K) := by
      rw [Polynomial.map_map, (pieceEmb K L₀).comp_algebraMap]
    rw [h1]
    exact (Polynomial.IsSplittingField.splits L₀ pp).map (pieceEmb K L₀ : L₀ →+* Ω K)
  ·
    rw [hroot]
    have hrange := Polynomial.IsSplittingField.adjoin_rootSet_eq_range L₀ pp (pieceEmb K L₀)
    have hgen : (fun z : Ω₀ K => (z : Ω K)) '' (L₀ : Set (Ω₀ K)) =
        (Algebra.adjoin (F₀ K) (pp.rootSet (Ω K)) : Set (Ω K)) := by
      rw [lift_generators_eq_range, hrange]
      rfl
    unfold lift
    rw [hgen]
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]

      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem r hr => exact IntermediateField.subset_adjoin _ _ hr
      | algebraMap r =>
          obtain ⟨f, hf⟩ := RingHom.mem_fieldRange.mp (F₀_le_fieldRange K r.2)
          show (r : Ω K) ∈ IntermediateField.adjoin (RatFunc K) (pp.rootSet (Ω K))
          rw [← hf]
          exact IntermediateField.algebraMap_mem _ f
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
    · exact IntermediateField.adjoin.mono _ _ _ Algebra.subset_adjoin

omit [IsAlgClosed K] in

private theorem finiteDimensional_lift (L₀ : IntermediateField (F₀ K) (Ω₀ K)) [FiniteDimensional (F₀ K) L₀]
    [IsGalois (F₀ K) L₀] : FiniteDimensional (RatFunc K) (lift K L₀) := by
  obtain ⟨qq, -, hsplit, hlift⟩ := exists_lift_eq_adjoin_rootSet K L₀
  rw [hlift]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  exact Polynomial.IsSplittingField.finiteDimensional _ qq

omit [IsAlgClosed K] in

private theorem isGalois_lift (L₀ : IntermediateField (F₀ K) (Ω₀ K)) [FiniteDimensional (F₀ K) L₀]
    [IsGalois (F₀ K) L₀] : IsGalois (RatFunc K) (lift K L₀) := by
  obtain ⟨qq, hsep, hsplit, hlift⟩ := exists_lift_eq_adjoin_rootSet K L₀
  rw [hlift]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  exact IsGalois.of_separable_splitting_field hsep

omit [IsAlgClosed K] in

private theorem baseChange_EF_eq_map (L₀ L₁ : IntermediateField (F₀ K) (Ω₀ K)) (j : L₀ →+* lift K L₁)
    (hj : ∀ z : L₀, ((j z : lift K L₁) : Ω K) = ((z : Ω₀ K) : Ω K)) :
    (EF K).baseChange (lift K L₁) = ((Ebase K).baseChange L₀).map j := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, EF_eq, Ebase_eq, map_ofJNe0Or1728,
    map_ofJNe0Or1728, map_ofJNe0Or1728]
  congr 1
  apply Subtype.ext
  rw [hj]
  rfl

omit [IsAlgClosed K] in

private theorem baseChange_EF_eq (L₀ : IntermediateField (F₀ K) (Ω₀ K)) :
    (EF K).baseChange (lift K L₀) = ((Ebase K).baseChange L₀).map (toLift K L₀) :=
  baseChange_EF_eq_map K L₀ L₀ (toLift K L₀) fun _ => rfl

private def toLiftOfLE {L₀ L₁ : IntermediateField (F₀ K) (Ω₀ K)} (h : L₀ ≤ L₁) : L₀ →+* lift K L₁ :=
  (toLift K L₁).comp (IntermediateField.inclusion h).toRingHom

omit [IsAlgClosed K] in
private theorem coe_toLiftOfLE {L₀ L₁ : IntermediateField (F₀ K) (Ω₀ K)} (h : L₀ ≤ L₁) (z : L₀) :
    ((toLiftOfLE K h z : lift K L₁) : Ω K) = ((z : Ω₀ K) : Ω K) := rfl

private def _root_.ModularCurve.SigmaDescent.castAddHom {k : Type u} [Field k] [DecidableEq k] {V V' : WeierstrassCurve k} (h : V' = V) :
    V'.toAffine.Point →+ V.toAffine.Point := by
  subst h; exact AddMonoidHom.id _

p2m_export "ModularCurve.SigmaDescent" "castAddHom"
private theorem castAddHom_injective {k : Type u} [Field k] [DecidableEq k] {V V' : WeierstrassCurve k} (h : V' = V) :
    Function.Injective (castAddHom h) := by
  subst h; exact fun _ _ hpq => hpq

omit [IsAlgClosed K] in

private theorem exists_restrict {L₀ L₁ : IntermediateField (F₀ K) (Ω₀ K)} (h : L₀ ≤ L₁) [Normal (F₀ K) L₀]
    (σ : lift K L₁ ≃ₐ[RatFunc K] lift K L₁) :
    ∃ σ₀ : L₀ ≃ₐ[F₀ K] L₀, ∀ z : L₀, σ (toLiftOfLE K h z) = toLiftOfLE K h (σ₀ z) := by

  have hfix : ∀ c : F₀ K,
      ((σ (toLiftOfLE K h (algebraMap (F₀ K) L₀ c)) : lift K L₁) : Ω K) = algebraMap (F₀ K) (Ω K) c := by
    intro c
    obtain ⟨f₀, hf₀⟩ := RingHom.mem_fieldRange.mp (F₀_le_fieldRange K c.2)
    have he : toLiftOfLE K h (algebraMap (F₀ K) L₀ c) = algebraMap (RatFunc K) (lift K L₁) f₀ :=
      Subtype.ext hf₀.symm
    rw [he, σ.commutes f₀]
    exact hf₀

  let g : L₀ →ₐ[F₀ K] Ω K :=
    ⟨(lift K L₁).val.toRingHom.comp
      (σ.toAlgHom.toRingHom.comp (toLiftOfLE K h)), hfix⟩

  letI : Algebra L₀ L₀ := Algebra.id L₀
  letI : Algebra L₀ (Ω K) := (pieceEmb K L₀).toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq (R := F₀ K) (S := L₀) (A := L₀) fun _ => rfl
  haveI := IsScalarTower.of_algebraMap_eq (R := F₀ K) (S := L₀) (A := Ω K)
    fun c => ((pieceEmb K L₀).commutes c).symm
  exact ⟨g.restrictNormal' L₀, fun z => Subtype.ext (g.restrictNormal_commutes L₀ z).symm⟩

private theorem castAddHom_some {k : Type u} [Field k] [DecidableEq k] {V V' : WeierstrassCurve k} (hV : V' = V)
    {x y : k} (hxy : V'.toAffine.Nonsingular x y) :
    castAddHom hV (.some x y hxy) = .some x y (hV ▸ hxy) := by
  subst hV; rfl

omit [IsAlgClosed K] in

private theorem torsion_fixed_restrict {L₀ L₁ : IntermediateField (F₀ K) (Ω₀ K)} (h : L₀ ≤ L₁) [DecidableEq (Ω K)] {n : ℕ}
    (σ : lift K L₁ ≃ₐ[RatFunc K] lift K L₁) (σ₀ : L₀ ≃ₐ[F₀ K] L₀)
    (hcomm : ∀ z : L₀, σ (toLiftOfLE K h z) = toLiftOfLE K h (σ₀ z))
    (hσ : ∀ P : ((EF K).baseChange (lift K L₁)).toAffine.Point, n • P = 0 →
      WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P) :
    ∀ P : ((Ebase K).baseChange L₀).toAffine.Point, n • P = 0 →
      WeierstrassCurve.Affine.Point.map σ₀.toAlgHom P = P := by
  intro P hP
  have hEE := (baseChange_EF_eq_map K L₀ L₁ (toLiftOfLE K h) (coe_toLiftOfLE K h)).symm
  let f₁ : ((Ebase K).baseChange L₀).toAffine.Point →+ ((EF K).baseChange (lift K L₁)).toAffine.Point :=
    (castAddHom hEE).comp (WeierstrassCurve.mapPointHom (toLiftOfLE K h))
  have hf₁ : Function.Injective f₁ := fun a b hab =>
    WeierstrassCurve.mapPoint_injective (toLiftOfLE K h) (castAddHom_injective hEE hab)

  have key : ∀ Q : ((Ebase K).baseChange L₀).toAffine.Point,
      WeierstrassCurve.Affine.Point.map σ.toAlgHom (f₁ Q) =
        f₁ (WeierstrassCurve.Affine.Point.map σ₀.toAlgHom Q) := by
    rintro (_ | ⟨x, y, hxy⟩)
    · show WeierstrassCurve.Affine.Point.map σ.toAlgHom (f₁ 0) =
        f₁ (WeierstrassCurve.Affine.Point.map σ₀.toAlgHom 0)
      simp only [map_zero]
    · show WeierstrassCurve.Affine.Point.map σ.toAlgHom
          (castAddHom hEE (WeierstrassCurve.mapPoint (toLiftOfLE K h) (.some x y hxy))) =
        castAddHom hEE (WeierstrassCurve.mapPoint (toLiftOfLE K h)
          (WeierstrassCurve.Affine.Point.map σ₀.toAlgHom (.some x y hxy)))

      rw [WeierstrassCurve.mapPoint_some, castAddHom_some, WeierstrassCurve.Affine.Point.map_some,
        WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.mapPoint_some, castAddHom_some]
      exact WeierstrassCurve.Affine.Point.some_congr' (hcomm x) (hcomm y) _ _
  have hP' : n • f₁ P = 0 := by rw [← map_nsmul, hP, map_zero]
  exact hf₁ ((key P).symm.trans (hσ (f₁ P) hP'))

omit [IsAlgClosed K] in

private theorem card_torsion_closure {n : ℕ} (hn : (n : K) ≠ 0) [DecidableEq (Ω K)] :
    Nat.card {P : ((EF K).baseChange (Ω K)).toAffine.Point // n • P = 0} = n ^ 2 := by
  have hnΩ : (n : Ω K) ≠ 0 := by
    rw [show (n : Ω K) = algebraMap K (Ω K) n by norm_num]
    exact (map_ne_zero _).mpr hn
  obtain ⟨eΩ⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω K) (EF K) hnΩ
  have e2 : {P : ((EF K).baseChange (Ω K)).toAffine.Point // n • P = 0} ≃
      Submodule.torsionBy ℤ ((EF K).baseChange (Ω K)).toAffine.Point n :=
    Equiv.subtypeEquivRight fun P => by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  rw [Nat.card_congr e2, ← Nat.card_congr eΩ.toEquiv, Nat.card_prod, Nat.card_zmod, sq]

omit [IsAlgClosed K] in

private theorem card_torsion_lift_eq {n : ℕ} (hn : (n : K) ≠ 0) (L₀ L₁ : IntermediateField (F₀ K) (Ω₀ K))
    (hXY : L₀ ≤ L₁) [DecidableEq (Ω K)]
    (hX : Nat.card {P : ((Ebase K).baseChange L₀).toAffine.Point // n • P = 0} = n ^ 2) :
    Nat.card {P : ((EF K).baseChange (lift K L₁)).toAffine.Point // n • P = 0} = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)

  let f₁ : ((Ebase K).baseChange L₀).toAffine.Point →+ ((EF K).baseChange (lift K L₁)).toAffine.Point :=
    (castAddHom (baseChange_EF_eq_map K L₀ L₁ (toLiftOfLE K hXY) (coe_toLiftOfLE K hXY)).symm).comp
      (WeierstrassCurve.mapPointHom (toLiftOfLE K hXY))
  have hf₁ : Function.Injective f₁ :=
    (castAddHom_injective _).comp (WeierstrassCurve.mapPoint_injective (toLiftOfLE K hXY))
  let g₁ : {P : ((Ebase K).baseChange L₀).toAffine.Point // n • P = 0} →
      {P : ((EF K).baseChange (lift K L₁)).toAffine.Point // n • P = 0} :=
    fun P => ⟨f₁ P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg₁ : Function.Injective g₁ := fun P Q h => Subtype.ext (hf₁ (congrArg Subtype.val h))

  let f₂ : ((EF K).baseChange (lift K L₁)).toAffine.Point →+ ((EF K).baseChange (Ω K)).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (IntermediateField.val (lift K L₁))
  have hf₂ : Function.Injective f₂ := WeierstrassCurve.Affine.Point.map_injective _
  let g₂ : {P : ((EF K).baseChange (lift K L₁)).toAffine.Point // n • P = 0} →
      {P : ((EF K).baseChange (Ω K)).toAffine.Point // n • P = 0} :=
    fun P => ⟨f₂ P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg₂ : Function.Injective g₂ := fun P Q h => Subtype.ext (hf₂ (congrArg Subtype.val h))
  have hTΩ := card_torsion_closure K hn
  haveI : Finite {P : ((EF K).baseChange (Ω K)).toAffine.Point // n • P = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hTΩ]; exact pow_ne_zero _ hn0)
  haveI : Finite {P : ((EF K).baseChange (lift K L₁)).toAffine.Point // n • P = 0} := Finite.of_injective g₂ hg₂
  apply le_antisymm
  · calc Nat.card {P : ((EF K).baseChange (lift K L₁)).toAffine.Point // n • P = 0}
        ≤ Nat.card {P : ((EF K).baseChange (Ω K)).toAffine.Point // n • P = 0} :=
          Nat.card_le_card_of_injective g₂ hg₂
      _ = n ^ 2 := hTΩ
  · calc n ^ 2 = Nat.card {P : ((Ebase K).baseChange L₀).toAffine.Point // n • P = 0} := hX.symm
      _ ≤ Nat.card {P : ((EF K).baseChange (lift K L₁)).toAffine.Point // n • P = 0} :=
          Nat.card_le_card_of_injective g₁ hg₁

private def comapHom {L L' : Type u} [Field L] [Field L'] (A : ValuationSubring L') (j : L →+* L') :
    A.comap j →+* A where
  toFun x := ⟨j (x : L), ValuationSubring.mem_comap.mp x.2⟩
  map_one' := Subtype.ext (by simp only [OneMemClass.coe_one, map_one])
  map_mul' x y := Subtype.ext (by simp only [MulMemClass.coe_mul, map_mul])
  map_zero' := Subtype.ext (by simp only [ZeroMemClass.coe_zero, map_zero])
  map_add' x y := Subtype.ext (by simp only [AddMemClass.coe_add, map_add])

private theorem subtype_comp_comapHom {L L' : Type u} [Field L] [Field L'] (A : ValuationSubring L') (j : L →+* L') :
    A.subtype.comp (comapHom A j) = j.comp (A.comap j).subtype :=
  RingHom.ext fun _ => rfl

private theorem isUnit_natCast_comap {L L' : Type u} [Field L] [Field L'] (A : ValuationSubring L') (j : L →+* L')
    (m : ℕ) (hm : IsUnit ((m : ℕ) : A)) : IsUnit ((m : ℕ) : A.comap j) := by
  obtain ⟨u, hu⟩ := hm
  have h1 : ((m : ℕ) : A) * ((u⁻¹ : Aˣ) : A) = 1 := by rw [← hu]; exact u.mul_inv
  have h1' : ((m : ℕ) : L') * A.subtype ((u⁻¹ : Aˣ) : A) = 1 := by
    simpa only [map_mul, map_natCast, map_one] using congrArg A.subtype h1
  have hm0' : ((m : ℕ) : L') ≠ 0 := left_ne_zero_of_mul_eq_one h1'
  have hm0 : ((m : ℕ) : L) ≠ 0 := by
    intro h0
    apply hm0'
    rw [← map_natCast j, h0, map_zero]
  have hmem : ((m : ℕ) : L)⁻¹ ∈ A.comap j := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast, inv_eq_of_mul_eq_one_right h1']
    exact ((u⁻¹ : Aˣ) : A).2
  refine ⟨⟨((m : ℕ) : A.comap j), ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hm0)
  · exact Subtype.ext (inv_mul_cancel₀ hm0)

end Transfers
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

section RouteDescent

open scoped Pointwise

variable {L L' : Type u} [Field L] [Field L'] (A : ValuationSubring L') (j : L →+* L')

private theorem isUnit_of_comapHom (x : A.comap j) (hx : IsUnit (comapHom A j x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx
  have h1 : comapHom A j x * ((u⁻¹ : Aˣ) : A) = 1 := by rw [← hu]; exact u.mul_inv
  have h1' : A.subtype (comapHom A j x) * A.subtype ((u⁻¹ : Aˣ) : A) = 1 := by
    simpa only [map_mul, map_one] using congrArg A.subtype h1
  have hx0 : (x : L) ≠ 0 := by
    rintro h0
    have hx0' : comapHom A j x = 0 := Subtype.ext (by show j (x : L) = 0; rw [h0, map_zero])
    rw [hx0', map_zero, zero_mul] at h1'
    exact zero_ne_one h1'
  have hmem : (x : L)⁻¹ ∈ A.comap j := by
    rw [ValuationSubring.mem_comap, map_inv₀]
    have : j (x : L) = A.subtype (comapHom A j x) := rfl
    rw [this, inv_eq_of_mul_eq_one_right h1']
    exact ((u⁻¹ : Aˣ) : A).2
  refine ⟨⟨x, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

private scoped instance : IsLocalHom (comapHom A j) := ⟨fun x hx => isUnit_of_comapHom A j x hx⟩

private noncomputable def resMap : IsLocalRing.ResidueField (A.comap j) →+* IsLocalRing.ResidueField A :=
  IsLocalRing.ResidueField.map (comapHom A j)

private theorem resMap_residue (x : A.comap j) :
    resMap A j (IsLocalRing.residue _ x) = IsLocalRing.residue A (comapHom A j x) :=
  IsLocalRing.ResidueField.map_residue _ x

private theorem exists_descend (g : VariableChange A) (v : VariableChange L) (hg : g.map A.subtype = v.map j) :
    ∃ g₀ : VariableChange (A.comap j), g₀.map (A.comap j).subtype = v ∧ g₀.map (comapHom A j) = g := by
  have hu : A.subtype g.u = j v.u := congrArg (fun C : VariableChange L' => (C.u : L')) hg
  have hr : A.subtype g.r = j v.r := congrArg VariableChange.r hg
  have hs : A.subtype g.s = j v.s := congrArg VariableChange.s hg
  have ht : A.subtype g.t = j v.t := congrArg VariableChange.t hg
  have mu : (v.u : L) ∈ A.comap j := ValuationSubring.mem_comap.mpr (hu ▸ (g.u : A).2)
  have mr : v.r ∈ A.comap j := ValuationSubring.mem_comap.mpr (hr ▸ g.r.2)
  have ms : v.s ∈ A.comap j := ValuationSubring.mem_comap.mpr (hs ▸ g.s.2)
  have mt : v.t ∈ A.comap j := ValuationSubring.mem_comap.mpr (ht ▸ g.t.2)
  have hcu : comapHom A j ⟨v.u, mu⟩ = (g.u : A) := Subtype.ext hu.symm
  have hunit : IsUnit (⟨(v.u : L), mu⟩ : A.comap j) := isUnit_of_comapHom A j _ (hcu ▸ g.u.isUnit)
  have hcr : comapHom A j ⟨v.r, mr⟩ = g.r := Subtype.ext hr.symm
  have hcs : comapHom A j ⟨v.s, ms⟩ = g.s := Subtype.ext hs.symm
  have hct : comapHom A j ⟨v.t, mt⟩ = g.t := Subtype.ext ht.symm
  refine ⟨⟨hunit.unit, ⟨v.r, mr⟩, ⟨v.s, ms⟩, ⟨v.t, mt⟩⟩, ?_, ?_⟩
  · refine VariableChange.ext (Units.ext ?_) rfl rfl rfl
    show ((hunit.unit : A.comap j) : L) = (v.u : L)
    rw [IsUnit.unit_spec]
  · refine VariableChange.ext (Units.ext ?_) hcr hcs hct
    show comapHom A j (hunit.unit : A.comap j) = (g.u : A)
    rw [IsUnit.unit_spec, hcu]

private theorem map_residue_eq_one_of_map (g₀ : VariableChange (A.comap j))
    (h : (g₀.map (comapHom A j)).map (IsLocalRing.residue A) = 1) :
    g₀.map (IsLocalRing.residue (A.comap j)) = 1 := by
  have hinj := (resMap A j).injective
  have key : ∀ x : A.comap j, IsLocalRing.residue A (comapHom A j x) = 1 → IsLocalRing.residue _ x = 1 := by
    intro x hx
    apply hinj
    rw [resMap_residue, hx, map_one]
  have key0 : ∀ x : A.comap j, IsLocalRing.residue A (comapHom A j x) = 0 → IsLocalRing.residue _ x = 0 := by
    intro x hx
    apply hinj
    rw [resMap_residue, hx, map_zero]
  have hu := congrArg (fun C : VariableChange (IsLocalRing.ResidueField A) => (C.u : IsLocalRing.ResidueField A)) h
  have hr := congrArg VariableChange.r h
  have hs := congrArg VariableChange.s h
  have ht := congrArg VariableChange.t h
  exact VariableChange.ext (Units.ext (key _ hu)) (key0 _ hr) (key0 _ hs) (key0 _ ht)

end RouteDescent
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

section DecompDescent

open scoped Pointwise

private theorem mem_decompositionSubgroup_iff_forall {k F : Type u} [Field k] [Field F] [Algebra k F]
    (B : ValuationSubring F) (τ : F ≃ₐ[k] F) :
    τ ∈ B.decompositionSubgroup k ↔ ∀ x : F, x ∈ B ↔ τ x ∈ B := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      have : τ • x ∈ τ • B := ValuationSubring.smul_mem_pointwise_smul_iff.mpr hx
      rwa [h] at this
    · intro hx
      rw [← h] at hx
      exact ValuationSubring.smul_mem_pointwise_smul_iff.mp hx
  · intro h
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, h (τ⁻¹ x),
      AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

private theorem mem_inertiaSubgroup_iff_forall {k F : Type u} [Field k] [Field F] [Algebra k F] (B : ValuationSubring F)
    (τ : B.decompositionSubgroup k) :
    τ ∈ B.inertiaSubgroup k ↔ ∀ b : B, IsLocalRing.residue B (τ • b) = IsLocalRing.residue B b := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  constructor
  · intro h b
    have := congrArg (fun e : RingAut (IsLocalRing.ResidueField B) => e (IsLocalRing.residue B b)) h
    simp only [MulSemiringAction.toRingAut_apply] at this
    rw [IsLocalRing.ResidueField.residue_smul (B.decompositionSubgroup k) τ b]
    exact this
  · intro h
    refine RingEquiv.ext fun r => ?_
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := B) r
    show τ • IsLocalRing.residue B b = IsLocalRing.residue B b
    rw [← IsLocalRing.ResidueField.residue_smul (B.decompositionSubgroup k) τ b, h]

variable (K : Type u) [Field K]

private theorem decomp_descend (L₀ : IntermediateField (F₀ K) (Ω₀ K)) (A : ValuationSubring (lift K L₀))
    (σ : lift K L₀ ≃ₐ[RatFunc K] lift K L₀) (σ₀ : L₀ ≃ₐ[F₀ K] L₀)
    (hcomm : ∀ z : L₀, σ (toLift K L₀ z) = toLift K L₀ (σ₀ z))
    (hσ : σ ∈ A.decompositionSubgroup (RatFunc K)) :
    σ₀ ∈ (A.comap (toLift K L₀)).decompositionSubgroup (F₀ K) := by
  rw [mem_decompositionSubgroup_iff_forall] at hσ ⊢
  intro z
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← hcomm]
  exact hσ _

private theorem inertia_descend (L₀ : IntermediateField (F₀ K) (Ω₀ K)) (A : ValuationSubring (lift K L₀))
    (σ : lift K L₀ ≃ₐ[RatFunc K] lift K L₀) (σ₀ : L₀ ≃ₐ[F₀ K] L₀)
    (hcomm : ∀ z : L₀, σ (toLift K L₀ z) = toLift K L₀ (σ₀ z))
    (hσ : σ ∈ A.decompositionSubgroup (RatFunc K))
    (hI : (⟨σ, hσ⟩ : A.decompositionSubgroup (RatFunc K)) ∈ A.inertiaSubgroup (RatFunc K)) :
    (⟨σ₀, decomp_descend K L₀ A σ σ₀ hcomm hσ⟩ : (A.comap (toLift K L₀)).decompositionSubgroup (F₀ K)) ∈
      (A.comap (toLift K L₀)).inertiaSubgroup (F₀ K) := by
  rw [mem_inertiaSubgroup_iff_forall] at hI ⊢
  intro b
  apply (resMap A (toLift K L₀)).injective
  rw [resMap_residue, resMap_residue]
  have h1 := hI (comapHom A (toLift K L₀) b)
  convert h1 using 2
  apply Subtype.ext
  show toLift K L₀ (σ₀ b) = σ (toLift K L₀ b)
  exact (hcomm b).symm

end DecompDescent
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

section RatFuncFrame

variable (K : Type u) [Field K] {M : Type u} [Field M] [Algebra (RatFunc K) M] [Algebra K M]
  [IsScalarTower K (RatFunc K) M]

private def tt : M := algebraMap (RatFunc K) M RatFunc.X

private theorem transcendental_tt : Transcendental K (tt K (M := M)) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) M).injective).mpr
    RatFunc.transcendental_X

private theorem algebraMap_mem_adjoin (f : RatFunc K) : algebraMap (RatFunc K) M f ∈ K⟮tt K (M := M)⟯ := by
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨f.num, f.denom, ?_⟩
  have key : ∀ p : Polynomial K, Polynomial.aeval (tt K (M := M)) p =
      algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p) := by
    intro p
    rw [tt, ← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply,
      Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [key, key, ← map_div₀, RatFunc.num_div_denom]

private def toAdjoin : RatFunc K →+* K⟮tt K (M := M)⟯ where
  toFun f := ⟨algebraMap (RatFunc K) M f, algebraMap_mem_adjoin K f⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' f g := Subtype.ext (map_mul _ f g)
  map_zero' := Subtype.ext (map_zero _)
  map_add' f g := Subtype.ext (map_add _ f g)

private theorem finiteDimensional_isGalois_adjoin [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M] :
    FiniteDimensional K⟮tt K (M := M)⟯ M ∧ IsGalois K⟮tt K (M := M)⟯ M := by
  letI : Algebra (RatFunc K) K⟮tt K (M := M)⟯ := (toAdjoin K).toAlgebra
  haveI : IsScalarTower (RatFunc K) K⟮tt K (M := M)⟯ M :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  exact ⟨Module.Finite.of_restrictScalars_finite (RatFunc K) _ M,
    IsGalois.tower_top_of_isGalois (RatFunc K) _ M⟩

private def toRatFuncAlgEquiv (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M) : M ≃ₐ[RatFunc K] M :=
  { (σ : M ≃+* M) with
    commutes' := fun f => σ.commutes (toAdjoin K f) }

private theorem toRatFuncAlgEquiv_eq_one_iff (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M) :
    toRatFuncAlgEquiv K σ = 1 ↔ σ = 1 := by
  constructor <;> intro h <;> ext x
  · exact congrArg (fun τ : M ≃ₐ[RatFunc K] M => τ x) h
  · exact congrArg (fun τ : M ≃ₐ[K⟮tt K (M := M)⟯] M => τ x) h

private theorem toRatFuncAlgEquiv_mem_decompositionSubgroup_iff (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M)
    (A : ValuationSubring M) :
    toRatFuncAlgEquiv K σ ∈ A.decompositionSubgroup (RatFunc K) ↔
      σ ∈ A.decompositionSubgroup K⟮tt K (M := M)⟯ := by
  simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff, SetLike.ext_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

private theorem toRatFuncAlgEquiv_mem_inertiaSubgroup (σ : M ≃ₐ[K⟮tt K (M := M)⟯] M) (A : ValuationSubring M)
    (hσ : σ ∈ A.decompositionSubgroup K⟮tt K (M := M)⟯)
    (hI : (⟨σ, hσ⟩ : A.decompositionSubgroup K⟮tt K (M := M)⟯) ∈ A.inertiaSubgroup K⟮tt K (M := M)⟯) :
    (⟨toRatFuncAlgEquiv K σ, (toRatFuncAlgEquiv_mem_decompositionSubgroup_iff K σ A).mpr hσ⟩ :
        A.decompositionSubgroup (RatFunc K)) ∈ A.inertiaSubgroup (RatFunc K) := by
  rw [mem_inertiaSubgroup_iff_forall] at hI ⊢
  intro b
  have h := hI b
  convert h using 2 <;> first | (with_reducible_and_instances rfl) | rfl | skip

end RatFuncFrame
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

section Assembly

variable (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]

omit [IsAlgClosed K] [DecidableEq K] in

private theorem baseChange_genCurve_lift [DecidableEq (Ω K)] (L₀ : IntermediateField (F₀ K) (Ω₀ K)) :
    (genCurve K (tt K (M := lift K L₀))).baseChange (lift K L₀) = (EF K).baseChange (lift K L₀) := by
  rw [baseChange_genCurve (transcendental_tt K), WeierstrassCurve.baseChange, EF_eq, map_ofJNe0Or1728]
  rfl

omit [IsAlgClosed K] [DecidableEq K] in

private theorem fixed_of_fixed_cast [DecidableEq (Ω K)] (X : IntermediateField (F₀ K) (Ω₀ K))
    (σ : lift K X ≃ₐ[K⟮tt K (M := lift K X)⟯] lift K X)
    (P : ((EF K).baseChange (lift K X)).toAffine.Point)
    (h : WeierstrassCurve.Affine.Point.map σ.toAlgHom
        (castAddHom (baseChange_genCurve_lift K X).symm P) = castAddHom (baseChange_genCurve_lift K X).symm P) :
    WeierstrassCurve.Affine.Point.map (toRatFuncAlgEquiv K σ).toAlgHom P = P := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · rw [castAddHom_some] at h
    simp only [WeierstrassCurve.Affine.Point.map_some] at h
    rw [WeierstrassCurve.Affine.Point.some.injEq] at h
    obtain ⟨hx, hy⟩ := h
    simp only [WeierstrassCurve.Affine.Point.map_some]
    exact WeierstrassCurve.Affine.Point.some_congr' (by exact hx) (by exact hy) _ _

omit [IsAlgClosed K] [DecidableEq K] [Fact q.Prime] in
private theorem charP_F₀ : CharP (F₀ K) q := by
  haveI : CharP (RatFunc K) q := charP_of_injective_ringHom (algebraMap K (RatFunc K)).injective q
  haveI : CharP (Ω K) q := charP_of_injective_ringHom (algebraMap (RatFunc K) (Ω K)).injective q
  exact (F₀ K).subtype.charP (F₀ K).subtype.injective q

omit [IsAlgClosed K] [DecidableEq K] [Fact q.Prime] in
include q in

private theorem natCast_F₀_ne_zero {n : ℕ} (hn : (n : K) ≠ 0) : (n : F₀ K) ≠ 0 := by
  haveI := charP_F₀ K q
  intro h
  apply hn
  rw [CharP.cast_eq_zero_iff K q]
  exact (CharP.cast_eq_zero_iff (F₀ K) q n).mp h

omit [IsAlgClosed K] [DecidableEq K] in

private theorem exists_aux_level : ∃ m : ℕ, (m : K) ≠ 0 ∧ (q = 2 → m = 3) ∧ (m = 2 ∨ m = 3) ∧ (m = 2 → q ≠ 2) := by
  have hq : q.Prime := Fact.out
  by_cases hq2 : q = 2
  · refine ⟨3, ?_, fun _ => rfl, Or.inr rfl, fun h => absurd h (by norm_num)⟩
    subst hq2
    intro h3
    have h23 : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h3
    omega
  · refine ⟨2, ?_, fun h => absurd h hq2, Or.inl rfl, fun _ => hq2⟩
    intro h2
    have hq2' : q ∣ 2 := (CharP.cast_eq_zero_iff K q 2).mp h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hq2' with h1 | h1
    · exact hq.one_lt.ne' h1
    · exact hq2 h1

private def RouteRow [DecidableEq (Ω K)] (m : ℕ) : Prop :=
  ∃ S : IntermediateField (F₀ K) (Ω₀ K), FiniteDimensional (F₀ K) S ∧ IsGalois (F₀ K) S ∧
    ∀ (M' : IntermediateField (F₀ K) (Ω₀ K)), S ≤ M' →
    ∀ (A : ValuationSubring M'), IsUnit ((m : ℕ) : A) → algebraMap (F₀ K) M' (Ebase K).j ∈ A →
    ∃ (W : WeierstrassCurve A) (κ : VariableChange M'),
      κ • (Ebase K).baseChange M' = W.map A.subtype ∧ IsUnit W.Δ ∧
      ∀ (σ : M' ≃ₐ[F₀ K] M') (hσ : σ ∈ A.decompositionSubgroup (F₀ K)),
        (⟨σ, hσ⟩ : A.decompositionSubgroup (F₀ K)) ∈ A.inertiaSubgroup (F₀ K) →
        (∀ P : ((Ebase K).baseChange M').toAffine.Point, m • P = 0 →
            WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P) →
        (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M' →+* M'))⁻¹ ∧
            g.map (IsLocalRing.residue A) = 1) →
        ∀ x : M', (x : Ω₀ K) ∈ S → σ x = x

set_option synthInstance.maxHeartbeats 400000 in

private def TorsionPiece [DecidableEq (Ω K)] (n : ℕ) (L : IntermediateField (F₀ K) (Ω₀ K)) : Prop :=
  FiniteDimensional (F₀ K) L ∧ IsGalois (F₀ K) L ∧
    Nat.card {P : ((Ebase K).baseChange L).toAffine.Point // n • P = 0} = n ^ 2 ∧
    ∀ σ : L ≃ₐ[F₀ K] L,
      (∀ P : ((Ebase K).baseChange L).toAffine.Point, n • P = 0 →
        WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P) → σ = 1

private def RestrictionLeg : Prop :=
  ∀ (L₀ L₁ : IntermediateField (F₀ K) (Ω₀ K)) (h : L₀ ≤ L₁) [Normal (F₀ K) L₀]
    (σ : lift K L₁ ≃ₐ[RatFunc K] lift K L₁),
    ∃ σ₀ : L₀ ≃ₐ[F₀ K] L₀, ∀ z : L₀, σ (toLiftOfLE K h z) = toLiftOfLE K h (σ₀ z)

private def TorsionDescentLeg [DecidableEq (Ω K)] : Prop :=
  ∀ (L₀ L₁ : IntermediateField (F₀ K) (Ω₀ K)) (h : L₀ ≤ L₁) (n : ℕ)
    (σ : lift K L₁ ≃ₐ[RatFunc K] lift K L₁) (σ₀ : L₀ ≃ₐ[F₀ K] L₀),
    (∀ z : L₀, σ (toLiftOfLE K h z) = toLiftOfLE K h (σ₀ z)) →
    (∀ P : ((EF K).baseChange (lift K L₁)).toAffine.Point, n • P = 0 →
      WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P) →
    ∀ P : ((Ebase K).baseChange L₀).toAffine.Point, n • P = 0 →
      WeierstrassCurve.Affine.Point.map σ₀.toAlgHom P = P

omit [IsAlgClosed K] [DecidableEq K] in

private theorem restrictionLeg_holds : RestrictionLeg K := fun _ _ h _ σ => exists_restrict K h σ

omit [IsAlgClosed K] [DecidableEq K] in

private theorem torsionDescentLeg_holds [DecidableEq (Ω K)] : TorsionDescentLeg K :=
  fun _ _ h _ σ σ₀ hcomm hσ => torsion_fixed_restrict K h σ σ₀ hcomm hσ

private def FrobLeg (E₀ : WeierstrassCurve K) [E₀.IsElliptic] : Prop :=
  ∀ (L₀ : IntermediateField (F₀ K) (Ω₀ K)) [Normal (F₀ K) L₀],
    FiniteDimensional K⟮algebraMap (RatFunc K) (lift K L₀) RatFunc.X⟯ (lift K L₀) →
    IsGalois K⟮algebraMap (RatFunc K) (lift K L₀) RatFunc.X⟯ (lift K L₀) →
    FrobContract K q E₀ (lift K L₀) (algebraMap (RatFunc K) (lift K L₀) RatFunc.X)

omit [IsAlgClosed K] [DecidableEq K] in
private theorem toLiftOfLE_rfl (L : IntermediateField (F₀ K) (Ω₀ K)) (z : L) :
    toLiftOfLE K (le_refl L) z = toLift K L z := rfl

omit [IsAlgClosed K] [DecidableEq K] in

private theorem restriction_fixes_S [DecidableEq (Ω K)] (m : ℕ) (hA2 : TorsionDescentLeg K)
    (S X : IntermediateField (F₀ K) (Ω₀ K))
    (A : ValuationSubring (lift K X)) (κb : VariableChange X)
    (hfaith : ∀ (τ : X ≃ₐ[F₀ K] X) (hτ : τ ∈ (A.comap (toLift K X)).decompositionSubgroup (F₀ K)),
      (⟨τ, hτ⟩ : (A.comap (toLift K X)).decompositionSubgroup (F₀ K)) ∈
          (A.comap (toLift K X)).inertiaSubgroup (F₀ K) →
      (∀ P : ((Ebase K).baseChange X).toAffine.Point, m • P = 0 →
          WeierstrassCurve.Affine.Point.map τ.toAlgHom P = P) →
      (∃ g : VariableChange (A.comap (toLift K X)),
          g.map (A.comap (toLift K X)).subtype = κb * (κb.map (τ : X →+* X))⁻¹ ∧
          g.map (IsLocalRing.residue (A.comap (toLift K X))) = 1) →
      ∀ x : X, (x : Ω₀ K) ∈ S → τ x = x)
    (σ : lift K X ≃ₐ[RatFunc K] lift K X) (hσ : σ ∈ A.decompositionSubgroup (RatFunc K))
    (hI : (⟨σ, hσ⟩ : A.decompositionSubgroup (RatFunc K)) ∈ A.inertiaSubgroup (RatFunc K))
    (hfixm : ∀ P : ((EF K).baseChange (lift K X)).toAffine.Point, m • P = 0 →
      WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P)
    (g : VariableChange A)
    (hg1 : g.map A.subtype = κb.map (toLift K X) * ((κb.map (toLift K X)).map (σ : lift K X →+* lift K X))⁻¹)
    (hg2 : g.map (IsLocalRing.residue A) = 1)
    (σX : X ≃ₐ[F₀ K] X) (hσX : ∀ z : X, σ (toLift K X z) = toLift K X (σX z)) :
    ∀ x : X, (x : Ω₀ K) ∈ S → σX x = x := by
  have hD₀ := decomp_descend K X A σ σX hσX hσ
  have hI₀ := inertia_descend K X A σ σX hσX hσ hI
  have htors := hA2 X X le_rfl m σ σX (fun z => hσX z) hfixm
  have hv : g.map A.subtype = (κb * (κb.map (σX : X →+* X))⁻¹).map (toLift K X) := by
    have hmul : (κb * (κb.map (σX : X →+* X))⁻¹).map (toLift K X) =
        κb.map (toLift K X) * ((κb.map (σX : X →+* X)).map (toLift K X))⁻¹ := by
      have h1 := map_mul (VariableChange.mapHom (toLift K X)) κb (κb.map (σX : X →+* X))⁻¹
      have h2 := map_inv (VariableChange.mapHom (toLift K X)) (κb.map (σX : X →+* X))
      rw [h2] at h1
      exact h1
    have hcomp : (σ : lift K X →+* lift K X).comp (toLift K X) = (toLift K X).comp (σX : X →+* X) :=
      RingHom.ext hσX
    rw [hmul, hg1, VariableChange.map_map, VariableChange.map_map, hcomp]
  obtain ⟨g₀, hg₀1, hg₀2⟩ := exists_descend A (toLift K X) g _ hv
  have hg₀3 : g₀.map (IsLocalRing.residue _) = 1 :=
    map_residue_eq_one_of_map A (toLift K X) g₀ (by rw [hg₀2]; exact hg2)
  exact hfaith σX hD₀ hI₀ htors ⟨g₀, hg₀1, hg₀3⟩

omit [IsAlgClosed K] [DecidableEq K] in

private theorem restriction_fixes_piece [DecidableEq (Ω K)] (hA1 : RestrictionLeg K) (hA2 : TorsionDescentLeg K)
    (X : IntermediateField (F₀ K) (Ω₀ K)) (σ : lift K X ≃ₐ[RatFunc K] lift K X)
    (σX : X ≃ₐ[F₀ K] X) (hσX : ∀ z : X, σ (toLift K X z) = toLift K X (σX z))
    (n : ℕ) (L : IntermediateField (F₀ K) (Ω₀ K)) [Normal (F₀ K) L] (hLX : L ≤ X)
    (hfixn : ∀ P : ((EF K).baseChange (lift K X)).toAffine.Point, n • P = 0 →
      WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P)
    (hLfaith : ∀ τ : L ≃ₐ[F₀ K] L, (∀ P : ((Ebase K).baseChange L).toAffine.Point, n • P = 0 →
      WeierstrassCurve.Affine.Point.map τ.toAlgHom P = P) → τ = 1) :
    ∀ x : X, (x : Ω₀ K) ∈ L → σX x = x := by
  intro x hxL
  obtain ⟨τ, hτ⟩ := hA1 L X hLX σ
  have hτ1 : τ = 1 := hLfaith τ (hA2 L X hLX n σ τ hτ hfixn)
  subst hτ1
  have hx : toLift K X x = toLiftOfLE K hLX ⟨(x : Ω₀ K), hxL⟩ := rfl
  apply (toLift_injective K X)
  rw [← hσX x, hx, hτ, AlgEquiv.one_apply]

omit [IsAlgClosed K] [DecidableEq K] in

private theorem eq_one_of_fixes_pieces (LN Lm S X : IntermediateField (F₀ K) (Ω₀ K)) (hX : X = (LN ⊔ Lm) ⊔ S)
    (hLNX : LN ≤ X) (hLmX : Lm ≤ X) (hSX : S ≤ X) (σX : X ≃ₐ[F₀ K] X)
    (hLNfix : ∀ x : X, (x : Ω₀ K) ∈ LN → σX x = x) (hLmfix : ∀ x : X, (x : Ω₀ K) ∈ Lm → σX x = x)
    (hSfix : ∀ x : X, (x : Ω₀ K) ∈ S → σX x = x) : σX = 1 := by
  let Fix : IntermediateField (F₀ K) X :=
    (AlgHom.equalizer (σX : ↥X →ₐ[↥(F₀ K)] ↥X) 1).toIntermediateField (by
      intro x hx
      change σX x⁻¹ = _
      have hx' : σX x = x := hx
      simp only [map_inv₀, hx', AlgHom.one_apply])
  have hmemFix : ∀ y : X, y ∈ Fix ↔ σX y = y := fun y => by
    show y ∈ AlgHom.equalizer (σX : ↥X →ₐ[↥(F₀ K)] ↥X) 1 ↔ _
    simp only [AlgHom.mem_equalizer]
    rfl
  have hle' : (LN ⊔ Lm) ⊔ S ≤ IntermediateField.lift Fix := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      have hyX : y ∈ X := hLNX hy
      exact (IntermediateField.mem_lift (⟨y, hyX⟩ : X)).mpr ((hmemFix _).mpr (hLNfix ⟨y, hyX⟩ hy))
    · intro y hy
      have hyX : y ∈ X := hLmX hy
      exact (IntermediateField.mem_lift (⟨y, hyX⟩ : X)).mpr ((hmemFix _).mpr (hLmfix ⟨y, hyX⟩ hy))
    · intro y hy
      have hyX : y ∈ X := hSX hy
      exact (IntermediateField.mem_lift (⟨y, hyX⟩ : X)).mpr ((hmemFix _).mpr (hSfix ⟨y, hyX⟩ hy))
  have hle : X ≤ IntermediateField.lift Fix := hX.le.trans hle'
  refine AlgEquiv.ext fun x => ?_
  have hx : x ∈ Fix := (IntermediateField.mem_lift x).mp (hle x.2)
  rw [AlgEquiv.one_apply]
  exact (hmemFix x).mp hx

omit [IsAlgClosed K] [DecidableEq K] in

private theorem eq_one_of_fixes_toLift (X : IntermediateField (F₀ K) (Ω₀ K)) (σ : lift K X ≃ₐ[RatFunc K] lift K X)
    (hfixgen : ∀ z : X, σ (toLift K X z) = toLift K X z) : σ = 1 := by
  let FixM : IntermediateField (RatFunc K) (lift K X) :=
    (AlgHom.equalizer (σ : ↥(lift K X) →ₐ[RatFunc K] ↥(lift K X)) 1).toIntermediateField (by
      intro x hx
      change σ x⁻¹ = _
      have hx' : σ x = x := hx
      simp only [map_inv₀, hx', AlgHom.one_apply])
  have hmemFixM : ∀ y : lift K X, y ∈ FixM ↔ σ y = y := fun y => by
    show y ∈ AlgHom.equalizer (σ : ↥(lift K X) →ₐ[RatFunc K] ↥(lift K X)) 1 ↔ _
    simp only [AlgHom.mem_equalizer]
    rfl
  have hle : lift K X ≤ IntermediateField.lift FixM := by
    show IntermediateField.adjoin (RatFunc K) _ ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    have hw : ((z : Ω K)) ∈ lift K X := mem_lift_of_mem K X hz
    exact (IntermediateField.mem_lift (⟨_, hw⟩ : lift K X)).mpr ((hmemFixM _).mpr (hfixgen ⟨z, hz⟩))
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.one_apply]
  exact (hmemFixM x).mp ((IntermediateField.mem_lift x).mp (hle x.2))

omit [IsAlgClosed K] [DecidableEq K] in

private theorem faithful_lift [DecidableEq (Ω K)] (hA1 : RestrictionLeg K) (hA2 : TorsionDescentLeg K)
    {N m : ℕ} (hN : (N : K) ≠ 0) (hmK : (m : K) ≠ 0)
    (LN Lm S X : IntermediateField (F₀ K) (Ω₀ K)) (hLN : TorsionPiece K N LN) (hLm : TorsionPiece K m Lm)
    (hLNX : LN ≤ X) (hLmX : Lm ≤ X) (hSX : S ≤ X) (hX : X = (LN ⊔ Lm) ⊔ S) [Normal (F₀ K) X]
    (A : ValuationSubring (lift K X)) (κb : VariableChange X)
    (hfaith : ∀ (τ : X ≃ₐ[F₀ K] X) (hτ : τ ∈ (A.comap (toLift K X)).decompositionSubgroup (F₀ K)),
      (⟨τ, hτ⟩ : (A.comap (toLift K X)).decompositionSubgroup (F₀ K)) ∈
          (A.comap (toLift K X)).inertiaSubgroup (F₀ K) →
      (∀ P : ((Ebase K).baseChange X).toAffine.Point, m • P = 0 →
          WeierstrassCurve.Affine.Point.map τ.toAlgHom P = P) →
      (∃ g : VariableChange (A.comap (toLift K X)),
          g.map (A.comap (toLift K X)).subtype = κb * (κb.map (τ : X →+* X))⁻¹ ∧
          g.map (IsLocalRing.residue (A.comap (toLift K X))) = 1) →
      ∀ x : X, (x : Ω₀ K) ∈ S → τ x = x)
    (σ : lift K X ≃ₐ[RatFunc K] lift K X) (hσ : σ ∈ A.decompositionSubgroup (RatFunc K))
    (hI : (⟨σ, hσ⟩ : A.decompositionSubgroup (RatFunc K)) ∈ A.inertiaSubgroup (RatFunc K))
    (hfix : ∀ (n : ℕ), (n : K) ≠ 0 → ∀ P : ((EF K).baseChange (lift K X)).toAffine.Point, n • P = 0 →
      WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P)
    (g : VariableChange A)
    (hg1 : g.map A.subtype = κb.map (toLift K X) * ((κb.map (toLift K X)).map (σ : lift K X →+* lift K X))⁻¹)
    (hg2 : g.map (IsLocalRing.residue A) = 1) :
    σ = 1 := by
  haveI : Normal (F₀ K) LN := hLN.2.1.to_normal
  haveI : Normal (F₀ K) Lm := hLm.2.1.to_normal
  obtain ⟨σX, hσX⟩ := hA1 X X le_rfl σ
  simp only [toLiftOfLE_rfl] at hσX
  have hSfix := restriction_fixes_S K m hA2 S X A κb hfaith σ hσ hI (hfix m hmK) g hg1 hg2 σX hσX
  have hLNfix := restriction_fixes_piece K hA1 hA2 X σ σX hσX N LN hLNX (hfix N hN) hLN.2.2.2
  have hLmfix := restriction_fixes_piece K hA1 hA2 X σ σX hσX m Lm hLmX (hfix m hmK) hLm.2.2.2
  have hσX1 : σX = 1 := eq_one_of_fixes_pieces K LN Lm S X hX hLNX hLmX hSX σX hLNfix hLmfix hSfix
  refine eq_one_of_fixes_toLift K X σ fun z => ?_
  rw [hσX z, hσX1]
  rfl

omit [IsAlgClosed K] [DecidableEq K] [Fact q.Prime] in
include q in

private theorem routeRow_of_served [DecidableEq (Ω K)]
    (hrow2 : (2 : F₀ K) ≠ 0 → RouteRow K 2) (hrow3 : (3 : F₀ K) ≠ 0 → RouteRow K 3)
    (m : ℕ) (hmK : (m : K) ≠ 0) (hm : m = 2 ∨ m = 3) : RouteRow K m := by
  have hmF : (m : F₀ K) ≠ 0 := natCast_F₀_ne_zero K q hmK
  rcases hm with rfl | rfl
  · exact hrow2 (by exact_mod_cast hmF)
  · exact hrow3 (by exact_mod_cast hmF)

omit [IsAlgClosed K] [DecidableEq K] [Fact q.Prime] in
include q in

private theorem routeRow_served [DecidableEq (Ω K)] (m : ℕ) (hmK : (m : K) ≠ 0) (hm : m = 2 ∨ m = 3) : RouteRow K m :=
  routeRow_of_served K q
    (fun h2 => WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero (Ω := Ω₀ K) (Ebase K) h2)
    (fun h3 => WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero (Ω := Ω₀ K) (Ebase K) h3)
    m hmK hm

omit [IsAlgClosed K] [DecidableEq K] [Fact q.Prime] in
include q in

private theorem exists_torsionPiece [DecidableEq (Ω K)] {n : ℕ} (hn : (n : K) ≠ 0) : ∃ L, TorsionPiece K n L := by
  obtain ⟨L, h1, h2, h3, h4⟩ :=
    WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq (Ω := Ω₀ K) (Ebase K)
      (natCast_F₀_ne_zero K q hn)
  exact ⟨L, h1, h2, h3, h4⟩

omit [IsAlgClosed K] [DecidableEq K] in

private theorem descent_model_clause [DecidableEq (Ω K)] (hA1 : RestrictionLeg K) (hA2 : TorsionDescentLeg K)
    {N m : ℕ} (hN : (N : K) ≠ 0) (hmK : (m : K) ≠ 0)
    (LN Lm S X : IntermediateField (F₀ K) (Ω₀ K)) (hLN : TorsionPiece K N LN) (hLm : TorsionPiece K m Lm)
    (hLNX : LN ≤ X) (hLmX : Lm ≤ X) (hSX : S ≤ X) (hXdef : X = (LN ⊔ Lm) ⊔ S) [Normal (F₀ K) X]
    (hS : ∀ (M' : IntermediateField (F₀ K) (Ω₀ K)), S ≤ M' →
      ∀ (A : ValuationSubring M'), IsUnit ((m : ℕ) : A) → algebraMap (F₀ K) M' (Ebase K).j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M'),
        κ • (Ebase K).baseChange M' = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M' ≃ₐ[F₀ K] M') (hσ : σ ∈ A.decompositionSubgroup (F₀ K)),
          (⟨σ, hσ⟩ : A.decompositionSubgroup (F₀ K)) ∈ A.inertiaSubgroup (F₀ K) →
          (∀ P : ((Ebase K).baseChange M').toAffine.Point, m • P = 0 →
              WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M' →+* M'))⁻¹ ∧
              g.map (IsLocalRing.residue A) = 1) →
          ∀ x : M', (x : Ω₀ K) ∈ S → σ x = x)
    (t : lift K X) (ht : t = tt K) :
    ∀ A : ValuationSubring (lift K X), IsUnit ((m : ℕ) : A) → t ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange (lift K X)),
        κ • (genCurve K t).baseChange (lift K X) = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : lift K X ≃ₐ[K⟮t⟯] lift K X) (hσ : σ ∈ A.decompositionSubgroup K⟮t⟯),
          (⟨σ, hσ⟩ : A.decompositionSubgroup K⟮t⟯) ∈ A.inertiaSubgroup K⟮t⟯ →
          (∀ (n : ℕ), (n : K) ≠ 0 → ∀ P : ((genCurve K t).baseChange (lift K X)).toAffine.Point, n • P = 0 →
            WeierstrassCurve.Affine.Point.map σ.toAlgHom P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : lift K X →+* lift K X))⁻¹ ∧
            g.map (IsLocalRing.residue A) = 1) →
          σ = 1 := by
  subst ht
  have hcurve := baseChange_genCurve_lift K X
  intro A hmA htA
  obtain ⟨Wb, κb, hκb, hΔb, hfaith⟩ := hS X hSX (A.comap (toLift K X))
    (isUnit_natCast_comap A (toLift K X) m hmA)
    (by
      rw [ValuationSubring.mem_comap, ofJ_j]
      convert htA using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip)
  refine ⟨Wb.map (comapHom A (toLift K X)), κb.map (toLift K X), ?_, ?_, ?_⟩
  · rw [hcurve, baseChange_EF_eq, WeierstrassCurve.map_variableChange, hκb, WeierstrassCurve.map_map,
      WeierstrassCurve.map_map, subtype_comp_comapHom]
  · rw [WeierstrassCurve.map_Δ]
    exact hΔb.map (comapHom A (toLift K X))
  · intro σ hσ hI hfix ⟨g, hg1, hg2⟩
    rw [← toRatFuncAlgEquiv_eq_one_iff K]
    refine faithful_lift K hA1 hA2 hN hmK LN Lm S X hLN hLm hLNX hLmX hSX hXdef A κb hfaith
      (toRatFuncAlgEquiv K σ) ((toRatFuncAlgEquiv_mem_decompositionSubgroup_iff K σ A).mpr hσ)
      (toRatFuncAlgEquiv_mem_inertiaSubgroup K σ A hσ hI) ?_ g hg1 hg2
    intro n hn P hP
    have := hfix n hn (castAddHom (baseChange_genCurve_lift K X).symm P) (by rw [← map_nsmul, hP, map_zero])
    exact fixed_of_fixed_cast K X σ P this

omit [IsAlgClosed K] [DecidableEq K] in
set_option synthInstance.maxHeartbeats 400000 in

private theorem descent_holds [DecidableEq (Ω K)] (hA1 : RestrictionLeg K) (hA2 : TorsionDescentLeg K)
    (N : ℕ) (hN : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (hfrob : FrobLeg K q E₀) (hroute : ∀ m : ℕ, (m : K) ≠ 0 → (m = 2 ∨ m = 3) → RouteRow K m) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M),
      Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      (∃ m : ℕ, (m : K) ≠ 0 ∧ (q = 2 → m = 3) ∧
        Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // m • P = 0} = m ^ 2 ∧
        ∀ A : ValuationSubring M, IsUnit ((m : ℕ) : A) → t ∈ A →
          ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
            κ • (genCurve K t).baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
            ∀ (σ : M ≃ₐ[K⟮t⟯] M) (hσ : σ ∈ A.decompositionSubgroup K⟮t⟯),
              (⟨σ, hσ⟩ : A.decompositionSubgroup K⟮t⟯) ∈ A.inertiaSubgroup K⟮t⟯ →
              (∀ (n : ℕ), (n : K) ≠ 0 → ∀ P : ((genCurve K t).baseChange M).toAffine.Point, n • P = 0 →
                WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P = P) →
              (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
                g.map (IsLocalRing.residue A) = 1) →
              σ = 1) ∧
      FrobContract K q E₀ M t := by
  obtain ⟨m, hmK, hm2, hm23, -⟩ := exists_aux_level K q
  obtain ⟨LN, hLN⟩ := exists_torsionPiece K q hN
  obtain ⟨Lm, hLm⟩ := exists_torsionPiece K q hmK
  obtain ⟨S, hSfd, hSgal, hS⟩ := hroute m hmK hm23
  haveI := hLN.1; haveI := hLN.2.1; haveI := hLm.1; haveI := hLm.2.1; haveI := hSfd; haveI := hSgal
  haveI hXfd : FiniteDimensional (F₀ K) ((LN ⊔ Lm) ⊔ S : IntermediateField (F₀ K) (Ω₀ K)) := inferInstance
  haveI hXgal : IsGalois (F₀ K) ((LN ⊔ Lm) ⊔ S : IntermediateField (F₀ K) (Ω₀ K)) := ⟨⟩
  obtain ⟨X, hXdef⟩ : ∃ X : IntermediateField (F₀ K) (Ω₀ K), X = (LN ⊔ Lm) ⊔ S := ⟨_, rfl⟩
  haveI : FiniteDimensional (F₀ K) X := hXdef ▸ hXfd
  haveI : IsGalois (F₀ K) X := hXdef ▸ hXgal
  have hLNX : LN ≤ X := hXdef ▸ le_sup_left.trans le_sup_left
  have hLmX : Lm ≤ X := hXdef ▸ le_sup_right.trans le_sup_left
  have hSX : S ≤ X := hXdef ▸ le_sup_right
  haveI hMfd : FiniteDimensional (RatFunc K) (lift K X) := finiteDimensional_lift K X
  haveI hMgal : IsGalois (RatFunc K) (lift K X) := isGalois_lift K X
  obtain ⟨hfd, hgal⟩ := finiteDimensional_isGalois_adjoin K (M := lift K X)
  have hcurve := baseChange_genCurve_lift K X
  refine ⟨lift K X, inferInstance, inferInstance, inferInstance, tt K, transcendental_tt K, hfd, hgal, ?_,
    ⟨m, hmK, hm2, ?_, ?_⟩, ?_⟩
  · rw [hcurve]
    exact card_torsion_lift_eq K hN LN X hLNX hLN.2.2.1
  · rw [hcurve]
    exact card_torsion_lift_eq K hmK Lm X hLmX hLm.2.2.1
  · exact descent_model_clause K hA1 hA2 hN hmK LN Lm S X hLN hLm hLNX hLmX hSX hXdef hS (tt K) rfl
  · exact hfrob X hfd hgal

omit [IsAlgClosed K] [DecidableEq K] in

private theorem descent_holds' [DecidableEq (Ω K)] (N : ℕ) (hN : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (hfrob : FrobLeg K q E₀) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M),
      Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      (∃ m : ℕ, (m : K) ≠ 0 ∧ (q = 2 → m = 3) ∧
        Nat.card {P : ((genCurve K t).baseChange M).toAffine.Point // m • P = 0} = m ^ 2 ∧
        ∀ A : ValuationSubring M, IsUnit ((m : ℕ) : A) → t ∈ A →
          ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
            κ • (genCurve K t).baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
            ∀ (σ : M ≃ₐ[K⟮t⟯] M) (hσ : σ ∈ A.decompositionSubgroup K⟮t⟯),
              (⟨σ, hσ⟩ : A.decompositionSubgroup K⟮t⟯) ∈ A.inertiaSubgroup K⟮t⟯ →
              (∀ (n : ℕ), (n : K) ≠ 0 → ∀ P : ((genCurve K t).baseChange M).toAffine.Point, n • P = 0 →
                WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P = P) →
              (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
                g.map (IsLocalRing.residue A) = 1) →
              σ = 1) ∧
      FrobContract K q E₀ M t :=
  descent_holds K q (restrictionLeg_holds K) (torsionDescentLeg_holds K) N hN E₀ hfrob (routeRow_served K q)

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

end ModularCurve.SigmaDescent
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine"

end SigmaDescentPart
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section SigmaFrobeniusPart

universe u

section SigA1

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace FrobLift
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

section RatFuncFrob

variable (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K]

private def ratFuncFrob : RatFunc K ≃+* RatFunc K :=
  IsFractionRing.ringEquivOfRingEquiv (Polynomial.mapEquiv (frobeniusEquiv K q))

private theorem ratFuncFrob_algebraMap_polynomial (p : K[X]) :
    ratFuncFrob K q (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (p.map (frobeniusEquiv K q : K →+* K)) := by
  simpa [ratFuncFrob, Polynomial.mapEquiv] using
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (Polynomial.mapEquiv (frobeniusEquiv K q)) p

private theorem ratFuncFrob_X : ratFuncFrob K q RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratFuncFrob_algebraMap_polynomial, Polynomial.map_X]

private theorem ratFuncFrob_C (a : K) : ratFuncFrob K q (RatFunc.C a) = RatFunc.C (a ^ q) := by
  rw [← RatFunc.algebraMap_C, ratFuncFrob_algebraMap_polynomial, Polynomial.map_C,
    RatFunc.algebraMap_C]
  rfl

private theorem ratFuncFrob_algebraMap (a : K) :
    ratFuncFrob K q (algebraMap K (RatFunc K) a) = algebraMap K (RatFunc K) (a ^ q) := by
  rw [RatFunc.algebraMap_eq_C, ratFuncFrob_C]

end RatFuncFrob
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Closure

variable (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K]
  (Ω : Type*) [Field Ω] [Algebra (RatFunc K) Ω] [IsAlgClosure (RatFunc K) Ω]

private def closureFrob : Ω ≃+* Ω :=
  IsAlgClosure.equivOfEquiv Ω Ω (ratFuncFrob K q)

private theorem closureFrob_algebraMap (f : RatFunc K) :
    closureFrob K q Ω (algebraMap (RatFunc K) Ω f) =
      algebraMap (RatFunc K) Ω (ratFuncFrob K q f) :=
  IsAlgClosure.equivOfEquiv_algebraMap Ω Ω (ratFuncFrob K q) f

private theorem closureFrob_X :
    closureFrob K q Ω (algebraMap (RatFunc K) Ω RatFunc.X) = algebraMap (RatFunc K) Ω RatFunc.X := by
  rw [closureFrob_algebraMap, ratFuncFrob_X]

variable [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]

private theorem closureFrob_algebraMap_base (a : K) :
    closureFrob K q Ω (algebraMap K Ω a) = algebraMap K Ω (a ^ q) := by
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) Ω a, closureFrob_algebraMap,
    ratFuncFrob_algebraMap, ← IsScalarTower.algebraMap_apply]

private theorem closureFrob_algebraMap_base' (a : K) :
    closureFrob K q Ω (algebraMap K Ω a) = algebraMap K Ω (frobeniusEquiv K q a) :=
  closureFrob_algebraMap_base K q Ω a

end Closure
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end ModularCurve.FrobLift
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigA1
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section SigA3

open AlgebraicCurve
open scoped IntermediateField Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace FrobLift
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

section Adjoin

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

private theorem apply_eq_self_of_mem_adjoin (t : M) (ψ : M →ₐ[K] M) (hψ : ψ t = t) {y : M}
    (hy : y ∈ K⟮t⟯) : ψ y = y := by
  let T : IntermediateField K M :=
    { (ψ : M →+* M).eqLocusField (RingHom.id M) with
      algebraMap_mem' := fun a => ψ.commutes a }
  have hle : K⟮t⟯ ≤ T := IntermediateField.adjoin_simple_le_iff.mpr hψ
  exact hle hy

private theorem isIntegral_of_apply_eq (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : M →ₐ[K] M)
    (hψ : ψ t = t) : ψ.toRingHom.IsIntegral := by
  intro y
  obtain ⟨p, hp, hpy⟩ := IsIntegral.of_finite K⟮t⟯ y
  refine ⟨p.map (algebraMap K⟮t⟯ M), hp.map _, ?_⟩
  have hcomp : ψ.toRingHom.comp (algebraMap K⟮t⟯ M) = algebraMap K⟮t⟯ M := by
    ext z
    exact apply_eq_self_of_mem_adjoin t ψ hψ z.2
  rw [Polynomial.eval₂_map, hcomp]
  exact hpy

end Adjoin
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

end Along
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Place

private theorem exists_semilinearAut_smul_place_eq
    (K : Type*) [Field K] [IsAlgClosed K] {M : Type*} [Field M] [Algebra K M]
    (q : ℕ) (t : M) (j₀ : K) (hj₀ : j₀ ^ q = j₀)
    (hfin : FiniteDimensional K⟮t⟯ M) (hgal : IsGalois K⟮t⟯ M)
    (g : SemilinearAut K M) (hga : ∀ a : K, g • algebraMap K M a = algebraMap K M (a ^ q))
    (hgt : g • t = t)
    (W₀ : Place K M) (hW₀ : 0 < W₀.ord (t - algebraMap K M j₀)) :
    ∃ frM : SemilinearAut K M,
      (∀ a : K, frM • algebraMap K M a = algebraMap K M (a ^ q)) ∧ frM • t = t ∧
        frM • W₀ = W₀ := by
  haveI := hfin
  haveI := hgal

  have hfix : g • (t - algebraMap K M j₀) = t - algebraMap K M j₀ := by
    rw [smul_sub, hgt, hga, hj₀]
  have hW₁ : 0 < (g • W₀).ord (t - algebraMap K M j₀) := by
    rw [← hfix, SemilinearAut.ord_smul]
    exact hW₀

  have hint : ∀ ψ : M →ₐ[K] M, ψ t = t → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_apply_eq t ψ hψ
  obtain ⟨-, -, hiii, -, -⟩ :=
    AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K t t j₀
      (AlgHom.id K M) rfl hfin hgal hint W₀ hW₀
  obtain ⟨ψ, hψ, hrestr⟩ := hiii (g • W₀) hW₁

  let ψₜ : M →ₐ[K⟮t⟯] M :=
    { (ψ : M →+* M) with
      commutes' := fun y => apply_eq_self_of_mem_adjoin t ψ hψ y.2 }
  let σ : M ≃ₐ[K] M :=
    (AlgEquiv.ofBijective ψₜ (Algebra.IsAlgebraic.algHom_bijective ψₜ)).restrictScalars K
  have hσ : ∀ x, σ x = ψ x := fun _ => rfl
  refine ⟨SemilinearAut.ofAlgAut σ * g, fun a => ?_, ?_, ?_⟩
  · rw [mul_smul, hga, SemilinearAut.ofAlgAut_smul]
    exact σ.commutes _
  · rw [mul_smul, hgt, SemilinearAut.ofAlgAut_smul, hσ]
    exact hψ
  · rw [mul_smul, ← hrestr]
    ext x
    rw [SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
      SemilinearAut.toRingAut_ofAlgAut, mem_restrictAlong_iff]
    have hx : ψ ((σ : M ≃+* M).symm x) = x := by
      rw [← hσ]
      exact σ.apply_symm_apply x
    rw [hx]

end Place
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end ModularCurve.FrobLift
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigA3
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section SigA4

open IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace FrobLift
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

section FixClosure

variable {Ω : Type*} [Field Ω]

private theorem apply_eq_self_of_mem_closure (Ψ : Ω →+* Ω) {x₀ : Ω} (h : Ψ x₀ = x₀) {x : Ω}
    (hx : x ∈ Subfield.closure ({x₀} : Set Ω)) : Ψ x = x := by
  have hle : Subfield.closure ({x₀} : Set Ω) ≤ Ψ.eqLocusField (RingHom.id Ω) :=
    Subfield.closure_le.mpr (Set.singleton_subset_iff.mpr h)
  exact hle hx

end FixClosure
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Normal

variable {Ω : Type*} [Field Ω] (F₀ : Subfield Ω)

private def algEquivOfFix (Ψ : Ω ≃+* Ω) (hΨ : ∀ x ∈ F₀, Ψ x = x) : Ω ≃ₐ[F₀] Ω :=
  { Ψ with commutes' := fun x => hΨ x x.2 }

private theorem apply_mem_of_normal (Ψ : Ω ≃+* Ω) (hΨ : ∀ x ∈ F₀, Ψ x = x)
    (E : IntermediateField F₀ Ω) [Normal F₀ E] {x : Ω} (hx : x ∈ E) : Ψ x ∈ E := by
  have h := AlgHom.fieldRange_of_normal ((algEquivOfFix F₀ Ψ hΨ : Ω →ₐ[F₀] Ω).comp E.val)
  have hmem : Ψ x ∈ ((algEquivOfFix F₀ Ψ hΨ : Ω →ₐ[F₀] Ω).comp E.val).fieldRange :=
    AlgHom.mem_fieldRange.mpr ⟨⟨x, hx⟩, rfl⟩
  rwa [h] at hmem

private theorem symm_apply_eq_self_of_apply_eq_self (Ψ : Ω ≃+* Ω) (hΨ : ∀ x ∈ F₀, Ψ x = x) :
    ∀ x ∈ F₀, Ψ.symm x = x := fun y hy =>
  calc Ψ.symm y = Ψ.symm (Ψ y) := by rw [hΨ y hy]
    _ = y := Ψ.symm_apply_apply y

end Normal
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Adjoin

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

private theorem apply_mem_adjoin (Ψ : Ω →+* Ω) (φ : F → F)
    (hΨ : ∀ f : F, Ψ (algebraMap F Ω f) = algebraMap F Ω (φ f))
    (S : Set Ω) (hS : ∀ s ∈ S, Ψ s ∈ adjoin F S) {x : Ω} (hx : x ∈ adjoin F S) :
    Ψ x ∈ adjoin F S := by
  let T : IntermediateField F Ω :=
    { (adjoin F S).toSubfield.comap Ψ with
      algebraMap_mem' := fun f => show Ψ (algebraMap F Ω f) ∈ adjoin F S by
        rw [hΨ]
        exact (adjoin F S).algebraMap_mem (φ f) }
  have hle : adjoin F S ≤ T := adjoin_le_iff.mpr hS
  exact hle hx

private theorem mem_adjoin_iff_apply_mem_adjoin (Ψ : Ω ≃+* Ω) (φ : F ≃+* F)
    (hΨ : ∀ f : F, Ψ (algebraMap F Ω f) = algebraMap F Ω (φ f))
    (F₀ : Subfield Ω) (hF₀ : ∀ x ∈ F₀, Ψ x = x)
    (E : IntermediateField F₀ Ω) [Normal F₀ E] (x : Ω) :
    x ∈ adjoin F (E : Set Ω) ↔ Ψ x ∈ adjoin F (E : Set Ω) := by
  have hΨ' : ∀ f : F, Ψ.symm (algebraMap F Ω f) = algebraMap F Ω (φ.symm f) := fun f => by
    apply Ψ.injective
    rw [RingEquiv.apply_symm_apply, hΨ, RingEquiv.apply_symm_apply]
  have hF₀' : ∀ y ∈ F₀, Ψ.symm y = y := symm_apply_eq_self_of_apply_eq_self F₀ Ψ hF₀
  constructor
  · exact apply_mem_adjoin (Ψ : Ω →+* Ω) φ hΨ (E : Set Ω)
      (fun s hs => subset_adjoin F (E : Set Ω) (apply_mem_of_normal F₀ Ψ hF₀ E hs))
  · intro h
    have h' := apply_mem_adjoin (Ψ.symm : Ω →+* Ω) φ.symm hΨ' (E : Set Ω)
      (fun s hs => subset_adjoin F (E : Set Ω) (apply_mem_of_normal F₀ Ψ.symm hF₀' E hs)) h
    simpa using h'

private theorem mem_adjoin_iff_apply_mem_adjoin_of_apply_eq (Ψ : Ω ≃+* Ω) (φ : F ≃+* F)
    (hΨ : ∀ f : F, Ψ (algebraMap F Ω f) = algebraMap F Ω (φ f))
    {x₀ : Ω} (hx₀ : Ψ x₀ = x₀)
    (E : IntermediateField (Subfield.closure ({x₀} : Set Ω)) Ω)
    [Normal (Subfield.closure ({x₀} : Set Ω)) E] (x : Ω) :
    x ∈ adjoin F (E : Set Ω) ↔ Ψ x ∈ adjoin F (E : Set Ω) :=
  mem_adjoin_iff_apply_mem_adjoin Ψ φ hΨ (Subfield.closure ({x₀} : Set Ω))
    (fun _ hy => apply_eq_self_of_mem_closure (Ψ : Ω →+* Ω) hx₀ hy) E x

end Adjoin
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end ModularCurve.FrobLift
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigA4
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section SigARestrict

open IntermediateField

namespace SigmaFrobeniusPackaging

section Packaging

variable {K 𝓕 Ω : Type u} [Field K] [Field 𝓕] [Field Ω] [Algebra K 𝓕] [Algebra 𝓕 Ω] [Algebra K Ω] [IsScalarTower K 𝓕 Ω]

private def restrict (Ψ : Ω ≃+* Ω) (M : IntermediateField 𝓕 Ω) (hM : ∀ x, x ∈ M ↔ Ψ x ∈ M) : ↥M ≃+* ↥M where
  toFun y := ⟨Ψ y, (hM y).mp y.2⟩
  invFun y := ⟨Ψ.symm y, (hM (Ψ.symm y)).mpr (by rw [Ψ.apply_symm_apply]; exact y.2)⟩
  left_inv y := Subtype.ext (Ψ.symm_apply_apply y)
  right_inv y := Subtype.ext (Ψ.apply_symm_apply y)
  map_mul' y z := Subtype.ext (map_mul Ψ (y : Ω) z)
  map_add' y z := Subtype.ext (map_add Ψ (y : Ω) z)

private theorem exists_semilinearAut (Ψ : Ω ≃+* Ω) (τ : K ≃+* K) (hK : ∀ a : K, Ψ (algebraMap K Ω a) = algebraMap K Ω (τ a))
    (M : IntermediateField 𝓕 Ω) (hM : ∀ x, x ∈ M ↔ Ψ x ∈ M) :
    ∃ frM : AlgebraicCurve.SemilinearAut K ↥M,
      (∀ a : K, frM • (algebraMap K ↥M a) = algebraMap K ↥M (τ a)) ∧
      ∀ y : ↥M, ((frM • y : ↥M) : Ω) = Ψ y := by
  have hcomm : ∀ a : K, restrict Ψ M hM (algebraMap K ↥M a) = algebraMap K ↥M (τ a) := by
    intro a
    apply Subtype.ext

    show Ψ (algebraMap K Ω a) = algebraMap K Ω (τ a)
    exact hK a
  refine ⟨⟨(restrict Ψ M hM, τ), fun a => hcomm a⟩, fun a => hcomm a, fun y => rfl⟩

private theorem exists_semilinearAut_pow (q : ℕ) (Ψ : Ω ≃+* Ω) (τ : K ≃+* K) (hτ : ∀ a : K, τ a = a ^ q)
    (hK : ∀ a : K, Ψ (algebraMap K Ω a) = algebraMap K Ω (τ a))
    (M : IntermediateField 𝓕 Ω) (hM : ∀ x, x ∈ M ↔ Ψ x ∈ M) :
    ∃ frM : AlgebraicCurve.SemilinearAut K ↥M,
      (∀ a : K, frM • (algebraMap K ↥M a) = algebraMap K ↥M (a ^ q)) ∧
      ∀ y : ↥M, Ψ (y : Ω) = y → frM • y = y := by
  obtain ⟨frM, h₁, h₂⟩ := exists_semilinearAut Ψ τ hK M hM
  refine ⟨frM, fun a => ?_, fun y hy => ?_⟩
  · rw [h₁ a, hτ a]
  · exact Subtype.ext ((h₂ y).trans hy)

end Packaging
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigmaFrobeniusPackaging
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigARestrict
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Corollary

open AlgebraicCurve ModularCurve.SigmaDescent ModularCurve.SigmaSpine
open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace FrobLift
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

private theorem j_congr {R : Type*} [CommRing R] {V₁ V₂ : WeierstrassCurve R} [V₁.IsElliptic]
    [V₂.IsElliptic] (h : V₁ = V₂) : V₁.j = V₂.j := by
  subst h
  rfl

private theorem lift_eq_adjoin_map (K : Type u) [Field K] (L₀ : IntermediateField (F₀ K) (Ω₀ K)) :
    lift K L₀ = IntermediateField.adjoin (RatFunc K)
      ((L₀.map (Ω₀ K).val : IntermediateField (F₀ K) (Ω K)) : Set (Ω K)) := by
  unfold ModularCurve.SigmaDescent.lift
  rfl

private theorem frobContract_lift (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (hfr : E₀.map (frobenius K q) = E₀)
    (L₀ : IntermediateField (F₀ K) (Ω₀ K)) [Normal (F₀ K) L₀]
    (hfin : FiniteDimensional K⟮algebraMap (RatFunc K) (lift K L₀) RatFunc.X⟯ (lift K L₀))
    (hgal : IsGalois K⟮algebraMap (RatFunc K) (lift K L₀) RatFunc.X⟯ (lift K L₀)) :
    FrobContract K q E₀ (lift K L₀) (algebraMap (RatFunc K) (lift K L₀) RatFunc.X) := by
  intro W₀ hW₀

  have hΨ := closureFrob_algebraMap K q (Ω K)
  have hx₀ : closureFrob K q (Ω K) (xΩ K) = xΩ K := closureFrob_X K q (Ω K)
  have hK : ∀ a : K, closureFrob K q (Ω K) (algebraMap K (Ω K) a) =
      algebraMap K (Ω K) (frobeniusEquiv K q a) :=
    closureFrob_algebraMap_base' K q (Ω K)

  haveI : Normal (F₀ K) (L₀.map (Ω₀ K).val) := Normal.of_algEquiv (L₀.equivMap (Ω₀ K).val)
  have hM : ∀ x, x ∈ lift K L₀ ↔ closureFrob K q (Ω K) x ∈ lift K L₀ := fun x => by
    rw [lift_eq_adjoin_map]
    exact mem_adjoin_iff_apply_mem_adjoin_of_apply_eq (closureFrob K q (Ω K)) (ratFuncFrob K q)
      hΨ hx₀ (L₀.map (Ω₀ K).val) x

  obtain ⟨g, hga, hgfix⟩ := SigmaFrobeniusPackaging.exists_semilinearAut_pow q (closureFrob K q (Ω K))
    (frobeniusEquiv K q) (fun _ => rfl) hK (lift K L₀) hM
  have hgt : g • algebraMap (RatFunc K) (lift K L₀) RatFunc.X =
      algebraMap (RatFunc K) (lift K L₀) RatFunc.X :=
    hgfix _ hx₀

  have hj : E₀.j ^ q = E₀.j := by
    have h := E₀.map_j (frobenius K q)
    rw [j_congr hfr, frobenius_def] at h
    exact h.symm

  exact exists_semilinearAut_smul_place_eq K q (algebraMap (RatFunc K) (lift K L₀) RatFunc.X)
    E₀.j hj hfin hgal g hga hgt W₀ hW₀

end ModularCurve.FrobLift
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end Corollary
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigmaFrobeniusPart
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section SigmaReductionPart

universe u

p2m_open "AlgebraicCurve ModularCurve~map_vcYInv~map_vcXInv~CycSub P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine"
open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace SigmaRed
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

p2m_open "WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing ValuationSubring"

namespace SigmaReductionCoordinates

section Coord

variable {K : Type*} [Field K]

variable {K' : Type*} [Field K'] (φ : K →+* K')

end Coord
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section IntegralCoord

variable {M : Type*} [Field M] {A : ValuationSubring M}

private lemma coe_map_u (C₀ : VariableChange A) :
    (((C₀.map A.subtype).u : Mˣ) : M) = ((C₀.u : Aˣ) : A) := rfl

private lemma coe_map_u_inv (C₀ : VariableChange A) :
    (((C₀.map A.subtype).u⁻¹ : Mˣ) : M) = ((C₀.u⁻¹ : Aˣ) : A) := by
  simp only [VariableChange.map, Units.coe_map_inv]; rfl

private lemma vcXInv_map_subtype (C₀ : VariableChange A) (x : M) :
    vcXInv (C₀.map A.subtype) x = ((C₀.u⁻¹ : Aˣ) : A) ^ 2 * (x - (C₀.r : M)) := by
  rw [vcXInv, coe_map_u_inv]; rfl

private lemma vcYInv_map_subtype (C₀ : VariableChange A) (x y : M) :
    vcYInv (C₀.map A.subtype) x y =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 3 * (y - (C₀.t : M) - (C₀.s : M) * (x - (C₀.r : M))) := by
  rw [vcYInv, coe_map_u_inv]; rfl

private lemma vcXInv_mem_iff (C₀ : VariableChange A) (x : M) :
    vcXInv (C₀.map A.subtype) x ∈ A ↔ x ∈ A := by
  constructor
  · intro h
    have hx : x = vcX (C₀.map A.subtype) (vcXInv (C₀.map A.subtype) x) := (vcX_vcXInv x).symm
    rw [hx, vcX, coe_map_u]
    exact add_mem (mul_mem (pow_mem (SetLike.coe_mem _) 2) h) (SetLike.coe_mem C₀.r)
  · intro hx
    rw [vcXInv_map_subtype]
    exact mul_mem (pow_mem (SetLike.coe_mem _) 2) (sub_mem hx (SetLike.coe_mem C₀.r))

private lemma vcYInv_mem (C₀ : VariableChange A) {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    vcYInv (C₀.map A.subtype) x y ∈ A := by
  rw [vcYInv_map_subtype]
  exact mul_mem (pow_mem (SetLike.coe_mem _) 3)
    (sub_mem (sub_mem hy (SetLike.coe_mem C₀.t))
      (mul_mem (SetLike.coe_mem C₀.s) (sub_mem hx (SetLike.coe_mem C₀.r))))

private lemma residue_vcXInv (C₀ : VariableChange A) {x : M} (hx : x ∈ A)
    (h : vcXInv (C₀.map A.subtype) x ∈ A) :
    residue A ⟨vcXInv (C₀.map A.subtype) x, h⟩ =
      vcXInv (C₀.map (residue A)) (residue A ⟨x, hx⟩) := by
  have hA : (⟨vcXInv (C₀.map A.subtype) x, h⟩ : A) =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 2 * (⟨x, hx⟩ - C₀.r) := by
    apply Subtype.ext
    show vcXInv (C₀.map A.subtype) x = _
    rw [vcXInv_map_subtype]
    push_cast
    ring
  rw [hA, vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

private lemma residue_vcYInv (C₀ : VariableChange A) {x y : M} (hx : x ∈ A) (hy : y ∈ A)
    (h : vcYInv (C₀.map A.subtype) x y ∈ A) :
    residue A ⟨vcYInv (C₀.map A.subtype) x y, h⟩ =
      vcYInv (C₀.map (residue A)) (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
  have hA : (⟨vcYInv (C₀.map A.subtype) x y, h⟩ : A) =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 3 * (⟨y, hy⟩ - C₀.t - C₀.s * (⟨x, hx⟩ - C₀.r)) := by
    apply Subtype.ext
    show vcYInv (C₀.map A.subtype) x y = _
    rw [vcYInv_map_subtype]
    push_cast
    ring
  rw [hA, vcYInv, VariableChange.map, Units.coe_map_inv]
  simp only [map_mul, map_pow, map_sub]
  rfl

end IntegralCoord
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section IntegralChange

variable {M : Type*} [Field M] {A : ValuationSubring M}

private lemma coe_notMem_nonunits_of_isUnit {a : A} (ha : IsUnit a) : (a : M) ∉ A.nonunits := by
  rw [coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, not_not]
  exact ha

private lemma pow_mem_nonunits {a : M} (ha : a ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) :
    a ^ n ∈ A.nonunits := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using ha
    · rw [pow_succ]
      exact A.nonunits.mul_mem (ih hpos.ne') ha

private lemma mem_of_sq_add_mul_eq {z b c : M} (hb : b ∈ A) (hc : c ∈ A) (h : z ^ 2 + b * z = c) :
    z ∈ A := by
  by_contra hz
  have hz0 : z ≠ 0 := fun h0 => hz (h0 ▸ A.zero_mem)
  have hzi : z⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem hz
  have key : (1 : M) = c * (z⁻¹ * z⁻¹) - b * z⁻¹ := by
    field_simp
    linear_combination h
  refine A.one_notMem_nonunits ?_
  rw [key]
  exact A.nonunits.sub_mem (A.mul_mem_nonunits hc (A.nonunits.mul_mem hzi hzi))
    (A.mul_mem_nonunits hb hzi)

private theorem exists_map_subtype_eq_of_smul_eq (W W' : WeierstrassCurve A) (g : VariableChange M)
    (hg : g • W'.map A.subtype = W.map A.subtype) (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) :
    ∃ g₀ : VariableChange A, g₀.map A.subtype = g := by
  obtain ⟨gu, r, s, t⟩ := g

  set u : M := (gu : M) with hu_def
  have hu0 : u ≠ 0 := gu.ne_zero
  have huinv : ((gu⁻¹ : Mˣ) : M) = u⁻¹ := Units.val_inv_eq_inv_val gu

  have hΔ : ((W.Δ : A) : M) = u⁻¹ ^ 12 * ((W'.Δ : A) : M) := by
    have h := congrArg WeierstrassCurve.Δ hg
    rw [variableChange_Δ, map_Δ, map_Δ] at h
    dsimp only at h
    rw [huinv] at h
    exact h.symm
  have hΔW : ((W.Δ : A) : M) ∉ A.nonunits := coe_notMem_nonunits_of_isUnit hW
  have hΔW' : ((W'.Δ : A) : M) ∉ A.nonunits := coe_notMem_nonunits_of_isUnit hW'

  have hu : u ∈ A ∧ u⁻¹ ∈ A := by
    rcases A.mem_or_inv_mem u with huA | huA
    · refine ⟨huA, A.inv_mem_of_notMem_nonunits fun hun => hΔW' ?_⟩
      have h' : ((W'.Δ : A) : M) = ((W.Δ : A) : M) * u ^ 12 := by
        rw [hΔ]; field_simp
      rw [h']
      exact A.mul_mem_nonunits (SetLike.coe_mem _) (pow_mem_nonunits hun (by norm_num))
    · refine ⟨?_, huA⟩
      have hun : u⁻¹ ∉ A.nonunits := fun hun => hΔW <| by
        rw [hΔ, mul_comm]
        exact A.mul_mem_nonunits (SetLike.coe_mem _) (pow_mem_nonunits hun (by norm_num))
      simpa using A.inv_mem_of_notMem_nonunits hun
  obtain ⟨huA, huiA⟩ := hu

  let u₀ : Aˣ := ⟨⟨u, huA⟩, ⟨u⁻¹, huiA⟩, Subtype.ext (mul_inv_cancel₀ hu0),
    Subtype.ext (inv_mul_cancel₀ hu0)⟩

  have h2A : (2 : M) ∈ A := by
    have : (2 : M) = ((2 : ℕ) : M) := by norm_num
    rw [this]; exact A.natCast_mem 2
  have h3A : (3 : M) ∈ A := by
    have : (3 : M) = ((3 : ℕ) : M) := by norm_num
    rw [this]; exact A.natCast_mem 3

  have ha₁ : (W'.map A.subtype).a₁ ∈ A := SetLike.coe_mem W'.a₁
  have ha₂ : (W'.map A.subtype).a₂ ∈ A := SetLike.coe_mem W'.a₂
  have ha₃ : (W'.map A.subtype).a₃ ∈ A := SetLike.coe_mem W'.a₃
  have ha₄ : (W'.map A.subtype).a₄ ∈ A := SetLike.coe_mem W'.a₄
  have ha₆ : (W'.map A.subtype).a₆ ∈ A := SetLike.coe_mem W'.a₆
  have hb₂ : (W'.map A.subtype).b₂ ∈ A := by rw [map_b₂]; exact SetLike.coe_mem _
  have hb₄ : (W'.map A.subtype).b₄ ∈ A := by rw [map_b₄]; exact SetLike.coe_mem _
  have hb₆ : (W'.map A.subtype).b₆ ∈ A := by rw [map_b₆]; exact SetLike.coe_mem _
  have hb₈ : (W'.map A.subtype).b₈ ∈ A := by rw [map_b₈]; exact SetLike.coe_mem _
  have hB₂ : (W.map A.subtype).a₂ ∈ A := SetLike.coe_mem W.a₂
  have hB₆ : (W.map A.subtype).a₆ ∈ A := SetLike.coe_mem W.a₆
  have hBb₆ : (W.map A.subtype).b₆ ∈ A := by rw [map_b₆]; exact SetLike.coe_mem _
  have hBb₈ : (W.map A.subtype).b₈ ∈ A := by rw [map_b₈]; exact SetLike.coe_mem _

  have h6 : u ^ 6 * (W.map A.subtype).b₆ = (W'.map A.subtype).b₆
      + 2 * r * (W'.map A.subtype).b₄ + r ^ 2 * (W'.map A.subtype).b₂ + 4 * r ^ 3 := by
    have h := congrArg WeierstrassCurve.b₆ hg
    rw [variableChange_b₆] at h
    dsimp only at h
    rw [huinv] at h
    rw [← h]; field_simp
  have h8 : u ^ 8 * (W.map A.subtype).b₈ = (W'.map A.subtype).b₈
      + 3 * r * (W'.map A.subtype).b₆ + 3 * r ^ 2 * (W'.map A.subtype).b₄
      + r ^ 3 * (W'.map A.subtype).b₂ + 3 * r ^ 4 := by
    have h := congrArg WeierstrassCurve.b₈ hg
    rw [variableChange_b₈] at h
    dsimp only at h
    rw [huinv] at h
    rw [← h]; field_simp
  have hr : r ∈ A := by
    by_contra hrA
    have hr0 : r ≠ 0 := fun h0 => hrA (h0 ▸ A.zero_mem)
    have hri : r⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem hrA
    have hri2 : r⁻¹ ^ 2 ∈ A.nonunits := pow_mem_nonunits hri two_ne_zero
    have hri3 : r⁻¹ ^ 3 ∈ A.nonunits := pow_mem_nonunits hri three_ne_zero
    have hri4 : r⁻¹ ^ 4 ∈ A.nonunits := pow_mem_nonunits hri four_ne_zero

    have h4 : (4 : M) =
        (u ^ 6 * (W.map A.subtype).b₆ - (W'.map A.subtype).b₆) * r⁻¹ ^ 3
          - 2 * (W'.map A.subtype).b₄ * r⁻¹ ^ 2 - (W'.map A.subtype).b₂ * r⁻¹ := by
      rw [h6]; field_simp; ring
    have h4m : (4 : M) ∈ A.nonunits := by
      rw [h4]
      refine A.nonunits.sub_mem (A.nonunits.sub_mem ?_ ?_) ?_
      · exact A.mul_mem_nonunits (sub_mem (mul_mem (pow_mem huA 6) hBb₆) hb₆) hri3
      · exact A.mul_mem_nonunits (mul_mem h2A hb₄) hri2
      · exact A.mul_mem_nonunits hb₂ hri

    have h3 : (3 : M) =
        (u ^ 8 * (W.map A.subtype).b₈ - (W'.map A.subtype).b₈) * r⁻¹ ^ 4
          - 3 * (W'.map A.subtype).b₆ * r⁻¹ ^ 3 - 3 * (W'.map A.subtype).b₄ * r⁻¹ ^ 2
          - (W'.map A.subtype).b₂ * r⁻¹ := by
      rw [h8]; field_simp; ring
    have h3m : (3 : M) ∈ A.nonunits := by
      rw [h3]
      refine A.nonunits.sub_mem (A.nonunits.sub_mem (A.nonunits.sub_mem ?_ ?_) ?_) ?_
      · exact A.mul_mem_nonunits (sub_mem (mul_mem (pow_mem huA 8) hBb₈) hb₈) hri4
      · exact A.mul_mem_nonunits (mul_mem h3A hb₆) hri3
      · exact A.mul_mem_nonunits (mul_mem h3A hb₄) hri2
      · exact A.mul_mem_nonunits hb₂ hri
    refine A.one_notMem_nonunits ?_
    have h1 : (1 : M) = 4 - 3 := by norm_num
    rw [h1]
    exact A.nonunits.sub_mem h4m h3m

  have h2 : u ^ 2 * (W.map A.subtype).a₂ =
      (W'.map A.subtype).a₂ - s * (W'.map A.subtype).a₁ + 3 * r - s ^ 2 := by
    have h := congrArg WeierstrassCurve.a₂ hg
    rw [variableChange_a₂] at h
    dsimp only at h
    rw [huinv] at h
    rw [← h]; field_simp
  have hs : s ∈ A := by
    refine mem_of_sq_add_mul_eq (b := (W'.map A.subtype).a₁)
      (c := (W'.map A.subtype).a₂ + 3 * r - u ^ 2 * (W.map A.subtype).a₂) ha₁ ?_ ?_
    · exact sub_mem (add_mem ha₂ (mul_mem h3A hr)) (mul_mem (pow_mem huA 2) hB₂)
    · linear_combination h2

  have h6' : u ^ 6 * (W.map A.subtype).a₆ =
      (W'.map A.subtype).a₆ + r * (W'.map A.subtype).a₄ + r ^ 2 * (W'.map A.subtype).a₂
        + r ^ 3 - t * (W'.map A.subtype).a₃ - t ^ 2 - r * t * (W'.map A.subtype).a₁ := by
    have h := congrArg WeierstrassCurve.a₆ hg
    rw [variableChange_a₆] at h
    dsimp only at h
    rw [huinv] at h
    rw [← h]; field_simp
  have ht : t ∈ A := by
    refine mem_of_sq_add_mul_eq (b := (W'.map A.subtype).a₃ + r * (W'.map A.subtype).a₁)
      (c := (W'.map A.subtype).a₆ + r * (W'.map A.subtype).a₄ + r ^ 2 * (W'.map A.subtype).a₂
        + r ^ 3 - u ^ 6 * (W.map A.subtype).a₆) (add_mem ha₃ (mul_mem hr ha₁)) ?_ ?_
    · exact sub_mem (add_mem (add_mem (add_mem ha₆ (mul_mem hr ha₄))
        (mul_mem (pow_mem hr 2) ha₂)) (pow_mem hr 3)) (mul_mem (pow_mem huA 6) hB₆)
    · linear_combination h6'

  refine ⟨⟨u₀, ⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩, ?_⟩
  ext <;> rfl

end IntegralChange
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Hom

variable {M : Type*} [Field M] [DecidableEq M]

end Hom
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigmaReductionCoordinates
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

open SigmaReductionCoordinates ModularCurve.SigmaSpine

section CastLemmas

variable {k : Type u} [Field k] [DecidableEq k]

end CastLemmas
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Stab

variable {K M : Type u} [Field K] [Field M] [Algebra K M] [DecidableEq M] (W₀ : Place K M)
  [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)]

omit [DecidableEq M] [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)] in
private theorem smul_mem_iff (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) (z : M) : σ • z ∈ W₀.toValuationSubring ↔ z ∈ W₀.toValuationSubring := by
  constructor
  · intro h
    have h' := ((stabRingEquiv W₀ σ hσ).symm ⟨σ • z, h⟩).2
    have hval : (((stabRingEquiv W₀ σ hσ).symm ⟨σ • z, h⟩ : W₀.toValuationSubring) : M) = z := inv_smul_smul σ z
    rwa [hval] at h'
  · intro h
    exact (stabRingEquiv W₀ σ hσ ⟨z, h⟩).2

omit [DecidableEq M] [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)] in
private theorem residueAut_residue (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) (a : W₀.toValuationSubring) :
    residueAut W₀ σ hσ (residue W₀.toValuationSubring a) = residue W₀.toValuationSubring (stabRingEquiv W₀ σ hσ a) := rfl

omit [DecidableEq M] [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)] in
private theorem residue_comp_stabRingEquiv (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) :
    (residue W₀.toValuationSubring).comp (stabRingEquiv W₀ σ hσ).toRingHom = (residueAut W₀ σ hσ).toRingHom.comp (residue W₀.toValuationSubring) :=
  RingHom.ext fun _ => rfl

omit [DecidableEq M] [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)] in
private theorem subtype_comp_stabRingEquiv (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) :
    W₀.toValuationSubring.subtype.comp (stabRingEquiv W₀ σ hσ).toRingHom =
      (SemilinearAut.toRingAut σ : M →+* M).comp W₀.toValuationSubring.subtype :=
  RingHom.ext fun _ => rfl

variable (W : WeierstrassCurve W₀.toValuationSubring)

private noncomputable def conj (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) : WeierstrassCurve W₀.toValuationSubring :=
  W.map (stabRingEquiv W₀ σ hσ).toRingHom

omit [DecidableEq M] [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)] in
private theorem conj_map_subtype (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) :
    (conj W₀ W σ hσ).map W₀.toValuationSubring.subtype = (W.map W₀.toValuationSubring.subtype).map (SemilinearAut.toRingAut σ : M →+* M) := by
  rw [conj, WeierstrassCurve.map_map, WeierstrassCurve.map_map, subtype_comp_stabRingEquiv]

omit [DecidableEq M] [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)] in
private theorem conj_map_residue (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) :
    (conj W₀ W σ hσ).map (residue W₀.toValuationSubring) = (W.map (residue W₀.toValuationSubring)).map (residueAut W₀ σ hσ).toRingHom := by
  rw [conj, WeierstrassCurve.map_map, WeierstrassCurve.map_map, residue_comp_stabRingEquiv]

omit [DecidableEq M] [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)] in
private theorem isUnit_conj_Δ (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀) (hW : IsUnit W.Δ) : IsUnit (conj W₀ W σ hσ).Δ := by
  rw [conj, map_Δ]; exact hW.map _

variable {t : M}

omit [DecidableEq (IsLocalRing.ResidueField W₀.toValuationSubring)] in

private theorem cocycle_smul_conj (ht : Transcendental K t) (κ : VariableChange M)
    (hκ : κ • (genCurve K t).baseChange M = W.map W₀.toValuationSubring.subtype)
    (σ : SemilinearAut K M) (hσt : σ • t = t) (hσ : σ • W₀ = W₀) :
    (κ * (κ.map (SemilinearAut.toRingAut σ : M →+* M))⁻¹) • (conj W₀ W σ hσ).map W₀.toValuationSubring.subtype =
      W.map W₀.toValuationSubring.subtype := by
  have h1 : (conj W₀ W σ hσ).map W₀.toValuationSubring.subtype =
      κ.map (SemilinearAut.toRingAut σ : M →+* M) • (genCurve K t).baseChange M := by
    rw [conj_map_subtype, ← hκ, ← map_variableChange, map_baseChange_genCurve ht _ hσt]
  rw [h1, ← mul_smul, inv_mul_cancel_right, hκ]

omit [DecidableEq M] in

private theorem heq_reducePoint_stab (hΔr : (W.map (residue W₀.toValuationSubring)).Δ ≠ 0) (g₀ : VariableChange W₀.toValuationSubring)
    (σ : SemilinearAut K M) (hσ : σ • W₀ = W₀)
    (hfix : g₀.map (residue W₀.toValuationSubring) • (W.map (residue W₀.toValuationSubring)).map (residueAut W₀ σ hσ).toRingHom = W.map (residue W₀.toValuationSubring))
    {x₁ y₁ x₂ y₂ : M} (h₁ : (W.map W₀.toValuationSubring.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map W₀.toValuationSubring.subtype).toAffine.Nonsingular x₂ y₂)
    (hx₂ : x₂ = vcXInv (g₀.map W₀.toValuationSubring.subtype) (σ • x₁))
    (hy₂ : y₂ = vcYInv (g₀.map W₀.toValuationSubring.subtype) (σ • x₁) (σ • y₁)) :
    HEq (vcInvFun (g₀.map (residue W₀.toValuationSubring)) ((W.map (residue W₀.toValuationSubring)).map (residueAut W₀ σ hσ).toRingHom).toAffine
        (mapPoint (residueAut W₀ σ hσ).toRingHom (reducePoint hΔr (.some x₁ y₁ h₁))))
      (reducePoint hΔr (.some x₂ y₂ h₂)) := by
  subst hx₂ hy₂
  by_cases hx₁ : x₁ ∈ W₀.toValuationSubring
  · have hy₁ : y₁ ∈ W₀.toValuationSubring := Affine.Y_mem_of_X_mem W h₁.1 hx₁
    have hσx₁ : σ • x₁ ∈ W₀.toValuationSubring := (smul_mem_iff W₀ σ hσ x₁).mpr hx₁
    have hσy₁ : σ • y₁ ∈ W₀.toValuationSubring := (smul_mem_iff W₀ σ hσ y₁).mpr hy₁
    have hx₂ : vcXInv (g₀.map W₀.toValuationSubring.subtype) (σ • x₁) ∈ W₀.toValuationSubring := (vcXInv_mem_iff g₀ _).mpr hσx₁
    have hy₂ : vcYInv (g₀.map W₀.toValuationSubring.subtype) (σ • x₁) (σ • y₁) ∈ W₀.toValuationSubring := vcYInv_mem g₀ hσx₁ hσy₁
    have hresx : residue W₀.toValuationSubring ⟨σ • x₁, hσx₁⟩ = residueAut W₀ σ hσ (residue W₀.toValuationSubring ⟨x₁, hx₁⟩) := rfl
    have hresy : residue W₀.toValuationSubring ⟨σ • y₁, hσy₁⟩ = residueAut W₀ σ hσ (residue W₀.toValuationSubring ⟨y₁, hy₁⟩) := rfl
    rw [reducePoint_some_of_mem hΔr h₁ hx₁, reducePoint_some_of_mem hΔr h₂ hx₂, mapPoint_some, vcInvFun_some]
    apply heq_some_of_eq hfix
    · rw [residue_vcXInv g₀ hσx₁ hx₂, hresx]
      rfl
    · rw [ValuationSubring.residue_eq_of_coe_eq W₀.toValuationSubring _
        (v := ⟨vcYInv (g₀.map W₀.toValuationSubring.subtype) (σ • x₁) (σ • y₁), hy₂⟩) rfl,
        residue_vcYInv g₀ hσx₁ hσy₁ hy₂, hresx, hresy]
      rfl
  · have hσx₁ : σ • x₁ ∉ W₀.toValuationSubring := fun hmem => hx₁ ((smul_mem_iff W₀ σ hσ x₁).mp hmem)
    have hx₂ : vcXInv (g₀.map W₀.toValuationSubring.subtype) (σ • x₁) ∉ W₀.toValuationSubring := by
      rw [vcXInv_mem_iff]; exact hσx₁
    rw [reducePoint_some_of_notMem hΔr h₁ hx₁, reducePoint_some_of_notMem hΔr h₂ hx₂, mapPoint_zero,
      vcInvFun_zero]
    exact heq_zero_of_eq hfix

end Stab
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

private theorem reductionContract_holds (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] : ReductionContract K E₀ := by
  intro M _ _ _ t ht hfin W₀ hW₀ _ W κ hκ hΔ
  classical

  have hΔr : (W.map (residue W₀.toValuationSubring)).Δ ≠ 0 := reducedΔ_ne_zero W₀ hΔ
  have hθ : ∀ P, reduceAlongHom W₀ W κ hκ hΔ P =
      reducePoint hΔr (SigmaSpine.castPt hκ (vcInvFun κ ((genCurve K t).baseChange M).toAffine P)) := by
    intro P
    show reducePoint hΔr (SigmaSpine.castAddHom hκ (vcInvFun κ ((genCurve K t).baseChange M).toAffine P)) = _
    rw [castAddHom_apply]
  refine ⟨?_, ?_⟩
  ·
    intro n P hn hP hθP
    cases P with
    | zero => rfl
    | some x y h =>
      exfalso
      have hQ : n • (SigmaSpine.castPt hκ (vcInvFun κ ((genCurve K t).baseChange M).toAffine (.some x y h))) = 0 := by
        have := congrArg ((SigmaSpine.castAddHom hκ).comp
          (SigmaSpine.vcInvAddHom κ ((genCurve K t).baseChange M))) hP
        rw [map_nsmul, _root_.map_zero, AddMonoidHom.comp_apply, castAddHom_apply] at this
        exact this
      rw [hθ] at hθP
      rw [vcInvFun_some, castPt_some] at hQ hθP
      have hx : vcXInv κ x ∈ W₀.toValuationSubring :=
        X_mem_of_nsmul_eq_zero_of_formalCoordinates (W := W) hn _ hQ
      rw [reducePoint_some_of_mem hΔr _ hx] at hθP
      exact Point.some_ne_zero _ hθP
  ·
    have hg : ∀ (σ : SemilinearAut K M), σ • t = t → ∀ hσ : σ • W₀ = W₀,
        ∃ g₀ : VariableChange W₀.toValuationSubring,
          g₀.map W₀.toValuationSubring.subtype = κ * (κ.map (SemilinearAut.toRingAut σ : M →+* M))⁻¹ :=
      fun σ hσt hσ => exists_map_subtype_eq_of_smul_eq W (conj W₀ W σ hσ) _
        (cocycle_smul_conj W₀ W ht κ hκ σ hσt hσ) hΔ (isUnit_conj_Δ W₀ W σ hσ hΔ)
    let g : SemilinearAut K M → VariableChange W₀.toValuationSubring := fun σ =>
      if h : σ • t = t ∧ σ • W₀ = W₀ then (hg σ h.1 h.2).choose else 1
    have hgσ : ∀ (σ : SemilinearAut K M) (hσt : σ • t = t) (hσ : σ • W₀ = W₀),
        (g σ).map W₀.toValuationSubring.subtype = κ * (κ.map (SemilinearAut.toRingAut σ : M →+* M))⁻¹ := by
      intro σ hσt hσ
      simp only [g, dif_pos (And.intro hσt hσ)]
      exact (hg σ hσt hσ).choose_spec
    have hgconj : ∀ (σ : SemilinearAut K M) (hσt : σ • t = t) (hσ : σ • W₀ = W₀), g σ • conj W₀ W σ hσ = W := by
      intro σ hσt hσ
      apply WeierstrassCurve.map_injective (f := W₀.toValuationSubring.subtype) Subtype.val_injective
      show (g σ • conj W₀ W σ hσ).map W₀.toValuationSubring.subtype = W.map W₀.toValuationSubring.subtype
      rw [← map_variableChange, hgσ σ hσt hσ, cocycle_smul_conj W₀ W ht κ hκ σ hσt hσ]
    have hgres : ∀ (σ : SemilinearAut K M) (hσt : σ • t = t) (hσ : σ • W₀ = W₀),
        (g σ).map (residue W₀.toValuationSubring) •
            (W.map (residue W₀.toValuationSubring)).map (residueAut W₀ σ hσ).toRingHom =
          W.map (residue W₀.toValuationSubring) := by
      intro σ hσt hσ
      rw [← conj_map_residue, map_variableChange, hgconj σ hσt hσ]
    refine ⟨g, ?_, ?_, ?_⟩
    · intro σ hσt hσ
      refine ⟨hgσ σ hσt hσ, hgres σ hσt hσ, fun P => ?_⟩
      cases P with
      | zero =>
        have hsl0 : semilinearPt ht σ hσt (0 : ((genCurve K t).baseChange M).toAffine.Point) = 0 := by
          rw [semilinearPt, mapPoint_zero, castPt_zero]
        rw [show (Point.zero : ((genCurve K t).baseChange M).toAffine.Point) = 0 from rfl, _root_.map_zero,
          mapPoint_zero, vcInvFun_zero, hsl0, _root_.map_zero]
        exact heq_zero_of_eq (hgres σ hσt hσ)
      | some x y h =>
        have hκfac : κ = (g σ).map W₀.toValuationSubring.subtype * κ.map (SemilinearAut.toRingAut σ : M →+* M) := by
          rw [hgσ σ hσt hσ, inv_mul_cancel_right]
        have hmx : ∀ z : M, σ • vcXInv κ z = vcXInv (κ.map (SemilinearAut.toRingAut σ : M →+* M)) (σ • z) :=
          fun z => map_vcXInv (SemilinearAut.toRingAut σ : M →+* M) κ z
        have hmy : ∀ z w : M, σ • vcYInv κ z w =
            vcYInv (κ.map (SemilinearAut.toRingAut σ : M →+* M)) (σ • z) (σ • w) :=
          fun z w => map_vcYInv (SemilinearAut.toRingAut σ : M →+* M) κ z w
        have key_x : vcXInv κ (σ • x) = vcXInv ((g σ).map W₀.toValuationSubring.subtype) (σ • vcXInv κ x) := by
          conv_lhs => rw [hκfac]
          rw [vcXInv_mul, hmx]
        have key_y : vcYInv κ (σ • x) (σ • y) =
            vcYInv ((g σ).map W₀.toValuationSubring.subtype) (σ • vcXInv κ x) (σ • vcYInv κ x y) := by
          conv_lhs => rw [hκfac]
          rw [vcYInv_mul, hmx, hmy]
        have hsl : semilinearPt ht σ hσt (.some x y h) = .some (σ • x) (σ • y)
            ((map_baseChange_genCurve ht (SemilinearAut.toRingAut σ : M →+* M) hσt) ▸
              (WeierstrassCurve.Affine.map_nonsingular _ (SemilinearAut.toRingAut σ : M →+* M).injective x y).mpr h) := by
          rw [semilinearPt, mapPoint_some, castPt_some]
          rfl
        rw [hθ, hθ, hsl, vcInvFun_some, vcInvFun_some, castPt_some, castPt_some]
        exact heq_reducePoint_stab W₀ W hΔr (g σ) σ hσ (hgres σ hσt hσ) _ _ key_x key_y
    ·
      intro σ τ hσt hσ hτt hτ
      have hστt : (σ * τ) • t = t := by rw [mul_smul, hτt, hσt]
      have hστ : (σ * τ) • W₀ = W₀ := by rw [mul_smul, hτ, hσ]
      have hcomp : (SemilinearAut.toRingAut (σ * τ) : M →+* M) =
          (SemilinearAut.toRingAut σ : M →+* M).comp (SemilinearAut.toRingAut τ : M →+* M) :=
        RingHom.ext fun z => mul_smul σ τ z
      have hM : (g (σ * τ)).map W₀.toValuationSubring.subtype =
          (g σ * (g τ).map (stabRingEquiv W₀ σ hσ).toRingHom).map W₀.toValuationSubring.subtype := by
        rw [VariableChange.map_mul', VariableChange.map_map, subtype_comp_stabRingEquiv,
          ← VariableChange.map_map, hgσ _ hστt hστ, hgσ σ hσt hσ, hgσ τ hτt hτ, VariableChange.map_mul',
          VariableChange.map_inv', VariableChange.map_map, hcomp]
        group
      have hA : g (σ * τ) = g σ * (g τ).map (stabRingEquiv W₀ σ hσ).toRingHom :=
        VariableChange.map_injective Subtype.val_injective hM
      rw [hA, VariableChange.map_mul', VariableChange.map_map, residue_comp_stabRingEquiv, ← VariableChange.map_map]
    ·
      intro σ hσ r
      have hdeg : W₀.deg ≠ 0 := AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin t ht W₀
      haveI : Module.Finite K W₀.ResidueField := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
      obtain ⟨c, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := W₀.ResidueField)).2 r
      rw [IsScalarTower.algebraMap_apply K W₀.toValuationSubring W₀.ResidueField c]
      show residueAut W₀ _ hσ (residue _ (algebraMap K W₀.toValuationSubring c)) =
        residue _ (algebraMap K W₀.toValuationSubring c)
      rw [residueAut_residue]
      congr 1
      apply Subtype.ext
      show SemilinearAut.ofAlgAut (σ.restrictScalars K) • algebraMap K M c = algebraMap K M c
      rw [SemilinearAut.ofAlgAut_smul]
      exact (σ.restrictScalars K).commutes c

end ModularCurve.SigmaRed
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigmaReductionPart
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section SigmaDictionaryPart

universe u

noncomputable section

p2m_open "WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace SigmaCompositeLevel
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

section SummingSet

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

private theorem mem_oddOrderSummingSet_pred_iff {Q : W.toAffine.Point} {N : ℕ} (hQ : addOrderOf Q = N)
    (hN : 0 < N) (P : F × F) :
    P ∈ W.oddOrderSummingSet Q (N - 1) ↔
      ∃ R ∈ AddSubgroup.zmultiples Q, R ≠ 0 ∧ R.coordsOrZero = P := by
  classical
  have hfin : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (hQ ▸ hN)
  rw [mem_oddOrderSummingSet]
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    exact ⟨k • Q, AddSubgroup.nsmul_mem_zmultiples Q k,
      nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega), rfl⟩
  · rintro ⟨R, hR, hR0, rfl⟩
    rw [hfin.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hR
    obtain ⟨k, hk, rfl⟩ := hR
    rw [Finset.mem_range, hQ] at hk
    refine ⟨k, ?_, by omega, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (zero_nsmul Q) hR0
    · exact hk0

private theorem oddOrderSummingSet_pred_eq_of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ} [NeZero N]
    (hQ : addOrderOf Q = N) (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.oddOrderSummingSet Q (N - 1) = W.oddOrderSummingSet Q' (N - 1) := by
  have hQ' : addOrderOf Q' = N := by
    rw [← Nat.card_zmultiples, ← h, Nat.card_zmultiples, hQ]
  ext P
  rw [mem_oddOrderSummingSet_pred_iff hQ (NeZero.pos N),
    mem_oddOrderSummingSet_pred_iff hQ' (NeZero.pos N), h]

private theorem fullKernelQuotient_eq_of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ} [NeZero N]
    (hQ : addOrderOf Q = N) (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.fullKernelQuotient Q N = W.fullKernelQuotient Q' N := by
  rw [fullKernelQuotient, fullKernelQuotient, oddOrderSummingSet_pred_eq_of_zmultiples_eq hQ h]

end SummingSet
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section RatPointHom

variable {F F' : Type u} [Field F] [Field F'] (f : F →+* F')

private theorem j_congr {R : Type u} [CommRing R] {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂)
    {inst₁ : W₁.IsElliptic} {inst₂ : W₂.IsElliptic} :
    @WeierstrassCurve.j R _ W₁ inst₁ = @WeierstrassCurve.j R _ W₂ inst₂ := by
  subst h
  rfl

private theorem _root_.ModularCurve.SigmaCompositeLevel.fibrePoly_map (Φ : Polynomial (Polynomial ℤ)) (a : F) :
    fibrePoly Φ (f a) = (fibrePoly Φ a).map f := by
  unfold ModularCurve.fibrePoly
  rw [Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

p2m_export "ModularCurve.SigmaCompositeLevel" "fibrePoly_map"
private theorem map_veluGx (W : WeierstrassCurve F) (x y : F) :
    f (W.veluGx x y) = (W.map f).veluGx (f x) (f y) := by
  simp only [WeierstrassCurve.veluGx, map_sub, map_add, map_mul, map_pow, map_ofNat,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]

private theorem map_veluGy (W : WeierstrassCurve F) (x y : F) :
    f (W.veluGy x y) = (W.map f).veluGy (f x) (f y) := by
  simp only [WeierstrassCurve.veluGy, map_neg, map_add, map_mul, map_ofNat,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

variable [DecidableEq F] [DecidableEq F']

private theorem addOrderOf_ratPointHom {W : WeierstrassCurve F} (Q : W.toAffine.Point) :
    addOrderOf (mapPointHom f Q) = addOrderOf Q :=
  addOrderOf_injective (mapPointHom f) (fun _ _ h => mapPoint_injective f h) Q

private theorem coordsOrZero_ratPointHom {W : WeierstrassCurve F} (Q : W.toAffine.Point) :
    (mapPointHom f Q).coordsOrZero = Prod.map f f Q.coordsOrZero := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact Prod.ext (map_zero f).symm (map_zero f).symm
  · rfl

private theorem oddOrderSummingSet_ratPointHom {W : WeierstrassCurve F} (Q : W.toAffine.Point) (n : ℕ) :
    (W.map f).oddOrderSummingSet (mapPointHom f Q) n =
      (W.oddOrderSummingSet Q n).image (Prod.map f f) := by
  unfold WeierstrassCurve.oddOrderSummingSet
  rw [Finset.image_image]
  congr 1
  funext k
  rw [Function.comp_apply, ← map_nsmul (mapPointHom f) k Q, coordsOrZero_ratPointHom]

private theorem map_fullKernelQuotient {W : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ) :
    (W.fullKernelQuotient Q N).map f = (W.map f).fullKernelQuotient (mapPointHom f Q) N := by
  have hinj : ∀ P ∈ W.oddOrderSummingSet Q (N - 1), ∀ P' ∈ W.oddOrderSummingSet Q (N - 1),
      Prod.map f f P = Prod.map f f P' → P = P' :=
    fun P _ P' _ h => (f.injective.prodMap f.injective) h
  rw [fullKernelQuotient, fullKernelQuotient, WeierstrassCurve.map_veluQuotientOfSums,
    oddOrderSummingSet_ratPointHom, Finset.sum_image hinj, Finset.sum_image hinj, map_sum, map_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun P _ => ?_
  · show f (W.veluGx P.1 P.2) = (W.map f).veluGx (f P.1) (f P.2)
    exact map_veluGx f W P.1 P.2
  · show f (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2) =
      f P.1 * (W.map f).veluGx (f P.1) (f P.2) - f P.2 * (W.map f).veluGy (f P.1) (f P.2)
    rw [map_sub, map_mul, map_mul, map_veluGx, map_veluGy]

private theorem fullKernelQuotient_ratPointHom_Δ {W : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ) :
    ((W.map f).fullKernelQuotient (mapPointHom f Q) N).Δ = f (W.fullKernelQuotient Q N).Δ := by
  rw [← map_fullKernelQuotient, WeierstrassCurve.map_Δ]

private theorem fullKernelQuotient_ratPointHom_Δ_ne_zero_iff {W : WeierstrassCurve F} (Q : W.toAffine.Point)
    (N : ℕ) :
    ((W.map f).fullKernelQuotient (mapPointHom f Q) N).Δ ≠ 0 ↔ (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  rw [fullKernelQuotient_ratPointHom_Δ, map_ne_zero f]

private theorem fullKernelQuotient_ratPointHom_j {W : WeierstrassCurve F} (Q : W.toAffine.Point) (N : ℕ)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0)
    (hΔ' : ((W.map f).fullKernelQuotient (mapPointHom f Q) N).Δ ≠ 0) :
    @WeierstrassCurve.j F' _ ((W.map f).fullKernelQuotient (mapPointHom f Q) N)
        ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ =
      f (@WeierstrassCurve.j F _ (W.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by
  haveI : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  exact (j_congr (map_fullKernelQuotient f Q N).symm).trans ((W.fullKernelQuotient Q N).map_j f)

end RatPointHom
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Disc

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

private theorem fullKernelQuotient_Δ_ne_zero_of_odd {N : ℕ} (hN : Odd N) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  rw [W.fullKernelQuotient_eq_veluQuotient_of_odd Q hN hQ]
  refine W.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq ((N - 1) / 2) Q ?_
  rw [hQ]
  obtain ⟨m, rfl⟩ := hN
  omega

private theorem fullKernelQuotient_Δ_ne_zero_of_two_ne_zero (h2 : (2 : F) ≠ 0) {N : ℕ} [NeZero N]
    (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  classical
  let f : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have h2' : (2 : AlgebraicClosure F) ≠ 0 := fun h =>
    h2 (f.injective (by rw [map_ofNat, map_zero]; exact h))
  have key := ModularCurve.TatePoint.fullKernelDiscAt_univ N h2' (W.map f) (mapPointHom f Q)
    (by rw [addOrderOf_ratPointHom, hQ])
  exact (fullKernelQuotient_ratPointHom_Δ_ne_zero_iff f Q N).mp key

private theorem fullKernelQuotient_Δ_ne_zero {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).Δ ≠ 0 := by
  rcases Nat.even_or_odd N with hev | hodd
  · refine fullKernelQuotient_Δ_ne_zero_of_two_ne_zero W (fun h2 => hN ?_) Q hQ
    obtain ⟨m, rfl⟩ := hev
    rw [Nat.cast_add, ← two_mul, h2, zero_mul]
  · exact fullKernelQuotient_Δ_ne_zero_of_odd W hodd Q hQ

end Disc
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Root

variable {F M : Type u} [Field F] [DecidableEq F] [Field M] [DecidableEq M] [IsAlgClosed M]
  (f : F →+* M)

private theorem isRoot_fibrePoly_j_fullKernelQuotient
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (data : ModularPolynomialData N)
    (W : WeierstrassCurve F) [W.IsElliptic] (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    {ι : Type} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Qfam : ι → (W.map f).toAffine.Point) (hQfam : ∀ i, addOrderOf (Qfam i) = N)
    (hinj : Function.Injective fun i => AddSubgroup.zmultiples (Qfam i))
    (i₀ : ι) (hi₀ : AddSubgroup.zmultiples (Qfam i₀) = AddSubgroup.zmultiples (mapPointHom f Q)) :
    (fibrePoly data.Φ W.j).IsRoot
      (@WeierstrassCurve.j F _ (W.fullKernelQuotient Q N)
        ⟨isUnit_iff_ne_zero.mpr (fullKernelQuotient_Δ_ne_zero W hN Q hQ)⟩) := by
  have hNM : (N : M) ≠ 0 := fun h => hN (f.injective (by rw [map_natCast, map_zero]; exact h))
  have hΔfam : ∀ i, ((W.map f).fullKernelQuotient (Qfam i) N).Δ ≠ 0 := fun i =>
    fullKernelQuotient_Δ_ne_zero (W.map f) hNM (Qfam i) (hQfam i)

  have hprod :=
    ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
      h0 hNM data (W.map f) hι Qfam hQfam hinj hΔfam

  have hrootM : (fibrePoly data.Φ (W.map f).j).IsRoot
      (@WeierstrassCurve.j M _ ((W.map f).fullKernelQuotient (Qfam i₀) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔfam i₀)⟩) := by
    rw [hprod, Polynomial.isRoot_prod]
    exact ⟨i₀, Finset.mem_univ i₀, by
      rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]⟩

  have hΔ' : ((W.map f).fullKernelQuotient (mapPointHom f Q) N).Δ ≠ 0 :=
    (fullKernelQuotient_ratPointHom_Δ_ne_zero_iff f Q N).mpr (fullKernelQuotient_Δ_ne_zero W hN Q hQ)
  have hjM : @WeierstrassCurve.j M _ ((W.map f).fullKernelQuotient (Qfam i₀) N)
        ⟨isUnit_iff_ne_zero.mpr (hΔfam i₀)⟩ =
      f (@WeierstrassCurve.j F _ (W.fullKernelQuotient Q N)
        ⟨isUnit_iff_ne_zero.mpr (fullKernelQuotient_Δ_ne_zero W hN Q hQ)⟩) :=
    (j_congr (fullKernelQuotient_eq_of_zmultiples_eq (hQfam i₀) hi₀)).trans
      (fullKernelQuotient_ratPointHom_j f Q N (fullKernelQuotient_Δ_ne_zero W hN Q hQ) hΔ')
  rw [hjM, WeierstrassCurve.map_j, fibrePoly_map] at hrootM
  exact hrootM.of_map f.injective

omit [IsAlgClosed M] in

private theorem zmultiples_ratPointHom_injective {W : WeierstrassCurve F} {ι : Type} (Q : ι → W.toAffine.Point)
    (hinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i)) :
    Function.Injective fun i => AddSubgroup.zmultiples (mapPointHom f (Q i)) := by
  intro i j h
  apply hinj
  have h' : (AddSubgroup.zmultiples (Q i)).map (mapPointHom f) =
      (AddSubgroup.zmultiples (Q j)).map (mapPointHom f) := by
    simpa only [AddMonoidHom.map_zmultiples] using h
  exact AddSubgroup.map_injective (fun _ _ h => mapPoint_injective f h) h'

private theorem isRoot_fibrePoly_j_fullKernelQuotient_of_family
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (data : ModularPolynomialData N)
    (W : WeierstrassCurve F) [W.IsElliptic]
    {ι : Type} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) (i : ι) :
    (fibrePoly data.Φ W.j).IsRoot
      (@WeierstrassCurve.j F _ (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩) := by
  classical
  exact isRoot_fibrePoly_j_fullKernelQuotient (algebraMap F (AlgebraicClosure F)) h0 hN data W (Q i)
    (hQ i) hι (fun k => mapPointHom (algebraMap F (AlgebraicClosure F)) (Q k))
    (fun k => by rw [addOrderOf_ratPointHom, hQ]) (zmultiples_ratPointHom_injective _ Q hQinj) i rfl

end Root
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section BaseChange

variable {F L : Type u} [Field F] [DecidableEq F] [Field L] [DecidableEq L] [Algebra F L]

private theorem ratPointHom_algebraMap_eq_pointMap {W : WeierstrassCurve F} (P : W.toAffine.Point) :
    mapPointHom (algebraMap F L) P =
      Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point) := by
  cases P <;> rfl

private theorem baseChange_fullKernelQuotient {W : WeierstrassCurve F} (P : W.toAffine.Point) (N : ℕ) :
    (W.fullKernelQuotient P N)⁄L =
      (W⁄L).fullKernelQuotient (Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point)) N := by
  rw [← ratPointHom_algebraMap_eq_pointMap]
  exact map_fullKernelQuotient (algebraMap F L) P N

private theorem baseChange_fullKernelQuotient_j {W : WeierstrassCurve F} (P : W.toAffine.Point) (N : ℕ)
    (hΔ : (W.fullKernelQuotient P N).Δ ≠ 0)
    (hΔ' : ((W⁄L).fullKernelQuotient
      (Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point)) N).Δ ≠ 0) :
    @WeierstrassCurve.j L _ ((W⁄L).fullKernelQuotient
        (Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point)) N)
        ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ =
      algebraMap F L (@WeierstrassCurve.j F _ (W.fullKernelQuotient P N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by
  haveI : (W.fullKernelQuotient P N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  exact (j_congr (baseChange_fullKernelQuotient P N).symm).trans
    ((W.fullKernelQuotient P N).map_j (algebraMap F L))

private theorem baseChange_fullKernelQuotient_Δ_ne_zero_iff {W : WeierstrassCurve F} (P : W.toAffine.Point) (N : ℕ) :
    ((W⁄L).fullKernelQuotient
        (Affine.Point.map (W' := W) (Algebra.ofId F L) (P : (W⁄F).toAffine.Point)) N).Δ ≠ 0 ↔
      (W.fullKernelQuotient P N).Δ ≠ 0 := by
  rw [← ratPointHom_algebraMap_eq_pointMap]
  exact fullKernelQuotient_ratPointHom_Δ_ne_zero_iff (algebraMap F L) P N

end BaseChange
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end ModularCurve.SigmaCompositeLevel
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

p2m_open "Polynomial WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine AddSubgroup"

namespace SigmaCyclicSubgroups

private theorem separable_fibrePoly_of_transcendental {K₀ F : Type u} [Field K₀] [Field F] [Algebra K₀ F]
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (hN : (N : F) ≠ 0) (jv : F) (hj : Transcendental K₀ jv) :
    (ModularCurve.fibrePoly data.Φ jv).Separable := by
  have hNK₀ : (N : K₀) ≠ 0 := by
    intro h
    apply hN
    rw [← map_natCast (algebraMap K₀ F) N, h, map_zero]
  have hsep :=
    ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero K₀ N data hNK₀
  have hinj : Function.Injective (Polynomial.aeval jv : Polynomial K₀ →ₐ[K₀] F) :=
    transcendental_iff_injective.mp hj
  let φ : RatFunc K₀ →+* F :=
    IsFractionRing.lift (g := (Polynomial.aeval jv : Polynomial K₀ →ₐ[K₀] F).toRingHom) hinj
  have hcoh : (φ.comp (algebraMap (Polynomial K₀) (RatFunc K₀))).comp
      (Polynomial.mapRingHom (Int.castRingHom K₀)) =
      Polynomial.eval₂RingHom (Int.castRingHom F) jv := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [IsFractionRing.lift_algebraMap]
    simp
  have hfib : ModularCurve.fibrePoly data.Φ jv =
      ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K₀))).map
        (algebraMap (Polynomial K₀) (RatFunc K₀))).map φ := by
    rw [ModularCurve.fibrePoly, Polynomial.map_map, Polynomial.map_map, hcoh]
  rw [hfib]
  exact hsep.map

private theorem injective_of_separable_prod {K : Type u} [Field K] {ι : Type} [Fintype ι]
    (c : ι → K) (p : Polynomial K) (hsep : p.Separable)
    (hp : p = ∏ i, (X - C (c i))) : Function.Injective c := by
  classical
  intro a b hab
  by_contra hne
  have hbmem : b ∈ Finset.univ.erase a :=
    Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ b⟩
  have hdvd : (X - C (c a)) * (X - C (c a)) ∣ p := by
    refine ⟨∏ i ∈ (Finset.univ.erase a).erase b, (X - C (c i)), ?_⟩
    rw [hp, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase (Finset.univ.erase a) _ hbmem, hab]
    ring
  exact Polynomial.not_isUnit_X_sub_C (c a) (hsep.squarefree _ hdvd)

section M3

variable {A : Type u} [AddCommGroup A]

private theorem isAddCyclic_zmultiples (g : A) : IsAddCyclic (zmultiples g) := by
  refine ⟨⟨g, mem_zmultiples g⟩, fun x => ?_⟩
  obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp x.2
  exact mem_zmultiples_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem exists_generator_of_isAddCyclic_card (H : AddSubgroup A) (N : ℕ)
    (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) :
    ∃ g : A, addOrderOf g = N ∧ H = zmultiples g := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h2 : addOrderOf g = Nat.card H := addOrderOf_eq_card_of_forall_mem_zmultiples hg
  refine ⟨(g : A), ?_, ?_⟩
  · exact (addOrderOf_injective H.subtype (AddSubgroup.subtype_injective H) g).trans
      (h2.trans hcard)
  · ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
      exact mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp hx
      rw [← hk]
      exact zsmul_mem g.2 k

private def cycSubEquiv (N : ℕ) :
    {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g} ≃
    {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N} where
  toFun C := ⟨C.1, by
    obtain ⟨g, hg, hC⟩ := C.2
    rw [hC]
    exact ⟨isAddCyclic_zmultiples g, by rw [Nat.card_zmultiples, hg]⟩⟩
  invFun H := ⟨H.1, by
    obtain ⟨g, h1, h2⟩ := exists_generator_of_isAddCyclic_card H.1 N H.2.1 H.2.2
    exact ⟨g, h1, h2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

private theorem natCard_cycSub_zmultiples_eq (N : ℕ) [NeZero N]
    (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ A N) :
    Nat.card {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g}
      = ModularCurve.dedekindPsi N := by
  rw [Nat.card_congr (cycSubEquiv N)]
  exact AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy N e

private theorem exists_family (N : ℕ) [NeZero N]
    (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ A N) :
    ∃ (ι : Type) (_ : Fintype ι) (Q : ι → A),
      Fintype.card ι = ModularCurve.dedekindPsi N ∧
      (∀ i, addOrderOf (Q i) = N) ∧
      Function.Injective (fun i => zmultiples (Q i)) ∧
      ∀ C : AddSubgroup A, (∃ g, addOrderOf g = N ∧ C = zmultiples g) →
        ∃ i, zmultiples (Q i) = C := by
  classical
  have hcount := natCard_cycSub_zmultiples_eq (A := A) N e
  have hfin : Finite {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g} :=
    (Nat.card_ne_zero.mp (by
      rw [hcount]
      exact (ModularCurve.dedekindPsi_pos N (NeZero.ne N)).ne')).2
  haveI := hfin
  haveI : Fintype {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g} :=
    Fintype.ofFinite _
  choose g hg hC using
    fun C : {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g} => C.2

  refine ⟨Fin (Fintype.card {C : AddSubgroup A // ∃ g, addOrderOf g = N ∧ C = zmultiples g}),
    inferInstance, fun i => g ((Fintype.equivFin _).symm i), ?_, fun i => hg _, ?_, ?_⟩
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcount]
  · intro i i' h
    apply (Fintype.equivFin _).symm.injective
    apply Subtype.ext
    rw [hC ((Fintype.equivFin _).symm i), hC ((Fintype.equivFin _).symm i')]
    exact h
  · intro C hCmem
    refine ⟨Fintype.equivFin _ ⟨C, hCmem⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact (hC ⟨C, hCmem⟩).symm

end M3
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section M4

variable {F L : Type u} [Field F] [Field L] [DecidableEq F] [DecidableEq L] [Algebra F L]

private noncomputable def ptMap (W : WeierstrassCurve F) :
    W.toAffine.Point →+ (W⁄L).toAffine.Point :=
  (WeierstrassCurve.Affine.Point.map (W' := W) (S := F) (Algebra.ofId F L) :
    W.toAffine.Point →+ (W⁄L).toAffine.Point)

private theorem ptMap_injective (W : WeierstrassCurve F) :
    Function.Injective (ptMap (L := L) W) :=
  WeierstrassCurve.Affine.Point.map_injective _

private theorem addOrderOf_ptMap (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    addOrderOf (ptMap (L := L) W P) = addOrderOf P := by
  have h := ptMap_injective (L := L) W
  exact addOrderOf_injective _ h P

private theorem map_zmultiples_ptMap (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    (zmultiples P).map (ptMap (L := L) W) = zmultiples (ptMap (L := L) W P) :=
  AddMonoidHom.map_zmultiples _ _

private theorem family_push (W : WeierstrassCurve F) (N : ℕ) {ι : Type} (Q : ι → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => zmultiples (Q i)) :
    (∀ i, addOrderOf (ptMap (L := L) W (Q i)) = N) ∧
      Function.Injective (fun i => zmultiples (ptMap (L := L) W (Q i))) := by
  refine ⟨fun i => by rw [addOrderOf_ptMap]; exact hQ i, fun a b h => ?_⟩
  apply hQinj
  have hmap : (zmultiples (Q a)).map (ptMap (L := L) W) =
      (zmultiples (Q b)).map (ptMap (L := L) W) := by
    rw [map_zmultiples_ptMap, map_zmultiples_ptMap]
    exact h
  exact AddSubgroup.map_injective (ptMap_injective W) hmap

end M4
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

private theorem fibrePoly_map {k l : Type u} [Field k] [Field l] (f : k →+* l)
    (Φ : Polynomial (Polynomial ℤ)) (a : k) :
    (ModularCurve.fibrePoly Φ a).map f = ModularCurve.fibrePoly Φ (f a) := by
  rw [ModularCurve.fibrePoly, ModularCurve.fibrePoly, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp

private theorem injective_of_separable_of_map_prod {F L : Type u} [Field F] [Field L] (emb : F →+* L)
    {ι : Type} [Fintype ι] (y : ι → F) (z : ι → L) (p : Polynomial F)
    (hsep : p.Separable)
    (hprod : p.map emb = ∏ i, (X - C (z i)))
    (hcompat : ∀ i, emb (y i) = z i) :
    Function.Injective y := by
  have hinj : Function.Injective z :=
    injective_of_separable_prod z (p.map emb) (hsep.map) hprod
  intro a b hab
  exact hinj (by rw [← hcompat a, ← hcompat b, hab])

private theorem card_roots_toFinset_eq_of_injective_family {F : Type u} [Field F] [DecidableEq F]
    (p : Polynomial F) (hp : p ≠ 0) {ι : Type} [Fintype ι] (y : ι → F)
    (hinj : Function.Injective y) (hroot : ∀ i, p.IsRoot (y i)) {m : ℕ}
    (hm : Fintype.card ι = m) (hdeg : p.natDegree = m) :
    p.roots.toFinset.card = m := by
  refine le_antisymm ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' p).trans_eq hdeg)) ?_
  have himg : Finset.univ.image y ⊆ p.roots.toFinset := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hp, hroot i⟩)
  calc m = Fintype.card ι := hm.symm
    _ = (Finset.univ.image y).card := (Finset.card_image_of_injective Finset.univ hinj).symm
    _ ≤ p.roots.toFinset.card := Finset.card_le_card himg

end SigmaCyclicSubgroups
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

namespace ModularCurve
p2m_export "ModularCurve" "fibrePoly qExpand dedekindPsi ModularPolynomialData coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full jqModC map_jqModC coeffMap coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffMap_qExpand ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero TatePoint.fullKernelDiscAt_univ dedekindPsi_pos exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental monic_fibrePoly natDegree_fibrePoly nonempty_modularPolynomialData"
namespace SigmaCompositeRoots
p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub"

p2m_open "Polynomial ModularCurve~map_vcYInv~map_vcXInv~CycSub P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve WeierstrassCurve~map_veluGy~map_veluGx WeierstrassCurve.Affine"

section Brick

variable {F : Type u} [Field F] [DecidableEq F] {N : ℕ} [NeZero N]

private noncomputable abbrev jQuot (W : WeierstrassCurve F) (Q : W.toAffine.Point)
    (hΔ : (W.fullKernelQuotient Q N).Δ ≠ 0) : F :=
  @WeierstrassCurve.j F _ (W.fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩

private theorem isRoot_fibrePoly_jQuot
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    (hN : (N : F) ≠ 0) (data : ModularPolynomialData N) (W : WeierstrassCurve F) [W.IsElliptic]
    {ι : Type} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) (i : ι) :
    (fibrePoly data.Φ W.j).IsRoot (jQuot W (Q i) (hΔ i)) :=
  ModularCurve.SigmaCompositeLevel.isRoot_fibrePoly_j_fullKernelQuotient_of_family h0 hN data W hι Q hQ
    hQinj hΔ i

private theorem jQuot_injective_of_transcendental
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {K₀ : Type u} [Field K₀] [Algebra K₀ F]
    (hN : (N : F) ≠ 0) (data : ModularPolynomialData N) (W : WeierstrassCurve F) [W.IsElliptic]
    (hj : Transcendental K₀ W.j)
    {ι : Type} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0) :
    Function.Injective (fun i => jQuot W (Q i) (hΔ i)) := by
  classical
  let L := AlgebraicClosure F
  haveI : DecidableEq L := Classical.decEq _
  let emb : F →+* L := algebraMap F L
  have hNL : (N : L) ≠ 0 := fun h => hN (emb.injective (by rw [map_natCast, map_zero]; exact h))
  haveI : (W⁄L).IsElliptic := by
    rw [show W⁄L = W.map emb from rfl]
    infer_instance

  let QL : ι → (W⁄L).toAffine.Point := fun i => SigmaCyclicSubgroups.ptMap (L := L) W (Q i)
  obtain ⟨hQL, hQLinj⟩ := SigmaCyclicSubgroups.family_push (L := L) W N Q hQ hQinj

  have hΔL : ∀ i, ((W⁄L).fullKernelQuotient (QL i) N).Δ ≠ 0 := fun i =>
    (ModularCurve.SigmaCompositeLevel.baseChange_fullKernelQuotient_Δ_ne_zero_iff (L := L) (Q i) N).mpr (hΔ i)

  have hprod :=
    ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
      h0 hNL data (W⁄L) hι QL hQL hQLinj hΔL

  let z : ι → L := fun i => @WeierstrassCurve.j L _ ((W⁄L).fullKernelQuotient (QL i) N)
      ⟨isUnit_iff_ne_zero.mpr (hΔL i)⟩

  have hmap : (fibrePoly data.Φ W.j).map emb = ∏ i, (X - C (z i)) := by
    have hjWL : (W⁄L).j = emb W.j := W.map_j emb
    rw [SigmaCyclicSubgroups.fibrePoly_map emb data.Φ W.j, ← hjWL]
    exact hprod

  have hsep : (fibrePoly data.Φ W.j).Separable :=
    SigmaCyclicSubgroups.separable_fibrePoly_of_transcendental N data hN W.j hj

  have hcompat : ∀ i, emb (jQuot W (Q i) (hΔ i)) = z i := fun i =>
    (ModularCurve.SigmaCompositeLevel.baseChange_fullKernelQuotient_j (L := L) (Q i) N (hΔ i) (hΔL i)).symm
  exact SigmaCyclicSubgroups.injective_of_separable_of_map_prod emb
    (fun i => jQuot W (Q i) (hΔ i)) z (fibrePoly data.Φ W.j) hsep hmap hcompat

private theorem card_roots_toFinset_fibrePoly_eq_dedekindPsi
    (h0 : ∀ {K₀ : Type u} [Field K₀] [IsAlgClosed K₀] [CharZero K₀] [DecidableEq K₀]
      {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
      (W : WeierstrassCurve K₀) [W.IsElliptic] (_hj : Transcendental ℚ W.j)
      {ι : Type} [Fintype ι] (_hι : Fintype.card ι = dedekindPsi N)
      (Q : ι → W.toAffine.Point) (_hQ : ∀ i, addOrderOf (Q i) = N)
      (_hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
      (hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0),
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K₀ _
          (W.fullKernelQuotient (Q i) N) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)))
    {K₀ : Type u} [Field K₀] [Algebra K₀ F]
    (hN : (N : F) ≠ 0) (data : ModularPolynomialData N) (W : WeierstrassCurve F) [W.IsElliptic]
    (hj : Transcendental K₀ W.j)
    (hfull : ∀ d, d ∣ N → Nat.card (Submodule.torsionBy ℤ W.toAffine.Point d) = d ^ 2) :
    ((data.Φ.map
        (Polynomial.eval₂RingHom (Int.castRingHom F) W.j)).roots.toFinset).card
      = dedekindPsi N := by
  classical

  show (fibrePoly data.Φ W.j).roots.toFinset.card = dedekindPsi N

  obtain ⟨e⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (NeZero.ne N) hfull
  obtain ⟨ι, hιfin, Q, hι, hQ, hQinj, -⟩ :=
    SigmaCyclicSubgroups.exists_family (A := W.toAffine.Point) N e
  letI := hιfin

  have hΔ : ∀ i, (W.fullKernelQuotient (Q i) N).Δ ≠ 0 := fun i =>
    ModularCurve.SigmaCompositeLevel.fullKernelQuotient_Δ_ne_zero W hN (Q i) (hQ i)

  exact SigmaCyclicSubgroups.card_roots_toFinset_eq_of_injective_family (fibrePoly data.Φ W.j)
    (monic_fibrePoly data.monic W.j).ne_zero (fun i => jQuot W (Q i) (hΔ i))
    (jQuot_injective_of_transcendental h0 hN data W hj hι Q hQ hQinj hΔ)
    (isRoot_fibrePoly_jQuot h0 hN data W hι Q hQ hQinj hΔ)
    hι ((natDegree_fibrePoly data.monic W.j).trans data.natDegree_eq)

end Brick
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end ModularCurve.SigmaCompositeRoots
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve"
open scoped IntermediateField

namespace SigmaFullFieldFrobenius

private theorem coeffMap_jqModC {K : Type u} [Field K] (τ : K →+* K) : coeffMap τ (jqModC K) = jqModC K :=
  map_jqModC τ

section FullFrob

variable {K : Type u} [Field K] (N : ℕ)

private theorem coeffMap_mem_full (τ : K →+* K) {x : LaurentSeries K}
    (hx : x ∈ modularFunctionFieldFullC K N) :
    coeffMap τ x ∈ modularFunctionFieldFullC K N := by
  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪
      divisorExpansionsC K N) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [coeffMap_algebraMap]
        exact (modularFunctionFieldFullC K N).algebraMap_mem _
      · obtain ⟨d, hd0, hdN, rfl⟩ := hy
        haveI : NeZero d := hd0
        rw [coeffMap_qExpand, coeffMap_jqModC]
        exact jqModCd_mem_full K N hdN
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

private noncomputable def coeffRingAutFull (τ : K ≃+* K) :
    modularFunctionFieldFullC K N ≃+* modularFunctionFieldFullC K N where
  toFun x := ⟨coeffMap (τ : K →+* K) (x : LaurentSeries K), coeffMap_mem_full N (τ : K →+* K) x.2⟩
  invFun x := ⟨coeffMap (τ.symm : K →+* K) (x : LaurentSeries K),
    coeffMap_mem_full N (τ.symm : K →+* K) x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (τ.symm : K →+* K) (coeffMap (τ : K →+* K) (x : LaurentSeries K))
      = (x : LaurentSeries K)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => τ.symm_apply_apply a) _, coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (τ : K →+* K) (coeffMap (τ.symm : K →+* K) (x : LaurentSeries K))
      = (x : LaurentSeries K)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => τ.apply_symm_apply a) _, coeffMap_id]
  map_mul' x y :=
    Subtype.ext (map_mul (coeffMap (τ : K →+* K)) (x : LaurentSeries K) (y : LaurentSeries K))
  map_add' x y :=
    Subtype.ext (map_add (coeffMap (τ : K →+* K)) (x : LaurentSeries K) (y : LaurentSeries K))

private theorem coeffRingAutFull_symm_algebraMap (τ : K ≃+* K) (a : K) :
    (coeffRingAutFull N τ).symm (algebraMap K (modularFunctionFieldFullC K N) a)
      = algebraMap K (modularFunctionFieldFullC K N) (τ.symm a) :=
  Subtype.ext (coeffMap_algebraMap (τ.symm : K →+* K) a)

private theorem coeffRingAutFull_symm_jq (τ : K ≃+* K) :
    (coeffRingAutFull N τ).symm ⟨jqModC K, jqModC_mem_full K N⟩
      = ⟨jqModC K, jqModC_mem_full K N⟩ :=
  Subtype.ext (map_jqModC (τ.symm : K →+* K))

private theorem coeffRingAutFull_symm_gen (τ : K ≃+* K) {d : ℕ} [NeZero d] (hd : d ∣ N) :
    (coeffRingAutFull N τ).symm ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩
      = ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ :=
  Subtype.ext <| by
    show coeffMap (τ.symm : K →+* K) (qExpand K d (jqModC K)) = qExpand K d (jqModC K)
    rw [coeffMap_qExpand, coeffMap_jqModC]

end FullFrob
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Twist

variable {K : Type u} [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K]
  (N : ℕ) [NeZero N] {M : Type u} [Field M] [Algebra K M]

private noncomputable def twistAlgHom (F : M →+* M) (hF : ∀ a : K, F (algebraMap K M a) = algebraMap K M (a ^ q))
    (φ : modularFunctionFieldFullC K N →ₐ[K] M) : modularFunctionFieldFullC K N →ₐ[K] M :=
  { F.comp (φ.toRingHom.comp ((coeffRingAutFull N (frobeniusEquiv K q)).symm :
      modularFunctionFieldFullC K N →+* modularFunctionFieldFullC K N)) with
    commutes' := fun a => by
      show F (φ ((coeffRingAutFull N (frobeniusEquiv K q)).symm
        (algebraMap K (modularFunctionFieldFullC K N) a))) = algebraMap K M a
      rw [coeffRingAutFull_symm_algebraMap, φ.commutes, hF]
      congr 1
      have h := (frobeniusEquiv K q).apply_symm_apply a
      rwa [coe_frobeniusEquiv, frobenius_def] at h }

variable (F : M →+* M) (hF : ∀ a : K, F (algebraMap K M a) = algebraMap K M (a ^ q))
  (φ : modularFunctionFieldFullC K N →ₐ[K] M)

omit [NeZero N] in
private theorem twistAlgHom_apply (x : modularFunctionFieldFullC K N) :
    twistAlgHom q N F hF φ x = F (φ ((coeffRingAutFull N (frobeniusEquiv K q)).symm x)) :=
  rfl

omit [NeZero N] in

private theorem twistAlgHom_jq :
    twistAlgHom q N F hF φ ⟨jqModC K, jqModC_mem_full K N⟩ = F (φ ⟨jqModC K, jqModC_mem_full K N⟩) := by
  rw [twistAlgHom_apply, coeffRingAutFull_symm_jq]

omit [NeZero N] in

private theorem twistAlgHom_gen {d : ℕ} [NeZero d] (hd : d ∣ N) :
    twistAlgHom q N F hF φ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩
      = F (φ ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩) := by
  rw [twistAlgHom_apply, coeffRingAutFull_symm_gen N _ hd]

end Twist
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section A

variable {K : Type u} [Field K] (N : ℕ) [NeZero N] {M : Type u} [Field M] [Algebra K M]

private theorem a_of_valueKeyed {ι : Type u} (Rel : ι → ι → Prop) {P : M → Prop} (t : M)
    (e : {ψ : modularFunctionFieldFullC K N →ₐ[K] M // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t} ≃
      {y : M // P y})
    (he : ∀ ψ, ((e ψ : {y : M // P y}) : M)
      = ψ.1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩)
    (jroot : ι → {y : M // P y})
    (σ : M →ₐ[K] M) (hσt : σ t = t)
    (hnat : ∀ H H' : ι, Rel H H' → ((jroot H' : {y : M // P y}) : M) = σ (jroot H))
    (H H' : ι) (hHH' : Rel H H') :
    ((e.symm (jroot H')).1 : modularFunctionFieldFullC K N →ₐ[K] M)
      = σ.comp (e.symm (jroot H)).1 := by
  set φ : modularFunctionFieldFullC K N →ₐ[K] M := (e.symm (jroot H)).1 with hφ
  have hφt : φ ⟨jqModC K, jqModC_mem_full K N⟩ = t := (e.symm (jroot H)).2
  have hφN : ((jroot H : {y : M // P y}) : M)
      = φ ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩ := by
    have h := he (e.symm (jroot H))
    rwa [Equiv.apply_symm_apply] at h
  have hψt : (σ.comp φ) ⟨jqModC K, jqModC_mem_full K N⟩ = t := by
    rw [AlgHom.comp_apply, hφt, hσt]
  have hval : e ⟨σ.comp φ, hψt⟩ = jroot H' := by
    apply Subtype.ext
    rw [he, hnat H H' hHH', hφN]
    rfl
  have hΦ' : e.symm (jroot H') = ⟨σ.comp φ, hψt⟩ := by
    rw [← hval, Equiv.symm_apply_apply]
  rw [hΦ']

end A
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section F5

variable {K : Type u} [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K]
  (N : ℕ) [NeZero N] {M : Type u} [Field M] [Algebra K M]

private theorem f5_of_valueKeyed {ι : Type u} (Rel : ι → ι → Prop) {P : M → Prop} (t : M)
    (e : {ψ : modularFunctionFieldFullC K N →ₐ[K] M // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t} ≃
      {y : M // P y})
    (he : ∀ ψ, ((e ψ : {y : M // P y}) : M)
      = ψ.1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩)
    (jroot : ι → {y : M // P y})
    (F : M →+* M) (hF : ∀ a : K, F (algebraMap K M a) = algebraMap K M (a ^ q)) (hFt : F t = t)
    (hnat : ∀ H H' : ι, Rel H H' → ((jroot H' : {y : M // P y}) : M) = F (jroot H))
    (H H' : ι) (hHH' : Rel H H') (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (e.symm (jroot H')).1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩
      = F ((e.symm (jroot H)).1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩) := by
  set φ : modularFunctionFieldFullC K N →ₐ[K] M := (e.symm (jroot H)).1 with hφ
  have hφt : φ ⟨jqModC K, jqModC_mem_full K N⟩ = t := (e.symm (jroot H)).2
  have hφN : ((jroot H : {y : M // P y}) : M)
      = φ ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩ := by
    have h := he (e.symm (jroot H))
    rwa [Equiv.apply_symm_apply] at h
  have hφ't : twistAlgHom q N F hF φ ⟨jqModC K, jqModC_mem_full K N⟩ = t := by
    rw [twistAlgHom_jq, hφt, hFt]
  have hval : e ⟨twistAlgHom q N F hF φ, hφ't⟩ = jroot H' := by
    apply Subtype.ext
    rw [he, hnat H H' hHH', hφN]
    exact twistAlgHom_gen q N F hF φ dvd_rfl
  have hΦ' : e.symm (jroot H') = ⟨twistAlgHom q N F hF φ, hφ't⟩ := by
    rw [← hval, Equiv.symm_apply_apply]
  rw [hΦ']
  exact twistAlgHom_gen q N F hF φ hd

end F5
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigmaFullFieldFrobenius
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

namespace SigmaQuotientNaturality

open ModularCurve.SigmaCompositeLevel

variable {M : Type u} [Field M] [DecidableEq M]

private def _root_.SigmaQuotientNaturality.castPt {V V' : WeierstrassCurve M} (h : V' = V) : V'.toAffine.Point ≃+ V.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

p2m_export "SigmaQuotientNaturality" "castPt"
private theorem fullKernelQuotient_castPt {V V' : WeierstrassCurve M} (h : V' = V) (P : V'.toAffine.Point)
    (N : ℕ) : V.fullKernelQuotient (castPt h P) N = V'.fullKernelQuotient P N := by
  subst h
  rfl

private theorem j_fullKernelQuotient_castPt_ratPointHom (W : WeierstrassCurve M) (ψ : M →+* M)
    (hE : W.map ψ = W) (g : W.toAffine.Point) (N : ℕ)
    (hΔ : (W.fullKernelQuotient g N).Δ ≠ 0)
    (hΔ' : (W.fullKernelQuotient (castPt hE (mapPointHom ψ g)) N).Δ ≠ 0) :
    @WeierstrassCurve.j M _ (W.fullKernelQuotient (castPt hE (mapPointHom ψ g)) N)
        ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      = ψ (@WeierstrassCurve.j M _ (W.fullKernelQuotient g N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by
  have hq : W.fullKernelQuotient (castPt hE (mapPointHom ψ g)) N
      = (W.map ψ).fullKernelQuotient (mapPointHom ψ g) N :=
    fullKernelQuotient_castPt hE _ N
  have hΔ'' : ((W.map ψ).fullKernelQuotient (mapPointHom ψ g) N).Δ ≠ 0 := by
    rw [← hq]
    exact hΔ'
  rw [j_congr hq (inst₂ := ⟨isUnit_iff_ne_zero.mpr hΔ''⟩)]
  exact fullKernelQuotient_ratPointHom_j ψ g N hΔ hΔ''

private theorem j_fullKernelQuotient_of_zmultiples_eq_map (W : WeierstrassCurve M) (ψ : M →+* M)
    (hE : W.map ψ = W) {g g' : W.toAffine.Point} {N : ℕ} [NeZero N] (hg' : addOrderOf g' = N)
    (hz : AddSubgroup.zmultiples g'
      = (AddSubgroup.zmultiples g).map ((castPt hE).toAddMonoidHom.comp (mapPointHom ψ)))
    (hΔ : (W.fullKernelQuotient g N).Δ ≠ 0) (hΔ' : (W.fullKernelQuotient g' N).Δ ≠ 0) :
    @WeierstrassCurve.j M _ (W.fullKernelQuotient g' N) ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      = ψ (@WeierstrassCurve.j M _ (W.fullKernelQuotient g N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by
  rw [AddMonoidHom.map_zmultiples] at hz
  have hq : W.fullKernelQuotient g' N = W.fullKernelQuotient (castPt hE (mapPointHom ψ g)) N :=
    fullKernelQuotient_eq_of_zmultiples_eq hg' hz
  have hΔ'' : (W.fullKernelQuotient (castPt hE (mapPointHom ψ g)) N).Δ ≠ 0 := by
    rw [← hq]
    exact hΔ'
  rw [j_congr hq (inst₂ := ⟨isUnit_iff_ne_zero.mpr hΔ''⟩)]
  exact j_fullKernelQuotient_castPt_ratPointHom W ψ hE g N hΔ hΔ''

end SigmaQuotientNaturality
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

open AlgebraicCurve

namespace SigmaDictionary

p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.SigmaCyclicSubgroups P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaCompositeLevel P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaCompositeRoots P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.SigmaFullFieldFrobenius P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.SigmaQuotientNaturality"
open scoped IntermediateField

section Furniture

variable {R A : Type*} [CommRing R] [CommRing A]

private theorem map_ofJNe0Or1728 (f : R →+* A) (j : R) :
    (ofJNe0Or1728 j).map f = ofJNe0Or1728 (f j) := by
  ext <;> simp [ofJNe0Or1728, map_ofNat]

end Furniture
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section GenCurve

variable {K M : Type u} [Field K] [Field M] [Algebra K M] {t : M}

variable (K) in

private abbrev tGen (t : M) : K⟮t⟯ := ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩

private theorem tGen_ne_zero (ht : Transcendental K t) : (tGen K t : K⟮t⟯) ≠ 0 := by
  intro h
  have h' : t = 0 := congrArg Subtype.val h
  exact ht (h' ▸ isAlgebraic_zero)

private theorem tGen_ne_1728 (ht : Transcendental K t) : (tGen K t : K⟮t⟯) ≠ 1728 := by
  intro h
  have h' : t = (1728 : M) := congrArg Subtype.val h
  apply ht
  rw [h', ← map_ofNat (algebraMap K M) 1728]
  exact isAlgebraic_algebraMap _

variable [DecidableEq M]

variable (K) in

private abbrev Wg (t : M) : WeierstrassCurve M :=
  (WeierstrassCurve.ofJ (tGen K t : K⟮t⟯)).baseChange M

private scoped instance instWgIsElliptic : (Wg K t).IsElliptic :=
  inferInstanceAs ((WeierstrassCurve.ofJ (tGen K t : K⟮t⟯)).map (algebraMap K⟮t⟯ M)).IsElliptic

private theorem Wg_eq (ht : Transcendental K t) : Wg K t = ofJNe0Or1728 t := by
  unfold Wg
  rw [ofJ_ne_0_ne_1728 (tGen K t) (tGen_ne_zero ht) (tGen_ne_1728 ht), WeierstrassCurve.baseChange,
    map_ofJNe0Or1728]
  rfl

private theorem map_Wg (ht : Transcendental K t) (ψ : M →+* M) (hψ : ψ t = t) : (Wg K t).map ψ = Wg K t := by
  rw [Wg_eq ht, map_ofJNe0Or1728, hψ]

private theorem Wg_j : (Wg K t).j = t := by
  show ((WeierstrassCurve.ofJ (tGen K t : K⟮t⟯)).map (algebraMap K⟮t⟯ M)).j = t
  rw [WeierstrassCurve.map_j, WeierstrassCurve.ofJ_j]
  rfl

end GenCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section CoordLaw

variable {M : Type u} [Field M] [DecidableEq M]

omit [DecidableEq M] in
private theorem _root_.SigmaDictionary.heq_some_of_eq {V V' : WeierstrassCurve M} (h : V' = V) (x y : M)
    (h₁ : V'.toAffine.Nonsingular x y) (h₂ : V.toAffine.Nonsingular x y) :
    HEq (WeierstrassCurve.Affine.Point.some x y h₁ : V'.toAffine.Point)
      (WeierstrassCurve.Affine.Point.some x y h₂ : V.toAffine.Point) := by
  subst h
  rfl

p2m_export "SigmaDictionary" "heq_some_of_eq"
private theorem castPt_eq_of_heq {V V' : WeierstrassCurve M} (h : V' = V) {P : V'.toAffine.Point}
    {Q : V.toAffine.Point} (hPQ : HEq P Q) : castPt h P = Q := by
  subst h
  exact eq_of_heq hPQ

private noncomputable def transport {W : WeierstrassCurve M} (ψ : M →+* M) (hE : W.map ψ = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hE).toAddMonoidHom.comp (mapPointHom ψ)

private theorem transport_apply {W : WeierstrassCurve M} (ψ : M →+* M) (hE : W.map ψ = W)
    (P : W.toAffine.Point) : transport ψ hE P = castPt hE (mapPointHom ψ P) :=
  rfl

private theorem eq_transport_of_coords {W : WeierstrassCurve M} (ψ : M →+* M) (hE : W.map ψ = W)
    (f : W.toAffine.Point →+ W.toAffine.Point)
    (hf : ∀ (x y : M) (h : W.toAffine.Nonsingular x y),
      ∃ h', f (.some x y h) = (.some (ψ x) (ψ y) h' : W.toAffine.Point)) :
    f = transport ψ hE := by
  ext P
  cases P with
  | zero =>
      rw [transport_apply]
      show f 0 = castPt hE (mapPointHom ψ 0)
      simp only [map_zero]
  | some x y h =>
      obtain ⟨h', hfP⟩ := hf x y h
      rw [hfP, transport_apply]
      exact (castPt_eq_of_heq hE (heq_some_of_eq hE (ψ x) (ψ y) _ h')).symm

end CoordLaw
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Torsion

variable {M : Type u} [Field M] [DecidableEq M]

private theorem natCard_torsionBy_eq_natCard_nsmul (W : WeierstrassCurve M) (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n)
      = Nat.card {P : W.toAffine.Point // n • P = 0} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun P => by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul])

private theorem hfull_of_card (W : WeierstrassCurve M) [W.IsElliptic] {N : ℕ} [NeZero N]
    (hNM : (N : M) ≠ 0) (hcard : Nat.card {P : W.toAffine.Point // N • P = 0} = N ^ 2) :
    ∀ d, d ∣ N → Nat.card (Submodule.torsionBy ℤ W.toAffine.Point d) = d ^ 2 := by
  intro d hd
  letI : DecidableEq (AlgebraicClosure M) := Classical.decEq _
  have hdM : (d : M) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := hd
    apply hNM
    rw [hc, Nat.cast_mul, h0, zero_mul]
  have hNL : (N : AlgebraicClosure M) ≠ 0 := by
    rw [← map_natCast (algebraMap M (AlgebraicClosure M))]
    exact (_root_.map_ne_zero _).mpr hNM
  have hdL : (d : AlgebraicClosure M) ≠ 0 := by
    rw [← map_natCast (algebraMap M (AlgebraicClosure M))]
    exact (_root_.map_ne_zero _).mpr hdM
  have hgeoN : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure M)).toAffine.Point N) = N ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure M) W hNL
  have hgeod : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure M)).toAffine.Point d) = d ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure M) W hdL

  let push : ∀ n : ℕ, Submodule.torsionBy ℤ W.toAffine.Point n →
      Submodule.torsionBy ℤ (W⁄(AlgebraicClosure M)).toAffine.Point n := fun n x =>
    ⟨ptMap (L := AlgebraicClosure M) W x, by
      rw [Submodule.mem_torsionBy_iff, ← map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp x.2,
        map_zero]⟩
  have hpush_inj : ∀ n, Function.Injective (push n) := fun n x y hxy =>
    Subtype.ext (ptMap_injective (L := AlgebraicClosure M) W (congrArg Subtype.val hxy))

  have hcardN : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point N) = N ^ 2 := by
    rw [natCard_torsionBy_eq_natCard_nsmul, hcard]
  haveI : Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure M)).toAffine.Point N) :=
    Nat.finite_of_card_ne_zero (by rw [hgeoN]; exact pow_ne_zero _ (NeZero.ne N))
  have hsurjN : Function.Surjective (push N) :=
    ((hpush_inj N).bijective_of_nat_card_le (by rw [hcardN, hgeoN])).2

  have hsurjd : Function.Surjective (push d) := by
    intro y
    have hyN : (y : (W⁄(AlgebraicClosure M)).toAffine.Point) ∈
        Submodule.torsionBy ℤ (W⁄(AlgebraicClosure M)).toAffine.Point N := by
      rw [Submodule.mem_torsionBy_iff]
      obtain ⟨c, hc⟩ := hd
      have hy := (Submodule.mem_torsionBy_iff _ _).mp y.2
      rw [hc, Nat.cast_mul, mul_comm, mul_zsmul, hy, smul_zero]
    obtain ⟨x, hx⟩ := hsurjN ⟨y, hyN⟩
    have hxval : ptMap (L := AlgebraicClosure M) W x = y := congrArg Subtype.val hx
    refine ⟨⟨x, ?_⟩, Subtype.ext hxval⟩
    rw [Submodule.mem_torsionBy_iff]
    apply ptMap_injective (L := AlgebraicClosure M) W
    rw [map_zsmul, map_zero]
    have hy := (Submodule.mem_torsionBy_iff _ _).mp y.2
    show (d : ℤ) • ptMap (L := AlgebraicClosure M) W (x : W.toAffine.Point) = 0
    rw [hxval]
    exact hy
  rw [← hgeod]
  exact Nat.card_eq_of_bijective (push d) ⟨hpush_inj d, hsurjd⟩

end Torsion
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

section Dictionary

variable {K : Type u} [Field K] (N : ℕ) [NeZero N]
  {M : Type u} [Field M] [DecidableEq M] [Algebra K M] {t : M}

variable (K) in

private abbrev CycSub (t : M) : ℕ → Type u := fun n =>
  {H : AddSubgroup (Wg K t).toAffine.Point // IsAddCyclic H ∧ Nat.card H = n}

private abbrev Roots (data : ModularPolynomialData N) (t : M) : Type u :=
  {y : M // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom M) t)).IsRoot y}

private theorem exists_rootEquiv (hN : (N : K) ≠ 0) (ht : Transcendental K t) (data : ModularPolynomialData N)
    (hcard : Nat.card {P : (Wg K t).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ r : CycSub K t N ≃ Roots N data t,
      ∀ (ψ : M →+* M) (hE : (Wg K t).map ψ = Wg K t) (H H' : CycSub K t N),
        H'.1 = H.1.map (transport ψ hE) → ((r H' : Roots N data t) : M) = ψ (r H) := by
  classical
  have hNM : (N : M) ≠ 0 := by
    rw [← map_natCast (algebraMap K M)]
    exact (_root_.map_ne_zero _).mpr hN
  have hWj : (Wg K t).j = t := Wg_j
  have hWtr : Transcendental K (Wg K t).j := by rw [hWj]; exact ht
  have hfull := hfull_of_card (Wg K t) hNM hcard
  obtain ⟨eZ⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (NeZero.ne N) hfull
  obtain ⟨ι, hι_fin, Q, hι, hQ, hQinj, hQsurj⟩ := exists_family (A := (Wg K t).toAffine.Point) N eZ
  letI : Fintype ι := hι_fin
  have hΔ : ∀ i, ((Wg K t).fullKernelQuotient (Q i) N).Δ ≠ 0 :=
    fun i => fullKernelQuotient_Δ_ne_zero (Wg K t) hNM (Q i) (hQ i)

  let toCyc : ι → CycSub K t N := fun i => cycSubEquiv N ⟨AddSubgroup.zmultiples (Q i), Q i, hQ i, rfl⟩
  have toCyc_val : ∀ i, (toCyc i).1 = AddSubgroup.zmultiples (Q i) := fun _ => rfl
  have toCyc_bij : Function.Bijective toCyc := by
    constructor
    · intro i j hij
      exact hQinj (by simpa [toCyc_val] using congrArg Subtype.val hij)
    · intro H
      obtain ⟨g, hg, hHg⟩ := exists_generator_of_isAddCyclic_card H.1 N H.2.1 H.2.2
      obtain ⟨i, hi⟩ := hQsurj H.1 ⟨g, hg, hHg⟩
      exact ⟨i, Subtype.ext (by rw [toCyc_val]; exact hi)⟩
  let eι : ι ≃ CycSub K t N := Equiv.ofBijective toCyc toCyc_bij
  have eι_symm_val : ∀ H : CycSub K t N, AddSubgroup.zmultiples (Q (eι.symm H)) = H.1 := by
    intro H
    have h := eι.apply_symm_apply H
    rw [← toCyc_val]
    exact congrArg Subtype.val h

  let jQ : ι → Roots N data t := fun i => ⟨jQuot (Wg K t) (Q i) (hΔ i), by
    have h := isRoot_fibrePoly_jQuot
      ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
      hNM data (Wg K t) hι Q hQ hQinj hΔ i
    rw [hWj] at h
    exact h⟩
  have jQ_inj : Function.Injective jQ := by
    intro i j hij
    exact jQuot_injective_of_transcendental
      ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
      (K₀ := K) hNM data (Wg K t) hWtr hι Q hQ hQinj hΔ (congrArg Subtype.val hij)

  have hroots : ((data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom M) t)).roots.toFinset).card
      = dedekindPsi N := by
    have h := card_roots_toFinset_fibrePoly_eq_dedekindPsi
      ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
      (K₀ := K) hNM data (Wg K t) hWtr hfull
    rw [hWj] at h
    exact h
  have hpoly_ne : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom M) t) ≠ 0 := by
    intro h
    have hpos := dedekindPsi_pos N (NeZero.ne N)
    rw [← hroots, h, Polynomial.roots_zero, Multiset.toFinset_zero, Finset.card_empty] at hpos
    exact lt_irrefl 0 hpos
  have hcardRoots : Nat.card (Roots N data t) = dedekindPsi N := by
    rw [← hroots, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpoly_ne])
  have hcardι : Nat.card ι = dedekindPsi N := by rw [Nat.card_eq_fintype_card, hι]
  haveI : Finite (Roots N data t) :=
    Nat.finite_of_card_ne_zero (by rw [hcardRoots]; exact (dedekindPsi_pos N (NeZero.ne N)).ne')
  have jroot_bij : Function.Bijective (jQ ∘ eι.symm) :=
    (jQ_inj.comp eι.symm.injective).bijective_of_nat_card_le
      (by rw [hcardRoots, Nat.card_congr eι.symm, hcardι])
  refine ⟨Equiv.ofBijective _ jroot_bij, ?_⟩

  intro ψ hE H H' hmap
  show jQuot (Wg K t) (Q (eι.symm H')) (hΔ _) = ψ (jQuot (Wg K t) (Q (eι.symm H)) (hΔ _))
  have hz : AddSubgroup.zmultiples (Q (eι.symm H'))
      = (AddSubgroup.zmultiples (Q (eι.symm H))).map
          ((castPt hE).toAddMonoidHom.comp (mapPointHom ψ)) := by
    rw [eι_symm_val, hmap, eι_symm_val]
    rfl
  exact j_fullKernelQuotient_of_zmultiples_eq_map (Wg K t) ψ hE (hQ _) hz (hΔ _) (hΔ _)

end Dictionary
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent"

end SigmaDictionary
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.SigmaDictionary"

namespace SigmaDictionary

p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.SigmaFullFieldFrobenius"
open scoped IntermediateField

private theorem dictionaryContract_holds (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ)
    [Fact q.Prime] [CharP K q] (N : ℕ) (hN : (N : K) ≠ 0) : DictionaryContract K q N hN := by
  intro M _ _ _ t ht _ _ hcard frM hFa hFt frE hF2
  haveI : NeZero N := ⟨fun h => hN (by rw [h, Nat.cast_zero])⟩
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  obtain ⟨e, he⟩ := exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental K N hN data
    M t ht
  obtain ⟨r, hr⟩ := exists_rootEquiv N hN (t := t) ht data hcard
  refine ⟨r.trans e.symm, ?_, ?_⟩
  ·
    intro σ H H' hmap
    have hσt : ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K) t = t :=
      (σ : M →ₐ[K⟮t⟯] M).commutes (tGen K t)
    have hE : (Wg K t).map (((σ : M →ₐ[K⟮t⟯] M).restrictScalars K) : M →+* M) = Wg K t :=
      map_Wg ht _ hσt
    have hf : WeierstrassCurve.Affine.Point.map (W' := genCurve K t) (σ : M →ₐ[K⟮t⟯] M)
        = transport (((σ : M →ₐ[K⟮t⟯] M).restrictScalars K) : M →+* M) hE := by
      refine eq_transport_of_coords _ hE _ fun x y h => ?_
      exact ⟨_, WeierstrassCurve.Affine.Point.map_some _ h⟩
    refine a_of_valueKeyed N (fun H H' : CycSub K t N => H'.1 = H.1.map (transport _ hE)) t e he r
      ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K) hσt (fun H H' hHH' => hr _ hE H H' hHH') H H' ?_
    exact hmap.trans (congrArg (fun φ => AddSubgroup.map φ H.1) hf)
  ·
    intro H H' hmap d _ hd
    have hFt' : (SemilinearAut.toRingAut frM : M →+* M) t = t := hFt
    have hE : (Wg K t).map (SemilinearAut.toRingAut frM : M →+* M) = Wg K t := map_Wg ht _ hFt'
    have hf : frE = transport (SemilinearAut.toRingAut frM : M →+* M) hE :=
      eq_transport_of_coords _ hE frE fun x y h => hF2 x y h
    exact f5_of_valueKeyed q N (fun H H' : CycSub K t N => H'.1 = H.1.map (transport _ hE)) t e he r
      (SemilinearAut.toRingAut frM : M →+* M) (fun a => hFa a) hFt' (fun H H' hHH' => hr _ hE H H' hHH')
      H H' (hmap.trans (congrArg (fun φ => AddSubgroup.map φ H.1) hf)) d hd

end SigmaDictionary
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.SigmaDictionary"

end SigmaDictionaryPart
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.SigmaDictionary"

universe u

p2m_open "ModularCurve~map_vcYInv~map_vcXInv~CycSub" in p2m_open "WeierstrassCurve~map_veluGy~map_veluGx" in open AlgebraicCurve _root_.P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve WeierstrassCurve.Affine in
open scoped IntermediateField in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
    (N : ℕ) (hN : (N : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hfr : E₀.map (frobenius K q) = E₀) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M)
      (W₀ : Place K M) (_ : 0 < W₀.ord (t - algebraMap K M E₀.j))
      (θ : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ E₀.toAffine.Point)
      (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K)
      (Φ : {H : AddSubgroup ((WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
              IsAddCyclic H ∧ Nat.card H = N} ≃
            {ψ : modularFunctionFieldFullC K N →ₐ[K] M // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t})
      (frM : SemilinearAut K M)
      (frE : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point)
      (fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point) (ε : ℤ),
      Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2 ∧
      (∀ (n : ℕ) (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          ¬ q ∣ n → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ • E₀ = E₀) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∧
      (∀ γ : VariableChange K, γ • E₀ = E₀ →
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
             (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))))) ∧
      (∀ (σ : M ≃ₐ[K⟮t⟯] M) (H H' : {H : AddSubgroup ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M)) →
          ((Φ H').1 : modularFunctionFieldFullC K N →ₐ[K] M) =
            ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp (Φ H).1) ∧
      (∀ a : K, frM • (algebraMap K M a) = algebraMap K M (a ^ q)) ∧
      frM • t = t ∧
      frM • W₀ = W₀ ∧
      (∀ (x y : M) (h : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Nonsingular x y),
        ∃ h', frE (.some x y h) = .some (frM • x) (frM • y) h') ∧
      (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y), ∃ h', fr₀ (.some x y h) = .some (x ^ q) (y ^ q) h') ∧
      (ε = 1 ∨ ε = -1) ∧
      (∀ P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point,
        N • P = 0 → θ (frE P) = ε • fr₀ (θ P)) ∧
      (∀ (H H' : {H : AddSubgroup ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map frE →
          ∀ (d : ℕ) [NeZero d] (hd : d ∣ N),
            (Φ H').1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ =
              frM • ((Φ H).1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩)) :=
  ModularCurve.SigmaSpine.spine K q N hN E₀ hfr (by
      classical
      exact ModularCurve.SigmaDescent.descent_holds' K q N hN E₀
        (by
          intro L₀ _ hfin hgal
          exact ModularCurve.FrobLift.frobContract_lift K q E₀ hfr L₀ hfin hgal)) (ModularCurve.SigmaRed.reductionContract_holds K E₀)
    (SigmaDictionary.dictionaryContract_holds K q N hN)

end
p2m_reactivate "P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine.RealisationAux P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaSpine P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.ModularCurve.SigmaDescent P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.SigmaDictionary"

end S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ
end P2MW
export P2MW.S_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ (solution)
