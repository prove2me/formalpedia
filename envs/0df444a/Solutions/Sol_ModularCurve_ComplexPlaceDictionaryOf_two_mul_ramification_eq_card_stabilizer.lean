-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3bff0271-650d-582d-8685-02b5cda0699e

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two
import Theorems.Thm_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq
import Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve AlgebraicCurve Filter"
open scoped MatrixGroups Topology Manifold

open MulAction
open scoped MatrixGroups

namespace Ws49
namespace OrbitStab

section General

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

theorem card_stabilizer_subgroup (L : Subgroup G) (a : α) :
    Nat.card (stabilizer L a) = Nat.card (L ⊓ stabilizer G a : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : G), g.1.2, by
        have h := g.2
        rw [mem_stabilizer_iff, Subgroup.smul_def] at h
        exact h⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, by
        rw [mem_stabilizer_iff, Subgroup.smul_def]
        exact g.2.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }

theorem relIndex_stabilizer_smul_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) (x : α) :
    H.relIndex (stabilizer G (g • x)) = H.relIndex (stabilizer G x) := by
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    ext y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro h
      have := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
      simpa [mul_assoc] using this
    · intro h
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← hH]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem relIndex_stabilizer_mul_card_stabilizer (H : Subgroup G) (x : α) :
    H.relIndex (stabilizer G x) * Nat.card (stabilizer H x) = Nat.card (stabilizer G x) := by
  rw [card_stabilizer_subgroup, ← Subgroup.subgroupOf_map_subtype,
    Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv.symm,
    Subgroup.relIndex, mul_comm]
  exact Subgroup.card_mul_index _

variable (H : Subgroup G) (a : α)

private def fib : Quotient (QuotientGroup.rightRel H) → orbitRel.Quotient H (orbit G a) :=
  Quotient.lift (fun g : G => Quotient.mk (orbitRel H (orbit G a)) ⟨g • a, mem_orbit a g⟩) (by
    intro g g' hgg'
    have hgg'' : g' * g⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hgg'
    refine Quotient.sound (mem_orbit_iff.mpr ?_)
    refine ⟨⟨g * g'⁻¹, by simpa using H.inv_mem hgg''⟩, Subtype.ext ?_⟩
    show (g * g'⁻¹) • g' • a = g • a
    rw [smul_smul, inv_mul_cancel_right])

private theorem fib_mk (g : G) :
    fib H a (Quotient.mk _ g) = Quotient.mk (orbitRel H (orbit G a)) ⟨g • a, mem_orbit a g⟩ := rfl

private theorem fib_surjective : Function.Surjective (fib H a) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp x.2
    exact ⟨Quotient.mk _ g, by rw [fib_mk]; congr 1; exact Subtype.ext hg⟩

theorem finite_orbitRelQuotient_orbit [H.FiniteIndex] : Finite (orbitRel.Quotient H (orbit G a)) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  exact Finite.of_surjective _ (fib_surjective H a)

private theorem card_fiber (q : orbitRel.Quotient H (orbit G a)) :
    Nat.card {c // fib H a c = q} = H.relIndex (stabilizer G ((q.out : orbit G a) : α)) := by
  classical
  set x : orbit G a := q.out with hx
  obtain ⟨g₀, hg₀⟩ := mem_orbit_iff.mp x.2
  have hq : Quotient.mk (orbitRel H (orbit G a)) x = q := Quotient.out_eq q
  let K : Subgroup G := stabilizer G (x : α)

  let φ : K → {c // fib H a c = q} := fun k => ⟨Quotient.mk _ ((k : G) * g₀), by
    rw [fib_mk, ← hq]
    congr 1
    apply Subtype.ext
    show ((k : G) * g₀) • a = (x : α)
    rw [mul_smul, hg₀]
    exact k.2⟩
  have hφ : ∀ k k' : K, φ k = φ k' ↔ QuotientGroup.rightRel (H.subgroupOf K) k k' := by
    intro k k'
    rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    show Quotient.mk (QuotientGroup.rightRel H) ((k : G) * g₀) = Quotient.mk _ ((k' : G) * g₀) ↔ _
    rw [Quotient.eq, QuotientGroup.rightRel_apply]
    simp [mul_assoc]
  let ψ : Quotient (QuotientGroup.rightRel (H.subgroupOf K)) → {c // fib H a c = q} :=
    Quotient.lift φ (fun k k' h => (hφ k k').mpr h)
  have hψ : Function.Bijective ψ := by
    constructor
    · intro c c'
      induction c using Quotient.inductionOn with
      | h k =>
        induction c' using Quotient.inductionOn with
        | h k' =>
          intro h
          exact Quotient.sound ((hφ k k').mp h)
    · rintro ⟨c, hc⟩
      induction c using Quotient.inductionOn with
      | h g =>
        rw [fib_mk, ← hq] at hc
        have hc' : (⟨g • a, mem_orbit a g⟩ : orbit G a) ∈ orbit H x := Quotient.exact hc
        obtain ⟨h, hh⟩ := mem_orbit_iff.mp hc'
        have hh' : (h : G) • (x : α) = g • a := congrArg Subtype.val hh
        refine ⟨Quotient.mk _ ⟨(h : G)⁻¹ * g * g₀⁻¹, ?_⟩, ?_⟩
        · rw [mem_stabilizer_iff, mul_smul, mul_smul, ← hg₀, inv_smul_smul, hg₀, ← hh', inv_smul_smul]
        · apply Subtype.ext
          show Quotient.mk (QuotientGroup.rightRel H) (((h : G)⁻¹ * g * g₀⁻¹) * g₀) = Quotient.mk _ g
          refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
          simp [mul_assoc]
  rw [← Nat.card_eq_of_bijective ψ hψ, Subgroup.relIndex, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (H.subgroupOf K))]

theorem exists_smul_out_eq (b : orbit G a) :
    ∃ h ∈ H, h • (((Quotient.mk (orbitRel H (orbit G a)) b).out : orbit G a) : α) = b := by
  have hrel : ((Quotient.mk (orbitRel H (orbit G a)) b).out : orbit G a) ∈ orbit H b :=
    Quotient.mk_out (s := orbitRel H (orbit G a)) b
  obtain ⟨h, hh⟩ := mem_orbit_iff.mp hrel
  refine ⟨((h⁻¹ : H) : G), (h⁻¹).2, ?_⟩
  rw [← hh, Subgroup.coe_inv]
  show (h : G)⁻¹ • (h : G) • (b : α) = b
  rw [inv_smul_smul]

theorem finsum_relIndex_stabilizer_eq_index [H.FiniteIndex] :
    ∑ᶠ q : orbitRel.Quotient H (orbit G a),
        H.relIndex (stabilizer G ((q.out : orbit G a) : α)) = H.index := by
  classical
  haveI := finite_orbitRelQuotient_orbit H a
  haveI : Fintype (orbitRel.Quotient H (orbit G a)) := Fintype.ofFinite _
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  rw [finsum_eq_sum_of_fintype, Subgroup.index,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H),
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (fib H a)), Nat.card_sigma]
  exact Finset.sum_congr rfl fun q _ => (card_fiber H a q).symm

end General

section PlusMinus

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

theorem mem_or_mul_mem_of_mem_sup_zpowers (H : Subgroup G) {z : G} (hz : z ∈ Subgroup.center G)
    (hz2 : z * z = 1) {g : G} (hg : g ∈ H ⊔ Subgroup.zpowers z) : g ∈ H ∨ g * z ∈ H := by
  have hcomm : ∀ g : G, g * z = z * g := fun g => (Subgroup.mem_center_iff.mp hz g)
  let K : Subgroup G :=
    { carrier := {g | g ∈ H ∨ g * z ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (H.mul_mem hx hy)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inr ?_
          rw [mul_assoc, hcomm y, ← mul_assoc]
          exact H.mul_mem hx hy
        · refine Or.inl ?_
          have : x * y = (x * z) * (y * z) := by
            rw [mul_assoc, ← mul_assoc z, ← hcomm y, mul_assoc y, hz2, mul_one]
          rw [this]
          exact H.mul_mem hx hy
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (H.inv_mem hx)
        · refine Or.inr ?_
          have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
          have : x⁻¹ * z = (x * z)⁻¹ := by rw [mul_inv_rev, hzinv, hcomm]
          rw [this]
          exact H.inv_mem hx }
  have hle : H ⊔ Subgroup.zpowers z ≤ K := by
    refine sup_le (fun g hg => Or.inl hg) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hz2]; exact H.one_mem)
  exact hle hg

theorem card_stabilizer_sup_zpowers_mul_card_inf (H : Subgroup G) {z : G}
    (hz : z ∈ Subgroup.center G) (hz2 : z * z = 1) (hz1 : z ≠ 1) (a : α) (hza : z • a = a) :
    Nat.card (stabilizer (H ⊔ Subgroup.zpowers z : Subgroup G) a) *
        Nat.card (H ⊓ Subgroup.zpowers z : Subgroup G) =
      2 * Nat.card (stabilizer H a) := by
  classical
  set Z : Subgroup G := Subgroup.zpowers z with hZ
  set S : Subgroup G := stabilizer G a with hS
  have hcardZ : Nat.card Z = 2 := by
    rw [hZ, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two, hz2]) hz1
  have hzS : z ∈ S := hza
  rw [card_stabilizer_subgroup, card_stabilizer_subgroup]
  by_cases hzH : z ∈ H
  ·
    have hZH : Z ≤ H := by rw [hZ, Subgroup.zpowers_le]; exact hzH
    rw [sup_eq_left.mpr hZH, inf_eq_right.mpr hZH, hcardZ, mul_comm]
  ·
    have hinf : Nat.card (H ⊓ Z : Subgroup G) = 1 := by
      have hdvd : Nat.card (H ⊓ Z : Subgroup G) ∣ 2 := hcardZ ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · exfalso
        apply hzH
        haveI : Finite Z := Nat.finite_of_card_ne_zero (by rw [hcardZ]; decide)
        have heq : H ⊓ Z = Z :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hcardZ])
        have : z ∈ H ⊓ Z := by rw [heq, hZ]; exact Subgroup.mem_zpowers z
        exact this.1
    rw [hinf, mul_one]
    set A : Subgroup G := (H ⊔ Z) ⊓ S with hA
    set B : Subgroup G := H ⊓ S with hB
    have hBA : B ≤ A := inf_le_inf_right S le_sup_left
    have hidx : (B.subgroupOf A).index = 2 := by
      rw [← Subgroup.relIndex, Subgroup.relIndex_eq_two_iff]
      refine ⟨z, ⟨Subgroup.mem_sup_right (by rw [hZ]; exact Subgroup.mem_zpowers z), hzS⟩, ?_⟩
      rintro b ⟨hbHZ, hbS⟩
      have hbzS : b * z ∈ S := S.mul_mem hbS hzS
      rcases mem_or_mul_mem_of_mem_sup_zpowers H hz hz2 hbHZ with hbH | hbzH
      ·
        refine Or.inr ⟨⟨hbH, hbS⟩, ?_⟩
        rintro ⟨hbz, -⟩
        exact hzH (by simpa using H.mul_mem (H.inv_mem hbH) hbz)
      · refine Or.inl ⟨⟨hbzH, hbzS⟩, ?_⟩
        rintro ⟨hbH, -⟩
        exact hzH (by simpa using H.mul_mem (H.inv_mem hbH) hbzH)
    have hcard : Nat.card A = Nat.card B * 2 := by
      rw [← hidx, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv]
      exact (Subgroup.card_mul_index _).symm
    rw [hcard, mul_comm]

theorem negOne_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  rw [mul_neg_one, neg_one_mul]

theorem negOne_mul_negOne : (-1 : SL(2, ℤ)) * (-1) = 1 := by
  rw [neg_one_mul, neg_neg]

theorem negOne_ne_one : (-1 : SL(2, ℤ)) ≠ 1 := by
  intro h
  have h00 := congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp at h00

theorem negOne_smul (τ : UpperHalfPlane) : (-1 : SL(2, ℤ)) • τ = τ := by
  rw [ModularGroup.SL_neg_smul, one_smul]

theorem card_stabilizer_negOne_sup_mul_card_inf_zpowers_negOne (Γ : Subgroup SL(2, ℤ))
    (τ : UpperHalfPlane) :
    Nat.card (stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) *
        Nat.card (Γ ⊓ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) =
      2 * Nat.card (stabilizer Γ τ) :=
  card_stabilizer_sup_zpowers_mul_card_inf Γ negOne_mem_center negOne_mul_negOne negOne_ne_one τ
    (negOne_smul τ)

theorem finsum_relIndex_stabilizer_eq_index_negOne_sup (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (τ : UpperHalfPlane) :
    ∑ᶠ q : orbitRel.Quotient (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))
        (orbit SL(2, ℤ) τ),
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).relIndex
          (stabilizer SL(2, ℤ) ((q.out : orbit SL(2, ℤ) τ) : UpperHalfPlane))
      = (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  haveI : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  exact finsum_relIndex_stabilizer_eq_index _ τ

end PlusMinus

end Ws49.OrbitStab

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf ComplexPlaceDictionaryOf algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange constantCoeff_jNum qExpFunctionFieldC intFormRatiosC_subset jqModC map_jqModC place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two exists_smul_eq_of_E4_cube_div_discriminant_eq E4_cube_div_discriminant_smul jqModC_eq_qExpansion_E4_cube_div_discriminant jqModC_mem_intFormRatiosC realizeOf_eq_div"
namespace ComplexPlaceDictionaryOf
p2m_export "ModularCurve.ComplexPlaceDictionaryOf" "pt_smul_of_mem ramification meromorphicOrderAt_realizeOf ramification_pos mk pt card_stabilizer_dvd_two_mul_ramification exists_pt_eq_of_mem"
namespace RamEqCard
p2m_open "ModularCurve.ComplexPlaceDictionaryOf ModularCurve"

abbrev pm (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) := Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))

theorem le_pm (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pm Γ := le_sup_left

theorem neg_one_mem_pm (Γ : Subgroup SL(2, ℤ)) : (-1 : SL(2, ℤ)) ∈ pm Γ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

scoped instance normal_zpowers_neg_one : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun a ha g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hc : g * (-1 : SL(2, ℤ)) ^ k * g⁻¹ = (-1) ^ k := by
    rw [((Commute.neg_one_right g).zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hc]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

theorem mem_zpowers_neg_one_iff (a : SL(2, ℤ)) :
    a ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rcases Int.even_or_odd k with hk | hk
    · left; rw [hk.neg_one_zpow]
    · right; rw [hk.neg_one_zpow]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem mem_pm_iff (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) : γ ∈ pm Γ ↔ γ ∈ Γ ∨ -γ ∈ Γ := by
  constructor
  · intro h
    have h' : γ ∈ ((pm Γ : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
    rw [pm, Subgroup.mul_normal] at h'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp h'
    rcases (mem_zpowers_neg_one_iff b).mp hb with rfl | rfl
    · left; simpa using ha
    · right; simpa using ha
  · rintro (h | h)
    · exact le_pm Γ h
    · have : γ = -γ * (-1) := by simp
      rw [this]
      exact mul_mem (le_pm Γ h) (neg_one_mem_pm Γ)

scoped instance (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (pm Γ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pm Γ)

scoped instance finite_stabilizer_SL (σ : ℍ) : Finite (MulAction.stabilizer SL(2, ℤ) σ) := by
  have hfin := ProperlyDiscontinuousSMul.finite_stabilizer (Γ := 𝒮ℒ) σ
  have : Finite (MulAction.stabilizer (𝒮ℒ) σ) := hfin
  refine Finite.of_injective
    (fun γ => (⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)), ⟨γ, rfl⟩⟩, γ.2⟩ :
      MulAction.stabilizer (𝒮ℒ) σ)) ?_
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer (𝒮ℒ) σ => ((x : 𝒮ℒ) : GL (Fin 2) ℝ)) h
  exact Subtype.ext (Matrix.SpecialLinearGroup.mapGL_injective this)

scoped instance finite_stabilizer_sub (Γ' : Subgroup SL(2, ℤ)) (σ : ℍ) :
    Finite (MulAction.stabilizer Γ' σ) := by
  refine Finite.of_injective
    (fun γ => (⟨((γ : Γ') : SL(2, ℤ)), γ.2⟩ : MulAction.stabilizer SL(2, ℤ) σ)) ?_
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer SL(2, ℤ) σ => (x : SL(2, ℤ))) h
  exact Subtype.ext (Subtype.ext this)

def jfun : ℍ → ℂ := fun z => (ModularForm.E₄ : ℍ → ℂ) z ^ 3 / ModularForm.discriminant z

theorem jfun_smul (g : SL(2, ℤ)) (z : ℍ) : jfun (g • z) = jfun z :=
  ModularCurve.E4_cube_div_discriminant_smul g z

theorem exists_smul_eq_of_jfun_eq {σ τ : ℍ} (h : jfun σ = jfun τ) : ∃ g : SL(2, ℤ), g • τ = σ :=
  ModularCurve.exists_smul_eq_of_E4_cube_div_discriminant_eq τ σ h.symm

variable {Γ : Subgroup SL(2, ℤ)} {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

abbrev CF (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : Type := ↥(laurentBaseChange ℂ F₀)

theorem exists_coe_eq_jqModC (Γ : Subgroup SL(2, ℤ)) (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF : F₀ = qExpFunctionFieldC ℚ Γ) : ∃ x : CF F₀, (x : LaurentSeries ℂ) = jqModC ℂ := by
  have hmem : jqModC ℚ ∈ F₀ := by
    rw [hF]
    exact intFormRatiosC_subset ℚ Γ (jqModC_mem_intFormRatiosC ℚ Γ)
  refine ⟨⟨coeffEmb ℂ (jqModC ℚ), coeffEmb_mem_laurentBaseChange ℂ hmem⟩, ?_⟩
  show coeffEmb ℂ (jqModC ℚ) = jqModC ℂ
  exact map_jqModC (algebraMap ℚ ℂ)

theorem sub_algebraMap_ne_zero (x : CF F₀) (hx : (x : LaurentSeries ℂ) = jqModC ℂ) (c : ℂ) :
    x - algebraMap ℂ (CF F₀) c ≠ 0 := by
  intro h
  have h1 : ((x - algebraMap ℂ (CF F₀) c : CF F₀) : LaurentSeries ℂ) = 0 := by rw [h]; rfl
  have h2 : ((x - algebraMap ℂ (CF F₀) c : CF F₀) : LaurentSeries ℂ) =
      jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) c := by
    rw [← hx]; rfl
  have h3 := congrArg (fun y : LaurentSeries ℂ => y.coeff (-1)) (h1.symm.trans h2)
  simp only [HahnSeries.coeff_zero, HahnSeries.coeff_sub', Pi.sub_apply,
    algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by decide),
    sub_zero] at h3

  have h4 : (jqModC ℂ).coeff (-1) = 1 := by
    rw [show (jqModC ℂ).coeff (-1) = (jqModC ℂ).coeff (((0 : ℕ) : ℤ) + (-1)) by simp, jqModC,
      HahnSeries.coeff_single_mul_add, one_mul, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]
  rw [h4] at h3
  exact one_ne_zero h3.symm

section Forms

variable (Γ : Subgroup SL(2, ℤ))

def restrict {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ₁ k) (h : Γ₂ ≤ Γ₁) :
    ModularForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := by
    simpa using f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[scoped simp] theorem restrict_apply {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ₁ k)
    (h : Γ₂ ≤ Γ₁) (τ : ℍ) : restrict f h τ = f τ := rfl

theorem le_SL : ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

def res {k : ℤ} (f : ModularForm 𝒮ℒ k) : ModularForm (Γ : Subgroup SL(2, ℤ)) k :=
  restrict f (le_SL Γ)

@[scoped simp] theorem res_apply {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) : res Γ f τ = f τ := rfl

abbrev qL {k : ℤ} (f : ModularForm (Γ : Subgroup SL(2, ℤ)) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

abbrev qL₁ {k : ℤ} (f : ModularForm 𝒮ℒ k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

variable {Γ}

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom_apply]

theorem qL_mul (hT : ModularGroup.T ∈ Γ) {a b : ℤ} (f : ModularForm (Γ : Subgroup SL(2, ℤ)) a)
    (g : ModularForm (Γ : Subgroup SL(2, ℤ)) b) : qL Γ (f.mul g) = qL Γ f * qL Γ g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT), PowerSeries.coe_mul]

theorem qL_sub (hT : ModularGroup.T ∈ Γ) {a : ℤ} (f g : ModularForm (Γ : Subgroup SL(2, ℤ)) a) :
    qL Γ (f - g) = qL Γ f - qL Γ g := by
  simp only [qL, ModularForm.coe_sub,
    ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods hT), PowerSeries.coe_sub]

theorem algebraMap_laurentSeries_eq_C (c : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

theorem qL_smul (hT : ModularGroup.T ∈ Γ) {a : ℤ} (c : ℂ) (f : ModularForm (Γ : Subgroup SL(2, ℤ)) a) :
    qL Γ (c • f) = HahnSeries.C c * qL Γ f := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods hT), Algebra.smul_def,
    PowerSeries.algebraMap_eq, PowerSeries.coe_mul, HahnSeries.ofPowerSeries_C]

theorem qL_mcast {a b : ℤ} (h : a = b) (f : ModularForm (Γ : Subgroup SL(2, ℤ)) a) :
    qL Γ (ModularForm.mcast h f) = qL Γ f := rfl

variable (Γ) in
theorem qL_res {k : ℤ} (f : ModularForm 𝒮ℒ k) : qL Γ (res Γ f) = qL₁ f := rfl

variable (Γ) in

def numer (A : ModularForm (Γ : Subgroup SL(2, ℤ)) 4) (B : ModularForm (Γ : Subgroup SL(2, ℤ)) 12)
    (c : ℂ) : ModularForm (Γ : Subgroup SL(2, ℤ)) 12 :=
  ModularForm.mcast (by norm_num) (A.mul (A.mul A)) - c • B

theorem numer_apply (A : ModularForm (Γ : Subgroup SL(2, ℤ)) 4)
    (B : ModularForm (Γ : Subgroup SL(2, ℤ)) 12) (c : ℂ) (τ : ℍ) :
    numer Γ A B c τ = A τ ^ 3 - c * B τ := by
  simp only [numer, ModularForm.sub_apply, ModularForm.coe_mcast, ModularForm.coe_mul,
    Pi.mul_apply, ModularForm.IsGLPos.smul_apply, smul_eq_mul]
  ring

theorem qL_numer (hT : ModularGroup.T ∈ Γ) (A : ModularForm (Γ : Subgroup SL(2, ℤ)) 4)
    (B : ModularForm (Γ : Subgroup SL(2, ℤ)) 12) (c : ℂ) :
    qL Γ (numer Γ A B c) = qL Γ A ^ 3 - HahnSeries.C c * qL Γ B := by
  rw [numer, qL_sub hT, qL_mcast, qL_mul hT, qL_mul hT, qL_smul hT]
  ring

theorem pres_numer (hT : ModularGroup.T ∈ Γ) (A : ModularForm (Γ : Subgroup SL(2, ℤ)) 4)
    (B : ModularForm (Γ : Subgroup SL(2, ℤ)) 12) (hB : qL Γ B ≠ 0) (c : ℂ) :
    (qL Γ A ^ 3 / qL Γ B - algebraMap ℂ (LaurentSeries ℂ) c) * qL Γ B = qL Γ (numer Γ A B c) := by
  rw [qL_numer hT, sub_mul, div_mul_cancel₀ _ hB, algebraMap_laurentSeries_eq_C]

variable (Γ) in

def A4 : ModularForm (Γ : Subgroup SL(2, ℤ)) 4 := res Γ ModularForm.E₄

variable (Γ) in

def B12 : ModularForm (Γ : Subgroup SL(2, ℤ)) 12 :=
  res Γ ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12)

@[scoped simp] theorem A4_apply (τ : ℍ) : A4 Γ τ = ModularForm.E₄ τ := rfl
@[scoped simp] theorem B12_apply (τ : ℍ) : B12 Γ τ = ModularForm.discriminant τ := rfl

theorem B12_ne (τ : ℍ) : (B12 Γ : ℍ → ℂ) τ ≠ 0 := ModularForm.discriminant_ne_zero τ

theorem qL_ne_zero (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f : ModularForm (Γ : Subgroup SL(2, ℤ)) k)
    (hf : f ≠ 0) : qL Γ f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem qL_B12_ne (hT : ModularGroup.T ∈ Γ) : qL Γ (B12 Γ) ≠ 0 :=
  qL_ne_zero hT _ (fun h => B12_ne (Γ := Γ) UpperHalfPlane.I (by rw [h]; rfl))

theorem jqModC_eq : jqModC ℂ = qL Γ (A4 Γ) ^ 3 / qL Γ (B12 Γ) := by
  rw [jqModC_eq_qExpansion_E4_cube_div_discriminant]
  rfl

end Forms

theorem coe_algebraMap (c : ℂ) :
    ((algebraMap ℂ (CF F₀) c : CF F₀) : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) c := rfl

theorem realizeOf_sub (hT : ModularGroup.T ∈ Γ) (x : CF F₀) (hx : (x : LaurentSeries ℂ) = jqModC ℂ)
    (c : ℂ) (z : ℍ) :
    realizeOf Γ ((x - algebraMap ℂ (CF F₀) c : CF F₀) : LaurentSeries ℂ) z = jfun z - c := by
  have hx' : ((x - algebraMap ℂ (CF F₀) c : CF F₀) : LaurentSeries ℂ) =
      qL Γ (A4 Γ) ^ 3 / qL Γ (B12 Γ) - algebraMap ℂ (LaurentSeries ℂ) c := by
    rw [← jqModC_eq, ← hx]; rfl
  rw [hx', realizeOf_eq_div Γ hT (numer Γ (A4 Γ) (B12 Γ) c) (B12 Γ) _
    (pres_numer hT _ _ (qL_B12_ne hT) c) z (B12_ne z)]
  simp only [numer_apply, A4_apply, B12_apply, jfun]
  show _ / ModularForm.discriminant z = _
  rw [sub_div, mul_div_cancel_right₀ _ (ModularForm.discriminant_ne_zero z)]

theorem ord_mul_ramification (hT : ModularGroup.T ∈ Γ) (D : ComplexPlaceDictionaryOf Γ F₀) (x : CF F₀)
    (hx : (x : LaurentSeries ℂ) = jqModC ℂ) (σ : ℍ) :
    (D.pt σ).ord (x - algebraMap ℂ (CF F₀) (jfun σ)) * (D.ramification σ : ℤ) =
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) σ) / 2 : ℕ) : ℤ) := by
  have hne := sub_algebraMap_ne_zero x hx (jfun σ)
  have h := D.meromorphicOrderAt_realizeOf σ _ hne
  have hfun : (fun z : ℂ => realizeOf Γ ((x - algebraMap ℂ (CF F₀) (jfun σ) : CF F₀) : LaurentSeries ℂ)
      (ofComplex z)) = fun z : ℂ => (ModularForm.E₄ : ℍ → ℂ) (ofComplex z) ^ 3 /
            ModularForm.discriminant (ofComplex z)
          - (ModularForm.E₄ : ℍ → ℂ) σ ^ 3 / ModularForm.discriminant σ := by
    funext z; exact realizeOf_sub hT x hx (jfun σ) (ofComplex z)
  rw [hfun, meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two σ] at h
  have h' : (((Nat.card (MulAction.stabilizer SL(2, ℤ) σ) / 2 : ℕ) : ℤ) : WithTop ℤ) =
      (((D.ramification σ : ℤ) * (D.pt σ).ord (x - algebraMap ℂ (CF F₀) (jfun σ)) : ℤ) : WithTop ℤ) := h
  have h'' := WithTop.coe_injective h'
  rw [mul_comm]
  exact_mod_cast h''.symm

def negOne (σ : ℍ) : MulAction.stabilizer SL(2, ℤ) σ :=
  ⟨-1, by rw [MulAction.mem_stabilizer_iff, ModularGroup.SL_neg_smul, one_smul]⟩

theorem orderOf_negOne (σ : ℍ) : orderOf (negOne σ) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    simp [negOne]
  · intro h
    have := congrArg (fun γ : MulAction.stabilizer SL(2, ℤ) σ => ((γ : SL(2, ℤ)) 0 0)) h
    simp [negOne] at this

theorem two_dvd_card_stabilizer (σ : ℍ) : 2 ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) σ) := by
  have h := orderOf_dvd_natCard (negOne σ)
  rwa [orderOf_negOne] at h

theorem two_le_card_stabilizer (σ : ℍ) : 2 ≤ Nat.card (MulAction.stabilizer SL(2, ℤ) σ) :=
  Nat.le_of_dvd Nat.card_pos (two_dvd_card_stabilizer σ)

theorem ord_pos_of_jfun_eq (hT : ModularGroup.T ∈ Γ) (D : ComplexPlaceDictionaryOf Γ F₀) (x : CF F₀)
    (hx : (x : LaurentSeries ℂ) = jqModC ℂ) {σ : ℍ} {c : ℂ} (h : jfun σ = c) :
    0 < (D.pt σ).ord (x - algebraMap ℂ (CF F₀) c) := by
  subst h
  have h1 := ord_mul_ramification hT D x hx σ
  have h2 : (1 : ℤ) ≤ ((Nat.card (MulAction.stabilizer SL(2, ℤ) σ) / 2 : ℕ) : ℤ) := by
    have := two_le_card_stabilizer σ
    have : 1 ≤ Nat.card (MulAction.stabilizer SL(2, ℤ) σ) / 2 := by omega
    exact_mod_cast this
  have h3 : (0 : ℤ) < (D.ramification σ : ℤ) := by exact_mod_cast D.ramification_pos σ
  by_contra hle
  push_neg at hle
  have : (D.pt σ).ord (x - algebraMap ℂ (CF F₀) (jfun σ)) * (D.ramification σ : ℤ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hle h3.le
  omega

theorem jfun_eq_of_ord_pos (hT : ModularGroup.T ∈ Γ) (D : ComplexPlaceDictionaryOf Γ F₀) (x : CF F₀)
    (hx : (x : LaurentSeries ℂ) = jqModC ℂ) {σ : ℍ} {c : ℂ}
    (h : 0 < (D.pt σ).ord (x - algebraMap ℂ (CF F₀) c)) : jfun σ = c := by
  have hne := sub_algebraMap_ne_zero x hx c
  have hord := D.meromorphicOrderAt_realizeOf σ _ hne
  set F : ℂ → ℂ := fun z : ℂ =>
    realizeOf Γ ((x - algebraMap ℂ (CF F₀) c : CF F₀) : LaurentSeries ℂ) (ofComplex z) with hFdef
  have hF : F = fun z : ℂ => jfun (ofComplex z) - c := by
    funext z; exact realizeOf_sub hT x hx c (ofComplex z)

  have hpos : 0 < meromorphicOrderAt F (σ : ℂ) := by
    rw [hord]
    have : (0 : ℤ) < (D.ramification σ : ℤ) * (D.pt σ).ord (x - algebraMap ℂ (CF F₀) c) :=
      mul_pos (by exact_mod_cast D.ramification_pos σ) h
    exact_mod_cast this
  have hlim0 : Tendsto F (𝓝[≠] (σ : ℂ)) (𝓝 0) := tendsto_zero_of_meromorphicOrderAt_pos hpos

  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jfun :=
    (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero
  have hdiff : DifferentiableOn ℂ (jfun ∘ ofComplex) {w : ℂ | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hmd
  have hcont : ContinuousAt (jfun ∘ ofComplex) (σ : ℂ) :=
    (hdiff.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds σ.im_pos)).continuousAt
  have hlim1 : Tendsto F (𝓝[≠] (σ : ℂ)) (𝓝 (jfun σ - c)) := by
    rw [hF]
    have : Tendsto (fun z : ℂ => (jfun ∘ ofComplex) z - c) (𝓝 (σ : ℂ)) (𝓝 (jfun σ - c)) := by
      have h1 := hcont.tendsto
      simp only [Function.comp_apply, ofComplex_apply] at h1
      exact h1.sub_const c
    exact this.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique hlim1 hlim0
  exact sub_eq_zero.mp this

theorem pt_smul_of_mem_pm (D : ComplexPlaceDictionaryOf Γ F₀) {γ : SL(2, ℤ)} (hγ : γ ∈ pm Γ) (σ : ℍ) :
    D.pt (γ • σ) = D.pt σ := by
  rcases (mem_pm_iff Γ γ).mp hγ with h | h
  · exact D.pt_smul_of_mem h σ
  · have hγ' : γ = (-1 : SL(2, ℤ)) * (-γ) := by simp
    rw [hγ', mul_smul, ModularGroup.SL_neg_smul, one_smul]
    exact D.pt_smul_of_mem h σ

structure JLine (Γ : Subgroup SL(2, ℤ)) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) where
  x : CF F₀
  hx : (x : LaurentSeries ℂ) = jqModC ℂ
  φ : RatFunc ℂ →ₐ[ℂ] CF F₀
  hφ : φ.toRingHom.IsIntegral
  φ_X : φ RatFunc.X = x
  hpd : HasPrincipalDivisors ℂ (CF F₀)
  finrankAlong_le : finrankAlong ℂ φ ≤ (pm Γ).index

  sum_fiber : ∀ (c : ℂ) (S : Finset (Place ℂ (CF F₀))),
    (∀ W, W ∈ S ↔ 0 < W.ord (x - algebraMap ℂ (CF F₀) c)) →
      ∑ W ∈ S, W.ord (x - algebraMap ℂ (CF F₀) c) = (finrankAlong ℂ φ : ℤ)

section JLineGeneric

variable {F : Type*} [Field F] [Algebra ℂ F] (x : F) (htr : Transcendental ℂ x)

def jphi : RatFunc ℂ →ₐ[ℂ] F :=
  ((IntermediateField.adjoin ℂ ({x} : Set F)).val).comp
    (RatFunc.algEquivOfTranscendental x htr : RatFunc ℂ →ₐ[ℂ] IntermediateField.adjoin ℂ ({x} : Set F))

theorem jphi_apply (r : RatFunc ℂ) :
    jphi x htr r = ((RatFunc.algEquivOfTranscendental x htr r : IntermediateField.adjoin ℂ ({x} : Set F)) : F) :=
  rfl

theorem jphi_X : jphi x htr RatFunc.X = x := by
  rw [jphi_apply]
  exact RatFunc.algEquivOfTranscendental_X x htr

theorem jphi_symm (k : IntermediateField.adjoin ℂ ({x} : Set F)) :
    jphi x htr ((RatFunc.algEquivOfTranscendental x htr).symm k) = (k : F) := by
  rw [jphi_apply, AlgEquiv.apply_symm_apply]

theorem jphi_compat :
    (letI := algebraAlong (jphi x htr);
      RingHom.comp (algebraMap (RatFunc ℂ) F)
          ((RatFunc.algEquivOfTranscendental x htr).symm.toRingEquiv :
            IntermediateField.adjoin ℂ ({x} : Set F) ≃+* RatFunc ℂ)
        = RingHom.comp (RingEquiv.refl F : F ≃+* F)
            (algebraMap (IntermediateField.adjoin ℂ ({x} : Set F)) F)) := by
  ext k
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.refl_apply]
  exact jphi_symm x htr k

variable [FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F]

theorem finiteAlong_jphi : FiniteAlong ℂ (jphi x htr) := by
  letI := algebraAlong (jphi x htr)
  exact Module.Finite.of_equiv_equiv
    ((RatFunc.algEquivOfTranscendental x htr).symm.toRingEquiv :
      IntermediateField.adjoin ℂ ({x} : Set F) ≃+* RatFunc ℂ)
    (RingEquiv.refl F) (jphi_compat x htr)

theorem isIntegral_jphi : (jphi x htr).toRingHom.IsIntegral := by
  letI := algebraAlong (jphi x htr)
  haveI : Module.Finite (RatFunc ℂ) F := finiteAlong_jphi x htr
  intro y
  exact Algebra.IsIntegral.isIntegral y

theorem separableAlong_jphi : SeparableAlong ℂ (jphi x htr) := by
  letI := algebraAlong (jphi x htr)
  haveI : Module.Finite (RatFunc ℂ) F := finiteAlong_jphi x htr
  exact Algebra.IsSeparable.of_integral _ _

theorem finrankAlong_jphi :
    finrankAlong ℂ (jphi x htr) = Module.finrank (IntermediateField.adjoin ℂ ({x} : Set F)) F := by
  letI := algebraAlong (jphi x htr)
  exact (Algebra.finrank_eq_of_equiv_equiv
    ((RatFunc.algEquivOfTranscendental x htr).symm.toRingEquiv :
      IntermediateField.adjoin ℂ ({x} : Set F) ≃+* RatFunc ℂ)
    (RingEquiv.refl F) (jphi_compat x htr)).symm

theorem sum_ord_eq_finrankAlong [HasPrincipalDivisors ℂ F] (hdeg : ∀ W : Place ℂ F, W.deg = 1)
    (c : ℂ) (S : Finset (Place ℂ F)) (hS : ∀ W, W ∈ S ↔ 0 < W.ord (x - algebraMap ℂ F c)) :
    ∑ W ∈ S, W.ord (x - algebraMap ℂ F c) = (finrankAlong ℂ (jphi x htr) : ℤ) := by
  classical
  set φ := jphi x htr with hφdef
  have hφ : φ.toRingHom.IsIntegral := isIntegral_jphi x htr
  have hFI : FundamentalIdentityAlong ℂ φ hφ :=
    fundamentalIdentityAlong φ hφ (finiteAlong_jphi x htr) (separableAlong_jphi x htr)
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : FundamentalIdentity ℂ (RatFunc ℂ) F := hFI
  have hid := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := ℂ) (F := RatFunc ℂ)
    (F' := F) (RationalFunctionField.placeOfPoint ℂ c)
  rw [RationalFunctionField.deg_placeOfPoint, Nat.cast_one, mul_one] at hid
  have φ_X : φ RatFunc.X = x := jphi_X x htr
  have hXc : φ RatFunc.X - algebraMap ℂ F c = x - algebraMap ℂ F c := by rw [φ_X]
  have hXC : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C c) =
      RatFunc.X - algebraMap ℂ (RatFunc ℂ) c := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rfl
  have hpoly : φ (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C c)) =
      x - algebraMap ℂ F c := by
    rw [hXC, map_sub, φ_X, AlgHom.commutes]
  have hmem : ∀ W : Place ℂ F,
      W ∈ (RationalFunctionField.placeOfPoint ℂ c).fiber F ↔ 0 < W.ord (x - algebraMap ℂ F c) := by
    intro W
    rw [Place.mem_fiber]
    have hordW : W.ord (x - algebraMap ℂ F c) =
        Place.ramificationIndexAlong φ W *
          (W.restrictAlong φ hφ).ord
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X - Polynomial.C c)) := by
      rw [← hpoly]
      exact Place.ord_restrictAlong φ hφ W _
    rw [RationalFunctionField.ord_X_sub_C ℂ c] at hordW

    have hδ_c : (Finsupp.single (RationalFunctionField.placeOfPoint ℂ c) (1 : ℤ) +
        Finsupp.single (RationalFunctionField.placeInfty ℂ) (-1 : ℤ))
          (RationalFunctionField.placeOfPoint ℂ c) = 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne
        (RationalFunctionField.placeOfPoint_ne_placeInfty ℂ c), add_zero]
    have hδ_a : ∀ a : ℂ, a ≠ c → (Finsupp.single (RationalFunctionField.placeOfPoint ℂ c) (1 : ℤ) +
        Finsupp.single (RationalFunctionField.placeInfty ℂ) (-1 : ℤ))
          (RationalFunctionField.placeOfPoint ℂ a) = 0 := by
      intro a hac
      rw [Finsupp.add_apply,
        Finsupp.single_eq_of_ne (fun h => hac ((RationalFunctionField.placeOfPoint_injective ℂ) h)),
        Finsupp.single_eq_of_ne (RationalFunctionField.placeOfPoint_ne_placeInfty ℂ a), add_zero]
    have hδ_inf : (Finsupp.single (RationalFunctionField.placeOfPoint ℂ c) (1 : ℤ) +
        Finsupp.single (RationalFunctionField.placeInfty ℂ) (-1 : ℤ))
          (RationalFunctionField.placeInfty ℂ) = -1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (RationalFunctionField.placeOfPoint_ne_placeInfty ℂ c).symm, zero_add]
    have hepos : 0 < (Place.ramificationIndexAlong φ W : ℤ) := by
      exact_mod_cast Place.ramificationIndex_pos (F := RatFunc ℂ) (w := W)
    constructor
    · intro hW
      have hW' : W.restrictAlong φ hφ = RationalFunctionField.placeOfPoint ℂ c := hW
      rw [hordW, hW', hδ_c, mul_one]
      exact hepos
    · intro hpos
      show W.restrictAlong φ hφ = RationalFunctionField.placeOfPoint ℂ c
      rw [hordW] at hpos
      rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty ℂ (W.restrictAlong φ hφ) with
        ⟨a, ha⟩ | hinf
      · by_cases hac : a = c
        · rw [ha, hac]
        · exfalso
          rw [ha, hδ_a a hac, mul_zero] at hpos
          exact lt_irrefl _ hpos
      · exfalso
        rw [hinf, hδ_inf] at hpos
        have : (Place.ramificationIndexAlong φ W : ℤ) * (-1) < 0 := by linarith
        exact lt_asymm this hpos
  have hSeq : S = (RationalFunctionField.placeOfPoint ℂ c).fiber F := by
    ext W; rw [hS, hmem]
  rw [hSeq]
  show _ = ((Module.finrank (RatFunc ℂ) F : ℕ) : ℤ)
  rw [← hid]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hW' : W.restrictAlong φ hφ = RationalFunctionField.placeOfPoint ℂ c := Place.mem_fiber.mp hW
  rw [hdeg W, Nat.cast_one, mul_one, ← hXc]
  exact (Place.ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint φ hφ W c hW').symm

end JLineGeneric

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem nonempty_jLine (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = qExpFunctionFieldC ℚ Γ) :
    Nonempty (JLine Γ F₀) := by
  classical
  obtain ⟨x, hx⟩ := exists_coe_eq_jqModC Γ F₀ hF
  subst hF
  obtain ⟨htr, hfd⟩ :=
    transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      ℂ Γ hT x hx
  haveI := hfd
  haveI hpd : HasPrincipalDivisors ℂ (CF (qExpFunctionFieldC ℚ Γ)) :=
    hasPrincipalDivisors_of_transcendental ℂ x htr
  have hle : finrankAlong ℂ (jphi x htr) ≤ (pm Γ).index := by
    rw [finrankAlong_jphi]
    exact finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index ℂ Γ hT (pm Γ)
      (le_pm Γ) (fun γ h => (mem_pm_iff Γ γ).mp h) x hx
  exact ⟨⟨x, hx, jphi x htr, isIntegral_jphi x htr, jphi_X x htr, hpd, hle,
    sum_ord_eq_finrankAlong x htr
      (fun W => place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC ℂ Γ hT _ rfl W)⟩⟩

section Orbits

variable (Γ)

abbrev OrbQ (τ : ℍ) : Type :=
  MulAction.orbitRel.Quotient (pm Γ) (MulAction.orbit SL(2, ℤ) τ)

def rep (τ : ℍ) (q : OrbQ Γ τ) : ℍ := ((q.out : MulAction.orbit SL(2, ℤ) τ) : ℍ)

variable {Γ}

theorem exists_smul_eq_rep (τ : ℍ) (q : OrbQ Γ τ) : ∃ g : SL(2, ℤ), g • τ = rep Γ τ q :=
  MulAction.mem_orbit_iff.mp (q.out : MulAction.orbit SL(2, ℤ) τ).2

theorem jfun_rep (τ : ℍ) (q : OrbQ Γ τ) : jfun (rep Γ τ q) = jfun τ := by
  obtain ⟨g, hg⟩ := exists_smul_eq_rep τ q
  rw [← hg, jfun_smul]

theorem card_stabilizer_rep (τ : ℍ) (q : OrbQ Γ τ) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) (rep Γ τ q)) = Nat.card (MulAction.stabilizer SL(2, ℤ) τ) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_rep τ q
  rw [← hg]
  exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • τ = g • τ)).toEquiv).symm

theorem exists_mem_pm_smul_rep_eq (τ : ℍ) (σ : ℍ) (hσ : σ ∈ MulAction.orbit SL(2, ℤ) τ) :
    ∃ h ∈ pm Γ, h • rep Γ τ (Quotient.mk _ ⟨σ, hσ⟩) = σ :=
  Ws49.OrbitStab.exists_smul_out_eq (pm Γ) τ ⟨σ, hσ⟩

theorem two_mul_card_div_two (σ : ℍ) :
    (2 : ℤ) * ((Nat.card (MulAction.stabilizer SL(2, ℤ) σ) / 2 : ℕ) : ℤ) =
      (Nat.card (MulAction.stabilizer SL(2, ℤ) σ) : ℤ) := by
  obtain ⟨m, hm⟩ := two_dvd_card_stabilizer σ
  rw [hm, Nat.mul_div_cancel_left _ two_pos]
  push_cast
  ring

theorem two_le_card_stabilizer_pm (σ : ℍ) : 2 ≤ Nat.card (MulAction.stabilizer (pm Γ) σ) := by
  let n : MulAction.stabilizer (pm Γ) σ :=
    ⟨⟨-1, neg_one_mem_pm Γ⟩, by
      rw [MulAction.mem_stabilizer_iff]
      show ((-1 : SL(2, ℤ))) • σ = σ
      rw [ModularGroup.SL_neg_smul, one_smul]⟩
  have hn : orderOf n = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext; apply Subtype.ext
      simp [n]
    · intro h
      have := congrArg (fun γ : MulAction.stabilizer (pm Γ) σ => (((γ : pm Γ) : SL(2, ℤ)) 0 0)) h
      simp [n] at this
  have h := orderOf_dvd_natCard n
  rw [hn] at h
  exact Nat.le_of_dvd Nat.card_pos h

theorem termwise (hT : ModularGroup.T ∈ Γ) (D : ComplexPlaceDictionaryOf Γ F₀) (x : CF F₀)
    (hx : (x : LaurentSeries ℂ) = jqModC ℂ) (σ : ℍ) (c : ℂ) (hc : jfun σ = c) :
    0 < (D.pt σ).ord (x - algebraMap ℂ (CF F₀) c) ∧
      (D.pt σ).ord (x - algebraMap ℂ (CF F₀) c) ≤
        ((pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) σ) : ℤ) ∧
      ((D.pt σ).ord (x - algebraMap ℂ (CF F₀) c) =
          ((pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) σ) : ℤ) →
        2 * D.ramification σ = Nat.card (MulAction.stabilizer (pm Γ) σ)) := by
  subst hc
  set A : ℤ := (D.pt σ).ord (x - algebraMap ℂ (CF F₀) (jfun σ)) with hA
  set B : ℕ := (pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) σ) with hB
  set s : ℕ := Nat.card (MulAction.stabilizer (pm Γ) σ) with hs
  set s₁ : ℕ := Nat.card (MulAction.stabilizer SL(2, ℤ) σ) with hs₁
  set e : ℕ := D.ramification σ with he
  have hApos : 0 < A := ord_pos_of_jfun_eq hT D x hx rfl
  have hAe : A * (e : ℤ) = ((s₁ / 2 : ℕ) : ℤ) := ord_mul_ramification hT D x hx σ
  have hAe2 : 2 * (A * (e : ℤ)) = (s₁ : ℤ) := by rw [hAe]; exact two_mul_card_div_two σ
  have hBs : (B : ℤ) * (s : ℤ) = (s₁ : ℤ) := by
    exact_mod_cast Ws49.OrbitStab.relIndex_stabilizer_mul_card_stabilizer (pm Γ) σ
  obtain ⟨k, hk⟩ := card_stabilizer_dvd_two_mul_ramification Γ hT F₀ D σ
  have hk' : (2 : ℤ) * (e : ℤ) = (s : ℤ) * (k : ℤ) := by exact_mod_cast hk
  have hspos : (0 : ℤ) < (s : ℤ) := by exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer (pm Γ) σ))
  have hepos : (0 : ℤ) < (e : ℤ) := by exact_mod_cast D.ramification_pos σ
  have hkpos : (0 : ℤ) < (k : ℤ) := by
    by_contra hle
    push Not at hle
    have : (s : ℤ) * (k : ℤ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hspos.le hle
    linarith

  have hAkB : A * (k : ℤ) = (B : ℤ) := by
    have h1 : A * (k : ℤ) * (s : ℤ) = (B : ℤ) * (s : ℤ) := by
      calc A * (k : ℤ) * (s : ℤ) = A * ((s : ℤ) * (k : ℤ)) := by ring
        _ = A * (2 * (e : ℤ)) := by rw [hk']
        _ = 2 * (A * (e : ℤ)) := by ring
        _ = (s₁ : ℤ) := hAe2
        _ = (B : ℤ) * (s : ℤ) := hBs.symm
    exact mul_right_cancel₀ hspos.ne' h1
  refine ⟨hApos, ?_, ?_⟩
  · nlinarith
  · intro hAB

    have hk1 : (k : ℤ) = 1 := by
      have : A * (k : ℤ) = A * 1 := by rw [hAkB, ← hAB, mul_one]
      exact mul_left_cancel₀ hApos.ne' this
    have : (2 : ℤ) * (e : ℤ) = (s : ℤ) := by rw [hk', hk1, mul_one]
    exact_mod_cast this

theorem sum_relIndex_eq_index [Γ.FiniteIndex] (τ : ℍ) [Fintype (OrbQ Γ τ)] :
    ∑ q : OrbQ Γ τ, (((pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) (rep Γ τ q)) : ℕ) : ℤ) =
      ((pm Γ).index : ℤ) := by
  have h := Ws49.OrbitStab.finsum_relIndex_stabilizer_eq_index_negOne_sup Γ τ
  rw [finsum_eq_sum_of_fintype] at h
  have h' : ∑ q : OrbQ Γ τ, (pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) (rep Γ τ q)) =
      (pm Γ).index := by
    rw [← h]
    exact Finset.sum_congr rfl fun q _ => rfl
  exact_mod_cast h'

theorem sum_ord_rep_eq [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (hF : F₀ = qExpFunctionFieldC ℚ Γ)
    (D : ComplexPlaceDictionaryOf Γ F₀)
    (hsep : ∀ τ τ' : ℍ, D.pt τ = D.pt τ' → ∃ γ ∈ Γ, γ • τ = τ') (J : JLine Γ F₀)
    (τ : ℍ) [Fintype (OrbQ Γ τ)] :
    ∑ q : OrbQ Γ τ, (D.pt (rep Γ τ q)).ord (J.x - algebraMap ℂ (CF F₀) (jfun τ)) =
      (finrankAlong ℂ J.φ : ℤ) := by
  classical
  have hinj : Function.Injective (fun q : OrbQ Γ τ => D.pt (rep Γ τ q)) := by
    intro q₁ q₂ h
    obtain ⟨γ, hγ, hγe⟩ := hsep _ _ h
    have hrel : (MulAction.orbitRel (pm Γ) (MulAction.orbit SL(2, ℤ) τ)) (q₂.out) (q₁.out) := by
      show (q₂.out : MulAction.orbit SL(2, ℤ) τ) ∈
        MulAction.orbit (pm Γ) (q₁.out : MulAction.orbit SL(2, ℤ) τ)
      refine MulAction.mem_orbit_iff.mpr ⟨⟨γ, le_pm Γ hγ⟩, ?_⟩
      apply Subtype.ext
      exact hγe
    calc q₁ = Quotient.mk _ q₁.out := (Quotient.out_eq q₁).symm
      _ = Quotient.mk _ q₂.out := (Quotient.sound hrel).symm
      _ = q₂ := Quotient.out_eq q₂
  have hS : ∀ W, W ∈ Finset.univ.image (fun q : OrbQ Γ τ => D.pt (rep Γ τ q)) ↔
      0 < W.ord (J.x - algebraMap ℂ (CF F₀) (jfun τ)) := by
    intro W
    constructor
    · intro hW
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hW
      exact ord_pos_of_jfun_eq hT D J.x J.hx (jfun_rep τ q)
    · intro hpos

      have hne : J.x - algebraMap ℂ (CF F₀) (jfun τ) ≠ 0 := sub_algebraMap_ne_zero J.x J.hx _
      have hmem_sub : J.x - algebraMap ℂ (CF F₀) (jfun τ) ∈ W.toValuationSubring :=
        Place.mem_of_ord_nonneg W hne hpos.le
      have hmem_c : (algebraMap ℂ (CF F₀) (jfun τ)) ∈ W.toValuationSubring := W.algebraMap_mem' _
      have hxW : J.x ∈ W.toValuationSubring := by
        have := add_mem hmem_sub hmem_c
        simpa using this
      obtain ⟨σ, hσ⟩ := exists_pt_eq_of_mem Γ hT F₀ hF D W J.x J.hx hxW
      have hj : jfun σ = jfun τ :=
        jfun_eq_of_ord_pos hT D J.x J.hx (by rw [hσ]; exact hpos)
      obtain ⟨g, hg⟩ := exists_smul_eq_of_jfun_eq hj
      have hσorb : σ ∈ MulAction.orbit SL(2, ℤ) τ := MulAction.mem_orbit_iff.mpr ⟨g, hg⟩
      obtain ⟨h, hh, hhe⟩ := exists_mem_pm_smul_rep_eq (Γ := Γ) τ σ hσorb
      refine Finset.mem_image.mpr ⟨Quotient.mk _ ⟨σ, hσorb⟩, Finset.mem_univ _, ?_⟩
      calc D.pt (rep Γ τ (Quotient.mk _ ⟨σ, hσorb⟩))
          = D.pt (h • rep Γ τ (Quotient.mk _ ⟨σ, hσorb⟩)) := (pt_smul_of_mem_pm D hh _).symm
        _ = D.pt σ := by rw [hhe]
        _ = W := hσ
  have := J.sum_fiber (jfun τ) (Finset.univ.image fun q : OrbQ Γ τ => D.pt (rep Γ τ q)) hS
  rw [Finset.sum_image (fun q₁ _ q₂ _ h => hinj h)] at this
  exact this

end Orbits

def twoI : ℍ := ⟨2 * Complex.I, by simp⟩

theorem twoI_mem_fd : twoI ∈ ModularGroup.fd := by
  constructor
  · show 1 ≤ Complex.normSq (2 * Complex.I)
    norm_num [Complex.normSq_apply]
  · show |(2 * Complex.I).re| ≤ 1 / 2
    simp

theorem card_stabilizer_twoI : Nat.card (MulAction.stabilizer SL(2, ℤ) twoI) = 2 := by
  have him : (twoI : ℂ).im = 2 := by simp [twoI]
  have hI : twoI ≠ UpperHalfPlane.I := by
    intro h
    have := congrArg (fun z : ℍ => (z : ℂ).im) h
    simp [twoI] at this
  have hρ : twoI ≠ UpperHalfPlane.ρ := by
    intro h
    have h2 : ((twoI : ℍ) : ℂ).im = ((UpperHalfPlane.ρ : ℍ) : ℂ).im := by rw [h]
    rw [him] at h2
    have h3 : ((UpperHalfPlane.ρ : ℍ) : ℂ).im ≤ 1 := by
      have := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ 4 by norm_num)
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
      simp [UpperHalfPlane.ρ]
      linarith
    linarith
  have hρ' : twoI ≠ (1 : ℝ) +ᵥ UpperHalfPlane.ρ := by
    intro h
    have h2 : ((twoI : ℍ) : ℂ).im = (((1 : ℝ) +ᵥ UpperHalfPlane.ρ : ℍ) : ℂ).im := by rw [h]
    rw [him] at h2
    have h3 : (((1 : ℝ) +ᵥ UpperHalfPlane.ρ : ℍ) : ℂ).im ≤ 1 := by
      have := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ 4 by norm_num)
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
      simp [UpperHalfPlane.ρ, UpperHalfPlane.coe_vadd]
      linarith
    linarith
  have hiff : ∀ g : SL(2, ℤ), g ∈ MulAction.stabilizer SL(2, ℤ) twoI ↔
      g ∈ ({1, -1} : Finset SL(2, ℤ)) := by
    intro g
    rw [MulAction.mem_stabilizer_iff, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun hg => ModularGroup.stabilizer_of_ne twoI_mem_fd hg hI hρ hρ', ?_⟩
    rintro (rfl | rfl)
    · exact one_smul _ _
    · rw [ModularGroup.SL_neg_smul, one_smul]
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (q := fun g => g ∈ ({1, -1} : Finset SL(2, ℤ))) hiff), Nat.card_eq_finsetCard]
  decide

theorem index_le_finrankAlong [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (hF : F₀ = qExpFunctionFieldC ℚ Γ)
    (D : ComplexPlaceDictionaryOf Γ F₀)
    (hsep : ∀ τ τ' : ℍ, D.pt τ = D.pt τ' → ∃ γ ∈ Γ, γ • τ = τ') (J : JLine Γ F₀) :
    ((pm Γ).index : ℤ) ≤ (finrankAlong ℂ J.φ : ℤ) := by
  classical
  haveI : Finite (OrbQ Γ twoI) := Ws49.OrbitStab.finite_orbitRelQuotient_orbit (pm Γ) twoI
  letI : Fintype (OrbQ Γ twoI) := Fintype.ofFinite _
  rw [← sum_relIndex_eq_index (Γ := Γ) twoI, ← sum_ord_rep_eq hT hF D hsep J twoI]
  refine Finset.sum_le_sum fun q _ => ?_

  have hs₁ : Nat.card (MulAction.stabilizer SL(2, ℤ) (rep Γ twoI q)) = 2 := by
    rw [card_stabilizer_rep, card_stabilizer_twoI]
  have hBs := Ws49.OrbitStab.relIndex_stabilizer_mul_card_stabilizer (pm Γ) (rep Γ twoI q)
  rw [hs₁] at hBs
  have hs2 := two_le_card_stabilizer_pm (Γ := Γ) (rep Γ twoI q)
  have hB : (pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) (rep Γ twoI q)) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : 2 * 2 ≤ (pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) (rep Γ twoI q)) *
        Nat.card (MulAction.stabilizer (pm Γ) (rep Γ twoI q)) := Nat.mul_le_mul hlt hs2
    omega
  have hA := (termwise hT D J.x J.hx (rep Γ twoI q) (jfun twoI) (jfun_rep twoI q)).1
  calc (((pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) (rep Γ twoI q)) : ℕ) : ℤ) ≤ 1 := by
        exact_mod_cast hB
    _ ≤ _ := hA

theorem two_mul_ramification_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = qExpFunctionFieldC ℚ Γ)
    (D : ComplexPlaceDictionaryOf Γ F₀)
    (hsep : ∀ τ τ' : ℍ, D.pt τ = D.pt τ' → ∃ γ ∈ Γ, γ • τ = τ')
    (τ : ℍ) :
    2 * D.ramification τ = Nat.card (MulAction.stabilizer (pm Γ) τ) := by
  classical
  obtain ⟨J⟩ := nonempty_jLine Γ hT F₀ hF
  haveI : Finite (OrbQ Γ τ) := Ws49.OrbitStab.finite_orbitRelQuotient_orbit (pm Γ) τ
  letI : Fintype (OrbQ Γ τ) := Fintype.ofFinite _

  have hle : ∀ q ∈ (Finset.univ : Finset (OrbQ Γ τ)),
      (D.pt (rep Γ τ q)).ord (J.x - algebraMap ℂ (CF F₀) (jfun τ)) ≤
        (((pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) (rep Γ τ q)) : ℕ) : ℤ) :=
    fun q _ => (termwise hT D J.x J.hx (rep Γ τ q) (jfun τ) (jfun_rep τ q)).2.1
  have hge : ∑ q : OrbQ Γ τ, (((pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) (rep Γ τ q)) : ℕ) : ℤ) ≤
      ∑ q : OrbQ Γ τ, (D.pt (rep Γ τ q)).ord (J.x - algebraMap ℂ (CF F₀) (jfun τ)) := by
    rw [sum_relIndex_eq_index (Γ := Γ) τ, sum_ord_rep_eq hT hF D hsep J τ]
    exact index_le_finrankAlong hT hF D hsep J
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm (Finset.sum_le_sum hle) hge)

  set q₀ : OrbQ Γ τ := Quotient.mk _ ⟨τ, MulAction.mem_orbit_self τ⟩ with hq₀
  obtain ⟨h, hh, hhe⟩ := exists_mem_pm_smul_rep_eq (Γ := Γ) τ τ (MulAction.mem_orbit_self τ)
  have h0 := heq q₀ (Finset.mem_univ _)

  have hpt : D.pt (rep Γ τ q₀) = D.pt τ := by
    rw [← (pt_smul_of_mem_pm D hh (rep Γ τ q₀)), hhe]
  have hrel : (pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) (rep Γ τ q₀)) =
      (pm Γ).relIndex (MulAction.stabilizer SL(2, ℤ) τ) := by
    rw [← Ws49.OrbitStab.relIndex_stabilizer_smul_of_mem (pm Γ) hh (rep Γ τ q₀), hhe]
  rw [hpt, hrel] at h0
  exact (termwise hT D J.x J.hx τ (jfun τ) rfl).2.2 h0

end ModularCurve.ComplexPlaceDictionaryOf.RamEqCard
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionaryOf P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionaryOf.RamEqCard"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionaryOf"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionaryOf P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionaryOf.RamEqCard"

open scoped MatrixGroups in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
    (hsep : ∀ τ τ' : UpperHalfPlane, D.pt τ = D.pt τ' → ∃ γ ∈ Γ, γ • τ = τ')
    (τ : UpperHalfPlane) :
    2 * D.ramification τ =
      Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) :=
  ModularCurve.ComplexPlaceDictionaryOf.RamEqCard.two_mul_ramification_eq Γ hT F₀ hF D hsep τ

end S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer (solution)
