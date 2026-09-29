-- Prove2me | solution 1 for ModularCurve.existsToricDichotomyData_of_jZeroSemistableSpecialization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c4bd4131-f678-5005-be7f-7a261ebf093a

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_ToricDichotomyData
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.IsPrincipal Pic0 SemilinearAut SemilinearAut.baseAut GluingData GluedPic0 GluedPic0.toPic0Pair GluedPic0.nodeUnit SemilinearAut.nodePerm SemilinearAut.baseAutUnitsHom SemilinearAut.baseAutUnitsHom_apply GluedPic0.glueMap GluedPic0.glueMap_nodeUnit"
p2m_open "AlgebraicCurve"

section MiddleExact

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (S : Finset (Place K F × Place K F))

namespace GluedPic0
p2m_export "AlgebraicCurve.GluedPic0" "mk_surjective mk_eq_mk_iff toPic0Pair toPic0Pair_mk nodeUnit nodeUnit_apply toPic0Pair_nodeUnit glueMap glueMap_nodeUnit"
p2m_open "AlgebraicCurve.GluedPic0"

p2m_open "AlgebraicCurve.GluingData"

private theorem ker_toPic0Pair_eq_range_nodeUnit
    (hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap K ((s : Place K F × Place K F).1.ResidueField)) ∧
        Function.Surjective (algebraMap K ((s : Place K F × Place K F).2.ResidueField))) :
    (toPic0Pair S).ker = (nodeUnit S).range := by
  ext ξ
  constructor
  · intro hξ
    obtain ⟨x, rfl⟩ := mk_surjective S ξ
    rw [AddMonoidHom.mem_ker, toPic0Pair_mk, Prod.mk_eq_zero] at hξ
    obtain ⟨h₁, h₂⟩ := hξ
    obtain ⟨g₁, hg₁, hpt₁⟩ : Divisor.IsPrincipal (x : GluingData K F S).1 :=
      (QuotientAddGroup.eq_zero_iff _).mp h₁
    obtain ⟨g₂, hg₂, hpt₂⟩ : Divisor.IsPrincipal (x : GluingData K F S).2.1 :=
      (QuotientAddGroup.eq_zero_iff _).mp h₂
    have hval : ∀ s : ↥S, ∃ a b : Kˣ,
        (s : Place K F × Place K F).1.HasValue g₁ (a : K) ∧
          (s : Place K F × Place K F).2.HasValue g₂ (b : K) := by
      intro s
      obtain ⟨hz₁, hz₂⟩ := x.2.2.2 (s : Place K F × Place K F) s.2
      obtain ⟨hm₁, hu₁⟩ := (s : Place K F × Place K F).1.exists_isUnit_of_ord_eq_zero hg₁
        ((hpt₁ _).symm.trans hz₁)
      obtain ⟨hm₂, hu₂⟩ := (s : Place K F × Place K F).2.exists_isUnit_of_ord_eq_zero hg₂
        ((hpt₂ _).symm.trans hz₂)
      obtain ⟨a, ha, hane⟩ := (s : Place K F × Place K F).1.exists_hasValue_of_surjective
        (hrat s).1 hm₁
      obtain ⟨b, hb, hbne⟩ := (s : Place K F × Place K F).2.exists_hasValue_of_surjective
        (hrat s).2 hm₂
      exact ⟨Units.mk0 a (hane hu₁), Units.mk0 b (hbne hu₂), ha, hb⟩
    choose a b hab using hval
    have hpP : IsGluedPrincipal S
        (((x : GluingData K F S).1, (x : GluingData K F S).2.1,
          fun s => Additive.ofMul (a s / b s)) : GluingData K F S) :=
      ⟨g₁, g₂, a, b, hg₁, hg₂, hpt₁, hpt₂, hab, rfl⟩
    refine ⟨(x : GluingData K F S).2.2 - fun s => Additive.ofMul (a s / b s), ?_⟩
    rw [nodeUnit_apply, mk_eq_mk_iff]
    have hEq : (((x : GluingData K F S).1, (x : GluingData K F S).2.1,
          fun s => Additive.ofMul (a s / b s)) : GluingData K F S) =
        -((0, 0, (x : GluingData K F S).2.2 - fun s => Additive.ofMul (a s / b s)) :
          GluingData K F S) + (x : GluingData K F S) := by
      refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
      · simp
      · simp
      · funext s
        simp only [Prod.snd_neg, Prod.snd_add, Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
        abel
    exact hEq ▸ hpP
  · rintro ⟨w, rfl⟩
    rw [AddMonoidHom.mem_ker, toPic0Pair_nodeUnit]

end GluedPic0

end MiddleExact

end AlgebraicCurve

end

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "HeckeOperatorsCommuteBar heckeModuleBar JZero HeckeAlg heckeGen heckeTorsion mem_heckeTorsion_iff PrimeToTorsion PrimeToTorsion.zero PrimeToTorsion.add PrimeToTorsion.map inertiaInvariants instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable JZeroSemistableSpecialization modularFunctionFieldC ToricFrobeniusHecke IsEventuallyEisenstein HasLowerLevelTorsion ToricFrobeniusSq IsToricDichotomyQGuarded heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization.AlgebraicCurve IsLocalRing"

local notation "Qbar" => AlgebraicClosure ℚ

section Reduction

set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 1600000

open MvPolynomial AddMonoidHom

variable {A : ValuationSubring Qbar} {N q : ℕ} {hq : q.Prime} [NeZero N]

private theorem _root_.ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_decompositionSubgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L] {A : ValuationSubring L}
    {φ : L ≃ₐ[K] L} (hφ : φ ∈ A.decompositionSubgroup K)
    {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K) :
    φ⁻¹ * τ * φ ∈ A.inertiaSubgroupIn K := by
  rw [ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map] at hτ ⊢
  obtain ⟨τ', hτ', rfl⟩ := hτ
  refine ⟨⟨φ, hφ⟩⁻¹ * τ' * ⟨φ, hφ⟩, ?_, ?_⟩
  · exact Subgroup.Normal.conj_mem' (inferInstanceAs (MonoidHom.ker _).Normal) τ' hτ' ⟨φ, hφ⟩
  · rfl

p2m_alias "P2MW.S_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization.ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_decompositionSubgroup" "ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_decompositionSubgroup"

private theorem _root_.ValuationSubring.IsFrobeniusAt.conj_mem_inertiaSubgroupIn
    {K L : Type*} [Field K] [Field L] [Algebra K L] {A : ValuationSubring L}
    {φ : L ≃ₐ[K] L} {q : ℕ} (hφ : A.IsFrobeniusAt φ q)
    {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K) :
    φ⁻¹ * τ * φ ∈ A.inertiaSubgroupIn K :=
  ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_decompositionSubgroup
    hφ.mem_decompositionSubgroup hτ

p2m_alias "P2MW.S_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization.ValuationSubring.IsFrobeniusAt.conj_mem_inertiaSubgroupIn" "ValuationSubring.IsFrobeniusAt.conj_mem_inertiaSubgroupIn"
omit [NeZero N] in

private theorem frob_smul_mem_inertiaInvariants {φ : Qbar ≃ₐ[ℚ] Qbar} (hφ : A.IsFrobeniusAt φ q)
    {x : JZero (N * q)} (hx : x ∈ inertiaInvariants A (N * q)) :
    φ • x ∈ inertiaInvariants A (N * q) := by
  intro σ hσ
  have key : (φ⁻¹ * σ * φ) • x = x := hx _ (hφ.conj_mem_inertiaSubgroupIn hσ)
  calc σ • φ • x = (σ * φ) • x := (mul_smul σ φ x).symm
    _ = (φ * (φ⁻¹ * σ * φ)) • x := by rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = φ • (φ⁻¹ * σ * φ) • x := mul_smul φ _ x
    _ = φ • x := by rw [key]

variable [Module HeckeAlg (JZero (N * q))]
  [SMulCommClass (Qbar ≃ₐ[ℚ] Qbar) HeckeAlg (JZero (N * q))]

omit [NeZero N] in

private theorem hecke_smul_mem_inertiaInvariants (T : HeckeAlg) {x : JZero (N * q)}
    (hx : x ∈ inertiaInvariants A (N * q)) : T • x ∈ inertiaInvariants A (N * q) :=
  fun σ hσ => by rw [smul_comm, hx σ hσ]

variable [Module HeckeAlg (JZero N)]
  [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]
variable (D : JZeroSemistableSpecialization A N q hq)

omit [SMulCommClass (Qbar ≃ₐ[ℚ] Qbar) HeckeAlg (JZero (N * q))] in

private theorem baseAutUnitsHom_eq_nsmul (x : Additive (ResidueField A)ˣ) :
    SemilinearAut.baseAutUnitsHom D.frob x = q • x := by
  rw [SemilinearAut.baseAutUnitsHom_apply]
  have h : Units.map ((SemilinearAut.baseAut D.frob :
      ResidueField A →+* ResidueField A) : ResidueField A →* ResidueField A) x.toMul
      = x.toMul ^ q := by
    ext
    simp [D.baseAut_frob]
  rw [h, ofMul_pow, ofMul_toMul]

omit [SMulCommClass (Qbar ≃ₐ[ℚ] Qbar) HeckeAlg (JZero (N * q))] in

private theorem glueMap_nodeUnit_eq_nsmul (w : ↥D.nodes → Additive (ResidueField A)ˣ) :
    GluedPic0.glueMap D.nodes D.frob D.frob_nodeStable (GluedPic0.nodeUnit D.nodes w)
      = q • GluedPic0.nodeUnit D.nodes
          (fun t => w ((SemilinearAut.nodePerm D.nodes D.frob D.frob_nodeStable).symm t)) := by
  rw [GluedPic0.glueMap_nodeUnit]
  have h : (fun t => SemilinearAut.baseAutUnitsHom D.frob
      (w ((SemilinearAut.nodePerm D.nodes D.frob D.frob_nodeStable).symm t)))
      = q • (fun t => w ((SemilinearAut.nodePerm D.nodes D.frob D.frob_nodeStable).symm t)) := by
    funext t
    rw [Pi.smul_apply, baseAutUnitsHom_eq_nsmul]
  rw [h, map_nsmul]

omit [SMulCommClass (Qbar ≃ₐ[ℚ] Qbar) HeckeAlg (JZero (N * q))] in

private theorem nodePerm_symm_eq (t : ↥D.nodes) :
    (SemilinearAut.nodePerm D.nodes D.frob D.frob_nodeStable).symm t
      = SemilinearAut.nodePerm D.nodes D.frob D.frob_nodeStable t := by
  rw [Equiv.symm_apply_eq]
  exact (D.nodePerm_nodePerm t).symm

omit [SMulCommClass (Qbar ≃ₐ[ℚ] Qbar) HeckeAlg (JZero (N * q))] in

private theorem glueMap_glueMap_nodeUnit_eq_zsmul (w : ↥D.nodes → Additive (ResidueField A)ˣ) :
    GluedPic0.glueMap D.nodes D.frob D.frob_nodeStable
        (GluedPic0.glueMap D.nodes D.frob D.frob_nodeStable (GluedPic0.nodeUnit D.nodes w))
      = ((q : ℤ) ^ 2) • GluedPic0.nodeUnit D.nodes w := by
  rw [glueMap_nodeUnit_eq_nsmul, map_nsmul, glueMap_nodeUnit_eq_nsmul]
  have hww : (fun t => w ((SemilinearAut.nodePerm D.nodes D.frob D.frob_nodeStable).symm
      ((SemilinearAut.nodePerm D.nodes D.frob D.frob_nodeStable).symm t))) = w := by
    funext t
    rw [nodePerm_symm_eq, nodePerm_symm_eq, D.nodePerm_nodePerm]
  rw [hww]
  rw [(mul_nsmul (GluedPic0.nodeUnit D.nodes w) q q).symm, ← natCast_zsmul,
    show ((q * q : ℕ) : ℤ) = (q : ℤ) ^ 2 by push_cast; ring]

private def toricPart : Submodule HeckeAlg (JZero (N * q)) where
  carrier := {x | PrimeToTorsion q x ∧ ∃ h : x ∈ inertiaInvariants A (N * q),
    D.comp ⟨x, h⟩ = 0 ∧ GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, h⟩) = 0}
  zero_mem' := by
    have h0 : (⟨(0 : JZero (N * q)), (inertiaInvariants A (N * q)).zero_mem⟩ :
        ↥(inertiaInvariants A (N * q))) = 0 := rfl
    exact ⟨PrimeToTorsion.zero hq.ne_one, (inertiaInvariants A (N * q)).zero_mem,
      by rw [h0, map_zero], by rw [h0, map_zero, map_zero]⟩
  add_mem' := by
    rintro a b ⟨hta, ha, hacomp, haν⟩ ⟨htb, hb, hbcomp, hbν⟩
    have hab : (⟨a + b, add_mem ha hb⟩ : ↥(inertiaInvariants A (N * q)))
        = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    refine ⟨PrimeToTorsion.add hq hta htb, add_mem ha hb, ?_, ?_⟩
    · rw [hab, map_add, hacomp, hbcomp, add_zero]
    · rw [hab, map_add, map_add, haν, hbν, add_zero]
  smul_mem' := by
    rintro c x ⟨htx, hk, hcomp, hν⟩
    have hck : c • x ∈ inertiaInvariants A (N * q) := hecke_smul_mem_inertiaInvariants c hk
    exact ⟨PrimeToTorsion.map (DistribSMul.toAddMonoidHom (JZero (N * q)) c) htx, hck,
      D.comp_hecke_of_comp_eq_zero c ⟨x, hk⟩ hck hcomp,
      D.toPic0Pair_sp_eq_zero c ⟨x, hk⟩ hck hcomp hν⟩

private theorem mem_toricPart {x : JZero (N * q)} :
    x ∈ toricPart D ↔ PrimeToTorsion q x ∧ ∃ h : x ∈ inertiaInvariants A (N * q),
      D.comp ⟨x, h⟩ = 0 ∧ GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, h⟩) = 0 :=
  Iff.rfl

private theorem comp_eisensteinElt_smul (ℓ : Nat.Primes) (hℓgood : ¬ (ℓ : ℕ) ∣ N * q)
    {x : JZero (N * q)} (hH : x ∈ inertiaInvariants A (N * q))
    (humem : (heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x ∈ inertiaInvariants A (N * q)) :
    D.comp ⟨(heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x, humem⟩ = 0 := by
  have hT : heckeGen ℓ • x ∈ inertiaInvariants A (N * q) :=
    hecke_smul_mem_inertiaInvariants _ hH
  have h1 : D.comp ⟨heckeGen ℓ • x, hT⟩ = (((ℓ : ℕ) : ℤ) + 1) • D.comp ⟨x, hH⟩ :=
    D.comp_heckeGen ℓ hℓgood ⟨x, hH⟩ hT
  have hsplit : (⟨(heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x, humem⟩ :
      ↥(inertiaInvariants A (N * q)))
      = ⟨heckeGen ℓ • x, hT⟩ - ((ℓ : ℕ) + 1) • ⟨x, hH⟩ := by
    apply Subtype.ext
    show (heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x
        = heckeGen ℓ • x - ((ℓ : ℕ) + 1) • x
    rw [sub_smul, (Nat.cast_add_one (R := HeckeAlg) (ℓ : ℕ)).symm,
      Nat.cast_smul_eq_nsmul HeckeAlg]
  rw [hsplit, map_sub, map_nsmul, h1, ← natCast_zsmul, Nat.cast_add_one, sub_self]

private theorem comp_eq_zero_of_mem_heckeTorsion {𝔪 : Ideal HeckeAlg} (hmax : 𝔪.IsMaximal)
    (heis : ¬ IsEventuallyEisenstein 𝔪) {x : JZero (N * q)}
    (hx : x ∈ heckeTorsion (JZero (N * q)) 𝔪)
    (hH : x ∈ inertiaInvariants A (N * q)) : D.comp ⟨x, hH⟩ = 0 := by
  have hkill : ∀ t ∈ 𝔪, t • x = 0 := (mem_heckeTorsion_iff _ _ _).mp hx
  simp only [IsEventuallyEisenstein] at heis
  push Not at heis
  obtain ⟨ℓ, hℓS, hu⟩ := heis ((N * q).primeFactors.subtype Nat.Prime)
  have hℓgood : ¬ (ℓ : ℕ) ∣ N * q := by
    intro hdvd
    exact hℓS (Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr
      ⟨ℓ.2, hdvd, mul_ne_zero (NeZero.ne N) hq.ne_zero⟩))
  have humem : (heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x ∈ inertiaInvariants A (N * q) :=
    hecke_smul_mem_inertiaInvariants _ hH
  have hcompu : D.comp ⟨(heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x, humem⟩ = 0 :=
    comp_eisensteinElt_smul D ℓ hℓgood hH humem
  obtain ⟨r, i, hi, hri⟩ := hmax.exists_inv hu
  have hrmem : r • ((heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x)
      ∈ inertiaInvariants A (N * q) := hecke_smul_mem_inertiaInvariants _ humem
  have hx1 : (⟨x, hH⟩ : ↥(inertiaInvariants A (N * q)))
      = ⟨r • ((heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x), hrmem⟩ := by
    apply Subtype.ext
    show x = r • ((heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x)
    conv_lhs => rw [← one_smul HeckeAlg x, ← hri]
    rw [add_smul, mul_smul, hkill i hi, add_zero]
  rw [hx1]
  exact D.comp_hecke_of_comp_eq_zero r ⟨_, humem⟩ hrmem hcompu

private theorem toricFrobeniusSq_toricPart (φ : Qbar ≃ₐ[ℚ] Qbar) (hφ : A.IsFrobeniusAt φ q) :
    ToricFrobeniusSq (q : ℕ) φ (toricPart D) := by
  intro x hx
  obtain ⟨htx, hH, hcomp, hν⟩ := hx
  have hHφ : φ • x ∈ inertiaInvariants A (N * q) := frob_smul_mem_inertiaInvariants hφ hH
  have hHφφ : φ • φ • x ∈ inertiaInvariants A (N * q) :=
    frob_smul_mem_inertiaInvariants hφ hHφ
  have hcompφ : D.comp ⟨φ • x, hHφ⟩ = 0 := D.comp_frob_of_comp_eq_zero φ hφ ⟨x, hH⟩ hHφ hcomp
  have hcompφφ : D.comp ⟨φ • φ • x, hHφφ⟩ = 0 :=
    D.comp_frob_of_comp_eq_zero φ hφ ⟨φ • x, hHφ⟩ hHφφ hcompφ
  obtain ⟨w, hw⟩ : D.sp ⟨x, hH⟩ ∈ (GluedPic0.nodeUnit D.nodes).range := by
    rw [← GluedPic0.ker_toPic0Pair_eq_range_nodeUnit D.nodes
      (fun s => D.nodes_rational s.1 s.2)]
    exact mem_ker.mpr hν
  have hHz : φ • φ • x - ((q : ℤ) ^ 2) • x ∈ inertiaInvariants A (N * q) :=
    sub_mem hHφφ ((inertiaInvariants A (N * q)).zsmul_mem hH _)
  have hzsplit : (⟨φ • φ • x - ((q : ℤ) ^ 2) • x, hHz⟩ : ↥(inertiaInvariants A (N * q)))
      = ⟨φ • φ • x, hHφφ⟩ - ((q : ℤ) ^ 2) • ⟨x, hH⟩ := by
    apply Subtype.ext
    rfl
  have hcompz : D.comp ⟨φ • φ • x - ((q : ℤ) ^ 2) • x, hHz⟩ = 0 := by
    rw [hzsplit, map_sub, map_zsmul, hcompφφ, hcomp, zsmul_zero, sub_self]
  have hspz : D.sp ⟨φ • φ • x - ((q : ℤ) ^ 2) • x, hHz⟩ = 0 := by
    rw [hzsplit, map_sub, map_zsmul, D.sp_frob φ hφ ⟨φ • x, hHφ⟩ hHφφ hcompφ,
      D.sp_frob φ hφ ⟨x, hH⟩ hHφ hcomp, ← hw, glueMap_glueMap_nodeUnit_eq_zsmul, hw,
      sub_self]
  have hztors : PrimeToTorsion q (φ • φ • x - ((q : ℤ) ^ 2) • x) :=
    PrimeToTorsion.map
      ((DistribSMul.toAddMonoidHom (JZero (N * q)) φ).comp
          (DistribSMul.toAddMonoidHom (JZero (N * q)) φ)
        - DistribSMul.toAddMonoidHom (JZero (N * q)) ((q : ℤ) ^ 2)) htx
  have hz0 : (⟨φ • φ • x - ((q : ℤ) ^ 2) • x, hHz⟩ : ↥(inertiaInvariants A (N * q))) = 0 :=
    D.sp_injective ⟨_, hHz⟩ hztors hcompz hspz
  have hz0' : φ • φ • x - ((q : ℤ) ^ 2) • x = 0 := by
    have := Subtype.ext_iff.mp hz0
    rwa [ZeroMemClass.coe_zero] at this
  exact sub_eq_zero.mp hz0'

private theorem toricFrobeniusHecke_toricPart (φ : Qbar ≃ₐ[ℚ] Qbar) (hφ : A.IsFrobeniusAt φ q) :
    ToricFrobeniusHecke ⟨q, hq⟩ φ (toricPart D) := by
  intro x hx
  obtain ⟨htx, hH, hcomp, hν⟩ := hx
  have hHT : heckeGen ⟨q, hq⟩ • x ∈ inertiaInvariants A (N * q) :=
    hecke_smul_mem_inertiaInvariants _ hH
  have hHqT : (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x ∈ inertiaInvariants A (N * q) :=
    hecke_smul_mem_inertiaInvariants _ hH
  have hHφ : φ • x ∈ inertiaInvariants A (N * q) := frob_smul_mem_inertiaInvariants hφ hH
  have hcompqT : D.comp ⟨(((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x, hHqT⟩ = 0 :=
    D.comp_hecke_of_comp_eq_zero _ ⟨x, hH⟩ hHqT hcomp
  have hcompφ : D.comp ⟨φ • x, hHφ⟩ = 0 := D.comp_frob_of_comp_eq_zero φ hφ ⟨x, hH⟩ hHφ hcomp
  obtain ⟨w, hw⟩ : D.sp ⟨x, hH⟩ ∈ (GluedPic0.nodeUnit D.nodes).range := by
    rw [← GluedPic0.ker_toPic0Pair_eq_range_nodeUnit D.nodes
      (fun s => D.nodes_rational s.1 s.2)]
    exact mem_ker.mpr hν
  have hspT : D.sp ⟨heckeGen ⟨q, hq⟩ • x, hHT⟩
      = GluedPic0.nodeUnit D.nodes
          (fun t => w ((SemilinearAut.nodePerm D.nodes D.frob D.frob_nodeStable).symm t)) :=
    D.sp_heckeGen_self ⟨x, hH⟩ hHT hcomp w hw.symm
  have hspqT : D.sp ⟨(((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x, hHqT⟩
      = GluedPic0.glueMap D.nodes D.frob D.frob_nodeStable (D.sp ⟨x, hH⟩) := by
    have hsub : (⟨(((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x, hHqT⟩ :
        ↥(inertiaInvariants A (N * q))) = q • ⟨heckeGen ⟨q, hq⟩ • x, hHT⟩ := by
      apply Subtype.ext
      show (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x = q • (heckeGen ⟨q, hq⟩ • x)
      rw [mul_smul, Nat.cast_smul_eq_nsmul]
    rw [hsub, map_nsmul, hspT, ← glueMap_nodeUnit_eq_nsmul, hw]
  have hHz : φ • x - (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x
      ∈ inertiaInvariants A (N * q) := sub_mem hHφ hHqT
  have hzsplit : (⟨φ • x - (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x, hHz⟩ :
      ↥(inertiaInvariants A (N * q)))
      = ⟨φ • x, hHφ⟩ - ⟨(((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x, hHqT⟩ := by
    apply Subtype.ext
    rfl
  have hcompz : D.comp ⟨φ • x - (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x, hHz⟩ = 0 := by
    rw [hzsplit, map_sub, hcompφ, hcompqT, sub_self]
  have hspz : D.sp ⟨φ • x - (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x, hHz⟩ = 0 := by
    rw [hzsplit, map_sub, D.sp_frob φ hφ ⟨x, hH⟩ hHφ hcomp, hspqT, sub_self]
  have hztors : PrimeToTorsion q (φ • x - (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x) :=
    PrimeToTorsion.map
      (DistribSMul.toAddMonoidHom (JZero (N * q)) φ
        - DistribSMul.toAddMonoidHom (JZero (N * q))
            (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩)) htx
  have hz0 : (⟨φ • x - (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x, hHz⟩ :
      ↥(inertiaInvariants A (N * q))) = 0 :=
    D.sp_injective ⟨_, hHz⟩ hztors hcompz hspz
  have hz0' : φ • x - (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩) • x = 0 := by
    have := Subtype.ext_iff.mp hz0
    rwa [ZeroMemClass.coe_zero] at this
  exact sub_eq_zero.mp hz0'

private theorem hasLowerLevelTorsion_of_component {S : Finset Nat.Primes}
    (hSbad : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ N * q → ℓ ∈ S)
    {𝔪 : Ideal HeckeAlg} {x : JZero (N * q)}
    (hkill : ∀ t ∈ 𝔪, t • x = 0) (hH : x ∈ inertiaInvariants A (N * q))
    (hcomp0 : D.comp ⟨x, hH⟩ = 0)
    {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) (hpx : p • x = 0)
    (π : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N) ×
        Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N) →+
      Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
    (hπ : ∀ (T : HeckeAlg) z, π (T • z) = T • π z)
    (hπc : π (GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, hH⟩)) ≠ 0) :
    HasLowerLevelTorsion S 𝔪 (JZero N) := by
  have hqp : ¬ q ∣ p := fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm
  have hpsub : p • (⟨x, hH⟩ : ↥(inertiaInvariants A (N * q))) = 0 := by
    apply Subtype.ext
    show p • x = 0
    exact hpx
  have hπtors : PrimeToTorsion q (π (GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, hH⟩))) :=
    PrimeToTorsion.map (π.comp ((GluedPic0.toPic0Pair D.nodes).comp D.sp))
      ⟨p, hp.pos, hqp, hpsub⟩
  obtain ⟨y, hytors, hy⟩ := D.spN_surjective _ hπtors
  obtain ⟨n', hn'0, hn'q, hn'y⟩ := hytors
  refine ⟨y, fun h0 => hπc (by rw [← hy, h0, map_zero]), ?_, ?_⟩
  · intro m hm
    apply D.spN_injective
    · exact PrimeToTorsion.map (DistribSMul.toAddMonoidHom (JZero N) ((m : HeckeAlg)))
        ⟨n', hn'0, hn'q, hn'y⟩
    · have hmx : m • (⟨x, hH⟩ : ↥(inertiaInvariants A (N * q))) = 0 := by
        apply Subtype.ext
        show m • x = 0
        rw [← Nat.cast_smul_eq_nsmul HeckeAlg, hkill _ hm]
      rw [D.spN_hecke, hy, Nat.cast_smul_eq_nsmul HeckeAlg, ← map_nsmul π,
        ← map_nsmul (GluedPic0.toPic0Pair D.nodes), ← map_nsmul D.sp, hmx, map_zero,
        map_zero, map_zero]
  · intro ℓ hℓS b hgb
    have hℓgood : ¬ (ℓ : ℕ) ∣ N * q := fun hdvd => hℓS (hSbad ℓ hdvd)
    have hHT : heckeGen ℓ • x ∈ inertiaInvariants A (N * q) :=
      hecke_smul_mem_inertiaInvariants _ hH
    have hC : C b = ((b : ℤ) : HeckeAlg) := eq_intCast (C : ℤ →+* HeckeAlg) b
    have hsubty : (⟨heckeGen ℓ • x, hHT⟩ : ↥(inertiaInvariants A (N * q))) - b • ⟨x, hH⟩
        = 0 := by
      apply Subtype.ext
      show heckeGen ℓ • x - b • x = 0
      rw [← Int.cast_smul_eq_zsmul HeckeAlg, ← hC, ← sub_smul, hkill _ hgb]
    apply D.spN_injective
    · exact PrimeToTorsion.map (DistribSMul.toAddMonoidHom (JZero N) (heckeGen ℓ - C b))
        ⟨n', hn'0, hn'q, hn'y⟩
    · rw [D.spN_hecke, hy, sub_smul, hC, Int.cast_smul_eq_zsmul HeckeAlg,
        ← map_zsmul π, ← hπ, ← map_sub π,
        ← D.toPic0Pair_sp_heckeGen ℓ hℓgood ⟨x, hH⟩ hHT hcomp0,
        ← map_zsmul (GluedPic0.toPic0Pair D.nodes), ← map_zsmul D.sp,
        ← map_sub (GluedPic0.toPic0Pair D.nodes), ← map_sub D.sp, hsubty, map_zero, map_zero,
        map_zero]

private theorem isToricDichotomyQGuarded_toricPart {S : Finset Nat.Primes}
    (hSbad : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ N * q → ℓ ∈ S) :
    IsToricDichotomyQGuarded (q : ℕ) S (A.inertiaSubgroupIn ℚ) (toricPart D) (JZero N) := by
  intro 𝔪 hmax heis hqu x hx hinv
  have hH : x ∈ inertiaInvariants A (N * q) := hinv
  have hkill : ∀ t ∈ 𝔪, t • x = 0 := (mem_heckeTorsion_iff _ _ _).mp hx
  have hcomp0 : D.comp ⟨x, hH⟩ = 0 := comp_eq_zero_of_mem_heckeTorsion D hmax heis hx hH
  obtain ⟨p, hp, hpq, hpx⟩ := D.exists_prime_torsion 𝔪 hmax hqu x hx
  by_cases hν : GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, hH⟩) = 0
  · exact Or.inl ⟨⟨p, hp.pos, fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm,
      hpx⟩, hH, hcomp0, hν⟩
  · refine Or.inr ?_
    have hcomp_ne : (GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, hH⟩)).1 ≠ 0 ∨
        (GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, hH⟩)).2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hν (Prod.ext hcon.1 hcon.2)
    rcases hcomp_ne with h1 | h2
    · exact hasLowerLevelTorsion_of_component D hSbad hkill hH hcomp0 hp hpq hpx
        (AddMonoidHom.fst _ _) (fun T z => rfl) h1
    · exact hasLowerLevelTorsion_of_component D hSbad hkill hH hcomp0 hp hpq hpx
        (AddMonoidHom.snd _ _) (fun T z => rfl) h2

theorem _root_.P2MW.S_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization.solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N q : ℕ) [NeZero N] (hq : q.Prime)
    (S : Finset Nat.Primes) (hSbad : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ N * q → ℓ ∈ S)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    letI := ModularCurve.heckeModuleBar (N * q)
    letI := ModularCurve.heckeModuleBar N
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ [Module ModularCurve.HeckeAlg (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField A)
        (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N))]
      (D : ModularCurve.JZeroSemistableSpecialization A N q hq),
      ∃ 𝒯 : Submodule ModularCurve.HeckeAlg (ModularCurve.JZero (N * q)),
        (∀ x : ModularCurve.JZero (N * q), x ∈ 𝒯 ↔
          ModularCurve.PrimeToTorsion q x ∧
          ∃ h : x ∈ ModularCurve.inertiaInvariants A (N * q),
            D.comp ⟨x, h⟩ = 0 ∧
            AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, h⟩) = 0) ∧
        ModularCurve.ToricFrobeniusSq (q : ℕ) φ 𝒯 ∧
        ModularCurve.IsToricDichotomyQGuarded (q : ℕ) S (A.inertiaSubgroupIn ℚ) 𝒯
          (ModularCurve.JZero N) ∧
        ModularCurve.ToricFrobeniusHecke ⟨q, hq⟩ φ 𝒯 := by
  intro instP D
  haveI : NeZero q := ⟨hq.ne_zero⟩
  letI := ModularCurve.heckeModuleBar (N * q)
  letI := ModularCurve.heckeModuleBar N
  letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI hcomm : HeckeOperatorsCommuteBar (N * q) :=
    ModularCurve.heckeOperatorsCommuteBar (N * q)
  haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg
      (JZero (N * q)) :=
    ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar (N * q) hcomm
  exact ⟨toricPart D, fun _ => Iff.rfl,
    toricFrobeniusSq_toricPart D φ hφ,
    isToricDichotomyQGuarded_toricPart D hSbad,
    toricFrobeniusHecke_toricPart D φ hφ⟩

end Reduction

end ModularCurve

end

end S_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization
end P2MW
export P2MW.S_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization (solution)
