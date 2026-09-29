-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_sPartDual_eq_of_forall_cancel_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/04dec5d4-66f7-59d0-b91f-bd19f8a570b9

import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_LanglandsTunnell_Converse_sPartDual_eq_single
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.NumberField IsDedekindDomain"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.stdRootNumberAt Converse.sPartDual_eq_single TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero TateLocal.psiLocal_ne_one"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "pinnedExp IsAdmissibleTwist sPartDual sPartDual_eq_single"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

private theorem norm_le_one_of_forall_pow_norm_sub_one_lt (u : ℂ)
    (hu : ∀ n : ℕ, ‖u ^ n - 1‖ < 1) : ‖u‖ ≤ 1 := by
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) (not_le.mp h)
  have h1 := hu n
  have h2 : ‖u‖ ^ n - 1 ≤ ‖u ^ n - 1‖ := by
    simpa only [norm_pow, norm_one] using norm_sub_norm_le (u ^ n) 1
  linarith

private theorem eq_zero_of_abs_le_pi_of_forall_cos_pos (t : ℝ) (htpi : |t| ≤ Real.pi)
    (h : ∀ n : ℕ, 0 < Real.cos (n * t)) : t = 0 := by
  by_contra hne
  have ht : 0 < |t| := abs_pos.mpr hne
  have hcos : ∀ n : ℕ, 0 < Real.cos (n * |t|) := by
    intro n
    have hn := h n
    rwa [← Real.cos_abs, abs_mul, Nat.abs_cast] at hn
  have hex : ∃ n : ℕ, Real.pi / 2 ≤ n * |t| := by
    obtain ⟨n, hn⟩ := exists_nat_ge (Real.pi / 2 / |t|)
    exact ⟨n, (div_le_iff₀ ht).mp hn⟩
  classical
  have hspec : Real.pi / 2 ≤ (Nat.find hex : ℝ) * |t| := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · exfalso
      rw [h0] at hspec
      simp only [Nat.cast_zero, zero_mul] at hspec
      linarith [Real.pi_pos]
    · exact h0
  have hprev : ¬ Real.pi / 2 ≤ ((Nat.find hex - 1 : ℕ) : ℝ) * |t| :=
    Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
  rw [Nat.cast_sub hpos, Nat.cast_one] at hprev
  have hlt : (Nat.find hex : ℝ) * |t| < Real.pi / 2 + |t| := by
    have := not_le.mp hprev
    nlinarith
  have hle : (Nat.find hex : ℝ) * |t| ≤ Real.pi + Real.pi / 2 := by linarith
  have := Real.cos_nonpos_of_pi_div_two_le_of_le hspec hle
  linarith [hcos (Nat.find hex)]

private theorem c3id_units_eq_one_of_forall_zpow_norm_sub_one_lt (z : ℂˣ)
    (hz : ∀ n : ℤ, ‖((z ^ n : ℂˣ) : ℂ) - 1‖ < 1) : z = 1 := by
  have hpow : ∀ n : ℤ, ‖(z : ℂ) ^ n - 1‖ < 1 := fun n => by
    simpa only [Units.val_zpow_eq_zpow_val] using hz n
  have hz1 : ‖(z : ℂ)‖ ≤ 1 :=
    norm_le_one_of_forall_pow_norm_sub_one_lt _ fun n => by
      simpa only [zpow_natCast] using hpow n
  have hz2 : ‖((z : ℂ))⁻¹‖ ≤ 1 :=
    norm_le_one_of_forall_pow_norm_sub_one_lt _ fun n => by
      have h := hpow (-(n : ℤ))
      rwa [zpow_neg, zpow_natCast, ← inv_pow] at h
  have hzpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hnorm : ‖(z : ℂ)‖ = 1 := by
    rw [norm_inv, inv_le_one₀ hzpos] at hz2
    exact le_antisymm hz1 hz2
  have hcos : ∀ n : ℕ, 0 < Real.cos (n * Complex.arg (z : ℂ)) := by
    intro n
    have h1 := hpow n
    rw [zpow_natCast] at h1
    have hre : ((z : ℂ) ^ n).re = Real.cos (n * Complex.arg (z : ℂ)) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (z : ℂ)]
      rw [hnorm, Complex.ofReal_one, one_mul, ← Complex.exp_nat_mul, ← mul_assoc]
      have hc : ((n : ℂ) * ((Complex.arg (z : ℂ) : ℝ) : ℂ))
          = (((n : ℝ) * Complex.arg (z : ℂ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hc, Complex.exp_ofReal_mul_I_re]
    have h2 : |((z : ℂ) ^ n - 1).re| ≤ ‖(z : ℂ) ^ n - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re, hre] at h2
    have h3 := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
    linarith
  have harg : Complex.arg (z : ℂ) = 0 :=
    eq_zero_of_abs_le_pi_of_forall_cos_pos _ (Complex.abs_arg_le_pi _) hcos
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hnorm, harg] at h
  simpa using h.symm

end LanglandsTunnell.Converse

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.stdRootNumberAt Converse.sPartDual_eq_single TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero TateLocal.psiLocal_ne_one"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel stdRootNumberAt higherUnitsAt mem_higherUnitsAt_iff one_mem_higherUnitsAt HasConductorExponentAt hasConductorExponentAt_zero_iff conductorExponentAt conductorExponentAt_eq_of_hasConductorExponentAt stdRootNumberAt_mul_of_hasConductorExponentAt_zero psiLocal_ne_one"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

private theorem c3id_exists_hasConductorExponentAt_of_continuous (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ c : ℕ, HasConductorExponentAt K v χ c := by
  classical
  suffices hex : ∃ n : ℕ, ∀ u ∈ higherUnitsAt K v n, χ u = 1 by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun m hm => ?_⟩
    by_contra hcon
    exact Nat.find_min hex hm fun u hu => by_contra fun hne => hcon ⟨u, hu, hne⟩

  have hU : {x : ℂˣ | ‖(x : ℂ) - 1‖ < 1} ∈ nhds (1 : ℂˣ) := by
    have hopen : IsOpen {x : ℂˣ | ‖(x : ℂ) - 1‖ < 1} :=
      isOpen_lt (Units.continuous_val.sub continuous_const).norm continuous_const
    refine hopen.mem_nhds ?_
    simp
  have hN : (fun u : (v.adicCompletion K)ˣ => χ u) ⁻¹' {x : ℂˣ | ‖(x : ℂ) - 1‖ < 1}
      ∈ nhds (1 : (v.adicCompletion K)ˣ) :=
    hχ.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)

  rw [Units.isInducing_embedProduct.nhds_eq_comap] at hN
  obtain ⟨W, hW, hWsub⟩ := Filter.mem_comap.mp hN
  rw [map_one, ← Prod.mk_one_one] at hW
  obtain ⟨W₁, hW₁, W₂, hW₂, hW₁₂⟩ := mem_nhds_prod_iff.mp hW
  have hW₂' : MulOpposite.op ⁻¹' W₂ ∈ nhds (1 : v.adicCompletion K) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rw [MulOpposite.op_one]; exact hW₂)
  have hV : W₁ ∩ MulOpposite.op ⁻¹' W₂ ∈ nhds (1 : v.adicCompletion K) := Filter.inter_mem hW₁ hW₂'
  have hkey : ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ →
      ‖((χ u : ℂˣ) : ℂ) - 1‖ < 1 := by
    intro u hu hu'
    have hmem : Units.embedProduct (v.adicCompletion K) u ∈ W₁ ×ˢ W₂ :=
      Set.mk_mem_prod hu.1 hu'.2
    exact hWsub (Set.mem_preimage.mpr (hW₁₂ hmem))

  obtain ⟨n, hn0, hn⟩ : ∃ n : ℕ, 0 < n ∧ ∀ y : v.adicCompletion K,
      Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ)) → y ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ := by
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hV
    have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) :=
      (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
    refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1,
      Nat.succ_pos _, fun y hy => ?_⟩
    refine hγ ?_
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    calc Valued.v (y - 1) ≤ _ := hy
      _ < WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) :=
          WithZero.exp_lt_exp.mpr (by omega)
      _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := WithZero.exp_log hγ0
  have hn0' : n ≠ 0 := hn0.ne'

  let H : Subgroup (v.adicCompletion K)ˣ :=
    { carrier := higherUnitsAt K v n
      one_mem' := one_mem_higherUnitsAt K v n
      mul_mem' := by
        intro a b ha hb
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨hb1, hb2⟩ := hb
        have ha2' := ha2.resolve_left hn0'
        have hb2' := hb2.resolve_left hn0'
        refine ⟨?_, Or.inr ?_⟩
        · rw [Units.val_mul, map_mul, ha1, hb1, one_mul]
        · have heq : ((a * b : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1
              = (a : v.adicCompletion K) * ((b : v.adicCompletion K) - 1)
                + ((a : v.adicCompletion K) - 1) := by
            rw [Units.val_mul]
            ring
          rw [heq]
          refine Valued.v.map_add_le ?_ ha2'
          rw [map_mul, ha1, one_mul]
          exact hb2'
      inv_mem' := by
        intro a ha
        obtain ⟨ha1, ha2⟩ := ha
        have ha2' := ha2.resolve_left hn0'
        have hinv : Valued.v ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀, ha1, inv_one]
        refine ⟨hinv, Or.inr ?_⟩
        have heq : ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1
            = ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)
              * (1 - (a : v.adicCompletion K)) := by
          rw [mul_sub, mul_one, Units.inv_mul]
        rw [heq, map_mul, hinv, one_mul, Valuation.map_sub_swap]
        exact ha2' }
  have hball : ∀ w : (v.adicCompletion K)ˣ, w ∈ H →
      (w : v.adicCompletion K) ∈ W₁ ∩ MulOpposite.op ⁻¹' W₂ := by
    intro w hw
    have hw' : w ∈ higherUnitsAt K v n := hw
    exact hn _ (((mem_higherUnitsAt_iff K v).mp hw').2.resolve_left hn0')

  refine ⟨n, fun u hu => ?_⟩
  have huH : u ∈ H := hu
  refine LanglandsTunnell.Converse.c3id_units_eq_one_of_forall_zpow_norm_sub_one_lt (χ u) fun m => ?_
  rw [← map_zpow]
  exact hkey _ (hball _ (H.zpow_mem huH m)) (hball _ (H.inv_mem (H.zpow_mem huH m)))

end LanglandsTunnell.TateLocal

p2m_open "NumberField P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.NumberField NumberField.AdelicLevel IsDedekindDomain Topology Filter"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place AdeleRing TateGlobal.localChar"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "localChar"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

omit [NumberField F] in
private theorem r06_cofinite_le_principal_compl_singleton :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
  Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite

open scoped Classical in
private def r06_finSinglePrincipal (c : v.adicCompletion F) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) :=
  ⟨Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c,
    Filter.eventually_principal.mpr fun w hw => by
      have hwv : w ≠ v := by simpa using hw
      show Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w ∈ _
      rw [Function.update_of_ne hwv]
      exact one_mem _⟩

open scoped Classical in
private theorem r06_continuous_finSinglePrincipal : Continuous (r06_finSinglePrincipal (F := F) v) := by
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
  show Continuous fun c : v.adicCompletion F =>
    Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w
  by_cases hw : w = v
  · subst hw
    simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hw]
    exact continuous_const

open scoped Classical in
private theorem r06_localUnit_val_eq (t : (v.adicCompletion F)ˣ) :
    ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
      = RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (r06_cofinite_le_principal_compl_singleton v)
          (r06_finSinglePrincipal v (t : v.adicCompletion F)) :=
  RestrictedProduct.ext (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) fun _ => rfl

private theorem r06_continuous_localUnit_val :
    Continuous fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
  have h : (fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
      = (RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (r06_cofinite_le_principal_compl_singleton v)) ∘ (r06_finSinglePrincipal v) ∘ Units.val :=
    funext fun t => r06_localUnit_val_eq v t
  rw [h]
  exact (RestrictedProduct.continuous_inclusion _).comp
    ((r06_continuous_finSinglePrincipal v).comp Units.continuous_val)

private theorem r06_continuous_emb :
    Continuous ⇑((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (r06_continuous_localUnit_val v)
  · have h : (fun t : (v.adicCompletion F)ˣ =>
          ((((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v) t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
            : AdeleRing (𝓞 F) F))
        = (fun t : (v.adicCompletion F)ˣ =>
            (((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v) t : (AdeleRing (𝓞 F) F)ˣ)
              : AdeleRing (𝓞 F) F)) ∘ (fun t => t⁻¹) := by
      funext t
      simp only [Function.comp_apply, map_inv]
    rw [h]
    refine Continuous.comp ?_ continuous_inv
    show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (r06_continuous_localUnit_val v)

end NumberField.TateGlobal

end

namespace NumberField p2m_export "NumberField" "InfiniteAdeleRing place AdeleRing TateGlobal.localChar" namespace TateGlobal p2m_export "NumberField.TateGlobal" "localChar" end NumberField.TateGlobal
p2m_open_scoped "NumberField NumberField.TateGlobal" in
private theorem NumberField.TateGlobal.c3id_continuous_localChar
    {K : Type} [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : Continuous ⇑χ) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous ⇑(localChar χ v) := by
  show Continuous (⇑χ ∘ ⇑((Units.map (finIncl (𝓞 K) K)).comp (localUnit (𝓞 K) K v)))
  exact hχ.comp (r06_continuous_emb v)

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp TateLocal.stdRootNumberAt Converse.sPartDual_eq_single TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero TateLocal.psiLocal_ne_one"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "pinnedExp IsAdmissibleTwist sPartDual sPartDual_eq_single"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.LanglandsTunnell.TateLocal NumberField.TateGlobal P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.NumberField.TateGlobal NumberField.AdelicLevel NumberField.StandardAddChar AutomorphicForm"

private theorem c3id_hasCond_transfer (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {f g : (v.adicCompletion K)ˣ →* ℂˣ}
    (hfg : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → f u = g u) {c : ℕ}
    (h : HasConductorExponentAt K v f c) : HasConductorExponentAt K v g c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [← hfg u ((mem_higherUnitsAt_iff K v).mp hu).1]
    exact h.1 u hu
  · obtain ⟨u, hu, hne⟩ := h.2 m hm
    exact ⟨u, hu, by rwa [← hfg u ((mem_higherUnitsAt_iff K v).mp hu).1]⟩

private theorem c3id_hasCond_inv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {f : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ} (h : HasConductorExponentAt K v f c) :
    HasConductorExponentAt K v f⁻¹ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, h.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := h.2 m hm
    exact ⟨u, hu, by rwa [MonoidHom.inv_apply, Ne, inv_eq_one]⟩

private theorem c3id_monomial_alg (u u₀ : ℂˣ) (Q E₁ E₂ : ℂ) (A B : ℤ) :
    ((u * u₀⁻¹ : ℂˣ) : ℂ) ^ B * E₁ * (((u * u₀⁻¹ : ℂˣ) : ℂ) ^ A * E₂) * Q ^ (-(B + A)) =
      E₁ * E₂ * ((u₀⁻¹ : ℂˣ) : ℂ) ^ (B + A) * ((((u⁻¹ : ℂˣ) : ℂ)) * Q) ^ (-(B + A)) := by
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [mul_zpow, mul_zpow, mul_zpow, inv_zpow' (u : ℂ), neg_neg, zpow_add₀ u.ne_zero B A,
    zpow_add₀ (inv_ne_zero u₀.ne_zero) B A]
  ring

private theorem c3id_perPlace (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ χ₀ ψ e : (v.adicCompletion K)ˣ →* ℂˣ) (hχ₀c : Continuous ⇑χ₀) (hψc : Continuous ⇑ψ)
    (hcanc : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ u * e u = 1)
    (hcanc₀ : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ₀ u * e u = 1)
    (hχu : ‖((χ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1)
    (hχ₀u : ‖((χ₀ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1)
    (hψu : ‖((ψ (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1) :
    conductorExponentAt K v χ = conductorExponentAt K v e ∧
    conductorExponentAt K v χ = conductorExponentAt K v χ₀ ∧
    conductorExponentAt K v (ψ * χ) = conductorExponentAt K v (ψ * χ₀) ∧
    stdRootNumberAt K v χ =
      (((χ * χ₀⁻¹) (uniformizerUnit K v) : ℂˣ) : ℂ) ^
          ((conductorExponentAt K v χ₀ : ℤ) + addCharLevel (psiLocal K v)) * stdRootNumberAt K v χ₀ ∧
    stdRootNumberAt K v (ψ * χ) =
      (((χ * χ₀⁻¹) (uniformizerUnit K v) : ℂˣ) : ℂ) ^
          ((conductorExponentAt K v (ψ * χ₀) : ℤ) + addCharLevel (psiLocal K v)) *
        stdRootNumberAt K v (ψ * χ₀) := by

  have hagree : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ₀ u = χ u :=
    fun u hu => (eq_inv_of_mul_eq_one_left (hcanc₀ u hu)).trans
      (eq_inv_of_mul_eq_one_left (hcanc u hu)).symm

  have hν0 : HasConductorExponentAt K v (χ * χ₀⁻¹) 0 :=
    (hasConductorExponentAt_zero_iff K v).mpr fun u hu => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ← hagree u hu, mul_inv_cancel]

  have hdec₁ : χ = χ₀ * (χ * χ₀⁻¹) := by
    ext x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (χ₀ x), inv_mul_cancel_right]
  have hdec₂ : ψ * χ = (ψ * χ₀) * (χ * χ₀⁻¹) := by
    ext x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_assoc, mul_comm (χ₀ x), inv_mul_cancel_right]

  obtain ⟨a₀, ha₀⟩ := LanglandsTunnell.TateLocal.c3id_exists_hasConductorExponentAt_of_continuous K v χ₀ hχ₀c
  have hψχ₀c : Continuous ⇑(ψ * χ₀) := (hψc.mul hχ₀c).congr fun x => (MonoidHom.mul_apply ψ χ₀ x).symm
  obtain ⟨b₀, hb₀⟩ :=
    LanglandsTunnell.TateLocal.c3id_exists_hasConductorExponentAt_of_continuous K v (ψ * χ₀) hψχ₀c

  have haχ : HasConductorExponentAt K v χ a₀ := c3id_hasCond_transfer K v hagree ha₀
  have haeinv : HasConductorExponentAt K v e⁻¹ a₀ :=
    c3id_hasCond_transfer K v (fun u hu => by
      rw [MonoidHom.inv_apply]; exact eq_inv_of_mul_eq_one_left (hcanc₀ u hu)) ha₀
  have hae : HasConductorExponentAt K v e a₀ := by exact c3id_hasCond_inv K v haeinv
  have hbψχ : HasConductorExponentAt K v (ψ * χ) b₀ :=
    c3id_hasCond_transfer K v (fun u hu => by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, hagree u hu]) hb₀
  have eχ := conductorExponentAt_eq_of_hasConductorExponentAt K v haχ
  have eχ₀ := conductorExponentAt_eq_of_hasConductorExponentAt K v ha₀
  have ee := conductorExponentAt_eq_of_hasConductorExponentAt K v hae
  have eψχ := conductorExponentAt_eq_of_hasConductorExponentAt K v hbψχ
  have eψχ₀ := conductorExponentAt_eq_of_hasConductorExponentAt K v hb₀
  refine ⟨eχ.trans ee.symm, eχ.trans eχ₀.symm, eψχ.trans eψχ₀.symm, ?_, ?_⟩
  · have huν : ‖(((χ * χ₀⁻¹) (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
        norm_inv, hχu, hχ₀u, inv_one, mul_one]
    have h1 := LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v χ₀
      (χ * χ₀⁻¹) a₀ ha₀ hν0 hχ₀u huν (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)
    rw [← hdec₁] at h1
    rw [eχ₀]
    exact h1
  · have huν : ‖(((χ * χ₀⁻¹) (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
        norm_inv, hχu, hχ₀u, inv_one, mul_one]
    have hu : ‖(((ψ * χ₀) (uniformizerUnit K v) : ℂˣ) : ℂ)‖ = 1 := by
      rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hψu, hχ₀u, mul_one]
    have h2 := LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v (ψ * χ₀)
      (χ * χ₀⁻¹) b₀ hb₀ hν0 hu huν (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)
    rw [← hdec₂] at h2
    rw [eψχ₀]
    exact h2

end LanglandsTunnell.Converse

p2m_open "NumberField P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.NumberField NumberField.AdelicLevel IsDedekindDomain"
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.LanglandsTunnell.Converse NumberField.TateGlobal P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.NumberField.TateGlobal LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar AutomorphicForm

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.LanglandsTunnell _root_.LanglandsTunnell.Converse _root_.P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units.LanglandsTunnell.Converse in

theorem solution
    (K : Type) [Field K] [NumberField K] (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ (Ad : (↥SK → ℤ) → ℂ) (n₀ : ↥SK → ℤ), (∀ n, n ≠ n₀ → Ad n = 0) ∧
      ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
        (∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
          localChar μ v u * epsS v u = 1) →
        (∀ v ∈ SK, conductorExponentAt K v (localChar μ v) = conductorExponentAt K v (epsS v)) ∧
        (fun t : ℂ => ∏ w : ↥SK,
    LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
      LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
      (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
        (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1))) =
          sPartDual K SK Ad μ := by
  classical
  have hω' : IsIdeleClassChar (𝓞 K) K ω ∧ Continuous ⇑ω ∧ IsUnitaryChar (𝓞 K) K ω := hω
  obtain ⟨-, hωc, hωun⟩ := hω'
  have hωun' : ∀ x, ‖((ω x : ℂˣ) : ℂ)‖ = 1 := hωun
  by_cases hclass : ∃ μ₀ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ₀ ∧
      ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        localChar μ₀ v u * epsS v u = 1
  swap
  ·
    refine ⟨fun _ => 0, fun _ => 0, fun _ _ => rfl, fun μ hμ hcanc => ?_⟩
    exact absurd ⟨μ, hμ, hcanc⟩ hclass
  obtain ⟨μ₀, hμ₀, hcanc₀⟩ := hclass
  have hμ₀' : IsIdeleClassChar (𝓞 K) K μ₀ ∧ Continuous ⇑μ₀ ∧ IsUnitaryChar (𝓞 K) K μ₀ := hμ₀
  obtain ⟨-, hμ₀c, hμ₀un⟩ := hμ₀'
  have hμ₀un' : ∀ x, ‖((μ₀ x : ℂˣ) : ℂ)‖ = 1 := hμ₀un

  let M : ↥SK → ℤ := fun w =>
    ((conductorExponentAt K w.1 (localChar ω w.1 * localChar μ₀ w.1) : ℤ) + addCharLevel (psiLocal K w.1)) +
      ((conductorExponentAt K w.1 (localChar μ₀ w.1) : ℤ) + addCharLevel (psiLocal K w.1))
  let n₀ : ↥SK → ℤ := fun w => -M w
  let C : ℂ := ∏ w : ↥SK,
    stdRootNumberAt K w.1 (localChar ω w.1 * localChar μ₀ w.1) * stdRootNumberAt K w.1 (localChar μ₀ w.1) *
      (((μ₀ (uniformizerIdele K w.1))⁻¹ : ℂˣ) : ℂ) ^ M w
  refine ⟨fun n => if n = n₀ then C else 0, n₀, fun n hn => if_neg hn, ?_⟩
  intro μ hμ hcanc
  have hμ' : IsIdeleClassChar (𝓞 K) K μ ∧ Continuous ⇑μ ∧ IsUnitaryChar (𝓞 K) K μ := hμ
  obtain ⟨-, -, hμun⟩ := hμ'
  have hμun' : ∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1 := hμun
  have L : ∀ w : ↥SK, _ := fun w : ↥SK =>
    c3id_perPlace K w.1 (localChar μ w.1) (localChar μ₀ w.1) (localChar ω w.1) (epsS w.1)
      (NumberField.TateGlobal.c3id_continuous_localChar μ₀ hμ₀c w.1)
      (NumberField.TateGlobal.c3id_continuous_localChar ω hωc w.1)
      (hcanc w.1 w.2) (hcanc₀ w.1 w.2) (hμun' (uniformizerIdele K w.1)) (hμ₀un' (uniformizerIdele K w.1))
      (hωun' (uniformizerIdele K w.1))
  refine ⟨fun v hv => (L ⟨v, hv⟩).1, ?_⟩
  funext t
  rw [LanglandsTunnell.Converse.sPartDual_eq_single K SK (fun n => if n = n₀ then C else 0) μ t n₀
    (fun n hn => if_neg hn)]
  simp only [if_true]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hωμ : localChar (ω * μ) w.1 = localChar ω w.1 * localChar μ w.1 := MonoidHom.ext fun _ => rfl
  have hpeμ : LanglandsTunnell.Converse.pinnedExp K μ w.1 =
      (conductorExponentAt K w.1 (localChar μ w.1) : ℤ) + addCharLevel (psiLocal K w.1) := rfl
  have hpeωμ : LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 =
      (conductorExponentAt K w.1 (localChar (ω * μ) w.1) : ℤ) + addCharLevel (psiLocal K w.1) := rfl
  have hν : (((localChar μ w.1 * (localChar μ₀ w.1)⁻¹) (uniformizerUnit K w.1) : ℂˣ) : ℂ) =
      ((μ (uniformizerIdele K w.1) * (μ₀ (uniformizerIdele K w.1))⁻¹ : ℂˣ) : ℂ) := rfl
  rw [hpeμ, hpeωμ, hωμ, (L w).2.1, (L w).2.2.1, (L w).2.2.2.1, (L w).2.2.2.2, hν]
  exact c3id_monomial_alg (μ (uniformizerIdele K w.1)) (μ₀ (uniformizerIdele K w.1)) _ _ _ _ _

end S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_sPartDual_eq_of_forall_cancel_units (solution)
