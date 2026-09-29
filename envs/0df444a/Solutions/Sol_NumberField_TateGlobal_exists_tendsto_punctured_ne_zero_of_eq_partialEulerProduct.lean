-- Prove2me | solution 1 for NumberField.TateGlobal.exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a0a194cb-f862-58a8-adcf-7efeaff1f0df

import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
import Theorems.Thm_NumberField_TateGlobal_exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

section

set_option autoImplicit false

p2m_open "Filter Topology NumberField P2MW.S_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct.NumberField.TateGlobal AutomorphicForm IsDedekindDomain Complex"
open NumberField.AdelicLevel (uniformizerUnit valued_uniformizerUnit)

noncomputable section

namespace NumberField
p2m_export "NumberField" "place AdeleRing TateGlobal.ideleNorm multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one TateGlobal.exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normPowChar coe_normPowChar_apply norm_coe_normPowChar_apply normPowChar_eq_one_of_ideleNorm_eq_one ideleNorm ideleNorm_pos localChar IsUnramifiedCharAt ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg continuous_ideleNorm exists_finset_forall_isUnramifiedCharAt_of_continuous not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one"
namespace LineNonvanishing
p2m_open "NumberField.TateGlobal NumberField"

section Generic

variable {ι : Type*}

private theorem hasProd_of_hasProd_inv {x : ι → ℂ} {E : ℂ} (h : HasProd (fun i => (x i)⁻¹) E) (hE : E ≠ 0) :
    HasProd x E⁻¹ := by
  have h' : Tendsto (fun s : Finset ι => ∏ i ∈ s, (x i)⁻¹) _ (𝓝 E) := h
  unfold HasProd
  simpa only [Finset.prod_inv_distrib, inv_inv] using h'.inv₀ hE

private theorem inv_tprod_eq_tprod_inv {x : ι → ℂ} (hm : Multipliable fun i => (x i)⁻¹)
    (hE : (∏' i, (x i)⁻¹) ≠ 0) : (∏' i, x i)⁻¹ = ∏' i, (x i)⁻¹ := by
  rw [(hasProd_of_hasProd_inv hm.hasProd hE).tprod_eq, inv_inv]

private theorem frequently_re_lt_nhdsNE (z : ℂ) : ∃ᶠ w in 𝓝[≠] z, z.re < w.re := by
  have ht : Tendsto (fun ε : ℝ => z + (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun ε : ℝ => z + (ε : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (z + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add continuous_ofReal).tendsto (0 : ℝ)
      rw [ofReal_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left, ofReal_eq_zero]
      exact hε.ne'
  refine ht.frequently (Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  simp [hε]

private theorem tendsto_nhdsNE_of_meromorphicAt_of_frequently_eq {f g : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z)
    (hg : AnalyticAt ℂ g z) (hfg : ∃ᶠ w in 𝓝[≠] z, f w = g w) : Tendsto f (𝓝[≠] z) (𝓝 (g z)) := by
  have hsub : MeromorphicAt (f - g) z := hf.sub hg.meromorphicAt
  have h0 : (f - g) =ᶠ[𝓝[≠] z] 0 :=
    hsub.frequently_zero_iff_eventuallyEq_zero.1 (hfg.mono fun w hw => by simp [hw])
  have hgf : g =ᶠ[𝓝[≠] z] f := h0.mono fun w hw => by
    have hw' : f w - g w = 0 := hw
    exact (sub_eq_zero.1 hw').symm
  exact (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgf

end Generic

variable (K : Type) [Field K] [NumberField K]

private theorem localChar_mul (χ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : localChar (χ * η) v t = localChar χ v t * localChar η v t := rfl

private theorem apply_uniformizerIdele (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    χ (uniformizerIdele K v) = localChar χ v (uniformizerUnit K v) := rfl

private theorem isUnramifiedCharAt_normPowChar (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedCharAt (normPowChar K t) v := by
  by_contra h
  have h75 := ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K t v
  rw [if_neg h] at h75
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  exact hN ((cpow_eq_zero_iff _ _).1 h75.symm).1

private theorem coe_normPowChar_uniformizerIdele (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    ((normPowChar K t (uniformizerIdele K v) : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(I * t)) := by
  have h75 := ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K t v
  rwa [if_pos (isUnramifiedCharAt_normPowChar K t v)] at h75

variable {K}

private theorem localChar_eq_of_isUnramifiedCharAt {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : IsUnramifiedCharAt χ v) (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    localChar χ v ϖ = localChar χ v (uniformizerUnit K v) := by
  set u : (v.adicCompletion K)ˣ := (uniformizerUnit K v)⁻¹ * ϖ with hu
  have hϖ' : ϖ = uniformizerUnit K v * u := by rw [hu, mul_inv_cancel_left]
  have hval : Valued.v (u : v.adicCompletion K) = 1 := by
    rw [hu, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, valued_uniformizerUnit, hϖ]
    exact inv_mul_cancel₀ (by simp)
  have h1 : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  have h2 : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  rw [hϖ', map_mul, hχ u h1 h2, mul_one]

open scoped Classical in

private theorem coe_localChar_eq_ite_of_isUnramifiedCharAt
    {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)} (hχ : IsUnramifiedCharAt χ v)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    ((localChar χ v ϖ : ℂˣ) : ℂ)
      = (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) := by
  rw [if_pos hχ, apply_uniformizerIdele, localChar_eq_of_isUnramifiedCharAt hχ ϖ hϖ]

private theorem coe_localChar_normPowChar (t : ℝ) {v : HeightOneSpectrum (𝓞 K)} (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    ((localChar (normPowChar K t) v ϖ : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(I * t)) := by
  rw [localChar_eq_of_isUnramifiedCharAt (isUnramifiedCharAt_normPowChar K t v) ϖ hϖ, ← apply_uniformizerIdele]
  exact coe_normPowChar_uniformizerIdele K t v

private theorem one_sub_coe_localChar_mul_normPowChar_mul_cpow (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (t : ℝ)
    {v : HeightOneSpectrum (𝓞 K)} (ϖ : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) (s : ℂ) :
    1 - ((localChar (χ * normPowChar K t) v ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)
      = 1 - ((localChar χ v ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * t)) := by
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  rw [localChar_mul, Units.val_mul, coe_localChar_normPowChar t ϖ hϖ, mul_assoc, ← cpow_add _ _ hN, neg_add,
    add_comm]

private theorem tprod_one_sub_localChar_mul_normPowChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (t : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) (s : ℂ) :
    (∏' v : {v // v ∉ S},
        (1 - ((localChar (χ * normPowChar K t) v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
      = ∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + I * t))) :=
  tprod_congr fun v => one_sub_coe_localChar_mul_normPowChar_mul_cpow χ t (ϖ v.1) (hϖ v.1) s

variable (K)

private theorem continuous_normPowChar (t : ℝ) : Continuous (normPowChar K t) := by
  have hb : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((ideleNorm K x : ℝ) : ℂ) :=
    continuous_ofReal.comp (continuous_ideleNorm K)
  have hval : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((normPowChar K t x : ℂˣ) : ℂ) := by
    simp only [coe_normPowChar_apply]
    exact hb.cpow continuous_const fun x => ofReal_mem_slitPlane.2 (ideleNorm_pos x)
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hval.inv₀ fun x => (normPowChar K t x).ne_zero

private theorem isIdeleClassChar_normPowChar_of_forall (t : ℝ)
    (hprod : ∀ u : Kˣ, ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) = 1) :
    IsIdeleClassChar (𝓞 K) K (normPowChar K t) := fun u =>
  normPowChar_eq_one_of_ideleNorm_eq_one t (hprod u)

private theorem isUnitaryChar_normPowChar (t : ℝ) : IsUnitaryChar (𝓞 K) K (normPowChar K t) := fun x =>
  norm_coe_normPowChar_apply t x

variable {K}

namespace IsIdeleClassChar
private theorem _root_.NumberField.TateGlobal.LineNonvanishing.IsIdeleClassChar.mul {χ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : IsIdeleClassChar (𝓞 K) K χ)
    (hη : IsIdeleClassChar (𝓞 K) K η) : IsIdeleClassChar (𝓞 K) K (χ * η) := fun u => by
  rw [MonoidHom.mul_apply, hχ u, hη u, mul_one]

end IsIdeleClassChar
p2m_export "NumberField.TateGlobal.LineNonvanishing" "IsIdeleClassChar.mul"
namespace IsUnitaryChar
private theorem _root_.NumberField.TateGlobal.LineNonvanishing.IsUnitaryChar.mul {χ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 K) K χ)
    (hη : IsUnitaryChar (𝓞 K) K η) : IsUnitaryChar (𝓞 K) K (χ * η) := fun x => by
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ x, hη x, mul_one]

end IsUnitaryChar
p2m_export "NumberField.TateGlobal.LineNonvanishing" "IsUnitaryChar.mul"
private theorem continuous_mul_char {χ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : Continuous χ) (hη : Continuous η) :
    Continuous (χ * η) := by
  show Continuous fun x => χ x * η x
  exact hχ.mul hη

private theorem mul_normPowChar_props {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ) (hχF : IsIdeleClassChar (𝓞 K) K χ) (t : ℝ)
    (hprod : ∀ u : Kˣ, ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) = 1) :
    Continuous (χ * normPowChar K t) ∧ IsUnitaryChar (𝓞 K) K (χ * normPowChar K t)
      ∧ IsIdeleClassChar (𝓞 K) K (χ * normPowChar K t) :=
  ⟨continuous_mul_char hχc (continuous_normPowChar K t), IsUnitaryChar.mul hχu (isUnitaryChar_normPowChar K t),
    IsIdeleClassChar.mul hχF (isIdeleClassChar_normPowChar_of_forall K t hprod)⟩

private theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 K)) : 1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  exact_mod_cast lt_of_le_of_ne (Nat.one_le_iff_ne_zero.2 h0) (Ne.symm h1)

private theorem one_sub_mul_cpow_ne_zero (v : HeightOneSpectrum (𝓞 K)) {z : ℂ} (hz : ‖z‖ ≤ 1) {σ : ℝ} (hσ : 0 < σ) :
    1 - z * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)) ≠ 0 := by
  intro h
  have hlt : ‖z * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))‖ < 1 := by
    rw [norm_mul, ← ofReal_natCast, ← ofReal_neg, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans (one_lt_absNorm v)),
      ofReal_re]
    calc ‖z‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)
        ≤ 1 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hz (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ < 1 := by
          rw [one_mul]
          exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_absNorm v) (neg_neg_of_pos hσ)
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

private theorem continuousAt_inv_eulerFactor (v : HeightOneSpectrum (𝓞 K)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ContinuousAt (fun σ : ℝ => (1 - z * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹) 1 := by
  have hpow : Continuous fun σ : ℝ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)) :=
    continuous_const.cpow continuous_ofReal.neg fun _ => by
      rw [← ofReal_natCast]
      exact ofReal_mem_slitPlane.2 (zero_lt_one.trans (one_lt_absNorm v))
  exact (continuous_const.sub (continuous_const.mul hpow)).continuousAt.inv₀
    (one_sub_mul_cpow_ne_zero v hz zero_lt_one)

open scoped Classical in

private theorem norm_ite_le_one {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hχu : IsUnitaryChar (𝓞 K) K χ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖(if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)‖ ≤ 1 := by
  split_ifs
  · exact (hχu _).le
  · simp

open scoped Classical in

private theorem not_tendsto_inv_tprod_one_sub_localChar_nhds_zero (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 K) K χ) (hχF : IsIdeleClassChar (𝓞 K) K χ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    ¬ Tendsto
        (fun σ : ℝ => (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹)
        (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
  intro H

  set z : {v // v ∉ S} → ℂ := fun v => ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) with hz_def
  set z' : {v // v ∉ S} → ℂ :=
    fun v => if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0 with hz'_def
  have hz1 : ∀ v, ‖z v‖ ≤ 1 := fun v => (hχu _).le
  have hz'1 : ∀ v, ‖z' v‖ ≤ 1 := fun v => norm_ite_le_one hχu v.1

  set f : ℝ → {v // v ∉ S} → ℂ :=
    fun σ v => (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ with hf_def
  set g : ℝ → {v // v ∉ S} → ℂ :=
    fun σ v => (1 - z' v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ with hg_def
  obtain ⟨hmul, -, hne⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K S z hz1

  have hE : ∀ σ : ℝ, 1 < σ →
      (∏' v : {v // v ∉ S},
        (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹
        = ∏' v, f σ v := fun σ hσ => by
    have hre : 1 < ((σ : ℂ)).re := by simpa using hσ
    exact inv_tprod_eq_tprod_inv (hmul _ hre) (hne _ hre)
  have Hf : Tendsto (fun σ => ∏' v, f σ v) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    refine H.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : (1 : ℝ) < σ) using hE σ hσ

  obtain ⟨R, hR⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous K χ hχc
  set s : Finset {v // v ∉ S} := R.subtype (fun v => v ∉ S) with hs_def
  have hagree : ∀ σ : ℝ, ∀ v ∉ s, f σ v = g σ v := fun σ v hv => by
    have hvR : v.1 ∉ R := fun h => hv (Finset.mem_subtype.2 h)
    simp only [hf_def, hg_def, hz_def, hz'_def]
    rw [coe_localChar_eq_ite_of_isUnramifiedCharAt (hR v.1 hvR) (ϖ v.1) (hϖ v.1)]

  have hsplit : ∀ σ : ℝ, 1 < σ →
      (∏' v, g σ v) = (∏' v, f σ v) * ((∏ v ∈ s, g σ v) / ∏ v ∈ s, f σ v) := fun σ hσ => by
    have hre : 1 < ((σ : ℂ)).re := by simpa using hσ
    exact (hmul _ hre).tsum_congr_cofinite₀
      (fun v _ => inv_ne_zero (one_sub_mul_cpow_ne_zero v.1 (hz1 v) (zero_lt_one.trans hσ))) (hagree σ)

  have hcorr : Tendsto (fun σ : ℝ => (∏ v ∈ s, g σ v) / ∏ v ∈ s, f σ v) (𝓝[>] (1 : ℝ))
      (𝓝 ((∏ v ∈ s, g 1 v) / ∏ v ∈ s, f 1 v)) := by
    refine ContinuousAt.tendsto (ContinuousAt.div₀ ?_ ?_ ?_) |>.mono_left nhdsWithin_le_nhds
    · exact tendsto_finsetProd _ fun v _ => continuousAt_inv_eulerFactor v.1 (hz'1 v)
    · exact tendsto_finsetProd _ fun v _ => continuousAt_inv_eulerFactor v.1 (hz1 v)
    · exact Finset.prod_ne_zero_iff.2 fun v _ =>
        inv_ne_zero (one_sub_mul_cpow_ne_zero v.1 (hz1 v) zero_lt_one)
  have Hg : Tendsto (fun σ => ∏' v, g σ v) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have h := Hf.mul hcorr
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : (1 : ℝ) < σ) using (hsplit σ hσ).symm
  exact not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar K χ hχF hχc hχu S Hg

private theorem apply_one_ne_zero_of_analyticAt_of_eq_inv_tprod (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 K) K χ) (hχF : IsIdeleClassChar (𝓞 K) K χ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) (L : ℂ → ℂ)
    (hLE : ∀ s : ℂ, 1 < s.re → L s = (∏' v : {v // v ∉ S},
      (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (hL1 : AnalyticAt ℂ L 1) : L 1 ≠ 0 := by
  intro h0
  refine not_tendsto_inv_tprod_one_sub_localChar_nhds_zero χ hχc hχu hχF S ϖ hϖ ?_
  have hcast : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have h := (continuous_ofReal.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    rwa [ofReal_one] at h
  have hL : Tendsto (fun σ : ℝ => L (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hc := hL1.continuousAt.tendsto
    rw [h0] at hc
    exact hc.comp hcast
  refine hL.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : (1 : ℝ) < σ) using hLE _ (by simpa using hσ)

private theorem exists_tendsto_punctured_ne_zero_of_exists_continuation (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 K) K χ)
    (hχF : IsIdeleClassChar (𝓞 K) K χ) (L : ℂ → ℂ) (hL : MeromorphicOn L Set.univ)
    (hLE : ∀ s : ℂ, 1 < s.re →
      L s = (∏' v : {v // v ∉ S},
        (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (t : ℝ)
    (hprod : ∀ u : Kˣ, ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) = 1)
    (hcont : ∃ L' : ℂ → ℂ, MeromorphicOn L' Set.univ ∧
      (∀ s : ℂ, 1 < s.re →
        L' s = (∏' v : {v // v ∉ S},
          (1 - ((localChar (χ * normPowChar K t) v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ∧
      AnalyticAt ℂ L' 1) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto L (nhdsWithin (1 + t * I) {1 + t * I}ᶜ) (nhds c) := by
  obtain ⟨L', -, hL'E, hL'1⟩ := hcont
  obtain ⟨hψc, hψu, hψF⟩ := mul_normPowChar_props hχc hχu hχF t hprod
  have hne : L' 1 ≠ 0 :=
    apply_one_ne_zero_of_analyticAt_of_eq_inv_tprod (χ * normPowChar K t) hψc hψu hψF S ϖ hϖ L' hL'E hL'1
  have hz : (1 + t * I) - t * I = 1 := add_sub_cancel_right 1 (t * I)
  have hg : AnalyticAt ℂ (fun w : ℂ => L' (w - t * I)) (1 + t * I) := by
    have hf : AnalyticAt ℂ (fun w : ℂ => w - t * I) (1 + t * I) := analyticAt_id.sub analyticAt_const
    exact AnalyticAt.comp_of_eq' hL'1 hf hz
  have hagree : ∃ᶠ w in 𝓝[≠] (1 + t * I), L w = L' (w - t * I) := by
    refine (frequently_re_lt_nhdsNE (1 + t * I)).mono fun w hw => ?_
    have hre : 1 < w.re := by simpa using hw
    have hre' : 1 < (w - t * I).re := by simpa using hre
    rw [hLE w hre, hL'E _ hre', tprod_one_sub_localChar_mul_normPowChar χ t S ϖ hϖ,
      show w - t * I + I * t = w by ring]
  refine ⟨L' 1, hne, ?_⟩
  have hlim := tendsto_nhdsNE_of_meromorphicAt_of_frequently_eq (hL _ (Set.mem_univ (1 + t * I))) hg hagree
  simpa only [hz] using hlim

end NumberField.TateGlobal.LineNonvanishing

end

end

section

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct.NumberField AutomorphicForm IsDedekindDomain"

open _root_.NumberField.TateGlobal _root_.P2MW.S_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct.NumberField.TateGlobal in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ)
    (L : ℂ → ℂ) (hL : MeromorphicOn L Set.univ)
    (hLE : ∀ s : ℂ, 1 < s.re →
      L s = (∏' v : {v // v ∉ S},
        (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (t : ℝ) (ht : χ * normPowChar F t ≠ 1) :
    ∃ c : ℂ, c ≠ 0 ∧
      Filter.Tendsto L (nhdsWithin (1 + t * Complex.I) {1 + t * Complex.I}ᶜ) (nhds c) := by
  have hprod : ∀ u : Fˣ,
      NumberField.TateGlobal.ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u) = 1 := by
    intro u
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
    simpa [NumberField.TateGlobal.ideleNorm] using congrArg (fun x : NNReal => (x : ℝ)) h
  obtain ⟨hψc, hψu, hψF⟩ :=
    NumberField.TateGlobal.LineNonvanishing.mul_normPowChar_props hχc hχu hχF t hprod
  exact NumberField.TateGlobal.LineNonvanishing.exists_tendsto_punctured_ne_zero_of_exists_continuation
    S ϖ hϖ χ hχc hχu hχF L hL hLE t hprod
    (NumberField.TateGlobal.exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one F S ϖ hϖ
      (χ * normPowChar F t) hψc hψu hψF ht)

end

end S_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct (solution)
