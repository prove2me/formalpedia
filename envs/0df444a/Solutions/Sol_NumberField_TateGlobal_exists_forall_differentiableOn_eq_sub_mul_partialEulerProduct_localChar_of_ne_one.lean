-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/37d3a945-1142-5997-9b53-fc92eab481d9

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm Filter Topology
open scoped Topology

noncomputable section

namespace HeckeContProof

variable (F : Type) [Field F] [NumberField F]

theorem localChar_eq_of_isUnramifiedCharAt {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : IsUnramifiedCharAt χ v) (ϖ₁ ϖ₂ : (v.adicCompletion F)ˣ)
    (h₁ : Valued.v (ϖ₁ : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (h₂ : Valued.v (ϖ₂ : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    localChar χ v ϖ₁ = localChar χ v ϖ₂ := by
  have hu : Valued.v (((ϖ₁⁻¹ * ϖ₂ : (v.adicCompletion F)ˣ)) : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, h₁, h₂, inv_mul_cancel₀ WithZero.exp_ne_zero]
  have hu' : Valued.v ((((ϖ₁⁻¹ * ϖ₂)⁻¹ : (v.adicCompletion F)ˣ)) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have h1 : localChar χ v (ϖ₁⁻¹ * ϖ₂) = 1 :=
    hv _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le)
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu'.le)
  calc localChar χ v ϖ₁ = localChar χ v ϖ₁ * localChar χ v (ϖ₁⁻¹ * ϖ₂) := by rw [h1, mul_one]
    _ = localChar χ v ϖ₂ := by rw [← map_mul, mul_inv_cancel_left]

theorem localChar_eq_apply_uniformizerIdele {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : IsUnramifiedCharAt χ v) (ϖv : (v.adicCompletion F)ˣ)
    (hϖv : Valued.v (ϖv : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    localChar χ v ϖv = χ (uniformizerIdele F v) :=
  localChar_eq_of_isUnramifiedCharAt F hv ϖv (uniformizerUnit F v) hϖv (valued_uniformizerUnit F v)

theorem norm_localChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) : ‖((localChar χ v u : ℂˣ) : ℂ)‖ = 1 :=
  hχu _

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  have h2 : Ideal.absNorm v.asIdeal ≠ 1 := fun h1' => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h1')
  omega

theorem norm_absNorm_cpow_neg (v : HeightOneSpectrum (𝓞 F)) (w : ℂ) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-w.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by have := two_le_absNorm F v; omega), Complex.neg_re]

theorem norm_absNorm_cpow_neg_lt_one (v : HeightOneSpectrum (𝓞 F)) {w : ℂ} (hw : 0 < w.re) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ < 1 := by
  rw [norm_absNorm_cpow_neg]
  have h2 : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm F v
  exact Real.rpow_lt_one_of_one_lt_of_neg h2 (by linarith)

theorem one_sub_mul_cpow_ne_zero (v : HeightOneSpectrum (𝓞 F)) {z : ℂ} (hz : ‖z‖ ≤ 1) {w : ℂ} (hw : 0 < w.re) :
    1 - z * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w) ≠ 0 := by
  intro h
  have h1 : z * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖z * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ < 1 := by
    rw [norm_mul]
    calc ‖z‖ * ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖
        ≤ 1 * ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact norm_absNorm_cpow_neg_lt_one F v hw
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

theorem differentiableOn_inv_one_sub_mul_cpow (v : HeightOneSpectrum (𝓞 F)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    DifferentiableOn ℂ (fun w : ℂ => (1 - z * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹) {w : ℂ | 0 < w.re} := by
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have := two_le_absNorm F v
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have hd : Differentiable ℂ (fun w : ℂ => 1 - z * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) :=
    (differentiable_const _).sub ((differentiable_const z).mul (differentiable_id.neg.const_cpow (Or.inl hN)))
  exact hd.differentiableOn.inv fun w hw => one_sub_mul_cpow_ne_zero F v hz hw

theorem hasProd_inv₀ {ι : Type*} {f : ι → ℂ} {a : ℂ} (hf : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  have h : (fun s : Finset ι => ∏ b ∈ s, (f b)⁻¹) = fun s => (∏ b ∈ s, f b)⁻¹ := by
    funext s
    exact Finset.prod_inv_distrib (f := f) (s := s)
  unfold HasProd at hf ⊢
  rw [h]
  exact hf.inv₀ ha

theorem tprod_mul_of_finite_mulSupport {ι : Type*} {b c : ι → ℂ} (hb : Multipliable b)
    (hc : (Function.mulSupport c).Finite) :
    ∏' i, b i * c i = (∏' i, b i) * ∏ᶠ i, c i := by
  rw [Multipliable.tprod_mul hb (multipliable_of_hasFiniteMulSupport hc), tprod_eq_finprod hc]

theorem inv_tprod_eq_tprod_inv (S : Finset (HeightOneSpectrum (𝓞 F)))
    (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) (w : ℂ) (hw : 1 < w.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
      = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ := by
  obtain ⟨hE1, -, hE3⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S z hz
  obtain ⟨a, ha⟩ := hE1 w hw
  have ha0 : a ≠ 0 := by rw [← ha.tprod_eq]; exact hE3 w hw
  have hinv := hasProd_inv₀ ha ha0
  simp only [inv_inv] at hinv
  rw [hinv.tprod_eq, inv_inv, ha.tprod_eq]

theorem normPowChar_zero_eq_one : normPowChar F 0 = 1 := by
  ext x
  rw [coe_normPowChar_apply, MonoidHom.one_apply, Units.val_one, Complex.ofReal_zero, mul_zero, Complex.cpow_zero]

theorem localChar_normPowChar_uniformizer (t : ℝ) (v : HeightOneSpectrum (𝓞 F)) (ϖv : (v.adicCompletion F)ˣ)
    (hϖv : Valued.v (ϖv : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    ((localChar (normPowChar F t) v ϖv : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) := by
  classical
  have h := NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg F t v
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have := two_le_absNorm F v
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have hun : IsUnramifiedCharAt (normPowChar F t) v := by
    by_contra hn
    rw [if_neg hn] at h
    exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hN)) h.symm
  rw [if_pos hun] at h
  rw [localChar_eq_apply_uniformizerIdele F hun ϖv hϖv]
  exact h

theorem differentiableOn_update_of_tendsto {f : ℂ → ℂ} {U : Set ℂ} {c κ : ℂ}
    (hU : IsOpen U) (hc : c ∈ U) (hf : DifferentiableOn ℂ f (U \ {c}))
    (ht : Tendsto f (𝓝[≠] c) (𝓝 κ)) :
    DifferentiableOn ℂ (Function.update f c κ) U := by
  classical
  intro z hz
  by_cases hzc : z = c
  · subst hzc
    have hcont : ContinuousAt (Function.update f z κ) z := continuousAt_update_same.mpr ht
    have hdiff : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ (Function.update f z κ) w := by
      have hmem : U \ {z} ∈ 𝓝[≠] z := by
        exact diff_mem_nhdsWithin_compl (hU.mem_nhds hz) {z}
      filter_upwards [hmem] with w hw
      have hwz : w ≠ z := fun h => hw.2 h
      have hopen : IsOpen (U \ {z}) := hU.sdiff isClosed_singleton
      have h1 : DifferentiableAt ℂ f w := (hf w hw).differentiableAt (hopen.mem_nhds hw)
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hwz] with u hu
      exact Function.update_of_ne hu _ _
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcont).differentiableAt.differentiableWithinAt
  · have hz' : z ∈ U \ {c} := ⟨hz, hzc⟩
    have hopen : IsOpen (U \ {c}) := hU.sdiff isClosed_singleton
    have h1 : DifferentiableAt ℂ f z := (hf z hz').differentiableAt (hopen.mem_nhds hz')
    refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [isOpen_ne.mem_nhds hzc] with u hu
    exact Function.update_of_ne hu _ _

theorem caseB (t : ℝ) (ht : t ≠ 0) :
    ∃ s₁ : ℂ, s₁.re = 1 ∧ s₁ ≠ 1 ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
        (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
        ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q {w : ℂ | 0 < w.re} ∧
          ∀ w : ℂ, 1 < w.re →
            Q w = (w - s₁) * (∏' v : {v // v ∉ S},
              (1 - ((localChar (normPowChar F t) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
  classical
  set s₁ : ℂ := 1 - Complex.I * t with hs₁
  refine ⟨s₁, by simp [hs₁], ?_, fun S ϖ hϖ => ?_⟩
  · intro h
    have := congrArg Complex.im h
    simp [hs₁] at this
    exact ht this
  obtain ⟨Z, κ, hκ, -, hZa, hZeq, hZt⟩ :=
    NumberField.exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul F S

  set f : ℂ → ℂ := fun w => (w - s₁) * Z (w + Complex.I * t) with hf
  have hshift : ∀ w : ℂ, w + Complex.I * t - 1 = w - s₁ := fun w => by rw [hs₁]; ring
  have hfd : DifferentiableOn ℂ f (Set.univ \ {s₁}) := by
    intro w hw
    have hw1 : w + Complex.I * t ≠ 1 := by
      intro h
      apply hw.2
      show w = s₁
      rw [hs₁, ← h]; ring
    have hZd : DifferentiableAt ℂ Z (w + Complex.I * t) := (hZa _ hw1).differentiableAt
    exact (((differentiableAt_id.sub_const _).mul
      (hZd.comp w (differentiableAt_id.add_const _))).differentiableWithinAt)
  have hft : Tendsto f (𝓝[≠] s₁) (𝓝 κ) := by
    have hτ : Tendsto (fun w : ℂ => w + Complex.I * t) (𝓝[≠] s₁) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : s₁ + Complex.I * t = 1 := by rw [hs₁]; ring
        rw [← this]
        exact ((continuous_id.add continuous_const).tendsto s₁).mono_left nhdsWithin_le_nhds
      · refine eventually_nhdsWithin_of_forall fun w hw => ?_
        intro h
        apply hw
        show w = s₁
        rw [hs₁, ← (h : w + Complex.I * t = 1)]; ring
    have h2 := hZt.comp hτ
    refine h2.congr fun w => ?_
    show (w + Complex.I * t - 1) * Z (w + Complex.I * t) = f w
    rw [hf, hshift]
  refine ⟨Function.update f s₁ κ, ?_, fun w hw => ?_⟩
  · exact (differentiableOn_update_of_tendsto isOpen_univ (Set.mem_univ _) hfd hft).mono (Set.subset_univ _)
  · have hws : w ≠ s₁ := by
      intro h
      have := congrArg Complex.re h
      simp [hs₁] at this
      linarith
    rw [Function.update_of_ne hws]
    simp only [hf]
    congr 1

    have hw' : 1 < (w + Complex.I * t).re := by simpa using hw
    obtain ⟨hmul, hone⟩ := hZeq (w + Complex.I * t) hw'
    have hT0 : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(w + Complex.I * t)))) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hone
      exact zero_ne_one hone
    have hZval : Z (w + Complex.I * t) = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(w + Complex.I * t))))⁻¹ :=
      eq_inv_of_mul_eq_one_left hone
    rw [hZval]
    congr 1
    refine tprod_congr fun v => ?_
    have hN : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ≠ 0 := by
      have := two_le_absNorm F v.1
      exact_mod_cast (show Ideal.absNorm v.1.asIdeal ≠ 0 by omega)
    rw [show -(w + Complex.I * t) = -(Complex.I * t) + -w by ring, Complex.cpow_add _ _ hN,
      localChar_normPowChar_uniformizer F t v.1 (ϖ v.1) (hϖ v.1)]

theorem caseA (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) (hA : ∃ x ∈ normOneIdeles F, χ x ≠ 1) :
    ∃ s₁ : ℂ, s₁.re = 1 ∧ s₁ ≠ 1 ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
        (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
        ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q {w : ℂ | 0 < w.re} ∧
          ∀ w : ℂ, 1 < w.re →
            Q w = (w - s₁) * (∏' v : {v // v ∉ S},
              (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
  classical
  refine ⟨1 + Complex.I, by simp, by intro h; simpa using congrArg Complex.im h, fun S ϖ hϖ => ?_⟩
  obtain ⟨L, hLd, hLeq⟩ :=
    NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one F χ hχF
      hχc hχu hA S
  obtain ⟨R₀, hR₀⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous F χ hχc

  set z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ := fun v => ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) with hz
  set zi : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ := fun v =>
    if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0 with hzi
  have hzle : ∀ v, ‖z v‖ ≤ 1 := fun v => (norm_localChar F χ hχu v.1 (ϖ v.1)).le
  have hzile : ∀ v, ‖zi v‖ ≤ 1 := by
    intro v
    simp only [hzi]
    split_ifs
    · exact (hχu _).le
    · simp

  set T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S} := R₀.subtype (fun v => v ∉ S) with hT
  set r : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ → ℂ := fun v w =>
    if IsUnramifiedCharAt χ v.1 then 1 else (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ with hr
  have hrsupp : ∀ w, (Function.mulSupport fun v => r v w) ⊆ (T : Set _) := by
    intro w v hv
    rw [Finset.mem_coe, hT, Finset.mem_subtype]
    by_contra hvR
    apply hv
    show r v w = 1
    simp only [hr, if_pos (hR₀ v.1 hvR)]
  have hrd : ∀ v, DifferentiableOn ℂ (r v) {w : ℂ | 0 < w.re} := by
    intro v
    simp only [hr]
    split_ifs
    · exact differentiableOn_const _
    · exact differentiableOn_inv_one_sub_mul_cpow F v.1 (hzle v)
  refine ⟨fun w => (w - (1 + Complex.I)) * L w * ∏ v ∈ T, r v w, ?_, fun w hw => ?_⟩
  · refine ((differentiableOn_id.sub (differentiableOn_const _)).mul hLd.differentiableOn).mul ?_
    have hfun : (fun w : ℂ => ∏ v ∈ T, r v w) = ∏ v ∈ T, r v := by
      funext w
      rw [Finset.prod_apply]
    rw [hfun]
    exact DifferentiableOn.finsetProd fun v _ => hrd v
  ·
    show (w - (1 + Complex.I)) * L w * ∏ v ∈ T, r v w = _
    rw [mul_assoc]
    congr 1
    have hw0 : 0 < w.re := by linarith
    have hsplit : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹
          = (1 - zi v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ * r v w := by
      intro v
      simp only [hzi, hr]
      by_cases hun : IsUnramifiedCharAt χ v.1
      · rw [if_pos hun, if_pos hun, mul_one]
        simp only [hz]
        rw [localChar_eq_apply_uniformizerIdele F hun (ϖ v.1) (hϖ v.1)]
      · rw [if_neg hun, if_neg hun, zero_mul, sub_zero, inv_one, one_mul]
    have hmul : Multipliable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        (1 - zi v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ :=
      (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S zi hzile).1 w hw
    rw [show (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
        = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹
        from inv_tprod_eq_tprod_inv F S z hzle w hw]
    symm
    calc (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹)
        = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - zi v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ * r v w := tprod_congr hsplit
      _ = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - zi v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹) * ∏ᶠ v, r v w :=
          tprod_mul_of_finite_mulSupport hmul ((T.finite_toSet).subset (hrsupp w))
      _ = L w * ∏ v ∈ T, r v w := by
          rw [hLeq w hw, finprod_eq_prod_of_mulSupport_subset _ (hrsupp w)]

theorem main (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) (hχ1 : χ ≠ 1) :
    ∃ s₁ : ℂ, s₁.re = 1 ∧ s₁ ≠ 1 ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
        (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
        ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q {w : ℂ | 0 < w.re} ∧
          ∀ w : ℂ, 1 < w.re →
            Q w = (w - s₁) * (∏' v : {v // v ∉ S},
              (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
  by_cases hA : ∃ x ∈ normOneIdeles F, χ x ≠ 1
  · exact caseA F χ hχc hχu hχF hA
  · push Not at hA
    obtain ⟨t, rfl⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles F _ hχc hχu hA
    have ht : t ≠ 0 := by
      rintro rfl
      exact hχ1 (normPowChar_zero_eq_one F)
    exact caseB F t ht

end HeckeContProof

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) (hχ1 : χ ≠ 1) :
    ∃ s₁ : ℂ, s₁.re = 1 ∧ s₁ ≠ 1 ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
        (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
        ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q {w : ℂ | 0 < w.re} ∧
          ∀ w : ℂ, 1 < w.re →
            Q w = (w - s₁) * (∏' v : {v // v ∉ S},
              (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ :=
  HeckeContProof.main F χ hχc hχu hχF hχ1

end S_NumberField_TateGlobal_exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one (solution)
