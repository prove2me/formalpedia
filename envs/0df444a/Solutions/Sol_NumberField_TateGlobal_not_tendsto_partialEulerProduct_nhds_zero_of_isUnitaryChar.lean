-- Prove2me | solution 1 for NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a2439e30-d091-5548-a629-c7ce14a7401d

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Mathlib
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one
import Theorems.Thm_NumberField_TateGlobal_apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one
import Theorems.Thm_NumberField_tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open Filter Topology

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain
open Filter Topology

noncomputable section

section Plumbing

theorem absNorm_cast_ne_zero {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

theorem absNorm_pos' {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    0 < Ideal.absNorm v.asIdeal :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

theorem bdd_of_germ {E : ℂ → ℂ}
    (h : ∃ U ∈ 𝓝 (1 : ℂ), ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ ∀ s ∈ U, 1 < s.re → L s = E s) :
    ∃ B δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ → ‖E (σ : ℂ)‖ ≤ B := by
  obtain ⟨U, hU, L, hLd, hLE⟩ := h
  have hc : ContinuousAt L 1 := hLd.continuousOn.continuousAt hU
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨δ₂, hδ₂, hcont⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  refine ⟨‖L 1‖ + 1, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun σ hσ1 hσδ => ?_⟩
  have hdist : dist (σ : ℂ) 1 = σ - 1 := by
    rw [Complex.dist_eq, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (sub_pos.mpr hσ1).le]
  have hmem : (σ : ℂ) ∈ U := hball (by rw [Metric.mem_ball, hdist]; linarith [min_le_left δ₁ δ₂])
  have hre : 1 < (σ : ℂ).re := by simpa using hσ1
  rw [← hLE _ hmem hre]
  have h1 : dist (L σ) (L 1) < 1 := hcont (by rw [hdist]; linarith [min_le_right δ₁ δ₂])
  rw [dist_eq_norm] at h1
  calc ‖L σ‖ = ‖L 1 + (L σ - L 1)‖ := by ring_nf
    _ ≤ ‖L 1‖ + ‖L σ - L 1‖ := norm_add_le _ _
    _ ≤ ‖L 1‖ + 1 := by linarith

theorem germ_normPow (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (t : ℝ) (ht : t ≠ 0) :
    ∃ U ∈ 𝓝 (1 : ℂ), ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ ∀ s ∈ U, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  obtain ⟨L, hLd, hLE, -⟩ := NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul K T
  have hUo : IsOpen ({s : ℂ | 1 / 2 < s.re} \ {1 - Complex.I * t}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have h1U : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} \ {1 - Complex.I * t} := by
    refine ⟨by norm_num, fun h => ht ?_⟩
    have := congrArg Complex.im (Set.mem_singleton_iff.mp h)
    simpa using this
  refine ⟨_, hUo.mem_nhds h1U, fun s => L (s + Complex.I * t), ?_, ?_⟩
  · refine hLd.comp (differentiableOn_id.add_const _) fun s hs => ⟨?_, fun h => hs.2 ?_⟩
    · show 1 / 2 < (s + Complex.I * t).re
      simpa using hs.1
    · have h' : s + Complex.I * t = 1 := h
      rw [Set.mem_singleton_iff]
      linear_combination h'
  · intro s hs hs1
    show L (s + Complex.I * t) = _
    rw [hLE (s + Complex.I * t) (by simpa using hs1)]
    refine tprod_congr fun v => ?_
    rw [neg_add, Complex.cpow_add _ _ (absNorm_cast_ne_zero v.1), mul_comm]

theorem zeta_bound (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ C / (σ - 1) := by
  obtain ⟨L, hLd, hLE, κ, hκ, hT⟩ := NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul K T
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast (ne_of_gt hσ)
  have hlim := (hT.comp hmap).norm
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), ‖(((σ : ℂ)) - 1) * L (σ : ℂ)‖ < ‖κ‖ + 1 :=
    hlim.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨‖κ‖ + 1, u - 1, sub_pos.mpr hu, fun σ hσ1 hσu => ?_⟩
  have hb : ‖((σ : ℂ) - 1) * L (σ : ℂ)‖ < ‖κ‖ + 1 := hsub ⟨hσ1, by linarith⟩
  rw [norm_mul, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (sub_pos.mpr hσ1).le] at hb
  rw [← hLE (σ : ℂ) (by simpa using hσ1), le_div_iff₀ (sub_pos.mpr hσ1), mul_comm]
  exact hb.le

end Plumbing

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ¬ Filter.Tendsto
        (fun σ : ℝ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹)
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (0 : ℂ)) := by

  have hζ : ∃ C δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ C / (σ - 1) := by
    exact zeta_bound K T
  by_cases hA : ∀ x ∈ normOneIdeles K, χ x = 1
  ·

    obtain ⟨t, rfl⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles K χ _hχc _hχu hA
    simp_rw [NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K t]
    by_cases ht : t = 0
    ·
      subst ht
      intro h0
      have h0' := h0.norm
      simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.cpow_zero, one_mul, norm_zero] at h0'
      exact not_tendsto_atTop_of_tendsto_nhds h0' (NumberField.tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop K T)
    ·
      refine NumberField.not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one K T (fun v => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)))
        (fun v => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * ((2 * t : ℝ) : ℂ)))) ?_ hζ
        (germ_normPow K T t ht) (bdd_of_germ (germ_normPow K T (2 * t) (mul_ne_zero two_ne_zero ht)))
      intro v; left
      beta_reduce
      refine ⟨?_, ?_⟩
      · rw [Complex.norm_natCast_cpow_of_pos (absNorm_pos' v.1)]
        simp
      · have he : -(Complex.I * ((2 * t : ℝ) : ℂ)) = (2 : ℕ) * (-(Complex.I * t)) := by push_cast; ring
        rw [he, Complex.cpow_nat_mul]
  ·
    push Not at hA
    obtain ⟨x, hx, hx1⟩ := hA
    obtain ⟨L, hLd, hLE⟩ := NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one K χ _hχ _hχc _hχu ⟨x, hx, hx1⟩ T
    have h1 : χ ≠ 1 := fun h => hx1 (by rw [h]; rfl)
    by_cases h2 : χ ^ 2 = 1
    ·
      have hL1 := NumberField.TateGlobal.apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one K χ _hχ _hχc _hχu h2 h1 T L hLd hLE
      intro h0
      have hlim : Tendsto (fun σ : ℝ => L (σ : ℂ)) (𝓝[>] 1) (𝓝 (L 1)) := by
        have := (hLd.continuous.comp Complex.continuous_ofReal).continuousAt (x := (1 : ℝ))
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have heq : (fun σ : ℝ => L (σ : ℂ)) =ᶠ[𝓝[>] (1 : ℝ)]
          (fun σ : ℝ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹) := by
        filter_upwards [self_mem_nhdsWithin] with σ hσ
        exact hLE σ (by simpa using hσ)
      exact hL1 (tendsto_nhds_unique (hlim.congr' heq) h0)
    ·
      have hχ2c : Continuous ⇑(χ ^ 2 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := by
        have : ⇑(χ ^ 2 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) = fun x => χ x ^ 2 := funext fun x => by simp
        rw [this]; exact _hχc.pow 2
      have hχ2u : IsUnitaryChar (𝓞 K) K (χ ^ 2) := fun y => by simp [_hχu y]
      have hχ2F : IsIdeleClassChar (𝓞 K) K (χ ^ 2) := fun u => by simp [_hχ u]
      refine NumberField.not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one K T
        (fun v => if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0)
        (fun v => if IsUnramifiedCharAt (χ ^ 2) v.1 then (((χ ^ 2) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0)
        ?_ hζ ⟨Set.univ, univ_mem, L, hLd.differentiableOn, fun s _ hs => hLE s hs⟩ ?_
      ·
        intro v
        beta_reduce
        by_cases hv : IsUnramifiedCharAt χ v.1
        · left
          have hv2 : IsUnramifiedCharAt (χ ^ 2) v.1 := by
            intro u hu hu'
            have := hv u hu hu'
            simp only [localChar, MonoidHom.coe_comp, Function.comp_apply] at this ⊢
            rw [MonoidHom.pow_apply, this, one_pow]
          rw [if_pos hv, if_pos hv2]
          exact ⟨_hχu _, by simp⟩
        · right
          rw [if_neg hv]
          refine ⟨rfl, ?_⟩
          split_ifs
          · exact (hχ2u _).le
          · simp
      ·
        by_cases hA2 : ∀ y ∈ normOneIdeles K, (χ ^ 2) y = 1
        · obtain ⟨t2, ht2⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles K (χ ^ 2) hχ2c hχ2u hA2
          have ht2ne : t2 ≠ 0 := fun h => h2 (by rw [ht2, h]; exact normPowChar_zero)
          rw [ht2]
          simp_rw [NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K t2]
          exact bdd_of_germ (germ_normPow K T t2 ht2ne)
        · push Not at hA2
          obtain ⟨y, hy, hy1⟩ := hA2
          obtain ⟨L2, hL2d, hL2E⟩ := NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one K (χ ^ 2) hχ2F hχ2c hχ2u ⟨y, hy, hy1⟩ T
          exact bdd_of_germ ⟨Set.univ, univ_mem, L2, hL2d.differentiableOn, fun s _ hs => hL2E s hs⟩

end

end S_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
end P2MW
export P2MW.S_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar (solution)
