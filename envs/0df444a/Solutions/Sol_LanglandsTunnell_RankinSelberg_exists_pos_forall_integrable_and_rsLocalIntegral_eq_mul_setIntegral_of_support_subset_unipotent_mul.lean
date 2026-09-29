-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5e863bd9-8ecf-5112-89ac-b8a3b4dd8617

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar UnramifiedWhittaker

open scoped ENNReal NNReal

noncomputable section

namespace RSBumpEvalGL2

section GL2

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL ℚ p

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range

theorem continuous_entry (i j : Fin 2) : Continuous fun g : G => (g : Mat) i j :=
  (Units.continuous_val).matrix_elem i j

theorem coe_unip_eq :
    ((unip p : Subgroup G) : Set G) = {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Mat) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Mat) 0 1) : G) : Mat) = (g : Mat)
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip : IsClosed ((unip p : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  exact ((isClosed_singleton.preimage (continuous_entry p 0 0)).inter
    ((isClosed_singleton.preimage (continuous_entry p 1 0)).inter
      (isClosed_singleton.preimage (continuous_entry p 1 1))))

theorem unip_eq_unipotentGL2 (n : unip p) : (n : G) = unipotentGL2 (((n : G) : Mat) 0 1) := by
  obtain ⟨z, hz⟩ := n.2
  rw [← hz]
  change (unipotentGL2 z.toAdd : G) = unipotentGL2 (((unipotentGL2 z.toAdd : G) : Mat) 0 1)
  have h01 : (((unipotentGL2 z.toAdd : G) : Mat) 0 1) = z.toAdd := by simp [unipotentGL2_coe]
  rw [h01]

theorem unip_comm (m n : unip p) : m * n = n * m := by
  refine Subtype.ext ?_
  change (m : G) * (n : G) = (n : G) * (m : G)
  rw [unip_eq_unipotentGL2 p m, unip_eq_unipotentGL2 p n, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem det_unipotentGL2 (x : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem unipotent_eq_unipotentGL2 (x : F) : (unipotent x : G) = unipotentGL2 x :=
  Units.ext rfl

def unipElt (x : F) : unip p := ⟨unipotentGL2 x, ⟨Multiplicative.ofAdd x, rfl⟩⟩

@[scoped simp] theorem coe_unipElt (x : F) : ((unipElt p x : unip p) : G) = unipotentGL2 x := rfl

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem continuous_modulus_det :
    Continuous fun g : G =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) := by
  have : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) :
      ℝ) : ℂ)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

end GL2

section UnipHaar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance locallyCompactSpace_unip : LocallyCompactSpace (unip p) := (isClosed_unip p).locallyCompactSpace

scoped instance secondCountable_unip : SecondCountableTopology (unip p) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unip p : Subgroup G) : Set G)

theorem isMulRightInvariant_unip (μN : Measure (unip p)) [μN.IsMulLeftInvariant] : μN.IsMulRightInvariant := by
  refine ⟨fun n₀ => ?_⟩
  have h : (fun n : unip p => n * n₀) = fun n => n₀ * n := funext fun n => unip_comm p n n₀
  rw [h]
  exact map_mul_left_eq_self μN n₀

end UnipHaar

section Unfold

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem integrable_and_integral_eq_unfold
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Φ : G → ℂ) (hΦm : Measurable Φ) (hΦi : Integrable Φ μ) :
    Integrable (fun g : G => ∫ x : H, Φ ((x : G) * g) ∂μH) (μ.withDensity (HaarQuotient.density H μH)) ∧
    ∫ g, Φ g ∂μ = ∫ g, (∫ x : H, Φ ((x : G) * g) ∂μH) ∂(μ.withDensity (HaarQuotient.density H μH)) := by
  classical
  have hS : IsFundamentalDomain (↥(⊥ : Subgroup G)) (Set.univ : Set G) μ :=
    ⟨MeasurableSet.univ.nullMeasurableSet, Filter.Eventually.of_forall fun x => ⟨1, Set.mem_univ _⟩,
      Subsingleton.pairwise⟩
  haveI : Subsingleton (↥((⊥ : Subgroup G).subgroupOf H)) := ⟨fun a b => by
    refine Subtype.ext (Subtype.ext ?_)
    have ha := a.2
    have hb := b.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  have hT : IsFundamentalDomain (↥((⊥ : Subgroup G).subgroupOf H)) (Set.univ : Set H) μH :=
    ⟨MeasurableSet.univ.nullMeasurableSet, Filter.Eventually.of_forall fun x => ⟨1, Set.mem_univ _⟩,
      Subsingleton.pairwise⟩
  have hfin : ∫⁻ g in Set.univ, ‖Φ g‖ₑ ∂μ < ⊤ := by
    rw [Measure.restrict_univ]
    exact hΦi.2
  obtain ⟨-, h2, h3⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ H hH μH ⊥ bot_le Φ
      hΦm (fun γ hγ g => by rw [Subgroup.mem_bot.mp hγ, one_mul]) Set.univ hS Set.univ hT hfin
  simp only [Measure.restrict_univ] at h2 h3
  set μD := μ.withDensity (HaarQuotient.density H μH) with hμD
  set Ξ : MulAction.orbitRel.Quotient H G → ℂ := fun q => ∫ x : H, Φ ((x : G) * q.out) ∂μH with hΞ
  have hmk : Measurable (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) := measurable_quotient_mk''
  have hmeas : HaarQuotient.measure μ H μH = Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD :=
    rfl
  rw [hmeas] at h2 h3
  have hΞi : Integrable Ξ (Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD) := h2
  have hcomp : Integrable (Ξ ∘ (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)) μD :=
    (integrable_map_measure hΞi.aestronglyMeasurable hmk.aemeasurable).mp hΞi
  have hint : ∫ q, Ξ q ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD) =
      ∫ g, Ξ (Quotient.mk'' g) ∂μD :=
    integral_map hmk.aemeasurable hΞi.aestronglyMeasurable
  have hfib : ∀ g : G, Ξ (Quotient.mk'' g) = ∫ x : H, Φ ((x : G) * g) ∂μH := by
    intro g
    have hrel : @Setoid.r _ (MulAction.orbitRel H G) ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
      Quotient.mk_out' g
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    simp only [hΞ]
    rw [← hn, Subgroup.smul_def, smul_eq_mul]
    have := integral_mul_right_eq_self (μ := μH) (fun x : H => Φ ((x : G) * g)) n
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  have hfun : (Ξ ∘ (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)) = fun g => ∫ x : H, Φ ((x : G) * g) ∂μH :=
    funext fun g => hfib g
  refine ⟨hfun ▸ hcomp, ?_⟩
  rw [h3, hint]
  exact integral_congr_ae (Filter.Eventually.of_forall hfib)

end Unfold

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

def detPow (s : ℂ) (g : G) : ℂ :=
  ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2)

theorem detPow_unipotent_mul (s : ℂ) (x : F) (g : G) : detPow p s (unipotent x * g) = detPow p s g := by
  simp only [detPow, unipotent_eq_unipotentGL2, map_mul, det_unipotentGL2, one_mul]

theorem measurable_detPow (s : ℂ) : Measurable (detPow p s) :=
  (continuous_modulus_det p).measurable.pow_const _

theorem detPow_eq_one_of_modulus_eq_one (s : ℂ) (u : G)
    (hu : modulus ((Matrix.GeneralLinearGroup.det u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) = 1) :
    detPow p s u = 1 := by
  simp only [detPow, hu, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow]

theorem main :
    ∀ (μ₂ : Measure G) [μ₂.IsHaarMeasure]
      (μN₂ : Measure (unip p)) [μN₂.IsHaarMeasure]
      (U : Subgroup G) (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G))
      (hUdet : ∀ u ∈ U, modulus ((Matrix.GeneralLinearGroup.det u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) = 1),
    ∃ c : ℝ, 0 < c ∧
      ∀ (s : ℂ) (W Fn : G → ℂ),
        Measurable (fun g : G => W g * Fn g) →
        IntegrableOn (fun g : G => W g * Fn g) (U : Set G) μ₂ →
        (∀ (x : F) (g : G), W (unipotent x * g) * Fn (unipotent x * g) = W g * Fn g) →
        (∀ g : G, W g * Fn g ≠ 0 → ∃ (x : F) (u : G), u ∈ U ∧ g = unipotent x * u) →
        Integrable (fun g : G => (W g * Fn g) * detPow p s g) (μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) ∧
        RSCarrier.rsLocalIntegral μ₂ (unip p) μN₂
            (fun g : G => (modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ))
            s W Fn =
          (c : ℂ) * ∫ u in (U : Set G), W u * Fn u ∂μ₂ := by
  intro μ₂ _ μN₂ _ U hUc hUo hUdet
  haveI : μN₂.IsMulRightInvariant := isMulRightInvariant_unip p μN₂

  set S : Set (unip p) := ((↑) : unip p → G) ⁻¹' (U : Set G) with hS
  have hSopen : IsOpen S := hUo.preimage continuous_subtype_val
  have hSne : S.Nonempty := ⟨1, by simp [hS, U.one_mem]⟩
  have hSpos : 0 < μN₂ S := hSopen.measure_pos μN₂ hSne
  have hce : Topology.IsClosedEmbedding ((↑) : unip p → G) :=
    Topology.IsClosedEmbedding.subtypeVal (isClosed_unip p)
  have hScomp : IsCompact S := hce.isCompact_preimage hUc
  have hSfin : μN₂ S < ⊤ := hScomp.measure_lt_top
  have hSmeas : MeasurableSet S := hSopen.measurableSet
  set m : ℝ := (μN₂ S).toReal with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
  refine ⟨m⁻¹, inv_pos.mpr hmpos, ?_⟩
  intro s W Fn hmeas hint hinv hsupp

  set R : G → ℂ := fun g => (W g * Fn g) * detPow p s g with hR
  have hRm : Measurable R := hmeas.mul (measurable_detPow p s)
  have hRinv : ∀ (x : F) (g : G), R (unipotent x * g) = R g := fun x g => by
    simp only [hR, hinv x g, detPow_unipotent_mul]
  have hRU : ∀ u ∈ U, R u = W u * Fn u := fun u hu => by
    simp only [hR, detPow_eq_one_of_modulus_eq_one p s u (hUdet u hu), mul_one]

  set f : G → ℂ := (U : Set G).indicator (fun g => (m : ℂ)⁻¹ * R g) with hf
  have hUmeas : MeasurableSet (U : Set G) := hUo.measurableSet
  have hfm : Measurable f := (measurable_const.mul hRm).indicator hUmeas
  have hRintU : IntegrableOn R (U : Set G) μ₂ := by
    refine hint.congr_fun (fun u hu => ?_) hUmeas
    exact (hRU u hu).symm
  have hfi : Integrable f μ₂ := by
    rw [hf, integrable_indicator_iff hUmeas]
    exact hRintU.const_mul _

  have hfib : ∀ g : G, ∫ n : unip p, f ((n : G) * g) ∂μN₂ = R g := by
    intro g
    by_cases hg : W g * Fn g = 0
    ·
      have hRg : R g = 0 := by simp only [hR, hg, zero_mul]
      have hzero : ∀ n : unip p, f ((n : G) * g) = 0 := by
        intro n
        by_cases h : (n : G) * g ∈ (U : Set G)
        · simp only [hf, Set.indicator_of_mem h]
          rw [unip_eq_unipotentGL2 p n, ← unipotent_eq_unipotentGL2, hRinv, hRg, mul_zero]
        · simp only [hf, Set.indicator_of_notMem h]
      simp_rw [hzero, integral_zero, hRg]
    · obtain ⟨x, u, hu, rfl⟩ := hsupp g hg

      set T : Set (unip p) := (fun n : unip p => n * unipElt p x) ⁻¹' S with hT
      have hTmeas : MeasurableSet T := (measurable_mul_const _) hSmeas
      have hTS : μN₂ T = μN₂ S := measure_preimage_mul_right μN₂ (unipElt p x) S
      have hval : ∀ n : unip p, f ((n : G) * (unipotent x * u)) = T.indicator (fun _ => (m : ℂ)⁻¹ * R (unipotent x * u)) n := by
        intro n
        have hmem : ((n : G) * (unipotent x * u) ∈ (U : Set G)) ↔ n ∈ T := by
          simp only [hT, hS, Set.mem_preimage, SetLike.mem_coe]
          rw [← mul_assoc]
          change (n : G) * unipotent x * u ∈ U ↔ ((n * unipElt p x : unip p) : G) ∈ U
          rw [Subgroup.coe_mul, coe_unipElt, ← unipotent_eq_unipotentGL2]
          exact ⟨fun h => by simpa using U.mul_mem h (U.inv_mem hu), fun h => U.mul_mem h hu⟩
        by_cases hn : n ∈ T
        · rw [Set.indicator_of_mem hn]
          simp only [hf, Set.indicator_of_mem (hmem.mpr hn)]
          rw [unip_eq_unipotentGL2 p n, ← unipotent_eq_unipotentGL2, hRinv]
        · rw [Set.indicator_of_notMem hn]
          have h' : (n : G) * (unipotent x * u) ∉ (U : Set G) := fun h => hn (hmem.mp h)
          simp only [hf, Set.indicator_of_notMem h']
      simp_rw [hval]
      rw [integral_indicator_const _ hTmeas, measureReal_def, hTS]
      change (μN₂ S).toReal • ((m : ℂ)⁻¹ * R (unipotent x * u)) = R (unipotent x * u)
      rw [Complex.real_smul, ← hm, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]

  obtain ⟨hU1, hU2⟩ := integrable_and_integral_eq_unfold μ₂ (unip p) (isClosed_unip p) μN₂ f hfm hfi
  have hfun : (fun g : G => ∫ n : unip p, f ((n : G) * g) ∂μN₂) = R := funext hfib
  rw [hfun] at hU1 hU2
  refine ⟨hU1, ?_⟩
  have hRS : RSCarrier.rsLocalIntegral μ₂ (unip p) μN₂
      (fun g : G => (modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ))
      s W Fn = ∫ g, R g ∂(μ₂.withDensity (HaarQuotient.density (unip p) μN₂)) := rfl
  rw [hRS, ← hU2, hf, integral_indicator hUmeas, integral_const_mul, Complex.ofReal_inv]
  congr 1
  exact setIntegral_congr_fun hUmeas fun u hu => hRU u hu

end Main

end RSBumpEvalGL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul.RSBumpEvalGL2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul.RSBumpEvalGL2"

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal UnramifiedWhittaker in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure]
      (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
      (_hUc : IsCompact (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
      (_hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
      (_hUdet : ∀ u ∈ U,
        modulus ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1),
    ∃ c : ℝ, 0 < c ∧
      ∀ (s : ℂ) (W F : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        Measurable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W g * F g) →
        IntegrableOn (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W g * F g)
          (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ →
        (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          W (unipotent x * g) * F (unipotent x * g) = W g * F g) →
        (∀ g : GL (Fin 2) (p.adicCompletion ℚ), W g * F g ≠ 0 →
          ∃ (x : p.adicCompletion ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)), u ∈ U ∧ g = unipotent x * u) →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W g * F g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
            s W F =
          (c : ℂ) * ∫ u in (U : Set (GL (Fin 2) (p.adicCompletion ℚ))), W u * F u ∂μ₂ :=
  RSBumpEvalGL2.main p

end S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_integrable_and_rsLocalIntegral_eq_mul_setIntegral_of_support_subset_unipotent_mul (solution)
