-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integral_setIntegral_translate_kirillov_pairing_eq_mul_of_invariant_of_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/10af494e-3691-5d32-a0c7-12647d2e4859

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Theorems.Thm_AutomorphicForm_WhittakerModel_span_translates_stable_and_law_and_smooth_and_central
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integral_setIntegral_translate_kirillov_pairing_eq_mul_of_invariant_of_cuspidal

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction UnramifiedWhittaker
open NumberField.AdelicLevel (diagOne)
open scoped Classical

noncomputable section

namespace GJK2

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G₂" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
local notation "scal" => (Matrix.GeneralLinearGroup.scalar (Fin 2) : (p.adicCompletion ℚ)ˣ →* GL (Fin 2) (p.adicCompletion ℚ))

theorem secondCountableTopology_units : SecondCountableTopology Fˣ :=
  (Units.isEmbedding_val₀ (G₀ := F)).secondCountableTopology

theorem borelSpace_units [MeasurableSpace F] [BorelSpace F] : BorelSpace Fˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := F)).isInducing.eq_induced, borel_comap, ← BorelSpace.measurable_eq (α := F)]
    rfl⟩

theorem secondCountableTopology_GL : SecondCountableTopology G₂ := by
  haveI : SecondCountableTopology M2 := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  haveI : SecondCountableTopology M2ᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M2)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem isAddHaarMeasure_selfDualHaarAt :
    letI : MeasurableSpace F := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  refine Measure.IsAddHaarMeasure.nnreal_smul _ ?_
  have hq : (0 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) :=
    zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p)
  exact (NNReal.rpow_pos hq).ne'

section Generic

variable {G : Type*} [Group G]

theorem translate_mem_span (f : G → ℂ) (h : G) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h'))) :
    (fun g : G => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : G => (W₁ + W₂) (g * h)) = (fun g : G => W₁ (g * h)) + fun g : G => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : G => (a • W) (g * h)) = a • fun g : G => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem span_le_span_of_mem (f W₀ : G → ℂ)
    (h₀ : f ∈ Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h'))) :
    Submodule.span ℂ (Set.range fun h' : G => fun g : G => f (g * h')) ≤
      Submodule.span ℂ (Set.range fun h' : G => fun g : G => W₀ (g * h')) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span W₀ h h₀

variable [TopologicalSpace G] [ContinuousMul G]

theorem continuous_of_open_stabilizer (f : G → ℂ)
    (hF : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, f (g * k) = f g) :
    Continuous f := by
  obtain ⟨U, hU, hinv⟩ := hF
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show f (g * k) ∈ s
    rw [hinv k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

end Generic

theorem exists_pow_dvd_and_not (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) :
    ∃ b : ℕ, p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N := by
  classical
  refine ⟨(Associates.mk p.asIdeal).count (Associates.mk N).factors, ?_, ?_⟩
  · have h := finprod_mem_dvd p (Ideal.hasFiniteMulSupport hN)
    rw [Ideal.finprod_heightOneSpectrum_factorization hN] at h
    exact h
  · have h := Ideal.finprod_not_dvd p N hN
    rwa [Ideal.finprod_heightOneSpectrum_factorization hN] at h

theorem exists_uniformizer : ∃ ϖ : F, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation ℚ p)).symm π : F),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

theorem v_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem isOpen_ball (m : ℤ) : IsOpen {x : F | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hset : {x : F | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_zpow p hϖ, WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m := mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem isCompact_ball (m : ℤ) : IsCompact {x : F | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hϖ0 : ϖ ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hO : IsCompact (p.adicCompletionIntegers ℚ : Set F) := by
    rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact
  have hset : {x : F | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ (-m) * x) '' (p.adicCompletionIntegers ℚ : Set F) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · intro hx
      refine ⟨ϖ ^ m * x, ?_, ?_⟩
      · rw [Valuation.map_mul, v_zpow p hϖ]
        calc WithZero.exp (-m) * Valued.v x ≤ WithZero.exp (-m) * WithZero.exp m := mul_le_mul_right hx _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      · rw [← mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, one_mul]
    · rintro ⟨y, hy, rfl⟩
      rw [Valuation.map_mul, v_zpow p hϖ, neg_neg]
      calc WithZero.exp m * Valued.v y ≤ WithZero.exp m * 1 := mul_le_mul_right hy _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact hO.image (continuous_const_mul _)

theorem isCompact_annulus (N₀ M : ℤ) :
    IsCompact {t : Fˣ | WithZero.exp N₀ < Valued.v (t : F) ∧ Valued.v (t : F) ≤ WithZero.exp M} := by
  have himage : (Units.val : Fˣ → F) '' {t : Fˣ | WithZero.exp N₀ < Valued.v (t : F) ∧ Valued.v (t : F) ≤ WithZero.exp M} =
      {x : F | Valued.v x ≤ WithZero.exp M} ∩ {x : F | Valued.v x ≤ WithZero.exp N₀}ᶜ := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      have hx0 : x ≠ 0 := by
        intro h; rw [h, Valuation.map_zero] at h1; exact absurd h1 (not_lt.mpr zero_le')
      exact ⟨Units.mk0 x hx0, ⟨h1, h2⟩, rfl⟩
  rw [(Units.isEmbedding_val₀ (G₀ := F)).isCompact_iff, himage]
  exact (isCompact_ball p M).inter_right (isOpen_ball p N₀).isClosed_compl

theorem continuous_diagOne : Continuous (diagOne : Fˣ → G₂) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun t : Fˣ => Matrix.diagonal ![(t : F), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · change Continuous (fun t : Fˣ => Matrix.diagonal ![((t⁻¹ : Fˣ) : F), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first
        | exact continuous_const
        | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

theorem coe_scal (z : Fˣ) : ((scal z : G₂) : M2) = Matrix.diagonal fun _ => (z : F) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.scalar]

theorem continuous_scal : Continuous fun z : Fˣ => (scal z : G₂) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : (fun z : Fˣ => ((scal z : G₂) : M2)) = fun z : Fˣ => Matrix.diagonal fun _ : Fin 2 => (z : F) :=
      funext fun z => coe_scal p z
    show Continuous fun z : Fˣ => ((scal z : G₂) : M2)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · have h : (fun z : Fˣ => (((scal z : G₂)⁻¹ : G₂) : M2)) = fun z : Fˣ => Matrix.diagonal fun _ : Fin 2 => ((z⁻¹ : Fˣ) : F) :=
      funext fun z => by rw [← map_inv, coe_scal]
    show Continuous fun z : Fˣ => (((scal z : G₂)⁻¹ : G₂) : M2)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

theorem diagUnits2_eq_diagOne (y : Fˣ) : (diagUnits2 y 1 : G₂) = diagOne y := by
  apply Units.ext
  rw [coe_diagUnits2]
  show _ = Matrix.diagonal ![(y : F), 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem main
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      (∀ k ∈ K, θ₀ (Matrix.GeneralLinearGroup.det k) = 1) →
      ∀ u ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ u' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        (∀ k ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), u' (g * k) = u' g) →
        (∫ t : (p.adicCompletion ℚ)ˣ,
            (∫ k in (K : Set (GL (Fin 2) (p.adicCompletion ℚ))), u (diagOne t * k) ∂μ₂) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
          ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) *
            ∫ t : (p.adicCompletion ℚ)ˣ, u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _ K hKo hKc hKθ u hu u' hu' hu'K
  haveI := isAddHaarMeasure_selfDualHaarAt p
  haveI : BorelSpace Fˣ := borelSpace_units p
  haveI := secondCountableTopology_units p
  haveI := secondCountableTopology_GL p
  haveI : LocallyCompactSpace G₂ := locallyCompactSpace_localGL ℚ p
  haveI hν : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ).IsHaarMeasure :=
    LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)
  have hKm : MeasurableSet (K : Set G₂) := hKo.measurableSet

  obtain ⟨b, hb⟩ := exists_pow_dvd_and_not p N hN
  have hw₂Kb :=
    LanglandsTunnell.RankinSelberg.forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq
      p N w₂base hw₂K b hb
  obtain ⟨-, hVlaw, hVsm, hVcen⟩ :=
    AutomorphicForm.WhittakerModel.span_translates_stable_and_law_and_smooth_and_central p w₂base hw₂law b
      (fun k hk g => hw₂Kb k g hk) θ₀ hcentral
  have hu_c : Continuous u := continuous_of_open_stabilizer u (hVsm u hu)
  have hu'_c : Continuous u' := continuous_of_open_stabilizer u' (hVsm u' hu')

  have hadm' : ∀ U : Subgroup G₂, IsOpen (U : Set G₂) →
      ∃ B : Finset (G₂ → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G₂ => fun g : G₂ => u' (g * h)),
          (∀ k ∈ U, ∀ g : G₂, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G₂ → ℂ)) := by
    intro U hU
    obtain ⟨B, hB⟩ := hw₂adm U hU
    exact ⟨B, fun w' hw' hinv => hB w' (span_le_span_of_mem u' w₂base hu' hw') hinv⟩
  obtain ⟨C, A, τ, m₁, -, hKD⟩ :=
    AutomorphicForm.WhittakerModel.exists_norm_diagUnits2_mul_le_and_eq_zero_of_admissible_of_centralChar
      p θ₀ u' (hVlaw u' hu') (hVsm u' hu') hadm' (hVcen u' hu')
  have hfar : ∀ y : Fˣ, WithZero.exp m₁ < Valued.v (y : F) → u' (diagOne y) = 0 := by
    intro y hy
    have h := (hKD 1 (Subgroup.one_mem _) y 1).2 (by rwa [inv_one, mul_one])
    rwa [mul_one, diagUnits2_eq_diagOne] at h
  obtain ⟨N₀, hN₀⟩ := hcusp u' hu'

  set g₂ : Fˣ → ℂ := fun t => u' (scal t⁻¹ * diagOne (-t)) with hg₂def
  have hg₂ : ∀ t : Fˣ, u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹ = g₂ t := by
    intro t
    simp only [hg₂def]
    rw [hVcen u' hu' t⁻¹ (diagOne (-t)), map_inv, Units.val_inv_eq_inv_val, mul_comm]
  have hneg : Continuous fun t : Fˣ => -t := by
    have : (fun t : Fˣ => -t) = fun t => (-1 : Fˣ) * t := funext fun t => by rw [neg_one_mul]
    rw [this]; exact continuous_const.mul continuous_id
  have hg₂c : Continuous g₂ :=
    hu'_c.comp (((continuous_scal p).comp continuous_inv).mul ((continuous_diagOne p).comp hneg))
  set Ann : Set Fˣ := {t : Fˣ | WithZero.exp N₀ < Valued.v (t : F) ∧ Valued.v (t : F) ≤ WithZero.exp m₁} with hAnn
  have hAnnc : IsCompact Ann := isCompact_annulus p N₀ m₁
  have hg₂0 : ∀ t, t ∉ Ann → g₂ t = 0 := by
    intro t ht
    rw [← hg₂]
    simp only [hAnn, Set.mem_setOf_eq, not_and_or, not_lt, not_le] at ht
    have hvneg : Valued.v (((-t : Fˣ)) : F) = Valued.v (t : F) := by rw [Units.val_neg, Valuation.map_neg]
    rcases ht with h | h
    · rw [hN₀ (-t) (by rw [hvneg]; exact h), zero_mul]
    · rw [hfar (-t) (by rw [hvneg]; exact h), zero_mul]
  have hg₂cs : HasCompactSupport g₂ := HasCompactSupport.intro hAnnc hg₂0
  have hg₂i : Integrable g₂ (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) :=
    hg₂c.integrable_of_hasCompactSupport hg₂cs

  set J : Fˣ → G₂ → ℂ := fun t k => u (diagOne t * k) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹ with hJ
  have hJ' : ∀ t k, J t k = u (diagOne t * k) * g₂ t := by
    intro t k; simp only [hJ]; rw [mul_assoc, hg₂]

  have hUc : Continuous fun z : Fˣ × G₂ => u (diagOne z.1 * z.2) :=
    hu_c.comp (((continuous_diagOne p).comp continuous_fst).mul continuous_snd)
  obtain ⟨M, hM⟩ := (hAnnc.prod hKc).exists_bound_of_continuousOn hUc.continuousOn
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _

  haveI : IsFiniteMeasure (μ₂.restrict (K : Set G₂)) := isFiniteMeasure_restrict.mpr hKc.measure_lt_top.ne
  have hint : Integrable (Function.uncurry J)
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (μ₂.restrict (K : Set G₂))) := by
    have heq : Function.uncurry J = fun z : Fˣ × G₂ => u (diagOne z.1 * z.2) * g₂ z.1 :=
      funext fun z => hJ' z.1 z.2
    rw [heq]
    refine Integrable.mono' ((hg₂i.norm.const_mul M').mul_prod (integrable_const (1 : ℝ)))
      (hUc.mul (hg₂c.comp continuous_fst)).aestronglyMeasurable ?_
    have hmeas : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (μ₂.restrict (K : Set G₂)) =
        ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod μ₂).restrict (Set.univ ×ˢ (K : Set G₂)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hmeas]
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod hKm) fun z hz => ?_
    simp only [Set.mem_prod, Set.mem_univ, true_and] at hz
    rw [norm_mul, mul_one]
    by_cases ht : z.1 ∈ Ann
    · refine mul_le_mul_of_nonneg_right ((hM z ⟨ht, hz⟩).trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hg₂0 z.1 ht, norm_zero, mul_zero, mul_zero]

  have hslice : ∀ k ∈ K, ∫ t, J t k ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
      ∫ t : Fˣ, u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
    intro k hk
    have h2 := (LanglandsTunnell.RankinSelberg.integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral hcusp k u hu u' hu').2
    beta_reduce at h2
    rw [hKθ k hk, Units.val_one, one_mul] at h2
    rw [← h2]
    simp only [hJ]
    congr 1
    funext t
    rw [hu'K k hk]

  calc (∫ t : Fˣ, (∫ k in (K : Set G₂), u (diagOne t * k) ∂μ₂) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
      = ∫ t : Fˣ, ∫ k in (K : Set G₂), J t k ∂μ₂ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
        congr 1; funext t
        simp only [hJ]
        rw [← integral_mul_const, ← integral_mul_const]
    _ = ∫ k in (K : Set G₂), ∫ t : Fˣ, J t k ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∂μ₂ :=
        integral_integral_swap hint
    _ = ∫ k in (K : Set G₂), (∫ t : Fˣ, u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂μ₂ :=
        setIntegral_congr_fun hKm hslice
    _ = _ := by
        rw [setIntegral_const, Complex.real_smul]
        rfl

end GJK2

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      (∀ k ∈ K, θ₀ (Matrix.GeneralLinearGroup.det k) = 1) →
      ∀ u ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ u' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        (∀ k ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), u' (g * k) = u' g) →
        (∫ t : (p.adicCompletion ℚ)ˣ,
            (∫ k in (K : Set (GL (Fin 2) (p.adicCompletion ℚ))), u (diagOne t * k) ∂μ₂) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
          ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) *
            ∫ t : (p.adicCompletion ℚ)ˣ, u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) :=
  GJK2.main p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral hcusp

end S_LanglandsTunnell_RankinSelberg_integral_setIntegral_translate_kirillov_pairing_eq_mul_of_invariant_of_cuspidal
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integral_setIntegral_translate_kirillov_pairing_eq_mul_of_invariant_of_cuspidal (solution)
