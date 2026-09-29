-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4ebfc0c2-d680-599a-b6d3-9df37a37916a

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_integrable_prod_and_integral_eq_mul_setIntegral_unipotent_diagUnits2_of_forall_lintegral_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

open scoped ENNReal NNReal
noncomputable section
namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel TateLocal.integersPositiveCompacts TateLocal.coe_integersPositiveCompacts TateLocal.isHaarMeasure_comap_val_mulMeasure TateLocal.modulus_adicCompletion_eq_nnnorm RankinSelberg.forall_integrable_prod_and_integral_eq_mul_setIntegral_unipotent_diagUnits2_of_forall_lintegral_eq RankinSelberg.isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "forall_integrable_prod_and_integral_eq_mul_setIntegral_unipotent_diagUnits2_of_forall_lintegral_eq isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2"
namespace U1Spine
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section Local
variable (p : HeightOneSpectrum (𝓞 ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))
scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem secondCountableTopology_units : SecondCountableTopology (p.adicCompletion ℚ)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).secondCountableTopology

theorem coe_unip_eq :
    (((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      {g : GL (Fin 2) (p.adicCompletion ℚ) | (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip :
    IsClosed (((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [coe_unip_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j := fun i j => (Units.continuous_val).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem unip_comm (a b : (unipotentGL2Hom (R := p.adicCompletion ℚ)).range) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  refine Subtype.ext ?_
  change (a : GL (Fin 2) (p.adicCompletion ℚ)) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem isMulRightInvariant_unip [MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ))]
    (μN : Measure (unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN.IsMulLeftInvariant] :
    μN.IsMulRightInvariant := by
  constructor
  intro g
  have : (fun x : (unipotentGL2Hom (R := p.adicCompletion ℚ)).range => x * g) = fun x => g * x :=
    funext fun x => unip_comm p x g
  rw [this]
  exact map_mul_left_eq_self μN g

theorem borelSpace_units [MeasurableSpace (p.adicCompletion ℚ)] [BorelSpace (p.adicCompletion ℚ)] :
    BorelSpace (p.adicCompletion ℚ)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := p.adicCompletion ℚ)]
    rfl⟩

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

theorem continuous_diagUnits2 :
    Continuous fun q : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ => diagUnits2 q.1 q.2 := by
  have hval : Continuous fun q : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
      ((diagUnits2 q.1 q.2 : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
    refine continuous_matrix (f := fun q : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
      ((diagUnits2 q.1 q.2 : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ?_
    intro i j
    fin_cases i <;> fin_cases j
    · simp only [coe_diagUnits2, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      exact Units.continuous_val.comp continuous_fst
    · simp only [coe_diagUnits2, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact continuous_const
    · simp only [coe_diagUnits2, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact continuous_const
    · simp only [coe_diagUnits2, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact Units.continuous_val.comp continuous_snd
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun q : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
      (((diagUnits2 q.1 q.2)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) =
      (fun q : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
        ((diagUnits2 q.1 q.2 : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∘
      (fun q => (q.1⁻¹, q.2⁻¹)) := by
    funext q; rfl
  rw [this]
  exact hval.comp ((continuous_inv.comp continuous_fst).prodMk (continuous_inv.comp continuous_snd))

theorem continuous_chart :
    Continuous fun q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
      diagUnits2 q.2.1 q.2.2 * q.1 :=
  ((continuous_diagUnits2 p).comp continuous_snd).mul continuous_fst

end Local

section HaarScale

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem regular_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).Regular := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.Regular.smul ENNReal.coe_ne_top

theorem map_mul_left_selfDualHaarAt (c : p.adicCompletion ℚ) (hc : c ≠ 0) :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).map (fun x => c * x) = (modulus c)⁻¹ • selfDualHaarAt ℚ p := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  haveI : (selfDualHaarAt ℚ p).Regular := regular_selfDualHaarAt p
  set u : (p.adicCompletion ℚ)ˣ := Units.mk0 c hc with hu
  have hfun : (fun x : p.adicCompletion ℚ => c * x) = fun x => u • x := by
    funext x; rw [hu, Units.smul_mk0]; rfl
  ext s hs
  rw [Measure.map_apply (measurable_const_mul c) hs, hfun, Set.preimage_smul, Measure.coe_nnreal_smul_apply,
    ← MeasureTheory.distribHaarChar_mul, map_inv, modulus_of_ne_zero hc, ← hu, ENNReal.coe_inv (ne_of_gt (distribHaarChar_pos))]

theorem integral_comp_mul_left_selfDualHaarAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : p.adicCompletion ℚ → E) (c : p.adicCompletion ℚ) (hc : c ≠ 0) :
    letI := localBorel ℚ p
    ∫ x, f (c * x) ∂(selfDualHaarAt ℚ p) = ((modulus c)⁻¹ : ℝ≥0) • ∫ x, f x ∂(selfDualHaarAt ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  have he : ((MeasurableEquiv.mulLeft₀ c hc : p.adicCompletion ℚ ≃ᵐ p.adicCompletion ℚ) : p.adicCompletion ℚ → p.adicCompletion ℚ) =
      fun x => c * x := rfl
  calc ∫ x, f (c * x) ∂(selfDualHaarAt ℚ p) = ∫ x, f ((MeasurableEquiv.mulLeft₀ c hc) x) ∂(selfDualHaarAt ℚ p) := rfl
    _ = ∫ y, f y ∂((selfDualHaarAt ℚ p).map (MeasurableEquiv.mulLeft₀ c hc)) := (integral_map_equiv _ f).symm
    _ = _ := by rw [he, map_mul_left_selfDualHaarAt p c hc, integral_smul_nnreal_measure]

theorem lintegral_comp_mul_left_selfDualHaarAt (f : p.adicCompletion ℚ → ℝ≥0∞) (c : p.adicCompletion ℚ) (hc : c ≠ 0) :
    letI := localBorel ℚ p
    ∫⁻ x, f (c * x) ∂(selfDualHaarAt ℚ p) = ((modulus c)⁻¹ : ℝ≥0∞) * ∫⁻ x, f x ∂(selfDualHaarAt ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  have he : ((MeasurableEquiv.mulLeft₀ c hc : p.adicCompletion ℚ ≃ᵐ p.adicCompletion ℚ) : p.adicCompletion ℚ → p.adicCompletion ℚ) =
      fun x => c * x := rfl
  calc ∫⁻ x, f (c * x) ∂(selfDualHaarAt ℚ p) = ∫⁻ x, f ((MeasurableEquiv.mulLeft₀ c hc) x) ∂(selfDualHaarAt ℚ p) := rfl
    _ = ∫⁻ y, f y ∂((selfDualHaarAt ℚ p).map (MeasurableEquiv.mulLeft₀ c hc)) := (lintegral_map_equiv f _).symm
    _ = _ := by rw [he, map_mul_left_selfDualHaarAt p c hc, lintegral_smul_measure, ENNReal.smul_def, ENNReal.coe_inv (modulus_ne_zero hc)]; rfl

end HaarScale

section Algebra

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F𝔽" => p.adicCompletion ℚ
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem unipotent_coe (x : F𝔽) : ((unipotent x : G2) : Mat) = !![1, x; 0, 1] := rfl

theorem unipotent_eq_upperUnipotent2 (x : F𝔽) : (unipotent x : G2) = upperUnipotent2 p x := Units.ext rfl

theorem diagUnits2_eq_diagonal2 (a₁ a₂ : (F𝔽)ˣ) : (diagUnits2 a₁ a₂ : G2) = diagonal2 p ![a₁, a₂] := by
  apply Units.ext
  rw [coe_diagUnits2, diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem coe_unipotent_mul_diagUnits2_mul (x : F𝔽) (a₁ a₂ : (F𝔽)ˣ) (k : G2) :
    ((unipotent x * diagUnits2 a₁ a₂ * k : G2) : Mat) = !![(a₁ : F𝔽), (a₂ : F𝔽) * x; 0, (a₂ : F𝔽)] * (k : Mat) := by
  rw [Units.val_mul, Units.val_mul, unipotent_coe, coe_diagUnits2]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem det_unipotent (x : F𝔽) : Matrix.GeneralLinearGroup.det (unipotent x : G2) = 1 := by
  ext; rw [Matrix.GeneralLinearGroup.val_det_apply, unipotent_coe, Matrix.det_fin_two_of]; simp

theorem det_diagUnits2 (a₁ a₂ : (F𝔽)ˣ) : Matrix.GeneralLinearGroup.det (diagUnits2 a₁ a₂ : G2) = a₁ * a₂ := by
  ext; rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits2, Matrix.det_fin_two_of]; simp

theorem det_chart (x : F𝔽) (a₁ a₂ : (F𝔽)ˣ) (k : G2) :
    Matrix.GeneralLinearGroup.det (unipotent x * diagUnits2 a₁ a₂ * k : G2) = a₁ * a₂ * Matrix.GeneralLinearGroup.det k := by
  rw [map_mul, map_mul, det_unipotent, det_diagUnits2, one_mul]

theorem ps_chart {lam : Fin 2 → ((F𝔽)ˣ →* ℂˣ)} {f : G2 → ℂ} (hf : f ∈ principalSeries2 p lam)
    (x : F𝔽) (a₁ a₂ : (F𝔽)ˣ) (k : G2) :
    f (unipotent x * diagUnits2 a₁ a₂ * k) =
      ((lam 0 a₁ : ℂˣ) : ℂ) * ((lam 1 a₂ : ℂˣ) : ℂ) *
        ((Real.sqrt (‖(a₁ : F𝔽)‖ / ‖(a₂ : F𝔽)‖) : ℝ) : ℂ) * f k := by
  obtain ⟨-, hN, hT⟩ := (mem_principalSeries2_iff).1 hf
  rw [mul_assoc, unipotent_eq_upperUnipotent2, hN, diagUnits2_eq_diagonal2, hT]
  simp [torusChar2, halfModulus2, Fin.prod_univ_two]

theorem modulus_det_of_mem_localLevelOne {k : G2} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    modulus ((Matrix.GeneralLinearGroup.det k : (F𝔽)ˣ) : F𝔽) = 1 := by
  have hent : ∀ {g : G2}, (∀ i j, ‖(g : Mat) i j‖ ≤ 1) → ‖((Matrix.GeneralLinearGroup.det g : (F𝔽)ˣ) : F𝔽)‖ ≤ 1 := by
    intro g h
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; exact mul_le_one₀ (h 0 0) (norm_nonneg _) (h 1 1)
    · rw [norm_neg, norm_mul]; exact mul_le_one₀ (h 0 1) (norm_nonneg _) (h 1 0)
  have hle : ∀ {g : G2} (i j : Fin 2), (∀ i j, (g : Mat) i j ∈ p.adicCompletionIntegers ℚ) → ‖(g : Mat) i j‖ ≤ 1 :=
    fun i j h => Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 (h i j))
  obtain ⟨h1, h2⟩ := (AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ p k).1 hk
  have n1 : ‖((Matrix.GeneralLinearGroup.det k : (F𝔽)ˣ) : F𝔽)‖ ≤ 1 := hent (fun i j => hle i j h1.integral)
  have n2 : ‖((Matrix.GeneralLinearGroup.det k⁻¹ : (F𝔽)ˣ) : F𝔽)‖ ≤ 1 := hent (fun i j => hle i j h2.integral)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at n2
  have hpos : 0 < ‖((Matrix.GeneralLinearGroup.det k : (F𝔽)ˣ) : F𝔽)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have n3 : 1 ≤ ‖((Matrix.GeneralLinearGroup.det k : (F𝔽)ˣ) : F𝔽)‖ := by rwa [inv_le_one₀ hpos] at n2
  have : ‖((Matrix.GeneralLinearGroup.det k : (F𝔽)ˣ) : F𝔽)‖₊ = 1 := by
    ext; rw [coe_nnnorm]; exact le_antisymm n1 n3
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, this]

theorem coe_modulus_eq_norm (x : F𝔽) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem bookkeeping (m₁ m₂ : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) (s : ℂ) :
    (m₁ : ℂ) ^ (s + 1 / 2) * (m₂ : ℂ) ^ (s + 1 / 2) * ((Real.sqrt (m₁ / m₂) : ℝ) : ℂ) *
        (((m₂ * m₁⁻¹ : ℝ)) : ℂ) * (((m₂⁻¹ : ℝ)) : ℂ) = (m₁ : ℂ) ^ s * (m₂ : ℂ) ^ s := by
  have h1 : (m₁ : ℂ) ≠ 0 := by exact_mod_cast h₁.ne'
  have h2 : (m₂ : ℂ) ≠ 0 := by exact_mod_cast h₂.ne'
  have hsqrt : ((Real.sqrt (m₁ / m₂) : ℝ) : ℂ) = (m₁ : ℂ) ^ ((1 / 2 : ℂ)) * ((m₂ : ℂ) ^ ((1 / 2 : ℂ)))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow h₁.le h₂.le, Complex.ofReal_div,
      Complex.ofReal_cpow h₁.le, Complex.ofReal_cpow h₂.le, div_eq_mul_inv]
    norm_num
  rw [hsqrt]
  have e1 : (m₁ : ℂ) ^ (s + 1 / 2) * (m₁ : ℂ) ^ ((1 / 2 : ℂ)) = (m₁ : ℂ) ^ s * (m₁ : ℂ) := by
    rw [← Complex.cpow_add _ _ h1, show s + 1 / 2 + 1 / 2 = s + 1 by ring, Complex.cpow_add _ _ h1, Complex.cpow_one]
  have e2 : (m₂ : ℂ) ^ (s + 1 / 2) * ((m₂ : ℂ) ^ ((1 / 2 : ℂ)))⁻¹ = (m₂ : ℂ) ^ s := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ h2, show s + 1 / 2 + -(1 / 2) = s by ring]
  push_cast
  calc (m₁ : ℂ) ^ (s + 1 / 2) * (m₂ : ℂ) ^ (s + 1 / 2) * ((m₁ : ℂ) ^ ((1 / 2 : ℂ)) * ((m₂ : ℂ) ^ ((1 / 2 : ℂ)))⁻¹) *
        ((m₂ : ℂ) * (m₁ : ℂ)⁻¹) * (m₂ : ℂ)⁻¹
      = ((m₁ : ℂ) ^ (s + 1 / 2) * (m₁ : ℂ) ^ ((1 / 2 : ℂ))) * ((m₂ : ℂ) ^ (s + 1 / 2) * ((m₂ : ℂ) ^ ((1 / 2 : ℂ)))⁻¹) *
          ((m₁ : ℂ)⁻¹ * ((m₂ : ℂ) * (m₂ : ℂ)⁻¹)) := by ring
    _ = (m₁ : ℂ) ^ s * (m₂ : ℂ) ^ s := by rw [e1, e2, mul_inv_cancel₀ h2]; field_simp

end Algebra

section Valuation
open scoped WithZero

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation K v)).symm π : v.adicCompletion K),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

variable {K v}

theorem uniformizer_ne_zero {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ϖ ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem v_uniformizer_pow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (n : ℕ) : Valued.v (ϖ ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [← zpow_natCast, v_uniformizer_zpow hϖ]

theorem v_add_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : v.adicCompletion K} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem v_mul_le {x y : v.adicCompletion K} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a)
    (hy : Valued.v y ≤ WithZero.exp b) : Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem exp_neg_succ_lt_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) < (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exp_neg_succ_le_one (n : ℕ) : WithZero.exp (-((n : ℤ) + 1)) ≤ (1 : ℤᵐ⁰) :=
  (exp_neg_succ_lt_one n).le

theorem exp_antitone_succ (n : ℕ) :
    WithZero.exp (-(((n + 1 : ℕ) : ℤ) + 1)) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem v_lt_one_iff (x : v.adicCompletion K) :
    Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem eq_zero_of_forall_v_le (x : v.adicCompletion K)
    (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-((n : ℤ) + 1))) : x = 0 := by
  by_contra hx
  have hx' : Valued.v x ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v x) with hL
  have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx').symm
  have := h ((-L).toNat)
  rw [hxL, WithZero.exp_le_exp] at this
  omega

theorem v_eq_one_of_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ (hx.trans_lt (exp_neg_succ_lt_one n))

theorem ne_zero_of_v_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx

theorem v_inv_sub_one {x : v.adicCompletion K} {n : ℕ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    Valued.v (x⁻¹ - 1) ≤ WithZero.exp (-((n : ℤ) + 1)) := by
  have h1 := v_eq_one_of_sub_one hx
  have hx0 := ne_zero_of_v_eq_one h1
  have : x⁻¹ - 1 = x⁻¹ * (-(x - 1)) := by field_simp; ring
  rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, one_mul]
  exact hx

theorem isOpen_ball (m : ℤ) : IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hset : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow hϖ,
      WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem exists_eq_zpow_mul (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (y : v.adicCompletion K) (hy : y ≠ 0) :
    ∃ (j : ℤ) (t : v.adicCompletion K), Valued.v t = 1 ∧ y = ϖ ^ j * t ∧
      Valued.v y = WithZero.exp (-j) := by
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  have hy' : Valued.v y ≠ 0 := by rwa [ne_eq, Valuation.zero_iff]
  set L := WithZero.log (Valued.v y) with hL
  have hyL : Valued.v y = WithZero.exp L := (WithZero.exp_log hy').symm
  refine ⟨-L, ϖ ^ L * y, ?_, ?_, ?_⟩
  · rw [Valuation.map_mul, v_uniformizer_zpow hϖ, hyL, ← WithZero.exp_add, neg_add_cancel,
      WithZero.exp_zero]
  · rw [zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0), one_mul]
  · rw [neg_neg, hyL]

end Valuation

section CharNorm

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

theorem exists_eq_zpow_mul_unit (π : (F)ˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) (y : (F)ˣ) :
    ∃ (m : ℤ) (u : (F)ˣ), Valued.v (u : F) = 1 ∧ y = π ^ m * u := by
  have hvy : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set m : ℤ := -WithZero.log (Valued.v (y : F)) with hm
  have hvπm : Valued.v (((π ^ m : (F)ˣ)) : F) = Valued.v (y : F) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, hm, neg_neg,
      WithZero.exp_log hvy]
  refine ⟨m, (π ^ m)⁻¹ * y, ?_, (mul_inv_cancel_left (π ^ m) y).symm⟩
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπm, inv_mul_cancel₀ hvy]

theorem v_zpow_mul_unit (π : (F)ˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) (m : ℤ) (u : (F)ˣ)
    (hu : Valued.v (u : F) = 1) : Valued.v (((π ^ m * u : (F)ˣ)) : F) = WithZero.exp (-m) := by
  rw [Units.val_mul, map_mul, hu, mul_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul,
    mul_neg, mul_one]

def qR : ℝ := ((Ideal.absNorm p.asIdeal : NNReal) : ℝ)

theorem one_lt_qR : 1 < qR p := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  unfold qR; exact_mod_cast this

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

theorem norm_eq_one_of_v (u : F) (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  have := norm_eq_qR_zpow p u 0 (by rw [hu, neg_zero, WithZero.exp_zero])
  rw [this, neg_zero, zpow_zero]

theorem isCompact_units_sphere : IsCompact {u : (F)ˣ | Valued.v (u : F) = 1} := by
  have hO : IsCompact ((p.adicCompletionIntegers ℚ : Set F)) := by
    rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
    exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact
  have hS : IsCompact {x : F | Valued.v x = 1} := by
    refine hO.of_isClosed_subset ?_ (fun x hx => by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx)
    have ho : IsOpen {x : F | Valued.v x = 1}ᶜ := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hx
      by_cases hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) = 0
      · have h0 : x = 0 := (Valuation.zero_iff _).1 hx0
        subst h0
        have hball : {y : F | Valued.v y ≤ WithZero.exp (-1 : ℤ)} ∈ nhds (0 : F) :=
          (isOpen_ball (K := ℚ) (v := p) (-1)).mem_nhds (by simp)
        refine Filter.mem_of_superset hball fun y hy => ?_
        rw [Set.mem_compl_iff, Set.mem_setOf_eq]
        intro h1
        rw [Set.mem_setOf_eq, h1, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
        omega
      · have h := Valued.locally_const hx0
        refine Filter.mem_of_superset h fun y hy => ?_
        rw [Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [Set.mem_setOf_eq] at hy
        rw [hy]; exact hx
    exact ⟨ho⟩
  have himage : (Units.val : (F)ˣ → F) '' {u : (F)ˣ | Valued.v (u : F) = 1} = {x : F | Valued.v x = 1} := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [(Units.isEmbedding_val₀ (G₀ := F)).isCompact_iff, himage]
  exact hS

theorem norm_char_unit_eq_one (θ : (F)ˣ →* ℂˣ) (hcont : Continuous fun t : (F)ˣ => ((θ t : ℂˣ) : ℂ))
    (u : (F)ˣ) (hu : Valued.v (u : F) = 1) : ‖((θ u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨M, hM⟩ := (isCompact_units_sphere p).exists_bound_of_continuousOn hcont.continuousOn
  have hpow : ∀ (w : (F)ˣ), Valued.v (w : F) = 1 → ∀ k : ℕ, ‖((θ w : ℂˣ) : ℂ)‖ ^ k ≤ M := by
    intro w hw k
    have hmem : w ^ k ∈ {u : (F)ˣ | Valued.v (u : F) = 1} := by
      show Valued.v (((w ^ k : (F)ˣ)) : F) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, hw, one_pow]
    have := hM _ hmem
    rwa [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  have hle : ∀ (w : (F)ˣ), Valued.v (w : F) = 1 → ‖((θ w : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro w hw
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hpow w hw k) (not_le.2 hk)
  have h1 := hle u hu
  have h2 := hle u⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((θ u : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (θ u).ne_zero
  have h3 : 1 ≤ ‖((θ u : ℂˣ) : ℂ)‖ := by rwa [inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h3

theorem norm_char_zpow_mul_unit (θ : (F)ˣ →* ℂˣ) (hcont : Continuous fun t : (F)ˣ => ((θ t : ℂˣ) : ℂ))
    (π : (F)ˣ) (m : ℤ) (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    ‖((θ (π ^ m * u) : ℂˣ) : ℂ)‖ = ‖((θ π : ℂˣ) : ℂ)‖ ^ m := by
  rw [map_mul, map_zpow, Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow,
    norm_char_unit_eq_one p θ hcont u hu, mul_one]

theorem zpow_eq_rpow (c : ℝ) (hc : 0 < c) (m : ℤ) :
    c ^ m = (qR p ^ (-m)) ^ (-Real.log c / Real.log (qR p)) := by
  have hq : 1 < qR p := one_lt_qR p
  have hq0 : 0 < qR p := zero_lt_one.trans hq
  have hlogq : Real.log (qR p) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hq0 hq.ne'
  rw [← Real.rpow_intCast (qR p) (-m), ← Real.rpow_mul hq0.le, Real.rpow_def_of_pos hq0,
    ← Real.rpow_intCast c m, Real.rpow_def_of_pos hc]
  congr 1
  field_simp
  push_cast
  ring

theorem exists_norm_char_eq_rpow (χ : (F)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ σχ : ℝ, ∀ a : (F)ˣ, ‖((χ a : ℂˣ) : ℂ)‖ = ‖(a : F)‖ ^ σχ := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer ℚ p
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖ
  set π : (F)ˣ := Units.mk0 ϖ hϖ0 with hπdef
  have hπ : Valued.v (π : F) = WithZero.exp (-1 : ℤ) := hϖ
  have hcont : Continuous fun t : (F)ˣ => ((χ t : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (continuous_def.2 fun s _ => hχ s)
  refine ⟨-Real.log ‖((χ π : ℂˣ) : ℂ)‖ / Real.log (qR p), fun a => ?_⟩
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_zpow_mul_unit p π hπ a
  rw [norm_char_zpow_mul_unit p χ hcont π m u hu, norm_eq_qR_zpow p _ m (v_zpow_mul_unit p π hπ m u hu)]
  exact zpow_eq_rpow p _ (norm_pos_iff.2 (χ π).ne_zero) m

end CharNorm

section Shell
variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => p.adicCompletion ℚ
attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def shell (n : ℤ) : Set Fˣ := {y : Fˣ | Valued.v (y : F) = WithZero.exp (-(n))}

theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell p n) :=
  (hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).1 n

theorem exists_mem_shell (a : Fˣ) : ∃ n : ℤ, a ∈ shell p n := by
  obtain ⟨n, hn, -⟩ := (hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.1 a
  exact ⟨n, hn⟩

theorem measure_shell_eq (n : ℤ) :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p n) =
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) :=
  ((hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.2.1 n).1

theorem measure_shell_zero_lt_top :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) < ⊤ :=
  ((hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p).2.2.1 0).2.2

theorem norm_of_mem_shell {n : ℤ} {a : Fˣ} (h : a ∈ shell p n) : ‖(a : F)‖ = qR p ^ (-n) :=
  norm_eq_qR_zpow p (a : F) n h

theorem qR_pos : 0 < qR p := lt_trans zero_lt_one (one_lt_qR p)

theorem rpow_norm_shell (t : ℝ) (n₀ : ℤ) (m : ℕ) {a : Fˣ} (h : a ∈ shell p (n₀ + m)) :
    ENNReal.ofReal (‖(a : F)‖ ^ t) =
      ENNReal.ofReal (qR p ^ (-(n₀ : ℝ) * t)) * ENNReal.ofReal (qR p ^ (-t)) ^ m := by
  have hq := qR_pos p
  rw [norm_of_mem_shell p h, ← ENNReal.ofReal_pow (Real.rpow_nonneg hq.le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hq.le _)]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul_natCast hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

theorem lintegral_indicator_norm_rpow_lt_top (B t : ℝ) (ht : 0 < t) :
    ∫⁻ a : Fˣ, Set.indicator {a : Fˣ | ‖(a : F)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t)) a
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) < ⊤ := by
  have hq1 := one_lt_qR p

  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hq1
  set n₀ : ℤ := 1 - (k : ℤ) with hn₀
  set c : ENNReal := ENNReal.ofReal (qR p ^ (-(n₀ : ℝ) * t)) with hc
  set r : ENNReal := ENNReal.ofReal (qR p ^ (-t)) with hr
  have hr1 : r < 1 := ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith))

  have hpt : ∀ a : Fˣ,
      Set.indicator {a : Fˣ | ‖(a : F)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t)) a ≤
        ∑' m : ℕ, (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a := by
    intro a
    by_cases hB : ‖(a : F)‖ ≤ B
    · obtain ⟨n, hn⟩ := exists_mem_shell p a
      have hnorm := norm_of_mem_shell p hn
      have hn₀n : n₀ ≤ n := by
        have h1 : qR p ^ (-n) < qR p ^ (k : ℤ) := by
          rw [← hnorm, zpow_natCast]; exact lt_of_le_of_lt hB hk
        have h2 := (zpow_lt_zpow_iff_right₀ hq1).1 h1
        omega
      obtain ⟨m, hm⟩ : ∃ m : ℕ, n = n₀ + m := ⟨(n - n₀).toNat, by omega⟩
      have hn' : a ∈ shell p (n₀ + m) := hm ▸ hn
      calc Set.indicator {a : Fˣ | ‖(a : F)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t)) a
          = ENNReal.ofReal (‖(a : F)‖ ^ t) :=
            Set.indicator_of_mem (show a ∈ {a : Fˣ | ‖(a : F)‖ ≤ B} from hB) _
        _ = c * r ^ m := rpow_norm_shell p t n₀ m hn'
        _ = (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a :=
            (Set.indicator_of_mem hn' (fun _ => c * r ^ m)).symm
        _ ≤ ∑' m : ℕ, (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a :=
            ENNReal.le_tsum (f := fun m : ℕ => (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a) m
    · rw [Set.indicator_of_notMem (show a ∉ {a : Fˣ | ‖(a : F)‖ ≤ B} from hB)]; exact zero_le

  have hS0 := measure_shell_zero_lt_top p
  calc ∫⁻ a : Fˣ, Set.indicator {a : Fˣ | ‖(a : F)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t)) a
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
      ≤ ∫⁻ a : Fˣ, ∑' m : ℕ, (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := lintegral_mono hpt
    _ = ∑' m : ℕ, ∫⁻ a : Fˣ, (shell p (n₀ + m)).indicator (fun _ => c * r ^ m) a
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) :=
        lintegral_tsum fun m => ((measurable_const.indicator (measurableSet_shell p _))).aemeasurable
    _ = ∑' m : ℕ, c * r ^ m * (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) := by
        congr 1; funext m
        rw [lintegral_indicator_const (measurableSet_shell p _), measure_shell_eq p]
    _ = c * (∑' m : ℕ, r ^ m) * (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) hS0
        rw [ENNReal.tsum_geometric]
        exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr1)

end Shell

section Chart
variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F𝔽" => p.adicCompletion ℚ
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

def GJint (F : G2 → ℂ) (Φ : Mat → ℂ) (χ : (F𝔽)ˣ →* ℂˣ) (s : ℂ) : G2 → ℂ := fun g =>
  F g * Φ (g : Mat) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ) ^ (s + 1 / 2)

def chartConst (lam : Fin 2 → ((F𝔽)ˣ →* ℂˣ)) (F : G2 → ℂ) (χ : (F𝔽)ˣ →* ℂˣ) (s : ℂ) (k : G2) (a₁ a₂ : (F𝔽)ˣ) : ℂ :=
  ((lam 0 a₁ : ℂˣ) : ℂ) * ((lam 1 a₂ : ℂˣ) : ℂ) * ((Real.sqrt (‖(a₁ : F𝔽)‖ / ‖(a₂ : F𝔽)‖) : ℝ) : ℂ) * F k *
    ((((χ a₁ : ℂˣ) : ℂ) * ((χ a₂ : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)) *
      (((‖(a₁ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2) * ((‖(a₂ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2)))

theorem GJint_chart {lam : Fin 2 → ((F𝔽)ˣ →* ℂˣ)} {F : G2 → ℂ} (hF : F ∈ principalSeries2 p lam)
    (Φ : Mat → ℂ) (χ : (F𝔽)ˣ →* ℂˣ) (s : ℂ) {k : G2} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (a₁ a₂ : (F𝔽)ˣ) (x : F𝔽) :
    GJint p F Φ χ s (unipotent x * diagUnits2 a₁ a₂ * k) =
      chartConst p lam F χ s k a₁ a₂ * Φ (!![(a₁ : F𝔽), (a₂ : F𝔽) * x; 0, (a₂ : F𝔽)] * (k : Mat)) := by
  have hmod : ((modulus (((a₁ * a₂ * Matrix.GeneralLinearGroup.det k : (F𝔽)ˣ)) : F𝔽) : ℝ) : ℂ) ^ (s + 1 / 2) =
      ((‖(a₁ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2) * ((‖(a₂ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2) := by
    rw [Units.val_mul, Units.val_mul, modulus_mul, modulus_mul, modulus_det_of_mem_localLevelOne p hk, mul_one,
      NNReal.coe_mul, coe_modulus_eq_norm, coe_modulus_eq_norm, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [GJint, chartConst]
  rw [ps_chart p hF, coe_unipotent_mul_diagUnits2_mul, det_chart, map_mul, map_mul, Units.val_mul, Units.val_mul, hmod]
  ring

theorem norm_chartConst (lam : Fin 2 → ((F𝔽)ˣ →* ℂˣ)) (F : G2 → ℂ) (χ : (F𝔽)ˣ →* ℂˣ) (s : ℂ) (k : G2) (a₁ a₂ : (F𝔽)ˣ)
    {σ₀' σ₁' σχ : ℝ} (h0 : ∀ a : (F𝔽)ˣ, ‖((lam 0 a : ℂˣ) : ℂ)‖ = ‖(a : F𝔽)‖ ^ σ₀')
    (h1 : ∀ a : (F𝔽)ˣ, ‖((lam 1 a : ℂˣ) : ℂ)‖ = ‖(a : F𝔽)‖ ^ σ₁') (hχ' : ∀ a : (F𝔽)ˣ, ‖((χ a : ℂˣ) : ℂ)‖ = ‖(a : F𝔽)‖ ^ σχ) :
    ‖chartConst p lam F χ s k a₁ a₂‖ * ‖(a₂ : F𝔽)‖⁻¹ * (‖(a₂ : F𝔽)‖ * ‖(a₁ : F𝔽)‖⁻¹) =
      ‖F k‖ * ‖((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)‖ *
        (‖(a₁ : F𝔽)‖ ^ (s.re + σχ + σ₀') * ‖(a₂ : F𝔽)‖ ^ (s.re + σχ + σ₁')) := by
  have hm₁ : 0 < ‖(a₁ : F𝔽)‖ := norm_pos_iff.2 a₁.ne_zero
  have hm₂ : 0 < ‖(a₂ : F𝔽)‖ := norm_pos_iff.2 a₂.ne_zero
  have hc1 : ‖(((‖(a₁ : F𝔽)‖ : ℝ) : ℂ)) ^ (s + 1 / 2)‖ = ‖(a₁ : F𝔽)‖ ^ (s.re + 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hm₁]; simp
  have hc2 : ‖(((‖(a₂ : F𝔽)‖ : ℝ) : ℂ)) ^ (s + 1 / 2)‖ = ‖(a₂ : F𝔽)‖ ^ (s.re + 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hm₂]; simp
  have hsq : Real.sqrt (‖(a₁ : F𝔽)‖ / ‖(a₂ : F𝔽)‖) = ‖(a₁ : F𝔽)‖ ^ (1 / 2 : ℝ) * ‖(a₂ : F𝔽)‖ ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hm₁.le hm₂.le, Real.rpow_neg hm₂.le, div_eq_mul_inv]
  have hn : ‖chartConst p lam F χ s k a₁ a₂‖ =
      ‖(a₁ : F𝔽)‖ ^ σ₀' * ‖(a₂ : F𝔽)‖ ^ σ₁' * (‖(a₁ : F𝔽)‖ ^ (1 / 2 : ℝ) * ‖(a₂ : F𝔽)‖ ^ (-(1 / 2) : ℝ)) * ‖F k‖ *
        (‖(a₁ : F𝔽)‖ ^ σχ * ‖(a₂ : F𝔽)‖ ^ σχ * ‖((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)‖) *
          (‖(a₁ : F𝔽)‖ ^ (s.re + 1 / 2) * ‖(a₂ : F𝔽)‖ ^ (s.re + 1 / 2)) := by
    unfold chartConst
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, h0, h1, hχ' a₁, hχ' a₂, hc1, hc2,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hsq]
    ring
  have e1 : ‖(a₁ : F𝔽)‖ ^ σ₀' * ‖(a₁ : F𝔽)‖ ^ (1 / 2 : ℝ) * ‖(a₁ : F𝔽)‖ ^ σχ * ‖(a₁ : F𝔽)‖ ^ (s.re + 1 / 2) * ‖(a₁ : F𝔽)‖⁻¹ =
      ‖(a₁ : F𝔽)‖ ^ (s.re + σχ + σ₀') := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hm₁, ← Real.rpow_add hm₁, ← Real.rpow_add hm₁, ← Real.rpow_add hm₁]
    congr 1; ring
  have e2 : ‖(a₂ : F𝔽)‖ ^ σ₁' * ‖(a₂ : F𝔽)‖ ^ (-(1 / 2) : ℝ) * ‖(a₂ : F𝔽)‖ ^ σχ * ‖(a₂ : F𝔽)‖ ^ (s.re + 1 / 2) =
      ‖(a₂ : F𝔽)‖ ^ (s.re + σχ + σ₁') := by
    rw [← Real.rpow_add hm₂, ← Real.rpow_add hm₂, ← Real.rpow_add hm₂]
    congr 1; ring
  rw [hn]
  calc _ = ‖F k‖ * ‖((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)‖ *
        ((‖(a₁ : F𝔽)‖ ^ σ₀' * ‖(a₁ : F𝔽)‖ ^ (1 / 2 : ℝ) * ‖(a₁ : F𝔽)‖ ^ σχ * ‖(a₁ : F𝔽)‖ ^ (s.re + 1 / 2) * ‖(a₁ : F𝔽)‖⁻¹) *
          (‖(a₂ : F𝔽)‖ ^ σ₁' * ‖(a₂ : F𝔽)‖ ^ (-(1 / 2) : ℝ) * ‖(a₂ : F𝔽)‖ ^ σχ * ‖(a₂ : F𝔽)‖ ^ (s.re + 1 / 2)) *
          (‖(a₂ : F𝔽)‖ * ‖(a₂ : F𝔽)‖⁻¹)) := by ring
    _ = _ := by rw [e1, e2, mul_inv_cancel₀ hm₂.ne', mul_one]

theorem bounds_of_entry_bound (a y d : F𝔽) (k : G2) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) (B : ℝ)
    (hB : ∀ i j : Fin 2, ‖(!![a, y; 0, d] * (k : Mat)) i j‖ ≤ B) : ‖a‖ ≤ B ∧ ‖d‖ ≤ B ∧ ‖y‖ ≤ B := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 0)
  have hki : ∀ i j : Fin 2, ‖((k⁻¹ : G2) : Mat) i j‖ ≤ 1 := fun i j =>
    Valued.toNormedField.norm_le_one_iff.2
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 (((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ p k).1 hk).2.integral i j))
  have bnd : ∀ i j i' j', ‖(!![a, y; 0, d] * (k : Mat)) i j * ((k⁻¹ : G2) : Mat) i' j'‖ ≤ B := fun i j i' j' => by
    rw [norm_mul]; exact (mul_le_mul (hB i j) (hki i' j') (norm_nonneg _) hB0).trans (by rw [mul_one])
  have hinv : !![a, y; 0, d] * (k : Mat) * ((k⁻¹ : G2) : Mat) = !![a, y; 0, d] := by
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have ha : a = (!![a, y; 0, d] * (k : Mat) * ((k⁻¹ : G2) : Mat)) 0 0 := by rw [hinv]; simp
  have hd : d = (!![a, y; 0, d] * (k : Mat) * ((k⁻¹ : G2) : Mat)) 1 1 := by rw [hinv]; simp
  have hy : y = (!![a, y; 0, d] * (k : Mat) * ((k⁻¹ : G2) : Mat)) 0 1 := by rw [hinv]; simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at ha hd hy
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (bnd 0 0 0 0) (bnd 0 1 1 0))
  · rw [hd]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (bnd 1 0 0 1) (bnd 1 1 1 1))
  · rw [hy]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (bnd 0 0 0 1) (bnd 0 1 1 1))

theorem exists_entry_bound (Φ : Mat → ℂ) (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, ∀ m ∈ tsupport Φ, ∀ i j : Fin 2, ‖m i j‖ ≤ B := by
  have hc : ∀ i j : Fin 2, Continuous fun m : Mat => ‖m i j‖ := fun i j =>
    (continuous_id.matrix_elem i j).norm
  choose B hB using fun i j => hΦc.isCompact.exists_bound_of_continuousOn ((hc i j).continuousOn)
  refine ⟨max (max (B 0 0) (B 0 1)) (max (B 1 0) (B 1 1)), fun m hm i j => ?_⟩
  have h := hB i j m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  fin_cases i <;> fin_cases j
  · exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem measurable_GJint {lam : Fin 2 → ((F𝔽)ˣ →* ℂˣ)} {F : G2 → ℂ} (hF : F ∈ principalSeries2 p lam)
    (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (χ : (F𝔽)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (s : ℂ) :
    letI := localGLBorel ℚ p
    Measurable (GJint p F Φ χ s) := by
  letI := localGLBorel ℚ p
  haveI : BorelSpace G2 := borelSpace_localGLBorel ℚ p
  obtain ⟨hFlc, -, -⟩ := (mem_principalSeries2_iff).1 hF
  have h1 : Continuous F := hFlc.continuous
  have h2 : Continuous fun g : G2 => Φ (g : Mat) := hΦ.continuous.comp Units.continuous_val
  have h3 : Continuous fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hχ.continuous.comp (Units.continuous_iff.2
      ⟨Units.continuous_val.matrix_det, by
        have : (fun g : G2 => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (F𝔽)ˣ) : F𝔽)) =
            fun g : G2 => (((g⁻¹ : G2) : Mat)).det := by
          funext g; rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [this]; exact Units.continuous_coe_inv.matrix_det⟩))
  have h4 : Measurable fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ) := by
    have : (fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ)) =
        fun g : G2 => (((‖((g : Mat)).det‖) : ℝ) : ℂ) := by
      funext g; rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact (Complex.continuous_ofReal.comp (Units.continuous_val.matrix_det.norm)).measurable
  exact ((h1.measurable.mul h2.measurable).mul h3.measurable).mul (h4.pow_const _)

end Chart

theorem absConvPrimal
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (κ : ℝ), 0 < κ →
      (∀ G : GL (Fin 2) (p.adicCompletion ℚ) → ENNReal, Measurable G →
          ∫⁻ g, G g ∂μ₂ =
            ENNReal.ofReal κ *
              ∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
                (∫⁻ x : p.adicCompletion ℚ, G (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) ∂(selfDualHaarAt ℚ p)) *
                  (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ENNReal)
                ∂((μ₂.restrict (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod
                  ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
                    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →
      ∀ F ∈ principalSeries2 p lam,
      ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            F g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI iGL : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI iBGL : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ κ hκ h3808 F hF Φ hΦ hΦc
  classical
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) := secondCountableTopology_localGL p
  haveI : SecondCountableTopology (p.adicCompletion ℚ)ˣ := secondCountableTopology_units p
  haveI : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := AutomorphicForm.locallyCompactSpace_localGL ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := borelSpace_units p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  haveI hμx : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure :=
    LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)
  haveI : SigmaCompactSpace (p.adicCompletion ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (p.adicCompletion ℚ)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := sigmaCompactSpace_of_locallyCompact_secondCountable

  obtain ⟨σ₀', h0⟩ := exists_norm_char_eq_rpow p (lam 0) (hlam 0)
  obtain ⟨σ₁', h1⟩ := exists_norm_char_eq_rpow p (lam 1) (hlam 1)
  obtain ⟨σχ, hχ'⟩ := exists_norm_char_eq_rpow p χ hχ
  refine ⟨max (-(σχ + σ₀')) (-(σχ + σ₁')), fun s hs => ?_⟩
  have he₁ : 0 < s.re + σχ + σ₀' := by have := lt_of_le_of_lt (le_max_left _ _) hs; linarith
  have he₂ : 0 < s.re + σχ + σ₁' := by have := lt_of_le_of_lt (le_max_right _ _) hs; linarith

  set σ : Measure (p.adicCompletion ℚ) := selfDualHaarAt ℚ p with hσ
  set μx : Measure (p.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hμxdef
  set Kset : Set (GL (Fin 2) (p.adicCompletion ℚ)) :=
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) with hKset
  set P : Measure (GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ)) :=
    (μ₂.restrict Kset).prod (μx.prod μx) with hP
  obtain ⟨hK0c, hK0o⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot
  have hKmeas : MeasurableSet Kset := hK0o.measurableSet
  have hHm : Measurable (GJint p F Φ χ s) := measurable_GJint p hF Φ hΦ χ hχ s
  change Integrable (GJint p F Φ χ s) μ₂
  refine ⟨hHm.aestronglyMeasurable, ?_⟩

  obtain ⟨hFlc, -, -⟩ := (mem_principalSeries2_iff).1 hF
  obtain ⟨B, hB⟩ := exists_entry_bound p Φ hΦc
  obtain ⟨CΦ, hCΦ⟩ := hΦc.exists_bound_of_continuous hΦ.continuous
  obtain ⟨CF, hCF⟩ := hK0c.exists_bound_of_continuousOn (f := F) hFlc.continuous.continuousOn
  have hχdet : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hχ.continuous.comp (Units.continuous_iff.2
      ⟨Units.continuous_val.matrix_det, by
        have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) =
            fun g => (((g⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).det := by
          funext g; rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [this]; exact Units.continuous_coe_inv.matrix_det⟩))
  obtain ⟨Cχ, hCχ⟩ := hK0c.exists_bound_of_continuousOn hχdet.continuousOn
  have hCF0 : 0 ≤ CF := le_trans (norm_nonneg _) (hCF 1 (Subgroup.one_mem _))
  have hCχ0 : 0 ≤ Cχ := le_trans (norm_nonneg _) (hCχ 1 (Subgroup.one_mem _))
  have hCΦ0 : 0 ≤ CΦ := le_trans (norm_nonneg _) (hCΦ 0)

  set ball : Set (p.adicCompletion ℚ) := {y | ‖y‖ ≤ B} with hball
  have hballc : IsCompact ball := by
    have : ball = Metric.closedBall (0 : p.adicCompletion ℚ) B := by
      ext y; simp [hball, Metric.mem_closedBall, dist_zero_right]
    rw [this]; exact isCompact_closedBall 0 B
  have hballm : MeasurableSet ball := hballc.isClosed.measurableSet
  set V : ℝ≥0∞ := ENNReal.ofReal CΦ * σ ball with hV
  have hVtop : V < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hballc.measure_lt_top
  set f₁ : (p.adicCompletion ℚ)ˣ → ℝ≥0∞ := fun a =>
    Set.indicator {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₀'))) a with hf₁
  set f₂ : (p.adicCompletion ℚ)ˣ → ℝ≥0∞ := fun a =>
    Set.indicator {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} (fun a => ENNReal.ofReal (‖(a : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₁'))) a with hf₂
  have hballU : MeasurableSet {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} :=
    (isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  have hf₁m : Measurable f₁ :=
    (ENNReal.measurable_ofReal.comp ((continuous_norm.comp Units.continuous_val).measurable.pow_const _)).indicator hballU
  have hf₂m : Measurable f₂ :=
    (ENNReal.measurable_ofReal.comp ((continuous_norm.comp Units.continuous_val).measurable.pow_const _)).indicator hballU

  have hae : ∀ᵐ q ∂P, q.1 ∈ Kset := by
    rw [ae_iff]
    have hsub : {q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) | ¬ q.1 ∈ Kset} ⊆
        Ksetᶜ ×ˢ (Set.univ : Set ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ)) := fun q hq => ⟨hq, Set.mem_univ _⟩
    refine measure_mono_null hsub ?_
    rw [hP, Measure.prod_prod, Measure.restrict_apply hKmeas.compl, Set.compl_inter_self, measure_empty, zero_mul]

  have hmaj : ∀ᵐ q ∂P,
      (∫⁻ x : p.adicCompletion ℚ, ‖GJint p F Φ χ s (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1)‖ₑ ∂σ) *
        (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ≥0∞) ≤
      (ENNReal.ofReal (CF * Cχ) * V) * (f₁ q.2.1 * f₂ q.2.2) := by
    filter_upwards [hae] with q hq
    obtain ⟨k, a₁, a₂⟩ := q
    have hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by rw [hKset] at hq; exact hq
    simp only
    have hm₁ : 0 < ‖(a₁ : p.adicCompletion ℚ)‖ := norm_pos_iff.2 a₁.ne_zero
    have hm₂ : 0 < ‖(a₂ : p.adicCompletion ℚ)‖ := norm_pos_iff.2 a₂.ne_zero

    have hΦm : Measurable fun y : p.adicCompletion ℚ =>
        ‖Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))‖ₑ := by
      refine (hΦ.continuous.comp ?_).measurable.enorm
      refine Continuous.mul (continuous_matrix ?_) continuous_const
      intro i j; fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_id
      · exact continuous_const
      · exact continuous_const
    have hstep1 : (∫⁻ x : p.adicCompletion ℚ, ‖GJint p F Φ χ s (unipotent x * diagUnits2 a₁ a₂ * k)‖ₑ ∂σ) =
        ‖chartConst p lam F χ s k a₁ a₂‖ₑ * (((modulus (a₂ : p.adicCompletion ℚ))⁻¹ : ℝ≥0∞) *
          ∫⁻ y : p.adicCompletion ℚ, ‖Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] *
            (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))‖ₑ ∂σ) := by
      have e1 : ∀ x, ‖GJint p F Φ χ s (unipotent x * diagUnits2 a₁ a₂ * k)‖ₑ =
          ‖chartConst p lam F χ s k a₁ a₂‖ₑ * ‖Φ (!![(a₁ : p.adicCompletion ℚ), (a₂ : p.adicCompletion ℚ) * x; 0, (a₂ : p.adicCompletion ℚ)] *
            (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))‖ₑ := fun x => by
        rw [GJint_chart p hF Φ χ s hk, enorm_mul]
      rw [lintegral_congr e1, lintegral_const_mul' _ _ enorm_ne_top]
      congr 1
      have := lintegral_comp_mul_left_selfDualHaarAt p
        (fun y : p.adicCompletion ℚ => ‖Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] *
          (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))‖ₑ) (a₂ : p.adicCompletion ℚ) a₂.ne_zero
      rw [hσ, this]

    have hstep2 : ∫⁻ y : p.adicCompletion ℚ, ‖Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] *
          (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))‖ₑ ∂σ ≤
        Set.indicator {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} (fun _ => (1 : ℝ≥0∞)) a₁ *
          Set.indicator {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} (fun _ => (1 : ℝ≥0∞)) a₂ * V := by
      by_cases hab : ‖(a₁ : p.adicCompletion ℚ)‖ ≤ B ∧ ‖(a₂ : p.adicCompletion ℚ)‖ ≤ B
      · rw [Set.indicator_of_mem (show a₁ ∈ {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} from hab.1),
          Set.indicator_of_mem (show a₂ ∈ {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} from hab.2),
          one_mul, one_mul, hV, ← lintegral_indicator_const hballm]
        refine lintegral_mono (fun y => ?_)
        by_cases hy : Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = 0
        · rw [hy, enorm_zero]; exact zero_le
        · have hmem := bounds_of_entry_bound p _ y _ k hk B (hB _ (subset_tsupport _ hy))
          rw [Set.indicator_of_mem (show y ∈ ball from hmem.2.2), ← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hCΦ _)
      · have hzero : ∀ y, Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = 0 := by
          intro y; by_contra hy
          have hmem := bounds_of_entry_bound p _ y _ k hk B (hB _ (subset_tsupport _ hy))
          exact hab ⟨hmem.1, hmem.2.1⟩
        simp only [hzero, enorm_zero, lintegral_zero]
        exact zero_le

    have hreal : ‖chartConst p lam F χ s k a₁ a₂‖ * ‖(a₂ : p.adicCompletion ℚ)‖⁻¹ *
        (‖(a₂ : p.adicCompletion ℚ)‖ * ‖(a₁ : p.adicCompletion ℚ)‖⁻¹) ≤
        CF * Cχ * (‖(a₁ : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₀') * ‖(a₂ : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₁')) := by
      rw [norm_chartConst p lam F χ s k a₁ a₂ h0 h1 hχ']
      have hpow : 0 ≤ ‖(a₁ : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₀') * ‖(a₂ : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₁') :=
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hCF k hk) (hCχ k hk) (norm_nonneg _) hCF0) hpow
    have hmodinv : (((modulus (a₂ : p.adicCompletion ℚ))⁻¹ : ℝ≥0∞)) = ENNReal.ofReal (‖(a₂ : p.adicCompletion ℚ)‖⁻¹) := by
      rw [← ENNReal.coe_inv (modulus_ne_zero a₂.ne_zero), ENNReal.ofReal, Real.toNNReal_inv, ← coe_modulus_eq_norm,
        Real.toNNReal_coe]
    have hmodq : ((modulus ((a₂ * a₁⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ≥0∞)) =
        ENNReal.ofReal (‖(a₂ : p.adicCompletion ℚ)‖ * ‖(a₁ : p.adicCompletion ℚ)‖⁻¹) := by
      rw [← ENNReal.ofReal_coe_nnreal, coe_modulus_eq_norm, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv]
    rw [hstep1, hmodinv, hmodq, ← ofReal_norm_eq_enorm]
    by_cases hab : ‖(a₁ : p.adicCompletion ℚ)‖ ≤ B ∧ ‖(a₂ : p.adicCompletion ℚ)‖ ≤ B
    · have hI : ∫⁻ y : p.adicCompletion ℚ, ‖Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] *
            (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))‖ₑ ∂σ ≤ V := by
        refine hstep2.trans ?_
        rw [Set.indicator_of_mem (show a₁ ∈ {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} from hab.1),
          Set.indicator_of_mem (show a₂ ∈ {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} from hab.2),
          one_mul, one_mul]
      have hf : f₁ a₁ * f₂ a₂ = ENNReal.ofReal (‖(a₁ : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₀') *
          ‖(a₂ : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₁')) := by
        simp only [hf₁, hf₂]
        rw [Set.indicator_of_mem (show a₁ ∈ {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} from hab.1),
          Set.indicator_of_mem (show a₂ ∈ {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} from hab.2),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
      calc ENNReal.ofReal ‖chartConst p lam F χ s k a₁ a₂‖ *
            (ENNReal.ofReal (‖(a₂ : p.adicCompletion ℚ)‖⁻¹) *
              ∫⁻ y : p.adicCompletion ℚ, ‖Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] *
                (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))‖ₑ ∂σ) *
            ENNReal.ofReal (‖(a₂ : p.adicCompletion ℚ)‖ * ‖(a₁ : p.adicCompletion ℚ)‖⁻¹)
          ≤ ENNReal.ofReal ‖chartConst p lam F χ s k a₁ a₂‖ * (ENNReal.ofReal (‖(a₂ : p.adicCompletion ℚ)‖⁻¹) * V) *
            ENNReal.ofReal (‖(a₂ : p.adicCompletion ℚ)‖ * ‖(a₁ : p.adicCompletion ℚ)‖⁻¹) := by gcongr
        _ = ENNReal.ofReal (‖chartConst p lam F χ s k a₁ a₂‖ * ‖(a₂ : p.adicCompletion ℚ)‖⁻¹ *
              (‖(a₂ : p.adicCompletion ℚ)‖ * ‖(a₁ : p.adicCompletion ℚ)‖⁻¹)) * V := by
            rw [ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (inv_nonneg.2 (norm_nonneg _))),
              ENNReal.ofReal_mul (norm_nonneg (chartConst p lam F χ s k a₁ a₂))]
            ring
        _ ≤ ENNReal.ofReal (CF * Cχ * (‖(a₁ : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₀') *
              ‖(a₂ : p.adicCompletion ℚ)‖ ^ (s.re + σχ + σ₁'))) * V := by gcongr
        _ = (ENNReal.ofReal (CF * Cχ) * V) * (f₁ a₁ * f₂ a₂) := by
            rw [hf, ENNReal.ofReal_mul (mul_nonneg hCF0 hCχ0)]; ring
    · have hI : ∫⁻ y : p.adicCompletion ℚ, ‖Φ (!![(a₁ : p.adicCompletion ℚ), y; 0, (a₂ : p.adicCompletion ℚ)] *
            (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))‖ₑ ∂σ = 0 := by
        refine le_antisymm (hstep2.trans ?_) (zero_le)
        rcases not_and_or.1 hab with h | h
        · rw [Set.indicator_of_notMem (show a₁ ∉ {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} from h)]; simp
        · rw [Set.indicator_of_notMem (show a₂ ∉ {a : (p.adicCompletion ℚ)ˣ | ‖(a : p.adicCompletion ℚ)‖ ≤ B} from h)]; simp
      rw [hI, mul_zero, mul_zero, zero_mul]
      exact zero_le

  have hlin := h3808 (fun g => ‖GJint p F Φ χ s g‖ₑ) hHm.enorm
  show ∫⁻ g, ‖GJint p F Φ χ s g‖ₑ ∂μ₂ < ⊤
  rw [hlin]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  calc ∫⁻ q, (∫⁻ x : p.adicCompletion ℚ, ‖GJint p F Φ χ s (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1)‖ₑ ∂σ) *
          (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ≥0∞) ∂P
      ≤ ∫⁻ q, (ENNReal.ofReal (CF * Cχ) * V) * (f₁ q.2.1 * f₂ q.2.2) ∂P := lintegral_mono_ae hmaj
    _ = (ENNReal.ofReal (CF * Cχ) * V) * ∫⁻ q, f₁ q.2.1 * f₂ q.2.2 ∂P := by
        rw [lintegral_const_mul]
        exact (hf₁m.comp (measurable_fst.comp measurable_snd)).mul (hf₂m.comp (measurable_snd.comp measurable_snd))
    _ = (ENNReal.ofReal (CF * Cχ) * V) * ((μ₂.restrict Kset) Set.univ * ((∫⁻ a, f₁ a ∂μx) * ∫⁻ a, f₂ a ∂μx)) := by
        congr 1
        have hgm : Measurable (fun q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
            f₁ q.2.1 * f₂ q.2.2) :=
          (hf₁m.comp (measurable_fst.comp measurable_snd)).mul (hf₂m.comp (measurable_snd.comp measurable_snd))
        rw [hP, lintegral_prod _ hgm.aemeasurable]
        have hin : ∀ k : GL (Fin 2) (p.adicCompletion ℚ),
            (∫⁻ a : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ, f₁ (k, a).2.1 * f₂ (k, a).2.2 ∂(μx.prod μx)) =
              (∫⁻ a, f₁ a ∂μx) * ∫⁻ a, f₂ a ∂μx := fun k =>
          lintegral_prod_mul hf₁m.aemeasurable hf₂m.aemeasurable
        rw [lintegral_congr hin, lintegral_const, mul_comm]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVtop) (ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top ?_ ?_))
        · rw [Measure.restrict_apply_univ]; exact hK0c.measure_lt_top
        · exact lintegral_indicator_norm_rpow_lt_top p B _ he₁
        · exact lintegral_indicator_norm_rpow_lt_top p B _ he₂

section Main
variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F𝔽" => p.adicCompletion ℚ
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem main
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (κ : ℝ), 0 < κ →
      (∀ G : GL (Fin 2) (p.adicCompletion ℚ) → ENNReal, Measurable G →
          ∫⁻ g, G g ∂μ₂ =
            ENNReal.ofReal κ *
              ∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
                (∫⁻ x : p.adicCompletion ℚ, G (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) ∂(selfDualHaarAt ℚ p)) *
                  (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ENNReal)
                ∂((μ₂.restrict (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod
                  ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
                    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →
      ∀ F ∈ principalSeries2 p lam,
      ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        let ϕ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun ad =>
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
              (∫ x : (p.adicCompletion ℚ), Φ (!![ad.1, x; 0, ad.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂
        (IsLocallyConstant ϕ ∧ HasCompactSupport ϕ) ∧
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            F g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
          Integrable (fun ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
            ϕ ((ad.1 : (p.adicCompletion ℚ)), (ad.2 : (p.adicCompletion ℚ))) *
              (((χ * lam 0) ad.1 : ℂˣ) : ℂ) * (((χ * lam 1) ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s) ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          godementZeta2 p μ₂ F Φ χ (s + 1 / 2) =
            (κ : ℂ) * ∫ ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ,
              ϕ ((ad.1 : (p.adicCompletion ℚ)), (ad.2 : (p.adicCompletion ℚ))) *
              (((χ * lam 0) ad.1 : ℂˣ) : ℂ) * (((χ * lam 1) ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s ∂((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI iGL : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI iBGL : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ κ hκ h3808 F hF Φ hΦ hΦc ϕ
  classical
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) := secondCountableTopology_localGL p
  haveI : SecondCountableTopology (p.adicCompletion ℚ)ˣ := secondCountableTopology_units p
  haveI : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := AutomorphicForm.locallyCompactSpace_localGL ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := borelSpace_units p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  haveI hμx : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure :=
    LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)
  haveI : SigmaCompactSpace (p.adicCompletion ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (p.adicCompletion ℚ)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  refine ⟨LanglandsTunnell.RankinSelberg.isLocallyConstant_and_hasCompactSupport_slice_of_mem_principalSeries2 p lam hlam χ hχ
      F hF Φ hΦ hΦc μ₂, ?_⟩
  obtain ⟨σA, hA⟩ := absConvPrimal p lam hlam χ hχ μ₂ κ hκ h3808 F hF Φ hΦ hΦc
  refine ⟨σA, fun s hs => ?_⟩

  set σ : Measure (p.adicCompletion ℚ) := selfDualHaarAt ℚ p with hσ
  set μx : Measure (p.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hμxdef
  set Kset : Set G2 := (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G2) with hKset
  set P : Measure (G2 × ((F𝔽)ˣ × (F𝔽)ˣ)) := (μ₂.restrict Kset).prod (μx.prod μx) with hP
  obtain ⟨hK0c, hK0o⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot
  have hKmeas : MeasurableSet Kset := hK0o.measurableSet
  set H : G2 → ℂ := fun g => F g * Φ (g : Mat) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ) ^ (s + 1 / 2) with hH
  have hHint : Integrable H μ₂ := hA s hs
  obtain ⟨hIWint, hIWeq⟩ :=
    LanglandsTunnell.RankinSelberg.forall_integrable_prod_and_integral_eq_mul_setIntegral_unipotent_diagUnits2_of_forall_lintegral_eq
      p μ₂ κ hκ h3808 H hHint
  set J : G2 → ((F𝔽)ˣ × (F𝔽)ˣ) → ℂ := fun k a => F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
      (∫ x : F𝔽, Φ (!![((a.1 : (F𝔽)ˣ) : F𝔽), x; 0, ((a.2 : (F𝔽)ˣ) : F𝔽)] * (k : Mat)) ∂σ) with hJ
  set cfac : ((F𝔽)ˣ × (F𝔽)ˣ) → ℂ := fun a => (((χ * lam 0) a.1 : ℂˣ) : ℂ) * (((χ * lam 1) a.2 : ℂˣ) : ℂ) *
      ((modulus (a.1 : F𝔽) : ℝ) : ℂ) ^ s * ((modulus (a.2 : F𝔽) : ℝ) : ℂ) ^ s with hc

  have hpt : ∀ k ∈ Kset, ∀ a₁ a₂ : (F𝔽)ˣ,
      (∫ x : F𝔽, H (unipotent x * diagUnits2 a₁ a₂ * k) ∂σ) * ((modulus ((a₂ * a₁⁻¹ : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ) =
        J k (a₁, a₂) * cfac (a₁, a₂) := by
    intro k hk a₁ a₂
    have hk' : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by rw [hKset] at hk; exact hk
    have hm₁ : 0 < ‖(a₁ : F𝔽)‖ := norm_pos_iff.2 a₁.ne_zero
    have hm₂ : 0 < ‖(a₂ : F𝔽)‖ := norm_pos_iff.2 a₂.ne_zero

    have hHx : ∀ x : F𝔽, H (unipotent x * diagUnits2 a₁ a₂ * k) =
        (((lam 0 a₁ : ℂˣ) : ℂ) * ((lam 1 a₂ : ℂˣ) : ℂ) * ((Real.sqrt (‖(a₁ : F𝔽)‖ / ‖(a₂ : F𝔽)‖) : ℝ) : ℂ) * F k *
          ((((χ a₁ : ℂˣ) : ℂ) * ((χ a₂ : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)) *
          (((‖(a₁ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2) * ((‖(a₂ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2)))) *
          Φ (!![(a₁ : F𝔽), (a₂ : F𝔽) * x; 0, (a₂ : F𝔽)] * (k : Mat)) := by
      intro x
      have hmod : ((modulus (((a₁ * a₂ * Matrix.GeneralLinearGroup.det k : (F𝔽)ˣ)) : F𝔽) : ℝ) : ℂ) ^ (s + 1 / 2) =
          ((‖(a₁ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2) * ((‖(a₂ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2) := by
        rw [Units.val_mul, Units.val_mul, modulus_mul, modulus_mul, modulus_det_of_mem_localLevelOne p hk', mul_one,
          NNReal.coe_mul, coe_modulus_eq_norm, coe_modulus_eq_norm, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
      simp only [hH]
      rw [ps_chart p hF, coe_unipotent_mul_diagUnits2_mul, det_chart, map_mul, map_mul, Units.val_mul, Units.val_mul, hmod]
      ring

    have hsub := integral_comp_mul_left_selfDualHaarAt p
      (fun y : F𝔽 => Φ (!![(a₁ : F𝔽), y; 0, (a₂ : F𝔽)] * (k : Mat))) (a₂ : F𝔽) a₂.ne_zero
    have hI : (∫ x : F𝔽, H (unipotent x * diagUnits2 a₁ a₂ * k) ∂σ) =
        (((lam 0 a₁ : ℂˣ) : ℂ) * ((lam 1 a₂ : ℂˣ) : ℂ) * ((Real.sqrt (‖(a₁ : F𝔽)‖ / ‖(a₂ : F𝔽)‖) : ℝ) : ℂ) * F k *
          ((((χ a₁ : ℂˣ) : ℂ) * ((χ a₂ : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)) *
          (((‖(a₁ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2) * ((‖(a₂ : F𝔽)‖ : ℝ) : ℂ) ^ (s + 1 / 2)))) *
          ((((‖(a₂ : F𝔽)‖⁻¹ : ℝ)) : ℂ) * ∫ y : F𝔽, Φ (!![(a₁ : F𝔽), y; 0, (a₂ : F𝔽)] * (k : Mat)) ∂σ) := by
      rw [integral_congr_ae (ae_of_all _ hHx), integral_const_mul, hσ, hsub, NNReal.smul_def, Complex.real_smul,
        NNReal.coe_inv, coe_modulus_eq_norm]
    have hmodC : ((modulus ((a₂ * a₁⁻¹ : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ) = (((‖(a₂ : F𝔽)‖ * ‖(a₁ : F𝔽)‖⁻¹ : ℝ)) : ℂ) := by
      rw [coe_modulus_eq_norm, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv]
    have hb := bookkeeping ‖(a₁ : F𝔽)‖ ‖(a₂ : F𝔽)‖ hm₁ hm₂ s
    rw [hI, hmodC]
    simp only [hJ, hc, MonoidHom.mul_apply, Units.val_mul, coe_modulus_eq_norm]
    linear_combination (((lam 0 a₁ : ℂˣ) : ℂ) * ((lam 1 a₂ : ℂˣ) : ℂ) * F k *
      (((χ a₁ : ℂˣ) : ℂ) * ((χ a₂ : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)) *
      ∫ y : F𝔽, Φ (!![(a₁ : F𝔽), y; 0, (a₂ : F𝔽)] * (k : Mat)) ∂σ) * hb

  have hae : ∀ᵐ q ∂P, q.1 ∈ Kset := by
    rw [ae_iff]
    have hsub : {q : G2 × ((F𝔽)ˣ × (F𝔽)ˣ) | ¬ q.1 ∈ Kset} ⊆ Ksetᶜ ×ˢ (Set.univ : Set ((F𝔽)ˣ × (F𝔽)ˣ)) :=
      fun q hq => ⟨hq, Set.mem_univ _⟩
    refine measure_mono_null hsub ?_
    rw [hP, Measure.prod_prod, Measure.restrict_apply hKmeas.compl, Set.compl_inter_self, measure_empty, zero_mul]
  have hGint : Integrable (fun q : G2 × ((F𝔽)ˣ × (F𝔽)ˣ) => J q.1 q.2 * cfac q.2) P := by
    have h1 := hIWint.integral_prod_left
    refine h1.congr ?_
    filter_upwards [hae] with q hq
    show (∫ x : F𝔽, H (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) *
        ((modulus ((q.2.2 * q.2.1⁻¹ : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ) ∂σ) = J q.1 q.2 * cfac q.2
    rw [integral_mul_const]
    exact hpt q.1 hq q.2.1 q.2.2

  have hslice : ∀ a : (F𝔽)ˣ × (F𝔽)ˣ, ∫ k, J k a * cfac a ∂(μ₂.restrict Kset) =
      ϕ ((a.1 : F𝔽), (a.2 : F𝔽)) * (((χ * lam 0) a.1 : ℂˣ) : ℂ) * (((χ * lam 1) a.2 : ℂˣ) : ℂ) *
        ((modulus (a.1 : F𝔽) : ℝ) : ℂ) ^ s * ((modulus (a.2 : F𝔽) : ℝ) : ℂ) ^ s := by
    intro a
    rw [integral_mul_const]
    show (∫ k in Kset, J k a ∂μ₂) * cfac a = _
    simp only [hJ, hc]
    ring

  have hZ : Integrable (fun ad : (F𝔽)ˣ × (F𝔽)ˣ =>
      ϕ ((ad.1 : F𝔽), (ad.2 : F𝔽)) * (((χ * lam 0) ad.1 : ℂˣ) : ℂ) * (((χ * lam 1) ad.2 : ℂˣ) : ℂ) *
        ((modulus (ad.1 : F𝔽) : ℝ) : ℂ) ^ s * ((modulus (ad.2 : F𝔽) : ℝ) : ℂ) ^ s) (μx.prod μx) := by
    have h2 := hGint.integral_prod_right
    refine h2.congr (ae_of_all _ fun a => ?_)
    exact hslice a

  have hgz : godementZeta2 p μ₂ F Φ χ (s + 1 / 2) = ∫ g, H g ∂μ₂ := rfl
  have hiter : (∫ k in Kset, ∫ a₁ : (F𝔽)ˣ, ∫ a₂ : (F𝔽)ˣ,
        (∫ x : F𝔽, H (unipotent x * diagUnits2 a₁ a₂ * k) ∂σ) *
          ((modulus ((a₂ * a₁⁻¹ : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ) ∂μx ∂μx ∂μ₂) =
      ∫ k in Kset, ∫ a₁ : (F𝔽)ˣ, ∫ a₂ : (F𝔽)ˣ, J k (a₁, a₂) * cfac (a₁, a₂) ∂μx ∂μx ∂μ₂ := by
    refine setIntegral_congr_fun hKmeas (fun k hk => ?_)
    refine integral_congr_ae (ae_of_all _ fun a₁ => ?_)
    refine integral_congr_ae (ae_of_all _ fun a₂ => ?_)
    exact hpt k hk a₁ a₂
  have hprod : (∫ k in Kset, ∫ a₁ : (F𝔽)ˣ, ∫ a₂ : (F𝔽)ˣ, J k (a₁, a₂) * cfac (a₁, a₂) ∂μx ∂μx ∂μ₂) =
      ∫ q, J q.1 q.2 * cfac q.2 ∂P := by
    rw [hP, integral_prod _ hGint]
    refine integral_congr_ae ?_
    exact (hGint.prod_right_ae).mono fun k hk => (integral_prod _ hk).symm
  have hswap : (∫ q, J q.1 q.2 * cfac q.2 ∂P) =
      ∫ a : (F𝔽)ˣ × (F𝔽)ˣ, ∫ k, J k a * cfac a ∂(μ₂.restrict Kset) ∂(μx.prod μx) := by
    rw [hP, integral_prod_symm _ hGint]
  refine ⟨hHint, hZ, ?_⟩
  rw [hgz, hIWeq]
  show (κ : ℂ) * (∫ k in Kset, ∫ a₁ : (F𝔽)ˣ, ∫ a₂ : (F𝔽)ˣ,
        (∫ x : F𝔽, H (unipotent x * diagUnits2 a₁ a₂ * k) ∂σ) *
          ((modulus ((a₂ * a₁⁻¹ : (F𝔽)ˣ) : F𝔽) : ℝ) : ℂ) ∂μx ∂μx ∂μ₂) = _
  rw [hiter, hprod, hswap, integral_congr_ae (ae_of_all _ hslice)]

end Main

end LanglandsTunnell.RankinSelberg.U1Spine
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell.RankinSelberg.U1Spine"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell.RankinSelberg"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2.LanglandsTunnell.RankinSelberg.U1Spine"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (κ : ℝ), 0 < κ →
      (∀ G : GL (Fin 2) (p.adicCompletion ℚ) → ENNReal, Measurable G →
          ∫⁻ g, G g ∂μ₂ =
            ENNReal.ofReal κ *
              ∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
                (∫⁻ x : p.adicCompletion ℚ, G (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) ∂(selfDualHaarAt ℚ p)) *
                  (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ENNReal)
                ∂((μ₂.restrict (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod
                  ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
                    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →
      ∀ F ∈ principalSeries2 p lam,
      ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        let ϕ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun ad =>
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
              (∫ x : (p.adicCompletion ℚ), Φ (!![ad.1, x; 0, ad.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂
        (IsLocallyConstant ϕ ∧ HasCompactSupport ϕ) ∧
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            F g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
          Integrable (fun ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
            ϕ ((ad.1 : (p.adicCompletion ℚ)), (ad.2 : (p.adicCompletion ℚ))) *
              (((χ * lam 0) ad.1 : ℂˣ) : ℂ) * (((χ * lam 1) ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s) ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          godementZeta2 p μ₂ F Φ χ (s + 1 / 2) =
            (κ : ℂ) * ∫ ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ,
              ϕ ((ad.1 : (p.adicCompletion ℚ)), (ad.2 : (p.adicCompletion ℚ))) *
              (((χ * lam 0) ad.1 : ℂˣ) : ℂ) * (((χ * lam 1) ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s ∂((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) :=
  LanglandsTunnell.RankinSelberg.U1Spine.main p lam hlam χ hχ

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_eq_mul_twoVarZeta_slice_of_mem_principalSeries2 (solution)
