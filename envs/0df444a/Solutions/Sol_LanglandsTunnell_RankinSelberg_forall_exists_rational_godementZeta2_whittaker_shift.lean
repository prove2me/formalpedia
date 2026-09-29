-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3cce8479-d372-5875-9d0e-7edec17b70f8

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
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_AutomorphicForm_exists_forall_mem_of_isOpen_of_congruence
import Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rowSlice_twist_shellGauge_and_rationalTorusShell
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_godementZeta2_eq_mul_rsLocalIntegral_rowSlice
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_shift
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_shift
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace C1Red

section N2
variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem mem_range_unipotentGL2Hom_iff (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    g ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range ↔
      (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    change ((unipotentGL2 (Multiplicative.toAdd x) : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 = 1 ∧
      ((unipotentGL2 (Multiplicative.toAdd x) : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 ∧
      ((unipotentGL2 (Multiplicative.toAdd x) : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1
    simp [unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1), ?_⟩
    apply Units.ext
    change ((unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  have hset : ((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0) ⁻¹' {1} ∩
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0) ⁻¹' {0} ∩
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, mem_range_unipotentGL2Hom_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, and_assoc]
  rw [hset]
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j := fun i j =>
    (Continuous.matrix_elem Units.continuous_val i j)
  exact ((isClosed_singleton.preimage (hc 0 0)).inter (isClosed_singleton.preimage (hc 1 0))).inter
    (isClosed_singleton.preimage (hc 1 1))

end N2

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (p.adicCompletion ℚ)
local notation "G2" => (GL (Fin 2) (p.adicCompletion ℚ))

theorem exists_uniformizer :
    ∃ ϖ : p.adicCompletionIntegers ℚ, algebraMap (p.adicCompletionIntegers ℚ) F ϖ ≠ 0 ∧
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) F ϖ) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer ℚ
  set x : F := (((WithVal.equiv (HeightOneSpectrum.valuation ℚ p)).symm π : WithVal (HeightOneSpectrum.valuation ℚ p)) : F) with hx
  have hv : Valued.v x = WithZero.exp (-1 : ℤ) := by
    rw [hx, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p π]; exact hπ
  have hmem : x ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by norm_num)
  refine ⟨⟨x, hmem⟩, ?_, ?_⟩
  · intro h0
    have : Valued.v x = 0 := by
      rw [show x = 0 from h0, Valuation.map_zero]
    rw [hv] at this; exact WithZero.exp_ne_zero this
  · exact hv

theorem isLocallyConstant_of_stab (w : G2 → ℂ) (U : Subgroup G2) (hU : IsOpen (U : Set G2))
    (hw : ∀ k ∈ U, ∀ g : G2, w (g * k) = w g) : IsLocallyConstant w := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hmem : g ∈ (fun h => g⁻¹ * h) ⁻¹' (U : Set G2) := by simp
  filter_upwards [(hU.preimage (continuous_const.mul continuous_id)).mem_nhds hmem] with h hh
  have := hw (g⁻¹ * h) hh g
  rw [mul_inv_cancel_left] at this
  exact this

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel in

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : NNReal) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : NNReal) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem unipotent_mul_unipotent (a b : F) : (unipotent a : G2) * unipotent b = unipotent (a + b) := by
  apply Units.ext
  change ((unipotentGL2 a : G2) : Matrix (Fin 2) (Fin 2) F) * ((unipotentGL2 b : G2) : Matrix (Fin 2) (Fin 2) F) =
    ((unipotentGL2 (a + b) : G2) : Matrix (Fin 2) (Fin 2) F)
  simp only [unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem det_unipotent_mul (a : F) (g : G2) :
    Matrix.GeneralLinearGroup.det ((unipotent a : G2) * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  have : Matrix.GeneralLinearGroup.det (unipotent a : G2) = 1 := by
    apply Units.ext
    change ((unipotentGL2 a : G2) : Matrix (Fin 2) (Fin 2) F).det = 1
    simp [unipotentGL2_coe, Matrix.det_fin_two]
  rw [this, one_mul]

end C1Red

open C1Red in
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
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∀ s₀ : ℂ,
          ∃ (P Q : Polynomial ℂ) (m : ℤ) (σ : ℝ), Q ≠ 0 ∧
            ∀ s : ℂ, σ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + s₀) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
  classical
  letI := localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := locallyCompactSpace_localGL ℚ p
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) := Units.isEmbedding_embedProduct.secondCountableTopology
  intro μ₂ _ w hw Φ hΦlc hΦcs s₀

  obtain ⟨ϖ, hπ, hϖ⟩ := C1Red.exists_uniformizer p
  haveI : LocallyCompactSpace ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range :=
    (C1Red.isClosed_range_unipotentGL2Hom p).locallyCompactSpace
  set μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range := Measure.haar with hμN₂

  obtain ⟨⟨Uw, hUwo, hUw⟩, hwlaw, hwcen, hwgr, hwrec⟩ :=
    AutomorphicForm.WhittakerModel.forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence p θ₀ N hN w₂base
      hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral hπ hϖ w hw
  have hwlc : IsLocallyConstant w := C1Red.isLocallyConstant_of_stab p w Uw hUwo hUw

  obtain ⟨hA, hAshell, hArat⟩ :=
    LanglandsTunnell.RankinSelberg.rowSlice_twist_shellGauge_and_rationalTorusShell p hπ hϖ Φ hΦlc hΦcs χ hχ

  obtain ⟨b, hb⟩ := AutomorphicForm.exists_forall_mem_of_isOpen_of_congruence p Uw hUwo
  have hK0 := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (⊤ : Ideal (𝓞 ℚ)) (by simp)).2
  set Kb : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ⊓ Uw with hKb
  have hKbo : IsOpen (Kb : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
    rw [hKb, Subgroup.coe_inf]; exact hK0.inter hUwo
  have hKbK : Kb ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by rw [hKb]; exact inf_le_left
  have hKbc : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) i j) ≤
        WithZero.exp (-(b : ℤ))) → k ∈ Kb := by
    intro k hk hc; rw [hKb]; exact ⟨hk, hb k hk hc⟩
  have hB : ∀ k ∈ Kb, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g := by
    intro k hk g; rw [hKb] at hk; exact hUw k hk.2 g

  have hAB : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (∫ y : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p y *
            Φ ((unipotent y * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) (unipotent x * g) * w (unipotent x * g) =
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (∫ y : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p y *
            Φ ((unipotent y * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) g * w g := by
    intro x g
    haveI := C1Red.isAddHaarMeasure_selfDualHaarAt p
    beta_reduce
    rw [C1Red.det_unipotent_mul, hwlaw]
    have hint : (∫ y : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p y *
        Φ ((unipotent y * (unipotent x * g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) =
        (NumberField.StandardAddChar.psiLocal ℚ p (-x) : ℂ) *
          ∫ y : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p y *
            Φ ((unipotent y * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p) := by
      rw [← integral_const_mul]
      rw [← integral_add_right_eq_self (μ := selfDualHaarAt ℚ p)
        (fun z : p.adicCompletion ℚ => (NumberField.StandardAddChar.psiLocal ℚ p (-x) : ℂ) *
          (NumberField.StandardAddChar.psiLocal ℚ p z * Φ ((unipotent z * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))) x]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      beta_reduce
      rw [← mul_assoc, C1Red.unipotent_mul_unipotent, ← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2; ring
    rw [hint]
    have h1 : (NumberField.StandardAddChar.psiLocal ℚ p (-x) : ℂ) * NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    calc _ = ((NumberField.StandardAddChar.psiLocal ℚ p (-x) : ℂ) * NumberField.StandardAddChar.psiLocal ℚ p x) *
          ((∫ y : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p y *
            Φ ((unipotent y * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * w g) := by ring
      _ = _ := by rw [h1, one_mul]

  obtain ⟨P, Q, m, σ₂, hQ, hRC⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
      p hπ hϖ b Kb hKbo hKbK hKbc
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
      w hA hB hAB hAshell (hArat b Kb hKbK) θ₀ hwcen hwgr hwrec μ₂ μN₂

  obtain ⟨κ, hκ, hR1⟩ := LanglandsTunnell.RankinSelberg.exists_pos_forall_godementZeta2_eq_mul_rsLocalIntegral_rowSlice p μ₂ μN₂
  obtain ⟨σI, hI⟩ := LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_shift p θ₀ N hN w₂base
    hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral χ hχ μ₂ w hw Φ hΦlc hΦcs s₀

  set c₀ : ℂ := (Ideal.absNorm p.asIdeal : ℂ) ^ (-(s₀ + 1 / 2)) with hc₀
  have hN0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
    have : (1 : ℕ) < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  refine ⟨Polynomial.C ((κ : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (s₀ + 1 / 2))) * P.comp (Polynomial.C c₀ * Polynomial.X),
    Q.comp (Polynomial.C c₀ * Polynomial.X), m, max σI (σ₂ - (s₀ + 1 / 2).re), ?_, ?_⟩
  ·
    intro h
    rw [Polynomial.comp_eq_zero_iff] at h
    rcases h with h | ⟨-, h2⟩
    · exact hQ h
    · have hc : c₀ ≠ 0 := by
        rw [hc₀]; intro h0; rw [Complex.cpow_eq_zero_iff] at h0; exact hN0 h0.1
      have h3 : (Polynomial.C c₀ * Polynomial.X).coeff 1 = (Polynomial.C ((Polynomial.C c₀ * Polynomial.X).coeff 0)).coeff 1 := by
        rw [← h2]
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one, Polynomial.coeff_C, if_neg one_ne_zero] at h3
      exact hc h3
  · intro s hs
    have hsI : σI < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₂ : σ₂ < (s + s₀ + 1 / 2).re := by
      have h := lt_of_le_of_lt (le_max_right _ _) hs
      have e1 : (s + s₀ + 1 / 2 : ℂ).re = s.re + s₀.re + 1 / 2 := by
        rw [Complex.add_re, Complex.add_re, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
      have e2 : (s₀ + 1 / 2 : ℂ).re = s₀.re + 1 / 2 := by
        rw [Complex.add_re, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
      rw [e1]; rw [e2] at h; linarith
    have h1 := hR1 w hwlc hwlaw Φ hΦlc hΦcs χ hχ (s + s₀) (hI s hsI)
    have h2 := (hRC (s + s₀ + 1 / 2) hs₂).2
    rw [h1]

    have e1 : (Polynomial.C c₀ * Polynomial.X).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ (-(s + s₀ + 1 / 2)) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hc₀, ← Complex.cpow_add _ _ hN0]
      congr 1; ring
    have e2 : (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (s + s₀ + 1 / 2)) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (s₀ + 1 / 2)) := by
      rw [← Complex.cpow_add _ _ hN0]; congr 1; ring
    rw [Polynomial.eval_comp, e1, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, e1, mul_assoc, h2, e2]
    ring

end S_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_shift
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_shift (solution)
