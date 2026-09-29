-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/80efd7b5-fa42-575f-8e87-ddf6cb8881e2

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
import Mathlib
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal Topology Filter
open scoped NNReal ENNReal Classical Pointwise

namespace ShellAverageEngine

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem isClosed_ball (k : ℤ) : IsClosed {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem isOpen_ball (k : ℤ) : IsOpen {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem sphere_eq_diff (k : ℤ) :
    {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k}
      = {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp k} \
          {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp (k - 1)} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨hy.le, fun h => ?_⟩
    rw [hy, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm]
    congr 1
    omega

theorem isClosed_sphere (k : ℤ) : IsClosed {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isClosed_ball v _).sdiff (isOpen_ball v _)

theorem isOpen_sphere (k : ℤ) : IsOpen {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isOpen_ball v _).sdiff (isClosed_ball v _)

theorem coe_integers_eq :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

theorem isCompact_ball_zero : IsCompact {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp 0} := by
  rw [← coe_integers_eq]
  exact isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)

theorem isCompact_units_setF : IsCompact {u : (v.adicCompletion K) | Valued.v u = 1} := by
  refine (isCompact_ball_zero v).of_isClosed_subset ?_ ?_
  · have := isClosed_sphere v 0
    rwa [WithZero.exp_zero] at this
  · intro u hu
    have hu' : Valued.v u = 1 := hu
    show Valued.v u ≤ WithZero.exp 0
    rw [hu', WithZero.exp_zero]

theorem isOpen_units_setF : IsOpen {u : (v.adicCompletion K) | Valued.v u = 1} := by
  have := isOpen_sphere v 0
  rwa [WithZero.exp_zero] at this

def USet : Set (v.adicCompletion K)ˣ := {u : (v.adicCompletion K)ˣ | Valued.v (u : (v.adicCompletion K)) = 1}

theorem image_val_USet : Units.val '' USet v = {u : (v.adicCompletion K) | Valued.v u = 1} := by
  ext x
  simp only [Set.mem_image, USet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hx
    have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)
    exact ⟨Units.mk0 x hx0, hx, rfl⟩

theorem isCompact_USet : IsCompact (USet v) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, image_val_USet]
  exact isCompact_units_setF v

theorem isOpen_USet : IsOpen (USet v) :=
  (isOpen_units_setF v).preimage Units.continuous_val

theorem continuous_diagOne :
    Continuous (diagOne : (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun t : (v.adicCompletion K)ˣ => Matrix.diagonal ![(t : v.adicCompletion K), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · change Continuous (fun t : (v.adicCompletion K)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first
        | exact continuous_const
        | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

scoped instance borelSpace_unitsKv : BorelSpace (v.adicCompletion K)ˣ := borelSpace_units

scoped instance measurableMul_unitsKv : MeasurableMul (v.adicCompletion K)ˣ := by infer_instance

theorem measurableSet_USet : MeasurableSet (USet v) := (isOpen_USet v).measurableSet

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

def mulHaar : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val (mulMeasure μ)

scoped instance isHaarMeasure_mulHaar : (mulHaar v μ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure K v μ

end Kv

theorem isAddHaarMeasure_selfDualHaarAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal K v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt K v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

section K0

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

theorem isLocalLevelOne_top_iff (m : Matrix (Fin 2) (Fin 2) F) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m ↔ ∀ i j, Valued.v (m i j) ≤ 1 := by
  constructor
  · intro h i j
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := p)).mp (h.integral i j)
  · intro h
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := p)).mpr (h i j), ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]; exact h 1 0
    · rw [AdelicLevel.idealBound_top]; exact Valuation.map_sub_le _ (h 1 1) (by simp)

theorem diagOne_mem_localLevelOne_top (u : Fˣ) (hu : Valued.v (u : F) = 1) :
    diagOne u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  rw [AdelicDock.mem_localLevelOne_iff, isLocalLevelOne_top_iff, isLocalLevelOne_top_iff, ← map_inv]
  have hu' : Valued.v (((u⁻¹ : Fˣ)) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  constructor
  · intro i j
    change Valued.v ((Matrix.diagonal ![(u : F), 1]) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hu]
  · intro i j
    change Valued.v ((Matrix.diagonal ![(((u⁻¹ : Fˣ)) : F), 1]) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Units.val_inv_eq_inv_val, map_inv₀, hu]

end K0

theorem diagUnitGL2_eq_diagOne {A : Type*} [CommRing A] (u : Aˣ) :
    LanglandsTunnell.CubicInduction.diagUnitGL2 u = diagOne u := by
  apply Units.ext
  ext i j
  rw [LanglandsTunnell.CubicInduction.coe_diagUnitGL2, NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem diagUnitGL2_eq_diagOne' {A : Type*} [CommRing A] :
    (LanglandsTunnell.CubicInduction.diagUnitGL2 : Aˣ → GL (Fin 2) A) = diagOne :=
  funext diagUnitGL2_eq_diagOne

end ShellAverageEngine
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant.ShellAverageEngine"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant.ShellAverageEngine"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical
open scoped NNReal ENNReal

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (F : GL (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant F →
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} ≠ 0 ∧
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} ≠ ⊤ ∧
      IntegrableOn F (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ ∧
      IntegrableOn (fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}, F (diagUnitGL2 u * k)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
        (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ ∧
      (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}).toReal : ℂ) *
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))), F k ∂μ₂ =
        ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}, F (diagUnitGL2 u * k)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂μ₂ := by
  intro μ₂ _ F hF
  letI igl : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  letI ims : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := ShellAverageEngine.isAddHaarMeasure_selfDualHaarAt ℚ p
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ p
  haveI : SecondCountableTopology (p.adicCompletion ℚ)ˣ := Units.isEmbedding_val₀.secondCountableTopology

  have hνeq : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ) =
      ShellAverageEngine.mulHaar p (selfDualHaarAt ℚ p) := rfl
  haveI hνHaar : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure := by
    rw [hνeq]; infer_instance
  have hUeq : ({u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}) = ShellAverageEngine.USet p := rfl
  have hUmeas : MeasurableSet {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := by
    rw [hUeq]; exact ShellAverageEngine.measurableSet_USet p
  have hUcpt : IsCompact {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := by
    rw [hUeq]; exact ShellAverageEngine.isCompact_USet p
  have hUopen : IsOpen {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := by
    rw [hUeq]; exact ShellAverageEngine.isOpen_USet p
  have hUfin : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} < ⊤ :=
    hUcpt.measure_lt_top
  have hUpos : 0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} :=
    hUopen.measure_pos _ ⟨1, by simp⟩
  obtain ⟨hK0c, hK0o⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot

  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), K₀ = AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (p.adicCompletion ℚ)ˣ, ν = Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Set (p.adicCompletion ℚ)ˣ, U = {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} := ⟨_, rfl⟩
  rw [← hK₀] at hK0c hK0o
  rw [← hν, ← hU] at hUfin hUpos
  rw [← hU] at hUmeas hUcpt hUopen
  haveI hνH : ν.IsHaarMeasure := by rw [hν]; exact hνHaar
  have hK0meas : MeasurableSet (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hK0o.measurableSet
  have hK0fin : μ₂ (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))) < ⊤ := hK0c.measure_lt_top
  have hUmem : ∀ u : (p.adicCompletion ℚ)ˣ, u ∈ U ↔ Valued.v (u : p.adicCompletion ℚ) = 1 := fun u => by rw [hU]; rfl
  have hcontD : Continuous (diagUnitGL2 : (p.adicCompletion ℚ)ˣ → GL (Fin 2) (p.adicCompletion ℚ)) := by
    rw [ShellAverageEngine.diagUnitGL2_eq_diagOne']
    exact ShellAverageEngine.continuous_diagOne p
  have hdiagK : ∀ u ∈ U, diagUnitGL2 u ∈ K₀ := fun u hu => by
    rw [hK₀, ShellAverageEngine.diagUnitGL2_eq_diagOne]
    exact ShellAverageEngine.diagOne_mem_localLevelOne_top p u ((hUmem u).mp hu)
  have hFc : Continuous F := hF.continuous

  have hIF : IntegrableOn F (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ := by
    obtain ⟨B, hB⟩ := hK0c.exists_bound_of_continuousOn hFc.continuousOn
    refine Measure.integrableOn_of_bounded (M := B) hK0fin.ne hFc.measurable.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hK0meas]
    exact Filter.Eventually.of_forall fun k hk => hB k hk

  have hinv : ∀ u ∈ U, ∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), F (diagUnitGL2 u * k) ∂μ₂ =
      ∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), F k ∂μ₂ := by
    intro u hu
    have hdu : diagUnitGL2 u ∈ K₀ := hdiagK u hu
    rw [← integral_indicator hK0meas, ← integral_indicator hK0meas]
    have hfun : (fun k => (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))).indicator
          (fun k => F (diagUnitGL2 u * k)) k) =
        fun k => (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))).indicator F (diagUnitGL2 u * k) := by
      funext k
      have hiff : diagUnitGL2 u * k ∈ (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))) ↔
          k ∈ (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
        simp only [SetLike.mem_coe]
        exact ⟨fun h => by simpa using K₀.mul_mem (K₀.inv_mem hdu) h, fun h => K₀.mul_mem hdu h⟩
      by_cases hk : k ∈ (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ)))
      · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (hiff.mpr hk)]
      · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem (fun h => hk (hiff.mp h))]
    rw [hfun]
    exact integral_mul_left_eq_self _ (diagUnitGL2 u)

  haveI : IsFiniteMeasure (ν.restrict U) := ⟨by rw [Measure.restrict_apply_univ]; exact hUfin⟩
  haveI : IsFiniteMeasure (μ₂.restrict (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK0fin⟩
  have hcontH : Continuous fun q : (p.adicCompletion ℚ)ˣ × GL (Fin 2) (p.adicCompletion ℚ) => F (diagUnitGL2 q.1 * q.2) :=
    hFc.comp ((hcontD.comp continuous_fst).mul continuous_snd)
  obtain ⟨Cb, hCb⟩ := (hUcpt.prod hK0c).exists_bound_of_continuousOn hcontH.continuousOn
  have hInt : Integrable (fun q : (p.adicCompletion ℚ)ˣ × GL (Fin 2) (p.adicCompletion ℚ) => F (diagUnitGL2 q.1 * q.2))
      ((ν.restrict U).prod (μ₂.restrict (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))))) := by
    refine Integrable.mono' (integrable_const Cb) hcontH.measurable.aestronglyMeasurable ?_
    have hmem : ∀ᵐ q ∂((ν.restrict U).prod (μ₂.restrict (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))))),
        q ∈ U ×ˢ (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem (hUmeas.prod hK0meas)]
      filter_upwards [ae_restrict_mem hUmeas] with u hu
      filter_upwards [ae_restrict_mem hK0meas] with k hk
      exact ⟨hu, hk⟩
    filter_upwards [hmem] with q hq
    exact hCb q hq

  have hIavg : IntegrableOn (fun k : GL (Fin 2) (p.adicCompletion ℚ) => ∫ u in U, F (diagUnitGL2 u * k) ∂ν)
      (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ :=
    hInt.integral_prod_right

  have hT : ∫ u in U, (∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), F k ∂μ₂) ∂ν =
      ∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), (∫ u in U, F (diagUnitGL2 u * k) ∂ν) ∂μ₂ := by
    calc ∫ u in U, (∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), F k ∂μ₂) ∂ν
        = ∫ u in U, (∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), F (diagUnitGL2 u * k) ∂μ₂) ∂ν :=
          setIntegral_congr_fun hUmeas fun u hu => (hinv u hu).symm
      _ = ∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), (∫ u in U, F (diagUnitGL2 u * k) ∂ν) ∂μ₂ :=
          integral_integral_swap hInt
  have hmain : ((ν U).toReal : ℂ) * ∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), F k ∂μ₂ =
      ∫ k in (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))), (∫ u in U, F (diagUnitGL2 u * k) ∂ν) ∂μ₂ := by
    rw [← hT, setIntegral_const, Complex.real_smul]
    rfl
  subst hK₀ hν hU
  exact ⟨hUpos.ne', hUfin.ne, hIF, hIavg, hmain⟩

end S_LanglandsTunnell_RankinSelberg_setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant (solution)
