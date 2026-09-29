-- Prove2me | solution 1 for MarkovChainCLT.uniformly_ergodic_iff_phi_mixing_ae
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:44:31.168118+00:00
-- url     : https://prove2.me/submissions/958399b0-c30b-47b0-a44b-fc6136bbc74b

import Definitions.Def_MarkovIterKernel
import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Invariance
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist_of_bounded
import Theorems.Thm_MarkovChainCLT_condExp_coord_add
import Theorems.Thm_MarkovChainCLT_exists_countable_isSetRing_generateFrom
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_measurable_tvDist_kernel
import Theorems.Thm_MarkovChainCLT_tvDist_le_sSup_of_isSetRing
import Theorems.Thm_MarkovChainCLT_uniformlyErgodic_phiMixing_exp
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NumberPhiIndicator

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ)
    (A B : Set Ω)
    (hA : MeasurableSet[processSigma Y (Set.Iic k)] A)
    (hA0 : P A ≠ 0)
    (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) :
    |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ phiMixingCoef P Y n := by
  -- Key element of the phi-sup
  have hPA_fin : P A ≠ ⊤ := measure_ne_top P A
  have hPA_pos : 0 < (P A).toReal := ENNReal.toReal_pos hA0 hPA_fin
  have hPA_le_one : (P A).toReal ≤ 1 := by
    have h : P A ≤ 1 := by
      calc P A ≤ P Set.univ := measure_mono (Set.subset_univ A)
        _ = 1 := measure_univ
    exact ENNReal.toReal_mono (by simp) h
  have hPA_nonneg : 0 ≤ (P A).toReal := ENNReal.toReal_nonneg
  -- the phi-element for our k, A, B
  have hmem : |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal| ∈
      {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
        MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
        MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
        r = |(P (A' ∩ B')).toReal / (P A').toReal - (P B').toReal|} :=
    ⟨k, A, B, hA, hA0, hB, rfl⟩
  -- boundedness of the phi-set by 1
  have hbdd : BddAbove
      {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
        MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
        MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
        r = |(P (A' ∩ B')).toReal / (P A').toReal - (P B').toReal|} := by
    use 1
    intro r hr
    obtain ⟨k', A', B', _, hA'0, _, rfl⟩ := hr
    have h1 : (P B').toReal ≤ 1 := by
      have h : P B' ≤ 1 := by
        calc P B' ≤ P Set.univ := measure_mono (Set.subset_univ B')
          _ = 1 := measure_univ
      exact ENNReal.toReal_mono (by simp) h
    have h2 : (P (A' ∩ B')).toReal / (P A').toReal ≤ 1 := by
      have hsub : P (A' ∩ B') ≤ P A' := measure_mono Set.inter_subset_left
      have hle : (P (A' ∩ B')).toReal ≤ (P A').toReal :=
        ENNReal.toReal_mono (measure_ne_top P _) hsub
      have hpos : 0 < (P A').toReal := ENNReal.toReal_pos hA'0 (measure_ne_top P _)
      rw [div_le_one hpos]
      exact hle
    have hnn1 : 0 ≤ (P B').toReal := ENNReal.toReal_nonneg
    have hnn2 : 0 ≤ (P (A' ∩ B')).toReal / (P A').toReal := by positivity
    -- |a - b| ≤ 1 for a,b ∈ [0,1]
    rw [abs_le]
    constructor <;> linarith
  have hle : |(P (A ∩ B)).toReal / (P A).toReal - (P B).toReal| ≤ phiMixingCoef P Y n := by
    unfold phiMixingCoef
    exact le_csSup hbdd hmem
  -- factor (P A).toReal
  have hfactor : (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal =
      (P A).toReal * ((P (A ∩ B)).toReal / (P A).toReal - (P B).toReal) := by
    field_simp
  rw [hfactor, abs_mul]
  have hPA_abs : |(P A).toReal| = (P A).toReal := abs_of_nonneg hPA_nonneg
  rw [hPA_abs]
  calc (P A).toReal * |((P (A ∩ B)).toReal / (P A).toReal - (P B).toReal)|
      ≤ 1 * phiMixingCoef P Y n := by
        apply mul_le_mul hPA_le_one hle (abs_nonneg _) (by positivity)
    _ = phiMixingCoef P Y n := one_mul _

end NumberPhiIndicator
section PhiIffMain

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal ProbabilityTheory

namespace NumberPhiEvents

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

theorem nonneg (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    0 ≤ phiMixingCoef P Y n := by
  simpa using _root_.NumberPhiIndicator.solution P Y n 0 Set.univ Set.univ
    MeasurableSet.univ (by simp) MeasurableSet.univ

theorem conditional_diff_le_one (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) (hA : P A ≠ 0) :
    |P.real (A ∩ B) / P.real A - P.real B| ≤ 1 := by
  have hpos : 0 < P.real A := ENNReal.toReal_pos hA (measure_ne_top P A)
  have hratio : P.real (A ∩ B) / P.real A ≤ 1 := by
    apply (div_le_one hpos).mpr
    exact measureReal_mono Set.inter_subset_left (measure_ne_top P A)
  have hB : P.real B ≤ 1 := by
    simpa using measureReal_mono (Set.subset_univ B) (measure_ne_top P Set.univ)
  have hn : 0 ≤ P.real (A ∩ B) / P.real A := div_nonneg (measureReal_nonneg) (measureReal_nonneg)
  rw [abs_le]
  constructor <;> linarith [measureReal_nonneg (μ := P) (s := B)]

theorem weighted_event (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (n k : ℕ) (A B : Set Ω)
    (hA : MeasurableSet[processSigma Y (Set.Iic k)] A)
    (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) :
    |P.real (A ∩ B) - P.real A * P.real B| ≤ phiMixingCoef P Y n * P.real A := by
  by_cases hA0 : P A = 0
  · have hi : P (A ∩ B) = 0 := measure_mono_null Set.inter_subset_left hA0
    simp [measureReal_def, hA0, hi]
  have hbdd : BddAbove {r : ℝ | ∃ k' : ℕ, ∃ A' B' : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
      MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
      r = |P.real (A' ∩ B') / P.real A' - P.real B'|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨k', A', B', _, hA', _, rfl⟩
    exact conditional_diff_le_one P A' B' hA'
  have hr : |P.real (A ∩ B) / P.real A - P.real B| ≤ phiMixingCoef P Y n := by
    exact le_csSup hbdd ⟨k, A, B, hA, hA0, hB, rfl⟩
  have hpos : 0 < P.real A := ENNReal.toReal_pos hA0 (measure_ne_top P A)
  have hfactor : P.real (A ∩ B) - P.real A * P.real B =
      (P.real (A ∩ B) / P.real A - P.real B) * P.real A := by
    field_simp
  rw [hfactor, abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_right hr hpos.le

end NumberPhiEvents

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter Preorder
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace PhiTV

variable {X : Type*} [MeasurableSpace X]

theorem coord_measurable (s : Set ℕ) (i : ℕ) (hi : i ∈ s) :
    Measurable[processSigma (fun j (ω : ℕ → X) => ω j) s]
      (fun ω : ℕ → X => ω i) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

theorem setIntegral_transition (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (n : ℕ) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ x in A, (iterKernel P n x).real B ∂π =
      (chainMeasure P π).real
        ((fun ω : ℕ → X => ω 0) ⁻¹' A ∩ (fun ω : ℕ → X => ω n) ⁻¹' B) := by
  classical
  let ν := chainMeasure P π
  let g : X → ℝ := B.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hB
  have hgb : ∀ x, |g x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ B <;> simp [g, hx]
  have hintg (μ : Measure X) [IsFiniteMeasure μ] : Integrable g μ :=
    ⟨hg.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1)
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hgb x))⟩
  have hker : ∀ x, (∫ y, g y ∂iterKernel P n x) =
      (iterKernel P n x).real B := by
    intro x
    simp [g, integral_indicator hB]
  have hcond := condExp_coord_add P π g hg 1 hgb 0 n
  simp_rw [hker] at hcond
  simp only [zero_add] at hcond
  have hmle : MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) 0) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → X)) := (measurable_frestrictLe 0).comap_le
  haveI : IsFiniteMeasure (ν.trim hmle) := isFiniteMeasure_trim hmle
  have hcoord : Measurable[MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) 0) inferInstance]
      (fun ω : ℕ → X => ω 0) := by
    have hrest : Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) 0) inferInstance]
        (frestrictLe (π := fun _ : ℕ => X) 0) := Measurable.of_comap_le le_rfl
    exact (measurable_pi_apply (⟨0, by simp⟩ : Finset.Iic 0)).comp hrest
  have hgint : Integrable (fun ω : ℕ → X => g (ω n)) ν :=
    ⟨(hg.comp (measurable_pi_apply n)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1)
        (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hgb (ω n)))⟩
  have hset := setIntegral_condExp hmle hgint (hcoord hA)
  have hEq : ∫ ω in (fun ω : ℕ → X => ω 0) ⁻¹' A,
      (iterKernel P n (ω 0)).real B ∂ν =
      ∫ ω in (fun ω : ℕ → X => ω 0) ⁻¹' A, g (ω n) ∂ν := by
    exact (setIntegral_congr_ae (hA.preimage (measurable_pi_apply 0))
      (hcond.mono fun _ h _ => h)).trans hset
  have hmap := setIntegral_map (μ := ν) hA
    ((Kernel.measurable_coe (iterKernel P n) hB).ennreal_toReal.aestronglyMeasurable)
    (measurable_pi_apply 0).aemeasurable
  rw [map_coord_chainMeasure P π hinv 0] at hmap
  change (∫ y in A, (iterKernel P n y).real B ∂π) =
    ∫ ω in (fun ω : ℕ → X => ω 0) ⁻¹' A, (iterKernel P n (ω 0)).real B ∂ν at hmap
  rw [hmap, hEq]
  have hfun : (fun ω : ℕ → X => g (ω n)) =
      ((fun ω : ℕ → X => ω n) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    simp [g, Set.indicator_apply]
  have hBm : MeasurableSet ((fun ω : ℕ → X => ω n) ⁻¹' B) :=
    hB.preimage (measurable_pi_apply n)
  rw [hfun, integral_indicator hBm]
  simp [Measure.restrict_apply hBm, Set.inter_comm, measureReal_def, ν]

theorem ae_event_bound (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (n : ℕ) (B : Set X) (hB : MeasurableSet B) :
    ∀ᵐ x ∂π, |(iterKernel P n x).real B - π.real B| ≤
      phiMixingCoef (chainMeasure P π) (fun i ω => ω i) n := by
  let φ := phiMixingCoef (chainMeasure P π) (fun i ω => ω i) n
  let f : X → ℝ := fun x => (iterKernel P n x).real B - π.real B
  have hfmeas : Measurable f :=
    (Kernel.measurable_coe (iterKernel P n) hB).ennreal_toReal.sub measurable_const
  have hfint : Integrable f π := by
    apply Integrable.sub _ (integrable_const _)
    exact ⟨(Kernel.measurable_coe (iterKernel P n) hB).ennreal_toReal.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        simpa using measureReal_mono (Set.subset_univ B)
          (measure_ne_top (iterKernel P n x) Set.univ)))⟩
  have hset (A : Set X) (hA : MeasurableSet A) :
      |∫ x in A, f x ∂π| ≤ φ * π.real A := by
    have he := NumberPhiEvents.weighted_event (chainMeasure P π) (fun i ω => ω i) n 0
      ((fun ω : ℕ → X => ω 0) ⁻¹' A) ((fun ω : ℕ → X => ω n) ⁻¹' B)
      (coord_measurable (Set.Iic 0) 0 (by simp) hA)
      (coord_measurable (Set.Ici (0 + n)) n (by simp) hB)
    have hreal (j : ℕ) (S : Set X) (hS : MeasurableSet S) :
        (chainMeasure P π).real ((fun ω : ℕ → X => ω j) ⁻¹' S) = π.real S := by
      rw [measureReal_def, ← Measure.map_apply (measurable_pi_apply j) hS,
        map_coord_chainMeasure P π hinv j]
      rfl
    rw [hreal 0 A hA, hreal n B hB, ← setIntegral_transition P π hinv n A B hA hB] at he
    have hkint : Integrable (fun x => (iterKernel P n x).real B) π :=
      hfint.add (integrable_const (π.real B)) |>.congr (ae_of_all _ (fun x => by simp [f]))
    simpa [f, integral_sub hkint.integrableOn (integrable_const (π.real B)), mul_comm] using he
  have hu : f ≤ᵐ[π] fun _ => φ := by
    apply ae_le_of_forall_setIntegral_le hfint (integrable_const _)
    intro A hA _
    simpa [mul_comm] using (le_abs_self (∫ x in A, f x ∂π)).trans (hset A hA)
  have hl : (fun _ => -φ) ≤ᵐ[π] f := by
    apply ae_le_of_forall_setIntegral_le (integrable_const _) hfint
    intro A hA _
    have hh := (abs_le.mp (hset A hA)).1
    simpa [mul_comm] using hh
  filter_upwards [hu, hl] with x hx hy
  exact abs_le.mpr ⟨hy, hx⟩

theorem ae_tv_bound [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (n : ℕ) :
    ∀ᵐ x ∂π, tvDist (iterKernel P n x) π ≤
      phiMixingCoef (chainMeasure P π) (fun i ω => ω i) n := by
  obtain ⟨C, hCcount, hCring, hCm, hCuniv, hCgen⟩ :=
    MarkovChainCLT.exists_countable_isSetRing_generateFrom (X := X)
  have hCae : ∀ᵐ x ∂π, ∀ B ∈ C, |(iterKernel P n x).real B - π.real B| ≤
      phiMixingCoef (chainMeasure P π) (fun i ω => ω i) n := by
    exact (ae_ball_iff hCcount).mpr (fun B hBC => ae_event_bound P π hinv n B (hCm B hBC))
  filter_upwards [hCae] with x hx
  have hcov : ∃ D : Set (Set X), D.Countable ∧ D ⊆ C ∧
      ((iterKernel P n x) + π) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, by simpa using hCuniv, ?_⟩
    simp
  refine (MarkovChainCLT.tvDist_le_sSup_of_isSetRing (iterKernel P n x) π C hCring hCm hcov hCgen.symm).trans ?_
  apply csSup_le
  · exact ⟨0, Set.univ, hCuniv, by simp⟩
  · rintro r ⟨B, hBC, rfl⟩
    exact hx B hBC

end PhiTV

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal

namespace AEKernelContraction

variable {X : Type*} [MeasurableSpace X]

theorem abs_prob_diff_le_one (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set X) : |μ.real A - ν.real A| ≤ 1 := by
  have hμ : μ.real A ≤ 1 := by
    simpa using measureReal_mono (Set.subset_univ A) (measure_ne_top μ Set.univ)
  have hν : ν.real A ≤ 1 := by
    simpa using measureReal_mono (Set.subset_univ A) (measure_ne_top ν Set.univ)
  rw [abs_le]
  constructor <;> linarith [measureReal_nonneg (μ := μ) (s := A),
    measureReal_nonneg (μ := ν) (s := A)]

theorem tv_bddAbove (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove {r : ℝ | ∃ A : Set X, MeasurableSet A ∧
      r = |(μ A).toReal - (ν A).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, _, rfl⟩
  exact abs_prob_diff_le_one μ ν A

theorem tv_nonneg (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ tvDist μ ν :=
  le_csSup (tv_bddAbove μ ν) ⟨∅, MeasurableSet.empty, by simp⟩

theorem abs_measure_sub_le_tv (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set X) (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ tvDist μ ν :=
  le_csSup (tv_bddAbove μ ν) ⟨A, hA, rfl⟩

theorem integral_kernel_measure (K : Kernel X X) [IsMarkovKernel K]
    (ρ : Measure X) [IsProbabilityMeasure ρ] (A : Set X) (hA : MeasurableSet A) :
    (∫ y, ((K y) A).toReal ∂ρ) = ((K ∘ₘ ρ) A).toReal := by
  rw [Measure.bind_apply hA K.aemeasurable]
  apply integral_toReal (K.measurable_coe hA).aemeasurable
  filter_upwards with y
  exact measure_lt_top (K y) A

theorem tv_comp_le (Q K : Kernel X X) [IsMarkovKernel Q] [IsMarkovKernel K]
    (π : Measure X) [IsProbabilityMeasure π]
    (hQinv : Kernel.Invariant Q π) (hKinv : Kernel.Invariant K π)
    (C : ℝ) (hC : 0 ≤ C) (hK : ∀ᵐ y ∂π, tvDist (K y) π ≤ C) :
    ∀ᵐ x ∂π, tvDist ((K ∘ₖ Q) x) π ≤ 2 * C * tvDist (Q x) π := by
  change Q ∘ₘ π = π at hQinv
  change K ∘ₘ π = π at hKinv
  have hgood : ∀ᵐ x ∂π, ∀ᵐ y ∂Q x, tvDist (K y) π ≤ C := by
    apply Measure.ae_ae_of_ae_comp
    simpa only [hQinv] using hK
  filter_upwards [hgood] with x hx
  have hbound0 : 0 ≤ 2 * C * tvDist (Q x) π :=
    mul_nonneg (mul_nonneg (by norm_num) hC) (tv_nonneg (Q x) π)
  refine Real.sSup_le ?_ hbound0
  rintro r ⟨A, hA, rfl⟩
  let g : X → ℝ := fun y => ((K y) A).toReal - π.real A
  let gc : X → ℝ := fun y => max (-C) (min C (g y))
  have hgm : Measurable g := (K.measurable_coe hA).ennreal_toReal.sub measurable_const
  have hgcm : Measurable gc := measurable_const.max (measurable_const.min hgm)
  have hgcb (y : X) : |gc y| ≤ C := by
    apply abs_le.2
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have heq (y : X) (hy : tvDist (K y) π ≤ C) : gc y = g y := by
    have habs : |g y| ≤ C := (abs_measure_sub_le_tv (K y) π A hA).trans hy
    change max (-C) (min C (g y)) = g y
    rw [min_eq_right (abs_le.mp habs).2, max_eq_right (abs_le.mp habs).1]
  have hgcπ : gc =ᵐ[π] g := hK.mono fun y hy => heq y hy
  have hgcQ : gc =ᵐ[Q x] g := hx.mono fun y hy => heq y hy
  have hraw (ρ : Measure X) [IsProbabilityMeasure ρ] :
      Integrable (fun y => ((K y) A).toReal) ρ := by
    apply Integrable.of_bound (K.measurable_coe hA).ennreal_toReal.aestronglyMeasurable 1
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one : K y A ≤ 1))
  have hint (ρ : Measure X) [IsProbabilityMeasure ρ] :
      (∫ y, g y ∂ρ) = ((K ∘ₘ ρ) A).toReal - π.real A := by
    rw [integral_sub (hraw ρ) (integrable_const _), integral_kernel_measure K ρ A hA]
    simp
  have hmean : (∫ y, g y ∂π) = 0 := by
    rw [hint π, hKinv]
    simp only [measureReal_def, sub_self]
  have h := abs_integral_sub_le_tvDist_of_bounded (Q x) π gc hgcm C hC hgcb
  rw [integral_congr_ae hgcQ, integral_congr_ae hgcπ, hmean, sub_zero, hint (Q x)] at h
  exact h

end AEKernelContraction

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal

namespace AEGeometricRate

variable {X : Type*} [MeasurableSpace X]

theorem iter_invariant (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (n : ℕ) :
    Kernel.Invariant (iterKernel P n) π := by
  change iterKernel P n ∘ₘ π = π
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterKernel_succ, ← Measure.comp_assoc, ih]
    exact hinv

theorem iter_add (P : Kernel X X) [IsMarkovKernel P] (n m : ℕ) :
    iterKernel P (n + m) = iterKernel P n ∘ₖ iterKernel P m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, iterKernel_succ, ih, iterKernel_succ, Kernel.comp_assoc]

theorem tv_le_one (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := by
  refine Real.sSup_le ?_ (by norm_num)
  rintro r ⟨A, _, rfl⟩
  exact AEKernelContraction.abs_prob_diff_le_one μ ν A

theorem block_bound (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (N : ℕ) (hN : ∀ᵐ x ∂π, tvDist (iterKernel P N x) π ≤ 1 / 4)
    (q r : ℕ) :
    ∀ᵐ x ∂π, tvDist (iterKernel P (q * N + r) x) π ≤ (1 / 2 : ℝ) ^ q := by
  induction q with
  | zero => exact ae_of_all _ (fun x => by simpa using tv_le_one (iterKernel P r x) π)
  | succ q ih =>
    have hc := AEKernelContraction.tv_comp_le (iterKernel P (q * N + r)) (iterKernel P N)
      π (iter_invariant P π hinv _) (iter_invariant P π hinv _) (1 / 4) (by norm_num) hN
    have hidx : (q + 1) * N + r = N + (q * N + r) := by ring
    rw [← iter_add, ← hidx] at hc
    filter_upwards [hc, ih] with x hx hi
    calc
      tvDist (iterKernel P ((q + 1) * N + r) x) π
          ≤ 2 * (1 / 4) * tvDist (iterKernel P (q * N + r) x) π := hx
      _ ≤ 2 * (1 / 4) * (1 / 2 : ℝ) ^ q := mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = (1 / 2 : ℝ) ^ (q + 1) := by rw [pow_succ]; ring

theorem exists_rate_of_lag (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (N : ℕ) (hNpos : 1 ≤ N)
    (hN : ∀ᵐ x ∂π, tvDist (iterKernel P N x) π ≤ 1 / 4) :
    ∃ R t : ℝ, 0 ≤ R ∧ 0 ≤ t ∧ t < 1 ∧
      ∀ᵐ x ∂π, ∀ n : ℕ, 1 ≤ n → tvDist (iterKernel P n x) π ≤ R * t ^ n := by
  let t : ℝ := (1 / 2 : ℝ) ^ ((N : ℝ)⁻¹)
  have hN0 : N ≠ 0 := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN0)
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have ht1 : t < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (inv_pos.mpr hNr)
  have htpow : t ^ N = 1 / 2 := Real.rpow_inv_natCast_pow (by norm_num) hN0
  have hnum (n : ℕ) : (1 / 2 : ℝ) ^ (n / N) ≤ 2 * t ^ n := by
    have hr : n % N ≤ N := (Nat.mod_lt n (Nat.pos_of_ne_zero hN0)).le
    have hrem : 1 / 2 ≤ t ^ (n % N) := by
      rw [← htpow]
      exact pow_le_pow_of_le_one ht.le ht1.le hr
    have hdecomp : n / N * N + n % N = n := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod n N
    have hp : t ^ n = (1 / 2 : ℝ) ^ (n / N) * t ^ (n % N) := by
      conv_lhs => rw [← hdecomp]
      rw [pow_add, mul_comm (n / N) N, pow_mul, htpow]
    rw [hp]
    have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ (n / N) := by positivity
    nlinarith
  refine ⟨2, t, by norm_num, ht.le, ht1, ?_⟩
  have hb : ∀ n : ℕ, ∀ᵐ x ∂π,
      tvDist (iterKernel P n x) π ≤ (1 / 2 : ℝ) ^ (n / N) := by
    intro n
    have hh := block_bound P π hinv N hN (n / N) (n % N)
    simpa only [Nat.mul_comm (n / N) N, Nat.div_add_mod] using hh
  filter_upwards [ae_all_iff.mpr hb] with x hx
  intro n _
  exact (hx n).trans (hnum n)

end AEGeometricRate

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π) :
    (MarkovChainCLT.UniformlyErgodic P π →
        Tendsto (fun n => MarkovChainCLT.phiMixingCoef
          (MarkovChainCLT.chainMeasure P π) (fun i ω => ω i) n) atTop (𝓝 0))
    ∧ (Tendsto (fun n => MarkovChainCLT.phiMixingCoef
          (MarkovChainCLT.chainMeasure P π) (fun i ω => ω i) n) atTop (𝓝 0) →
        ∃ R t : ℝ, 0 ≤ R ∧ 0 ≤ t ∧ t < 1 ∧
          ∀ᵐ x ∂π, ∀ n : ℕ, 1 ≤ n →
            MarkovChainCLT.tvDist (MarkovChainCLT.iterKernel P n x) π ≤ R * t ^ n)
    ∧ (MarkovChainCLT.UniformlyErgodic P π → ∃ c θ : ℝ, 0 ≤ c ∧ 0 < θ ∧ ∀ n : ℕ, 1 ≤ n →
        MarkovChainCLT.phiMixingCoef (MarkovChainCLT.chainMeasure P π)
          (fun i ω => ω i) n ≤ c * Real.exp (-θ * n)) := by
  have hfwd := uniformlyErgodic_phiMixing_exp P π hP
  refine ⟨?_, ?_, hfwd⟩
  · intro huni
    obtain ⟨c, θ, _, hθ, hb⟩ := hfwd huni
    have hexp : Tendsto (fun n : ℕ => Real.exp (-θ * n)) atTop (𝓝 0) := by
      simpa only [neg_mul, Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hθ)
    have hlim := hexp.const_mul c
    simp only [mul_zero] at hlim
    apply squeeze_zero' (Eventually.of_forall (fun n => NumberPhiEvents.nonneg _ _ n)) _ hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact hb n hn
  · intro hmix
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hmix).2 (1 / 4) (by norm_num))
    let N' := max N 1
    have hN' : 1 ≤ N' := le_max_right _ _
    have hsmall := hN N' (le_max_left _ _)
    apply AEGeometricRate.exists_rate_of_lag P π hP.1 N' hN'
    filter_upwards [PhiTV.ae_tv_bound P π hP.1 N'] with x hx
    exact hx.trans hsmall.le

#print axioms solution

end PhiIffMain
#print axioms solution
