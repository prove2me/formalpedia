-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiJointPopulationMeasurableVersion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T16:09:07.360739+00:00
-- url     : https://prove2.me/submissions/56b66611-caea-4712-a1cd-7de9c6649bb9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveJointIntegerProcessVersion
import Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveFirstNegativePassageVersion
import Theorems.Thm_Kyprianou_Ch01_measurableReciprocalOccupationFromJointIntegerProcess
import Theorems.Thm_Kyprianou_Ch01_measurableJointInverseReciprocalOccupationFromSections
import Theorems.Thm_Kyprianou_Ch01_measurableWithTopIntegerRandomTimeEvaluation
import Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationPathwiseCongr
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false


theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    :
    ∀ z : ℕ, ∃ Z : ℝ≥0 → Ω → ℕ,
      Measurable (fun v : ℝ≥0 × Ω => Z v.1 v.2) ∧
      ∀ u : ℝ≥0, ∀ᵐ ω ∂Q,
        Z u ω =
          (compoundPoissonToBranching
            (integerCompoundPoisson z arrival marks) u ω).toNat := by
  intro z
  let X : ℝ≥0 → Ω → ℤ := integerCompoundPoisson z arrival marks
  obtain ⟨W, hWjoint, hWeq⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveJointIntegerProcessVersion
      Q rate hrate arrival marks jumpLaw hdriver z
  obtain ⟨V, hVmeas, hVeq⟩ :=
    Kyprianou.Ch01.reverseLampertiNonexplosiveFirstNegativePassageVersion
      Q rate hrate arrival marks jumpLaw hdriver z
  have hOccMeas (s : ℝ≥0) :
      Measurable (fun w : Ω => reciprocalOccupation W s w) :=
    Kyprianou.Ch01.measurableReciprocalOccupationFromJointIntegerProcess
      W hWjoint s
  have hUjoint : Measurable
      (fun v : ℝ≥0 × Ω =>
        inverseReciprocalOccupation W v.1 v.2) :=
    Kyprianou.Ch01.measurableJointInverseReciprocalOccupationFromSections
      W hOccMeas
  let T : ℝ≥0 × Ω → WithTop ℝ≥0 :=
    fun v => min (inverseReciprocalOccupation W v.1 v.2) (V v.2)
  have hTjoint : Measurable T :=
    hUjoint.min (hVmeas.comp measurable_snd)
  let F : ℝ≥0 → (ℝ≥0 × Ω) → ℤ :=
    fun s v => W s v.2
  have hFjoint : Measurable
      (fun v : ℝ≥0 × (ℝ≥0 × Ω) =>
        F v.1 v.2) := by
    have hDrop : Measurable
        (fun v : ℝ≥0 × (ℝ≥0 × Ω) =>
          (v.1, v.2.2)) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    exact hWjoint.comp hDrop
  let Z : ℝ≥0 → Ω → ℕ :=
    fun u w =>
      (if T (u, w) = ⊤ then (0 : ℤ)
       else W ((T (u, w)).untopD 0) w).toNat
  have hZjoint : Measurable
      (fun v : ℝ≥0 × Ω => Z v.1 v.2) := by
    change Measurable
      (fun v : ℝ≥0 × Ω =>
        (if T v = ⊤ then (0 : ℤ)
         else F ((T v).untopD 0) v).toNat)
    exact Kyprianou.Ch01.measurableWithTopIntegerRandomTimeEvaluation
      F hFjoint T hTjoint
  refine ⟨Z, hZjoint, ?_⟩
  intro u
  filter_upwards [hWeq, hVeq] with w hpath hpass
  have hInv (v : ℝ≥0) :
      inverseReciprocalOccupation W v w =
        inverseReciprocalOccupation X v w :=
    Kyprianou.Ch01.inverseReciprocalOccupationPathwiseCongr
      W X w hpath v
  have hClock : T (u, w) =
      min (inverseReciprocalOccupation X u w)
        (firstNegativePassage X w) := by
    dsimp [T]
    rw [hInv u, hpass]
  change
    (if T (u, w) = ⊤ then (0 : ℤ)
     else W ((T (u, w)).untopD 0) w).toNat =
      (compoundPoissonToBranching X u w).toNat
  rw [hClock]
  unfold compoundPoissonToBranching
  cases h : min (inverseReciprocalOccupation X u w)
      (firstNegativePassage X w) with
  | top => simp [h]
  | coe s =>
      simp only [h]
      rw [if_neg (WithTop.coe_ne_top : (s : WithTop ℝ≥0) ≠ ⊤),
        WithTop.untopD_coe]
      exact congrArg Int.toNat (hpath s)
