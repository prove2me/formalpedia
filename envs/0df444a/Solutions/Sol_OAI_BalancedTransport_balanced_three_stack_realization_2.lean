-- Prove2me | solution 2 for OAI.BalancedTransport.balanced_three_stack_realization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:02:43.115411+00:00
-- url     : https://prove2.me/submissions/14b5bbcc-0b7b-4d92-9384-e889d4e592bd

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MainResult.lean:L12-L83
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.BalancedTransport.balanced_three_stack_realization.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_BalancedTransport_balanced_three_stack_realization) verbatim and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveGluing
import Theorems.Thm_OAI_BalancedTransport_Analysis_unique_in_comparison
import Theorems.Thm_OAI_BalancedTransport_Coding_interval_eq_image
import Theorems.Thm_OAI_BalancedTransport_Coding_stream_mem_interior
import Theorems.Thm_OAI_BalancedTransport_Effectivity_ElementaryScalar_spaceD
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_differentiableAt
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_hasDerivAt
import Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_foldl
import Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_rat_pow
import Theorems.Thm_OAI_BalancedTransport_Effectivity_effectiveFamily_of_elementary_pieces
import Theorems.Thm_OAI_BalancedTransport_Effectivity_effective_affine_force
import Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_guarded_solid_box_motion
import Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_loadingVelocity
import Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_movingBoxVelocity
import Theorems.Thm_OAI_BalancedTransport_Effectivity_fieldArgs_time_hasDerivAt
import Theorems.Thm_OAI_BalancedTransport_Effectivity_loadingSupport_ball
import Theorems.Thm_OAI_BalancedTransport_FiniteMachine_normalized_halting_iff
import Theorems.Thm_OAI_BalancedTransport_Geometry_BoxLayout_separated_of_disjoint
import Theorems.Thm_OAI_BalancedTransport_Geometry_BoxMotion_path_guarded
import Theorems.Thm_OAI_BalancedTransport_Geometry_BoxMotion_velocity_collars
import Theorems.Thm_OAI_BalancedTransport_Geometry_BoxMotion_velocity_compact_support
import Theorems.Thm_OAI_BalancedTransport_Geometry_ForwardEq_mixedD
import Theorems.Thm_OAI_BalancedTransport_Geometry_boundedMixed_of_compact_repeating
import Theorems.Thm_OAI_BalancedTransport_Geometry_fullMixedD_eq_mixedD
import Theorems.Thm_OAI_BalancedTransport_Geometry_loadingVelocity_supported
import Theorems.Thm_OAI_BalancedTransport_Geometry_movingBoxVelocity_jointSmooth
import Theorems.Thm_OAI_BalancedTransport_Geometry_prescribed_residual_regularity
import Theorems.Thm_OAI_BalancedTransport_Geometry_repeatTemplate_eq
import Theorems.Thm_OAI_BalancedTransport_Geometry_repeatTemplate_jointSmooth
import Theorems.Thm_OAI_BalancedTransport_Recorder_Checkpoint_next_exec
import Theorems.Thm_OAI_BalancedTransport_Recorder_Checkpoint_rationalInitial_cast
import Theorems.Thm_OAI_BalancedTransport_Recorder_code_mem_observer_iff
import Theorems.Thm_OAI_BalancedTransport_Recorder_guarded_period_step
import Theorems.Thm_OAI_BalancedTransport_Recorder_source_boxes_disjoint
import Theorems.Thm_OAI_BalancedTransport_Recorder_target_boxes_disjoint

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RecorderRules ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Instruction
open Stream'
variable {Q Γ : Type*}

end BalancedTransport.Recorder.Instruction
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Row
open Stream'
variable {Q Γ : Type*}
open Control Letter

theorem balanced (M : Machine Q Γ) (r : Row Q Γ) :
    (r.instruction M).Balanced := by
  cases r <;> simp [instruction, Instruction.Balanced]

end BalancedTransport.Recorder.Row
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ]
open Letter Control

theorem source_separation (M : Machine Q Γ) {r s : Row Q Γ}
    (hr : r.valid M) (hs : s.valid M) {t u : Tails Q Γ}
    (he : (r.instruction M).source t = (s.instruction M).source u) : r = s ∧ t = u := by
  have hrs : r = s := by
    have hh := congrArg (sourceRow M) he
    simpa [sourceRow_source M r hr, sourceRow_source M s hs] using hh
  subst s
  exact ⟨rfl, by simpa using congrArg (Instruction.sourceTails (r.instruction M)) he⟩

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ]

theorem step_deterministic (M : Machine Q Γ) {c d e : Configuration Q Γ}
    (hd : Step M c d) (he : Step M c e) : d = e := by
  obtain ⟨r, hr, t, hrt, hrd⟩ := hd
  obtain ⟨s, hs, u, hsu, hse⟩ := he
  obtain ⟨rfl, rfl⟩ := source_separation M hr hs (hrt.symm.trans hsu)
  exact hrd.trans hse.symm

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} (M : Machine Q Γ)
open Letter Control

end BalancedTransport.Recorder
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.PrefixCoding ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*}

namespace Exec

variable {M : Machine Q Γ}

theorem single {source target : Configuration Q Γ} (step : Step M source target) :
    Exec M 1 source target :=
  .cons step (.refl target)

theorem trans {firstLength secondLength : ℕ} {source middle target : Configuration Q Γ}
    (first : Exec M firstLength source middle) (second : Exec M secondLength middle target) :
    Exec M (firstLength + secondLength) source target := by
  induction first with
  | refl => simpa using second
  | cons step _ inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Exec.cons step (inductionHypothesis second))

end Exec

variable (M : Machine Q Γ)
open Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

theorem stream_mem_unit {B : ℕ} (digit : S → Fin B) (s : Stream' S) :
    stream digit s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem prefix_mem_unit {r : ℝ} (hr : 0 ≤ r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (w : List S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    prefixPoint r digit w z ∈ Set.Icc (0 : ℝ) 1 := by
  induction w with
  | nil => simpa using hz
  | cons a w ih =>
      rw [prefix_cons]
      exact ⟨mul_nonneg hr (add_nonneg (hd₀ a) ih.1),
        (mul_le_mul_of_nonneg_left (show digit a + prefixPoint r digit w z ≤
          digit a + 1 by linarith [ih.2]) hr).trans (hd₁ a)⟩

theorem interval_subset_unit {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (w : List S) : interval r digit w ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [interval_eq_image hr]
  rintro _ ⟨z, hz, rfl⟩
  exact prefix_mem_unit hr.le digit hd₀ hd₁ w hz

end BalancedTransport.Coding
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.BoxCoding ----
namespace OAI

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Instruction
variable {Q Γ : Type*}

end BalancedTransport.Recorder.Instruction
end

noncomputable section
namespace BalancedTransport

theorem residual_zero_pressure_solution (ν : ℝ) (U : Velocity)
    (hU : Smooth U) (hzero : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    ZeroDataSolution ν (affineForce (inertialCoefficient U) (viscousCoefficient U) ν)
      U (fun _ _ => 0) := by
  refine ⟨hU, contDiffOn_const, hzero, hdiv, ?_⟩
  intro t ht x
  have hp : gradient (fun _ _ => 0) t x = 0 := by
    ext i
    simp [gradient, spaceD]
  rw [hp]
  simp only [affineForce, inertialCoefficient, viscousCoefficient, smul_neg, neg_zero, zero_add]
  abel

end BalancedTransport
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem oddDigit_pos {n : ℕ} (a : Fin n) : 0 < (oddDigit a : ℝ) := by
  dsimp [oddDigit]
  positivity

theorem oddDigit_upper {n : ℕ} (a : Fin n) :
    (oddDigit a : ℝ) + 1 < (2 * n + 1 : ℕ) := by
  have hh : (2 * a.val + 1) + 1 < 2 * n + 1 := by omega
  exact_mod_cast hh

theorem oddDigit_gap {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (oddDigit a : ℝ) + 1 < (oddDigit b : ℝ) ∨
      (oddDigit b : ℝ) + 1 < (oddDigit a : ℝ) := by
  have hv : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
  rcases lt_or_gt_of_ne hv with h | h
  · left
    have hh : (2 * a.val + 1) + 1 < 2 * b.val + 1 := by omega
    exact_mod_cast hh
  · right
    have hh : (2 * b.val + 1) + 1 < 2 * a.val + 1 := by omega
    exact_mod_cast hh

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}

theorem placement_positive [Fintype Q] [DecidableEq Q] (M : Machine Q Γ)
    (s : Control Q) (hs : s ≠ .ready M.halt) : 0 < placement M s := by simp [placement, hs]

theorem placement_injective [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) :
    Function.Injective (placement M) := by
  intro s t h
  by_cases hs : s = .ready M.halt <;> by_cases ht : t = .ready M.halt
  · exact hs.trans ht.symm
  · simp [placement, hs, ht] at h
  · simp [placement, hs, ht] at h
  · simp only [placement, hs, ht, ↓reduceIte, Nat.add_right_cancel_iff] at h
    exact (Fintype.equivFin (Control Q)).injective (Fin.ext h)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

theorem base_pos : 0 < base Q Γ := by simp [base]

theorem digit_pos (a : Letter Q Γ) : 0 < (digit a : ℝ) :=
  Coding.oddDigit_pos _

theorem digit_upper (a : Letter Q Γ) : (digit a : ℝ) + 1 < base Q Γ :=
  Coding.oddDigit_upper _

theorem digit_gap (a b : Letter Q Γ) (hab : a ≠ b) :
    (digit a : ℝ) + 1 < (digit b : ℝ) ∨ (digit b : ℝ) + 1 < (digit a : ℝ) :=
  Coding.oddDigit_gap _ _ (fun he => hab ((Fintype.equivFin _).injective he))

end BalancedTransport.Recorder
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Work ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pd_add (i : Fin 3) {f g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  simp only [pd, fderiv_fun_add hf hg, add_apply]

theorem pd_sub (i : Fin 3) {f g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp only [pd, fderiv_fun_sub hf hg, sub_apply]

theorem pd_mul (i : Fin 3) {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y * g y) x = f x * pd i g x + g x * pd i f x := by
  simp only [pd, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]

theorem pd_apply (i j : Fin 3) {f : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    pd i (fun y => f y j) x = pd i f x j := by
  simp only [pd, fderiv_apply hf, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

theorem pd_contDiff (i : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (pd i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem pd_comm (i j : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x
  have he (v : Space) : fderiv ℝ (fun y => fderiv ℝ f y v) x =
      (ContinuousLinearMap.apply ℝ F v) ∘L fderiv ℝ (fderiv ℝ f) x :=
    ((ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)
  simp only [he, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact hf.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) _ _

theorem divergence_curl {A : Space → Space} (hA : ContDiff ℝ (⊤ : ℕ∞) A) (x : Space) :
    divergence (curl A) x = 0 := by
  have he := contDiff_pi.mp hA
  have hd (i j : Fin 3) : DifferentiableAt ℝ (pd i (fun y => A y j)) x :=
    (pd_contDiff i (he j)).differentiable (by simp) x
  simp only [divergence, Fin.sum_univ_succ, curl, Matrix.cons_val_zero,
    Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  change (pd 0 (fun y => pd 1 (fun z => A z 2) y - pd 2 (fun z => A z 1) y) x) +
    ((pd 1 (fun y => pd 2 (fun z => A z 0) y - pd 0 (fun z => A z 2) y) x) +
    (pd 2 (fun y => pd 0 (fun z => A z 1) y - pd 1 (fun z => A z 0) y) x)) = 0
  rw [pd_sub _ (hd 1 2) (hd 2 1), pd_sub _ (hd 2 0) (hd 0 2),
    pd_sub _ (hd 0 1) (hd 1 0)]
  rw [pd_comm 0 1 (he 2), pd_comm 0 2 (he 1), pd_comm 1 2 (he 0)]
  ring

theorem curl_congr {A B : Space → Space} {x : Space}
    (h : A =ᶠ[𝓝 x] B) : curl A x = curl B x := by
  have he (j : Fin 3) : (fun y => A y j) =ᶠ[𝓝 x] (fun y => B y j) :=
    h.mono (fun _ hh => congrFun hh j)
  simp only [curl, pd, (he 0).fderiv_eq, (he 1).fderiv_eq, (he 2).fderiv_eq]

theorem tsupport_curl_subset (A : Space → Space) :
    tsupport (curl A) ⊆ tsupport A := by
  apply closure_minimal _ (isClosed_tsupport A)
  intro x hx
  by_contra hxA
  have hh : A =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxA
  have hz := curl_congr hh
  exact hx (by simpa using hz)

theorem affinePotential_contDiff (c v l : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (affinePotential c v l) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [affinePotential] <;> fun_prop

theorem curl_affinePotential (c v l : Space) (hl : ∑ i, l i = 0) (x : Space) :
    curl (affinePotential c v l) x = fun i => v i + l i * (x i - c i) := by
  have hl' : l 0 + l 1 + l 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hl
  funext i
  fin_cases i <;>
    simp (disch := fun_prop) [curl, affinePotential, pd_add, pd_sub, pd_mul, Pi.single_apply] <;>
    nlinarith [mul_eq_zero_of_left hl' (x 0 - c 0),
      mul_eq_zero_of_left hl' (x 1 - c 1), mul_eq_zero_of_left hl' (x 2 - c 2)]

theorem openEnlargement_isOpen (a b : Space) (η : ℝ) :
    IsOpen (openEnlargement a b η) := by
  exact isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem closedEnlargement_isCompact (a b : Space) (η : ℝ) :
    IsCompact (closedEnlargement a b η) := isCompact_Icc

theorem boxCutoff_contDiff (a b : Space) (η : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (boxCutoff a b η) := by
  unfold boxCutoff
  fun_prop

theorem boxCutoff_eq_one {a b : Space} {η : ℝ} (hη : 0 < η) {x : Space}
    (hx : x ∈ closedEnlargement a b η) : boxCutoff a b η x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  obtain ⟨hl, hr⟩ := (mem_closedEnlargement _ _ _ _).mp hx i
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith)), one_mul]

theorem boxCutoff_eventually_one {a b : Space} {η : ℝ} (hη : 0 < η)
    {x : Space} (hx : x ∈ openEnlargement a b η) :
    boxCutoff a b η =ᶠ[𝓝 x] 1 := by
  filter_upwards [(openEnlargement_isOpen a b η).mem_nhds hx] with y hy
  apply boxCutoff_eq_one hη
  exact (mem_closedEnlargement _ _ _ _).mpr fun i =>
    ⟨((mem_openEnlargement _ _ _ _).mp hy i).1.le,
      ((mem_openEnlargement _ _ _ _).mp hy i).2.le⟩

theorem boxCutoff_eq_zero {a b : Space} {η : ℝ} (hη : 0 < η) {x : Space}
    (hx : x ∉ closedEnlargement a b (2 * η)) : boxCutoff a b η x = 0 := by
  rw [mem_closedEnlargement] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hl : a i - 2 * η ≤ x i
  · have he : Real.smoothTransition ((b i + 2 * η - x i) / η) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith [hi hl]) hη.le)
    rw [he, mul_zero]
  · have he : Real.smoothTransition ((x i - a i + 2 * η) / η) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith) hη.le)
    rw [he, zero_mul]

theorem localizedAffine_divergence (a b c v l : Space) (η : ℝ) (x : Space) :
    divergence (localizedAffine a b c v l η) x = 0 :=
  divergence_curl ((boxCutoff_contDiff a b η).smul (affinePotential_contDiff c v l)) x

theorem localizedAffine_eq {a b c v l : Space} {η : ℝ} (hη : 0 < η)
    (hl : ∑ i, l i = 0) {x : Space} (hx : x ∈ openEnlargement a b η) :
    localizedAffine a b c v l η x = fun i => v i + l i * (x i - c i) := by
  unfold localizedAffine
  rw [curl_congr (show (fun y => boxCutoff a b η y • affinePotential c v l y) =ᶠ[𝓝 x]
      affinePotential c v l from (boxCutoff_eventually_one hη hx).mono
        (fun y hy => by simp only [hy, Pi.one_apply, one_smul])), curl_affinePotential c v l hl]

theorem tsupport_localizedAffine_subset (a b c v l : Space) {η : ℝ} (hη : 0 < η) :
    tsupport (localizedAffine a b c v l η) ⊆ closedEnlargement a b (2 * η) := by
  refine (tsupport_curl_subset _).trans ?_
  apply closure_minimal _ (closedEnlargement_isCompact _ _ _).isClosed
  intro x hx
  by_contra hn
  exact hx (by simp [boxCutoff_eq_zero hη hn])

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TimeRegularity ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem JointSmooth.spaceD {f : Field F} (hf : JointSmooth f) (i : Fin 3) :
    JointSmooth (spaceD i f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × Space => f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem divergence_eq_div {A : Velocity} (hA : JointSmooth A) (t : ℝ) (x : Space) :
    divergence (A t) x = div A t x := by
  apply Finset.sum_congr rfl
  intro i _
  exact pd_apply i i ((hA.slice t).differentiable (by simp) x)

lemma logarithmicRate_trace_zero {d : ℝ → Space} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (hdet : ∀ t, ∏ i, d t i = 1) (t : ℝ) :
    ∑ i, logarithmicRate d t i = 0 := by
  have dh (i : Fin 3) := ((contDiff_pi.mp hd i).differentiable (by simp) t).hasDerivAt
  have hconst : (fun s => d s 0 * d s 1 * d s 2) = fun _ => (1 : ℝ) := by
    funext s
    simpa [Fin.prod_univ_succ, mul_assoc] using hdet s
  have hh := ((dh 0).fun_mul (dh 1)).fun_mul (dh 2)
  rw [hconst] at hh
  have hz := hh.unique (hasDerivAt_const t (1 : ℝ))
  simp only [logarithmicRate, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change deriv (fun s => d s 0) t / d t 0 +
    (deriv (fun s => d s 1) t / d t 1 + deriv (fun s => d s 2) t / d t 2) = 0
  field_simp [hn t 0, hn t 1, hn t 2]
  nlinarith

theorem movingBoxVelocity_divergence {c d : ℝ → Space}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (a b : Space) (η t : ℝ) (x : Space) :
    div (movingBoxVelocity a b c d η) t x = 0 := by
  rw [← divergence_eq_div (movingBoxVelocity_jointSmooth hc hd hn a b η)]
  exact localizedAffine_divergence _ _ _ _ _ _ _

lemma affinePath_mem_plateau {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) {z : Space} (hz : z ∈ Set.Icc a b) {t : ℝ}
    (hd : ∀ i, 0 < d t i) :
    affinePath c d z t ∈ openEnlargement (lowerEndpoint a c d t)
      (lowerEndpoint b c d t) η := by
  rw [mem_openEnlargement]
  intro i
  have hz₁ := hz.1 i
  have hz₂ := hz.2 i
  dsimp [lowerEndpoint, affinePath]
  constructor <;> nlinarith [hd i]

theorem affinePath_hasDerivAt_of_mem_plateau {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hp : ∀ t i, 0 < d t i) (hdet : ∀ t, ∏ i, d t i = 1)
    {z : Space} (t : ℝ)
    (hx : affinePath c d z t ∈ openEnlargement
      (lowerEndpoint a c d t) (lowerEndpoint b c d t) η) :
    HasDerivAt (affinePath c d z)
      (movingBoxVelocity a b c d η t (affinePath c d z t)) t := by
  have hn (s : ℝ) (i : Fin 3) := (hp s i).ne'
  rw [movingBoxVelocity, localizedAffine_eq hη (logarithmicRate_trace_zero hd hn hdet t)
    hx]
  apply hasDerivAt_pi.mpr
  intro i
  have hci := (hasDerivAt_pi.mp ((hc.differentiable (by simp) t).hasDerivAt) i)
  have hdi := ((contDiff_pi.mp hd i).differentiable (by simp) t).hasDerivAt
  have he : deriv c t i + logarithmicRate d t i * (affinePath c d z t i - c t i) =
      deriv c t i + deriv (fun s => d s i) t * z i := by
    dsimp [logarithmicRate, affinePath]
    field_simp [hn t i]
    ring
  rw [he]
  exact hci.fun_add (hdi.mul_const (z i))

theorem affinePath_hasDerivAt {a b : Space} {c d : ℝ → Space} {η : ℝ}
    (hη : 0 < η) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hp : ∀ t i, 0 < d t i) (hdet : ∀ t, ∏ i, d t i = 1)
    {z : Space} (hz : z ∈ Set.Icc a b) (t : ℝ) :
    HasDerivAt (affinePath c d z)
      (movingBoxVelocity a b c d η t (affinePath c d z t)) t :=
  affinePath_hasDerivAt_of_mem_plateau hη hc hd hp hdet t
    (affinePath_mem_plateau hη hz (hp t))

theorem movingBoxVelocity_zero {a b : Space} {c d : ℝ → Space} {η t : ℝ}
    (hc : deriv c t = 0) (hd : ∀ i, deriv (fun s => d s i) t = 0) :
    movingBoxVelocity a b c d η t = 0 := by
  have hl : logarithmicRate d t = 0 := by ext i; simp [logarithmicRate, hd]
  simp [movingBoxVelocity, hc, hl]

lemma tsupport_movingBoxVelocity_subset (a b : Space) (c d : ℝ → Space) {η : ℝ}
    (hη : 0 < η) (t : ℝ) :
    tsupport (movingBoxVelocity a b c d η t) ⊆
      closedEnlargement (lowerEndpoint a c d t) (lowerEndpoint b c d t) (2 * η) :=
  tsupport_localizedAffine_subset _ _ _ _ _ hη

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FieldBounds ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma JointSmooth.fullMixedD {v : Field F} (hv : JointSmooth v) (a : MultiIndex) :
    JointSmooth (fullMixedD a v) := by
  induction a with
  | nil => exact hv
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD i

lemma JointSmooth.timeSlice {v : Field F} (hv : JointSmooth v) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => v t x) := hv.comp (contDiff_id.prodMk contDiff_const)

lemma SpatiallySupported.spaceD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) (hK : IsClosed K) (i : Fin 3) :
    SpatiallySupported K (spaceD i v) := by
  intro t x hx
  have he : v t =ᶠ[𝓝 x] 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact h t y hy
  change fderiv ℝ (v t) x (Pi.single i 1) = 0
  rw [he.fderiv_eq]
  simp

lemma SpatiallySupported.fullMixedD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) (hK : IsClosed K) (a : MultiIndex) :
    SpatiallySupported K (fullMixedD a v) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD hK i

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.CompactFamilies ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

lemma JointSmooth.sum {v : ι → Field F} (hv : ∀ i, JointSmooth (v i)) :
    JointSmooth (fun t x => ∑ i, v i t x) := by
  exact ContDiff.sum (fun i _ => hv i)

lemma div_sum {v : ι → Velocity} (hv : ∀ i, JointSmooth (v i)) (t : ℝ) (x : Space) :
    div (fun t x => ∑ i, v i t x) t x = ∑ i, div (v i) t x := by
  have hd (i : ι) := ((hv i).slice t).differentiable (by simp) x
  simp only [div, spaceD, fderiv_fun_sum (fun i _ => hd i), sum_apply,
    Finset.sum_apply]
  exact Finset.sum_comm

lemma familyVelocity_jointSmooth {c d : ι → ℝ → Space}
    (hc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i))
    (hd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (d i))
    (hn : ∀ i t j, d i t j ≠ 0) (a b : ι → Space) (η : ℝ) :
    JointSmooth (familyVelocity a b c d η) :=
  JointSmooth.sum (fun i => movingBoxVelocity_jointSmooth (hc i) (hd i) (hn i) (a i) (b i) η)

lemma familyVelocity_divergence {c d : ι → ℝ → Space}
    (hc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i))
    (hd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (d i))
    (hn : ∀ i t j, d i t j ≠ 0) (a b : ι → Space) (η t : ℝ) (x : Space) :
    div (familyVelocity a b c d η) t x = 0 := by
  change div (fun t x => ∑ i, movingBoxVelocity (a i) (b i) (c i) (d i) η t x) t x = 0
  rw [div_sum
    (fun i => movingBoxVelocity_jointSmooth (hc i) (hd i) (hn i) (a i) (b i) η)]
  exact Finset.sum_eq_zero (fun i _ =>
    movingBoxVelocity_divergence (hc i) (hd i) (hn i) (a i) (b i) η t x)

lemma openEnlargement_subset_closedEnlargement {a b : Space} {η δ : ℝ}
    (h : η ≤ δ) : openEnlargement a b η ⊆ closedEnlargement a b δ := by
  intro x hx
  rw [mem_openEnlargement] at hx
  rw [mem_closedEnlargement]
  intro i
  constructor <;> linarith [(hx i).1, (hx i).2]

lemma familyVelocity_eq_on_plateau {a b : ι → Space} {c d : ι → ℝ → Space}
    {η t : ℝ} (hη : 0 < η) (i : ι) {x : Space}
    (hx : x ∈ openEnlargement (lowerEndpoint (a i) (c i) (d i) t)
      (lowerEndpoint (b i) (c i) (d i) t) η)
    (hsep : Pairwise fun i j => Disjoint
      (closedEnlargement (lowerEndpoint (a i) (c i) (d i) t)
        (lowerEndpoint (b i) (c i) (d i) t) (2 * η))
      (closedEnlargement (lowerEndpoint (a j) (c j) (d j) t)
        (lowerEndpoint (b j) (c j) (d j) t) (2 * η))) :
    familyVelocity a b c d η t x = movingBoxVelocity (a i) (b i) (c i) (d i) η t x := by
  apply Finset.sum_eq_single i
  · intro j _ hji
    apply image_eq_zero_of_notMem_tsupport
    intro hxj
    exact Set.disjoint_left.mp (hsep (Ne.symm hji))
      (openEnlargement_subset_closedEnlargement (by linarith) hx)
      (tsupport_movingBoxVelocity_subset (a j) (b j) (c j) (d j) hη t hxj)
  · simp

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ResidualRegularity ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma JointSmooth.smooth {v : Field F} (hv : JointSmooth v) : Smooth v := hv.contDiffOn

lemma JointSmooth.laplacian {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (BalancedTransport.laplacian v) := JointSmooth.sum (fun i => (hv.spaceD i).spaceD i)

lemma JointSmooth.convection {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (BalancedTransport.convection v) := by
  apply JointSmooth.sum
  intro i
  exact (contDiff_pi.mp hv i).smul (hv.spaceD i)

lemma JointSmooth.fullInertial {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (fullInertial v) := hv.fullTimeD.add hv.convection

lemma JointSmooth.viscousCoefficient {v : Velocity} (hv : JointSmooth v) :
    JointSmooth (viscousCoefficient v) := hv.laplacian.neg

lemma fullInertial_forwardEq {v : Velocity} (hv : JointSmooth v) :
    ForwardEq (fullInertial v) (inertialCoefficient v) := by
  intro t ht
  funext x
  change BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x = timeD v t x + BalancedTransport.convection v t x
  rw [show BalancedTransport.Geometry.fullTimeD v t x = timeD v t x from fullMixedD_eq_mixedD hv [none] t ht x]

lemma SpatiallySupported.laplacian {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) (hK : IsClosed K) : SpatiallySupported K (BalancedTransport.laplacian v) := by
  intro t x hx
  exact Finset.sum_eq_zero (fun i _ => ((h.spaceD hK i).spaceD hK i) t x hx)

lemma SpatiallySupported.convection {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) : SpatiallySupported K (BalancedTransport.convection v) := by
  intro t x hx
  change ∑ i, (v t x i) • BalancedTransport.spaceD i v t x = 0
  simp [h t x hx]

lemma SpatiallySupported.fullInertial {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) : SpatiallySupported K (fullInertial v) := by
  intro t x hx
  change BalancedTransport.Geometry.fullTimeD v t x + BalancedTransport.convection v t x = 0
  rw [h.fullTimeD t x hx, h.convection t x hx, add_zero]

lemma SpatiallySupported.viscousCoefficient {K : Set Space} {v : Velocity}
    (h : SpatiallySupported K v) (hK : IsClosed K) :
    SpatiallySupported K (viscousCoefficient v) := by
  intro t x hx
  change -BalancedTransport.laplacian v t x = 0
  rw [h.laplacian hK t x hx, neg_zero]

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RelativeForce ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

lemma fullMixedD_add {v w : Velocity} (hv : JointSmooth v) (hw : JointSmooth w)
    (a : MultiIndex) : fullMixedD a (fun t x => v t x + w t x) =
      fun t x => fullMixedD a v t x + fullMixedD a w t x := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    cases i with
    | none =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [fullTimeD, deriv_fun_add (((hv.fullMixedD a).timeSlice x).differentiable (by simp) t)
        (((hw.fullMixedD a).timeSlice x).differentiable (by simp) t)]
      rfl
    | some i =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [spaceD, fderiv_fun_add (((hv.fullMixedD a).slice t).differentiable (by simp) x)
        (((hw.fullMixedD a).slice t).differentiable (by simp) x)]
      rfl

lemma fullMixedD_smul (v : Velocity) (c : ℝ) (a : MultiIndex) :
    fullMixedD a (fun t x => c • v t x) = fun t x => c • fullMixedD a v t x := by
  induction a with
  | nil => rfl
  | cons i a ih =>
    cases i with
    | none =>
      simp only [fullMixedD, ih]
      ext t x k
      rw [fullTimeD, deriv_fun_const_smul_field]
      rfl
    | some i =>
      simp only [fullMixedD, ih]
      ext t x k
      change fderiv ℝ (c • fullMixedD a v t) x _ k = _
      rw [fderiv_const_smul_field]
      rfl

lemma mixedD_affineForce_of_extensions {v w V W : Velocity}
    (hv : JointSmooth V) (hw : JointSmooth W) (hev : ForwardEq V v) (hew : ForwardEq W w)
    (c : ℝ) (a : MultiIndex) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    mixedD a (affineForce v w c) t x = mixedD a v t x + c • mixedD a w t x := by
  have hcw : JointSmooth (fun t x => c • W t x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space => c • W z.1 z.2)
    exact (contDiff_const (c := c)).smul hw
  have hadd : JointSmooth (fun t x => V t x + c • W t x) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Space => V z.1 z.2 + c • W z.1 z.2)
    exact hv.add hcw
  have he : ForwardEq (fun t x => V t x + c • W t x) (affineForce v w c) := by
    intro t ht
    funext x
    change V t x + c • W t x = v t x + c • w t x
    rw [hev t ht, hew t ht]
  rw [← congrFun ((he.mixedD a) t ht) x,
    ← fullMixedD_eq_mixedD hadd a t ht x, fullMixedD_add hv hcw,
    fullMixedD_smul]
  dsimp only
  rw [fullMixedD_eq_mixedD hv a t ht x,
    fullMixedD_eq_mixedD hw a t ht x,
    congrFun ((hev.mixedD a) t ht) x, congrFun ((hew.mixedD a) t ht) x]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity

lemma family_effective_field {v : Family Velocity} (hv : EffectiveFamily v)
    (M : FiniteMachine) (w : Input M) (O : Set (ℕ →. ℕ)) : EffectiveFieldIn O (v M w) := by
  obtain ⟨E, b, R, hE, hb, _, heval, hbound, _⟩ := hv
  refine ⟨(fun s => E (inputCode M w, s)), (fun a => b (inputCode M w, a)),
    (hE.comp ((Computable.const _).pair Computable.id)).computableIn,
    (hb.comp ((Computable.const _).pair Computable.id)).computableIn, ?_, ?_⟩
  · intro a z n hz i
    exact heval M w a z n hz i
  · intro a t ht x
    exact hbound M w a t ht x

lemma realName_oracle_computable (name : ℕ → ℚ) :
    ComputableIn {nameOracle name} name := by
  have h := Nat.RecursiveIn.oracle (O := {nameOracle name}) (nameOracle name) (Set.mem_singleton _)
  change Nat.RecursiveIn {nameOracle name} (fun n => Part.some (Encodable.encode (name n))) at h
  have hr := Nat.RecursiveIn.comp (Primrec.nat_iff.mp primrec_ratRank).recursiveIn h
  apply Nat.RecursiveIn.of_eq hr
  intro n
  simp only [Part.bind_some, Encodable.decode_nat,
    Part.coe_some, Part.map_some]
  change (Part.some (rawRatCode (name n))).bind (fun k => Part.some (ratRank k)) = _
  rw [Part.bind_some]
  exact congrArg Part.some (ratRank_code (name n))

theorem effective_viscosity_clauses {v w V W : Velocity}
    (hv : Geometry.JointSmooth V) (hw : Geometry.JointSmooth W)
    (hev : Geometry.ForwardEq V v) (hew : Geometry.ForwardEq W w)
    (ev : EffectiveFieldIn ∅ v) (ew : EffectiveFieldIn ∅ w) (ν : ℝ) :
    (ComputableReal ν → EffectiveFieldIn ∅ (affineForce v w ν)) ∧
    (∀ name : ℕ → ℚ, RealName name ν →
      EffectiveFieldIn {nameOracle name} (affineForce v w ν)) := by
  have hlin := Geometry.mixedD_affineForce_of_extensions hv hw hev hew ν
  constructor
  · rintro ⟨name, hc, hn⟩
    exact effective_affine_force ev ew hc.computableIn hn hlin
  · intro name hn
    have lift {f : Velocity} (hf : EffectiveFieldIn ∅ f) (O : Set (ℕ →. ℕ)) :
        EffectiveFieldIn O f := by
      obtain ⟨E,b,hE,hb,heval,hbound⟩ := hf
      refine ⟨E,b,?_,?_,heval,hbound⟩
      · exact hE.mono (Set.empty_subset O)
      · exact hb.mono (Set.empty_subset O)
    exact effective_affine_force (lift ev _) (lift ew _)
      (realName_oracle_computable name) hn hlin

theorem residual_effective_viscosity {U : Family Velocity}
    (hU : ∀ M w, Geometry.JointSmooth (U M w))
    (ef₀ : EffectiveFamily (fun M w => inertialCoefficient (U M w)))
    (ef₁ : EffectiveFamily (fun M w => viscousCoefficient (U M w)))
    (M : FiniteMachine) (w : Input M) (ν : ℝ) :
    (ComputableReal ν → EffectiveFieldIn ∅
      (affineForce (inertialCoefficient (U M w)) (viscousCoefficient (U M w)) ν)) ∧
    (∀ name : ℕ → ℚ, RealName name ν → EffectiveFieldIn {nameOracle name}
      (affineForce (inertialCoefficient (U M w)) (viscousCoefficient (U M w)) ν)) :=
  effective_viscosity_clauses (hU M w).fullInertial (hU M w).viscousCoefficient
    (Geometry.fullInertial_forwardEq (hU M w)) (fun _ _ => rfl)
    (family_effective_field ef₀ M w ∅) (family_effective_field ef₁ M w ∅) ν

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MachineRecursion ----
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Effectivity
open Effectivity.ComputableRules

lemma primrec_rawBase : Primrec (fun p : ℕ × List ℕ × ℤ => rawBase p.1 p.2.1 p.2.2) := by
  unfold rawBase
  exact Primrec.ite
    (Primrec.eq.comp (primrec_int_ofNat.comp (primrec_int_toNat.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd))
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd)
      (primrec_int_toNat.comp (Primrec.snd.comp Primrec.snd))) Primrec.fst)
    Primrec.fst

lemma computable_rawRead : Computable (fun p : ℕ × List ℕ × List (ℤ × ℕ) × ℤ =>
    rawRead p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold rawRead
  apply Primrec.to_comp
  apply Primrec.list_foldl (h := fun (p : ℕ × List ℕ × List (ℤ × ℕ) × ℤ) (v : ℕ × (ℤ × ℕ)) =>
      if p.2.2.2 = v.2.1 then v.2.2 else v.1) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (primrec_rawBase.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact (Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd)).to₂

lemma computable_rawMove : Computable rawMove := by
  unfold rawMove
  exact (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const (0:ℤ))
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
      (Primrec.const (-1:ℤ)) (Primrec.const (1:ℤ)))).to_comp

lemma computable_rawSymbol : Computable (fun r : RawRun =>
    rawRead r.1.2.2.2.1 r.2.1 r.2.2.2.2 r.2.2.2.1) := by
  have hM : Computable (fun r : RawRun => r.1) := Computable.fst
  have hw : Computable (fun r : RawRun => r.2.1) := Computable.fst.comp Computable.snd
  have hc : Computable (fun r : RawRun => r.2.2) := Computable.snd.comp Computable.snd
  have hh : Computable (fun r : RawRun => r.2.2.2.1) := Computable.fst.comp (Computable.snd.comp hc)
  have hs : Computable (fun r : RawRun => r.2.2.2.2) := Computable.snd.comp (Computable.snd.comp hc)
  have hb : Computable (fun r : RawRun => r.1.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hM)))
  exact computable_rawRead.comp
    (g := fun r : RawRun => (r.1.2.2.2.1,r.2.1,r.2.2.2.2,r.2.2.2.1))
    (hb.pair (hw.pair (hs.pair hh)))

lemma computable_rawInstruction : Computable (fun r : RawRun =>
    (r.1.2.2.2.2.getD r.2.2.1 []).getD
      (rawRead r.1.2.2.2.1 r.2.1 r.2.2.2.2 r.2.2.2.1) none) := by
  have hq : Computable (fun r : RawRun => r.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have ht : Computable (fun r : RawRun => r.1.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  exact (Primrec.list_getD (none : Option RawInstruction)).to_comp.comp
    ((Primrec.list_getD ([] : List (Option RawInstruction))).to_comp.comp ht hq) computable_rawSymbol

lemma computable_rawAdvanceState : Computable (fun p : RawState × RawInstruction =>
    (p.2.1, p.1.2.1 + rawMove p.2.2.2, p.1.2.2 ++ [(p.1.2.1,p.2.2.1)])) := by
  have hh : Computable (fun p : RawState × RawInstruction => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun p : RawState × RawInstruction => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hw : Computable (fun p : RawState × RawInstruction => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hd : Computable (fun p : RawState × RawInstruction => rawMove p.2.2.2) :=
    computable_rawMove.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact (Computable.fst.comp Computable.snd).pair
    ((primrec_int_add.to_comp.comp hh hd).pair
      (Primrec.list_append.to_comp.comp hs
        (Primrec.list_cons.to_comp.comp (hh.pair hw) (Computable.const []))))

lemma computable_rawAdvance : Computable (fun p : RawRun × RawInstruction =>
    (p.1.1, p.1.2.1, p.2.1, p.1.2.2.2.1 + rawMove p.2.2.2,
      p.1.2.2.2.2 ++ [(p.1.2.2.2.1,p.2.2.1)])) := by
  have hc : Computable (fun p : RawRun × RawInstruction => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  exact (Computable.fst.comp Computable.fst).pair
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      (computable_rawAdvanceState.comp (g := fun p : RawRun × RawInstruction => (p.1.2.2,p.2))
        (hc.pair Computable.snd)))

lemma computable_rawStep : Computable rawStep :=
  Computable.option_map computable_rawInstruction computable_rawAdvance.to₂

lemma computable_rawInit : Computable rawInit := by
  have hp : Computable (fun n : ℕ => (Encodable.decode (α := ℕ × List ℕ) n).getD (0,[])) :=
    Computable.option_getD Computable.decode (Computable.const _)
  have hm : Computable (fun n : ℕ =>
      (Encodable.decode (α := RawMachine) ((Encodable.decode (α := ℕ × List ℕ) n).getD (0,[])).1).getD (0,0,0,0,[])) :=
    Computable.option_getD (Computable.decode.comp (Computable.fst.comp hp)) (Computable.const _)
  exact hm.pair ((Computable.snd.comp hp).pair
    ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hm))).pair
      ((Computable.const (0 : ℤ)).pair (Computable.const []))))

lemma rawBase_initial (M : FiniteMachine) (w : Input M) (z : ℤ) :
    rawBase M.blank.val (w.map Fin.val) z = ((initialConfiguration M w).tape z).val := by
  have hz : ((z.toNat : ℤ) = z) ↔ 0 ≤ z := by omega
  simp only [rawBase, initialConfiguration, hz]
  split_ifs with h
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[z.toNat]? <;> rfl
  · rfl

lemma rawRead_append (b : ℕ) (w : List ℕ) (s : List (ℤ × ℕ)) (z k : ℤ) (a : ℕ) :
    rawRead b w (s ++ [(k,a)]) z = if z = k then a else rawRead b w s z := by
  simp [rawRead, List.foldl_append]

lemma serialize_instruction (M : FiniteMachine) (q : Fin (M.states+1)) (a : Fin (M.symbols+1)) :
    (((serialize M).2.2.2.2.getD q.val []).getD a.val none) =
      (M.transition q a).map (fun v => (v.state.val, v.write.val, v.move.number)) := by
  have hq : q.val < (List.finRange (M.states+1)).length := by simpa using q.isLt
  have ha : a.val < (List.finRange (M.symbols+1)).length := by simpa using a.isLt
  simp [serialize, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq,
    List.getElem?_eq_getElem ha]

lemma rawRel_initial (M : FiniteMachine) (w : Input M) :
    RawRel M w (initialConfiguration M w) (rawInit (inputCode M w)) := by
  rw [rawInit_inputCode]
  exact ⟨rfl,rfl,rfl,rfl, fun z => rawBase_initial M w z⟩

lemma rawStep_rel (M : FiniteMachine) (w : Input M) (c : TapeConfiguration M) (r : RawRun)
    (hr : RawRel M w c r) :
    match machineStep M c with
    | none => rawStep r = none
    | some c' => ∃ r', rawStep r = some r' ∧ RawRel M w c' r' := by
  rcases r with ⟨m,w',q,h,s⟩
  rcases hr with ⟨rfl,rfl,hq,hh,hs⟩
  dsimp at hq hh
  subst q; subst h
  have hi := serialize_instruction M c.state (c.tape c.head)
  dsimp only [rawStep]
  rw [show (serialize M).2.2.2.1 = M.blank.val from rfl, hs, hi]
  unfold machineStep
  cases hv : M.transition c.state (c.tape c.head) with
  | none => rfl
  | some v =>
    simp only [Option.map_some, rawMove_number]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro z
    rw [rawRead_append, hs]
    by_cases hz : z = c.head
    · subst z; simp
    · simp [hz]

lemma raw_respects (M : FiniteMachine) (w : Input M) :
    StateTransition.Respects (machineStep M) rawStep (RawRel M w) := by
  intro c r hr
  have h := rawStep_rel M w c r hr
  cases he : machineStep M c with
  | none => simpa [he] using h
  | some c' =>
    simp only [he] at h
    obtain ⟨r',hs,hr'⟩ := h
    exact ⟨r',hr', Relation.TransGen.single hs⟩

lemma halts_iff_eval_dom (M : FiniteMachine) (w : Input M) :
    Halts M w ↔ (StateTransition.eval (machineStep M) (initialConfiguration M w)).Dom := by
  rw [Part.dom_iff_mem]
  simp only [StateTransition.mem_eval]
  rfl

lemma raw_eval_dom (M : FiniteMachine) (w : Input M) :
    (StateTransition.eval rawStep (rawInit (inputCode M w))).Dom ↔ Halts M w := by
  exact (StateTransition.tr_eval_dom (raw_respects M w) (rawRel_initial M w)).trans
    (halts_iff_eval_dom M w).symm

lemma partrec_raw_eval : Partrec (StateTransition.eval rawStep) := by
  unfold StateTransition.eval
  apply Partrec.fix
  apply Computable.partrec
  exact (Computable.option_casesOn computable_rawStep Computable.sumInl
    (Computable.sumInr.comp Computable.snd).to₂).of_eq (fun r => by
      cases rawStep r <;> rfl)

lemma universalPartial_partrec : Partrec universalPartial :=
  (partrec_raw_eval.comp computable_rawInit).map (Computable.const 0).to₂

lemma universalPartial_dom (M : FiniteMachine) (w : Input M) :
    (universalPartial (inputCode M w)).Dom ↔ Halts M w := raw_eval_dom M w

lemma exists_universal_code : ∃ c : Turing.ToPartrec.Code, ∀ n,
    (c.eval [n]).Dom ↔ (universalPartial n).Dom := by
  obtain ⟨c,hc⟩ := Turing.ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr universalPartial_partrec)
  refine ⟨c, fun n => ?_⟩
  have h := hc ⟨[n],rfl⟩
  simpa [List.Vector.head] using congrArg Part.Dom h

end BalancedTransport.Universal
end

end OAI

-- Lean 4.33.1 equivalent of the upstream Lean 4.34 theorem name (used by the inlined block below).
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

-- ---- inlined from the OAI_BalancedTransport_Universal_post_step solution (the platform cannot check that node's statement) ----
-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FiniteSimulator ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.

namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {α : Type*} [Fintype α]

end BalancedTransport.Universal
end

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Inhabited Λ]
variable (P : TM0.Machine Γ Λ) (S : Finset Λ) (ss : TM0.Supports P S)

omit [Fintype Γ] [Inhabited Γ] in
lemma stateIndex_decode {q : Λ} (hq : q ∈ S) :
    (finiteUnindex ⟨default,ss.1⟩ (stateIndex P S ss q) : {q : Λ // q ∈ S}).val = q := by
  simp [stateIndex, hq]

lemma finitePostMachine_instruction (q : Λ) (hq : q ∈ S) (a : Γ) :
    (finitePostMachine P S ss).transition (stateIndex P S ss q) (finiteIndex a) =
      (P q a).map (postInstruction P S ss (finiteIndex a)) := by
  simp [finitePostMachine, stateIndex_decode P S ss hq]

lemma post_tape_head {c : TM0.Cfg Γ Λ} {d : TapeConfiguration (finitePostMachine P S ss)}
    (h : PostRel P S ss c d) : d.tape d.head = finiteIndex c.Tape.head := by
  simpa using h.2.2 0

lemma post_step (c : TM0.Cfg Γ Λ) (d : TapeConfiguration (finitePostMachine P S ss))
    (h : PostRel P S ss c d) :
    match TM0.step P c with
    | none => machineStep (finitePostMachine P S ss) d = none
    | some c' => ∃ d', machineStep (finitePostMachine P S ss) d = some d' ∧ PostRel P S ss c' d' := by
  have ht : (finitePostMachine P S ss).transition d.state (d.tape d.head) =
      (P c.q c.Tape.head).map (postInstruction P S ss (finiteIndex c.Tape.head)) := by
    rw [h.2.1, post_tape_head P S ss h, finitePostMachine_instruction P S ss _ h.1]
  unfold machineStep
  rw [ht]
  simp only [TM0.step]
  cases hp : P c.q c.Tape.head with
  | none => rfl
  | some v =>
    rcases v with ⟨q', act⟩
    have hq' : q' ∈ S := ss.2 hp h.1
    cases act with
    | write b =>
      simp only [Option.map_some, postInstruction]
      refine ⟨_,rfl,hq',rfl,?_⟩
      intro i
      change Function.update d.tape d.head (finiteIndex b) (d.head + 0 + i) =
        finiteIndex ((c.Tape.write b).nth i)
      simp only [Int.add_zero, Tape.write_nth]
      by_cases hi : i = 0
      · subst i; simp
      · have hi' : d.head + i ≠ d.head := by omega
        rw [ite_eq_right hi, Function.update_of_ne hi']
        exact h.2.2 i
    | move dir =>
      have hu : Function.update d.tape d.head (finiteIndex c.Tape.head) = d.tape := by
        rw [← post_tape_head P S ss h, Function.update_eq_self]
      cases dir with
      | left =>
        simp only [Option.map_some, postInstruction]
        refine ⟨_,rfl,hq',rfl,?_⟩
        intro i
        change Function.update d.tape d.head (finiteIndex c.Tape.head) (d.head + (-1) + i) =
          finiteIndex ((c.Tape.move .left).nth i)
        rw [hu, Tape.move_left_nth]
        convert h.2.2 (i-1) using 1
        congr 1
        ring
      | right =>
        simp only [Option.map_some, postInstruction]
        refine ⟨_,rfl,hq',rfl,?_⟩
        intro i
        change Function.update d.tape d.head (finiteIndex c.Tape.head) (d.head + 1 + i) =
          finiteIndex ((c.Tape.move .right).nth i)
        rw [hu, Tape.move_right_nth]
        convert h.2.2 (i+1) using 1
        congr 1
        ring

end BalancedTransport.Universal
end

end OAI


-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FiniteSimulator ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {α : Type*} [Fintype α]

end BalancedTransport.Universal
end

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Inhabited Λ]
variable (P : TM0.Machine Γ Λ) (S : Finset Λ) (ss : TM0.Supports P S)

lemma post_initial_rel (w : List Γ) : PostRel P S ss (TM0.init w)
    (initialConfiguration (finitePostMachine P S ss) (w.map finiteIndex)) := by
  refine ⟨ss.1, rfl, ?_⟩
  intro i
  simp only [initialConfiguration, zero_add, TM0.init, Tape.mk₁, Tape.mk₂]
  by_cases hi : 0 ≤ i
  · rw [ite_eq_left hi, ← Int.toNat_of_nonneg hi]
    simp only [Tape.mk'_nth_nat, ListBlank.nth_mk, List.getI_eq_getElem?_getD,
      List.getElem?_map, Int.toNat_natCast]
    cases w[i.toNat]? <;> rfl
  · have hi' : i < 0 := lt_of_not_ge hi
    rw [ite_eq_right hi]
    cases i with
    | ofNat n => exact False.elim (not_lt_of_ge (Int.natCast_nonneg _) hi')
    | negSucc n =>
      change finiteIndex (default : Γ) = finiteIndex ((ListBlank.mk []).nth n)
      rw [ListBlank.nth_mk]
      rfl

lemma post_respects : StateTransition.Respects (TM0.step P) (machineStep (finitePostMachine P S ss))
    (PostRel P S ss) := by
  intro c d hr
  have h := post_step P S ss c d hr
  cases he : TM0.step P c with
  | none => simpa [he] using h
  | some c' =>
    simp only [he] at h
    obtain ⟨d',hd,hr'⟩ := h
    exact ⟨d',hr',Relation.TransGen.single hd⟩

lemma halts_finitePostMachine (w : List Γ) :
    Halts (finitePostMachine P S ss) (w.map finiteIndex) ↔ (TM0.eval P w).Dom := by
  exact (halts_iff_eval_dom _ _).trans
    (StateTransition.tr_eval_dom (post_respects P S ss) (post_initial_rel P S ss w))

end BalancedTransport.Universal
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.UniversalInput ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing PartrecToTM2
open scoped Classical

lemma trNat_rec (n : ℕ) : trNat n =
    if n = 0 then [] else (if n % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat (n / 2) := by
  have h (p : Num) : trNat (p : ℕ) =
      if (p : ℕ) = 0 then [] else
        (if (p : ℕ) % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: trNat ((p : ℕ) / 2) := by
    cases p with
    | zero => simp [trNat,trNum]
    | pos p =>
      have hp := PosNum.to_nat_pos p
      cases p with
      | one => norm_num [trNat,trNum,trPosNum]
      | bit0 p =>
        have hp := PosNum.to_nat_pos p
        have he : ((Num.pos (PosNum.bit0 p) : Num) : ℕ) = (p : ℕ) + (p : ℕ) := rfl
        rw [he]
        have hdiv : ((p : ℕ) + (p : ℕ)) / 2 = (p : ℕ) := by omega
        have hmod : ((p : ℕ) + (p : ℕ)) % 2 = 0 := by omega
        rw [ite_eq_right (by omega),ite_eq_left hmod,hdiv]
        change trNum (((Num.pos (PosNum.bit0 p) : Num) : ℕ) : Num) =
          Γ'.bit0 :: trNum (((Num.pos p : Num) : ℕ) : Num)
        rw [Num.of_to_nat, Num.of_to_nat]
        rfl
      | bit1 p =>
        have hp := PosNum.to_nat_pos p
        have he : ((Num.pos (PosNum.bit1 p) : Num) : ℕ) = (p : ℕ) + (p : ℕ) + 1 := rfl
        rw [he]
        have hdiv : ((p : ℕ) + (p : ℕ) + 1) / 2 = (p : ℕ) := by omega
        have hmod : ((p : ℕ) + (p : ℕ) + 1) % 2 ≠ 0 := by omega
        rw [ite_eq_right (by omega),ite_eq_right hmod,hdiv]
        change trNum (((Num.pos (PosNum.bit1 p) : Num) : ℕ) : Num) =
          Γ'.bit1 :: trNum (((Num.pos p : Num) : ℕ) : Num)
        rw [Num.of_to_nat, Num.of_to_nat]
        rfl
  simpa using h (n : Num)

lemma computable_trNat : Computable trNat := by
  let g : Unit → List (List Γ') → Option (List Γ') := fun _ l =>
    some (if l.length = 0 then [] else
      (if l.length % 2 = 0 then Γ'.bit0 else Γ'.bit1) :: (l.getD (l.length / 2) []))
  have hg : Primrec₂ g := by
    change Primrec (fun z : Unit × List (List Γ') => g z.1 z.2)
    dsimp only [g]
    apply Primrec.option_some.comp
    apply Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0))
      (Primrec.const [])
    apply Primrec.list_cons.comp
    · exact Primrec.ite (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))
        (Primrec.const 0)) (Primrec.const Γ'.bit0) (Primrec.const Γ'.bit1)
    · exact (Primrec.list_getD ([] : List Γ')).comp Primrec.snd
        (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))
  have hh := Primrec.nat_strong_rec (fun (_ : Unit) => trNat) hg (by
    intro u n
    dsimp [g]
    simp only [List.length_map,List.length_range]
    by_cases hn : n = 0
    · subst n; simp
    · rw [ite_eq_right hn, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (by omega : n / 2 < n)]
      simp only [Option.map_some,Option.getD_some]
      rw [trNat_rec n,ite_eq_right hn])
  exact hh.to_comp.comp (Computable.const ()) Computable.id

lemma computable_trInit : Computable (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main) := by
  have hm : Computable (fun L : List Γ' => L.reverse.map
      (fun a => ((false, Function.update (fun _ : K' => (none : Option Γ')) K'.main (some a)) : StackAlphabet))) :=
    (Primrec.list_map Primrec.list_reverse ((Primrec.dom_finite
      (fun a : Γ' => ((false, Function.update (fun _ : K' => (none : Option Γ')) K'.main (some a)) : StackAlphabet))).comp Primrec.snd).to₂).to_comp
  exact Primrec.list_cons.to_comp.comp
    ((Primrec.dom_finite (fun a : StackAlphabet => ((true,a.2) : StackAlphabet))).to_comp.comp
      (Primrec.list_headI.to_comp.comp hm))
    (Primrec.list_tail.to_comp.comp hm)

lemma computable_translatedInput : Computable (fun n : ℕ =>
    (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [n])).map finiteIndex) := by
  have ht : Computable (fun n : ℕ => trList [n]) :=
    Primrec.list_append.to_comp.comp computable_trNat (Computable.const [Γ'.cons])
  exact (Primrec.list_map Primrec.id ((Primrec.dom_finite finiteIndex).comp Primrec.snd).to₂).to_comp.comp
    (computable_trInit.comp ht)

end BalancedTransport.Universal
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.UniversalMachine ----
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing PartrecToTM2 StateTransition
open scoped Classical

theorem finite_machine_of_code (c : ToPartrec.Code) :
    ∃ M : FiniteMachine, ∃ δ : ℕ → Input M,
      Computable δ ∧ ∀ n, Halts M (δ n) ↔ (c.eval [n]).Dom := by
  let : Inhabited PartrecToTM2.Λ' := ⟨trNormal c Cont'.halt⟩
  let P₁ := TM2to1.tr PartrecToTM2.tr
  let S₁ := TM2to1.trSupp PartrecToTM2.tr (codeSupp c Cont'.halt)
  have ss₁ : TM1.Supports P₁ S₁ := TM2to1.tr_supports PartrecToTM2.tr (PartrecToTM2.tr_supports c Cont'.halt)
  let P₀ := TM1to0.tr P₁
  let S₀ := TM1to0.trStmts P₁ S₁
  have ss₀ : TM0.Supports P₀ S₀ := TM1to0.tr_supports P₁ ss₁
  let δ : ℕ → List (Fin (Fintype.card StackAlphabet + 1)) := fun n =>
    (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [n])).map
      (finiteIndex (α := StackAlphabet))
  refine ⟨finitePostMachine P₀ S₀ ss₀, δ, computable_translatedInput, ?_⟩
  intro n
  rw [halts_finitePostMachine, TM1to0.tr_eval]
  refine (TM2to1.tr_eval_dom PartrecToTM2.tr K'.main (trList [n])).trans ?_
  have hi : (TM2.init K'.main (trList [n]) : TM2.Cfg (fun _ : K' => Γ') PartrecToTM2.Λ' (Option Γ')) =
      PartrecToTM2.init c [n] := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> simp [K'.elim,Function.update]
  change (eval (TM2.step PartrecToTM2.tr) (TM2.init K'.main (trList [n]))).Dom ↔ _
  rw [hi, PartrecToTM2.tr_eval]
  rfl

theorem exists_universal_machine :
    ∃ N : FiniteMachine, ∃ δ : ℕ → Input N,
      Computable δ ∧ ∀ M w, Halts N (δ (inputCode M w)) ↔ Halts M w := by
  obtain ⟨c,hc⟩ := exists_universal_code
  obtain ⟨N,δ,hδ,hh⟩ := finite_machine_of_code c
  exact ⟨N,δ,hδ, fun M w => (hh _).trans ((hc _).trans (universalPartial_dom M w))⟩

end BalancedTransport.Universal
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericDifferentiation ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma dual_drop (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (q : List ℝ) :
    ((o.dual d k).realFrom x q).drop 5 = q := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, tag]

lemma dual_value (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 4 0 = o.real d x s := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, real, tag, rat, left, right, h]

lemma dual_differential (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 0 0 =
      o.differential d k (fun a => s.getD a 0) (fun a => q.getD (5*a) 0) := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.realFrom, real, differential, tag, rat, left, right,
      Nat.add_assoc, h, pow_two]
  change (((if Fin.ofNat d a = k then 1 else 0) : ℚ) : ℝ) =
    (if Fin.ofNat d a = k then 1 else 0)
  by_cases hh : Fin.ofNat d a = k <;>
    simp only [hh, ite_true, ite_false, Rat.cast_one, Rat.cast_zero]

lemma dual_valid (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : o.Valid s) :
    (o.dual d k).ValidFrom x q := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ValidFrom, Valid, real, tag, rat, left, right, h] at hv ⊢
  exact hv

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericScopes ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma real_append (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (s q : List ℝ) (hs : o.Scoped s.length) : o.real d x (s ++ q) = o.real d x s := by
  have he (i : ℕ) (hi : i < s.length) : (s ++ q).getD i 0 = s.getD i 0 := by
    simp [List.getD, List.getElem?_append_left hi]
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp only [Scoped, real, tag, rat, left, right] at hs ⊢
  all_goals first | rfl | exact he _ hs | simp only [he _ hs] | simp only [he _ hs.1, he _ hs.2]

lemma valid_append (o : NumericOp) (s q : List ℝ) (hs : o.Scoped s.length) :
    o.Valid (s ++ q) ↔ o.Valid s := by
  by_cases ht : o.tag = 5
  · have hh : o.left < s.length := by unfold Scoped at hs; rw [ht] at hs; exact hs
    simp only [Valid, ht, forall_const]
    simp only [List.getD, List.getElem?_append_left hh]
  · simp [Valid, ht]

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma realFrom_length (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (realFrom p x s).length = p.length + s.length := by
  induction p generalizing s with
  | nil => simp [realFrom]
  | cons o p ih => simpa [realFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (o.real d x s :: s)

lemma realFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : realFrom p x (s ++ q) = realFrom p x s ++ q := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change realFrom p x (o.real d x (s ++ q) :: (s ++ q)) =
      realFrom p x (o.real d x s :: s) ++ q
    rw [o.real_append d x s q hs.1]
    exact ih (o.real d x s :: s) hs.2

lemma validFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : ValidFrom x p (s ++ q) ↔ ValidFrom x p s := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change o.Valid (s ++ q) ∧ ValidFrom x p (o.real d x (s ++ q) :: (s ++ q)) ↔
      o.Valid s ∧ ValidFrom x p (o.real d x s :: s)
    rw [o.valid_append s q hs.1, o.real_append d x s q hs.1]
    exact and_congr_right (fun _ => ih (o.real d x s :: s) hs.2)

lemma realFrom_empty_append (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    realFrom p x s = realFrom p x [] ++ s :=
  realFrom_append p x [] s hp

lemma validFrom_of_closed (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    ValidFrom x p s ↔ p.Valid x := p.validFrom_append x [] s hp

lemma realFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).realFrom x s = q.realFrom x (realFrom p x s) := List.foldl_append

lemma validFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).ValidFrom x s ↔ ValidFrom x p s ∧ q.ValidFrom x (realFrom p x s) := by
  induction p generalizing s with
  | nil => simp [ValidFrom, realFrom]
  | cons o p ih => simpa only [List.cons_append, ValidFrom, realFrom,
      List.foldl_cons, and_assoc] using and_congr_right (fun _ => ih _)

lemma scopedFrom_mono (p : NumericProgram) {n m : ℕ} (hnm : n ≤ m) :
    p.ScopedFrom n → p.ScopedFrom m := by
  intro h
  induction p generalizing n m with
  | nil => trivial
  | cons o p ih =>
    refine ⟨?_, ih (Nat.add_le_add_right hnm 1) h.2⟩
    rcases o with ⟨j,r,a,b⟩
    have ho := h.1
    fin_cases j <;> dsimp only [NumericOp.Scoped, NumericOp.tag, NumericOp.rat,
      NumericOp.left, NumericOp.right] at ho ⊢
    all_goals first | trivial | exact ho.trans_le hnm | exact ⟨ho.1.trans_le hnm,ho.2.trans_le hnm⟩

lemma scopedFrom_concat (p q : NumericProgram) (n : ℕ) :
    (p ++ q).ScopedFrom n ↔ p.ScopedFrom n ∧ q.ScopedFrom (n+p.length) := by
  induction p generalizing n with
  | nil => simp [ScopedFrom]
  | cons o p ih =>
    simp only [List.cons_append, ScopedFrom, List.length_cons]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1, and_assoc]

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericJets ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma dual_register (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s : List ℝ) (a : ℕ) :
    ((o.dual d k).realFrom x s).getD (5+a) 0 = s.getD a 0 := by
  have h := congrArg (fun l : List ℝ => l.getD a 0) (o.dual_drop d k x s)
  simpa [List.getD, List.getElem?_drop] using h

lemma dual_length (k : Fin d) (o : NumericOp) : (o.dual d k).length = 5 := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> rfl

lemma dual_scoped (k : Fin d) (o : NumericOp) {n : ℕ} (h : o.Scoped n) :
    (o.dual d k).ScopedFrom (5*n) := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ScopedFrom, Scoped, tag, left, right] at h ⊢
  all_goals omega

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma jetStep_length (k : Fin d) (p : NumericProgram) : (p.jetStep k).length = 5*p.length := by
  induction p with
  | nil => rfl
  | cons o p ih => simp only [jetStep, List.flatMap_cons, List.length_append,
      NumericOp.dual_length, List.length_cons] at ih ⊢; omega

lemma jetStep_scoped (k : Fin d) (p : NumericProgram) {n : ℕ} (h : p.ScopedFrom n) :
    (p.jetStep k).ScopedFrom (5*n) := by
  induction p generalizing n with
  | nil => trivial
  | cons o p ih =>
    rw [jetStep, List.flatMap_cons, scopedFrom_concat, NumericOp.dual_length]
    exact ⟨o.dual_scoped d k h.1, by simpa [jetStep, Nat.mul_add] using ih h.2⟩

lemma jetStep_closed (k : Fin d) (p : NumericProgram) (h : p.Closed) :
    (p.jetStep k).Closed := p.jetStep_scoped k h

lemma jetStep_validFrom (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ)
    (s q : List ℝ) (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : p.ValidFrom x s) :
    (p.jetStep k).ValidFrom x q ∧
      ∀ a, ((p.jetStep k).realFrom x q).getD (5*a+4) 0 = (p.realFrom x s).getD a 0 := by
  induction p generalizing s q with
  | nil => exact ⟨trivial, h⟩
  | cons o p ih =>
    have ho := o.dual_valid d k x s q h hv.1
    have hh (a : ℕ) : ((o.dual d k).realFrom x q).getD (5*a+4) 0 =
        (o.real d x s :: s).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k x s q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5,
          List.getD_cons_succ] using (o.dual_register d k x q (5*a+4)).trans (h a)
    have hi := ih _ _ hh hv.2
    refine ⟨?_, ?_⟩
    · exact (validFrom_concat _ _ x q).mpr ⟨ho, hi.1⟩
    · simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
        List.foldl_cons, List.foldl_append] using hi.2

lemma jetStep_valid (k : Fin d) (p : NumericProgram) {x : Fin d → ℝ} (hv : p.Valid x) :
    (p.jetStep k).Valid x := (p.jetStep_validFrom k x [] [] (by simp) hv).1

lemma jetStep_hasDerivAtFrom (k : Fin d) (p : NumericProgram)
    (x : ℝ → Fin d → ℝ) (s : ℝ → List ℝ) (q : List ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (h : ∀ a, q.getD (5*a+4) 0 = (s t).getD a 0)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (q.getD (5*a) 0) t)
    (hv : p.ValidFrom (x t) (s t)) :
    ∀ a, HasDerivAt (fun t => (p.realFrom (x t) (s t)).getD a 0)
      (((p.jetStep k).realFrom (x t) q).getD (5*a) 0) t := by
  induction p generalizing s q with
  | nil => exact hs
  | cons o p ih =>
    let s' : ℝ → List ℝ := fun v => o.real d (x v) (s v) :: s v
    let q' : List ℝ := (o.dual d k).realFrom (x t) q
    have hh (a : ℕ) : q'.getD (5*a+4) 0 = (s' t).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k (x t) (s t) q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5, s', q',
          List.getD_cons_succ] using (o.dual_register d k (x t) q (5*a+4)).trans (h a)
    have hd (a : ℕ) : HasDerivAt (fun v => (s' v).getD a 0) (q'.getD (5*a) 0) t := by
      cases a with
      | zero =>
        change HasDerivAt (fun v => o.real d (x v) (s v))
          (((o.dual d k).realFrom (x t) q).getD 0 0) t
        rw [o.dual_differential d k (x t) (s t) q h]
        exact o.hasDerivAt d k x s _ t hx hs hv.1
      | succ a =>
        change HasDerivAt (fun v => (s v).getD a 0)
          (((o.dual d k).realFrom (x t) q).getD (5*(a+1)) 0) t
        rw [show 5*(a+1)=5+5*a by omega, o.dual_register d k]
        exact hs a
    have hi := ih s' q' hh hd hv.2
    simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
      List.foldl_cons, List.foldl_append, s', q'] using hi

lemma differentiableAtFrom (p : NumericProgram) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : p.ValidFrom x (s x)) :
    ∀ a, DifferentiableAt ℝ (fun y => (p.realFrom y (s y)).getD a 0) x := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun y => o.real d y (s y) :: s y) ?_ hv.2
    intro a
    cases a with
    | zero => exact o.differentiableAt d x s hs hv.1
    | succ a => exact hs a

lemma differentiableAt (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    DifferentiableAt ℝ p.real x :=
  p.differentiableAtFrom x (fun _ => []) (fun _ => differentiableAt_const _) hv 0

lemma jetStep_real (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    (p.jetStep k).real x = fderiv ℝ p.real x (Pi.single k 1) := by
  let y : ℝ → Fin d → ℝ := fun t => x + t • Pi.single k 1
  have hy (i : Fin d) : HasDerivAt (fun t => y t i) (if i=k then 1 else 0) 0 := by
    have h := (hasDerivAt_const (0:ℝ) (x i)).add ((hasDerivAt_id (0:ℝ)).mul_const ((Pi.single k (1:ℝ) : Fin d → ℝ) i))
    simpa only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Function.const_apply, Pi.mul_apply, id_eq, mul_ite, mul_one, mul_zero, eq_comm, Pi.add_def, zero_add] using h
  have he : y 0 = x := by simp [y]
  have hh := p.jetStep_hasDerivAtFrom k y (fun _ => []) [] 0 hy (by simp)
    (by intro a; simpa using hasDerivAt_const (0:ℝ) (0:ℝ)) (by change p.Valid (y 0); rw [he]; exact hv) 0
  have hf := (p.differentiableAt x hv).hasFDerivAt.hasLineDerivAt (Pi.single k 1)
  exact HasDerivAt.unique (by simpa only [real, he, Nat.mul_zero] using hh) hf

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericAlgebra ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma literal_closed (q : ℚ) : (literal q).Closed := by trivial

lemma literal_valid (q : ℚ) (x : Fin d → ℝ) : (literal q).Valid x := by
  simp [literal, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

omit [NeZero d] in
lemma coordinate_closed (k : Fin d) : (coordinate k).Closed := by trivial

lemma coordinate_valid (k : Fin d) (x : Fin d → ℝ) : (coordinate k).Valid x := by
  simp [coordinate, Valid, ValidFrom, NumericOp.Valid, NumericOp.tag]

lemma coordinate_real (k : Fin d) (x : Fin d → ℝ) : (coordinate k).real x = x k := by
  simp [coordinate, real, realFrom, NumericOp.real, NumericOp.tag, NumericOp.left, Fin.ofNat_eq_cast]

lemma unary_real (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ) :
    (unary j n p).real x = NumericOp.real d (j,0,0,n) x (p.realFrom x []) := by
  simp [unary, real, realFrom, List.foldl_append]

lemma unary_valid (j : Fin 9) (n : ℕ) (p : NumericProgram) (x : Fin d → ℝ)
    (hp : p.Valid x) (hi : j = 5 → ((n+1:ℕ):ℝ)⁻¹ ≤ p.real x) :
    (unary j n p).Valid x := by
  exact (validFrom_concat _ _ _ _).mpr ⟨hp, ⟨hi, trivial⟩⟩

lemma unary_closed (j : Fin 9) (n : ℕ) (p : NumericProgram) (hp : p.Closed)
    (hne : p ≠ []) (hj : j = 4 ∨ j = 5 ∨ j = 7) : (unary j n p).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hne
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨hp, ?_⟩
  rcases hj with rfl | rfl | rfl <;> exact ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.left] using hn,trivial⟩

lemma realFrom_head {s : List ℝ} (hs : 0 < s.length) (t : List ℝ) :
    (s ++ t).getD 0 0 = s.getD 0 0 := by
  simp only [List.getD, List.getElem?_append_left hs]

lemma binary_real (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ [])
    (x : Fin d → ℝ) :
    (binary j p q).real x =
      NumericOp.real d (j,0,q.length,0) x (q.realFrom x [] ++ p.realFrom x []) := by
  cases q with
  | nil => exact (hne rfl).elim
  | cons head tail =>
    simp only [binary, real, realFrom_concat]
    rw [realFrom_empty_append (head :: tail) hq]
    rfl

lemma binary_register_left (p q : NumericProgram) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD q.length 0 = p.real x := by
  have he := q.realFrom_length x []
  simp only [List.length_nil, Nat.add_zero] at he
  rw [← he]
  simp only [List.getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

lemma binary_register_right (p q : NumericProgram) (hne : q ≠ []) (x : Fin d → ℝ) :
    (q.realFrom x [] ++ p.realFrom x []).getD 0 0 = q.real x := by
  apply realFrom_head
  simpa only [realFrom_length, List.length_nil, Nat.add_zero] using List.length_pos_iff.mpr hne

lemma binary_valid (j : Fin 9) (p q : NumericProgram) (hq : q.Closed) (hj : j ≠ 5)
    (x : Fin d → ℝ) (hpv : p.Valid x) (hqv : q.Valid x) : (binary j p q).Valid x := by
  apply (validFrom_concat _ _ _ _).mpr
  refine ⟨(validFrom_concat _ _ _ _).mpr ⟨hpv,
    (validFrom_of_closed q hq x _).mpr hqv⟩, ?_⟩
  exact ⟨fun h => (hj h).elim, trivial⟩

lemma binary_closed (j : Fin 9) (p q : NumericProgram) (hp : p.Closed) (hq : q.Closed)
    (hnep : p ≠ []) (hneq : q ≠ []) (hj : j = 2 ∨ j = 3) : (binary j p q).Closed := by
  have hn : 0 < p.length := List.length_pos_iff.mpr hnep
  have hqn : 0 < q.length := List.length_pos_iff.mpr hneq
  apply (scopedFrom_concat _ _ _).mpr
  refine ⟨(scopedFrom_concat _ _ _).mpr ⟨hp, q.scopedFrom_mono (Nat.zero_le _) hq⟩, ?_⟩
  rcases hj with rfl | rfl <;>
    simp only [ScopedFrom, NumericOp.Scoped, NumericOp.tag, NumericOp.left,
      NumericOp.right, List.length_append]
  all_goals exact ⟨⟨by omega, by omega⟩,trivial⟩

lemma binary_add_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 2 p q).real x = p.real x + q.real x := by
  rw [binary_real 2 p q hq hne]
  exact congrArg₂ (· + ·) (binary_register_left p q x) (binary_register_right p q hne x)

lemma binary_mul_real (p q : NumericProgram) (hq : q.Closed) (hne : q ≠ []) (x : Fin d → ℝ) :
    (binary 3 p q).real x = p.real x * q.real x := by
  rw [binary_real 3 p q hq hne]
  exact congrArg₂ (· * ·) (binary_register_left p q x) (binary_register_right p q hne x)

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e] {f g : (Fin d → ℝ) → ℝ}

lemma literal (q : ℚ) : Elementary (fun _ : Fin d → ℝ => (q : ℝ)) :=
  ⟨NumericProgram.literal q, by simp [NumericProgram.literal],
    NumericProgram.literal_closed q, NumericProgram.literal_valid q, rfl⟩

lemma coordinate (k : Fin d) : Elementary (fun z : Fin d → ℝ => z k) :=
  ⟨NumericProgram.coordinate k, by simp [NumericProgram.coordinate],
    NumericProgram.coordinate_closed k, NumericProgram.coordinate_valid k,
    funext (NumericProgram.coordinate_real k)⟩

lemma add (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x + g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 2 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 2 p q hpc hqc hpn hqn (Or.inl rfl),
    fun x => NumericProgram.binary_valid 2 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_add_real p q hqc hqn)⟩

lemma mul (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x * g x) := by
  obtain ⟨p, hpn, hpc, hpv, rfl⟩ := hf
  obtain ⟨q, hqn, hqc, hqv, rfl⟩ := hg
  exact ⟨NumericProgram.binary 3 p q, by simp [NumericProgram.binary],
    NumericProgram.binary_closed 3 p q hpc hqc hpn hqn (Or.inr rfl),
    fun x => NumericProgram.binary_valid 3 p q hqc (by decide) x (hpv x) (hqv x),
    funext (NumericProgram.binary_mul_real p q hqc hqn)⟩

lemma neg (hf : Elementary f) : Elementary (fun x => -f x) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 4 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 4 0 p hc hn (Or.inl rfl),
    fun x => NumericProgram.unary_valid 4 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma sub (hf : Elementary f) (hg : Elementary g) : Elementary (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma inv (hf : Elementary f) (n : ℕ) (hn : ∀ x, ((n+1:ℕ):ℝ)⁻¹ ≤ f x) :
    Elementary (fun x => (f x)⁻¹) := by
  obtain ⟨p, hne, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 5 n p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 5 n p hc hne (Or.inr (Or.inl rfl)),
    fun x => NumericProgram.unary_valid 5 n p x (hv x) (fun _ => hn x), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma exp (hf : Elementary f) : Elementary (fun x => Real.exp (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨NumericProgram.unary 7 0 p, by simp [NumericProgram.unary],
    NumericProgram.unary_closed 7 0 p hc hn (Or.inr (Or.inr rfl)),
    fun x => NumericProgram.unary_valid 7 0 p x (hv x) (by simp), ?_⟩
  funext x
  rw [NumericProgram.unary_real]
  rfl

lemma rho (n : ℕ) (hf : Elementary f) : Elementary (fun x => rhoJet n (f x)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p ++ [(6,0,n,0)], by simp, ?_, ?_, ?_⟩
  · apply (NumericProgram.scopedFrom_concat _ _ _).mpr
    exact ⟨hc, ⟨by simpa [NumericOp.Scoped, NumericOp.tag, NumericOp.right] using List.length_pos_iff.mpr hn, trivial⟩⟩
  · intro x
    exact (NumericProgram.validFrom_concat _ _ _ _).mpr ⟨hv x, ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩⟩
  · funext x
    simp only [NumericProgram.real, NumericProgram.realFrom_concat]
    rfl

lemma logLiteral (q : ℚ) : Elementary (fun _ : Fin d → ℝ => if 0 < q then Real.log (q : ℝ) else 0) := by
  refine ⟨[(8,q,0,0)], by simp, by simp [NumericProgram.Closed, NumericProgram.ScopedFrom, NumericOp.Scoped, NumericOp.tag], ?_, rfl⟩
  intro x
  exact ⟨by simp [NumericOp.Valid, NumericOp.tag], trivial⟩

lemma differentiable (hf : Elementary f) : Differentiable ℝ f := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact fun x => p.differentiableAt x (hv x)

lemma coordinateDerivative (hf : Elementary f) (k : Fin d) :
    Elementary (fun x => fderiv ℝ f x (Pi.single k 1)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p.jetStep k, ?_, p.jetStep_closed k hc, fun x => p.jetStep_valid k (hv x), ?_⟩
  · apply List.length_pos_iff.mp
    rw [NumericProgram.jetStep_length]
    exact Nat.mul_pos (by decide) (List.length_pos_iff.mpr hn)
  · funext x
    exact p.jetStep_real k x (hv x)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ i ∈ s, Elementary (f i)) : Elementary (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (literal (d := d) 0)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e]

lemma zero : Elementary (fun _ : Fin d → ℝ => (0 : ℝ)) := by simpa using (literal (d := d) 0)

lemma div_rat (q : ℚ) {f : (Fin d → ℝ) → ℝ} (hf : Elementary f) :
    Elementary (fun x => f x / (q : ℝ)) := by
  simpa [div_eq_mul_inv] using hf.mul (literal q⁻¹)

lemma operation (o : NumericOp) (g : (Fin d → ℝ) → (Fin e → ℝ))
    (s : (Fin d → ℝ) → List ℝ)
    (hg : ∀ k, Elementary (fun x => g x k))
    (hs : ∀ n, Elementary (fun x => (s x).getD n 0))
    (hv : ∀ x, o.Valid (s x)) : Elementary (fun x => o.real e (g x) (s x)) := by
  rcases o with ⟨j,q,a,b⟩
  fin_cases j <;> dsimp only [NumericOp.real, NumericOp.tag, NumericOp.rat,
    NumericOp.left, NumericOp.right]
  · exact literal q
  · exact hg _
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · exact (hs a).inv b (fun x => hv x rfl)
  · exact (hs b).rho a
  · exact (hs a).exp
  · exact logLiteral q

lemma program_registers (p : NumericProgram)
    (g : (Fin d → ℝ) → (Fin e → ℝ)) (s : (Fin d → ℝ) → List ℝ)
    (hg : ∀ k, Elementary (fun x => g x k))
    (hs : ∀ n, Elementary (fun x => (s x).getD n 0))
    (hv : ∀ x, p.ValidFrom (g x) (s x)) :
    ∀ n, Elementary (fun x => (p.realFrom (g x) (s x)).getD n 0) := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun x => o.real e (g x) (s x) :: s x)
    · intro n
      cases n with
      | zero => exact operation o g s hg hs (fun x => (hv x).1)
      | succ n => exact hs n
    · exact fun x => (hv x).2

lemma comp {f : (Fin e → ℝ) → ℝ} (hf : Elementary f)
    (g : (Fin d → ℝ) → (Fin e → ℝ))
    (hg : ∀ k, Elementary (fun x => g x k)) : Elementary (fun x => f (g x)) := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact program_registers p g (fun _ => []) hg (fun n => by simpa using (zero (d:=d)))
    (fun x => hv (g x)) 0

end BalancedTransport.Effectivity.Elementary
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Sobolev ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma supportedL2Curve_coe {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) (t : ℝ) :
    (supportedL2Curve hK hv hs t : Space → F) =ᵐ[volume] v t := MemLp.coeFn_toLp _

lemma supportL2Size_nonneg (K : Set Space) (hK : IsCompact K) : 0 ≤ supportL2Size K hK :=
  norm_nonneg _

omit [NormedSpace ℝ F] in
lemma lp_norm_bound_of_support {K : Set Space} (hK : IsCompact K)
    {f : Lp F 2 (volume : Measure Space)} {g : Space → F} {C : ℝ}
    (he : (f : Space → F) =ᵐ[volume] g) (hs : ∀ x, x ∉ K → g x = 0)
    (hb : ∀ x, ‖g x‖ ≤ C) : ‖f‖ ≤ C * supportL2Size K hK := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [he, indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure Space))
      (hs := hK.measurableSet) (hμs := hK.measure_lt_top.ne) (c := (1 : ℝ))] with x hfx hix
  rw [hfx, hix]
  by_cases hx : x ∈ K
  · simpa only [indicator_of_mem hx, norm_one, mul_one] using hb x
  · simp only [indicator_of_notMem hx, hs x hx, norm_zero, mul_zero, le_refl]

lemma time_difference_bound {v : Field F} (hv : JointSmooth v) {C : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Space) :
    ‖v s x - v t x‖ ≤ C * ‖s - t‖ :=
  (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun r _ => (hv.timeSlice x).differentiable (by simp) r)
    (fun r hr => hb r hr x) ht hs

lemma time_remainder_bound {v : Field F} (hv : JointSmooth v) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : Space) :
    ‖v s x - v t x - (s - t) • fullTimeD v t x‖ ≤ B * ‖s - t‖ * ‖s - t‖ := by
  let r : ℝ → F := fun q => v q x - v t x - (q - t) • fullTimeD v t x
  have hdr (q : ℝ) : HasDerivAt r (fullTimeD v q x - fullTimeD v t x) q := by
    convert (((hv.timeSlice x).differentiable (by simp) q).hasDerivAt.sub_const (v t x)).sub
        (((hasDerivAt_id q).sub_const t).smul_const (fullTimeD v t x)) using 1 <;>
      simp only [r, fullTimeD, id_eq, one_smul]
    rfl
  have hbound (q : ℝ) (hq : q ∈ uIcc t s) :
      ‖deriv r q‖ ≤ B * ‖s - t‖ := by
    rw [(hdr q).deriv]
    have hq₀ : 0 ≤ q := (le_min ht hs).trans hq.1
    refine (time_difference_bound hv.fullTimeD hb hq₀ ht x).trans ?_
    apply mul_le_mul_of_nonneg_left _ hB
    simpa only [Real.dist_eq, ← Real.norm_eq_abs, norm_sub_rev] using
      Real.dist_left_le_of_mem_uIcc hq
  have h := (convex_uIcc t s).norm_image_sub_le_of_norm_deriv_le
    (fun q _ => (hdr q).differentiableAt) hbound (left_mem_uIcc) (right_mem_uIcc)
  simpa only [r, sub_self, zero_smul, sub_zero] using h

lemma supportedL2Curve_difference_bound {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {C : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C)
    {s t : ℝ} (hs₀ : 0 ≤ s) (ht₀ : 0 ≤ t) :
    ‖supportedL2Curve hK hv hs s - supportedL2Curve hK hv hs t‖ ≤
      C * ‖s - t‖ * supportL2Size K hK := by
  apply lp_norm_bound_of_support hK
  · exact (Lp.coeFn_sub _ _).trans ((supportedL2Curve_coe hK hv hs s).sub
      (supportedL2Curve_coe hK hv hs t))
  · intro x hx
    change v s x - v t x = 0
    simp only [hs s x hx, hs t x hx, sub_self]
  · exact fun x => time_difference_bound hv hb hs₀ ht₀ x

lemma supportedL2Curve_continuousOn {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C) :
    ContinuousOn (supportedL2Curve hK hv hs) (Ici 0) := by
  let L : ℝ≥0 := ⟨C * supportL2Size K hK, mul_nonneg hC (supportL2Size_nonneg K hK)⟩
  apply LipschitzOnWith.continuousOn (K := L)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs₀ t ht₀
  simp only [dist_eq_norm]
  change ‖supportedL2Curve hK hv hs s - supportedL2Curve hK hv hs t‖ ≤
    C * supportL2Size K hK * ‖s - t‖
  convert supportedL2Curve_difference_bound hK hv hs hb hs₀ ht₀ using 1
  ring

lemma supportedL2Curve_hasDerivWithinAt {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (supportedL2Curve hK hv hs)
      (supportedL2Curve hK hv.fullTimeD hs.fullTimeD t) (Ici 0) t := by
  let V := supportedL2Curve hK hv hs
  let W := supportedL2Curve hK hv.fullTimeD hs.fullTimeD
  have hrem (s : ℝ) (hs₀ : 0 ≤ s) :
      ‖V s - V t - (s-t) • W t‖ ≤ B * ‖s-t‖ * ‖s-t‖ * supportL2Size K hK := by
    apply lp_norm_bound_of_support hK
    · exact (Lp.coeFn_sub _ _).trans (((Lp.coeFn_sub _ _).trans
        ((supportedL2Curve_coe hK hv hs s).sub (supportedL2Curve_coe hK hv hs t))).sub
        ((Lp.coeFn_smul _ _).trans ((supportedL2Curve_coe hK hv.fullTimeD hs.fullTimeD t).const_smul _)))
    · intro x hx
      change v s x - v t x - (s-t) • fullTimeD v t x = 0
      simp only [hs s x hx, hs t x hx, hs.fullTimeD t x hx, sub_self, smul_zero]
    · exact fun x => time_remainder_bound hv hB hb hs₀ ht x
  apply HasDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hc : ContinuousAt (fun s : ℝ => B * supportL2Size K hK * ‖s-t‖) t := by fun_prop
  have hn : ∀ᶠ s in 𝓝[Ici 0] t, B * supportL2Size K hK * ‖s-t‖ < ε :=
    mem_nhdsWithin_of_mem_nhds (hc.eventually (gt_mem_nhds (by simpa using hε)))
  filter_upwards [self_mem_nhdsWithin, hn] with s hs₀ hsε
  exact (hrem s hs₀).trans (by nlinarith [norm_nonneg (s-t)])

lemma spatialD_eq_fullMixedD (a : List (Fin 3)) (v : Field F) :
    spatialD a v = fullMixedD (a.map some) v := by
  induction a with
  | nil => rfl
  | cons i a ha => simp only [spatialD, List.map_cons, fullMixedD, ha]

theorem CH_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v)
    (k : ℕ) : CH k v := by
  intro a _
  let d := fullMixedD (a.map some) v
  have hd : JointSmooth d := hv.fullMixedD _
  have hds : SpatiallySupported K d := hs.fullMixedD hK.isClosed _
  obtain ⟨C, hC, hbound⟩ := hb (none :: a.map some)
  have he (t : ℝ) (ht : 0 ≤ t) (x : Space) :
      fullTimeD d t x = mixedD (none :: a.map some) v t x :=
    fullMixedD_eq_mixedD hv (none :: a.map some) t ht x
  have hb' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD d t x‖ ≤ C := by
    intro t ht x
    rw [he t ht x]
    exact hbound t ht x
  refine ⟨supportedL2Curve hK hd hds,
    supportedL2Curve_continuousOn hK hd hds hC hb', fun t _ => ?_⟩
  simpa only [spatialD_eq_fullMixedD] using supportedL2Curve_coe hK hd hds t

theorem C1L2_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v) :
    C1L2 v := by
  obtain ⟨C, hC, hc⟩ := hb [none]
  obtain ⟨B, hB, hb'⟩ := hb [none, none]
  have hc' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD v t x‖ ≤ C := by
    intro t ht x
    rw [show fullTimeD v t x = mixedD [none] v t x from fullMixedD_eq_mixedD hv [none] t ht x]
    exact hc t ht x
  have hb'' : ∀ t, 0 ≤ t → ∀ x, ‖fullTimeD (fullTimeD v) t x‖ ≤ B := by
    intro t ht x
    rw [show fullTimeD (fullTimeD v) t x = mixedD [none,none] v t x from
      fullMixedD_eq_mixedD hv [none, none] t ht x]
    exact hb' t ht x
  refine ⟨supportedL2Curve hK hv hs, supportedL2Curve hK hv.fullTimeD hs.fullTimeD,
    supportedL2Curve_continuousOn hK hv hs hC hc',
    supportedL2Curve_continuousOn hK hv.fullTimeD hs.fullTimeD hB hb'', fun t ht => ?_⟩
  refine ⟨supportedL2Curve_coe hK hv hs t, ?_,
    supportedL2Curve_hasDerivWithinAt hK hv hs hB hb'' ht⟩
  apply (supportedL2Curve_coe hK hv.fullTimeD hs.fullTimeD t).trans
  exact Eventually.of_forall (fun x => fullMixedD_eq_mixedD hv [none] t ht x)

lemma boundedOnFiniteSlabs_of_boundedMixed {v : Velocity} (hv : BoundedMixed v) :
    BoundedOnFiniteSlabs v := by
  obtain ⟨C, hC, hb⟩ := hv []
  have hd : ∀ i : Fin 3, ∃ D : ℝ, 0 ≤ D ∧ ∀ t, 0 ≤ t → ∀ x, ‖spaceD i v t x‖ ≤ D :=
    fun i => hv [some i]
  choose D hD hd using hd
  intro T _
  refine ⟨C + ∑ i, D i, add_nonneg hC (Finset.sum_nonneg (fun i _ => hD i)), ?_⟩
  intro t ht x
  constructor
  · exact (hb t ht.1 x).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hD i)))
  · intro i
    exact (hd i t ht.1 x).trans
      ((Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hC))

lemma spatialD_zero (a : List (Fin 3)) : spatialD a (0 : Field F) = 0 := by
  induction a with
  | nil => rfl
  | cons i a ha =>
    simp only [spatialD, ha]
    ext t x
    simp [spaceD]

lemma CH_zero (k : ℕ) : CH k (0 : Field F) := by
  intro a _
  refine ⟨0, continuousOn_const, fun t _ => ?_⟩
  rw [spatialD_zero]
  exact Lp.coeFn_zero F 2 (volume : Measure Space)

theorem comparisonClass_of_compact_boundedMixed {K : Set Space} (hK : IsCompact K)
    {v : Velocity} (hv : JointSmooth v) (hs : SpatiallySupported K v) (hb : BoundedMixed v) :
    ComparisonClass v (fun _ _ => 0) := by
  refine ⟨CH_of_compact_boundedMixed hK hv hs hb 2,
    C1L2_of_compact_boundedMixed hK hv hs hb,
    boundedOnFiniteSlabs_of_boundedMixed hb, fun _ => 0, ?_⟩
  convert CH_zero (F := ℝ) 1 using 1
  ext t x
  exact sub_zero 0

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Loading ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set

lemma loadingSwitch_contDiff : ContDiff ℝ (⊤ : ℕ∞) loadingSwitch := by
  unfold loadingSwitch
  fun_prop

lemma loadingSwitch_nonneg (t : ℝ) : 0 ≤ loadingSwitch t :=
  Real.smoothTransition.nonneg _

lemma loadingSwitch_le_one (t : ℝ) : loadingSwitch t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma loadingSwitch_zero {t : ℝ} (ht : t ≤ 1 / 4) : loadingSwitch t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma loadingSwitch_one {t : ℝ} (ht : 3 / 4 ≤ t) : loadingSwitch t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma loadingCenter_contDiff (z : Space) : ContDiff ℝ (⊤ : ℕ∞) (loadingCenter z) :=
  loadingSwitch_contDiff.smul contDiff_const

lemma loadingVelocity_jointSmooth (z : Space) (η : ℝ) :
    JointSmooth (loadingVelocity z η) :=
  movingBoxVelocity_jointSmooth (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) _ _ _

lemma loadingVelocity_divergence (z : Space) (η t : ℝ) (x : Space) :
    div (loadingVelocity z η) t x = 0 :=
  movingBoxVelocity_divergence (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) _ _ _ _ _

lemma loadingCenter_deriv_zero {z : Space} {t : ℝ} (ht : t < 1 / 4 ∨ 3 / 4 < t) :
    deriv (loadingCenter z) t = 0 := by
  rcases ht with ht | ht
  · have he : loadingCenter z =ᶠ[𝓝 t] fun _ => (0 : Space) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [loadingCenter, loadingSwitch_zero hs.le]
    rw [he.deriv_eq, deriv_const]
  · have he : loadingCenter z =ᶠ[𝓝 t] fun _ => z - fixedLabel := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [loadingCenter, loadingSwitch_one hs.le]
    rw [he.deriv_eq, deriv_const]

lemma loadingVelocity_zero {z : Space} {η t : ℝ} (ht : t < 1 / 4 ∨ 3 / 4 < t) :
    loadingVelocity z η t = 0 :=
  movingBoxVelocity_zero (loadingCenter_deriv_zero ht) (by intros; simp)

lemma loadingPath_hasDerivAt (z : Space) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (loadingPath z) (loadingVelocity z η t (loadingPath z t)) t :=
  affinePath_hasDerivAt hη (loadingCenter_contDiff z) contDiff_const
    (by intros; norm_num) (by intros; simp) (by exact ⟨le_rfl, le_rfl⟩) t

lemma loadingPath_eq (z : Space) (t : ℝ) (i : Fin 3) :
    loadingPath z t i = (1 - loadingSwitch t) * fixedLabel i + loadingSwitch t * z i := by
  dsimp [loadingPath, affinePath, loadingCenter]
  ring

lemma loadingPath_start (z : Space) : loadingPath z 0 = fixedLabel := by
  ext i
  rw [loadingPath_eq, loadingSwitch_zero (by norm_num)]
  ring

lemma loadingPath_end (z : Space) : loadingPath z 1 = z := by
  ext i
  rw [loadingPath_eq, loadingSwitch_one (by norm_num)]
  ring

lemma loadingPath_between (z : Space) (t : ℝ) (i : Fin 3) :
    min (fixedLabel i) (z i) ≤ loadingPath z t i ∧
      loadingPath z t i ≤ max (fixedLabel i) (z i) := by
  rw [loadingPath_eq]
  have h₀ := loadingSwitch_nonneg t
  have h₁ := loadingSwitch_le_one t
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left (fixedLabel i) (z i)))
        (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr (min_le_right (fixedLabel i) (z i))) h₀]
  · nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left (fixedLabel i) (z i)))
        (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr (le_max_right (fixedLabel i) (z i))) h₀]

lemma loadingSupport_compact (z : Space) (η : ℝ) : IsCompact (loadingSupport z η) :=
  isCompact_Icc

lemma loadingVelocity_repeats (z : Space) (η : ℝ) : RepeatsAfter 1 (loadingVelocity z η) := by
  intro t ht
  rw [loadingVelocity_zero (Or.inr (by linarith)),
    loadingVelocity_zero (Or.inr (by linarith))]

lemma loadingVelocity_boundedMixed (z : Space) {η : ℝ} (hη : 0 < η) :
    BoundedMixed (loadingVelocity z η) :=
  boundedMixed_of_compact_repeating (loadingSupport_compact z η)
    (loadingVelocity_jointSmooth z η) (loadingVelocity_supported z hη)
    (loadingVelocity_repeats z η)

theorem loadingPath_avoids_observer {z : Space} (hz : 4 ≤ z 0) (t : ℝ) :
    loadingPath z t ∉ observer := by
  intro h
  have hh : loadingPath z t 0 < 2 := (Set.mem_pi.mp h 0 (Set.mem_univ _)).2
  have hb := (loadingPath_between z t 0).1
  have hf : fixedLabel 0 = 4 := rfl
  rw [hf, min_eq_left hz] at hb
  linarith

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Material ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma exists_curve_on_interval {v : ℝ → E → E} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => v t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖v t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    {T : ℝ} (hT : 0 ≤ T) (a : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧ Continuous γ ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt γ (v t (γ t)) (Icc 0 T) t := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  let R : ℝ≥0 := ⟨(L : ℝ) * T, mul_nonneg L.coe_nonneg hT⟩
  have hp : IsPicardLindelof v t₀ a R 0 L K := by
    constructor
    · intro t ht
      exact (hl t ht.1).lipschitzOnWith
    · intro x _
      exact (hc x).mono Icc_subset_Ici_self
    · intro t ht x _
      exact hb t ht.1 x
    · change (L : ℝ) * max (T - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (L : ℝ) * T - 0
      simp [t₀, max_eq_left hT]
  have ha : a ∈ closedBall a (0 : ℝ≥0) := by simp
  obtain ⟨γ, hγ⟩ := ODE.FunSpace.exists_isFixedPt_next hp ha
  have he : ∀ t ∈ Icc (0 : ℝ) T,
      γ.compProj t = ODE.picard v 0 a γ.compProj t := by
    intro t ht
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact (ODE.FunSpace.isFixedPt_next_iff hp ha).mp hγ ⟨t, ht⟩
  refine ⟨γ.compProj, ?_, γ.continuous_compProj, fun t ht => ?_⟩
  · rw [he 0 ⟨le_rfl, hT⟩, ODE.picard_apply₀]
  · exact (ODE.hasDerivWithinAt_picard_Icc ⟨le_rfl, hT⟩ hp.continuousOn_uncurry
      γ.continuous_compProj.continuousOn
      (fun s hs => γ.compProj_mem_closedBall hp.mul_max_le) a ht).congr
      he (he t ht)

omit [CompleteSpace E] in
lemma hasDerivWithinAt_forward_of_Icc {γ : ℝ → E} {d : E} {t T : ℝ}
    (hd : HasDerivWithinAt γ d (Icc 0 T) t) (ht : t < T) :
    HasDerivWithinAt γ d (Ici 0) t := by
  apply hd.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hs₀ hs₁
  exact ⟨hs₀, hs₁.le⟩

omit [CompleteSpace E] in
lemma curves_agree_on_overlap {v : ℝ → E → E} {K : ℝ≥0}
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t))
    {γ δ : ℝ → E} {S T : ℝ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) S))
    (hδ : ContinuousOn δ (Icc (0 : ℝ) T))
    (hdγ : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt γ (v t (γ t)) (Icc 0 S) t)
    (hdδ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt δ (v t (δ t)) (Icc 0 T) t)
    (hinit : γ 0 = δ 0) {t : ℝ} (ht : 0 ≤ t) (htS : t ≤ S) (htT : t ≤ T) :
    γ t = δ t := by
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
      (fun s hs => (hl s hs.1).lipschitzOnWith)
      (hγ.mono (Icc_subset_Icc_right htS)) _ (fun _ _ => mem_univ _)
      (hδ.mono (Icc_subset_Icc_right htT)) _ (fun _ _ => mem_univ _) hinit ⟨ht, le_rfl⟩
  · intro s hs
    exact (hasDerivWithinAt_forward_of_Icc (hdγ s ⟨hs.1, hs.2.le.trans htS⟩)
      (hs.2.trans_le htS)).mono (Ici_subset_Ici.mpr hs.1)
  · intro s hs
    exact (hasDerivWithinAt_forward_of_Icc (hdδ s ⟨hs.1, hs.2.le.trans htT⟩)
      (hs.2.trans_le htT)).mono (Ici_subset_Ici.mpr hs.1)

theorem exists_global_curve {v : ℝ → E → E} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => v t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖v t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (v t)) (a : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧
      ∀ t, 0 ≤ t → HasDerivWithinAt γ (v t (γ t)) (Ici 0) t := by
  have hex (n : ℕ) := exists_curve_on_interval hc hb hl
    (T := (n : ℝ) + 1) (by positivity) a
  choose C hC₀ hCcts hCd using hex
  have hagree (m n : ℕ) {t : ℝ} (ht : 0 ≤ t)
      (htm : t ≤ (m : ℝ) + 1) (htn : t ≤ (n : ℝ) + 1) : C m t = C n t :=
    curves_agree_on_overlap hl (hCcts m).continuousOn (hCcts n).continuousOn
      (hCd m) (hCd n) ((hC₀ m).trans (hC₀ n).symm) ht htm htn
  let γ : ℝ → E := fun t => C ⌈t⌉₊ t
  have heq (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (htn : t ≤ (n : ℝ) + 1) : γ t = C n t :=
    hagree ⌈t⌉₊ n ht (by linarith [Nat.le_ceil t]) htn
  refine ⟨γ, hC₀ _, fun t ht => ?_⟩
  let n := ⌈t⌉₊
  have htlt : t < (n : ℝ) + 1 := by dsimp [n]; linarith [Nat.le_ceil t]
  have hd := hasDerivWithinAt_forward_of_Icc (hCd n t ⟨ht, htlt.le⟩) htlt
  have hne : γ =ᶠ[𝓝[Ici 0] t] C n := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htlt)] with s hs₀ hs₁
    exact heq n hs₀ hs₁.le
  rw [heq n ht htlt.le]
  exact hd.congr_of_eventuallyEq hne (heq n ht htlt.le)

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set Metric

theorem exists_materialFlow_of_bounded_lipschitz {U : Velocity} {L K : ℝ≥0}
    (hc : ∀ x, ContinuousOn (fun t => U t x) (Ici 0))
    (hb : ∀ t, 0 ≤ t → ∀ x, ‖U t x‖ ≤ L)
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (U t)) :
    ∃ X : MaterialFlow, IsMaterialFlow U X := by
  choose γ hγ₀ hγd using exists_global_curve hc hb hl
  exact ⟨fun t a => γ a t, hγ₀, hγd⟩

theorem materialFlow_unique {U : Velocity} {X Y : MaterialFlow} {K : ℝ≥0}
    (hl : ∀ t, 0 ≤ t → LipschitzWith K (U t))
    (hX : IsMaterialFlow U X) (hY : IsMaterialFlow U Y)
    {t : ℝ} (ht : 0 ≤ t) (a : Space) : X t a = Y t a := by
  apply curves_agree_on_overlap hl
      (HasDerivWithinAt.continuousOn (fun s hs => (hX.2 a s hs.1).mono Icc_subset_Ici_self))
      (HasDerivWithinAt.continuousOn (fun s hs => (hY.2 a s hs.1).mono Icc_subset_Ici_self))
      (fun s hs => (hX.2 a s hs.1).mono Icc_subset_Ici_self)
      (fun s hs => (hY.2 a s hs.1).mono Icc_subset_Ici_self)
      ((hX.1 a).trans (hY.1 a).symm) ht le_rfl le_rfl

lemma norm_linearMap_le_sum_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Space →L[ℝ] F) : ‖A‖ ≤ ∑ i : Fin 3, ‖A (Pi.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have he : A x = ∑ i : Fin 3, x i • A (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  rw [he]
  calc
    ‖∑ i : Fin 3, x i • A (Pi.single i 1)‖ ≤
        ∑ i : Fin 3, ‖x i • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖A (Pi.single i 1)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖A (Pi.single i 1)‖) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

lemma spatial_lipschitz_of_boundedMixed {U : Velocity}
    (hU : JointSmooth U) (hb : BoundedMixed U) :
    ∃ K : ℝ≥0, ∀ t, 0 ≤ t → LipschitzWith K (U t) := by
  choose C hC hbound using fun i : Fin 3 => hb [some i]
  let K : ℝ≥0 := ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i)⟩
  refine ⟨K, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
    ((hU.slice t).differentiable (by simp)) (fun x => ?_)⟩
  change ‖fderiv ℝ (U t) x‖ ≤ ∑ i, C i
  apply (norm_linearMap_le_sum_basis _).trans
  exact Finset.sum_le_sum (fun i _ => hbound i t ht x)

theorem exists_materialFlow_of_boundedMixed {U : Velocity}
    (hU : JointSmooth U) (hb : BoundedMixed U) :
    ∃ X : MaterialFlow, IsMaterialFlow U X := by
  obtain ⟨L, hL, hbound⟩ := hb []
  obtain ⟨K, hK⟩ := spatial_lipschitz_of_boundedMixed hU hb
  apply exists_materialFlow_of_bounded_lipschitz (L := ⟨L, hL⟩) (K := K)
  · intro x
    exact (hU.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  · exact hbound
  · exact hK

theorem exists_materialFlow_of_compact_repeating {K : Set Space} (hK : IsCompact K)
    {U : Velocity} (hU : JointSmooth U) (hs : SpatiallySupported K U)
    (hp : RepeatsAfter 1 U) : ∃ X : MaterialFlow, IsMaterialFlow U X :=
  exists_materialFlow_of_boundedMixed hU (boundedMixed_of_compact_repeating hK hU hs hp)

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Periodic ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set

lemma repeatTemplate_zero_period (v : Velocity) : Function.Periodic (repeatTemplate v) 1 := by
  intro t
  funext x
  change (∑' n : ℤ, v (t + 1 - n) x) = ∑' n : ℤ, v (t - n) x
  have hh := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => v (t + 1 - n) x)
  simpa only [Equiv.coe_addRight, Int.cast_add, Int.cast_one, add_sub_add_right_eq_sub] using hh.symm

lemma repeatTemplate_on_unit {v : Velocity} (hc : TimeCollars v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : repeatTemplate v t = v t := by
  funext x
  simpa using repeatTemplate_eq hc (n := 0) (by norm_num; constructor <;> linarith [ht.1, ht.2]) x

lemma repeatTemplate_supported {K : Set Space} {v : Velocity} (hs : SpatiallySupported K v) :
    SpatiallySupported K (repeatTemplate v) := by
  intro t x hx
  simp only [repeatTemplate, hs _ x hx, tsum_zero]

lemma repeatTemplate_divergence {v : Velocity} (hc : TimeCollars v)
    (hd : ∀ t x, div v t x = 0) (t : ℝ) (x : Space) :
    div (repeatTemplate v) t x = 0 := by
  have he : repeatTemplate v t = v (t - (⌊t⌋ : ℤ)) := by
    funext y
    apply repeatTemplate_eq hc
    have h₁ := Int.floor_le t
    have h₂ := Int.lt_floor_add_one t
    constructor <;> linarith
  simpa only [div, spaceD, he] using hd (t - (⌊t⌋ : ℤ)) x

lemma loadedRepeat_jointSmooth {load v : Velocity} (hl : JointSmooth load)
    (hv : JointSmooth v) (hc : TimeCollars v) : JointSmooth (loadedRepeat load v) := by
  have hg : JointSmooth (fun t (_ : Space) => afterLoadingGate t) := by
    dsimp [JointSmooth, afterLoadingGate]
    fun_prop
  exact hl.add (hg.smul (repeatTemplate_jointSmooth hv hc))

lemma loadedRepeat_before {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : loadedRepeat load v t = load t := by
  have hs : afterLoadingGate t • repeatTemplate v t = (0 : Space → Space) := by
    by_cases ht : t ≤ 3 / 4
    · have he : afterLoadingGate t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [he, zero_smul]
    · rw [repeatTemplate_on_unit hc ⟨ht₀, ht₁⟩, hc t (Or.inr (lt_of_not_ge ht)), smul_zero]
  ext x i
  change (load t x + (afterLoadingGate t • repeatTemplate v t) x) i = load t x i
  rw [hs]
  simp

lemma loadedRepeat_after {load v : Velocity} (hl : TimeCollars load)
    {t : ℝ} (ht : 1 ≤ t) : loadedRepeat load v t = repeatTemplate v t := by
  have he : afterLoadingGate t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  ext x i
  simp [loadedRepeat, he, hl t (Or.inr (by linarith))]

lemma loadedRepeat_support {K L : Set Space} {load v : Velocity}
    (hl : SpatiallySupported L load) (hv : SpatiallySupported K v) :
    SpatiallySupported (L ∪ K) (loadedRepeat load v) := by
  intro t x hx
  have hn := not_or.mp hx
  dsimp [loadedRepeat]
  rw [hl t x hn.1, repeatTemplate_supported hv t x hn.2, smul_zero, add_zero]

lemma loadedRepeat_repeats {load v : Velocity} (hl : TimeCollars load) :
    RepeatsAfter 1 (loadedRepeat load v) := by
  intro t ht
  rw [loadedRepeat_after hl (by linarith), loadedRepeat_after hl ht]
  exact repeatTemplate_zero_period v t

lemma div_add {u v : Velocity} (hu : JointSmooth u) (hv : JointSmooth v) (t : ℝ) (x : Space) :
    div (fun t x => u t x + v t x) t x = div u t x + div v t x := by
  simp only [div, spaceD,
    fderiv_fun_add ((hu.slice t).differentiable (by simp) x)
      ((hv.slice t).differentiable (by simp) x), add_apply, Pi.add_apply, Finset.sum_add_distrib]

lemma div_time_smul {u : Velocity} (hu : JointSmooth u) (a : ℝ → ℝ) (t : ℝ) (x : Space) :
    div (fun t x => a t • u t x) t x = a t * div u t x := by
  simp only [div, spaceD, fderiv_fun_const_smul ((hu.slice t).differentiable (by simp) x),
    smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma loadedRepeat_divergence {load v : Velocity} (hl : JointSmooth load)
    (hv : JointSmooth v) (hc : TimeCollars v)
    (hld : ∀ t x, div load t x = 0) (hvd : ∀ t x, div v t x = 0) (t : ℝ) (x : Space) :
    div (loadedRepeat load v) t x = 0 := by
  have hr := repeatTemplate_jointSmooth hv hc
  have hg : JointSmooth (fun t (_ : Space) => afterLoadingGate t) := by
    dsimp [JointSmooth, afterLoadingGate]
    fun_prop
  change div (fun t x => load t x + afterLoadingGate t • repeatTemplate v t x) t x = 0
  have hgr : JointSmooth (fun t x => afterLoadingGate t • repeatTemplate v t x) := hg.smul hr
  rw [div_add hl hgr, div_time_smul hr, hld t x, repeatTemplate_divergence hc hvd]
  ring

theorem loaded_template_realization (z : Space) {η : ℝ} (hη : 0 < η)
    {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hd : ∀ t x, div v t x = 0) :
    let U := loadedRepeat (loadingVelocity z η) v
    JointSmooth U ∧ SpatiallySupported (loadingSupport z η ∪ K) U ∧
    BoundedMixed U ∧ (∀ x, U 0 x = 0) ∧
    Function.Periodic (repeatTemplate v) 1 ∧
    (∀ t, 1 ≤ t → U t = repeatTemplate v t) ∧
    (∃ X, IsMaterialFlow U X) ∧
    ∀ ν : ℝ, ZeroDataSolution ν
      (affineForce (inertialCoefficient U) (viscousCoefficient U) ν) U (fun _ _ => 0) := by
  let load := loadingVelocity z η
  have hl : JointSmooth load := loadingVelocity_jointSmooth z η
  have hlc : TimeCollars load := fun _ ht => loadingVelocity_zero ht
  have hU := loadedRepeat_jointSmooth hl hv hc
  have hUs := loadedRepeat_support (loadingVelocity_supported z hη) hs
  have hUp := loadedRepeat_repeats (v := v) hlc
  have hUc := (loadingSupport_compact z η).union hK
  have hzero : ∀ x, loadedRepeat load v 0 x = 0 := by
    intro x
    rw [loadedRepeat_before hc le_rfl (by norm_num), hlc 0 (Or.inl (by norm_num))]
    rfl
  exact ⟨hU, hUs, boundedMixed_of_compact_repeating hUc hU hUs hUp, hzero,
    repeatTemplate_zero_period v, fun _ ht => loadedRepeat_after hlc ht,
    exists_materialFlow_of_compact_repeating hUc hU hUs hUp,
    fun ν => residual_zero_pressure_solution ν _ hU.smooth hzero
      (fun t _ x => loadedRepeat_divergence hl hv hc (loadingVelocity_divergence z η) hd t x)⟩

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Realization ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

theorem prescribed_residual_realization {K : Set Space} (hK : IsCompact K)
    {U : Velocity} (hU : JointSmooth U) (hs : SpatiallySupported K U)
    (hp : RepeatsAfter 1 U) (hzero : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    Smooth U ∧ Smooth (inertialCoefficient U) ∧ Smooth (viscousCoefficient U) ∧
    CommonCompactSupport U (inertialCoefficient U) (viscousCoefficient U) ∧
    BoundedMixed U ∧ BoundedMixed (inertialCoefficient U) ∧ BoundedMixed (viscousCoefficient U) ∧
    PeriodicAfterOne U ∧ ComparisonClass U (fun _ _ => 0) ∧
    (∃ X, IsMaterialFlow U X ∧ ∀ Y, IsMaterialFlow U Y →
      ∀ t, 0 ≤ t → ∀ x, X t x = Y t x) ∧
    ∀ ν : ℝ, 0 < ν → let f := affineForce (inertialCoefficient U) (viscousCoefficient U) ν
      ZeroDataSolution ν f U (fun _ _ => 0) ∧
      Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧ UniqueInComparison ν f U := by
  obtain ⟨hf₀, hf₁, hsupport, hbound, hb₀, hb₁, hperiod, hres⟩ :=
    prescribed_residual_regularity hK hU hs hp hzero hdiv
  have hclass := comparisonClass_of_compact_boundedMixed hK hU hs hbound
  obtain ⟨X, hX⟩ := exists_materialFlow_of_boundedMixed hU hbound
  obtain ⟨K', hK'⟩ := spatial_lipschitz_of_boundedMixed hU hbound
  refine ⟨hU.smooth, hf₀, hf₁, hsupport, hbound, hb₀, hb₁, hperiod, hclass,
    ⟨X, hX, fun Y hY t ht x => materialFlow_unique hK' hX hY ht x⟩, ?_⟩
  intro ν hν
  obtain ⟨hsol, hsm, hb, hp'⟩ := hres ν
  exact ⟨hsol, hsm, hb, hp', Analysis.unique_in_comparison hν.le hsol hclass⟩

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Motion ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma positive_start (m : BoxMotion A B safe η) : A.Positive := by
  have hh := m.positive 0
  rwa [m.start_width 0 le_rfl] at hh

end BalancedTransport.Geometry.BoxMotion
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryMotion ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma rat (q : ℚ) : RationalConstant (q : ℝ) := ⟨q,rfl⟩

lemma nat (n : ℕ) : RationalConstant (n : ℝ) := ⟨n, by simp⟩

lemma zero : RationalConstant 0 := by simpa using rat 0

lemma add {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a+b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a+b, by simp⟩

lemma mul {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a*b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a*b, by simp⟩

lemma elementary {d : ℕ} [NeZero d] {a : ℝ} (ha : RationalConstant a) :
    Elementary (fun _ : Fin d → ℝ => a) := by
  obtain ⟨a,rfl⟩ := ha; exact Elementary.literal a

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry Set

lemma const {c : ℝ} (hc : RationalConstant c) : ElementaryCurve (fun _ => c) := hc.elementary

lemma id : ElementaryCurve (fun t => t) := Elementary.coordinate 0

lemma sub {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t - g t) := Elementary.sub hf hg

lemma mul {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t * g t) := Elementary.mul hf hg

lemma comp {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f (g t)) := Elementary.comp hf (fun x _ => g (x 0)) (fun _ => hg)

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryMotion
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

end BalancedTransport.Effectivity.ElementaryMotion
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryCalculus ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
open BalancedTransport.Geometry

lemma congr {d : ℕ} [NeZero d] {f g : (Fin d → ℝ) → ℝ} (hf : Elementary f) (he : ∀x, f x = g x) : Elementary g := by
  rwa [← funext he]

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma fieldArgs_space_hasFDerivAt {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    HasFDerivAt (fun y => fieldArgs p t y)
      (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
        Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
          (fun _ => 0) k)) x := by
  apply hasFDerivAt_pi.mpr
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [fieldArgs] using hasFDerivAt_const t x
    · simpa [fieldArgs] using hasFDerivAt_apply i x
  · intro j
    simpa [fieldArgs] using hasFDerivAt_const (p j) x

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma fullTimeD (h : ElementaryScalar f) : ElementaryScalar (fun p => Geometry.fullTimeD (f p)) := by
  have hd := h.coordinateDerivative (Fin.castAdd d 0)
  apply hd.congr
  intro z
  have hh := (h.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp_hasDerivAt (fieldTime z) (fieldArgs_time_hasDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,Geometry.fullTimeD] using he.deriv.symm

end BalancedTransport.Effectivity.ElementaryScalar
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryFields ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma add (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x + g p t x) := Elementary.add hf hg

lemma mul (hf : ElementaryScalar f) (hg : ElementaryScalar g) : ElementaryScalar (fun p t x => f p t x * g p t x) := Elementary.mul hf hg

lemma neg (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => -f p t x) := Elementary.neg hf

lemma div_rat (q : ℚ) (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => f p t x / (q : ℝ)) := Elementary.div_rat q hf

lemma div_const {q : ℝ} (hq : RationalConstant q) (hf : ElementaryScalar f) : ElementaryScalar (fun p t x => f p t x / q) := by
  obtain ⟨q,rfl⟩ := hq; exact hf.div_rat q

lemma time : ElementaryScalar (fun _ : Fin d → ℝ => fun t _ => t) := Elementary.coordinate (Fin.castAdd d 0)

lemma curve {h : ℝ → ℝ} (hh : ElementaryCurve h) (hf : ElementaryScalar f) :
    ElementaryScalar (fun p t x => h (f p t x)) :=
  Elementary.comp hh (fun z _ => f (fieldParam z) (fieldTime z) (fieldSpace z)) (fun _ => hf)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → Field ℝ)
    (hf : ∀ i ∈ s, ElementaryScalar (f i)) : ElementaryScalar (fun p t x => ∑ i ∈ s, f i p t x) :=
  Elementary.sum s _ hf

lemma congr (hf : ElementaryScalar f) (he : ∀p t x, f p t x = g p t x) : ElementaryScalar g :=
  Elementary.congr hf (fun _ => he _ _ _)

lemma time_differentiable (hf : ElementaryScalar f) (p : Fin d → ℝ) (x : Space) :
    Differentiable ℝ (fun t => f p t x) := by
  intro t
  have hh := (hf.differentiable (fieldArgs p t x)).comp t
    (fieldArgs_time_hasDerivAt p t x).differentiableAt
  simpa only [Function.comp_def,fieldParam_args,fieldTime_args,fieldSpace_args] using hh

lemma space_differentiable (hf : ElementaryScalar f) (p : Fin d → ℝ) (t : ℝ) :
    Differentiable ℝ (f p t) := by
  intro x
  have hh := (hf.differentiable (fieldArgs p t x)).comp x
    (fieldArgs_space_hasFDerivAt p t x).differentiableAt
  simpa only [Function.comp_def,fieldParam_args,fieldTime_args,fieldSpace_args] using hh

end BalancedTransport.Effectivity.ElementaryScalar
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryField
open BalancedTransport.Geometry
variable {d : ℕ} {v w : (Fin d → ℝ) → Velocity}

lemma fullTimeD (hv : ElementaryField v) : ElementaryField (fun p => Geometry.fullTimeD (v p)) := by
  intro i
  apply (ElementaryScalar.fullTimeD (hv i)).congr
  intro p t x
  simp only [Geometry.fullTimeD, deriv_pi (fun k => (hv k).time_differentiable p x t)]

lemma spaceD (hv : ElementaryField v) (i : Fin 3) : ElementaryField (fun p => BalancedTransport.spaceD i (v p)) := by
  intro k
  apply (ElementaryScalar.spaceD (hv k) i).congr
  intro p t x
  simp only [BalancedTransport.spaceD, fderiv_pi (fun j => (hv j).space_differentiable p t x),
    ContinuousLinearMap.pi_apply]

lemma sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → Velocity)
    (hf : ∀ i ∈ s, ElementaryField (f i)) : ElementaryField (fun p t x => ∑ i ∈ s, f i p t x) := by
  intro k
  simpa only [Finset.sum_apply] using ElementaryScalar.sum s (fun i p t x => f i p t x k) (fun i hi => hf i hi k)

end BalancedTransport.Effectivity.ElementaryField
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RecorderSimulation ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

theorem inverse_base_pos : 0 < (base Q Γ : ℝ)⁻¹ :=
  inv_pos.mpr (Nat.cast_pos.mpr base_pos)

theorem digit_unit_bound (a : Letter Q Γ) :
    (base Q Γ : ℝ)⁻¹ * ((digit a : ℝ) + 1) ≤ 1 := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_one (Nat.cast_pos.mpr base_pos)).mpr (digit_upper a).le

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]
variable [DecidableEq Q]

theorem compiled_boxes_disjoint [DecidableEq Γ] (M : Machine Q Γ) :
    ((table M : Set (Row Q Γ)).Pairwise fun a b =>
      Disjoint ((a.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))
      ((b.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))) ∧
    ((table M : Set (Row Q Γ)).Pairwise fun a b =>
      Disjoint ((a.instruction M).targetBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))
      ((b.instruction M).targetBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))) := by
  constructor
  · intro a ha b hb hab
    exact source_boxes_disjoint M inverse_base_pos _ (fun a => (digit_pos a).le)
      digit_unit_bound digit_gap (placement M) (placement_injective M)
      ((mem_table M a).mp ha) ((mem_table M b).mp hb) hab
  · intro a _ b _ hab
    exact target_boxes_disjoint M inverse_base_pos _ (fun a => (digit_pos a).le)
      digit_unit_bound digit_gap (placement M) (placement_injective M) hab

theorem nonhalt_box_guard (M : Machine Q Γ) (s : Control Q) (hs : s ≠ .ready M.halt)
    (u : Fin 3 → List (Letter Q Γ)) {x : Space}
    (hx : x ∈ Coding.box (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ))
      (Coding.origin (placement M s)) u) : 4 ≤ x 0 := by
  have hl := (Coding.interval_subset_unit inverse_base_pos _ (fun a => (digit_pos a).le)
    digit_unit_bound (u 0) (hx 0)).1
  have hp : (1 : ℝ) ≤ placement M s := by exact_mod_cast placement_positive M s hs
  simp only [Coding.origin, Matrix.cons_val_zero] at hl
  linarith

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] in

theorem Row.sourceControl_ne_halt (M : Machine Q Γ) (a : Row Q Γ) (ha : a.valid M) :
    (a.instruction M).sourceControl ≠ .ready M.halt := by
  cases a <;> simp_all [Row.valid, Row.instruction]

theorem source_box_guard (M : Machine Q Γ) (a : Row Q Γ) (ha : a.valid M) {x : Space}
    (hx : x ∈ (a.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
      (fun c => (digit c : ℝ)) (placement M)) : 4 ≤ x 0 :=
  nonhalt_box_guard M _ (a.sourceControl_ne_halt M ha) _ hx

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control

theorem work_execution (M : Machine Q Γ) {c d : Checkpoint Q Γ}
    (h : Relation.ReflTransGen (WorkStep M) c d) :
    ∃ n, Exec M n (c.expand M) (d.expand M) := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | @tail d e hd hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨hnh, rfl⟩ := hstep
      exact ⟨_, hn.trans (next_exec M d hnh)⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

theorem no_step_from_halt (M : Machine Q Γ) {c d : Configuration Q Γ}
    (hc : c.control = .ready M.halt) : ¬Step M c d := by
  rintro ⟨r, hr, t, rfl, _⟩
  exact r.sourceControl_ne_halt M hr hc

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ] {M : Machine Q Γ}

theorem cancel_to_terminal {n m : ℕ} {c d e : Configuration Q Γ}
    (h : Exec M n c d) (g : Exec M m c e) (hd : ∀ f, ¬Step M d f) :
    ∃ k, n = m + k ∧ Exec M k e d := by
  induction g generalizing n with
  | refl => exact ⟨n, by omega, h⟩
  | @cons m c b e hcb hbe ih =>
      cases h with
      | refl => exact False.elim (hd b hcb)
      | @cons n c a d hca had =>
          have he := step_deterministic M hca hcb
          subst a
          obtain ⟨k, hk, he⟩ := ih had
          exact ⟨k, by omega, he⟩

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ]

theorem halt_reflection (M : Machine Q Γ) {n : ℕ} {c : Checkpoint Q Γ}
    {d : Configuration Q Γ} (h : Exec M n (c.expand M) d)
    (hd : d.control = .ready M.halt) :
    ∃ e, Relation.ReflTransGen (WorkStep M) c e ∧ e.state = M.halt := by
  induction n using Nat.strong_induction_on generalizing c d with
  | h n ih =>
      by_cases hc : c.state = M.halt
      · exact ⟨c, .refl, hc⟩
      · obtain ⟨k, hk, hkd⟩ := h.cancel_to_terminal (next_exec M c hc)
          (fun f => no_step_from_halt M hd)
        have hkn : k < n := by omega
        obtain ⟨e, he, hehalt⟩ := ih k hkn hkd hd
        exact ⟨e, (Relation.ReflTransGen.single (show WorkStep M c (c.next M) from
          ⟨hc, rfl⟩)).trans he, hehalt⟩

theorem halting_iff (M : Machine Q Γ) (c : Checkpoint Q Γ) :
    (∃ n d, Exec M n (c.expand M) d ∧ d.control = .ready M.halt) ↔
      ∃ e, Relation.ReflTransGen (WorkStep M) c e ∧ e.state = M.halt := by
  constructor
  · rintro ⟨n, d, h, hd⟩
    exact halt_reflection M h hd
  · rintro ⟨e, h, he⟩
    obtain ⟨n, hn⟩ := work_execution M h
    exact ⟨n, e.expand M, hn, by simpa [expand] using he⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

end BalancedTransport.Recorder.Checkpoint
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Bridge ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*} {M : Machine Q Γ}

theorem split {n m : ℕ} {c d : Configuration Q Γ} (h : Exec M (n + m) c d) :
    ∃ e, Exec M n c e ∧ Exec M m e d := by
  induction n generalizing c with
  | zero => exact ⟨c, .refl _, by simpa using h⟩
  | succ n ih =>
    have hh : Exec M ((n + m) + 1) c d := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    cases hh with
    | @cons _ _ b _ hcb hbd =>
      obtain ⟨e, hce, hed⟩ := ih hbd
      exact ⟨e, .cons hcb hce, hed⟩

lemma take {m n : ℕ} {c d : Configuration Q Γ} (h : Exec M n c d) (hm : m ≤ n) :
    ∃ e, Exec M m c e := by
  have hh : Exec M (m + (n - m)) c d := by rwa [Nat.add_sub_of_le hm]
  obtain ⟨e, he, _⟩ := hh.split
  exact ⟨e, he⟩

lemma one_iff {c d : Configuration Q Γ} : Exec M 1 c d ↔ Step M c d := by
  constructor
  · intro h
    cases h with
    | cons h h' => cases h'; exact h
  · exact single

lemma snoc {n : ℕ} {c d : Configuration Q Γ} (h : Exec M (n + 1) c d) :
    ∃ e, Exec M n c e ∧ Step M e d := by
  obtain ⟨e, he, hed⟩ := h.split
  exact ⟨e, he, one_iff.mp hed⟩

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*} {M : Machine Q Γ}

theorem arbitrarily_long_execution (M : Machine Q Γ) (c : Checkpoint Q Γ)
    (hh : ¬∃ d, Relation.ReflTransGen (WorkStep M) c d ∧ d.state = M.halt)
    (n : ℕ) : ∃ d, Exec M n (c.expand M) d := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    have hc : c.state ≠ M.halt := fun he => hh ⟨c, .refl, he⟩
    let m := 2 * (c.right.length + 1) + 2
    have hm : 0 < m := by dsimp [m]; omega
    have he : Exec M m (c.expand M) ((c.next M).expand M) := next_exec M c hc
    by_cases hnm : n ≤ m
    · exact he.take hnm
    · have hh' : ¬∃ d, Relation.ReflTransGen (WorkStep M) (c.next M) d ∧ d.state = M.halt := by
        rintro ⟨d, hd, hs⟩
        exact hh ⟨d, (Relation.ReflTransGen.single (show WorkStep M c (c.next M) from
          ⟨hc, rfl⟩)).trans hd, hs⟩
      obtain ⟨d, hd⟩ := ih (n - m) (by omega) (c.next M) hh'
      exact ⟨d, by simpa [Nat.add_sub_of_le (le_of_not_ge hnm)] using he.trans hd⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} {M : Machine Q Γ}
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

lemma Configuration.code_guard {M : Machine Q Γ} {c : Configuration Q Γ}
    (hc : c.control ≠ .ready M.halt) : 4 ≤ c.code M 0 := by
  have hp : (1 : ℝ) ≤ placement M c.control := by
    exact_mod_cast placement_positive M c.control hc
  have hb := (Coding.stream_mem_interior base_pos digit digit_pos digit_upper (c.stacks 0)).1
  change 4 ≤ 4 * (placement M c.control : ℝ) + Coding.stream digit (c.stacks 0)
  linarith

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set
open scoped NNReal

lemma materialFlow_loading {z : Space} {η : ℝ} (hη : 0 < η)
    {v : Velocity} (hv : TimeCollars v) {X : MaterialFlow}
    (hX : IsMaterialFlow (loadedRepeat (loadingVelocity z η) v) X)
    {L : ℝ≥0}
    (hL : ∀ t, 0 ≤ t → LipschitzWith L (loadingVelocity z η t))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    X t fixedLabel = loadingPath z t := by
  have hd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => X s fixedLabel)
        (loadingVelocity z η s (X s fixedLabel)) (Icc 0 1) s := by
    intro s hs
    have hh := (hX.2 fixedLabel s hs.1).mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from Icc_subset_Ici_self)
    rwa [loadedRepeat_before hv hs.1 hs.2] at hh
  exact curves_agree_on_overlap hL (HasDerivWithinAt.continuousOn hd)
    (HasDerivWithinAt.continuousOn (fun s _ => (loadingPath_hasDerivAt z hη s).hasDerivWithinAt))
    hd (fun s _ => (loadingPath_hasDerivAt z hη s).hasDerivWithinAt)
    ((hX.1 fixedLabel).trans (loadingPath_start z).symm) ht.1 ht.2 ht.2

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q]
variable {M : Machine Q Γ} {v load : Velocity} {X : MaterialFlow} {L : ℝ≥0}

lemma guarded_execution_endpoint (hg : GuardedTemplate M v) (hv : TimeCollars v)
    (hl : TimeCollars load)
    (hLip : ∀ t, 0 ≤ t → LipschitzWith L (v t))
    (hX : IsMaterialFlow (loadedRepeat load v) X)
    {c d : Configuration Q Γ} {n : ℕ} (h : Exec M n c d) (a : Space)
    (hinit : X 1 a = c.code M) : X ((n : ℝ) + 1) a = d.code M := by
  induction n generalizing d with
  | zero => cases h; simpa using hinit
  | succ n ih =>
      obtain ⟨e, he, hed⟩ := h.snoc
      have hn := guarded_period_step hg hv hl hLip hX hed n a (ih he)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hn.1

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set

lemma TimeCollars.repeats {v : Velocity} (hv : TimeCollars v) : RepeatsAfter 1 v := by
  intro t ht
  rw [hv t (Or.inr (by linarith)), hv (t + 1) (Or.inr (by linarith))]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

theorem loaded_template_halting_iff (M : Machine Q Γ) (c : Checkpoint Q Γ)
    {η : ℝ} (hη : 0 < η) {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hg : GuardedTemplate M v) {X : MaterialFlow}
    (hX : IsMaterialFlow (loadedRepeat (loadingVelocity ((c.expand M).code M) η) v) X) :
    (∃ t : ℝ, 0 ≤ t ∧ X t fixedLabel ∈ observer) ↔
      ∃ d, Relation.ReflTransGen (Checkpoint.WorkStep M) c d ∧ d.state = M.halt := by
  let z := (c.expand M).code M
  have hlc : TimeCollars (loadingVelocity z η) := fun _ ht => loadingVelocity_zero ht
  obtain ⟨L, hLip⟩ := spatial_lipschitz_of_boundedMixed hv
    (boundedMixed_of_compact_repeating hK hv hs hc.repeats)
  obtain ⟨L₀, hLip₀⟩ := spatial_lipschitz_of_boundedMixed (loadingVelocity_jointSmooth z η)
    (loadingVelocity_boundedMixed z hη)
  have hload : ∀ t ∈ Icc (0 : ℝ) 1, X t fixedLabel = loadingPath z t :=
    fun _ ht => materialFlow_loading hη hc hX hLip₀ ht
  have hinit : X 1 fixedLabel = z :=
    (hload 1 ⟨by norm_num, le_rfl⟩).trans (loadingPath_end z)
  have hend {n : ℕ} {d : Configuration Q Γ} (hd : Exec M n (c.expand M) d) :
      X ((n : ℝ) + 1) fixedLabel = d.code M :=
    guarded_execution_endpoint hg hc hlc hLip hX hd fixedLabel hinit
  constructor
  · rintro ⟨t, ht, hobs⟩
    by_contra hn
    have hstate : c.state ≠ M.halt := fun he => hn ⟨c, .refl, he⟩
    by_cases ht₁ : t ≤ 1
    · rw [hload t ⟨ht, ht₁⟩] at hobs
      exact loadingPath_avoids_observer
        (Configuration.code_guard (show (c.expand M).control ≠ .ready M.halt by
          exact fun he => hstate (Control.ready.inj he))) t hobs
    · let n : ℕ := ⌊t - 1⌋₊
      have hnf : (n : ℝ) ≤ t - 1 := Nat.floor_le (by linarith)
      have hnt : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - 1)
      let s := t - ((n : ℝ) + 1)
      have hs' : s ∈ Icc (0 : ℝ) 1 := by dsimp [s]; constructor <;> linarith
      obtain ⟨e, he⟩ := c.arbitrarily_long_execution M hn (n + 1)
      obtain ⟨d, hd, hde⟩ := he.snoc
      have hne : e.control ≠ .ready M.halt := fun hh =>
        hn (Checkpoint.halt_reflection M he hh)
      have hguard := (guarded_period_step hg hc hlc hLip hX hde n fixedLabel (hend hd)).2
        hne s hs'
      have heq : s + ((n : ℝ) + 1) = t := sub_add_cancel _ _
      exact hguard (by rwa [heq])
  · intro hhalt
    obtain ⟨n, d, hd, hh⟩ := (Checkpoint.halting_iff M c).mpr hhalt
    exact ⟨(n : ℝ) + 1, by positivity, by rw [hend hd]; exact (code_mem_observer_iff M d).mpr hh⟩

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open BalancedTransport.Geometry

theorem compiled_continuous_halting_iff (M : FiniteMachine) (w : Input M)
    {η : ℝ} (hη : 0 < η) {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hg : Recorder.GuardedTemplate M.normalized v) {X : MaterialFlow}
    (hX : IsMaterialFlow
      (loadedRepeat (loadingVelocity (((M.initialWork w).expand M.normalized).code M.normalized) η) v) X) :
    (∃ t : ℝ, 0 ≤ t ∧ X t fixedLabel ∈ observer) ↔ Halts M w :=
  (Recorder.loaded_template_halting_iff M.normalized (M.initialWork w) hη hK hv hc hs hg hX).trans
    (normalized_halting_iff M w)

end BalancedTransport.FiniteMachine
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MotionField ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mem_solid {A : BoxLayout ι} {i : ι} {x : Space} : x ∈ A.solid i ↔
    ∀ k, A.center i k - A.width i k ≤ x k ∧ x k ≤ A.center i k + A.width i k := by
  simp only [solid, mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply]
  exact forall_and.symm

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma fieldCenter_smooth (m : BoxMotion A B safe η) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (m.fieldCenter i) :=
  (contDiff_pi.mp m.smooth_center i).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma fieldScale_smooth (m : BoxMotion A B safe η) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (m.fieldScale i) := by
  apply contDiff_pi.mpr
  intro k
  exact (((contDiff_pi.mp (contDiff_pi.mp m.smooth_width i) k).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))).div_const _

lemma fieldScale_pos (m : BoxMotion A B safe η) (i : ι) (t : ℝ) (k : Fin 3) :
    0 < m.fieldScale i t k := div_pos (m.positive _ _ _) (m.positive_start _ _)

lemma fieldScale_det (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    ∏ k, m.fieldScale i t k = 1 := by
  simp only [fieldScale, Finset.prod_div_distrib, m.volume]
  exact div_self (ne_of_gt (Finset.prod_pos (fun k _ => m.positive_start i k)))

lemma velocity_jointSmooth (m : BoxMotion A B safe η) : JointSmooth m.velocity :=
  familyVelocity_jointSmooth m.fieldCenter_smooth m.fieldScale_smooth
    (fun i t k => (m.fieldScale_pos i t k).ne') _ _ _

lemma velocity_divergence (m : BoxMotion A B safe η) (t : ℝ) (x : Space) :
    div m.velocity t x = 0 :=
  familyVelocity_divergence m.fieldCenter_smooth m.fieldScale_smooth
    (fun i t k => (m.fieldScale_pos i t k).ne') _ _ _ _ _

lemma lowerEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i - m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  field_simp [(m.positive_start i k).ne']
  ring

lemma upperEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i + m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  rw [div_mul_cancel₀ _ (m.positive_start i k).ne']

lemma enlarged_disjoint (m : BoxMotion A B safe η) (t : ℝ) :
    Pairwise fun i j => Disjoint
      (closedEnlargement (lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t)
        (lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t) (2 * η))
      (closedEnlargement (lowerEndpoint (-A.width j) (m.fieldCenter j) (m.fieldScale j) t)
        (lowerEndpoint (A.width j) (m.fieldCenter j) (m.fieldScale j) t) (2 * η)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rw [m.lowerEndpoint_eq, m.upperEndpoint_eq, mem_closedEnlargement] at hi hj
  obtain ⟨k, hk⟩ := m.separation (2 * t - 1 / 2) i j hij
  have hbound : |m.center (2 * t - 1 / 2) i k - m.center (2 * t - 1 / 2) j k| ≤
      m.width (2 * t - 1 / 2) i k + m.width (2 * t - 1 / 2) j k + 4 * η := by
    apply abs_le.mpr
    have hi' := hi k
    have hj' := hj k
    dsimp at hi' hj'
    constructor <;> linarith
  exact hk.not_ge hbound

lemma path_start (m : BoxMotion A B safe η) (i : ι) (x : Space) : m.path i x 0 = x := by
  ext k
  have hc := m.start_center (-(1 / 2)) (by norm_num)
  have hw := m.start_width (-(1 / 2)) (by norm_num)
  simp only [path, affinePath, fieldCenter, fieldScale, mul_zero, zero_sub, Pi.sub_apply]
  rw [hc, hw, div_self (m.positive_start i k).ne', one_mul]
  ring

lemma path_end (m : BoxMotion A B safe η) (i : ι) (x : Space) :
    m.path i x 1 = A.affineMap B i x := by
  ext k
  change m.center (2 * 1 - 1 / 2) i k +
    m.width (2 * 1 - 1 / 2) i k / A.width i k * (x k - A.center i k) = _
  rw [m.end_center _ (by norm_num), m.end_width _ (by norm_num)]
  rfl

omit [Fintype ι] in
lemma reference_mem {i : ι} {x : Space} (hx : x ∈ A.solid i) :
    x - A.center i ∈ Icc (-A.width i) (A.width i) := by
  rw [BoxLayout.mem_solid] at hx
  constructor <;> intro k <;> dsimp <;> linarith [(hx k).1, (hx k).2]

lemma path_hasDerivAt (m : BoxMotion A B safe η) (hη : 0 < η)
    {i : ι} {x : Space} (hx : x ∈ A.solid i) (t : ℝ) :
    HasDerivAt (m.path i x) (m.velocity t (m.path i x t)) t := by
  have hz := reference_mem hx
  have hplateau := affinePath_mem_plateau (c := m.fieldCenter i) hη hz (m.fieldScale_pos i t)
  unfold path
  rw [velocity, familyVelocity_eq_on_plateau hη i hplateau (m.enlarged_disjoint t)]
  exact affinePath_hasDerivAt hη (m.fieldCenter_smooth i) (m.fieldScale_smooth i)
    (m.fieldScale_pos i) (m.fieldScale_det i) hz t

lemma fieldScale_before (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : t ≤ 1 / 4) :
    m.fieldScale i t = 1 := by
  ext k
  change m.width (2 * t - 1 / 2) i k / A.width i k = 1
  rw [m.start_width _ (by linarith), div_self (m.positive_start i k).ne']

lemma fieldScale_after (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : 3 / 4 ≤ t) :
    m.fieldScale i t = fun k => B.width i k / A.width i k := by
  unfold fieldScale
  rw [m.end_width _ (by linarith)]

end BalancedTransport.Geometry.BoxMotion
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.CompiledGeometry ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma BoxLayout.lower_mem {A : BoxLayout ι} (hp : A.Positive) (i : ι) :
    A.center i - A.width i ∈ A.solid i := by
  rw [BoxLayout.mem_solid]
  intro k
  exact ⟨le_rfl, by dsimp; linarith [hp i k]⟩

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Coding
open BalancedTransport.Geometry
variable {S ι : Type*}

lemma layout_positive {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (o : ι → Space) (u : ι → Fin 3 → List S) : (layout r digit o u).Positive := by
  intro i k
  exact div_pos (pow_pos hr _) (by norm_num)

lemma layout_solid [Fintype ι] (r : ℝ) (digit : S → ℝ) (o : ι → Space)
    (u : ι → Fin 3 → List S) (i : ι) :
    (layout r digit o u).solid i = box r digit (o i) (u i) := by
  ext x
  rw [BoxLayout.mem_solid]
  change (∀ k, o i k + word r digit (u i k) + r ^ (u i k).length / 2 -
      r ^ (u i k).length / 2 ≤ x k ∧
      x k ≤ o i k + word r digit (u i k) + r ^ (u i k).length / 2 +
      r ^ (u i k).length / 2) ↔
    ∀ k, word r digit (u i k) ≤ x k - o i k ∧
      x k - o i k ≤ word r digit (u i k) + r ^ (u i k).length
  constructor <;> intro h k <;> have := h k <;> constructor <;> linarith

lemma layout_affineMap {r : ℝ} (hr : r ≠ 0) (digit : S → ℝ) (o p : ι → Space)
    (u v : ι → Fin 3 → List S) (i : ι) (x : Space) :
    (layout r digit o u).affineMap (layout r digit p v) i x =
      boxMap r digit (o i) (p i) (u i) (v i) x := by
  ext k
  dsimp [BoxLayout.affineMap, layout, boxMap, replacement]
  field_simp
  ring

lemma layout_volume (r : ℝ) (digit : S → ℝ) (o p : ι → Space)
    (u v : ι → Fin 3 → List S) (i : ι)
    (h : ∑ k, (u i k).length = ∑ k, (v i k).length) :
    ∏ k, (layout r digit o u).width i k = ∏ k, (layout r digit p v).width i k := by
  simp only [layout, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, h]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
open BalancedTransport.Geometry
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

omit [DecidableEq Γ] in
lemma sourceLayout_solid (M : Machine Q Γ) (i : ActiveRow M) :
    (sourceLayout M).solid i = (i.val.instruction M).sourceBox
      (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) :=
  Coding.layout_solid _ _ _ _ _

omit [DecidableEq Γ] in
lemma targetLayout_solid (M : Machine Q Γ) (i : ActiveRow M) :
    (targetLayout M).solid i = (i.val.instruction M).targetBox
      (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) :=
  Coding.layout_solid _ _ _ _ _

omit [DecidableEq Γ] in
lemma sourceLayout_positive (M : Machine Q Γ) : (sourceLayout M).Positive :=
  Coding.layout_positive inverse_base_pos _ _ _

omit [DecidableEq Γ] in
lemma targetLayout_positive (M : Machine Q Γ) : (targetLayout M).Positive :=
  Coding.layout_positive inverse_base_pos _ _ _

lemma sourceLayout_separated (M : Machine Q Γ) : (sourceLayout M).Separated 0 := by
  apply BoxLayout.separated_of_disjoint (sourceLayout_positive M)
  intro i j hij
  rw [sourceLayout_solid, sourceLayout_solid]
  exact (compiled_boxes_disjoint M).1 i.property j.property (fun h => hij (Subtype.ext h))

lemma targetLayout_separated (M : Machine Q Γ) : (targetLayout M).Separated 0 := by
  apply BoxLayout.separated_of_disjoint (targetLayout_positive M)
  intro i j hij
  rw [targetLayout_solid, targetLayout_solid]
  exact (compiled_boxes_disjoint M).2 i.property j.property (fun h => hij (Subtype.ext h))

omit [DecidableEq Γ] in
lemma layouts_equal_volume (M : Machine Q Γ) (i : ActiveRow M) :
    ∏ k, (sourceLayout M).width i k = ∏ k, (targetLayout M).width i k := by
  apply Coding.layout_volume
  simpa [Instruction.sourcePrefixes, Instruction.targetPrefixes, Fin.sum_univ_succ,
    Instruction.Balanced, Nat.add_assoc] using i.val.balanced M

omit [DecidableEq Γ] in
lemma sourceLayout_guard (M : Machine Q Γ) : (sourceLayout M).Guarded (safeRows M) := by
  intro i _
  have hh := BoxLayout.lower_mem (sourceLayout_positive M) i
  rw [sourceLayout_solid] at hh
  have hn := source_box_guard M i.val ((mem_table M _).mp i.property) hh
  change 2 < (sourceLayout M).center i 0 - (sourceLayout M).width i 0
  change 4 ≤ (sourceLayout M).center i 0 - (sourceLayout M).width i 0 at hn
  linarith

omit [DecidableEq Γ] in
lemma targetLayout_guard (M : Machine Q Γ) : (targetLayout M).Guarded (safeRows M) := by
  intro i hi
  have hh := BoxLayout.lower_mem (targetLayout_positive M) i
  rw [targetLayout_solid] at hh
  have hn := nonhalt_box_guard M _ hi _ hh
  change 2 < (targetLayout M).center i 0 - (targetLayout M).width i 0
  change 4 ≤ (targetLayout M).center i 0 - (targetLayout M).width i 0 at hn
  linarith

omit [DecidableEq Γ] in
lemma layouts_affineMap (M : Machine Q Γ) (i : ActiveRow M) (x : Space) :
    (sourceLayout M).affineMap (targetLayout M) i x = (i.val.instruction M).fullMap M x :=
  Coding.layout_affineMap inverse_base_pos.ne' _ _ _ _ _ _ _

end BalancedTransport.Recorder
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryTemplate ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma neg {x : ℝ} (h : RationalConstant x) : RationalConstant (-x) := by
  obtain ⟨q,rfl⟩ := h; exact ⟨-q, by simp⟩

lemma inv {x : ℝ} (h : RationalConstant x) : RationalConstant x⁻¹ := by
  obtain ⟨q,rfl⟩ := h; exact ⟨q⁻¹, by simp⟩

lemma div {x y : ℝ} (hx : RationalConstant x) (hy : RationalConstant y) : RationalConstant (x/y) := by
  simpa only [div_eq_mul_inv] using hx.mul hy.inv

lemma pow {x : ℝ} (h : RationalConstant x) (n : ℕ) : RationalConstant (x^n) := by
  obtain ⟨q,rfl⟩ := h; exact ⟨q^n, by simp⟩

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

lemma elementary_motion_velocity {ι : Type*} [Fintype ι] {A B : BoxLayout ι} {safe : Set ι}
    {η : ℝ} (hr : RationalConstant η) (Ar : RationalLayout A) {m : BoxMotion A B safe η}
    (hm : ElementaryMotion m) (d : ℕ) : ElementaryField (fun _ : Fin d → ℝ => m.velocity) := by
  apply ElementaryField.sum Finset.univ
  intro i _
  have ht : ElementaryCurve (fun t : ℝ => 2*t-1/2) := by
    simpa using
      ((ElementaryCurve.const (RationalConstant.nat 2)).mul ElementaryCurve.id).sub
        (ElementaryCurve.const (RationalConstant.rat (1/2)))
  have hc : ElementaryField (fun _ : Fin d → ℝ => fun t _ => m.fieldCenter i t) :=
    fun k => ElementaryScalar.time.curve ((hm.1 i k).comp ht)
  have hw : ElementaryField (fun _ : Fin d → ℝ => fun t _ => m.fieldScale i t) :=
    fun k => (ElementaryScalar.time.curve ((hm.2 i k).comp ht)).div_const (Ar.2 i k)
  apply elementary_movingBoxVelocity (-A.width i) (A.width i)
    (fun k => (Ar.2 i k).neg) (Ar.2 i) hc hw
  · intro k
    obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
      (contDiff_pi.mp (m.fieldScale_smooth i) k).continuous.continuousOn
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (m.fieldScale_pos i t k)
    have hn' : (((n+1:ℕ):ℝ)⁻¹) ≤ m.fieldScale i t k := by simpa [one_div] using hn.le
    refine ⟨n, fun _ s => hn'.trans ?_⟩
    have hh : ∀ s ∈ Icc (0 : ℝ) 1, m.fieldScale i t k ≤ m.fieldScale i s k := hmin
    by_cases hs : s ≤ 1/4
    · simpa only [m.fieldScale_before i hs, m.fieldScale_before i (by norm_num : (0:ℝ) ≤ 1/4),
        Nat.cast_add, Nat.cast_one, one_div] using hh 0 (by simp)
    · by_cases hs' : 3/4 ≤ s
      · simpa only [m.fieldScale_after i hs', m.fieldScale_after i (by norm_num : (3:ℝ)/4 ≤ 1)] using hh 1 (by simp)
      · exact hh s ⟨by linarith,by linarith⟩
  · exact hr

lemma rational_word {S : Type*} {r : ℝ} {digit : S → ℝ} (hr : RationalConstant r)
    (hd : ∀s, RationalConstant (digit s)) (w : List S) : RationalConstant (Coding.word r digit w) := by
  induction w with
  | nil => exact RationalConstant.zero
  | cons a w ih => exact hr.mul ((hd a).add ih)

lemma rational_origin (n : ℕ) : ∀i, RationalConstant (Coding.origin n i) := by
  intro i
  fin_cases i
  · exact (RationalConstant.nat 4).mul (RationalConstant.nat n)
  · exact RationalConstant.zero
  · exact RationalConstant.zero

lemma rational_coding_layout {S ι : Type*} {r : ℝ} {digit : S → ℝ} {o : ι → Space}
    (hr : RationalConstant r) (hd : ∀s, RationalConstant (digit s)) (ho : RationalCenters o)
    (u : ι → Fin 3 → List S) : RationalLayout (Coding.layout r digit o u) := by
  constructor
  · intro i k
    exact ((ho i k).add (rational_word hr hd _)).add ((hr.pow _).div (RationalConstant.nat 2))
  · intro i k
    exact (hr.pow _).div (RationalConstant.nat 2)

lemma rational_sourceLayout {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]
    (M : Recorder.Machine Q Γ) : RationalLayout (Recorder.sourceLayout M) :=
  rational_coding_layout (RationalConstant.nat _).inv (fun _ => RationalConstant.nat _)
    (fun _ => rational_origin _) _

lemma rational_targetLayout {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]
    (M : Recorder.Machine Q Γ) : RationalLayout (Recorder.targetLayout M) :=
  rational_coding_layout (RationalConstant.nat _).inv (fun _ => RationalConstant.nat _)
    (fun _ => rational_origin _) _

theorem exists_elementary_guarded_template {Q Γ : Type*} [Fintype Q] [Fintype Γ]
    [DecidableEq Q] [DecidableEq Γ] (M : Recorder.Machine Q Γ) (d : ℕ) :
    ∃ (v : Velocity) (K : Set Space), IsCompact K ∧ JointSmooth v ∧ TimeCollars v ∧
      SpatiallySupported K v ∧ (∀ t x, div v t x = 0) ∧ Recorder.GuardedTemplate M v ∧
      ElementaryField (fun _ : Fin d → ℝ => v) := by
  obtain ⟨η,hη,m,hm⟩ := elementary_guarded_solid_box_motion (Recorder.sourceLayout M)
    (Recorder.targetLayout M) (Recorder.safeRows M) (rational_sourceLayout M) (rational_targetLayout M)
    (Recorder.sourceLayout_positive M) (Recorder.targetLayout_positive M)
    (Recorder.sourceLayout_separated M) (Recorder.targetLayout_separated M)
    (Recorder.layouts_equal_volume M) (Recorder.sourceLayout_guard M) (Recorder.targetLayout_guard M)
  have hp : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  obtain ⟨K,hK,hs⟩ := m.velocity_compact_support hp
  refine ⟨m.velocity,K,hK,m.velocity_jointSmooth,m.velocity_collars,hs,m.velocity_divergence,?_,
    elementary_motion_velocity (RationalConstant.rat η) (rational_sourceLayout M) hm d⟩
  intro r hr x hx
  let i : Recorder.ActiveRow M := ⟨r, (Recorder.mem_table M r).mpr hr⟩
  have hm : x ∈ (Recorder.sourceLayout M).solid i := by rwa [Recorder.sourceLayout_solid]
  refine ⟨m.path i x,m.path_start i x,?_,?_,?_⟩
  · rw [m.path_end, Recorder.layouts_affineMap]
  · intro t _
    exact (m.path_hasDerivAt hp hm t).hasDerivWithinAt
  · intro hsafe t _
    exact m.path_guarded hsafe hm t

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TemporalJets ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Filter Set
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma timeGerm_fullTimeD {v w : Field F} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    fullTimeD v =ᶠ[𝓝 t] fullTimeD w := by
  filter_upwards [h.eventually_nhds] with s hs
  funext x
  have he : (fun r => v r x) =ᶠ[𝓝 s] (fun r => w r x) := hs.mono (fun _ he => congrFun he x)
  exact he.deriv_eq

lemma timeGerm_spaceD {v w : Field F} {t : ℝ} (h : v =ᶠ[𝓝 t] w) (i : Fin 3) :
    spaceD i v =ᶠ[𝓝 t] spaceD i w := by
  filter_upwards [h] with s hs
  funext x
  change fderiv ℝ (v s) x _ = fderiv ℝ (w s) x _
  rw [hs]

lemma timeGerm_fullInertial {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    fullInertial v =ᶠ[𝓝 t] fullInertial w := by
  have hd : ∀ᶠ s in 𝓝 t, ∀ i : Fin 3, spaceD i v s = spaceD i w s :=
    (Filter.eventually_all).mpr (fun i => timeGerm_spaceD h i)
  filter_upwards [h, timeGerm_fullTimeD h, hd] with s hs ht hd
  funext x
  change fullTimeD v s x + BalancedTransport.convection v s x = fullTimeD w s x + BalancedTransport.convection w s x
  simp only [BalancedTransport.convection, hs, ht, hd]

lemma timeGerm_viscous {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    viscousCoefficient v =ᶠ[𝓝 t] viscousCoefficient w := by
  have hd : ∀ᶠ s in 𝓝 t, ∀ i : Fin 3, spaceD i (spaceD i v) s = spaceD i (spaceD i w) s :=
    (Filter.eventually_all).mpr (fun i => timeGerm_spaceD (timeGerm_spaceD h i) i)
  filter_upwards [hd] with s hd
  funext x
  change -(∑ i, spaceD i (spaceD i v) s x) = -(∑ i, spaceD i (spaceD i w) s x)
  simp only [hd]

lemma fullTimeD_translate (v : Field F) (b : ℝ) :
    fullTimeD (fun t => v (t-b)) = fun t => fullTimeD v (t-b) := by
  funext t x
  exact deriv_comp_sub_const (fun s => v s x) b t

lemma fullInertial_translate (v : Velocity) (b : ℝ) :
    fullInertial (fun t => v (t-b)) = fun t => fullInertial v (t-b) := by
  ext t x i
  simp only [fullInertial, fullTimeD_translate, convection, spaceD]

lemma viscous_translate (v : Velocity) (b : ℝ) :
    viscousCoefficient (fun t => v (t-b)) = fun t => viscousCoefficient v (t-b) := rfl

lemma loadedRepeat_before_open {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht : t < 5/4) : loadedRepeat load v t = load t := by
  by_cases hh : t ≤ 3/4
  · have he : afterLoadingGate t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    ext x i
    simp [loadedRepeat, he]
  · have he : repeatTemplate v t = 0 := by
      ext x i
      rw [repeatTemplate_eq hc (n := 0) (by simp only [Int.cast_zero, sub_zero]; constructor <;> linarith),
        Int.cast_zero, sub_zero, hc t (Or.inr (lt_of_not_ge hh))]
    ext x i
    simp [loadedRepeat, he]

lemma loadedRepeat_after_open {load v : Velocity} (hl : TimeCollars load) (hc : TimeCollars v)
    {t : ℝ} (ht : 3/4 < t) : loadedRepeat load v t = repeatTemplate v t := by
  by_cases hh : 1 ≤ t
  · exact loadedRepeat_after hl hh
  · have he : repeatTemplate v t = 0 := by
      ext x i
      rw [repeatTemplate_eq hc (n := 0) (by simp only [Int.cast_zero, sub_zero]; constructor <;> linarith),
        Int.cast_zero, sub_zero, hc t (Or.inr ht)]
    ext x i
    simp [loadedRepeat, he, hl t (Or.inr ht)]

lemma loadedRepeat_germ_before {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht : t < 1) : loadedRepeat load v =ᶠ[𝓝 t] load := by
  filter_upwards [eventually_lt_nhds (show t < 5/4 by linarith)] with s hs
  exact loadedRepeat_before_open hc hs

lemma loadedRepeat_germ_after {load v : Velocity} (hl : TimeCollars load) (hc : TimeCollars v)
    {t : ℝ} (ht : 1 ≤ t) :
    loadedRepeat load v =ᶠ[𝓝 t] (fun s => v (s-(⌊t⌋ : ℤ))) := by
  have hi : t - (⌊t⌋ : ℤ) ∈ Ioo (-1/4 : ℝ) (5/4) := by
    have := Int.floor_le t
    have := Int.lt_floor_add_one t
    constructor <;> linarith
  have hn : ∀ᶠ s : ℝ in 𝓝 t, s - (⌊t⌋ : ℤ) ∈ Ioo (-1/4 : ℝ) (5/4) :=
    (continuous_id.sub continuous_const).continuousAt.eventually (isOpen_Ioo.mem_nhds hi)
  filter_upwards [hn, eventually_gt_nhds (show (3 : ℝ)/4 < t by linarith)] with s hs hst
  rw [loadedRepeat_after_open hl hc hst]
  exact funext (repeatTemplate_eq hc hs)

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma ElementaryField.convection {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => convection (v p)) := by
  intro k
  simp only [BalancedTransport.convection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply ElementaryScalar.sum Finset.univ
  intro i _
  exact (hv i).mul ((hv.spaceD i) k)

lemma ElementaryField.fullInertial {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => fullInertial (v p)) :=
  fun i => ((hv.fullTimeD) i).add (hv.convection i)

lemma ElementaryField.viscous {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => viscousCoefficient (v p)) := by
  intro k
  simp only [viscousCoefficient, laplacian, Pi.neg_apply, Finset.sum_apply]
  apply ElementaryScalar.neg
  apply ElementaryScalar.sum Finset.univ
  intro i _
  exact ((hv.spaceD i).spaceD i) k

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveGluing ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

lemma computable_fin_lam {α β : Type*} [Primcodable α] [Primcodable β]
    {n : ℕ} {f : α → Fin n → β} (hf : ∀ i, Computable (fun a => f a i)) :
    Computable f := by
  exact (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hf)).of_eq
    (fun a => by funext i; simp)

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ComputableInitial ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Recorder Coding BalancedTransport.Geometry
open scoped Classical

lemma computable_rationalWord {S : Type*} [Primcodable S] [Fintype S] [Inhabited S]
    {B : ℕ} (digit : S → Fin B) : Computable (Coding.rationalWord digit) := by
  have h : Computable (fun w : List S => w.reverse.foldl
      (fun q a => (B : ℚ)⁻¹ * ((digit a : ℚ) + q)) 0) :=
    computable_foldl Primrec.list_reverse.to_comp (Computable.const 0)
      (computable_rat_mul.comp (Computable.const ((B : ℚ)⁻¹))
        (computable_rat_add.comp
          ((Primrec.dom_finite (fun a : S => (digit a : ℚ))).to_comp.comp
            (Computable.snd.comp Computable.snd))
          (Computable.fst.comp Computable.snd))).to₂
  apply h.of_eq
  intro w
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [List.reverse_cons,List.foldl_append,List.foldl_cons,
      List.foldl_nil, Coding.rationalWord] using
      (congrArg (fun q => (B : ℚ)⁻¹ * ((digit a : ℚ) + q)) ih)

lemma computable_rationalTailCode {S : Type*} [Primcodable S] [Fintype S] [Inhabited S]
    {B : ℕ} (digit : S → Fin B) (a : S) :
    Computable (fun w => Coding.rationalTailCode digit w a) :=
  computable_rat_add.comp (computable_rationalWord digit)
    (computable_rat_mul.comp
      (computable_rat_pow.comp (Computable.const ((B : ℚ)⁻¹)) Computable.list_length)
      (Computable.const ((digit a : ℚ) / ((B : ℚ) - 1))))

lemma computable_rationalInitial (N : FiniteMachine) :
    Computable (Recorder.Checkpoint.rationalInitial N.normalized (some N.initial)) := by
  let S := Recorder.Letter (Option (Fin (N.states+1))) (Fin (N.symbols+1))
  let : Primcodable S := Primcodable.ofEquiv (Fin (Fintype.card S)) (Fintype.equivFin S)
  let : Inhabited S := ⟨.boundary⟩
  have hwork : Primrec (fun a : Fin (N.symbols+1) => (Letter.work a : S)) := Primrec.dom_finite _
  have hh : Computable (fun w : Input N => w.headD N.blank) := by
    exact (Primrec.option_getD.comp Primrec.list_head? (Primrec.const N.blank)).to_comp.of_eq
      (fun w => by cases w <;> rfl)
  have hw : Computable (fun w : Input N =>
      (Letter.work (w.headD N.blank) : S) :: (w.tail.map Letter.work ++ [Letter.boundary])) :=
    Primrec.list_cons.to_comp.comp (hwork.to_comp.comp hh)
      (Primrec.list_append.to_comp.comp
        ((Primrec.list_map Primrec.list_tail (hwork.comp Primrec.snd).to₂).to_comp)
        (Computable.const [Letter.boundary]))
  apply computable_fin_lam
  intro i
  fin_cases i
  · exact Computable.const _
  · exact (computable_rationalTailCode (Recorder.digit (Q := Option (Fin (N.states+1)))
      (Γ := Fin (N.symbols+1))) (Letter.work N.blank)).comp hw
  · exact Computable.const _

lemma rationalInitial_bounded (N : FiniteMachine) :
    ∃ C : ℕ, ∀ w : Input N, ∀ i,
      |(Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) w i : ℝ)| ≤ C := by
  let k := Recorder.placement N.normalized (.ready (some N.initial))
  refine ⟨4*k+1, ?_⟩
  intro w i
  have he := congrFun (Recorder.Checkpoint.rationalInitial_cast N.normalized (some N.initial) w) i
  change (Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) w i : ℝ) = _ at he
  rw [he]
  change |Coding.origin k i + Coding.stream Recorder.digit _| ≤ _
  have hh := Coding.stream_mem_unit Recorder.digit
    (((Recorder.Checkpoint.initial N.normalized (some N.initial) w).expand N.normalized).stacks i)
  have ho : 0 ≤ Coding.origin k i ∧ Coding.origin k i ≤ 4*(k : ℝ) := by
    fin_cases i <;> dsimp [Coding.origin] <;> constructor <;>
      first | positivity | exact le_rfl
  rw [abs_of_nonneg (add_nonneg ho.1 hh.1)]
  push_cast
  linarith [hh.2, ho.2]

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveConstruction ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

lemma EffectiveFamily.forwardEq {V W : Family Velocity} (hV : EffectiveFamily V)
    (h : ∀M w, ForwardEq (V M w) (W M w)) : EffectiveFamily W := by
  obtain ⟨E,b,R,hE,hb,hR,he,hB,hs⟩ := hV
  refine ⟨E,b,R,hE,hb,hR,?_,?_,?_⟩
  · intro M w a z n hz i
    rw [← (h M w).mixedD a _ (by exact_mod_cast hz)]
    exact he M w a z n hz i
  · intro M w a t ht x
    rw [← (h M w).mixedD a t ht]
    exact hB M w a t ht x
  · intro M w t ht x hx
    rw [← h M w t ht]
    exact hs M w t ht x hx

lemma ElementaryPieces.fullInertial {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F) :
    ElementaryPieces (fun p => fullInertial (L p)) (fun p => fullInertial (V p)) κ
      (fun M w => fullInertial (F M w)) := by
  intro M w t ht
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact timeGerm_fullInertial hh
  · simpa only [fullInertial_translate] using timeGerm_fullInertial hh

lemma ElementaryPieces.viscous {d : ℕ} {L V : (Fin d → ℝ) → Velocity}
    {κ : ℕ → Fin d → ℚ} {F : Family Velocity} (h : ElementaryPieces L V κ F) :
    ElementaryPieces (fun p => viscousCoefficient (L p)) (fun p => viscousCoefficient (V p)) κ
      (fun M w => viscousCoefficient (F M w)) := by
  intro M w t ht
  have hh := h M w t ht
  split_ifs at hh ⊢ with hlt
  · exact timeGerm_viscous hh
  · simpa only [viscous_translate] using timeGerm_viscous hh

theorem effective_loaded_family {κ : ℕ → Fin 3 → ℚ} (hκ : Computable κ)
    (C : ℕ) (hC : ∀n i, |(κ n i : ℝ)| ≤ C)
    {v : Velocity} {K : Set Space} (hK : IsCompact K)
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (he : ElementaryField (fun _ : Fin 3 → ℝ => v)) :
    let U : Family Velocity := fun M w =>
      loadedRepeat (loadingVelocity (rationalSpace (κ (inputCode M w))) 1) v
    EffectiveFamily U ∧ EffectiveFamily (fun M w => inertialCoefficient (U M w)) ∧
      EffectiveFamily (fun M w => viscousCoefficient (U M w)) := by
  dsimp only
  let U : Family Velocity := fun M w =>
    loadedRepeat (loadingVelocity (rationalSpace (κ (inputCode M w))) 1) v
  have hU (M : FiniteMachine) (w : Input M) : JointSmooth (U M w) :=
    loadedRepeat_jointSmooth (loadingVelocity_jointSmooth _ _) hv hc
  have hp : ElementaryPieces (fun p : Fin 3 → ℝ => loadingVelocity p 1)
      (fun _ : Fin 3 → ℝ => v) κ U := by
    intro M w t ht
    split_ifs with hlt
    · exact loadedRepeat_germ_before hc hlt
    · exact loadedRepeat_germ_after (fun _ ht => loadingVelocity_zero ht) hc (le_of_not_gt hlt)
  obtain ⟨r,hr⟩ := hK.isBounded.subset_closedBall (0 : Space)
  obtain ⟨n,hn⟩ := exists_nat_ge r
  let R : ℕ := max n (C+6)
  have hS (M : FiniteMachine) (w : Input M) :
      SpatiallySupported (Metric.closedBall (0 : Space) R) (U M w) := by
    intro t x hx
    apply loadedRepeat_support (loadingVelocity_supported _ (by norm_num : (0 : ℝ) < 1)) hs t x
    intro hm
    apply hx
    rcases hm with hm | hm
    · exact Metric.closedBall_subset_closedBall (by exact_mod_cast (Nat.le_max_right n (C+6)))
        (loadingSupport_ball (hC (inputCode M w)) hm)
    · exact Metric.closedBall_subset_closedBall
        (hn.trans (by exact_mod_cast (Nat.le_max_left n (C+6)))) (hr hm)
  have el : ElementaryField (fun p : Fin 3 → ℝ => loadingVelocity p 1) :=
    elementary_loadingVelocity ⟨1, by simp⟩
  have sl := fun p : Fin 3 → ℝ => loadingVelocity_jointSmooth p 1
  have eu := effectiveFamily_of_elementary_pieces el he sl (fun _ => hv) hκ C R hC hU hS hp
  have e₀ := effectiveFamily_of_elementary_pieces el.fullInertial he.fullInertial
    (fun p => (sl p).fullInertial) (fun _ => hv.fullInertial) hκ C R hC
    (fun M w => (hU M w).fullInertial) (fun M w => (hS M w).fullInertial) hp.fullInertial
  have e₁ := effectiveFamily_of_elementary_pieces el.viscous he.viscous
    (fun p => (sl p).viscousCoefficient) (fun _ => hv.viscousCoefficient) hκ C R hC
    (fun M w => (hU M w).viscousCoefficient)
    (fun M w => (hS M w).viscousCoefficient Metric.isClosed_closedBall) hp.viscous
  exact ⟨eu,EffectiveFamily.forwardEq e₀ (fun M w => fullInertial_forwardEq (hU M w)),e₁⟩

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MainResult ----
namespace OAI

noncomputable section
namespace BalancedTransport
open BalancedTransport.Geometry

theorem balanced_three_stack_realization :
    ∃ U f₀ f₁ : Family Velocity,
    ∃ X : Family MaterialFlow,
    ∃ repeated : FiniteMachine → Velocity,
      EffectiveFamily U ∧ EffectiveFamily f₀ ∧ EffectiveFamily f₁ ∧
      (∀ M, Function.Periodic (repeated M) 1) ∧
      ∀ (M : FiniteMachine) (w : Input M),
        Smooth (U M w) ∧ Smooth (f₀ M w) ∧ Smooth (f₁ M w) ∧
        f₀ M w = inertialCoefficient (U M w) ∧
        f₁ M w = viscousCoefficient (U M w) ∧
        CommonCompactSupport (U M w) (f₀ M w) (f₁ M w) ∧
        BoundedMixed (U M w) ∧
        PeriodicAfterOne (U M w) ∧
        (∀ t, 1 ≤ t → ∀ x, U M w t x = repeated M t x) ∧
        ComparisonClass (U M w) (fun _ _ => 0) ∧
        IsMaterialFlow (U M w) (X M w) ∧
        ((∃ t : ℝ, 0 ≤ t ∧ X M w t fixedLabel ∈ observer) ↔ Halts M w) ∧
        ∀ ν : ℝ, 0 < ν →
          let f := affineForce (f₀ M w) (f₁ M w) ν
          ZeroDataSolution ν f (U M w) (fun _ _ => 0) ∧
          Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧
          UniqueInComparison ν f (U M w) ∧
          (ComputableReal ν → EffectiveFieldIn ∅ f) ∧
          (∀ name : ℕ → ℚ, RealName name ν → EffectiveFieldIn {nameOracle name} f) := by
  obtain ⟨N, δ, hδ, hh⟩ := Universal.exists_universal_machine
  obtain ⟨v, K, hK, hv, hc, hs, hd, hg, he⟩ :=
    Effectivity.exists_elementary_guarded_template N.normalized 3
  let κ : ℕ → Fin 3 → ℚ := fun n =>
    Recorder.Checkpoint.rationalInitial N.normalized (some N.initial) (δ n)
  have hκ : Computable κ := (Effectivity.computable_rationalInitial N).comp hδ
  obtain ⟨C, hC⟩ := Effectivity.rationalInitial_bounded N
  let z : Family Space := fun M w => rationalSpace (κ (inputCode M w))
  let U : Family Velocity := fun M w => loadedRepeat (loadingVelocity (z M w) 1) v
  have hz (M : FiniteMachine) (w : Input M) : z M w =
      ((N.initialWork (δ (inputCode M w))).expand N.normalized).code N.normalized :=
    Recorder.Checkpoint.rationalInitial_cast N.normalized (some N.initial) (δ (inputCode M w))
  have hu (M : FiniteMachine) (w : Input M) :=
    loaded_template_realization (z M w) (by norm_num : (0 : ℝ) < 1) hK hv hc hs hd
  have hlc (M : FiniteMachine) (w : Input M) : TimeCollars (loadingVelocity (z M w) 1) :=
    fun _ ht => loadingVelocity_zero ht
  have hr (M : FiniteMachine) (w : Input M) :=
    prescribed_residual_realization ((loadingSupport_compact (z M w) 1).union hK)
      (hu M w).1 (hu M w).2.1 (loadedRepeat_repeats (hlc M w)) (hu M w).2.2.2.1
      (fun t (_ : 0 ≤ t) x => loadedRepeat_divergence
        (loadingVelocity_jointSmooth (z M w) 1) hv hc
        (loadingVelocity_divergence (z M w) 1) hd t x)
  have ef : EffectiveFamily U ∧
      EffectiveFamily (fun M w => inertialCoefficient (U M w)) ∧
      EffectiveFamily (fun M w => viscousCoefficient (U M w)) :=
    Effectivity.effective_loaded_family hκ C (fun n => hC (δ n)) hK hv hc hs he
  choose X hX using (fun M w => (hu M w).2.2.2.2.2.2.1)
  refine ⟨U, (fun M w => inertialCoefficient (U M w)),
    (fun M w => viscousCoefficient (U M w)), X, (fun _ => repeatTemplate v),
    ef.1, ef.2.1, ef.2.2, (fun _ => repeatTemplate_zero_period v), ?_⟩
  intro M w
  obtain ⟨hsm, hsm₀, hsm₁, hsupp, hb, _, _, hp, hclass, _, hres⟩ := hr M w
  refine ⟨hsm, hsm₀, hsm₁, rfl, rfl, hsupp, hb, hp, ?_, hclass, hX M w, ?_, ?_⟩
  · intro t ht x
    exact congrFun ((hu M w).2.2.2.2.2.1 t ht) x
  · have hx : IsMaterialFlow
        (loadedRepeat (loadingVelocity
          (((N.initialWork (δ (inputCode M w))).expand N.normalized).code N.normalized) 1) v)
        (X M w) := by
      rw [← hz M w]
      exact hX M w
    exact (N.compiled_continuous_halting_iff (δ (inputCode M w))
      (by norm_num : (0 : ℝ) < 1) hK hv hc hs hg hx).trans (hh M w)
  · intro ν hν
    obtain ⟨hsol, hsf, hbf, hpf, huniq⟩ := hres ν hν
    have heff := Effectivity.residual_effective_viscosity (fun M w => (hu M w).1)
      ef.2.1 ef.2.2 M w ν
    exact ⟨hsol, hsf, hbf, hpf, huniq, heff.1, heff.2⟩

end BalancedTransport
end

end OAI

-- ---- mission target ----
open OAI OAI.BalancedTransport
open BalancedTransport.Geometry

namespace OAI
namespace BalancedTransport
theorem _root_.solution :
    ∃ U f₀ f₁ : Family Velocity,
    ∃ X : Family MaterialFlow,
    ∃ repeated : FiniteMachine → Velocity,
      EffectiveFamily U ∧ EffectiveFamily f₀ ∧ EffectiveFamily f₁ ∧
      (∀ M, Function.Periodic (repeated M) 1) ∧
      ∀ (M : FiniteMachine) (w : Input M),
        Smooth (U M w) ∧ Smooth (f₀ M w) ∧ Smooth (f₁ M w) ∧
        f₀ M w = inertialCoefficient (U M w) ∧
        f₁ M w = viscousCoefficient (U M w) ∧
        CommonCompactSupport (U M w) (f₀ M w) (f₁ M w) ∧
        BoundedMixed (U M w) ∧
        PeriodicAfterOne (U M w) ∧
        (∀ t, 1 ≤ t → ∀ x, U M w t x = repeated M t x) ∧
        ComparisonClass (U M w) (fun _ _ => 0) ∧
        IsMaterialFlow (U M w) (X M w) ∧
        ((∃ t : ℝ, 0 ≤ t ∧ X M w t fixedLabel ∈ observer) ↔ Halts M w) ∧
        ∀ ν : ℝ, 0 < ν →
          let f := affineForce (f₀ M w) (f₁ M w) ν
          ZeroDataSolution ν f (U M w) (fun _ _ => 0) ∧
          Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧
          UniqueInComparison ν f (U M w) ∧
          (ComputableReal ν → EffectiveFieldIn ∅ f) ∧
          (∀ name : ℕ → ℚ, RealName name ν → EffectiveFieldIn {nameOracle name} f) := by
  first
    | exact OAI.BalancedTransport.balanced_three_stack_realization
    | (apply OAI.BalancedTransport.balanced_three_stack_realization <;> assumption)
    | (intros; apply OAI.BalancedTransport.balanced_three_stack_realization <;> assumption)
end BalancedTransport
end OAI
