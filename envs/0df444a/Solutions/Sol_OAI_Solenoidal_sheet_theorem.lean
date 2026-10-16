-- Prove2me | solution 1 for OAI.Solenoidal.sheet_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:53:41.908986+00:00
-- url     : https://prove2.me/submissions/716d5c0f-7461-407b-ae19-fdd3f3be116a

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/SheetProgram.lean:L15-L58
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Solenoidal.sheet_theorem.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Solenoidal_sheet_theorem) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Circuits
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_CircuitPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EffectiveForcing
import Theorems.Thm_OAI_Solenoidal_ClassicalSolution_relativeEnergy_derivative_bound
import Theorems.Thm_OAI_Solenoidal_ClassicalSolution_relativeEnergy_hasDerivAt
import Theorems.Thm_OAI_Solenoidal_Computing_int_add
import Theorems.Thm_OAI_Solenoidal_Computing_int_mul
import Theorems.Thm_OAI_Solenoidal_Computing_rat_inv
import Theorems.Thm_OAI_Solenoidal_QBall_reciprocalApprox_approximates
import Theorems.Thm_OAI_Solenoidal_Rectangle_mem_iff_abs
import Theorems.Thm_OAI_Solenoidal_circuit_periodic_bound
import Theorems.Thm_OAI_Solenoidal_globalDirectForce_classicalSolution
import Theorems.Thm_OAI_Solenoidal_mixedDerivative_eqOn_cell
import Theorems.Thm_OAI_Solenoidal_mixed_lipschitz
import Theorems.Thm_OAI_Solenoidal_norm_flatten
import Theorems.Thm_OAI_Solenoidal_repeatedPath_on_collar
import Theorems.Thm_OAI_Solenoidal_scheduleVelocity_at_time
import Theorems.Thm_OAI_Solenoidal_scheduledPulse_integer_collar
import Theorems.Thm_OAI_Solenoidal_stageState_eq_sum
import Theorems.Thm_OAI_Solenoidal_tensorVelocity_formula
import Theorems.Thm_OAI_Solenoidal_travelProgram_on
import Theorems.Thm_OAI_Solenoidal_verticalPulse_formula
import Theorems.Thm_OAI_Solenoidal_verticalPulse_off_far
import Theorems.Thm_OAI_Solenoidal_zero_classical_solution

-- ---- from OAI.MathematicalPhysics.SheetFlows.DirectForce ----
namespace OAI

/-! SheetFlows direct force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem zero_spatially_periodic : SpatiallyPeriodic (0 : Field) := by
  intro t x k
  rfl

theorem zero_smooth : Smooth (0 : Field) := contDiff_const

theorem zero_mean_zero : MeanZero (0 : Field) := by
  intro t
  simp

theorem zero_divergence_free : DivergenceFree (0 : Field) := by
  intro t x
  simp [divergence]

theorem zero_one_periodic : OnePeriodic (0 : Field) := by
  intro t x
  rfl

theorem zero_integer_collars : IntegerCollars (0 : Field) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro n t x _
  rfl

theorem zero_effective : Effective (0 : Field) := by
  refine ⟨Nat.Partrec.Code.const (@Encodable.encode (Fin 3 → ℚ) Encodable.finArrow 0), ?_⟩
  intro α c z _ ε hε
  refine ⟨0, ?_, ?_⟩
  · simp [Nat.Partrec.Code.eval_const]
  · simpa using (show (0 : ℝ) < (ε : ℝ) by exact_mod_cast hε)

theorem zero_effective_bounds : EffectiveBounds (0 : Field) := by
  refine ⟨Nat.Partrec.Code.const (Encodable.encode (0 : ℚ)), ?_⟩
  intro α
  refine ⟨0, ?_, le_rfl, ?_⟩
  · simp [Nat.Partrec.Code.eval_const]
  · intro z
    simp

theorem zero_material_flow : MaterialFlow (0 : Field) (fun _ a => a) := by
  refine ⟨fun _ => rfl, fun _ => continuous_const.continuousOn, ?_⟩
  intro a t _
  exact hasDerivWithinAt_const t (Set.Ici 0) a

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Profiles ----
namespace OAI

/-! SheetFlows profiles. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

open Filter
open scoped Topology

theorem plateau_one {h d s : ℝ} (hd : 0 < d) (hs : |s| ≤ h + d / 2) :
    plateau h d s = 1 := by
  rcases abs_le.mp hs with ⟨hl, hu⟩
  have h₁ : 1 ≤ 2 * (s + h + d) / d := (le_div_iff₀ hd).mpr (by linarith)
  have h₂ : 1 ≤ 2 * (h + d - s) / d := (le_div_iff₀ hd).mpr (by linarith)
  simp only [plateau, Real.smoothTransition.one_of_one_le h₁,
    Real.smoothTransition.one_of_one_le h₂, mul_one]

theorem linearProfile_eq {h d s : ℝ} (hd : 0 < d) (hs : |s| ≤ h + d / 2) :
    linearProfile h d s = s := by simp [linearProfile, plateau_one hd hs]

theorem Cprofile_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10) :
    Cprofile h d c s = plateau h d (s - c) :=
  periodize_on_chart (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => plateau_zero hd) hl hu) hs

theorem Dprofile_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10) :
    Dprofile h d c s = linearProfile h d (s - c) :=
  periodize_on_chart (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => linearProfile_zero hd) hl hu) hs

theorem Cprofile_one {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : |s - c| ≤ h + d / 2) : Cprofile h d c s = 1 := by
  rw [Cprofile_on_chart hd hl hu hs]
  exact plateau_one hd hsc

theorem Dprofile_linear {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : |s - c| ≤ h + d / 2) : Dprofile h d c s = s - c := by
  rw [Dprofile_on_chart hd hl hu hs]
  exact linearProfile_eq hd hsc

theorem Cprofile_zero_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : h + d ≤ |s - c|) : Cprofile h d c s = 0 := by
  rw [Cprofile_on_chart hd hl hu hs]
  exact plateau_zero hd hsc

theorem Dprofile_zero_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : h + d ≤ |s - c|) : Dprofile h d c s = 0 := by
  rw [Dprofile_on_chart hd hl hu hs]
  exact linearProfile_zero hd hsc

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Clocks ----
namespace OAI

/-! SheetFlows clocks. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem slot_ordered {m : ℕ} {i j : Fin m} (hij : i < j) :
    slotRight m i < slotLeft m j := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  dsimp [slotLeft, slotRight]
  field_simp
  nlinarith

theorem scheduledPulse_contDiff {m : ℕ} (i : Fin m) :
    ContDiff ℝ (⊤ : ℕ∞) (scheduledPulse m i) :=
  periodicPulse_contDiff (slot_bounds i).2.1

theorem scheduledPulse_periodic {m : ℕ} (i : Fin m) :
    Function.Periodic (scheduledPulse m i) 1 := periodicPulse_periodic _ _

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Differential ----
namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem continuous_integrableOn_cell {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} (hg : Continuous g) : IntegrableOn g fundamentalCell := by
  apply (hg.integrableOn_Icc (a := (0 : Space)) (b := fun _ => 10)).mono_set
  intro x hx
  constructor
  · intro j
    exact (hx j (Set.mem_univ j)).1
  · intro j
    exact (hx j (Set.mem_univ j)).2.le

theorem scheduleVelocity_smooth {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (v i)) : Smooth (scheduleVelocity v) := by
  apply ContDiff.sum
  intro i _
  exact ((scheduledPulse_contDiff i).comp contDiff_fst).smul ((hv i).comp contDiff_snd)

theorem scheduleVelocity_spatially_periodic {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i x k, v i (x + deck k) = v i x) :
    SpatiallyPeriodic (scheduleVelocity v) := by
  intro t x k
  exact Finset.sum_congr rfl (fun i _ => congrArg (scheduledPulse m i t • ·) (hv i x k))

theorem scheduleVelocity_onePeriodic {m : ℕ} (v : Fin m → Space → Space) :
    OnePeriodic (scheduleVelocity v) := by
  intro t x
  apply Finset.sum_congr rfl
  intro i _
  rw [scheduledPulse_periodic i t]

theorem scheduleVelocity_meanZero {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, Continuous (v i)) (hz : ∀ i, (∫ x in fundamentalCell, v i x) = 0) :
    MeanZero (scheduleVelocity v) := by
  intro t
  dsimp [scheduleVelocity]
  rw [integral_finsetSum]
  · simp only [integral_smul, hz, smul_zero, Finset.sum_const_zero]
  · intro i _
    exact (continuous_integrableOn_cell (hv i)).smul (scheduledPulse m i t)

theorem scheduleVelocity_integerCollars {m : ℕ} (v : Fin m → Space → Space) :
    IntegerCollars (scheduleVelocity v) := by
  refine ⟨1/4, by norm_num, ?_⟩
  intro n t x ht
  apply Finset.sum_eq_zero
  intro i _
  rw [scheduledPulse_integer_collar i n ht, zero_smul]

theorem scheduleVelocity_initial {m : ℕ} (v : Fin m → Space → Space) (x : Space) :
    scheduleVelocity v 0 x = 0 := by
  rcases scheduleVelocity_integerCollars v with ⟨ε, hε, h⟩
  exact h 0 0 x (by simpa using hε)

theorem scheduleVelocity_divergence_free {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, Differentiable ℝ (v i))
    (hz : ∀ i x, ∑ j : Fin 3, fderiv ℝ (v i) x (basis j) j = 0) :
    DivergenceFree (scheduleVelocity v) := by
  intro t x
  rcases scheduleVelocity_at_time v t with ht | ⟨i, hi⟩
  · simp [divergence, spatialPartial, ht]
  · dsimp [divergence, spatialPartial]
    rw [hi, fderiv_const_smul (hv i x)]
    simp only [smul_apply, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, hz, mul_zero]

theorem scheduleVelocity_advection_zero {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, Differentiable ℝ (v i))
    (hz : ∀ i x, fderiv ℝ (v i) x (v i x) = 0) :
    ∀ t x, advection (scheduleVelocity v) t x = 0 := by
  intro t x
  rcases scheduleVelocity_at_time v t with ht | ⟨i, hi⟩
  · simp [advection, ht]
  · dsimp [advection]
    rw [hi, fderiv_const_smul (hv i x)]
    simp only [smul_apply, Pi.smul_apply, map_smul, hz, smul_zero]

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directional_contDiff {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (directional g v) :=
  (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

theorem directional_directional {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v w x : E) :
    directional (directional g v) w x = fderiv ℝ (fderiv ℝ g) x w v := by
  change fderiv ℝ (fun y => fderiv ℝ g y v) x w = _
  rw [fderiv_clm_apply ((contDiff_infty_iff_fderiv.mp hg).2.differentiable (by simp) x)
    (differentiableAt_const v)]
  simp

theorem directional_commute {g : E → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v w : E) :
    directional (directional g v) w = directional (directional g w) v := by
  funext x
  rw [directional_directional hg, directional_directional hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).eq w v

theorem directional_translation {g : E → F} (hg : Differentiable ℝ g)
    {c : E} (hc : ∀ x, g (x + c) = g x) (v x : E) :
    directional g v (x + c) = directional g v x := by
  have hd := (hg (x + c)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const c)
  have he : (fun y => g (y + c)) = g := funext hc
  have hd' : HasFDerivAt g (fderiv ℝ g (x + c)) x := by simpa only [Function.comp_def, id_eq, he, ContinuousLinearMap.comp_id] using hd
  exact (congrArg (fun L : E →L[ℝ] F => L v) hd'.fderiv).symm

end DirectionalCalculus

theorem fieldDirectional_smooth {u : Field} (hu : Smooth u) (v : SpaceTime) :
    Smooth (fieldDirectional u v) := directional_contDiff hu v

theorem spatialPartial_eq_fieldDirectional {u : Field} (hu : Smooth u) (j : Fin 3) :
    spatialPartial u j = fieldDirectional u (0, basis j) := by
  funext t x
  have h := (hu.differentiable (by simp) (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have he : fderiv ℝ (u t) x =
      (fderiv ℝ (Function.uncurry u) (t, x)).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) := h.fderiv
  change fderiv ℝ (u t) x (basis j) = _
  rw [he]
  rfl

theorem fullTimePartial_eq_fieldDirectional {u : Field} (hu : Smooth u) :
    fullTimePartial u = fieldDirectional u (1, 0) := by
  funext t x
  exact ((hu.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

theorem smooth_spatialPartial {u : Field} (hu : Smooth u) (j : Fin 3) :
    Smooth (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu j]
  exact fieldDirectional_smooth hu _

theorem smooth_fullTimePartial {u : Field} (hu : Smooth u) : Smooth (fullTimePartial u) := by
  rw [fullTimePartial_eq_fieldDirectional hu]
  exact fieldDirectional_smooth hu _

theorem smooth_laplacian {u : Field} (hu : Smooth u) : Smooth (laplacian u) := by
  exact ContDiff.sum (fun j _ => smooth_spatialPartial (smooth_spatialPartial hu j) j)

theorem smooth_spatial_slice {u : Field} (hu : Smooth u) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (u t) := hu.comp (contDiff_const.prodMk contDiff_id)

theorem globalDirectForce_smooth {u : Field} (hu : Smooth u) (ν : ℝ) :
    Smooth (globalDirectForce ν u) :=
  (smooth_fullTimePartial hu).sub ((contDiff_const (c := ν)).smul (smooth_laplacian hu))

theorem fieldDirectional_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (v : SpaceTime) : SpatiallyPeriodic (fieldDirectional u v) := by
  intro t x k
  unfold fieldDirectional
  have he : ((t, x + deck k) : SpaceTime) = (t, x) + (0, deck k) := by simp
  rw [he]
  exact directional_translation (g := Function.uncurry u) (hu.differentiable (by simp))
    (c := (0, deck k)) (fun z => by simpa [Function.uncurry] using hp z.1 z.2 k) v (t, x)

theorem fieldDirectional_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (v : SpaceTime) : OnePeriodic (fieldDirectional u v) := by
  intro t x
  unfold fieldDirectional
  have he : ((t + 1, x) : SpaceTime) = (t, x) + (1, 0) := by simp
  rw [he]
  exact directional_translation (g := Function.uncurry u) (hu.differentiable (by simp))
    (c := (1, 0)) (fun z => by simpa [Function.uncurry] using hp z.1 z.2) v (t, x)

theorem spatialPartial_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (j : Fin 3) : SpatiallyPeriodic (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu j]
  exact fieldDirectional_spatially_periodic hu hp _

theorem spatialPartial_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (j : Fin 3) : OnePeriodic (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu j]
  exact fieldDirectional_onePeriodic hu hp _

theorem globalDirectForce_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (ν : ℝ) : SpatiallyPeriodic (globalDirectForce ν u) := by
  have ht : SpatiallyPeriodic (fullTimePartial u) := by
    rw [fullTimePartial_eq_fieldDirectional hu]
    exact fieldDirectional_spatially_periodic hu hp _
  have hl : SpatiallyPeriodic (laplacian u) := by
    intro t x k
    exact Finset.sum_congr rfl (fun j _ =>
      spatialPartial_spatially_periodic (smooth_spatialPartial hu j)
        (spatialPartial_spatially_periodic hu hp j) j t x k)
  intro t x k
  simp only [globalDirectForce, ht t x k, hl t x k]

theorem globalDirectForce_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (ν : ℝ) : OnePeriodic (globalDirectForce ν u) := by
  have ht : OnePeriodic (fullTimePartial u) := by
    rw [fullTimePartial_eq_fieldDirectional hu]
    exact fieldDirectional_onePeriodic hu hp _
  have hl : OnePeriodic (laplacian u) := by
    intro t x
    exact Finset.sum_congr rfl (fun j _ =>
      spatialPartial_onePeriodic (smooth_spatialPartial hu j)
        (spatialPartial_onePeriodic hu hp j) j t x)
  intro t x
  simp only [globalDirectForce, ht t x, hl t x]

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ScheduledForce ----
namespace OAI

/-! SheetFlows scheduled force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem mixedDerivative_contDiff {u : Field} (hu : Smooth u) (α : List (Fin 4)) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedDerivative u α) := by
  induction α with
  | nil => exact hu
  | cons j α ih => exact directional_contDiff ih (spacetimeBasis j)

theorem mixedDerivative_translation {u : Field} (hu : Smooth u)
    (c : SpaceTime) (hc : ∀ z : SpaceTime, u (z + c).1 (z + c).2 = u z.1 z.2)
    (α : List (Fin 4)) (z : SpaceTime) :
    mixedDerivative u α (z + c) = mixedDerivative u α z := by
  induction α generalizing z with
  | nil => exact hc z
  | cons j α ih =>
    exact directional_translation ((mixedDerivative_contDiff hu α).differentiable (by simp))
      ih (spacetimeBasis j) z

theorem mixedDerivative_spatially_periodic {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (α : List (Fin 4)) :
    SpatiallyPeriodic (fun t x => mixedDerivative u α (t, x)) := by
  intro t x k
  have h := mixedDerivative_translation hu (0, deck k)
    (fun z => by simpa using hp z.1 z.2 k) α (t, x)
  simpa using h

theorem mixedDerivative_onePeriodic {u : Field} (hu : Smooth u)
    (hp : OnePeriodic u) (α : List (Fin 4)) :
    OnePeriodic (fun t x => mixedDerivative u α (t, x)) := by
  intro t x
  have h := mixedDerivative_translation hu (1, 0)
    (fun z => by simpa using hp z.1 z.2) α (t, x)
  simpa using h

theorem wrapSpace_mem (x : Space) : wrapSpace x ∈ Set.Icc 0 (fun _ => 10) := by
  constructor <;> intro j
  · exact mul_nonneg (by norm_num) (Int.fract_nonneg _)
  · have := Int.fract_lt_one (x j / 10)
    change 10 * Int.fract (x j / 10) ≤ 10
    linarith

theorem wrapSpace_add_deck (x : Space) :
    wrapSpace x + deck (fun j => ⌊x j / 10⌋) = x := by
  ext j
  simp only [Pi.add_apply, wrapSpace, deck, Int.fract]
  ring

theorem periodic_field_reduction {u : Field} (hspace : SpatiallyPeriodic u)
    (htime : OnePeriodic u) (t : ℝ) (x : Space) :
    u t x = u (Int.fract t) (wrapSpace x) := by
  calc
    u t x = u t (wrapSpace x) := by
      conv_lhs => rw [← wrapSpace_add_deck x]
      exact hspace t (wrapSpace x) _
    _ = u (Int.fract t) (wrapSpace x) := by
      have hp : Function.Periodic (fun s => u s (wrapSpace x)) 1 :=
        fun s => htime s (wrapSpace x)
      have h := hp.int_mul ⌊t⌋ (Int.fract t)
      simpa only [mul_one, Int.fract_add_floor] using h

theorem periodic_continuous_bounded {u : Field}
    (hu : Continuous (fun z : SpaceTime => u z.1 z.2))
    (hspace : SpatiallyPeriodic u) (htime : OnePeriodic u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t x, ‖u t x‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : SpaceTime))
    (b := (1, fun _ => 10))).exists_bound_of_continuousOn hu.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t x => ?_⟩
  rw [periodic_field_reduction hspace htime]
  apply (hC (Int.fract t, wrapSpace x) ?_).trans (le_max_left _ _)
  exact ⟨⟨Int.fract_nonneg t, (wrapSpace_mem x).1⟩,
    ⟨(Int.fract_lt_one t).le, (wrapSpace_mem x).2⟩⟩

theorem periodic_smooth_mixed_bounded {u : Field} (hu : Smooth u)
    (hspace : SpatiallyPeriodic u) (htime : OnePeriodic u) (α : List (Fin 4)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : SpaceTime, ‖mixedDerivative u α z‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := periodic_continuous_bounded
    (u := fun t x => mixedDerivative u α (t, x))
    (mixedDerivative_contDiff hu α).continuous
    (mixedDerivative_spatially_periodic hu hspace α)
    (mixedDerivative_onePeriodic hu htime α)
  exact ⟨B, hB, fun z => hbound z.1 z.2⟩

theorem fieldDirectional_commute {u : Field} (hu : Smooth u) (v w : SpaceTime) :
    fieldDirectional (fieldDirectional u v) w =
      fieldDirectional (fieldDirectional u w) v := by
  have h := directional_commute (g := Function.uncurry u) hu v w
  funext t x
  exact congrFun h (t, x)

theorem directional_component {g : SpaceTime → Space} (hg : Differentiable ℝ g)
    (v z : SpaceTime) (j : Fin 3) :
    directional (fun y => g y j) v z = directional g v z j := by
  dsimp [directional]
  rw [fderiv_apply (hg z) j]
  rfl

theorem divergence_fieldDirectional {u : Field} (hu : Smooth u)
    (v : SpaceTime) (t : ℝ) (x : Space) :
    divergence (fieldDirectional u v) t x =
      directional (fun z : SpaceTime => divergence u z.1 z.2) v (t, x) := by
  have hg (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : SpaceTime => spatialPartial u j z.1 z.2 j) :=
    (contDiff_apply ℝ ℝ j).comp (smooth_spatialPartial hu j)
  change (∑ j, spatialPartial (fieldDirectional u v) j t x j) =
    fderiv ℝ (fun z : SpaceTime => ∑ j, spatialPartial u j z.1 z.2 j) (t, x) v
  rw [fderiv_fun_sum (fun j _ => (hg j).differentiable (by simp) (t, x))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [spatialPartial_eq_fieldDirectional (fieldDirectional_smooth hu v) j,
    fieldDirectional_commute hu v (0, basis j)]
  have he := directional_component
    ((smooth_spatialPartial hu j).differentiable (by simp)) v (t, x) j
  rw [spatialPartial_eq_fieldDirectional hu j] at he ⊢
  exact he.symm

theorem fieldDirectional_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) (v : SpaceTime) : DivergenceFree (fieldDirectional u v) := by
  intro t x
  rw [divergence_fieldDirectional hu]
  have hz : (fun z : SpaceTime => divergence u z.1 z.2) = 0 :=
    funext (fun z => hdiv z.1 z.2)
  rw [hz, directional_zero]
  rfl

theorem spatialPartial_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) (j : Fin 3) : DivergenceFree (spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hu]
  exact fieldDirectional_divergence_free hu hdiv _

theorem fullTimePartial_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) : DivergenceFree (fullTimePartial u) := by
  rw [fullTimePartial_eq_fieldDirectional hu]
  exact fieldDirectional_divergence_free hu hdiv _

theorem divergence_sub {u v : Field} (hu : Smooth u) (hv : Smooth v) (t : ℝ) (x : Space) :
    divergence (u - v) t x = divergence u t x - divergence v t x := by
  change (∑ j, fderiv ℝ (u t - v t) x (basis j) j) = _
  rw [fderiv_sub ((smooth_spatial_slice hu t).differentiable (by simp) x)
    ((smooth_spatial_slice hv t).differentiable (by simp) x)]
  simp only [sub_apply, Pi.sub_apply, Finset.sum_sub_distrib]
  rfl

theorem divergence_smul {u : Field} (hu : Smooth u) (c t : ℝ) (x : Space) :
    divergence (c • u) t x = c * divergence u t x := by
  change (∑ j, fderiv ℝ (c • u t) x (basis j) j) = _
  rw [fderiv_const_smul ((smooth_spatial_slice hu t).differentiable (by simp) x) c]
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rfl

theorem divergence_sum {ι : Type*} [Fintype ι] (u : ι → Field)
    (hu : ∀ i, Smooth (u i)) (t : ℝ) (x : Space) :
    divergence (∑ i, u i) t x = ∑ i, divergence (u i) t x := by
  have hsum : (∑ i, u i) t = ∑ i, u i t := by simp
  unfold divergence spatialPartial
  rw [hsum, fderiv_sum (fun i _ => (smooth_spatial_slice (hu i) t).differentiable (by simp) x)]
  simp only [sum_apply, Finset.sum_apply]
  exact Finset.sum_comm

theorem laplacian_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) : DivergenceFree (laplacian u) := by
  intro t x
  have hL : laplacian u = ∑ j, spatialPartial (spatialPartial u j) j := by
    funext t x
    simp [laplacian]
  rw [hL, divergence_sum _ (fun j => smooth_spatialPartial (smooth_spatialPartial hu j) j)]
  apply Finset.sum_eq_zero
  intro j _
  exact spatialPartial_divergence_free (smooth_spatialPartial hu j)
    (spatialPartial_divergence_free hu hdiv j) j t x

theorem globalDirectForce_divergence_free {u : Field} (hu : Smooth u)
    (hdiv : DivergenceFree u) (ν : ℝ) : DivergenceFree (globalDirectForce ν u) := by
  intro t x
  change divergence (fullTimePartial u - ν • laplacian u) t x = 0
  have hv : Smooth (ν • laplacian u) :=
    (contDiff_const (c := ν)).smul (smooth_laplacian hu)
  rw [divergence_sub (smooth_fullTimePartial hu) hv,
    divergence_smul (smooth_laplacian hu),
    fullTimePartial_divergence_free hu hdiv t x, laplacian_divergence_free hu hdiv t x]
  simp

theorem cell_ae_eq_Icc : fundamentalCell =ᵐ[volume] Set.Icc (0 : Space) (fun _ => 10) :=
  Measure.univ_pi_Ico_ae_eq_Icc

theorem face_front_eq_back_deck (j : Fin 3) (y : Fin 2 → ℝ) :
    j.insertNth (10 : ℝ) y = j.insertNth 0 y + deck (Pi.single j 1) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k, rfl⟩
  · simp [deck]
  · simp [deck]

theorem periodic_integral_divergence_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Fin 3 → Space → E)
    (hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j))
    (hp : ∀ j x k, g j (x + deck k) = g j x) :
    (∫ x in fundamentalCell, ∑ j : Fin 3, fderiv ℝ (g j) x (basis j)) = 0 := by
  rw [setIntegral_congr_set cell_ae_eq_Icc]
  have hder : Continuous (fun x : Space => ∑ j : Fin 3, fderiv ℝ (g j) x (basis j)) :=
    (ContDiff.sum (fun j _ => directional_contDiff (hg j) (basis j))).continuous
  simp only [basis] at *
  rw [integral_divergence_of_hasFDerivAt_off_countable' (0 : Space) (fun _ => 10)
    (fun _ => by norm_num) g (fun j => fderiv ℝ (g j)) ∅ Set.countable_empty
    (fun j => (hg j).continuous.continuousOn)
    (fun x _ j => (hg j).differentiable (by simp) x |>.hasFDerivAt)
    hder.integrableOn_Icc]
  apply Finset.sum_eq_zero
  intro j _
  have he : (fun y : Fin 2 → ℝ => g j (j.insertNth 10 y)) =
      (fun y : Fin 2 → ℝ => g j (j.insertNth 0 y)) := by
    funext y
    rw [face_front_eq_back_deck]
    exact hp j _ _
  change (∫ y in Set.Icc _ _, g j (j.insertNth 10 y)) -
    (∫ y in Set.Icc _ _, g j (j.insertNth 0 y)) = 0
  rw [he, sub_self]

theorem periodic_integral_partial_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : Space → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : ∀ x k, g (x + deck k) = g x) (j : Fin 3) :
    (∫ x in fundamentalCell, fderiv ℝ g x (basis j)) = 0 := by
  classical
  have h := periodic_integral_divergence_zero (fun k => if k = j then g else 0)
    (fun k => by split_ifs <;> first | exact hg | exact contDiff_const)
    (fun k x l => by split_ifs <;> first | exact hp x l | rfl)
  have he (k : Fin 3) (x : Space) :
      fderiv ℝ (if k = j then g else 0) x (basis k) =
        if k = j then fderiv ℝ g x (basis j) else 0 := by
    by_cases hk : k = j
    · subst k
      simp
    · simp [hk]
  simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem spatialPartial_mean_zero {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (j : Fin 3) : MeanZero (spatialPartial u j) := by
  intro t
  exact periodic_integral_partial_zero (smooth_spatial_slice hu t) (hp t) j

theorem meanZero_sum {ι : Type*} [Fintype ι] (u : ι → Field)
    (hu : ∀ i, Smooth (u i)) (hz : ∀ i, MeanZero (u i)) : MeanZero (∑ i, u i) := by
  intro t
  simp only [Finset.sum_apply]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    continuous_integrableOn_cell (smooth_spatial_slice (hu i) t).continuous)]
  exact Finset.sum_eq_zero (fun i _ => hz i t)

theorem laplacian_mean_zero {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) : MeanZero (laplacian u) := by
  have hL : laplacian u = ∑ j, spatialPartial (spatialPartial u j) j := by
    funext t x
    simp [laplacian]
  rw [hL]
  exact meanZero_sum _ (fun j => smooth_spatialPartial (smooth_spatialPartial hu j) j)
    (fun j => spatialPartial_mean_zero (smooth_spatialPartial hu j)
      (spatialPartial_spatially_periodic hu hp j) j)

theorem scheduleVelocity_fullTimePartial {m : ℕ} (v : Fin m → Space → Space)
    (t : ℝ) (x : Space) :
    fullTimePartial (scheduleVelocity v) t x = ∑ i, deriv (scheduledPulse m i) t • v i x := by
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((scheduledPulse_contDiff i).differentiable (by simp) t).hasDerivAt.smul_const
      (v i x)))).deriv

theorem scheduleVelocity_fullTimePartial_mean_zero {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, Continuous (v i)) (hz : ∀ i, (∫ x in fundamentalCell, v i x) = 0) :
    MeanZero (fullTimePartial (scheduleVelocity v)) := by
  intro t
  simp_rw [scheduleVelocity_fullTimePartial]
  rw [integral_finsetSum Finset.univ
    (f := fun i x => deriv (scheduledPulse m i) t • v i x) (fun i _ =>
    (continuous_integrableOn_cell (hv i)).smul (deriv (scheduledPulse m i) t))]
  simp only [integral_smul, hz, smul_zero, Finset.sum_const_zero]

theorem globalDirectForce_mean_zero {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (ht : MeanZero (fullTimePartial u)) (ν : ℝ) :
    MeanZero (globalDirectForce ν u) := by
  intro t
  change (∫ x in fundamentalCell, fullTimePartial u t x - ν • laplacian u t x) = 0
  rw [integral_sub (f := fullTimePartial u t) (g := fun x => ν • laplacian u t x)
    (continuous_integrableOn_cell (smooth_spatial_slice (smooth_fullTimePartial hu) t).continuous)
    ((continuous_integrableOn_cell (smooth_spatial_slice (smooth_laplacian hu) t).continuous).smul ν),
    ht t, integral_smul, laplacian_mean_zero hu hp t]
  simp

theorem scheduled_direct_forcing {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (v i))
    (hp : ∀ i x k, v i (x + deck k) = v i x)
    (hz : ∀ i, (∫ x in fundamentalCell, v i x) = 0)
    (hdiv : ∀ i, DivergenceFree (fun _ => v i))
    (hadv : ∀ i x, fderiv ℝ (v i) x (v i x) = 0) (ν : ℝ) :
    let u := scheduleVelocity v
    let f := globalDirectForce ν u
    SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧ Smooth f ∧ Smooth u ∧
    MeanZero f ∧ MeanZero u ∧ DivergenceFree f ∧ DivergenceFree u ∧
    OnePeriodic f ∧ OnePeriodic u ∧
    ClassicalSolution ν f u (0 : Pressure) ∧ IntegerCollars u ∧
    (∀ t x, advection u t x = 0) ∧
    (∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖mixedDerivative f α z‖ ≤ B) ∧
    (∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖mixedDerivative u α z‖ ≤ B) := by
  dsimp only
  have hs := scheduleVelocity_smooth v hv
  have hsp := scheduleVelocity_spatially_periodic v hp
  have htp := scheduleVelocity_onePeriodic v
  have hd := scheduleVelocity_divergence_free v (fun i => (hv i).differentiable (by simp)) (fun i x => hdiv i 0 x)
  have ha := scheduleVelocity_advection_zero v (fun i => (hv i).differentiable (by simp)) hadv
  have hfs := globalDirectForce_smooth hs ν
  have hfsp := globalDirectForce_spatially_periodic hs hsp ν
  have hftp := globalDirectForce_onePeriodic hs htp ν
  refine ⟨hfsp, hsp, hfs, hs, ?_, ?_, ?_, hd, hftp, htp, ?_,
    scheduleVelocity_integerCollars v, ha, ?_, ?_⟩
  · exact globalDirectForce_mean_zero hs hsp
      (scheduleVelocity_fullTimePartial_mean_zero v (fun i => (hv i).continuous) hz) ν
  · exact scheduleVelocity_meanZero v (fun i => (hv i).continuous) hz
  · exact globalDirectForce_divergence_free hs hd ν
  · exact globalDirectForce_classicalSolution hs hsp hd (scheduleVelocity_initial v) ha ν
  · exact periodic_smooth_mixed_bounded hfs hfsp hftp
  · exact periodic_smooth_mixed_bounded hs hsp htp

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ClassicalRegularity ----
namespace OAI

/-! SheetFlows classical regularity. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem TorusC1.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g h : Space → E} (hg : TorusC1 g) (hh : TorusC1 h) : TorusC1 (g - h) := by
  refine ⟨hg.differentiable.sub hh.differentiable, ?_, ?_⟩
  · intro j
    have he (x : Space) : fderiv ℝ (g - h) x (basis j) =
        fderiv ℝ g x (basis j) - fderiv ℝ h x (basis j) := by
      rw [fderiv_sub (hg.differentiable x) (hh.differentiable x)]
      rfl
    simpa only [he] using (hg.continuous_partial j).fun_sub (hh.continuous_partial j)
  · intro x k
    simp only [Pi.sub_apply, hg.periodic, hh.periodic]

theorem cylinder_spatial_slice {E : Type*} [TopologicalSpace E]
    {g : ℝ → Space → E} {T t : ℝ}
    (hg : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T))
    (ht : t ∈ Set.Icc 0 T) : Continuous (g t) := by
  simpa only [Function.comp_def, id_eq] using hg.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, Set.mem_univ x⟩)

theorem ClassicalSolution.spatialC1 {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 ≤ t) : TorusC1 (u t) := by
  refine ⟨h.differentiable_x t ht, ?_, h.spatial_periodic_u t⟩
  intro j
  exact cylinder_spatial_slice (h.continuous_x t ht j) ⟨ht, le_refl t⟩

theorem fderiv_apply_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) (x d : Space) :
    fderiv ℝ g x d = ∑ j : Fin 3, d j • fderiv ℝ g x (basis j) := by
  have hd : d = ∑ j : Fin 3, d j • basis j := by
    ext k
    fin_cases k <;> simp [basis, Fin.sum_univ_succ]
  conv_lhs => rw [hd]
  simp only [map_sum, map_smul]

theorem kineticDensity_nonneg (a : Space) : 0 ≤ kineticDensity a := by
  unfold kineticDensity
  exact Finset.sum_nonneg (fun i _ => div_nonneg (mul_self_nonneg _) (by norm_num))

theorem kineticDensity_continuous : Continuous kineticDensity := by
  unfold kineticDensity
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).fun_mul (continuous_apply i)).div_const 2)

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.EnergyIdentities ----
namespace OAI

/-! SheetFlows energy identities. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem measurableSet_fundamentalCell : MeasurableSet fundamentalCell :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem fundamentalCell_subset_cube : fundamentalCell ⊆ Set.Icc (0 : Space) (fun _ => 10) := by
  intro x hx
  exact ⟨fun j => (hx j (Set.mem_univ j)).1, fun j => (hx j (Set.mem_univ j)).2.le⟩

theorem cylinder_uniform_bound {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → Space → E} {T : ℝ}
    (hc : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T)) :
    ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x ∈ fundamentalCell, ‖g t x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : Space))
    (b := fun _ => 10))).exists_bound_of_continuousOn
      (hc.mono (fun z hz => ⟨hz.1, Set.mem_univ z.2⟩))
  exact ⟨B, fun t ht x hx => hB (t, x) ⟨ht, fundamentalCell_subset_cube hx⟩⟩

theorem cylinder_integral_continuousOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → Space → E} {T : ℝ}
    (hc : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T)) :
    ContinuousOn (fun t => ∫ x in fundamentalCell, g t x) (Set.Icc 0 T) := by
  obtain ⟨B, hB⟩ := cylinder_uniform_bound hc
  apply continuousOn_of_dominated (bound := fun _ : Space => B)
  · intro t ht
    exact (continuous_integrableOn_cell (cylinder_spatial_slice hc ht)).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem measurableSet_fundamentalCell] with x hx
    exact hB t ht x hx
  · exact continuous_integrableOn_cell continuous_const
  · exact Filter.Eventually.of_forall (fun x =>
      hc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, Set.mem_univ x⟩))

theorem gradient_sub_at {p r : Pressure} {t : ℝ}
    (hp : Differentiable ℝ (p t)) (hr : Differentiable ℝ (r t)) :
    gradient (p-r) t = gradient p t - gradient r t := by
  funext x j
  change fderiv ℝ (p t - r t) x (basis j) = _
  rw [fderiv_sub (hp x) (hr x)]
  rfl

theorem relativeEnergy_nonneg (u v : Field) (t : ℝ) : 0 ≤ relativeEnergy u v t :=
  integral_nonneg (fun _ => kineticDensity_nonneg _)

theorem ClassicalSolution.relativeEnergy_zero {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p) :
    relativeEnergy u v 0 = 0 := by
  simp [relativeEnergy, hu.initial, hv.initial, kineticDensity]

theorem ClassicalSolution.relativeEnergy_continuousOn {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (relativeEnergy u v) (Set.Icc 0 T) :=
  cylinder_integral_continuousOn (kineticDensity_continuous.comp_continuousOn
    ((hv.continuous_u T hT).sub (hu.continuous_u T hT)))

theorem ClassicalSolution.gradient_cylinder_bound {ν : ℝ} {f u : Field} {p : Pressure}
    (hu : ClassicalSolution ν f u p) {T : ℝ} (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc 0 T, ∀ x ∈ fundamentalCell, ∀ j : Fin 3,
      ‖spatialPartial u j t x‖ ≤ B := by
  have hc : ContinuousOn (fun z : SpaceTime => fun j : Fin 3 => spatialPartial u j z.1 z.2)
      (cylinder T) := continuousOn_pi.mpr (hu.continuous_x T hT)
  obtain ⟨B, hB⟩ := cylinder_uniform_bound
    (g := fun t x => fun j : Fin 3 => spatialPartial u j t x) hc
  exact ⟨max B 0, le_max_right _ _, fun t ht x hx j =>
    (norm_le_pi_norm (fun j => spatialPartial u j t x) j).trans
      ((hB t ht x hx).trans (le_max_left _ _))⟩

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Uniqueness ----
namespace OAI

/-! SheetFlows uniqueness. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem energy_zero_of_differential_inequality {e e' : ℝ → ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn e (Set.Icc 0 T)) (he0 : e 0 = 0)
    (hn : ∀ t ∈ Set.Icc 0 T, 0 ≤ e t)
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt e (e' t) t)
    (hb : ∀ t ∈ Set.Ioo 0 T, e' t ≤ C * e t) :
    ∀ t ∈ Set.Icc 0 T, e t = 0 := by
  let φ : ℝ → ℝ := fun t => Real.exp (-C*t) * e t
  let φ' : ℝ → ℝ := fun t => Real.exp (-C*t) * (e' t - C * e t)
  have hcφ : ContinuousOn φ (Set.Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).fun_mul hc
  have hdφ (t : ℝ) (ht : t ∈ Set.Ioo 0 T) : HasDerivAt φ (φ' t) t := by
    have h : HasDerivAt φ
        (Real.exp (-C*t) * (-C) * e t + Real.exp (-C*t) * e' t) t := by
      simpa only [mul_one, id_eq, φ] using
        ((((hasDerivAt_id t).const_mul (-C)).exp).fun_mul (hd t ht))
    have heq : Real.exp (-C*t) * (-C) * e t + Real.exp (-C*t) * e' t = φ' t := by
      dsimp [φ']
      ring
    exact heq ▸ h
  have hbφ (t : ℝ) (ht : t ∈ Set.Ioo 0 T) : φ' t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hb t ht))
  have ha : AntitoneOn φ (Set.Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcφ
      (fun t ht => (hdφ t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
      (fun t ht => hbφ t (by simpa only [interior_Icc] using ht))
  intro t ht
  have hl := ha ⟨le_refl 0, hT⟩ ht ht.1
  change Real.exp (-C*t) * e t ≤ Real.exp (-C*0) * e 0 at hl
  rw [he0, mul_zero] at hl
  exact le_antisymm (le_of_mul_le_mul_left (by simpa only [mul_zero] using hl)
    (Real.exp_pos (-C*t))) (hn t ht)

theorem ClassicalSolution.relativeEnergy_eq_zero {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) : relativeEnergy u v t = 0 := by
  obtain ⟨B, hB, hgrad⟩ := hu.gradient_cylinder_bound ht
  apply energy_zero_of_differential_inequality (T := t) (C := 6*B) ht
    (hu.relativeEnergy_continuousOn hv ht) (hu.relativeEnergy_zero hv)
    (fun s _ => relativeEnergy_nonneg u v s)
    (fun s hs => hu.relativeEnergy_hasDerivAt hv hs.1)
    (fun s hs => hu.relativeEnergy_derivative_bound hv hν hs.1.le hB
      (hgrad s ⟨hs.1.le, hs.2.le⟩)) t ⟨ht, le_refl t⟩

theorem cube_subset_closure_interior :
    Set.Icc (0 : Space) (fun _ => 10) ⊆ closure (interior (Set.Icc (0 : Space) (fun _ => 10))) := by
  have hp : Set.Icc (0 : Space) (fun _ => 10) =
      Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (0 : ℝ) 10) := by
    ext x
    simp [Set.mem_Icc, Pi.le_def]
  rw [hp, interior_pi_set (Set.toFinite _), closure_pi_set]
  simp only [interior_Icc, closure_Ioo (by norm_num : (0:ℝ) ≠ 10)]
  exact Set.Subset.rfl

theorem kineticDensity_eq_zero_iff (a : Space) : kineticDensity a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    ext j
    have hj : a j * a j / 2 ≤ kineticDensity a :=
      Finset.single_le_sum (f := fun i => a i * a i / 2)
        (fun i _ => div_nonneg (mul_self_nonneg _) (by norm_num))
        (Finset.mem_univ j)
    rw [ha] at hj
    change a j = 0
    nlinarith [sq_nonneg (a j)]
  · rintro rfl
    simp [kineticDensity]

theorem periodic_energy_zero_implies_zero {w : Space → Space}
    (hc : Continuous w) (hp : ∀ x k, w (x+deck k) = w x)
    (he : (∫ x in fundamentalCell, kineticDensity (w x)) = 0) : ∀ x, w x = 0 := by
  have hcont := kineticDensity_continuous.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => kineticDensity_nonneg (w x))
    (continuous_integrableOn_cell hcont)).mp he
  rw [Measure.restrict_congr_set cell_ae_eq_Icc] at hae
  have hon := Measure.eqOn_of_ae_eq hae hcont.continuousOn continuousOn_const
    cube_subset_closure_interior
  intro x
  have hz : kineticDensity (w (wrapSpace x)) = 0 := hon (wrapSpace_mem x)
  have hper := hp (wrapSpace x) (fun j => ⌊x j / 10⌋)
  rw [wrapSpace_add_deck] at hper
  exact (kineticDensity_eq_zero_iff (w x)).mp (hper ▸ hz)

theorem ClassicalSolution.velocity_unique {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : Space) : v t x = u t x := by
  have hw := (hv.spatialC1 ht).sub (hu.spatialC1 ht)
  have he := periodic_energy_zero_implies_zero hw.differentiable.continuous hw.periodic
    (hu.relativeEnergy_eq_zero hv hν ht) x
  exact sub_eq_zero.mp he

theorem volume_fundamentalCell : volume fundamentalCell = 1000 := by
  norm_num [fundamentalCell, volume_pi, Measure.pi_pi]

theorem ClassicalSolution.pressure_gradient_unique {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : Space) : gradient p t x = gradient r t x := by
  have hvel (s : ℝ) (hs : 0 ≤ s) : v s = u s :=
    funext (fun y => hu.velocity_unique hv hν hs y)
  have htime : timePartial v t x = timePartial u t x :=
    derivWithin_congr (fun s hs => congrFun (hvel s hs) x) (congrFun (hvel t ht) x)
  have hadv : advection v t x = advection u t x := by simp only [advection, hvel t ht]
  have hlap : laplacian v t x = laplacian u t x := by
    unfold laplacian spatialPartial
    rw [hvel t ht]
  have hve := hv.equation t ht x
  rw [htime, hadv, hlap] at hve
  have hue := hu.equation t ht x
  have hneg := add_right_cancel (add_right_cancel (hve.symm.trans hue))
  exact neg_injective hneg

theorem ClassicalSolution.pressure_unique {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : Space) : p t x = r t x := by
  let q : Space → ℝ := p t - r t
  have hq : Differentiable ℝ q := (hv.differentiable_p t ht).sub (hu.differentiable_p t ht)
  have hd (y : Space) : fderiv ℝ q y = 0 := by
    have hj (j : Fin 3) : fderiv ℝ q y (basis j) = 0 := by
      change gradient (p-r) t y j = 0
      rw [gradient_sub_at (hv.differentiable_p t ht) (hu.differentiable_p t ht)]
      simp only [Pi.sub_apply, hu.pressure_gradient_unique hv hν ht y, sub_self]
    ext d
    rw [fderiv_apply_eq_sum]
    simp only [hj, smul_zero, Finset.sum_const_zero, zero_apply]
  have hconst (y : Space) : q y = q 0 := is_const_of_fderiv_eq_zero hq hd y 0
  have hint : (∫ y in fundamentalCell, q y) = 0 := by
    change (∫ y in fundamentalCell, p t y-r t y) = 0
    rw [integral_sub (continuous_integrableOn_cell (hv.differentiable_p t ht).continuous)
      (continuous_integrableOn_cell (hu.differentiable_p t ht).continuous),
      hv.pressure_mean_zero t ht, hu.pressure_mean_zero t ht, sub_self]
  simp only [hconst] at hint
  have h0 : q 0 = 0 := by
    simpa [measureReal_def, volume_fundamentalCell] using hint
  exact sub_eq_zero.mp ((hconst x).trans h0)

theorem ClassicalSolution.unique {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    v t x = u t x ∧ p t x = r t x :=
  ⟨hu.velocity_unique hv hν ht x, hu.pressure_unique hv hν ht x⟩

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.RectangleGeometry ----
namespace OAI

/-! SheetFlows rectangle geometry. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

namespace Rectangle

theorem upper_mem (R : Rectangle) : (fun j => (R.upper j : ℝ)) ∈ R.carrier := by
  intro j
  have h : (R.lower j : ℝ) < (R.upper j : ℝ) := by exact_mod_cast R.positive j
  exact ⟨h.le, le_rfl⟩

theorem offset_bound (R : Rectangle) (hR : R.inCodingSquare)
    {y : Plane} (hy : y ∈ R.carrier) (j : Fin 2) :
    |y j - R.center j| ≤ 1 / 2 :=
  ((R.mem_iff_abs y).mp hy j).trans (R.halfWidth_le_half hR j)

end Rectangle

theorem diagonalMap_upper (P Q : Rectangle) (r : Fin 2 → ℚ)
    (hr : ∀ j, 0 < r j)
    (himage : diagonalMap P Q r '' P.carrier = Q.carrier) :
    diagonalMap P Q r (fun j => (P.upper j : ℝ)) = fun j => (Q.upper j : ℝ) := by
  have hmax : ∀ y ∈ P.carrier, ∀ j,
      diagonalMap P Q r y j ≤ diagonalMap P Q r (fun k => (P.upper k : ℝ)) j := by
    intro y hy j
    have hj : (0 : ℝ) ≤ (r j : ℝ) := by exact_mod_cast (hr j).le
    dsimp [diagonalMap]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (hy j).2 _) hj)
  have hup : diagonalMap P Q r (fun j => (P.upper j : ℝ)) ∈ Q.carrier := by
    rw [← himage]
    exact ⟨_, P.upper_mem, rfl⟩
  obtain ⟨y, hy, he⟩ : ∃ y ∈ P.carrier,
      diagonalMap P Q r y = (fun j => (Q.upper j : ℝ)) := by
    have h := Q.upper_mem
    rw [← himage] at h
    exact h
  funext j
  apply le_antisymm (hup j).2
  simpa only [he] using hmax y hy j

theorem SheetData.ratio_mul_halfWidth {N : ℕ} (D : SheetData N)
    (i : Fin N) (j : Fin 2) :
    (D.ratio i j : ℝ) * (D.source i).halfWidth j = (D.target i).halfWidth j := by
  have h := congrFun (diagonalMap_upper (D.source i) (D.target i) (D.ratio i)
    (D.ratio_positive i) (D.image_eq i)) j
  dsimp [diagonalMap, Rectangle.center] at h
  dsimp [Rectangle.halfWidth]
  linarith

theorem SheetData.scaled_offset_bound {N : ℕ} (D : SheetData N)
    (i : Fin N) {y : Plane} (hy : y ∈ (D.source i).carrier) (j : Fin 2) :
    |(D.ratio i j : ℝ) * (y j - (D.source i).center j)| ≤ 1 / 2 := by
  have hr : (0 : ℝ) < (D.ratio i j : ℝ) := by exact_mod_cast D.ratio_positive i j
  rw [abs_mul, abs_of_pos hr]
  calc
    (D.ratio i j : ℝ) * |y j - (D.source i).center j| ≤
        (D.ratio i j : ℝ) * (D.source i).halfWidth j :=
      mul_le_mul_of_nonneg_left (((D.source i).mem_iff_abs y).mp hy j) hr.le
    _ = (D.target i).halfWidth j := D.ratio_mul_halfWidth i j
    _ ≤ 1 / 2 := (D.target i).halfWidth_le_half (D.target_inside i) j

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Trajectories ----
namespace OAI

/-! SheetFlows trajectories. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem launchPath_active {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    (i : Fin m) {t : ℝ} (ht : t ∈ Set.Icc (slotLeft m i) (slotRight m i)) :
    launchPath v a t = stageState v a i.val +
      pulseClock (slotLeft m i) (slotRight m i) t • stageIncrement v a i := by
  classical
  have he (j : Fin m) :
      pulseClock (slotLeft m j) (slotRight m j) t • stageIncrement v a j =
      (if j.val < i.val then stageIncrement v a j else 0) +
      (if j = i then
        pulseClock (slotLeft m i) (slotRight m i) t • stageIncrement v a i else 0) := by
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hjt := (slot_ordered hji).le.trans ht.1
      rw [pulseClock_one (slot_bounds j).2.1 hjt]
      simp [hji, hji.ne]
    · simp
    · have hjt := ht.2.trans (slot_ordered hij).le
      rw [pulseClock_zero (slot_bounds j).2.1 hjt]
      simp [not_lt_of_gt hij, hij.ne']
  unfold launchPath
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => he j)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← add_assoc, ← stageState_eq_sum v a i.isLt.le]

theorem launchPath_hasDerivAt {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, StraightInvariant (v i)) (a : Space) (t : ℝ) :
    HasDerivAt (launchPath v a)
      (∑ i : Fin m, localPulse (slotLeft m i) (slotRight m i) t • v i (launchPath v a t)) t := by
  have h : HasDerivAt (launchPath v a)
      (∑ i, localPulse (slotLeft m i) (slotRight m i) t • stageIncrement v a i) t := by
    convert (hasDerivAt_const t a).fun_add
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        (((pulseClock_contDiff (slotLeft m i) (slotRight m i)).differentiable (by simp)
          t).hasDerivAt.smul_const (stageIncrement v a i)))) using 1 <;>
      first | rfl | simp only [zero_add, localPulse]
  suffices he : (∑ i : Fin m, localPulse (slotLeft m i) (slotRight m i) t • v i (launchPath v a t)) =
      (∑ i : Fin m, localPulse (slotLeft m i) (slotRight m i) t • stageIncrement v a i) by
    rw [he]
    exact h
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : localPulse (slotLeft m i) (slotRight m i) t = 0
  · rw [hi, zero_smul, zero_smul]
  · have hleft : slotLeft m i < t := by
      by_contra h
      exact hi (localPulse_zero_left (slot_bounds i).2.1 (le_of_not_gt h))
    have hright : t < slotRight m i := by
      by_contra h
      exact hi (localPulse_zero_right (slot_bounds i).2.1 (le_of_not_gt h))
    rw [launchPath_active v a i ⟨hleft.le, hright.le⟩]
    exact congrArg (localPulse (slotLeft m i) (slotRight m i) t • ·)
      (hv i (stageState v a i.val) _)

theorem launchPath_periodic_ode {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, StraightInvariant (v i)) (a : Space) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    HasDerivAt (launchPath v a) (scheduleVelocity v t (launchPath v a t)) t := by
  have he (i : Fin m) : scheduledPulse m i t = localPulse (slotLeft m i) (slotRight m i) t :=
    periodicPulse_on_chart (slot_bounds i).2.1 (by linarith [(slot_bounds i).1])
      (by linarith [(slot_bounds i).2.2]) ht
  simpa only [scheduleVelocity, he] using launchPath_hasDerivAt v hv a t

theorem repeatedPath_on_Ico {m : ℕ} (v : Fin m → Space → Space) (a : Space)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    repeatedPath v a t = launchPath v (periodState v a n) (t - n) := by
  rw [repeatedPath, Nat.floor_eq_on_Ico n t ht]

theorem repeatedPath_at_nat {m : ℕ} (v : Fin m → Space → Space) (a : Space) (n : ℕ) :
    repeatedPath v a (n : ℝ) = periodState v a n :=
  repeatedPath_on_collar v a n (by simp)

theorem repeatedPath_hasDerivAt_nat {m : ℕ} (v : Fin m → Space → Space) (a : Space) (n : ℕ) :
    HasDerivAt (repeatedPath v a) 0 (n : ℝ) := by
  apply (hasDerivAt_const (n : ℝ) (periodState v a n)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show (n : ℝ) ∈ Set.Ioo ((n : ℝ) - 1/4) (n + 1/4) by
    constructor <;> linarith)] with t ht
  exact repeatedPath_on_collar v a n (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)

theorem scheduleVelocity_at_nat {m : ℕ} (v : Fin m → Space → Space) (n : ℕ) (x : Space) :
    scheduleVelocity v (n : ℝ) x = 0 := by
  obtain ⟨ε, hε, hz⟩ := scheduleVelocity_integerCollars v
  apply hz (n : ℤ)
  simpa using hε

theorem repeatedPath_hasDerivAt {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, StraightInvariant (v i)) (a : Space) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (repeatedPath v a) (scheduleVelocity v t (repeatedPath v a t)) t := by
  let n : ℕ := ⌊t⌋₊
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht
  have htn : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
  by_cases hnat : t = (n : ℝ)
  · rw [hnat, scheduleVelocity_at_nat]
    exact repeatedPath_hasDerivAt_nat v a n
  · have hnt' : (n : ℝ) < t := lt_of_le_of_ne hnt (Ne.symm hnat)
    have he : repeatedPath v a =ᶠ[𝓝 t]
        (fun s => launchPath v (periodState v a n) (s - n)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (n : ℝ) ((n : ℝ)+1) from
        ⟨hnt', htn⟩)] with s hs
      exact repeatedPath_on_Ico v a n ⟨hs.1.le, hs.2⟩
    have hp (x : Space) : scheduleVelocity v (t - n) x = scheduleVelocity v t x := by
      have hper : Function.Periodic (fun s => scheduleVelocity v s x) 1 :=
        fun s => scheduleVelocity_onePeriodic v s x
      simpa only [mul_one] using hper.sub_nat_mul_eq (x := t) n
    have hD := (launchPath_periodic_ode v hv (periodState v a n)
      (show t - (n : ℝ) ∈ Set.Icc 0 1 from ⟨sub_nonneg.mpr hnt, by linarith⟩)).scomp t
      ((hasDerivAt_id t).sub_const (n : ℝ))
    simp only [one_smul, hp] at hD
    exact hD.congr_of_eventuallyEq he

theorem schedule_material_flow {m : ℕ} (v : Fin m → Space → Space)
    (hv : ∀ i, StraightInvariant (v i)) :
    MaterialFlow (scheduleVelocity v) (fun t a => repeatedPath v a t) ∧
      (∀ a, repeatedPath v a 1 = stageState v a m) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro a
    simpa only [Nat.cast_zero, periodState] using repeatedPath_at_nat v a 0
  · intro a t ht
    exact (repeatedPath_hasDerivAt v hv a ht).continuousAt.continuousWithinAt
  · intro a t ht
    exact (repeatedPath_hasDerivAt v hv a ht).hasDerivWithinAt
  · intro a
    simpa only [Nat.cast_one, periodState] using repeatedPath_at_nat v a 1

end Solenoidal

end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Pulses ----
namespace OAI

/-! SheetFlows pulses. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem sheet_theorem_empty (D : SheetData 0) (ν : ℝ) (hν : 0 < ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧
      Smooth f ∧ Smooth u ∧ Effective f ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (fun _ _ => 0) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin 0, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      EffectiveBounds f ∧ EffectiveBounds u ∧ (0 = 0 → f = 0 ∧ u = 0) := by
  refine ⟨0, 0, fun _ a => a, zero_spatially_periodic, zero_spatially_periodic,
    zero_smooth, zero_smooth, zero_effective, zero_mean_zero, zero_divergence_free,
    zero_one_periodic, zero_classical_solution ν, ?_, zero_material_flow, ?_,
    zero_integer_collars, ?_, zero_effective_bounds, zero_effective_bounds, fun _ => ⟨rfl, rfl⟩⟩
  · intro v p hv t ht x
    exact (zero_classical_solution ν).unique hv hν.le ht x
  · intro i
    exact Fin.elim0 i
  · intro t x
    simp

namespace StationaryPulse

end StationaryPulse

theorem runProgram_fixed (P : List StationaryPulse) (a : Space)
    (h : ∀ p ∈ P, p.field a = 0) : runProgram P a = a := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rw [runProgram_cons]
    have hp : p.apply a = a := by simp [StationaryPulse.apply, h p (by simp)]
    rw [hp]
    exact ih (fun q hq => h q (by simp [hq]))

theorem stageState_list_eq (P : List StationaryPulse) (a : Space) :
    stageState (fun i : Fin P.length => (P.get i).field) a P.length = runProgram P a := by
  have h (n : ℕ) (hn : n ≤ P.length) :
      stageState (fun i : Fin P.length => (P.get i).field) a n = runProgram (P.take n) a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn' : n < P.length := Nat.lt_of_succ_le hn
      rw [stageState, stageField_fin _ ⟨n, hn'⟩, ih (Nat.le_of_succ_le hn)]
      rw [List.take_succ_eq_append_getElem hn', runProgram_append]
      rfl
  simpa using h P.length (le_refl _)

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Localization ----
namespace OAI

/-! SheetFlows localization. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem Rectangle.disjoint_of_separated {N : ℕ} {R : Fin N → Rectangle}
    (h : SeparatelySeparated R) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (R i).carrier (R j).carrier := by
  obtain ⟨δ,hδ,hh⟩ := h i j hij
  rw [Set.disjoint_left]
  intro y hi hj
  have hn := hh y hi y hj
  simp only [sub_self, norm_zero] at hn
  exact (not_le_of_gt hδ) hn

theorem Rectangle.exists_coordinate_gap {P Q : Rectangle} (h : Disjoint P.carrier Q.carrier) :
    ∃ k, P.upper k < Q.lower k ∨ Q.upper k < P.lower k := by
  by_contra hn
  push Not at hn
  have hmin (k : Fin 2) : max (P.lower k) (Q.lower k) ≤ min (P.upper k) (Q.upper k) := by
    rcases hn k with ⟨h₁,h₂⟩
    exact max_le (le_min (P.positive k).le h₂) (le_min h₁ (Q.positive k).le)
  have hy : (fun k => ((max (P.lower k) (Q.lower k) : ℚ) : ℝ)) ∈ P.carrier ∩ Q.carrier := by
    constructor
    · intro k
      dsimp only
      constructor
      · exact_mod_cast le_max_left (P.lower k) (Q.lower k)
      · exact_mod_cast (hmin k).trans (min_le_left _ _)
    · intro k
      dsimp only
      constructor
      · exact_mod_cast le_max_right (P.lower k) (Q.lower k)
      · exact_mod_cast (hmin k).trans (min_le_right _ _)
  exact Set.disjoint_left.mp h hy.1 hy.2

theorem Rectangle.collar_of_coordinate_gap {P Q : Rectangle} {d : ℝ} {k : Fin 2}
    (h : (P.upper k : ℝ) + d ≤ Q.lower k ∨ (Q.upper k : ℝ) + d ≤ P.lower k)
    {y : Plane} (hy : y ∈ Q.carrier) : P.halfWidth k + d ≤ |y k - P.center k| := by
  rcases h with h | h
  · apply le_abs.mpr
    left
    have hyk := (hy k).1
    dsimp [Rectangle.halfWidth, Rectangle.center]
    linarith
  · apply le_abs.mpr
    right
    have hyk := (hy k).2
    dsimp [Rectangle.halfWidth, Rectangle.center]
    linarith

theorem Rectangle.exists_rational_collar {N : ℕ} {R : Fin N → Rectangle}
    (h : SeparatelySeparated R) :
    ∃ d : ℚ, 0 < d ∧ d ≤ 1/10 ∧ Rectangle.CollarSeparated R (d : ℝ) := by
  classical
  have hpair (i j : Fin N) : ∃ d : ℚ, 0 < d ∧
      (i ≠ j → ∀ y ∈ (R j).carrier,
        ∃ k, (R i).halfWidth k + (d : ℝ) ≤ |y k - (R i).center k|) := by
    by_cases hij : i = j
    · exact ⟨1, by norm_num, fun hc => (hc hij).elim⟩
    obtain ⟨k,hk⟩ := Rectangle.exists_coordinate_gap (Rectangle.disjoint_of_separated h hij)
    rcases hk with hk | hk
    · refine ⟨(R j).lower k - (R i).upper k, sub_pos.mpr hk, fun _ y hy => ⟨k, ?_⟩⟩
      apply Rectangle.collar_of_coordinate_gap (Or.inl ?_) hy
      push_cast
      ring_nf
      exact le_refl _
    · refine ⟨(R i).lower k - (R j).upper k, sub_pos.mpr hk, fun _ y hy => ⟨k, ?_⟩⟩
      apply Rectangle.collar_of_coordinate_gap (Or.inr ?_) hy
      push_cast
      ring_nf
      exact le_refl _
  choose ds hpos hg using hpair
  let S : Finset ℚ := insert (1/10) (Finset.univ.image (fun ij : Fin N × Fin N => ds ij.1 ij.2))
  have hS : S.Nonempty := ⟨1/10, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, S.min'_le _ (Finset.mem_insert_self _ _), ?_⟩
  · rw [Finset.lt_min'_iff]
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · norm_num
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp hq
    exact hpos i j
  · intro i j hij y hy
    obtain ⟨k,hk⟩ := hg i j hij y hy
    refine ⟨k, le_trans ?_ hk⟩
    apply add_le_add (le_refl _)
    exact_mod_cast S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ (i,j))))

theorem Rectangle.CollarSeparated.mono {N : ℕ} {R : Fin N → Rectangle} {d e : ℝ}
    (h : Rectangle.CollarSeparated R d) (he : e ≤ d) : Rectangle.CollarSeparated R e := by
  intro i j hij y hy
  obtain ⟨k,hk⟩ := h i j hij y hy
  exact ⟨k, (add_le_add (le_refl _) he).trans hk⟩

theorem SheetData.exists_rational_collar {N : ℕ} (D : SheetData N) :
    ∃ d : ℚ, 0 < d ∧ d ≤ 1/10 ∧ Rectangle.CollarSeparated D.source (d : ℝ) ∧
      Rectangle.CollarSeparated D.target (d : ℝ) := by
  obtain ⟨a,ha,ha',hs⟩ := Rectangle.exists_rational_collar D.source_separated
  obtain ⟨b,hb,_,ht⟩ := Rectangle.exists_rational_collar D.target_separated
  refine ⟨min a b, lt_min ha hb, (min_le_left _ _).trans ha', hs.mono ?_, ht.mono ?_⟩
  · exact_mod_cast min_le_left a b
  · exact_mod_cast min_le_right a b

theorem Rectangle.point_bounds (R : Rectangle) (hR : R.inCodingSquare)
    {y : Plane} (hy : y ∈ R.carrier) (j : Fin 2) : 2 ≤ y j ∧ y j ≤ 3 := by
  have hl : (2:ℝ) ≤ R.lower j := by exact_mod_cast (hR j).1
  have hu : (R.upper j:ℝ) ≤ 3 := by exact_mod_cast (hR j).2
  exact ⟨hl.trans (hy j).1, (hy j).2.trans hu⟩

variable (d : Collar)

theorem verticalPulse_field (R : Rectangle) (hR : R.inCodingSquare) (s : ℝ) (x : Space) :
    (verticalPulse d R hR s).field x =
      (Cprofile (R.halfWidth 0) d.size (R.center 0+s) (x 0) *
        (Cprofile (R.halfWidth 1) d.size (R.center 1) (x 1) -
          Cprofile (R.halfWidth 1) d.size (R.center 1+4) (x 1))) • basis 2 := by
  simp [verticalPulse, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem rect_support_chart (R : Rectangle) (hR : R.inCodingSquare) (j : Fin 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) :
    R.halfWidth j + d.size ≤ R.center j + s ∧
      R.center j + s + (R.halfWidth j + d.size) ≤ 10 := by
  have hw := R.halfWidth_le_half hR j
  have hc := R.center_bounds hR j
  constructor <;> linarith [d.small, hs.1, hs.2]

theorem correction_off (R : Rectangle) (hR : R.inCodingSquare)
    {y : ℝ} (hy : y ∈ Set.Icc 2 3) :
    Cprofile (R.halfWidth 1) d.size (R.center 1+4) y = 0 := by
  have hc := rect_support_chart d R hR 1 (s := 4) (by norm_num)
  apply Cprofile_zero_on_chart d.positive hc.1 hc.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
  apply le_abs.mpr
  right
  linarith [R.halfWidth_le_half hR 1, (R.center_bounds hR 1).1, d.small, hy.2]

theorem rect_profile_one (R : Rectangle) (hR : R.inCodingSquare) (j : Fin 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) {y : Plane} (hy : y ∈ R.carrier) :
    Cprofile (R.halfWidth j) d.size (R.center j+s) (y j+s) = 1 := by
  have hc := rect_support_chart d R hR j hs
  apply Cprofile_one d.positive hc.1 hc.2
  · have hb := R.point_bounds hR hy j
    constructor <;> linarith [hs.1, hs.2, hb.1, hb.2]
  · have hb := (R.mem_iff_abs y).mp hy j
    have he : y j + s - (R.center j+s) = y j - R.center j := by ring
    rw [he]
    linarith [d.positive]

theorem verticalPulse_own (R : Rectangle) (hR : R.inCodingSquare)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) {y : Plane} (hy : y ∈ R.carrier) (z : ℝ) :
    (verticalPulse d R hR s).field (lifted s z y) = basis 2 := by
  rw [verticalPulse_field]
  have h₀ := rect_profile_one d R hR 0 hs hy
  have h₁ := rect_profile_one d R hR 1 (s := 0) (by norm_num) hy
  simp only [add_zero] at h₁
  simp only [lifted, Matrix.cons_val_zero, Matrix.cons_val_one, h₀, h₁,
    correction_off d R hR (R.point_bounds hR hy 1), sub_zero, mul_one, one_smul]

theorem rect_profile_gap_zero (P Q : Rectangle) (hP : P.inCodingSquare)
    (hQ : Q.inCodingSquare) (k : Fin 2) {s : ℝ} (hs : s ∈ Set.Icc 0 4)
    {y : Plane} (hy : y ∈ Q.carrier)
    (hgap : P.halfWidth k + d.size ≤ |y k-P.center k|) :
    Cprofile (P.halfWidth k) d.size (P.center k+s) (y k+s) = 0 := by
  have hc := rect_support_chart d P hP k hs
  apply Cprofile_zero_on_chart d.positive hc.1 hc.2
  · have hb := Q.point_bounds hQ hy k
    constructor <;> linarith [hs.1, hs.2, hb.1, hb.2]
  · have he : y k+s-(P.center k+s) = y k-P.center k := by ring
    rw [he]
    exact hgap

theorem verticalPulse_off_same {N : ℕ} (R : Fin N → Rectangle)
    (hR : ∀ i, (R i).inCodingSquare) (hsep : Rectangle.CollarSeparated R d.size)
    {i j : Fin N} (hij : i ≠ j) {s : ℝ} (hs : s ∈ Set.Icc 0 4)
    {y : Plane} (hy : y ∈ (R j).carrier) (z : ℝ) :
    (verticalPulse d (R i) (hR i) s).field (lifted s z y) = 0 := by
  obtain ⟨k,hk⟩ := hsep i j hij y hy
  have hc := correction_off d (R i) (hR i) ((R j).point_bounds (hR j) hy 1)
  rw [verticalPulse_field]
  fin_cases k
  · have hz := rect_profile_gap_zero d (R i) (R j) (hR i) (hR j) 0 hs hy hk
    simp [lifted, hz]
  · have hz := rect_profile_gap_zero d (R i) (R j) (hR i) (hR j) 1 (s := 0) (by norm_num) hy hk
    simp only [add_zero] at hz
    simp [lifted, hc, hz]

theorem horizontalPulse_field (j : Fin 2) (x : Space) :
    (horizontalPulse d j).field x =
      (Cprofile 0 d.size 5 (x 2) - Cprofile 0 d.size 8 (x 2)) • basis j.castSucc := by
  simp [horizontalPulse, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem horizontalPulse_off (j : Fin 2) {x : Space} (hx : x 2 = 2) :
    (horizontalPulse d j).field x = 0 := by
  have h₅ : Cprofile 0 d.size 5 2 = 0 := by
    apply Cprofile_zero_on_chart d.positive <;> norm_num <;> linarith [d.small, d.positive]
  have h₈ : Cprofile 0 d.size 8 2 = 0 := by
    apply Cprofile_zero_on_chart d.positive <;> norm_num <;> linarith [d.small, d.positive]
  simp only [horizontalPulse_field, hx, h₅, h₈, sub_self, zero_smul]

theorem travelProgram_off (δ : Plane) (x : Space) (hx : x 2 = 2) :
    runProgram (travelProgram d δ) x = x := by
  apply runProgram_fixed
  intro p hp
  simp only [travelProgram, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp [horizontalPulse_off d _ hx]

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ShearCore ----
namespace OAI

/-! SheetFlows shear core. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

variable (d : Collar)

theorem coreLift0_field (x : Space) : (coreLift0 d).field x =
    (Dprofile (1/2) d.size 5 (x 0) * Cprofile (1/2) d.size 6 (x 1)) • basis 2 := by
  simp [coreLift0, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem coreLift1_field (x : Space) : (coreLift1 d).field x =
    (Cprofile (1/2) d.size 5 (x 0) * Dprofile (1/2) d.size 6 (x 1)) • basis 2 := by
  simp [coreLift1, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem coreHorizontal_field (j : Fin 2) (x : Space) : (coreHorizontal d j).field x =
    Dprofile (1/2) d.size 5 (x 2) • basis j.castSucc := by
  simp [coreHorizontal, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem coreC_one {c r : ℝ} (hc : c ∈ Set.Icc 5 6) (hr : |r| ≤ 1/2) :
    Cprofile (1/2) d.size c (c+r) = 1 := by
  apply Cprofile_one d.positive
  · linarith [d.small, hc.1]
  · linarith [d.small, hc.2]
  · have hh := abs_le.mp hr
    constructor <;> linarith [hc.1, hc.2, hh.1, hh.2]
  · rw [add_sub_cancel_left]
    linarith [d.positive]

theorem coreD_linear {c r : ℝ} (hc : c ∈ Set.Icc 5 6) (hr : |r| ≤ 1/2) :
    Dprofile (1/2) d.size c (c+r) = r := by
  have hl : 1/2 + d.size ≤ c := by linarith [d.small, hc.1]
  have hu : c + (1/2+d.size) ≤ 10 := by linarith [d.small, hc.2]
  have hp : c+r ∈ Set.Icc 0 10 := by
    have hh := abs_le.mp hr
    constructor <;> linarith [hc.1, hc.2, hh.1, hh.2]
  have hb : |c+r-c| ≤ 1/2+d.size/2 := by
    rw [add_sub_cancel_left]
    linarith [d.positive]
  simpa only [add_sub_cancel_left] using Dprofile_linear d.positive hl hu hp hb

theorem coreC_off {c y : ℝ} (hc : c ∈ Set.Icc 5 6) (hy : y ∈ Set.Icc 2 3) :
    Cprofile (1/2) d.size c y = 0 := by
  apply Cprofile_zero_on_chart d.positive
  · linarith [d.small, hc.1]
  · linarith [d.small, hc.2]
  · constructor <;> linarith [hy.1, hy.2]
  · apply le_abs.mpr (Or.inr ?_)
    linarith [d.small, hc.1, hy.2]

theorem coreD_off {c y : ℝ} (hc : c ∈ Set.Icc 5 6) (hy : y ∈ Set.Icc 2 3) :
    Dprofile (1/2) d.size c y = 0 := by
  apply Dprofile_zero_on_chart d.positive
  · linarith [d.small, hc.1]
  · linarith [d.small, hc.2]
  · constructor <;> linarith [hy.1, hy.2]
  · apply le_abs.mpr (Or.inr ?_)
    linarith [d.small, hc.1, hy.2]

theorem coreLift0_on {r s : ℝ} (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (z : ℝ) :
    (coreLift0 d).field ![5+r,6+s,z] = r • basis 2 := by
  simp only [coreLift0_field, Matrix.cons_val_zero, Matrix.cons_val_one,
    coreD_linear d (by norm_num : (5:ℝ) ∈ Set.Icc 5 6) hr,
    coreC_one d (by norm_num : (6:ℝ) ∈ Set.Icc 5 6) hs, mul_one]

theorem coreLift1_on {r s : ℝ} (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (z : ℝ) :
    (coreLift1 d).field ![5+r,6+s,z] = s • basis 2 := by
  simp only [coreLift1_field, Matrix.cons_val_zero, Matrix.cons_val_one,
    coreC_one d (by norm_num : (5:ℝ) ∈ Set.Icc 5 6) hr,
    coreD_linear d (by norm_num : (6:ℝ) ∈ Set.Icc 5 6) hs, one_mul]

theorem coreLift0_off (x : Space) (hx : x 1 ∈ Set.Icc 2 3) : (coreLift0 d).field x = 0 := by
  rw [coreLift0_field, coreC_off d (by norm_num : (6:ℝ) ∈ Set.Icc 5 6) hx, mul_zero, zero_smul]

theorem coreLift1_off (x : Space) (hx : x 1 ∈ Set.Icc 2 3) : (coreLift1 d).field x = 0 := by
  rw [coreLift1_field, coreD_off d (by norm_num : (6:ℝ) ∈ Set.Icc 5 6) hx, mul_zero, zero_smul]

theorem coreHorizontal_on (j : Fin 2) (x y : ℝ) {r : ℝ} (hr : |r| ≤ 1/2) :
    (coreHorizontal d j).field ![x,y,5+r] = r • basis j.castSucc := by
  rw [coreHorizontal_field]
  change Dprofile (1/2) d.size 5 (5+r) • basis j.castSucc = _
  rw [coreD_linear d (by norm_num : (5:ℝ) ∈ Set.Icc 5 6) hr]

theorem coreHorizontal_off (j : Fin 2) (x : Space) (hx : x 2 = 2) :
    (coreHorizontal d j).field x = 0 := by
  rw [coreHorizontal_field, hx,
    coreD_off d (by norm_num : (5:ℝ) ∈ Set.Icc 5 6) (by norm_num : (2:ℝ) ∈ Set.Icc 2 3), zero_smul]

theorem tripleProgram0_on {l r s : ℝ} (hl : l ≠ 0)
    (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (hlr : |l*r| ≤ 1/2) :
    runProgram (tripleProgram0 d l) ![5+r,6+s,5] = ![5+l*r,6+s,5] := by
  have h₁ : (coreLift0 d).apply ![5+r,6+s,5] = ![5+r,6+s,5+r] := by
    rw [StationaryPulse.apply, coreLift0_on d hr hs]
    ext i; fin_cases i <;> simp [basis]
  have h₂ : ((coreHorizontal d 0).scale (l-1)).apply ![5+r,6+s,5+r] =
      ![5+l*r,6+s,5+r] := by
    rw [StationaryPulse.apply, StationaryPulse.scale_field, coreHorizontal_on d 0 _ _ hr]
    ext i; fin_cases i <;> simp [basis]
    ring
  have h₃ : ((coreLift0 d).scale (-1/l)).apply ![5+l*r,6+s,5+r] = ![5+l*r,6+s,5] := by
    rw [StationaryPulse.apply, StationaryPulse.scale_field, coreLift0_on d hlr hs]
    ext i; fin_cases i <;> simp [basis]
    field_simp [hl]
    ring
  change ((coreLift0 d).scale (-1/l)).apply
    (((coreHorizontal d 0).scale (l-1)).apply ((coreLift0 d).apply ![5+r,6+s,5])) = _
  rw [h₁, h₂, h₃]

theorem tripleProgram1_on {l r s : ℝ} (hl : l ≠ 0)
    (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (hls : |l*s| ≤ 1/2) :
    runProgram (tripleProgram1 d l) ![5+r,6+s,5] = ![5+r,6+l*s,5] := by
  have h₁ : (coreLift1 d).apply ![5+r,6+s,5] = ![5+r,6+s,5+s] := by
    rw [StationaryPulse.apply, coreLift1_on d hr hs]
    ext i; fin_cases i <;> simp [basis]
  have h₂ : ((coreHorizontal d 1).scale (l-1)).apply ![5+r,6+s,5+s] =
      ![5+r,6+l*s,5+s] := by
    rw [StationaryPulse.apply, StationaryPulse.scale_field, coreHorizontal_on d 1 _ _ hs]
    ext i; fin_cases i <;> simp [basis]
    ring
  have h₃ : ((coreLift1 d).scale (-1/l)).apply ![5+r,6+l*s,5+s] = ![5+r,6+l*s,5] := by
    rw [StationaryPulse.apply, StationaryPulse.scale_field, coreLift1_on d hr hls]
    ext i; fin_cases i <;> simp [basis]
    field_simp [hl]
    ring
  change ((coreLift1 d).scale (-1/l)).apply
    (((coreHorizontal d 1).scale (l-1)).apply ((coreLift1 d).apply ![5+r,6+s,5])) = _
  rw [h₁, h₂, h₃]

theorem processingProgram_on {l m r s : ℝ} (hl : l ≠ 0) (hm : m ≠ 0)
    (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (hlr : |l*r| ≤ 1/2) (hms : |m*s| ≤ 1/2) :
    runProgram (processingProgram d l m) ![5+r,6+s,5] = ![5+l*r,6+m*s,5] := by
  rw [processingProgram, runProgram_append, tripleProgram0_on d hl hr hs hlr,
    tripleProgram1_on d hm hlr hs hms]

theorem processingProgram_off (l m : ℝ) (x : Space)
    (hx : x 1 ∈ Set.Icc 2 3) (hz : x 2 = 2) :
    runProgram (processingProgram d l m) x = x := by
  apply runProgram_fixed
  intro p hp
  simp only [processingProgram, tripleProgram0, tripleProgram1, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
    simp [coreLift0_off d x hx, coreLift1_off d x hx, coreHorizontal_off d _ x hz]

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Routing ----
namespace OAI

/-! SheetFlows routing. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem verticalPulse_apply (d : Collar) (R : Rectangle) (hR : R.inCodingSquare)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) {y : Plane} (hy : y ∈ R.carrier) (z c : ℝ) :
    ((verticalPulse d R hR s).scale c).apply (lifted s z y) = lifted s (z+c) y := by
  rw [StationaryPulse.apply, StationaryPulse.scale_field, verticalPulse_own d R hR hs hy]
  ext i; fin_cases i <;> simp [lifted, basis]

theorem evacuateProgram_on (d : Collar) (R : Rectangle) (hR : R.inCodingSquare)
    {y : Plane} (hy : y ∈ R.carrier) :
    runProgram (evacuateProgram d R hR) (lifted 0 2 y) = lifted 4 2 y := by
  have h₁ := verticalPulse_apply d R hR (s := 0) (by norm_num) hy 2 3
  have h₂ := verticalPulse_apply d R hR (s := 4) (by norm_num) hy 5 (-3)
  norm_num only at h₁ h₂
  simp only [evacuateProgram, runProgram_append, runProgram_cons, runProgram_nil, h₁]
  rw [show runProgram (travelProgram d ![4,0]) (lifted 0 5 y) = lifted 4 5 y by
    simp only [lifted, travelProgram_on, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]]
  exact h₂

theorem evacuateProgram_off_input {N : ℕ} (d : Collar) (R : Fin N → Rectangle)
    (hR : ∀ i, (R i).inCodingSquare) (hs : Rectangle.CollarSeparated R d.size)
    {i j : Fin N} (hij : i ≠ j) {y : Plane} (hy : y ∈ (R j).carrier) :
    runProgram (evacuateProgram d (R i) (hR i)) (lifted 0 2 y) = lifted 0 2 y := by
  have h₀ := verticalPulse_off_same d R hR hs hij (s := 0) (by norm_num) hy 2
  have h₄ := verticalPulse_off_far d (R i) (R j) (hR i) (hR j)
    (s := 4) (t := 0) (by norm_num) (by norm_num) (by norm_num) hy 2
  simp only [evacuateProgram, runProgram_append, runProgram_cons, runProgram_nil,
    StationaryPulse.scale_apply_of_field_zero _ _ h₀,
    travelProgram_off d _ _ (by rfl : (lifted 0 2 y) 2 = 2),
    StationaryPulse.scale_apply_of_field_zero _ _ h₄]

theorem evacuateProgram_off_output {N : ℕ} (d : Collar) (R : Fin N → Rectangle)
    (hR : ∀ i, (R i).inCodingSquare) (hs : Rectangle.CollarSeparated R d.size)
    {i j : Fin N} (hij : i ≠ j) {y : Plane} (hy : y ∈ (R j).carrier) :
    runProgram (evacuateProgram d (R i) (hR i)) (lifted 4 2 y) = lifted 4 2 y := by
  have h₀ := verticalPulse_off_far d (R i) (R j) (hR i) (hR j)
    (s := 0) (t := 4) (by norm_num) (by norm_num) (by norm_num) hy 2
  have h₄ := verticalPulse_off_same d R hR hs hij (s := 4) (by norm_num) hy 2
  simp only [evacuateProgram, runProgram_append, runProgram_cons, runProgram_nil,
    StationaryPulse.scale_apply_of_field_zero _ _ h₀,
    travelProgram_off d _ _ (by rfl : (lifted 4 2 y) 2 = 2),
    StationaryPulse.scale_apply_of_field_zero _ _ h₄]

theorem SheetData.image_mem {N : ℕ} (D : SheetData N) (i : Fin N)
    {y : Plane} (hy : y ∈ (D.source i).carrier) :
    diagonalMap (D.source i) (D.target i) (D.ratio i) y ∈ (D.target i).carrier := by
  rw [← D.image_eq i]
  exact Set.mem_image_of_mem _ hy

theorem instructionProgram_on {N : ℕ} (d : Collar) (D : SheetData N) (i : Fin N)
    {y : Plane} (hy : y ∈ (D.source i).carrier) :
    runProgram (instructionProgram d D i) (lifted 4 2 y) =
      lifted 0 2 (diagonalMap (D.source i) (D.target i) (D.ratio i) y) := by
  let r := y 0 - (D.source i).center 0
  let s := y 1 - (D.source i).center 1
  have hr : |r| ≤ 1/2 := (D.source i).offset_bound (D.source_inside i) hy 0
  have hs : |s| ≤ 1/2 := (D.source i).offset_bound (D.source_inside i) hy 1
  have hlr : |(D.ratio i 0:ℝ)*r| ≤ 1/2 := D.scaled_offset_bound i hy 0
  have hms : |(D.ratio i 1:ℝ)*s| ≤ 1/2 := D.scaled_offset_bound i hy 1
  have hl : (D.ratio i 0:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D.ratio_positive i 0)
  have hm : (D.ratio i 1:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D.ratio_positive i 1)
  have hlift := verticalPulse_apply d (D.source i) (D.source_inside i) (s := 4)
    (by norm_num) hy 2 3
  norm_num only at hlift
  have hgo : runProgram (travelProgram d ![1-(D.source i).center 0,6-(D.source i).center 1])
      (lifted 4 5 y) = ![5+r,6+s,5] := by
    rw [lifted, travelProgram_on]
    ext j; fin_cases j <;> simp [r,s] <;> ring
  have hback : runProgram (travelProgram d ![(D.target i).center 0-5,(D.target i).center 1-6])
      ![5+(D.ratio i 0:ℝ)*r,6+(D.ratio i 1:ℝ)*s,5] =
      lifted 0 5 (diagonalMap (D.source i) (D.target i) (D.ratio i) y) := by
    rw [travelProgram_on]
    ext j; fin_cases j <;> simp [r,s,lifted,diagonalMap] <;> ring
  have hdrop := verticalPulse_apply d (D.target i) (D.target_inside i) (s := 0)
    (by norm_num) (D.image_mem i hy) 5 (-3)
  norm_num only at hdrop
  simp only [instructionProgram, runProgram_append, runProgram_cons, runProgram_nil,
    hlift, hgo, processingProgram_on d hl hm hr hs hlr hms, hback, hdrop]

theorem instructionProgram_off_input {N : ℕ} (d : Collar) (D : SheetData N)
    (hsource : Rectangle.CollarSeparated D.source d.size)
    {i j : Fin N} (hij : i ≠ j) {y : Plane} (hy : y ∈ (D.source j).carrier) :
    runProgram (instructionProgram d D i) (lifted 4 2 y) = lifted 4 2 y := by
  have h₁ := verticalPulse_off_same d D.source D.source_inside hsource hij
    (s := 4) (by norm_num) hy 2
  have h₂ := verticalPulse_off_far d (D.target i) (D.source j)
    (D.target_inside i) (D.source_inside j) (s := 0) (t := 4)
    (by norm_num) (by norm_num) (by norm_num) hy 2
  have hx : (lifted 4 2 y) 1 ∈ Set.Icc 2 3 :=
    (D.source j).point_bounds (D.source_inside j) hy 1
  have hz : (lifted 4 2 y) 2 = 2 := rfl
  simp only [instructionProgram, runProgram_append, runProgram_cons, runProgram_nil,
    StationaryPulse.scale_apply_of_field_zero _ _ h₁, travelProgram_off d _ _ hz,
    processingProgram_off d _ _ _ hx hz, StationaryPulse.scale_apply_of_field_zero _ _ h₂]

theorem instructionProgram_off_output {N : ℕ} (d : Collar) (D : SheetData N)
    (htarget : Rectangle.CollarSeparated D.target d.size)
    {i j : Fin N} (hij : i ≠ j) {y : Plane} (hy : y ∈ (D.target j).carrier) :
    runProgram (instructionProgram d D i) (lifted 0 2 y) = lifted 0 2 y := by
  have h₁ := verticalPulse_off_far d (D.source i) (D.target j)
    (D.source_inside i) (D.target_inside j) (s := 4) (t := 0)
    (by norm_num) (by norm_num) (by norm_num) hy 2
  have h₂ := verticalPulse_off_same d D.target D.target_inside htarget hij
    (s := 0) (by norm_num) hy 2
  have hx : (lifted 0 2 y) 1 ∈ Set.Icc 2 3 :=
    (D.target j).point_bounds (D.target_inside j) hy 1
  have hz : (lifted 0 2 y) 2 = 2 := rfl
  simp only [instructionProgram, runProgram_append, runProgram_cons, runProgram_nil,
    StationaryPulse.scale_apply_of_field_zero _ _ h₁, travelProgram_off d _ _ hz,
    processingProgram_off d _ _ _ hx hz, StationaryPulse.scale_apply_of_field_zero _ _ h₂]

theorem runProgram_flatMap_fixed {ι : Type*} (l : List ι)
    (P : ι → List StationaryPulse) (a : Space)
    (h : ∀ i ∈ l, runProgram (P i) a = a) :
    runProgram (l.flatMap P) a = a := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [List.flatMap_cons, runProgram_append, h i (by simp)]
      exact ih (fun j hj => h j (by simp [hj]))

theorem runProgram_separate_branches {ι A : Type*} (l : List ι) (hl : l.Nodup)
    (P : ι → List StationaryPulse) (domain : ι → Set A)
    (input output : ι → A → Space)
    (hown : ∀ i a, a ∈ domain i → runProgram (P i) (input i a) = output i a)
    (hin : ∀ i j, i ≠ j → ∀ a ∈ domain j,
      runProgram (P i) (input j a) = input j a)
    (hout : ∀ i j, i ≠ j → ∀ a ∈ domain j,
      runProgram (P i) (output j a) = output j a) :
    ∀ i ∈ l, ∀ a ∈ domain i, runProgram (l.flatMap P) (input i a) = output i a := by
  classical
  induction l with
  | nil => simp
  | cons j l ih =>
      rcases List.nodup_cons.mp hl with ⟨hjl,hl⟩
      intro i hi a ha
      rw [List.flatMap_cons, runProgram_append]
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hown i a ha]
        exact runProgram_flatMap_fixed l P (output i a) (fun k hk =>
          hout k i (fun h => hjl (h ▸ hk)) a ha)
      · have hji : j ≠ i := fun h => hjl (h ▸ hi)
        rw [hin j i hji a ha]
        exact ih hl i hi a ha

theorem sheetProgram_on {N : ℕ} (d : Collar) (D : SheetData N)
    (hsource : Rectangle.CollarSeparated D.source d.size)
    (htarget : Rectangle.CollarSeparated D.target d.size)
    (i : Fin N) {y : Plane} (hy : y ∈ (D.source i).carrier) :
    runProgram (sheetProgram d D) (sheet y) =
      sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y) := by
  have hev := runProgram_separate_branches (List.finRange N) (List.nodup_finRange N)
    (fun i => evacuateProgram d (D.source i) (D.source_inside i))
    (fun i => (D.source i).carrier) (fun _ => lifted 0 2) (fun _ => lifted 4 2)
    (fun i _ hy => evacuateProgram_on d (D.source i) (D.source_inside i) hy)
    (fun _ _ hij _ hj => evacuateProgram_off_input d D.source D.source_inside hsource hij hj)
    (fun _ _ hij _ hj => evacuateProgram_off_output d D.source D.source_inside hsource hij hj)
    i (List.mem_finRange i) y hy
  have hop := runProgram_separate_branches (List.finRange N) (List.nodup_finRange N)
    (instructionProgram d D) (fun i => (D.source i).carrier) (fun _ => lifted 4 2)
    (fun i y => lifted 0 2 (diagonalMap (D.source i) (D.target i) (D.ratio i) y))
    (fun i _ hy => instructionProgram_on d D i hy)
    (fun _ _ hij _ hj => instructionProgram_off_input d D hsource hij hj)
    (fun _ j hij _ hj => instructionProgram_off_output d D htarget hij (D.image_mem j hj))
    i (List.mem_finRange i) y hy
  have hs (y : Plane) : sheet y = lifted 0 2 y := by simp [sheet,lifted]
  rw [sheetProgram, runProgram_append, hs, hev, hop, hs]

end Solenoidal
end

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.JetCalculus ----
namespace OAI

/-! SheetFlows jet calculus. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial
namespace Solenoidal

theorem flatJet_smooth (p : ℚ[X]) : ContDiff ℝ (⊤ : ℕ∞) (flatJet p) :=
  expNegInvGlue.contDiff_polynomial_eval_inv_mul _

theorem transitionReciprocal_smooth : ContDiff ℝ (⊤ : ℕ∞) transitionReciprocal := by
  exact (expNegInvGlue.contDiff.add
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))).inv
      (fun x => (Real.smoothTransition.pos_denom x).ne')

namespace JetExpr

theorem smooth (f : JetExpr) : ContDiff ℝ (⊤ : ℕ∞) f.eval := by
  induction f with
  | const q => exact contDiff_const
  | id => exact contDiff_id
  | add f g hf hg => exact hf.add hg
  | mul f g hf hg => exact hf.mul hg
  | affine a b f hf => exact hf.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  | flat p => exact flatJet_smooth p
  | reciprocal => exact transitionReciprocal_smooth

end JetExpr

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.BoxJets ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! SheetFlows box jets. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

namespace BoxExpr

theorem smooth (e : BoxExpr) : ContDiff ℝ (⊤ : ℕ∞) e.eval := by
  induction e with
  | const q => exact contDiff_const
  | coord j e => exact e.smooth.comp (coordinateLinear j).contDiff
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem diff_correct (e : BoxExpr) (j : Fin 4) (z : SpaceTime) :
    (e.diff j).eval z = fderiv ℝ e.eval z (spacetimeBasis j) := by
  induction e with
  | const q => simp [diff,eval]
  | coord i e =>
      have h := HasDerivAt.comp_hasFDerivAt z (e.diff_correct (coordinateLinear i z))
        (coordinateLinear i).hasFDerivAt
      have he : (.coord i e : BoxExpr).eval = e.eval ∘ coordinateLinear i := rfl
      rw [he, h.fderiv]
      by_cases hij : i=j
      · subst j
        simp only [diff, ↓reduceIte, eval, smul_apply, coordinateLinear_basis,
          smul_eq_mul, mul_one]
      · simp only [diff, eval, Rat.cast_zero, smul_apply,
          coordinateLinear_basis, ite_eq_right hij, smul_eq_mul, mul_zero]
  | add e f he hf =>
      simp only [diff, eval, fderiv_fun_add (e.smooth.differentiable (by simp) z)
        (f.smooth.differentiable (by simp) z), add_apply, he, hf]
  | mul e f he hf =>
      simp only [diff, eval, fderiv_fun_mul (e.smooth.differentiable (by simp) z)
        (f.smooth.differentiable (by simp) z), add_apply,
        smul_apply, smul_eq_mul, he, hf]
      ring

end BoxExpr

theorem expressionField_smooth (e : Fin 3 → BoxExpr) : Smooth (expressionField e) :=
  contDiff_pi.mpr (fun j => (e j).smooth)

theorem mixedDerivative_expressionField (e : Fin 3 → BoxExpr) (α : List (Fin 4)) :
    mixedDerivative (expressionField e) α = fun z j => ((e j).mixed α).eval z := by
  induction α with
  | nil => rfl
  | cons k α ih =>
      ext z j
      rw [mixedDerivative,ih]
      change (fderiv ℝ (fun z j => ((e j).mixed α).eval z) z (spacetimeBasis k)) j = _
      rw [fderiv_pi (fun i => ((e i).mixed α).smooth.differentiable (by simp) z)]
      exact (((e j).mixed α).diff_correct k z).symm

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.RationalFormula ----
namespace OAI

/-! SheetFlows rational formula. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

namespace BoxExpr

end BoxExpr

namespace HasRationalFormula

theorem smul {u : Field} (hu : HasRationalFormula u) (q : ℚ) :
    HasRationalFormula ((q:ℝ) • u) := by
  obtain ⟨e,he⟩ := hu
  refine ⟨fun j => .mul (.const q) (e j), ?_⟩
  intro z hz
  ext j
  have hh := congrFun (he hz) j
  simpa only [expressionField,BoxExpr.eval,Pi.smul_apply,smul_eq_mul] using congrArg ((q:ℝ)*·) hh

theorem sum {ι : Type*} [Fintype ι] {u : ι → Field}
    (hu : ∀ i, HasRationalFormula (u i)) : HasRationalFormula (∑ i, u i) := by
  choose e he using hu
  refine ⟨fun j => BoxExpr.sum (fun i => e i j), ?_⟩
  intro z hz
  ext j
  simp only [Finset.sum_apply,expressionField,BoxExpr.eval_sum]
  exact Finset.sum_congr rfl (fun i _ => congrFun (he i hz) j)

theorem mixed {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) (α : List (Fin 4)) :
    HasRationalFormula (fun t x => mixedDerivative u α (t,x)) := by
  obtain ⟨e,he⟩ := hu
  refine ⟨fun j => (e j).mixed α, ?_⟩
  intro z hz
  have hh := mixedDerivative_eqOn_cell hs (expressionField_smooth e) he α hz
  rw [mixedDerivative_expressionField] at hh
  exact hh

theorem directional {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) (j : Fin 4) :
    HasRationalFormula (fieldDirectional u (spacetimeBasis j)) := hu.mixed hs [j]

theorem fullTimePartial {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) :
    HasRationalFormula (Solenoidal.fullTimePartial u) := by
  rw [fullTimePartial_eq_fieldDirectional hs]
  exact hu.directional hs 0

theorem spatialPartial {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) (j : Fin 3) :
    HasRationalFormula (Solenoidal.spatialPartial u j) := by
  rw [spatialPartial_eq_fieldDirectional hs]
  have hh := hu.directional hs j.succ
  have he : spacetimeBasis j.succ = (0,basis j) := by fin_cases j <;> rfl
  rwa [he] at hh

theorem laplacian {u : Field} (hu : HasRationalFormula u) (hs : Smooth u) :
    HasRationalFormula (Solenoidal.laplacian u) :=
  .sum (fun j => (hu.spatialPartial hs j).spatialPartial (smooth_spatialPartial hs j) j)

end HasRationalFormula

theorem timeProfile_formula {u : Field} (hu : HasRationalFormula u) {g : ℝ → ℝ}
    (p : PeriodicJet 1 g) : HasRationalFormula (fun t x => g t • u t x) := by
  obtain ⟨e,he⟩ := hu
  refine ⟨fun j => .mul (.coord 0 p.expression) (e j), ?_⟩
  intro z hz
  ext j
  have hh := congrFun (he hz) j
  have ht := p.on_chart (show z.1 ∈ Set.Icc (0:ℝ) (1:ℚ) by simpa using And.intro hz.1.1 hz.2.1)
  change g z.1 * u z.1 z.2 j = p.expression.eval z.1 * (e j).eval z
  change u z.1 z.2 j = (e j).eval z at hh
  rw [hh,ht]

theorem scheduleVelocity_formula {m : ℕ} (v : Fin m → Space → Space)
    (h : ∀ i, HasRationalFormula (fun _ => v i)) :
    HasRationalFormula (scheduleVelocity v) := by
  have hh := HasRationalFormula.sum (fun i => timeProfile_formula (h i) (scheduledPulse_jet i))
  convert hh using 1
  ext t x j
  simp [scheduleVelocity,Finset.sum_apply]

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.FormulaProfiles ----
namespace OAI

/-! SheetFlows formula profiles. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

namespace RationalParameter

theorem rat (q : ℚ) : RationalParameter (q:ℝ) := ⟨q,rfl⟩
theorem ofNat (n : ℕ) : RationalParameter (n:ℝ) := ⟨n,by simp⟩
theorem add {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a+b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a+b,by simp⟩
theorem sub {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a-b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a-b,by simp⟩
theorem div {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a/b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a/b,by simp⟩
theorem neg {a : ℝ} (ha : RationalParameter a) : RationalParameter (-a) := by
  obtain ⟨a,rfl⟩ := ha
  exact ⟨-a,by simp⟩
end RationalParameter

theorem Rectangle.center_rational (R : Rectangle) (j : Fin 2) :
    RationalParameter (R.center j) :=
  ((RationalParameter.rat _).add (.rat _)).div (.ofNat 2)

theorem Cprofile_hasJet {h d c : ℝ}
    (hh : RationalParameter h) (hd : RationalParameter d) (hc : RationalParameter c)
    (hpos : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    Nonempty (PeriodicJet 10 (Cprofile h d c)) := by
  obtain ⟨h,rfl⟩ := hh; obtain ⟨d,rfl⟩ := hd; obtain ⟨c,rfl⟩ := hc
  exact ⟨Cprofile_jet h d c (by exact_mod_cast hpos) (by exact_mod_cast hl) (by exact_mod_cast hu)⟩

theorem Dprofile_hasJet {h d c : ℝ}
    (hh : RationalParameter h) (hd : RationalParameter d) (hc : RationalParameter c)
    (hpos : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    Nonempty (PeriodicJet 10 (Dprofile h d c)) := by
  obtain ⟨h,rfl⟩ := hh; obtain ⟨d,rfl⟩ := hd; obtain ⟨c,rfl⟩ := hc
  exact ⟨Dprofile_jet h d c (by exact_mod_cast hpos) (by exact_mod_cast hl) (by exact_mod_cast hu)⟩

namespace StationaryPulse

theorem RationalFormula.scale {p : StationaryPulse} {c : ℝ}
    (hp : p.RationalFormula) (hc : RationalParameter c) : (p.scale c).RationalFormula := by
  obtain ⟨q,rfl⟩ := hc
  exact hp.smul q

theorem rationalFormula_tensor (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j))
    (hp : ∀ j, Function.Periodic (g j) 10)
    (hi : ∀ s, g i s = 1) (j : Fin 3)
    (hz : (∫ s in Set.Ico (0 : ℝ) 10, g j s) = 0)
    (hr : ∀ j, Nonempty (PeriodicJet 10 (g j))) :
    (tensor i g hsm hp hi j hz).RationalFormula := tensorVelocity_formula i g hr

end StationaryPulse

variable (d : Collar) (hd : RationalParameter d.size)
include hd

theorem horizontalPulse_formula (j : Fin 2) : (horizontalPulse d j).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  intro k
  fin_cases k
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩
  · obtain ⟨a⟩ := Cprofile_hasJet (show RationalParameter 0 from ⟨0, by norm_num⟩) hd (show RationalParameter 5 from ⟨5, by norm_num⟩) d.positive
      (show 0+d.size ≤ 5 by linarith [d.small])
      (show 5+(0+d.size) ≤ 10 by linarith [d.small])
    obtain ⟨b⟩ := Cprofile_hasJet (show RationalParameter 0 from ⟨0, by norm_num⟩) hd (show RationalParameter 8 from ⟨8, by norm_num⟩) d.positive
      (show 0+d.size ≤ 8 by linarith [d.small])
      (show 8+(0+d.size) ≤ 10 by linarith [d.small])
    exact ⟨a.sub b⟩

theorem coreLift0_formula : (coreLift0 d).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  intro k
  fin_cases k
  · exact Dprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 5 from ⟨5, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])
  · exact Cprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 6 from ⟨6, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩

theorem coreLift1_formula : (coreLift1 d).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  intro k
  fin_cases k
  · exact Cprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 5 from ⟨5, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])
  · exact Dprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 6 from ⟨6, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩

theorem coreHorizontal_formula (j : Fin 2) : (coreHorizontal d j).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  intro k
  fin_cases k
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩
  · exact Dprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 5 from ⟨5, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])

theorem travelProgram_formula (v : Plane) (hv : ∀ j, RationalParameter (v j)) :
    ∀ p ∈ travelProgram d v, p.RationalFormula := by
  intro p hp
  simp only [travelProgram,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact (horizontalPulse_formula d hd 0).scale (hv 0)
  · exact (horizontalPulse_formula d hd 1).scale (hv 1)

theorem tripleProgram0_formula {l : ℝ} (hl : RationalParameter l) :
    ∀ p ∈ tripleProgram0 d l, p.RationalFormula := by
  have h1 : RationalParameter (1:ℝ) := ⟨1,by norm_num⟩
  intro p hp
  simp only [tripleProgram0,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact coreLift0_formula d hd
  · exact (coreHorizontal_formula d hd 0).scale (hl.sub h1)
  · exact (coreLift0_formula d hd).scale (h1.neg.div hl)

theorem tripleProgram1_formula {l : ℝ} (hl : RationalParameter l) :
    ∀ p ∈ tripleProgram1 d l, p.RationalFormula := by
  have h1 : RationalParameter (1:ℝ) := ⟨1,by norm_num⟩
  intro p hp
  simp only [tripleProgram1,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact coreLift1_formula d hd
  · exact (coreHorizontal_formula d hd 1).scale (hl.sub h1)
  · exact (coreLift1_formula d hd).scale (h1.neg.div hl)

theorem processingProgram_formula {l m : ℝ} (hl : RationalParameter l)
    (hm : RationalParameter m) : ∀ p ∈ processingProgram d l m, p.RationalFormula := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact tripleProgram0_formula d hd hl p hp
  · exact tripleProgram1_formula d hd hm p hp

theorem evacuateProgram_formula (R : Rectangle) (hR : R.inCodingSquare) :
    ∀ p ∈ evacuateProgram d R hR, p.RationalFormula := by
  intro p hp
  simp only [evacuateProgram,List.mem_append,List.mem_singleton] at hp
  rcases hp with (rfl | hp) | rfl
  · exact (verticalPulse_formula d hd R hR (by norm_num) ⟨0,by norm_num⟩).scale ⟨3,by norm_num⟩
  · apply travelProgram_formula d hd _ _ _ hp
    intro j; fin_cases j
    · exact ⟨4,by norm_num⟩
    · exact ⟨0,by norm_num⟩
  · exact (verticalPulse_formula d hd R hR (by norm_num) ⟨4,by norm_num⟩).scale ⟨-3,by norm_num⟩

theorem instructionProgram_formula {N : ℕ} (D : SheetData N) (i : Fin N) :
    ∀ p ∈ instructionProgram d D i, p.RationalFormula := by
  intro p hp
  simp only [instructionProgram,List.mem_append,List.mem_singleton] at hp
  rcases hp with (((rfl | hp) | hp) | hp) | rfl
  · exact (verticalPulse_formula d hd _ (D.source_inside i) (by norm_num)
      ⟨4,by norm_num⟩).scale ⟨3,by norm_num⟩
  · apply travelProgram_formula d hd _ _ _ hp
    intro j; fin_cases j
    · exact (show RationalParameter 1 from ⟨1,by norm_num⟩).sub ((D.source i).center_rational 0)
    · exact (show RationalParameter 6 from ⟨6,by norm_num⟩).sub ((D.source i).center_rational 1)
  · exact processingProgram_formula d hd (.rat _) (.rat _) _ hp
  · apply travelProgram_formula d hd _ _ _ hp
    intro j; fin_cases j
    · exact ((D.target i).center_rational 0).sub ⟨5,by norm_num⟩
    · exact ((D.target i).center_rational 1).sub ⟨6,by norm_num⟩
  · exact (verticalPulse_formula d hd _ (D.target_inside i) (by norm_num)
      ⟨0,by norm_num⟩).scale ⟨-3,by norm_num⟩

theorem sheetProgram_formula {N : ℕ} (D : SheetData N) :
    ∀ p ∈ sheetProgram d D, p.RationalFormula := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hp
    exact evacuateProgram_formula d hd _ (D.source_inside i) p hi
  · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hp
    exact instructionProgram_formula d hd D i p hi

theorem sheetVelocity_formula {N : ℕ} (D : SheetData N) :
    HasRationalFormula (scheduleVelocity
      (fun i : Fin (sheetProgram d D).length => ((sheetProgram d D).get i).field)) :=
  scheduleVelocity_formula _ (fun index => sheetProgram_formula d hd D _ (List.get_mem _ index))

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.RationalBalls ----
namespace OAI

/-! SheetFlows rational balls. -/

section
open Set Filter
open scoped Topology BigOperators
namespace Solenoidal

namespace QBall

theorem radius_nonneg {a : QBall} {x : ℝ} (h : a.Contains x) : 0 ≤ a.2 := by
  exact_mod_cast (abs_nonneg _).trans h

theorem add_contains {a b : QBall} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (add a b).Contains (x+y) := by
  dsimp [Contains,add]
  push_cast
  calc
    |(a.1:ℝ)+b.1-(x+y)| = |((a.1:ℝ)-x)+((b.1:ℝ)-y)| := by ring_nf
    _ ≤ |(a.1:ℝ)-x|+|(b.1:ℝ)-y| := abs_add_le _ _
    _ ≤ (a.2:ℝ)+b.2 := add_le_add ha hb

theorem mul_contains {a b : QBall} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (mul a b).Contains (x*y) := by
  have har : (0:ℝ) ≤ a.2 := by exact_mod_cast radius_nonneg ha
  have hbr : (0:ℝ) ≤ b.2 := by exact_mod_cast radius_nonneg hb
  have hx : |x| ≤ |(a.1:ℝ)|+a.2 := by
    calc
      |x| = |(a.1:ℝ)-((a.1:ℝ)-x)| := by ring_nf
      _ ≤ |(a.1:ℝ)|+|(a.1:ℝ)-x| := abs_sub _ _
      _ ≤ _ := add_le_add le_rfl ha
  dsimp [Contains,mul]
  push_cast
  calc
    |(a.1:ℝ)*b.1-x*y| = |(a.1:ℝ)*((b.1:ℝ)-y) + ((a.1:ℝ)-x)*y| := by ring_nf
    _ ≤ |(a.1:ℝ)*((b.1:ℝ)-y)| + |((a.1:ℝ)-x)*y| := abs_add_le _ _
    _ = |(a.1:ℝ)| *|(b.1:ℝ)-y| + |(a.1:ℝ)-x| *|y| := by simp only [abs_mul]
    _ ≤ |(a.1:ℝ)| *b.2 + a.2*(|(b.1:ℝ)|+b.2) := by
      have hy : |y| ≤ |(b.1:ℝ)|+b.2 := by
        calc
          |y| = |(b.1:ℝ)-((b.1:ℝ)-y)| := by ring_nf
          _ ≤ |(b.1:ℝ)|+|(b.1:ℝ)-y| := abs_sub _ _
          _ ≤ _ := add_le_add le_rfl hb
      exact add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul ha hy (abs_nonneg _) har)
    _ = _ := by ring

theorem Approximates.center {A : ℕ → QBall} {x : ℝ} (h : Approximates A x) :
    Tendsto (fun n => ((A n).1:ℝ)) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => h.contains n) h.radius

theorem approximates_point (q : ℚ) : Approximates (fun _ => point q) (q:ℝ) :=
  ⟨fun _ => point_contains q, by simp [point]⟩

theorem Approximates.add {A B : ℕ → QBall} {x y : ℝ}
    (ha : Approximates A x) (hb : Approximates B y) :
    Approximates (fun n => add (A n) (B n)) (x+y) := by
  refine ⟨fun n => add_contains (ha.contains n) (hb.contains n), ?_⟩
  simpa [QBall.add] using ha.radius.add hb.radius

theorem Approximates.mul {A B : ℕ → QBall} {x y : ℝ}
    (ha : Approximates A x) (hb : Approximates B y) :
    Approximates (fun n => mul (A n) (B n)) (x*y) := by
  refine ⟨fun n => mul_contains (ha.contains n) (hb.contains n), ?_⟩
  simpa [QBall.mul] using ((ha.center.abs.mul hb.radius).add
    (hb.center.abs.mul ha.radius)).add (ha.radius.mul hb.radius)

theorem Approximates.pow {A : ℕ → QBall} {x : ℝ}
    (h : Approximates A x) (m : ℕ) :
    Approximates (fun n => pow (A n) m) (x^m) := by
  induction m with
  | zero => simpa [QBall.pow] using approximates_point 1
  | succ m hm => simpa [QBall.pow,pow_succ] using hm.mul h

theorem smallExp_approximates (q : ℚ) (hq : |q| ≤ 1/2) :
    Approximates (smallExp q) (Real.exp (q:ℝ)) := by
  have hq' : |(q:ℝ)| ≤ 1/2 := by
    have h : ((|q|:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := Rat.cast_le.mpr hq
    simpa using h
  refine ⟨?_, ?_⟩
  · intro n
    have he := Real.exp_bound (show |(q:ℝ)| ≤ 1 by linarith) (Nat.succ_pos n)
    have hf : (1:ℝ) ≤ (n+1).factorial := by exact_mod_cast (n+1).factorial_pos
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.succ_pos n
    have hb : (((n+1).succ:ℕ):ℝ) / ((n+1).factorial * (n+1:ℕ)) ≤ 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      push_cast
      have := mul_le_mul_of_nonneg_right hf (show (0:ℝ) ≤ n+1 by positivity)
      nlinarith
    have hp := pow_le_pow_left₀ (abs_nonneg (q:ℝ)) hq' (n+1)
    have hg := he.trans (mul_le_mul hp hb (by positivity) (by positivity))
    simpa [Contains,smallExp,taylor,abs_sub_comm,mul_comm] using hg
  · have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_const (1/2:ℝ)
    simpa [smallExp,pow_succ] using hh.const_mul 2

theorem expScale_pos (q : ℚ) : 0 < expScale q := by unfold expScale; omega

theorem expScale_large (q : ℚ) : |q / (expScale q:ℚ)| ≤ 1/2 := by
  have hden : (1:ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have hn : |q| ≤ (q.num.natAbs:ℚ) := by
    have hnum : |(q.num:ℚ)| = (q.num.natAbs:ℚ) := by
      cases h : q.num with
      | ofNat n => simp
      | negSucc n => simp [Int.negSucc_eq]
    calc
      |q| = |(q.num:ℚ)| / q.den := by
        conv_lhs => rw [← Rat.num_div_den q]
        rw [abs_div,abs_of_nonneg (show (0:ℚ) ≤ (q.den:ℚ) by positivity)]
      _ ≤ |(q.num:ℚ)| := div_le_self (abs_nonneg _) hden
      _ = _ := hnum
  rw [abs_div,abs_of_pos (show (0:ℚ) < (expScale q:ℚ) by exact_mod_cast expScale_pos q),
    div_le_iff₀ (show (0:ℚ) < (expScale q:ℚ) by exact_mod_cast expScale_pos q)]
  dsimp [expScale]
  push_cast
  linarith

theorem expApprox_approximates (q : ℚ) :
    Approximates (expApprox q) (Real.exp (q:ℝ)) := by
  have h := (smallExp_approximates _ (expScale_large q)).pow (expScale q)
  have he : Real.exp ((q / (expScale q:ℚ):ℚ):ℝ) ^ expScale q = Real.exp (q:ℝ) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    field_simp [(show (expScale q:ℝ) ≠ 0 by exact_mod_cast (expScale_pos q).ne')]
  exact he ▸ h

theorem flatApprox_approximates (m : ℕ) (q : ℚ) :
    Approximates (flatApprox m q) (flatJet (Polynomial.X^m) (q:ℝ)) := by
  unfold flatApprox
  by_cases hq : q ≤ 0
  · have hq' : (q:ℝ) ≤ 0 := by exact_mod_cast hq
    simpa [hq,flatJet,expNegInvGlue.zero_of_nonpos hq'] using approximates_point 0
  · have hq' : ¬ (q:ℝ) ≤ 0 := by exact_mod_cast hq
    have h := (approximates_point (q⁻¹^m)).mul (expApprox_approximates (-q⁻¹))
    simpa [hq,flatJet,expNegInvGlue,hq'] using h

end QBall
end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Computing ----
namespace OAI

/-! SheetFlows computing. -/

section
open Encodable
namespace Solenoidal.Computing

theorem int_ofNat : Primrec Int.ofNat :=
  Primrec.encode_iff.mp (Primrec.nat_mul.comp (.const 2) .id)

theorem int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) .id) (.const 1))

theorem int_neg : Primrec ((- ·) : ℤ → ℤ) := by
  have h : Primrec (fun z : ℤ => Int.casesOn (motive := fun _ => ℤ) z
      (fun n => Nat.casesOn n (0 : ℤ) Int.negSucc) (fun n => Int.ofNat (n+1))) := by
    exact int_cases .id
      (Primrec.nat_casesOn .snd (.const 0) (int_negSucc.comp .snd).to₂)
      (int_ofNat.comp (Primrec.succ.comp .snd))
  exact h.of_eq (fun z => by cases z with
    | ofNat n => cases n <;> rfl
    | negSucc n => rfl)

theorem int_edivNat : Primrec₂ (fun (z : ℤ) (n : ℕ) => z / (n:ℤ)) := by
  let f : ℤ×ℕ → ℤ := fun p => Int.casesOn p.1
    (fun m => Int.ofNat (m / p.2))
    (fun m => Nat.casesOn p.2 0 (fun n => Int.negSucc (m / (n+1))))
  have h : Primrec f := by
    apply int_cases .fst
    · exact int_ofNat.comp (Primrec.nat_div.comp .snd (Primrec.snd.comp .fst))
    · exact Primrec.nat_casesOn (Primrec.snd.comp .fst) (.const 0)
        (int_negSucc.comp (Primrec.nat_div.comp (Primrec.snd.comp .fst)
          (Primrec.succ.comp .snd))).to₂
  exact h.of_eq (fun ⟨a,b⟩ => by cases a <;> cases b <;> rfl)

theorem int_nonneg : PrimrecPred (fun z : ℤ => 0 ≤ z) := by
  refine ⟨inferInstance, ?_⟩
  refine (int_cases .id (Primrec₂.const true) (Primrec₂.const false)).of_eq ?_
  intro z
  cases z with
  | ofNat n => change true = decide (0 ≤ (n:ℤ)); simp
  | negSucc n => rfl

theorem int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) :=
  (int_nonneg.comp (int_add.comp .snd (int_neg.comp .fst))).of_eq
    (fun p => by simp [← sub_eq_add_neg])

theorem rat_num : Primrec Rat.num :=
  Primrec.fst.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e := ratEquiv)))

theorem rat_den : Primrec Rat.den :=
  Primrec.snd.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e := ratEquiv)))

theorem rat_mk_iff {α : Type*} [Primcodable α] {f : α → ℚ} :
    Primrec f ↔ Primrec (fun a => (f a).num) ∧ Primrec (fun a => (f a).den) := by
  refine ⟨fun h => ⟨rat_num.comp h,rat_den.comp h⟩, fun h => ?_⟩
  exact (Primrec.of_equiv_iff ratEquiv).mp
    ((Primrec.subtype_val_iff).mp (h.1.pair h.2))

theorem rat_mk : Primrec₂ mkRat := by
  apply rat_mk_iff.mpr
  constructor
  · exact (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 0)
      (int_edivNat.comp .fst (nat_gcd.comp .snd (int_natAbs.comp .fst)))).of_eq
        (fun p => (Rat.num_mkRat p.1 p.2).symm)
  · exact (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1)
      (Primrec.nat_div.comp .snd (nat_gcd.comp .snd (int_natAbs.comp .fst)))).of_eq
        (fun p => (Rat.den_mkRat p.1 p.2).symm)

theorem rat_int : Primrec (fun z : ℤ => (z:ℚ)) :=
  rat_mk_iff.mpr ⟨.id,.const 1⟩

theorem rat_nat : Primrec (fun n : ℕ => (n:ℚ)) := rat_int.comp int_ofNat

theorem rat_neg : Primrec (fun q : ℚ => -q) :=
  rat_mk_iff.mpr ⟨int_neg.comp rat_num,rat_den⟩

theorem rat_add : Primrec₂ ((·+·) : ℚ → ℚ → ℚ) :=
  (rat_mk.comp (int_add.comp
    (int_mul.comp (rat_num.comp .fst) (int_ofNat.comp (rat_den.comp .snd)))
    (int_mul.comp (rat_num.comp .snd) (int_ofNat.comp (rat_den.comp .fst))))
    (Primrec.nat_mul.comp (rat_den.comp .fst) (rat_den.comp .snd))).of_eq
      (fun p => (Rat.add_def' p.1 p.2).symm)

theorem rat_sub : Primrec₂ ((·-·) : ℚ → ℚ → ℚ) :=
  (rat_add.comp .fst (rat_neg.comp .snd)).of_eq (fun _ => (sub_eq_add_neg ..).symm)

theorem rat_mul : Primrec₂ ((·*·) : ℚ → ℚ → ℚ) :=
  (rat_mk.comp (int_mul.comp (rat_num.comp .fst) (rat_num.comp .snd))
    (Primrec.nat_mul.comp (rat_den.comp .fst) (rat_den.comp .snd))).of_eq
      (fun p => by conv_rhs => rw [← Rat.mkRat_self p.1, ← Rat.mkRat_self p.2]
                   exact (Rat.mkRat_mul_mkRat ..).symm)

theorem rat_le : PrimrecRel ((·≤·) : ℚ → ℚ → Prop) :=
  (int_le.comp
    (int_mul.comp (rat_num.comp .fst) (int_ofNat.comp (rat_den.comp .snd)))
    (int_mul.comp (rat_num.comp .snd) (int_ofNat.comp (rat_den.comp .fst)))).of_eq
      (fun p => (Rat.le_iff (a := p.1) (b := p.2)).symm)

theorem rat_lt : PrimrecRel ((·<·) : ℚ → ℚ → Prop) :=
  ((rat_le.comp .snd .fst).not).of_eq (fun _ => not_le)

theorem rat_abs : Primrec (fun q : ℚ => |q|) :=
  (Primrec.ite (rat_le.comp (.const 0) .id) .id rat_neg).of_eq
    (fun q => by by_cases h : 0 ≤ q
                 · simp [h,abs_of_nonneg h]
                 · simp [h,abs_of_neg (lt_of_not_ge h)])

theorem rat_div : Primrec₂ ((·/·) : ℚ → ℚ → ℚ) :=
  (rat_mul.comp .fst (rat_inv.comp .snd)).of_eq (fun _ => (div_eq_mul_inv ..).symm)

theorem rat_max : Primrec₂ ((max) : ℚ → ℚ → ℚ) :=
  (Primrec.ite rat_le .snd .fst).of_eq (fun _ => rfl)

theorem rat_pow : Primrec₂ ((·^·) : ℚ → ℕ → ℚ) := by
  exact (Primrec.nat_rec (.const 1)
    (rat_mul.comp (Primrec.snd.comp .snd) .fst).to₂).of_eq
      (fun q n => by induction n with
        | zero => simp
        | succ n ih => simp_all [pow_succ])

theorem nat_factorial : Primrec Nat.factorial := by
  have h : Primrec (fun n : ℕ => Nat.rec (motive := fun _ => ℕ) 1 (fun m r => (m+1)*r) n) :=
    Primrec.nat_rec₁ 1
      (Primrec.nat_mul.comp (Primrec.succ.comp .fst) .snd)
  exact h.of_eq (fun n => by induction n with
    | zero => rfl
    | succ n ih => simp [Nat.factorial_succ,ih])

theorem rat_floor : Primrec (fun q : ℚ => ⌊q⌋) :=
  (int_edivNat.comp rat_num rat_den).of_eq (fun q => by
    change q.num / (q.den:ℤ) = q.floor
    exact (Rat.floor_def q).symm)

end Solenoidal.Computing
end

section
open Encodable
open scoped BigOperators
namespace Solenoidal.Computing

theorem ball_point : Primrec QBall.point := Primrec.id.pair (.const 0)
theorem ball_add : Primrec₂ QBall.add :=
  (rat_add.comp (Primrec.fst.comp .fst) (Primrec.fst.comp .snd)).pair
    (rat_add.comp (Primrec.snd.comp .fst) (Primrec.snd.comp .snd))
theorem ball_mul : Primrec₂ QBall.mul :=
  (rat_mul.comp (Primrec.fst.comp .fst) (Primrec.fst.comp .snd)).pair
    (rat_add.comp (rat_add.comp
      (rat_mul.comp (rat_abs.comp (Primrec.fst.comp .fst)) (Primrec.snd.comp .snd))
      (rat_mul.comp (rat_abs.comp (Primrec.fst.comp .snd)) (Primrec.snd.comp .fst)))
      (rat_mul.comp (Primrec.snd.comp .fst) (Primrec.snd.comp .snd)))

theorem ball_pow : Primrec₂ QBall.pow :=
  (Primrec.nat_rec (.const (QBall.point 1))
    (ball_mul.comp (Primrec.snd.comp .snd) .fst).to₂).of_eq
      (fun a n => by induction n with
        | zero => rfl
        | succ n ih => simp [QBall.pow,ih])

theorem rat_sum_range {α : Type*} [Primcodable α] {g : α → ℕ → ℚ}
    (hg : Primrec₂ g) : Primrec₂ (fun a n => ∑ i ∈ Finset.range n, g a i) :=
  (Primrec.nat_rec (.const 0)
    (rat_add.comp (Primrec.snd.comp .snd)
      (hg.comp .fst (Primrec.fst.comp .snd))).to₂).of_eq
      (fun a n => by induction n with
        | zero => simp
        | succ n ih => simp [Finset.sum_range_succ,ih])

theorem ball_taylor : Primrec₂ QBall.taylor :=
  rat_sum_range (rat_div.comp rat_pow (rat_nat.comp (nat_factorial.comp .snd)))

theorem ball_smallExp : Primrec₂ QBall.smallExp :=
  (ball_taylor.comp .fst (Primrec.succ.comp .snd)).pair
    (rat_mul.comp (.const 2) (rat_pow.comp (.const (1/2)) (Primrec.succ.comp .snd)))

theorem ball_expScale : Primrec QBall.expScale :=
  Primrec.nat_mul.comp (.const 2) (Primrec.succ.comp (int_natAbs.comp rat_num))

theorem ball_expApprox : Primrec₂ QBall.expApprox :=
  ball_pow.comp (ball_smallExp.comp
    (rat_div.comp .fst (rat_nat.comp (ball_expScale.comp .fst))) .snd)
    (ball_expScale.comp .fst)

theorem ball_clampInv : Primrec QBall.clampInv :=
  (rat_inv.comp (rat_max.comp (.const (1/32)) .fst)).pair
    (rat_mul.comp (.const 512) .snd)

theorem ball_flatApprox : Primrec (fun p : ℕ × ℚ × ℕ => QBall.flatApprox p.1 p.2.1 p.2.2) :=
  Primrec.ite (rat_le.comp (Primrec.fst.comp .snd) (.const 0)) (.const (QBall.point 0))
    (ball_mul.comp (ball_point.comp (rat_pow.comp (rat_inv.comp (Primrec.fst.comp .snd)) .fst))
      (ball_expApprox.comp (rat_neg.comp (rat_inv.comp (Primrec.fst.comp .snd)))
        (Primrec.snd.comp .snd)))

theorem ball_reciprocalApprox : Primrec₂ QBall.reciprocalApprox :=
  ball_clampInv.comp (ball_add.comp
    (ball_flatApprox.comp ((Primrec.const 0).pair (Primrec.fst.pair .snd)))
    (ball_flatApprox.comp ((Primrec.const 0).pair
      ((rat_sub.comp (.const 1) .fst).pair .snd))))

end Solenoidal.Computing
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Circuits ----
namespace OAI

/-! SheetFlows circuits. -/

section
open Set Filter Encodable Denumerable
open scoped BigOperators Topology Polynomial
namespace Solenoidal

theorem flatJet_sub (p q : ℚ[X]) : flatJet (p-q) = flatJet p - flatJet q := by
  funext x
  simp [flatJet,sub_mul]

theorem flatJet_C_mul (a : ℚ) (p : ℚ[X]) :
    flatJet (Polynomial.C a*p) = fun x => (a:ℝ)*flatJet p x := by
  funext x
  simp [flatJet,mul_assoc]

theorem flatMono_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (flatMono n) (flatMono (n+2) x - (n:ℝ)*flatMono (n+1) x) x := by
  have hp : flatNext (Polynomial.X^n) =
      Polynomial.X^(n+2) - Polynomial.C (n:ℚ)*Polynomial.X^(n+1) := by
    cases n with
    | zero => simp [flatNext]
    | succ n =>
      rw [flatNext, Polynomial.derivative_X_pow]
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  have h := flatJet_hasDerivAt (Polynomial.X^n) x
  rw [hp,flatJet_sub,flatJet_C_mul] at h
  simpa [flatMono] using h

namespace Atom

theorem profile_smooth (k : ℕ) : ContDiff ℝ (⊤:ℕ∞) (profile k) := by
  unfold profile
  split
  · exact contDiff_id
  · split
    · exact transitionReciprocal_smooth
    · exact flatJet_smooth _

theorem smooth (a : Atom) : ContDiff ℝ (⊤:ℕ∞) a.eval :=
  (profile_smooth _).comp
    ((contDiff_const.mul (coordinateLinear a.1).contDiff).add contDiff_const)

theorem bound_nonneg (a : Atom) (R : ℚ) : 0 ≤ a.bound R := by
  unfold bound
  split
  · positivity
  · split <;> positivity

end Atom

namespace Circuit

open Nat.Partrec

theorem smooth (e : Circuit) : ContDiff ℝ (⊤:ℕ∞) (eval e) := by
  induction e with
  | zero | succ | left | right => exact contDiff_const
  | pair a b ha hb => exact ha.add hb
  | comp a b ha hb => exact ha.mul hb
  | prec a b ha hb => exact Atom.smooth _
  | rfind' a ha => exact contDiff_const

theorem bound_nonneg (e : Circuit) (R : ℚ) : 0 ≤ bound e R := by
  induction e with
  | zero | succ | left | right => exact le_rfl
  | pair a b ha hb => exact add_nonneg ha hb
  | comp a b ha hb => exact mul_nonneg ha hb
  | prec a b ha hb => exact Atom.bound_nonneg _ _
  | rfind' a ha => exact abs_nonneg _

theorem atom_approximates (a : Atom) (q : Fin 4 → ℚ) :
    QBall.Approximates (a.approx q) (a.eval (ofRational q)) := by
  unfold Atom.approx
  split
  · rename_i h
    simpa [Atom.eval,Atom.profile,Atom.argument, coordinate_ofRational,h] using QBall.approximates_point (a.argument q)
  · split
    · rename_i h h1
      simpa [Atom.eval,Atom.profile,Atom.argument, coordinate_ofRational,h,h1] using QBall.reciprocalApprox_approximates (a.argument q)
    · rename_i h h1
      simpa [Atom.eval,Atom.profile,Atom.argument, coordinate_ofRational,flatMono,h,h1] using
        QBall.flatApprox_approximates (a.2.2.2-2) (a.argument q)

theorem approximates (e : Circuit) (q : Fin 4 → ℚ) :
    QBall.Approximates (e.approx q) ((eval e) (ofRational q)) := by
  induction e with
  | zero | succ | left | right => simpa [approx,eval] using QBall.approximates_point 0
  | pair a b ha hb => exact ha.add hb
  | comp a b ha hb => exact ha.mul hb
  | prec a b ha hb => exact atom_approximates _ _
  | rfind' a ha => exact QBall.approximates_point _

end Circuit
end Solenoidal
end

open Set Filter Encodable Denumerable
open scoped BigOperators Topology Polynomial
namespace Solenoidal
namespace Atom

theorem profile_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (profile k) (profileDerivative k x) x := by
  unfold profile profileDerivative
  split
  · exact hasDerivAt_id x
  · split
    · exact transitionReciprocal_hasDerivAt x
    · exact flatMono_deriv _ x

end Atom
namespace Circuit
open Nat.Partrec

theorem atomDiff_eval (j : Fin 4) (a : Atom) (z : SpaceTime) :
    eval (atomDiff j a) z =
      (a.2.1:ℝ) * Atom.profileDerivative a.2.2.2
        ((a.2.1:ℝ)*coordinateLinear a.1 z+a.2.2.1) * (if a.1=j then 1 else 0) := by
  unfold atomDiff
  split
  · simp only [eval_mul,eval_const,mul_one]
    congr 1
    unfold Atom.profileDerivative
    split
    · simp
    · split
      · rename_i h h0 h1
        have he : (-(a.2.1:ℝ))*coordinateLinear a.1 z+(1-(a.2.2.1:ℝ)) =
            1-((a.2.1:ℝ)*coordinateLinear a.1 z+a.2.2.1) := by ring
        simp only [eval_mul,eval_const,eval_sub,eval_atom]
        simp [Atom.eval,Atom.profile,Atom.withKind,Atom.reflect,h1]
        left
        congr 1
        ring
      · rename_i h h0 h1
        simp only [eval_sub,eval_const,eval_mul,eval_atom]
        simp [Atom.eval,Atom.withKind,Atom.profile,
          show a.2.2.2-2+4≠1 by omega,
          show a.2.2.2-2+3≠1 by omega]
  · simp_all

theorem diff_correct (e : Circuit) (j : Fin 4) (z : SpaceTime) :
    eval (diff j e) z = fderiv ℝ (eval e) z (spacetimeBasis j) := by
  induction e with
  | zero | succ | left | right => simp [diff,eval]
  | pair a b ha hb =>
      simp only [diff,eval_add,eval,fderiv_fun_add ((smooth a).differentiable (by simp) z)
        ((smooth b).differentiable (by simp) z),add_apply,ha,hb]
  | comp a b ha hb =>
      simp only [diff,eval_add,eval,fderiv_fun_mul ((smooth a).differentiable (by simp) z)
        ((smooth b).differentiable (by simp) z),add_apply,
        smul_apply,smul_eq_mul,ha,hb]
      ring
  | prec a b ha hb =>
      dsimp only [diff,eval]
      rw [atomDiff_eval]
      let v : Atom := data a
      have h := (Atom.profile_deriv v.2.2.2 ((v.2.1:ℝ)*coordinateLinear v.1 z+v.2.2.1)).comp_hasFDerivAt z
        (((coordinateLinear v.1).hasFDerivAt.const_mul (v.2.1:ℝ)).add_const (v.2.2.1:ℝ))
      change _ = fderiv ℝ (Atom.eval v) z (spacetimeBasis j)
      have hh : HasFDerivAt (Atom.eval v)
          (Atom.profileDerivative v.2.2.2 ((v.2.1:ℝ)*coordinateLinear v.1 z+v.2.2.1) •
            (v.2.1:ℝ) • coordinateLinear v.1) z := h
      rw [hh.fderiv]
      simp only [smul_apply,smul_eq_mul,coordinateLinear_basis]
      ring
  | rfind' a ha => simp [diff,eval]

theorem field_smooth (e : Fin 3 → Circuit) : Smooth (field e) :=
  contDiff_pi.mpr (fun j => smooth (e j))

theorem mixed_field (e : Fin 3 → Circuit) (α : List (Fin 4)) :
    mixedDerivative (field e) α = fun z j => eval (mixed (e j) α) z := by
  induction α with
  | nil => rfl
  | cons k α ih =>
      ext z j
      rw [mixedDerivative,ih]
      change (fderiv ℝ (fun z j => eval (mixed (e j) α) z) z (spacetimeBasis k)) j = _
      rw [fderiv_pi (fun i => (smooth (mixed (e i) α)).differentiable (by simp) z)]
      exact (diff_correct _ k z).symm

theorem eval_polynomial (p : ℚ[X]) (j : Fin 4) (a b : ℚ) (z : SpaceTime) :
    eval (polynomial p j a b) z = flatJet p ((a:ℝ)*coordinateLinear j z+b) := by
  simp only [polynomial,eval_suml,List.map_map,Function.comp_def,eval_mul,eval_const,eval_atom]
  simp only [Atom.eval,Atom.profile, show ∀ n : ℕ, n+2 ≠ 0 by omega,
    show ∀ n : ℕ, n+2 ≠ 1 by omega,ite_false,Nat.add_sub_cancel,flatMono,flatJet]
  simp only [Polynomial.map_pow,Polynomial.map_X,Polynomial.eval_pow,Polynomial.eval_X,
    ← mul_assoc]
  simp only [Finset.sum_map_toList, ← Finset.sum_mul]
  congr 1
  rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum]
  rfl

end Circuit
namespace JetExpr

theorem compile_correct (e : JetExpr) (j : Fin 4) (a b : ℚ) (z : SpaceTime) :
    Circuit.eval (e.compile j a b) z = e.eval ((a:ℝ)*coordinateLinear j z+b) := by
  induction e generalizing a b with
  | const q => simp [compile,eval]
  | id => simp [compile,eval,Atom.eval,Atom.profile]
  | add e f he hf => simp [compile,eval,he,hf]
  | mul e f he hf => simp [compile,eval,he,hf]
  | affine c d e he =>
      simp only [compile,eval,he,Rat.cast_add,Rat.cast_mul]
      congr 1
      ring
  | flat p => exact Circuit.eval_polynomial _ _ _ _ _
  | reciprocal => simp [compile,eval,Atom.eval,Atom.profile]

end JetExpr
namespace BoxExpr

theorem compile_correct (e : BoxExpr) (z : SpaceTime) :
    Circuit.eval e.compile z = e.eval z := by
  induction e with
  | const q => simp [compile,eval]
  | coord j e => simpa [compile,eval] using e.compile_correct j 1 0 z
  | add e f he hf => simp [compile,eval,he,hf]
  | mul e f he hf => simp [compile,eval,he,hf]

end BoxExpr
end Solenoidal

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.CircuitPrograms ----
namespace OAI

/-! SheetFlows circuit programs. -/

section
open Encodable Denumerable
namespace Solenoidal.Computing
open Nat.Partrec

theorem atom_argument : Primrec₂ Atom.argument :=
  rat_add.comp
    (rat_mul.comp (Primrec.fst.comp (Primrec.snd.comp .fst))
      (Primrec.fin_app.comp .snd (Primrec.fst.comp .fst)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .fst)))

theorem atom_bound : Primrec₂ Atom.bound := by
  let k : Atom×ℚ → ℕ := fun p => p.1.2.2.2
  have hk : Primrec k := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .fst))
  exact Primrec.ite (Primrec.eq.comp hk (.const 0))
    (rat_add.comp (rat_mul.comp (rat_abs.comp (Primrec.fst.comp (Primrec.snd.comp .fst)))
        (rat_abs.comp .snd)) (rat_abs.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .fst)))))
    (Primrec.ite (Primrec.eq.comp hk (.const 1)) (.const 16)
      (rat_nat.comp (nat_factorial.comp (Primrec.nat_sub.comp hk (.const 2)))))

theorem atom_approx : Primrec (fun p : Atom × (Fin 4 → ℚ) × ℕ => Atom.approx p.1 p.2.1 p.2.2) := by
  let k : Atom×(Fin 4 → ℚ)×ℕ → ℕ := fun p => p.1.2.2.2
  have hk : Primrec k := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .fst))
  have hq : Primrec (fun p : Atom×(Fin 4 → ℚ)×ℕ => Atom.argument p.1 p.2.1) :=
    atom_argument.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (fun p : Atom×(Fin 4 → ℚ)×ℕ => p.2.2) := Primrec.snd.comp .snd
  exact Primrec.ite (Primrec.eq.comp hk (.const 0)) (ball_point.comp hq)
    (Primrec.ite (Primrec.eq.comp hk (.const 1)) (ball_reciprocalApprox.comp hq hn)
      (ball_flatApprox.comp ((Primrec.nat_sub.comp hk (.const 2)).pair (hq.pair hn))))

theorem circuit_data {α : Type*} [Primcodable α] [Inhabited α] :
    Primrec (@Circuit.data α _ _) :=
  Primrec.option_getD_default.comp (Primrec.decode.comp Primrec.encode)

theorem circuit_const : Primrec Circuit.const :=
  Code.primrec_rfind'.comp ((Primrec.ofNat Code).comp Primrec.encode)

theorem circuit_atom : Primrec Circuit.atom :=
  Code.primrec₂_prec.comp ((Primrec.ofNat Code).comp Primrec.encode) (.const Code.zero)

theorem circuit_add : Primrec₂ Circuit.add := Code.primrec₂_pair
theorem circuit_mul : Primrec₂ Circuit.mul := Code.primrec₂_comp
theorem circuit_sub : Primrec₂ Circuit.sub :=
  circuit_add.comp .fst (circuit_mul.comp (.const (Circuit.const (-1))) .snd)

theorem circuit_bound : Primrec₂ Circuit.bound := by
  have h := Code.primrec_recOn' (α := Circuit×ℚ) (σ := ℚ) Primrec.fst
    (Primrec.const 0) (Primrec.const 0) (Primrec.const 0) (Primrec.const 0)
    (rat_add.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (rat_mul.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (atom_bound.comp (circuit_data.comp (Primrec.fst.comp .snd)) (Primrec.snd.comp .fst)).to₂
    (rat_abs.comp (circuit_data.comp (Primrec.fst.comp .snd))).to₂
  exact h.of_eq (fun p => by
    induction p.1 with
    | zero | succ | left | right => rfl
    | pair a b ha hb => simp [Circuit.bound,ha,hb]
    | comp a b ha hb => simp [Circuit.bound,ha,hb]
    | prec a b ha hb => rfl
    | rfind' a ha => rfl)

theorem circuit_approx : Primrec (fun p : Circuit×(Fin 4 → ℚ)×ℕ => Circuit.approx p.1 p.2.1 p.2.2) := by
  have h := Code.primrec_recOn' (α := Circuit×(Fin 4 → ℚ)×ℕ) (σ := QBall) Primrec.fst
    (Primrec.const (QBall.point 0)) (Primrec.const (QBall.point 0))
    (Primrec.const (QBall.point 0)) (Primrec.const (QBall.point 0))
    (ball_add.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (ball_mul.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (atom_approx.comp ((circuit_data.comp (Primrec.fst.comp .snd)).pair (Primrec.snd.comp .fst))).to₂
    (ball_point.comp (circuit_data.comp (Primrec.fst.comp .snd))).to₂
  exact h.of_eq (fun p => by
    induction p.1 with
    | zero | succ | left | right => rfl
    | pair a b ha hb => simp [Circuit.approx,ha,hb]
    | comp a b ha hb => simp [Circuit.approx,ha,hb]
    | prec a b ha hb => rfl
    | rfind' a ha => rfl)

theorem atom_withKind : Primrec₂ Atom.withKind :=
  (Primrec.fst.comp .fst).pair ((Primrec.fst.comp (Primrec.snd.comp .fst)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .fst))).pair .snd))

theorem atom_reflect : Primrec Atom.reflect :=
  Primrec.fst.pair ((rat_neg.comp (Primrec.fst.comp .snd)).pair
    ((rat_sub.comp (.const 1) (Primrec.fst.comp (Primrec.snd.comp .snd))).pair
      (Primrec.snd.comp (Primrec.snd.comp .snd))))

theorem circuit_atomDiff : Primrec₂ Circuit.atomDiff := by
  let k : Fin 4×Atom → ℕ := fun p => p.2.2.2.2
  have hk : Primrec k := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))
  have hat (f : Fin 4×Atom → Atom) (hf : Primrec f) (n : Fin 4×Atom → ℕ) (hn : Primrec n) :
      Primrec (fun p => Circuit.atom ((f p).withKind (n p))) :=
    circuit_atom.comp (atom_withKind.comp hf hn)
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp .snd) .fst)
    (circuit_mul.comp (circuit_const.comp (Primrec.fst.comp (Primrec.snd.comp .snd)))
      (Primrec.ite (Primrec.eq.comp hk (.const 0)) (.const (Circuit.const 1))
        (Primrec.ite (Primrec.eq.comp hk (.const 1))
          (circuit_mul.comp (.const (Circuit.const (-1)))
            (circuit_mul.comp (circuit_mul.comp (circuit_atom.comp .snd) (circuit_atom.comp .snd))
              (circuit_sub.comp (hat _ .snd _ (.const 4))
                (hat _ (atom_reflect.comp .snd) _ (.const 4)))))
          (circuit_sub.comp
            (hat _ .snd _ (Primrec.nat_add.comp (Primrec.nat_sub.comp hk (.const 2)) (.const 4)))
            (circuit_mul.comp (circuit_const.comp (rat_nat.comp (Primrec.nat_sub.comp hk (.const 2))))
              (hat _ .snd _ (Primrec.nat_add.comp (Primrec.nat_sub.comp hk (.const 2)) (.const 3))))))))
    (.const (Circuit.const 0))

theorem circuit_diff : Primrec₂ Circuit.diff := by
  have h := Code.primrec_recOn' (α := Fin 4×Circuit) (σ := Circuit) Primrec.snd
    (Primrec.const (Circuit.const 0)) (Primrec.const (Circuit.const 0))
    (Primrec.const (Circuit.const 0)) (Primrec.const (Circuit.const 0))
    (circuit_add.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))).to₂
    (circuit_add.comp
      (circuit_mul.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
        (Primrec.fst.comp (Primrec.snd.comp .snd)))
      (circuit_mul.comp (Primrec.fst.comp .snd)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))))).to₂
    (circuit_atomDiff.comp (Primrec.fst.comp .fst) (circuit_data.comp (Primrec.fst.comp .snd))).to₂
    (Primrec₂.const (Circuit.const 0))
  exact h.of_eq (fun p => by
    induction p.2 with
    | zero | succ | left | right => rfl
    | pair a b ha hb => simp [Circuit.diff,ha,hb]
    | comp a b ha hb => simp [Circuit.diff,ha,hb]
    | prec a b ha hb => rfl
    | rfind' a ha => rfl)

theorem circuit_mixed : Primrec₂ Circuit.mixed := by
  have h := Primrec.list_foldr (α := Circuit×List (Fin 4)) Primrec.snd Primrec.fst
    (circuit_diff.comp (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
  exact h.of_eq (fun p => by
    induction p.2 with
    | nil => rfl
    | cons j a ha => simp [Circuit.mixed,List.foldr,ha])

end Solenoidal.Computing
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

theorem HasRationalFormula.circuit {u : Field} (h : HasRationalFormula u) : HasCircuit u := by
  obtain ⟨e,he⟩ := h
  refine ⟨fun j => BoxExpr.compile (e j), ?_⟩
  intro z hz
  rw [he hz]
  ext j
  exact (BoxExpr.compile_correct (e j) z).symm

namespace Circuit

theorem jetBound_nonneg (e : Fin 3 → Circuit) (a : List (Fin 4)) : 0 ≤ jetBound e a :=
  Finset.sum_nonneg (fun _ _ => bound_nonneg _ _)

theorem wrapRat_correct (q : Fin 4 → ℚ) : ofRational (wrapRat q) =
    (Int.fract (ofRational q).1,wrapSpace (ofRational q).2) := by
  apply Prod.ext
  · simp [ofRational,wrapRat,Rat.cast_fract]
  · ext j
    fin_cases j <;> simp [ofRational,wrapRat,wrapSpace,Rat.cast_fract]

end Circuit

theorem circuit_periodic_jet {u : Field} (hu : Smooth u) (hx : SpatiallyPeriodic u)
    (ht : OnePeriodic u) {e : Fin 3 → Circuit}
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell)
    (a : List (Fin 4)) (z : SpaceTime) :
    mixedDerivative u a z = mixedDerivative (Circuit.field e) a (Int.fract z.1,wrapSpace z.2) := by
  have hp := periodic_field_reduction
    (mixedDerivative_spatially_periodic hu hx a) (mixedDerivative_onePeriodic hu ht a) z.1 z.2
  change mixedDerivative u a z = mixedDerivative u a (Int.fract z.1,wrapSpace z.2) at hp
  rw [hp]
  exact mixedDerivative_eqOn_cell hu (Circuit.field_smooth e) he a
    ⟨⟨Int.fract_nonneg _,(wrapSpace_mem z.2).1⟩,
      ⟨(Int.fract_lt_one _).le,(wrapSpace_mem z.2).2⟩⟩

theorem circuit_periodic_approx {u : Field} (hu : Smooth u) (hx : SpatiallyPeriodic u)
    (ht : OnePeriodic u) {e : Fin 3 → Circuit}
    (he : Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell)
    (a : List (Fin 4)) (q : Fin 4 → ℚ) (j : Fin 3) :
    QBall.Approximates (fun n => Circuit.jetApprox e a q n j)
      (mixedDerivative u a (Circuit.ofRational q) j) := by
  rw [circuit_periodic_jet hu hx ht he, Circuit.mixed_field,← Circuit.wrapRat_correct]
  exact Circuit.approximates _ _

namespace Computing

theorem fin_sum_rat {α : Type*} [Primcodable α] {n : ℕ} {f : α → Fin n → ℚ}
    (hf : ∀ i, Primrec (fun a => f a i)) : Primrec (fun a => ∑ i, f a i) := by
  induction n with
  | zero => simpa using (Primrec.const (0:ℚ) : Primrec (fun _ : α => (0:ℚ)))
  | succ n ih =>
    simpa [Fin.sum_univ_succ] using rat_add.comp (hf 0) (ih (fun i => hf i.succ))

theorem circuit_jetBound (e : Fin 3 → Circuit) : Primrec (Circuit.jetBound e) :=
  fin_sum_rat (fun j => circuit_bound.comp (circuit_mixed.comp (.const (e j)) .id) (.const 10))

theorem circuit_wrapRat : Primrec Circuit.wrapRat := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.mk
  exact rat_mul.comp
    (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1) (.const 10))
    (rat_sub.comp
      (rat_div.comp Primrec.fin_app
        (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1) (.const 10)))
      (rat_int.comp (rat_floor.comp (rat_div.comp Primrec.fin_app
        (Primrec.ite (Primrec.eq.comp .snd (.const 0)) (.const 1) (.const 10))))))

theorem circuit_jetApprox (e : Fin 3 → Circuit) :
    Primrec (fun p : List (Fin 4) × (Fin 4 → ℚ) × ℕ => Circuit.jetApprox e p.1 p.2.1 p.2.2) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.mk
  exact circuit_approx.comp
    ((circuit_mixed.comp (Primrec.fin_app.comp (.const e) .snd) (Primrec.fst.comp .fst)).pair
      ((circuit_wrapRat.comp (Primrec.fst.comp (Primrec.snd.comp .fst))).pair
        (Primrec.snd.comp (Primrec.snd.comp .fst))))

theorem partrec_code {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α →. β} (h : Partrec f) : ∃ c : Nat.Partrec.Code,
      ∀ a b, b ∈ f a → encode b ∈ c.eval (encode a) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp h
  refine ⟨c,fun a b hb => ?_⟩
  rw [hc]
  simp only [encodek,Part.coe_some,Part.bind_some]
  exact Part.mem_map encode hb

end Computing

theorem HasCircuit.effectiveBounds {u : Field} (h : HasCircuit u) (hu : Smooth u)
    (hx : SpatiallyPeriodic u) (ht : OnePeriodic u) : EffectiveBounds u := by
  obtain ⟨e,he⟩ := h
  obtain ⟨c,hc⟩ := Computing.partrec_code (Computing.circuit_jetBound e).to_comp.partrec
  refine ⟨c,fun a => ⟨Circuit.jetBound e a, hc a _ (Part.mem_some _),
    Circuit.jetBound_nonneg e a, circuit_periodic_bound hu hx ht he a⟩⟩

theorem jetLipschitz_nonneg {B : List (Fin 4) → ℚ} (h : ∀ a, 0 ≤ B a)
    (a : List (Fin 4)) : 0 ≤ jetLipschitz B a := Finset.sum_nonneg (fun _ _ => h _)

namespace Computing

theorem jetLipschitz_pr {B : List (Fin 4) → ℚ} (hB : Primrec B) : Primrec (jetLipschitz B) :=
  fin_sum_rat (fun j => hB.comp (Primrec.list_cons.comp (.const j) .id))

end Computing
end Solenoidal

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.EffectiveForcing ----
namespace OAI

/-! SheetFlows effective forcing. -/

section
open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal
namespace Computing

theorem readCode_pr {α : Type*} [Primcodable α] [Inhabited α] :
    Partrec₂ (@readCode α _ _) := by
  exact Nat.Partrec.Code.eval_part.map
    ((Primrec.option_getD_default.comp (Primrec.decode.comp .snd)).to_comp.to₂)

theorem readCode_mem {α : Type*} [Primcodable α] [Inhabited α]
    {c : Nat.Partrec.Code} {n : ℕ} {a : α} (h : encode a ∈ c.eval n) : a ∈ readCode c n := by
  unfold readCode
  have hh := Part.mem_map (fun k => (decode k).getD (default:α)) h
  simpa only [encodek,Option.getD_some] using hh

theorem precision_pr : Partrec₂ precision := by
  exact Partrec.rfind
    ((rat_lt.comp (rat_mul.comp (Primrec.fst.comp .fst)
      (rat_pow.comp (.const (1/2)) .snd))
      (rat_div.comp (Primrec.snd.comp .fst) (.const 2))).decide.to_comp.partrec.to₂)

theorem radiusSum_pr : Primrec radiusSum :=
  fin_sum_rat (fun j => Primrec.snd.comp (Primrec.fin_app.comp .id (.const j)))

theorem centers_pr : Primrec centers := by
  apply Primrec.fin_curry.mpr
  exact (Primrec.fst.comp Primrec.fin_app).to₂

theorem ballTest_pr : Primrec₂ ballTest :=
  (rat_lt.comp (radiusSum_pr.comp .snd) (rat_div.comp .fst (.const 2))).decide.to₂

theorem improve_pr {A : BallOracle} (hA : Partrec A) : Partrec (improve A) := by
  have ha : Partrec (fun p : (List (Fin 4) × RationalPoint × ℚ) × ℕ =>
      A (p.1.1,p.1.2.1,p.2)) :=
    hA.comp ((Primrec.fst.comp .fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp .fst)).pair .snd)).to_comp
  have hp : Partrec₂ (fun p : List (Fin 4) × RationalPoint × ℚ => fun n =>
      (A (p.1,p.2.1,n)).map (ballTest p.2.2)) :=
    (ha.map (ballTest_pr.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .fst)))
      .snd).to_comp.to₂).to₂
  exact (Partrec.rfind hp).bind
    (ha.map (centers_pr.comp .snd).to_comp.to₂).to₂

theorem evalJets_pr {B : List (Fin 4) → ℚ} (hB : Primrec B)
    {A : BallOracle} (hA : Partrec A) : Partrec (evalJets B A) := by
  have hn : Partrec (fun p : List (Fin 4) × Nat.Partrec.Code × ℚ =>
      precision (jetLipschitz B p.1) p.2.2) :=
    precision_pr.comp ((jetLipschitz_pr hB).comp .fst).to_comp (Primrec.snd.comp .snd).to_comp
  have hq : Partrec (fun p : (List (Fin 4) × Nat.Partrec.Code × ℚ) × ℕ =>
      @readCode RationalPoint _ _ p.1.2.1 p.2) :=
    readCode_pr.comp (Primrec.fst.comp (Primrec.snd.comp .fst)).to_comp Primrec.snd.to_comp
  exact hn.bind (hq.bind
    ((improve_pr hA).comp ((Primrec.fst.comp (Primrec.fst.comp .fst)).pair
      (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp .fst))))).to_comp).to₂).to₂

end Computing
end Solenoidal
end

section
open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal
namespace Computing

theorem precision_correct (L ε : ℚ) (hε : 0 < ε) :
    ∃ n, n ∈ precision L ε ∧ L*(1/2:ℚ)^n < ε/2 := by
  have hlim : Tendsto (fun n : ℕ => (L:ℝ)*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).const_mul (L:ℝ)
  have heps : (0:ℝ) < (ε:ℝ)/2 := by exact_mod_cast (div_pos hε (by norm_num : (0:ℚ)<2))
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds heps)).exists
  have hnq : L*(1/2:ℚ)^n < ε/2 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hn
  have hd : (precision L ε).Dom := Nat.rfind_dom.mpr
    ⟨n,by simpa only [Part.mem_some_iff,true_eq_decide_iff] using hnq,
      fun {_} _ => trivial⟩
  obtain ⟨k,hk⟩ := Part.dom_iff_mem.mp hd
  refine ⟨k,hk,?_⟩
  have hh := Nat.rfind_spec hk
  simpa only [Part.mem_some_iff,true_eq_decide_iff] using hh

theorem radiusSum_nonneg {b : BallVector} {v : Space} (h : ∀ j, (b j).Contains (v j)) :
    0 ≤ radiusSum b := Finset.sum_nonneg (fun j _ => QBall.radius_nonneg (h j))

theorem centers_error {b : BallVector} {v : Space} (h : ∀ j, (b j).Contains (v j)) :
    ‖(fun j => (centers b j:ℝ)) - v‖ ≤ (radiusSum b:ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast radiusSum_nonneg h)).mpr
  intro j
  exact (h j).trans (by exact_mod_cast
    Finset.single_le_sum (fun k _ => QBall.radius_nonneg (h k)) (Finset.mem_univ j))

theorem improve_correct {A : BallOracle} {u : Field} (hA : OracleCorrect A u)
    (a : List (Fin 4)) (q : RationalPoint) (ε : ℚ) (hε : 0 < ε) :
    ∃ r : Fin 3 → ℚ, r ∈ improve A (a,q,ε) ∧
      ‖(fun j => (r j:ℝ)) - mixedDerivative u a (Circuit.ofRational q)‖ < (ε:ℝ)/2 := by
  obtain ⟨b,hb,happrox⟩ := hA a q
  have hlim : Tendsto (fun n => (radiusSum (b n):ℝ)) atTop (𝓝 0) := by
    simpa [radiusSum] using tendsto_finsetSum Finset.univ (fun j _ => (happrox j).radius)
  have heps : (0:ℝ) < (ε:ℝ)/2 := by exact_mod_cast (div_pos hε (by norm_num : (0:ℚ)<2))
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds heps)).exists
  have hnq : radiusSum (b n) < ε/2 := by exact_mod_cast hn
  have htest (m : ℕ) : ballTest ε (b m) ∈ (A (a,q,m)).map (ballTest ε) :=
    Part.mem_map _ (hb m)
  have hd : (Nat.rfind (fun m => (A (a,q,m)).map (ballTest ε))).Dom := by
    apply Nat.rfind_dom.mpr
    refine ⟨n,?_,fun {m} _ => (htest m).1⟩
    simpa only [ballTest,decide_eq_true hnq] using htest n
  obtain ⟨k,hk⟩ := Part.dom_iff_mem.mp hd
  have heq : ballTest ε (b k) = true := Part.mem_unique (htest k) (Nat.rfind_spec hk)
  have he : radiusSum (b k) < ε/2 := of_decide_eq_true heq
  refine ⟨centers (b k),Part.mem_bind hk (Part.mem_map centers (hb k)),?_⟩
  exact (centers_error (fun j => (happrox j).contains k)).trans_lt (by exact_mod_cast he)

theorem ofRational_distance (q : RationalPoint) (z : SpaceTime) :
    ‖Circuit.ofRational q - z‖ = ‖(fun j => (q j:ℝ)) - flatten z‖ := by
  rw [← norm_flatten]
  congr 1
  ext j
  fin_cases j <;> rfl

theorem evalJets_correct {u : Field} (hu : Smooth u) {B : List (Fin 4) → ℚ}
    (hB : ∀ a, 0 ≤ B a) (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    {A : BallOracle} (hA : OracleCorrect A u)
    (a : List (Fin 4)) (c : Nat.Partrec.Code) (z : SpaceTime) (hc : NamesPoint c z)
    (ε : ℚ) (hε : 0 < ε) : ∃ r : Fin 3 → ℚ, r ∈ evalJets B A (a,c,ε) ∧
      ‖(fun j => (r j:ℝ)) - mixedDerivative u a z‖ < (ε:ℝ) := by
  obtain ⟨n,hn,hnlt⟩ := precision_correct (jetLipschitz B a) ε hε
  obtain ⟨q,hq,hqerr⟩ := hc n
  obtain ⟨r,hr,hrerr⟩ := improve_correct hA a q ε hε
  refine ⟨r,Part.mem_bind hn (Part.mem_bind (readCode_mem hq) hr),?_⟩
  have hdist : ‖Circuit.ofRational q-z‖ ≤ (1/2:ℝ)^n := by
    rwa [ofRational_distance]
  have hlip := mixed_lipschitz hu hB hb a (Circuit.ofRational q) z
  have herr : ‖mixedDerivative u a (Circuit.ofRational q) - mixedDerivative u a z‖ < (ε:ℝ)/2 := by
    apply hlip.trans_lt
    apply (mul_le_mul_of_nonneg_left hdist (by exact_mod_cast jetLipschitz_nonneg hB a)).trans_lt
    have hh : ((jetLipschitz B a * (1/2:ℚ)^n : ℚ):ℝ) < ((ε/2:ℚ):ℝ) :=
      Rat.cast_lt.mpr hnlt
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  calc
    ‖(fun j => (r j:ℝ)) - mixedDerivative u a z‖ ≤
        ‖(fun j => (r j:ℝ)) - mixedDerivative u a (Circuit.ofRational q)‖ +
        ‖mixedDerivative u a (Circuit.ofRational q) - mixedDerivative u a z‖ := by
          simpa only [dist_eq_norm] using dist_triangle
            (fun j => (r j:ℝ)) (mixedDerivative u a (Circuit.ofRational q))
            (mixedDerivative u a z)
    _ < (ε:ℝ)/2+(ε:ℝ)/2 := add_lt_add hrerr herr
    _ = _ := by ring

end Computing

theorem effective_of_oracle {u : Field} (hu : Smooth u) {B : List (Fin 4) → ℚ}
    (hBpr : Primrec B) (hB : ∀ a, 0 ≤ B a)
    (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    {A : Computing.BallOracle} (hApr : Partrec A) (hA : Computing.OracleCorrect A u) : Effective u := by
  obtain ⟨e,he⟩ := Computing.partrec_code (Computing.evalJets_pr hBpr hApr)
  refine ⟨e,fun a c z hc ε hε => ?_⟩
  obtain ⟨r,hr,herr⟩ := Computing.evalJets_correct hu hB hb hA a c z hc ε hε
  have hh := he (a,c,ε) r hr
  exact ⟨r,hh,herr⟩

end Solenoidal
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

theorem mixedDerivative_add {u v : Field} (hu : Smooth u) (hv : Smooth v) (a : List (Fin 4)) :
    mixedDerivative (u+v) a = mixedDerivative u a + mixedDerivative v a := by
  induction a with
  | nil => rfl
  | cons j a ih =>
    funext z
    rw [mixedDerivative,ih]
    dsimp only
    rw [fderiv_add ((mixedDerivative_contDiff hu a).differentiable (by simp) z)
      ((mixedDerivative_contDiff hv a).differentiable (by simp) z)]
    rfl

theorem mixedDerivative_smul {u : Field} (hu : Smooth u) (r : ℝ) (a : List (Fin 4)) :
    mixedDerivative (r • u) a = r • mixedDerivative u a := by
  induction a with
  | nil => rfl
  | cons j a ih =>
    funext z
    rw [mixedDerivative,ih]
    dsimp only
    rw [fderiv_const_smul ((mixedDerivative_contDiff hu a).differentiable (by simp) z)]
    rfl

theorem smooth_linear {u v : Field} (hu : Smooth u) (hv : Smooth v) (r : ℝ) :
    Smooth (u+r•v) := hu.add (hv.const_smul r)

theorem mixedDerivative_linear {u v : Field} (hu : Smooth u) (hv : Smooth v)
    (r : ℝ) (a : List (Fin 4)) :
    mixedDerivative (u+r•v) a = mixedDerivative u a + r • mixedDerivative v a := by
  rw [mixedDerivative_add (v := r • v) hu (hv.const_smul r),mixedDerivative_smul hv]

namespace Computing

theorem realBall_pr : Partrec₂ realBall :=
  (readCode_pr.map (Primrec.snd.pair
    (rat_pow.comp (.const (1/2)) (Primrec.snd.comp .fst))).to_comp.to₂)

theorem realBall_correct {c : Nat.Partrec.Code} {r : ℝ} (h : NamesReal c r) :
    ∃ b : ℕ → QBall, (∀ n, b n ∈ realBall c n) ∧ QBall.Approximates b r := by
  classical
  choose q hq he using h
  refine ⟨fun n => (q n,(1/2:ℚ)^n),fun n => Part.mem_map _ (readCode_mem (hq n)),?_,?_⟩
  · intro n
    simpa [QBall.Contains] using he n
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1))

theorem linearBalls_pr : Primrec (fun p : QBall × BallVector × BallVector => linearBalls p.1 p.2.1 p.2.2) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.mk
  exact ball_add.comp
    (Primrec.fin_app.comp (Primrec.fst.comp (Primrec.snd.comp .fst)) .snd)
    (ball_mul.comp (Primrec.fst.comp .fst)
      (Primrec.fin_app.comp (Primrec.snd.comp (Primrec.snd.comp .fst)) .snd))

theorem linearOracle_pr (c : Nat.Partrec.Code) {A B : BallOracle}
    (hA : Partrec A) (hB : Partrec B) : Partrec (linearOracle c A B) := by
  have hr : Partrec (fun p : JetRequest => realBall c p.2.2) :=
    realBall_pr.comp (.const c) (Primrec.snd.comp .snd).to_comp
  have ha : Partrec (fun p : JetRequest × QBall => A p.1) := hA.comp .fst
  have hb : Partrec (fun p : (JetRequest × QBall) × BallVector => B p.1.1) :=
    hB.comp (Primrec.fst.comp .fst).to_comp
  exact hr.bind (ha.bind (hb.map
    (linearBalls_pr.comp ((Primrec.snd.comp (Primrec.fst.comp .fst)).pair
      ((Primrec.snd.comp .fst).pair .snd))).to_comp.to₂).to₂).to₂

theorem linearOracle_correct {c : Nat.Partrec.Code} {r : ℝ} (hc : NamesReal c r)
    {u v : Field} (hu : Smooth u) (hv : Smooth v) {A B : BallOracle}
    (hA : OracleCorrect A u) (hB : OracleCorrect B v) :
    OracleCorrect (linearOracle c A B) (u+r•v) := by
  obtain ⟨br,hbr,hbrc⟩ := realBall_correct hc
  intro a q
  obtain ⟨bu,hbu,hbuc⟩ := hA a q
  obtain ⟨bv,hbv,hbvc⟩ := hB a q
  refine ⟨fun n => linearBalls (br n) (bu n) (bv n),fun n =>
    Part.mem_bind (hbr n) (Part.mem_bind (hbu n) (Part.mem_map _ (hbv n))),?_⟩
  intro j
  rw [mixedDerivative_linear hu hv]
  exact (hbuc j).add (hbrc.mul (hbvc j))

end Computing

theorem NamesReal.rationalBound {c : Nat.Partrec.Code} {r : ℝ} (h : NamesReal c r) :
    ∃ M : ℚ, 0 ≤ M ∧ |r| ≤ (M:ℝ) := by
  obtain ⟨q,hq,he⟩ := h 0
  refine ⟨|q|+1,by positivity,?_⟩
  have hh := abs_sub_comm (q:ℝ) r
  have ht : |r| ≤ |r-(q:ℝ)|+|(q:ℝ)| := by
    simpa using abs_add_le (r-(q:ℝ)) (q:ℝ)
  simp only [pow_zero] at he
  push_cast
  rw [← hh] at ht
  linarith

theorem linearBound_pr (M : ℚ) {B C : List (Fin 4) → ℚ} (hb : Primrec B) (hc : Primrec C) :
    Primrec (linearBound M B C) := Computing.rat_add.comp hb (Computing.rat_mul.comp (.const M) hc)

theorem linearBound_nonneg {M : ℚ} (hM : 0 ≤ M) {B C : List (Fin 4) → ℚ}
    (hb : ∀ a, 0 ≤ B a) (hc : ∀ a, 0 ≤ C a) (a : List (Fin 4)) :
    0 ≤ linearBound M B C a := add_nonneg (hb a) (mul_nonneg hM (hc a))

theorem linearBound_correct {u v : Field} (hu : Smooth u) (hv : Smooth v) {r : ℝ}
    {M : ℚ} (hM : |r| ≤ (M:ℝ)) {B C : List (Fin 4) → ℚ}
    (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    (hc : ∀ a z, ‖mixedDerivative v a z‖ ≤ (C a:ℝ)) (a : List (Fin 4)) (z : SpaceTime) :
    ‖mixedDerivative (u+r•v) a z‖ ≤ (linearBound M B C a:ℝ) := by
  rw [mixedDerivative_linear hu hv]
  apply (norm_add_le _ _).trans
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,linearBound,Rat.cast_add,Rat.cast_mul]
  exact add_le_add (hb a z) (mul_le_mul hM (hc a z) (norm_nonneg _)
    ((abs_nonneg r).trans hM))

theorem effectiveBounds_of_bound {u : Field} {B : List (Fin 4) → ℚ}
    (hpr : Primrec B) (hn : ∀ a, 0 ≤ B a) (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ)) :
    EffectiveBounds u := by
  obtain ⟨c,hc⟩ := Computing.partrec_code hpr.to_comp.partrec
  exact ⟨c,fun a => ⟨B a,hc a (B a) (Part.mem_some _),hn a,hb a⟩⟩

theorem HasCircuit.computable_linear {u v : Field} (hU : HasCircuit u) (hV : HasCircuit v)
    (hu : Smooth u) (hv : Smooth v) (hux : SpatiallyPeriodic u) (hvx : SpatiallyPeriodic v)
    (hut : OnePeriodic u) (hvt : OnePeriodic v) {r : ℝ} (hr : ComputableReal r) :
    Effective (u+r•v) ∧ EffectiveBounds (u+r•v) := by
  obtain ⟨c,hc⟩ := hr
  obtain ⟨M,hM,hMr⟩ := hc.rationalBound
  obtain ⟨e,he⟩ := hU
  obtain ⟨f,hf⟩ := hV
  let B := linearBound M (Circuit.jetBound e) (Circuit.jetBound f)
  have hBp : Primrec B := linearBound_pr M (Computing.circuit_jetBound e) (Computing.circuit_jetBound f)
  have hBn : ∀ a, 0 ≤ B a := linearBound_nonneg hM (Circuit.jetBound_nonneg e) (Circuit.jetBound_nonneg f)
  have hBb : ∀ a z, ‖mixedDerivative (u+r•v) a z‖ ≤ (B a:ℝ) :=
    linearBound_correct hu hv hMr (circuit_periodic_bound hu hux hut he) (circuit_periodic_bound hv hvx hvt hf)
  constructor
  · apply effective_of_oracle (smooth_linear hu hv r) hBp hBn hBb
      (Computing.linearOracle_pr c (Computing.circuit_jetApprox e).to_comp.partrec
        (Computing.circuit_jetApprox f).to_comp.partrec)
    apply Computing.linearOracle_correct hc hu hv
    · intro a q
      exact ⟨Circuit.jetApprox e a q,fun _ => Part.mem_some _,circuit_periodic_approx hu hux hut he a q⟩
    · intro a q
      exact ⟨Circuit.jetApprox f a q,fun _ => Part.mem_some _,circuit_periodic_approx hv hvx hvt hf a q⟩
  · exact effectiveBounds_of_bound hBp hBn hBb

theorem HasRationalFormula.directForce_effective {u : Field} (h : HasRationalFormula u)
    (hu : Smooth u) (hx : SpatiallyPeriodic u) (ht : OnePeriodic u) {ν : ℝ}
    (hν : ComputableReal ν) : Effective (globalDirectForce ν u) ∧ EffectiveBounds (globalDirectForce ν u) := by
  have hux : SpatiallyPeriodic (Solenoidal.fullTimePartial u) := by
    rw [fullTimePartial_eq_fieldDirectional hu]
    exact fieldDirectional_spatially_periodic hu hx _
  have hut : OnePeriodic (Solenoidal.fullTimePartial u) := by
    rw [fullTimePartial_eq_fieldDirectional hu]
    exact fieldDirectional_onePeriodic hu ht _
  have hvx : SpatiallyPeriodic ((-1:ℝ) • Solenoidal.laplacian u) := by
    intro t x k
    change (-1:ℝ) • (∑ j, Solenoidal.spatialPartial (Solenoidal.spatialPartial u j) j t (x+deck k)) =
      (-1:ℝ) • (∑ j, Solenoidal.spatialPartial (Solenoidal.spatialPartial u j) j t x)
    congr 1
    exact Finset.sum_congr rfl (fun j _ => spatialPartial_spatially_periodic
      (smooth_spatialPartial hu j) (spatialPartial_spatially_periodic hu hx j) j t x k)
  have hvt : OnePeriodic ((-1:ℝ) • Solenoidal.laplacian u) := by
    intro t x
    change (-1:ℝ) • (∑ j, Solenoidal.spatialPartial (Solenoidal.spatialPartial u j) j (t+1) x) =
      (-1:ℝ) • (∑ j, Solenoidal.spatialPartial (Solenoidal.spatialPartial u j) j t x)
    congr 1
    exact Finset.sum_congr rfl (fun j _ => spatialPartial_onePeriodic
      (smooth_spatialPartial hu j) (spatialPartial_onePeriodic hu ht j) j t x)
  have hV : HasCircuit ((-1:ℝ) • Solenoidal.laplacian u) := by
    simpa only [Rat.cast_neg, Rat.cast_one] using (((h.laplacian hu).smul (-1)).circuit)
  have hvs : Smooth ((-1:ℝ) • Solenoidal.laplacian u) :=
    (smooth_laplacian hu).const_smul (-1:ℝ)
  have hh := ((h.fullTimePartial hu).circuit).computable_linear
    hV (smooth_fullTimePartial hu) hvs hux hvx hut hvt hν
  have he : globalDirectForce ν u = Solenoidal.fullTimePartial u + ν • ((-1:ℝ) • Solenoidal.laplacian u) := by
    ext t x j
    simp [globalDirectForce,sub_eq_add_neg]
  rwa [← he] at hh

end Solenoidal

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.SheetProgram ----
namespace OAI

/-! SheetFlows sheet program. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem sheet_theorem {N : ℕ} (D : SheetData N) (ν : ℝ)
    (hν : 0 < ν) (hνcomp : ComputableReal ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧
      Smooth f ∧ Smooth u ∧ Effective f ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (fun _ _ => 0) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin N, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      EffectiveBounds f ∧ EffectiveBounds u ∧
      (N = 0 → f = 0 ∧ u = 0) := by
  cases N with
  | zero => exact sheet_theorem_empty D ν hν
  | succ N =>
      obtain ⟨δ,hδ,hδsmall,hs,ht⟩ := D.exists_rational_collar
      have hδsmall' : (δ:ℝ) ≤ 1/10 := by
        have hc : δ*10 ≤ 1 := (le_div_iff₀ (by norm_num)).mp hδsmall
        have hc' : (δ:ℝ)*10 ≤ 1 := by exact_mod_cast hc
        linarith
      let d : Collar := ⟨(δ:ℝ), by exact_mod_cast hδ, hδsmall'⟩
      let P := sheetProgram d D
      let v : Fin P.length → Space → Space := fun i => (P.get i).field
      obtain ⟨hfsp,husp,hfs,hus,hfm,_,hfd,_,hfp,hup,hsol,hcol,hadv,_,_⟩ :=
        scheduled_direct_forcing v (fun i => (P.get i).smooth)
          (fun i => (P.get i).periodic) (fun i => (P.get i).mean_zero)
          (fun i => (P.get i).divergence_zero) (fun i => (P.get i).nonlinear_zero) ν
      have hformula : HasRationalFormula (scheduleVelocity v) :=
        sheetVelocity_formula d ⟨δ,rfl⟩ D
      obtain ⟨heff,hbounds⟩ := hformula.directForce_effective hus husp hup hνcomp
      obtain ⟨hflow,hend⟩ := schedule_material_flow v (fun i => (P.get i).straight)
      refine ⟨globalDirectForce ν (scheduleVelocity v), scheduleVelocity v,
        fun t a => repeatedPath v a t, hfsp,husp,hfs,hus,heff,hfm,hfd,hfp,hsol,
        ?_,hflow,?_,hcol,hadv,hbounds,hformula.circuit.effectiveBounds hus husp hup,?_⟩
      · intro w p hw t ht x
        exact hsol.unique hw hν.le ht x
      · intro i y hy
        dsimp only
        rw [hend,stageState_list_eq P, sheetProgram_on d D hs ht i hy]
      · simp

end Solenoidal
end
end

end OAI

-- ---- mission target ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators

theorem solution {N : ℕ} (D : SheetData N) (ν : ℝ)
    (hν : 0 < ν) (hνcomp : ComputableReal ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧
      Smooth f ∧ Smooth u ∧ Effective f ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (fun _ _ => 0) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin N, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      EffectiveBounds f ∧ EffectiveBounds u ∧
      (N = 0 → f = 0 ∧ u = 0) := by
  first
    | exact OAI.Solenoidal.sheet_theorem D ν hν hνcomp
    | exact OAI.Solenoidal.sheet_theorem
    | (apply OAI.Solenoidal.sheet_theorem <;> assumption)
    | (intros; apply OAI.Solenoidal.sheet_theorem <;> assumption)
