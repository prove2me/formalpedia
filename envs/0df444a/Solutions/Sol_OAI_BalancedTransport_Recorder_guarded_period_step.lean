-- Prove2me | solution 1 for OAI.BalancedTransport.Recorder.guarded_period_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:45:54.90801+00:00
-- url     : https://prove2.me/submissions/7f715453-fecb-4253-8a23-06ebb67a80a2

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Bridge.lean:L146-L176
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Recorder.guarded_period_step. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_BalancedTransport_Geometry_repeatTemplate_eq

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.PrefixCoding ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*}

namespace Exec

variable {M : Machine Q Γ}

end Exec

variable (M : Machine Q Γ)
open Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

theorem prefix_mem_interval {r : ℝ} (hr : 0 ≤ r) (digit : S → ℝ)
    (w : List S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    prefixPoint r digit w z ∈ interval r digit w := by
  have hpow := pow_nonneg hr w.length
  dsimp [prefixPoint, interval]
  constructor
  · linarith [mul_nonneg hpow hz.1]
  · nlinarith [hz.2]

theorem replacement_prefix {r : ℝ} (hr : r ≠ 0) (digit : S → ℝ)
    (u v : List S) (z : ℝ) :
    replacement r digit u v (prefixPoint r digit u z) = prefixPoint r digit v z := by
  dsimp [replacement, prefixPoint]
  field_simp
  ring

theorem stream_mem_unit {B : ℕ} (digit : S → Fin B) (s : Stream' S) :
    stream digit s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem stream_cons {B : ℕ} (digit : S → Fin B) (a : S) (s : Stream' S) :
    stream digit (a :: s) = (B : ℝ)⁻¹ * ((digit a : ℝ) + stream digit s) := by
  have hh := Real.ofDigits_eq_sum_add_ofDigits (fun n => digit ((a :: s) n)) 1
  simpa [stream, Real.ofDigitsTerm, Stream'.cons, mul_add, mul_comm] using hh

theorem stream_append {B : ℕ} (digit : S → Fin B) (w : List S) (s : Stream' S) :
    stream digit (w ++ₛ s) =
      prefixPoint (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w (stream digit s) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [Stream'.appendStream', stream_cons, ih, prefix_cons]

theorem stream_append_mem_interval {B : ℕ} (digit : S → Fin B)
    (w : List S) (s : Stream' S) :
    stream digit (w ++ₛ s) ∈ interval (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w := by
  rw [stream_append]
  exact prefix_mem_interval (inv_nonneg.mpr (Nat.cast_nonneg _)) _ _ (stream_mem_unit _ _)

theorem replacement_stream {B : ℕ} (hB : B ≠ 0) (digit : S → Fin B)
    (u v : List S) (s : Stream' S) :
    replacement (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) u v (stream digit (u ++ₛ s)) =
      stream digit (v ++ₛ s) := by
  rw [stream_append, stream_append]
  exact replacement_prefix (inv_ne_zero (Nat.cast_ne_zero.mpr hB)) _ _ _ _

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

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

theorem codedPoint_mem_box {B : ℕ} (digit : S → Fin B) (o : Space)
    (u : Fin 3 → List S) (s : Fin 3 → Stream' S) :
    codedPoint digit o (fun i => u i ++ₛ s i) ∈
      box (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) o u := by
  intro i
  simpa only [codedPoint, add_sub_cancel_left] using
    stream_append_mem_interval digit (u i) (s i)

theorem boxMap_codedPoint {B : ℕ} (hB : B ≠ 0) (digit : S → Fin B) (o o' : Space)
    (u v : Fin 3 → List S) (s : Fin 3 → Stream' S) :
    boxMap (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) o o' u v
      (codedPoint digit o (fun i => u i ++ₛ s i)) =
      codedPoint digit o' (fun i => v i ++ₛ s i) := by
  funext i
  simp only [boxMap, codedPoint, add_sub_cancel_left]
  rw [replacement_stream hB]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

theorem base_pos : 0 < base Q Γ := by simp [base]

end BalancedTransport.Recorder
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Material ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

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

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set Metric

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

lemma loadedRepeat_after {load v : Velocity} (hl : TimeCollars load)
    {t : ℝ} (ht : 1 ≤ t) : loadedRepeat load v t = repeatTemplate v t := by
  have he : afterLoadingGate t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  ext x i
  simp [loadedRepeat, he, hl t (Or.inr (by linarith))]

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RecorderSimulation ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]
variable [DecidableEq Q]

theorem Instruction.fullMap_code (M : Machine Q Γ) (inst : Instruction Q Γ)
    (t : Tails Q Γ) :
    inst.fullMap M ((inst.source t).code M) = (inst.target t).code M := by
  let tails : Fin 3 → Stream' (Letter Q Γ) := ![t.left, t.right, t.history]
  have hs : (inst.source t).stacks = fun i => inst.sourcePrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  have ht : (inst.target t).stacks = fun i => inst.targetPrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  unfold fullMap Configuration.code
  rw [hs, ht]
  exact Coding.boxMap_codedPoint (Nat.ne_of_gt base_pos) _ _ _ _ _ _

theorem Instruction.source_code_mem (M : Machine Q Γ) (inst : Instruction Q Γ)
    (t : Tails Q Γ) :
    (inst.source t).code M ∈
      inst.sourceBox (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) := by
  let tails : Fin 3 → Stream' (Letter Q Γ) := ![t.left, t.right, t.history]
  have hs : (inst.source t).stacks = fun i => inst.sourcePrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  change Coding.codedPoint digit _ (inst.source t).stacks ∈ _
  rw [hs]
  exact Coding.codedPoint_mem_box _ _ _ _

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

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ] {M : Machine Q Γ}

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ]

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

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*} {M : Machine Q Γ}

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} {M : Machine Q Γ}
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set
open scoped NNReal

lemma IsMaterialFlow.shift_unit {U : Velocity} {X : MaterialFlow}
    (hX : IsMaterialFlow U X) (a : Space) {b : ℝ} (hb : 0 ≤ b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => X (s + b) a) (U (t + b) (X (t + b) a)) (Icc 0 1) t := by
  have hd := (hX.2 a (t + b) (add_nonneg ht.1 hb)).scomp t
    ((hasDerivAt_id t).add_const b).hasDerivWithinAt
    (show MapsTo (fun s : ℝ => s + b) (Icc 0 1) (Ici 0) from
      fun s hs => add_nonneg hs.1 hb)
  simpa only [Function.comp_def, one_smul, id_eq] using hd

lemma loadedRepeat_on_later_unit {load v : Velocity}
    (hl : TimeCollars load) (hv : TimeCollars v) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    loadedRepeat load v (t + ((n : ℝ) + 1)) = v t := by
  rw [loadedRepeat_after hl (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) n])]
  have hp := (repeatTemplate_zero_period v).nat_mul (n + 1) t
  simp only [Nat.cast_add, Nat.cast_one, mul_one] at hp
  rw [hp, repeatTemplate_on_unit hv ht]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q]
variable {M : Machine Q Γ} {v load : Velocity} {X : MaterialFlow} {L : ℝ≥0}

lemma guarded_period_step (hg : GuardedTemplate M v) (hv : TimeCollars v)
    (hl : TimeCollars load)
    (hLip : ∀ t, 0 ≤ t → LipschitzWith L (v t))
    (hX : IsMaterialFlow (loadedRepeat load v) X)
    {c d : Configuration Q Γ} (hcd : Step M c d) (n : ℕ) (a : Space)
    (hstart : X ((n : ℝ) + 1) a = c.code M) :
    X ((n : ℝ) + 2) a = d.code M ∧
      (d.control ≠ .ready M.halt → ∀ t ∈ Icc (0 : ℝ) 1,
        X (t + ((n : ℝ) + 1)) a ∉ observer) := by
  obtain ⟨r, hr, tails, rfl, rfl⟩ := hcd
  obtain ⟨γ, hγ₀, hγ₁, hdγ, hguard⟩ := hg r hr _
    ((r.instruction M).source_code_mem M tails)
  have hdX : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => X (s + ((n : ℝ) + 1)) a)
        (v s (X (s + ((n : ℝ) + 1)) a)) (Icc 0 1) s := by
    intro s hs
    have hh := Geometry.IsMaterialFlow.shift_unit hX a
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity) hs
    rwa [loadedRepeat_on_later_unit hl hv n hs] at hh
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, X (t + ((n : ℝ) + 1)) a = γ t := by
    intro t ht
    exact curves_agree_on_overlap hLip (HasDerivWithinAt.continuousOn hdX)
      (HasDerivWithinAt.continuousOn hdγ) hdX hdγ
      (by simpa only [zero_add] using hstart.trans hγ₀.symm) ht.1 ht.2 ht.2
  constructor
  · have he := (heq 1 ⟨by norm_num, le_rfl⟩).trans
      (hγ₁.trans ((r.instruction M).fullMap_code M tails))
    simpa only [show (1 : ℝ) + ((n : ℝ) + 1) = (n : ℝ) + 2 by ring] using he
  · intro hnh t ht
    rw [heq t ht]
    exact hguard hnh t ht

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open BalancedTransport.Geometry

end BalancedTransport.FiniteMachine
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal


theorem solution : type_of% @_root_.OAI.BalancedTransport.Recorder.guarded_period_step := @_root_.OAI.BalancedTransport.Recorder.guarded_period_step
