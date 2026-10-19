-- Prove2me | solution 1 for OAI.BalancedTransport.Recorder.source_boxes_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:16:35.412121+00:00
-- url     : https://prove2.me/submissions/efb8a7fa-8c79-48fc-a5a7-67bffe82c342

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/BoxCoding.lean:L284-L310
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Recorder.source_boxes_disjoint. The node keeps its source
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
import Theorems.Thm_OAI_BalancedTransport_Coding_interval_eq_image
import Theorems.Thm_OAI_BalancedTransport_Coding_prefix_gap

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

end Exec

variable (M : Machine Q Γ)
open Letter Control

end BalancedTransport.Recorder
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

theorem disjoint_of_first_difference {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (p u v : List S) (a b : S) (hab : digit a + 1 < digit b) :
    Disjoint (interval r digit (p ++ a :: u)) (interval r digit (p ++ b :: v)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := prefix_gap hr digit hd₀ hd₁ p u v a b hx hy
  have hp : 0 < r ^ (p.length + 1) * (digit b - digit a - 1) :=
    mul_pos (pow_pos hr _) (by linarith)
  linarith

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

theorem first_difference {u v : List S} (hu : ¬ u.IsPrefix v) (hv : ¬ v.IsPrefix u) :
    ∃ p a b u' v', u = p ++ a :: u' ∧ v = p ++ b :: v' ∧ a ≠ b := by
  classical
  induction u generalizing v with
  | nil => exact False.elim (hu ⟨v, by simp⟩)
  | cons a u ih =>
      cases v with
      | nil => exact False.elim (hv ⟨a :: u, by simp⟩)
      | cons b v =>
          by_cases hab : a = b
          · subst b
            have hu' : ¬u.IsPrefix v := by
              rintro ⟨w, hw⟩
              exact hu ⟨w, by simpa using congrArg (List.cons a) hw⟩
            have hv' : ¬v.IsPrefix u := by
              rintro ⟨w, hw⟩
              exact hv ⟨w, by simpa using congrArg (List.cons a) hw⟩
            obtain ⟨p, b, c, u', v', hu'', hv'', hbc⟩ := ih hu' hv'
            exact ⟨a :: p, b, c, u', v', by simp [hu''], by simp [hv''], hbc⟩
          · exact ⟨[], a, b, u, v, rfl, rfl, hab⟩

theorem incompatible_intervals_disjoint {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    {u v : List S} (hu : ¬u.IsPrefix v) (hv : ¬v.IsPrefix u) :
    Disjoint (interval r digit u) (interval r digit v) := by
  obtain ⟨p, a, b, u', v', rfl, rfl, hab⟩ := first_difference hu hv
  rcases hgap a b hab with hab' | hba'
  · exact disjoint_of_first_difference hr digit hd₀ hd₁ p u' v' a b hab'
  · exact (disjoint_of_first_difference hr digit hd₀ hd₁ p v' u' b a hba').symm

theorem comparable_of_intersection {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    {u v : List S} {x : ℝ} (hu : x ∈ interval r digit u) (hv : x ∈ interval r digit v) :
    u.IsPrefix v ∨ v.IsPrefix u := by
  by_contra h
  push Not at h
  exact Set.disjoint_left.mp (incompatible_intervals_disjoint hr digit hd₀ hd₁ hgap h.1 h.2)
    hu hv

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem common_extensions (filler : S) {u v : List S}
    (h : u.IsPrefix v ∨ v.IsPrefix u) :
    ∃ s t : Stream' S, u ++ₛ s = v ++ₛ t := by
  rcases h with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · exact ⟨w ++ₛ Stream'.const filler, Stream'.const filler,
      (Stream'.append_append_stream _ _ _).symm⟩
  · exact ⟨Stream'.const filler, w ++ₛ Stream'.const filler,
      Stream'.append_append_stream _ _ _⟩

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

theorem control_eq_of_box_intersection {r : ℝ} (hr : 0 < r) (digit : S → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    {k l : ℕ} {u v : Fin 3 → List S} {x : Space}
    (hu : x ∈ box r digit (origin k) u) (hv : x ∈ box r digit (origin l) v) : k = l := by
  have hu' := interval_subset_unit hr digit hd₀ hd₁ (u 0) (hu 0)
  have hv' := interval_subset_unit hr digit hd₀ hd₁ (v 0) (hv 0)
  simp only [origin, Matrix.cons_val_zero, Set.mem_Icc] at hu' hv'
  rcases lt_trichotomy k l with h | h | h
  · have h' : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast h
    linarith [hu'.2, hv'.1]
  · exact h
  · have h' : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h
    linarith [hv'.2, hu'.1]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}

theorem source_boxes_disjoint [DecidableEq Q] [DecidableEq Γ] (M : Machine Q Γ)
    {r : ℝ} (hr : 0 < r) (digit : Letter Q Γ → ℝ)
    (hd₀ : ∀ a, 0 ≤ digit a) (hd₁ : ∀ a, r * (digit a + 1) ≤ 1)
    (hgap : ∀ a b, a ≠ b → digit a + 1 < digit b ∨ digit b + 1 < digit a)
    (id : Control Q → ℕ) (hid : Function.Injective id)
    {a b : Row Q Γ} (ha : a.valid M) (hb : b.valid M) (hab : a ≠ b) :
    Disjoint ((a.instruction M).sourceBox r digit id)
      ((b.instruction M).sourceBox r digit id) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hcontrol : (a.instruction M).sourceControl = (b.instruction M).sourceControl :=
    hid (Coding.control_eq_of_box_intersection hr digit hd₀ hd₁ hx hy)
  have hi : ∀ i : Fin 3,
      ((a.instruction M).sourcePrefixes i).IsPrefix ((b.instruction M).sourcePrefixes i) ∨
      ((b.instruction M).sourcePrefixes i).IsPrefix ((a.instruction M).sourcePrefixes i) := by
    intro i
    apply Coding.comparable_of_intersection hr digit hd₀ hd₁ hgap (hx i)
    simpa only [Instruction.sourceBox, hcontrol] using hy i
  choose s t he using fun i => Coding.common_extensions (Letter.boundary : Letter Q Γ) (hi i)
  have heq : (a.instruction M).source ⟨s 0, s 1, s 2⟩ =
      (b.instruction M).source ⟨t 0, t 1, t 2⟩ := by
    dsimp [Instruction.source]
    congr 1
    · exact he 0
    · exact he 1
    · exact he 2
  exact hab (source_separation M ha hb heq).1

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

end BalancedTransport.Recorder
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Recorder


theorem solution : type_of% @_root_.OAI.BalancedTransport.Recorder.source_boxes_disjoint := @_root_.OAI.BalancedTransport.Recorder.source_boxes_disjoint
