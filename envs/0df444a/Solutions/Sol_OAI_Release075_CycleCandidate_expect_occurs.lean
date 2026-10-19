-- Prove2me | solution 1 for OAI.Release075.CycleCandidate.expect_occurs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:08:45.521377+00:00
-- url     : https://prove2.me/submissions/667dceb5-2d8e-414e-87d0-6360dcfa29c4

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L224-L247
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.CycleCandidate.expect_occurs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_expect_selected_product

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

/-- The displayed upper count still has independent prescribed directions because
its candidate marks are distinct. -/
theorem expect_occurs [Fintype A] [Fintype (Projectivization K V)] [Nontrivial V]
    (c : CycleCandidate (K := K) S σ) :
    (𝔼 ω : S → Projectivization K V, if c.Occurs ω then (1 : ℝ) else 0) =
      (1 / Fintype.card (Projectivization K V) : ℝ) ^ Fintype.card A := by
  calc
    _ = 𝔼 ω : S → Projectivization K V,
        ∏ a, if ω (c.marks a) = c.direction a then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro ω _
      rw [Fintype.prod_boole]
      by_cases h : ∀ a : A, ω (c.marks a) = c.direction a
      · rw [ite_eq_left h]
        exact ite_eq_left h
      · rw [ite_eq_right h]
        exact ite_eq_right h
    _ = ∏ a, (𝔼 d : Projectivization K V, if d = c.direction a then (1 : ℝ) else 0) :=
      by
      exact expect_selected_product (D := Projectivization K V) c.marks
        (fun a d => if d = c.direction a then (1 : ℝ) else 0)
    _ = _ := by
      simp only [Fintype.expect_eq_sum_div_card, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, Finset.prod_const, Finset.card_univ]
end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.CycleCandidate
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.Release075.CycleCandidate.expect_occurs := @_root_.OAI.Release075.CycleCandidate.expect_occurs
