-- Prove2me | solution 1 for OAI.Release075.expect_centered_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:04:22.547856+00:00
-- url     : https://prove2.me/submissions/33f10682-9749-4acb-bfec-0457dc20ee14

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L76-L103
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.expect_centered_sum_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_expect_two_coordinates

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Independence of coordinates under the uniform average on a finite product. -/
theorem expect_pi_product {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D]
    (f : I → D → ℝ) :
    (𝔼 ω : I → D, ∏ i, f i (ω i)) = ∏ i, 𝔼 d, f i d := by
  classical
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

/-- A coordinate of a uniform product has the uniform marginal. -/
theorem expect_coordinate {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    (i : I) (f : D → ℝ) : (𝔼 ω : I → D, f (ω i)) = 𝔼 d, f d := by
  classical
  have h := expect_pi_product (fun j d => if j = i then f d else 1)
  have hm (j : I) : (𝔼 d, if j = i then f d else (1 : ℝ)) =
      if j = i then (𝔼 d, f d) else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simpa only [hm, Finset.prod_ite_eq', Finset.mem_univ, ite_true] using h

/-- Variance of a sum of independent coordinates, proved by a finite double sum. -/
theorem expect_centered_sum_sq {I D : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [Nonempty D] (b : I → D → ℝ) (p : I → ℝ)
    (hp : ∀ i, (𝔼 d, b i d) = p i) :
    (𝔼 ω : I → D, ((∑ i, b i (ω i)) - ∑ i, p i)^2) =
      ∑ i, (𝔼 d, (b i d - p i)^2) := by
  classical
  let X : I → D → ℝ := fun i d => b i d - p i
  have hzero (i : I) : (𝔼 d, X i d) = 0 := by
    simp [X, Finset.expect_sub_distrib, hp]
  have hcross (i j : I) :
      (𝔼 ω : I → D, X i (ω i) * X j (ω j)) =
      if i = j then (𝔼 d, (X i d)^2) else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [← sq]
      exact expect_coordinate i (fun d => (X i d)^2)
    · rw [ite_eq_right hij, expect_two_coordinates i j hij, hzero, zero_mul]
  calc
    _ = 𝔼 ω : I → D, ∑ i, ∑ j, X i (ω i) * X j (ω j) := by
      apply Finset.expect_congr rfl
      intro ω _
      rw [← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, 𝔼 ω : I → D, X i (ω i) * X j (ω j) := by
      rw [Finset.expect_sum_comm]
      congr 1; ext i
      rw [Finset.expect_sum_comm]
    _ = _ := by simp [hcross, X]

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

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
open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.Release075.expect_centered_sum_sq := @_root_.OAI.Release075.expect_centered_sum_sq
