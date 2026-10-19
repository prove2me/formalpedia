-- Prove2me | solution 1 for OAI.Release075.expect_selected_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:06:00.549362+00:00
-- url     : https://prove2.me/submissions/f3176a0b-48db-4752-9092-93bc02579a92

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L128-L145
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.expect_selected_product. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

/-- Joint moments of any injectively selected coordinates. -/
theorem expect_selected_product {A I D : Type*} [Fintype A] [Fintype I]
    [DecidableEq I] [Fintype D] [Nonempty D]
    (e : A ↪ I) (f : A → D → ℝ) :
    (𝔼 ω : I → D, ∏ a, f a (ω (e a))) = ∏ a, 𝔼 d, f a d := by
  classical
  let F : I → D → ℝ := fun i d => Function.extend e (fun a => f a d) (fun _ => 1) i
  have hin (a : A) (d : D) : F (e a) d = f a d := e.injective.extend_apply _ _ _
  have hout (i : I) (hi : i ∉ Set.range e) (d : D) : F i d = 1 :=
    Function.extend_apply' _ _ _ hi
  have hprod (ω : I → D) : (∏ a, f a (ω (e a))) = ∏ i, F i (ω i) :=
    Fintype.prod_of_injective e e.injective _ _ (fun i hi => hout i hi _) (fun a => (hin _ _).symm)
  have hmean : (∏ a, 𝔼 d, f a d) = ∏ i, 𝔼 d, F i d := by
    apply Fintype.prod_of_injective e e.injective
    · intro i hi; simp only [hout i hi, Fintype.expect_const]
    · intro a; simp only [hin]
  simp_rw [hprod, hmean]
  exact expect_pi_product F

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


theorem solution : type_of% @_root_.OAI.Release075.expect_selected_product := @_root_.OAI.Release075.expect_selected_product
