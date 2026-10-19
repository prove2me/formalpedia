-- Prove2me | solution 1 for OAI.Release075.expect_two_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:02:58.294996+00:00
-- url     : https://prove2.me/submissions/5ebf8b5d-6185-468a-97d6-a252f7478aff

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L34-L53
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.expect_two_coordinates. The node keeps its source
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

/-- Distinct coordinate functions have a factorized second moment. -/
theorem expect_two_coordinates {I D : Type*} [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    (i j : I) (hij : i ≠ j) (f g : D → ℝ) :
    (𝔼 ω : I → D, f (ω i) * g (ω j)) = (𝔼 d, f d) * (𝔼 d, g d) := by
  classical
  let F : I → D → ℝ := fun k d =>
    (if k = i then f d else 1) * (if k = j then g d else 1)
  have hprod (ω : I → D) : (∏ k, F k (ω k)) = f (ω i) * g (ω j) := by
    simp only [F, Finset.prod_mul_distrib]
    simp
  have hmean (k : I) : (𝔼 d, F k d) =
      (if k = i then (𝔼 d, f d) else 1) * (if k = j then (𝔼 d, g d) else 1) := by
    by_cases hi : k = i
    · subst k; simp [F, hij]
    · by_cases hj : k = j
      · subst k; simp [F, hi]
      · simp [F, hi, hj]
  have h := expect_pi_product F
  simpa only [hprod, hmean, Finset.prod_mul_distrib,
    Finset.prod_ite_eq', Finset.mem_univ, ite_true] using h

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


theorem solution : type_of% @_root_.OAI.Release075.expect_two_coordinates := @_root_.OAI.Release075.expect_two_coordinates
