-- Prove2me | solution 1 for OAI.SquareRootDegree.Observations.grouped_score
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:19:10.333922+00:00
-- url     : https://prove2.me/submissions/a9bc5f88-0b6e-4d45-84d7-edaac94a8218

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Observations.lean:L62-L81
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.Observations.grouped_score. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations

-- ---- from OAI.Combinatorics.BooleanFunctions.Walsh ----
namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Finite Walsh calculus -/

theorem average_sum {α κ : Type*} [Fintype α] (s : Finset κ) (f : κ → α → ℝ) :
    average (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### Degree calculus for finite observations -/

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Conditioning ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Uniform finite conditioning, without measure-theoretic assumptions -/

theorem average_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    average f = average (fun x => average (fun y => f (x,y))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_update {ι α : Type*} [DecidableEq ι] [Fintype ι] [Fintype α] [Nonempty α]
    (f : (ι → α) → ℝ) (i : ι) :
    average (fun x => average (fun a => f (Function.update x i a))) = average f := by
  classical
  have h := average_equiv (updateSwap (α := α) i) (fun p => f p.1)
  rw [average_prod, average_prod] at h
  simpa [updateSwap, average_const] using h

theorem cellMoment_eq_zero_of_mass_eq_zero {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) (h : cellMass F b = 0) :
    cellMoment F g b = 0 := by
  classical
  have hc : ∀ x, cell F b x = 0 := by
    intro x
    have hs : ∑ x, cell F b x = 0 := by
      unfold cellMass average at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by unfold cell; split <;> norm_num)).mp hs x (Finset.mem_univ x)
  simp [cellMoment, hc]

theorem mass_mul_conditionalValue {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) :
    cellMass F b * conditionalValue F g b = cellMoment F g b := by
  by_cases h : cellMass F b = 0
  · simp [h, cellMoment_eq_zero_of_mass_eq_zero F g b h]
  · simp [conditionalValue, field]

theorem average_mul_comp_eq_sum {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β) (g : α → ℝ) (h : β → ℝ) :
    average (fun x => h (F x) * g x) = ∑ b, h b * cellMoment F g b := by
  classical
  simp only [cellMoment, ← average_const_mul, ← average_sum]
  congr 1
  funext x
  simp [cell]

theorem cellMoment_conditionalAverage {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) :
    cellMoment F (conditionalAverage F g) b = cellMoment F g b := by
  have he : (fun x => cell F b x * conditionalAverage F g x) =
      (fun x => cell F b x * conditionalValue F g b) := by
    funext x
    unfold cell conditionalAverage
    split_ifs with h
    · rw [h]
    · simp
  rw [cellMoment, he, average_mul_const]
  exact mass_mul_conditionalValue F g b

theorem conditionalAverage_projection {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) (h : β → ℝ) :
    average (fun x => h (F x) * conditionalAverage F g x) =
      average (fun x => h (F x) * g x) := by
  rw [average_mul_comp_eq_sum, average_mul_comp_eq_sum]
  simp only [cellMoment_conditionalAverage]

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Projection ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Projection
attribute [local instance] Classical.propDecidable
variable {α β γ κ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype γ]

omit [Nonempty α] [Fintype β] in
/-- Conditional averages are characterized by their cell moments. -/
theorem conditional_eq_of_projection (F : α → β) (g h : α → ℝ)
    (hp : ∀ p : β → ℝ, average (fun x => p (F x)*g x) = average (fun x => p (F x)*h x)) :
    conditionalAverage F g = conditionalAverage F h := by
  funext x
  unfold conditionalAverage conditionalValue cellMoment
  congr 1
  exact hp (cell id (F x))

omit [Fintype γ] in
theorem pi_projection [Fintype κ] [DecidableEq κ] (F : α → β) (g : α → ℝ)
    (p : (κ → β) → ℝ) (j : κ) :
    average (fun x : κ → α => p (fun i => F (x i))*g (x j)) =
      average (fun x : κ → α => p (fun i => F (x i))*conditionalAverage F g (x j)) := by
  rw [← average_update _ j,← average_update (fun x : κ → α =>
    p (fun i => F (x i))*conditionalAverage F g (x j)) j]
  congr 1
  funext x
  have he (a : α) : (fun i => F (Function.update x j a i)) =
      Function.update (fun i => F (x i)) j (F a) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  simp only [he,Function.update_self]
  exact (conditionalAverage_projection F g
    (fun b => p (Function.update (fun i => F (x i)) j b))).symm

omit [Fintype γ] in
theorem pi_conditional_sum [Fintype κ] [DecidableEq κ]
    (F : α → β) (H : (κ → β) → γ) (g : α → ℝ) :
    conditionalAverage (fun x : κ → α => H (fun i => F (x i)))
      (fun x => ∑ i, g (x i)) =
    conditionalAverage (fun x : κ → α => H (fun i => F (x i)))
      (fun x => ∑ i, conditionalAverage F g (x i)) := by
  apply conditional_eq_of_projection
  intro p
  simp only [Finset.mul_sum,average_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact pi_projection F g (p ∘ H) j

omit [Nonempty α] [Fintype β] [Fintype γ] in
theorem conditional_equiv {δ : Type*} [Fintype δ] (e : α ≃ δ)
    {ε : Type*} (F : δ → ε) (g : δ → ℝ) :
    conditionalAverage (F ∘ e) (g ∘ e) = conditionalAverage F g ∘ e := by
  funext x
  unfold conditionalAverage conditionalValue cellMoment cellMass
  have hm := average_equiv e (cell F (F (e x)))
  have hg := average_equiv e (fun y => cell F (F (e x)) y*g y)
  exact congrArg₂ (fun a b : ℝ => a/b) hg hm

end Projection
end SquareRootDegree

namespace SquareRootDegree
namespace Projection
attribute [local instance] Classical.propDecidable

variable {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conditional_tuple_sum (F : α → β) (g : α → ℝ) :
    conditionalAverage (fun x : ι → α => fun i => F (x i)) (fun x => ∑ i, g (x i)) =
      fun x => ∑ i, conditionalAverage F g (x i) := by
  have hp := pi_conditional_sum (κ := ι) F id g
  simp only [id_eq] at hp
  rw [hp]
  exact conditional_comp (fun x : ι → α => fun i => F (x i))
    (fun b => ∑ i, conditionalValue F g (b i))

end Projection
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Observations ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable

variable {γ β κ : Type*} [Fintype γ] [Fintype β] [Fintype κ]
  [DecidableEq γ] [DecidableEq κ]

omit [Fintype β] [DecidableEq γ] [DecidableEq κ] in
theorem cubeSum_block (x : Cube (κ × γ)) :
    cubeSum x = ∑ j, cubeSum (fun i => x (j,i)) := by
  exact Fintype.sum_prod_type _

theorem grouped_score (F : Cube γ → β) :
    score (grouped (κ := κ) F) = fun x => ∑ j, score F (fun i => x (j,i)) := by
  let e := blockCurry κ γ Bool
  let G : (κ → Cube γ) → (κ → β) := fun x j => F (x j)
  let R : (κ → Cube γ) → ℝ := fun x => ∑ j, cubeSum (x j)
  have he : cubeSum (γ := κ × γ) = R ∘ e := by funext x; exact cubeSum_block x
  have hp := Projection.conditional_tuple_sum (ι := κ) F cubeSum
  have hc := Projection.conditional_equiv e G R
  have hscore : conditionalAverage (G ∘ e) (cubeSum (γ := κ × γ)) =
      (fun x => ∑ j, conditionalAverage F cubeSum (x j)) ∘ e := by
    rw [he,hc]
    exact congrArg (fun p => p ∘ e) hp
  convert hscore using 1
  · unfold score
    congr 1
  · unfold score
    funext x
    apply Finset.sum_congr rfl
    intro j _
    congr 1

end Observations
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.Observations
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
variable {γ β κ : Type*} [Fintype γ] [Fintype β] [Fintype κ]
  [DecidableEq γ] [DecidableEq κ]

theorem solution (F : Cube γ → β) :
    score (grouped (κ := κ) F) = fun x => ∑ j, score F (fun i => x (j,i)) := by
  first
    | exact OAI.SquareRootDegree.Observations.grouped_score F
    | exact OAI.SquareRootDegree.Observations.grouped_score
    | (apply OAI.SquareRootDegree.Observations.grouped_score <;> assumption)
    | (intros; apply OAI.SquareRootDegree.Observations.grouped_score <;> assumption)
