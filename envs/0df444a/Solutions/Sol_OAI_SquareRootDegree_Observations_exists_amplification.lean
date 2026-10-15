-- Prove2me | solution 1 for OAI.SquareRootDegree.Observations.exists_amplification
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:39:25.350829+00:00
-- url     : https://prove2.me/submissions/ba3676aa-b57f-4403-94e1-f3e4612b4bf0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Grouping.lean:L70-L99
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.Observations.exists_amplification. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_CellDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Grouping
import Theorems.Thm_OAI_SquareRootDegree_FiniteMoments_normalized_product_centered_sq
import Theorems.Thm_OAI_SquareRootDegree_Observations_grouped_score
import Theorems.Thm_OAI_SquareRootDegree_Producer_exists_table_gain
import Theorems.Thm_OAI_SquareRootDegree_Switching_full_conditional_sum

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

theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_sum {α κ : Type*} [Fintype α] (s : Finset κ) (f : κ → α → ℝ) :
    average (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ average f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun x _ => h x)

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

theorem average_conditionalAverage {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) : average (conditionalAverage F g) = average g := by
  simpa using conditionalAverage_projection F g (fun _ => 1)

theorem conditionalAverage_lower_bound {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) (p : β → ℝ) :
    average (fun x => g x ^ 2) - average (fun x => (g x - p (F x)) ^ 2) ≤
      average (fun x => conditionalAverage F g x ^ 2) := by
  have h := average_nonneg (fun x => sq_nonneg (conditionalAverage F g x - p (F x)))
  have he : (fun x => (conditionalAverage F g x - p (F x)) ^ 2) =
      (fun x => conditionalAverage F g x ^ 2 - 2 * (p (F x) * conditionalAverage F g x) +
        p (F x) ^ 2) := by funext x; ring
  have he' : (fun x => (g x - p (F x)) ^ 2) =
      (fun x => g x ^ 2 - 2 * (p (F x) * g x) + p (F x) ^ 2) := by funext x; ring
  rw [he, average_add, average_sub, average_const_mul, conditionalAverage_projection] at h
  rw [he', average_add, average_sub, average_const_mul]
  linarith

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Blocks ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Disjoint blocks and finite observation degree calculus -/

attribute [local instance] Classical.propDecidable

theorem average_pi_prod {κ α : Type*} [Fintype κ] [Fintype α] (f : κ → α → ℝ) :
    average (fun x : κ → α => ∏ i, f i (x i)) = ∏ i, average (f i) := by
  simp only [average, Fintype.card_fun, Nat.cast_pow, inv_pow, ← Fintype.prod_sum,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem average_pi_eval {κ α : Type*} [Fintype κ] [Fintype α] [Nonempty α]
    (j : κ) (f : α → ℝ) : average (fun x : κ → α => f (x j)) = average f := by
  have he := average_pi_prod (fun i a => if i = j then f a else 1)
  have hif (i : κ) : average (fun a : α => if i = j then f a else 1) =
      if i = j then average f else 1 := by
    split_ifs <;> simp_all [average_const]
  simpa [Finset.prod_ite_eq, hif] using he

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

omit [Nonempty α] [Fintype β] in
theorem conditional_const_mul (F : α → β) (g : α → ℝ) (c : ℝ) :
    conditionalAverage F (fun x => c*g x) = fun x => c*conditionalAverage F g x := by
  funext x
  unfold conditionalAverage conditionalValue cellMoment
  simp_rw [show ∀ y, cell F (F x) y*(c*g y) = c*(cell F (F x) y*g y) by intros; ring]
  rw [average_const_mul]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Projection
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.FiniteCLT ----
namespace OAI

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace SquareRootDegree
namespace FiniteCLT
attribute [local instance] Classical.propDecidable

variable {α : Type*} [MeasurableSpace α]

end FiniteCLT
end SquareRootDegree

namespace SquareRootDegree
namespace UniformFinite
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem average_pi_eval_any {κ : Type*} [Fintype κ] [DecidableEq κ]
    (j : κ) (f : α → ℝ) : average (fun x : κ → α => f (x j)) = average f := by
  convert average_pi_eval j f using 1
  congr 1
  exact Subsingleton.elim _ _

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem centered_sq_any {κ : Type*} [Fintype κ] [DecidableEq κ] (T : α → ℝ)
    (h0 : average T = 0) :
    average (fun x : κ → α => (∑ i, T (x i))^2) = ∑ _ : κ, average (fun a => (T a)^2) := by
  have h := FiniteMoments.normalized_product_centered_sq
    (fun (_ : κ) (_ : α) => (1:ℝ)) (fun _ => average_const 1)
    (fun _ => T) (by simpa using fun (_ : κ) => h0)
  simp only [Finset.prod_const_one,one_mul] at h
  convert h using 1
  congr 1
  exact Subsingleton.elim _ _

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem average_normalizedSum (T : α → ℝ) (h0 : average T = 0) (n : ℕ) :
    average (FiniteCLT.normalizedSum T n) = 0 := by
  unfold FiniteCLT.normalizedSum
  rw [average_const_mul,average_sum]
  simp only [average_pi_eval_any,h0,Finset.sum_const_zero,mul_zero]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem average_normalizedSum_sq (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) {n : ℕ} (hn : 0 < n) :
    average (fun x => (FiniteCLT.normalizedSum T n x)^2) = 1 := by
  have h := centered_sq_any (κ := Fin n) T h0
  simp only [h1,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  simp only [FiniteCLT.normalizedSum,mul_pow,average_const_mul,h,inv_pow]
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  exact inv_mul_cancel₀ (show (n:ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

end UniformFinite
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

omit [Fintype β] [Fintype κ] in
theorem cubeSum_zero : average (cubeSum (γ := γ)) = 0 := by
  unfold cubeSum
  rw [average_sum]
  have hz : average sign = 0 := by norm_num [average,sign,Fintype.sum_bool]
  have hi (i : γ) : average (fun x : Cube γ => sign (x i)) = 0 := by
    calc _ = average sign := by
           convert average_pi_eval i sign using 1
           congr 1
           exact Subsingleton.elim _ _
      _ = 0 := hz
  simp only [hi,Finset.sum_const_zero]

omit [Fintype κ] in
theorem score_zero (F : Cube γ → β) : average (score F) = 0 := by
  rw [score,average_conditionalAverage]
  exact cubeSum_zero

omit [Fintype β] [DecidableEq γ] [DecidableEq κ] in
theorem cubeSum_block (x : Cube (κ × γ)) :
    cubeSum x = ∑ j, cubeSum (fun i => x (j,i)) := by
  exact Fintype.sum_prod_type _

omit [Fintype β] [Fintype κ] [DecidableEq κ] in
theorem variance_nonneg (F : Cube γ → β) : 0 ≤ variance F :=
  average_nonneg (fun _ => sq_nonneg _)

omit [Fintype κ] [DecidableEq κ] in
theorem standard_zero (F : Cube γ → β) : average (standard F) = 0 := by
  change average (fun x => (Real.sqrt (variance F))⁻¹*score F x) = 0
  rw [average_const_mul,score_zero,mul_zero]

omit [Fintype β] [Fintype κ] [DecidableEq κ] in
theorem standard_sq (F : Cube γ → β) (hv : 0 < variance F) :
    average (fun x => (standard F x)^2) = 1 := by
  change average (fun x => ((Real.sqrt (variance F))⁻¹*score F x)^2) = 1
  simp only [mul_pow,average_const_mul,inv_pow]
  rw [Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

end Observations
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Switching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι] [DecidableEq ι]

omit [Fintype β] [Fintype ι] in
theorem average_prod_add_sq {δ : Type*} [Fintype δ] [Nonempty δ]
    (f : α → ℝ) (g : δ → ℝ) :
    average (fun x : α × δ => (f x.1+g x.2)^2) =
      average (fun x => (f x)^2)+2*average f*average g+average (fun y => (g y)^2) := by
  have he : (fun x : α × δ => (f x.1+g x.2)^2) =
      fun x => (f x.1)^2+2*f x.1*g x.2+(g x.2)^2 := by funext x; ring
  rw [he,average_prod]
  simp only [average_add,average_const,average_const_mul,average_mul_const]

omit [Fintype β] in
theorem oldSum_sq (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    average (fun x : EventSpace α ι => (oldSum T x)^2) = Fintype.card ι+1 := by
  have h := FiniteMoments.normalized_product_centered_sq
    (fun (_ : ι) (_ : α) => (1:ℝ)) (fun _ => average_const 1)
    (fun _ => T) (by simpa using fun (_ : ι) => h0)
  simp only [Finset.prod_const_one,one_mul,h1,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  have h' : average (fun x : ι → α => (∑ i, T (x i))^2) = (Fintype.card ι : ℝ) := by
    convert h using 1
    congr 1
    exact Subsingleton.elim _ _
  simp only [oldSum]
  rw [average_prod_add_sq T (fun z : ι → α => ∑ i, T (z i)),h0,h1,h']
  ring

omit [Fintype β] in
theorem totalSum_sq (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    average (fun x : FullSpace α ι => (totalSum T x)^2) = Fintype.card ι+2 := by
  simp only [totalSum]
  rw [average_prod_add_sq,oldSum_sq T h0 h1,h0,h1]
  ring

omit [Fintype β] in
theorem prediction_error (F : α → β) (A : EventSpace β ι → Prop)
    (T : α → ℝ) (t : β → ℝ) (ht : ∀ a, t (F a) = T a) (b : ℝ)
    (h1 : average (fun a => (T a)^2) = 1) :
    average (fun x : FullSpace α ι => (totalSum T x-predictor t b (observation F A x))^2) =
      1-SoftEvent.deficit T b (fun z => if A (oldLabels F z) then 1 else 0) := by
  have he (z : EventSpace α ι) (w : α) :
      (totalSum T (z,w)-predictor t b (observation F A (z,w)))^2 =
      if A (oldLabels F z) then (oldSum T z-b)^2 else (T w)^2 := by
    by_cases ha : A (oldLabels F z)
    · have ho : observation F A (z,w) = Sum.inr (F w) := ite_eq_left ha
      rw [ho,ite_eq_left ha]
      simp only [predictor,Sum.elim_inr,totalSum,ht]
      congr 1; ring
    · have ho : observation F A (z,w) = Sum.inl (oldLabels F z) := ite_eq_right ha
      rw [ho,ite_eq_right ha]
      simp only [predictor,Sum.elim_inl,totalSum,oldSum,oldLabels,ht]
      congr 1; ring
  rw [average_prod]
  simp_rw [he]
  have hi (z : EventSpace α ι) :
      average (fun w : α => if A (oldLabels F z) then (oldSum T z-b)^2 else (T w)^2) =
      1-(if A (oldLabels F z) then 1 else 0)*(1-(oldSum T z-b)^2) := by
    by_cases ha : A (oldLabels F z) <;> simp [ha,average_const,h1]
  simp_rw [hi]
  rw [average_sub,average_const]
  unfold SoftEvent.deficit
  congr 1
  congr 1
  exact Subsingleton.elim _ _

theorem retained_gain (F : α → β) (A : EventSpace β ι → Prop)
    (T : α → ℝ) (t : β → ℝ) (ht : ∀ a, t (F a) = T a) (b c : ℝ)
    (h0 : average T = 0) (h1 : average (fun a => (T a)^2) = 1)
    (hc : c < SoftEvent.deficit T b (fun z => if A (oldLabels F z) then 1 else 0)) :
    Fintype.card ι+1+c < average (fun x => (conditionalAverage (observation F A) (totalSum T) x)^2) := by
  have h := conditionalAverage_lower_bound (observation F A) (totalSum T) (predictor t b)
  rw [totalSum_sq T h0 h1,prediction_error F A T t ht b h1] at h
  linarith

end Switching
end SquareRootDegree

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι]

omit [Fintype α] [Nonempty α] [Fintype β] in
theorem sum_full (T : α → ℝ) (x : Slots ι → α) :
    (∑ j, T (x j)) = totalSum T (fullEquiv α ι x) := by
  simp only [Fintype.sum_option,totalSum,oldSum,fullEquiv,Equiv.coe_fn_mk]
  ring

end Switching
end SquareRootDegree

namespace SquareRootDegree
namespace Switching
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype ι] [DecidableEq ι]

end Switching
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.CellDegree ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace CellDegree
attribute [local instance] Classical.propDecidable
variable {γ β ι : Type*} [Fintype γ] [Fintype β] [Fintype ι]

end CellDegree
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
open Switching
attribute [local instance] Classical.propDecidable
variable {γ β ι : Type*} [Fintype γ] [Fintype β] [Fintype ι]
  [DecidableEq γ] [DecidableEq ι]

omit [Fintype β] [DecidableEq γ] [DecidableEq ι] in
theorem cubeSum_full (x : Cube (Slots ι × γ)) :
    cubeSum x = totalSum cubeSum (fullCubeEquiv γ ι x) := by
  rw [cubeSum_block]
  exact sum_full cubeSum (blockCurry (Slots ι) γ Bool x)

theorem switched_score (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool) :
    score (switched F S L) =
      conditionalAverage (observation F (TableRounding.tableEvent S L)) (totalSum (score F)) ∘
        fullCubeEquiv γ ι := by
  have he : cubeSum (γ := Slots ι × γ) = totalSum cubeSum ∘ fullCubeEquiv γ ι := by
    funext x; exact cubeSum_full x
  unfold score switched
  change conditionalAverage
    (observation F (TableRounding.tableEvent S L) ∘ fullCubeEquiv γ ι) cubeSum = _
  rw [he,Projection.conditional_equiv]
  apply congrArg (fun p => p ∘ fullCubeEquiv γ ι)
  exact full_conditional_sum F (TableRounding.tableEvent S L) cubeSum

theorem switched_variance (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool) :
    variance (switched F S L) =
      average (fun x => (conditionalAverage (observation F (TableRounding.tableEvent S L))
        (totalSum (score F)) x)^2) := by
  unfold variance
  rw [switched_score]
  convert average_equiv (fullCubeEquiv γ ι)
    (fun x => (conditionalAverage (observation F (TableRounding.tableEvent S L))
        (totalSum (score F)) x)^2) using 1
  congr 1

theorem switched_variance_scaled (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool)
    (T : Cube γ → ℝ) (k : ℝ) (hT : score F = fun x => k*T x) :
    variance (switched F S L) = k^2*
      average (fun x => (conditionalAverage (observation F (TableRounding.tableEvent S L))
        (totalSum T) x)^2) := by
  rw [switched_variance,hT]
  have he : totalSum (ι := ι) (fun x : Cube γ => k*T x) = fun x => k*totalSum T x := by
    funext x
    simp only [totalSum,oldSum,← Finset.mul_sum]
    ring
  rw [he,Projection.conditional_const_mul]
  simp only [mul_pow,average_const_mul]

end Observations
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Grouping ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
open Switching FiniteCLT UniformFinite GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable

variable {α δ ι : Type*} [Fintype α] [Fintype δ] [Fintype ι]

theorem deficit_equiv (e : α ≃ δ) (T : δ → ℝ) (b : ℝ)
    (a : EventSpace δ ι → ℝ) :
    SoftEvent.deficit (T ∘ e) b (a ∘ eventCongr e) = SoftEvent.deficit T b a := by
  unfold SoftEvent.deficit
  convert average_equiv (eventCongr (ι := ι) e)
    (fun x => a x*(1-(T x.1+∑ j, T (x.2 j)-b)^2)) using 1
  congr 1

variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

omit [Fintype α] [Fintype δ] [Fintype ι] [Fintype β] in
theorem groupScale_sq (F : Cube γ → β) (n : ℕ) :
    (groupScale F n)^2 = n*variance F := by
  rw [groupScale,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt (variance_nonneg F)]

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem grouped_score_scaled (F : Cube γ → β) (hv : 0 < variance F) {n : ℕ} (hn : 0 < n) :
    score (grouped (κ := Fin n) F) = fun x => groupScale F n * groupStandard F n x := by
  rw [grouped_score]
  funext x
  simp only [groupScale,groupStandard,normalizedSum,Function.comp_apply,blockCurry,Equiv.coe_fn_mk,
    standard,standardValue,← Finset.mul_sum]
  have hv' := (Real.sqrt_pos.mpr hv).ne'
  have hn' := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  unfold score conditionalAverage
  field_simp

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem groupStandard_zero (F : Cube γ → β) (n : ℕ) : average (groupStandard F n) = 0 := by
  rw [groupStandard]
  change average (fun x => normalizedSum (standard F) n (blockCurry (Fin n) γ Bool x)) = 0
  rw [average_equiv]
  exact average_normalizedSum (standard F) (standard_zero F) n

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem groupStandard_sq (F : Cube γ → β) (hv : 0 < variance F) {n : ℕ} (hn : 0 < n) :
    average (fun x => (groupStandard F n x)^2) = 1 := by
  unfold groupStandard
  rw [show (fun x => (normalizedSum (standard F) n ∘ blockCurry (Fin n) γ Bool) x ^ 2) =
    (fun x => (normalizedSum (standard F) n x)^2) ∘ blockCurry (Fin n) γ Bool from rfl]
  change average (fun x => (normalizedSum (standard F) n (blockCurry (Fin n) γ Bool x))^2) = 1
  exact (average_equiv (blockCurry (Fin n) γ Bool)
    (fun x => (normalizedSum (standard F) n x)^2)).trans
    (average_normalizedSum_sq (standard F) (standard_zero F) (standard_sq F hv) hn)

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem exists_amplification (F : Cube γ → β) (hv : 0 < variance F) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : (Fin n → β) → Leaves, ∃ L : Leaves → (Fin n → β) → Bool,
      (n:ℝ)*variance F*(Fintype.card Leaves+1+eta) <
        variance (switched (grouped (κ := Fin n) F) S L) := by
  let : MeasurableSpace (Cube γ) := ⊤
  obtain ⟨n,hn,b,S,L,hg⟩ := Producer.exists_table_gain F (standardValue F)
    (standard_zero F) (standard_sq F hv)
  refine ⟨n,hn,S,L,?_⟩
  let G := grouped (κ := Fin n) F
  let T := groupStandard F n
  let A := TableRounding.tableEvent S L
  have hd : eta < SoftEvent.deficit T b
      (fun x => if A (oldLabels G x) then 1 else 0) := by
    have he := deficit_equiv (blockCurry (Fin n) γ Bool)
      (normalizedSum (standard F) n) b
      (fun x => if A ((fun j => F (x.1 j)),fun i j => F (x.2 i j)) then 1 else 0)
    have hA : (fun x : EventSpace (Cube (Fin n × γ)) Leaves => if A (oldLabels G x) then (1:ℝ) else 0) =
        (fun x => if A ((fun j => F (x.1 j)),fun i j => F (x.2 i j)) then 1 else 0) ∘
          eventCongr (blockCurry (Fin n) γ Bool) := rfl
    change eta < SoftEvent.deficit (normalizedSum (standard F) n ∘ blockCurry (Fin n) γ Bool) b _
    rw [hA,he]
    exact hg
  have hr := retained_gain G A T (normalizedSum (standardValue F) n) (fun _ => rfl) b eta
    (groupStandard_zero F n) (groupStandard_sq F hv hn) hd
  have hs := switched_variance_scaled G S L T (groupScale F n) (grouped_score_scaled F hv hn)
  rw [groupScale_sq] at hs
  rw [hs]
  have hnV : 0 < (n:ℝ)*variance F := mul_pos (Nat.cast_pos.mpr hn) hv
  exact mul_lt_mul_of_pos_left hr hnV

end Observations
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.Observations
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open Switching FiniteCLT UniformFinite GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable
variable {α δ ι : Type*} [Fintype α] [Fintype δ] [Fintype ι]
variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem solution (F : Cube γ → β) (hv : 0 < variance F) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : (Fin n → β) → Leaves, ∃ L : Leaves → (Fin n → β) → Bool,
      (n:ℝ)*variance F*(Fintype.card Leaves+1+eta) <
        variance (switched (grouped (κ := Fin n) F) S L) := by
  first
    | exact OAI.SquareRootDegree.Observations.exists_amplification F hv
    | exact OAI.SquareRootDegree.Observations.exists_amplification
    | (apply OAI.SquareRootDegree.Observations.exists_amplification <;> assumption)
    | (intros; apply OAI.SquareRootDegree.Observations.exists_amplification <;> assumption)
