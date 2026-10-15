-- Prove2me | solution 1 for OAI.SquareRootDegree.SoftEvent.soft_deficit_eq_gain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:32:15.443333+00:00
-- url     : https://prove2.me/submissions/4baa831e-f438-4196-95e5-d4cf296d6b59

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/SoftEvent.lean:L139-L190
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.SoftEvent.soft_deficit_eq_gain. The node keeps its source
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
import Theorems.Thm_OAI_SquareRootDegree_FiniteMoments_normalized_product_shifted_sq

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

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.FiniteMoments ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

attribute [local instance] Classical.propDecidable

namespace FiniteMoments
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem average_normalized_weight (w : α → ℝ) (hw : average w ≠ 0) :
    average (fun x => w x / average w) = 1 := by
  simp only [div_eq_mul_inv,average_mul_const,mul_inv_cancel₀ hw]

end FiniteMoments
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.SoftEvent ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SoftEvent
attribute [local instance] Classical.propDecidable
open FiniteMoments MomentTransfer
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]

omit [Nonempty α] in
theorem average_div_const (f : α → ℝ) (c : ℝ) :
    average (fun a => f a/c) = average f/c := by
  simp only [div_eq_mul_inv,average_mul_const]

omit [Nonempty α] in
theorem weighted_shifted_sq (w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : ι → α → ℝ) (c : ℝ) :
    average (fun x : ι → α => (∏ i, w i (x i))*(c+∑ i, T i (x i))^2) =
      (∏ i, average (w i)) * ((c+∑ i, average (fun a => w i a*T i a)/average (w i))^2 +
        ∑ i, (average (fun a => w i a*(T i a)^2)/average (w i) -
          (average (fun a => w i a*T i a)/average (w i))^2)) := by
  let r := fun i a => w i a/average (w i)
  have hr (i : ι) : average (r i) = 1 := average_normalized_weight _ (hw i)
  have he : (fun x : ι → α => (∏ i, w i (x i))*(c+∑ i, T i (x i))^2) =
      fun x => (∏ i, average (w i))*((∏ i, r i (x i))*(c+∑ i, T i (x i))^2) := by
    funext x
    dsimp [r]
    rw [Finset.prod_div_distrib]
    field_simp [Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)]
  rw [he,average_const_mul]
  have hm (i : ι) : average (fun a => r i a*T i a) =
      average (fun a => w i a*T i a)/average (w i) := by
    simp only [r,div_mul_eq_mul_div,average_div_const]
  have hh := normalized_product_shifted_sq r hr T _ hm c
  simp only [r,div_mul_eq_mul_div,average_div_const] at hh
  exact congrArg ((∏ i, average (w i)) * ·) hh

omit [Nonempty α] in
theorem weighted_deficit (w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : α → ℝ) (c : ℝ) :
    average (fun x : ι → α => (∏ i, w i (x i))*(1-(c+∑ i, T (x i))^2)) =
      (∏ i, (rawMoments T w) 0 i) *
        (1-(c+∑ i, means (rawMoments T w) i)^2-∑ i, vars (rawMoments T w) i) := by
  simp only [mul_sub,mul_one,average_sub]
  rw [average_pi_prod w,weighted_shifted_sq w hw (fun _ => T) c]
  simp only [rawMoments,means,vars,Fin.val_zero,Fin.val_one,show ((2 : Fin 3):ℕ) = 2 from rfl,pow_zero,pow_one,mul_one]
  ring

theorem prod_set_one (f : ι → ℝ) (i : ι) :
    (∏ j, if j = i then 1 else f j) = ∏ j ∈ Finset.univ.erase i, f j := by
  rw [← Finset.prod_erase_mul Finset.univ (fun j => if j = i then 1 else f j) (Finset.mem_univ i)]
  simp only [ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem sum_set_zero (f : ι → ℝ) (i : ι) :
    (∑ j, if j = i then 0 else f j) = ∑ j ∈ Finset.univ.erase i, f j := by
  rw [← Finset.sum_erase_add Finset.univ (fun j => if j = i then 0 else f j) (Finset.mem_univ i)]
  simp only [ite_true,add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem weighted_deficit_without (w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : α → ℝ) (h0 : average T = 0) (h1 : average (fun a => (T a)^2) = 1)
    (c : ℝ) (i : ι) :
    average (fun x : ι → α => (∏ j ∈ Finset.univ.erase i, w j (x j))*(1-(c+∑ j, T (x j))^2)) =
      -((∏ j, rawMoments T w 0 j)/rawMoments T w 0 i) *
        ((c+∑ j, means (rawMoments T w) j-means (rawMoments T w) i)^2+
          ∑ j ∈ Finset.univ.erase i, vars (rawMoments T w) j) := by
  let l := rawMoments T w
  have hb (j) : rawMoments T (without w i) 0 j = if j = i then 1 else l 0 j := by
    by_cases hj : j = i <;> simp [rawMoments,without,hj,average_const,l]
  have hm (j) : means (rawMoments T (without w i)) j = if j = i then 0 else means l j := by
    by_cases hj : j = i <;> simp [means,rawMoments,without,hj,average_const,h0,l]
  have hv (j) : vars (rawMoments T (without w i)) j = if j = i then 1 else vars l j := by
    by_cases hj : j = i
    · simp [vars,hm,rawMoments,without,hj,average_const,h1]
    · simp [vars,hm,rawMoments,without,hj,l]
  have hwb (j) : average (without w i j) ≠ 0 := by
    change average (fun a => if j = i then 1 else w j a) ≠ 0
    by_cases hj : j = i <;> simp [hj,average_const,hw]
  have he : (fun x : ι → α => (∏ j ∈ Finset.univ.erase i, w j (x j))*(1-(c+∑ j, T (x j))^2)) =
      fun x => (∏ j, without w i j (x j))*(1-(c+∑ j, T (x j))^2) := by
    funext x
    change _ = (∏ j, if j = i then 1 else w j (x j))*(1-(c+∑ j, T (x j))^2)
    rw [prod_set_one]
  rw [he,weighted_deficit (without w i) hwb T c]
  simp_rw [hb,hm,hv]
  rw [prod_set_one,sum_set_zero]
  have hp : (∏ j ∈ Finset.univ.erase i, l 0 j) = (∏ j, l 0 j)/l 0 i := by
    apply (eq_div_iff (by simpa [l,rawMoments] using hw i)).mpr
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have hs := Finset.sum_erase_add Finset.univ (fun j => means l j) (Finset.mem_univ i)
  have hvs : (∑ j, if j = i then (1:ℝ) else vars l j) = 1+∑ j ∈ Finset.univ.erase i, vars l j := by
    rw [← Finset.sum_erase_add Finset.univ (fun j => if j = i then (1:ℝ) else vars l j)
      (Finset.mem_univ i)]
    simp only [ite_true]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [ite_eq_right (Finset.mem_erase.mp hj).1]
  rw [hp,hvs,show (∑ j ∈ Finset.univ.erase i, means l j) = (∑ j, means l j)-means l i by linarith]
  change _ = -((∏ j, l 0 j)/l 0 i)*((c+∑ j, means l j-means l i)^2+
    ∑ j ∈ Finset.univ.erase i, vars l j)
  ring

omit [Nonempty α] in
theorem quadratic_average (T w : α → ℝ) (a v : ℝ) :
    average (fun x => w x*((1+T x-a)^2+v)) = average (fun x => w x*(T x)^2) +
      2*(1-a)*average (fun x => w x*T x) + ((1-a)^2+v)*average w := by
  have he : (fun x => w x*((1+T x-a)^2+v)) = fun x =>
      w x*(T x)^2+2*(1-a)*(w x*T x)+((1-a)^2+v)*w x := by funext x; ring
  rw [he,average_add,average_add,average_const_mul,average_const_mul]

theorem soft_deficit_eq_gain (s w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : α → ℝ) (h0 : average T = 0) (h1 : average (fun a => (T a)^2) = 1) :
    deficit T ((∑ i, means (rawMoments T w) i)-1) (softWeight s w) =
      gain (rawMoments T w) (rawMoments T s) := by
  let l := rawMoments T w
  let b := (∑ i, means l i)-1
  let P := ∏ i, l 0 i
  let v := ∑ i, vars l i
  have hshift (u : α) (z : ι → α) : T u+∑ i, T (z i)-b = T u-b+∑ i, T (z i) := by ring
  have hex (u : α) (i : ι) :
      average (fun z : ι → α => (∏ j ∈ Finset.univ.erase i, w j (z j))*
        (1-(T u-b+∑ j, T (z j))^2)) = -(P/l 0 i)*
          ((1+T u-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j) := by
    rw [weighted_deficit_without w hw T h0 h1 (T u-b) i]
    change -(P/l 0 i)*_ = _
    congr 2
    dsimp [b]
    ring
  have hall (u : α) :
      average (fun z : ι → α => (∏ j, w j (z j))*(1-(T u-b+∑ j, T (z j))^2)) =
        P*(1-(1+T u)^2-v) := by
    rw [weighted_deficit w hw T (T u-b)]
    change P*(1-(T u-b+∑ i, means l i)^2-v) = _
    dsimp [b]
    ring
  have ha : average (fun u => P*(1-(1+T u)^2-v)) = -P*(1+v) := by
    have he : (fun u => P*(1-(1+T u)^2-v)) = fun u =>
        -P*(T u)^2-2*P*T u-P*v := by funext u; ring
    rw [he,average_sub,average_sub,average_const_mul,average_const_mul,average_const,h0,h1]
    ring
  have hi (i : ι) : average (fun u => s i u*(-(P/l 0 i)*
      ((1+T u-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j))) =
      -P*((rawMoments T s 2 i+2*(1-means l i)*rawMoments T s 1 i+
        ((1-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j)*rawMoments T s 0 i)/l 0 i) := by
    have he : (fun u => s i u*(-(P/l 0 i)*
        ((1+T u-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j))) = fun u =>
        -(P/l 0 i)*(s i u*((1+T u-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j)) := by
      funext u; ring
    rw [he,average_const_mul,quadratic_average]
    simp only [rawMoments,Fin.val_zero,Fin.val_one,show ((2:Fin 3):ℕ)=2 from rfl,pow_zero,pow_one,mul_one]
    ring
  change deficit T b (softWeight s w) = _
  rw [deficit,average_prod]
  simp only [softWeight,sub_mul,Finset.sum_mul]
  simp_rw [hshift,mul_assoc]
  simp only [average_sub,average_sum,average_const_mul]
  simp_rw [hex,hall]
  rw [ha]
  simp_rw [hi]
  rw [← Finset.mul_sum]
  change -P*(_)-(-P*(1+v)) = P*(1+v-_)
  ring

end SoftEvent
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.SoftEvent
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
open FiniteMoments MomentTransfer
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]

theorem solution (s w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : α → ℝ) (h0 : average T = 0) (h1 : average (fun a => (T a)^2) = 1) :
    deficit T ((∑ i, means (rawMoments T w) i)-1) (softWeight s w) =
      gain (rawMoments T w) (rawMoments T s) := by
  first
    | exact OAI.SquareRootDegree.SoftEvent.soft_deficit_eq_gain s w hw T h0 h1
    | exact OAI.SquareRootDegree.SoftEvent.soft_deficit_eq_gain
    | (apply OAI.SquareRootDegree.SoftEvent.soft_deficit_eq_gain <;> assumption)
    | (intros; apply OAI.SquareRootDegree.SoftEvent.soft_deficit_eq_gain <;> assumption)
