-- Prove2me | solution 1 for OAI.SquareRootDegree.Producer.exists_table_gain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:37:35.761194+00:00
-- url     : https://prove2.me/submissions/f2546c21-a9c9-4a78-882d-7f5292608df4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Producer.lean:L72-L94
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.Producer.exists_table_gain. The node keeps its source
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
import Theorems.Thm_OAI_SquareRootDegree_FiniteMoments_normalized_product_centered_sq
import Theorems.Thm_OAI_SquareRootDegree_MomentTransfer_eventually_positive_gain
import Theorems.Thm_OAI_SquareRootDegree_SoftEvent_soft_deficit_eq_gain
import Theorems.Thm_OAI_SquareRootDegree_TableRounding_event_indicator

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

-- ---- from OAI.Combinatorics.BooleanFunctions.FiniteCLT ----
namespace OAI

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace SquareRootDegree
namespace FiniteCLT
attribute [local instance] Classical.propDecidable

variable {α : Type*} [MeasurableSpace α]

theorem measurable_normalizedSum (T : α → ℝ) (hT : Measurable T) (n : ℕ) :
    Measurable (normalizedSum T n) := by
  unfold normalizedSum
  fun_prop

theorem finite_product_clt (μ : Measure α) [IsProbabilityMeasure μ]
    (T : α → ℝ) (hT : Measurable T)
    (h0 : ∫ x, T x ∂μ = 0) (h1 : ∫ x, (T x)^2 ∂μ = 1) :
    TendstoInDistribution (normalizedSum T) atTop (fun x : ℝ => x)
      (fun n => Measure.pi (fun _ : Fin n => μ)) (gaussianReal 0 1) := by
  obtain ⟨Ω, mΩ, P, X, hmX, hlX, hiX, hP⟩ := exists_iid ℕ μ
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure P := hP
  have hi : iIndepFun (fun i ω => T (X i ω)) P := hiX.comp (fun _ => T) (fun _ => hT)
  have hl (i : ℕ) : HasLaw (fun ω => T (X i ω)) (μ.map T) P :=
    (show HasLaw T (μ.map T) μ from ⟨hT.aemeasurable, rfl⟩).fun_comp (hlX i)
  have hid (i : ℕ) : IdentDistrib (fun ω => T (X i ω)) (fun ω => T (X 0 ω)) P P :=
    (hl i).identDistrib (hl 0)
  have hz : ∫ ω, T (X 0 ω) ∂P = 0 :=
    ((hlX 0).integral_comp hT.aestronglyMeasurable).trans h0
  have ho : ∫ ω, (T (X 0 ω)) ^ 2 ∂P = 1 :=
    ((hlX 0).integral_comp (hT.pow_const 2).aestronglyMeasurable).trans h1
  have hc := tendstoInDistribution_inv_sqrt_mul_sum
    (P' := gaussianReal 0 1) (Y := fun x : ℝ => x) HasLaw.id hz ho hi hid
  refine ⟨fun n => (measurable_normalizedSum T hT n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  have hdist (n : ℕ) :
      IdentDistrib (normalizedSum T n)
        (fun ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, T (X k ω))
        (Measure.pi (fun _ : Fin n => μ)) P := by
    have hfin : HasLaw (fun ω (i : Fin n) => X i ω) (Measure.pi (fun _ : Fin n => μ)) P :=
      (hiX.precomp Fin.val_injective).hasLaw_pi (fun i => hlX i)
    have hn := (show HasLaw (normalizedSum T n)
        ((Measure.pi (fun _ : Fin n => μ)).map (normalizedSum T n))
        (Measure.pi (fun _ : Fin n => μ)) from
      ⟨(measurable_normalizedSum T hT n).aemeasurable, rfl⟩).fun_comp hfin
    have he : (fun ω => normalizedSum T n (fun i : Fin n => X i ω)) =
        (fun ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, T (X k ω)) := by
      funext ω
      unfold normalizedSum
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun k => T (X k ω)) n
    rw [he] at hn
    exact (show HasLaw (normalizedSum T n) _ (Measure.pi (fun _ : Fin n => μ))
      from ⟨(measurable_normalizedSum T hT n).aemeasurable, rfl⟩).identDistrib hn
  apply hc.tendsto.congr
  intro n
  exact Subtype.ext (hdist n).map_eq.symm

end FiniteCLT
end SquareRootDegree

namespace SquareRootDegree
namespace UniformFinite
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem uniform_singleton (a : α) : uniformMeasure α {a} = (Fintype.card α : ENNReal)⁻¹ := by
  rw [uniformMeasure,PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),PMF.uniformOfFintype_apply]

theorem integral_uniform (f : α → ℝ) : (∫ x, f x ∂uniformMeasure α) = average f := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [Measure.real,uniform_singleton,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  exact (Finset.mul_sum ..).symm

theorem uniform_pi [Fintype ι] [DecidableEq ι] :
    Measure.pi (fun _ : ι => uniformMeasure α) = uniformMeasure (ι → α) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton,uniform_singleton]
  simp only [uniform_singleton,Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,ENNReal.inv_pow]

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

theorem uniform_clt (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    TendstoInDistribution (FiniteCLT.normalizedSum T) atTop (fun x : ℝ => x)
      (fun n => uniformMeasure (Fin n → α)) (gaussianReal 0 1) := by
  have hm : Measurable T := measurable_of_finite T
  have hz : (∫ x, T x ∂uniformMeasure α) = 0 := (integral_uniform T).trans h0
  have hv : (∫ x, (T x)^2 ∂uniformMeasure α) = 1 := (integral_uniform _).trans h1
  have hc := FiniteCLT.finite_product_clt (uniformMeasure α) T hm hz hv
  simpa only [uniform_pi] using hc

end UniformFinite
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothGaussian ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothGaussian

theorem tent_nonneg (a h x : ℝ) : 0 ≤ tent a h x := le_max_left _ _

theorem tent_le_one {h : ℝ} (hh : 0 < h) (a x : ℝ) : tent a h x ≤ 1 := by
  apply max_le zero_le_one
  have := div_nonneg (abs_nonneg (x-a)) hh.le
  linarith

end SmoothGaussian
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothSelector ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothSelector

theorem clip_nonneg (x : ℝ) : 0 ≤ clip x := le_max_left _ _
theorem clip_le_one (x : ℝ) : clip x ≤ 1 := max_le zero_le_one (min_le_left _ _)
theorem clip_mono : Monotone clip := fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)
theorem hat_nonneg (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    0 ≤ hat N δ i t := by
  unfold hat
  exact sub_nonneg.mpr (clip_mono (by linarith))

theorem hats_sum (N : ℕ) (δ t : ℝ) :
    ∑ i : Fin (2*N+1), hat N δ i t = clip (t/δ+N+1)-clip (t/δ-N) := by
  unfold hat
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    clip (t/δ+N-i+1)-clip (t/δ+N-i)) (2*N+1)]
  have he (i : ℕ) : clip (t/δ+N-i+1)-clip (t/δ+N-i) =
      clip (t/δ+N-i+1)-clip (t/δ+N-(i+1:ℕ)+1) := by push_cast; ring_nf
  simp_rw [he]
  rw [Finset.sum_range_sub']
  push_cast
  congr 1 <;> congr 1 <;> ring

theorem hats_sum_le_one (N : ℕ) (δ t : ℝ) :
    ∑ i : Fin (2*N+1), hat N δ i t ≤ 1 := by
  rw [hats_sum]
  linarith [clip_le_one (t/δ+N+1),clip_nonneg (t/δ-N)]

theorem weight_nonneg (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    0 ≤ weight N δ i t := by
  unfold weight
  split_ifs <;> linarith [hat_nonneg N δ i t, hats_sum_le_one N δ t]

end SmoothSelector
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.GaussianGain ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace GaussianGain
open SmoothGaussian SmoothSelector

theorem gaussian_sq_integral (v : ℝ≥0) :
    (∫ x, x^2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (show AEMeasurable (fun x : ℝ => x) (gaussianReal 0 v) from measurable_id.aemeasurable)] at h
  simpa using h

theorem width_pos : 0 < width := by unfold width; positivity
end GaussianGain
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Rounding ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

attribute [local instance] Classical.propDecidable

namespace SquareRootDegree
namespace FiniteRounding

theorem productWeight_nonneg {ι α : Type*} [Fintype ι]
    (p : ι → α → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : ι → α) :
    0 ≤ productWeight p x := Finset.prod_nonneg (fun i _ => hp i (x i))

theorem bernoulli_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (b : Bool) :
    0 ≤ bernoulliWeight p b := by cases b <;> simp [bernoulliWeight] <;> linarith

theorem leafWeight_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp' : ∀ a, p a ≤ 1) (t : α → Bool) :
    0 ≤ leafWeight p t := productWeight_nonneg _ (fun a => bernoulli_nonneg (hp a) (hp' a)) t

theorem exists_ge_weighted_sum {α : Type*} [Fintype α] (p f : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (c : ℝ)
    (hc : c < ∑ a, p a * f a) : ∃ a, c < f a := by
  by_contra h
  push Not at h
  have he : ∑ a, p a * f a ≤ c := by
    calc ∑ a, p a * f a ≤ ∑ a, p a * c := by
           apply Finset.sum_le_sum; intro a _; exact mul_le_mul_of_nonneg_left (h a) (hp a)
      _ = c := by rw [← Finset.sum_mul, hs, one_mul]
  exact (not_lt_of_ge he) hc

end FiniteRounding
end SquareRootDegree

namespace SquareRootDegree
namespace TableRounding
open FiniteRounding SoftEvent
attribute [local instance] Classical.propDecidable
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

theorem tableWeight_nonneg (s w : ι → β → ℝ) (hs : ∀ i b, 0 ≤ s i b)
    (hw : ∀ i b, 0 ≤ w i b) (hw' : ∀ i b, w i b ≤ 1) (t) : 0 ≤ tableWeight s w t := by
  exact mul_nonneg (productWeight_nonneg _ (fun b i => hs i b) _)
    (productWeight_nonneg _ (fun i => leafWeight_nonneg _ (hw i) (hw' i)) _)

theorem tableWeight_sum (s w : ι → β → ℝ) (hs : ∀ b, ∑ i, s i b = 1) :
    ∑ t, tableWeight s w t = 1 := by
  simp only [tableWeight,Fintype.sum_prod_type,← Finset.mul_sum,
    sum_productWeight _ (fun i => leafWeight_sum (w i)),mul_one]
  exact sum_productWeight _ hs

theorem weighted_leaf_prod (w : ι → β → ℝ) (x : ι → β) (I : Finset ι) :
    ∑ L : ι → β → Bool, productWeight (fun i => leafWeight (w i)) L *
      ∏ i ∈ I, bit (L i (x i)) = ∏ i ∈ I, w i (x i) := by
  have h := weighted_product (fun i => leafWeight (w i))
    (fun i (t : β → Bool) => if i ∈ I then bit (t (x i)) else 1)
  have hi (i : ι) : (∑ t : β → Bool, leafWeight (w i) t *
      (if i ∈ I then bit (t (x i)) else 1)) = if i ∈ I then w i (x i) else 1 := by
    by_cases hi : i ∈ I
    · simp only [hi,ite_true,bit]
      exact leafWeight_eval (w i) (x i)
    · simp [hi]
  simpa only [Finset.prod_ite_mem,Finset.inter_univ,Finset.univ_inter,hi] using h

theorem weighted_indicator (s w : ι → β → ℝ) (hs : ∀ b, ∑ i, s i b = 1)
    (x : β × (ι → β)) :
    ∑ t, tableWeight s w t * (if tableEvent t.1 t.2 x then (1:ℝ) else 0) =
      softWeight s w x := by
  -- First average the independent leaf-test tables.
  have hL (S : β → ι) :
      (∑ L : ι → β → Bool, productWeight (fun i => leafWeight (w i)) L *
        ((∑ i, (if S x.1 = i then (1:ℝ) else 0) *
          ∏ j ∈ Finset.univ.erase i, bit (L j (x.2 j))) - ∏ j, bit (L j (x.2 j)))) =
      (∑ i, (if S x.1 = i then (1:ℝ) else 0) * ∏ j ∈ Finset.univ.erase i, w j (x.2 j)) -
        ∏ j, w j (x.2 j) := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_left_comm _ (if _ then _ else _),← Finset.mul_sum,weighted_leaf_prod]
  have hS (i : ι) : (∑ S : β → ι, productWeight (fun b i => s i b) S *
      (if S x.1 = i then (1:ℝ) else 0)) = s i x.1 := by
    simpa using weighted_evaluation (fun b i => s i b) hs x.1 (fun j => if j = i then 1 else 0)
  simp only [tableWeight,Fintype.sum_prod_type]
  simp_rw [event_indicator,mul_assoc,← Finset.mul_sum]
  change (∑ S : β → ι, productWeight (fun b i => s i b) S *
    (∑ L : ι → β → Bool, productWeight (fun i => leafWeight (w i)) L *
      ((∑ i, (if S x.1 = i then (1:ℝ) else 0) *
        ∏ j ∈ Finset.univ.erase i, bit (L j (x.2 j))) - ∏ j, bit (L j (x.2 j))))) = _
  simp_rw [hL,mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,hS]
  rw [sum_productWeight _ hs,one_mul]
  rfl

theorem weighted_deficit (s w : ι → β → ℝ) (hs : ∀ b, ∑ i, s i b = 1)
    (F : α → β) (T : α → ℝ) (b : ℝ) :
    (∑ t, tableWeight s w t * deficit T b
      (fun x => if tableEvent t.1 t.2 (F x.1,fun i => F (x.2 i)) then 1 else 0)) =
      deficit T b (softWeight (fun i a => s i (F a)) (fun i a => w i (F a))) := by
  simp only [deficit,← average_const_mul,← average_sum]
  congr 1
  funext x
  simp_rw [← mul_assoc,← Finset.sum_mul,weighted_indicator s w hs]
  rfl

theorem exists_event_deficit (s w : ι → β → ℝ)
    (hs : ∀ b, ∑ i, s i b = 1) (hs0 : ∀ i b, 0 ≤ s i b)
    (hw0 : ∀ i b, 0 ≤ w i b) (hw1 : ∀ i b, w i b ≤ 1)
    (F : α → β) (T : α → ℝ) (b c : ℝ)
    (hc : c < deficit T b (softWeight (fun i a => s i (F a)) (fun i a => w i (F a)))) :
    ∃ S : β → ι, ∃ L : ι → β → Bool,
      c < deficit T b (fun x => if tableEvent S L (F x.1,fun i => F (x.2 i)) then 1 else 0) := by
  rw [← weighted_deficit s w hs F T b] at hc
  obtain ⟨t,ht⟩ := exists_ge_weighted_sum (tableWeight s w) _
    (tableWeight_nonneg s w hs0 hw0 hw1) (tableWeight_sum s w hs) c hc
  exact ⟨t.1,t.2,ht⟩

end TableRounding
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Producer ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Producer
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT MomentTransfer GaussianGain
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem normalized_moments_tendsto (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) (k : Fin 3) :
    Tendsto (fun n => ∫ x, (normalizedSum T n x)^(k:ℕ) ∂uniformMeasure (Fin n → α)) atTop
      (𝓝 (∫ x : ℝ, x^(k:ℕ) ∂gaussianReal 0 1)) := by
  fin_cases k
  · simp only [pow_zero,integral_const,probReal_univ,one_smul]
    exact tendsto_const_nhds
  · simp only [pow_one,integral_uniform,average_normalizedSum T h0,
      integral_id_gaussianReal]
    exact tendsto_const_nhds
  · change Tendsto (fun n => ∫ x, (normalizedSum T n x)^2 ∂uniformMeasure (Fin n → α)) atTop
      (𝓝 (∫ x : ℝ, x^2 ∂gaussianReal 0 1))
    rw [gaussian_sq_integral]
    have he : (fun n => ∫ x, (normalizedSum T n x)^2 ∂uniformMeasure (Fin n → α)) =ᶠ[atTop]
        (fun _ => (1:ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [integral_uniform,average_normalizedSum_sq T h0 h1 hn]
    exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem exists_soft_gain (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    ∃ n : ℕ, 0 < n ∧
      (∀ i : Leaves, 0 < average (fun x => leafTest i (normalizedSum T n x))) ∧
      eta < SoftEvent.deficit (normalizedSum T n)
        ((∑ i, means (SoftEvent.rawMoments (normalizedSum T n)
          (fun i x => leafTest i (normalizedSum T n x))) i)-1)
        (SoftEvent.softWeight (fun i x => selectorTest i (normalizedSum T n x))
          (fun i x => leafTest i (normalizedSum T n x))) := by
  have hc := uniform_clt T h0 h1
  have hp := eventually_positive_gain (fun n => uniformMeasure (Fin n → α))
    (normalizedSum T) (fun n => measurable_of_finite _) hc
    (fun n k => Integrable.of_finite) (normalized_moments_tendsto T h0 h1)
  obtain ⟨n,hn,hp⟩ := ((eventually_gt_atTop 0).and hp).exists
  have hl (i : Leaves) : 0 < average (fun x => leafTest i (normalizedSum T n x)) := by
    simpa only [moments,Fin.val_zero,pow_zero,mul_one,integral_uniform] using hp.1 i
  refine ⟨n,hn,hl,?_⟩
  have hs := SoftEvent.soft_deficit_eq_gain
    (fun i x => selectorTest i (normalizedSum T n x))
    (fun i x => leafTest i (normalizedSum T n x)) (fun i => (hl i).ne')
    (normalizedSum T n) (average_normalizedSum T h0 n) (average_normalizedSum_sq T h0 h1 hn)
  rw [hs]
  have he : (moments (uniformMeasure (Fin n → α)) (normalizedSum T n) leafTest) =
      SoftEvent.rawMoments (normalizedSum T n) (fun i x => leafTest i (normalizedSum T n x)) := by
    funext k i
    exact integral_uniform _
  have he' : (moments (uniformMeasure (Fin n → α)) (normalizedSum T n) selectorTest) =
      SoftEvent.rawMoments (normalizedSum T n) (fun i x => selectorTest i (normalizedSum T n x)) := by
    funext k i
    exact integral_uniform _
  rw [he,he'] at hp
  convert hp.2 using 1
  congr 1

theorem exists_table_gain [Fintype β] (F : α → β) (t : β → ℝ)
    (h0 : average (fun a => t (F a)) = 0)
    (h1 : average (fun a => (t (F a))^2) = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : ℝ, ∃ S : (Fin n → β) → Leaves,
      ∃ L : Leaves → (Fin n → β) → Bool,
      eta < SoftEvent.deficit (normalizedSum (fun a => t (F a)) n) b
        (fun x => if TableRounding.tableEvent S L
          ((fun j => F (x.1 j)),fun i j => F (x.2 i j)) then 1 else 0) := by
  obtain ⟨n,hn,_,hg⟩ := exists_soft_gain (fun a => t (F a)) h0 h1
  let b := (∑ i, means (SoftEvent.rawMoments (normalizedSum (fun a => t (F a)) n)
          (fun i x => leafTest i (normalizedSum (fun a => t (F a)) n x))) i)-1
  have he (x : Fin n → α) : normalizedSum t n (fun j => F (x j)) =
      normalizedSum (fun a => t (F a)) n x := rfl
  obtain ⟨S,L,hSL⟩ := TableRounding.exists_event_deficit
    (fun (i : Leaves) (y : Fin n → β) => selectorTest i (normalizedSum t n y))
    (fun (i : Leaves) (y : Fin n → β) => leafTest i (normalizedSum t n y))
    (fun y => SmoothSelector.weight_sum gridN step (normalizedSum t n y))
    (fun i y => SmoothSelector.weight_nonneg gridN step i (normalizedSum t n y))
    (fun i y => SmoothGaussian.tent_nonneg _ _ _)
    (fun i y => SmoothGaussian.tent_le_one width_pos _ _)
    (fun x : Fin n → α => fun j => F (x j))
    (normalizedSum (fun a => t (F a)) n) b eta (by simpa only [he] using hg)
  exact ⟨n,hn,b,S,L,hSL⟩

end Producer
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.Producer
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT MomentTransfer GaussianGain
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem solution [Fintype β] (F : α → β) (t : β → ℝ)
    (h0 : average (fun a => t (F a)) = 0)
    (h1 : average (fun a => (t (F a))^2) = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : ℝ, ∃ S : (Fin n → β) → Leaves,
      ∃ L : Leaves → (Fin n → β) → Bool,
      eta < SoftEvent.deficit (normalizedSum (fun a => t (F a)) n) b
        (fun x => if TableRounding.tableEvent S L
          ((fun j => F (x.1 j)),fun i j => F (x.2 i j)) then 1 else 0) := by
  first
    | exact OAI.SquareRootDegree.Producer.exists_table_gain F t h0 h1
    | exact OAI.SquareRootDegree.Producer.exists_table_gain
    | (apply OAI.SquareRootDegree.Producer.exists_table_gain <;> assumption)
    | (intros; apply OAI.SquareRootDegree.Producer.exists_table_gain <;> assumption)
