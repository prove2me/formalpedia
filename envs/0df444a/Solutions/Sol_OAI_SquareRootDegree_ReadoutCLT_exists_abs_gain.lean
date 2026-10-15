-- Prove2me | solution 1 for OAI.SquareRootDegree.ReadoutCLT.exists_abs_gain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:43:05.901978+00:00
-- url     : https://prove2.me/submissions/d37dd208-46af-44b7-a544-bd5693c54968

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/ReadoutCLT.lean:L38-L52
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.ReadoutCLT.exists_abs_gain. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Amplification
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_ReadoutCLT
import Theorems.Thm_OAI_SquareRootDegree_SmoothGaussian_beta_lower

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

theorem average_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-! ### Degree calculus for finite observations -/

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

theorem tent_le_one {h : ℝ} (hh : 0 < h) (a x : ℝ) : tent a h x ≤ 1 := by
  apply max_le zero_le_one
  have := div_nonneg (abs_nonneg (x-a)) hh.le
  linarith

theorem tent_eq_zero {a h x : ℝ} (hh : 0 < h) (hx : h ≤ |x-a|) :
    tent a h x = 0 := by
  unfold tent
  apply max_eq_left
  have : 1 ≤ |x-a|/h := (one_le_div hh).mpr hx
  linarith

theorem tent_ne_zero_iff {a h x : ℝ} (hh : 0 < h) :
    tent a h x ≠ 0 ↔ |x-a| < h := by
  constructor
  · intro hn
    exact lt_of_not_ge (fun hx => hn (tent_eq_zero hh hx))
  · intro hx
    apply ne_of_gt
    apply lt_of_lt_of_le _ (le_max_right _ _)
    have := (div_lt_one hh).mpr hx
    linarith

theorem tent_support {a h : ℝ} (hh : 0 < h) :
    Function.support (tent a h) ⊆ Set.Icc (a-h) (a+h) := by
  intro x hx
  have he := (tent_ne_zero_iff hh).mp hx
  rw [abs_lt] at he
  constructor <;> linarith

theorem tent_compactSupport {a h : ℝ} (hh : 0 < h) : HasCompactSupport (tent a h) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a-h) (b := a+h))
  intro x hx
  by_contra hn
  exact hx (tent_support hh hn)

theorem tent_mass_pos {a h : ℝ} (hh : 0 < h) :
    0 < mass (gaussianReal 0 1) (tent a h) := by
  apply lt_of_lt_of_le _ (beta_lower hh)
  positivity

end SmoothGaussian
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.MomentTransfer ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace MomentTransfer
open SmoothGaussian SmoothSelector GaussianGain
/-- Only compact continuous test functions are passed through weak convergence. -/
theorem compact_test_tendsto {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ω n → ℝ) (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1))
    (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun n => ∫ x, f (T n x) ∂P n) atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hT.tendsto)
    (ofCompactSupport f hf hc)
  change Tendsto (fun n => ∫ x, f x ∂(P n).map (T n)) atTop
    (𝓝 (∫ x, f x ∂(gaussianReal 0 1).map (fun x => x))) at h
  rw [Measure.map_id'] at h
  have he (n : ℕ) : (∫ x, f x ∂(P n).map (T n)) =
      ∫ x, f (T n x) ∂P n := by
    rw [integral_map (hT.forall_aemeasurable n) hf.aestronglyMeasurable]
  simpa only [he] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end MomentTransfer
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.ReadoutCLT ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace ReadoutCLT
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem constant_pos : 0 < constant := by
  have h := SmoothGaussian.tent_mass_pos (a := (1:ℝ)) (h := (1/2:ℝ)) (by norm_num)
  unfold constant test
  rw [integral_const_mul]
  positivity

theorem test_le_abs (x : ℝ) : test x ≤ |x| := by
  by_cases h : |x-1| < 1/2
  · have hx := (abs_lt.mp h).1
    have ht := SmoothGaussian.tent_le_one (by norm_num : (0:ℝ) < 1/2) 1 x
    unfold test
    have ha := le_abs_self x
    linarith
  · rw [test,SmoothGaussian.tent_eq_zero (by norm_num : (0:ℝ) < 1/2) (le_of_not_gt h),mul_zero]
    exact abs_nonneg x

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem exists_abs_gain (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    ∃ n : ℕ, 0 < n ∧ constant < average (fun x => |normalizedSum T n x|) := by
  have hc := MomentTransfer.compact_test_tendsto
    (fun n => uniformMeasure (Fin n → α)) (normalizedSum T) (uniform_clt T h0 h1)
    test (by unfold test; fun_prop)
    ((SmoothGaussian.tent_compactSupport (a := (1:ℝ)) (by norm_num : (0:ℝ) < 1/2)).mul_left (f := fun _ : ℝ => (1/2:ℝ)))
  have hl : constant < ∫ x, test x ∂gaussianReal 0 1 := by
    have := constant_pos
    unfold constant at *
    linarith
  obtain ⟨n,hn,hg⟩ := ((eventually_gt_atTop 0).and (hc.eventually (lt_mem_nhds hl))).exists
  refine ⟨n,hn,hg.trans_le ?_⟩
  rw [integral_uniform]
  exact average_mono (fun x => test_le_abs (normalizedSum T n x))

end ReadoutCLT
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.ReadoutCLT
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem solution (T : α → ℝ) (h0 : average T = 0)
    (h1 : average (fun a => (T a)^2) = 1) :
    ∃ n : ℕ, 0 < n ∧ constant < average (fun x => |normalizedSum T n x|) := by
  first
    | exact OAI.SquareRootDegree.ReadoutCLT.exists_abs_gain T h0 h1
    | exact OAI.SquareRootDegree.ReadoutCLT.exists_abs_gain
    | (apply OAI.SquareRootDegree.ReadoutCLT.exists_abs_gain <;> assumption)
    | (intros; apply OAI.SquareRootDegree.ReadoutCLT.exists_abs_gain <;> assumption)
