-- Prove2me | solution 1 for OAI.ComparatorModel.RecursivePotentials.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:18:53.824106+00:00
-- url     : https://prove2.me/submissions/3faec30d-64d9-4b1d-b272-6505680b36a1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/Challenge.lean:L259-L261
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ComparatorModel.RecursivePotentials.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ComparatorModel_RecursivePotentials_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableLp
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableStability
import Definitions.Def_OAI_Analysis_RecursivePotentials_Main
import Definitions.Def_OAI_Analysis_RecursivePotentials_Challenge
import Theorems.Thm_OAI_RecursivePotentials_AggregationSpace_lp_comparisons
import Theorems.Thm_OAI_RecursivePotentials_AggregationVector_finite_recursion
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_path_step
import Theorems.Thm_OAI_RecursivePotentials_IsReflexive_of_equiv
import Theorems.Thm_OAI_RecursivePotentials_SquareSum_isReflexive
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_averaged_modulus_cubic
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_finite_center_midpoint_gap
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_finite_tail_dense
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_finite_unit_dense
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_homogeneous_cubic_tail
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_separated_midpoint_families
import Theorems.Thm_OAI_RecursivePotentials_VariableExponent_finite_cubic
import Theorems.Thm_OAI_RecursivePotentials_VariableExponent_sixth_of_cubic
import Theorems.Thm_OAI_RecursivePotentials_XJoined_no_equivalent_AUC
import Theorems.Thm_OAI_RecursivePotentials_XSigma_no_equivalent_AUC
import Theorems.Thm_OAI_RecursivePotentials_XZero_no_equivalent_AUC
import Theorems.Thm_OAI_RecursivePotentials_ZeroTreeSpace_finite_tail_dense
import Theorems.Thm_OAI_RecursivePotentials_ZeroTreeSpace_tail_eq_coordinate_kernel
import Theorems.Thm_OAI_RecursivePotentials_averagedModulus_lower_of_witness
import Theorems.Thm_OAI_RecursivePotentials_bounded_trees_modulus_le_zero
import Theorems.Thm_OAI_RecursivePotentials_hilbert_isReflexive

-- ---- from OAI.Analysis.RecursivePotentials.TreeGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (v : TreeVector T) :
    projection T H hH (projection T H hH v) = projection T H hH v := by
  change ι →₀ ℝ at v
  apply Finsupp.ext
  intro s
  change T.projectHead H (T.projectHead H v) s = T.projectHead H v s
  simp [FiniteRootedTree.projectHead, Finsupp.filter_apply]
  intro hs hs'
  exact (hs hs').elim

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[continuity, fun_prop] lemma continuous_P (s : ι) : Continuous (P T s) :=
  Completion.continuous_extension

@[continuity, fun_prop] lemma continuous_Q (s : ι) : Continuous (Q T s) :=
  Completion.continuous_extension

lemma P_sub_Q (s : ι) (x : TreeSpace T) : P T s x - Q T s x = coordinate T s x := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq ((continuous_P T s).sub (continuous_Q T s))
        (coordinate T s).continuous
  | ih v => simpa using T.P_sub_Q v s

theorem norm_eq (x : TreeSpace T) : ‖x‖ = P T T.root x + Q T T.root x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq continuous_norm ((continuous_P T T.root).add (continuous_Q T T.root))
  | ih v => simp [TreeVector.norm_def, FiniteRootedTree.normSum]

lemma projection_contracts (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    ‖projection T H hH x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (continuous_norm.comp (projection T H hH).continuous) continuous_norm
  | ih v => simpa only [projection_coe, Completion.norm_coe] using
      TreeVector.projection_contracts T H hH v

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    projection T H hH (projection T H hH x) = projection T H hH x := by
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v => simp only [projection_coe, TreeVector.projection_idem]

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma restrict_initial (K : Finset ι) (hK : T.Initial K) (H : Finset ι)
    (hH : T.Initial H) :
    (T.restrict K hK).Initial (Finset.univ.filter (fun s : K => s.1 ∈ H)) := by
  constructor
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH.1
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH.2 s.1 (Finset.mem_filter.mp hs).2⟩

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma ofHead_support (H : Finset ι) (f : H → ℝ) :
    (show ι →₀ ℝ from ofHead T H f).support ⊆ H := by
  intro s hs
  by_contra hh
  have he : (ofHead T H f) s = 0 := by rw [ofHead_apply, dite_eq_right hh]
  exact (Finsupp.mem_support_iff.mp hs) he

lemma not_finite_dimensional {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) [Infinite ι] :
    ¬Module.Finite ℝ (TreeVector T) := by
  intro h
  let : Module.Finite ℝ (ι →₀ ℝ) := h
  exact Infinite.not_finite (Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis ι ℝ (ι →₀ ℝ)))

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem supported_is_finite (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T)
    (hx : projection T H hH x = x) :
    ∃ v : TreeVector T, (v : TreeSpace T) = x ∧ (show ι →₀ ℝ from v).support ⊆ H := by
  refine ⟨TreeVector.ofHead T H (headCoordinates T H x), ?_, TreeVector.ofHead_support T H _⟩
  rw [← projection_reconstructs T H hH x, hx]

theorem not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (TreeSpace T) := by
  intro h
  let := h
  have hf := FiniteDimensional.of_injective
    (Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).toLinearMap
    (Completion.coe_injective (TreeVector T))
  exact TreeVector.not_finite_dimensional T hf

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma nontrivial_space (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    Nontrivial F.space := by
  by_contra hn
  have : Subsingleton F.space := not_nontrivial_iff_subsingleton.mp hn
  let := F.finiteQuotient
  exact hE (Module.Finite.of_submodule_quotient F.space)

lemma exists_unit (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    ∃ y ∈ F.space, ‖y‖ = 1 := by
  have := F.nontrivial_space hE
  obtain ⟨y, hy⟩ := exists_norm_eq F.space (by norm_num : (0 : ℝ) ≤ 1)
  exact ⟨y, y.2, hy⟩

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.ZeroRootGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

theorem XSigma_averaged_modulus {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t ^ 3 / 128 ≤ averagedModulus XSigma t :=
  TreeSpace.averaged_modulus_cubic sequenceTree ht ht1

theorem XJoined_averaged_modulus {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t ^ 3 / 128 ≤ averagedModulus XJoined t :=
  TreeSpace.averaged_modulus_cubic joinedTree ht ht1

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma norm_inclusion (v : ZeroTreeVector T) : ‖inclusion T v‖ = 2 * ‖v‖ := by
  rw [inclusion_apply, norm_half]
  ring

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma norm_inclusion (x : ZeroTreeSpace T) : ‖inclusion T x‖ = 2 * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
      rw [inclusion_coe, Completion.norm_coe, Completion.norm_coe]
      exact ZeroTreeVector.norm_inclusion T v

lemma inclusion_injective : Function.Injective (inclusion T) := by
  intro x y h
  have he : inclusion T (x - y) = 0 := by rw [map_sub, h, sub_self]
  have hn := norm_inclusion T (x - y)
  rw [he, norm_zero] at hn
  have hz : ‖x - y‖ = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma root_zero (x : ZeroTreeSpace T) : TreeSpace.coordinate T T.root (inclusion T x) = 0 := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_const
  | ih v =>
      rw [inclusion_coe, TreeSpace.coordinate_coe]
      exact ZeroTreeVector.root_zero T v

theorem norm_eq_common (x : ZeroTreeSpace T) :
    ‖x‖ = TreeSpace.P T T.root (inclusion T x) ∧
      ‖x‖ = TreeSpace.Q T T.root (inclusion T x) := by
  have hdiff := TreeSpace.P_sub_Q T T.root (inclusion T x)
  rw [root_zero] at hdiff
  have hnorm := TreeSpace.norm_eq T (inclusion T x)
  rw [norm_inclusion] at hnorm
  constructor <;> linarith

lemma inclusion_projection (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    inclusion T (projection T H hH x) = TreeSpace.projection T H hH (inclusion T x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v => simp only [projection_coe, inclusion_coe, TreeSpace.projection_coe,
      ZeroTreeVector.inclusion_projection]

lemma projection_contracts (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    ‖projection T H hH x‖ ≤ ‖x‖ := by
  have h := TreeSpace.projection_contracts T H hH (inclusion T x)
  rw [← inclusion_projection, norm_inclusion, norm_inclusion] at h
  linarith

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    projection T H hH (projection T H hH x) = projection T H hH x := by
  apply inclusion_injective T
  rw [inclusion_projection, inclusion_projection, TreeSpace.projection_idem]

lemma include_tail (H : Finset ι) (hH : T.Initial H) (z : ZeroTreeSpace T)
    (hz : z ∈ tail T H hH) : inclusion T z ∈ TreeSpace.tail T H hH := by
  change TreeSpace.projection T H hH (inclusion T z) = 0
  rw [← inclusion_projection, show projection T H hH z = 0 from hz, map_zero]

theorem homogeneous_cubic (x : ZeroTreeSpace T) {H : Finset ι} (hH : T.Initial H)
    (hx : projection T H hH x = x) (z : ZeroTreeSpace T)
    (hz : z ∈ tail T H hH) (hz0 : z ≠ 0) :
    (‖x + z‖ + ‖x - z‖) / 2 ≥ ‖x‖ + ‖z‖ ^ 3 / (8 * (2 * ‖x‖ + ‖z‖) ^ 2) := by
  obtain ⟨v, hv, hvH⟩ := TreeSpace.supported_is_finite T H hH (inclusion T x) (by
    rw [← inclusion_projection, hx])
  have he := TreeSpace.homogeneous_cubic_tail T v hH hvH (inclusion T z)
    (include_tail T H hH z hz) (fun h => hz0 ((inclusion T).map_eq_zero_iff (inclusion_injective T) |>.mp h))
  rw [hv, ← map_add, ← map_sub, norm_inclusion, norm_inclusion, norm_inclusion,
    norm_inclusion] at he
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hden : 0 < 8 * (2 * ‖x‖ + ‖z‖) ^ 2 := by positivity
  have hscale : (2 * ‖z‖) ^ 3 / (8 * (2 * (2 * ‖x‖) + 2 * ‖z‖) ^ 2) =
      2 * (‖z‖ ^ 3 / (8 * (2 * ‖x‖ + ‖z‖) ^ 2)) := by
    field_simp

  rw [hscale] at he
  linarith

end ZeroTreeSpace

theorem XZero_homogeneous_cubic (x : XZero) {H : Finset JoinedNode}
    (hH : joinedTree.Initial H) (hx : ZeroTreeSpace.projection joinedTree H hH x = x)
    (z : XZero) (hz : z ∈ ZeroTreeSpace.tail joinedTree H hH) (hz0 : z ≠ 0) :
    (‖x + z‖ + ‖x - z‖) / 2 ≥ ‖x‖ + ‖z‖ ^ 3 / (8 * (2 * ‖x‖ + ‖z‖) ^ 2) :=
  ZeroTreeSpace.homogeneous_cubic joinedTree x hH hx z hz hz0

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (ZeroTreeVector T) := by
  intro h
  have : Module.Finite ℝ (TreeVector.coordinate T T.root).ker := h
  have : Module.Finite ℝ (TreeVector T ⧸ (TreeVector.coordinate T T.root).ker) :=
    Submodule.CoFG.ker (TreeVector.coordinate T T.root).toLinearMap
  exact TreeVector.not_finite_dimensional T
    (Module.Finite.of_submodule_quotient (TreeVector.coordinate T T.root).ker)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[continuity, fun_prop] lemma continuous_P (s : ι) : Continuous (P T s) := by
  exact (TreeSpace.continuous_P T s).comp (inclusion T).continuous

@[continuity, fun_prop] lemma continuous_Q (s : ι) : Continuous (Q T s) := by
  exact (TreeSpace.continuous_Q T s).comp (inclusion T).continuous

lemma coordinate_projection (H : Finset ι) (hH : T.Initial H) (s : ι) (x : ZeroTreeSpace T) :
    coordinate T s (projection T H hH x) = if s ∈ H then coordinate T s x else 0 := by
  change TreeSpace.coordinate T s (inclusion T (projection T H hH x)) = _
  rw [inclusion_projection, TreeSpace.coordinate_projection]
  rfl

lemma tail_closed (H : Finset ι) (hH : T.Initial H) :
    IsClosed (tail T H hH : Set (ZeroTreeSpace T)) := (projection T H hH).isClosed_ker

lemma tail_finite_codimension (H : Finset ι) (hH : T.Initial H) :
    Module.Finite ℝ (ZeroTreeSpace T ⧸ tail T H hH) := by
  rw [tail_eq_coordinate_kernel]
  exact Submodule.CoFG.ker (headCoordinates T H).toLinearMap

theorem not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (ZeroTreeSpace T) := by
  intro h
  let := h
  have hf := FiniteDimensional.of_injective
    (Completion.toComplL : ZeroTreeVector T →L[ℝ] ZeroTreeSpace T).toLinearMap
    (Completion.coe_injective (ZeroTreeVector T))
  exact ZeroTreeVector.not_finite_dimensional T hf

end ZeroTreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

end RecursivePotentials

end

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.EquivalentNorms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

lemma upper_pos : 0 < A.upper := A.lower_pos.trans_le A.lower_le_upper

lemma nonneg (x : E) : 0 ≤ A.N x := apply_nonneg _ _

lemma pos {x : E} (hx : x ≠ 0) : 0 < A.N x :=
  (mul_pos A.lower_pos (norm_pos_iff.mpr hx)).trans_le (A.lower_bound x)

lemma sub_le (x y : E) : A.N x - A.N y ≤ A.N (x - y) := by
  have h := map_add_le_add A.N (x - y) y
  rw [sub_add_cancel] at h
  linarith

lemma lipschitz_estimate (x y : E) : |A.N x - A.N y| ≤ A.upper * ‖x - y‖ := by
  apply abs_le.mpr
  constructor
  · have h := A.sub_le y x
    have hb := A.upper_bound (y - x)
    rw [norm_sub_rev] at hb
    linarith
  · exact (A.sub_le x y).trans (A.upper_bound (x - y))

lemma exists_unit (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    ∃ y ∈ F.space, A.N y = 1 := by
  obtain ⟨x, hx, hxn⟩ := F.exists_unit hE
  have hx0 : x ≠ 0 := by intro he; simp [he] at hxn
  have hp := A.pos hx0
  refine ⟨(A.N x)⁻¹ • x, F.space.smul_mem _ hx, ?_⟩
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

lemma inner_nonempty (x : E) (t : ℝ) (F : CofiniteSubspace E)
    (hE : ¬Module.Finite ℝ E) :
    {r : ℝ | ∃ y ∈ F.space, A.N y = 1 ∧ r = A.N (x + t • y) - 1}.Nonempty := by
  obtain ⟨y, hy, hy1⟩ := A.exists_unit F hE
  exact ⟨_, y, hy, hy1, rfl⟩

lemma inner_bddBelow (x : E) (t : ℝ) (F : CofiniteSubspace E) :
    BddBelow {r : ℝ | ∃ y ∈ F.space, A.N y = 1 ∧ r = A.N (x + t • y) - 1} := by
  refine ⟨-1, ?_⟩
  rintro r ⟨y, hy, hy1, rfl⟩
  linarith [A.nonneg (x + t • y)]

lemma inner_upper {x : E} (hx : A.N x = 1) {t : ℝ} (ht : 0 ≤ t)
    (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) : A.inner x t F ≤ t := by
  obtain ⟨y, hy, hy1⟩ := A.exists_unit F hE
  have hi : A.inner x t F ≤ A.N (x + t • y) - 1 :=
    csInf_le (A.inner_bddBelow x t F) ⟨y, hy, hy1, rfl⟩
  have h := map_add_le_add A.N x (t • y)
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht, hx, hy1, mul_one] at h
  linarith

end EquivalentNorm

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end ZeroTreeSpace

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

lemma continuous : Continuous A.N := by
  have h : LipschitzWith ⟨A.upper, A.upper_pos.le⟩ A.N := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (A.N x) (A.N y) ≤ A.upper * dist x y
    rw [Real.dist_eq, dist_eq_norm]
    exact A.lipschitz_estimate x y
  exact h.continuous

lemma norming_functional {x : E} (hx : x ≠ 0) :
    ∃ f : E →L[ℝ] ℝ, f x = A.N x ∧ ∀ y, ‖f y‖ ≤ A.N y := by
  let e := LinearEquiv.toSpanNonzeroSingleton ℝ E x hx
  let f : Module.Dual ℝ (Submodule.span ℝ {x}) := (A.N x) • e.symm.toLinearMap
  have hb : ∀ y : Submodule.span ℝ {x}, ‖f y‖ ≤ A.N y := by
    intro y
    obtain ⟨r, rfl⟩ := e.surjective y
    have he : ((e r : Submodule.span ℝ {x}) : E) = r • x := rfl
    change ‖A.N x * e.symm (e r)‖ ≤ _
    rw [e.symm_apply_apply, he, map_smul_eq_mul, norm_mul, Real.norm_of_nonneg (A.nonneg x)]
    exact le_of_eq (mul_comm _ _)
  obtain ⟨g, hg, hgb⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    (Submodule.span ℝ {x}) f A.continuous hb
  refine ⟨g, ?_, hgb⟩
  have he : ((e 1 : Submodule.span ℝ {x}) : E) = x := by
    change (1 : ℝ) • x = x
    simp
  have hg1 := hg (e 1)
  rw [he] at hg1
  simpa [f] using hg1

lemma modulus_nonneg (hE : ¬Module.Finite ℝ E) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ A.modulus t := by
  have hn : {r : ℝ | ∃ x : E, A.N x = 1 ∧ r = sSup (Set.range (A.inner x t))}.Nonempty := by
    obtain ⟨x, hx, hx1⟩ := A.exists_unit CofiniteSubspace.top hE
    exact ⟨_, x, hx1, rfl⟩
  apply le_csInf hn
  rintro r ⟨x, hx1, rfl⟩
  have hx : x ≠ 0 := by intro he; simp [he] at hx1
  obtain ⟨f, hfx, hf⟩ := A.norming_functional hx
  let F : CofiniteSubspace E := ⟨f.ker, f.isClosed_ker, Submodule.CoFG.ker f.toLinearMap⟩
  have hi : 0 ≤ A.inner x t F := by
    apply le_csInf (A.inner_nonempty x t F hE)
    rintro r ⟨y, hy, hy1, rfl⟩
    have hy0 : f y = 0 := hy
    have hb := hf (x + t • y)
    rw [map_add, map_smul, hy0, smul_zero, add_zero, hfx, hx1, norm_one] at hb
    linarith
  have hb : BddAbove (Set.range (A.inner x t)) := by
    refine ⟨t, ?_⟩
    rintro r ⟨F, rfl⟩
    exact A.inner_upper hx1 ht F hE
  exact hi.trans (le_csSup hb (Set.mem_range_self _))

end EquivalentNorm

theorem bounded_trees_modulus_eq_zero {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬Module.Finite ℝ E) (A : EquivalentNorm E) (u : ℕ → List ℕ → E)
    {m M c : ℝ} (hm : 0 < m) (hM : 0 < M) (hc : 0 < c)
    (hu : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length ≤ h → m ≤ ‖u h s‖ ∧ ‖u h s‖ ≤ M)
    (hd : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      WeaklyNull (fun k => u h (s ++ [k]) - u h s))
    (hdc : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      ∀ k, c ≤ ‖u h (s ++ [k]) - u h s‖) :
    A.modulus (A.lower * c / (2 * A.upper * M)) = 0 := by
  apply le_antisymm (bounded_trees_modulus_le_zero hE A u hm hM hc hu hd hdc)
  apply A.modulus_nonneg hE
  have := A.lower_pos
  have := A.upper_pos
  positivity

end RecursivePotentials

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.JoinedGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end FiniteRootedTree

open Filter Topology

open scoped ENNReal

noncomputable section

lemma isReflexive_iff {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsReflexive E ↔ ∀ F : (E →L[ℝ] ℝ) →L[ℝ] ℝ, ∃ x : E, ∀ f : E →L[ℝ] ℝ, F f = f x := by
  constructor
  · intro h F
    obtain ⟨x, hx⟩ := h F
    exact ⟨x, fun f => (congrArg (fun G : (E →L[ℝ] ℝ) →L[ℝ] ℝ => G f) hx).symm⟩
  · intro h F
    obtain ⟨x, hx⟩ := h F
    exact ⟨x, ContinuousLinearMap.ext (fun f => (hx f).symm)⟩

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

end SquareSum

end

open UniformSpace

noncomputable section

lemma IsReflexive.prod {E : Type uSpace} {F : Type uOther} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hE : IsReflexive E) (hF : IsReflexive F) :
    IsReflexive (E × F) := by
  rw [isReflexive_iff] at hE hF ⊢
  intro G
  let D₁ : (E →L[ℝ] ℝ) →L[ℝ] ((E × F) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (E × F) E ℝ).flip (ContinuousLinearMap.fst ℝ E F)
  let D₂ : (F →L[ℝ] ℝ) →L[ℝ] ((E × F) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (E × F) F ℝ).flip (ContinuousLinearMap.snd ℝ E F)
  obtain ⟨x, hx⟩ := hE (G.comp D₁)
  obtain ⟨y, hy⟩ := hF (G.comp D₂)
  refine ⟨(x, y), ?_⟩
  intro f
  let f₁ := f.comp (ContinuousLinearMap.inl ℝ E F)
  let f₂ := f.comp (ContinuousLinearMap.inr ℝ E F)
  have hf : f = D₁ f₁ + D₂ f₂ := by
    apply ContinuousLinearMap.ext
    intro z
    change f z = f (z.1, 0) + f (0, z.2)
    rw [← map_add]
    simp
  rw [hf, map_add]
  change G (D₁ f₁) + G (D₂ f₂) = f₁ x + f₂ y
  exact congrArg₂ (· + ·) (hx f₁) (hy f₂)

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

end SquareSum

end

namespace TreeVector

open scoped ENNReal

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeVector

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem finite_height_isReflexive (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : IsReflexive (TreeSpace T) :=
  hilbert_isReflexive.of_equiv (hilbertEquiv T h hh).symm

end

end TreeSpace

namespace Joined

noncomputable section

open UniformSpace

lemma components_reflexive (h : ℕ+) : IsReflexive (Component h) :=
  TreeSpace.finite_height_isReflexive (componentTree h) h.val (fun s => s.2)

theorem outer_isReflexive : IsReflexive Outer := SquareSum.isReflexive Component components_reflexive

end

end Joined

theorem XJoined_isReflexive : IsReflexive XJoined :=
  (hilbert_isReflexive (E := ℝ)).prod Joined.outer_isReflexive |>.of_equiv Joined.freeEquiv.symm

namespace Joined

noncomputable section

open UniformSpace

end

end Joined

theorem XZero_isReflexive : IsReflexive XZero := Joined.outer_isReflexive.of_equiv Joined.zeroEquiv.symm

noncomputable section

lemma logarithmicGamma_pos {M β : ℝ} (hβ : 0 < β) (hM : β ≤ M) :
    0 < logarithmicGamma M β := by
  have hm : 0 < M := hβ.trans_le hM
  unfold logarithmicGamma
  positivity

end

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

open Filter

open scoped Topology

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem averaged_modulus_all_radii_lower [Infinite ι] {t : ℝ} (ht : 0 < t) :
    min t (1/2) ^ 3 / 128 ≤ averagedModulus (TreeSpace T) t := by
  apply averagedModulus_lower_of_witness (not_finite_dimensional T) ht.le
  intro x hx ε hε
  obtain ⟨v, hv, hvx⟩ := finite_unit_dense T x hx hε
  let H := T.head (show ι →₀ ℝ from v)
  have hH : T.Initial H := T.head_initial v
  refine ⟨cofiniteTail T H hH, ?_⟩
  intro y hy hy1
  have hty : t ≤ ‖t • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hzy : t • y ∈ tail T H hH := (tail T H hH).smul_mem t hy
  have hfinite := finite_center_midpoint_gap T v hH (T.support_subset_head v) hv
    (t • y) hzy (lt_min ht (by norm_num))
      ((min_le_right t (1/2)).trans_lt (by norm_num)) ((min_le_left _ _).trans hty)
  have h₁ : ‖(v : TreeSpace T) + t • y‖ ≤ ‖x + t • y‖ + ‖(v : TreeSpace T) - x‖ := by
    calc
      ‖(v : TreeSpace T) + t • y‖ = ‖x + t • y + ((v : TreeSpace T) - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have h₂ : ‖(v : TreeSpace T) - t • y‖ ≤ ‖x - t • y‖ + ‖(v : TreeSpace T) - x‖ := by
    calc
      ‖(v : TreeSpace T) - t • y‖ = ‖x - t • y + ((v : TreeSpace T) - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  unfold averagedGain
  linarith

theorem averaged_modulus_pos [Infinite ι] {t : ℝ} (ht : 0 < t) :
    0 < averagedModulus (TreeSpace T) t :=
  lt_of_lt_of_le (by positivity : 0 < min t (1/2) ^ 3 / 128)
    (averaged_modulus_all_radii_lower T ht)

end

end TreeSpace

section Lens

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_center_le {x y : E} {R : ℝ} (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) : ‖x‖ ≤ R := by
  have h := norm_add_le (x+y) (x-y)
  have he : x+y+(x-y) = (2 : ℝ) • x := by module
  rw [he, norm_smul] at h
  norm_num at h
  linarith

lemma norm_perturbation_le {x y : E} {R : ℝ} (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) : ‖y‖ ≤ R := by
  apply norm_center_le (x := y) (y := x)
  · simpa [add_comm] using hp
  · simpa [norm_sub_rev] using hm

end Lens

namespace TreeSpace

noncomputable section

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

theorem XJoined_separated_families {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      (ε ≤ 2 → η = min (1/2) (logarithmicGamma 2 (ε/16))) ∧
      ∀ (x : XJoined) (z : ℕ → XJoined),
        (∀ n, ‖x+z n‖ ≤ 1) → (∀ n, ‖x-z n‖ ≤ 1) →
        (∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖ ≤ 1-η := by
  by_cases hε2 : ε ≤ 2
  · refine ⟨min (1/2) (logarithmicGamma 2 (ε/16)), ?_, ?_, fun _ => rfl, ?_⟩
    · exact lt_min (by norm_num) (logarithmicGamma_pos (by positivity) (by linarith))
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · exact fun x z hp hm hs => TreeSpace.separated_midpoint_families joinedTree hε hε2 x z hp hm hs
  · refine ⟨1/2, by norm_num, by norm_num, fun h => (hε2 h).elim, ?_⟩
    intro x z hp hm hs
    have h0 := norm_perturbation_le (hp 0) (hm 0)
    have h1 := norm_perturbation_le (hp 1) (hm 1)
    have hsep := hs 0 1 (by norm_num)
    have htri := norm_sub_le (z 0) (z 1)
    exfalso; linarith

end RecursivePotentials

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.VariableCompletion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

namespace VariableTree

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end VariableTree

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

@[continuity, fun_prop] lemma continuous_P (s : ι) : Continuous (P T e s) :=
  Completion.continuous_extension

@[continuity, fun_prop] lemma continuous_Q (s : ι) : Continuous (Q T e s) :=
  Completion.continuous_extension

lemma P_nonneg (s : ι) (x : AggregationSpace T e) : 0 ≤ P T e s x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le continuous_const (continuous_P T e s)
  | ih v => simpa using VariableTree.P_nonneg T e v s

lemma Q_nonneg (s : ι) (x : AggregationSpace T e) : 0 ≤ Q T e s x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le continuous_const (continuous_Q T e s)
  | ih v => simpa using VariableTree.Q_nonneg T e v s

theorem norm_eq (x : AggregationSpace T e) : ‖x‖ = P T e T.root x + Q T e T.root x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq continuous_norm ((continuous_P T e T.root).add (continuous_Q T e T.root))
  | ih v => simp [AggregationVector.norm_def, VariableTree.normSum]

lemma coordinate_projection (H : Finset ι) (hH : T.Initial H) (s : ι) (x : AggregationSpace T e) :
    coordinate T e s (projection T e H hH x) = if s ∈ H then coordinate T e s x else 0 := by
  induction x using Completion.induction_on with
  | hp =>
      by_cases hs : s ∈ H
      · simp only [ite_eq_left hs]
        exact isClosed_eq (by fun_prop) (by fun_prop)
      · simp only [ite_eq_right hs]
        exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
      rw [projection_coe, coordinate_coe, coordinate_coe]
      exact VariableTree.projectHead_apply T H v s

end AggregationSpace

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma ofHead_apply (H : Finset ι) (f : H → ℝ) (s : ι) :
    ofHead T e H f s = if hs : s ∈ H then f ⟨s, hs⟩ else 0 := by
  change FiniteRootedTree.extend H f s = _
  simp [FiniteRootedTree.extend]

lemma ofHead_support (H : Finset ι) (f : H → ℝ) :
    (show ι →₀ ℝ from ofHead T e H f).support ⊆ H := by
  intro s hs
  by_contra hh
  have he : (ofHead T e H f) s = 0 := by rw [ofHead_apply, dite_eq_right hh]
  exact (Finsupp.mem_support_iff.mp hs) he

lemma basisVector_apply (s c : ι) : basisVector T e s c = if s = c then 1 else 0 :=
  Finsupp.single_apply

lemma not_finite_dimensional {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent) [Infinite ι] : ¬Module.Finite ℝ (AggregationVector T e) := by
  intro h
  let : Module.Finite ℝ (ι →₀ ℝ) := h
  exact Infinite.not_finite (Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis ι ℝ (ι →₀ ℝ)))

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem projection_reconstructs (H : Finset ι) (hH : T.Initial H) (x : AggregationSpace T e) :
    projection T e H hH x = ((AggregationVector.ofHead T e H (headCoordinates T e H x)) : AggregationSpace T e) := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (projection T e H hH).continuous
      · exact ((Completion.toComplL : AggregationVector T e →L[ℝ] AggregationSpace T e).comp
          ((AggregationVector.ofHead T e H).comp (headCoordinates T e H))).continuous
  | ih v =>
      rw [projection_coe]
      apply congrArg ((↑) : AggregationVector T e → AggregationSpace T e)
      apply Finsupp.ext
      intro s
      change VariableTree.projectHead T H v s = AggregationVector.ofHead T e H (headCoordinates T e H (v : AggregationSpace T e)) s
      rw [AggregationVector.ofHead_apply]
      have hp := VariableTree.projectHead_apply T H (show ι →₀ ℝ from v) s
      rw [hp]
      by_cases hs : s ∈ H
      · simp only [ite_eq_left hs, dite_eq_left hs, headCoordinates_apply, coordinate_coe]
      · simp only [ite_eq_right hs, dite_eq_right hs]

theorem supported_is_finite (H : Finset ι) (hH : T.Initial H) (x : AggregationSpace T e)
    (hx : projection T e H hH x = x) :
    ∃ v : AggregationVector T e, (v : AggregationSpace T e) = x ∧ (show ι →₀ ℝ from v).support ⊆ H := by
  refine ⟨AggregationVector.ofHead T e H (headCoordinates T e H x), ?_, AggregationVector.ofHead_support T e H _⟩
  rw [← projection_reconstructs T e H hH x, hx]

theorem not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (AggregationSpace T e) := by
  intro h
  let := h
  have hf := FiniteDimensional.of_injective
    (Completion.toComplL : AggregationVector T e →L[ℝ] AggregationSpace T e).toLinearMap
    (Completion.coe_injective (AggregationVector T e))
  exact AggregationVector.not_finite_dimensional T e hf

end AggregationSpace

namespace VariableExponent

lemma cubicConstant_pos : 0 < cubicConstant := by unfold cubicConstant; positivity

lemma cubicConstant_le_one : cubicConstant ≤ 1 := by
  have he : 1 ≤ 6 * Real.exp 1 := by linarith [Real.exp_one_gt_two]
  have hi : (6 * Real.exp 1)⁻¹ ≤ (1 : ℝ) := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) he
  exact (pow_le_pow_left₀ (by positivity) hi 3).trans_eq (one_pow 3)

lemma sixthConstant_pos : 0 < sixthConstant := by unfold sixthConstant; positivity

end VariableExponent

namespace VariableTree

open VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem normSum_cubic (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x z : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hx : x.support ⊆ H) (hz : ∀ s ∈ H, z s = 0) :
    cubicConstant * normSum T e z ^ 3 ≤
      ((normSum T e (x+z) + normSum T e (x-z))/2 - normSum T e x) *
        max (normSum T e (x+z)) (normSum T e (x-z)) ^ 2 := by
  let K := T.ancestorClosure (x.support ∪ z.support)
  have hK : T.Initial K := T.ancestorClosure_initial _
  have hxK : x.support ⊆ K := (Finset.subset_union_left).trans (T.subset_ancestorClosure _)
  have hzK : z.support ⊆ K := (Finset.subset_union_right).trans (T.subset_ancestorClosure _)
  have hpK : (x+z).support ⊆ K := Finsupp.support_add.trans (Finset.union_subset hxK hzK)
  have hmK : (x-z).support ⊆ K := Finsupp.support_sub.trans (Finset.union_subset hxK hzK)
  let U := T.restrict K hK
  let xf : K → ℝ := fun c => x c.1
  let zf : K → ℝ := fun c => z c.1
  have hxf : ∀ s ∉ Finset.univ.filter (fun s : K => s.1 ∈ H), xf s = 0 := by
    intro s hs
    have hsH : s.1 ∉ H := by simpa using hs
    exact Finsupp.notMem_support_iff.mp (fun hs => hsH (hx hs))
  have hzf : ∀ s ∈ Finset.univ.filter (fun s : K => s.1 ∈ H), zf s = 0 := by
    intro s hs; exact hz s.1 (Finset.mem_filter.mp hs).2
  have hstepU : ∀ c, c ≠ U.root → U.depth c = U.depth (U.parent c) + 1 := by
    intro c hc
    exact hstep c.1 (fun heq => hc (Subtype.ext heq))
  have hheightU : ∀ s, U.depth s ≤ h.val := fun s => hheight s.1
  have hh := finite_cubic U e h he (T.restrict_initial K hK H hH) hxf hzf hstepU hheightU
  have hn₁ : normSum T e x = U.pRootSum e xf := normSum_on_head T e x K hK hxK
  have hn₂ : normSum T e z = U.pRootSum e zf := normSum_on_head T e z K hK hzK
  have hn₃ : normSum T e (x+z) = U.pRootSum e (xf+zf) := normSum_on_head T e (x+z) K hK hpK
  have hn₄ : normSum T e (x-z) = U.pRootSum e (xf-zf) := normSum_on_head T e (x-z) K hK hmK
  rwa [hn₁, hn₂, hn₃, hn₄]

end VariableTree

namespace AggregationSpace

open UniformSpace VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem cubic_projected_tail (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x : AggregationVector T e) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : AggregationSpace T e) :
    cubicConstant * ‖z - projection T e H hH z‖ ^ 3 ≤
      ((‖(x : AggregationSpace T e) + (z-projection T e H hH z)‖ +
          ‖(x : AggregationSpace T e) - (z-projection T e H hH z)‖)/2 - ‖(x : AggregationSpace T e)‖) *
        max ‖(x : AggregationSpace T e) + (z-projection T e H hH z)‖
          ‖(x : AggregationSpace T e) - (z-projection T e H hH z)‖ ^ 2 := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih v =>
    simp only [projection_coe, ← Completion.coe_sub, ← Completion.coe_add, Completion.norm_coe,
      AggregationVector.norm_def]
    apply VariableTree.normSum_cubic T e h he hstep hheight x _ hH hx
    intro s hs
    change v s - VariableTree.projectHead T H v s = 0
    exact sub_eq_zero.mpr ((VariableTree.projectHead_apply T H (show ι →₀ ℝ from v) s).trans (ite_eq_left hs)).symm

theorem cubic_tail (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x : AggregationVector T e) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : AggregationSpace T e)
    (hz : z ∈ tail T e H hH) :
    cubicConstant * ‖z‖ ^ 3 ≤
      ((‖(x : AggregationSpace T e)+z‖ + ‖(x : AggregationSpace T e)-z‖)/2 - ‖(x : AggregationSpace T e)‖) *
        max ‖(x : AggregationSpace T e)+z‖ ‖(x : AggregationSpace T e)-z‖ ^ 2 := by
  have hh := cubic_projected_tail T e h he hstep hheight x hH hx z
  have hz0 : projection T e H hH z = 0 := hz
  simpa only [hz0,sub_zero] using hh

theorem cubic_supported (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x z : AggregationSpace T e) {H : Finset ι} (hH : T.Initial H)
    (hx : projection T e H hH x = x) (hz : z ∈ tail T e H hH) :
    cubicConstant * ‖z‖ ^ 3 ≤
      ((‖x+z‖ + ‖x-z‖)/2 - ‖x‖) * max ‖x+z‖ ‖x-z‖ ^ 2 := by
  obtain ⟨v,rfl,hv⟩ := supported_is_finite T e H hH x hx
  exact cubic_tail T e h he hstep hheight v hH hv z hz

lemma cubic_zero (z : AggregationSpace T e) :
    cubicConstant * ‖z‖ ^ 3 ≤
      ((‖(0 : AggregationSpace T e)+z‖ + ‖(0 : AggregationSpace T e)-z‖)/2 - ‖(0 : AggregationSpace T e)‖) *
        max ‖(0 : AggregationSpace T e)+z‖ ‖(0 : AggregationSpace T e)-z‖ ^ 2 := by
  simp only [zero_add,zero_sub,norm_neg,norm_zero,sub_zero,max_self]
  have hh := mul_le_mul_of_nonneg_right cubicConstant_le_one (pow_nonneg (norm_nonneg z) 3)
  nlinarith

end AggregationSpace

end RecursivePotentials

end

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.VariableLp ----
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

open Filter Topology TopologicalSpace

open scoped ENNReal

noncomputable section

namespace LpSupport

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
  [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

end LpSupport

namespace PowerExponent

end PowerExponent

namespace ScalarLp

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι]

variable (p q : PowerExponent) (hpq : p.val.HolderConjugate q.val)

include hpq

theorem isReflexive : IsReflexive (Space ι p) := by
  rw [isReflexive_iff]
  intro F
  let G : Space ι q →L[ℝ] ℝ := F.comp (pairing p q hpq)
  let x := restrict q p hpq.symm G
  have hG : G = (pairing p q hpq).flip x := by
    apply lp.ext_continuousLinearMap ENNReal.ofReal_ne_top
    intro i
    apply ContinuousLinearMap.ext
    intro a
    change G (lp.single _ i a) = pairing p q hpq (lp.single _ i a) x
    rw [apply_single]

    rw [pairing_single_left]
    rfl
  refine ⟨x, ?_⟩
  intro f
  have hh := congrArg (fun H : Space ι q →L[ℝ] ℝ => H (restrict p q hpq f)) hG
  change F (pairing p q hpq (restrict p q hpq f)) = pairing p q hpq (restrict p q hpq f) x at hh
  simpa only [pairing_restrict] using hh

end ScalarLp

end

namespace AggregationVector

noncomputable section

open scoped ENNReal

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end

end AggregationVector

namespace AggregationSpace

noncomputable section

open AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma lpEquiv_coe (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (v : AggregationVector T e) :
    lpEquiv T e hp hstep h hh (v : AggregationSpace T e) = toLpLinear T e v :=
  ContinuousLinearMap.fromCompletion_apply_coe _ v

lemma lpEquiv_apply (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (x : AggregationSpace T e) (s : ι) :
    lpEquiv T e hp hstep h hh x s = coordinate T e s x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq; exact ((lp.evalCLM ℝ (fun _ : ι => ℝ) (ENNReal.ofReal e.val) s).comp (lpEquiv T e hp hstep h hh).toContinuousLinearMap).continuous; exact (coordinate T e s).continuous
  | ih v => rw [lpEquiv_coe,toLpLinear_apply,coordinate_coe]

theorem finite_height_reflexive (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : IsReflexive (AggregationSpace T e) := by
  let p : PowerExponent := ⟨e.val,hp⟩
  exact (ScalarLp.isReflexive p p.conjugate p.holder (ι := ι)).of_equiv (lpEquiv T e hp hstep h hh).symm

end

end AggregationSpace

end RecursivePotentials

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.VariableStability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

open Filter Topology TopologicalSpace

open scoped ENNReal

namespace VariableExponent

noncomputable section

lemma holder_mixed {ι : Type uIndex} (S : Finset ι) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (a b : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i) :
    ∑ i ∈ S, a i ^ r * b i ^ (1-r) ≤ (∑ i ∈ S, a i) ^ r * (∑ i ∈ S, b i) ^ (1-r) := by
  have hq : 0 < 1-r := by linarith
  have hpq := Real.HolderConjugate.inv_inv hr hq (by ring : r+(1-r)=1)
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg S hpq
    (fun i hi => Real.rpow_nonneg (ha i hi) r) (fun i hi => Real.rpow_nonneg (hb i hi) (1-r))
  have he₁ : ∀ i ∈ S, (a i ^ r) ^ r⁻¹ = a i := by
    intro i hi; rw [← Real.rpow_mul (ha i hi),mul_inv_cancel₀ hr.ne',Real.rpow_one]
  have he₂ : ∀ i ∈ S, (b i ^ (1-r)) ^ (1-r)⁻¹ = b i := by
    intro i hi; rw [← Real.rpow_mul (hb i hi),mul_inv_cancel₀ hq.ne',Real.rpow_one]
  simp_rw [Finset.sum_congr rfl he₁, Finset.sum_congr rfl he₂] at hh
  simpa only [one_div,inv_inv] using hh

lemma cuberoot_cube {a : ℝ} (ha : 0 ≤ a) : (a ^ 3) ^ (1/3:ℝ) = a := by
  rw [← Real.rpow_natCast,← Real.rpow_mul ha]
  norm_num

lemma cube_cuberoot {a : ℝ} (ha : 0 ≤ a) : (a ^ (1/3:ℝ)) ^ 3 = a := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

lemma cube_two_thirds {a : ℝ} (ha : 0 ≤ a) : (a ^ (2/3:ℝ)) ^ 3 = a ^ 2 := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

lemma square_cuberoot {a : ℝ} (ha : 0 ≤ a) : (a ^ 2) ^ (1/3:ℝ) = a ^ (2/3:ℝ) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul ha]
  norm_num

lemma cubic_transport {ι : Type uIndex} (S : Finset ι) {C : ℝ} (hC : 0 ≤ C)
    (a b d : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i)
    (hd : ∀ i ∈ S, 0 ≤ d i) (h : ∀ i ∈ S, C * a i ^ 3 ≤ b i * d i ^ 2) :
    C * (∑ i ∈ S, a i)^3 ≤ (∑ i ∈ S, b i) * (∑ i ∈ S, d i)^2 := by
  have hr (i) (hi : i ∈ S) : C ^ (1/3:ℝ) * a i ≤ b i ^ (1/3:ℝ) * d i ^ (2/3:ℝ) := by
    have hh := Real.rpow_le_rpow (mul_nonneg hC (pow_nonneg (ha i hi) 3)) (h i hi) (by norm_num : (0:ℝ)≤1/3)
    rw [Real.mul_rpow hC (pow_nonneg (ha i hi) 3),cuberoot_cube (ha i hi),
      Real.mul_rpow (hb i hi) (sq_nonneg _),square_cuberoot (hd i hi)] at hh
    exact hh
  have hmixed := holder_mixed S (by norm_num : (0:ℝ)<1/3) (by norm_num : (1/3:ℝ)<1) b d hb hd
  norm_num only at hmixed
  have hs := (Finset.sum_le_sum hr).trans hmixed
  rw [← Finset.mul_sum] at hs
  norm_num only at hs
  have hB : 0 ≤ ∑ i ∈ S, b i := Finset.sum_nonneg hb
  have hdS : 0 ≤ ∑ i ∈ S, d i := Finset.sum_nonneg hd
  have hh := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg hC _) (Finset.sum_nonneg ha)) hs 3
  rw [mul_pow,mul_pow,cube_cuberoot hC,cube_cuberoot hB,cube_two_thirds hdS] at hh
  exact hh

lemma cubic_transport_tsum {ι : Type uIndex} {C : ℝ} (hC : 0 ≤ C)
    (a b d : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hd : ∀ i, 0 ≤ d i)
    (has : Summable a) (hbs : Summable b) (hds : Summable d)
    (h : ∀ i, C*a i^3 ≤ b i*d i^2) :
    C*(∑' i, a i)^3 ≤ (∑' i, b i)*(∑' i, d i)^2 := by
  classical
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (has.hasSum.pow 3))
    (Filter.Tendsto.mul hbs.hasSum (hds.hasSum.pow 2))
    (Filter.Eventually.of_forall fun S => cubic_transport S hC a b d
      (fun i hi => ha i) (fun i hi => hb i) (fun i hi => hd i) (fun i hi => h i))

lemma energy_of_cubic {C a b B Y : ℝ} (_hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (_hY : 0 ≤ Y) (hBm : B ≤ (a+b)/2)
    (hcubic : C*Y^3 ≤ ((a+b)/2-B)*max a b ^ 2) :
    C*Y^3 ≤ (a^2+b^2-2*B^2)*max a b := by
  let M := max a b
  let D := (a+b)/2-B
  have hM : 0 ≤ M := ha.trans (le_max_left _ _)
  have hD : 0 ≤ D := sub_nonneg.mpr hBm
  have hMsum : M ≤ a+b := max_le (by linarith) (by linarith)
  have hE : D*M ≤ a^2+b^2-2*B^2 := by
    have hh := mul_nonneg hD (show 0 ≤ a+b-M by linarith)
    have hx := mul_nonneg hD hB
    dsimp [D] at *
    nlinarith [sq_nonneg (a-b)]
  exact hcubic.trans (by simpa only [M,pow_two,mul_assoc] using mul_le_mul_of_nonneg_right hE hM)

section Outer

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
  [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

lemma outer_hasSum_square {ι : Type uIndex} [DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] (x : Outer E) :
    HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (by norm_num : (0:ℝ)<(2 : ENNReal).toReal) x

lemma norm_midpoint_average {F : Type uOther} [NormedAddCommGroup F] [NormedSpace ℝ F] (x y : F) :
    ‖x‖ ≤ (‖x+y‖+‖x-y‖)/2 ∧ ‖y‖ ≤ (‖x+y‖+‖x-y‖)/2 := by
  have hx := norm_add_le (x+y) (x-y)
  have hy := norm_sub_le (x+y) (x-y)
  have h₁ : x+y+(x-y) = (2:ℝ) • x := by module
  have h₂ : x+y-(x-y) = (2:ℝ) • y := by module
  rw [h₁,norm_smul] at hx
  rw [h₂,norm_smul] at hy
  norm_num only [Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at hx hy
  constructor <;> linarith

lemma midpoint_energy_nonneg {F : Type uOther} [NormedAddCommGroup F] [NormedSpace ℝ F] (x y : F) :
    0 ≤ ‖x+y‖^2+‖x-y‖^2-2*‖x‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg x) (norm_midpoint_average x y).1 2
  nlinarith [sq_nonneg (‖x+y‖-‖x-y‖)]

theorem outer_sixth_of_components {C : ℝ} (hC : 0 ≤ C) (x y : Outer E)
    (hc : ∀ i, C*‖y i‖^6 ≤ (‖x i+y i‖^2+‖x i-y i‖^2-2*‖x i‖^2)*
      (‖x i+y i‖^2+‖x i-y i‖^2)^2) :
    C*‖y‖^6 ≤ (‖x+y‖^2+‖x-y‖^2-2*‖x‖^2)*(‖x+y‖^2+‖x-y‖^2)^2 := by
  have hp : HasSum (fun i => ‖x i+y i‖^2) (‖x+y‖^2) := outer_hasSum_square E (x+y)
  have hm : HasSum (fun i => ‖x i-y i‖^2) (‖x-y‖^2) := outer_hasSum_square E (x-y)
  have hx := outer_hasSum_square E x
  have hy := outer_hasSum_square E y
  have hS := hp.add hm
  have hD := hS.sub (hx.mul_left 2)
  have hh := cubic_transport_tsum hC (fun i => ‖y i‖^2)
    (fun i => ‖x i+y i‖^2+‖x i-y i‖^2-2*‖x i‖^2)
    (fun i => ‖x i+y i‖^2+‖x i-y i‖^2)
    (fun i => sq_nonneg _) (fun i => midpoint_energy_nonneg (x i) (y i)) (fun i => by positivity)
    hy.summable hD.summable hS.summable (fun i => by convert hc i using 1 ; ring)
  rw [hy.tsum_eq,hD.tsum_eq,hS.tsum_eq] at hh
  convert hh using 1 ; ring

theorem outer_cubic_squared {C : ℝ} (hC : 0 ≤ C) (x y : Outer E)
    (hc : ∀ i, C*‖y i‖^3 ≤ ((‖x i+y i‖+‖x i-y i‖)/2-‖x i‖)*max ‖x i+y i‖ ‖x i-y i‖^2) :
    C^2*‖y‖^6 ≤ (‖x+y‖^2+‖x-y‖^2)*(‖x+y‖^2+‖x-y‖^2-2*‖x‖^2)^2 := by
  let A := fun i => ‖x i+y i‖
  let B := fun i => ‖x i-y i‖
  let M := fun i => max (A i) (B i)
  let D := fun i => A i^2+B i^2-2*‖x i‖^2
  have hM (i) : 0 ≤ M i := (norm_nonneg _).trans (le_max_left _ _)
  have hD (i) : 0 ≤ D i := midpoint_energy_nonneg (x i) (y i)
  have hc' (i) : C*‖y i‖^3 ≤ D i*M i :=
    energy_of_cubic hC (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_midpoint_average (x i) (y i)).1 (hc i)
  have hMi (i) : M i^2 ≤ A i^2+B i^2 := by
    rcases le_total (A i) (B i) with hh | hh
    · dsimp only [M]; rw [max_eq_right hh]; linarith [sq_nonneg (A i)]
    · dsimp only [M]; rw [max_eq_left hh]; linarith [sq_nonneg (B i)]
  have hp : HasSum (fun i => A i^2) (‖x+y‖^2) := outer_hasSum_square E (x+y)
  have hm : HasSum (fun i => B i^2) (‖x-y‖^2) := outer_hasSum_square E (x-y)
  have hx := outer_hasSum_square E x
  have hy := outer_hasSum_square E y
  have hS := hp.add hm
  have hDs : HasSum D (‖x+y‖^2+‖x-y‖^2-2*‖x‖^2) := hS.sub (hx.mul_left 2)
  have hMs : Summable (fun i => M i^2) := Summable.of_nonneg_of_le (fun i => sq_nonneg _) hMi hS.summable
  have hh := cubic_transport_tsum (sq_nonneg C) (fun i => ‖y i‖^2) (fun i => M i^2) D
    (fun i => sq_nonneg _) (fun i => sq_nonneg _) hD hy.summable hMs hDs.summable
    (fun i => by have hh := pow_le_pow_left₀ (mul_nonneg hC (pow_nonneg (norm_nonneg _) 3)) (hc' i) 2; nlinarith [sq_nonneg (C*‖y i‖^3)])
  have hMsum : (∑' i, M i^2) ≤ ‖x+y‖^2+‖x-y‖^2 := by
    rw [← hS.tsum_eq]
    exact Summable.tsum_le_tsum hMi hMs hS.summable
  calc
    C^2*‖y‖^6 = C^2*(∑' i, ‖y i‖^2)^3 := by rw [hy.tsum_eq]; ring
    _ ≤ (∑' i, M i^2)*(∑' i, D i)^2 := hh
    _ ≤ (‖x+y‖^2+‖x-y‖^2)*(∑' i, D i)^2 := mul_le_mul_of_nonneg_right hMsum (sq_nonneg _)
    _ = _ := by rw [hDs.tsum_eq]

theorem outer_cubic_of_components {C : ℝ} (hC : 0 ≤ C) (x y : Outer E)
    (hc : ∀ i, C*‖y i‖^3 ≤ ((‖x i+y i‖+‖x i-y i‖)/2-‖x i‖)*max ‖x i+y i‖ ‖x i-y i‖^2)
    {R : ℝ} (hR : 0 < R) (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖x‖^2 + C/(2*Real.sqrt 2*R)*‖y‖^3 ≤ R^2 := by
  have hh := outer_cubic_squared E hC x y hc
  have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hD := midpoint_energy_nonneg x y
  have hx : ‖x‖ ≤ R := by have hx := (norm_midpoint_average x y).1; linarith
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have he : (‖x+y‖^2+‖x-y‖^2-2*‖x‖^2)^2 ≤ (2*(R^2-‖x‖^2))^2 := by
    exact pow_le_pow_left₀ hD (by linarith) 2
  have hh' : C^2*‖y‖^6 ≤ (2*R^2)*(2*(R^2-‖x‖^2))^2 := hh.trans
    (mul_le_mul (by linarith) he (sq_nonneg _) (by positivity))
  have hq : 0 < 2*Real.sqrt 2*R := by positivity
  have hsq : (2*Real.sqrt 2*R*(R^2-‖x‖^2))^2 = (2*R^2)*(2*(R^2-‖x‖^2))^2 := by
    calc
      _ = 4*(Real.sqrt 2)^2*R^2*(R^2-‖x‖^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]; ring
  have hfinal : C*‖y‖^3 ≤ 2*Real.sqrt 2*R*(R^2-‖x‖^2) := by
    apply (sq_le_sq₀ (mul_nonneg hC (pow_nonneg (norm_nonneg _) 3)) (mul_nonneg hq.le (sub_nonneg.mpr hx2))).mp
    rw [hsq]
    calc
      (C*‖y‖^3)^2 = C^2*‖y‖^6 := by ring
      _ ≤ _ := hh'
  have hd : C*‖y‖^3/(2*Real.sqrt 2*R) ≤ R^2-‖x‖^2 := (div_le_iff₀ hq).mpr (by simpa only [mul_comm (R^2-‖x‖^2)] using hfinal)
  have heq : C*‖y‖^3/(2*Real.sqrt 2*R) = C/(2*Real.sqrt 2*R)*‖y‖^3 := by ring
  rw [heq] at hd
  linarith

end Outer

end

end VariableExponent

namespace AggregationVector

noncomputable section

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end

end AggregationVector

namespace AggregationSpace

noncomputable section

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

@[continuity,fun_prop] lemma continuous_childP (s : ι) :
    Continuous (childP T e s) := Completion.continuous_extension

@[continuity,fun_prop] lemma continuous_childQ (s : ι) :
    Continuous (childQ T e s) := Completion.continuous_extension

lemma childP_apply (s c : ι) (x : AggregationSpace T e) :
    childP T e s x c = if c ≠ T.root ∧ T.parent c = s then P T e c x else 0 := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (lp.evalCLM ℝ (fun _ : ι => ℝ) (ENNReal.ofReal e.val) c).continuous.comp (continuous_childP T e s)
      · split_ifs <;> fun_prop
  | ih v => simp only [childP_coe,P_coe,AggregationVector.childP,AggregationVector.childLp_apply]

lemma childQ_apply (s c : ι) (x : AggregationSpace T e) :
    childQ T e s x c = if c ≠ T.root ∧ T.parent c = s then Q T e c x else 0 := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (lp.evalCLM ℝ (fun _ : ι => ℝ) (ENNReal.ofReal e.val) c).continuous.comp (continuous_childQ T e s)
      · split_ifs <;> fun_prop
  | ih v => simp only [childQ_coe,Q_coe,AggregationVector.childQ,AggregationVector.childLp_apply]

theorem recursion (s : ι) (x : AggregationSpace T e) :
    (P T e s x,Q T e s x) = leastPair (coordinate T e s x) ‖childP T e s x‖ ‖childQ T e s x‖ := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · fun_prop
      · unfold leastPair
        fun_prop
  | ih v => simpa only [P_coe,Q_coe,coordinate_coe,childP_coe,childQ_coe] using
      AggregationVector.finite_recursion T e s v

lemma childP_norm_formula (s : ι) (x : AggregationSpace T e) :
    ‖childP T e s x‖ = (∑' c, if c ≠ T.root ∧ T.parent c = s then P T e c x ^ e.val else 0) ^ (1/e.val) := by
  rw [lp.norm_eq_tsum_rpow (by simpa only [ENNReal.toReal_ofReal e.pos.le] using e.pos)]
  simp only [ENNReal.toReal_ofReal e.pos.le,Real.norm_eq_abs,childP_apply]
  congr 1
  apply tsum_congr
  intro c
  split_ifs <;> simp [abs_of_nonneg (P_nonneg T e c x),Real.zero_rpow e.ne_zero]

lemma childQ_norm_formula (s : ι) (x : AggregationSpace T e) :
    ‖childQ T e s x‖ = (∑' c, if c ≠ T.root ∧ T.parent c = s then Q T e c x ^ e.val else 0) ^ (1/e.val) := by
  rw [lp.norm_eq_tsum_rpow (by simpa only [ENNReal.toReal_ofReal e.pos.le] using e.pos)]
  simp only [ENNReal.toReal_ofReal e.pos.le,Real.norm_eq_abs,childQ_apply]
  congr 1
  apply tsum_congr
  intro c
  split_ifs <;> simp [abs_of_nonneg (Q_nonneg T e c x),Real.zero_rpow e.ne_zero]

end

end AggregationSpace

namespace Variable

noncomputable section

open UniformSpace VariableExponent Filter Topology TopologicalSpace

lemma component_comparisons (h : ℕ+) (x : Component h) :
    (h.val+1:ℝ)^(-1/heightExponent h)*‖componentEquiv h x‖ ≤ ‖x‖ ∧
    ‖x‖ ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖componentEquiv h x‖ :=
  AggregationSpace.lp_comparisons (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h) x

lemma component_reflexive (h : ℕ+) : IsReflexive (Component h) :=
  AggregationSpace.finite_height_reflexive (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h)

theorem reflexive : IsReflexive Xv := SquareSum.isReflexive Component component_reflexive

lemma componentEquiv_apply (h : ℕ+) (x : Component h) (s : ComponentNode h) :
    componentEquiv h x s = componentCoordinate h s x :=
  AggregationSpace.lpEquiv_apply (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h) x s

lemma component_ext (h : ℕ+) {x y : Component h}
    (he : ∀ s, componentCoordinate h s x = componentCoordinate h s y) : x = y := by
  apply (componentEquiv h).injective
  apply Subtype.ext
  funext s
  exact (componentEquiv_apply h x s).trans ((he s).trans (componentEquiv_apply h y s).symm)

lemma coordinates_ext {x y : Xv} (h : ∀ s, coordinate s x = coordinate s y) : x = y := by
  apply Subtype.ext
  funext i
  exact component_ext i (fun s => h ⟨i,s⟩)

lemma coordinate_basis (s t : Node) : coordinate s (basis t) = if s = t then 1 else 0 := by
  obtain ⟨h,s⟩ := s
  obtain ⟨k,t⟩ := t
  by_cases he : h = k
  · subst k
    simp only [coordinate_apply,basis,lp.single_apply_self,componentCoordinate,
      AggregationSpace.coordinate_coe,AggregationVector.basisVector_apply]
    congr 1
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,eq_comm]
  · rw [coordinate_apply,basis,lp.single_apply_ne _ _ _ he,map_zero,ite_eq_right]
    intro hh
    exact he (congrArg Sigma.fst hh)

lemma projection_apply (S : Finset Node) (x : Xv) :
    projection S x = ∑ s ∈ S, coordinate s x • basis s := by
  simp [projection]

lemma coordinate_projection (S : Finset Node) (s : Node) (x : Xv) :
    coordinate s (projection S x) = if s ∈ S then coordinate s x else 0 := by
  rw [projection_apply,map_sum]
  simp only [map_smul,coordinate_basis,smul_eq_mul,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq]

lemma projection_idem (S : Finset Node) (x : Xv) :
    projection S (projection S x) = projection S x := by
  apply coordinates_ext
  intro s
  simp only [coordinate_projection]
  split_ifs <;> rfl

lemma component_projection_fixed (h : ℕ+) (H : Finset (ComponentNode h))
    (hH : (componentTree h).Initial H) (x : Component h)
    (hx : ∀ s ∉ H, componentCoordinate h s x = 0) :
    AggregationSpace.projection (componentTree h) (exponent h) H hH x = x := by
  apply component_ext h
  intro s
  rw [componentCoordinate,AggregationSpace.coordinate_projection]
  split_ifs with hs
  · rfl
  · exact (hx s hs).symm

lemma component_mem_tail (h : ℕ+) (H : Finset (ComponentNode h)) (hH : (componentTree h).Initial H)
    (y : Component h) (hy : ∀ s ∈ H, componentCoordinate h s y = 0) :
    y ∈ AggregationSpace.tail (componentTree h) (exponent h) H hH := by
  change AggregationSpace.projection (componentTree h) (exponent h) H hH y = 0
  apply component_ext h
  intro s
  rw [map_zero,componentCoordinate,AggregationSpace.coordinate_projection]
  split_ifs with hs
  · exact hy s hs
  · rfl

lemma component_cubic (x y : Xv) (A : ∀ h, Finset (ComponentNode h)) (hA : AdmissibleHeads x y A)
    (h : ℕ+) :
    cubicConstant*‖y h‖^3 ≤ ((‖x h+y h‖+‖x h-y h‖)/2-‖x h‖)*max ‖x h+y h‖ ‖x h-y h‖^2 := by
  by_cases hx : x h = 0
  · rw [hx]
    exact AggregationSpace.cubic_zero (componentTree h) (exponent h) (y h)
  · obtain ⟨hH,hxH,hyH⟩ := hA h hx
    exact AggregationSpace.cubic_supported (componentTree h) (exponent h) h rfl
      (component_step h) (component_height h) (x h) (y h) hH
      (component_projection_fixed h (A h) hH (x h) hxH) (component_mem_tail h (A h) hH (y h) hyH)

lemma component_sixth (x y : Xv) (A : ∀ h, Finset (ComponentNode h)) (hA : AdmissibleHeads x y A)
    (h : ℕ+) :
    sixthConstant*‖y h‖^6 ≤ (‖x h+y h‖^2+‖x h-y h‖^2-2*‖x h‖^2)*(‖x h+y h‖^2+‖x h-y h‖^2)^2 := by
  have hmid := norm_midpoint_average (x h) (y h)
  exact sixth_of_cubic (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hmid.1 hmid.2 (component_cubic x y A hA h)

theorem cubic_stability (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (hA : AdmissibleHeads x y A) {R : ℝ} (hR : 0 < R) (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖x‖^2+cubicConstant/(2*Real.sqrt 2*R)*‖y‖^3 ≤ R^2 :=
  outer_cubic_of_components Component cubicConstant_pos.le x y (component_cubic x y A hA) hR hp hm

theorem sixth_stability (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (hA : AdmissibleHeads x y A) :
    sixthConstant*‖y‖^6/(‖x+y‖^2+‖x-y‖^2)^2 ≤ ‖x+y‖^2+‖x-y‖^2-2*‖x‖^2 := by
  have hh := outer_sixth_of_components Component sixthConstant_pos.le x y (component_sixth x y A hA)
  by_cases hz : ‖x+y‖^2+‖x-y‖^2 = 0
  · rw [hz,zero_pow (by decide : 2 ≠ 0),div_zero]
    have hmid := midpoint_energy_nonneg x y
    rwa [hz] at hmid
  · exact (div_le_iff₀ (sq_pos_of_pos (lt_of_le_of_ne (by positivity) (Ne.symm hz)))).mpr hh

end

end Variable

namespace ScalarLp

noncomputable section

open Filter Topology

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι]

lemma coordinate_cofinite {ι : Type uIndex} [DecidableEq ι] (p : PowerExponent) (x : Space ι p) :
    Tendsto (fun i => x i) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := ((lp.memℓp x).summable (by simpa only [ENNReal.toReal_ofReal p.pos.le] using p.pos)).tendsto_cofinite_zero
  simp only [ENNReal.toReal_ofReal p.pos.le] at hh
  have hout := (Real.continuous_rpow_const (one_div_pos.mpr p.pos).le).continuousAt.tendsto.comp hh
  simpa only [Function.comp_def,← Real.rpow_mul (norm_nonneg _),mul_one_div_cancel p.ne_zero,
    Real.rpow_one,Real.zero_rpow (one_div_ne_zero p.ne_zero)] using hout

lemma basis_functionals_tendsto_zero (p : PowerExponent) (s : ℕ → ι) (hs : Function.Injective s)
    (f : Space ι p →L[ℝ] ℝ) :
    Tendsto (fun n => f (lp.single (ENNReal.ofReal p.val) (s n) 1)) atTop (𝓝 0) := by
  have hh := (coordinate_cofinite p.conjugate (restrict p p.conjugate p.holder f)).comp
    (hs.tendsto_cofinite.mono_left Filter.atTop_le_cofinite)
  exact hh

end

end ScalarLp

namespace Variable

noncomputable section

open UniformSpace VariableExponent Filter Topology TopologicalSpace

lemma finite_single (h : ℕ+) (v : AggregationVector (componentTree h) (exponent h)) :
    FiniteTotalSupport (lp.single 2 h (v : Component h)) := by
  refine ⟨(show ComponentNode h →₀ ℝ from v).support.image (Sigma.mk h),?_⟩
  rintro ⟨k,s⟩ hs
  by_cases he : k = h
  · subst k
    rw [coordinate_apply,lp.single_apply_self,componentCoordinate,AggregationSpace.coordinate_coe]
    apply Finsupp.notMem_support_iff.mp
    intro hh
    exact hs (Finset.mem_image.mpr ⟨s,hh,rfl⟩)
  · rw [coordinate_apply,lp.single_apply_ne _ _ _ he,map_zero]

lemma finite_support_dense : Dense {x : Xv | FiniteTotalSupport x} := by
  change Dense (finiteSubmodule : Set Xv)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply SquareSum.closedSubmodule_eq_top Component _ finiteSubmodule.isClosed_topologicalClosure
  intro h x
  induction x using Completion.induction_on with
  | hp =>
      exact finiteSubmodule.isClosed_topologicalClosure.preimage (lp.singleContinuousLinearMap ℝ Component 2 h).continuous
  | ih v => exact finiteSubmodule.le_topologicalClosure (finite_single h v)

lemma projection_finite_rank (S : Finset Node) : FiniteDimensional ℝ (projection S).range := by
  let V := Submodule.span ℝ (basis '' (S : Set Node))
  let : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (S.finite_toSet.image basis)
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  rintro z ⟨x,rfl⟩
  rw [ContinuousLinearMap.coe_coe,projection_apply]
  exact V.sum_mem fun s hs => V.smul_mem _ (Submodule.subset_span ⟨s,hs,rfl⟩)

lemma projection_weaklyNull {y : ℕ → Xv} (hy : WeaklyNull y) (S : Finset Node) :
    Tendsto (fun j => projection S (y j)) atTop (𝓝 0) := by
  have hh := tendsto_finsetSum S (fun s hs => (hy (coordinate s)).smul_const (basis s))
  simpa only [zero_smul,Finset.sum_const_zero,← projection_apply] using hh

lemma fiber_mem (S : Finset Node) (h : ℕ+) (s : ComponentNode h) :
    s ∈ fiber S h ↔ (⟨h,s⟩ : Node) ∈ S := Finset.mem_preimage

lemma heads_admissible (w y : Xv) (S : Finset Node) (hw : ∀ s ∉ S, coordinate s w = 0) :
    AdmissibleHeads w (y-projection (ancestralUnion S) y) (ancestralHeads S) := by
  intro h hh
  have hnon : h ∈ S.image Sigma.fst := by
    by_contra hn
    apply hh
    apply component_ext h
    intro s
    rw [map_zero]
    exact hw ⟨h,s⟩ (fun hs => hn (Finset.mem_image.mpr ⟨⟨h,s⟩,hs,rfl⟩))
  refine ⟨(componentTree h).ancestorClosure_initial _,?_,?_⟩
  · intro s hs
    exact hw ⟨h,s⟩ (fun hm => hs ((componentTree h).subset_ancestorClosure _ ((fiber_mem S h s).mpr hm)))
  · intro s hs
    change coordinate ⟨h,s⟩ (y-projection (ancestralUnion S) y) = 0
    have hm : (⟨h,s⟩ : Node) ∈ ancestralUnion S := Finset.mem_sigma.mpr ⟨hnon,hs⟩
    rw [map_sub,coordinate_projection,ite_eq_left hm,sub_self]

lemma weakTailConstant_pos : 0 < weakTailConstant := by
  unfold weakTailConstant
  exact div_pos cubicConstant_pos (by positivity)

lemma cubic_stability_mul (w z : Xv) (hw : FiniteTotalSupport w)
    (A : ∀ h, Finset (ComponentNode h)) (hA : AdmissibleHeads w z A)
    {R : ℝ} (hR : 0 < R) (hp : ‖w+z‖ ≤ R) (hm : ‖w-z‖ ≤ R) :
    ‖w‖^2*R+weakTailConstant*‖z‖^3 ≤ R^3 := by
  have hh := mul_le_mul_of_nonneg_right (cubic_stability w z hw A hA hR hp hm) hR.le
  have he : (‖w‖^2+cubicConstant/(2*Real.sqrt 2*R)*‖z‖^3)*R =
      ‖w‖^2*R+weakTailConstant*‖z‖^3 := by
    unfold weakTailConstant
    field_simp [hR.ne']
  rw [he] at hh
  calc
    _ ≤ R^2*R := hh
    _ = R^3 := by ring

lemma finite_center_weak_bound (x : Xv) {ε : ℝ} (hε : 0 < ε)
    (y : ℕ → Xv) (hy : WeaklyNull y) (hyε : ∀ j, ε ≤ ‖y j‖)
    (hp : ∀ j, ‖x+y j‖ ≤ 1) (hm : ∀ j, ‖x-y j‖ ≤ 1)
    (w : Xv) (hw : FiniteTotalSupport w) :
    ‖w‖^2*(1+‖x-w‖)+weakTailConstant*ε^3 ≤ (1+‖x-w‖)^3 := by
  obtain ⟨S,hS⟩ := hw
  let P := projection (ancestralUnion S)
  let d : ℕ → ℝ := fun j => ‖P (y j)‖
  let z : ℕ → Xv := fun j => y j-P (y j)
  let C : ℝ := 1+‖x-w‖
  let R : ℕ → ℝ := fun j => C+d j
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [norm_zero] using (projection_weaklyNull hy (ancestralUnion S)).norm
  have hR : Tendsto R atTop (𝓝 C) := by
    simpa only [add_zero] using tendsto_const_nhds.add hd
  have hpos (j) : 0 < R j := by dsimp [R,C,d]; positivity
  have hplus (j) : ‖w+z j‖ ≤ R j := by
    calc
      ‖w+z j‖ = ‖(x+y j)+(w-x)-P (y j)‖ := by congr 1; dsimp [z]; abel
      _ ≤ ‖x+y j‖+‖w-x‖+‖P (y j)‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 1+‖x-w‖+d j := by rw [norm_sub_rev w x]; gcongr; exact hp j
      _ = R j := rfl
  have hminus (j) : ‖w-z j‖ ≤ R j := by
    calc
      ‖w-z j‖ = ‖(x-y j)+(w-x)+P (y j)‖ := by congr 1; dsimp [z]; abel
      _ ≤ ‖x-y j‖+‖w-x‖+‖P (y j)‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 1+‖x-w‖+d j := by rw [norm_sub_rev w x]; gcongr; exact hm j
      _ = R j := rfl
  have hineq (j) : ‖w‖^2*R j+weakTailConstant*‖z j‖^3 ≤ R j^3 :=
    cubic_stability_mul w (z j) ⟨S,hS⟩ (ancestralHeads S) (heads_admissible w (y j) S hS)
      (hpos j) (hplus j) (hminus j)
  have hlow (j) : ε-d j ≤ ‖z j‖ :=
    (sub_le_sub_right (hyε j) _).trans (norm_sub_norm_le (y j) (P (y j)))
  have hev : ∀ᶠ j in atTop, ‖w‖^2*R j+weakTailConstant*(ε-d j)^3 ≤ R j^3 := by
    filter_upwards [hd.eventually (eventually_lt_nhds hε)] with j hj
    apply le_trans _ (hineq j)
    gcongr
    · exact weakTailConstant_pos.le
    · exact hlow j
  have hl : Tendsto (fun j => ‖w‖^2*R j+weakTailConstant*(ε-d j)^3) atTop
      (𝓝 (‖w‖^2*C+weakTailConstant*(ε-0)^3)) :=
    (tendsto_const_nhds.mul hR).add
      (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hd).pow 3))
  have hh := le_of_tendsto_of_tendsto hl (hR.pow 3) hev
  simpa only [sub_zero] using hh

theorem weak_null_cubic (x : Xv) {ε : ℝ} (hε : 0 < ε)
    (y : ℕ → Xv) (hy : WeaklyNull y) (hyε : ∀ j, ε ≤ ‖y j‖)
    (hp : ∀ j, ‖x+y j‖ ≤ 1) (hm : ∀ j, ‖x-y j‖ ≤ 1) :
    ‖x‖^2+weakTailConstant*ε^3 ≤ 1 := by
  let K : Set Xv := {w | ‖w‖^2*(1+‖x-w‖)+weakTailConstant*ε^3 ≤ (1+‖x-w‖)^3}
  have hc : IsClosed K := isClosed_le (by fun_prop) (by fun_prop)
  have hi : {w : Xv | FiniteTotalSupport w} ⊆ K :=
    fun w hw => finite_center_weak_bound x hε y hy hyε hp hm w hw
  have hx : x ∈ K := closure_minimal hi hc (finite_support_dense x)
  simpa only [K,Set.mem_ofPred_eq,sub_self,norm_zero,add_zero,mul_one,one_pow] using hx

theorem weak_tail (x : Xv) {ε : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (y : ℕ → Xv) (hy : WeaklyNull y) (hyε : ∀ j, ε ≤ ‖y j‖)
    (hp : ∀ j, ‖x+y j‖ ≤ 1) (hm : ∀ j, ‖x-y j‖ ≤ 1) :
    ‖x‖ ≤ theta ε ∧ theta ε < 1 := by
  have hh := weak_null_cubic x hε y hy hyε hp hm
  have hr : 0 ≤ 1-weakTailConstant*ε^3 := by nlinarith [sq_nonneg ‖x‖]
  constructor
  · exact (Real.le_sqrt (norm_nonneg x) hr).mpr (by linarith)
  · apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr
    have hpos : 0 < weakTailConstant*ε^3 := mul_pos weakTailConstant_pos (pow_pos hε 3)
    norm_num
    linarith

end

end Variable

end RecursivePotentials

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.Main ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

open Filter Topology TopologicalSpace

open scoped ENNReal

namespace VariableTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma path_upper (s : ι) : GlobalUpper T e (T.path s) := by
  intro a S hS
  apply (e.agg_le_iff S (T.path s) (T.path_nonneg s a)).mpr
  have hpow (c) : |T.path s c|^e.val = (T.path s c)^2 := by
    rw [T.path_apply]
    split_ifs <;> simp [Real.zero_rpow e.ne_zero]
  calc
    _ = ∑ c ∈ S, T.path s c^2 := Finset.sum_congr rfl (fun c hc => hpow c)
    _ ≤ T.path s a^2 := T.path_upper s a S hS
    _ = T.path s a^e.val := by rw [←hpow,abs_of_nonneg (T.path_nonneg s a)]

lemma path_fields (s c : ι) : P T e (T.path s) c = T.path s c ∧ Q T e (T.path s) c = 0 := by
  have hh := potentials_minimal T e (T.path s) (T.path s) 0 (T.path_nonneg s)
    (fun _ => le_rfl) (fun _ => sub_zero _) (path_upper T e s)
    (by intro s S hs; exact (e.agg_zero S).le) c
  have hq : Q T e (T.path s) c = 0 := le_antisymm hh.2 (Q_nonneg T e _ _)
  have hp := P_sub_Q T e (T.path s) c
  rw [hq,sub_zero] at hp
  exact ⟨hp,hq⟩

lemma normSum_path (s : ι) : normSum T e (T.path s) = 1 := by
  unfold normSum
  rw [(path_fields T e s T.root).1,(path_fields T e s T.root).2,T.path_root,add_zero]

lemma twice_coordinate_le_normSum (v : ι →₀ ℝ) (hv : v T.root = 0) (s : ι) :
    2*|v s| ≤ normSum T e v := by
  have hd := P_sub_Q T e v T.root
  rw [hv] at hd
  have hp := (P_upper T e v).le_root T e (P_nonneg T e v) s
  have hq := (Q_upper T e v).le_root T e (Q_nonneg T e v) s
  have hc := P_sub_Q T e v s
  have hp0 := P_nonneg T e v s
  have hq0 := Q_nonneg T e v s
  unfold normSum
  rcases le_total 0 (v s) with hs | hs
  · rw [abs_of_nonneg hs]; linarith
  · rw [abs_of_nonpos hs]; linarith

end VariableTree

namespace Variable

open UniformSpace VariableExponent Filter Topology

lemma componentEquiv_basis (h : ℕ+) (s : ComponentNode h) :
    componentEquiv h (componentBasis h s) = lp.single (ENNReal.ofReal (heightExponent h)) s 1 := by
  apply Subtype.ext
  funext t
  rw [componentEquiv_apply,componentBasis,componentCoordinate,AggregationSpace.coordinate_coe,
    AggregationVector.basisVector_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

lemma componentBasis_lower (h : ℕ+) (s : ComponentNode h) (hs : s ≠ (componentTree h).root) :
    2 ≤ ‖componentBasis h s‖ := by
  rw [componentBasis,Completion.norm_coe,AggregationVector.norm_def]
  have hh := VariableTree.twice_coordinate_le_normSum (componentTree h) (exponent h)
    (Finsupp.single s 1) (by simp [hs]) s
  simpa only [AggregationVector.basisVector,Finsupp.single_eq_same,abs_one,mul_one] using hh

lemma componentBasis_weaklyNull (h : ℕ+) (s : ℕ → ComponentNode h) (hs : Function.Injective s) :
    WeaklyNull (fun n => componentBasis h (s n)) := by
  intro f
  let p : PowerExponent := ⟨heightExponent h,heightExponent_gt_one h⟩
  let : Fact (1 ≤ ENNReal.ofReal p.val) := ⟨ENNReal.one_le_ofReal.mpr p.one_lt.le⟩
  have hh := ScalarLp.basis_functionals_tendsto_zero p s hs
    (f.comp (componentEquiv h).symm.toContinuousLinearMap)
  convert hh using 1
  funext n
  change f (componentBasis h (s n)) = f ((componentEquiv h).symm (lp.single _ (s n) 1))
  exact congrArg f (((componentEquiv h).symm_apply_apply (componentBasis h (s n))).symm.trans
    (congrArg (componentEquiv h).symm (componentEquiv_basis h (s n))))

lemma basis_weaklyNull (h : ℕ+) (s : ℕ → ComponentNode h) (hs : Function.Injective s) :
    WeaklyNull (fun n => basis ⟨h,s n⟩) := by
  intro f
  exact componentBasis_weaklyNull h s hs (f.comp (lp.singleContinuousLinearMap ℝ Component 2 h))

lemma componentPath_norm (h : ℕ+) (s : ComponentNode h) : ‖componentPath h s‖ = 1 := by
  let v : AggregationVector (componentTree h) (exponent h) := (componentTree h).path s
  change ‖(v : Component h)‖ = 1
  exact (Completion.norm_coe v).trans (VariableTree.normSum_path (componentTree h) (exponent h) s)

lemma componentPath_step (h : ℕ+) (s : ComponentNode h) (hs : s ≠ (componentTree h).root) :
    componentPath h s-componentPath h ((componentTree h).parent s) = componentBasis h s := by
  change ((↑(show AggregationVector (componentTree h) (exponent h) from (componentTree h).path s)) : Component h)-
    ↑(show AggregationVector (componentTree h) (exponent h) from (componentTree h).path ((componentTree h).parent s)) = _
  rw [←Completion.coe_sub]
  apply congrArg (fun a : AggregationVector (componentTree h) (exponent h) => (a : Component h))
  change (componentTree h).path s-(componentTree h).path ((componentTree h).parent s) = Finsupp.single s 1
  rw [(componentTree h).path_step s hs]
  abel

lemma pathVector_norm (h : ℕ) (s : List ℕ) : ‖pathVector h s‖ = 1 := by
  rw [pathVector,lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2),componentPath_norm]

lemma pathNode_child (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    pathNode h (s++[k]) ≠ (componentTree (pathHeight h)).root ∧
      (componentTree (pathHeight h)).parent (pathNode h (s++[k])) = pathNode h s := by
  have hs' : s.length ≤ h := hs.le
  have hsk : (s++[k]).length ≤ h := by simp; omega
  constructor
  · intro he
    have hh := congrArg Subtype.val he
    simp only [pathNode,componentTree,List.take_of_length_le hsk,List.append_eq_nil_iff,List.cons_ne_self, and_false] at hh
  · apply Subtype.ext
    simp [componentTree,pathNode,List.take_of_length_le hs',List.take_of_length_le hsk]

lemma pathVector_step (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    pathVector h (s++[k])-pathVector h s = basis ⟨(pathHeight h),children h s hs k⟩ := by
  have hh := componentPath_step (pathHeight h) (pathNode h (s++[k])) (pathNode_child h s hs k).1
  rw [(pathNode_child h s hs k).2] at hh
  change lp.single 2 _ _-lp.single 2 _ _ = _
  rw [←lp.single_sub,hh]
  rfl

lemma pathVector_increments (h : ℕ) (s : List ℕ) (hs : s.length < h) :
    WeaklyNull (fun k => pathVector h (s++[k])-pathVector h s) := by
  simp_rw [pathVector_step h s hs]
  exact basis_weaklyNull _ (children h s hs) (children h s hs).injective

lemma pathVector_increment_lower (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    2 ≤ ‖pathVector h (s++[k])-pathVector h s‖ := by
  rw [pathVector_step h s hs k]
  change 2 ≤ ‖lp.single 2 _ (componentBasis _ _)‖
  rw [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)]
  exact componentBasis_lower _ _ (pathNode_child h s hs k).1

lemma not_finite_dimensional : ¬Module.Finite ℝ Xv := by
  intro hh
  let := hh
  have hf : Function.Injective (fun x : Component (1:ℕ+) => lp.single 2 (1:ℕ+) x) := by
    intro x y he
    have h := congrArg (fun z : Xv => z (1:ℕ+)) he
    simpa only [lp.single_apply_self] using h
  have hfin := FiniteDimensional.of_injective (lp.singleContinuousLinearMap ℝ Component 2 (1:ℕ+)).toLinearMap hf
  let : Infinite (ComponentNode (1:ℕ+)) := Infinite.of_injective
    (fun n : ℕ => (⟨[n],by simp⟩ : ComponentNode (1:ℕ+))) (by intro n m he; simpa using congrArg Subtype.val he)
  exact AggregationSpace.not_finite_dimensional (componentTree (1:ℕ+)) (exponent (1:ℕ+)) hfin

theorem one_sided_modulus_zero (A : EquivalentNorm Xv) : A.modulus (A.lower/A.upper) = 0 := by
  have he : A.lower*2/(2*A.upper*1) = A.lower/A.upper := by field_simp [A.upper_pos.ne']
  rw [←he]
  apply bounded_trees_modulus_eq_zero not_finite_dimensional A pathVector
    (m := 1) (M := 1) (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs; rw [pathVector_norm]; exact ⟨le_rfl,le_rfl⟩
  · intro h hh s hs; exact pathVector_increments h s hs
  · intro h hh s hs k; exact pathVector_increment_lower h s hs k

theorem no_equivalent_AUC (A : EquivalentNorm Xv) : ¬A.AUC := by
  intro h
  have hp : 0 < A.lower/A.upper := div_pos A.lower_pos A.upper_pos
  have hh := h _ hp
  rw [one_sided_modulus_zero] at hh
  exact lt_irrefl _ hh

end Variable

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma eq_zero_of_coordinates_zero (x : TreeSpace T)
    (hx : ∀ s, coordinate T s x = 0) : x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg x)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v,hv⟩ := Completion.denseRange_coe.exists_dist_lt x (half_pos hε)
  have hvx : ‖(v : TreeSpace T)-x‖ < ε/2 := by simpa [dist_eq_norm,norm_sub_rev] using hv
  let H := T.head (show ι →₀ ℝ from v)
  have hH : T.Initial H := T.head_initial v
  have hxH : headCoordinates T H x = 0 := by ext s; exact hx s
  have hPx : projection T H hH x = 0 := by
    rw [projection_reconstructs,hxH,map_zero,Completion.coe_zero]
  have hPv : projection T H hH (v : TreeSpace T) = v := by
    rw [projection_coe]
    apply congrArg ((↑) : TreeVector T → TreeSpace T)
    change ι →₀ ℝ at v
    apply Finsupp.ext
    intro s
    change T.projectHead H v s = v s
    rw [T.projectHead_apply]
    split_ifs with hs
    · rfl
    · exact (Finsupp.notMem_support_iff.mp fun ht => hs (T.support_subset_head v ht)).symm
  have hp := projection_contracts T H hH ((v : TreeSpace T)-x)
  rw [map_sub,hPx,sub_zero,hPv] at hp
  have htri := norm_add_le (x-(v : TreeSpace T)) (v : TreeSpace T)
  rw [sub_add_cancel,norm_sub_rev] at htri
  linarith

lemma coordinates_ext {x y : TreeSpace T}
    (h : ∀ s, coordinate T s x = coordinate T s y) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_coordinates_zero T
  intro s
  rw [map_sub,h s,sub_self]

lemma projection_finite_rank (H : Finset ι) (hH : T.Initial H) :
    FiniteDimensional ℝ (projection T H hH).range := by
  let : Module.Finite ℝ (TreeSpace T ⧸ (projection T H hH).ker) := tail_finite_codimension T H hH
  exact Module.Finite.of_surjective (projection T H hH).toLinearMap.quotKerEquivRange.toLinearMap
    (projection T H hH).toLinearMap.quotKerEquivRange.surjective

end TreeSpace

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma coordinates_ext {x y : ZeroTreeSpace T}
    (h : ∀ s, coordinate T s x = coordinate T s y) : x = y :=
  inclusion_injective T (TreeSpace.coordinates_ext T h)

lemma projection_fixed_iff (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    projection T H hH x = x ↔ ∀ s ∉ H, coordinate T s x = 0 := by
  constructor
  · intro hx s hs
    have hh := coordinate_projection T H hH s x
    rwa [hx,ite_eq_right hs] at hh
  · intro hx
    apply coordinates_ext T
    intro s
    rw [coordinate_projection]
    split_ifs with hs
    · rfl
    · exact (hx s hs).symm

lemma mem_tail_iff (H : Finset ι) (hH : T.Initial H) (x : ZeroTreeSpace T) :
    x ∈ tail T H hH ↔ ∀ s ∈ H, coordinate T s x = 0 := by
  rw [tail_eq_coordinate_kernel]
  change headCoordinates T H x = 0 ↔ _
  constructor
  · intro hx s hs
    exact congrFun hx ⟨s,hs⟩
  · intro hx
    ext s
    exact hx s s.2

lemma projection_finite_rank (H : Finset ι) (hH : T.Initial H) :
    FiniteDimensional ℝ (projection T H hH).range := by
  let : Module.Finite ℝ (ZeroTreeSpace T ⧸ (projection T H hH).ker) := tail_finite_codimension T H hH
  exact Module.Finite.of_surjective (projection T H hH).toLinearMap.quotKerEquivRange.toLinearMap
    (projection T H hH).toLinearMap.quotKerEquivRange.surjective

end ZeroTreeSpace

theorem XZero_cubic_of_support (x : XZero) {H : Finset JoinedNode}
    (hH : joinedTree.Initial H) (hx : ∀ s ∉ H, ZeroTreeSpace.coordinate joinedTree s x = 0)
    (z : XZero) (hz : ∀ s ∈ H, ZeroTreeSpace.coordinate joinedTree s z = 0) (hz0 : z ≠ 0) :
    (‖x + z‖ + ‖x - z‖) / 2 ≥ ‖x‖ + ‖z‖ ^ 3 / (8 * (2 * ‖x‖ + ‖z‖) ^ 2) :=
  XZero_homogeneous_cubic x hH ((ZeroTreeSpace.projection_fixed_iff joinedTree H hH x).mpr hx)
    z ((ZeroTreeSpace.mem_tail_iff joinedTree H hH z).mpr hz) hz0

lemma rootSumCompletionStatement {ι : Type uIndex} [DecidableEq ι] [Infinite ι]
    (T : FiniteRootedTree ι) : RootSumCompletionStatement T where
  complete := inferInstance
  infinite_dimensional := TreeSpace.not_finite_dimensional T
  coordinate_continuous := fun s => (TreeSpace.coordinate T s).continuous
  coordinate_extends := TreeSpace.coordinate_coe T
  fields_continuous := fun s => ⟨TreeSpace.continuous_P T s,TreeSpace.continuous_Q T s⟩
  fields_extend := fun s v => ⟨TreeSpace.P_coe T s v,TreeSpace.Q_coe T s v⟩
  root_formula := TreeSpace.norm_eq T
  projections := fun H hH => ⟨TreeSpace.projection_contracts T H hH,TreeSpace.projection_idem T H hH,
    TreeSpace.coordinate_projection T H hH,TreeSpace.projection_finite_rank T H hH,
    TreeSpace.tail_closed T H hH,TreeSpace.tail_finite_codimension T H hH,
    fun x hx _ hε => TreeSpace.finite_tail_dense T H hH x hx hε⟩

lemma zeroRootCompletionStatement {ι : Type uIndex} [DecidableEq ι] [Infinite ι]
    (T : FiniteRootedTree ι) : ZeroRootCompletionStatement T where
  complete := inferInstance
  infinite_dimensional := ZeroTreeSpace.not_finite_dimensional T
  coordinate_continuous := fun s => (ZeroTreeSpace.coordinate T s).continuous
  coordinate_extends := ZeroTreeSpace.coordinate_coe T
  fields_continuous := fun s => ⟨ZeroTreeSpace.continuous_P T s,ZeroTreeSpace.continuous_Q T s⟩
  fields_extend := fun s v => ⟨ZeroTreeSpace.P_coe T s v,ZeroTreeSpace.Q_coe T s v⟩
  root_fixed := ZeroTreeSpace.root_zero T
  root_formula := ZeroTreeSpace.norm_eq_common T
  projections := fun H hH => ⟨ZeroTreeSpace.projection_contracts T H hH,ZeroTreeSpace.projection_idem T H hH,
    ZeroTreeSpace.coordinate_projection T H hH,ZeroTreeSpace.projection_finite_rank T H hH,
    ZeroTreeSpace.tail_closed T H hH,ZeroTreeSpace.tail_finite_codimension T H hH,
    fun x hx _ hε => ZeroTreeSpace.finite_tail_dense T H hH x hx hε⟩

theorem rec_completion : RootSumCompletionStatement sequenceTree ∧
    ZeroRootCompletionStatement joinedTree ∧ RootSumCompletionStatement joinedTree ∧
    IsReflexive XZero ∧ IsReflexive XJoined :=
  ⟨rootSumCompletionStatement sequenceTree,zeroRootCompletionStatement joinedTree,
    rootSumCompletionStatement joinedTree,XZero_isReflexive,XJoined_isReflexive⟩

theorem rec_main :
    (∀ t : ℝ, 0 < t → t < 1 → t^3/128 ≤ averagedModulus XSigma t ∧ t^3/128 ≤ averagedModulus XJoined t) ∧
    (∀ (H : Finset JoinedNode), joinedTree.Initial H → ∀ x : XZero,
      (∀ s ∉ H, ZeroTreeSpace.coordinate joinedTree s x = 0) → ∀ z : XZero,
      (∀ s ∈ H, ZeroTreeSpace.coordinate joinedTree s z = 0) → z ≠ 0 →
      (‖x+z‖+‖x-z‖)/2 ≥ ‖x‖+‖z‖^3/(8*(2*‖x‖+‖z‖)^2)) ∧
    (∀ A : EquivalentNorm XSigma, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XZero, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XJoined, ¬A.AUC) :=
  ⟨fun _ ht ht1 => ⟨XSigma_averaged_modulus ht ht1,XJoined_averaged_modulus ht ht1⟩,
    fun _ hH x hx z hz hz0 => XZero_cubic_of_support x hH hx z hz hz0,
    XSigma_no_equivalent_AUC,XZero_no_equivalent_AUC,XJoined_no_equivalent_AUC⟩

theorem stop_all_radii {t : ℝ} (ht : 0 < t) : 0 < averagedModulus XSigma t :=
  TreeSpace.averaged_modulus_pos sequenceTree ht

namespace Variable

open VariableExponent

lemma component_recursion (h : ℕ+) (x : Component h) (s : ComponentNode h) :
    (AggregationSpace.P (componentTree h) (exponent h) s x,
      AggregationSpace.Q (componentTree h) (exponent h) s x) =
    leastPair (componentCoordinate h s x)
      ((∑' c, if c ≠ (componentTree h).root ∧ (componentTree h).parent c = s then
        AggregationSpace.P (componentTree h) (exponent h) c x ^ heightExponent h else 0) ^ (1/heightExponent h))
      ((∑' c, if c ≠ (componentTree h).root ∧ (componentTree h).parent c = s then
        AggregationSpace.Q (componentTree h) (exponent h) c x ^ heightExponent h else 0) ^ (1/heightExponent h)) := by
  rw [AggregationSpace.recursion,AggregationSpace.childP_norm_formula,AggregationSpace.childQ_norm_formula]
  rfl

lemma norm_eq_nu (h : ℕ+) (x : Component h) : ‖x‖ = nu h (componentEquiv h x) := by
  rw [nu,(componentEquiv h).symm_apply_apply]
  exact AggregationSpace.norm_eq (componentTree h) (exponent h) x

lemma nu_comparisons (h : ℕ+) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)) :
    (h.val+1:ℝ)^(-1/heightExponent h)*‖v‖ ≤ nu h v ∧
    nu h v ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖v‖ := by
  have hh := component_comparisons h ((componentEquiv h).symm v)
  rwa [norm_eq_nu,(componentEquiv h).apply_symm_apply] at hh

lemma nu_eq_norm (h : ℕ+) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)) :
    nu h v = ‖(componentEquiv h).symm v‖ :=
  (AggregationSpace.norm_eq (componentTree h) (exponent h) ((componentEquiv h).symm v)).symm

lemma sourceNormStatement (h : ℕ+) : SourceNormStatement h where
  nonneg v := by rw [nu_eq_norm]; exact norm_nonneg _
  definite v := by
    rw [nu_eq_norm,norm_eq_zero]
    constructor
    · intro hv
      apply (componentEquiv h).symm.injective
      simpa only [map_zero] using hv
    · rintro rfl
      exact map_zero _
  triangle v w := by
    simp only [nu_eq_norm,map_add]
    exact norm_add_le _ _
  homogeneous a v := by
    simp only [nu_eq_norm,map_smul,norm_smul,Real.norm_eq_abs]

theorem space :
    (∀ h : ℕ+, CompleteSpace (Component h) ∧ IsReflexive (Component h) ∧
      SeparableSpace (Component h →L[ℝ] ℝ) ∧ SourceNormStatement h ∧
      ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h),
        (h.val+1:ℝ)^(-1/heightExponent h)*‖v‖ ≤ nu h v ∧
        nu h v ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖v‖) ∧
    CompleteSpace Xv ∧ IsReflexive Xv ∧ SeparableSpace (Xv →L[ℝ] ℝ) ∧
    Dense {x : Xv | FiniteTotalSupport x} ∧
    ∀ S : Finset Node, Continuous (projection S) ∧ FiniteDimensional ℝ (projection S).range ∧
      (∀ x : Xv, projection S (projection S x) = projection S x) ∧
      ∀ (s : Node) (x : Xv), coordinate s (projection S x) = if s ∈ S then coordinate s x else 0 :=
  ⟨fun h => ⟨inferInstance,component_reflexive h,inferInstance,sourceNormStatement h,nu_comparisons h⟩,
    inferInstance,reflexive,inferInstance,finite_support_dense,
    fun S => ⟨(projection S).continuous,projection_finite_rank S,projection_idem S,coordinate_projection S⟩⟩

lemma lpPotentials_recursion (h : ℕ+)
    (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)) (s : ComponentNode h) :
    lpPotentials h v s = leastPair (v s)
      (aggregateChildren h s (fun c => (lpPotentials h v c).1))
      (aggregateChildren h s (fun c => (lpPotentials h v c).2)) := by
  have hc : componentCoordinate h s ((componentEquiv h).symm v) = v s := by
    rw [←componentEquiv_apply,(componentEquiv h).apply_symm_apply]
  simpa only [lpPotentials,aggregateChildren,hc] using
    component_recursion h ((componentEquiv h).symm v) s

lemma recursion_unique (h : ℕ+) (v : ComponentNode h → ℝ)
    (f g : ComponentNode h → ℝ × ℝ)
    (hf : ∀ s, f s = leastPair (v s)
      (aggregateChildren h s (fun c => (f c).1))
      (aggregateChildren h s (fun c => (f c).2)))
    (hg : ∀ s, g s = leastPair (v s)
      (aggregateChildren h s (fun c => (g c).1))
      (aggregateChildren h s (fun c => (g c).2))) : f = g := by
  have he : ∀ n : ℕ, ∀ s : ComponentNode h, h.val-s.1.length = n → f s = g s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      have hcEqual (c : ComponentNode h)
          (hc : c ≠ (componentTree h).root ∧ (componentTree h).parent c = s) : f c = g c := by
        have hstep := component_step h c hc.1
        rw [hc.2] at hstep
        change c.1.length = s.1.length+1 at hstep
        have hcHeight := c.2
        exact ih (h.val-c.1.length) (by omega) c rfl
      rw [hf s,hg s]
      have ha : aggregateChildren h s (fun c => (f c).1) = aggregateChildren h s (fun c => (g c).1) := by
        unfold aggregateChildren
        congr 1
        apply tsum_congr
        intro c
        split_ifs with hc
        · exact congrArg (fun z : ℝ × ℝ => z.1 ^ heightExponent h) (hcEqual c hc)
        · rfl
      have hb : aggregateChildren h s (fun c => (f c).2) = aggregateChildren h s (fun c => (g c).2) := by
        unfold aggregateChildren
        congr 1
        apply tsum_congr
        intro c
        split_ifs with hc
        · exact congrArg (fun z : ℝ × ℝ => z.2 ^ heightExponent h) (hcEqual c hc)
        · rfl
      rw [ha,hb]
  funext s
  exact he _ s rfl

theorem lp_model_exact (h : ℕ+)
    (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h))
    (f : ComponentNode h → ℝ × ℝ)
    (hf : ∀ s, f s = leastPair (v s)
      (aggregateChildren h s (fun c => (f c).1))
      (aggregateChildren h s (fun c => (f c).2))) :
    f = lpPotentials h v ∧ nu h v = (f (componentTree h).root).1+(f (componentTree h).root).2 := by
  have he := recursion_unique h v f (lpPotentials h v) hf (lpPotentials_recursion h v)
  refine ⟨he,?_⟩
  rw [he]
  rfl

end Variable

end RecursivePotentials

end

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.Challenge ----
namespace OAI

noncomputable section

/-! Proved construction certificates and a statement-preservation check for the
self-contained Comparator challenge. All eleven original conclusions are retained. -/

namespace RecursivePotentials

open VariableExponent Filter Topology TopologicalSpace UniformSpace

namespace Variable

end Variable

end RecursivePotentials

namespace ComparatorModel.RecursivePotentials

attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalHeads
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalTree
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalZero
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalAggregation
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalLp
private theorem rootStatement_iff {ι : Type} [DecidableEq ι] (T : FiniteRootedTree ι) :
    RootSumCompletionStatement T ↔ _root_.OAI.RecursivePotentials.RootSumCompletionStatement T := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption

private theorem zeroStatement_iff {ι : Type} [DecidableEq ι] (T : FiniteRootedTree ι) :
    ZeroRootCompletionStatement T ↔ _root_.OAI.RecursivePotentials.ZeroRootCompletionStatement T := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption

private theorem sourceNormStatement_iff (h : ℕ+) :
    Variable.SourceNormStatement h ↔ _root_.OAI.RecursivePotentials.Variable.SourceNormStatement h := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption

private theorem result0_iff : rec_mainStatement ↔ _root_.OAI.RecursivePotentials.rec_mainOriginalStatement := Iff.rfl

private theorem result1_iff : rec_completionStatement ↔ _root_.OAI.RecursivePotentials.rec_completionOriginalStatement := by
  simp only [rec_completionStatement, _root_.OAI.RecursivePotentials.rec_completionOriginalStatement, rootStatement_iff, zeroStatement_iff]
  rfl

private theorem result2_iff : stop_all_radiiStatement ↔ _root_.OAI.RecursivePotentials.stop_all_radiiOriginalStatement := Iff.rfl

private theorem result3_iff : XJoined_separated_familiesStatement ↔ _root_.OAI.RecursivePotentials.XJoined_separated_familiesOriginalStatement := Iff.rfl

-- Compare the finite-rank projections pointwise, so the statement comparison does not
-- repeatedly unfold the completion and operator-space instances.
private theorem variableCoordinate_eq (s : Variable.Node) :
    Variable.coordinate s = _root_.OAI.RecursivePotentials.Variable.coordinate s := rfl

private theorem variableBasis_eq (s : Variable.Node) :
    Variable.basis s = _root_.OAI.RecursivePotentials.Variable.basis s := rfl

private theorem variableProjection_apply (S : Finset Variable.Node) (x : Variable.Xv) :
    Variable.projection S x = ∑ s ∈ S, Variable.coordinate s x • Variable.basis s := by
  simp only [Variable.projection, sum_apply, ContinuousLinearMap.smulRight_apply]

private theorem originalVariableProjection_apply
    (S : Finset _root_.OAI.RecursivePotentials.Variable.Node)
    (x : _root_.OAI.RecursivePotentials.Variable.Xv) :
    _root_.OAI.RecursivePotentials.Variable.projection S x =
      ∑ s ∈ S, _root_.OAI.RecursivePotentials.Variable.coordinate s x •
        _root_.OAI.RecursivePotentials.Variable.basis s := by
  simp only [_root_.OAI.RecursivePotentials.Variable.projection, sum_apply,
    ContinuousLinearMap.smulRight_apply]

private theorem variableAddCommMonoid_eq :
    (inferInstance : AddCommMonoid Variable.Xv) =
      (inferInstance : AddCommMonoid _root_.OAI.RecursivePotentials.Variable.Xv) := rfl

private theorem variableModule_eq :
    (inferInstance : Module ℝ Variable.Xv) =
      (inferInstance : Module ℝ _root_.OAI.RecursivePotentials.Variable.Xv) := rfl

private theorem variableProjection_sum_eq (S : Finset Variable.Node) (x : Variable.Xv) :
    (∑ s ∈ S, Variable.coordinate s x • Variable.basis s) =
      (∑ s ∈ S, _root_.OAI.RecursivePotentials.Variable.coordinate s x •
        _root_.OAI.RecursivePotentials.Variable.basis s) := by
  simp +instances only [variableAddCommMonoid_eq, variableModule_eq,
    variableCoordinate_eq, variableBasis_eq]
  rfl

private theorem variableProjection_apply_eq (S : Finset Variable.Node) (x : Variable.Xv) :
    Variable.projection S x = _root_.OAI.RecursivePotentials.Variable.projection S x :=
  (variableProjection_apply S x).trans
    ((variableProjection_sum_eq S x).trans (originalVariableProjection_apply S x).symm)

private theorem variableProjection_eq (S : Finset Variable.Node) :
    Variable.projection S = _root_.OAI.RecursivePotentials.Variable.projection S :=
  ContinuousLinearMap.ext (variableProjection_apply_eq S)

private theorem variableProjection_toLinearMap_eq (S : Finset Variable.Node) :
    (Variable.projection S : Variable.Xv →ₗ[ℝ] Variable.Xv) =
      (_root_.OAI.RecursivePotentials.Variable.projection S :
        _root_.OAI.RecursivePotentials.Variable.Xv →ₗ[ℝ] _root_.OAI.RecursivePotentials.Variable.Xv) :=
  congrArg (fun T : Variable.Xv →L[ℝ] Variable.Xv => T.toLinearMap) (variableProjection_eq S)

private theorem variableProjection_finiteDimensional_iff (S : Finset Variable.Node) :
    FiniteDimensional ℝ (Variable.projection S).range ↔
      FiniteDimensional ℝ (_root_.OAI.RecursivePotentials.Variable.projection S).range :=
  (congrArg (fun T : Variable.Xv →ₗ[ℝ] Variable.Xv => FiniteDimensional ℝ T.range)
    (variableProjection_toLinearMap_eq S)).to_iff

private theorem variableFiniteTotalSupport_iff (x : Variable.Xv) :
    Variable.FiniteTotalSupport x ↔ _root_.OAI.RecursivePotentials.Variable.FiniteTotalSupport x := by
  simp only [Variable.FiniteTotalSupport, _root_.OAI.RecursivePotentials.Variable.FiniteTotalSupport,
    variableCoordinate_eq]
  rfl

private theorem result4_iff : Variable.spaceStatement ↔ _root_.OAI.RecursivePotentials.Variable.spaceOriginalStatement := by
  simp only [Variable.spaceStatement, _root_.OAI.RecursivePotentials.Variable.spaceOriginalStatement,
    sourceNormStatement_iff, variableProjection_finiteDimensional_iff, variableProjection_eq,
    variableCoordinate_eq, variableFiniteTotalSupport_iff]
  rfl

private theorem result5_iff : Variable.lp_model_exactStatement ↔ _root_.OAI.RecursivePotentials.Variable.lp_model_exactOriginalStatement := Iff.rfl

private theorem result6_iff : Variable.one_sided_modulus_zeroStatement ↔ _root_.OAI.RecursivePotentials.Variable.one_sided_modulus_zeroOriginalStatement := Iff.rfl

private theorem result7_iff : Variable.no_equivalent_AUCStatement ↔ _root_.OAI.RecursivePotentials.Variable.no_equivalent_AUCOriginalStatement := Iff.rfl

private theorem result8_iff : Variable.sixth_stabilityStatement ↔ _root_.OAI.RecursivePotentials.Variable.sixth_stabilityOriginalStatement := Iff.rfl

private theorem result9_iff : Variable.cubic_stabilityStatement ↔ _root_.OAI.RecursivePotentials.Variable.cubic_stabilityOriginalStatement := Iff.rfl

private theorem result10_iff : Variable.weak_tailStatement ↔ _root_.OAI.RecursivePotentials.Variable.weak_tailOriginalStatement := Iff.rfl

private theorem results_iff_original :
    (rec_mainStatement ∧
    rec_completionStatement ∧
    stop_all_radiiStatement ∧
    XJoined_separated_familiesStatement ∧
    Variable.spaceStatement ∧
    Variable.lp_model_exactStatement ∧
    Variable.one_sided_modulus_zeroStatement ∧
    Variable.no_equivalent_AUCStatement ∧
    Variable.sixth_stabilityStatement ∧
    Variable.cubic_stabilityStatement ∧
    Variable.weak_tailStatement) ↔ _root_.OAI.RecursivePotentials.OriginalResults := by
  exact and_congr result0_iff (and_congr result1_iff (and_congr result2_iff (and_congr result3_iff (and_congr result4_iff (and_congr result5_iff (and_congr result6_iff (and_congr result7_iff (and_congr result8_iff (and_congr result9_iff (result10_iff))))))))))

/-- Packaging the construction obligations preserves the original eleven statements. -/
theorem main_iff_original : MainClaim ↔ _root_.OAI.RecursivePotentials.OriginalResults := by
  constructor
  · rintro ⟨_, _, _, _, _, h⟩
    exact results_iff_original.mp h
  · intro h
    exact ⟨canonicalHeads, canonicalTree, canonicalZero, canonicalAggregation, canonicalLp,
      results_iff_original.mpr h⟩

theorem main : MainClaim := by
  apply main_iff_original.mpr
  exact ⟨@_root_.OAI.RecursivePotentials.rec_main, @_root_.OAI.RecursivePotentials.rec_completion, @_root_.OAI.RecursivePotentials.stop_all_radii, @_root_.OAI.RecursivePotentials.XJoined_separated_families, @_root_.OAI.RecursivePotentials.Variable.space, @_root_.OAI.RecursivePotentials.Variable.lp_model_exact, @_root_.OAI.RecursivePotentials.Variable.one_sided_modulus_zero, @_root_.OAI.RecursivePotentials.Variable.no_equivalent_AUC, @_root_.OAI.RecursivePotentials.Variable.sixth_stability, @_root_.OAI.RecursivePotentials.Variable.cubic_stability, @_root_.OAI.RecursivePotentials.Variable.weak_tail⟩

end ComparatorModel.RecursivePotentials

end

end OAI

-- ---- mission target ----
open OAI OAI.ComparatorModel OAI.ComparatorModel.RecursivePotentials
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open scoped BigOperators
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalHeads
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalTree
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalZero
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalAggregation
attribute [local instance] OAI.ComparatorModel.RecursivePotentials.canonicalLp

namespace OAI
namespace ComparatorModel
namespace RecursivePotentials
theorem _root_.solution : MainClaim := by
  first
    | exact OAI.ComparatorModel.RecursivePotentials.main
    | (apply OAI.ComparatorModel.RecursivePotentials.main <;> assumption)
    | (intros; apply OAI.ComparatorModel.RecursivePotentials.main <;> assumption)
end RecursivePotentials
end ComparatorModel
end OAI
