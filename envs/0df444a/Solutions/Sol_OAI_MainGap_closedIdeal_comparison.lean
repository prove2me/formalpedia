-- Prove2me | solution 1 for OAI.MainGap.closedIdeal_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:26:23.233669+00:00
-- url     : https://prove2.me/submissions/f3e12563-2aea-4ec0-9ec3-f71296cb5ab2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealComparison.lean:L94-L107
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.closedIdeal_comparison. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Theorems.Thm_OAI_MainGap_FiniteCuntzLE_block
import Theorems.Thm_OAI_MainGap_mem_Her_of_nonneg_le
import Theorems.Thm_OAI_MainGap_scalarCuntzLE_iff_finite
import Theorems.Thm_OAI_MainGap_scalarCuntzLE_of_mem_Her

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma mul_star_mem_Her (h : A) : h * star h ∈ Her h := by
  apply (isClosed_Her h).mem_of_tendsto
    (((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const (star h))
  exact Filter.Eventually.of_forall (sandwich_mem_Her h)

lemma self_mem_Her {h : A} (hh : 0 ≤ h) : h ∈ Her h := by
  have hm : h * h ∈ Her h := by
    simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using mul_star_mem_Her h
  simpa only [CFC.sqrt_mul_self h hh] using
    sqrt_mem_Her hm (by simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using
      star_mul_self_nonneg h)

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Comparison ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
lemma matrix_mul_assoc {l m n k : ℕ} (x : CStarMatrix (Fin l) (Fin m) A)
    (y : CStarMatrix (Fin m) (Fin n) A) (z : CStarMatrix (Fin n) (Fin k) A) :
    (x * y) * z = x * (y * z) := Matrix.mul_assoc x y z

lemma matrix_star_mul {l m n : ℕ} (x : CStarMatrix (Fin l) (Fin m) A)
    (y : CStarMatrix (Fin m) (Fin n) A) :
    (x * y).conjTranspose = y.conjTranspose * x.conjTranspose :=
  Matrix.conjTranspose_mul x y

lemma continuous_matrix_mul {X : Type*} [TopologicalSpace X] {l m n : ℕ}
    {x : X → CStarMatrix (Fin l) (Fin m) A} {y : X → CStarMatrix (Fin m) (Fin n) A}
    (hx : Continuous x) (hy : Continuous y) : Continuous (fun t => x t * y t) :=
  hx.matrix_mul hy

lemma finiteCuntzLE_iff_closure {m n : ℕ} (d : CStarMatrix (Fin n) (Fin n) A)
    (v : CStarMatrix (Fin m) (Fin m) A) :
    FiniteCuntzLE d v ↔ d ∈ closure (Set.range
      (fun r : CStarMatrix (Fin m) (Fin n) A => r.conjTranspose * v * r)) := by
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨_, fun j => ⟨r j, rfl⟩, hr⟩
  · rintro ⟨x, hx, ht⟩
    choose r hr using hx
    exact ⟨r, by simpa only [hr] using ht⟩

lemma FiniteCuntzLE.conjugate {l m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A} (hdv : FiniteCuntzLE d v)
    (x : CStarMatrix (Fin n) (Fin l) A) :
    FiniteCuntzLE (x.conjTranspose * d * x) v := by
  obtain ⟨r, hr⟩ := hdv
  refine ⟨fun j => r j * x, ?_⟩
  have hc : Continuous (fun d : CStarMatrix (Fin n) (Fin n) A =>
      x.conjTranspose * d * x) :=
    continuous_matrix_mul (continuous_matrix_mul continuous_const continuous_id) continuous_const
  convert hc.continuousAt.tendsto.comp hr using 1
  ext j
  rw [matrix_star_mul]
  simp only [Function.comp_apply, matrix_mul_assoc]

lemma FiniteCuntzLE.trans {l m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A} {w : CStarMatrix (Fin l) (Fin l) A}
    (hdv : FiniteCuntzLE d v) (hvw : FiniteCuntzLE v w) : FiniteCuntzLE d w := by
  rw [finiteCuntzLE_iff_closure] at hdv ⊢
  apply closure_minimal _ isClosed_closure hdv
  rintro _ ⟨x, rfl⟩
  exact (finiteCuntzLE_iff_closure _ _).mp (hvw.conjugate x)

lemma matrixBlock_diagonal (n m : ℕ) (h : A) :
    matrixBlock (diagonalCorner n h) (diagonalCorner m h) = diagonalCorner (n+m) h := by
  apply CStarMatrix.ext
  intro i j
  change (Matrix.fromBlocks (Matrix.diagonal (fun _ => h)) 0 0
    (Matrix.diagonal (fun _ => h))).submatrix _ _ i j = _
  rw [Matrix.fromBlocks_diagonal]
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, diagonalCorner,
    CStarMatrix.ofMatrix_apply, Equiv.apply_eq_iff_eq]
  split_ifs with hij
  · cases finSumFinEquiv.symm i <;> rfl
  · rfl

lemma diagonalCorner_one (h : A) : diagonalCorner 1 h = scalarCorner h := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  change Matrix.diagonal (fun _ => h) i j = h
  simp [Matrix.diagonal, hij]

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.IdealDetection ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.idealDetectionOrder
attribute [local instance] OAI.MainGap.idealDetectionStarOrder
lemma ScalarCuntzLE.trans {u v w : A} (h : ScalarCuntzLE u v)
    (h' : ScalarCuntzLE v w) : ScalarCuntzLE u w :=
  (scalarCuntzLE_iff_finite _ _).mpr
    (((scalarCuntzLE_iff_finite _ _).mp h).trans ((scalarCuntzLE_iff_finite _ _).mp h'))

lemma scalarCuntzLE_of_order {u v : A} (hu : 0 ≤ u) (h : u ≤ v) :
    ScalarCuntzLE u v := scalarCuntzLE_of_mem_Her hu (hu.trans h) (mem_Her_of_nonneg_le hu h)

lemma scalarCuntzLE_smul {v : A} (hv : 0 ≤ v) {K : ℝ} (hK : 0 < K) :
    ScalarCuntzLE (K • v) v := by
  apply scalarCuntzLE_of_mem_Her (smul_nonneg hK.le hv) hv
  exact real_smul_mem_Her (self_mem_Her hv) K

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.IdealComparison ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.idealComparisonPartialOrder
attribute [local instance] OAI.MainGap.idealComparisonStarOrderedRing
lemma ScalarCuntzLE.conjugate_scalar {u v : A} (h : ScalarCuntzLE u v) (x : A) :
    ScalarCuntzLE (star x * u * x) v := by
  have hc : Continuous (fun z : A => star x * z * x) := by fun_prop
  have hm := image_closure_subset_closure_image hc ⟨u, h, rfl⟩
  apply closure_mono (s := (fun z : A => star x * z * x) ''
      Set.range (fun w : A => star w * v * w)) _ hm
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  exact ⟨w * x, by simp only [star_mul, mul_assoc]⟩

lemma scalarCuntzLE_left_square (x z : A) :
    ScalarCuntzLE (star (x * z) * (x * z)) (star z * z) := by
  have hnorm : star x * x ≤ (‖x‖ ^ 2 + 1) • (1 : A) := by
    apply (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := x)).trans
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_le_smul_of_nonneg_right (by linarith) (zero_le_one : (0 : A) ≤ 1)
  have h := star_left_conjugate_le_conjugate hnorm z
  have hh : star (x * z) * (x * z) ≤ (‖x‖ ^ 2 + 1) • (star z * z) := by
    simpa only [star_mul, mul_assoc, mul_smul_comm, smul_mul_assoc, mul_one] using h
  exact (scalarCuntzLE_of_order (star_mul_self_nonneg _) hh).trans
    (scalarCuntzLE_smul (star_mul_self_nonneg _) (by positivity))

lemma scalarCuntzLE_add_of_proper {u w v : A} (hv : ProperlyInfinite v)
    (hu : ScalarCuntzLE u v) (hw : ScalarCuntzLE w v) : ScalarCuntzLE (u + w) v := by
  have h := ((scalarCuntzLE_iff_finite _ _).mp hu).block
    ((scalarCuntzLE_iff_finite _ _).mp hw)
  have heq : matrixBlock (scalarCorner v) (scalarCorner v) = doubleCorner v := by
    rw [← diagonalCorner_one v, matrixBlock_diagonal]
    rfl
  rw [heq] at h
  have hh := h.trans hv
  let Y : CStarMatrix (Fin 2) (Fin 1) A := CStarMatrix.ofMatrix (fun _ _ => 1)
  have hy : Y.conjTranspose * matrixBlock (scalarCorner u) (scalarCorner w) * Y =
      scalarCorner (u + w) := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i
    fin_cases j
    simp only [CStarMatrix.mul_apply, Fin.sum_univ_two]
    rw [Fin.sum_univ_two]
    change ((star (1 : A) * u + star 1 * 0) * 1 +
      (star 1 * 0 + star 1 * w) * 1) = u + w
    simp
  exact (scalarCuntzLE_iff_finite _ _).mpr (by simpa only [hy] using hh.conjugate Y)

lemma square_add_le (x y : A) :
    star (x + y) * (x + y) ≤ (2 : ℝ) • (star x * x + star y * y) := by
  have hh := star_mul_self_nonneg (x - y)
  have heq : (2 : ℝ) • (star x * x + star y * y) - star (x + y) * (x + y) =
      star (x - y) * (x - y) := by
    simp only [star_add, star_sub, two_smul]
    noncomm_ring
  rw [← sub_nonneg, heq]
  exact hh

lemma square_comparison_add {x y v : A} (hv : ProperlyInfinite v)
    (hx : ScalarCuntzLE (star x * x) v) (hy : ScalarCuntzLE (star y * y) v) :
    ScalarCuntzLE (star (x + y) * (x + y)) v := by
  exact (scalarCuntzLE_of_order (star_mul_self_nonneg _) (square_add_le x y)).trans
    ((scalarCuntzLE_smul (add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _))
      (by norm_num : (0 : ℝ) < 2)).trans (scalarCuntzLE_add_of_proper hv hx hy))

lemma idealSpan_square_comparison {v z : A} (hv : 0 ≤ v) (hpi : ProperlyInfinite v)
    (hz : z ∈ idealSpan v) : ScalarCuntzLE (star z * z) v := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, y, rfl⟩ := hz
    have hvv : ScalarCuntzLE (star v * v) v := by
      apply scalarCuntzLE_of_mem_Her (star_mul_self_nonneg _) hv
      rw [hv.isSelfAdjoint.star_eq]
      exact mul_mem (self_mem_Her hv) (self_mem_Her hv)
    have hh := ((scalarCuntzLE_left_square x v).trans hvv).conjugate_scalar y
    simpa only [star_mul, mul_assoc] using hh
  | zero =>
    exact subset_closure ⟨0, by simp⟩
  | add x y hx hy ihx ihy => exact square_comparison_add hpi ihx ihy
  | smul c x hx ih =>
    have hh := (scalarCuntzLE_left_square (c • (1 : A)) x).trans ih
    simpa only [smul_mul_assoc, one_mul] using hh

theorem closedIdeal_comparison {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hpi : ProperlyInfinite v) (h : u ∈ closedIdeal v hv.isSelfAdjoint) :
    ScalarCuntzLE u v := by
  let J := closedIdeal v hv.isSelfAdjoint
  have hs : CFC.sqrt u ∈ J := by
    rw [CFC.sqrt_eq_real_sqrt u hu]
    let : IsClosed (J : Set A) := closedIdeal_closed v hv.isSelfAdjoint
    exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt h
  have hc : Continuous (fun x : A => star x * x) := by fun_prop
  have hh := image_closure_subset_closure_image hc ⟨CFC.sqrt u, hs, rfl⟩
  simp only [(CFC.sqrt_nonneg u).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self u hu] at hh
  apply isClosed_closure.closure_subset_iff.mpr _ hh
  rintro _ ⟨x, hx, rfl⟩
  exact idealSpan_square_comparison hv hpi hx

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.idealComparisonNonUnitalPartialOrder
attribute [local instance] OAI.MainGap.idealComparisonNonUnitalStarOrderedRing
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.idealComparisonPartialOrder
attribute [local instance] OAI.MainGap.idealComparisonStarOrderedRing


theorem solution : type_of% @_root_.OAI.MainGap.closedIdeal_comparison := @_root_.OAI.MainGap.closedIdeal_comparison
