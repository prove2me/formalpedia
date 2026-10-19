-- Prove2me | solution 1 for OAI.MainGap.four_avoidance_unital
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:48:24.233953+00:00
-- url     : https://prove2.me/submissions/01c2957b-3fb1-4bc9-9667-55be87672f30

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Avoidance.lean:L114-L182
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.four_avoidance_unital. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_FiniteCuntzLE_block
import Theorems.Thm_OAI_MainGap_ProperlyInfinite_finite_copies
import Theorems.Thm_OAI_MainGap_cut_cut
import Theorems.Thm_OAI_MainGap_first_pair_choice
import Theorems.Thm_OAI_MainGap_four_limit_impossible
import Theorems.Thm_OAI_MainGap_last_pair_choice
import Theorems.Thm_OAI_MainGap_norm_sub_cut_le
import Theorems.Thm_OAI_MainGap_ramp_mul_cut
import Theorems.Thm_OAI_MainGap_represented_mixed_estimate
import Theorems.Thm_OAI_MainGap_selfConsistent_cutoff_bound

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_sandwich {h k : A} (hk : k ∈ Her h) (a : A) : k * a * star k ∈ Her h := by
  let k' : Her h := ⟨k, hk⟩
  change (k' : A) * a * star (k' : A) ∈ Her h
  refine (sandwichMap_dense h).induction_on k'
    ((isClosed_Her h).preimage (by fun_prop)) ?_
  intro b
  change (h * b * star h) * a * star (h * b * star h) ∈ Her h
  convert sandwich_mem_Her h (b * star h * a * h * star b) using 1
  simp only [star_mul, star_star, mul_assoc]

lemma Her_mono_of_mem {h k : A} (hk : k ∈ Her h) : Her k ≤ Her h := by
  apply closure_minimal _ (isClosed_Her h)
  rintro _ ⟨a, rfl⟩
  exact Her_sandwich hk a

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

lemma cut_nonneg (d : A) (ε : ℝ) : 0 ≤ cut d ε := by
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)

lemma cut_mem_Her {d : A} (hd : 0 ≤ d) (ε : ℝ) : cut d ε ∈ Her d := by
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her hd)

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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.OrthogonalSlots ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
open scoped CStarAlgebra
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass
namespace RegularTransport
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

end RegularTransport

namespace OrthogonalSlots
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

end OrthogonalSlots

section FiniteSum

lemma FiniteCuntzLE.double {d v : A}
    (hdv : FiniteCuntzLE (scalarCorner d) (scalarCorner v)) :
    FiniteCuntzLE (doubleCorner d) (doubleCorner v) := by
  have hh := hdv.block hdv
  rw [← diagonalCorner_one d, ← diagonalCorner_one v, matrixBlock_diagonal,
    matrixBlock_diagonal] at hh
  exact hh

lemma finiteSum_cuntzLE {v : A} (hv : ProperlyInfinite v) {n : ℕ} (r : Fin n → A) :
    FiniteCuntzLE (scalarCorner (∑ i, star (r i) * v * r i)) (scalarCorner v) := by
  let x : CStarMatrix (Fin n) (Fin 1) A := CStarMatrix.ofMatrix (fun i _ => r i)
  have hcomp : x.conjTranspose * diagonalCorner n v * x =
      scalarCorner (∑ i, star (r i) * v * r i) := by
    ext i j
    change (∑ k : Fin n, (∑ l : Fin n, star (r l) *
      (if l = k then v else 0)) * r k) = _
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  rw [← hcomp]
  exact (hv.finite_copies n).conjugate x

lemma finiteSum_two_cuntzLE {v : A} (hv : ProperlyInfinite v) {n : ℕ} (r : Fin n → A) :
    FiniteCuntzLE (diagonalCorner 2 (∑ i, star (r i) * v * r i)) (scalarCorner v) :=
  (finiteSum_cuntzLE hv r).double.trans hv

lemma finsetSum_cuntzLE {v : A} (hv : ProperlyInfinite v) {ι : Type*}
    (E : Finset ι) (r : ι → A) :
    FiniteCuntzLE (diagonalCorner 2 (∑ i ∈ E, star (r i) * v * r i)) (scalarCorner v) := by
  classical
  let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  have hsum : (∑ i : Fin (Fintype.card E), star (r (e i)) * v * r (e i)) =
      ∑ i ∈ E, star (r i) * v * r i := by
    calc
      _ = ∑ i : E, star (r i) * v * r i := Equiv.sum_comp e _
      _ = _ := by simpa using (Finset.sum_attach E (fun i => star (r i) * v * r i))
  rw [← hsum]
  exact finiteSum_two_cuntzLE hv _

end FiniteSum
end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section MoreHer
variable [PartialOrder A] [StarOrderedRing A]

end MoreHer
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section Ramps
variable [PartialOrder A] [StarOrderedRing A]

lemma norm_mem_quasispectrum_of_nonneg {a : A} (ha : 0 ≤ a) :
    ‖a‖ ∈ quasispectrum ℝ a := by
  simpa using quasispectrum.algebraMap_mem ℝ
    (NonUnitalIsometricContinuousFunctionalCalculus.isGreatest_quasispectrum a ha).1

lemma continuous_rampFn (l u : ℝ) : Continuous (rampFn l u) :=
  continuous_const.min (((continuous_id.sub continuous_const).max continuous_const).div_const _)

lemma rampFn_nonneg {l u t : ℝ} (hlu : l ≤ u) : 0 ≤ rampFn l u t :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) (sub_nonneg.mpr hlu))

lemma rampFn_le_one (l u t : ℝ) : rampFn l u t ≤ 1 := min_le_left _ _

lemma rampFn_zero {l u t : ℝ} (ht : t ≤ l) : rampFn l u t = 0 := by
  simp only [rampFn, max_eq_right (sub_nonpos.mpr ht), zero_div, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]

lemma rampFn_one {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) : rampFn l u t = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
  rw [one_mul, max_eq_left (sub_nonneg.mpr (hlu.le.trans ht))]
  linarith

lemma ramp_nonneg (a : A) {l u : ℝ} (hlu : l ≤ u) : 0 ≤ ramp a l u :=
  cfcₙ_nonneg (fun _ _ => rampFn_nonneg hlu)

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_ramp_le_one (a : A) {l u : ℝ} (hlu : l ≤ u) : ‖ramp a l u‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t _
  rw [Real.norm_eq_abs, abs_of_nonneg (rampFn_nonneg hlu)]
  exact rampFn_le_one _ _ _

lemma ramp_mem_Her_cut {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) :
    ramp a l u ∈ Her (cut a l) := by
  have hcomp : ramp a l u = cfcₙ (fun t : ℝ => min 1 (t / (u-l))) (cut a l) := by
    unfold ramp cut
    exact cfcₙ_comp (fun t : ℝ => min 1 (t / (u-l))) (fun t : ℝ => max (t-l) 0) a
      (continuous_const.min (continuous_id.div_const _)).continuousOn (by norm_num)
      ((continuous_id.sub continuous_const).max continuous_const).continuousOn
      (by simp [max_eq_right (neg_nonpos.mpr hl)]) (.of_nonneg ha)
  rw [hcomp]
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her (cut_nonneg a l))

lemma norm_ramp_eq_one {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l)
    (hlu : l < u) (hu : u ≤ ‖a‖) : ‖ramp a l u‖ = 1 := by
  apply le_antisymm (norm_ramp_le_one a hlu.le)
  have ht := norm_apply_le_norm_cfcₙ (rampFn l u) a
    (norm_mem_quasispectrum_of_nonneg ha) (continuous_rampFn l u).continuousOn
    (rampFn_zero hl) (.of_nonneg ha)
  change 1 ≤ ‖cfcₙ (rampFn l u) a‖
  simpa only [rampFn_one hlu hu, norm_one] using ht

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_map {B : Type*} [NonUnitalCStarAlgebra B] (π : A →⋆ₙₐ[ℂ] B)
    {h k : A} (hk : k ∈ Her h) : π k ∈ Her (π h) := by
  have hc : IsClosed {k : A | π k ∈ Her (π h)} :=
    (isClosed_Her (π h)).preimage (map_continuous π)
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change π (h * a * star h) ∈ Her (π h)
  simpa only [map_mul, map_star] using sandwich_mem_Her (π h) (π a)

lemma Her_fixed_left {h t : A} (ht : t * h = h) {k : A} (hk : k ∈ Her h) : t * k = k := by
  have hc : IsClosed {k : A | t * k = k} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change t * (h * a * star h) = h * a * star h
  simp only [← mul_assoc, ht]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.ChoicePairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.choicePairsPartialOrder
attribute [local instance] OAI.MainGap.choicePairsStarOrderedRing
lemma fixed_left_of_modulus {b z : A} (h : b * (z * star z) = z * star z) : b*z=z := by
  apply sub_eq_zero.mp
  apply (CStarRing.mul_star_self_eq_zero_iff _).mp
  have hs := congrArg star h
  simp only [star_mul, star_star] at hs
  calc
    (b*z-z) * star (b*z-z) = b*(z*star z)*star b - (z*star z)*star b - b*(z*star z) + z*star z := by
      simp only [star_sub, star_mul]; noncomm_ring
    _ = 0 := by rw [h]; noncomm_ring

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma firstSandwich_nonneg {U V : A} (hV : 0 ≤ V) (η : ℝ) (E : Finset A) :
    0 ≤ firstSandwich U V η E := by
  have hsum : 0 ≤ ∑ w ∈ E, w * V * star w :=
    Finset.sum_nonneg (fun w _ => star_right_conjugate_nonneg hV w)
  simpa only [firstSandwich, IsSelfAdjoint.of_nonneg (cut_nonneg U η) |>.star_eq] using
    star_right_conjugate_nonneg hsum (cut U η)

lemma firstSandwich_mem (U V : A) (η : ℝ) (E : Finset A) :
    firstSandwich U V η E ∈ Her (cut U η) := by
  simpa only [firstSandwich, IsSelfAdjoint.of_nonneg (cut_nonneg U η) |>.star_eq] using
    sandwich_mem_Her (cut U η) (∑ w ∈ E, w * V * star w)

lemma firstSandwich_two_cuntzLE {U V : A} (hV : ProperlyInfinite V)
    (η : ℝ) (E : Finset A) :
    FiniteCuntzLE (diagonalCorner 2 (firstSandwich U V η E)) (scalarCorner V) := by
  have heq : firstSandwich U V η E =
      ∑ w ∈ E, star (star w * cut U η) * V * (star w * cut U η) := by
    simp only [firstSandwich, Finset.mul_sum, Finset.sum_mul, star_mul, star_star,
      IsSelfAdjoint.of_nonneg (cut_nonneg U η) |>.star_eq]
    apply Finset.sum_congr rfl
    intro w _
    noncomm_ring
  rw [heq]
  exact finsetSum_cuntzLE hV E _

lemma norm_ramp_bound {d : A} (hd : 0 ≤ d) {η h : ℝ} (hη : 0 < η)
    (hh0 : 0 ≤ h) (hh : h < 1) (hbound : ramp d η (2*η) ≤ h • (1 : A)) : ‖d‖ < 2*η := by
  by_contra! hnorm
  have hone := norm_ramp_eq_one hd hη.le (by linarith) hnorm
  have hD := ramp_nonneg d (by linarith : η ≤ 2*η)
  have hnle : ‖ramp d η (2*η)‖ ≤ h := by
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hh0 hD).mpr (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hbound)
  linarith

end MainGap

namespace MainGap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma complement_nonneg {H : A} (hH : IsSelfAdjoint H) (hnorm : ‖H‖ ≤ 1) :
    0 ≤ 1 - H * H := by
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (H * H) ?_).mp
  · calc
      ‖H * H‖ = ‖H‖ ^ 2 := hH.norm_mul_self
      _ ≤ 1 := (sq_le_one_iff₀ (norm_nonneg H)).mpr hnorm
  · simpa only [hH.star_eq] using star_mul_self_nonneg H

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.instPartialOrder_oAI
attribute [local instance] OAI.MainGap.instStarOrderedRing_oAI
lemma deficiency_selfAdjoint (d : A) : IsSelfAdjoint (deficiency d) := IsSelfAdjoint.cfc

lemma squareSandwich_nonneg {x : A} (hx : IsSelfAdjoint x) (Q : A) (hQ : IsSelfAdjoint Q) :
    0 ≤ x * Q * Q * x := by
  have := star_mul_self_nonneg (Q*x)
  simpa only [star_mul, hx.star_eq, hQ.star_eq, mul_assoc] using this

lemma squareSandwich_mem {x : A} (hx : IsSelfAdjoint x) (Q : A) :
    x * Q * Q * x ∈ Her x := by
  simpa only [hx.star_eq, mul_assoc] using sandwich_mem_Her x (Q*Q)

lemma cut_mem_cutHer {X : A} (hX : 0 ≤ X) {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) :
    cut X u ∈ Her (cut X l) := by
  have heq : cut X u = cut (cut X l) (u-l) := by
    rw [cut_cut hX hl (sub_nonneg.mpr hlu)]
    congr 1
    ring
  rw [heq]
  exact cut_mem_Her (cut_nonneg X l) _

lemma firstX_mem {X : A} (hX : 0 ≤ X) : firstX X ∈ fourHer X :=
  cut_mem_cutHer hX (by norm_num) (by norm_num)
lemma firstV_mem {X : A} (hX : 0 ≤ X) : firstV X ∈ fourHer X :=
  cut_mem_cutHer hX (by norm_num) (by norm_num)
lemma firstU_nonneg (X B : A) : 0 ≤ firstU X B :=
  squareSandwich_nonneg (.of_nonneg (cut_nonneg X _)) _ (deficiency_selfAdjoint _)
lemma firstU_mem {X : A} (hX : 0 ≤ X) (B : A) : firstU X B ∈ fourHer X :=
  Her_mono_of_mem (firstX_mem hX) (squareSandwich_mem (.of_nonneg (cut_nonneg X _)) _)

lemma firstK_mem {X : A} (hX : 0 ≤ X) : firstK X ∈ fourHer X := by
  exact Her_mono_of_mem (cut_mem_cutHer hX (by norm_num : (0:ℝ) ≤ 1/32)
    (by norm_num : (1/32:ℝ) ≤ 3/64)) (ramp_mem_Her_cut hX (by norm_num))

lemma prospectiveDefect_nonneg (X B : A) : 0 ≤ prospectiveDefect X B :=
  ramp_nonneg _ (by norm_num)
lemma prospectiveDefect_mem {X : A} (hX : 0 ≤ X) (B : A) :
    prospectiveDefect X B ∈ fourHer X := by
  change cfcₙ _ _ ∈ Her (cut X (1/32))
  apply cfcₙ_mem (𝕜' := ℂ)
  have h := Her_sandwich (firstK_mem hX) (scalingDefect (firstH X) (firstR X B))
  simpa only [firstK, IsSelfAdjoint.of_nonneg (ramp_nonneg X (by norm_num : (3/64:ℝ) ≤ 1/16)) |>.star_eq] using h

lemma lastX_nonneg (X B : A) : 0 ≤ lastX X B := cut_nonneg _ _
lemma lastX_mem {X : A} (hX : 0 ≤ X) (B : A) : lastX X B ∈ fourHer X :=
  Her_mono_of_mem (prospectiveDefect_mem hX B) (cut_mem_Her (prospectiveDefect_nonneg X B) _)
lemma lastR_nonneg (X B₁ B₃ : A) : 0 ≤ lastR X B₁ B₃ :=
  squareSandwich_nonneg (.of_nonneg (lastX_nonneg X B₁)) _ (deficiency_selfAdjoint _)
lemma lastR_mem {X : A} (hX : 0 ≤ X) (B₁ B₃ : A) : lastR X B₁ B₃ ∈ fourHer X :=
  Her_mono_of_mem (lastX_mem hX B₁) (squareSandwich_mem (.of_nonneg (lastX_nonneg X B₁)) _)

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.FourChoices ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourChoicesPartialOrder
attribute [local instance] OAI.MainGap.fourChoicesStarOrderedRing
theorem finite_four_choices {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hp : ∀ z : A, 0 ≤ z → z ∈ fourHer X → ProperlyInfinite z)
    (E : Finset A) {η : ℝ} (hη : 0 < η) :
    ∃ T : Fin 4 → A,
      (∀ i, ‖T i‖ ≤ 1) ∧ (∀ i, T i ∈ fourHer X) ∧
      T 0 * star (T 0) = ramp (firstSandwich (firstU X (B 0)) (firstV X) η E) η (2*η) ∧
      T 1 * star (T 1) = T 0 * star (T 0) ∧ T 0 * star (T 1) = 0 ∧
      star (T 0) * T 0 ∈ Her (firstV X) ∧ star (T 1) * T 1 ∈ Her (firstV X) ∧
      star (T 2) * T 3 = 0 ∧ star (T 2) * T 2 = star (T 3) * T 3 ∧
      T 2 * star (T 2) ∈ Her (cut (lastR X (B 0) (B 2)) η) ∧
      T 3 * star (T 3) ∈ Her (cut (lastR X (B 0) (B 2)) η) ∧
      (∀ {D : Type*} [NonUnitalCStarAlgebra D] (π : A →⋆ₙₐ[ℂ] D),
        4*η ≤ ‖π (lastR X (B 0) (B 2))‖ → ‖π (T 2)‖ = 1) := by
  let U := firstU X (B 0)
  let V := firstV X
  let R := lastR X (B 0) (B 2)
  let D₀ := firstSandwich U V η E
  have hV : 0 ≤ V := cut_nonneg X _
  have hVk : V ∈ fourHer X := firstV_mem hX
  have hDk : D₀ ∈ fourHer X := Her_mono_of_mem (firstU_mem hX (B 0))
    (Her_mono_of_mem (cut_mem_Her (firstU_nonneg X (B 0)) η) (firstSandwich_mem U V η E))
  obtain ⟨T₀, hT₀norm, hT₀mem, hT₀mod, hT₀outer⟩ :=
    first_pair_choice (firstSandwich_nonneg hV η E) hV
      (firstSandwich_two_cuntzLE (hp V hV hVk) η E) hDk hVk hη
  obtain ⟨T₂, hT₂norm, hT₂mem, hT₂mod, hT₂outer, hT₂rep⟩ :=
    last_pair_choice (lastR_nonneg X (B 0) (B 2)) (lastR_mem hX _ _) hη
      (hp (cut R η) (cut_nonneg R η)
        (Her_mono_of_mem (lastR_mem hX _ _) (cut_mem_Her (lastR_nonneg X (B 0) (B 2)) η)))
  refine ⟨![T₀ 0, T₀ 1, T₂ 0, T₂ 1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> first | exact hT₀norm _ | exact hT₂norm _
  · intro i; fin_cases i <;> first | exact hT₀mem _ | exact hT₂mem _
  · simpa using hT₀mod 0 0
  · simpa using (hT₀mod 1 1).trans (hT₀mod 0 0).symm
  · simpa using hT₀mod 0 1
  · exact hT₀outer 0 0
  · exact hT₀outer 1 1
  · simpa using hT₂mod 0 1
  · simpa using (hT₂mod 0 0).trans (hT₂mod 1 1).symm
  · exact hT₂outer 0 0
  · exact hT₂outer 1 1
  · intro D _ π hR
    exact hT₂rep π hR 0

end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
attribute [local instance] OAI.MainGap.fourChoicesMapDomainOrder
attribute [local instance] OAI.MainGap.fourChoicesMapDomainStarOrder
attribute [local instance] OAI.MainGap.fourChoicesMapCodomainOrder
attribute [local instance] OAI.MainGap.fourChoicesMapCodomainStarOrder
variable (π : A →⋆ₐ[ℂ] D)

lemma map_cut_sa {a : A} (ha : IsSelfAdjoint a) {l : ℝ} (hl : 0 ≤ l) :
    π (cut a l) = cut (π a) l :=
  π.toNonUnitalStarAlgHom.map_cfcₙ (fun t : ℝ => max (t-l) 0) a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)]) (map_continuous π) ha (ha.map π)

lemma map_ramp_sa {a : A} (ha : IsSelfAdjoint a) {l u : ℝ} (hl : 0 ≤ l) :
    π (ramp a l u) = ramp (π a) l u :=
  π.toNonUnitalStarAlgHom.map_cfcₙ (rampFn l u) a
    (continuous_rampFn l u).continuousOn (rampFn_zero hl)
    (map_continuous π) ha (ha.map π)

lemma map_deficiency {d : A} (hd : IsSelfAdjoint d) :
    π (deficiency d) = deficiency (π d) :=
  π.map_cfc (fun t : ℝ => max (1/2-t) 0) d
    ((continuous_const.sub continuous_id).max continuous_const).continuousOn
    (map_continuous π) hd (hd.map π)

lemma map_sqrt {a : A} (ha : 0 ≤ a) : π (CFC.sqrt a) = CFC.sqrt (π a) :=
  π.toNonUnitalStarAlgHom.map_cfcₙ NNReal.sqrt a (by fun_prop) (by simp)
    (map_continuous π) ha (map_nonneg π ha)

lemma map_firstX {X : A} (hX : IsSelfAdjoint X) : π (firstX X) = firstX (π X) :=
  map_cut_sa π hX (by norm_num)
lemma map_firstH {X : A} (hX : IsSelfAdjoint X) : π (firstH X) = firstH (π X) :=
  map_ramp_sa π hX (by norm_num)
lemma map_firstK {X : A} (hX : IsSelfAdjoint X) : π (firstK X) = firstK (π X) :=
  map_ramp_sa π hX (by norm_num)

lemma map_firstU {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (firstU X B) = firstU (π X) (π B) := by
  simp only [firstU, map_mul, map_firstX π hX,
    map_deficiency π (.mul_star_self B), map_star]

lemma map_firstR {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (firstR X B) = firstR (π X) (π B) := by
  change π ((Real.sqrt 2) • (star B * firstH X)) = _
  calc
    π ((Real.sqrt 2) • (star B * firstH X)) = (Real.sqrt 2) • π (star B * firstH X) :=
      π.toAlgHom.map_smul_of_tower _ _
    _ = firstR (π X) (π B) := by simp only [firstR, map_mul, map_star, map_firstH π hX]

lemma map_scalingComplement {H : A} (hH : IsSelfAdjoint H) (hn : ‖H‖ ≤ 1) :
    π (scalingComplement H) = scalingComplement (π H) := by
  simp only [scalingComplement, map_sqrt π (complement_nonneg hH hn), map_sub, map_one, map_mul]

lemma map_scalingDefect {H : A} (hH : IsSelfAdjoint H) (hn : ‖H‖ ≤ 1) (r : A) :
    π (scalingDefect H r) = scalingDefect (π H) (π r) := by
  simp only [scalingDefect, scalingIsometry, map_sub, map_mul, map_star, map_one, map_add,
    map_scalingComplement π hH hn]

lemma scalingDefect_selfAdjoint (H r : A) : IsSelfAdjoint (scalingDefect H r) :=
  (IsSelfAdjoint.one A).sub (.mul_star_self _)

lemma prospective_input_selfAdjoint (X B : A) :
    IsSelfAdjoint (firstK X * scalingDefect (firstH X) (firstR X B) * firstK X) := by
  have hK : IsSelfAdjoint (firstK X) := .of_nonneg (ramp_nonneg X (by norm_num))
  rw [isSelfAdjoint_iff]
  simp only [star_mul, hK.star_eq, scalingDefect_selfAdjoint _ _ |>.star_eq, mul_assoc]

lemma map_prospectiveDefect {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (prospectiveDefect X B) = prospectiveDefect (π X) (π B) := by
  have hH : IsSelfAdjoint (firstH X) := .of_nonneg (ramp_nonneg X (by norm_num))
  have hn : ‖firstH X‖ ≤ 1 := norm_ramp_le_one _ (by norm_num)
  simp only [prospectiveDefect, map_ramp_sa π (prospective_input_selfAdjoint X B) le_rfl,
    map_mul, map_firstK π hX, map_scalingDefect π hH hn, map_firstH π hX,
    map_firstR π hX]

lemma map_lastX {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (lastX X B) = lastX (π X) (π B) := by
  have hp : IsSelfAdjoint (prospectiveDefect X B) := .of_nonneg (ramp_nonneg _ (by norm_num))
  rw [lastX, map_cut_sa π hp (by norm_num), map_prospectiveDefect π hX]
  rfl

lemma map_lastR {X : A} (hX : IsSelfAdjoint X) (B C : A) :
    π (lastR X B C) = lastR (π X) (π B) (π C) := by
  simp only [lastR, map_mul, map_lastX π hX,
    map_deficiency π (.mul_star_self C), map_star]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourChoiceStructureOrder
attribute [local instance] OAI.MainGap.fourChoiceStructureStarOrder
universe v

theorem fourChoice_nonempty {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hp : ∀ z : A, 0 ≤ z → z ∈ fourHer X → ProperlyInfinite z)
    (E : Finset A) {η : ℝ} (hη : 0 < η) : Nonempty (FourChoice.{v, _} X B E η) := by
  obtain ⟨T, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
    finite_four_choices hX B hp E hη
  exact ⟨⟨T, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩⟩

lemma firstH_fixes_V {X : A} (hX : 0 ≤ X) : firstH X * firstV X = firstV X :=
  ramp_mul_cut hX (by norm_num) (by norm_num) le_rfl

namespace FourChoice
variable {X : A} {B : Fin 4 → A} {E : Finset A} {η : ℝ} (F : FourChoice.{v, _} X B E η)

lemma first_mem (hη : 0 < η) :
    F.T 0 * star (F.T 0) ∈ Her (cut (firstU X (B 0)) η) := by
  rw [F.first_mod]
  exact Her_mono_of_mem (firstSandwich_mem _ _ η E)
    (Her_mono_of_mem (cut_mem_Her (firstSandwich_nonneg (cut_nonneg X _) η E) η)
      (ramp_mem_Her_cut (firstSandwich_nonneg (cut_nonneg X _) η E) hη.le))

lemma first_support₀ (hX : 0 ≤ X) : firstH X * star (F.T 0) = star (F.T 0) := by
  apply fixed_left_of_modulus
  simp only [star_star]
  exact Her_fixed_left (firstH_fixes_V hX) F.outer₀

lemma first_support₁ (hX : 0 ≤ X) : firstH X * star (F.T 1) = star (F.T 1) := by
  apply fixed_left_of_modulus
  simp only [star_star]
  exact Her_fixed_left (firstH_fixes_V hX) F.outer₁

lemma last_support : ramp (prospectiveDefect X (B 0)) 0 (1/2) * F.T 3 = F.T 3 := by
  apply fixed_left_of_modulus
  apply Her_fixed_left (ramp_mul_cut (prospectiveDefect_nonneg X _)
    le_rfl (by norm_num : (0:ℝ) < 1/2) le_rfl)
  exact Her_mono_of_mem (squareSandwich_mem (.of_nonneg (lastX_nonneg X _)) _)
    (Her_mono_of_mem (cut_mem_Her (lastR_nonneg X _ _) η) F.outer₃)

variable {D : Type v} [CStarAlgebra D]
attribute [local instance] OAI.MainGap.FourChoice.fourChoiceRepresentationOrder
attribute [local instance] OAI.MainGap.FourChoice.fourChoiceRepresentationStarOrder
variable (π : A →⋆ₐ[ℂ] D) (hX : 0 ≤ X) (hη : 0 < η)
  (hmatch : ∀ i, π (F.T i) = π (B i))

include F hX hη hmatch in
lemma first_bound : π (B 0) * star (π (B 0)) ≤ (1/2 : ℝ) • (1 : D) := by
  have hm := Her_map π.toNonUnitalStarAlgHom (F.first_mem hη)
  change π (F.T 0 * star (F.T 0)) ∈ Her (π (cut (firstU X (B 0)) η)) at hm
  simp only [map_mul, map_star, hmatch] at hm
  rw [map_cut_sa π (.of_nonneg (firstU_nonneg X (B 0))) hη.le,
    map_firstU π (.of_nonneg hX)] at hm
  exact selfConsistent_cutoff_bound (cut_nonneg (π X) _)
    (mul_star_self_nonneg _) hη (by norm_num) hm

include F hX hη hmatch in
lemma last_bound : π (B 2) * star (π (B 2)) ≤ (1/2 : ℝ) • (1 : D) := by
  have hm := Her_map π.toNonUnitalStarAlgHom F.outer₂
  change π (F.T 2 * star (F.T 2)) ∈ Her (π (cut (lastR X (B 0) (B 2)) η)) at hm
  simp only [map_mul, map_star, hmatch] at hm
  rw [map_cut_sa π (.of_nonneg (lastR_nonneg X (B 0) (B 2))) hη.le,
    map_lastR π (.of_nonneg hX)] at hm
  exact selfConsistent_cutoff_bound (lastX_nonneg (π X) _)
    (mul_star_self_nonneg _) hη (by norm_num) hm

include F hX hη hmatch in
lemma first_norm : ‖π (firstSandwich (firstU X (B 0)) (firstV X) η E)‖ < 2*η := by
  have hpos : 0 ≤ firstSandwich (firstU X (B 0)) (firstV X) η E :=
    firstSandwich_nonneg (cut_nonneg X _) η E
  have hmod := congrArg π F.first_mod
  rw [map_mul, map_star, hmatch, map_ramp_sa π (.of_nonneg hpos) hη.le] at hmod
  apply norm_ramp_bound (map_nonneg π hpos)
    hη (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  rw [← hmod]
  exact F.first_bound π hX hη hmatch

include F hX hη hmatch in
lemma last_norm_lt : ‖π (lastR X (B 0) (B 2))‖ < 4*η := by
  by_contra! hn
  have hone : ‖π (B 2)‖ = 1 := by
    have ht : ‖π (F.T 2)‖ = 1 := F.last_norm π.toNonUnitalStarAlgHom hn
    rwa [hmatch] at ht
  have hle : ‖π (B 2) * star (π (B 2))‖ ≤ 1/2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (by norm_num : (0:ℝ) ≤ 1/2)
      (mul_star_self_nonneg _)).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using F.last_bound π hX hη hmatch
  rw [CStarRing.norm_self_mul_star, hone] at hle
  norm_num at hle

end FourChoice
end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Ultrafilter ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable (A : Type*)
lemma fourEta_pos (i : FourIndex A) : 0 < fourEta A i := by
  unfold fourEta
  positivity

lemma fourEta_tendsto : Tendsto (fourEta A) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hf : Tendsto (fun i : FourIndex A => i.1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop (n, (∅ : Finset A))] with i hi
    exact hi.1
  exact h.comp hf

lemma fourIndex_eventually_mem (w : A) : ∀ᶠ i : FourIndex A in atTop, w ∈ i.2 := by
  classical
  filter_upwards [eventually_ge_atTop ((0:ℕ), ({w} : Finset A))] with i hi
  exact hi.2 (Finset.mem_singleton_self w)

lemma fourUltra_le : (fourUltra A : Filter (FourIndex A)) ≤ atTop := by
  classical
  exact Ultrafilter.of_le atTop

lemma fourEta_ultra : Tendsto (fourEta A) (fourUltra A : Filter (FourIndex A)) (𝓝 0) :=
  (fourEta_tendsto A).mono_left (fourUltra_le A)
end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.ultrafilterPartialOrder
attribute [local instance] OAI.MainGap.ultrafilterStarOrderedRing
end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Avoidance ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
open Filter
open scoped Topology
universe u v
variable {ι : Type*} {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.avoidanceLimitPartialOrder
attribute [local instance] OAI.MainGap.avoidanceLimitStarOrderedRing
attribute [local instance] OAI.MainGap.avoidanceLimitOperatorPartialOrder
attribute [local instance] OAI.MainGap.avoidanceLimitOperatorStarOrderedRing
variable {H : ι → Type v} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

end MainGap

namespace MainGap
universe u v
open Filter
open scoped Topology
variable (A : Type u) [CStarAlgebra A]

attribute [instance] HilbertRep.normed HilbertRep.inner HilbertRep.complete

variable {A}
attribute [local instance] OAI.MainGap.avoidancePartialOrder
attribute [local instance] OAI.MainGap.avoidanceStarOrderedRing
attribute [local instance] OAI.MainGap.avoidanceOperatorPartialOrder
attribute [local instance] OAI.MainGap.avoidanceOperatorStarOrderedRing
theorem four_avoidance_unital {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hp : ∀ z : A, 0 ≤ z → z ∈ fourHer X → ProperlyInfinite z) :
    ∃ T : Fin 4 → A, (∀ j, ‖T j‖ ≤ 1) ∧ (∀ j, T j ∈ fourHer X) ∧
      ∀ R : HilbertRep.{u,v} A, (1/4 : ℝ) < ‖R.hom X‖ →
        ¬ ∀ j, R.hom (T j) = R.hom (B j) := by
  classical
  by_contra! hbad
  let F : ∀ i : FourIndex A, FourChoice.{v,u} X B i.2 (fourEta A i) :=
    fun i => Classical.choice (fourChoice_nonempty hX B hp i.2 (fourEta_pos A i))
  have hbad' : ∀ i : FourIndex A, ∃ R : HilbertRep.{u,v} A,
      (1/4 : ℝ) < ‖R.hom X‖ ∧ ∀ j, R.hom ((F i).T j) = R.hom (B j) :=
    fun i => hbad (F i).T (F i).contractive (F i).mem
  choose R hRX hmatch using hbad'
  let π := fun i => (R i).hom
  change ∀ i j, π i ((F i).T j) = π i (B j) at hmatch
  have hVbig : ∀ i, (1/8 : ℝ) < ‖π i (firstV X)‖ := by
    intro i
    have hn : ‖π i X - π i (firstV X)‖ ≤ (1/8 : ℝ) := by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (π i) _).trans
        (norm_sub_cut_le hX (by norm_num))
    have hm := norm_sub_norm_le (π i X) (π i (firstV X))
    have hi := hRX i
    change (1/4 : ℝ) < ‖π i X‖ at hi
    linarith
  choose ξ hξ hξV using fun i => (π i (firstV X)).exists_lt_apply_of_lt_opNorm (hVbig i)
  have hnξ : ∀ i, ‖ξ i‖ ≤ 1 := fun i => (hξ i).le
  have hEt := fourEta_ultra A
  apply four_limit_impossible (fourUltra A) π ξ hnξ hX B
    (Filter.Eventually.of_forall (fun i => (hξV i).le))
    (fun i => (F i).first_bound (π i) hX (fourEta_pos A i) (hmatch i)) ?_ ?_ ?_ ?_ ?_
    (fun i => (F i).last_bound (π i) hX (fourEta_pos A i) (hmatch i)) ?_ ?_ ?_ ?_
  · intro i
    have hm := congrArg (π i) (F i).first_equal
    simpa only [map_mul, map_star, hmatch i] using hm
  · intro i
    have hm := congrArg (π i) (F i).first_cross
    simpa only [map_mul, map_star, hmatch i, map_zero] using hm
  · intro i
    have hm := congrArg (π i) ((F i).first_support₀ hX)
    simpa only [map_mul, map_star, hmatch i] using hm
  · intro i
    have hm := congrArg (π i) ((F i).first_support₁ hX)
    simpa only [map_mul, map_star, hmatch i] using hm
  · intro w
    have hg : Tendsto (fun i : FourIndex A =>
        Real.sqrt (2 * fourEta A i) * ‖CFC.sqrt (firstV X)‖ +
          fourEta A i * ‖w‖ * ‖firstV X‖) (fourUltra A : Filter (FourIndex A)) (𝓝 0) := by
      convert ((hEt.const_mul 2).sqrt.mul_const ‖CFC.sqrt (firstV X)‖).add
        ((hEt.mul_const ‖w‖).mul_const ‖firstV X‖) using 1; norm_num
    apply squeeze_zero' (Filter.Eventually.of_forall (fun i => norm_nonneg _)) ?_ hg
    filter_upwards [fourUltra_le A (fourIndex_eventually_mem A w)] with i hi
    exact represented_mixed_estimate (π i) (firstU_nonneg _ _) (cut_nonneg X _)
      (fourEta_pos A i) hi ((F i).first_norm (π i) hX (fourEta_pos A i) (hmatch i)).le
  · intro i
    have hm := congrArg (π i) (F i).last_cross
    simpa only [map_mul, map_star, hmatch i, map_zero] using hm
  · intro i
    have hm := congrArg (π i) (F i).last_equal
    simpa only [map_mul, map_star, hmatch i] using hm
  · have ht : Tendsto (fun i : FourIndex A => 4 * fourEta A i)
        (fourUltra A : Filter (FourIndex A)) (𝓝 0) := by
      simpa using hEt.const_mul 4
    exact squeeze_zero' (Filter.Eventually.of_forall (fun i => norm_nonneg _))
      (Filter.Eventually.of_forall (fun i =>
        ((F i).last_norm_lt (π i) hX (fourEta_pos A i) (hmatch i)).le)) ht
  · intro i
    have hm := congrArg (π i) (F i).last_support
    simpa only [map_mul, hmatch i] using hm

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open Filter
open scoped Topology
attribute [local instance] OAI.MainGap.avoidancePartialOrder
attribute [local instance] OAI.MainGap.avoidanceStarOrderedRing
attribute [local instance] OAI.MainGap.avoidanceOperatorPartialOrder
attribute [local instance] OAI.MainGap.avoidanceOperatorStarOrderedRing


theorem solution.{u,v} : type_of% @_root_.OAI.MainGap.four_avoidance_unital.{u,v} := @_root_.OAI.MainGap.four_avoidance_unital.{u,v}
