-- Prove2me | solution 1 for OAI.BorsukNine.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:50:04.310715+00:00
-- url     : https://prove2.me/submissions/6424beb1-d345-4437-aa26-b3e8af9ca5b5

import Mathlib
import Definitions.Def_BorsukNine
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_Admissible_face_extends_four
import Theorems.Thm_OAI_BorsukNine_Admissible_face_extends_three
import Theorems.Thm_OAI_BorsukNine_Admissible_no_free_ridge
import Theorems.Thm_OAI_BorsukNine_Admissible_tetra_no_free_triangle
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_no_ten_system

section
-- module Solutions.OAIQ058_BK.Compat
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Equivariance
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]

section Cone

lemma cone_simplex (K : PreAbstractSimplicialComplex V) (a : V) {s : Finset V} (hs : s ∈ K) :
    cone K a (simplex K s) = if a ∈ s then 0 else simplex K (insert a s) := by
  simp [simplex_of_mem K hs, cone, Finsupp.linearCombination_single]

lemma cone_boundary_simplex (K : PreAbstractSimplicialComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) (ha : a ∉ s) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases hc : s.card = 1
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
    have hab : a ≠ b := by simpa using ha
    have hs' : ({a} : Finset V) ∈ K :=
      (K.isRelLowerSet_faces hinsert).2 (by simp) (Finset.singleton_nonempty a)
    rw [cone_simplex K a hs, ite_eq_right ha, boundary_simplex K hinsert,
      boundary_simplex K hs, augmentation_simplex K hs]
    simp [ha, Finset.erase_insert_of_ne hab]
  · have hn : s.Nonempty := (K.isRelLowerSet_faces hs).1
    have hc' : 2 ≤ s.card := by have := hn.card_pos; omega
    have he (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
      omega
    have heK (b : V) (hb : b ∈ s) : s.erase b ∈ K :=
      (K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (he b hb)
    rw [cone_simplex K a hs, ite_eq_right ha, boundary_simplex K hinsert,
      augmentation_simplex K hs, ite_eq_right hc, zero_smul, add_zero,
      boundary_simplex K hs, map_sum, Finset.sum_insert ha, Finset.erase_insert ha]
    apply congrArg (fun z => simplex K s + z)
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := by intro hh; subst b; exact ha hb
    have hn : a ∉ s.erase b := fun hh => ha (Finset.mem_of_mem_erase hh)
    rw [cone_simplex K a (heK b hb), ite_eq_right hn, Finset.erase_insert_of_ne hab]

lemma cone_boundary_simplex_all (K : PreAbstractSimplicialComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases ha : a ∈ s
  · by_cases hc : s.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
      have hab : a = b := Finset.mem_singleton.mp ha
      subst b
      rw [cone_simplex K a hs, ite_eq_left ha, map_zero, boundary_simplex K hs,
        augmentation_simplex K hs]
      simp [chain_add_self]
    · have hcn (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
        have hn := (K.isRelLowerSet_faces hs).1.card_pos
        rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
        omega
      have hcon : cone K a (boundary K (simplex K s)) = simplex K s := by
        rw [boundary_simplex K hs, map_sum]
        rw [Finset.sum_eq_single a]
        · rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) (hcn a ha))]
          simp [Finset.insert_erase ha]
        · intro b hb hba
          rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (hcn b hb))]
          simp [Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩]
        · exact fun hn => False.elim (hn ha)
      rw [cone_simplex K a hs, ite_eq_left ha, map_zero, hcon,
        augmentation_simplex K hs, ite_eq_right hc, zero_smul, add_zero, chain_add_self]
  · exact cone_boundary_simplex K a hs hinsert ha

omit [DecidableEq V] in
lemma chain_eq_sum (K : PreAbstractSimplicialComplex V) (c : Chain K) :
    c = ∑ s ∈ c.support, c s • simplex K s.val := by
  conv_lhs => rw [← c.sum_single]
  simp [Finsupp.sum, simplex_of_mem K, Finsupp.smul_single]

lemma cone_boundary (K : PreAbstractSimplicialComplex V) (a : V) (c : Chain K)
    (hc : ∀ s ∈ c.support, insert a s.val ∈ K) :
    boundary K (cone K a c) = c + cone K a (boundary K c) +
      augmentation K c • simplex K {a} := by
  classical
  conv_lhs => rw [chain_eq_sum K c]
  rw [map_sum, map_sum]
  have he (s : { s : Finset V // s ∈ K }) (hs : s ∈ c.support) :
      boundary K (cone K a (c s • simplex K s.val)) =
        c s • simplex K s.val + cone K a (boundary K (c s • simplex K s.val)) +
        augmentation K (c s • simplex K s.val) • simplex K {a} := by
    rw [map_smul, map_smul, cone_boundary_simplex_all K a s.property (hc s hs)]
    simp only [smul_add, map_smul, smul_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← map_sum, ← map_sum, ← Finset.sum_smul, ← map_sum, ← chain_eq_sum K c]

end Cone

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SmithTheory_Involution
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
section Involution
variable {ι : Type*}

lemma involutionNorm_sq (τ : ι ≃ ι) (hτ : Function.Involutive τ) :
    (involutionNorm τ).comp (involutionNorm τ) = 0 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro a
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  simp only [LinearMap.comp_apply, involutionNorm_apply, hsymm, ht,
    LinearMap.zero_apply, Finsupp.zero_apply]
  simp [add_comm, CharTwo.add_self_eq_zero]

end Involution

end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SymmetricCoordinates
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SymmetricCoordinates
variable {ν : Type*} [Fintype ν] [LinearOrder ν]

omit [Fintype ν] in
lemma symmetricCoordinates_upper (x : EuclideanSpace ℝ (UpperTriangle ν))
    (i j : ν) (hij : i ≤ j) : symmetricCoordinates x i j = x ⟨(i,j), hij⟩ := by
  change (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) = _
  exact dite_eq_left hij

omit [Fintype ν] in
lemma symmetricCoordinates_selfAdjoint (x : EuclideanSpace ℝ (UpperTriangle ν)) :
    IsSelfAdjoint (symmetricCoordinates x) := by
  change (symmetricCoordinates x)ᴴ = symmetricCoordinates x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change (if h : j ≤ i then x ⟨(j,i),h⟩ else x ⟨(i,j),le_of_not_ge h⟩) =
    (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have he := le_antisymm hij hji
      subst j
      rfl
    · simp [hij, hji]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [hij, hji]

omit [Fintype ν] in
lemma symmetricCoordinates_injective : Function.Injective (symmetricCoordinates (ν := ν)) := by
  intro x y hxy
  apply PiLp.ext
  intro p
  have h := congrArg (fun A : Matrix ν ν ℝ => A p.val.1 p.val.2) hxy
  simpa only [symmetricCoordinates_upper _ _ _ p.property] using h

end SymmetricCoordinates

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixNorm
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixNorm
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "E" => EuclideanSpace ℝ ν

lemma matrix_action_norm_sq (A : Matrix ν ν ℝ) (x : E) :
    ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x‖ ^ 2 =
      ⟪x, (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) (star A * A) x⟫ := by
  rw [map_mul, map_star]
  change ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x‖ ^ 2 =
    ⟪x, (star ((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A)) ((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) A x)⟫
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

lemma sqrt_action_norm_sq (Q : Matrix ν ν ℝ) (hQ : 0 ≤ Q) (x : E) :
    ‖(Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) (CFC.sqrt Q) x‖ ^ 2 = ⟪x, (Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)) Q x⟫ := by
  rw [matrix_action_norm_sq, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]

end MatrixNorm

section MatrixRange
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)
lemma matrix_sqrt_range (Q : Matrix ν ν ℝ) (hQ : 0 ≤ Q) :
    LinearMap.range (op (CFC.sqrt Q)).toLinearMap = LinearMap.range (op Q).toLinearMap := by
  have hs : star (op (CFC.sqrt Q)) = op (CFC.sqrt Q) := by
    rw [← map_star, (CFC.sqrt_nonneg Q).star_eq]
  have hh := LinearMap.range_adjoint_comp_self (op (CFC.sqrt Q)).toLinearMap
  have ha : (op (CFC.sqrt Q)).toLinearMap.adjoint = (op (CFC.sqrt Q)).toLinearMap := by
    change (ContinuousLinearMap.adjoint (op (CFC.sqrt Q))).toLinearMap = _
    rw [← ContinuousLinearMap.star_eq_adjoint, hs]
  rw [ha] at hh
  have hm : (op (CFC.sqrt Q)).toLinearMap.comp (op (CFC.sqrt Q)).toLinearMap = (op Q).toLinearMap := by
    change (op (CFC.sqrt Q) * op (CFC.sqrt Q)).toLinearMap = _
    rw [← map_mul, CFC.sqrt_mul_sqrt_self Q hQ]
  rw [hm] at hh
  exact hh.symm

end MatrixRange

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_Basic
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine

open scoped RealInnerProductSpace ContDiff

theorem continuous_projector : Continuous projector := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  exact (PiLp.continuous_apply 2 _ ij.1).mul (PiLp.continuous_apply 2 _ ij.2)

theorem isCompact_projectorSet : IsCompact projectorSet := by
  have h : {u : Vector4 | ‖u‖ = 1} = Metric.sphere 0 1 := by
    ext u
    simp
  rw [projectorSet, h]
  exact (isCompact_sphere (0 : Vector4) 1).image continuous_projector

theorem projector_inner (u v : Vector4) :
    ⟪projector u, projector v⟫ = ⟪u, v⟫ ^ 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, projector]
  change (∑ ij : Fin 4 × Fin 4, (v ij.1 * v ij.2) * (u ij.1 * u ij.2)) =
    (∑ i : Fin 4, v i * u i) ^ 2
  rw [Fintype.sum_prod_type]
  simp only [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem projector_norm_sq (u : Vector4) : ‖projector u‖ ^ 2 = ‖u‖ ^ 4 := by
  rw [← real_inner_self_eq_norm_sq, projector_inner, real_inner_self_eq_norm_sq]
  ring

theorem projectorSet_subset_traceOneSymmetric : projectorSet ⊆ traceOneSymmetric := by
  rintro _ ⟨u, hu, rfl⟩
  constructor
  · intro i j
    simp [mul_comm]
  · have he : (∑ i : Fin 4, u i * u i) = ‖u‖ ^ 2 := by
      exact (EuclideanSpace.inner_eq_star_dotProduct u u).symm.trans
        (real_inner_self_eq_norm_sq u)
    change ‖u‖ = 1 at hu
    simp only [projector_apply, he, hu, one_pow]

theorem projector_dist_sq (u v : Vector4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) ^ 2 = 2 - 2 * ⟪u, v⟫ ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real, projector_norm_sq, projector_norm_sq,
    projector_inner, hu, hv]
  ring

theorem projector_dist_le (u v : Vector4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) ≤ Real.sqrt 2 := by
  have hd := projector_dist_sq u v hu hv
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [sq_nonneg ⟪u, v⟫, dist_nonneg (x := projector u) (y := projector v)]

theorem projector_dist_eq_sqrt_two_iff (u v : Vector4)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) = Real.sqrt 2 ↔ ⟪u, v⟫ = 0 := by
  have hd := projector_dist_sq u v hu hv
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  constructor
  · intro h
    rw [h] at hd
    nlinarith [sq_nonneg ⟪u, v⟫]
  · intro h
    rw [h] at hd
    have hn := dist_nonneg (x := projector u) (y := projector v)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith

theorem diam_projectorSet : Metric.diam projectorSet = Real.sqrt 2 := by
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg 2)
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact projector_dist_le u v hu hv
  · let u : Vector4 := EuclideanSpace.single 0 1
    let v : Vector4 := EuclideanSpace.single 1 1
    have hu : ‖u‖ = 1 := by simp [u]
    have hv : ‖v‖ = 1 := by simp [v]
    have huv : ⟪u, v⟫ = 0 := by simp [u, v, EuclideanSpace.inner_single_left]
    have hd := (projector_dist_eq_sqrt_two_iff u v hu hv).mpr huv
    rw [← hd]
    exact Metric.dist_le_diam_of_mem isCompact_projectorSet.isBounded
      ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩

theorem contDiff_projector : ContDiff ℝ ∞ projector := by
  apply (contDiff_piLp 2).mpr
  intro ij
  exact (contDiff_piLp_apply (p := 2) (i := ij.1)).mul (contDiff_piLp_apply (p := 2) (i := ij.2))

theorem dist_lt_of_mem_thickening_small {C : Set Matrix4}
    (hC : C ⊆ projectorSet) (hd : Metric.diam C < Real.sqrt 2)
    {P Q : Matrix4}
    (hP : P ∈ Metric.thickening ((Real.sqrt 2 - Metric.diam C) / 4) C)
    (hQ : Q ∈ Metric.thickening ((Real.sqrt 2 - Metric.diam C) / 4) C) :
    dist P Q < Real.sqrt 2 := by
  rcases Metric.mem_thickening_iff.mp hP with ⟨p, hp, hPp⟩
  rcases Metric.mem_thickening_iff.mp hQ with ⟨q, hq, hQq⟩
  have hb := isCompact_projectorSet.isBounded.subset hC
  have hpq := Metric.dist_le_diam_of_mem hb hp hq
  have ht : dist P Q ≤ dist P p + dist p q + dist Q q := by
    calc
      dist P Q ≤ dist P p + dist p Q := dist_triangle P p Q
      _ ≤ dist P p + (dist p q + dist q Q) :=
        add_le_add le_rfl (dist_triangle p q Q)
      _ = dist P p + dist p q + dist Q q := by rw [dist_comm q Q]; ring
  linarith

open scoped Manifold

theorem cover_to_admissible (h : HasTenSmallCover) :
    ∃ f : Vector4 → Fin 10 → ℝ, Admissible f := by
  classical
  rcases h with ⟨C, hCX, hcov, hdiam⟩
  let U : Fin 10 → Set Matrix4 := fun i =>
    Metric.thickening ((Real.sqrt 2 - Metric.diam (C i)) / 4) (C i)
  have hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_thickening
  have hCU : ∀ i, C i ⊆ U i := by
    intro i
    apply Metric.self_subset_thickening
    linarith [hdiam i]
  have hXU : projectorSet ⊆ ⋃ i, U i := by
    intro P hP
    rcases Set.mem_iUnion.mp (hcov hP) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hCU i hi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Matrix4)) isCompact_projectorSet.isClosed U hU hXU
  refine ⟨fun u i => ρ i (projector u), ?_⟩
  constructor
  · intro i
    exact (contMDiff_iff_contDiff.mp (ρ i).contMDiff).comp contDiff_projector
  · intro u i
    simp
  · intro u _ i
    exact ρ.nonneg i (projector u)
  · intro u hu
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (show projector u ∈ projectorSet
      from ⟨u, hu, rfl⟩)
  · intro u v hu hv huv i ⟨hui, hvi⟩
    have huU : projector u ∈ U i := hρ i (subset_tsupport _ (ne_of_gt hui))
    have hvU : projector v ∈ U i := hρ i (subset_tsupport _ (ne_of_gt hvi))
    have hd := dist_lt_of_mem_thickening_small (hCX i) (hdiam i) huU hvU
    rw [(projector_dist_eq_sqrt_two_iff u v hu hv).mpr huv] at hd
    exact lt_irrefl _ hd

lemma Admissible.support_nonempty {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u : V} (hu : ‖u‖ = 1) :
    (positiveSupport f u).Nonempty := by
  classical
  have hs : 0 < ∑ i, f u i := by rw [hf.sum_one u hu]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hf.nonneg u hu i)).mp hs
  exact ⟨i, (mem_positiveSupport f u i).mpr hi⟩

lemma Admissible.disjoint_supports {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u v : V}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : ⟪u, v⟫ = 0) :
    Disjoint (positiveSupport f u) (positiveSupport f v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hf.orthogonal u v hu hv horth i
    ⟨(mem_positiveSupport f u i).mp hi, (mem_positiveSupport f v i).mp hj⟩

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_HomogeneousLift
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
section HomogeneousLift
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*}

lemma homogeneousLift_unit (f : V → ι → ℝ) {v : V} (hv : ‖v‖ = 1) :
    homogeneousLift f v = f v := by
  ext i
  simp [homogeneousLift, hv]

variable [Fintype ι]

lemma Admissible.lift_nonneg {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    0 ≤ homogeneousLift f v i := by
  by_cases hv : v = 0
  · simp [hv]
  · exact mul_nonneg (sq_nonneg _) (hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i)

lemma Admissible.lift_sum {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ∑ i, homogeneousLift f v i = ‖v‖ ^ 2 := by
  classical
  by_cases hv : v = 0
  · simp [hv]
  · simp only [homogeneousLift, ← Finset.mul_sum]
    have hn : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    rw [hf.sum_one _ hn, mul_one]

lemma Admissible.lift_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    homogeneousLift f v i ≤ ‖v‖ ^ 2 := by
  classical
  rw [← hf.lift_sum v]
  exact Finset.single_le_sum (fun j _ => hf.lift_nonneg v j) (Finset.mem_univ i)

lemma Admissible.lift_norm_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ‖homogeneousLift f v‖ ≤ ‖v‖ ^ 2 := by
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg _)]
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf.lift_nonneg v i)] using hf.lift_le v i

omit [Fintype ι] in
lemma homogeneousLift_smul_pos (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 < t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  ext i
  have he : (‖t • v‖⁻¹ : ℝ) • (t • v) = (‖v‖⁻¹ : ℝ) • v := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv_rev, smul_smul]
    congr 1
    field_simp
  change ‖t • v‖ ^ 2 * f ((‖t • v‖⁻¹ : ℝ) • (t • v)) i = t ^ 2 * (‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  ring

lemma Admissible.lift_continuous {f : V → ι → ℝ} (hf : Admissible f) :
    Continuous (homogeneousLift f) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    rw [ContinuousAt, homogeneousLift_zero]
    apply squeeze_zero_norm (fun x => hf.lift_norm_le x)
    have hc : Continuous (fun x : V => ‖x‖ ^ 2) := continuous_norm.pow 2
    simpa using hc.tendsto (0 : V)
  · have hn : ContinuousAt (fun x : V => (‖x‖⁻¹ : ℝ) • x) v :=
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hv)).smul continuousAt_id
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_norm.continuousAt.pow 2).mul ((hf.smooth i).continuous.continuousAt.comp hn)

end HomogeneousLift

open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_SphereMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMeasure
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

variable {V}

omit [Nontrivial V] in
lemma sphereRotation_preserves_toSphere (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) volume.toSphere volume.toSphere := by
  refine ⟨(sphereRotation e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereRotation e).measurable hs,
    Measure.toSphere_apply' _ ((sphereRotation e).measurable hs), Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereRotation e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨r, hr, e u, ⟨sphereRotation e u, hu, rfl⟩, by simp⟩
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, he⟩
      refine ⟨r, hr, e.symm u, ⟨(sphereRotation e).symm u, ?_, rfl⟩, ?_⟩
      · simpa using hu
      · apply e.injective
        simpa using he
  rw [hset]
  have he := e.measurePreserving.map_eq
  have hm := e.toMeasurableEquiv.measurableEmbedding.map_apply volume
    (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv] at hm
  rw [he] at hm
  exact hm.symm

omit [Nontrivial V] in
lemma sphereRotation_preserves_probability (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) (sphereProbability V) (sphereProbability V) := by
  exact (sphereRotation_preserves_toSphere e).smul_measure _

omit [Nontrivial V] in
lemma integral_sphere_rotation (e : V ≃ₗᵢ[ℝ] V) (g : UnitSphere V → ℝ) :
    (∫ x, g (sphereRotation e x) ∂sphereProbability V) =
      ∫ x, g x ∂sphereProbability V :=
  (sphereRotation_preserves_probability e).integral_comp
    (sphereRotation e).measurableEmbedding g

end SphereMeasure

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_IntegralLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section IntegralLift
variable {ν ι : Type*} [Fintype ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

omit [Nonempty ν] in
lemma Admissible.integrand_continuous {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    Continuous (fun x : UnitSphere E => homogeneousLift f (T x) i) :=
  (continuous_apply i).comp (hf.lift_continuous.comp (T.continuous.comp continuous_subtype_val))

lemma Admissible.integrand_integrable {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    Integrable (fun x : UnitSphere E => homogeneousLift f (T x) i) (sphereProbability E) :=
  (hf.integrand_continuous T i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [Nonempty ν] in
lemma Admissible.integralLift_nonneg {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) : 0 ≤ integralLift f T i :=
  mul_nonneg (Nat.cast_nonneg _) (integral_nonneg (fun _ => hf.lift_nonneg _ i))

lemma Admissible.integralLift_sum {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) : ∑ i, integralLift f T i =
      (Fintype.card ν : ℝ) * ∫ x : UnitSphere E, ‖T x‖ ^ 2 ∂sphereProbability E := by
  classical
  simp only [integralLift, ← Finset.mul_sum]
  rw [← integral_finsetSum _ (fun i _ => hf.integrand_integrable T i)]
  simp only [hf.lift_sum]

lemma Admissible.integralLift_pos_iff_sphere {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    0 < integralLift f T i ↔ ∃ x : UnitSphere E, 0 < homogeneousLift f (T x) i := by
  have hc : (0 : ℝ) < Fintype.card ν := Nat.cast_pos.mpr Fintype.card_pos
  rw [integralLift, mul_pos_iff_of_pos_left hc]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have he : (fun x : UnitSphere E => homogeneousLift f (T x) i) = 0 := by
      funext x
      exact le_antisymm (hn x) (hf.lift_nonneg _ i)
    rw [he] at h
    change 0 < ∫ _ : UnitSphere E, (0 : ℝ) ∂sphereProbability E at h
    simp only [integral_zero, lt_self_iff_false] at h
  · rintro ⟨x, hx⟩
    exact integral_pos_of_integrable_nonneg_nonzero (hf.integrand_continuous T i)
      (hf.integrand_integrable T i) (fun _ => hf.lift_nonneg _ i) hx.ne'

lemma Admissible.integralLift_continuous {f : E → ι → ℝ} (hf : Admissible f) :
    Continuous (integralLift f) := by
  apply continuous_pi
  intro i
  apply continuous_const.mul
  have hc : Continuous (fun p : (E →L[ℝ] E) × UnitSphere E =>
      homogeneousLift f (p.1 p.2) i) :=
    (continuous_apply i).comp (hf.lift_continuous.comp
      (continuous_fst.clm_apply (continuous_subtype_val.comp continuous_snd)))
  have hi := continuous_parametric_integral_of_continuous
    (μ := sphereProbability E)
    (f := fun (T : E →L[ℝ] E) (x : UnitSphere E) => homogeneousLift f (T x) i)
    hc isCompact_univ
  simpa only [setIntegral_univ] using hi

lemma Admissible.integralLift_pos_iff {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    0 < integralLift f T i ↔ ∃ x : E, 0 < homogeneousLift f (T x) i := by
  rw [hf.integralLift_pos_iff_sphere]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hn : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx0)
    refine ⟨⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx0)⟩, ?_⟩
    simp only [map_smul, homogeneousLift_smul_pos f _ hn, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (sq_pos_of_pos hn) hx

lemma Admissible.integralLift_support {f : E → ι → ℝ} (hf : Admissible f)
    (T : E →L[ℝ] E) (i : ι) :
    0 < integralLift f T i ↔ ∃ v : E,
      v ∈ LinearMap.range T.toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.integralLift_pos_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : T x ≠ 0 := by
      intro hz
      simp only [hz, homogeneousLift_zero, Pi.zero_apply, lt_self_iff_false] at hx
    refine ⟨‖T x‖⁻¹ • T x, ⟨‖T x‖⁻¹ • x, by simp⟩,
      norm_smul_inv_norm (𝕜 := ℝ) hx0, ?_⟩
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mp hx
  · rintro ⟨v, ⟨x, rfl⟩, hv, hx⟩
    refine ⟨x, ?_⟩
    rw [homogeneousLift_unit f (show ‖T x‖ = 1 from hv)]
    exact hx

end IntegralLift

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_SphereMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMoments
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sphere_coord_integrable (i j : ι) :
    Integrable (fun x : UnitSphere E => (x : E) i * (x : E) j) (sphereProbability E) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val)
  · exact HasCompactSupport.of_compactSpace _

omit [Nonempty ι] in
lemma sphere_coord_cross {i j : ι} (hij : i ≠ j) :
    (∫ x : UnitSphere E, (x : E) i * (x : E) j ∂sphereProbability E) = 0 := by
  classical
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hi := integral_sphere_rotation e (fun x : UnitSphere E => (x : E) i * (x : E) j)
  have he : (fun x : UnitSphere E => (sphereRotation e x : E) i * (sphereRotation e x : E) j) =
      fun x : UnitSphere E => -((x : E) i * (x : E) j) := by
    funext x
    simp [sphereRotation, e, hij.symm]
  rw [he, integral_neg] at hi
  linarith

omit [Nonempty ι] in
lemma sphere_coord_diag_eq (i j : ι) :
    (∫ x : UnitSphere E, (x : E) i * (x : E) i ∂sphereProbability E) =
      ∫ x : UnitSphere E, (x : E) j * (x : E) j ∂sphereProbability E := by
  classical
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hi := integral_sphere_rotation e (fun x : UnitSphere E => (x : E) j * (x : E) j)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp [sphereRotation, e, Equiv.piCongrLeft']

lemma sphere_coord_diag (i : ι) :
    (∫ x : UnitSphere E, (x : E) i * (x : E) i ∂sphereProbability E) =
      (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hs : (∑ j, ∫ x : UnitSphere E, (x : E) j * (x : E) j ∂sphereProbability E) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => sphere_coord_integrable j j)]
    have he : (fun x : UnitSphere E => ∑ j, (x : E) j * (x : E) j) = fun _ => (1 : ℝ) := by
      funext x
      have hn : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
      have hh := EuclideanSpace.real_norm_sq_eq (x : E)
      rw [hn] at hh
      simpa only [one_pow, pow_two, one_mul] using hh.symm
    rw [he]
    simp
  have hval : (Fintype.card ι : ℝ) *
      (∫ x : UnitSphere E, (x : E) i * (x : E) i ∂sphereProbability E) = 1 := by
    rw [← hs]
    rw [Finset.sum_congr rfl (fun j _ => sphere_coord_diag_eq j i)]
    simp
  exact eq_inv_of_mul_eq_one_right hval

lemma sphere_quadratic_integral (A : Matrix ι ι ℝ) :
    (∫ x : UnitSphere E, (x : E).ofLp ⬝ᵥ A *ᵥ (x : E).ofLp ∂sphereProbability E) =
      Matrix.trace A * (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hc (i j : ι) : Integrable (fun x : UnitSphere E =>
      A i j * ((x : E) i * (x : E) j)) (sphereProbability E) :=
    (sphere_coord_integrable i j).const_mul _
  have he : (fun x : UnitSphere E => (x : E).ofLp ⬝ᵥ A *ᵥ (x : E).ofLp) =
      fun x : UnitSphere E => ∑ i, ∑ j, A i j * ((x : E) i * (x : E) j) := by
    funext x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hc i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hc _ j), integral_const_mul]
  calc
    _ = ∑ i, A i i * (Fintype.card ι : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [sphere_coord_diag]
      · intro j _ hji
        rw [sphere_coord_cross hji.symm, mul_zero]
      · simp
    _ = _ := by rw [← Finset.sum_mul]; rfl

end SphereMoments

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_MatrixKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix

section PositiveExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma Admissible.positiveExtension_nonneg {f : E → ι → ℝ} (hf : Admissible f)
    (Q : Matrix ν ν ℝ) (i : ι) : 0 ≤ positiveExtension f Q i :=
  hf.integralLift_nonneg _ _

lemma Admissible.positiveExtension_sum {f : E → ι → ℝ} (hf : Admissible f)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) : ∑ i, positiveExtension f Q i = Matrix.trace Q := by
  classical
  rw [positiveExtension, hf.integralLift_sum]
  simp_rw [sqrt_action_norm_sq Q hQ, Matrix.inner_toEuclideanCLM]
  rw [sphere_quadratic_integral]
  have hn : (Fintype.card ν : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  field_simp

lemma Admissible.positiveExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (positiveExtension f) {Q : Matrix ν ν ℝ | 0 ≤ Q} := by
  have hc : Continuous (fun Q : Matrix ν ν ℝ => op Q) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact hf.integralLift_continuous.comp_continuousOn
    (hc.comp_continuousOn CFC.continuousOn_sqrt)

lemma Admissible.positiveExtension_support {f : E → ι → ℝ} (hf : Admissible f)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) (i : ι) :
    0 < positiveExtension f Q i ↔ ∃ v : E,
      v ∈ LinearMap.range (op Q).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [positiveExtension, hf.integralLift_support, matrix_sqrt_range Q hQ]

end PositiveExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_MatrixGeometry_SignedExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SignedExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma matrix_images_orthogonal {P N : Matrix ν ν ℝ} (hP : 0 ≤ P) (hPN : P * N = 0)
    (x y : E) : ⟪op P x, op N y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have hs : star (op P) = op P := by rw [← map_star, hP.star_eq]
  rw [hs]
  change ⟪x, (op P * op N) y⟫ = 0
  rw [← map_mul, hPN, map_zero]
  simp

lemma Admissible.positiveExtension_orthogonal {f : E → ι → ℝ} (hf : Admissible f)
    {P N : Matrix ν ν ℝ} (hP : 0 ≤ P) (hN : 0 ≤ N) (hPN : P * N = 0) (i : ι) :
    positiveExtension f P i * positiveExtension f N i = 0 := by
  apply mul_eq_zero.mpr
  by_contra hn
  push Not at hn
  have hp := lt_of_le_of_ne (hf.positiveExtension_nonneg P i) (Ne.symm hn.1)
  have hn' := lt_of_le_of_ne (hf.positiveExtension_nonneg N i) (Ne.symm hn.2)
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hP i).mp hp
  obtain ⟨w, ⟨y, rfl⟩, hw, hy⟩ := (hf.positiveExtension_support hN i).mp hn'
  exact hf.orthogonal _ _ hv hw (matrix_images_orthogonal hP hPN x y) i ⟨hx, hy⟩

omit [Nonempty ν] [Fintype ι] in
lemma signedExtension_odd (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    signedExtension f (-A) = -signedExtension f A := by
  simp [signedExtension, CFC.posPart_neg, CFC.negPart_neg]

lemma Admissible.signedExtension_abs_sum {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) :
    ∑ i, |signedExtension f A i| = Matrix.trace (CFC.abs A) := by
  classical
  have hcoord (i : ι) : |signedExtension f A i| =
      positiveExtension f A⁺ i + positiveExtension f A⁻ i := by
    have hp := hf.positiveExtension_nonneg A⁺ i
    have hn := hf.positiveExtension_nonneg A⁻ i
    have hprod := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    rcases mul_eq_zero.mp hprod with hz | hz
    · simp [signedExtension, hz, abs_of_nonneg hn]
    · simp [signedExtension, hz, abs_of_nonneg hp]
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib, hf.positiveExtension_sum (CFC.posPart_nonneg A),
    hf.positiveExtension_sum (CFC.negPart_nonneg A), ← Matrix.trace_add,
    CFC.posPart_add_negPart A hA]

omit [Nonempty ν] in
lemma matrix_posPart_continuousOn :
    ContinuousOn (fun A : Matrix ν ν ℝ => A⁺) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : Matrix ν ν ℝ => (1 / 2 : ℝ) • (CFC.abs A + A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.add continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁺ = (1 / 2 : ℝ) • (CFC.abs A + A)
  rw [CFC.abs_add_self A hA, two_smul, smul_add]
  module

omit [Nonempty ν] in
lemma matrix_negPart_continuousOn :
    ContinuousOn (fun A : Matrix ν ν ℝ => A⁻) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : Matrix ν ν ℝ => (1 / 2 : ℝ) • (CFC.abs A - A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.sub continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁻ = (1 / 2 : ℝ) • (CFC.abs A - A)
  rw [CFC.abs_sub_self A hA, two_smul, smul_add]
  module

lemma Admissible.signedExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (signedExtension f) {A : Matrix ν ν ℝ | IsSelfAdjoint A} := by
  apply ContinuousOn.sub
  · exact hf.positiveExtension_continuousOn.comp matrix_posPart_continuousOn
      (fun A _ => CFC.posPart_nonneg A)
  · exact hf.positiveExtension_continuousOn.comp matrix_negPart_continuousOn
      (fun A _ => CFC.negPart_nonneg A)

end SignedExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_FullSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section FullSupport
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]

omit [Nonempty ν] in
lemma matrix_psd_trace_zero {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q)
    (htrace : Matrix.trace Q = 0) : Q = 0 := by
  have hprod : (CFC.sqrt Q)ᴴ * CFC.sqrt Q = Q := by
    rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]
  have hz : CFC.sqrt Q = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    (hprod.symm ▸ htrace)
  rw [← hprod, hz]
  simp

end FullSupport

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_SphereExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

lemma Admissible.signedExtension_eq_zero_iff {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) : signedExtension f A = 0 ↔ A = 0 := by
  constructor
  · intro hz
    have ht : Matrix.trace (CFC.abs A) = 0 := by
      rw [← hf.signedExtension_abs_sum hA, hz]
      simp
    have habs : CFC.abs A = 0 := matrix_psd_trace_zero (CFC.abs_nonneg A) ht
    have hsq := CFC.abs_mul_abs A
    rw [habs, zero_mul] at hsq
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [Matrix.star_eq_conjTranspose] using hsq.symm
  · rintro rfl
    simp [signedExtension]

lemma Admissible.normalizedSignedExtension_norm {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (hneq : A ≠ 0) :
    ‖normalizedSignedExtension f A‖ = 1 := by
  have hn : WithLp.toLp 2 (signedExtension f A) ≠ 0 := by
    intro hz
    have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hz
    exact hneq ((hf.signedExtension_eq_zero_iff hA).mp hs)
  simp [normalizedSignedExtension, norm_smul, norm_inv, hn]

omit [Nonempty ν] in
lemma normalizedSignedExtension_odd (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    normalizedSignedExtension f (-A) = -normalizedSignedExtension f A := by
  simp [normalizedSignedExtension, signedExtension_odd, WithLp.toLp_neg]

lemma Admissible.normalizedSignedExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (normalizedSignedExtension f) {A : Matrix ν ν ℝ | IsSelfAdjoint A ∧ A ≠ 0} := by
  have hc : ContinuousOn (fun A : Matrix ν ν ℝ => WithLp.toLp 2 (signedExtension f A))
      {A | IsSelfAdjoint A ∧ A ≠ 0} :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hf.signedExtension_continuousOn.mono (fun _ h => h.1))
  apply ContinuousOn.smul (ContinuousOn.inv₀ hc.norm _) hc
  intro A hA
  rw [norm_ne_zero_iff]
  intro hh
  have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hh
  exact hA.2 ((hf.signedExtension_eq_zero_iff hA.1).mp hs)

end SphereExtension

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_SphereGeometry_OddSphereMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section OddSphereMap
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν

lemma Admissible.sphereExtension_norm {f : E → ι → ℝ} (hf : Admissible f)
    {x : EuclideanSpace ℝ (UpperTriangle ν)} (hx : ‖x‖ = 1) : ‖sphereExtension f x‖ = 1 := by
  apply hf.normalizedSignedExtension_norm (symmetricCoordinates_selfAdjoint x)
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx

omit [Nonempty ν] in
lemma sphereExtension_odd (f : E → ι → ℝ) (x : EuclideanSpace ℝ (UpperTriangle ν)) :
    sphereExtension f (-x) = -sphereExtension f x := by
  simp only [sphereExtension, map_neg, normalizedSignedExtension_odd]

lemma Admissible.sphereExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (sphereExtension f) {x : EuclideanSpace ℝ (UpperTriangle ν) | ‖x‖ = 1} := by
  apply hf.normalizedSignedExtension_continuousOn.comp
    (symmetricCoordinates.continuous_of_finiteDimensional.continuousOn) (fun x hx => ?_)
  refine ⟨symmetricCoordinates_selfAdjoint x, ?_⟩
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx

end OddSphereMap

end BorsukNine

namespace BorsukNine.SmithTheory

variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

lemma tower_augmentation_zero (d N : P →ₗ[K] P)
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (n : ℕ) (φ : P →ₗ[K] Q) (hφN : φ.comp N = 0) (hφd : φ.comp d = 0)
    (c : ℕ → P) (htower : ∀ i < n, d (c (i + 1)) = N (c i))
    (htop : N (c n) = 0) : φ (c 0) = 0 := by
  induction n generalizing φ c with
  | zero =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    rw [← hψ, LinearMap.comp_apply, htop, map_zero]
  | succ n ih =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    have hN : (ψ.comp d).comp N = 0 := by
      rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc, hψ, hφd]
    have hd' : (ψ.comp d).comp d = 0 := by
      rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]
    have hh := ih (ψ.comp d) hN hd' (fun i => c (i + 1))
      (fun i hi => htower (i + 1) (Nat.add_lt_add_right hi 1)) htop
    rw [← hψ, LinearMap.comp_apply, ← htower 0 (Nat.zero_lt_succ n)]
    exact hh

end BorsukNine.SmithTheory

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_NormMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma antipodal_tower_augmentation_zero (K : PreAbstractSimplicialComplex V)
    (e : V ≃ V) (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (n : ℕ) (c : ℕ → Chain K)
    (htower : ∀ i < n, boundary K (c (i+1)) = normMap K e (c i))
    (htop : normMap K e (c n) = 0) : augmentation K (c 0) = 0 := by
  apply SmithTheory.tower_augmentation_zero (boundary K) (normMap K e)
    (boundary_sq K) (boundary_normMap K e (fun s hs => (he s).mp hs))
    _ n (augmentation K) (augmentation_normMap K e (fun s hs => (he s).mp hs))
    (augmentation_boundary K) c htower htop
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)

omit [DecidableEq V] in
lemma simplex_mem_degree (K : PreAbstractSimplicialComplex V) {s : Finset V}
    (hs : s ∈ K) : simplex K s ∈ degreeChains K s.card := by
  rw [simplex_of_mem K hs]
  exact Finsupp.single_mem_supported _ _ rfl

omit [DecidableEq V] [DecidableEq W] in
lemma grade_map (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (d e : ℕ)
    (hT : ∀ s ∈ K, s.card = d → T (simplex K s) ∈ degreeChains L e) :
    degreeChains K d ≤ (degreeChains L e).comap T := by
  rw [degreeChains, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, rfl⟩
  change T (Finsupp.single s 1) ∈ degreeChains L e
  rw [← simplex_of_mem K s.property]
  exact hT s.val s.property hs

omit [DecidableEq V] in
lemma mapChains_degree (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (f : V → W) (hf : ∀ s ∈ K, s.image f ∈ L) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree L (hf s hs)
  · exact Submodule.zero_mem _

omit [DecidableEq V] in
lemma degreeChains_eq_bot_of_card_bound (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hK : ∀ s ∈ K, s.card < d) : degreeChains K d = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  apply Finsupp.ext
  intro s
  have hne : s.val.card ≠ d := ne_of_lt (hK s.val s.property)
  exact (Finsupp.mem_supported' F₂ c).mp hc s hne

omit [DecidableEq V] in
lemma augmentation_eq_zero_of_degree (K : PreAbstractSimplicialComplex V) (d : ℕ)
    (hd : d ≠ 1) {c : Chain K} (hc : c ∈ degreeChains K d) : augmentation K c = 0 := by
  have hle : degreeChains K d ≤ LinearMap.ker (augmentation K) := by
    rw [degreeChains, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    change augmentation K (Finsupp.single s 1) = 0
    rw [← simplex_of_mem K s.property, augmentation_simplex K s.property]
    simp [show s.val.card ≠ 1 by simpa only [Set.mem_ofPred_eq] using hs ▸ hd]
  exact hle hc

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MemSupportSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma mem_support_simplex (K : PreAbstractSimplicialComplex V) (s : Finset V)
    (t : {s : Finset V // s ∈ K}) :
    t ∈ (simplex K s).support ↔ t.val = s := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs, Finsupp.support_single _ one_ne_zero]
    simp only [Finset.mem_singleton, Subtype.ext_iff]
  · simp only [simplex, dite_eq_right hs, Finsupp.support_zero, Finset.notMem_empty, false_iff]
    intro he
    exact hs (he ▸ t.property)

omit [DecidableEq V] [DecidableEq W] in
lemma support_linearMap (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (c : Chain K)
    {t : {s : Finset W // s ∈ L}} (ht : t ∈ (T c).support) :
    ∃ s ∈ c.support, t ∈ (T (simplex K s.val)).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (T c) t = 0 := by
    conv_lhs => rw [chain_eq_sum K c]
    rw [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    rw [map_smul, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp (hn s hs), smul_zero]
  exact (Finsupp.mem_support_iff.mp ht) hh

lemma support_cone (K : PreAbstractSimplicialComplex V) (a : V) (c : Chain K)
    {t : {s : Finset V // s ∈ K}} (ht : t ∈ (cone K a c).support) :
    ∃ s ∈ c.support, a ∉ s.val ∧ t.val = insert a s.val := by
  obtain ⟨s, hs, ht⟩ := support_linearMap K K (cone K a) c ht
  rw [cone_simplex K a s.property] at ht
  split_ifs at ht with ha
  · simp at ht
  · exact ⟨s, hs, ha, (mem_support_simplex K _ t).mp ht⟩

lemma cone_degree (K : PreAbstractSimplicialComplex V) (a : V) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K (d+1)).comap (cone K a) := by
  intro c hc t ht
  obtain ⟨s, hs, ha, he⟩ := support_cone K a c ht
  change t.val.card = d+1
  rw [he, Finset.card_insert_of_notMem ha, hc hs]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SubdivSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma subdivSimplex_one (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    {s : Finset V} (hc : s.card = 1) : subdivSimplex L b s = simplex L {b s} := by
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  rw [subdivSimplex, dite_eq_left hn, ite_eq_left hc]

lemma subdivSimplex_many (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    {s : Finset V} (hn : s.Nonempty) (hc : s.card ≠ 1) :
    subdivSimplex L b s = cone L (b s) (∑ a ∈ s, subdivSimplex L b (s.erase a)) := by
  rw [subdivSimplex, dite_eq_left hn, ite_eq_right hc]
  exact congrArg (cone L (b s)) (Finset.sum_attach s (fun a : V => subdivSimplex L b (s.erase a)))

omit [DecidableEq V] [DecidableEq W] in
lemma vertexCarrier_mono (b : Finset V → W) {s t : Finset V} (hst : s ⊆ t) :
    vertexCarrier b s ⊆ vertexCarrier b t := by
  rintro w ⟨u, hu, hus, hb⟩
  exact ⟨u, hu, hus.trans hst, hb⟩

omit [DecidableEq V] [DecidableEq W] in
lemma center_mem_carrier (b : Finset V → W) {s : Finset V} (hs : s.Nonempty) :
    b s ∈ vertexCarrier b s := ⟨s, hs, Finset.Subset.refl _, rfl⟩

lemma support_sum_chains (L : PreAbstractSimplicialComplex W) {α : Type*}
    (s : Finset α) (c : α → Chain L) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (∑ a ∈ s, c a).support) : ∃ a ∈ s, t ∈ (c a).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (∑ a ∈ s, c a) t = 0 := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero (fun a ha => Finsupp.notMem_support_iff.mp (hn a ha))
  exact Finsupp.mem_support_iff.mp ht hh

lemma subdivSimplex_carrier (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (subdivSimplex L b s).support) : ↑t.val ⊆ vertexCarrier b s := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, mem_support_simplex] at ht
      rw [ht]
      exact Finset.singleton_subset_set_iff.mpr (center_mem_carrier b hn)
    · rw [subdivSimplex_many L b hn hc] at ht
      obtain ⟨u, hu, _, htu⟩ := support_cone L (b s) _ ht
      obtain ⟨a, ha, hua⟩ := support_sum_chains L s _ hu
      have hu' := ih (s.erase a) (Finset.erase_ssubset ha) hua
      rw [htu, Finset.coe_insert]
      exact Set.insert_subset (center_mem_carrier b hn)
        (hu'.trans (vertexCarrier_mono b (Finset.erase_subset a s)))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SimplexMemDegreeAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma simplex_mem_degree_all (K : PreAbstractSimplicialComplex V) (s : Finset V) :
    simplex K s ∈ degreeChains K s.card := by
  classical
  by_cases hs : s ∈ K
  · exact simplex_mem_degree K hs
  · simp only [simplex, dite_eq_right hs]
    exact Submodule.zero_mem _

lemma subdivSimplex_degree (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) : subdivSimplex L b s ∈ degreeChains L s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · rw [subdivSimplex_empty]
      exact Submodule.zero_mem _
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, hc]
      exact simplex_mem_degree_all L {b s}
    · rw [subdivSimplex_many L b hn hc]
      have hsum : (∑ a ∈ s, subdivSimplex L b (s.erase a)) ∈ degreeChains L (s.card-1) := by
        apply Submodule.sum_mem
        intro a ha
        have hh := ih (s.erase a) (Finset.erase_ssubset ha)
        simpa only [Finset.card_erase_of_mem ha] using hh
      have hpos := hn.card_pos
      simpa only [Submodule.mem_comap, Nat.sub_add_cancel hpos] using
        cone_degree L (b s) (s.card-1) hsum

omit [DecidableEq V] [DecidableEq W] in
lemma SubdivisionCarrier.center (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) : {b s} ∈ L :=
  hb s hs {b s} (Finset.singleton_nonempty _) (Finset.singleton_subset_set_iff.mpr
    (center_mem_carrier b (K.isRelLowerSet_faces hs).1))

lemma subdivSimplex_augmentation (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    augmentation L (subdivSimplex L b s) = augmentation K (simplex K s) := by
  rw [augmentation_simplex K hs]
  by_cases hc : s.card = 1
  · rw [subdivSimplex_one L b hc, augmentation_simplex L (hb.center K L b hs)]
    simp [hc]
  · rw [ite_eq_right hc]
    exact augmentation_eq_zero_of_degree L _ hc (subdivSimplex_degree L b s)

lemma subdivMap_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  simp [simplex_of_mem K hs, subdivMap, Finsupp.linearCombination_single]

lemma subdivMap_simplex_subset (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) : subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact subdivMap_simplex K L b ((K.isRelLowerSet_faces ht).2 hs hn)

lemma subdivMap_augmentation (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (augmentation L).comp (subdivMap K L b) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_augmentation K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]

lemma subdivMap_boundary_simplex (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (boundary K (simplex K s)) =
      ∑ a ∈ s, subdivSimplex L b (s.erase a) := by
  rw [boundary_simplex K hs, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact subdivMap_simplex_subset K L b hs (Finset.erase_subset a s)

lemma subdivSimplex_boundary (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    boundary L (subdivSimplex L b s) = subdivMap K L b (boundary K (simplex K s)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn := (K.isRelLowerSet_faces hs).1
    by_cases hc : s.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      rw [subdivSimplex_one L b hc, boundary_simplex L (hb.center K L b hs),
        boundary_simplex K hs]
      simp
    · have hd : boundary L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have he : boundary L (subdivMap K L b (boundary K (simplex K s))) =
            subdivMap K L b (boundary K (boundary K (simplex K s))) := by
          rw [boundary_simplex K hs]
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rcases (s.erase a).eq_empty_or_nonempty with heq | hne
          · simp [heq]
          · have hK : s.erase a ∈ K := (K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) hne
            rw [subdivMap_simplex K L b hK]
            exact ih (s.erase a) (Finset.erase_ssubset ha) hK
        rw [he, boundary_twice_simplex K hs, map_zero]
      have hε : augmentation L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have hh := LinearMap.congr_fun (subdivMap_augmentation K L b hb)
          (boundary K (simplex K s))
        rw [LinearMap.comp_apply, augmentation_boundary_simplex K hs] at hh
        exact hh
      have hcone : ∀ t ∈ (subdivMap K L b (boundary K (simplex K s))).support,
          insert (b s) t.val ∈ L := by
        rw [subdivMap_boundary_simplex K L b hs]
        intro t ht
        obtain ⟨a, ha, hta⟩ := support_sum_chains L s _ ht
        have ht' := (subdivSimplex_carrier L b _ hta).trans
          (vertexCarrier_mono b (Finset.erase_subset a s))
        apply hb s hs _ (Finset.insert_nonempty _ _)
        rw [Finset.coe_insert]
        exact Set.insert_subset (center_mem_carrier b hn) ht'
      rw [subdivSimplex_many L b hn hc, ← subdivMap_boundary_simplex K L b hs,
        cone_boundary L (b s) _ hcone, hd, hε, map_zero, zero_smul, add_zero, add_zero]

lemma subdivMap_boundary (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (boundary L).comp (subdivMap K L b) = (subdivMap K L b).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_boundary K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_SignedVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma cross_card (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) : s.card ≤ n := by
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hs.2.2).symm
    _ ≤ (Finset.range n).card := Finset.card_le_card (by
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv))
    _ = n := Finset.card_range n

lemma cross_singleton (n i : ℕ) (hi : i < n) (b : Bool) :
    ({(i,b)} : Finset SignedVertex) ∈ cross n := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · simpa using hi
  · simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (i,b)

lemma cross_insert (n i : ℕ) (hi : i < n) (s : Finset SignedVertex)
    (hs : s ∈ cross n) (hsi : ∀ v ∈ s, v.1 < i) (b : Bool) :
    insert (i,b) s ∈ cross n := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hi
    · exact hs.2.1 v hv
  · intro v hv w hw he
    rcases Finset.mem_insert.mp hv with rfl | hv <;>
      rcases Finset.mem_insert.mp hw with rfl | hw
    · rfl
    · exact False.elim ((ne_of_lt (hsi w hw)) he.symm)
    · exact False.elim ((ne_of_lt (hsi v hv)) he)
    · exact hs.2.2 hv hw he

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma support_mapChains_injective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (hf : Function.Injective f)
    (c : Chain K) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (mapChains K L f c).support) :
    ∃ s ∈ c.support, t.val = s.val.image f := by
  obtain ⟨s, hs, hst⟩ := support_linearMap K L (mapChains K L f) c ht
  rw [mapChains_simplex K L f s.property, mapSimplex,
    ite_eq_left (Finset.card_image_iff.mpr hf.injOn), mem_support_simplex] at hst
  exact ⟨s, hs, hst⟩

lemma normMap_sq (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e) :
    (normMap K e).comp (normMap K e) = 0 := by
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_sq _ (faceEquiv_involutive K e he hi)

lemma normMap_degree (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K d).comap (normMap K e) := by
  intro c hc
  exact (degreeChains K d).add_mem hc (mapChains_degree K K e he d hc)

lemma crossTower_support (n i : ℕ) {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (crossTower n i).support) : ∀ v ∈ s.val, v.1 ≤ i := by
  induction i generalizing s with
  | zero =>
    have he := (mem_support_simplex (cross n) {(0,false)} s).mp hs
    rw [he]
    intro v hv
    have he' := Finset.mem_singleton.mp hv
    exact he' ▸ Nat.le_refl 0
  | succ i ih =>
    obtain ⟨t, ht, _, he⟩ := support_cone (cross n) (i+1,false) _ hs
    rw [he]
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact le_rfl
    · have hu : t ∈ (crossTower n i).support ∪
          (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
        Finsupp.support_add ht
      rcases Finset.mem_union.mp hu with ht | ht
      · exact (ih ht v hv).trans (Nat.le_succ i)
      · obtain ⟨u, hu, he⟩ := support_mapChains_injective (cross n) (cross n) flip
          flip.injective _ ht
        rw [he] at hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact (ih hu w hw).trans (Nat.le_succ i)

lemma crossTower_degree (n i : ℕ) : crossTower n i ∈ degreeChains (cross n) (i+1) := by
  induction i with
  | zero => exact simplex_mem_degree_all (cross n) {(0,false)}
  | succ i ih =>
    exact cone_degree (cross n) (i+1,false) (i+1)
      (normMap_degree (cross n) flip (cross_flip_forward n) (i+1) ih)

lemma crossTower_cone_faces (n i : ℕ) (hi : i+1 < n)
    {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (normMap (cross n) flip (crossTower n i)).support) :
    insert (i+1,false) s.val ∈ cross n := by
  apply cross_insert n (i+1) hi s.val s.property
  intro v hv
  have hu : s ∈ (crossTower n i).support ∪
      (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
    Finsupp.support_add hs
  rcases Finset.mem_union.mp hu with hs | hs
  · exact Nat.lt_succ_of_le (crossTower_support n i hs v hv)
  · obtain ⟨t, ht, he⟩ := support_mapChains_injective (cross n) (cross n) flip
      flip.injective _ hs
    rw [he] at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.lt_succ_of_le (crossTower_support n i ht w hw)

lemma crossTower_norm_boundary (n i : ℕ) (hi : i < n) :
    boundary (cross n) (normMap (cross n) flip (crossTower n i)) = 0 := by
  induction i with
  | zero =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n 0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n) (simplex (cross n) {(0,false)})) = 0
    rw [boundary_simplex (cross n) (cross_singleton n 0 hi false)]
    simp
  | succ i ih =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n (i+1))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n)
      (cone (cross n) (i+1,false) (normMap (cross n) flip (crossTower n i)))) = 0
    rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
      ih (by omega)]
    have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n i)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
    rw [ha, map_zero, zero_smul, add_zero, add_zero]
    exact LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _

lemma crossTower_boundary (n i : ℕ) (hi : i+1 < n) :
    boundary (cross n) (crossTower n (i+1)) = normMap (cross n) flip (crossTower n i) := by
  change boundary (cross n) (cone (cross n) (i+1,false)
    (normMap (cross n) flip (crossTower n i))) = _
  rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
    crossTower_norm_boundary n i (by omega)]
  have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
    (crossTower n i)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
  rw [ha, map_zero, zero_smul, add_zero, add_zero]

lemma crossTower_augmentation (n : ℕ) (hn : 0 < n) :
    augmentation (cross n) (crossTower n 0) = 1 := by
  rw [crossTower, augmentation_simplex (cross n) (cross_singleton n 0 hn false)]
  simp

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CrossChainDimensionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains

lemma cross_chain_dimension_bound (n m : ℕ)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross m))
    (hd : (boundary (cross m)).comp T = T.comp (boundary (cross n)))
    (hN : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip))
    (ha : (augmentation (cross m)).comp T = augmentation (cross n))
    (hgrade : ∀ d, degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap T) :
    n ≤ m := by
  by_contra hnm
  have hmn : m < n := Nat.lt_of_not_ge hnm
  let c : ℕ → Chain (cross m) := fun i => T (crossTower n i)
  have hstep : ∀ i < m, boundary (cross m) (c (i+1)) =
      normMap (cross m) flip (c i) := by
    intro i hi
    change boundary (cross m) (T (crossTower n (i+1))) =
      normMap (cross m) flip (T (crossTower n i))
    rw [← LinearMap.comp_apply, hd, LinearMap.comp_apply,
      crossTower_boundary n i (by omega), ← LinearMap.comp_apply, ← hN,
      LinearMap.comp_apply]
  have htop : c m = 0 := by
    have hg := hgrade (m+1) (crossTower_degree n m)
    change c m ∈ degreeChains (cross m) (m+1) at hg
    rw [degreeChains_eq_bot_of_card_bound (cross m) (m+1)
      (fun s hs => Nat.lt_succ_of_le (cross_card m s hs)), Submodule.mem_bot] at hg
    exact hg
  have hh := antipodal_tower_augmentation_zero (cross m) flip (cross_flip m)
    flip_involutive (cross_free m) m c hstep (by rw [htop, map_zero])
  change augmentation (cross m) (T (crossTower n 0)) = 0 at hh
  rw [← LinearMap.comp_apply, ha, crossTower_augmentation n (by omega)] at hh
  exact one_ne_zero hh

end BorsukNine.SimplicialChains

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma barycenter_eq_centerMass (s : Finset E) :
    barycenter s = s.centerMass (fun _ => (1 : ℝ)) id := by
  simp [barycenter, Finset.centerMass]

lemma barycenter_mem_convex {A : Set E} (hA : Convex ℝ A) {s : Finset E}
    (hs : s.Nonempty) (hsA : (s : Set E) ⊆ A) : barycenter s ∈ A := by
  rw [barycenter_eq_centerMass]
  apply hA.centerMass_mem
  · intro x hx; exact zero_le_one
  · simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card)
  · intro x hx; exact hsA hx

lemma barycenter_norm_le {s : Finset E} (hs : s.Nonempty) {D : ℝ}
    (hD : ∀ x ∈ s, ‖x‖ ≤ D) : ‖barycenter s‖ ≤ D := by
  have h := barycenter_mem_convex (convex_closedBall (0 : E) D) hs (A := Metric.closedBall 0 D)
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hD x hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

lemma barycenter_inner {s : Finset E} (hs : s.Nonempty) (w : E)
    (hw : ∀ x ∈ s, ⟪w,x⟫ = 1) : ⟪w,barycenter s⟫ = 1 := by
  rw [barycenter, real_inner_smul_right, inner_sum]
  simp only [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero)

lemma barycenter_sub_eq {s : Finset E} (hs : s.Nonempty) (x : E) :
    barycenter s - x = (s.card : ℝ)⁻¹ • ∑ y ∈ s, (y-x) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero), one_smul]
  rfl

lemma barycenter_dist_vertex [DecidableEq E] {s : Finset E} {x : E} (hx : x ∈ s)
    {D : ℝ} (hD : ∀ y ∈ s, ∀ z ∈ s, dist y z ≤ D) :
    dist (barycenter s) x ≤ ((s.card : ℝ)-1) / s.card * D := by
  have hs : s.Nonempty := ⟨x,hx⟩
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [dist_eq_norm, barycenter_sub_eq hs x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  have hh : (∑ y ∈ s, (y-x)) = ∑ y ∈ s.erase x, (y-x) := by
    rw [← Finset.sum_erase_add _ _ hx]
    simp
  rw [hh]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ y ∈ s.erase x, (y-x)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, ‖y-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt hc))
    _ ≤ (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, D := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hc))
      apply Finset.sum_le_sum
      intro y hy
      simpa only [dist_eq_norm] using hD y (Finset.mem_of_mem_erase hy) x hx
    _ = ((s.card : ℝ)-1) / s.card * D := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hx,
        Nat.cast_sub hs.card_pos, Nat.cast_one]
      ring

lemma barycenter_dist_carrier [DecidableEq E] {s t : Finset E} (ht : t.Nonempty)
    (hts : t ⊆ s) {D : ℝ} (hD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D) :
    dist (barycenter s) (barycenter t) ≤ ((s.card : ℝ)-1) / s.card * D := by
  have h := barycenter_mem_convex
    (convex_closedBall (barycenter s) (((s.card : ℝ)-1) / s.card * D)) ht
    (fun x hx => (Metric.mem_closedBall').mpr (barycenter_dist_vertex (hts hx) hD))
  exact (Metric.mem_closedBall').mp h

lemma barycenter_mesh_factor {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    ((a : ℝ)-1) / a ≤ ((n : ℝ)-1) / n := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le ha han
  apply (div_le_div_iff₀ ha' hn').mpr
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  nlinarith

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_BarycenterNeg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]

lemma barycenter_neg (s : Finset E) : barycenter (s.image Neg.neg) = -barycenter s := by
  rw [barycenter, Finset.card_image_iff.mpr neg_injective.injOn,
    Finset.sum_image neg_injective.injOn, Finset.sum_neg_distrib,
    smul_neg, barycenter]

lemma hemisphere_neg (R : ℝ) (s : Finset E) :
    s ∈ hemisphereComplex R ↔ s.image Neg.neg ∈ hemisphereComplex R := by
  constructor
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨hn.image _, -w, by simpa using hw, ?_⟩
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa using hh y hy
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨Finset.image_nonempty.mp hn, -w, by simpa using hw, ?_⟩
    intro x hx
    have h := hh (-x) (Finset.mem_image_of_mem Neg.neg hx)
    simpa using h

omit [DecidableEq E] in
lemma hemisphere_subdivision_carrier (R : ℝ) :
    SubdivisionCarrier (hemisphereComplex R : PreAbstractSimplicialComplex E)
      (hemisphereComplex R) barycenter := by
  rintro s ⟨hn,w,hw,hh⟩ t ht hts
  refine ⟨ht,w,hw,?_⟩
  intro x hx
  obtain ⟨u,hu,hus,rfl⟩ := hts hx
  exact ⟨barycenter_norm_le hu (fun y hy => (hh y (hus hy)).1),
    barycenter_inner hu w (fun y hy => (hh y (hus hy)).2)⟩

lemma subdivSimplex_mesh (R : ℝ) (s : Finset E) (n : ℕ) (hsn : s.card ≤ n)
    (D : ℝ) (hD : 0 ≤ D) (hsD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (subdivSimplex (hemisphereComplex R) barycenter s).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ ((n : ℝ)-1) / n * D := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    have hfac : 0 ≤ ((n : ℝ)-1) / n := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hn.card_pos hsn
      exact div_nonneg (by linarith) (by positivity)
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one _ _ hc, mem_support_simplex] at ht
      intro x hx y hy
      rw [ht, Finset.mem_singleton] at hx hy
      subst x; subst y
      simpa only [dist_self] using mul_nonneg hfac hD
    · rw [subdivSimplex_many _ _ hn hc] at ht
      obtain ⟨u,hu,_,htu⟩ := support_cone _ (barycenter s) _ ht
      obtain ⟨a,ha,hua⟩ := support_sum_chains _ s _ hu
      have hsmall := ih (s.erase a) (Finset.erase_ssubset ha)
        (le_trans (Finset.card_le_card (Finset.erase_subset a s)) hsn)
        (fun x hx y hy => hsD x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)) hua
      have hcarrier := (subdivSimplex_carrier _ barycenter _ hua).trans
        (vertexCarrier_mono barycenter (Finset.erase_subset a s))
      have hcenter (x : E) (hx : x ∈ u.val) :
          dist (barycenter s) x ≤ ((n : ℝ)-1) / n * D := by
        obtain ⟨v,hv,hvs,rfl⟩ := hcarrier hx
        exact (barycenter_dist_carrier hv hvs hsD).trans
          (mul_le_mul_of_nonneg_right (barycenter_mesh_factor hn.card_pos hsn) hD)
      intro x hx y hy
      rw [htu, Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · simpa only [dist_self] using mul_nonneg hfac hD
      · exact hcenter y hy
      · rw [dist_comm]; exact hcenter x hx
      · exact hsmall x hx y hy

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MapChainsEquivSimplexAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W U : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq U]

omit [DecidableEq W] [DecidableEq U] in
lemma mapChains_equiv_simplex_all (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (s : Finset V) :
    mapChains K K e (simplex K s) = simplex K (s.image e) := by
  classical
  by_cases hs : s ∈ K
  · rw [mapChains_simplex K K e hs, mapSimplex,
      ite_eq_left (Finset.card_image_iff.mpr e.injective.injOn)]
  · have ht : s.image e ∉ K := (he s).not.mp hs
    simp [simplex, hs, ht]

omit [DecidableEq W] [DecidableEq U] in
lemma cone_equivariant (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (a : V) :
    (mapChains K K e).comp (cone K a) = (cone K (e a)).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hm := mapChains_equiv_simplex_all K e he s.val
  have hc := cone_simplex K a s.property
  have hsc := cone_simplex K (e a) ((he s.val).mp s.property)
  have hh : mapChains K K e (cone K a (simplex K s.val)) =
      cone K (e a) (mapChains K K e (simplex K s.val)) := by
    rw [hc, hm, hsc]
    by_cases ha : a ∈ s.val
    · rw [ite_eq_left ha, ite_eq_left (Finset.mem_image_of_mem e ha), map_zero]
    · have hna : e a ∉ s.val.image e := by
        intro h
        obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h
        exact ha (e.injective heq ▸ hb)
      rw [ite_eq_right ha, ite_eq_right hna, mapChains_equiv_simplex_all K e he,
        Finset.image_insert]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

omit [DecidableEq U] in
lemma subdivSimplex_equivariant (L : PreAbstractSimplicialComplex W)
    (e : V ≃ V) (d : W ≃ W) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) (s : Finset V) :
    mapChains L L d (subdivSimplex L b s) = subdivSimplex L b (s.image e) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp
    have hc : (s.image e).card = s.card := Finset.card_image_iff.mpr e.injective.injOn
    by_cases hs : s.card = 1
    · rw [subdivSimplex_one L b hs, subdivSimplex_one L b (hc.trans hs),
        mapChains_equiv_simplex_all L d hd, Finset.image_singleton, hb]
    · rw [subdivSimplex_many L b hn hs,
        subdivSimplex_many L b (hn.image e) (by omega)]
      have hcone := LinearMap.congr_fun (cone_equivariant L d hd (b s))
        (∑ a ∈ s, subdivSimplex L b (s.erase a))
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcone
      rw [hcone, map_sum, hb, Finset.sum_image (fun a _ b _ he => e.injective he)]
      apply congrArg (cone L (d (b s)))
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih (s.erase a) (Finset.erase_ssubset ha), image_erase_of_injOn e s e.injective.injOn ha]

omit [DecidableEq U] in
lemma subdivMap_equivariant (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (mapChains L L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hh : mapChains L L d (subdivMap K L b (simplex K s.val)) =
      subdivMap K L b (mapChains K K e (simplex K s.val)) := by
    rw [subdivMap_simplex K L b s.property, subdivSimplex_equivariant L e d hd b hb,
      mapChains_equiv_simplex_all K e he, subdivMap_simplex K L b ((he s.val).mp s.property)]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

omit [DecidableEq U] in
lemma subdivMap_norm (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (normMap L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, subdivMap_equivariant K L e d he hd b hb]

omit [DecidableEq U] in
lemma subdivMap_degree (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (b : Finset V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (subdivMap K L b) := by
  apply grade_map K L _ d d
  intro s hs hsd
  rw [subdivMap_simplex K L b hs, ← hsd]
  exact subdivSimplex_degree L b s

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_LinearMapSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma linearMap_eq_of_support {K : PreAbstractSimplicialComplex V}
    {M : Type*} [AddCommMonoid M] [Module F₂ M]
    (T U : Chain K →ₗ[F₂] M) (c : Chain K)
    (hc : ∀ s ∈ c.support, T (simplex K s.val) = U (simplex K s.val)) : T c = U c := by
  rw [chain_eq_sum K c, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, map_smul, hc s hs]

lemma mapChains_boundary_simplex_of_image (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hinj), boundary_simplex L ht]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, ite_eq_left (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, ite_eq_right (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]

lemma mapChains_boundary_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    boundary L (mapChains K L f c) = mapChains K L f (boundary K c) := by
  apply linearMap_eq_of_support ((boundary L).comp (mapChains K L f))
    ((mapChains K L f).comp (boundary K)) c
  intro s hs
  exact mapChains_boundary_simplex_of_image K L f s.property (hc s hs)

omit [DecidableEq V] in
lemma mapChains_augmentation_simplex_of_image (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, ite_eq_left hcard, augmentation_simplex L ht, hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]

omit [DecidableEq V] in
lemma mapChains_augmentation_of_support (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    augmentation L (mapChains K L f c) = augmentation K c := by
  apply linearMap_eq_of_support ((augmentation L).comp (mapChains K L f)) (augmentation K) c
  intro s hs
  exact mapChains_augmentation_simplex_of_image K L f s.property (hc s hs)

omit [DecidableEq V] in
lemma mapChains_degree_all (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _

lemma mapChains_equivariant (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (mapChains L L d).comp (mapChains K L f) =
      (mapChains K L f).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have him : (s.val.image e).image f = (s.val.image f).image d := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun x hx => hf s.val s.property x hx)
  have hcard : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  have hcard' : ((s.val.image f).image d).card = (s.val.image f).card :=
    Finset.card_image_iff.mpr d.injective.injOn
  have hh : mapChains L L d (mapChains K L f (simplex K s.val)) =
      mapChains K L f (mapChains K K e (simplex K s.val)) := by
    rw [mapChains_simplex K L f s.property, mapChains_equiv_simplex_all K e he,
      mapChains_simplex K L f ((he s.val).mp s.property)]
    simp only [mapSimplex, him, hcard, hcard']
    split_ifs
    · exact mapChains_equiv_simplex_all L d hd _
    · exact map_zero _
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]

lemma mapChains_norm (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (normMap L d).comp (mapChains K L f) =
      (mapChains K L f).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, mapChains_equivariant K L e d he hd f hf]

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_CrossEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma crossEmbedding_norm (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ‖crossEmbedding n v‖ = 1 := by
  simp only [crossEmbedding, dite_eq_left hv, norm_smul, PiLp.norm_single]
  cases v.2 <;> norm_num

lemma crossEmbedding_flip (n : ℕ) (v : SignedVertex) :
    crossEmbedding n (flip v) = -crossEmbedding n v := by
  rcases v with ⟨i,b⟩
  cases b <;> simp only [crossEmbedding, flip_apply] <;> split_ifs <;> simp_all

lemma crossEmbedding_inner_ne (n : ℕ) {v w : SignedVertex}
    (hvw : v.1 ≠ w.1) : ⟪crossEmbedding n v, crossEmbedding n w⟫ = 0 := by
  unfold crossEmbedding
  split_ifs <;> simp_all [EuclideanSpace.inner_single_left]

lemma crossEmbedding_inner_self (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ⟪crossEmbedding n v, crossEmbedding n v⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, crossEmbedding_norm n v hv]
  norm_num

lemma crossEmbedding_face (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image (crossEmbedding n) ∈ hemisphereComplex (n:ℝ) := by
  refine ⟨hs.1.image _, ∑ v ∈ s, crossEmbedding n v, ?_, ?_⟩
  · calc
      ‖∑ v ∈ s, crossEmbedding n v‖ ≤ ∑ v ∈ s, ‖crossEmbedding n v‖ := norm_sum_le _ _
      _ = s.card := by simp only [Finset.sum_congr rfl (fun v hv => crossEmbedding_norm n v (hs.2.1 v hv)), Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (n:ℝ) := by exact_mod_cast cross_card n s hs
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨le_of_eq (crossEmbedding_norm n v (hs.2.1 v hv)), ?_⟩
    rw [sum_inner, Finset.sum_eq_single v]
    · exact crossEmbedding_inner_self n v (hs.2.1 v hv)
    · intro w hw hwv
      exact crossEmbedding_inner_ne n (fun he => hwv (hs.2.2 hw hv he))
    · exact fun hn => False.elim (hn hv)

lemma crossGeometricMap_boundary (n : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (boundary (cross n)) :=
  mapChains_boundary _ _ _ (crossEmbedding_face n)

lemma crossGeometricMap_augmentation (n : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      augmentation (cross n) := mapChains_augmentation _ _ _ (crossEmbedding_face n)

lemma crossGeometricMap_degree (n d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (crossGeometricMap n) := mapChains_degree _ _ _ (crossEmbedding_face n) d

lemma crossGeometricMap_norm (n : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (normMap (cross n) flip) := by
  apply mapChains_norm _ _ flip (Equiv.neg _) (cross_flip n) (hemisphere_neg (n:ℝ))
  intro s hs x hx
  exact crossEmbedding_flip n x

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_MaxIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset

lemma maxIndex_le {m : ℕ} [NeZero m] (g : Fin m → ℝ) (i : Fin m) :
    g i ≤ g (maxIndex g) :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose_spec.2 i (Finset.mem_univ _)

lemma peakIndex_neg {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) :
    peakIndex (-y) = peakIndex y := by
  unfold peakIndex
  congr 1
  ext i
  simp

lemma euclidean_norm_le_sum_abs {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ‖y‖ ≤ ∑ i, |y i| := by
  have hy : y = ∑ i, EuclideanSpace.single i (y i) := by
    ext i
    simp
  calc
    ‖y‖ = ‖∑ i, EuclideanSpace.single i (y i)‖ := congrArg norm hy
    _ ≤ ∑ i, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
    _ = ∑ i, |y i| := by simp

lemma peak_large {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    (1:ℝ) / m ≤ |y (peakIndex y)| := by
  have h := euclidean_norm_le_sum_abs y
  rw [hy] at h
  have hsum : ∑ i : Fin m, |y i| ≤ (m:ℝ) * |y (peakIndex y)| := by
    calc
      ∑ i : Fin m, |y i| ≤ ∑ _ : Fin m, |y (peakIndex y)| :=
        Finset.sum_le_sum (fun i _ => maxIndex_le (fun j => |y j|) i)
      _ = _ := by simp
  exact (div_le_iff₀ (by exact_mod_cast NeZero.pos m)).mpr (by nlinarith)

lemma sphereLabel_bound {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) :
    (sphereLabel y).1 < m := (peakIndex y).isLt

lemma sphereLabel_neg {m : ℕ} [NeZero m] (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) :
    sphereLabel (-y) = flip (sphereLabel y) := by
  have hpeak : y (peakIndex y) ≠ 0 := by
    have h := peak_large y hy
    have hm : (0:ℝ) < (1:ℝ)/m := div_pos zero_lt_one (by exact_mod_cast NeZero.pos m)
    intro he
    rw [he, abs_zero] at h
    linarith
  apply Prod.ext
  · simp only [sphereLabel, peakIndex_neg, flip_apply]
  · simp only [sphereLabel, peakIndex_neg, flip_apply, PiLp.neg_apply]
    by_cases h : y (peakIndex y) < 0
    · have h' : ¬ -y (peakIndex y) < 0 := by linarith
      simp [h,h']
    · have h' : -y (peakIndex y) < 0 := by rcases lt_or_gt_of_ne hpeak with hn | hp <;> linarith
      simp [h,h']

lemma sphereLabel_compatible {m : ℕ} [NeZero m]
    (y z : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hd : dist y z < (1:ℝ)/m) (hi : (sphereLabel y).1 = (sphereLabel z).1) :
    sphereLabel y = sphereLabel z := by
  have he : peakIndex y = peakIndex z := Fin.ext hi
  have hcoord : |y (peakIndex y) - z (peakIndex y)| ≤ dist y z := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le y z (peakIndex y)
  have hym := peak_large y hy
  have hzm := peak_large z hz
  rw [← he] at hzm
  apply Prod.ext hi
  change decide (y (peakIndex y) < 0) = decide (z (peakIndex z) < 0)
  rw [← he]
  congr 1
  apply propext
  constructor
  · intro hyneg
    by_contra hzneg
    have hzpos := le_of_not_gt hzneg
    rw [abs_of_neg hyneg] at hym
    rw [abs_of_nonpos (by linarith)] at hcoord
    linarith
  · intro hzneg
    by_contra hyneg
    have hypos := le_of_not_gt hyneg
    rw [abs_of_neg hzneg] at hzm
    rw [abs_of_nonneg (by linarith)] at hcoord
    linarith

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]

lemma refinement_boundary (R : ℝ) (r : ℕ) :
    (boundary (hemisphereComplex R : PreAbstractSimplicialComplex E)).comp (refinement R r) =
      (refinement R r).comp (boundary (hemisphereComplex R)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc, subdivMap_boundary _ _ _ (hemisphere_subdivision_carrier R),
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

lemma refinement_augmentation (R : ℝ) (r : ℕ) :
    (augmentation (hemisphereComplex R : PreAbstractSimplicialComplex E)).comp
      (refinement R r) = augmentation (hemisphereComplex R) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_augmentation _ _ _ (hemisphere_subdivision_carrier R), ih]

lemma refinement_norm (R : ℝ) (r : ℕ) :
    (normMap (hemisphereComplex R : PreAbstractSimplicialComplex E) (Equiv.neg E)).comp
      (refinement R r) = (refinement R r).comp (normMap (hemisphereComplex R) (Equiv.neg E)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_norm _ _ (Equiv.neg E) (Equiv.neg E) (hemisphere_neg R) (hemisphere_neg R)
        barycenter (barycenter_neg), LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

lemma refinement_degree (R : ℝ) (r d : ℕ) :
    degreeChains (hemisphereComplex R : PreAbstractSimplicialComplex E) d ≤
      (degreeChains (hemisphereComplex R) d).comap (refinement R r) := by
  induction r with
  | zero => intro c hc; exact hc
  | succ r ih =>
    intro c hc
    change subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c) ∈ degreeChains (hemisphereComplex R) d
    exact subdivMap_degree (hemisphereComplex R : PreAbstractSimplicialComplex E)
      (hemisphereComplex R) barycenter d (ih hc)

lemma refinement_mesh (R : ℝ) (r n : ℕ) {c : Chain (hemisphereComplex R : PreAbstractSimplicialComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) n) {D : ℝ} (hD : 0 ≤ D)
    (hmesh : ∀ s ∈ c.support, ∀ x ∈ s.val, ∀ y ∈ s.val, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * D := by
  induction r generalizing t with
  | zero => simpa only [refinement, LinearMap.id_apply, pow_zero, one_mul] using hmesh t ht
  | succ r ih =>
    change t ∈ (subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c)).support at ht
    obtain ⟨s,hs,hts⟩ := support_linearMap _ _ _ _ ht
    rw [subdivMap_simplex _ _ _ s.property] at hts
    have hdeg := refinement_degree R r n hc hs
    change s.val.card = n at hdeg
    have hn : 0 < n := hdeg ▸ s.property.1.card_pos
    have hfac : 0 ≤ ((n:ℝ)-1)/n := by
      have hh : (1:ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg (by linarith) (by positivity)
    have hh := subdivSimplex_mesh R s.val n (le_of_eq hdeg)
      ((((n:ℝ)-1)/n)^r * D) (mul_nonneg (pow_nonneg hfac _) hD) (ih hs) hts
    simpa only [pow_succ', mul_assoc] using hh

omit [DecidableEq E] in
lemma hemisphere_mesh_two (R : ℝ) {s : Finset E} (hs : s ∈ hemisphereComplex R)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ 2 := by
  obtain ⟨_, _, _, unit_norm⟩ := hs
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 2 := by linarith [(unit_norm x hx).1, (unit_norm y hy).1]

lemma refinement_mesh_uniform (R : ℝ) (r n d : ℕ) (hd : d ≤ n)
    {c : Chain (hemisphereComplex R : PreAbstractSimplicialComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) d)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  have hdeg := refinement_degree R r d hc ht
  have htpos := t.property.1.card_pos
  change t.val.card = d at hdeg
  have hdpos : 0 < d := hdeg ▸ htpos
  have hfac : 0 ≤ ((d:ℝ)-1)/d := by
    have hh : (1:ℝ) ≤ d := by exact_mod_cast hdpos
    exact div_nonneg (by linarith) (by positivity)
  have hm := refinement_mesh R r d hc (D := 2) (by norm_num)
    (fun simplex _ _ first_mem _ second_mem =>
      hemisphere_mesh_two R simplex.property first_mem second_mem) ht
  intro x hx y hy
  exact (hm x hx y hy).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hfac (barycenter_mesh_factor hdpos hd) r) (by norm_num))

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_FineCrossMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma fineCrossMap_boundary (n r : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (boundary (cross n)) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_boundary,
    LinearMap.comp_assoc, crossGeometricMap_boundary, ← LinearMap.comp_assoc]

lemma fineCrossMap_augmentation (n r : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) = augmentation (cross n) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_augmentation,
    crossGeometricMap_augmentation]

lemma fineCrossMap_norm (n r : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (normMap (cross n) flip) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_norm,
    LinearMap.comp_assoc, crossGeometricMap_norm, ← LinearMap.comp_assoc]

lemma fineCrossMap_degree (n r d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (fineCrossMap n r) := by
  intro c hc
  change refinement (n:ℝ) r (crossGeometricMap n c) ∈ degreeChains (hemisphereComplex (n:ℝ)) d
  exact refinement_degree (E := EuclideanSpace ℝ (Fin n)) (n:ℝ) r d
    (crossGeometricMap_degree n d hc)

lemma fineCrossMap_simplex_mesh (n r : ℕ) {s : Finset SignedVertex} (hs : s ∈ cross n)
    {t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  apply refinement_mesh_uniform (n:ℝ) r n s.card (cross_card n s hs)
    (crossGeometricMap_degree n s.card (simplex_mem_degree _ hs)) ht

lemma annulus_compact (n : ℕ) : IsCompact (annulus n) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2

lemma hemisphere_vertex_annulus (n : ℕ) (hn : 0 < n)
    {s : Finset (EuclideanSpace ℝ (Fin n))} (hs : s ∈ hemisphereComplex (n:ℝ))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) : x ∈ annulus n := by
  obtain ⟨_,w,hw,hh⟩ := hs
  refine ⟨?_,(hh x hx).1⟩
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  have h := real_inner_le_norm w x
  rw [(hh x hx).2] at h
  calc
    1 ≤ ‖w‖ * ‖x‖ := h
    _ ≤ (n:ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg x)
    _ = ‖x‖ * (n:ℝ) := mul_comm _ _

lemma annular_odd_dimension_bound (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) : n ≤ m := by
  classical
  let : NeZero m := ⟨by omega⟩
  have hunif := (annulus_compact n).uniformContinuousOn_of_continuous hg
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hunif ((1:ℝ)/m)
    (div_pos zero_lt_one (by exact_mod_cast hm))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  have hmeshδ : (((n:ℝ)-1)/n)^r * 2 < δ := by linarith
  let K : PreAbstractSimplicialComplex (EuclideanSpace ℝ (Fin n)) := hemisphereComplex (n:ℝ)
  let f : EuclideanSpace ℝ (Fin n) → SignedVertex := fun x => sphereLabel (g x)
  let U : Chain K →ₗ[F₂] Chain (cross m) := mapChains K (cross m) f
  let T : Chain (cross n) →ₗ[F₂] Chain (cross m) := U.comp (fineCrossMap n r)
  have hfine (s : Finset SignedVertex) (hs : s ∈ cross n)
      (t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ K})
      (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) : t.val.image f ∈ cross m := by
    refine ⟨t.property.1.image _, ?_, ?_⟩
    · intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact sphereLabel_bound (g x)
    · intro v hv w hw he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      have hxa := hemisphere_vertex_annulus n hn t.property hx
      have hya := hemisphere_vertex_annulus n hn t.property hy
      apply sphereLabel_compatible (g x) (g y) (hgn x hxa) (hgn y hya) _ he
      exact hclose x hxa y hya ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hmeshδ)
  have hdb : (boundary (cross m)).comp T = T.comp (boundary (cross n)) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : boundary (cross m) (T (simplex (cross n) s.val)) =
        T (boundary (cross n) (simplex (cross n) s.val)) := by
      change boundary (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_boundary_of_support K (cross m) f _ (hfine s.val s.property)]
      have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
      rw [hb]
      rfl
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have haug : (augmentation (cross m)).comp T = augmentation (cross n) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : augmentation (cross m) (T (simplex (cross n) s.val)) =
        augmentation (cross n) (simplex (cross n) s.val) := by
      change augmentation (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_augmentation_of_support K (cross m) f _ (hfine s.val s.property)]
      exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have hnorm : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip) := by
    have hu : (normMap (cross m) flip).comp U = U.comp (normMap K (Equiv.neg _)) := by
      apply mapChains_norm K (cross m) (Equiv.neg _) flip
        (hemisphere_neg (n:ℝ)) (cross_flip m) f
      intro s hs x hx
      have hxa := hemisphere_vertex_annulus n hn hs hx
      change sphereLabel (g (-x)) = flip (sphereLabel (g x))
      rw [hgo x hxa, sphereLabel_neg _ (hgn x hxa)]
    change (normMap (cross m) flip).comp (U.comp (fineCrossMap n r)) =
      (U.comp (fineCrossMap n r)).comp (normMap (cross n) flip)
    rw [← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
      fineCrossMap_norm, ← LinearMap.comp_assoc]
  apply cross_chain_dimension_bound n m T hdb hnorm haug
  intro d c hc
  change mapChains K (cross m) f (fineCrossMap n r c) ∈ degreeChains (cross m) d
  exact mapChains_degree_all K (cross m) f d (fineCrossMap_degree n r d hc)

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_UnitRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

lemma unitRadial_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : ‖unitRadial x‖ = 1 := by
  rw [unitRadial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma unitRadial_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    unitRadial (-x) = -unitRadial x := by simp [unitRadial]

lemma unitRadial_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : ∀ x ∈ S, x ≠ 0) : ContinuousOn unitRadial S := by
  exact (continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr (hS x hx))).smul
    continuous_id.continuousOn

lemma odd_sphere_dimension_bound (n m : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : n ≤ m := by
  by_cases hm : 0 < m
  · have ha : ∀ x ∈ annulus n, x ≠ 0 := by
      intro x hx hzero
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      have hp : (0:ℝ) < 1/(n:ℝ) := div_pos zero_lt_one hn'
      simp only [annulus, Set.mem_ofPred_eq, hzero, norm_zero] at hx
      linarith [hx.1]
    apply annular_odd_dimension_bound n m hn hm (fun x => f (unitRadial x))
    · exact hf.comp (unitRadial_continuousOn ha) (fun x hx => unitRadial_norm (ha x hx))
    · intro x hx
      exact hfn _ (unitRadial_norm (ha x hx))
    · intro x hx
      rw [unitRadial_neg, hfo _ (unitRadial_norm (ha x hx))]
  · have hm0 : m = 0 := by omega
    subst m
    let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0,hn⟩ 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hzero : f x = 0 := Subsingleton.elim _ _
    have hh := hfn x hx
    rw [hzero, norm_zero] at hh
    exact False.elim (zero_ne_one hh)

lemma dropLast_zero_iff (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    dropLast n x = 0 ↔ x = x (Fin.last n) • EuclideanSpace.single (Fin.last n) 1 := by
  constructor
  · intro hx
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · have hj := congrArg (fun y : EuclideanSpace ℝ (Fin n) => y j) hx
      simpa [dropLast] using hj
  · intro hx
    rw [hx]
    ext i
    simp [dropLast]

lemma dropLast_nonzero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖ = 1)
    (hxp : x ≠ EuclideanSpace.single (Fin.last n) 1)
    (hxm : x ≠ -EuclideanSpace.single (Fin.last n) 1) : dropLast n x ≠ 0 := by
  intro hz
  have he := (dropLast_zero_iff n x).mp hz
  have ha : |x (Fin.last n)| = 1 := by
    conv_rhs => rw [← hx, he]
    simp [norm_smul]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp ha with hp | hm
  · apply hxp
    simpa [hp] using he
  · apply hxm
    simpa [hm] using he

lemma odd_sphere_surjective (n : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ f x = y := by
  intro y hy
  by_contra hmiss
  push Not at hmiss
  let e : EuclideanSpace ℝ (Fin (n+1)) := EuclideanSpace.single (Fin.last n) 1
  have he : ‖e‖ = 1 := by simp [e]
  let R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
    Submodule.reflection (ℝ ∙ (y-e))ᗮ
  have hRy : R y = e := Submodule.reflection_sub (hy.trans he.symm)
  have hnzero (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖ = 1) :
      dropLast n (R (f x)) ≠ 0 := by
    apply dropLast_nonzero n (R (f x)) (by rw [R.norm_map, hfn x hx])
    · intro hp
      exact hmiss x hx (R.injective (hp.trans hRy.symm))
    · intro hm
      have hneg : R (f (-x)) = e := by rw [hfo x hx, map_neg, hm, neg_neg]
      exact hmiss (-x) (by simpa using hx) (R.injective (hneg.trans hRy.symm))
  let g : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin n) :=
    fun x => unitRadial (dropLast n (R (f x)))
  have hicont : ContinuousOn (fun x => dropLast n (R (f x))) {x | ‖x‖ = 1} :=
    (dropLast n).continuous_of_finiteDimensional.comp_continuousOn (R.continuous.comp_continuousOn hf)
  have hgc : ContinuousOn g {x | ‖x‖ = 1} := by
    apply (unitRadial_continuousOn (S := {z : EuclideanSpace ℝ (Fin n) | z ≠ 0})
      (fun _ h => h)).comp hicont
    exact fun x hx => hnzero x hx
  have hgn (x) (hx : ‖x‖ = 1) : ‖g x‖ = 1 := unitRadial_norm (hnzero x hx)
  have hgo (x) (hx : ‖x‖ = 1) : g (-x) = -g x := by
    dsimp [g]
    rw [hfo x hx, map_neg, map_neg, unitRadial_neg]
  have hd := odd_sphere_dimension_bound (n+1) n (by omega) g hgc hgn hgo
  omega

end BorsukNine.SimplicialChains

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Simplicial_OddSphereDimensionBoundFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine.SimplicialChains

lemma odd_sphere_dimension_bound_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (f : EuclideanSpace ℝ α → EuclideanSpace ℝ β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : Fintype.card α ≤ Fintype.card β := by
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin α)
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin β)
  apply odd_sphere_dimension_bound (Fintype.card α) (Fintype.card β)
    Fintype.card_pos (fun x => B (f (A.symm x)))
  · exact B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx))
  · intro x hx
    rw [B.norm_map, hfn _ (by simpa using hx)]
  · intro x hx
    rw [map_neg, hfo _ (by simpa using hx), map_neg]

lemma odd_sphere_surjective_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (hc : Fintype.card α = Fintype.card β)
    (f : EuclideanSpace ℝ α → EuclideanSpace ℝ β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ f x = y := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := α)))
  let ea : α ≃ Fin (n+1) := (Fintype.equivFin α).trans (finCongr hn)
  let eb : β ≃ Fin (n+1) := (Fintype.equivFin β).trans (finCongr (hc.symm.trans hn))
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eb
  have hg := odd_sphere_surjective n (fun x => B (f (A.symm x)))
    (B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx)))
    (fun x hx => by rw [B.norm_map, hfn _ (by simpa using hx)])
    (fun x hx => by rw [map_neg, hfo _ (by simpa using hx), map_neg])
  intro y hy
  obtain ⟨x,hx,he⟩ := hg (B y) (by simpa using hy)
  exact ⟨A.symm x, by simpa using hx, B.injective he⟩

end BorsukNine.SimplicialChains

namespace BorsukNine
open scoped RealInnerProductSpace

section LabelBound
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]

lemma Admissible.label_bound {f : EuclideanSpace ℝ ν → ι → ℝ} (hf : Admissible f) :
    Fintype.card (UpperTriangle ν) ≤ Fintype.card ι := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_dimension_bound_fintype (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)

lemma Admissible.sphereExtension_surjective {f : EuclideanSpace ℝ ν → ι → ℝ}
    (hf : Admissible f) (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ sphereExtension f x = y := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_surjective_fintype hc (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)

lemma Admissible.signedExtension_ray {f : EuclideanSpace ℝ ν → ι → ℝ}
    (hf : Admissible f) (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι)
    {y : ι → ℝ} (hy : y ≠ 0) :
    ∃ A : Matrix ν ν ℝ, IsSelfAdjoint A ∧ ∃ t : ℝ, 0 < t ∧ signedExtension f A = t • y := by
  let Y : EuclideanSpace ℝ ι := WithLp.toLp 2 y
  have hY : Y ≠ 0 := fun hh => hy (WithLp.toLp_injective 2 hh)
  obtain ⟨x,hx,he⟩ := hf.sphereExtension_surjective hc (SimplicialChains.unitRadial Y)
    (SimplicialChains.unitRadial_norm hY)
  let A := symmetricCoordinates x
  have hA : A ≠ 0 := by
    intro hzero
    have hh : x = 0 := symmetricCoordinates_injective (hzero.trans (map_zero _).symm)
    simp [hh] at hx
  have hs : signedExtension f A ≠ 0 := fun hh => hA
    ((hf.signedExtension_eq_zero_iff (symmetricCoordinates_selfAdjoint x)).mp hh)
  let Z : EuclideanSpace ℝ ι := WithLp.toLp 2 (signedExtension f A)
  have hZ : Z ≠ 0 := fun hh => hs (WithLp.toLp_injective 2 hh)
  refine ⟨A, symmetricCoordinates_selfAdjoint x, ‖Z‖ / ‖Y‖,
    div_pos (norm_pos_iff.mpr hZ) (norm_pos_iff.mpr hY), ?_⟩
  change ‖Z‖⁻¹ • Z = ‖Y‖⁻¹ • Y at he
  have he' := congrArg (fun z => ‖Z‖ • z) he
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hZ), one_smul, smul_smul,
    ← div_eq_mul_inv] at he'
  exact WithLp.toLp_injective 2 he'

end LabelBound

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_Restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section Restrict
variable {V W ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]

lemma Admissible.comp_isometry {f : V → ι → ℝ} (hf : Admissible f) (e : W →ₗᵢ[ℝ] V) :
    Admissible (fun x => f (e x)) := by
  refine ⟨fun i => (hf.smooth i).comp e.contDiff,?_,?_,?_,?_⟩
  · intro x i
    rw [map_neg,hf.antipodal]
  · intro x hx i
    exact hf.nonneg _ ((e.norm_map x).trans hx) i
  · intro x hx
    exact hf.sum_one _ ((e.norm_map x).trans hx)
  · intro x y hx hy hxy i
    exact hf.orthogonal _ _ ((e.norm_map x).trans hx) ((e.norm_map y).trans hy)
      ((e.inner_map_map x y).trans hxy) i

lemma Admissible.restrict_labels {f : V → ι → ℝ} (hf : Admissible f)
    (s : Finset ι) (hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f x i = 0) :
    Admissible (fun x (i : s) => f x i.val) := by
  classical
  refine ⟨fun i => hf.smooth i.val,fun x i => hf.antipodal x i.val,
    fun x hx i => hf.nonneg x hx i.val,?_,fun x y hx hy hxy i => hf.orthogonal x y hx hy hxy i.val⟩
  intro x hx
  rw [← hf.sum_one x hx]
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hzero x hx i hi)

end Restrict

lemma orthogonal_isometry (k : ℕ) {u : EuclideanSpace ℝ (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k+1)),
      ∀ x, ⟪u,e x⟫ = 0 := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_⟩
  intro x
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_SpectralSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SpectralSupport
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma Admissible.signedExtension_pos_iff {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    0 < signedExtension f A i ↔ 0 < positiveExtension f A⁺ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change 0 < positiveExtension f A⁺ i - positiveExtension f A⁻ i ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_left (ne_of_gt h)
    rwa [hz,sub_zero]

lemma Admissible.signedExtension_positive_support {f : E → ι → ℝ} (hf : Admissible f)
    (A : Matrix ν ν ℝ) (i : ι) :
    0 < signedExtension f A i ↔ ∃ v : E,
      v ∈ LinearMap.range (op A⁺).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.signedExtension_pos_iff,hf.positiveExtension_support (CFC.posPart_nonneg A)]

lemma Admissible.signedExtension_range_labels {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} {I : Finset ι}
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : E} (hv : v ∈ LinearMap.range (op A⁺).toLinearMap) (hvn : ‖v‖ = 1)
    {i : ι} (hi : i ∉ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hvn i)
  by_contra hn
  have hp : 0 < f v i := lt_of_not_ge hn
  exact (not_lt_of_ge (hI i hi)) ((hf.signedExtension_positive_support A i).mpr ⟨v,hv,hvn,hp⟩)

end SpectralSupport
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_SupportIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
section SupportIncidence
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [InnerProductSpace ℝ V] [DecidableEq ι] in
lemma SupportFace.mono {f : V → ι → ℝ} {S U : Finset ι} (h : SupportFace f S) (hUS : U ⊆ S) : SupportFace f U := by
  obtain ⟨u,hu,hSu⟩ := h
  exact ⟨u,hu,hUS.trans hSu⟩
end SupportIncidence

lemma exists_unit_orthogonal_dim {k n : ℕ} (hn : n < k) (v : Fin n → EuclideanSpace ℝ (Fin k)) :
    ∃ w : EuclideanSpace ℝ (Fin k), ‖w‖ = 1 ∧ ∀ i, ⟪v i,w⟫ = 0 := by
  classical
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin k)) := Submodule.span ℝ (Set.range v)
  have hW : W ≠ ⊤ := by
    intro he
    have hh := finrank_le_of_span_eq_top he
    have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
    rw [hd,Fintype.card_fin] at hh
    omega
  have hO : Wᗮ ≠ ⊥ := fun he => hW (Submodule.orthogonal_eq_bot_iff.mp he)
  obtain ⟨w,hw,hwne⟩ := (Submodule.ne_bot_iff Wᗮ).mp hO
  refine ⟨(‖w‖⁻¹ : ℝ) • w,norm_smul_inv_norm hwne,?_⟩
  intro i
  rw [inner_smul_right,Submodule.inner_right_of_mem_orthogonal
    (show v i ∈ W from Submodule.subset_span (Set.mem_range_self i)) hw,mul_zero]

lemma Admissible.exists_label_absent_dim {k n : ℕ} {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ (Fin k) → ι → ℝ} (hf : Admissible f) (hn : n < k)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ i, ∀ j, i ∉ positiveSupport f (v j) := by
  obtain ⟨w,hw,hvw⟩ := exists_unit_orthogonal_dim hn v
  obtain ⟨i,hi⟩ := hf.support_nonempty hw
  exact ⟨i,fun j hj => Finset.disjoint_left.mp (hf.disjoint_supports (hv j) hw (hvw j)) hj hi⟩

section SixPure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin 3)
lemma Admissible.support_card_three_le_of_card {f : E → ι → ℝ}
    (hf : Admissible f) (hcard : Fintype.card ι = 6) {u : E} (hu : ‖u‖ = 1) :
    (positiveSupport f u).card ≤ 3 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 2 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl,hcard] at hb
  omega

lemma Admissible.triangle_no_free_edge {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {I U : Finset ι} (hIc : I.card = 3)
    (hIf : SupportFace f I) (hUI : U ⊆ I) (hUc : U.card = 2) :
    ∃ I' : Finset ι, I'.card = 3 ∧ SupportFace f I' ∧ U ⊆ I' ∧ I' ≠ I := by
  classical
  obtain ⟨w,hw,hIw⟩ := hIf
  have hmax (u : E) (hu : ‖u‖ = 1) (hIu : I ⊆ positiveSupport f u) : positiveSupport f u = I :=
    (Finset.eq_of_subset_of_card_le hIu (by rw [hIc]; exact hf.support_card_three_le_of_card hcard hu)).symm
  have hcomp : (Iᶜ : Finset ι).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,hcard,hIc]
    decide
  let : Nonempty ↥(Iᶜ : Finset ι) := hcomp.to_subtype
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  obtain ⟨u,hu,hUu,hnu⟩ := hf.no_free_ridge (k := 2) (by decide) hdim (by omega) hIc hUI hUc hmax hw
    (fun i hi => (mem_positiveSupport f w i).mp (hIw hi))
  obtain ⟨I',hI'c,hI'f,hI'u⟩ := hf.face_extends_three hcard (⟨u,hu,Finset.Subset.refl _⟩ : SupportFace f (positiveSupport f u))
  exact ⟨I',hI'c,hI'f,hUu.trans hI'u,fun he => hnu (he ▸ hI'u)⟩
end SixPure

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_TenPure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory

namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section TwoLabels
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.sum_two_labels {f : V → ι → ℝ} (hf : Admissible f)
    {u : V} (hu : ‖u‖ = 1) {i j : ι} (hij : i ≠ j)
    (hzero : ∀ l, l ≠ i → l ≠ j → f u l = 0) : f u i + f u j = 1 := by
  have hsum : ∑ l, f u l = ∑ l ∈ ({i,j} : Finset ι), f u l :=
    (Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => hzero l (by aesop) (by aesop))).symm
  simpa only [Finset.sum_pair hij] using hsum.symm.trans (hf.sum_one u hu)

lemma Admissible.two_labels_meet {f : V → ι → ℝ} (hf : Admissible f)
    (W : Submodule ℝ V) {i j : ι} (hij : i ≠ j)
    (hzero : ∀ u ∈ W, ‖u‖ = 1 → ∀ l, l ≠ i → l ≠ j → f u l = 0)
    {u v : V} (huW : u ∈ W) (hu : ‖u‖ = 1) (hui : 0 < f u i)
    (hvW : v ∈ W) (hv : ‖v‖ = 1) (hvj : 0 < f v j) :
    ∃ w : V, ‖w‖ = 1 ∧ 0 < f w i ∧ 0 < f w j := by
  classical
  by_contra hn
  have hnot (w : V) (hw : ‖w‖ = 1) : ¬ (0 < f w i ∧ 0 < f w j) := fun hh => hn ⟨w,hw,hh⟩
  have hui' : f u i = 1 := by
    have hj0 : f u j = 0 := le_antisymm (not_lt.mp (fun hp => hnot u hu ⟨hui,hp⟩)) (hf.nonneg u hu j)
    have hh := hf.sum_two_labels hu hij (hzero u huW hu)
    linarith
  have hvi : f v i = 0 := le_antisymm (not_lt.mp (fun hp => hnot v hv ⟨hp,hvj⟩)) (hf.nonneg v hv i)
  obtain ⟨v',hv'W,hv',hv'i,hinner⟩ : ∃ v' : V, v' ∈ W ∧ ‖v'‖ = 1 ∧ f v' i = 0 ∧ 0 ≤ ⟪u,v'⟫ := by
    by_cases hi : 0 ≤ ⟪u,v⟫
    · exact ⟨v,hvW,hv,hvi,hi⟩
    · exact ⟨-v,W.neg_mem hvW,by simpa using hv,by simpa only [hf.antipodal] using hvi,by simp only [inner_neg_right]; linarith⟩
  let p : ℝ → V := fun t => (1-t) • u + t • v'
  have hp : Continuous p := ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have hpW (t : ℝ) : p t ∈ W := W.add_mem (W.smul_mem _ huW) (W.smul_mem _ hv'W)
  have hpz (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : p t ≠ 0 := by
    intro hz
    have hi := congrArg (fun x : V => ⟪u,x⟫) hz
    have hi' : (1-t)+t*⟪u,v'⟫ = 0 := by
      simpa only [p,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one,inner_zero_right] using hi
    have ht1 : t = 1 := by nlinarith [ht.2,mul_nonneg ht.1 hinner]
    have hv0 : v' = 0 := by simpa only [p,ht1,sub_self,zero_smul,one_smul,zero_add] using hz
    simp [hv0] at hv'
  let q : ℝ → V := fun t => unitRadial (p t)
  have hq : ContinuousOn q (Icc (0:ℝ) 1) :=
    (unitRadial_continuousOn (S := p '' Icc (0:ℝ) 1) (by rintro x ⟨t,ht,rfl⟩; exact hpz t ht)).comp hp.continuousOn (fun t ht => ⟨t,ht,rfl⟩)
  have hqn (t) (ht : t ∈ Icc (0:ℝ) 1) : ‖q t‖ = 1 := unitRadial_norm (hpz t ht)
  have hqW (t) : q t ∈ W := W.smul_mem _ (hpW t)
  have hq0 : q 0 = u := by simp only [q,p,sub_zero,one_smul,zero_smul,add_zero,unitRadial,hu,inv_one,one_smul]
  have hq1 : q 1 = v' := by simp only [q,p,sub_self,zero_smul,one_smul,zero_add,unitRadial,hv',inv_one,one_smul]
  have hcont : ContinuousOn (fun t => f (q t) i) (Icc (0:ℝ) 1) := (hf.smooth i).continuous.comp_continuousOn hq
  have hhalf : (1/2 : ℝ) ∈ Icc (f (q 1) i) (f (q 0) i) := by rw [hq0,hq1,hui',hv'i]; constructor <;> norm_num
  obtain ⟨t,ht,hth⟩ := intermediate_value_Icc' (zero_le_one : (0:ℝ) ≤ 1) hcont hhalf
  have hsum := hf.sum_two_labels (hqn t ht) hij (hzero (q t) (hqW t) (hqn t ht))
  exact hnot (q t) (hqn t ht) ⟨by linarith,by linarith⟩
end TwoLabels

end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_AllPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section AllPairs
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)
lemma Admissible.all_pairs {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) {i j : ι} (hij : i ≠ j) :
    ∃ u : E, ‖u‖ = 1 ∧ 0 < f u i ∧ 0 < f u j := by
  classical
  let y : ι → ℝ := fun l => if l = i ∨ l = j then 1 else -1
  have hy : y ≠ 0 := by intro h; have hi := congrFun h i; simp [y] at hi
  obtain ⟨A,hA,t,ht,hAt⟩ := hf.signedExtension_ray hdim hy
  have hai : 0 < signedExtension f A i := by rw [hAt]; simpa [y] using ht
  have haj : 0 < signedExtension f A j := by rw [hAt]; simpa [y] using ht
  obtain ⟨u,huW,hu,hui⟩ := (hf.signedExtension_positive_support A i).mp hai
  obtain ⟨v,hvW,hv,hvj⟩ := (hf.signedExtension_positive_support A j).mp haj
  apply hf.two_labels_meet (LinearMap.range (op A⁺).toLinearMap) hij ?_ huW hu hui hvW hv hvj
  intro w hw hwn l hli hlj
  apply hf.signedExtension_range_labels (I := {i,j}) ?_ hw hwn (by simp [hli,hlj])
  intro l hl
  have hli : l ≠ i := by aesop
  have hlj : l ≠ j := by aesop
  rw [hAt]
  simp only [Pi.smul_apply,smul_eq_mul,y,ite_eq_right (not_or.mpr ⟨hli,hlj⟩),mul_neg_one]
  linarith
end AllPairs
end BorsukNine

namespace BorsukNine.SixCounting

variable {α : Type*} [DecidableEq α]

attribute [local instance] OAI.BorsukNine.SixCounting.instDecidablePred_solutions
lemma pair_incidence_count (C : Finset α) (T : Finset α → Prop) :
    ∑ P ∈ C.powersetCard 2, ((triangles C T).filter (P ⊆ ·)).card =
      3 * (triangles C T).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    ∑ U ∈ triangles C T, ∑ P ∈ C.powersetCard 2, (if P ⊆ U then (1 : ℕ) else 0) =
        ∑ U ∈ triangles C T, (U.powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [← Finset.card_filter]
      congr 1
      ext P
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨fun h => ⟨h.2, h.1.2⟩,
        fun h => ⟨⟨h.1.trans (mem_triangles.mp hU).1, h.2⟩, h.1⟩⟩
    _ = 3 * (triangles C T).card := by
      have he : ∀ U ∈ triangles C T, (U.powersetCard 2).card = 3 := by
        intro U hU
        rw [Finset.card_powersetCard, (mem_triangles.mp hU).2.1]
        decide
      rw [Finset.sum_congr rfl he]
      simp [mul_comm]

lemma complement_triangle {C U : Finset α} (hC : C.card = 6)
    (hU : U ∈ C.powersetCard 3) : C \ U ∈ C.powersetCard 3 := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.sdiff_subset, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hU).1,
    hC, (Finset.mem_powersetCard.mp hU).2]

lemma triangle_count_upper {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U)) :
    (triangles C T).card ≤ 10 := by
  classical
  let A := triangles C T
  let B := C.powersetCard 3 \ A
  have hA : A ⊆ C.powersetCard 3 := Finset.filter_subset _ _
  have hi : (A.image (fun U => C \ U)) ⊆ B := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC (hA hV), ?_⟩
    intro hh
    exact hdisj V (hA hV) (mem_triangles.mp hV).2.2 (mem_triangles.mp hh).2.2
  have hinj : Set.InjOn (fun U => C \ U) (↑A : Set (Finset α)) := by
    intro U hU V hV he
    have hh := congrArg (fun W => C \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hU).1,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1] using hh
  have hc : A.card ≤ B.card := calc
    A.card = (A.image (fun U => C \ U)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ B.card := Finset.card_le_card hi
  have hB : B.card = 20 - A.card := by
    rw [Finset.card_sdiff_of_subset hA, Finset.card_powersetCard, hC]
    norm_num [Nat.choose]
  change A.card ≤ 10
  omega

lemma triangle_count_eq_ten {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card) :
    (triangles C T).card = 10 := by
  have hupper := triangle_count_upper hC hdisj
  have hlower : 30 ≤ ∑ P ∈ C.powersetCard 2,
      ((triangles C T).filter (P ⊆ ·)).card := by
    calc
      30 = ∑ _P ∈ C.powersetCard 2, 2 := by
        norm_num [Finset.card_powersetCard, hC, Nat.choose]
      _ ≤ _ := Finset.sum_le_sum hpairs
  rw [pair_incidence_count] at hlower
  omega

lemma pair_degree_eq_two {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card)
    {P : Finset α} (hP : P ∈ C.powersetCard 2) :
    ((triangles C T).filter (P ⊆ ·)).card = 2 := by
  have hsum : (∑ _P ∈ C.powersetCard 2, 2) =
      ∑ P ∈ C.powersetCard 2, ((triangles C T).filter (P ⊆ ·)).card := by
    rw [pair_incidence_count, triangle_count_eq_ten hC hdisj hpairs]
    norm_num [Finset.card_powersetCard, hC, Nat.choose]
  exact ((Finset.sum_eq_sum_iff_of_le hpairs).mp hsum P hP).symm

lemma complementary_iff {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card)
    {U : Finset α} (hU : U ∈ C.powersetCard 3) : T U ↔ ¬T (C \ U) := by
  classical
  refine ⟨hdisj U hU, ?_⟩
  intro hn
  let A := triangles C T
  let B := C.powersetCard 3 \ A
  have hA : A ⊆ C.powersetCard 3 := Finset.filter_subset _ _
  have hi : (A.image (fun U => C \ U)) ⊆ B := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC (hA hV), ?_⟩
    intro hh
    exact hdisj V (hA hV) (mem_triangles.mp hV).2.2 (mem_triangles.mp hh).2.2
  have hinj : Set.InjOn (fun U => C \ U) (↑A : Set (Finset α)) := by
    intro U hU V hV he
    have hh := congrArg (fun W => C \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hU).1,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1] using hh
  have he : A.image (fun U => C \ U) = B := by
    apply Finset.eq_of_subset_of_card_le hi
    rw [Finset.card_image_of_injOn hinj, Finset.card_sdiff_of_subset hA,
      Finset.card_powersetCard, hC]
    change Nat.choose 6 3 - (triangles C T).card ≤ (triangles C T).card
    rw [triangle_count_eq_ten hC hdisj hpairs]
    decide
  have hcU : C \ U ∈ B := by
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC hU, ?_⟩
    intro hh
    exact hn (mem_triangles.mp hh).2.2
  rw [← he] at hcU
  obtain ⟨V, hV, hVU⟩ := Finset.mem_image.mp hcU
  have hEq : V = U := by
    have hh := congrArg (fun W => C \ W) hVU
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powersetCard.mp hU).1] using hh
  exact hEq ▸ (mem_triangles.mp hV).2.2

end BorsukNine.SixCounting

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Support_SixFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
attribute [local instance] Classical.propDecidable
open scoped RealInnerProductSpace
section SixFaces
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin 3)
lemma Admissible.six_complement_exclusion {f : E → ι → ℝ} (hf : Admissible f)
    {U : Finset ι} (hU : SupportFace f U) : ¬ SupportFace f Uᶜ := by
  classical
  rintro ⟨v,hv,hUv⟩
  obtain ⟨u,hu,hUu⟩ := hU
  obtain ⟨i,hi⟩ := hf.exists_label_absent_dim (n := 2) (by decide) ![u,v] (by
    intro j
    fin_cases j <;> simp [hu,hv])
  by_cases h : i ∈ U
  · exact hi 0 (hUu h)
  · exact hi 1 (hUv (Finset.mem_compl.mpr h))

lemma Admissible.six_pair_lower {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    2 ≤ ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card := by
  classical
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hPc
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  obtain ⟨u,hu,hui,huj⟩ := hf.all_pairs hdim hij
  have hpair : SupportFace f {i,j} := ⟨u,hu,by
    intro l hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact (mem_positiveSupport _ _ _).mpr hui
    · exact (mem_positiveSupport _ _ _).mpr huj⟩
  obtain ⟨I,hIc,hIf,hPI⟩ := hf.face_extends_three hcard hpair
  obtain ⟨I',hI'c,hI'f,hPI',hne⟩ := hf.triangle_no_free_edge hcard hIc hIf hPI (by simp [hij])
  have hsub : {I,I'} ⊆ (SixCounting.triangles Finset.univ (SupportFace f)).filter ({i,j} ⊆ ·) := by
    intro J hJ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr ⟨Finset.subset_univ _,hIc,hIf⟩,hPI⟩
    · exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr ⟨Finset.subset_univ _,hI'c,hI'f⟩,hPI'⟩
  have hc := Finset.card_le_card hsub
  simpa [hne.symm] using hc

lemma Admissible.six_complementary {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hUc : U.card = 3) :
    SupportFace f U ↔ ¬ SupportFace f Uᶜ := by
  classical
  have hC : (Finset.univ : Finset ι).card = 6 := by simpa using hcard
  have hd : ∀ U ∈ (Finset.univ : Finset ι).powersetCard 3,
      SupportFace f U → ¬ SupportFace f (Finset.univ \ U) := by
    intro U _ hU
    simpa only [← Finset.compl_eq_univ_sdiff] using hf.six_complement_exclusion hU
  have hp : ∀ P ∈ (Finset.univ : Finset ι).powersetCard 2,
      2 ≤ ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card := by
    intro P hP
    exact hf.six_pair_lower hcard (Finset.mem_powersetCard.mp hP).2
  simpa only [← Finset.compl_eq_univ_sdiff] using SixCounting.complementary_iff hC hd hp
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ U,hUc⟩)

lemma Admissible.six_pair_degree {f : E → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card = 2 := by
  classical
  apply SixCounting.pair_degree_eq_two
    (C := Finset.univ) (by simpa using hcard) ?_ ?_ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hPc⟩)
  · intro U _ hU
    simpa only [← Finset.compl_eq_univ_sdiff] using hf.six_complement_exclusion hU
  · intro P hP
    exact hf.six_pair_lower hcard (Finset.mem_powersetCard.mp hP).2
end SixFaces

lemma pair_triangle_card {α : Type*} [DecidableEq α] (C P : Finset α) (T : Finset α → Prop)
    (hPC : P ⊆ C) (hPc : P.card = 2) :
    (SixCounting.triangles C T |>.filter (P ⊆ ·)).card =
      ((C \ P).filter (fun w => T (insert w P))).card := by
  classical
  symm
  apply Finset.card_bij (fun w _ => insert w P)
  · intro w hw
    obtain ⟨hw,hT⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwC,hwP⟩ := Finset.mem_sdiff.mp hw
    exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr
      ⟨Finset.insert_subset hwC hPC,by rw [Finset.card_insert_of_notMem hwP,hPc],hT⟩,Finset.subset_insert _ _⟩
  · intro w hw v hv he
    have hwP := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
    have hm : w ∈ insert v P := he ▸ Finset.mem_insert_self w P
    exact (Finset.mem_insert.mp hm).resolve_right hwP
  · intro U hU
    obtain ⟨hU,hPU⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUC,hUc,hT⟩ := SixCounting.mem_triangles.mp hU
    have hd : (U \ P).card = 1 := by rw [Finset.card_sdiff_of_subset hPU,hUc,hPc]
    obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hd
    have hwm : w ∈ U \ P := by rw [hw]; simp
    obtain ⟨hwU,hwP⟩ := Finset.mem_sdiff.mp hwm
    have he : insert w P = U := by
      have hh := Finset.sdiff_union_of_subset hPU
      simpa only [hw,Finset.singleton_union] using hh
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hUC hwU,hwP⟩,he ▸ hT⟩,he⟩

lemma Admissible.six_pair_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : EuclideanSpace ℝ (Fin 3) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    ((Pᶜ : Finset ι).filter (fun w => SupportFace f (insert w P))).card = 2 := by
  classical
  rw [Finset.compl_eq_univ_sdiff,← pair_triangle_card _ _ _ (Finset.subset_univ P) hPc]
  exact hf.six_pair_degree hcard hPc
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Projectors_Within
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
attribute [local instance] Classical.propDecidable
section Within
variable {α : Type*} [DecidableEq α]
lemma withinLabels_card {C U : Finset α} (hUC : U ⊆ C) : (withinLabels C U).card = U.card := by
  rw [withinLabels,Finset.card_subtype,Finset.filter_true_of_mem]
  exact fun _ hi => hUC hi
lemma withinLabels_compl (C U : Finset α) :
    withinLabels C (C \ U) = (withinLabels C U)ᶜ := by
  ext i
  simp [i.property]
lemma withinLabels_insert (C U : Finset α) (i : C) :
    withinLabels C (insert i.val U) = insert i (withinLabels C U) := by
  ext j
  simp only [mem_withinLabels,Finset.mem_insert,Subtype.ext_iff]
end Within

section FacetSix
variable {f : Vector4 → Fin 10 → ℝ}

lemma Admissible.facet_complement_exclusion (hf : Admissible f) {S U : Finset (Fin 10)}
    (hS : SupportFace f S) (hU : SupportFace f U) : ¬ SupportFace f (Sᶜ \ U) := by
  classical
  rintro ⟨v,hv,hCv⟩
  obtain ⟨w,hw,hSw⟩ := hS
  obtain ⟨u,hu,hUu⟩ := hU
  obtain ⟨i,hi⟩ := hf.exists_label_absent_dim (n := 3) (by decide) ![w,u,v] (by
    intro j
    fin_cases j <;> simp [hw,hu,hv])
  by_cases hiS : i ∈ S
  · exact hi 0 (hSw hiS)
  by_cases hiU : i ∈ U
  · exact hi 1 (hUu hiU)
  exact hi 2 (hCv (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hiS,hiU⟩))

lemma restricted_face_image {C U : Finset (Fin 10)} (hUC : U ⊆ C)
    (e : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] Vector4)
    (hU : SupportFace (fun x (i : C) => f (e x) i.val) (withinLabels C U)) :
    SupportFace f U := by
  obtain ⟨x,hx,hUx⟩ := hU
  refine ⟨e x,by simpa using hx,?_⟩
  intro i hi
  exact (mem_positiveSupport _ _ _).mpr ((mem_positiveSupport _ _ (⟨i,hUC hi⟩ : C)).mp
    (hUx (mem_withinLabels.mpr hi)))

lemma Admissible.facet_six_properties (hf : Admissible f) {S : Finset (Fin 10)}
    (hSc : S.card = 4) (hSf : SupportFace f S) :
    (∀ U ⊆ Sᶜ, U.card = 3 → (SupportFace f U ↔ ¬ SupportFace f (Sᶜ \ U))) ∧
    (∀ P ⊆ Sᶜ, P.card = 2 →
      ((Sᶜ \ P).filter (fun w => SupportFace f (insert w P))).card = 2) := by
  classical
  obtain ⟨w,hw,hSw⟩ := hSf
  obtain ⟨e,he⟩ := orthogonal_isometry 3 hw
  let C : Finset (Fin 10) := Sᶜ
  let g : EuclideanSpace ℝ (Fin 3) → C → ℝ := fun x i => f (e x) i.val
  have hCc : C.card = 6 := by dsimp [C]; rw [Finset.card_compl,Fintype.card_fin,hSc]
  have hcard : Fintype.card C = 6 := by simpa using hCc
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ C, f (e x) i = 0 := by
    intro x hx i hi
    have hiS : i ∈ S := by simpa [C] using hi
    have hwpos : 0 < f w i := (mem_positiveSupport _ _ _).mp (hSw hiS)
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal w (e x) hw
      (by simpa using hx) (he x) i ⟨hwpos,hp⟩)) (hf.nonneg _ (by simpa using hx) i)
  have hg : Admissible g := (hf.comp_isometry e).restrict_labels C hzero
  have hmap {U : Finset (Fin 10)} (hUC : U ⊆ C) :
      SupportFace g (withinLabels C U) → SupportFace f U := restricted_face_image hUC e
  have hfaces {U : Finset (Fin 10)} (hUC : U ⊆ C) (hUc : U.card = 3) :
      SupportFace g (withinLabels C U) ↔ SupportFace f U := by
    refine ⟨hmap hUC,?_⟩
    intro hU
    apply (hg.six_complementary hcard (by rw [withinLabels_card hUC,hUc])).mpr
    rw [← withinLabels_compl]
    intro hcomp
    exact hf.facet_complement_exclusion ⟨w,hw,hSw⟩ hU (hmap Finset.sdiff_subset hcomp)
  constructor
  · intro U hUC hUc
    have hcUc : (C \ U).card = 3 := by rw [Finset.card_sdiff_of_subset hUC,hCc,hUc]
    rw [← hfaces hUC hUc,← hfaces Finset.sdiff_subset hcUc,withinLabels_compl]
    exact hg.six_complementary hcard (by rw [withinLabels_card hUC,hUc])
  · intro P hPC hPc
    let P' := withinLabels C P
    have hP'c : P'.card = 2 := by rw [withinLabels_card hPC,hPc]
    have hinsert {i : C} (hi : i ∉ P') :
        SupportFace g (insert i P') ↔ SupportFace f (insert i.val P) := by
      have hiP : i.val ∉ P := by simpa only [P',mem_withinLabels] using hi
      have hh := hfaces (Finset.insert_subset i.property hPC)
        (by rw [Finset.card_insert_of_notMem hiP,hPc])
      simpa only [withinLabels_insert] using hh
    have hc := hg.six_pair_count hcard hP'c
    have hcount : ((P'ᶜ).filter (fun i => SupportFace g (insert i P'))).card =
        ((C \ P).filter (fun i => SupportFace f (insert i P))).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        obtain ⟨hiP,hif⟩ := Finset.mem_filter.mp hi
        have hiP' := Finset.mem_compl.mp hiP
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨i.property,by
          simpa only [P',mem_withinLabels] using hiP'⟩,(hinsert hiP').mp hif⟩
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro i hi
        obtain ⟨hiC,hif⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiC,hiP⟩ := Finset.mem_sdiff.mp hiC
        have hiP' : (⟨i,hiC⟩ : C) ∉ P' := by simpa only [P',mem_withinLabels] using hiP
        exact ⟨⟨i,hiC⟩,Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hiP',(hinsert hiP').mpr hif⟩,rfl⟩
    exact hcount.symm.trans hc
end FacetSix
end BorsukNine

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_Counterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
attribute [local instance] Classical.propDecidable

theorem Admissible.support_ten_system {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f) :
    FiniteObstruction.TenSystem (fun U => U.card = 3 ∧ SupportFace f U)
      (fun S => S.card = 4 ∧ SupportFace f S) := by
  classical
  constructor
  · intro S hS
    exact hS.1
  · intro S U hS hUS hUc
    exact ⟨hUc,hS.2.mono hUS⟩
  · intro U hU
    obtain ⟨S,hSc,hSf,hUS⟩ := hf.face_extends_four hU.2
    exact ⟨S,⟨hSc,hSf⟩,hUS⟩
  · intro S U hS hUS hUc
    obtain ⟨S',hS'c,hS'f,hUS',hne⟩ := hf.tetra_no_free_triangle hS.1 hS.2 hUS hUc
    exact ⟨S',⟨hS'c,hS'f⟩,hUS',hne⟩
  · intro S U hS hUC hUc
    have hCc : (Sᶜ \ U).card = 3 := by
      rw [Finset.card_sdiff_of_subset hUC,Finset.card_compl,Fintype.card_fin,hS.1,hUc]
    simpa only [hUc,hCc,true_and] using (hf.facet_six_properties hS.1 hS.2).1 U hUC hUc
  · intro S P hS hPC hPc
    trans ((Sᶜ \ P).filter (fun w => SupportFace f (insert w P))).card
    · apply congrArg Finset.card
      ext w
      simp only [Finset.mem_filter]
      constructor
      · intro support_mem
        exact ⟨support_mem.1, support_mem.2.2⟩
      · intro support_mem
        refine ⟨support_mem.1, ⟨?_, support_mem.2⟩⟩
        rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp support_mem.1).2, hPc]
    · exact (hf.facet_six_properties hS.1 hS.2).2 P hPC hPc

theorem no_admissible_ten : ¬ ∃ f : Vector4 → Fin 10 → ℝ, Admissible f := by
  rintro ⟨f,hf⟩
  have hempty : SupportFace f ∅ := ⟨EuclideanSpace.single 0 1,by simp,Finset.empty_subset _⟩
  obtain ⟨S,hSc,hSf,_⟩ := hf.face_extends_four hempty
  exact FiniteObstruction.no_ten_system hf.support_ten_system ⟨S,hSc,hSf⟩

theorem main_theorem_oai :
    IsCompact projectorSet ∧
    projectorSet ⊆ traceOneSymmetric ∧
    Metric.diam projectorSet = Real.sqrt 2 ∧
    ¬ HasTenSmallCover := by
  refine ⟨isCompact_projectorSet,projectorSet_subset_traceOneSymmetric,diam_projectorSet,?_⟩
  intro h
  exact no_admissible_ten (cover_to_admissible h)

end BorsukNine

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.main_theorem_oai := @OAI.BorsukNine.main_theorem_oai
