-- Prove2me | solution 1 for OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input_s236
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T20:23:27.921189+00:00
-- url     : https://prove2.me/submissions/a5e25c27-97f9-43c9-acfd-b776302109f3

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_OAIQ236Ap011

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

open _root_.Matrix

theorem harmonic_inverse_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (i j : ι) : 0 ≤ C⁻¹ i j := by
  have hv : ∀ k : ι, (0 : ℝ) ≤ (Pi.single j (1 : ℝ) : ι → ℝ) k := by
    intro k
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  have hi := harmonic_extension_nonneg C hC hOff (Pi.single j 1) hv i
  simpa [Matrix.mulVec_single] using hi

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FusionFold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.instDecidableRelStringLabelStringAdjacent
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ)

omit [Fintype V] in
lemma fusionUnfoldedCartan_symm (d : V → V → FusionEdge E)
    (hd : ∀ s t, d s t = d t s) (α β : V × FusionLabel m) :
    fusionUnfoldedCartan m d α β = fusionUnfoldedCartan m d β α := by
  classical
  simp only [fusionUnfoldedCartan, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
  rw [hd α.1 β.1, FusionEdge.multiplicity_symm]
  simp only [eq_comm]

omit [Fintype V] in
lemma fusionUnfoldedCartan_off (d : V → V → FusionEdge E)
    (α β : V × FusionLabel m) (h : α ≠ β) :
    fusionUnfoldedCartan m d α β ≤ 0 := by
  simp only [fusionUnfoldedCartan, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply, ite_eq_right h, zero_sub]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

lemma harmonic_posDef_of_strict_rows {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) (hCv : ∀ i, 0 < (C *ᵥ v) i) : C.PosDef := by
  classical
  have hHerm : C.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j; exact hSym j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  simp only [star_trivial]
  let w : ι → ℝ := fun i => x i / v i
  have hxw : x = v*w := by
    funext i
    exact (mul_div_cancel₀ (x i) (ne_of_gt (hv i))).symm
  have he : 0 ≤ (1/2 : ℝ) * ∑ i, ∑ j, (-C i j * v i * v j) * (w i-w j)^2 := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i=j
    · subst j; simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr (hOff i j hij)) (hv i).le)
        (hv j).le) (sq_nonneg _)
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    apply hx
    funext i
    exact not_ne_iff.mp (fun hi => hn ⟨i,hi⟩)
  have hsum : 0 < ∑ i, v i*(C *ᵥ v) i*(w i)^2 := by
    apply Finset.sum_pos'
    · intro j _; exact mul_nonneg (mul_pos (hv j) (hCv j)).le (sq_nonneg _)
    · refine ⟨i, Finset.mem_univ i, mul_pos (mul_pos (hv i) (hCv i)) ?_⟩
      exact sq_pos_of_ne_zero (div_ne_zero hi (ne_of_gt (hv i)))
  rw [hxw, harmonic_scaled_form C hSym]
  linarith

lemma fusion_positive_definite (hm : ∀ e, 2 ≤ m e) (d : V → V → FusionEdge E)
    (hd : ∀ s t, d s t = d t s)
    (hOff : ∀ s t, s ≠ t → fusionFoldedCartan m d s t ≤ 0)
    (hC : (fusionFoldedCartan m d).PosDef) : (fusionUnfoldedCartan m d).PosDef := by
  let C := fusionFoldedCartan m d
  let v : V → ℝ := C⁻¹ *ᵥ (fun _ => 1)
  have hv : ∀ s, 0 < v s := by
    intro s
    change 0 < ∑ t, C⁻¹ s t * 1
    apply Finset.sum_pos'
    · intro t _; exact mul_nonneg (harmonic_inverse_nonneg C hC hOff s t) (by norm_num)
    · exact ⟨s, Finset.mem_univ s, mul_pos hC.inv.diag_pos (by norm_num)⟩
  apply harmonic_posDef_of_strict_rows (fusionUnfoldedCartan m d)
    (fusionUnfoldedCartan_symm m d hd) (fusionUnfoldedCartan_off m d)
    (fusionFold m v)
  · intro α; exact mul_pos (fusionWeight_pos m hm α.2) (hv α.1)
  · rw [fusion_intertwining m hm d, show C *ᵥ v = (fun _ => 1) from harmonic_solve C hC _]
    intro α
    simpa only [fusionFold, mul_one] using fusionWeight_pos m hm α.2

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SphericalFoldedMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.labelSplit_apply _root_.OAI.HarmonicArtin.labelSplit_symm_at _root_.OAI.HarmonicArtin.labelSplit_symm_rest _root_.OAI.HarmonicArtin.unfoldedHom_simple _root_.OAI.HarmonicArtin.unfoldedMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [LinearOrder S]

theorem spherical_unfolded_posDef (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J) :
    (fusionUnfoldedCartan (fusionLabelSize M)
      (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j))).PosDef := by
  apply fusion_positive_definite (fusionLabelSize M)
    (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
    (fun i j:J=>coxeterFusionEdge M (.inl i) (.inl j))
    (fun i j=>coxeterFusionEdge_symm M (.inl i) (.inl j))
  · intro i j hij
    rw [spherical_folded_matrix]
    exact Geometric.cartan_off_nonpos M i j (fun h=>hij (Subtype.ext h))
  · rw [spherical_folded_matrix]
    exact Geometric.spherical_cartan_posDef M J hJ

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshInsertionMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality of weighted path insertions. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I P Q : Type} [Fintype I] [Fintype P] [Fintype Q]

omit [Fintype P] in
/-- Rows obtained by inserting disjoint labeled detours are orthogonal. -/
theorem insertion_matrix_mul_conjTranspose (f : I × P → Q)
    (hf : Function.Injective f) (a : I → ℂ) :
    let C : Matrix P Q ℂ := fun p q => ∑ i, if q=f (i,p) then a i else 0
    C*C.conjTranspose = (∑ i, a i*star (a i)) • (1 : Matrix P P ℂ) := by
  ext p r
  change (∑ q : Q, (∑ i : I, if q=f (i,p) then a i else 0) *
    star (∑ j : I, if q=f (j,r) then a j else 0)) =
      (∑ i : I, a i*star (a i)) * (if p=r then 1 else 0)
  simp only [star_sum,apply_ite star,star_zero,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  trans ∑ i : I, ∑ j : I, if f (i,r)=f (j,p) then a j*star (a i) else 0
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ite_mul,zero_mul,mul_ite,mul_zero]
    simp
  · have he : ∀ i j : I, f (i,r)=f (j,p) ↔ i=j ∧ p=r := by
      intro i j
      constructor
      · intro h
        obtain ⟨hi,hr⟩ := Prod.mk.inj (hf h)
        exact ⟨hi,hr.symm⟩
      · rintro ⟨rfl,rfl⟩
        rfl
    simp only [he]
    by_cases hpr : p=r
    · subst r
      simp
    · simp [hpr]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshPathSpaces
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite path spaces and weighted last-backtrack contractions. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (G : SimpleGraph V)

lemma meshInsertBacktrack_injective {n : ℕ} {v : V} :
    Function.Injective (fun up : {u : V // G.Adj u v} × MeshPaths G n v =>
      meshInsertBacktrack G up.1 up.2) := by
  rintro ⟨u,p⟩ ⟨w,q⟩ h
  change (⟨u,⟨⟨v,u.property.symm⟩,p⟩⟩ : MeshPaths G (n+2) v)=
    ⟨w,⟨⟨v,w.property.symm⟩,q⟩⟩ at h
  obtain ⟨hu,hinner⟩ := Sigma.mk.inj_iff.mp h
  cases hu
  have hp := (Sigma.mk.inj_iff.mp (eq_of_heq hinner)).2
  exact Prod.ext rfl (eq_of_heq hp)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshContraction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path-space loop identity and extension functor. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- Inserting and then contracting a final backtrack multiplies by the
Perron eigenvalue. This is proved for the actual path matrices. -/
theorem meshContraction_loop (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (n : ℕ) (v : V) :
    meshContractionMatrix G μ n v * (meshContractionMatrix G μ n v).conjTranspose =
      (δ : ℂ) • (1 : Matrix (MeshPaths G n v) (MeshPaths G n v) ℂ) := by
  have h := insertion_matrix_mul_conjTranspose
    (fun up : {u : V // G.Adj u v} × MeshPaths G n v => meshInsertBacktrack G up.1 up.2)
    (meshInsertBacktrack_injective G) (fun u => (Real.sqrt (μ u/μ v) : ℂ))
  have hweight : (∑ u : {u : V // G.Adj u v},
      (Real.sqrt (μ u/μ v) : ℂ)*star (Real.sqrt (μ u/μ v) : ℂ))=(δ : ℂ) := by
    have hs : ∀ u : {u : V // G.Adj u v},
        (Real.sqrt (μ u/μ v) : ℂ)*star (Real.sqrt (μ u/μ v) : ℂ)=(μ u/μ v : ℝ) := by
      intro u
      rw [Complex.star_def,Complex.conj_ofReal,←Complex.ofReal_mul,
        Real.mul_self_sqrt (div_nonneg (hμ u).le (hμ v).le)]
    simp only [hs,←Complex.ofReal_sum]
    congr 1
    rw [←Finset.sum_div,heigen,mul_div_cancel_right₀ _ (ne_of_gt (hμ v))]
  rw [hweight] at h
  exact h

omit [Fintype V] in
lemma meshExtend_one (n : ℕ) (v : V) :
    meshExtendMatrix G (fun u => (1 : Matrix (MeshPaths G n u) (MeshPaths G n u) ℂ)) v=1 := by
  unfold meshExtendMatrix
  change Matrix.blockDiagonal'
    (1 : ∀ u : {u : V // G.Adj u v},
      Matrix (MeshPaths G n u.val) (MeshPaths G n u.val) ℂ) = _
  rw [Matrix.blockDiagonal'_one]
  ext p q
  simp only [Matrix.one_apply]
  change (if p=q then (1 : ℂ) else 0) =
    @ite ℂ (p=q) (Classical.propDecidable _) 1 0
  split_ifs <;> rfl

lemma meshExtend_mul {k m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G k v) (MeshPaths G m v) ℂ)
    (B : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshExtendMatrix G (fun u => A u*B u) v=meshExtendMatrix G A v*meshExtendMatrix G B v :=
  Matrix.blockDiagonal'_mul _ _

omit [Fintype V] in
lemma meshExtend_adjoint {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    (meshExtendMatrix G A v).conjTranspose=meshExtendMatrix G (fun u => (A u).conjTranspose) v :=
  Matrix.blockDiagonal'_conjTranspose _

omit [Fintype V] in
lemma meshExtend_sub {m n : ℕ}
    (A B : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshExtendMatrix G (fun u => A u-B u) v=meshExtendMatrix G A v-meshExtendMatrix G B v :=
  Matrix.blockDiagonal'_sub _ _

omit [Fintype V] in
lemma meshExtend_smul {m n : ℕ} (a : ℂ)
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshExtendMatrix G (fun u => a • A u) v=a • meshExtendMatrix G A v :=
  Matrix.blockDiagonal'_smul a (fun u : {u : V // G.Adj u v} => A u.val)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshAdjacent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adjacent contraction identities on the actual finite path spaces. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma meshContraction_mul (μ : V → ℝ) (n : ℕ) (v : V) {R : Type} [Fintype R]
    (B : Matrix (MeshPaths G (n+2) v) R ℂ) (p : MeshPaths G n v) (r : R) :
    (meshContractionMatrix G μ n v * B) p r =
      ∑ u : {u : V // G.Adj u v},
        (Real.sqrt (μ u/μ v) : ℂ) * B (meshInsertBacktrack G u p) r := by
  change (∑ q, (∑ u : {u : V // G.Adj u v},
    if q=meshInsertBacktrack G u p then (Real.sqrt (μ u/μ v) : ℂ) else 0)*B q r)=_
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

lemma meshContraction_head (μ : V → ℝ) (n : ℕ) (v : V)
    (p : MeshPaths G n v) (u : {u : V // G.Adj u v})
    (q : MeshPaths G (n+1) u.val) :
    meshContractionMatrix G μ n v p ⟨u,q⟩ =
      if q=⟨⟨v,u.property.symm⟩,p⟩ then (Real.sqrt (μ u/μ v) : ℂ) else 0 := by
  change (∑ w : {w : V // G.Adj w v},
    if (⟨u,q⟩ : MeshPaths G (n+2) v)=meshInsertBacktrack G w p
    then (Real.sqrt (μ w/μ v) : ℂ) else 0)=_
  rw [Finset.sum_eq_single u]
  · by_cases hq : q=⟨⟨v,u.property.symm⟩,p⟩
    · subst q
      simp only [meshInsertBacktrack,ite_true, if_true]
      exact (ite_eq_left rfl).symm
    · have hne : (⟨u,q⟩ : MeshPaths G (n+2) v)≠meshInsertBacktrack G u p := by
        intro h
        exact hq (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      simp only [hne,hq,ite_false, if_false]
  · intro w _ hwu
    have hne : (⟨u,q⟩ : MeshPaths G (n+2) v)≠meshInsertBacktrack G w p := by
      intro h
      exact hwu (congrArg Sigma.fst h).symm
    simp [hne]
  · simp

lemma meshContraction_return (μ : V → ℝ) (n : ℕ) (v : V)
    (u : {u : V // G.Adj u v}) (p : MeshPaths G (n+1) v)
    (r : MeshPaths G n u.val) :
    meshContractionMatrix G μ n u.val r ⟨⟨v,u.property.symm⟩,p⟩ =
      if p=⟨u,r⟩ then (Real.sqrt (μ v/μ u) : ℂ) else 0 := by
  simpa only using meshContraction_head G μ n u.val r ⟨v,u.property.symm⟩ p

omit [Fintype V] in
lemma mesh_sqrt_reciprocal (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (u v : V) :
    (Real.sqrt (μ u/μ v) : ℂ)*(Real.sqrt (μ v/μ u) : ℂ)=1 := by
  rw [←Complex.ofReal_mul,←Real.sqrt_mul (div_nonneg (hμ u).le (hμ v).le)]
  have hratio : μ u/μ v*(μ v/μ u)=1 := by
    field_simp [ne_of_gt (hμ u),ne_of_gt (hμ v)]
  rw [hratio,Real.sqrt_one,Complex.ofReal_one]

/-- Contracting after insertion at the preceding position is the identity.
The two weights are reciprocal positive square roots. -/
theorem meshContraction_adjacent (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (n : ℕ) (v : V) :
    meshContractionMatrix G μ (n+1) v *
      meshExtendMatrix G (fun u => (meshContractionMatrix G μ n u).conjTranspose) v =
      (1 : Matrix (MeshPaths G (n+1) v) (MeshPaths G (n+1) v) ℂ) := by
  ext p r
  rw [meshContraction_mul]
  rw [Matrix.one_apply]
  obtain ⟨u,r⟩ := r
  let f (w : {w : V // G.Adj w v}) : MeshPaths G (n+2) w.val :=
    ⟨⟨v,w.property.symm⟩,p⟩
  change (∑ w : {w : V // G.Adj w v}, (Real.sqrt (μ w/μ v) : ℂ)*
    Matrix.blockDiagonal' (fun z : {z : V // G.Adj z v} =>
      (meshContractionMatrix G μ n z.val).conjTranspose)
      ⟨w,f w⟩ ⟨u,r⟩)=_
  rw [Finset.sum_eq_single u]
  · rw [Matrix.blockDiagonal'_apply_eq,Matrix.conjTranspose_apply,meshContraction_return]
    split_ifs with h
    · rw [Complex.star_def,Complex.conj_ofReal,mesh_sqrt_reciprocal μ hμ]
    · simp
  · intro w _ hwu
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hwu,mul_zero]
  · simp

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshSpectralUpper
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-dimensional spectral bound used to choose positive mesh weights. -/
namespace HarmonicArtin.ParabolicIntersections
open Unitary
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V]

lemma mesh_spectral_upper {A : Matrix V V ℝ} (hA : A.IsHermitian) (d : ℝ)
    (hbound : ∀ i, hA.eigenvalues i≤d) :
    (d • (1 : Matrix V V ℝ)-A).PosSemidef := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal hA.eigenvalues
  have hspec : A=conjStarAlgAut ℝ _ U D := by
    simpa [U,D] using hA.spectral_theorem
  have hdiag : d • (1 : Matrix V V ℝ)-D=Matrix.diagonal (fun i => d-hA.eigenvalues i) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [D]
    · simp [D,hij]
  have hd : (d • (1 : Matrix V V ℝ)-D).PosSemidef := by
    rw [hdiag,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (hbound i)
  have he : d • (1 : Matrix V V ℝ)-A=
      conjStarAlgAut ℝ _ U (d • (1 : Matrix V V ℝ)-D) := by
    rw [map_sub,map_smul,map_one,←hspec]
  rw [he,conjStarAlgAut_apply]
  exact hd.mul_mul_conjTranspose_same _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshPerron
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative top eigenvectors, without a Perron--Frobenius axiom. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
open _root_.Matrix
variable {V : Type} [Fintype V]

lemma mesh_quadratic_abs_le (A : Matrix V V ℝ) (hA : ∀ i j, 0≤A i j)
    (x : V → ℝ) : x ⬝ᵥ (A *ᵥ x) ≤ (fun i => |x i|) ⬝ᵥ (A *ᵥ fun i => |x i|) := by
  simp only [dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_left (le_abs_self (x i*x j)) (hA i j)
  simpa only [abs_mul,mul_assoc,mul_left_comm,mul_comm] using h

lemma mesh_abs_top_eigenvector (A : Matrix V V ℝ) (hA : ∀ i j, 0≤A i j)
    (d : ℝ) (hupper : (d • (1 : Matrix V V ℝ)-A).PosSemidef)
    (x : V → ℝ) (heigen : A *ᵥ x=d • x) :
    A *ᵥ (fun i => |x i|)=d • (fun i => |x i|) := by
  let y : V → ℝ := fun i => |x i|
  have hsq : y ⬝ᵥ y=x ⬝ᵥ x := by
    simp only [dotProduct,y,←sq,sq_abs]
  have hq := mesh_quadratic_abs_le A hA x
  have hx : x ⬝ᵥ (A *ᵥ x)=d*(x ⬝ᵥ x) := by
    rw [heigen,dotProduct_smul,smul_eq_mul]
  have he : y ⬝ᵥ ((d • (1 : Matrix V V ℝ)-A) *ᵥ y)=d*(y ⬝ᵥ y)-y ⬝ᵥ (A *ᵥ y) := by
    rw [sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul]
  have hnonneg := hupper.dotProduct_mulVec_nonneg y
  simp only [star_trivial] at hnonneg
  have hz : y ⬝ᵥ ((d • (1 : Matrix V V ℝ)-A) *ᵥ y)=0 := by
    change x ⬝ᵥ (A *ᵥ x)≤y ⬝ᵥ (A *ᵥ y) at hq
    rw [he,hsq] at hnonneg ⊢
    linarith
  have hzero := (hupper.dotProduct_mulVec_zero_iff _).mp (by simpa only [star_trivial] using hz)
  rw [sub_mulVec,smul_mulVec,one_mulVec] at hzero
  exact (sub_eq_zero.mp hzero).symm

theorem mesh_nonnegative_top_eigenvector [Nonempty V] (A : Matrix V V ℝ)
    (hA : A.IsHermitian) (hpos : ∀ i j, 0≤A i j) :
    ∃ (d : ℝ) (y : V → ℝ), y≠0 ∧ (∀ i, 0≤y i) ∧ A *ᵥ y=d • y := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues Finset.univ_nonempty
  let d := hA.eigenvalues j
  let x : V → ℝ := fun i => hA.eigenvectorBasis j i
  have hx : x≠0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero j)
  have hupper : (d • (1 : Matrix V V ℝ)-A).PosSemidef :=
    mesh_spectral_upper hA d (fun i => hj i (Finset.mem_univ i))
  refine ⟨d,fun i => |x i|,?_,fun i => abs_nonneg _,?_⟩
  · intro hz
    apply hx
    funext i
    exact abs_eq_zero.mp (congrFun hz i)
  · exact mesh_abs_top_eigenvector A hpos d hupper x (hA.mulVec_eigenvectorBasis j)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshGraphWeights
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive mesh weights for a connected graph with positive Cartan form. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
open _root_.Matrix
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma mesh_adjacency_sum (y : V → ℝ) (v : V) :
    (G.adjMatrix ℝ *ᵥ y) v=∑ u : {u : V // G.Adj u v}, y u := by
  rw [G.adjMatrix_mulVec_apply]
  exact Finset.sum_subtype (G.neighborFinset v) (by intro u; simp [G.adj_comm]) y

lemma mesh_connected_eigenvector_pos (hG : G.Connected) (d : ℝ)
    (y : V → ℝ) (hy : y≠0) (hnonneg : ∀ v, 0≤y v)
    (heigen : G.adjMatrix ℝ *ᵥ y=d • y) : ∀ v, 0<y v := by
  have hzero_adj {u v : V} (hadj : G.Adj u v) (hu : y u=0) : y v=0 := by
    have hs : (∑ w : {w : V // G.Adj w u}, y w)=0 := by
      have h := congrFun heigen u
      rw [mesh_adjacency_sum] at h
      simpa only [Pi.smul_apply,smul_eq_mul,hu,mul_zero] using h
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun (w : {w : V // G.Adj w u}) _ => hnonneg w.val)).mp hs
      ⟨v,hadj.symm⟩ (Finset.mem_univ _)
  have hzero_path {u v : V} (p : G.Walk u v) : y u=0 → y v=0 := by
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => exact fun ha => ih (hzero_adj hab ha)
  intro u
  by_contra hpos
  have hu : y u=0 := le_antisymm (le_of_not_gt hpos) (hnonneg u)
  apply hy
  funext v
  exact hzero_path (hG.preconnected u v).some hu

/-- Positive definiteness of `2I-B` gives exactly the spectral interval
needed by the essential-path argument, on each nontrivial component. -/
theorem mesh_graph_positive_weights (hG : G.Connected)
    (hedge : ∃ u v, G.Adj u v)
    (hcartan : ((2 : ℝ) • (1 : Matrix V V ℝ)-G.adjMatrix ℝ).PosDef) :
    ∃ (μ : V → ℝ) (d : ℝ), (∀ v, 0<μ v) ∧ 0<d ∧ d<2 ∧
      ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=d*μ v := by
  let : Nonempty V := hG.nonempty
  have hsym : (G.adjMatrix ℝ).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact G.isSymm_adjMatrix
  have hentries : ∀ u v, 0≤G.adjMatrix ℝ u v := by
    intro u v
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  obtain ⟨d,μ,hne,hnonneg,heigen⟩ := mesh_nonnegative_top_eigenvector (G.adjMatrix ℝ) hsym hentries
  have hμ := mesh_connected_eigenvector_pos G hG d μ hne hnonneg heigen
  have heq (v : V) : (∑ u : {u : V // G.Adj u v}, μ u)=d*μ v := by
    have h := congrFun heigen v
    simpa only [mesh_adjacency_sum,Pi.smul_apply,smul_eq_mul] using h
  obtain ⟨u,v,huv⟩ := hedge
  have hsum : 0<(∑ w : {w : V // G.Adj w v}, μ w) := by
    exact Finset.sum_pos' (fun w _ => (hμ w).le)
      ⟨⟨u,huv⟩,Finset.mem_univ _,hμ u⟩
  have hd : 0<d := by
    rw [heq] at hsum
    exact (mul_pos_iff.mp hsum).resolve_right (by intro h; exact (not_lt_of_ge (hμ v).le) h.2) |>.1
  have hform := hcartan.dotProduct_mulVec_pos hne
  simp only [star_trivial,sub_mulVec,smul_mulVec,one_mulVec,heigen,
    dotProduct_sub,dotProduct_smul,smul_eq_mul] at hform
  have hsq : 0≤μ ⬝ᵥ μ := Finset.sum_nonneg (fun i _ => mul_self_nonneg (μ i))
  have hd2 : d<2 := by
    by_contra h
    have hm : d*(μ ⬝ᵥ μ)≥2*(μ ⬝ᵥ μ) := mul_le_mul_of_nonneg_right (le_of_not_gt h) hsq
    linarith
  exact ⟨μ,d,hμ,hd,hd2,heq⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshMatrixAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluating complex path matrices in an arbitrary complex module. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I J K R : Type} [Fintype I] [Fintype J] [Fintype K]
variable [AddCommGroup R] [Module ℂ R]

omit [Fintype J] [Fintype K] in
lemma meshApply_sub (A B : Matrix I J ℂ) (f : I → R) :
    meshApply (A-B) f=meshApply A f-meshApply B f := by
  funext q
  simp only [meshApply,Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib,Pi.sub_apply]

omit [Fintype J] [Fintype K] in
lemma meshApply_smul (a : ℂ) (A : Matrix I J ℂ) (f : I → R) :
    meshApply (a • A) f=a • meshApply A f := by
  funext q
  simp only [meshApply,Matrix.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,Pi.smul_apply]

omit [Fintype K] in
lemma meshApply_mul (A : Matrix I J ℂ) (B : Matrix J K ℂ) (f : I → R) :
    meshApply (A*B) f=meshApply B (meshApply A f) := by
  funext q
  simp only [meshApply,Matrix.mul_apply,Finset.sum_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_comm]

omit [Fintype J] [Fintype K] in
lemma meshApply_one (f : I → R) : meshApply (1 : Matrix I I ℂ) f=f := by
  funext q
  simp [meshApply,Matrix.one_apply]

omit [Fintype J] [Fintype K] in
lemma meshApply_zero (f : I → R) : meshApply (0 : Matrix I J ℂ) f=0 := by
  funext q
  simp [meshApply]

omit [Fintype J] [Fintype K] in
lemma meshApply_zero_right (A : Matrix I J ℂ) : meshApply A (0 : I → R)=0 := by
  funext q
  simp [meshApply]

variable {V : Type} [Fintype V] (G : SimpleGraph V)

omit [Fintype I] [Fintype J] [Fintype K] in
/-- Extending a prefix matrix commutes with a linear last-edge operation. -/
lemma meshApply_extend {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ)
    (f : ∀ v, MeshPaths G m v → R) (v : V)
    (L : ∀ _u : {u : V // G.Adj u v}, R →ₗ[ℂ] R) :
    meshApply (meshExtendMatrix G A v)
      (fun p : MeshPaths G (m+1) v => L p.1 (f p.1.val p.2)) =
      fun q : MeshPaths G (n+1) v => L q.1 (meshApply (A q.1.val) (f q.1.val) q.2) := by
  funext q
  obtain ⟨u,q⟩ := q
  change (∑ p : Σ w : {w : V // G.Adj w v}, MeshPaths G m w.val,
    Matrix.blockDiagonal' (fun w : {w : V // G.Adj w v} => A w.val) p ⟨u,q⟩ •
      L p.1 (f p.1.val p.2))=_
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single u]
  · simp only [Matrix.blockDiagonal'_apply_eq,meshApply,map_sum,map_smul]
  · intro w _ hwu
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hwu,zero_smul]
  · simp

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshNaturality
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prefix operator commutes with contraction of the final backtrack. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma meshContraction_insert (μ : V → ℝ) (n : ℕ) (v : V)
    (p q : MeshPaths G n v) (u : {u : V // G.Adj u v}) :
    meshContractionMatrix G μ n v p (meshInsertBacktrack G u q)=
      if q=p then (Real.sqrt (μ u/μ v) : ℂ) else 0 := by
  calc
    _ = @ite ℂ ((⟨⟨v,u.property.symm⟩,q⟩ : MeshPaths G (n+1) u.val)=
        ⟨⟨v,u.property.symm⟩,p⟩) (Classical.propDecidable _)
        (Real.sqrt (μ u/μ v) : ℂ) 0 :=
      meshContraction_head G μ n v p u ⟨⟨v,u.property.symm⟩,q⟩
    _ = _ := by
      have he : (⟨⟨v,u.property.symm⟩,q⟩ : MeshPaths G (n+1) u.val)=
          ⟨⟨v,u.property.symm⟩,p⟩ ↔ q=p := by
        constructor
        · intro h
          exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
        · rintro rfl
          rfl
      simp only [he]

lemma meshContraction_no_return (μ : V → ℝ) (n : ℕ) (v : V)
    (p : MeshPaths G n v) (u : {u : V // G.Adj u v})
    (w : {w : V // G.Adj w u.val}) (q : MeshPaths G n w.val) (hw : w.val≠v) :
    meshContractionMatrix G μ n v p ⟨u,⟨w,q⟩⟩=0 := by
  calc
    _ = @ite ℂ ((⟨w,q⟩ : MeshPaths G (n+1) u.val)=⟨⟨v,u.property.symm⟩,p⟩)
      (Classical.propDecidable _) (Real.sqrt (μ u/μ v) : ℂ) 0 :=
        meshContraction_head G μ n v p u ⟨w,q⟩
    _ = 0 := by
      apply ite_eq_right
      intro he
      exact hw (congrArg (fun z => (Sigma.fst z).val) he)

omit [Fintype V] in
lemma meshExtend_twice_insert {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V)
    (p : MeshPaths G m v) (q : MeshPaths G n v)
    (u w : {u : V // G.Adj u v}) :
    meshExtendMatrix G (meshExtendMatrix G A) v
      (meshInsertBacktrack G u p) (meshInsertBacktrack G w q)=
        if u=w then A v p q else 0 := by
  let lp : MeshPaths G (m+1) u.val := ⟨⟨v,u.property.symm⟩,p⟩
  let rp : MeshPaths G (n+1) w.val := ⟨⟨v,w.property.symm⟩,q⟩
  change Matrix.blockDiagonal' (fun z : {z : V // G.Adj z v} =>
    meshExtendMatrix G A z.val) ⟨u,lp⟩ ⟨w,rp⟩=_
  by_cases h : u=w
  · subst w
    rw [Matrix.blockDiagonal'_apply_eq,ite_eq_left rfl]
    change Matrix.blockDiagonal' (fun z : {z : V // G.Adj z u.val} => A z.val)
      ⟨⟨v,u.property.symm⟩,p⟩ ⟨⟨v,u.property.symm⟩,q⟩=_
    exact Matrix.blockDiagonal'_apply_eq _ _ _ _
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,ite_eq_right h]

omit [Fintype V] in
lemma meshExtend_twice_no_return {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V)
    (p : MeshPaths G m v) (u w : {u : V // G.Adj u v})
    (x : {x : V // G.Adj x w.val}) (q : MeshPaths G n x.val) (hx : x.val≠v) :
    meshExtendMatrix G (meshExtendMatrix G A) v
      (meshInsertBacktrack G u p) ⟨w,⟨x,q⟩⟩=0 := by
  let lp : MeshPaths G (m+1) u.val := ⟨⟨v,u.property.symm⟩,p⟩
  let rp : MeshPaths G (n+1) w.val := ⟨x,q⟩
  change Matrix.blockDiagonal' (fun z : {z : V // G.Adj z v} =>
    meshExtendMatrix G A z.val) ⟨u,lp⟩ ⟨w,rp⟩=0
  by_cases h : u=w
  · subst w
    rw [Matrix.blockDiagonal'_apply_eq]
    change Matrix.blockDiagonal' (fun z : {z : V // G.Adj z u.val} => A z.val)
      ⟨⟨v,u.property.symm⟩,p⟩ ⟨x,q⟩=0
    apply Matrix.blockDiagonal'_apply_ne
    intro he
    exact hx (congrArg Subtype.val he).symm
  · exact Matrix.blockDiagonal'_apply_ne _ _ _ h

/-- No property of the prefix operator is needed: the final pair is
disjoint from it, so contraction is natural for every endpoint family. -/
theorem meshContraction_naturality (μ : V → ℝ) {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshContractionMatrix G μ m v * meshExtendMatrix G (meshExtendMatrix G A) v =
      A v * meshContractionMatrix G μ n v := by
  ext p r
  rw [meshContraction_mul]
  obtain ⟨u,w,q⟩ := r
  by_cases hw : w.val=v
  · have he : w=⟨v,u.property.symm⟩ := Subtype.ext hw
    subst w
    change (∑ x : {x : V // G.Adj x v}, (Real.sqrt (μ x/μ v) : ℂ)*
      meshExtendMatrix G (meshExtendMatrix G A) v
        (meshInsertBacktrack G x p) (meshInsertBacktrack G u q))=_
    simp only [meshExtend_twice_insert,mul_ite,mul_zero]
    rw [Finset.sum_ite_eq']
    change _ = ∑ t : MeshPaths G n v,
      A v p t * meshContractionMatrix G μ n v t (meshInsertBacktrack G u q)
    simp only [meshContraction_insert,mul_ite,mul_zero]
    simp [mul_comm]
  · change (∑ x : {x : V // G.Adj x v}, (Real.sqrt (μ x/μ v) : ℂ)*
      meshExtendMatrix G (meshExtendMatrix G A) v
        (meshInsertBacktrack G x p) ⟨u,⟨w,q⟩⟩)=_
    simp only [meshExtend_twice_no_return G A v p _ u w q hw,mul_zero,Finset.sum_const_zero]
    change 0 = ∑ t : MeshPaths G n v,
      A v p t * meshContractionMatrix G μ n v t ⟨u,⟨w,q⟩⟩
    simp only [meshContraction_no_return G μ n v _ u w q hw,mul_zero,Finset.sum_const_zero]

theorem meshContraction_adjacent_right (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (n : ℕ) (v : V) :
    meshExtendMatrix G (meshContractionMatrix G μ n) v *
      (meshContractionMatrix G μ (n+1) v).conjTranspose=1 := by
  have h := congrArg Matrix.conjTranspose (meshContraction_adjacent G μ hμ n v)
  simpa only [Matrix.conjTranspose_mul,meshExtend_adjoint,
    Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_one] using h

theorem meshContraction_naturality_adjoint (μ : V → ℝ) {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    meshExtendMatrix G (meshExtendMatrix G A) v *
      (meshContractionMatrix G μ n v).conjTranspose=
        (meshContractionMatrix G μ m v).conjTranspose*A v := by
  have h := congrArg Matrix.conjTranspose
    (meshContraction_naturality G μ (fun v => (A v).conjTranspose) v)
  simpa only [Matrix.conjTranspose_mul,meshExtend_adjoint,
    Matrix.conjTranspose_conjTranspose] using h

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshQuantum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite positivity interval for the Jones--Wenzl scalar recurrence. -/
namespace HarmonicArtin.ParabolicIntersections

lemma meshQuantum_step (δ : ℝ) (n : ℕ) :
    meshQuantum δ (n+2)=δ*meshQuantum δ (n+1)-meshQuantum δ n := rfl

/-- For `δ<2`, the recurrence starting at `0,1` cannot remain strictly
positive. This discrete concavity proof avoids choosing an angle. -/
theorem mesh_quantum_eventually_nonpositive (δ : ℝ) (hδ : δ<2)
    (q : ℕ → ℝ) (hzero : q 0=0) (hone : q 1=1)
    (hrec : ∀ n, q (n+2)=δ*q (n+1)-q n) :
    ∃ n, 0<n ∧ q n≤0 := by
  by_contra hex
  have hpos : ∀ n, 0<n → 0<q n := by
    intro n hn
    by_contra hq
    exact hex ⟨n,hn,le_of_not_gt hq⟩
  have hnonneg : ∀ n, 0≤q n := by
    intro n
    cases n with
    | zero => rw [hzero]
    | succ n => exact (hpos _ (Nat.succ_pos n)).le
  let d : ℕ → ℝ := fun n => q (n+1)-q n
  have hd0 : d 0=1 := by simp only [d,hzero,hone] <;> norm_num
  have hstep : ∀ n, d (n+1)=d n-(2-δ)*q (n+1) := by
    intro n
    dsimp [d]
    rw [show n+1+1=n+2 by omega,hrec]
    ring
  have hanti : Antitone d := antitone_nat_of_succ_le (fun n => by
    rw [hstep]
    have := hnonneg (n+1)
    nlinarith)
  have hnegative : ∃ n, d n<0 := by
    by_contra hneg
    have hdpos : ∀ n, 0≤d n := by
      intro n
      by_contra hn
      exact hneg ⟨n,lt_of_not_ge hn⟩
    have hmono : Monotone q := monotone_nat_of_le_succ (fun n => by
      have := hdpos n
      dsimp [d] at this
      linarith)
    have hqone : ∀ n, 1≤q (n+1) := by
      intro n
      simpa only [hone] using hmono (Nat.le_add_left 1 n)
    have hbound : ∀ n, d n≤1-(n:ℝ)*(2-δ) := by
      intro n
      induction n with
      | zero => simp only [Nat.cast_zero,zero_mul,sub_zero,hd0,le_refl]
      | succ n ih =>
        rw [hstep,Nat.cast_succ]
        have := hqone n
        nlinarith
    obtain ⟨n,hn⟩ := exists_nat_gt (1/(2-δ))
    have hden : 0<2-δ := by linarith
    have hn' : 1<(n:ℝ)*(2-δ) := (div_lt_iff₀ hden).mp hn
    have := hbound n
    have := hdpos n
    linarith
  obtain ⟨n,hn⟩ := hnegative
  have hlinear : ∀ k, q (n+k)≤q n+(k:ℝ)*d n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hanti (Nat.le_add_right n k)
      have he : q (n+(k+1))=q (n+k)+d (n+k) := by dsimp [d]; simp only [Nat.add_assoc] <;> ring
      rw [he,Nat.cast_succ]
      linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (q n/(-d n))
  have hdneg : 0 < -d n := by linarith
  have hk' : q n<(k:ℝ)*(-d n) := (div_lt_iff₀ hdneg).mp hk
  have := hlinear k
  have := hnonneg (n+k)
  nlinarith

/-- The first nonpositive scalar gives a finite cutoff, and all earlier
nonzero-index scalars are positive, as required by the projection recursion. -/
theorem mesh_quantum_cutoff (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2)
    (q : ℕ → ℝ) (hzero : q 0=0) (hone : q 1=1)
    (hrec : ∀ n, q (n+2)=δ*q (n+1)-q n) :
    ∃ h, 3≤h ∧ q h≤0 ∧ ∀ n, 0<n → n<h → 0<q n := by
  classical
  have hex := mesh_quantum_eventually_nonpositive δ hδ2 q hzero hone hrec
  let h := Nat.find hex
  have hh : 0<h ∧ q h≤0 := Nat.find_spec hex
  have hp : ∀ n, 0<n → n<h → 0<q n := by
    intro n hn hnh
    have hnot := Nat.find_min hex hnh
    exact lt_of_not_ge (fun hqn => hnot ⟨hn,hqn⟩)
  have htwo : q 2=δ := by simpa only [zero_add,hzero,hone,mul_one,sub_zero] using hrec 0
  have hge : 3≤h := by
    by_contra hlt
    have he : h=1 ∨ h=2 := by omega
    rcases he with he|he
    · have := hh.2; rw [he,hone] at this; linarith
    · have := hh.2; rw [he,htwo] at this; linarith
  exact ⟨h,hge,hh.2,hp⟩

theorem meshQuantum_cutoff (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2) :
    ∃ h, 3≤h ∧ meshQuantum δ h≤0 ∧
      ∀ n, 0 < n → n < h → 0 < meshQuantum δ n :=
  mesh_quantum_cutoff δ hδ0 hδ2 (meshQuantum δ)
    (meshQuantum_zero δ) (meshQuantum_one δ) (meshQuantum_step δ)

lemma meshQuantum_ratio_step (δ : ℝ) (n : ℕ) (h : meshQuantum δ (n+2)≠0) :
    δ-(meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹=
      meshQuantum δ (n+3)/meshQuantum δ (n+2) := by
  have hrec : meshQuantum δ (n+3)=δ*meshQuantum δ (n+2)-meshQuantum δ (n+1) :=
    meshQuantum_step δ (n+1)
  rw [inv_div,hrec]
  field_simp [h]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshProjectionAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional projection calculation in the mesh argument. -/
namespace HarmonicArtin.ParabolicIntersections
open scoped ComplexOrder
attribute [local instance] Classical.decEq
variable {I J : Type} [Fintype I] [Fintype J]

/-- The loop, adjacent, and prefix identities give the next scalar in
the projection recurrence. -/
theorem mesh_scalar_step (C D : Matrix I J ℂ) (P : Matrix I I ℂ)
    (R : Matrix J J ℂ) (delta a : ℂ)
    (hPsq : P*P=P) (hCR : C*R=P*C) (hRC : R*C.conjTranspose=C.conjTranspose*P)
    (hloop : C*C.conjTranspose=delta • (1 : Matrix I I ℂ))
    (hadj : C*D.conjTranspose=1) (hadj' : D*C.conjTranspose=1) :
    C*(R-a • (R*D.conjTranspose*D*R))*C.conjTranspose=(delta-a) • P := by
  have hfirst : C*R*C.conjTranspose=delta • P := by
    rw [hCR,Matrix.mul_assoc,hloop,Matrix.mul_smul,Matrix.mul_one]
  have hsecond : C*(R*D.conjTranspose*D*R)*C.conjTranspose=P := by
    calc
      _ = (C*R)*D.conjTranspose*D*(R*C.conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = (P*C)*D.conjTranspose*D*(C.conjTranspose*P) := by rw [hCR,hRC]
      _ = P*(C*D.conjTranspose)*(D*C.conjTranspose)*P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hadj,hadj',Matrix.mul_one,Matrix.mul_one,hPsq]
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    hfirst,hsecond,sub_smul]

/-- Removing the scaled row-space projection imposes one more contraction.
All hypotheses here are matrix identities, proved for the path operators
in the mesh construction. -/
theorem mesh_projection_correction (Q : Matrix I I ℂ) (T : Matrix J I ℂ)
    (P : Matrix J J ℂ) (lam : ℝ) (hlam : lam≠0)
    (hQstar : Q.conjTranspose=Q) (hQsq : Q*Q=Q)
    (hTQ : T*Q=T) (hTT : T*T.conjTranspose=(lam : ℂ) • P) (hPT : P*T=T) :
    let R := Q - ((lam⁻¹ : ℝ) : ℂ) • (T.conjTranspose*T)
    R.conjTranspose=R ∧ R*R=R ∧ R*Q=R ∧ T*R=0 ∧
      Matrix.trace R=Matrix.trace Q-Matrix.trace P := by
  let a : ℂ := (lam⁻¹ : ℝ)
  let B : Matrix I I ℂ := a • (T.conjTranspose*T)
  have ha : a*(lam : ℂ)=1 := by
    dsimp [a]
    rw [←Complex.ofReal_mul,inv_mul_cancel₀ hlam,Complex.ofReal_one]
  have hQT : Q*T.conjTranspose=T.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hTQ
    simpa only [Matrix.conjTranspose_mul,hQstar] using h
  have hQB : Q*B=B := by
    dsimp [B]
    rw [Matrix.mul_smul,←Matrix.mul_assoc,hQT]
  have hBQ : B*Q=B := by
    dsimp [B]
    rw [Matrix.smul_mul,Matrix.mul_assoc,hTQ]
  have hBT : T*B=T := by
    dsimp [B]
    rw [Matrix.mul_smul,←Matrix.mul_assoc,hTT,Matrix.smul_mul,hPT,smul_smul,ha,one_smul]
  have hBB : B*B=B := by
    dsimp [B]
    rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc,
      ←Matrix.mul_assoc T T.conjTranspose T,hTT,Matrix.smul_mul,hPT,
      Matrix.mul_smul,smul_smul,smul_smul]
    rw [mul_assoc,ha,mul_one]
  have hBstar : B.conjTranspose=B := by
    simp only [B,a,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,Complex.star_def,Complex.conj_ofReal]
  have htrace : Matrix.trace B=Matrix.trace P := by
    dsimp [B]
    rw [Matrix.trace_smul,Matrix.trace_mul_comm,hTT,Matrix.trace_smul,smul_smul,ha,one_smul]
  change (Q-B).conjTranspose=Q-B ∧ (Q-B)*(Q-B)=Q-B ∧
    (Q-B)*Q=Q-B ∧ T*(Q-B)=0 ∧ Matrix.trace (Q-B)=_
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [Matrix.conjTranspose_sub,hQstar,hBstar]
  · rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hQsq,hQB,hBQ,hBB]
    abel
  · rw [Matrix.sub_mul,hQsq,hBQ]
  · rw [Matrix.mul_sub,hTQ,hBT,sub_self]
  · rw [Matrix.trace_sub,htrace]

/-- A self-adjoint idempotent is positive, and trace zero forces it to
vanish. These are the positivity facts used at the scalar cutoff. -/
theorem mesh_projection_trace (P : Matrix I I ℂ)
    (hstar : P.conjTranspose=P) (hsq : P*P=P) :
    0≤(Matrix.trace P).re ∧ (Matrix.trace P=0 ↔ P=0) := by
  have hpos : P.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [hstar,hsq] at h
  have hz := Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := P)
  rw [hstar,hsq] at hz
  exact ⟨(Complex.nonneg_iff.mp hpos.trace_nonneg).1,hz⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshTrace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive weighted traces detect vanishing of all endpoint projections. -/
namespace HarmonicArtin.ParabolicIntersections
open scoped ComplexOrder
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V]

lemma meshWeightedTrace_nonneg {D : V → Type} [∀ v, Fintype (D v)]
    (μ : V → ℝ) (hμ : ∀ v, 0≤μ v) (P : ∀ v, Matrix (D v) (D v) ℂ)
    (hstar : ∀ v, (P v).conjTranspose=P v) (hsq : ∀ v, P v*P v=P v) :
    0≤(meshWeightedTrace μ P).re := by
  simp only [meshWeightedTrace,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact Finset.sum_nonneg (fun v _ => mul_nonneg (hμ v)
    (mesh_projection_trace (P v) (hstar v) (hsq v)).1)

/-- Strict positivity of the vertex weights turns a zero weighted trace
of orthogonal projections into the vanishing of each projection. -/
theorem meshWeightedTrace_zero {D : V → Type} [∀ v, Fintype (D v)]
    (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (P : ∀ v, Matrix (D v) (D v) ℂ)
    (hstar : ∀ v, (P v).conjTranspose=P v) (hsq : ∀ v, P v*P v=P v)
    (hz : meshWeightedTrace μ P=0) : ∀ v, P v=0 := by
  have hpos : ∀ v, (P v).PosSemidef := by
    intro v
    have h := Matrix.posSemidef_conjTranspose_mul_self (P v)
    rwa [hstar v,hsq v] at h
  have ht : ∀ v, 0≤(Matrix.trace (P v)).re := fun v =>
    (Complex.nonneg_iff.mp (hpos v).trace_nonneg).1
  have hsum : (∑ v, μ v*(Matrix.trace (P v)).re)=0 := by
    have h := congrArg Complex.re hz
    simpa only [meshWeightedTrace,Complex.re_sum,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.zero_re] using h
  have heach := Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v∈Finset.univ) => mul_nonneg (hμ v).le (ht v))
  intro v
  have hv : μ v*(Matrix.trace (P v)).re=0 := heach.mp hsum v (Finset.mem_univ v)
  have hreal : (Matrix.trace (P v)).re=0 :=
    (mul_eq_zero.mp hv).resolve_left (ne_of_gt (hμ v))
  have himag : (Matrix.trace (P v)).im=0 :=
    (Complex.nonneg_iff.mp (hpos v).trace_nonneg).2.symm
  have htrace : Matrix.trace (P v)=0 := Complex.ext hreal himag
  exact (mesh_projection_trace (P v) (hstar v) (hsq v)).2.mp htrace

variable (G : SimpleGraph V)

lemma meshExtend_trace {n : ℕ}
    (P : ∀ v, Matrix (MeshPaths G n v) (MeshPaths G n v) ℂ) (v : V) :
    Matrix.trace (meshExtendMatrix G P v)=
      ∑ u : {u : V // G.Adj u v}, Matrix.trace (P u.val) := by
  exact Matrix.trace_blockDiagonal' _

/-- Extension multiplies the weighted trace by the Perron eigenvalue. -/
lemma meshWeightedTrace_extend (μ : V → ℝ) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    {n : ℕ} (P : ∀ v, Matrix (MeshPaths G n v) (MeshPaths G n v) ℂ) :
    meshWeightedTrace μ (meshExtendMatrix G P)=
      (δ : ℂ)*meshWeightedTrace μ P := by
  unfold meshWeightedTrace
  simp_rw [meshExtend_trace]
  conv_lhs => simp only [Finset.mul_sum]
  rw [←Fintype.sum_sigma (fun p : Σ v : V, {u : V // G.Adj u v} =>
    (μ p.1 : ℂ)*Matrix.trace (P p.2.val))]
  calc
    (∑ p : Σ v : V, {u : V // G.Adj u v},
        (μ p.1 : ℂ)*Matrix.trace (P p.2.val)) =
      ∑ p : Σ v : V, {u : V // G.Adj u v},
        (μ p.2.val : ℂ)*Matrix.trace (P p.1) := by
          apply Fintype.sum_equiv (meshEdgeFlip G)
          intro p
          rfl
    _ = ∑ v, (∑ u : {u : V // G.Adj u v}, (μ u : ℂ))*Matrix.trace (P v) := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_mul]
    _ = (δ : ℂ)*∑ v, (μ v : ℂ)*Matrix.trace (P v) := by
      simp_rw [←Complex.ofReal_sum,heigen,Complex.ofReal_mul,mul_assoc]
      rw [Finset.mul_sum]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshProjection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jones--Wenzl projections on the actual finite path spaces. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma meshProjection_zero (μ : V → ℝ) (δ : ℝ) (v : V) :
    meshProjection G μ δ 0 v=1 := rfl

lemma meshProjection_one (μ : V → ℝ) (δ : ℝ) (v : V) :
    meshProjection G μ δ 1 v=1 := rfl

lemma meshProjection_step (μ : V → ℝ) (δ : ℝ) (n : ℕ) (v : V) :
    meshProjection G μ δ (n+2) v =
      let Q := meshExtendMatrix G (meshProjection G μ δ (n+1)) v
      let T := meshContractionMatrix G μ n v*Q
      Q - (((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
        (T.conjTranspose*T) := rfl

/-- Self-adjointness uses only the real coefficients in the recursion;
it holds even beyond the range in which the matrices are projections. -/
theorem meshProjection_selfAdjoint (μ : V → ℝ) (δ : ℝ) :
    ∀ n v, (meshProjection G μ δ n v).conjTranspose=meshProjection G μ δ n v := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro v; rw [meshProjection_zero,Matrix.conjTranspose_one]
  | one => intro v; rw [meshProjection_one,Matrix.conjTranspose_one]
  | more n _ ih =>
    intro v
    have hQ : (meshExtendMatrix G (meshProjection G μ δ (n+1)) v).conjTranspose=
        meshExtendMatrix G (meshProjection G μ δ (n+1)) v := by
      simp only [meshExtend_adjoint,ih]
    rw [meshProjection_step,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hQ]
    simp only [Complex.star_def,Complex.conj_ofReal]

/-- One step of the actual recursion, once its scalar identity has been
established from the preceding path identities. -/
theorem meshProjection_correct (μ : V → ℝ) (δ : ℝ) (n : ℕ) (v : V)
    (hden : meshQuantum δ (n+2)/meshQuantum δ (n+1)≠0)
    (hQstar : (meshExtendMatrix G (meshProjection G μ δ (n+1)) v).conjTranspose=
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v)
    (hQsq : meshExtendMatrix G (meshProjection G μ δ (n+1)) v *
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v=
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v)
    (hscalar : meshContractionMatrix G μ n v *
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v *
      (meshContractionMatrix G μ n v).conjTranspose =
      ((meshQuantum δ (n+2)/meshQuantum δ (n+1) : ℝ) : ℂ) • meshProjection G μ δ n v)
    (himage : meshProjection G μ δ n v * (meshContractionMatrix G μ n v *
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v)=
      meshContractionMatrix G μ n v * meshExtendMatrix G (meshProjection G μ δ (n+1)) v) :
    (meshProjection G μ δ (n+2) v).conjTranspose=meshProjection G μ δ (n+2) v ∧
      meshProjection G μ δ (n+2) v * meshProjection G μ δ (n+2) v=
        meshProjection G μ δ (n+2) v ∧
      meshProjection G μ δ (n+2) v * meshExtendMatrix G (meshProjection G μ δ (n+1)) v=
        meshProjection G μ δ (n+2) v ∧
      meshContractionMatrix G μ n v * meshProjection G μ δ (n+2) v=0 ∧
      Matrix.trace (meshProjection G μ δ (n+2) v)=
        Matrix.trace (meshExtendMatrix G (meshProjection G μ δ (n+1)) v)-
          Matrix.trace (meshProjection G μ δ n v) := by
  let Q := meshExtendMatrix G (meshProjection G μ δ (n+1)) v
  let C := meshContractionMatrix G μ n v
  change Q.conjTranspose=Q at hQstar
  change Q*Q=Q at hQsq
  have hTQ : (C*Q)*Q=C*Q := by rw [Matrix.mul_assoc,hQsq]
  have hTT : (C*Q)*(C*Q).conjTranspose=
      ((meshQuantum δ (n+2)/meshQuantum δ (n+1) : ℝ) : ℂ) • meshProjection G μ δ n v := by
    rw [Matrix.conjTranspose_mul,hQstar,Matrix.mul_assoc,←Matrix.mul_assoc Q,hQsq,
      ←Matrix.mul_assoc]
    exact hscalar
  obtain ⟨hstar,hsq,hnest,hkill,htrace⟩ := mesh_projection_correction Q (C*Q)
    (meshProjection G μ δ n v) (meshQuantum δ (n+2)/meshQuantum δ (n+1))
    hden hQstar hQsq hTQ hTT himage
  rw [meshProjection_step]
  dsimp only
  refine ⟨hstar,hsq,hnest,?_,htrace⟩
  have hleft : Q*(Q-(((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
      ((C*Q).conjTranspose*(C*Q)))=
      Q-(((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
        ((C*Q).conjTranspose*(C*Q)) := by
    have h := congrArg Matrix.conjTranspose hnest
    rw [Matrix.conjTranspose_mul,hQstar,hstar] at h
    exact h
  change C*(Q-(((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
    ((C*Q).conjTranspose*(C*Q)))=0
  rw [←hleft,←Matrix.mul_assoc]
  exact hkill

lemma meshProjection_extend_step (μ : V → ℝ) (δ : ℝ) (n : ℕ) (v : V)
    (hstar : ∀ w, (meshProjection G μ δ (n+1) w).conjTranspose=
      meshProjection G μ δ (n+1) w) :
    let R := meshExtendMatrix G (meshExtendMatrix G (meshProjection G μ δ (n+1))) v
    let D := meshExtendMatrix G (meshContractionMatrix G μ n) v
    meshExtendMatrix G (meshProjection G μ δ (n+2)) v =
      R-(((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
        (R*D.conjTranspose*D*R) := by
  dsimp only
  have hRstar : (meshExtendMatrix G (meshExtendMatrix G
      (meshProjection G μ δ (n+1))) v).conjTranspose=
      meshExtendMatrix G (meshExtendMatrix G (meshProjection G μ δ (n+1))) v := by
    simp only [meshExtend_adjoint,hstar]
  rw [funext (meshProjection_step G μ δ n)]
  simp only [meshExtend_sub,meshExtend_smul,
    meshExtend_mul,←meshExtend_adjoint,Matrix.conjTranspose_mul]
  rw [hRstar]
  simp only [Matrix.mul_assoc]

lemma meshProjection_scalar_zero (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v) (v : V) :
    meshContractionMatrix G μ 0 v * meshExtendMatrix G (meshProjection G μ δ 1) v *
      (meshContractionMatrix G μ 0 v).conjTranspose =
      ((meshQuantum δ 2/meshQuantum δ 1 : ℝ) : ℂ) • meshProjection G μ δ 0 v := by
  have hPone : meshProjection G μ δ 1=fun v =>
      (1 : Matrix (MeshPaths G 1 v) (MeshPaths G 1 v) ℂ) :=
    funext (meshProjection_one G μ δ)
  have hq : meshQuantum δ 2/meshQuantum δ 1=δ := by norm_num [meshQuantum]
  rw [hq,meshProjection_zero,hPone,meshExtend_one,Matrix.mul_one]
  exact meshContraction_loop G μ hμ δ heigen 0 v

lemma meshProjection_scalar_succ (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (n : ℕ) (hq : meshQuantum δ (n+2)≠0)
    (hstar : ∀ w, (meshProjection G μ δ (n+1) w).conjTranspose=
      meshProjection G μ δ (n+1) w)
    (hsq : ∀ w, meshProjection G μ δ (n+1) w * meshProjection G μ δ (n+1) w=
      meshProjection G μ δ (n+1) w) (v : V) :
    meshContractionMatrix G μ (n+1) v *
      meshExtendMatrix G (meshProjection G μ δ (n+2)) v *
      (meshContractionMatrix G μ (n+1) v).conjTranspose =
      ((meshQuantum δ (n+3)/meshQuantum δ (n+2) : ℝ) : ℂ) •
        meshProjection G μ δ (n+1) v := by
  rw [meshProjection_extend_step G μ δ n v hstar]
  have h := mesh_scalar_step (meshContractionMatrix G μ (n+1) v)
    (meshExtendMatrix G (meshContractionMatrix G μ n) v)
    (meshProjection G μ δ (n+1) v)
    (meshExtendMatrix G (meshExtendMatrix G (meshProjection G μ δ (n+1))) v)
    (δ : ℂ) (((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ)
    (hsq v) (meshContraction_naturality G μ (meshProjection G μ δ (n+1)) v)
    (meshContraction_naturality_adjoint G μ (meshProjection G μ δ (n+1)) v)
    (meshContraction_loop G μ hμ δ heigen (n+1) v)
    (by simpa only [meshExtend_adjoint] using meshContraction_adjacent G μ hμ n v)
    (meshContraction_adjacent_right G μ hμ n v)
  rw [←Complex.ofReal_sub,meshQuantum_ratio_step δ n hq] at h
  exact h

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshProjectionInduction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Jones--Wenzl induction before the first nonpositive quantum integer. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

theorem meshProjectionStage_zero (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v) :
    MeshProjectionStage G μ δ 0 where
  lower_star v := by simp only [meshProjection_zero,Matrix.conjTranspose_one]
  lower_square v := by simp only [meshProjection_zero,Matrix.one_mul]
  upper_star v := by
    change (1 : Matrix (MeshPaths G 1 v) (MeshPaths G 1 v) ℂ).conjTranspose=1
    exact Matrix.conjTranspose_one
  upper_square v := by
    change (1 : Matrix (MeshPaths G 1 v) (MeshPaths G 1 v) ℂ)*1=1
    exact Matrix.one_mul 1
  nested v := by
    rw [funext (meshProjection_zero G μ δ),meshExtend_one]
    exact Matrix.mul_one _
  scalar := meshProjection_scalar_zero G μ hμ δ heigen
  trace_recurrence hn := (hn rfl).elim

theorem meshProjectionStage_succ (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (n : ℕ) (h : MeshProjectionStage G μ δ n)
    (hq₁ : meshQuantum δ (n+1)≠0) (hq₂ : meshQuantum δ (n+2)≠0) :
    MeshProjectionStage G μ δ (n+1) := by
  have hQstar (v : V) :
      (meshExtendMatrix G (meshProjection G μ δ (n+1)) v).conjTranspose=
        meshExtendMatrix G (meshProjection G μ δ (n+1)) v := by
    simp only [meshExtend_adjoint,h.upper_star]
  have hQsq (v : V) : meshExtendMatrix G (meshProjection G μ δ (n+1)) v *
      meshExtendMatrix G (meshProjection G μ δ (n+1)) v=
        meshExtendMatrix G (meshProjection G μ δ (n+1)) v := by
    rw [←meshExtend_mul]
    simp only [h.upper_square]
  have himage (v : V) : meshProjection G μ δ n v *
      (meshContractionMatrix G μ n v * meshExtendMatrix G (meshProjection G μ δ (n+1)) v)=
      meshContractionMatrix G μ n v * meshExtendMatrix G (meshProjection G μ δ (n+1)) v := by
    let R := meshExtendMatrix G (meshExtendMatrix G (meshProjection G μ δ n)) v
    let Q := meshExtendMatrix G (meshProjection G μ δ (n+1)) v
    let C := meshContractionMatrix G μ n v
    have hRstar : R.conjTranspose=R := by simp only [R,meshExtend_adjoint,h.lower_star]
    have hQR : Q*R=Q := by
      dsimp only [Q,R]
      rw [←meshExtend_mul]
      simp only [h.nested]
    have hRQ : R*Q=Q := by
      have hh := congrArg Matrix.conjTranspose hQR
      rw [Matrix.conjTranspose_mul,hRstar,hQstar] at hh
      exact hh
    have hCR : C*R=meshProjection G μ δ n v*C :=
      meshContraction_naturality G μ (meshProjection G μ δ n) v
    change meshProjection G μ δ n v*(C*Q)=C*Q
    rw [←Matrix.mul_assoc,←hCR,Matrix.mul_assoc,hRQ]
  have hnew (v : V) := meshProjection_correct G μ δ n v
    (div_ne_zero hq₂ hq₁) (hQstar v) (hQsq v) (h.scalar v) (himage v)
  exact {
    lower_star := h.upper_star
    lower_square := h.upper_square
    upper_star := fun v => (hnew v).1
    upper_square := fun v => (hnew v).2.1
    nested := fun v => (hnew v).2.2.1
    scalar := meshProjection_scalar_succ G μ hμ δ heigen n hq₂ h.upper_star h.upper_square
    trace_recurrence := fun _ v => by
      rw [show n+1-1=n by omega]
      exact (hnew v).2.2.2.2 }

/-- Every stage strictly before the quantum cutoff is an actual
orthogonal projection, with the required nesting and scalar identity. -/
theorem meshProjectionStage_before_cutoff (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (H : ℕ) (hpos : ∀ n, 0 < n → n < H → 0 < meshQuantum δ n) :
    ∀ n, n+1<H → MeshProjectionStage G μ δ n := by
  intro n
  induction n with
  | zero => intro _; exact meshProjectionStage_zero G μ hμ δ heigen
  | succ n ih =>
    intro hn
    apply meshProjectionStage_succ G μ hμ δ heigen n (ih (by omega))
    · exact ne_of_gt (hpos (n+1) (by omega) (by omega))
    · exact ne_of_gt (hpos (n+2) (by omega) (by omega))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshProjectionCutoff
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual path projections vanish at a finite quantum cutoff. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

lemma meshProjection_trace_zero (μ : V → ℝ) (δ : ℝ) :
    meshWeightedTrace μ (meshProjection G μ δ 0)=∑ v, (μ v : ℂ) := by
  simp only [meshWeightedTrace,meshProjection_zero,Matrix.trace_one]
  simp only [MeshPaths,Fintype.card_punit,Nat.cast_one,mul_one]

lemma meshProjection_trace_one (μ : V → ℝ) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v) :
    meshWeightedTrace μ (meshProjection G μ δ 1)=(δ : ℂ)*∑ v, (μ v : ℂ) := by
  have hp : meshProjection G μ δ 1=
      meshExtendMatrix G (meshProjection G μ δ 0) := by
    funext v
    rw [meshProjection_one,funext (meshProjection_zero G μ δ),meshExtend_one]
  rw [hp,meshWeightedTrace_extend G μ δ heigen,meshProjection_trace_zero]

lemma meshProjection_trace_step (μ : V → ℝ) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (n : ℕ) (h : MeshProjectionStage G μ δ (n+1)) :
    meshWeightedTrace μ (meshProjection G μ δ (n+2))=
      (δ : ℂ)*meshWeightedTrace μ (meshProjection G μ δ (n+1))-
        meshWeightedTrace μ (meshProjection G μ δ n) := by
  have ht (v : V) : Matrix.trace (meshProjection G μ δ (n+2) v)=
      Matrix.trace (meshExtendMatrix G (meshProjection G μ δ (n+1)) v)-
        Matrix.trace (meshProjection G μ δ n v) := by
    have hh := h.trace_recurrence (by omega) v
    rw [show n+1-1=n by omega] at hh
    exact hh
  calc
    _ = meshWeightedTrace μ (meshExtendMatrix G (meshProjection G μ δ (n+1)))-
        meshWeightedTrace μ (meshProjection G μ δ n) := by
      simp only [meshWeightedTrace,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      rw [ht,mul_sub]
    _ = _ := by rw [meshWeightedTrace_extend G μ δ heigen]

/-- The weighted trace is the quantum integer, without any graph
classification or assumption of mesh nilpotence. -/
theorem meshProjection_weightedTrace (μ : V → ℝ) (hμ : ∀ v, 0<μ v) (δ : ℝ)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (H : ℕ) (hpos : ∀ n, 0 < n → n < H → 0 < meshQuantum δ n) :
    ∀ n, n<H → meshWeightedTrace μ (meshProjection G μ δ n)=
      (meshQuantum δ (n+1) : ℂ)*∑ v, (μ v : ℂ) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro _
    simpa only [Nat.zero_add,meshQuantum_one,Complex.ofReal_one,one_mul] using
      meshProjection_trace_zero G μ δ
  | one =>
    intro _
    have hq : meshQuantum δ (1+1)=δ := by norm_num [meshQuantum]
    rw [hq]
    exact meshProjection_trace_one G μ δ heigen
  | more n ih ih₁ =>
    intro hn
    have hs := meshProjectionStage_before_cutoff G μ hμ δ heigen H hpos (n+1) hn
    rw [meshProjection_trace_step G μ δ heigen n hs,ih₁ (by omega),ih (by omega)]
    have hq : meshQuantum δ (n+2+1)=δ*meshQuantum δ (n+1+1)-meshQuantum δ (n+1) :=
      meshQuantum_step δ (n+1)
    rw [hq,Complex.ofReal_sub,Complex.ofReal_mul]
    ring

/-- Some positive length has zero path projection. This is the finite
essential-path bound, proved from a positive adjacency eigenvector below 2. -/
theorem meshProjection_eventually_zero (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v) :
    ∃ N : ℕ, 0<N ∧ ∀ v, meshProjection G μ δ N v=0 := by
  obtain ⟨H,hH,hq,hpos⟩ := meshQuantum_cutoff δ hδ0 hδ2
  let N := H-1
  have hN : 0<N := by dsimp [N]; omega
  have hNH : N<H := by dsimp [N]; omega
  have hstage := meshProjectionStage_before_cutoff G μ hμ δ heigen H hpos (H-2) (by omega)
  have hlen : H-2+1=N := by dsimp [N]; omega
  have hstar : ∀ v, (meshProjection G μ δ N v).conjTranspose=meshProjection G μ δ N v := by
    rw [←hlen]
    exact hstage.upper_star
  have hsq : ∀ v, meshProjection G μ δ N v*meshProjection G μ δ N v=
      meshProjection G μ δ N v := by
    rw [←hlen]
    exact hstage.upper_square
  have hw := meshProjection_weightedTrace G μ hμ δ heigen H hpos N hNH
  rw [show N+1=H by dsimp [N]; omega] at hw
  have hnonneg := meshWeightedTrace_nonneg μ (fun v => (hμ v).le)
    (meshProjection G μ δ N) hstar hsq
  have hnonpos : (meshWeightedTrace μ (meshProjection G μ δ N)).re≤0 := by
    rw [hw]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.re_sum]
    exact mul_nonpos_of_nonpos_of_nonneg hq (Finset.sum_nonneg (fun v _ => (hμ v).le))
  have him : (meshWeightedTrace μ (meshProjection G μ δ N)).im=0 := by
    rw [hw]
    simp
  have hz : meshWeightedTrace μ (meshProjection G μ δ N)=0 :=
    Complex.ext (le_antisymm hnonpos hnonneg) him
  exact ⟨N,hN,meshWeightedTrace_zero μ hμ (meshProjection G μ δ N) hstar hsq hz⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshPathEvaluation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted mesh relations annihilate sufficiently long actual paths. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V R : Type} [Fintype V] (G : SimpleGraph V)
variable [Ring R] [Algebra ℂ R]

omit [Fintype V] [Algebra ℂ R] in
lemma meshPathEvaluate_insert (B : ∀ u v, G.Adj u v → R) (n : ℕ) (v : V)
    (u : {u : V // G.Adj u v}) (p : MeshPaths G n v) :
    meshPathEvaluate G B (n+2) v (meshInsertBacktrack G u p)=
      meshPathEvaluate G B n v p * B v u.val u.property.symm * B u.val v u.property := rfl

lemma meshApply_contraction_adjoint (μ : V → ℝ) (n : ℕ) (v : V)
    (f : MeshPaths G (n+2) v → R) (p : MeshPaths G n v) :
    meshApply (meshContractionMatrix G μ n v).conjTranspose f p=
      ∑ u : {u : V // G.Adj u v}, (Real.sqrt (μ u/μ v) : ℂ) •
        f (meshInsertBacktrack G u p) := by
  change (∑ q, star (∑ u : {u : V // G.Adj u v},
    if q=meshInsertBacktrack G u p then (Real.sqrt (μ u/μ v) : ℂ) else 0) • f q)=_
  simp only [star_sum,apply_ite star,star_zero,Complex.star_def,Complex.conj_ofReal,
    Finset.sum_smul,ite_smul,zero_smul]
  rw [Finset.sum_comm]
  simp

lemma meshPathEvaluate_contracts (μ : V → ℝ) (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      (Real.sqrt (μ u/μ v) : ℂ) • (B v u.val u.property.symm * B u.val v u.property))=0)
    (n : ℕ) (v : V) :
    meshApply (meshContractionMatrix G μ n v).conjTranspose
      (meshPathEvaluate G B (n+2) v)=0 := by
  funext p
  rw [meshApply_contraction_adjoint]
  simp only [meshPathEvaluate_insert,Pi.zero_apply]
  calc
    _ = meshPathEvaluate G B n v p *
        (∑ u : {u : V // G.Adj u v}, (Real.sqrt (μ u/μ v) : ℂ) •
          (B v u.val u.property.symm * B u.val v u.property)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_assoc,mul_smul_comm]
    _ = 0 := by rw [hmesh,mul_zero]

lemma meshPathEvaluate_extend (B : ∀ u v, G.Adj u v → R) {m n : ℕ}
    (A : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ)
    (hA : ∀ v, meshApply (A v) (meshPathEvaluate G B m v)=meshPathEvaluate G B n v)
    (v : V) : meshApply (meshExtendMatrix G A v) (meshPathEvaluate G B (m+1) v)=
      meshPathEvaluate G B (n+1) v := by
  let L (u : {u : V // G.Adj u v}) : R →ₗ[ℂ] R := {
    toFun := fun x => x*B u.val v u.property
    map_add' := fun x y => add_mul x y _
    map_smul' := fun a x => smul_mul_assoc a x _ }
  change meshApply (meshExtendMatrix G A v)
    (fun p => L p.1 (meshPathEvaluate G B m p.1.val p.2))=_
  rw [meshApply_extend]
  funext q
  rw [hA]
  rfl

/-- Every recursively defined projection acts as the identity after
evaluation in an algebra satisfying the weighted mesh relations. -/
theorem meshPathEvaluate_projection (μ : V → ℝ) (δ : ℝ)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      (Real.sqrt (μ u/μ v) : ℂ) • (B v u.val u.property.symm * B u.val v u.property))=0) :
    ∀ n v, meshApply (meshProjection G μ δ n v) (meshPathEvaluate G B n v)=
      meshPathEvaluate G B n v := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro v; rw [meshProjection_zero,meshApply_one]
  | one => intro v; rw [meshProjection_one,meshApply_one]
  | more n _ ih =>
    intro v
    let Q := meshExtendMatrix G (meshProjection G μ δ (n+1)) v
    let C := meshContractionMatrix G μ n v
    let f := meshPathEvaluate G B (n+2) v
    have hQ : meshApply Q f=f := meshPathEvaluate_extend G B _ ih v
    have hQstar : Q.conjTranspose=Q := by
      simp only [Q,meshExtend_adjoint,meshProjection_selfAdjoint]
    have hkill : meshApply (C*Q).conjTranspose f=0 := by
      rw [Matrix.conjTranspose_mul,hQstar,meshApply_mul,hQ]
      exact meshPathEvaluate_contracts G μ B hmesh n v
    rw [meshProjection_step,meshApply_sub,meshApply_smul,meshApply_mul]
    change meshApply Q f - _ • meshApply (C*Q) (meshApply (C*Q).conjTranspose f)=f
    rw [hQ,hkill,meshApply_zero_right,smul_zero,sub_zero]

/-- A single finite path length vanishes in every algebra satisfying the
weighted mesh relations. The proof uses the actual finite path matrices. -/
theorem weighted_mesh_paths_vanish (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      (Real.sqrt (μ u/μ v) : ℂ) • (B v u.val u.property.symm * B u.val v u.property))=0) :
    ∃ N : ℕ, 0<N ∧ ∀ v p, meshPathEvaluate G B N v p=0 := by
  obtain ⟨N,hN,hzero⟩ := meshProjection_eventually_zero G μ hμ δ hδ0 hδ2 heigen
  refine ⟨N,hN,?_⟩
  intro v p
  have h := meshPathEvaluate_projection G μ δ B hmesh N v
  rw [hzero,meshApply_zero] at h
  exact (congrFun h p).symm

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshNormalization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passage from the weighted essential-path relations to all-plus meshes. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V R : Type} [Fintype V] (G : SimpleGraph V) [Ring R] [Algebra ℂ R]

lemma mesh_normalization_weight (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Real.sqrt (a/b)*(Real.sqrt a)⁻¹*(Real.sqrt b)⁻¹=b⁻¹ := by
  rw [Real.sqrt_div ha.le]
  have hsa := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hsb := ne_of_gt (Real.sqrt_pos.mpr hb)
  calc
    _ = ((Real.sqrt b)^2)⁻¹ := by field_simp
    _ = b⁻¹ := by rw [Real.sq_sqrt hb.le]

lemma meshRescale_relation (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      B v u.val u.property.symm * B u.val v u.property)=0) (v : V) :
    (∑ u : {u : V // G.Adj u v}, (Real.sqrt (μ u/μ v) : ℂ) •
      (meshRescale G μ B v u.val u.property.symm * meshRescale G μ B u.val v u.property))=0 := by
  have hc (u : {u : V // G.Adj u v}) :
      (Real.sqrt (μ u/μ v) : ℂ) * ((Real.sqrt (μ v))⁻¹ : ℂ) *
        ((Real.sqrt (μ u))⁻¹ : ℂ)=(μ v)⁻¹ := by
    calc
      _ = (Real.sqrt (μ u/μ v) : ℂ) * ((Real.sqrt (μ u))⁻¹ : ℂ) *
          ((Real.sqrt (μ v))⁻¹ : ℂ) := by ring
      _ = _ := by exact_mod_cast mesh_normalization_weight (μ u) (μ v) (hμ u) (hμ v)
  simp only [meshRescale,smul_mul_assoc,mul_smul_comm,smul_smul]
  simp only [←mul_assoc,hc]
  rw [←Finset.smul_sum,hmesh,smul_zero]

omit [Fintype V] in
lemma meshPathScale_ne_zero (μ : V → ℝ) (hμ : ∀ v, 0<μ v) :
    ∀ n v p, meshPathScale G μ n v p≠0 := by
  intro n
  induction n with
  | zero => intro v p; exact one_ne_zero
  | succ n ih =>
    intro v p
    change meshPathScale G μ n p.1.val p.2 * ((Real.sqrt (μ v))⁻¹ : ℂ)≠0
    apply mul_ne_zero (ih p.1.val p.2)
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hμ v))))

omit [Fintype V] in
lemma meshRescale_evaluate (μ : V → ℝ) (B : ∀ u v, G.Adj u v → R) :
    ∀ n v p, meshPathEvaluate G (meshRescale G μ B) n v p=
      meshPathScale G μ n v p • meshPathEvaluate G B n v p := by
  intro n
  induction n with
  | zero => intro v p; exact (one_smul ℂ (1 : R)).symm
  | succ n ih =>
    intro v p
    change meshPathEvaluate G (meshRescale G μ B) n p.1.val p.2 *
      (((Real.sqrt (μ v))⁻¹ : ℂ) • B p.1.val v p.1.property)=_
    rw [ih,smul_mul_assoc,mul_smul_comm,smul_smul]
    rfl

/-- Unweighted all-plus mesh relations suffice for the same finite path
bound. The rescaling factors are explicitly proved nonzero. -/
theorem allPlus_mesh_paths_vanish (μ : V → ℝ) (hμ : ∀ v, 0<μ v)
    (δ : ℝ) (hδ0 : 0<δ) (hδ2 : δ<2)
    (heigen : ∀ v, (∑ u : {u : V // G.Adj u v}, μ u)=δ*μ v)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      B v u.val u.property.symm * B u.val v u.property)=0) :
    ∃ N : ℕ, 0<N ∧ ∀ v p, meshPathEvaluate G B N v p=0 := by
  obtain ⟨N,hN,hzero⟩ := weighted_mesh_paths_vanish G μ hμ δ hδ0 hδ2 heigen
    (meshRescale G μ B) (meshRescale_relation G μ hμ B hmesh)
  refine ⟨N,hN,?_⟩
  intro v p
  have h := hzero v p
  rw [meshRescale_evaluate] at h
  exact (smul_eq_zero.mp h).resolve_left (meshPathScale_ne_zero G μ hμ N v p)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshGraphNilpotence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mesh path bounds, including disconnected positive Cartan graphs. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
open _root_.Matrix
variable {V R : Type} [Fintype V] (G : SimpleGraph V) [Ring R] [Algebra ℂ R]

theorem connected_mesh_paths_vanish (hG : G.Connected)
    (hcartan : ((2 : ℝ) • (1 : Matrix V V ℝ)-G.adjMatrix ℝ).PosDef)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      B v u.val u.property.symm * B u.val v u.property)=0) :
    ∃ N : ℕ, 0<N ∧ ∀ v p, meshPathEvaluate G B N v p=0 := by
  by_cases hedge : ∃ u v, G.Adj u v
  · obtain ⟨μ,d,hμ,hd0,hd2,heigen⟩ := mesh_graph_positive_weights G hG hedge hcartan
    exact allPlus_mesh_paths_vanish G μ hμ d hd0 hd2 heigen B hmesh
  · refine ⟨1,by omega,?_⟩
    intro v p
    exact (hedge ⟨p.1.val,v,p.1.property⟩).elim

omit [Fintype V] [Algebra ℂ R] in
lemma meshPathEvaluate_longer (B : ∀ u v, G.Adj u v → R) (N : ℕ)
    (hN : ∀ v p, meshPathEvaluate G B N v p=0) :
    ∀ n, N≤n → ∀ v p, meshPathEvaluate G B n v p=0 := by
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => exact hN
  | succ k ih =>
    intro v p
    change meshPathEvaluate G B (N+k) p.1.val p.2 * B p.1.val v p.1.property=0
    rw [ih (by omega),zero_mul]

omit [Fintype V] [Algebra ℂ R] in
lemma meshPathInComponent_evaluate (C : G.ConnectedComponent)
    (B : ∀ u v, G.Adj u v → R) : ∀ n v p,
    meshPathEvaluate C.toSimpleGraph (fun u v h => B u.val v.val h) n v
      (meshPathInComponent G C n v p)=meshPathEvaluate G B n v.val p := by
  intro n
  induction n with
  | zero => intro v p; rfl
  | succ n ih =>
    intro v p
    dsimp only [meshPathInComponent,meshPathEvaluate]
    rw [ih]

omit [Fintype V] in
lemma mesh_component_cartan (C : G.ConnectedComponent)
    (hcartan : ((2 : ℝ) • (1 : Matrix V V ℝ)-G.adjMatrix ℝ).PosDef) :
    let _ : DecidableEq C := Classical.decEq C
    ((2 : ℝ) • (1 : Matrix C C ℝ)-C.toSimpleGraph.adjMatrix ℝ).PosDef := by
  let : DecidableEq C := Classical.decEq C
  have h := hcartan.submatrix (e := ((↑) : C → V)) Subtype.val_injective
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext u v
  by_cases huv : u=v
  · subst v
    simp [Matrix.submatrix_apply]
  · have hval : u.val≠v.val := fun hh => huv (Subtype.ext hh)
    simp [Matrix.submatrix_apply,SimpleGraph.adjMatrix_apply,
      SimpleGraph.ConnectedComponent.toSimpleGraph,SimpleGraph.induce,huv,hval]
    rfl

/-- Every finite graph with positive definite Cartan form has a finite
all-plus mesh path bound, whether or not the graph is connected. -/
theorem positive_cartan_mesh_paths_vanish
    (hcartan : ((2 : ℝ) • (1 : Matrix V V ℝ)-G.adjMatrix ℝ).PosDef)
    (B : ∀ u v, G.Adj u v → R)
    (hmesh : ∀ v, (∑ u : {u : V // G.Adj u v},
      B v u.val u.property.symm * B u.val v u.property)=0) :
    ∃ N : ℕ, 0<N ∧ ∀ v p, meshPathEvaluate G B N v p=0 := by
  have hC (C : G.ConnectedComponent) : ∃ N : ℕ, 0<N ∧
      ∀ v p, meshPathEvaluate C.toSimpleGraph (fun u v h => B u.val v.val h) N v p=0 := by
    apply connected_mesh_paths_vanish C.toSimpleGraph C.connected_toSimpleGraph
      (mesh_component_cartan G C hcartan)
    intro v
    calc
      _ = ∑ u : {u : V // G.Adj u v.val}, B v.val u.val u.property.symm *
          B u.val v.val u.property := by
        apply Fintype.sum_equiv (meshComponentNeighborEquiv G C v)
        intro u
        rfl
      _ = 0 := hmesh v.val
  let n : G.ConnectedComponent → ℕ := fun C => (hC C).choose
  have hn (C : G.ConnectedComponent) : ∀ v p,
      meshPathEvaluate C.toSimpleGraph (fun u v h => B u.val v.val h) (n C) v p=0 :=
    (hC C).choose_spec.2
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let N := Finset.univ.sup n+1
  refine ⟨N,by dsimp [N]; omega,?_⟩
  intro v p
  let C := G.connectedComponentMk v
  have hv : v∈C := by exact (C.mem_supp_iff v).mpr rfl
  have hbound : n C≤N := by
    have hle := Finset.le_sup (f := n) (Finset.mem_univ C)
    dsimp [N]
    omega
  have hz := meshPathEvaluate_longer C.toSimpleGraph (fun u v h => B u.val v.val h)
    (n C) (hn C) N hbound ⟨v,hv⟩ (meshPathInComponent G C N ⟨v,hv⟩ p)
  rwa [meshPathInComponent_evaluate] at hz

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshQuiver
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simple graph of a finite induced reversible quiver. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) (U : Set V)

variable (hloop : ∀ a, Q.source a≠Q.target a)

lemma meshChosenArrow_reverse (hsimple : QuiverSimpleOn Q U) {u v : U}
    (h : (meshQuiverGraph Q U hloop).Adj u v) :
    meshChosenArrow Q U hloop h.symm=Q.reverse (meshChosenArrow Q U hloop h) := by
  apply meshChosenArrow_eq Q U hloop hsimple
  · rw [Q.source_reverse,meshChosenArrow_target]
  · rw [Q.target_reverse,meshChosenArrow_source]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshQuiverWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_length _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.dual_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.source_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.Path.target_dual _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.linearMap_pathBasis _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_base _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_left _root_.OAI.HarmonicArtin.ReversibleQuiver.StringFunctor.reverse_right _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.corner_val _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge.reverse_reverse _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.arrow_vertexId _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.pathCoordinates_vertex _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_false _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.selfCornerEquiv_true _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.token_vertexId _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.vertexId_mul_self _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.vertex_vertexId
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonzero arrow words are actual paths in the induced simple graph. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A R : Type} (Q : ReversibleQuiver V A) (U : Set V)
  (hloop : ∀ a, Q.source a≠Q.target a) (hsimple : QuiverSimpleOn Q U)
  [Ring R]

include hsimple in
/-- The outside and noncomposable relations leave only genuine paths.
The last-vertex annihilation statement is maintained in the induction. -/
theorem mesh_word_is_path (B : A → R)
    (houtside : ∀ a, Q.source a∉U ∨ Q.target a∉U → B a=0)
    (hpath : ∀ a b, Q.target a≠Q.source b → B a*B b=0) (w : List A) :
    (w.map B).prod=0 ∨ w=[] ∨
      ∃ (v : U) (p : MeshPaths (meshQuiverGraph Q U hloop) w.length v),
        meshPathEvaluate (meshQuiverGraph Q U hloop) (meshArrowValues Q U hloop B)
          w.length v p=(w.map B).prod ∧
        ∀ a, Q.source a≠v.val → (w.map B).prod*B a=0 := by
  induction w using List.reverseRecOn with
  | nil => exact Or.inr (Or.inl rfl)
  | append_singleton w a ih =>
    by_cases hz : ((w++[a]).map B).prod=0
    · exact Or.inl hz
    have heq : ((w++[a]).map B).prod=(w.map B).prod*B a := by simp
    have hBa : B a≠0 := by
      intro ha
      apply hz
      rw [heq,ha,mul_zero]
    have hSa : Q.source a∈U := by
      by_contra h
      exact hBa (houtside a (Or.inl h))
    have hTa : Q.target a∈U := by
      by_contra h
      exact hBa (houtside a (Or.inr h))
    let target : U := ⟨Q.target a,hTa⟩
    have hkill : ∀ b, Q.source b≠target.val → ((w++[a]).map B).prod*B b=0 := by
      intro b hb
      rw [heq,mul_assoc,hpath a b hb.symm,mul_zero]
    right
    right
    rcases ih with hw | hw | ⟨v,p,hp,hv⟩
    · exact (hz (by rw [heq,hw,zero_mul])).elim
    · subst w
      let source : U := ⟨Q.source a,hSa⟩
      have edge : (meshQuiverGraph Q U hloop).Adj source target := ⟨a,rfl,rfl⟩
      refine ⟨target,⟨⟨source,edge⟩,PUnit.unit⟩,?_,hkill⟩
      simp only [List.nil_append,List.length_singleton,List.map_singleton,List.prod_singleton]
      change 1*B (meshChosenArrow Q U hloop edge)=B a
      rw [one_mul,meshChosenArrow_eq Q U hloop hsimple edge a rfl rfl]
    · have hsource : Q.source a=v.val := by
        by_contra h
        exact hz (heq.trans (hv a h))
      have edge : (meshQuiverGraph Q U hloop).Adj v target := ⟨a,hsource,rfl⟩
      rw [List.length_append,List.length_singleton]
      refine ⟨target,⟨⟨v,edge⟩,p⟩,?_,hkill⟩
      change meshPathEvaluate (meshQuiverGraph Q U hloop) (meshArrowValues Q U hloop B)
        w.length v p * B (meshChosenArrow Q U hloop edge)=_
      rw [hp,meshChosenArrow_eq Q U hloop hsimple edge a hsource rfl,heq]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshQuiverAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidFirstReducedDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.braidTwistFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.homSpacePairing_perfect _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.inverseTwistIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.testIndexDecidableEq _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.finiteDimensional _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive Cartan quivers satisfy the explicit mesh ideal bound. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A R : Type} [Fintype V] [Fintype A]
  (Q : ReversibleQuiver V A) (U : Set V)
  (hloop : ∀ a, Q.source a≠Q.target a) (hsimple : QuiverSimpleOn Q U)
  [Ring R] [Algebra ℂ R]
include hsimple

noncomputable local instance (priority := 2000) meshRegionDecEq_rea0be5_1 : DecidableEq U := Classical.decEq U
omit [Algebra ℂ R] in
lemma meshArrowValues_relation (B : A → R)
    (houtside : ∀ a, Q.source a∉U ∨ Q.target a∉U → B a=0)
    (hmesh : ∀ v∈U, (∑ a, if Q.source a=v then B a*B (Q.reverse a) else 0)=0)
    (v : U) :
    (∑ u : {u : U // (meshQuiverGraph Q U hloop).Adj u v},
      meshArrowValues Q U hloop B v u.val u.property.symm *
        meshArrowValues Q U hloop B u.val v u.property)=0 := by
  let p : A → Prop := fun a => Q.source a=v.val ∧ Q.target a∈U
  let f : A → R := fun a => if Q.source a=v.val then B a*B (Q.reverse a) else 0
  have hrest : (∑ a : {a : A // ¬p a}, f a)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    by_cases hs : Q.source a=v.val
    · have ht : Q.target a∉U := fun ht => a.property ⟨hs,ht⟩
      simp only [f,hs,ite_true, if_true,houtside a (Or.inr ht),zero_mul]
    · simp only [f,hs,ite_false, if_false]
  have hsum := Fintype.sum_subtype_add_sum_subtype p f
  rw [hrest,add_zero] at hsum
  calc
    _ = ∑ a : {a : A // p a}, B a*B (Q.reverse a) := by
      apply Fintype.sum_equiv (meshQuiverNeighborEquiv Q U hloop hsimple v)
      intro u
      change B (meshChosenArrow Q U hloop u.property.symm) *
        B (meshChosenArrow Q U hloop u.property)=
        B (meshChosenArrow Q U hloop u.property.symm) *
          B (Q.reverse (meshChosenArrow Q U hloop u.property.symm))
      rw [←meshChosenArrow_reverse Q U hloop hsimple u.property.symm]
    _ = ∑ a : {a : A // p a}, f a := by
      apply Finset.sum_congr rfl
      intro a _
      exact (ite_eq_left a.property.1).symm
    _ = ∑ a, f a := hsum
    _ = 0 := hmesh v.val v.property

theorem quiver_mesh_words_vanish
    (hcartan : ((2 : ℝ) • (1 : Matrix U U ℝ)-(meshQuiverGraph Q U hloop).adjMatrix ℝ).PosDef)
    (B : A → R)
    (houtside : ∀ a, Q.source a∉U ∨ Q.target a∉U → B a=0)
    (hpath : ∀ a b, Q.target a≠Q.source b → B a*B b=0)
    (hmesh : ∀ v∈U, (∑ a, if Q.source a=v then B a*B (Q.reverse a) else 0)=0) :
    ∃ N : ℕ, 0<N ∧ ∀ w : List A, w.length=N → (w.map B).prod=0 := by
  obtain ⟨N,hN,hzero⟩ := positive_cartan_mesh_paths_vanish (meshQuiverGraph Q U hloop)
    hcartan (meshArrowValues Q U hloop B) (meshArrowValues_relation Q U hloop hsimple B houtside hmesh)
  refine ⟨N,hN,?_⟩
  intro w hw
  rcases mesh_word_is_path Q U hloop hsimple B houtside hpath w with hz|hwnil|⟨v,p,hp,_⟩
  · exact hz
  · subst w
    simp only [List.length_nil] at hw
    omega
  · subst N
    exact hp.symm.trans (hzero v p)

/-- The exact free-algebra ideal statement used in the conditional main
theorems, now proved for every finite simple positive Cartan quiver. -/
theorem meshNilpotent_of_positive_cartan
    (hcartan : ((2 : ℝ) • (1 : Matrix U U ℝ)-(meshQuiverGraph Q U hloop).adjMatrix ℝ).PosDef) :
    MeshNilpotent Q U := by
  let I : TwoSidedIdeal (FreeAlgebra ℂ A) := TwoSidedIdeal.span (meshRelations Q U)
  let φ : FreeAlgebra ℂ A →ₐ[ℂ] I.ringCon.Quotient := I.ringCon.mkₐ ℂ
  let B : A → I.ringCon.Quotient := fun a => φ (FreeAlgebra.ι ℂ a)
  have hmem (z : FreeAlgebra ℂ A) : z∈I ↔ φ z=0 := by
    have hk : z∈TwoSidedIdeal.ker I.ringCon.mk' ↔ z∈I := by
      rw [TwoSidedIdeal.ker_ringCon_mk']
    exact hk.symm.trans (TwoSidedIdeal.mem_ker I.ringCon.mk')
  have houtside : ∀ a, Q.source a∉U ∨ Q.target a∉U → B a=0 := by
    intro a ha
    apply (hmem _).mp
    exact TwoSidedIdeal.subset_span (Or.inl (Or.inl ⟨a,ha,rfl⟩))
  have hpath : ∀ a b, Q.target a≠Q.source b → B a*B b=0 := by
    intro a b hab
    change φ (FreeAlgebra.ι ℂ a)*φ (FreeAlgebra.ι ℂ b)=0
    rw [←map_mul]
    apply (hmem _).mp
    exact TwoSidedIdeal.subset_span (Or.inl (Or.inr ⟨a,b,hab,rfl⟩))
  have hmesh : ∀ v∈U, (∑ a, if Q.source a=v then B a*B (Q.reverse a) else 0)=0 := by
    intro v hv
    have hz : φ (meshRelation Q v)=0 := (hmem _).mp
      (TwoSidedIdeal.subset_span (Or.inr ⟨v,hv,rfl⟩))
    simpa only [meshRelation,map_sum,apply_ite,map_mul,map_zero] using hz
  obtain ⟨N,hN,hwords⟩ := quiver_mesh_words_vanish Q U hloop hsimple hcartan B houtside hpath hmesh
  refine ⟨N,hN,?_⟩
  intro w hw
  apply (hmem _).mpr
  simpa only [B,map_list_prod,List.map_map,Function.comp_def] using hwords w hw

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_SphericalMesh
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ParabolicIntersections.relativeEligibleWithinTop
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.deligneRightTranslate_type _root_.OAI.HarmonicArtin.ParabolicIntersections.foldedPositiveHom_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedFamily_one _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_source _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.path_target _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_arrow_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_token_leaf _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_core _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.zigzag_vertex_leaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharging the finite spherical mesh input for the actual fusion quiver. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => (fun Y : Set S => fusionColorRegion (V := S⊕Unit) m (Sum.inl '' Y))

omit [Fintype S] in
lemma sphericalRegionEquiv_symm_val (Y : Set S) (u : U Y) :
    unfoldedInclusion M Y ((sphericalRegionEquiv M Y).symm u)=u.val := by
  exact congrArg Subtype.val ((sphericalRegionEquiv M Y).apply_symm_apply u)

lemma spherical_mesh_simple (Y : Set S) (hY : IsSpherical M Y) : QuiverSimpleOn Q (U Y) := by
  rintro ⟨⟨s,t⟩,i⟩ ⟨⟨s',t'⟩,j⟩ hs ht he₁ he₂
  change s=s' at he₁
  change t=t' at he₂
  subst s'
  subst t'
  change s∈U Y at hs
  change t∈U Y at ht
  obtain ⟨a,ha⟩ : ∃ a : Y × FusionLabel m, unfoldedInclusion M Y a=s := by
    change s∈Set.range (unfoldedInclusion M Y)
    rw [unfoldedInclusion_range M Y]
    exact hs
  obtain ⟨b,hb⟩ : ∃ b : Y × FusionLabel m, unfoldedInclusion M Y b=t := by
    change t∈Set.range (unfoldedInclusion M Y)
    rw [unfoldedInclusion_range M Y]
    exact ht
  have hmult : (coxeterFusionEdge M s.1 t.1).multiplicity m s.2 t.2≤1 := by
    rw [←ha,←hb]
    exact spherical_fusion_multiplicity_le_one M Y hY a.1 b.1 a.2 b.2
  have hi := i.isLt
  have hj := j.isLt
  change i.val<(coxeterFusionEdge M s.1 t.1).multiplicity m s.2 t.2 at hi
  change j.val<(coxeterFusionEdge M s.1 t.1).multiplicity m s.2 t.2 at hj
  congr 1
  apply Fin.ext
  omega

lemma fusion_mesh_arrow_exists (u v : FusionVertex (V := S⊕Unit) m) :
    (∃ a, (Q).source a=u ∧ (Q).target a=v) ↔
      0<(coxeterFusionEdge M u.1 v.1).multiplicity m u.2 v.2 := by
  constructor
  · rintro ⟨⟨⟨s,t⟩,i⟩,hs,ht⟩
    change s=u at hs
    change t=v at ht
    subst s
    subst t
    exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  · intro h
    exact ⟨⟨(u,v),⟨0,h⟩⟩,rfl,rfl⟩

theorem spherical_mesh_cartan (Y : Set S) (hY : IsSpherical M Y) :
    let _ : DecidableEq (U Y) := Classical.decEq _
    ((2 : ℝ) • (1 : Matrix (U Y) (U Y) ℝ)-
      (meshQuiverGraph Q (U Y) (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M))).adjMatrix ℝ).PosDef := by
  let : DecidableEq (U Y) := Classical.decEq _
  let e := sphericalRegionEquiv M Y
  have hp := (spherical_unfolded_posDef M Y hY).submatrix e.symm.injective
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext u v
  let a := e.symm u
  let b := e.symm v
  have hu : unfoldedInclusion M Y a=u.val := sphericalRegionEquiv_symm_val M Y u
  have hv : unfoldedInclusion M Y b=v.val := sphericalRegionEquiv_symm_val M Y v
  have hadj : (meshQuiverGraph Q (U Y)
      (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M))).Adj u v ↔
      0<(coxeterFusionEdge M (.inl a.1) (.inl b.1)).multiplicity m a.2 b.2 := by
    change (∃ c, (Q).source c=u.val ∧ (Q).target c=v.val) ↔ _
    rw [←hu,←hv,fusion_mesh_arrow_exists]
  have hn := spherical_fusion_multiplicity_le_one M Y hY a.1 b.1 a.2 b.2
  change ((2 : ℝ) • (1 : Matrix (U Y) (U Y) ℝ)-
      (meshQuiverGraph Q (U Y) (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M))).adjMatrix ℝ) u v=
    fusionUnfoldedCartan m (fun i j : Y => coxeterFusionEdge M (.inl i) (.inl j)) a b
  by_cases huv : u=v
  · subst v
    change ((2 : ℝ) • (1 : Matrix (U Y) (U Y) ℝ)-
      (meshQuiverGraph Q (U Y) (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M))).adjMatrix ℝ) u u=
      fusionUnfoldedCartan m (fun i j : Y => coxeterFusionEdge M (.inl i) (.inl j)) a a
    simp [fusionUnfoldedCartan,coxeterFusionEdge_diag,FusionEdge.multiplicity]
  · have hab : a≠b := fun h => huv (e.symm.injective h)
    have hm : (coxeterFusionEdge M (.inl a.1) (.inl b.1)).multiplicity m a.2 b.2=0 ∨
        (coxeterFusionEdge M (.inl a.1) (.inl b.1)).multiplicity m a.2 b.2=1 := by omega
    rcases hm with hm|hm <;>
      simp [SimpleGraph.adjMatrix_apply,hadj,hm,huv,
        fusionUnfoldedCartan,hab]

/-- The finite-Dynkin mesh nilpotence input for every spherical set of
colors, proved for the precise ambient fusion-quiver relations. -/
theorem spherical_mesh_nilpotent (Y : Set S) (hY : IsSpherical M Y) : MeshNilpotent Q (U Y) := by
  apply meshNilpotent_of_positive_cartan Q (U Y)
    (fusionQuiver_no_loops _ _ _ (coxeterFusionEdge_diag M)) (spherical_mesh_simple M Y hY)
  exact spherical_mesh_cartan M Y hY

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_UnconditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unconditional parabolic intersections and closure

The spherical mesh input is proved by weighted path contractions and finite
Jones--Wenzl projections. Together with the proved standard embeddings,
folding, and acyclic evaluation, this discharges every input to Theorem 1.1
and Corollary 1.2 of paper 082-03. The dynamical corollary below still names
its separate published geometric input explicitly.
-/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The full spherical mesh input, without hypotheses from the literature. -/
theorem spherical_mesh_input_s236_oai : PublishedMeshInput M :=
  fun Y hY => spherical_mesh_nilpotent M Y hY

end HarmonicArtin.ParabolicIntersections

end OAI
end

theorem solution : type_of% @OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input_s236_oai := @OAI.HarmonicArtin.ParabolicIntersections.spherical_mesh_input_s236_oai
