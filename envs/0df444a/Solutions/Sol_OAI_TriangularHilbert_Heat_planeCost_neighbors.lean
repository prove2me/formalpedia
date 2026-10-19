-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.planeCost_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:53:29.218186+00:00
-- url     : https://prove2.me/submissions/97ece4e0-26df-4dda-992b-5521f6118e70

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneTime.lean:L100-L117
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.planeCost_neighbors. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Theorems.Thm_OAI_TriangularHilbert_Heat_heatPlane_integrable
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_le_of_le_smul
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rootCost_eq_of_solution
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rowStar_mul_adjoint
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_starInsert_eq_insertRow
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_sylv_solvable_inserted_gram
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_vertexRoot_insert

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

theorem traceReal_mul_cycle (A B C : Matrix ι ι ℂ) :
    traceReal (A * B * C) = traceReal (C * A * B) := by
  unfold traceReal; rw [Matrix.trace_mul_cycle]
theorem traceReal_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : 0 ≤ traceReal A :=
  (RCLike.nonneg_iff.mp hA.trace_nonneg).1

theorem hsReal_symm (X Y : Matrix ι ι ℂ) : hsReal X Y = hsReal Y X := by
  unfold hsReal
  rw [← traceReal_star (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem hsReal_sylv_symm {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) : hsReal X (sylv A Y) = hsReal (sylv A X) Y := by
  simp only [hsReal, sylv, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hA.eq, mul_add, add_mul, traceReal_add]
  rw [← Matrix.mul_assoc Xᴴ A Y, ← Matrix.mul_assoc Xᴴ Y A,
    traceReal_mul_cycle Xᴴ Y A]

theorem penalty_nonneg {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (X : Matrix ι ι ℂ) : 0 ≤ penalty A X := by
  simp only [penalty, hsReal, sylv, mul_add, traceReal_add]
  have h₁ := traceReal_nonneg (hA.conjTranspose_mul_mul_same X)
  have h₂ := traceReal_nonneg (hA.mul_mul_conjTranspose_same X)
  rw [Matrix.mul_assoc] at h₁
  rw [← Matrix.mul_assoc Xᴴ X A, traceReal_mul_cycle Xᴴ X A,
    traceReal_mul_cycle A Xᴴ X]
  exact add_nonneg h₁ h₂

theorem penalty_sub {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    penalty A (X - Y) = penalty A X + penalty A Y - 2 * hsReal (sylv A Y) X := by
  simp only [penalty, sylv_sub_right, hsReal_sub_left, hsReal_sub_right]
  rw [hsReal_symm Y (sylv A X), ← hsReal_sylv_symm hA, hsReal_symm X (sylv A Y)]
  ring

theorem penalty_mono {A B : Matrix ι ι ℂ} (hAB : A ≤ B) (X : Matrix ι ι ℂ) :
    penalty A X ≤ penalty B X := by
  have h := penalty_nonneg hAB X
  simpa only [penalty, sylv_sub_left, hsReal_sub_right, sub_nonneg] using h

theorem variation_sylv {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X Y : Matrix ι ι ℂ) :
    variation A (sylv A Y) X = penalty A Y - penalty A (X - Y) := by
  rw [variation, penalty_sub hA]
  ring

theorem variation_bddAbove {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) : BddAbove (Set.range (variation A K)) := by
  obtain ⟨Y, rfl⟩ := hsol
  refine ⟨penalty A Y, ?_⟩
  rintro _ ⟨X, rfl⟩
  rw [variation_sylv hA.isHermitian]
  exact sub_le_self _ (penalty_nonneg hA _)

theorem variation_le_rootCost {A K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hsol : ∃ Y, sylv A Y = K) (X : Matrix ι ι ℂ) :
    (3 / 2 : ℝ) * variation A K X ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩

theorem rootCost_antitone {A B K : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    rootCost B K ≤ rootCost A K := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans
    (le_csSup (variation_bddAbove hA hsol) ⟨X, rfl⟩)

theorem hsReal_eq_sum (X Y : Matrix ι ι ℂ) :
    hsReal X Y = ∑ i, ∑ j, (star (X i j) * Y i j).re := by
  simp only [hsReal, traceReal, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  exact Finset.sum_comm

variable [DecidableEq ι]

theorem traceReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    traceReal (conjStarAlgAut ℂ _ U X) = traceReal X := by
  unfold traceReal
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem hsReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X Y : Matrix ι ι ℂ) :
    hsReal (conjStarAlgAut ℂ _ U X) (conjStarAlgAut ℂ _ U Y) = hsReal X Y := by
  change traceReal (star (conjStarAlgAut ℂ _ U X) * conjStarAlgAut ℂ _ U Y) = _
  rw [← map_star, ← map_mul, traceReal_unitary_conj]
  rfl

theorem variation_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A K X : Matrix ι ι ℂ) :
    variation (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U K)
      (conjStarAlgAut ℂ _ U X) = variation A K X := by
  simp only [variation, penalty, sylv_unitary_conj, hsReal_unitary_conj]

theorem hessianCost_antitone {P Q K : Matrix ι ι ℂ}
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) (hPQ : P ≤ Q) :
    hessianCost Q K ≤ hessianCost P K := by
  exact rootCost_antitone (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hsol (CFC.monotone_sqrt hPQ)

theorem sqrt_smul {P : Matrix ι ι ℂ} (hP : P.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • P) = Real.sqrt c • CFC.sqrt P := by
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, Real.mul_self_sqrt hc, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · exact smul_nonneg (Real.sqrt_nonneg c) (CFC.sqrt_nonneg P)

theorem hsReal_single (K : Matrix ι ι ℂ) (i j : ι) (z : ℂ) :
    hsReal K (Matrix.single i j z) = (star (K i j) * z).re := by
  simp [hsReal_eq_sum, Matrix.single_apply, ite_and, apply_ite]

theorem sylv_diagonal_single (q : ι → ℝ) (i j : ι) (z : ℂ) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) (Matrix.single i j z) =
      Matrix.single i j (((q i + q j : ℝ) : ℂ) * z) := by
  ext a b
  rw [sylv_diagonal_apply]
  by_cases ha : i = a
  · subst a
    by_cases hb : j = b
    · subst b; simp
    · simp [hb]
  · simp [ha]

theorem sylv_solvable_diagonal_of_bddAbove (q : ι → ℝ) (K : Matrix ι ι ℂ)
    (hb : BddAbove (Set.range (variation (Matrix.diagonal (fun i => (q i : ℂ))) K))) :
    ∃ Y, sylv (Matrix.diagonal (fun i => (q i : ℂ))) Y = K := by
  refine ⟨diagonalSolution q K, diagonalSolution_solves q K ?_⟩
  intro i j hij
  by_contra hK
  obtain ⟨b, hb⟩ := hb
  let X := Matrix.single i j (K i j)
  have hzero : sylv (Matrix.diagonal (fun i => (q i : ℂ))) X = 0 := by
    simp [X, sylv_diagonal_single, hij]
  have hhs : hsReal K X = ‖K i j‖^2 := by
    rw [hsReal_single]
    simp only [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖K i j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hK)
  let t : ℝ := b / (2 * ‖K i j‖^2) + 1
  have ht := hb (Set.mem_range_self (t • X))
  change variation _ K (t • X) ≤ b at ht
  simp only [variation, penalty, sylv_smul_right, hzero, smul_zero,
    hsReal_zero_right, sub_zero, hsReal_smul_right, hhs] at ht
  have hcalc : 2 * (t * ‖K i j‖^2) = b + 2 * ‖K i j‖^2 := by
    dsimp [t]
    field_simp [ne_of_gt hpos]
  rw [hcalc] at ht
  linarith

theorem sylv_solvable_of_bddAbove {A K : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hb : BddAbove (Set.range (variation A K))) : ∃ Y, sylv A Y = K := by
  let U := hA.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  let K' := f K
  have hAd : f A = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have hb' : BddAbove (Set.range (variation (f A) K')) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b, ?_⟩
    rintro _ ⟨X, rfl⟩
    obtain ⟨Y, rfl⟩ := f.surjective X
    change variation (f A) (f K) (f Y) ≤ b
    exact (variation_unitary_conj (star U) A K Y) ▸ hb (Set.mem_range_self Y)
  rw [hAd] at hb'
  obtain ⟨Y, hY⟩ := sylv_solvable_diagonal_of_bddAbove _ K' hb'
  refine ⟨f.symm Y, ?_⟩
  apply f.injective
  change f (sylv A (f.symm Y)) = f K
  calc
    _ = sylv (f A) (f (f.symm Y)) := (sylv_unitary_conj (star U) A (f.symm Y)).symm
    _ = sylv (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) Y := by
      rw [f.apply_symm_apply, hAd]
    _ = _ := hY

theorem sylv_solvable_mono {A B K : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.IsHermitian) (hsol : ∃ Y, sylv A Y = K) (hAB : A ≤ B) :
    ∃ Y, sylv B Y = K := by
  apply sylv_solvable_of_bddAbove hB
  obtain ⟨b, hb⟩ := variation_bddAbove hA hsol
  refine ⟨b, ?_⟩
  rintro _ ⟨X, rfl⟩
  exact (sub_le_sub_left (penalty_mono hAB X) _).trans (hb (Set.mem_range_self X))

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem blocks_mul (A B : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks (A * B) = blocks A * blocks B := by
  exact (Matrix.compRingEquiv Three ι ℂ).map_mul A B

omit [Fintype ι] [DecidableEq ι] in
theorem blocks_star (A : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks Aᴴ = (blocks A)ᴴ := rfl

omit [DecidableEq ι] in
theorem blocks_trace (A : Matrix Three Three (Matrix ι ι ℂ)) :
    Matrix.trace (blocks A) = ∑ v, Matrix.trace (A v v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma blockD_mul (A B : Three → Matrix ι ι ℂ) :
    blockD A * blockD B = blockD (fun v => A v * B v) := by
  unfold blockD
  rw [← blocks_mul, Matrix.diagonal_mul_diagonal]

omit [Fintype ι] [DecidableEq ι] in
lemma blockD_star (A : Three → Matrix ι ι ℂ) :
    (blockD A)ᴴ = blockD (fun v => (A v)ᴴ) := by
  unfold blockD
  rw [← blocks_star, Matrix.diagonal_conjTranspose]
  rfl

lemma blockD_posSemidef (A : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef) : (blockD A).PosSemidef := by
  have he : blockD A = (blockD (fun v => CFC.sqrt (A v)))ᴴ *
      blockD (fun v => CFC.sqrt (A v)) := by
    rw [blockD_star, blockD_mul]
    congr 1
    funext v
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A v))).isHermitian.eq,
      CFC.sqrt_mul_sqrt_self (A v) (hA v).nonneg]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma sqrt_blockD (A : Three → Matrix ι ι ℂ) (hA : ∀ v, (A v).PosSemidef) :
    CFC.sqrt (blockD A) = blockD (fun v => CFC.sqrt (A v)) := by
  apply CFC.sqrt_unique
  · rw [blockD_mul]
    congr 1
    funext v
    exact CFC.sqrt_mul_sqrt_self (A v) (hA v).nonneg
  · exact (blockD_posSemidef _ (fun v =>
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A v)))).nonneg

omit [DecidableEq ι] in
lemma hsReal_blocks_blockD (K : Matrix Three Three (Matrix ι ι ℂ))
    (Y : Three → Matrix ι ι ℂ) :
    hsReal (blocks K) (blockD Y) = ∑ v, hsReal (K v v) (Y v) := by
  simp only [hsReal, blockD, ← blocks_star, ← blocks_mul, traceReal, blocks_trace,
    Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, Complex.re_sum]

omit [DecidableEq ι] in
lemma sylv_blockD (A Y : Three → Matrix ι ι ℂ) :
    sylv (blockD A) (blockD Y) = blockD (fun v => sylv (A v) (Y v)) := by
  unfold sylv
  rw [blockD_mul, blockD_mul]
  unfold blockD
  change (Matrix.compRingEquiv Three ι ℂ) _ + (Matrix.compRingEquiv Three ι ℂ) _ =
    (Matrix.compRingEquiv Three ι ℂ) _
  rw [← map_add, ← Matrix.diagonal_add]

lemma rootCost_blockD_ge_diagonal (A : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef) (K : Matrix Three Three (Matrix ι ι ℂ))
    (hsol : ∃ Y, sylv (blockD A) Y = blocks K)
    (hdiag : ∀ v, ∃ Y, sylv (A v) Y = K v v) :
    ∑ v, rootCost (A v) (K v v) ≤ rootCost (blockD A) (blocks K) := by
  choose Y hY using hdiag
  have hv := variation_le_rootCost (blockD_posSemidef A hA) hsol (blockD Y)
  have he : variation (blockD A) (blocks K) (blockD Y) =
      ∑ v, hsReal (K v v) (Y v) := by
    rw [variation, penalty, sylv_blockD]
    simp only [hY]
    rw [hsReal_blocks_blockD]
    change 2 * (∑ v, hsReal (K v v) (Y v)) -
      hsReal (blocks (Matrix.diagonal Y)) (blockD (fun v => K v v)) = _
    rw [hsReal_blocks_blockD, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [Matrix.diagonal_apply_eq]
    apply Finset.sum_congr rfl
    intro v _
    rw [hsReal_symm (Y v) (K v v)]
    ring
  rw [he] at hv
  simp_rw [rootCost_eq_of_solution (hA _) (hY _)]
  simpa only [Finset.mul_sum] using hv

omit [DecidableEq ι] in
lemma gramRow_eq (R : Three → Matrix ι ι ℂ) : gramRow R = (wideRow R)ᴴ * wideRow R := by
  rfl

omit [DecidableEq ι] in
lemma insertRow_eq (R : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) :
    insertRow R L = (wideRow R)ᴴ * L * wideRow R := by
  rfl

omit [DecidableEq ι] in
lemma gramRow_posSemidef (R : Three → Matrix ι ι ℂ) : (gramRow R).PosSemidef := by
  rw [gramRow_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma pinchedRow_posSemidef (R : Three → Matrix ι ι ℂ) : (pinchedRow R).PosSemidef :=
  blockD_posSemidef _ (fun _ => Matrix.posSemidef_conjTranspose_mul_self _)

lemma gramRow_le_two_pinchedRow (R : Three → Matrix ι ι ℂ)
    (v : Three) (hR : R v = 0) : gramRow R ≤ (2 : ℝ) • pinchedRow R := by
  let R' : Three → Matrix ι ι ℂ := fun i => if i = v + 1 then R i else -(R i)
  have he : (2 : ℝ) • pinchedRow R - gramRow R = gramRow R' := by
    ext a b
    rcases a with ⟨a, i⟩
    rcases b with ⟨b, j⟩
    change (2 : ℝ) • (Matrix.diagonal (fun k => (R k)ᴴ * R k) a b i j) -
      ((R a)ᴴ * R b) i j = ((R' a)ᴴ * R' b) i j
    fin_cases v
    · change R 0 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
    · change R 1 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
    · change R 2 = 0 at hR
      fin_cases a <;> fin_cases b <;> simp [R', hR, two_mul, sub_eq_add_neg]
  rw [Matrix.le_iff, he]
  exact gramRow_posSemidef R'

theorem hessianCost_gramRow_ge_edges (R : Three → Matrix ι ι ℂ)
    (L : Matrix ι ι ℂ) (v : Three) (hR : R v = 0) :
    (∑ w, hessianCost ((R w)ᴴ * R w) ((R w)ᴴ * L * R w)) ≤
      Real.sqrt 2 * hessianCost (gramRow R) (insertRow R L) := by
  have hsol : ∃ Y, sylv (CFC.sqrt (gramRow R)) Y = insertRow R L := by
    rw [gramRow_eq, insertRow_eq]
    exact sylv_solvable_inserted_gram _ _
  have hQ := pinchedRow_posSemidef R
  have hle := gramRow_le_two_pinchedRow R v hR
  have hqs : (CFC.sqrt (pinchedRow R)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (pinchedRow R))
  have hsol2 := sylv_solvable_mono
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (gramRow R)))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((2 : ℝ) • pinchedRow R))).isHermitian
    hsol (CFC.monotone_sqrt hle)
  rw [sqrt_smul hQ (by norm_num : (0 : ℝ) ≤ 2)] at hsol2
  have hsolQ : ∃ Y, sylv (CFC.sqrt (pinchedRow R)) Y = insertRow R L := by
    obtain ⟨Y, hY⟩ := hsol2
    refine ⟨Real.sqrt 2 • Y, ?_⟩
    rwa [sylv_smul_right, ← sylv_smul_left]
  have hdiag (w : Three) := sylv_solvable_inserted_gram (R w) L
  have hs : CFC.sqrt (pinchedRow R) = blockD (fun w => CFC.sqrt ((R w)ᴴ * R w)) :=
    sqrt_blockD _ (fun _ => Matrix.posSemidef_conjTranspose_mul_self _)
  have hl := rootCost_blockD_ge_diagonal
    (fun w => CFC.sqrt ((R w)ᴴ * R w))
    (fun w => Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((R w)ᴴ * R w)))
    (fun i j => (R i)ᴴ * L * R j) (by simpa only [← hs, insertRow] using hsolQ) hdiag
  calc
    _ ≤ hessianCost (pinchedRow R) (insertRow R L) := by
      simpa only [hessianCost, hs, insertRow] using hl
    _ ≤ _ := hessianCost_le_of_le_smul hQ hsol (by norm_num : (0 : ℝ) < 2) hle

lemma rowStar_blocks (W : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar W v = blocks (fun a b => if a = v then triangleBlocks W a b else 0) := by
  ext a b
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  simp only [rowStar, vertexProj, Matrix.diagonal_mul, triangle, blocks, Matrix.comp_apply]
  change (if a = v then (1 : ℂ) else 0) * triangleBlocks W a b i j =
    (if a = v then triangleBlocks W a b else 0) i j
  split_ifs <;> simp

lemma starGram_eq_gramRow (W : Three → Matrix ι ι ℂ) (v : Three) :
    starGram W v = gramRow (triangleBlocks W v) := by
  unfold starGram
  rw [rowStar_blocks]
  let A : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change (blocks A)ᴴ * blocks A = _
  rw [← blocks_star, ← blocks_mul]
  unfold gramRow
  congr 1
  apply Matrix.ext
  intro a b
  change (∑ c, star (A c a) * A c b) = (triangleBlocks W v a)ᴴ * triangleBlocks W v b
  simp [A, apply_ite, Matrix.star_eq_conjTranspose]

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_adj (W : Three → Matrix ι ι ℂ) (v w : Three) :
    (triangleBlocks W v w)ᴴ = triangleBlocks W w v := by
  fin_cases v <;> fin_cases w <;> simp [triangleBlocks]

omit [Fintype ι] [DecidableEq ι] in
lemma triangleBlocks_diag (W : Three → Matrix ι ι ℂ) (v : Three) :
    triangleBlocks W v v = 0 := by
  fin_cases v <;> simp [triangleBlocks]

omit [DecidableEq ι] in
lemma centerGram_posSemidef (W : Three → Matrix ι ι ℂ) (v : Three) :
    (centerGram W v).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun w _ => (Matrix.posSemidef_self_mul_conjTranspose _).nonneg)

omit [DecidableEq ι] in
lemma edgeGram_le_centerGram (W : Three → Matrix ι ι ℂ) (v w : Three) :
    (triangleBlocks W w v)ᴴ * triangleBlocks W w v ≤ centerGram W v := by
  rw [triangleBlocks_adj]
  rw [← triangleBlocks_adj W v w]
  exact Finset.single_le_sum (fun a _ =>
    (Matrix.posSemidef_self_mul_conjTranspose (triangleBlocks W v a)).nonneg)
    (Finset.mem_univ w)

theorem neighbor_comparison (W D : Three → Matrix ι ι ℂ) (w : Three) :
    (∑ v, hessianCost (centerGram W v)
      ((triangleBlocks W w v)ᴴ * D w * triangleBlocks W w v)) ≤
      Real.sqrt 2 * hessianCost (starGram W w) (starInsert W D w) := by
  rw [starGram_eq_gramRow, starInsert_eq_insertRow]
  calc
    _ ≤ ∑ v, hessianCost ((triangleBlocks W w v)ᴴ * triangleBlocks W w v)
        ((triangleBlocks W w v)ᴴ * D w * triangleBlocks W w v) := by
      apply Finset.sum_le_sum
      intro v _
      exact hessianCost_antitone (sylv_solvable_inserted_gram _ _)
        (edgeGram_le_centerGram W v w)
    _ ≤ _ := hessianCost_gramRow_ge_edges _ (D w) w (triangleBlocks_diag W w)

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CostBlock ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma traceReal_blockD (P : Three → Matrix ι ι ℂ) :
    traceReal (blockD P) = ∑ v, traceReal (P v) := by
  simp [traceReal, Matrix.trace, blockD, Fintype.sum_prod_type]

omit [DecidableEq ι] in
lemma hsReal_blockD (A B : Three → Matrix ι ι ℂ) :
    hsReal (blockD A) (blockD B) = ∑ v, hsReal (A v) (B v) := by
  simp only [hsReal, blockD_star, blockD_mul, traceReal_blockD]

lemma rootCost_blockD (A K : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef)
    (hsol : ∀ v, ∃ Y, sylv (A v) Y = K v) :
    rootCost (blockD A) (blockD K) = ∑ v, rootCost (A v) (K v) := by
  choose Y hY using hsol
  have hsol' : sylv (blockD A) (blockD Y) = blockD K := by
    rw [sylv_blockD]
    congr 1
    funext v
    exact hY v
  rw [rootCost_eq_of_solution (blockD_posSemidef A hA) hsol',
    hsReal_blockD, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact (rootCost_eq_of_solution (hA v) (hY v)).symm

lemma hessianCost_blockD (P K : Three → Matrix ι ι ℂ)
    (hP : ∀ v, (P v).PosSemidef)
    (hsol : ∀ v, ∃ Y, sylv (CFC.sqrt (P v)) Y = K v) :
    hessianCost (blockD P) (blockD K) = ∑ v, hessianCost (P v) (K v) := by
  change rootCost (CFC.sqrt (blockD P)) (blockD K) =
    ∑ v, rootCost (CFC.sqrt (P v)) (K v)
  rw [sqrt_blockD P hP]
  exact rootCost_blockD _ K
    (fun v => Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P v))) hsol

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma vertexRoot_star (g : Three → ι → ℝ) : (vertexRoot g)ᴴ = vertexRoot g := by
  unfold vertexRoot
  rw [Matrix.diagonal_conjTranspose]
  simp

lemma vertexRoot_sq (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * vertexRoot g = Matrix.diagonal (fun a => (g a.1 a.2 : ℂ)) := by
  rw [vertexRoot, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg a.1 a.2)]

lemma vertexRoot_commute_vertexProj (g : Three → ι → ℝ) (v : Three) :
    vertexRoot g * vertexProj v = vertexProj v * vertexRoot g := by
  dsimp only [vertexRoot, vertexProj]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

lemma triangle_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    triangle (weightedArray A g) = vertexRoot g * triangle A * vertexRoot g := by
  ext ⟨v,i⟩ ⟨w,j⟩
  fin_cases v <;> fin_cases w <;>
    simp [triangle, triangleBlocks, blocks, weightedArray, vertexRoot,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      mul_comm, mul_left_comm, mul_assoc] <;> first | exact Or.inl (mul_comm _ _) | ring

lemma rowStar_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :
    rowStar (weightedArray A g) v = vertexRoot g * rowStar A v * vertexRoot g := by
  unfold rowStar
  rw [triangle_weightedArray]
  simp only [← Matrix.mul_assoc]
  rw [← vertexRoot_commute_vertexProj]

lemma starGram_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    starGram (weightedArray A g) v = weightedGram (rowBare A g v) (fun a => g a.1 a.2) := by
  have hr : rowStar (weightedArray A g) v = vertexRoot g * rowBare A g v := by
    rw [rowStar_weightedArray, rowBare, Matrix.mul_assoc]
  rw [starGram, hr, Matrix.conjTranspose_mul, vertexRoot_star]
  unfold weightedGram
  calc
    _ = (rowBare A g v)ᴴ * (vertexRoot g * vertexRoot g) * rowBare A g v := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [vertexRoot_sq g hg]

lemma centerGram_weightedArray_padded (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    rowStar (weightedArray A g) v * (rowStar (weightedArray A g) v)ᴴ =
      weightedGram (colBare A g v) (fun a => g a.1 a.2) := by
  rw [rowStar_weightedArray]
  unfold colBare weightedGram
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, vertexRoot_star]
  rw [← vertexRoot_sq g hg]
  simp only [Matrix.mul_assoc]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.StarInsertion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hessianCost_zero_direction (P : Matrix ι ι ℂ) : hessianCost P 0 = 0 := by
  unfold hessianCost
  rw [rootCost_eq_of_solution (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P))
    (show sylv (CFC.sqrt P) 0 = 0 by simp [sylv])]
  simp [hsReal]

lemma hessianCost_singleBlock (P K : Matrix ι ι ℂ) (hP : P.PosSemidef) (v : Three)
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) :
    hessianCost (blockD (fun w => if w = v then P else 0))
      (blockD (fun w => if w = v then K else 0)) = hessianCost P K := by
  rw [hessianCost_blockD _ _ (fun w => by split_ifs; exact hP; exact Matrix.PosSemidef.zero)
    (fun w => by split_ifs; exact hsol; exact ⟨0, by simp [sylv]⟩)]
  apply (Finset.sum_eq_single v _ _).trans
  · simp only [ite_true]
  · intro w _ hw
    simp only [ite_eq_right hw, hessianCost_zero_direction]
  · simp

lemma rowStar_blockD_adjoint (W D : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar W v * blockD D * (rowStar W v)ᴴ =
      blockD (fun a => if a = v then
        ∑ w, triangleBlocks W v w * D w * (triangleBlocks W v w)ᴴ else 0) := by
  rw [rowStar_blocks]
  let R : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change blocks R * blocks (Matrix.diagonal D) * (blocks R)ᴴ = _
  rw [← blocks_star, ← blocks_mul, ← blocks_mul]
  unfold blockD
  congr 1
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose]
  change (∑ c, R a c * D c * (R b c)ᴴ) = _
  dsimp only [R]
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst a
    subst b
    simp only [ite_true, Matrix.diagonal_apply_eq]
  · simp [ha, hb, Ne.symm hb]
  · simp [ha, hb]
  · simp only [ite_eq_right ha, zero_mul, Finset.sum_const_zero]
    by_cases hab : a = b
    · subst b
      rw [Matrix.diagonal_apply_eq, ite_eq_right ha]
    · rw [Matrix.diagonal_apply_ne _ hab]

lemma rowStar_singleBlock_adjoint (W : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (v w : Three) :
    rowStar W v * blockD (fun a => if a = w then L else 0) * (rowStar W v)ᴴ =
      blockD (fun a => if a = v then triangleBlocks W v w * L * (triangleBlocks W v w)ᴴ else 0) := by
  rw [rowStar_blockD_adjoint]
  congr 1
  funext a
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma hessianCost_rowStar_singleBlock (W : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (v w : Three) :
    hessianCost (rowStar W v * (rowStar W v)ᴴ)
      (rowStar W v * blockD (fun a => if a = w then L else 0) * (rowStar W v)ᴴ) =
      hessianCost (centerGram W v) ((triangleBlocks W w v)ᴴ * L * triangleBlocks W w v) := by
  rw [rowStar_mul_adjoint, rowStar_singleBlock_adjoint]
  have hsol := sylv_solvable_mono
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((triangleBlocks W w v)ᴴ * triangleBlocks W w v)))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (centerGram W v))).isHermitian
    (sylv_solvable_inserted_gram (triangleBlocks W w v) L)
    (CFC.sqrt_le_sqrt _ _ (edgeGram_le_centerGram W v w))
  rw [← triangleBlocks_adj W w v, Matrix.conjTranspose_conjTranspose]
  exact hessianCost_singleBlock _ _ (centerGram_posSemidef W v) v hsol

lemma rowBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (rowBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      starInsert (weightedArray A g) (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) v := by
  unfold starInsert
  rw [rowStar_weightedArray]
  unfold weightedGram rowBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.mul_assoc]

lemma colBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (colBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      rowStar (weightedArray A g) v *
        blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) *
        (rowStar (weightedArray A g) v)ᴴ := by
  rw [rowStar_weightedArray]
  unfold weightedGram colBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatCost ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma localGram_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localGram A h u p σ v v = starGram (heatArray A h u p σ) v := by
  simp only [localGram, fixedBase, ite_true]
  exact (starGram_weightedArray A _ (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

lemma localGram_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    localGram A h u p σ v w = rowStar (heatArray A h u p σ) v *
      (rowStar (heatArray A h u p σ) v)ᴴ := by
  simp only [localGram, fixedBase, ite_eq_right hw]
  exact (centerGram_weightedArray_padded A _
    (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_eq_insert (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (w : Three) :
    groupFirst h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w =
      fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 *
        (if a.1 = w then score (u a.2) (p a.1) (σ a.1) else 0) := by
  funext a
  simp only [groupFirst, heatWeights]
  split_ifs with ha
  · rw [ha, mul_comm]
  · rw [mul_zero]

lemma localFirst_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localFirst A h u p σ v v =
      starInsert (heatArray A h u p σ) (heatScores u p σ) v := by
  simp only [localFirst, fixedBase, ite_true, groupFirst_eq_insert]
  rw [rowBare_insert A (heatWeights h u p σ)
    (fun w i => if w = v then score (u i) (p w) (σ w) else 0)
    (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v]
  rw [starInsert_eq_insertRow, starInsert_eq_insertRow]
  simp only [heatArray, heatScores, ite_true]

lemma localFirst_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    localFirst A h u p σ v w = rowStar (heatArray A h u p σ) v *
      blockD (fun a => if a = w then heatScores u p σ w else 0) *
      (rowStar (heatArray A h u p σ) v)ᴴ := by
  simp only [localFirst, fixedBase, ite_eq_right hw, groupFirst_eq_insert]
  rw [colBare_insert A (heatWeights h u p σ)
    (fun a i => if a = w then score (u i) (p a) (σ a) else 0)
    (fun a i => (weight_pos hh (hσ a) (u i) (p a)).le) v]
  congr 2
  congr 1
  funext a
  by_cases ha : a = w
  · subst a
    simp [heatScores]
  · simp [ha]

lemma heatCost_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    heatCost A h u p σ v v = hessianCost (starGram (heatArray A h u p σ) v)
      (starInsert (heatArray A h u p σ) (heatScores u p σ) v) := by
  rw [heatCost, localGram_center A hh u p hσ, localFirst_center A hh u p hσ]

lemma heatCost_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    heatCost A h u p σ v w = hessianCost (centerGram (heatArray A h u p σ) v)
      ((triangleBlocks (heatArray A h u p σ) w v)ᴴ * heatScores u p σ w *
        triangleBlocks (heatArray A h u p σ) w v) := by
  rw [heatCost, localGram_other A hh u p hσ hw, localFirst_other A hh u p hσ hw]
  exact hessianCost_rowStar_singleBlock _ _ v w

lemma heatCost_neighbors (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (w : Three) :
    (∑ v, if v = w then 0 else heatCost A h u p σ v w) ≤
      Real.sqrt 2 * heatCost A h u p σ w w := by
  rw [heatCost_center A hh u p hσ]
  convert neighbor_comparison (heatArray A h u p σ) (heatScores u p σ) w using 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = w
  · subst v
    simp [triangleBlocks_diag, hessianCost_zero_direction]
  · rw [ite_eq_right hv, heatCost_other A hh u p hσ (Ne.symm hv)]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneTime ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma planeCost_neighbors (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a) (w : Three) :
    (∑ v, if v = w then 0 else planeIntegral (fun p => heatCost A h u p σ v w) d) ≤
      Real.sqrt 2 * planeIntegral (fun p => heatCost A h u p σ w w) d := by
  have hi := heatPlane_integrable A hh u d hσ
  have hv v : Integrable (fun z : ℝ × ℝ => if v = w then (0:ℝ) else heatCost A h u (chart 2 d z) σ v w) := by
    split_ifs
    · exact integrable_zero _ _ _
    · exact hi.cost 2 v w
  have he : (∑ v, if v = w then 0 else planeIntegral (fun p => heatCost A h u p σ v w) d) =
      ∫ z : ℝ × ℝ, ∑ v, if v = w then 0 else heatCost A h u (chart 2 d z) σ v w := by
    rw [integral_finsetSum _ (fun v _ => hv v)]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp [planeIntegral]
  rw [he, planeIntegral, ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ (fun v _ => hv v))
    ((hi.cost 2 w w).const_mul _) (fun z => heatCost_neighbors A hh u (chart 2 d z) hσ w)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.planeCost_neighbors.{uι} := @_root_.OAI.TriangularHilbert.Heat.planeCost_neighbors.{uι}
