-- Prove2me | solution 1 for GeometryOfGraphs.EuclidDist.corollary_3_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T06:55:10.15492+00:00
-- url     : https://prove2.me/submissions/940d1016-340d-4471-b01e-44ef03fddab9

import Mathlib
import Definitions.Def_GeometryOfGraphs_EuclidDist_EuclideanDistortion

-- BEGIN COMPLETE MODULE ConeSeparation
section

open Set
namespace GeometryOfGraphs.EuclidDist.Proof

lemma separate_cone_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyConvexSpace ℝ E] {C B : Set E} (hc : Convex ℝ C) (hcl : IsClosed C)
    (hzero : (0:E) ∈ C) (hsmul : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ C, r • x ∈ C)
    (hb : Convex ℝ B) (hbc : IsCompact B) (hdis : Disjoint C B) :
    ∃ f : StrongDual ℝ E, (∀ x ∈ C, f x ≤ 0) ∧ ∀ x ∈ B, 0 < f x := by
  obtain ⟨f,u,v,hC,huv,hB⟩ := geometric_hahn_banach_closed_compact hc hcl hb hbc hdis
  have hu : 0 < u := by simpa using hC 0 hzero
  refine ⟨f,?_,fun x hx => hu.trans (huv.trans (hB x hx))⟩
  intro x hx
  by_contra hn
  have hp : 0 < f x := lt_of_not_ge hn
  have hr : 0 ≤ (u + 1) / f x := by positivity
  have hh := hC (((u+1)/f x) • x) (hsmul _ hr x hx)
  rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hp.ne'] at hh
  linarith

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE ConeSeparation

-- BEGIN COMPLETE MODULE MatrixPairing
section

open scoped BigOperators
open Matrix
namespace GeometryOfGraphs.EuclidDist.Proof
variable {X : Type*} [Fintype X]

def matrixPair (A B : Matrix X X ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

lemma matrixPair_transpose (A B : Matrix X X ℝ) :
    matrixPair Aᵀ B = matrixPair A Bᵀ := by
  unfold matrixPair
  rw [Finset.sum_comm]
  rfl

lemma linear_matrixPair (f : (Matrix X X ℝ) →ₗ[ℝ] ℝ) (D : Matrix X X ℝ)
    [DecidableEq X] :
    f D = matrixPair (fun i j => f (Matrix.single i j 1)) D := by
  calc
    f D = ∑ i, ∑ j, f (Matrix.single i j (D i j)) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single D]
      simp only [map_sum]
    _ = matrixPair (fun i j => f (Matrix.single i j 1)) D := by
      unfold matrixPair
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have he : Matrix.single i j (D i j) = D i j • Matrix.single i j (1:ℝ) := by
        simp
      rw [he,map_smul,smul_eq_mul]
      exact mul_comm _ _

noncomputable def symmetrize (A : Matrix X X ℝ) : Matrix X X ℝ := fun i j => (A i j + A j i) / 2

omit [Fintype X] in
lemma symmetrize_symm (A : Matrix X X ℝ) : (symmetrize A).IsSymm := by
  ext i j
  simp [symmetrize,add_comm]

lemma matrixPair_symmetrize (A B : Matrix X X ℝ) :
    matrixPair (symmetrize A) B = (matrixPair A B + matrixPair A Bᵀ) / 2 := by
  have he : matrixPair (symmetrize A) B = (matrixPair A B + matrixPair Aᵀ B) / 2 := by
    simp only [matrixPair,symmetrize,Matrix.transpose_apply]
    simp_rw [add_div,add_mul,Finset.sum_add_distrib]
    congr 1 <;> simp_rw [Finset.sum_div]
    all_goals apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
  rw [he,matrixPair_transpose]

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE MatrixPairing

-- BEGIN COMPLETE MODULE RowZeroMatrix
section

namespace GeometryOfGraphs.EuclidDist.Proof
variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def rowZero (A : Matrix X X ℝ) : Matrix X X ℝ :=
  A - Matrix.diagonal (fun i => ∑ j, A i j)

lemma rowZero_symm (A : Matrix X X ℝ) (hA : A.IsSymm) : (rowZero A).IsSymm := by
  exact hA.sub (Matrix.isSymm_diagonal _)

lemma rowZero_sum (A : Matrix X X ℝ) (i : X) : ∑ j, rowZero A i j = 0 := by
  simp [rowZero,Matrix.diagonal_apply,Finset.sum_sub_distrib]

lemma rowZero_mulVec_one (A : Matrix X X ℝ) : (rowZero A).mulVec (fun _ => 1) = 0 := by
  ext i
  simpa [Matrix.mulVec,dotProduct] using rowZero_sum A i

lemma rowZero_pair (A D : Matrix X X ℝ) (hD : ∀ i, D i i = 0) :
    matrixPair (rowZero A) D = matrixPair A D := by
  simp [matrixPair,rowZero,sub_mul,Finset.sum_sub_distrib,Matrix.diagonal_apply,ite_mul,hD]

omit [DecidableEq X] in
lemma rowZero_quadratic_identity (Q : Matrix X X ℝ) (hQ : Q.IsSymm)
    (hr : ∀ i, ∑ j, Q i j = 0) (z : X → ℝ) :
    matrixPair Q (fun i j => (z i - z j)^2) =
      -2 * (∑ i, ∑ j, z i * Q i j * z j) := by
  have hc (j : X) : ∑ i, Q i j = 0 := by
    calc
      (∑ i, Q i j) = ∑ i, Q j i := Finset.sum_congr rfl (fun i _ => (congrFun (congrFun hQ i) j).symm)
      _ = 0 := hr j
  have h1 : (∑ i, ∑ j, Q i j * z i ^ 2) = 0 := by
    simp_rw [← Finset.sum_mul,hr,zero_mul]
    simp
  have h2 : (∑ i, ∑ j, Q i j * z j ^ 2) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hc,zero_mul]
    simp
  calc
    matrixPair Q (fun i j => (z i-z j)^2) =
        ∑ i, ∑ j, (Q i j * z i^2 + Q i j * z j^2 - 2*(z i*Q i j*z j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intros
      ring
    _ = -2 * (∑ i, ∑ j, z i * Q i j * z j) := by
      simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
      rw [h1,h2]
      ring

lemma rowZero_posSemidef_of_sqdist (A : Matrix X X ℝ) (hA : A.IsSymm)
    (hneg : ∀ z : X → ℝ, matrixPair A (fun i j => (z i-z j)^2) ≤ 0) :
    (rowZero A).PosSemidef := by
  have hs := rowZero_symm A hA
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr hs)
  intro z
  have h : matrixPair (rowZero A) (fun i j => (z i-z j)^2) ≤ 0 := by
    calc
      _ = matrixPair A (fun i j => (z i-z j)^2) := rowZero_pair A _ (by intro i; simp)
      _ ≤ 0 := hneg z
  rw [rowZero_quadratic_identity _ hs (rowZero_sum A)] at h
  have hh : 0 ≤ ∑ i, ∑ j, z i * rowZero A i j * z j := by linarith
  simpa [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc] using hh

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE RowZeroMatrix

-- BEGIN COMPLETE MODULE DistanceBox
section

open Set Matrix
namespace GeometryOfGraphs.EuclidDist.Proof
variable {X : Type*} [Fintype X]

def distanceBox (d : X → X → ℝ) (c : ℝ) : Set (Matrix X X ℝ) :=
  {D | ∀ i j, d i j ^ 2 ≤ D i j ∧ D i j ≤ c^2 * d i j^2}

omit [Fintype X] in
lemma distanceBox_compact (d : X → X → ℝ) (c : ℝ) : IsCompact (distanceBox d c) := by
  exact isCompact_pi_infinite (fun i => isCompact_pi_infinite (fun j =>
    isCompact_Icc (a := d i j^2) (b := c^2*d i j^2)))

omit [Fintype X] in
lemma distanceBox_convex (d : X → X → ℝ) (c : ℝ) : Convex ℝ (distanceBox d c) := by
  intro D hD E hE a b ha hb hab i j
  change d i j^2 ≤ a*D i j+b*E i j ∧ a*D i j+b*E i j ≤ c^2*d i j^2
  constructor
  · calc
      d i j^2 = a*(d i j^2)+b*(d i j^2) := by rw [← add_mul,hab,one_mul]
      _ ≤ a*D i j+b*E i j := add_le_add (mul_le_mul_of_nonneg_left (hD i j).1 ha)
        (mul_le_mul_of_nonneg_left (hE i j).1 hb)
  · calc
      a*D i j+b*E i j ≤ a*(c^2*d i j^2)+b*(c^2*d i j^2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hD i j).2 ha)
          (mul_le_mul_of_nonneg_left (hE i j).2 hb)
      _ = c^2*d i j^2 := by rw [← add_mul,hab,one_mul]

omit [Fintype X] in
lemma distanceBox_nonempty (d : X → X → ℝ) {c : ℝ} (hc : 1 ≤ c) :
    (distanceBox d c).Nonempty := by
  refine ⟨fun i j => d i j^2,fun i j => ⟨le_rfl,?_⟩⟩
  have hh : 1 ≤ c^2 := by nlinarith
  nlinarith [sq_nonneg (d i j)]

omit [Fintype X] in
lemma distanceBox_transpose {d : X → X → ℝ} (hs : ∀ i j, d i j = d j i)
    {c : ℝ} {D : Matrix X X ℝ} (hD : D ∈ distanceBox d c) : Dᵀ ∈ distanceBox d c := by
  intro i j
  simpa only [Matrix.transpose_apply,hs j i] using hD j i

omit [Fintype X] in
lemma distanceBox_diag {d : X → X → ℝ} (hz : ∀ i, d i i = 0)
    {c : ℝ} {D : Matrix X X ℝ} (hD : D ∈ distanceBox d c) (i : X) : D i i = 0 := by
  have hh := hD i i
  simp only [hz i,zero_pow (by decide : 2 ≠ 0),mul_zero] at hh
  exact le_antisymm hh.2 hh.1

noncomputable def boxMinimizer (d : X → X → ℝ) (c : ℝ) (Q : Matrix X X ℝ) : Matrix X X ℝ :=
  fun i j => if Q i j < 0 then c^2*d i j^2 else d i j^2

omit [Fintype X] in
lemma boxMinimizer_mem (d : X → X → ℝ) {c : ℝ} (hc : 1 ≤ c) (Q : Matrix X X ℝ) :
    boxMinimizer d c Q ∈ distanceBox d c := by
  have hb := (distanceBox_nonempty d hc).choose_spec
  have hh : ∀ i j, d i j^2 ≤ c^2*d i j^2 := fun i j => (hb i j).1.trans (hb i j).2
  intro i j
  dsimp [boxMinimizer]
  split <;> exact ⟨by first | exact hh i j | rfl,by first | exact hh i j | rfl⟩

lemma boxMinimizer_pair (d : X → X → ℝ) (c : ℝ) (Q : Matrix X X ℝ) :
    matrixPair Q (boxMinimizer d c Q) =
      (∑ i, ∑ j, if 0 < Q i j then Q i j*d i j^2 else 0) +
        c^2*(∑ i, ∑ j, if Q i j < 0 then Q i j*d i j^2 else 0) := by
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,matrixPair,boxMinimizer]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rcases lt_trichotomy (Q i j) 0 with hn | hz | hp
  · simp only [if_pos hn,if_neg (not_lt_of_ge hn.le)]
    ring
  · simp [hz]
  · simp [if_neg (not_lt_of_ge hp.le),if_pos hp]

lemma signed_sum_le_pair {d : X → X → ℝ} {c : ℝ} (Q D : Matrix X X ℝ)
    (hD : D ∈ distanceBox d c) :
    (∑ i, ∑ j, if 0 < Q i j then Q i j*d i j^2 else 0) +
        c^2*(∑ i, ∑ j, if Q i j < 0 then Q i j*d i j^2 else 0) ≤ matrixPair Q D := by
  rw [← boxMinimizer_pair]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hn : Q i j < 0
  · exact (by simpa only [boxMinimizer,if_pos hn] using
      mul_le_mul_of_nonpos_left (hD i j).2 hn.le)
  · exact (by simpa only [boxMinimizer,if_neg hn] using
      mul_le_mul_of_nonneg_left (hD i j).1 (le_of_not_gt hn))

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE DistanceBox

-- BEGIN COMPLETE MODULE SquaredEuclidean
section

open scoped BigOperators
open Set Matrix
namespace GeometryOfGraphs.EuclidDist.Proof

/-- Squared distance matrices, expressed by conditional negative definiteness. -/
def IsSquaredEuclidean {X : Type*} [Fintype X] (D : Matrix X X ℝ) : Prop :=
  D.IsSymm ∧ (∀ i, D i i = 0) ∧
    ∀ z : X → ℝ, (∑ i, z i) = 0 → ∑ i, ∑ j, z i * D i j * z j ≤ 0

theorem squaredCone_zero {X : Type*} [Fintype X] :
    IsSquaredEuclidean (0 : Matrix X X ℝ) := by
  simp [IsSquaredEuclidean, Matrix.IsSymm]

theorem squaredCone_add {X : Type*} [Fintype X] {D E : Matrix X X ℝ}
    (hD : IsSquaredEuclidean D) (hE : IsSquaredEuclidean E) :
    IsSquaredEuclidean (D + E) := by
  refine ⟨hD.1.add hE.1, fun i => by simp [hD.2.1 i, hE.2.1 i], ?_⟩
  intro z hz
  simpa only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib] using
    add_nonpos (hD.2.2 z hz) (hE.2.2 z hz)

theorem squaredCone_smul {X : Type*} [Fintype X] {D : Matrix X X ℝ}
    (hD : IsSquaredEuclidean D) {r : ℝ} (hr : 0 ≤ r) :
    IsSquaredEuclidean (r • D) := by
  refine ⟨hD.1.smul r, fun i => by simp [hD.2.1 i], ?_⟩
  intro z hz
  have he : (∑ i, ∑ j, z i * (r • D) i j * z j) =
      r * (∑ i, ∑ j, z i * D i j * z j) := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he]
  exact mul_nonpos_of_nonneg_of_nonpos hr (hD.2.2 z hz)

theorem squaredCone_convex {X : Type*} [Fintype X] :
    Convex ℝ {D : Matrix X X ℝ | IsSquaredEuclidean D} := by
  intro D hD E hE a b ha hb hab
  exact squaredCone_add (squaredCone_smul hD ha) (squaredCone_smul hE hb)

theorem squaredCone_closed {X : Type*} [Fintype X] :
    IsClosed {D : Matrix X X ℝ | IsSquaredEuclidean D} := by
  have hs : IsClosed {D : Matrix X X ℝ | D.IsSymm} := by
    change IsClosed {D : Matrix X X ℝ | D.transpose = D}
    apply isClosed_eq <;> fun_prop
  simp only [IsSquaredEuclidean, ofPred_and, ofPred_forall]
  refine hs.inter ((isClosed_iInter fun i => ?_).inter ?_)
  · apply isClosed_eq <;> fun_prop
  · exact isClosed_iInter fun z => isClosed_iInter fun _ =>
      isClosed_le (by fun_prop) continuous_const

theorem squaredCone_one_dimensional {X : Type*} [Fintype X] (v : X → ℝ) :
    IsSquaredEuclidean (fun i j => (v i - v j) ^ 2) := by
  refine ⟨?_, fun i => by simp, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    ring
  · intro z hz
    have he : (∑ i, ∑ j, z i * (v i - v j) ^ 2 * z j) =
        (∑ i, z i * v i ^ 2) * (∑ j, z j) +
        (∑ i, z i) * (∑ j, z j * v j ^ 2) - 2 * (∑ i, z i * v i) ^ 2 := by
      simp only [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intros
      ring
    rw [he, hz]
    nlinarith [sq_nonneg (∑ i, z i * v i)]

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE SquaredEuclidean

-- BEGIN COMPLETE MODULE DistortionSeparator
section

open scoped Matrix.Norms.Elementwise
open Set Matrix
namespace GeometryOfGraphs.EuclidDist.Proof
variable {X : Type*} [Fintype X] [DecidableEq X]

lemma distortion_separator (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d)
    (c : ℝ) (hdis : Disjoint {D : Matrix X X ℝ | IsSquaredEuclidean D} (distanceBox d c)) :
    ∃ Q : Matrix X X ℝ, Q.PosSemidef ∧ Q.mulVec (fun _ => 1) = 0 ∧
      ∀ D ∈ distanceBox d c, 0 < matrixPair Q D := by
  obtain ⟨f,hC,hB⟩ := separate_cone_compact (C := {D : Matrix X X ℝ | IsSquaredEuclidean D})
    squaredCone_convex squaredCone_closed
    squaredCone_zero (fun r hr D hD => squaredCone_smul hD hr)
    (distanceBox_convex d c) (distanceBox_compact d c) hdis
  let A : Matrix X X ℝ := fun i j => f (Matrix.single i j 1)
  have hf (D : Matrix X X ℝ) : f D = matrixPair A D := linear_matrixPair f.toLinearMap D
  have hsymC (D : Matrix X X ℝ) (hD : IsSquaredEuclidean D) :
      matrixPair (symmetrize A) D ≤ 0 := by
    rw [matrixPair_symmetrize,hD.1]
    have hh := hC D hD
    rw [hf] at hh
    linarith
  have hsymB (D : Matrix X X ℝ) (hD : D ∈ distanceBox d c) :
      0 < matrixPair (symmetrize A) D := by
    rw [matrixPair_symmetrize]
    have h1 := hB D hD
    have h2 := hB Dᵀ (distanceBox_transpose hd.2.2.1 hD)
    rw [hf] at h1 h2
    linarith
  refine ⟨rowZero (symmetrize A),?_,rowZero_mulVec_one _,?_⟩
  · exact rowZero_posSemidef_of_sqdist _ (symmetrize_symm A)
      (fun z => hsymC _ (squaredCone_one_dimensional z))
  · intro D hD
    rw [rowZero_pair _ _ (distanceBox_diag hd.1 hD)]
    exact hsymB D hD

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE DistortionSeparator

-- BEGIN COMPLETE MODULE ConditionalGram
section

open scoped BigOperators
open Matrix
namespace GeometryOfGraphs.EuclidDist.Proof

noncomputable def anchorGram {X : Type*} (D : Matrix X X ℝ) (o : X) : Matrix X X ℝ :=
  fun i j => (D i o + D j o - D i j) / 2

theorem anchorGram_distance {X : Type*} [Fintype X] {D : Matrix X X ℝ}
    (hD : IsSquaredEuclidean D) (o i j : X) :
    anchorGram D o i i + anchorGram D o j j - 2 * anchorGram D o i j = D i j := by
  simp only [anchorGram, hD.2.1]
  ring

theorem anchorGram_posSemidef {X : Type*} [Fintype X] {D : Matrix X X ℝ}
    (hD : IsSquaredEuclidean D) (o : X) : (anchorGram D o).PosSemidef := by
  classical
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, anchorGram]
    rw [hD.1.apply i j]
    ring
  · intro z
    let s := ∑ i, z i
    let w : X → ℝ := fun i => z i - if i = o then s else 0
    have hw : ∑ i, w i = 0 := by simp [w, s, Finset.sum_sub_distrib]
    have hh := hD.2.2 w hw
    have he : (∑ i, ∑ j, w i * D i j * w j) =
        (∑ i, ∑ j, z i * D i j * z j) -
        s * (∑ j, D o j * z j) - s * (∑ i, z i * D i o) := by
      have hs0 (f : X → X → ℝ) :
          (∑ i, ∑ j, if i = o then f i j else 0) = ∑ j, f o j := by
        rw [Finset.sum_comm]
        simp
      simp only [w, sub_mul, mul_sub, Finset.sum_sub_distrib]
      simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hD.2.1, Finset.mul_sum]
      rw [hs0]
      ring_nf
    have hs : (∑ j, D o j * z j) = ∑ j, z j * D j o := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hD.1.apply j o]
      ring
    rw [he, hs] at hh
    have hg : star z ⬝ᵥ (anchorGram D o *ᵥ z) =
        s * (∑ i, z i * D i o) - (∑ i, ∑ j, z i * D i j * z j) / 2 := by
      change (∑ i, z i * (∑ j, anchorGram D o i j * z j)) = _
      calc
        _ = ((∑ i, z i * D i o) * (∑ j, z j) +
            (∑ i, z i) * (∑ j, z j * D j o) -
            (∑ i, ∑ j, z i * D i j * z j)) / 2 := by
          simp only [anchorGram, Finset.mul_sum, Finset.sum_mul,
            ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intros
          ring
        _ = _ := by dsimp [s]; ring
    rw [hg]
    linarith

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE ConditionalGram

-- BEGIN COMPLETE MODULE GramRealization
section

open scoped BigOperators MatrixOrder
open Matrix
namespace GeometryOfGraphs.EuclidDist.Proof

theorem gram_realization {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℝ} (hA : A.PosSemidef) :
    ∃ φ : X → EuclideanSpace ℝ (Fin (Fintype.card X)),
      ∀ i j, ‖φ i - φ j‖ ^ 2 = A i i + A j j - 2 * A i j := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  let e := Fintype.equivFin X
  let φ : X → EuclideanSpace ℝ (Fin (Fintype.card X)) :=
    fun i => WithLp.toLp 2 (fun k => B (e.symm k) i)
  refine ⟨φ, fun i j => ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ k, (B (e.symm k) i - B (e.symm k) j) ^ 2) = _
  have hs := e.symm.sum_comp (fun k => (B k i - B k j) ^ 2)
  rw [hs]
  rw [hB]
  simp only [star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

theorem squaredCone_realization {X : Type*} [Fintype X] [DecidableEq X]
    {D : Matrix X X ℝ} (hD : IsSquaredEuclidean D) :
    ∃ φ : X → EuclideanSpace ℝ (Fin (Fintype.card X)),
      ∀ i j, ‖φ i - φ j‖ ^ 2 = D i j := by
  cases isEmpty_or_nonempty X with
  | inl h => exact ⟨fun _ => 0, fun i => isEmptyElim i⟩
  | inr h =>
    let o := Classical.choice h
    obtain ⟨φ, hφ⟩ := gram_realization (anchorGram_posSemidef hD o)
    exact ⟨φ, fun i j => (hφ i j).trans (anchorGram_distance hD o i j)⟩

theorem squaredCone_sum {X I : Type*} [Fintype X] (s : Finset I)
    (D : I → Matrix X X ℝ) (hD : ∀ k ∈ s, IsSquaredEuclidean (D k)) :
    IsSquaredEuclidean (∑ k ∈ s, D k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (squaredCone_zero (X := X))
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact squaredCone_add (hD k (Finset.mem_insert_self _ _))
      (ih fun j hj => hD j (Finset.mem_insert_of_mem hj))

theorem squaredCone_euclidean {X I : Type*} [Fintype X] [Fintype I]
    (φ : X → EuclideanSpace ℝ I) :
    IsSquaredEuclidean (fun i j => ‖φ i - φ j‖ ^ 2) := by
  have he : (fun i j => ‖φ i - φ j‖ ^ 2) =
      ∑ k, (fun i j => (φ i k - φ j k) ^ 2) := by
    funext i j
    simp only [Finset.sum_apply, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
  rw [he]
  exact squaredCone_sum Finset.univ
    (fun k => fun i j => (φ i k - φ j k) ^ 2)
    (fun k _ => squaredCone_one_dimensional (fun i => φ i k))

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE GramRealization

-- BEGIN COMPLETE MODULE EmbeddingSquared
section

open scoped BigOperators
open Matrix
namespace GeometryOfGraphs.EuclidDist.Proof

theorem embedsEuclidean_iff_squared {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d)
    (c : ℝ) (hc : 1 ≤ c) :
    EmbedsEuclidean d c ↔ ∃ D : Matrix X X ℝ, IsSquaredEuclidean D ∧
      ∀ i j, d i j ^ 2 ≤ D i j ∧ D i j ≤ c ^ 2 * d i j ^ 2 := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  constructor
  · rintro ⟨m, φ, hφ⟩
    let ψ : X → EuclideanSpace ℝ (Fin m) := fun i => c • φ i
    refine ⟨fun i j => ‖ψ i - ψ j‖ ^ 2, squaredCone_euclidean ψ, ?_⟩
    intro i j
    have hn : ‖ψ i - ψ j‖ = c * ‖φ i - φ j‖ := by
      simp only [ψ, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    change d i j ^ 2 ≤ ‖ψ i - ψ j‖ ^ 2 ∧ ‖ψ i - ψ j‖ ^ 2 ≤ c ^ 2 * d i j ^ 2
    rw [hn]
    constructor
    · exact (sq_le_sq₀ (hd.2.1 i j) (mul_nonneg hc0.le (norm_nonneg _))).2 (hφ i j).2
    · have hh := mul_le_mul_of_nonneg_left (hφ i j).1 hc0.le
      have hh' := (sq_le_sq₀ (mul_nonneg hc0.le (norm_nonneg _))
        (mul_nonneg hc0.le (hd.2.1 i j))).2 hh
      simpa only [mul_pow] using hh'
  · rintro ⟨D, hD, hbox⟩
    obtain ⟨φ, hφ⟩ := squaredCone_realization hD
    refine ⟨Fintype.card X, fun i => c⁻¹ • φ i, ?_⟩
    intro i j
    have hlow : d i j ≤ ‖φ i - φ j‖ :=
      (sq_le_sq₀ (hd.2.1 i j) (norm_nonneg _)).1 (by rw [hφ]; exact (hbox i j).1)
    have hupp : ‖φ i - φ j‖ ≤ c * d i j := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc0.le (hd.2.1 i j))).1
      rw [hφ, mul_pow]
      exact (hbox i j).2
    have hn : ‖c⁻¹ • φ i - c⁻¹ • φ j‖ = ‖φ i - φ j‖ / c := by
      simp only [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0,
        div_eq_mul_inv, mul_comm]
    rw [hn]
    constructor
    · exact (div_le_iff₀ hc0).2 (by simpa only [mul_comm] using hupp)
    · calc
        d i j ≤ ‖φ i - φ j‖ := hlow
        _ = c * (‖φ i - φ j‖ / c) := by field_simp

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE EmbeddingSquared

-- BEGIN COMPLETE MODULE SquaredPairing
section

open scoped BigOperators
open Matrix
namespace GeometryOfGraphs.EuclidDist.Proof

theorem psd_pairing_one_dimensional_nonpos {X : Type*} [Fintype X]
    {Q : Matrix X X ℝ} (hQ : Q.PosSemidef)
    (hrow : Q.mulVec (fun _ => (1 : ℝ)) = 0) (v : X → ℝ) :
    ∑ i, ∑ j, Q i j * (v i - v j) ^ 2 ≤ 0 := by
  have hr (i : X) : ∑ j, Q i j = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hrow i
  have hs (i j : X) : Q j i = Q i j := by
    simpa using hQ.1.apply i j
  have hcol (j : X) : ∑ i, Q i j = 0 := by
    simpa only [hs] using hr j
  have h1 : (∑ i, ∑ j, Q i j * v i ^ 2) = 0 := by
    simp_rw [← Finset.sum_mul, hr, zero_mul]
    simp
  have h2 : (∑ i, ∑ j, Q i j * v j ^ 2) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, zero_mul]
    simp
  have he : (∑ i, ∑ j, Q i j * (v i - v j) ^ 2) =
      (∑ i, ∑ j, Q i j * v i ^ 2) +
      (∑ i, ∑ j, Q i j * v j ^ 2) -
      2 * (star v ⬝ᵥ (Q *ᵥ v)) := by
    simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he, h1, h2]
  linarith [hQ.dotProduct_mulVec_nonneg v]

theorem psd_pairing_sqdist_nonpos {X : Type*} [Fintype X] [DecidableEq X]
    {D Q : Matrix X X ℝ} (hD : IsSquaredEuclidean D) (hQ : Q.PosSemidef)
    (hrow : Q.mulVec (fun _ => (1 : ℝ)) = 0) :
    ∑ i, ∑ j, Q i j * D i j ≤ 0 := by
  obtain ⟨φ, hφ⟩ := squaredCone_realization hD
  simp_rw [← hφ, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k, ∑ j, Q i j * (φ i k - φ j k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, Q i j * (φ i k - φ j k) ^ 2 := Finset.sum_comm
    _ ≤ 0 := Finset.sum_nonpos fun k _ =>
      psd_pairing_one_dimensional_nonpos hQ hrow (fun i => φ i k)

end GeometryOfGraphs.EuclidDist.Proof
end
-- END COMPLETE MODULE SquaredPairing

-- BEGIN COMPLETE MODULE DistortionRoot
section

namespace GeometryOfGraphs.EuclidDist

/-- Corollary 3.5 (p. 224), first sentence: a finite metric space `(X, d)` embeds in a Euclidean
space with distortion at most `c` iff for every positive semidefinite `Q` with `Q · 1 = 0`,
`∑_{q_ij > 0} q_ij d_ij^2 + c^2 ∑_{q_ij < 0} q_ij d_ij^2 ≤ 0` (sums over ordered pairs). -/
theorem corollary_3_5 {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    EmbedsEuclidean d c ↔
      ∀ Q : Matrix X X ℝ, Q.PosSemidef → Q.mulVec (fun _ => (1 : ℝ)) = 0 →
        (∑ i, ∑ j, if 0 < Q i j then Q i j * d i j ^ 2 else 0) +
          c ^ 2 * (∑ i, ∑ j, if Q i j < 0 then Q i j * d i j ^ 2 else 0) ≤ 0 := by
  rw [Proof.embedsEuclidean_iff_squared d hd c hc]
  constructor
  · rintro ⟨D,hD,hbox⟩ Q hQ hrow
    exact (Proof.signed_sum_le_pair Q D hbox).trans
      (Proof.psd_pairing_sqdist_nonpos hD hQ hrow)
  · intro h
    by_contra hn
    have hdis : Disjoint {D : Matrix X X ℝ | Proof.IsSquaredEuclidean D} (Proof.distanceBox d c) := by
      rw [Set.disjoint_left]
      intro D hD hbox
      exact hn ⟨D,hD,hbox⟩
    obtain ⟨Q,hQ,hrow,hpos⟩ := Proof.distortion_separator d hd c hdis
    have hp := hpos (Proof.boxMinimizer d c Q) (Proof.boxMinimizer_mem d hc Q)
    rw [Proof.boxMinimizer_pair] at hp
    exact (not_lt_of_ge (h Q hQ hrow)) hp


end GeometryOfGraphs.EuclidDist

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    GeometryOfGraphs.EuclidDist.EmbedsEuclidean d c ↔
      ∀ Q : Matrix X X ℝ, Q.PosSemidef → Q.mulVec (fun _ => (1 : ℝ)) = 0 →
        (∑ i, ∑ j, if 0 < Q i j then Q i j * d i j ^ 2 else 0) +
          c ^ 2 * (∑ i, ∑ j, if Q i j < 0 then Q i j * d i j ^ 2 else 0) ≤ 0 := GeometryOfGraphs.EuclidDist.corollary_3_5 d hd c hc
end
-- END COMPLETE MODULE DistortionRoot
