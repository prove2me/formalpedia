-- Prove2me | solution 1 for OAI.ThreeManifold.Neck.curvatureTerm_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:23:17.169491+00:00
-- url     : https://prove2.me/submissions/cc722094-248b-4746-bbfa-79ca27751838

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L705-L736
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Neck.curvatureTerm_product. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Theorems.Thm_OAI_ThreeManifold_Neck_pairing_hasDerivAt

-- ---- from OAI.Geometry.ConjugatePoints.Neck ----
namespace OAI

noncomputable section

/-!
# Tensor identities and the local and torus neck metrics.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff

namespace ThreeManifold.Tensor
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma derivative_contract (D : n → n → n → ℝ) (z l : n) (u v w : n → ℝ) :
    (∑ k, ∑ i, ∑ j, (if i = z then (1 : ℝ) else 0) * D l j k * w k * u i * v j) =
      u z * contract D v w l := by
  calc
    (∑ k, ∑ i, ∑ j, (if i = z then (1 : ℝ) else 0) * D l j k * w k * u i * v j) =
        ∑ k, ∑ j, D l j k * w k * u z * v j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp [ite_mul]
    _ = u z * contract D v w l := by
      rw [contract, Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring

omit [DecidableEq n] in
lemma composition_contract (C : n → n → n → ℝ) (l : n) (u v w : n → ℝ) :
    (∑ k, ∑ i, ∑ j, (∑ a, C l i a * C a j k) * w k * u i * v j) =
      contract C u (contract C v w) l := by
  simp only [contract, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ k, ∑ a, C l i a * C a j k * w k * u i * v j) =
        ∑ a, ∑ j, ∑ k, C l i a * C a j k * w k * u i * v j := by
      simp only [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun k a =>
        C l i a * C a _ k * w k * u i * v _)]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma curvature_contract (C D : n → n → n → ℝ) (z l : n) (u v w : n → ℝ) :
    (∑ k, ∑ i, ∑ j,
       ((if i = z then (1 : ℝ) else 0) * D l j k -
         (if j = z then (1 : ℝ) else 0) * D l i k +
         ∑ a, (C l i a * C a j k - C l j a * C a i k)) * w k * u i * v j) =
      u z * contract D v w l - v z * contract D u w l +
        contract C u (contract C v w) l - contract C v (contract C u w) l := by
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hd' : (∑ k, ∑ i, ∑ j,
      (if j = z then (1 : ℝ) else 0) * D l i k * w k * u i * v j) =
      v z * contract D u w l := by
    convert derivative_contract D z l v u w using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc' : (∑ k, ∑ i, ∑ j,
      (∑ a, C l j a * C a i k) * w k * u i * v j) =
      contract C v (contract C u w) l := by
    convert composition_contract C l v u w using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [derivative_contract, hd', composition_contract, hc']
  ring

end ThreeManifold.Tensor

namespace ThreeManifold.Neck
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

lemma matrix_mul_hasDerivAt {M N : ℝ → TMat} {M' N' : TMat} {s : ℝ}
    (hM : HasDerivAt M M' s) (hN : HasDerivAt N N' s) :
    HasDerivAt (fun r => M r * N r) (M' * N s + M s * N') s := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h (k : Fin 2) (_hk : k ∈ Finset.univ) :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hN k) j)
  convert! HasDerivAt.fun_sum h using 1
  simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

lemma mulVec_hasDerivAt {M : ℝ → TMat} {u : ℝ → TVec} {M' : TMat} {u' : TVec} {s : ℝ}
    (hM : HasDerivAt M M' s) (hu : HasDerivAt u u' s) :
    HasDerivAt (fun r => M r *ᵥ u r) (M' *ᵥ u s + M s *ᵥ u') s := by
  apply hasDerivAt_pi.mpr
  intro i
  have h (k : Fin 2) (_hk : k ∈ Finset.univ) :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) k).mul (hasDerivAt_pi.mp hu k)
  convert! HasDerivAt.fun_sum h using 1
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Finset.sum_add_distrib]

lemma split_join (u : Vec) : splitVector (joinVector u) = u := by
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

lemma blockMatrix_mul (P Q : TMat) :
    blockMatrix P * blockMatrix Q = blockMatrix (P * Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
lemma blockMatrix_one : blockMatrix (1 : TMat) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
lemma blockMatrix_inverse {P Q : TMat} (hQP : Q * P = 1) :
    (blockMatrix Q)⁻¹ = blockMatrix P := by
  apply Matrix.inv_eq_right_inv
  rw [blockMatrix_mul, hQP, blockMatrix_one]

lemma block_entry_hasDerivAt {Q : ℝ → TMat} {A : TMat} {s : ℝ}
    (hQ : HasDerivAt Q A s) (i j : Fin 3) :
    HasDerivAt (fun r => blockMatrix (Q r) i j) (blockJet A i j) s := by
  have h (k l : Fin 2) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ k) l
  fin_cases i <;> fin_cases j <;>
    simp only [blockMatrix, blockJet] <;>
    first | exact hasDerivAt_const _ _ | exact h _ _

lemma coordPartial_block {Q : ℝ → TMat} {A : TMat} {x : E3}
    (hQ : HasDerivAt Q A (x 0)) (i j k : Fin 3) :
    coordPartial (fun y => blockMatrix (Q (y 0)) i j) x k =
      (if k = 0 then 1 else 0) * blockJet A i j := by
  have h := (block_entry_hasDerivAt hQ i j).hasFDerivAt.comp x
    (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  change HasFDerivAt (fun y : E3 => blockMatrix (Q (y 0)) i j) _ x at h
  change (fderiv ℝ (fun y : E3 => blockMatrix (Q (y 0)) i j) x) (basisVector k) = _
  rw [h.fderiv]
  fin_cases k <;> simp [basisVector, ContinuousLinearMap.comp_apply]

lemma coordPartial_congr_germ {f h : E3 → ℝ} {x : E3}
    (heq : f =ᶠ[nhds x] h) (i : Fin 3) :
    coordPartial f x i = coordPartial h x i := by
  rw [coordPartial, coordPartial, heq.fderiv_eq]

lemma christoffel_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q : ℝ → TMat} {P A : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hQ : HasDerivAt Q A (x 0)) (hQP : Q (x 0) * P = 1)
    (i j k : Fin 3) :
    christoffel g c x i j k = (1 / 2 : ℝ) * ∑ l : Fin 3,
      blockMatrix P i l *
        ((if j = 0 then 1 else 0) * blockJet A l k +
         (if k = 0 then 1 else 0) * blockJet A l j -
         (if l = 0 then 1 else 0) * blockJet A j k) := by
  have hentry (a b d : Fin 3) :
      coordPartial (fun y => metricMatrix g c y a b) x d =
        (if d = 0 then 1 else 0) * blockJet A a b := by
    rw [coordPartial_congr_germ
      (Filter.Eventually.mono hg (fun _ h => congrFun (congrFun h a) b))]
    exact coordPartial_block hQ a b d
  rw [christoffel, hg.eq_of_nhds, blockMatrix_inverse hQP]
  simp only [hentry]

lemma connectionTerm_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q : ℝ → TMat} {P A : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hQ : HasDerivAt Q A (x 0)) (hQP : Q (x 0) * P = 1)
    (hA : Aᵀ = A) (u v : E3) :
    connectionTerm g c x u v =
      joinVector (gamma P A (splitVector u) (splitVector v)) := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  ext i
  fin_cases i <;>
    simp [connectionTerm, christoffel_product g c hg hQ hQP,
      blockMatrix, blockJet, joinVector, gamma, splitVector, pairing,
      dotProduct, Matrix.mulVec, Fin.sum_univ_succ, h10] <;> ring

lemma join_gamma_hasDerivAt {P A : ℝ → TMat} {B : TMat} {s : ℝ}
    (hP : HasDerivAt P (-P s * A s * P s) s) (hA : HasDerivAt A B s)
    (U V : Vec) :
    HasDerivAt (fun r => joinVector (gamma (P r) (A r) U V))
      (joinVector (gammaPrime (P s) (A s) B U V)) s := by
  have hPA : HasDerivAt (fun r => P r * A r)
      (P s * B - P s * A s * P s * A s) s := by
    convert! matrix_mul_hasDerivAt hP hA using 1
    simp only [neg_mul, sub_eq_add_neg, add_comm]
  have hU := mulVec_hasDerivAt hPA (hasDerivAt_const s U.2)
  have hV := mulVec_hasDerivAt hPA (hasDerivAt_const s V.2)
  simp only [Matrix.mulVec_zero, add_zero] at hU hV
  have htor := ((hV.const_smul U.1).add (hU.const_smul V.1)).const_smul (1 / 2 : ℝ)
  have hpair := pairing_hasDerivAt hA (hasDerivAt_const s U.2)
    (hasDerivAt_const s V.2)
  simp only [pairing, dotProduct_zero, zero_dotProduct, Matrix.mulVec_zero,
    zero_add, add_zero] at hpair
  have hbase := hpair.const_mul (-(1 / 2 : ℝ))
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hbase using 1
  · convert! hasDerivAt_pi.mp htor 0 using 1
    funext r
    change ((1 / 2 : ℝ) • (U.1 • (P r *ᵥ (A r *ᵥ V.2)) +
      V.1 • (P r *ᵥ (A r *ᵥ U.2)))) 0 = _
    simp only [Matrix.mulVec_mulVec, Pi.smul_apply, Pi.add_apply]
  · convert! hasDerivAt_pi.mp htor 1 using 1
    funext r
    change ((1 / 2 : ℝ) • (U.1 • (P r *ᵥ (A r *ᵥ V.2)) +
      V.1 • (P r *ᵥ (A r *ᵥ U.2)))) 1 = _
    simp only [Matrix.mulVec_mulVec, Pi.smul_apply, Pi.add_apply]

lemma connectionTerm_basis {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    (x : E3) (i j k : Fin 3) :
    connectionTerm g c x (basisVector j) (basisVector k) i = christoffel g c x i j k := by
  simp [connectionTerm, basisVector, Pi.single_apply]

lemma coordPartial_join_gamma {P A : ℝ → TMat} {B : TMat} {x : E3}
    (hP : HasDerivAt P (-P (x 0) * A (x 0) * P (x 0)) (x 0))
    (hA : HasDerivAt A B (x 0)) (U V : Vec) (i k : Fin 3) :
    coordPartial (fun y => joinVector (gamma (P (y 0)) (A (y 0)) U V) i) x k =
      (if k = 0 then 1 else 0) *
        joinVector (gammaPrime (P (x 0)) (A (x 0)) B U V) i := by
  have h := (hasDerivAt_pi.mp (join_gamma_hasDerivAt hP hA U V) i).hasFDerivAt.comp x
    (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  change HasFDerivAt
    (fun y : E3 => joinVector (gamma (P (y 0)) (A (y 0)) U V) i) _ x at h
  change (fderiv ℝ
    (fun y : E3 => joinVector (gamma (P (y 0)) (A (y 0)) U V) i) x) (basisVector k) = _
  rw [h.fderiv]
  fin_cases k <;> simp [basisVector, ContinuousLinearMap.comp_apply]

lemma christoffel_product_germ {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q P A : ℝ → TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hj : ∀ᶠ r in nhds (x 0), HasDerivAt Q (A r) r ∧ Q r * P r = 1 ∧ (A r)ᵀ = A r)
    (i j k : Fin 3) :
    (fun y => christoffel g c y i j k) =ᶠ[nhds x]
      (fun y => joinVector (gamma (P (y 0)) (A (y 0))
        (splitVector (basisVector j)) (splitVector (basisVector k))) i) := by
  have hjx := (continuous_apply (0 : Fin 3)).continuousAt.tendsto.eventually hj
  filter_upwards [hg.eventuallyEq_nhds, hjx] with y hgy hy
  have h := congrFun (connectionTerm_product g c hgy hy.1 hy.2.1 hy.2.2
    (basisVector j) (basisVector k)) i
  rwa [connectionTerm_basis] at h

lemma christoffel_partial_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q P A : ℝ → TMat} {B : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hj : ∀ᶠ r in nhds (x 0), HasDerivAt Q (A r) r ∧ Q r * P r = 1 ∧ (A r)ᵀ = A r)
    (hP : HasDerivAt P (-P (x 0) * A (x 0) * P (x 0)) (x 0))
    (hA : HasDerivAt A B (x 0)) (i j k d : Fin 3) :
    coordPartial (fun y => christoffel g c y i j k) x d =
      (if d = 0 then 1 else 0) * joinVector (gammaPrime (P (x 0)) (A (x 0)) B
        (splitVector (basisVector j)) (splitVector (basisVector k))) i := by
  rw [coordPartial_congr_germ (christoffel_product_germ g c hg hj i j k)]
  exact coordPartial_join_gamma hP hA _ _ i d

lemma join_add (U V : Vec) : joinVector (U + V) = joinVector U + joinVector V := by
  ext i
  fin_cases i <;> rfl
lemma join_sub (U V : Vec) : joinVector (U - V) = joinVector U - joinVector V := by
  ext i
  fin_cases i <;> rfl
lemma join_smul (r : ℝ) (U : Vec) : joinVector (r • U) = r • joinVector U := by
  ext i
  fin_cases i <;> rfl

lemma gammaPrime_contract (P A B : TMat) (u v : E3) :
    Tensor.contract (fun l i j => joinVector (gammaPrime P A B
      (splitVector (basisVector i)) (splitVector (basisVector j))) l) u v =
    joinVector (gammaPrime P A B (splitVector u) (splitVector v)) := by
  unfold gammaPrime
  generalize P * B - P * A * P * A = H
  ext l
  fin_cases l <;>
    simp [Tensor.contract, joinVector, splitVector, basisVector, pairing,
      dotProduct, Matrix.mulVec, Fin.sum_univ_succ] <;> ring

lemma curvatureTerm_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q P A : ℝ → TMat} {B : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hj : ∀ᶠ r in nhds (x 0), HasDerivAt Q (A r) r ∧ Q r * P r = 1 ∧ (A r)ᵀ = A r)
    (hP : HasDerivAt P (-P (x 0) * A (x 0) * P (x 0)) (x 0))
    (hA : HasDerivAt A B (x 0)) (u v w : E3) :
    curvatureTerm g c x u v w =
      joinVector (curvatureJet (P (x 0)) (A (x 0)) B
        (splitVector u) (splitVector v) (splitVector w)) := by
  let C := christoffel g c x
  let D := fun l i j => joinVector (gammaPrime (P (x 0)) (A (x 0)) B
    (splitVector (basisVector i)) (splitVector (basisVector j))) l
  have hd (i j k d : Fin 3) := christoffel_partial_product g c hg hj hP hA i j k d
  have h0 := hj.self_of_nhds
  have hc (U V : E3) : Tensor.contract C U V =
      joinVector (gamma (P (x 0)) (A (x 0)) (splitVector U) (splitVector V)) :=
    connectionTerm_product g c hg h0.1 h0.2.1 h0.2.2 U V
  have hdc (U V : E3) : Tensor.contract D U V =
      joinVector (gammaPrime (P (x 0)) (A (x 0)) B (splitVector U) (splitVector V)) :=
    gammaPrime_contract _ _ _ _ _
  have hcurv : curvatureTerm g c x u v w =
      u 0 • Tensor.contract D v w - v 0 • Tensor.contract D u w +
        Tensor.contract C u (Tensor.contract C v w) -
        Tensor.contract C v (Tensor.contract C u w) := by
    ext l
    simp only [curvatureTerm, curvatureCoefficient, hd, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Tensor.curvature_contract C D 0 l u v w
  rw [hcurv]
  simp only [hdc, hc, split_join, curvatureJet, join_sub, join_add, join_smul]
  rfl

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

end ThreeManifold.Cometric

namespace ThreeManifold.LocalNeck

section
open Manifold Bundle Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

open Cometric Neck

end

open Manifold Bundle Set Filter Cometric Neck Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end ThreeManifold.LocalNeck

namespace ThreeManifold.TorusNeck

section
open Set Filter Topology Manifold Bundle
open scoped ContDiff Matrix.Norms.Elementwise
open LocalNeck QuotientConstruction

open Cometric Neck
end

open Set Filter Manifold Bundle Neck Cometric LocalNeck Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.TorusNeck

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Matrix
open scoped Matrix Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.Neck.curvatureTerm_product := @_root_.OAI.ThreeManifold.Neck.curvatureTerm_product
