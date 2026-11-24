-- Prove2me | solution 1 for LocalPush.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T09:47:20.739835+00:00
-- url     : https://prove2.me/submissions/d2fe28e7-13af-42fb-825b-5594c09b65bc

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset Matrix

namespace LocalPush.Aux

/-- Minimum principle for Z-matrices with positive row sums. -/
theorem zmat_nonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j)
    (y : ι → ℝ) (hy : ∀ i, 0 ≤ (M *ᵥ y) i) : ∀ i, 0 ≤ y i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i0, hi0⟩ := hcon
  obtain ⟨v, -, hv⟩ := Finset.exists_min_image Finset.univ y ⟨i0, Finset.mem_univ _⟩
  have hyv : y v < 0 := lt_of_le_of_lt (hv i0 (Finset.mem_univ _)) hi0
  have h1 : (M *ᵥ y) v ≤ (∑ j, M v j) * y v := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : v = j
    · subst hj; exact le_refl _
    · have := hoff v j hj
      have := hv j (Finset.mem_univ _)
      nlinarith
  have h2 : (∑ j, M v j) * y v < 0 := mul_neg_of_pos_of_neg (hrow v) hyv
  linarith [hy v]

theorem zmat_injective {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j) :
    Function.Injective M.mulVec := by
  intro x y hxy
  have h0 : M *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have a := zmat_nonneg M hoff hrow (x - y) (by intro i; rw [h0]; simp)
  have b := zmat_nonneg M hoff hrow (y - x) (by intro i; rw [← neg_sub, Matrix.mulVec_neg, h0]; simp)
  funext i
  have := a i; have := b i
  simp only [Pi.sub_apply] at *
  linarith

theorem zmat_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j) : IsUnit M.det :=
  (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_injective_iff_isUnit.mp (zmat_injective M hoff hrow))

theorem zmat_inv_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0) (hrow : ∀ i, 0 < ∑ j, M i j) (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∀ i, 0 ≤ (M⁻¹ *ᵥ y) i := by
  apply zmat_nonneg M hoff hrow
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (zmat_isUnit_det M hoff hrow), Matrix.one_mulVec]
  exact hy

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem deg_pos (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (v : V) : 0 < deg G v := by
  unfold deg; exact_mod_cast hG v

theorem Lα_apply (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (i j : V) :
    Lα G α i j = (if i = j then deg G i else 0) - (1 - α) * (if G.Adj i j then 1 else 0) := by
  simp [Lα, degM, adjM, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]

theorem Lα_off (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (hα1 : α < 1) (i j : V) (h : i ≠ j) :
    Lα G α i j ≤ 0 := by
  rw [Lα_apply, if_neg h]; split_ifs <;> nlinarith

theorem Lα_rowsum (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (i : V) :
    ∑ j, Lα G α i j = α * deg G i := by
  simp only [Lα_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ← Finset.mul_sum]
  have : (∑ j, if G.Adj i j then (1:ℝ) else 0) = deg G i := by
    rw [Finset.sum_boole]; simp [deg, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  rw [this]; ring

theorem Lα_isUnit_det (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) : IsUnit (Lα G α).det :=
  zmat_isUnit_det _ (Lα_off G α hα1) (fun i => by rw [Lα_rowsum]; exact mul_pos hα0 (deg_pos G hG i))

theorem Lα_symm (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) : (Lα G α)ᵀ = Lα G α := by
  ext i j; simp only [Matrix.transpose_apply, Lα_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]; simp [G.adj_comm]

/-- `I − (1−α)AD⁻¹ = L_α D⁻¹`. -/
theorem M_eq (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ) :
    (1 : Matrix V V ℝ) - (1 - α) • (adjM G * Dinv G) = Lα G α * Dinv G := by
  rw [Lα, Matrix.sub_mul, Matrix.smul_mul]
  congr 1
  rw [degM, Dinv, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, (deg_pos G hG i).ne']

theorem Dinv_isUnit_det (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) :
    IsUnit (Dinv G).det := by
  rw [Dinv, Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (deg_pos G hG i).ne')

theorem Dinv_inv (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) :
    (Dinv G)⁻¹ = degM G := by
  rw [Matrix.inv_eq_left_inv]
  rw [degM, Dinv, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, (deg_pos G hG i).ne']

theorem M_isUnit_det (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    IsUnit ((1 : Matrix V V ℝ) - (1 - α) • (adjM G * Dinv G)).det := by
  rw [M_eq G hG, Matrix.det_mul]
  exact (Lα_isUnit_det G hG α hα0 hα1).mul (Dinv_isUnit_det G hG)

theorem Lα_colsum (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (j : V) :
    ∑ i, Lα G α i j = α * deg G j := by
  rw [← Lα_rowsum G α j]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [← Lα_symm G α]
  rfl

theorem Linv_symm (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (i j : V) :
    (Lα G α)⁻¹ i j = (Lα G α)⁻¹ j i := by
  have : ((Lα G α)⁻¹)ᵀ = (Lα G α)⁻¹ := by rw [Matrix.transpose_nonsing_inv, Lα_symm]
  conv_lhs => rw [← this]
  rfl

end LocalPush.Aux


namespace LocalPush.Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Lα_mulVec_apply (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (x : V → ℝ) (v : V) :
    (Lα G α *ᵥ x) v = deg G v * x v - (1 - α) * ∑ w ∈ univ.filter (G.Adj v), x w := by
  simp only [Matrix.mulVec, dotProduct, Lα_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, one_mul, mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_filter]

theorem resid_apply (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (s : V) (x : V → ℝ) (v : V) :
    resid G α s x v = e s v - α⁻¹ * (deg G v * x v - (1 - α) * ∑ w ∈ univ.filter (G.Adj v), x w) := by
  simp [resid, Lα_mulVec_apply]

theorem sum_Lα_mulVec (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (x : V → ℝ) :
    ∑ v, (Lα G α *ᵥ x) v = α * ∑ v, deg G v * x v := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro u _
  rw [← Finset.sum_mul, Lα_colsum]; ring

theorem mass_identity (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α : ℝ) (hα0 : 0 < α)
    (x : V → ℝ) : ∑ v, deg G v * x v + ∑ v, resid G α s x v = 1 := by
  have : ∑ v, resid G α s x v = 1 - α⁻¹ * ∑ v, (Lα G α *ᵥ x) v := by
    simp [resid, Finset.sum_sub_distrib, e, Finset.mul_sum]
  rw [this, sum_Lα_mulVec]; field_simp; ring

theorem resid_outside (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α : ℝ) (x : V → ℝ)
    (S : Finset V) (hx : ∀ v ∉ S, x v = 0) (hs : s ∈ S) (v : V) (hv : v ∉ S) :
    resid G α s x v = (1 - α) / α * ∑ u ∈ S.filter (G.Adj v), x u := by
  rw [resid_apply, hx v hv]
  have hsv : s ≠ v := fun h => hv (h ▸ hs)
  have he : e s v = 0 := by simp [e, Pi.single_apply, hsv.symm]
  have hsum : ∑ w ∈ univ.filter (G.Adj v), x w = ∑ u ∈ S.filter (G.Adj v), x u := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    intro w _ hw; simp [hx w hw]
  rw [he, hsum]; ring

end LocalPush.Aux


namespace LocalPush.Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_nbr_ge (G : SimpleGraph V) [DecidableRel G.Adj] (y : V → ℝ) (v : V) (m : ℝ)
    (hm : ∀ w, m ≤ y w) : deg G v * m ≤ ∑ w ∈ univ.filter (G.Adj v), y w := by
  have hc : ((univ.filter (G.Adj v)).card : ℝ) = deg G v := by
    simp [deg, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  rw [← hc, ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun w _ => hm w

/-- Restricted minimum principle for `L_α`. -/
theorem Lα_minp (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (S : Finset V) (y : V → ℝ) (hy0 : ∀ v ∉ S, y v = 0)
    (hpos : ∀ v ∈ S, 0 ≤ (Lα G α *ᵥ y) v) : ∀ v, 0 ≤ y v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i0, hi0⟩ := hcon
  obtain ⟨v, -, hv⟩ := Finset.exists_min_image Finset.univ y ⟨i0, Finset.mem_univ _⟩
  have hyv : y v < 0 := lt_of_le_of_lt (hv i0 (Finset.mem_univ _)) hi0
  have hvS : v ∈ S := by
    by_contra h; rw [hy0 v h] at hyv; exact lt_irrefl _ hyv
  have h1 := hpos v hvS
  rw [Lα_mulVec_apply] at h1
  have h2 := sum_nbr_ge G y v (y v) (fun w => hv w (Finset.mem_univ _))
  have hd := deg_pos G hG v
  have : 0 < 1 - α := by linarith
  nlinarith [mul_neg_of_pos_of_neg hd hyv]

theorem Lα_minp_eq (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (S : Finset V) (y z : V → ℝ) (hy0 : ∀ v ∉ S, y v = 0)
    (hz0 : ∀ v ∉ S, z v = 0) (h : ∀ v ∈ S, (Lα G α *ᵥ y) v = (Lα G α *ᵥ z) v) : y = z := by
  have a := Lα_minp G hG α hα0 hα1 S (y - z) (fun v hv => by simp [hy0 v hv, hz0 v hv])
    (fun v hv => by rw [Matrix.mulVec_sub]; simp [h v hv])
  have b := Lα_minp G hG α hα0 hα1 S (z - y) (fun v hv => by simp [hy0 v hv, hz0 v hv])
    (fun v hv => by rw [Matrix.mulVec_sub]; simp [h v hv])
  funext v; have := a v; have := b v; simp only [Pi.sub_apply] at *; linarith

theorem ext_zero (S : Finset V) (z : S → ℝ) (v : V) (hv : v ∉ S) : ext S z v = 0 := by
  simp [ext, hv]

theorem ext_mem (S : Finset V) (z : S → ℝ) (v : S) : ext S z v = z v := by
  simp [ext, v.2]

theorem sum_ext (S : Finset V) (f : V → ℝ) (z : S → ℝ) :
    ∑ w, f w * ext S z w = ∑ w : S, f w * z w := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun w _ hw => by rw [ext_zero S z w hw, mul_zero])]
  rw [← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl; intro w _; rw [ext_mem]

theorem Lα_ext (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (S : Finset V) (z : S → ℝ)
    (v : S) : (Lα G α *ᵥ ext S z) v = (LαS G α S *ᵥ z) v := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_ext]; rfl

theorem LαS_isUnit_det (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (S : Finset V) : IsUnit (LαS G α S).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro z1 z2 h
  have := Lα_minp_eq G hG α hα0 hα1 S (ext S z1) (ext S z2) (ext_zero S z1) (ext_zero S z2)
    (fun v hv => by rw [Lα_ext G α S z1 ⟨v, hv⟩, Lα_ext G α S z2 ⟨v, hv⟩, h])
  funext v; have h2 := congrFun this v; rwa [ext_mem, ext_mem] at h2

theorem xS_zero (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ) (S : Finset V)
    (v : V) (hv : v ∉ S) : xS G s α lam S v = 0 := ext_zero S _ v hv

theorem xS_eq (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V) (α lam : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (S : Finset V) (v : V) (hv : v ∈ S) :
    (Lα G α *ᵥ xS G s α lam S) v = α * (e s v - lam * deg G v) := by
  rw [xS, Lα_ext G α S _ ⟨v, hv⟩, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (LαS_isUnit_det G hG α hα0 hα1 S), Matrix.one_mulVec]
  simp [bvec]

theorem xS_unique (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V) (α lam : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (S : Finset V) (y : V → ℝ) (hy0 : ∀ v ∉ S, y v = 0)
    (hy : ∀ v ∈ S, (Lα G α *ᵥ y) v = α * (e s v - lam * deg G v)) : y = xS G s α lam S :=
  Lα_minp_eq G hG α hα0 hα1 S y _ hy0 (xS_zero G s α lam S)
    (fun v hv => by rw [hy v hv, xS_eq G hG s α lam hα0 hα1 S v hv])

theorem resid_eq_of_Lα (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α : ℝ) (hα0 : 0 < α)
    (x : V → ℝ) (v : V) : (Lα G α *ᵥ x) v = α * (e s v - resid G α s x v) := by
  simp only [resid, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring

theorem resid_xS (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V) (α lam : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (S : Finset V) (v : V) (hv : v ∈ S) :
    resid G α s (xS G s α lam S) v = lam * deg G v := by
  have h1 := xS_eq G hG s α lam hα0 hα1 S v hv
  rw [resid_eq_of_Lα G s α hα0] at h1
  have := mul_left_cancel₀ hα0.ne' h1
  linarith

/-- Lemma 5.1 (monotonicity). -/
theorem mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (S T : Finset V) (hs : s ∈ S) (hT : T ⊆ bdry G S)
    (hr : ∀ v ∈ T, lam * deg G v < resid G α s (xS G s α lam S) v) :
    (∀ v, xS G s α lam S v ≤ xS G s α lam (S ∪ T) v) ∧
      ∀ v ∈ T, α / deg G v * (resid G α s (xS G s α lam S) v - lam * deg G v) ≤
        xS G s α lam (S ∪ T) v := by
  set x1 := xS G s α lam S
  set x2 := xS G s α lam (S ∪ T)
  have hTS : ∀ v ∈ T, v ∉ S := by
    intro v hv; have := hT hv; simp [bdry] at this; exact this.1
  -- L(x2 - x1) on S ∪ T
  have hL : ∀ v ∈ S ∪ T, (Lα G α *ᵥ (x2 - x1)) v = α * (resid G α s x1 v - lam * deg G v) := by
    intro v hv
    rw [Matrix.mulVec_sub, Pi.sub_apply, xS_eq G hG s α lam hα0 hα1 _ v hv,
      resid_eq_of_Lα G s α hα0 x1 v]; ring
  have hnn := Lα_minp G hG α hα0 hα1 (S ∪ T) (x2 - x1)
    (fun v hv => by
      simp only [Pi.sub_apply, x1, x2]
      rw [xS_zero G s α lam _ v hv, xS_zero G s α lam S v (fun h => hv (Finset.mem_union_left _ h))]
      simp)
    (fun v hv => by
      rw [hL v hv]
      rcases Finset.mem_union.mp hv with h | h
      · rw [resid_xS G hG s α lam hα0 hα1 S v h]; simp
      · exact mul_nonneg hα0.le (by linarith [hr v h]))
  refine ⟨fun v => by have := hnn v; simp only [Pi.sub_apply] at this; linarith, fun v hv => ?_⟩
  have h1 := hL v (Finset.mem_union_right _ hv)
  rw [Lα_mulVec_apply] at h1
  have h2 := sum_nbr_ge G (x2 - x1) v 0 hnn
  have hx1v : x1 v = 0 := xS_zero G s α lam S v (hTS v hv)
  simp only [Pi.sub_apply, hx1v, sub_zero, mul_zero] at h1 h2
  have hd := deg_pos G hG v
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  have : 0 ≤ 1 - α := by linarith
  nlinarith [mul_nonneg this h2]

end LocalPush.Aux


namespace LocalPush.Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem deg_ge_one (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (v : V) :
    1 ≤ deg G v := by
  unfold deg; exact_mod_cast hG v

theorem Lα_decomp (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) :
    Lα G α = α • G.degMatrix ℝ + (1 - α) • G.lapMatrix ℝ := by
  have : degM G = G.degMatrix ℝ := by
    ext i j; simp [degM, SimpleGraph.degMatrix, Matrix.diagonal_apply, deg]
  rw [Lα, adjM, this, SimpleGraph.lapMatrix]
  module

theorem quad_lower (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (hα1 : α < 1) (x : V → ℝ) :
    α * ∑ v, deg G v * x v ^ 2 ≤ x ⬝ᵥ (Lα G α *ᵥ x) := by
  rw [Lα_decomp, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, dotProduct_smul, SimpleGraph.dotProduct_mulVec_degMatrix]
  have h := SimpleGraph.lapMatrix_toLinearMap₂' ℝ G x
  rw [Matrix.toLinearMap₂'_apply'] at h
  have hl : 0 ≤ x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) := by
    rw [h]; positivity
  have : ∑ i, (G.degree i : ℝ) * x i * x i = ∑ v, deg G v * x v ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; simp [deg]; ring
  rw [this, smul_eq_mul, smul_eq_mul]
  have : 0 ≤ 1 - α := by linarith
  nlinarith [mul_nonneg this hl]

theorem quad_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (x : V → ℝ) : 0 ≤ x ⬝ᵥ (Lα G α *ᵥ x) := by
  refine le_trans ?_ (quad_lower G α hα1 x)
  apply mul_nonneg hα0.le
  exact Finset.sum_nonneg fun v _ => mul_nonneg (deg_pos G hG v).le (sq_nonneg _)

theorem ext_restr (S : Finset V) (z : V → ℝ) (hz : ∀ v ∉ S, z v = 0) : ext S (restr S z) = z := by
  funext v; by_cases hv : v ∈ S
  · simp [ext, restr, hv]
  · simp [ext, hv, hz v hv]

theorem restr_xS (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ) (S : Finset V) :
    restr S (xS G s α lam S) = (LαS G α S)⁻¹ *ᵥ bvec G s α lam S := by
  funext v; simp [restr, xS, ext_mem]

theorem quadS (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (S : Finset V) (z : V → ℝ)
    (hz : ∀ v ∉ S, z v = 0) :
    restr S z ⬝ᵥ (LαS G α S *ᵥ restr S z) = z ⬝ᵥ (Lα G α *ᵥ z) := by
  have h1 : ∀ v : S, (LαS G α S *ᵥ restr S z) v = (Lα G α *ᵥ z) v := by
    intro v; rw [← Lα_ext, ext_restr S z hz]
  simp only [dotProduct, h1]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun w _ hw => by rw [hz w hw, zero_mul])]
  rw [← Finset.sum_coe_sort S]; rfl

theorem resid_sub (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (s : V) (a b : V → ℝ) (v : V) :
    resid G α s a v - resid G α s b v = -(α⁻¹ * (Lα G α *ᵥ (a - b)) v) := by
  simp only [resid, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_sub]; ring

theorem resid_nonneg_xS (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hlam : 0 ≤ lam) (S : Finset V) (hs : s ∈ S)
    (x : V → ℝ) (hx0 : ∀ v ∉ S, x v = 0) (hx : ∀ v, 0 ≤ x v)
    (hrS : ∀ v ∈ S, 0 ≤ resid G α s x v) : ∀ v, 0 ≤ resid G α s x v := by
  intro v
  by_cases hv : v ∈ S
  · exact hrS v hv
  · rw [resid_outside G s α x S hx0 hs v hv]
    apply mul_nonneg (div_nonneg (by linarith) hα0.le)
    exact Finset.sum_nonneg fun u _ => hx u

theorem xS_s_le (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hlam : 0 ≤ lam) (S : Finset V) (hs : s ∈ S)
    (hx : ∀ v, 0 ≤ xS G s α lam S v) : ∑ v, deg G v * xS G s α lam S v ≤ 1 := by
  have hm := mass_identity G s α hα0 (xS G s α lam S)
  have hr := resid_nonneg_xS G hG s α lam hα0 hα1 hlam S hs _ (xS_zero G s α lam S) hx
    (fun v hv => by rw [resid_xS G hG s α lam hα0 hα1 S v hv]; exact mul_nonneg hlam (deg_pos G hG v).le)
  have := Finset.sum_nonneg fun v (_ : v ∈ univ) => hr v
  linarith

theorem quad_xS (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (S : Finset V) :
    xS G s α lam S ⬝ᵥ (Lα G α *ᵥ xS G s α lam S) =
      α * xS G s α lam S s - α * lam * ∑ v, deg G v * xS G s α lam S v := by
  have : ∀ v, xS G s α lam S v * (Lα G α *ᵥ xS G s α lam S) v =
      xS G s α lam S v * (α * (e s v - lam * deg G v)) := by
    intro v; by_cases hv : v ∈ S
    · rw [xS_eq G hG s α lam hα0 hα1 S v hv]
    · rw [xS_zero G s α lam S v hv]; simp
  simp only [dotProduct, this]
  simp only [mul_sub, Finset.sum_sub_distrib, e, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1 <;> [ring; (apply Finset.sum_congr rfl; intro v _; ring)]

theorem quad_xS_le (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hlam : 0 ≤ lam) (S : Finset V) (hs : s ∈ S)
    (hx : ∀ v, 0 ≤ xS G s α lam S v) :
    xS G s α lam S ⬝ᵥ (Lα G α *ᵥ xS G s α lam S) ≤ α := by
  rw [quad_xS G hG s α lam hα0 hα1 S]
  have h1 := xS_s_le G hG s α lam hα0 hα1 hlam S hs hx
  have h2 : deg G s * xS G s α lam S s ≤ ∑ v, deg G v * xS G s α lam S v :=
    Finset.single_le_sum (f := fun v => deg G v * xS G s α lam S v)
      (fun v _ => mul_nonneg (deg_pos G hG v).le (hx v)) (Finset.mem_univ s)
  have h3 := deg_ge_one G hG s
  have h4 : 0 ≤ ∑ v, deg G v * xS G s α lam S v :=
    Finset.sum_nonneg fun v _ => mul_nonneg (deg_pos G hG v).le (hx v)
  have h5 := hx s
  have : xS G s α lam S s ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hα0.le hlam) h4]

/-- Pointwise bound from an energy bound. -/
theorem pt_of_energy (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (z : V → ℝ) (μ : ℝ) (hμ : 0 ≤ μ)
    (hz : z ⬝ᵥ (Lα G α *ᵥ z) ≤ μ ^ 2 * α) (v : V) : |z v| ≤ μ := by
  have h1 := quad_lower G α hα1 z
  have h2 : deg G v * z v ^ 2 ≤ ∑ w, deg G w * z w ^ 2 :=
    Finset.single_le_sum (f := fun w => deg G w * z w ^ 2)
      (fun w _ => mul_nonneg (deg_pos G hG w).le (sq_nonneg _)) (Finset.mem_univ v)
  have h3 := deg_ge_one G hG v
  have h4 : z v ^ 2 ≤ μ ^ 2 := by
    have : α * (deg G v * z v ^ 2) ≤ α * μ ^ 2 := by nlinarith
    have h5 : deg G v * z v ^ 2 ≤ μ ^ 2 := le_of_mul_le_mul_left this hα0
    nlinarith [sq_nonneg (z v)]
  exact abs_le_of_sq_le_sq' h4 hμ |>.elim (fun a b => abs_le.mpr ⟨a, b⟩)

theorem Lα_pt_bound (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (z : V → ℝ) (μ : ℝ) (hz : ∀ v, |z v| ≤ μ) (v : V) :
    |(Lα G α *ᵥ z) v| ≤ 2 * deg G v * μ := by
  rw [Lα_mulVec_apply]
  have hc : ((univ.filter (G.Adj v)).card : ℝ) = deg G v := by
    simp [deg, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  have h1 : |∑ w ∈ univ.filter (G.Adj v), z w| ≤ deg G v * μ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [← hc, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun w _ => hz w
  have hd : 0 ≤ deg G v := by unfold deg; positivity
  have h2 : |deg G v * z v| ≤ deg G v * μ := by rw [abs_mul, abs_of_nonneg hd]; exact mul_le_mul_of_nonneg_left (hz v) hd
  have h3 : |(1 - α) * ∑ w ∈ univ.filter (G.Adj v), z w| ≤ deg G v * μ := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    have := abs_nonneg (∑ w ∈ univ.filter (G.Adj v), z w)
    nlinarith
  calc |deg G v * z v - (1 - α) * ∑ w ∈ univ.filter (G.Adj v), z w|
      ≤ |deg G v * z v| + |(1 - α) * ∑ w ∈ univ.filter (G.Adj v), z w| := abs_sub _ _
    _ ≤ 2 * deg G v * μ := by linarith

end LocalPush.Aux


namespace LocalPush.Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem params_facts {G : SimpleGraph V} [DecidableRel G.Adj] (hG : NoIsolated G) {s : V}
    {α lam η κ : ℝ} (hP : Params G s α lam η κ) : η < 1 ∧ κ < η ∧ lam < 1 := by
  have h1 := deg_ge_one G hG s
  have := hP.nontrivial; have := hP.lam_pos; have := hP.eta_pos; have := hP.kappa_le
  have := hP.alpha_pos; have := hP.alpha_lt_one
  have hη : η < 1 := by nlinarith
  refine ⟨hη, ?_, by nlinarith⟩
  have : 0.4 * α * η ^ 2 < η := by nlinarith
  linarith

/-- Lemma 5.2 in uniform form: `|x̃ − x^(S)| ≤ µ` entrywise and `|r̃ − r(x^(S))| ≤ 2µd/α`. -/
theorem solve_err (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (S : Finset V) (hs : s ∈ S) (hx : ∀ v, 0 ≤ xS G s α lam S v)
    (xt : V → ℝ) (hxt : ∀ v ∉ S, xt v = 0) (hsolve : SolveGood G s α lam κ S xt) :
    (∀ v, |xt v - xS G s α lam S v| ≤ mu α lam κ) ∧
    (∀ v, |resid G α s xt v - resid G α s (xS G s α lam S) v| ≤ 0.02 * min lam κ * deg G v) := by
  have hα0 := hP.alpha_pos; have hα1 := hP.alpha_lt_one
  set x := xS G s α lam S
  set z := xt - x
  have hz0 : ∀ v ∉ S, z v = 0 := fun v hv => by
    simp [z, hxt v hv, x, xS_zero G s α lam S v hv]
  have hμ : 0 ≤ mu α lam κ := by
    unfold mu; have h1 := hP.lam_pos; have h2 := hP.kappa_pos
    exact mul_nonneg (by linarith) (le_min h1.le h2.le)
  -- energy bound
  have hE : z ⬝ᵥ (Lα G α *ᵥ z) ≤ mu α lam κ ^ 2 * α := by
    unfold SolveGood enorm at hsolve
    rw [← restr_xS, show restr S xt - restr S x = restr S z from rfl, quadS G α S z hz0,
      quadS G α S x (xS_zero G s α lam S)] at hsolve
    have q1 := quad_nonneg G hG α hα0 hα1 z
    have q2 := quad_nonneg G hG α hα0 hα1 x
    have q3 := quad_xS_le G hG s α lam hα0 hα1 hP.lam_pos.le S hs hx
    have h2 := Real.sqrt_le_sqrt (le_of_lt (lt_of_le_of_lt q3 (lt_add_one α)))
    have hsq : z ⬝ᵥ (Lα G α *ᵥ z) ≤ (mu α lam κ * Real.sqrt (x ⬝ᵥ (Lα G α *ᵥ x))) ^ 2 := by
      rw [← Real.sq_sqrt q1]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsolve 2
    rw [mul_pow, Real.sq_sqrt q2] at hsq
    nlinarith [sq_nonneg (mu α lam κ)]
  have hpt := pt_of_energy G hG α hα0 hα1 z (mu α lam κ) hμ hE
  refine ⟨hpt, fun v => ?_⟩
  rw [resid_sub, abs_neg, abs_mul, abs_inv, abs_of_pos hα0]
  have := Lα_pt_bound G α hα0 hα1 z (mu α lam κ) hpt v
  rw [inv_mul_le_iff₀ hα0]
  unfold mu at this
  have hd := deg_pos G hG v
  nlinarith [mul_pos hα0 hd, min_le_left lam κ]

end LocalPush.Aux


namespace LocalPush.Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem resid_far (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α : ℝ) (x : V → ℝ)
    (S : Finset V) (hx : ∀ v ∉ S, x v = 0) (hs : s ∈ S) (v : V) (hv : v ∉ S) (hb : v ∉ bdry G S) :
    resid G α s x v = 0 := by
  rw [resid_outside G s α x S hx hs v hv]
  have : S.filter (G.Adj v) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro u hu hadj
    apply hb
    simp only [bdry, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv, u, hu, hadj⟩
  rw [this]; simp

theorem xS_single (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V) (α lam : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    xS G s α lam {s} = Pi.single s (α * (1 - lam * deg G s) / deg G s) := by
  symm
  apply xS_unique G hG s α lam hα0 hα1
  · intro v hv; simp at hv; simp [Pi.single_apply, hv]
  · intro v hv
    simp at hv; subst hv
    rw [Lα_mulVec_apply]
    have : ∑ w ∈ univ.filter (G.Adj v), (Pi.single v (α * (1 - lam * deg G v) / deg G v) : V → ℝ) w
        = 0 := by
      apply Finset.sum_eq_zero; intro w hw
      simp at hw
      simp [Pi.single_apply, (G.ne_of_adj hw).symm]
    rw [this]
    have hd := deg_pos G hG v
    simp [e]; field_simp

/-- The basic invariants of a good trajectory. -/
theorem traj_basic (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ)
    (hT : GoodTraj G s α lam η κ N S xt) :
    ∀ i ≤ N, s ∈ S i ∧ (∀ v, 0 ≤ exactX G s α lam S i v) ∧
      (∀ v ∈ S i, 0.9 * α * κ < exactX G s α lam S i v) := by
  have hα0 := hP.alpha_pos; have hα1 := hP.alpha_lt_one
  obtain ⟨hη1, hκη, -⟩ := params_facts hG hP
  intro i
  induction i with
  | zero =>
    intro _
    have hS0 := hT.start
    have hx0 : exactX G s α lam S 0 = Pi.single s (α * (1 - lam * deg G s) / deg G s) := by
      unfold exactX; rw [hS0]; exact xS_single G hG s α lam hα0 hα1
    have hd := deg_pos G hG s
    have hc : 0.9 * α * κ < α * (1 - lam * deg G s) / deg G s := by
      rw [lt_div_iff₀ hd]
      have h1 := hP.nontrivial
      have h2 := deg_ge_one G hG s
      have : 0.9 * κ * deg G s < η * deg G s := by nlinarith [hP.kappa_pos]
      nlinarith
    refine ⟨by rw [hS0]; simp, fun v => ?_, fun v hv => ?_⟩
    · rw [hx0]; simp only [Pi.single_apply]; split_ifs
      · linarith [mul_pos (mul_pos (by norm_num : (0:ℝ) < 0.9) hα0) hP.kappa_pos]
      · rfl
    · rw [hS0] at hv; simp at hv; subst hv; rw [hx0]; simp; exact hc
  | succ i ih =>
    intro hi
    obtain ⟨hs, hx, hxk⟩ := ih (by omega)
    have hlt : i < N := by omega
    have hnext := hT.next i hlt
    obtain ⟨-, herr⟩ := solve_err G hG s α lam η κ hP (S i) hs hx (xt i) (hT.supp_sub i hlt.le)
      (hT.solve i hlt.le)
    set Ti := (bdry G (S i)).filter fun v => (lam + κ) * deg G v < resid G α s (xt i) v
    have hexp : S (i + 1) = S i ∪ Ti := by rw [hnext]; rfl
    have hTi : ∀ v ∈ Ti, (lam + 0.9 * κ) * deg G v < resid G α s (exactX G s α lam S i) v := by
      intro v hv
      simp only [Ti, Finset.mem_filter] at hv
      have := herr v
      have hd := deg_pos G hG v
      have hm := min_le_right lam κ
      rw [abs_le] at this
      unfold exactX
      nlinarith [mul_le_mul_of_nonneg_right hm hd.le]
    have hmono := mono G hG s α lam hα0 hα1 (S i) Ti hs (Finset.filter_subset _ _)
      (fun v hv => by
        have := hTi v hv; unfold exactX at this; have hd := deg_pos G hG v; nlinarith [hP.kappa_pos])
    refine ⟨by rw [hexp]; exact Finset.mem_union_left _ hs, fun v => ?_, fun v hv => ?_⟩
    · unfold exactX; rw [hexp]; exact le_trans (hx v) (hmono.1 v)
    · unfold exactX; rw [hexp]
      rw [hexp] at hv
      rcases Finset.mem_union.mp hv with h | h
      · exact lt_of_lt_of_le (hxk v h) (hmono.1 v)
      · refine lt_of_lt_of_le ?_ (hmono.2 v h)
        have := hTi v h
        have hd := deg_pos G hG v
        rw [div_mul_eq_mul_div, lt_div_iff₀ hd]
        unfold exactX at this
        nlinarith

end LocalPush.Aux


namespace LocalPush.Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem traj_err (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ)
    (hT : GoodTraj G s α lam η κ N S xt) (i : ℕ) (hi : i ≤ N) :
    (∀ v, |xt i v - exactX G s α lam S i v| ≤ mu α lam κ) ∧
    (∀ v, |resid G α s (xt i) v - exactR G s α lam S i v| ≤ 0.02 * min lam κ * deg G v) := by
  obtain ⟨hs, hx, -⟩ := traj_basic G hG s α lam η κ hP N S xt hT i hi
  exact solve_err G hG s α lam η κ hP (S i) hs hx (xt i) (hT.supp_sub i hi) (hT.solve i hi)

theorem exactR_on (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (S : ℕ → Finset V) (i : ℕ) (v : V) (hv : v ∈ S i) :
    exactR G s α lam S i v = lam * deg G v :=
  resid_xS G hG s α lam hP.alpha_pos hP.alpha_lt_one (S i) v hv

theorem exactX_zero (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam : ℝ)
    (S : ℕ → Finset V) (i : ℕ) (v : V) (hv : v ∉ S i) : exactX G s α lam S i v = 0 :=
  xS_zero G s α lam (S i) v hv

theorem exactR_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ)
    (hT : GoodTraj G s α lam η κ N S xt) (i : ℕ) (hi : i ≤ N) : ∀ v, 0 ≤ exactR G s α lam S i v := by
  obtain ⟨hs, hx, -⟩ := traj_basic G hG s α lam η κ hP N S xt hT i hi
  exact resid_nonneg_xS G hG s α lam hP.alpha_pos hP.alpha_lt_one hP.lam_pos.le (S i) hs _
    (xS_zero G s α lam (S i)) hx (fun v hv => by
      unfold exactX
      rw [resid_xS G hG s α lam hP.alpha_pos hP.alpha_lt_one (S i) v hv]
      exact mul_nonneg hP.lam_pos.le (deg_pos G hG v).le)

theorem traj_step (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ)
    (hT : GoodTraj G s α lam η κ N S xt) (i : ℕ) (hi : i < N) :
    S i ⊆ S (i + 1) ∧ S (i + 1) \ S i ⊆ bdry G (S i) ∧
    (∀ v, exactX G s α lam S i v ≤ exactX G s α lam S (i + 1) v) ∧
    (∀ v ∈ S (i + 1) \ S i, (lam + 0.9 * κ) * deg G v < exactR G s α lam S i v) ∧
    (∀ v ∈ S (i + 1) \ S i, α / deg G v * (exactR G s α lam S i v - lam * deg G v) ≤
        exactX G s α lam S (i + 1) v) ∧
    (∀ v ∉ S (i + 1), exactR G s α lam S i v ≤ (lam + 1.1 * κ) * deg G v) ∧
    (∃ v, v ∈ S (i + 1) \ S i ∧ (lam + η - 0.02 * κ) * deg G v < exactR G s α lam S i v) := by
  have hα0 := hP.alpha_pos; have hα1 := hP.alpha_lt_one
  obtain ⟨hη1, hκη, -⟩ := params_facts hG hP
  obtain ⟨hs, hx, -⟩ := traj_basic G hG s α lam η κ hP N S xt hT i hi.le
  obtain ⟨-, herr⟩ := traj_err G hG s α lam η κ hP N S xt hT i hi.le
  set Ti := (bdry G (S i)).filter fun v => (lam + κ) * deg G v < resid G α s (xt i) v
  have hexp : S (i + 1) = S i ∪ Ti := by rw [hT.next i hi]; rfl
  have hTS : ∀ v ∈ Ti, v ∉ S i := by
    intro v hv; simp only [Ti, Finset.mem_filter, bdry, Finset.mem_univ, true_and] at hv; exact hv.1.1
  have hdiff : S (i + 1) \ S i = Ti := by
    rw [hexp]; ext v; simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩; · exact absurd h1 h2
      · exact h1
    · intro h; exact ⟨Or.inr h, hTS v h⟩
  have hm := min_le_right lam κ
  have hTi : ∀ v ∈ Ti, (lam + 0.9 * κ) * deg G v < exactR G s α lam S i v := by
    intro v hv
    simp only [Ti, Finset.mem_filter] at hv
    have := herr v
    have hd := deg_pos G hG v
    rw [abs_le] at this
    nlinarith [mul_le_mul_of_nonneg_right hm hd.le]
  have hmono := mono G hG s α lam hα0 hα1 (S i) Ti hs (Finset.filter_subset _ _)
    (fun v hv => by have := hTi v hv; unfold exactR exactX at this; have hd := deg_pos G hG v; nlinarith [hP.kappa_pos])
  refine ⟨by rw [hexp]; exact Finset.subset_union_left, by rw [hdiff]; exact Finset.filter_subset _ _,
    fun v => ?_, by rw [hdiff]; exact hTi, ?_, fun v hv => ?_, ?_⟩
  · unfold exactX; rw [hexp]; exact hmono.1 v
  · rw [hdiff]; intro v hv; unfold exactX exactR; rw [hexp]; exact hmono.2 v hv
  · have hvS : v ∉ S i := fun h => hv (by rw [hexp]; exact Finset.mem_union_left _ h)
    by_cases hb : v ∈ bdry G (S i)
    · have hnT : ¬ (lam + κ) * deg G v < resid G α s (xt i) v := by
        intro h; apply hv; rw [hexp]; apply Finset.mem_union_right
        simp only [Ti, Finset.mem_filter]; exact ⟨hb, h⟩
      push Not at hnT
      have := herr v
      have hd := deg_pos G hG v
      rw [abs_le] at this
      nlinarith [mul_le_mul_of_nonneg_right hm hd.le, hP.kappa_pos]
    · unfold exactR exactX
      rw [resid_far G s α _ (S i) (xS_zero G s α lam (S i)) hs v hvS hb]
      have hd := deg_pos G hG v
      nlinarith [hP.kappa_pos, hP.lam_pos]
  · have hns := hT.no_stop i hi
    unfold StopRule at hns; push Not at hns
    obtain ⟨v, hvb, hv⟩ := hns
    have hd := deg_pos G hG v
    have hvT : v ∈ Ti := by
      simp only [Ti, Finset.mem_filter]; exact ⟨hvb, by nlinarith [hP.kappa_pos]⟩
    refine ⟨v, by rw [hdiff]; exact hvT, ?_⟩
    have := herr v
    rw [abs_le] at this
    nlinarith [mul_le_mul_of_nonneg_right hm hd.le]

theorem traj_mono (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ)
    (hT : GoodTraj G s α lam η κ N S xt) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    S a ⊆ S b ∧ ∀ v, exactX G s α lam S a v ≤ exactX G s α lam S b v := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨subset_refl _, fun v => le_refl _⟩
  | succ b hab ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, -, h4, -⟩ := traj_step G hG s α lam η κ hP N S xt hT b (by omega)
    exact ⟨h1.trans h3, fun v => (h2 v).trans (h4 v)⟩

theorem traj_card (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ)
    (hT : GoodTraj G s α lam η κ N S xt) : ∀ i ≤ N, i + 1 ≤ (S i).card := by
  intro i
  induction i with
  | zero => intro _; rw [hT.start]; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    obtain ⟨hsub, -, -, -, -, -, ⟨v, hv, -⟩⟩ := traj_step G hG s α lam η κ hP N S xt hT i (by omega)
    have : (S i).card < (S (i + 1)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨v, (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩
    omega

theorem traj_vol (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ)
    (hT : GoodTraj G s α lam η κ N S xt) (i : ℕ) (hi : i ≤ N) : vol G (S i) ≤ 1 / lam := by
  have hα0 := hP.alpha_pos
  obtain ⟨hs, hx, -⟩ := traj_basic G hG s α lam η κ hP N S xt hT i hi
  have hr := exactR_nonneg G hG s α lam η κ hP N S xt hT i hi
  have hm := mass_identity G s α hα0 (exactX G s α lam S i)
  have h1 : 0 ≤ ∑ v, deg G v * exactX G s α lam S i v :=
    Finset.sum_nonneg fun v _ => mul_nonneg (deg_pos G hG v).le (hx v)
  have h2 : ∑ v ∈ S i, resid G α s (exactX G s α lam S i) v ≤ ∑ v, resid G α s (exactX G s α lam S i) v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hr v)
  have h3 : ∑ v ∈ S i, resid G α s (exactX G s α lam S i) v = lam * vol G (S i) := by
    rw [vol, Finset.mul_sum]; apply Finset.sum_congr rfl; intro v hv
    exact exactR_on G hG s α lam η κ hP S i v hv
  rw [le_div_iff₀ hP.lam_pos]
  linarith

end LocalPush.Aux


namespace LocalPush.Aux
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem xt_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (hG : NoIsolated G) (s : V)
    (α lam η κ : ℝ) (hP : Params G s α lam η κ) (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ)
    (hT : GoodTraj G s α lam η κ N S xt) (i : ℕ) (hi : i ≤ N) :
    (∀ v, 0 ≤ xt i v) ∧ (∀ v, 0 ≤ resid G α s (xt i) v) := by
  have hα0 := hP.alpha_pos; have hα1 := hP.alpha_lt_one
  obtain ⟨hs, hx, hxk⟩ := traj_basic G hG s α lam η κ hP N S xt hT i hi
  obtain ⟨e1, e2⟩ := traj_err G hG s α lam η κ hP N S xt hT i hi
  have hm := min_le_right lam κ
  have hm2 := min_le_left lam κ
  have hxt : ∀ v, 0 ≤ xt i v := by
    intro v
    by_cases hv : v ∈ S i
    · have := e1 v; have := hxk v hv; rw [abs_le] at *; unfold mu at *
      nlinarith [mul_le_mul_of_nonneg_left hm (by linarith : (0:ℝ) ≤ 0.01 * α)]
    · rw [hT.supp_sub i hi v hv]
  refine ⟨hxt, ?_⟩
  apply resid_nonneg_xS G hG s α lam hα0 hα1 hP.lam_pos.le (S i) hs (xt i) (hT.supp_sub i hi) hxt
  intro v hv
  have := e2 v
  rw [exactR_on G hG s α lam η κ hP S i v hv, abs_le] at this
  have hd := deg_pos G hG v
  nlinarith [mul_le_mul_of_nonneg_right hm2 hd.le, hP.lam_pos]

end LocalPush.Aux

open LocalPush LocalPush.Aux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ : ℝ) (hP : Params G s α lam η κ)
    (N : ℕ) (S : ℕ → Finset V) (xt : ℕ → V → ℝ) (hT : GoodTraj G s α lam η κ N S xt) :
    ((N : ℝ) + 1 ≤ 1 / lam) ∧
    (∀ i ≤ N,
      (∀ v, 0 ≤ exactX G s α lam S i v) ∧ (∀ v, 0 ≤ deg G v * exactX G s α lam S i v) ∧
      (∀ v, 0 ≤ exactR G s α lam S i v) ∧ (∀ v, 0 ≤ xt i v) ∧ (∀ v, 0 ≤ deg G v * xt i v) ∧
      (∀ v, 0 ≤ resid G α s (xt i) v) ∧
      (∀ v ∈ S i, 0.9 * α * κ < exactX G s α lam S i v) ∧ vol G (S i) ≤ 1 / lam) ∧
    (∀ i < N,
      (∀ v, exactX G s α lam S i v ≤ exactX G s α lam S (i + 1) v) ∧
      (∀ v ∈ S (i + 1) \ S i, (lam + 0.9 * κ) * deg G v < exactR G s α lam S i v) ∧
      (∀ v ∉ S (i + 1), exactR G s α lam S i v ≤ (lam + 1.1 * κ) * deg G v)) ∧
    (StopRule G s α lam η (S N) (xt N) →
      (∀ v, 0 ≤ deg G v * xt N v) ∧
      ∀ v, 0 ≤ resid G α s (fun u => deg G u * xt N u / deg G u) v ∧
        resid G α s (fun u => deg G u * xt N u / deg G u) v ≤ (lam + η) * deg G v) := by
  have hα0 := hP.alpha_pos; have hα1 := hP.alpha_lt_one
  obtain ⟨hη1, hκη, -⟩ := params_facts hG hP
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun hstop => ?_⟩
  · have h1 := traj_card G hG s α lam η κ hP N S xt hT N le_rfl
    have h2 := traj_vol G hG s α lam η κ hP N S xt hT N le_rfl
    have h3 : ((S N).card : ℝ) ≤ vol G (S N) := by
      rw [vol, Finset.card_eq_sum_ones, Nat.cast_sum]
      exact Finset.sum_le_sum fun v _ => by simpa using deg_ge_one G hG v
    have h4 : ((N : ℝ) + 1) ≤ (S N).card := by exact_mod_cast h1
    linarith
  · obtain ⟨hs, hx, hxk⟩ := traj_basic G hG s α lam η κ hP N S xt hT i hi
    obtain ⟨ht1, ht2⟩ := xt_nonneg G hG s α lam η κ hP N S xt hT i hi
    exact ⟨hx, fun v => mul_nonneg (deg_pos G hG v).le (hx v),
      exactR_nonneg G hG s α lam η κ hP N S xt hT i hi, ht1,
      fun v => mul_nonneg (deg_pos G hG v).le (ht1 v), ht2, hxk,
      traj_vol G hG s α lam η κ hP N S xt hT i hi⟩
  · obtain ⟨-, -, h3, h4, -, h6, -⟩ := traj_step G hG s α lam η κ hP N S xt hT i hi
    exact ⟨h3, h4, h6⟩
  · obtain ⟨hs, -, -⟩ := traj_basic G hG s α lam η κ hP N S xt hT N le_rfl
    obtain ⟨ht1, ht2⟩ := xt_nonneg G hG s α lam η κ hP N S xt hT N le_rfl
    obtain ⟨-, e2⟩ := traj_err G hG s α lam η κ hP N S xt hT N le_rfl
    have hf : (fun u => deg G u * xt N u / deg G u) = xt N := by
      funext u; field_simp [(deg_pos G hG u).ne']
    rw [hf]
    refine ⟨fun v => mul_nonneg (deg_pos G hG v).le (ht1 v), fun v => ⟨ht2 v, ?_⟩⟩
    have hd := deg_pos G hG v
    by_cases hv : v ∈ S N
    · have := e2 v
      rw [exactR_on G hG s α lam η κ hP S N v hv, abs_le] at this
      nlinarith [mul_le_mul_of_nonneg_right (min_le_right lam κ) hd.le, hP.kappa_pos]
    · by_cases hb : v ∈ bdry G (S N)
      · exact hstop v hb
      · rw [resid_far G s α (xt N) (S N) (hT.supp_sub N le_rfl) hs v hv hb]
        nlinarith [hP.lam_pos, hP.eta_pos]

