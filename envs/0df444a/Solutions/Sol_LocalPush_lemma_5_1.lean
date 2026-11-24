-- Prove2me | solution 1 for LocalPush.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T09:39:14.472077+00:00
-- url     : https://prove2.me/submissions/07b2c51a-2124-40ab-950e-1b702428a439

import Mathlib
import Definitions.Def_LocalPush_ResidueSystem

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

open LocalPush LocalPush.Aux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    (S T : Finset V) (hs : s ∈ S) (hT : T ⊆ bdry G S)
    (hr : ∀ v ∈ T, lam * deg G v < resid G α s (xS G s α lam S) v) :
    (∀ v, xS G s α lam S v ≤ xS G s α lam (S ∪ T) v) ∧
      ∀ v ∈ T, α / deg G v * (resid G α s (xS G s α lam S) v - lam * deg G v) ≤
        xS G s α lam (S ∪ T) v :=
  mono G hG s α lam hα0 hα1 S T hs hT hr

