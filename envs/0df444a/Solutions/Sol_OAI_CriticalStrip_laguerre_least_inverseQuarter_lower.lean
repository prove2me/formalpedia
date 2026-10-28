-- Prove2me | solution 1 for OAI.CriticalStrip.laguerre_least_inverseQuarter_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:33:21.421342+00:00
-- url     : https://prove2.me/submissions/4e05b425-1b43-4fe0-a7df-7eaea5ab5f46

import Mathlib
import Definitions.Def_OAIQ042S001

section
-- module Solutions.OAIQ042_SS.StripMass_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory

theorem pairKernel_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < pairKernel x y := by
  unfold pairKernel
  exact div_pos (sq_pos_of_pos (sub_pos.2 hxy)) (by linarith)

theorem pairKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ pairKernel x y := by
  unfold pairKernel
  positivity

theorem abs_one_sub_prod_le {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, |r i| ≤ 1) : |1 - ∏ i ∈ s, r i| ≤ ∑ i ∈ s, |1 - r i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have his : ∀ j ∈ s, |r j| ≤ 1 := fun j hj => hr j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      |1 - r i * ∏ j ∈ s, r j| = |(1 - r i) + r i * (1 - ∏ j ∈ s, r j)| := by congr 1; ring
      _ ≤ |1 - r i| + |r i * (1 - ∏ j ∈ s, r j)| := abs_add_le _ _
      _ = |1 - r i| + |r i| * |1 - ∏ j ∈ s, r j| := by rw [abs_mul]
      _ ≤ |1 - r i| + 1 * |1 - ∏ j ∈ s, r j| :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (hr i (Finset.mem_insert_self _ _)) (abs_nonneg _))
      _ ≤ |1 - r i| + ∑ j ∈ s, |1 - r j| := by simpa using add_le_add (le_refl |1 - r i|) (ih his)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

lemma top_wedge_determinant (n : ℕ) (v : Fin n → Vec n) :
    ExteriorAlgebra.ιMulti ℂ n v = (standardBasis n).det v • topWedge n := by
  have hf : ExteriorAlgebra.ιMulti ℂ n (M := Vec n) =
      ((standardBasis n).det).smulRight (topWedge n) := by
    apply (standardBasis n).ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change ExteriorAlgebra.ιMulti ℂ n ((standardBasis n) ∘ σ) =
      (((standardBasis n).det).smulRight (topWedge n)) ((standardBasis n) ∘ σ)
    simp [AlternatingMap.map_perm, topWedge, Module.Basis.det_self]
  exact DFunLike.congr_fun hf v

lemma generator_mem (n : ℕ) (i : Fin n) :
    generator n i ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ : Vec n →ₗ[ℂ] Grassmann n)) :=
  LinearMap.mem_range_self _ _

lemma twoForm_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    twoForm A ∈ ExteriorAlgebra.exteriorPower ℂ 2 (Vec n) := by
  unfold twoForm ExteriorAlgebra.exteriorPower
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  simpa only [pow_two] using Submodule.mul_mem_mul (generator_mem n i) (generator_mem n j)

lemma twoForm_pow_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    twoForm A ^ m ∈ ExteriorAlgebra.exteriorPower ℂ (2 * m) (Vec n) := by
  convert Submodule.pow_mem_pow _ (twoForm_mem A) m using 1
  all_goals try with_reducible_and_instances rfl
  exact pow_mul _ 2 m

lemma exteriorBasis_univ (n : ℕ) :
    (standardBasis n).ExteriorAlgebra Finset.univ = topWedge n := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (by simp : (Finset.univ : Finset (Fin n)).card = n)]
  unfold ExteriorAlgebra.ιMulti_family topWedge
  congr 1
  funext i
  simp only [Function.comp_apply]
  apply congrArg (standardBasis n)
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change Finset.univ.orderEmbOfFin (by simp) i = i
  exact congr_fun (Finset.orderEmbOfFin_unique (by simp)
    (fun x : Fin n => Finset.mem_univ x) (fun _ _ h => h)).symm i

@[simp] lemma topCoord_topWedge (n : ℕ) : topCoord n (topWedge n) = 1 := by
  rw [← exteriorBasis_univ]
  simp [topCoord, Module.Basis.coord_apply]

lemma topCoord_wedge (n : ℕ) (v : Fin n → Vec n) :
    topCoord n (ExteriorAlgebra.ιMulti ℂ n v) = (standardBasis n).det v := by
  rw [top_wedge_determinant, map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

lemma homogeneous_eq_coord_topWedge (n : ℕ) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    x = topCoord n x • topWedge n := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    rw [topCoord_wedge, top_wedge_determinant]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add, add_smul, ← ihx, ← ihy]
  | smul r x hx ih =>
    rw [map_smul, smul_eq_mul, ← smul_smul, ← ih]

lemma topCoord_map (n : ℕ) (f : Vec n →ₗ[ℂ] Vec n) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord n (ExteriorAlgebra.map f x) = f.det * topCoord n x := by
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, map_smul]
  unfold topWedge
  rw [ExteriorAlgebra.map_apply_ιMulti, topCoord_wedge]
  have hd : (standardBasis n).det (f ∘ standardBasis n) = f.det := by
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hd, smul_eq_mul, mul_comm]

lemma generator_anticomm (n : ℕ) (i j : Fin n) :
    generator n i * generator n j = -(generator n j * generator n i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

lemma sum_symmetric_offdiag {n : ℕ} {E : Type*} [AddCommGroup E]
    (F : Fin n → Fin n → E) (hF : ∀ i j, F i j = F j i)
    (hzero : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 • (∑ i, ∑ j ∈ Finset.Ioi i, F i j) := by
  have hij (i j : Fin n) : F i j =
      (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hzero]
    · simp [h, not_lt_of_gt h, hF i j]
  have hsum (i : Fin n) : (∑ j, if i < j then F i j else 0) =
      ∑ j ∈ Finset.Ioi i, F i j := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  calc
    ∑ i, ∑ j, F i j =
        (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ i, ∑ j, if j < i then F j i else 0) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hij i j
    _ = (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ j, ∑ i, if j < i then F j i else 0) := by
      rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
    _ = 2 • (∑ i, ∑ j ∈ Finset.Ioi i, F i j) := by
      simp only [hsum, two_nsmul]

lemma twoForm_full {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    twoForm A = (1 / 2 : ℂ) • ∑ i, ∑ j, A i j • (generator n i * generator n j) := by
  have hs := sum_symmetric_offdiag
    (fun i j => A i j • (generator n i * generator n j))
    (fun i j => by rw [hA i j, generator_anticomm n j i, neg_smul, smul_neg, neg_neg])
    (fun i => by simp [generator])
  rw [hs]
  change twoForm A = (1 / 2 : ℂ) • (2 • twoForm A)
  rw [← Nat.cast_smul_eq_nsmul ℂ 2, smul_smul]
  norm_num

lemma permMap_det (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permMap n σ).det = (Equiv.Perm.sign σ : ℂ) := by
  have he : permMap n σ ∘ standardBasis n = standardBasis n ∘ σ := by
    funext i
    exact permMap_basis n σ i
  have hd := Module.Basis.det_comp (standardBasis n) (permMap n σ) (standardBasis n)
  rw [he, AlternatingMap.map_perm, Module.Basis.det_self, mul_one] at hd
  simpa [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul] using hd.symm

lemma twoForm_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (σ : Equiv.Perm (Fin n)) :
    ExteriorAlgebra.map (permMap n σ) (twoForm A) =
      twoForm (fun i j => A (σ.symm i) (σ.symm j)) := by
  rw [twoForm_full A hA, twoForm_full _ (fun i j => hA _ _)]
  simp only [map_smul, map_sum, map_mul, permMap_generator]
  congr 1
  apply Fintype.sum_equiv σ
  intro i
  simp only [Equiv.symm_apply_apply]
  apply Fintype.sum_equiv σ
  intro j
  simp

lemma pfaffian_perm (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (σ : Equiv.Perm (Fin n)) :
    pfaffian n (fun i j => A (σ.symm i) (σ.symm j)) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian n A := by
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) :=
    by simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  change topCoord n (twoForm _ ^ (n / 2)) / _ =
    (Equiv.Perm.sign σ : ℂ) * (topCoord n (twoForm A ^ (n / 2)) / _)
  rw [← twoForm_perm A hA σ, ← map_pow, topCoord_map n _ _ hhom, permMap_det]
  ring

lemma wedge_anticomm {n : ℕ} (u v : Vec n) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v =
      -(ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ u) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

lemma wedge_commutes {n : ℕ} (u v : Vec n) (x : Grassmann n) :
    Commute (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r _).symm
  | ι w =>
    change (_ * _) * _ = _ * (_ * _)
    calc
      _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) :=
        mul_assoc _ _ _
      _ = -(ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
        rw [wedge_anticomm v w, mul_neg]
      _ = -((ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ v) := by
        rw [mul_assoc]
      _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ v := by
        rw [wedge_anticomm u w, neg_mul, neg_neg]
      _ = _ := mul_assoc _ _ _
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

lemma wedge_sq_zero {n : ℕ} (u v : Vec n) :
    (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) ^ 2 = 0 := by
  rw [pow_two, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι ℂ v), wedge_anticomm v u,
    neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero]
  simp

lemma generator_expansion (n : ℕ) (u : Vec n) :
    (∑ i, u i • generator n i) = ExteriorAlgebra.ι ℂ u := by
  have h := congrArg (ExteriorAlgebra.ι ℂ) ((standardBasis n).sum_repr u)
  simpa [standardBasis, generator, map_sum, map_smul] using h

lemma pow_add_sq_zero {E : Type*} [Ring E] [Algebra ℂ E] (a b : E)
    (hab : Commute a b) (hb : b ^ 2 = 0) (m : ℕ) :
    (a + b) ^ (m + 1) = a ^ (m + 1) + (m + 1 : ℂ) • (a ^ m * b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (a + b), ih, add_mul, mul_add, mul_add,
      smul_mul_assoc, smul_mul_assoc]
    have hba : a ^ m * b * a = a ^ (m + 1) * b := by
      rw [mul_assoc, hab.eq.symm, ← mul_assoc, ← pow_succ]
    have hbb : a ^ m * b * b = 0 := by rw [mul_assoc, ← pow_two, hb, mul_zero]
    rw [hba, hbb, smul_zero, add_zero, ← pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    module

lemma high_degree_zero {n k : ℕ} (hk : n < k) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ k (Vec n)) : x = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    apply AlternatingMap.map_linearDependent
    intro hv
    have h := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi] at h
    omega
  | zero => rfl
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul r x hx ih => simp [ih]

lemma border_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (i j : Fin (n + 1)) :
    border A u j i = -border A u i j := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [border_last_last, border_last_old, border_old_last, border_old_old,
      neg_zero, neg_neg]
  exact hA _ _

lemma twoForm_border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    twoForm (border A u) = ExteriorAlgebra.map (embedMap n) (twoForm A) +
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
  rw [twoForm_full _ (border_skew A hA u), twoForm_full A hA]
  simp only [map_smul, map_sum, map_mul, embedMap_generator]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc, border_old_old, border_old_last,
    border_last_old, border_last_last, zero_smul, add_zero, Finset.sum_add_distrib]
  have hu : (∑ i : Fin n, u i • generator (n + 1) i.castSucc) =
      ExteriorAlgebra.ι ℂ (embedMap n u) := by
    have h := congrArg (ExteriorAlgebra.map (embedMap n)) (generator_expansion n u)
    simpa using h
  have hp : (∑ i : Fin n, u i • (generator (n + 1) i.castSucc * generator (n + 1) (Fin.last n))) =
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
    rw [← hu, Finset.sum_mul]
    simp only [smul_mul_assoc]
  have hm : (∑ i : Fin n, -u i • (generator (n + 1) (Fin.last n) * generator (n + 1) i.castSucc)) =
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
    rw [← hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [generator_anticomm (n + 1) (Fin.last n), neg_smul, smul_neg, neg_neg]
  rw [hp, hm]
  module

lemma topWedge_snoc (n : ℕ) :
    topWedge (n + 1) = ExteriorAlgebra.map (embedMap n) (topWedge n) *
      generator (n + 1) (Fin.last n) := by
  unfold topWedge
  rw [ExteriorAlgebra.map_apply_ιMulti]
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Function.comp_apply, embedMap_basis, generator]

lemma topCoord_embed_mul_last {n : ℕ} (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord (n + 1) (ExteriorAlgebra.map (embedMap n) x * generator (n + 1) (Fin.last n)) =
      topCoord n x := by
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, smul_mul_assoc, ← topWedge_snoc,
    map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial
lemma pfaffian_border {n : ℕ} (hn : Odd n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    pfaffian (n + 1) (border A u) = borderLinear A u := by
  have hm : (n + 1) / 2 = n / 2 + 1 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hz : twoForm A ^ (n / 2 + 1) = 0 :=
    high_degree_zero (by omega) _ (twoForm_pow_mem A (n / 2 + 1))
  have hcomm : Commute (ExteriorAlgebra.map (embedMap n) (twoForm A))
      (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n)) :=
    (wedge_commutes _ _ _).symm
  unfold pfaffian
  change topCoord (n + 1) _ / _ = _
  rw [twoForm_border A hA, hm, pow_add_sq_zero _ _ hcomm (wedge_sq_zero _ _) (n / 2),
    ← map_pow, hz, map_zero, zero_add, map_smul, smul_eq_mul]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm0 : (↑(n / 2) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n / 2)
  rw [mul_div_mul_left _ _ hm0]
  rfl

lemma topCoord_embed_twice {n : ℕ} (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord (n + 2)
      (ExteriorAlgebra.map (embedMap (n + 1)) (ExteriorAlgebra.map (embedMap n) x) *
        (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1)))) =
      topCoord n x := by
  have ht : ExteriorAlgebra.map (embedMap (n + 1))
        (ExteriorAlgebra.map (embedMap n) (topWedge n)) *
        (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1))) =
      topWedge (n + 2) := by
    rw [← embedMap_generator (n + 1) (Fin.last n), ← mul_assoc, ← map_mul,
      ← topWedge_snoc, ← topWedge_snoc]
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, map_smul, smul_mul_assoc, ht, map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

lemma pfaffian_block_pair {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian (n + 2) (border (border A 0) (standardBasis (n + 1) (Fin.last n))) =
      pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have hm : (n + 1) / 2 = n / 2 := by obtain ⟨k, hk⟩ := hn; omega
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  rw [pfaffian_border hodd _ (border_skew A hA 0)]
  change topCoord (n + 2) _ / _ = _
  rw [twoForm_border A hA 0]
  simp only [map_zero, zero_mul, add_zero, embedMap_basis, hm, ← map_pow]
  change topCoord (n + 2)
    (ExteriorAlgebra.map (embedMap (n + 1)) (ExteriorAlgebra.map (embedMap n) (twoForm A ^ (n / 2))) *
      (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1)))) / _ = _
  rw [topCoord_embed_twice _ hhom]
  rfl

lemma basis_last (n : ℕ) : standardBasis (n + 1) (Fin.last n) = Fin.snoc (fun _ => 0) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [standardBasis, Pi.basisFun_apply]

lemma pfaffian_zero_row (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (i : Fin n) (hrow : ∀ j, A i j = 0) :
    pfaffian n A = 0 := by
  let f : Vec n →ₗ[ℂ] Vec n :=
    (standardBasis n).constr ℂ (fun j => if j = i then 0 else standardBasis n j)
  have hf (j : Fin n) : f (standardBasis n j) = if j = i then 0 else standardBasis n j := by
    exact (standardBasis n).constr_basis ℂ _ j
  have hdet : f.det = 0 := by
    have hd := Module.Basis.det_comp (standardBasis n) f (standardBasis n)
    rw [Module.Basis.det_self, mul_one] at hd
    rw [← hd]
    exact (standardBasis n).det.map_coord_zero i (by simp [hf])
  have hcol (j : Fin n) : A j i = 0 := by rw [hA, hrow, neg_zero]
  have hform : ExteriorAlgebra.map f (twoForm A) = twoForm A := by
    unfold twoForm
    simp only [map_sum, map_smul, map_mul, generator, ExteriorAlgebra.map_apply_ι, hf]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hji : j = i
    · subst j
      simp [hrow]
    by_cases hki : k = i
    · subst k
      simp [hcol]
    simp [hji, hki]
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  have htop := topCoord_map n f (twoForm A ^ (n / 2)) hhom
  rw [map_pow, hform, hdet, zero_mul] at htop
  change topCoord n (twoForm A ^ (n / 2)) / _ = 0
  rw [htop, zero_div]

lemma pfaffian_block_extra {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (t : ℂ) :
    pfaffian (n + 2) (border (border A 0) (Fin.snoc u t)) = t * pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have he : Fin.snoc u t = Fin.snoc u 0 + t • standardBasis (n + 1) (Fin.last n) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [basis_last]
  have hz : borderLinear (border A 0) (Fin.snoc u 0) = 0 := by
    rw [← pfaffian_border hodd _ (border_skew A hA 0)]
    apply pfaffian_zero_row (n + 2) (hodd.add_one) _
      (border_skew _ (border_skew A hA 0) _) (Fin.last n).castSucc
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [pfaffian_border hodd _ (border_skew A hA 0), he, map_add, map_smul, hz, zero_add]
  rw [← pfaffian_border hodd _ (border_skew A hA 0), pfaffian_block_pair hn A hA, smul_eq_mul]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

lemma prod_Ioi_castSucc {n : ℕ} (f : Fin (n + 1) → ℂ) (i : Fin n) :
    (∏ j ∈ Finset.Ioi i.castSucc, f j) = (∏ j ∈ Finset.Ioi i, f j.castSucc) * f (Fin.last n) := by
  have h1 : Finset.Ioi i.castSucc = Finset.univ.filter (fun j => i.castSucc < j) := by ext; simp
  have h2 : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext; simp
  rw [h1, h2, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp

lemma prod_Ioi_last {n : ℕ} (f : Fin (n + 1) → ℂ) :
    (∏ j ∈ Finset.Ioi (Fin.last n), f j) = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  have h := Finset.mem_Ioi.mp hj
  have hj := j.isLt
  change n < j.val at h
  omega

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ColumnGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip



noncomputable section
open scoped BigOperators
open Set MeasureTheory


theorem laguerreWeight_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < laguerreWeight a x :=
  mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

theorem measurable_laguerreWeight (a : ℝ) : Measurable (laguerreWeight a) := by
  unfold laguerreWeight
  fun_prop

theorem laguerreDensity_pos {N : ℕ} (a : ℝ) {r : Fin N → ℝ}
    (hr : r ∈ laguerreDomain N) : 0 < laguerreDensity N a r := by
  apply mul_pos
  · exact Finset.prod_pos fun i _ => laguerreWeight_pos a (hr.2 i)
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    exact pairKernel_pos (hr.2 i) (hr.1 (Finset.mem_Ioi.1 hj))

theorem measurable_laguerreDensity (N : ℕ) (a : ℝ) :
    Measurable (laguerreDensity N a) := by
  unfold laguerreDensity pairKernel
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_laguerreWeight a).comp (measurable_pi_apply i)
  · apply Finset.measurable_prod
    intro i _
    apply Finset.measurable_prod
    intro j _
    fun_prop

theorem isOpen_laguerreDomain (N : ℕ) : IsOpen (laguerreDomain N) := by
  have heq : laguerreDomain N =
      (⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i < j), {r | r i < r j}) ∩
      (⋂ i : Fin N, {r | 0 < r i}) := by
    ext r
    simp only [laguerreDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter, StrictMono]
  rw [heq]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_apply i)

theorem laguerreDomain_nonempty (N : ℕ) : (laguerreDomain N).Nonempty := by
  refine ⟨fun i => (i : ℝ) + 1, ?_, ?_⟩
  · intro i j hij
    dsimp
    exact_mod_cast (show i.val + 1 < j.val + 1 by omega)
  · intro i
    positivity

theorem pairKernel_le_right {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≤ y) :
    pairKernel x y ≤ y := by
  unfold pairKernel
  apply (div_le_iff₀ (by linarith : 0 < y + x)).2
  have hxx := mul_le_mul_of_nonneg_left hxy hx
  nlinarith [mul_nonneg hx hy.le]

theorem prod_pair_right (N : ℕ) (r : Fin N → ℝ) :
    (∏ i, ∏ j ∈ Finset.Ioi i, r j) = ∏ j, r j ^ j.val := by
  classical
  calc
    (∏ i, ∏ j ∈ Finset.Ioi i, r j) =
        ∏ i, ∏ j : Fin N, if i < j then r j else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_filter]
      congr 1
      ext j
      simp
    _ = ∏ j : Fin N, ∏ i : Fin N, if i < j then r j else 1 := Finset.prod_comm
    _ = ∏ j : Fin N, r j ^ j.val := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← Finset.prod_filter]
      simp [show Finset.univ.filter (fun i : Fin N => i < j) = Finset.Iio j by ext; simp]

theorem laguerreDensity_le_product {N : ℕ} (a : ℝ) {r : Fin N → ℝ}
    (hr : r ∈ laguerreDomain N) :
    laguerreDensity N a r ≤ ∏ i, laguerreWeight (a + i.val) (r i) := by
  have hp : (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j)) ≤
      ∏ i, ∏ j ∈ Finset.Ioi i, r j := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.prod_nonneg fun j _ => pairKernel_nonneg (hr.2 i).le (hr.2 j).le
    · intro i _
      apply Finset.prod_le_prod
      · intro j _
        exact pairKernel_nonneg (hr.2 i).le (hr.2 j).le
      · intro j hj
        exact pairKernel_le_right (hr.2 i).le (hr.2 j) (hr.1 (Finset.mem_Ioi.1 hj)).le
  rw [prod_pair_right] at hp
  calc
    laguerreDensity N a r ≤ (∏ i, laguerreWeight a (r i)) * ∏ i, r i ^ i.val :=
      mul_le_mul_of_nonneg_left hp (Finset.prod_nonneg fun i _ => (laguerreWeight_pos a (hr.2 i)).le)
    _ = ∏ i, laguerreWeight (a + i.val) (r i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      unfold laguerreWeight
      rw [show a + (i.val : ℝ) - 1 = (a - 1) + (i.val : ℝ) by ring,
        Real.rpow_add (hr.2 i), Real.rpow_natCast]
      ring

theorem integrableOn_laguerreWeight {a : ℝ} (ha : 0 < a) :
    IntegrableOn (laguerreWeight a) (Ioi 0) := by
  change IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-x)) (Ioi 0)
  simpa only [mul_comm] using Real.GammaIntegral_convergent ha

theorem integral_laguerreWeight {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi 0, laguerreWeight a x) = Real.Gamma a := by
  simpa only [laguerreWeight, mul_comm] using (Real.Gamma_eq_integral ha).symm

theorem integrableOn_laguerre_product {N : ℕ} {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : Fin N → ℝ => ∏ i, laguerreWeight (a + i.val) (r i))
      (Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) := by
  unfold IntegrableOn
  rw [volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod fun i =>
    integrableOn_laguerreWeight (by positivity : 0 < a + (i.val : ℝ))

theorem integrableOn_laguerreDensity (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (laguerreDensity N a) (laguerreDomain N) := by
  have hp := (integrableOn_laguerre_product (N := N) ha).mono_set
    (show laguerreDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)) from
      fun r hr i _ => hr.2 i)
  apply hp.mono' (measurable_laguerreDensity N a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simpa only [Real.norm_eq_abs, abs_of_pos (laguerreDensity_pos a hr)] using
    laguerreDensity_le_product a hr

theorem laguerreNormalizer_pos (N : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < laguerreNormalizer N a := by
  have hpos : 0 ≤ᵐ[volume.restrict (laguerreDomain N)] laguerreDensity N a := by
    filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
    exact (laguerreDensity_pos a hr).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos (integrableOn_laguerreDensity N ha)).2
  have hs : laguerreDomain N ⊆ Function.support (laguerreDensity N a) :=
    fun r hr => (laguerreDensity_pos a hr).ne'
  calc
    0 < volume (laguerreDomain N) :=
      (isOpen_laguerreDomain N).measure_pos volume (laguerreDomain_nonempty N)
    _ = (volume.restrict (laguerreDomain N)) (laguerreDomain N) :=
      (Measure.restrict_apply_self _ _).symm
    _ ≤ (volume.restrict (laguerreDomain N)) (Function.support (laguerreDensity N a)) :=
      measure_mono hs



theorem integrableOn_laguerre_inverse_coordinate {N : ℕ} {a p : ℝ}
    (ha : 0 < a) (i : Fin N) (hp : p < a + i.val) :
    IntegrableOn (fun r => (r i) ^ (-p) * laguerreDensity N a r) (laguerreDomain N) := by
  classical
  let b : Fin N → ℝ := fun j => a + j.val - if j = i then p else 0
  have hb : ∀ j, 0 < b j := by
    intro j
    by_cases hj : j = i
    · simpa [b, hj] using sub_pos.mpr hp
    · simp only [b, hj, ite_false, sub_zero]
      positivity
  have heq : ∀ r : Fin N → ℝ, (∀ j, 0 < r j) →
      (r i) ^ (-p) * (∏ j, laguerreWeight (a + j.val) (r j)) =
        ∏ j, laguerreWeight (b j) (r j) := by
    intro r hr
    calc
      _ = (∏ j, if j = i then (r j) ^ (-p) else 1) *
          ∏ j, laguerreWeight (a + j.val) (r j) := by simp
      _ = ∏ j, (if j = i then (r j) ^ (-p) else 1) *
          laguerreWeight (a + j.val) (r j) := (Finset.prod_mul_distrib).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases hj : j = i
        · simp only [b, hj, ite_true, laguerreWeight]
          rw [show a + (i.val : ℝ) - p - 1 = -p + (a + i.val - 1) by ring,
            Real.rpow_add (hr i)]
          ring
        · simp [b, hj]
  have hi : IntegrableOn (fun r : Fin N → ℝ => ∏ j, laguerreWeight (b j) (r j))
      (Set.univ.pi fun _ : Fin N => Ioi (0 : ℝ)) := by
    unfold IntegrableOn
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun j => integrableOn_laguerreWeight (hb j)
  have hs : laguerreDomain N ⊆ Set.univ.pi (fun _ : Fin N => Ioi (0 : ℝ)) :=
    fun r hr j _ => hr.2 j
  apply (hi.mono_set hs).mono'
    (((measurable_pi_apply i).pow_const _).mul (measurable_laguerreDensity N a)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  change ‖(r i) ^ (-p) * laguerreDensity N a r‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (hr.2 i) _).le
    (laguerreDensity_pos a hr).le),
    ← heq r hr.2]
  exact mul_le_mul_of_nonneg_left (laguerreDensity_le_product a hr)
    (Real.rpow_pos_of_pos (hr.2 i) _).le



theorem laguerreLaw_isProbabilityMeasure (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (laguerreLaw N a) := by
  refine ⟨?_⟩
  rw [laguerreLaw, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_laguerreDensity N ha)]
  · exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (laguerreNormalizer_pos N ha)).ne'
      ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
    exact (laguerreDensity_pos a hr).le

theorem ae_laguerreDomain (N : ℕ) (a : ℝ) :
    ∀ᵐ r ∂laguerreLaw N a, r ∈ laguerreDomain N := by
  apply Measure.ae_smul_measure
  apply (ae_withDensity_iff (measurable_laguerreDensity N a).ennreal_ofReal).2
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  exact fun _ => hr

theorem integral_laguerreLaw (N : ℕ) {a : ℝ} (ha : 0 < a) (f : (Fin N → ℝ) → ℝ) :
    (∫ r, f r ∂laguerreLaw N a) = laguerreExpectation N a f := by
  rw [laguerreLaw, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_laguerreDensity N a).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (laguerreNormalizer_pos N ha).le,
    smul_eq_mul, laguerreExpectation, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  rw [ENNReal.toReal_ofReal (laguerreDensity_pos a hr).le, mul_comm]

theorem integrable_laguerreLaw {N : ℕ} {a : ℝ} (ha : 0 < a)
    {f : (Fin N → ℝ) → ℝ}
    (hf : IntegrableOn (fun r => f r * laguerreDensity N a r) (laguerreDomain N)) :
    Integrable f (laguerreLaw N a) := by
  apply Integrable.smul_measure (c := (ENNReal.ofReal (laguerreNormalizer N a))⁻¹) ?_
    (by simp [laguerreNormalizer_pos N ha])
  apply (integrable_withDensity_iff_integrable_smul' (measurable_laguerreDensity N a).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  apply hf.congr
  filter_upwards [ae_restrict_mem (isOpen_laguerreDomain N).measurableSet] with r hr
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (laguerreDensity_pos a hr).le, mul_comm]

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TailIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory





theorem laguerreDomain_cons_iff {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    Fin.cons x r ∈ laguerreDomain (n + 1) ↔
      0 < x ∧ r ∈ laguerreDomain n ∧ ∀ i, x < r i := by
  simp only [laguerreDomain, mem_ofPred_eq, Fin.strictMono_cons, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ]
  tauto

theorem pairProduct_cons {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
      pairKernel ((Fin.cons x r : Fin (n + 1) → ℝ) i) ((Fin.cons x r : Fin (n + 1) → ℝ) j)) =
      (∏ j, pairKernel x (r j)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j) := by
  classical
  have he {m : ℕ} (s : Fin m → ℝ) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, pairKernel (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then pairKernel (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    ↓reduceIte, Fin.succ_pos, Fin.not_lt_zero, Fin.succ_lt_succ_iff, one_mul]

theorem laguerreDensity_cons {n : ℕ} (a x : ℝ) (r : Fin n → ℝ) :
    laguerreDensity (n + 1) a (Fin.cons x r) =
      laguerreWeight a x * laguerreDensity n a r * ∏ i, pairKernel x (r i) := by
  unfold laguerreDensity
  rw [pairProduct_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem laguerreDensity_succ_parameter {n : ℕ} (a : ℝ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) :
    laguerreDensity n (a + 1) r = laguerreDensity n a r * ∏ i, r i := by
  have he : ∀ i, laguerreWeight (a + 1) (r i) = laguerreWeight a (r i) * r i := by
    intro i
    unfold laguerreWeight
    rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add (hr i), Real.rpow_one]
    ring
  simp only [laguerreDensity, he, Finset.prod_mul_distrib]
  ring

theorem integral_fin_cons_eq (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    (∫ r, f r) = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) := by
  symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm).integral_comp' f

theorem integrable_fin_cons {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)) := by
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm).integrable_comp_of_integrable hf

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InverseIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace StripPfaffian
noncomputable section
open scoped BigOperators _root_.Matrix

lemma congruence_skew {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    ∀ i j, (M * A * M.transpose) j i = -(M * A * M.transpose) i j := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [hA l k]
  ring

lemma toLin_basis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    Matrix.toLin' M (standardBasis n i) = ∑ j, M j i • standardBasis n j := by
  ext k
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, standardBasis,
    Pi.basisFun_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]

lemma sum_four_reverse {ι E : Type*} [Fintype ι] [AddCommMonoid E]
    (F : ι → ι → ι → ι → E) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ l, ∑ k, ∑ j, ∑ i, F i j k l := by
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) :=
    ⟨(fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)),
     (fun p => (p.2.2.2, p.2.2.1, p.2.1, p.1)), by intro p; rfl, by intro p; rfl⟩
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv e (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => F p.2.2.2 p.2.2.1 p.2.1 p.1) (fun _ => rfl))

lemma twoForm_congruence {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    ExteriorAlgebra.map (Matrix.toLin' M) (twoForm A) = twoForm (M * A * M.transpose) := by
  rw [twoForm_full A hA, twoForm_full _ (congruence_skew M A hA)]
  simp only [map_smul, map_sum, map_mul]
  congr 1
  simp only [generator, ExteriorAlgebra.map_apply_ι,
    toLin_basis, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_smul,
    Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, Finset.sum_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [sum_four_reverse]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

lemma pfaffian_congruence {n : ℕ} (hn : Even n) (M A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian n (M * A * M.transpose) = M.det * pfaffian n A := by
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) :=
    by simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  change topCoord n (twoForm _ ^ (n / 2)) / _ =
    M.det * (topCoord n (twoForm A ^ (n / 2)) / _)
  rw [← twoForm_congruence M A hA, ← map_pow, topCoord_map n _ _ hhom]
  have hd : (Matrix.toLin' M).det = M.det := by
    rw [← LinearMap.det_toMatrix (standardBasis n)]
    congr 1
    ext i j
    simp [standardBasis, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hd]
  ring

lemma pfaffian_scale_coordinates {n : ℕ} (hn : Even n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (s : Fin n → ℂ) :
    pfaffian n (fun i j => s i * A i j * s j) = (∏ i, s i) * pfaffian n A := by
  have hM : Matrix.diagonal s * A * (Matrix.diagonal s).transpose =
      fun i j => s i * A i j * s j := by
    ext i j
    simp only [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simpa only [hM, Matrix.det_diagonal] using
    pfaffian_congruence hn (Matrix.diagonal s) A hA

lemma schurComplement_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u v : Vec n) (t : ℂ) :
    ∀ i j, schurComplement A u v t j i = -schurComplement A u v t i j := by
  intro i j
  simp only [schurComplement, hA i j]
  ring

lemma eliminatingShear_upper {n : ℕ} (u v : Vec n) (t : ℂ) :
    (eliminatingShear u v t).IsUpperTriangular := by
  intro i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun i => ?_) i) i
  all_goals
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) j
  all_goals
    intro hji
    simp only [id_eq] at hji
    simp_all [eliminatingShear]
  all_goals
    simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hji
    try omega

lemma eliminatingShear_det {n : ℕ} (u v : Vec n) (t : ℂ) :
    (eliminatingShear u v t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (eliminatingShear_upper u v t),
    Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp [eliminatingShear]

lemma eliminatingShear_congruence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (_hA : ∀ i j, A j i = -A i j) (u v : Vec n) {t : ℂ} (ht : t ≠ 0) :
    eliminatingShear u v t * border (border A u) (Fin.snoc v t) * (eliminatingShear u v t).transpose =
      border (border (schurComplement A u v t) 0) (Fin.snoc 0 t) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun i => ?_) i) i
  all_goals
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) j
  all_goals
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [Fin.sum_univ_castSucc]
    simp [eliminatingShear, schurComplement, ht]
  all_goals field_simp [ht]
  all_goals ring

lemma pfaffian_schur_complement {n : ℕ} (hn : Even n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j)
    (u v : Vec n) {t : ℂ} (ht : t ≠ 0) :
    pfaffian (n + 2) (border (border A u) (Fin.snoc v t)) =
      t * pfaffian n (schurComplement A u v t) := by
  have h := pfaffian_congruence (hn.add (by decide : Even 2))
    (eliminatingShear u v t) (border (border A u) (Fin.snoc v t))
    (border_skew _ (border_skew A hA u) _)
  rw [eliminatingShear_det, one_mul, eliminatingShear_congruence A hA u v ht,
    pfaffian_block_extra hn _ (schurComplement_skew A hA u v t)] at h
  exact h.symm

end

noncomputable section
open scoped BigOperators

lemma schurEntry_self (x : ℂ) : schurEntry x x = 0 := by simp [schurEntry]
lemma schurEntry_swap (x y : ℂ) : schurEntry y x = -schurEntry x y := by
  simp only [schurEntry, add_comm y x]
  ring
lemma schurMatrix_skew {n : ℕ} (x : Fin n → ℂ) :
    ∀ i j, schurMatrix x j i = -schurMatrix x i j :=
  fun i j => schurEntry_swap (x i) (x j)
lemma schurEntry_ne_zero {x y : ℂ} (hne : y ≠ x) (hd : x + y ≠ 0) :
    schurEntry x y ≠ 0 := div_ne_zero (sub_ne_zero.mpr hne) hd

lemma schurEntry_elimination {x y a b : ℂ}
    (hxy : x + y ≠ 0) (hxa : x + a ≠ 0) (hxb : x + b ≠ 0)
    (hya : y + a ≠ 0) (hyb : y + b ≠ 0) (_hab : a + b ≠ 0) (hne : b ≠ a) :
    schurEntry x y -
        (schurEntry x a * schurEntry y b - schurEntry x b * schurEntry y a) /
          schurEntry a b =
      (schurEntry x a * schurEntry x b) * schurEntry x y *
        (schurEntry y a * schurEntry y b) := by
  have hba := sub_ne_zero.mpr hne
  unfold schurEntry
  field_simp
  ring

lemma schurEntry_border_elimination {x y a : ℂ}
    (hxy : x + y ≠ 0) (hxa : x + a ≠ 0) (hya : y + a ≠ 0) :
    schurEntry x y - (schurEntry x a - schurEntry y a) =
      schurEntry x a * schurEntry x y * schurEntry y a := by
  unfold schurEntry
  field_simp
  ring

lemma schurMatrix_snoc {n : ℕ} (x : Fin n → ℂ) (a : ℂ) :
    schurMatrix (Fin.snoc x a) = border (schurMatrix x) (fun i => schurEntry (x i) a) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [schurMatrix, Fin.snoc_last, Fin.snoc_castSucc, border_last_last,
      border_last_old, border_old_last, border_old_old, schurEntry_self]
  exact schurEntry_swap _ _

lemma schurColumn_snoc {n : ℕ} (x : Fin n → ℂ) (a b : ℂ) :
    (fun i : Fin (n + 1) => schurEntry (Fin.snoc (α := fun _ => ℂ) x a i) b) =
      Fin.snoc (fun i => schurEntry (x i) b) (schurEntry a b) := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

lemma schurProduct_snoc {n : ℕ} (x : Fin n → ℂ) (a : ℂ) :
    schurProduct (Fin.snoc x a) = schurProduct x * ∏ i, schurEntry (x i) a := by
  unfold schurProduct
  rw [Fin.prod_univ_castSucc, prod_Ioi_last, mul_one]
  simp_rw [prod_Ioi_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  exact Finset.prod_mul_distrib

@[simp] lemma pfaffian_empty (A : Matrix (Fin 0) (Fin 0) ℂ) : pfaffian 0 A = 1 := by
  have h := topCoord_topWedge 0
  simpa [topCoord, topWedge, ExteriorAlgebra.ιMulti_zero_apply, pfaffian,
    Module.Basis.coord_apply] using h

lemma pfaffian_schur_snoc_snoc {n : ℕ} (hn : Even n) (x : Fin n → ℂ) (a b : ℂ)
    (hbase : pfaffian n (schurMatrix x) = schurProduct x)
    (hxx : ∀ i j, x i + x j ≠ 0) (hxa : ∀ i, x i + a ≠ 0)
    (hxb : ∀ i, x i + b ≠ 0) (hab : a + b ≠ 0) (hne : b ≠ a) :
    pfaffian (n + 2) (schurMatrix (Fin.snoc (Fin.snoc x a) b)) =
      schurProduct (Fin.snoc (Fin.snoc x a) b) := by
  have hc : schurComplement (schurMatrix x) (fun i => schurEntry (x i) a)
      (fun i => schurEntry (x i) b) (schurEntry a b) =
      fun i j => (schurEntry (x i) a * schurEntry (x i) b) * schurMatrix x i j *
        (schurEntry (x j) a * schurEntry (x j) b) := by
    ext i j
    exact schurEntry_elimination (hxx i j) (hxa i) (hxb i) (hxa j) (hxb j) hab hne
  rw [schurMatrix_snoc, schurMatrix_snoc, schurColumn_snoc,
    pfaffian_schur_complement hn _ (schurMatrix_skew x) _ _ (schurEntry_ne_zero hne hab),
    hc, pfaffian_scale_coordinates hn _ (schurMatrix_skew x), hbase]
  simp only [schurProduct_snoc, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Finset.prod_mul_distrib]
  ring

 
end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SchurIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
theorem pfaffian_schur_even (n : ℕ) (hn : Even n) (x : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian n (schurMatrix x) = schurProduct x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [schurProduct]
  | one => exact False.elim (by simp at hn)
  | more n ih _ =>
    have he : Even n := by
      rw [Nat.even_iff] at *
      omega
    revert hd hx
    refine Fin.snocCases (fun y b => ?_) x
    refine Fin.snocCases (fun z a => ?_) y
    intro hd hx
    apply pfaffian_schur_snoc_snoc he z a b
    · apply ih he
      · intro i j
        simpa only [Fin.snoc_castSucc] using hd i.castSucc.castSucc j.castSucc.castSucc
      · intro i j hij
        apply Fin.castSucc_injective
        apply Fin.castSucc_injective
        apply hx
        simpa only [Fin.snoc_castSucc] using hij
    · intro i j
      simpa only [Fin.snoc_castSucc] using hd i.castSucc.castSucc j.castSucc.castSucc
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd i.castSucc.castSucc (Fin.last n).castSucc
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd i.castSucc.castSucc (Fin.last (n + 1))
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd (Fin.last n).castSucc (Fin.last (n + 1))
    · intro hab
      exact Fin.castSucc_ne_last (Fin.last n) (hx (by
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hab.symm))

lemma pfaffian_schur_odd_snoc {n : ℕ} (hn : Even n) (x : Fin n → ℂ) (a : ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x)
    (ha : ∀ i, x i + a ≠ 0) :
    pfaffian (n + 2) (border (schurMatrix (Fin.snoc x a)) (fun _ => 1)) =
      schurProduct (Fin.snoc x a) := by
  have hc : schurComplement (schurMatrix x) (fun i => schurEntry (x i) a) (fun _ => 1) 1 =
      fun i j => schurEntry (x i) a * schurMatrix x i j * schurEntry (x j) a := by
    ext i j
    simpa only [schurComplement, schurMatrix, mul_one, one_mul, div_one] using
      schurEntry_border_elimination (hd i j) (ha i) (ha j)
  have h1 : (fun _ : Fin (n + 1) => (1 : ℂ)) = Fin.snoc (fun _ => 1) 1 := by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  rw [schurMatrix_snoc, h1,
    pfaffian_schur_complement hn _ (schurMatrix_skew x) _ _ one_ne_zero,
    one_mul, hc, pfaffian_scale_coordinates hn _ (schurMatrix_skew x),
    pfaffian_schur_even n hn x hd hx, schurProduct_snoc, mul_comm]

 
theorem pfaffian_schur_odd (n : ℕ) (hn : Odd n) (x : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian (n + 1) (border (schurMatrix x) (fun _ => 1)) = schurProduct x := by
  cases n with
  | zero => exact False.elim (by simp at hn)
  | succ n =>
    have he : Even n := by
      rw [Nat.odd_iff] at hn
      rw [Nat.even_iff]
      omega
    revert hd hx
    refine Fin.snocCases (fun y a => ?_) x
    intro hd hx
    apply pfaffian_schur_odd_snoc he y a
    · intro i j
      simpa only [Fin.snoc_castSucc] using hd i.castSucc j.castSucc
    · intro i j hij
      apply Fin.castSucc_injective
      apply hx
      simpa only [Fin.snoc_castSucc] using hij
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hd i.castSucc (Fin.last n)

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open MeasureTheory Set
open scoped BigOperators

lemma integral_translate_Ioi (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in Ioi a, f (x + b)) = ∫ x in Ioi (a + b), f x := by
  have hp : (fun x : ℝ => x + b) ⁻¹' Ioi (a + b) = Ioi a := by
    ext x
    simp
  simpa only [hp] using (measurePreserving_add_right volume b).setIntegral_preimage_emb
    (Homeomorph.addRight b).measurableEmbedding f (Ioi (a + b))

lemma integral_shifted_rpow {p : ℝ} (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), (1 + t) ^ (-(p + 1))) = 1 / p := by
  calc
    _ = ∫ x in Ioi (1 : ℝ), x ^ (-(p+1)) := by
      simpa only [zero_add, add_comm] using
        integral_translate_Ioi (fun x : ℝ => x ^ (-(p+1))) 0 1
    _ = 1 / p := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -(p+1)< -1) (by norm_num : (0:ℝ)<1),
        Real.one_rpow]
      rw [show -(p+1)+1 = -p by ring, neg_div_neg_eq]

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

lemma ae_pos_pair : ∀ᵐ rs : ℝ × ℝ ∂μ₊.prod μ₊, 0 < rs.1 ∧ 0 < rs.2 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  exact (ae_restrict_mem measurableSet_Ioi).mono fun r hr =>
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => ⟨hr, hs⟩

lemma measurable_gammaLaplace (p q : ℝ) : Measurable (gammaLaplace p q) := by
  unfold gammaLaplace laguerreWeight
  fun_prop

lemma integrable_gammaLaplace_section (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun t => gammaLaplace p q ((r,s),t)) μ₊ := by
  exact (integrableOn_exp_mul_Ioi (show -(r+s) < 0 by linarith) 0).const_mul
    (laguerreWeight p r * laguerreWeight q s * r)

lemma integral_gammaLaplace_section (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ t, gammaLaplace p q ((r,s),t) ∂μ₊) =
      laguerreWeight p r * laguerreWeight q s * (r / (r+s)) := by
  simp only [gammaLaplace, integral_const_mul,
    integral_exp_mul_Ioi (show -(r+s) < 0 by linarith) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

lemma integrable_gammaFraction {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun rs : ℝ × ℝ => laguerreWeight p rs.1 * laguerreWeight q rs.2 *
      (rs.1 / (rs.1 + rs.2))) (μ₊.prod μ₊) := by
  have hi := (integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq)
  apply hi.mono' (by unfold laguerreWeight; fun_prop)
  filter_upwards [ae_pos_pair] with rs hrs
  obtain ⟨hr,hs⟩ := hrs
  have hw : 0 ≤ laguerreWeight p rs.1 * laguerreWeight q rs.2 :=
    mul_nonneg (laguerreWeight_pos p hr).le (laguerreWeight_pos q hs).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (div_nonneg hr.le (add_pos hr hs).le))]
  exact mul_le_of_le_one_right hw ((div_le_one (add_pos hr hs)).2 (by linarith))

lemma integrable_gammaLaplace {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (gammaLaplace p q) ((μ₊.prod μ₊).prod μ₊) := by
  apply (integrable_prod_iff (measurable_gammaLaplace p q).aestronglyMeasurable).2
  constructor
  · exact ae_pos_pair.mono fun rs hrs => integrable_gammaLaplace_section p q hrs.1 hrs.2
  · apply (integrable_gammaFraction hp hq).congr
    filter_upwards [ae_pos_pair] with rs hrs
    rw [← integral_gammaLaplace_section p q hrs.1 hrs.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (Real.norm_of_nonneg (by
      unfold gammaLaplace
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (laguerreWeight_pos p hrs.1).le (laguerreWeight_pos q hrs.2).le) hrs.1.le)
        (Real.exp_pos _).le)).symm

lemma gammaLaplace_factor (p q : ℝ) {r s : ℝ} (hr : 0 < r) (_hs : 0 < s) (t : ℝ) :
    gammaLaplace p q ((r,s),t) =
      (r ^ p * Real.exp (-((1+t)*r))) *
        (s ^ (q-1) * Real.exp (-((1+t)*s))) := by
  unfold gammaLaplace laguerreWeight
  have hrp : r^p = r^(p-1)*r := by
    calc
      _ = r ^ ((p-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hr, Real.rpow_one]
  rw [hrp]
  have he : Real.exp (-r) * Real.exp (-s) * Real.exp (-(r+s)*t) =
      Real.exp (-((1+t)*r)) * Real.exp (-((1+t)*s)) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (r^(p-1) * r * s^(q-1)) *
        (Real.exp (-r) * Real.exp (-s) * Real.exp (-(r+s)*t)) := by ring
    _ = _ := by rw [he]; ring

lemma integral_gammaLaplace_pair {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    (∫ rs : ℝ × ℝ, gammaLaplace p q (rs,t) ∂μ₊.prod μ₊) =
      (Real.Gamma (p+1) * Real.Gamma q) * (1+t)^(-(p+q+1)) := by
  calc
    _ = ∫ rs : ℝ × ℝ, (rs.1^p * Real.exp (-((1+t)*rs.1))) *
        (rs.2^(q-1) * Real.exp (-((1+t)*rs.2))) ∂μ₊.prod μ₊ := by
      apply integral_congr_ae
      exact ae_pos_pair.mono fun rs hrs => gammaLaplace_factor p q hrs.1 hrs.2 t
    _ = (∫ r in Ioi 0, r^p * Real.exp (-((1+t)*r))) *
        (∫ s in Ioi 0, s^(q-1) * Real.exp (-((1+t)*s))) := integral_prod_mul (μ := μ₊) (ν := μ₊)
      (fun r : ℝ => r^p * Real.exp (-((1+t)*r)))
      (fun s : ℝ => s^(q-1) * Real.exp (-((1+t)*s)))
    _ = ((1/(1+t))^(p+1) * Real.Gamma (p+1)) *
        ((1/(1+t))^q * Real.Gamma q) := by
      rw [show p = (p+1)-1 by ring, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0<p+1)
        (by linarith : 0<1+t), Real.integral_rpow_mul_exp_neg_mul_Ioi hq (by linarith : 0<1+t)]
      ring_nf
    _ = _ := by
      rw [show p+q+1 = (p+1)+q by ring, neg_add, Real.rpow_add (by linarith : 0<1+t)]
      simp only [one_div, Real.inv_rpow (by linarith : 0≤1+t), Real.rpow_neg (by linarith : 0≤1+t)]
      ring

lemma integral_gammaFraction {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 *
      (rs.1 / (rs.1+rs.2)) ∂μ₊.prod μ₊) =
      Real.Gamma p * Real.Gamma q * (p / (p+q)) := by
  calc
    _ = ∫ rs : ℝ × ℝ, ∫ t, gammaLaplace p q (rs,t) ∂μ₊ ∂μ₊.prod μ₊ := by
      apply integral_congr_ae
      exact ae_pos_pair.mono fun rs hrs => (integral_gammaLaplace_section p q hrs.1 hrs.2).symm
    _ = ∫ t, ∫ rs : ℝ × ℝ, gammaLaplace p q (rs,t) ∂μ₊.prod μ₊ ∂μ₊ :=
      integral_integral_swap (integrable_gammaLaplace hp hq)
    _ = ∫ t, (Real.Gamma (p+1) * Real.Gamma q) * (1+t)^(-(p+q+1)) ∂μ₊ := by
      apply integral_congr_ae
      exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => integral_gammaLaplace_pair hp hq ht
    _ = _ := by
      rw [integral_const_mul, integral_shifted_rpow (add_pos hp hq), Real.Gamma_add_one hp.ne']
      ring



lemma gammaSkewIntegrand_eq (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    gammaSkewIntegrand p q (r,s) =
      laguerreWeight p r * laguerreWeight q s -
        2 * (laguerreWeight p r * laguerreWeight q s * (r/(r+s))) := by
  unfold gammaSkewIntegrand
  field_simp [(add_pos hr hs).ne', (add_pos hs hr).ne']
  ring

lemma integrable_gammaSkewIntegrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (gammaSkewIntegrand p q) (μ₊.prod μ₊) := by
  have h := ((integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq)).sub
    ((integrable_gammaFraction hp hq).const_mul 2)
  exact h.congr (ae_pos_pair.mono fun rs hrs => (gammaSkewIntegrand_eq p q hrs.1 hrs.2).symm)

lemma integral_gammaSkewIntegrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ rs : ℝ × ℝ, gammaSkewIntegrand p q rs ∂μ₊.prod μ₊) =
      Real.Gamma p * Real.Gamma q * ((q-p)/(p+q)) := by
  calc
    _ = (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 ∂μ₊.prod μ₊) -
        2 * (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 *
          (rs.1/(rs.1 + rs.2)) ∂μ₊.prod μ₊) := by
      rw [← integral_const_mul, ← integral_sub
        ((integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq))
        ((integrable_gammaFraction hp hq).const_mul 2)]
      exact integral_congr_ae (ae_pos_pair.mono fun rs hrs => gammaSkewIntegrand_eq p q hrs.1 hrs.2)
    _ = _ := by
      rw [integral_prod_mul (μ := μ₊) (ν := μ₊) (laguerreWeight p) (laguerreWeight q),
        integral_laguerreWeight hp, integral_laguerreWeight hq, integral_gammaFraction hp hq]
      field_simp [(add_pos hp hq).ne']
      ring

 
theorem laguerre_double_moment {a : ℝ} (ha : 0 < a) (i j : ℕ) :
    Integrable (gammaSkewIntegrand (a+i) (a+j)) (μ₊.prod μ₊) ∧
    (∫ rs : ℝ × ℝ, gammaSkewIntegrand (a+i) (a+j) rs ∂μ₊.prod μ₊) =
      Real.Gamma (a+i) * Real.Gamma (a+j) * (((j:ℝ)-i)/(2*a+i+j)) := by
  have hi : 0 < a+(i:ℝ) := by positivity
  have hj : 0 < a+(j:ℝ) := by positivity
  refine ⟨integrable_gammaSkewIntegrand hi hj, ?_⟩
  rw [integral_gammaSkewIntegrand hi hj]
  congr 2 <;> ring

end
end CriticalStrip

namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma border_scale_coordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u s : Vec n) :
    border (fun i j => s i * A i j * s j) (fun i => s i * u i) =
      fun i j => (Fin.snoc s (1:ℂ) : Vec (n+1)) i * border A u i j *
        (Fin.snoc s (1:ℂ) : Vec (n+1)) j := by
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  all_goals refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp [border]
  ring

lemma pfaffian_border_scale_coordinates {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (u s : Vec n) :
    pfaffian (n+1) (border (fun i j => s i * A i j * s j) (fun i => s i * u i)) =
      (∏ i, s i) * pfaffian (n+1) (border A u) := by
  rw [border_scale_coordinates, pfaffian_scale_coordinates hn.add_one _ (border_skew A hA u),
    Fin.prod_univ_castSucc]
  simp

 

theorem pfaffian_weighted_schur_even (n : ℕ) (hn : Even n) (x s : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian n (fun i j => s i * schurEntry (x i) (x j) * s j) =
      (∏ i, s i) * schurProduct x := by
  have h := pfaffian_scale_coordinates hn (schurMatrix x) (schurMatrix_skew x) s
  rw [pfaffian_schur_even n hn x hd hx] at h
  exact h

theorem pfaffian_weighted_schur_odd (n : ℕ) (hn : Odd n) (x s : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian (n+1) (border (fun i j => s i * schurEntry (x i) (x j) * s j) s) =
      (∏ i, s i) * schurProduct x := by
  have h := pfaffian_border_scale_coordinates hn (schurMatrix x) (schurMatrix_skew x)
    (fun _ => 1) s
  rw [pfaffian_schur_odd n hn x hd hx] at h
  simpa only [mul_one, schurMatrix] using h

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

lemma laguerreMomentMatrix_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    laguerreMomentMatrix n a = fun i j =>
      (Real.Gamma (a+i.val) : ℂ) *
        schurEntry ((a+i.val : ℝ) : ℂ) ((a+j.val : ℝ) : ℂ) *
          (Real.Gamma (a+j.val) : ℂ) := by
  ext i j
  rw [laguerreMomentMatrix, (laguerre_double_moment ha i.val j.val).2]
  simp only [StripPfaffian.schurEntry, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hn : ((a:ℂ)+j.val) - ((a:ℂ)+i.val) = (j.val:ℂ)-i.val := by ring
  have hd : ((a:ℂ)+i.val) + ((a:ℂ)+j.val) = 2*(a:ℂ)+i.val+j.val := by ring
  rw [hn,hd]
  ring

lemma laguerreMomentColumn_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    laguerreMomentColumn n a = fun i => (Real.Gamma (a+i.val) : ℂ) := by
  ext i
  exact congrArg Complex.ofReal (integral_laguerreWeight (by positivity))

lemma laguerre_schur_denominators {a : ℝ} (ha : 0 < a) (n : ℕ) (i j : Fin n) :
    ((a+i.val : ℝ) : ℂ) + ((a+j.val : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
  positivity

lemma laguerre_schur_injective (a : ℝ) (n : ℕ) :
    Function.Injective (fun i : Fin n => ((a+i.val : ℝ) : ℂ)) := by
  intro i j hij
  have h := Complex.ofReal_injective hij
  have he : (i.val:ℝ) = j.val := add_left_cancel h
  exact Fin.ext (Nat.cast_injective he)

lemma laguerreNormalizerProduct_eq (n : ℕ) (a : ℝ) :
    (laguerreNormalizerProduct n a : ℂ) =
      (∏ i : Fin n, (Real.Gamma (a+i.val) : ℂ)) *
        StripPfaffian.schurProduct (fun i : Fin n => ((a+i.val : ℝ) : ℂ)) := by
  simp only [laguerreNormalizerProduct, Complex.ofReal_mul, Complex.ofReal_prod,
    StripPfaffian.schurProduct]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  simp only [StripPfaffian.schurEntry, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  congr 1 <;> ring

 

theorem laguerreMomentMatrix_pfaffian_even {a : ℝ} (ha : 0 < a) (n : ℕ) (hn : Even n) :
    StripPfaffian.pfaffian n (laguerreMomentMatrix n a) = laguerreNormalizerProduct n a := by
  rw [laguerreMomentMatrix_eq ha, laguerreNormalizerProduct_eq]
  exact pfaffian_weighted_schur_even n hn _ _ (laguerre_schur_denominators ha n)
    (laguerre_schur_injective a n)

theorem laguerreMomentMatrix_pfaffian_odd {a : ℝ} (ha : 0 < a) (n : ℕ) (hn : Odd n) :
    StripPfaffian.pfaffian (n+1) (StripPfaffian.border (laguerreMomentMatrix n a)
      (laguerreMomentColumn n a)) = laguerreNormalizerProduct n a := by
  rw [laguerreMomentMatrix_eq ha, laguerreMomentColumn_eq ha, laguerreNormalizerProduct_eq]
  exact pfaffian_weighted_schur_odd n hn _ _ (laguerre_schur_denominators ha n)
    (laguerre_schur_injective a n)

end
end CriticalStrip

 

namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma sum_pow_list {ι E : Type*} [Fintype ι] [Semiring E] (f : ι → E) (m : ℕ) :
    (∑ i, f i) ^ m = ∑ v : Fin m → ι, (List.ofFn (fun j => f (v j))).prod := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih, Finset.mul_sum]
    conv_lhs => simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← Fintype.sum_prod_type (f := fun p : ι × (Fin m → ι) =>
      f p.1 * (List.ofFn (fun j => f (p.2 j))).prod)]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => ι))
    intro p
    simp [List.ofFn_succ, Fin.consEquiv]

lemma ofFn_smul_prod {n m : ℕ} (s : Fin m → ℂ) (v : Fin m → Grassmann n) :
    (List.ofFn (fun i => s i • v i)).prod =
      (∏ i, s i) • (List.ofFn v).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [ih, smul_mul_smul_comm]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma pair_wedge_product {n m : ℕ} (v : Fin (m*2) → Vec n) :
    (List.ofFn (fun i : Fin m => ExteriorAlgebra.ι ℂ (v (pairLeft i)) *
      ExteriorAlgebra.ι ℂ (v (pairRight i)))).prod = ExteriorAlgebra.ιMulti ℂ (m*2) v := by
  rw [ExteriorAlgebra.ιMulti_apply, List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 2
  funext i
  simp [List.ofFn_succ, pairLeft, pairRight, finProdFinEquiv, mul_comm, add_comm]

lemma twoForm_pow_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (m : ℕ) :
    twoForm A ^ m = (1/2:ℂ)^m • ∑ v : Fin (m*2) → Fin n,
      (∏ k : Fin m, A (v (pairLeft k)) (v (pairRight k))) •
        ExteriorAlgebra.ιMulti ℂ (m*2) (standardBasis n ∘ v) := by
  rw [twoForm_full A hA, smul_pow]
  congr 1
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n =>
    A p.1 p.2 • (generator n p.1 * generator n p.2)), sum_pow_list]
  simp_rw [ofFn_smul_prod]
  apply Fintype.sum_equiv (pairArrayEquiv (Fin n) m).symm
  intro p
  have hp : pairArrayEquiv (Fin n) m ((pairArrayEquiv (Fin n) m).symm p) = p :=
    Equiv.apply_symm_apply _ p
  conv_lhs => rw [← hp]
  simp only [pairArrayEquiv_apply, generator]
  congr 1
  exact pair_wedge_product (standardBasis n ∘ (pairArrayEquiv (Fin n) m).symm p)

lemma sum_basis_determinant (n : ℕ) (w : (Fin n → Fin n) → ℂ) :
    (∑ v : Fin n → Fin n, w v * (standardBasis n).det (standardBasis n ∘ v)) =
      ∑ σ : Equiv.Perm (Fin n), w σ * (Equiv.Perm.sign σ : ℂ) := by
  classical
  have hz : (∑ v : {f : Fin n → Fin n // ¬Function.Injective f},
      w v.val * (standardBasis n).det (standardBasis n ∘ v.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hd : (standardBasis n).det (standardBasis n ∘ v.val) = 0 := by
      apply AlternatingMap.map_eq_zero_of_not_injective
      intro hi
      exact v.property (fun a b hab => hi (by simp only [Function.comp_apply, hab]))
    rw [hd, mul_zero]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun v : Fin n → Fin n => Function.Injective v),
    hz, add_zero]
  apply Fintype.sum_equiv (permInjectiveEquiv n).symm
  intro v
  let σ := (permInjectiveEquiv n).symm v
  change w σ * (standardBasis n).det (standardBasis n ∘ σ) = w σ * _
  rw [AlternatingMap.map_perm, Module.Basis.det_self]
  simp [σ, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]



theorem pfaffian_permutation_expansion (m : ℕ)
    (A : Matrix (Fin (m*2)) (Fin (m*2)) ℂ) (hA : ∀ i j, A j i = -A i j) :
    pfaffian (m*2) A = ((1/2:ℂ)^m / m.factorial) *
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        pairEntries (fun i j => A (σ i) (σ j)) := by
  change topCoord (m*2) (twoForm A ^ ((m*2)/2)) / _ = _
  rw [Nat.mul_div_cancel m (by norm_num : 0 < 2), twoForm_pow_expansion A hA,
    map_smul, map_sum]
  simp only [map_smul, topCoord_wedge, smul_eq_mul]
  rw [sum_basis_determinant]
  unfold pairEntries
  simp only [mul_comm (∏ i : Fin m, _) (Equiv.Perm.sign _ : ℂ)]
  ring

end

 

noncomputable section
open scoped BigOperators
open MeasureTheory Set

lemma pairArray_preimage_pi {α : Type*} {m : ℕ} (s : Fin (m*2) → Set α) :
    (pairArrayEquiv α m).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i : Fin m => s (pairLeft i) ×ˢ s (pairRight i)) := by
  ext p
  simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_prod]
  constructor
  · intro hp i
    exact ⟨by simpa using hp (pairLeft i), by simpa using hp (pairRight i)⟩
  · intro hp j
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases j
    · change (pairArrayEquiv α m).symm p (pairLeft i) ∈ s (pairLeft i)
      simpa using (hp i).1
    · change (pairArrayEquiv α m).symm p (pairRight i) ∈ s (pairRight i)
      simpa using (hp i).2

lemma measurePreserving_pairArray {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) :
    MeasurePreserving (pairArrayMeasurableEquiv α m)
      (Measure.pi (fun _ : Fin (m*2) => μ))
        (Measure.pi (fun _ : Fin m => μ.prod μ)) := by
  suffices hs : MeasurePreserving (pairArrayMeasurableEquiv α m).symm
      (Measure.pi (fun _ : Fin m => μ.prod μ))
        (Measure.pi (fun _ : Fin (m*2) => μ)) from hs.symm
  refine ⟨(pairArrayMeasurableEquiv α m).symm.measurable, ?_⟩
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [MeasurableEquiv.map_apply]
  change (Measure.pi (fun _ : Fin m => μ.prod μ))
    ((pairArrayEquiv α m).symm ⁻¹' univ.pi s) = _
  rw [pairArray_preimage_pi, Measure.pi_pi]
  simp only [Measure.prod_prod]
  have h := finProdFinEquiv.prod_comp (fun i : Fin (m*2) => μ (s i))
  simpa only [Fintype.prod_prod_type, Fin.prod_univ_two, pairLeft, pairRight] using h

lemma integral_pair_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (f : Fin m → α × α → ℂ) :
    (∫ x : Fin (m*2) → α, ∏ i : Fin m, f i (x (pairLeft i), x (pairRight i))
      ∂Measure.pi (fun _ => μ)) = ∏ i, ∫ rs, f i rs ∂μ.prod μ := by
  rw [← integral_fintype_prod_eq_prod f (μ := fun _ : Fin m => μ.prod μ)]
  exact (measurePreserving_pairArray μ m).integral_comp' (fun p => ∏ i, f i (p i))

lemma integrable_pair_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) {f : Fin m → α × α → ℂ}
    (hf : ∀ i, Integrable (f i) (μ.prod μ)) :
    Integrable (fun x : Fin (m*2) → α => ∏ i : Fin m,
      f i (x (pairLeft i), x (pairRight i))) (Measure.pi (fun _ => μ)) := by
  exact (measurePreserving_pairArray μ m).integrable_comp_of_integrable
    (Integrable.fintype_prod hf)

lemma prod_pairs {M : Type*} [CommMonoid M] {m : ℕ} (f : Fin (m*2) → M) :
    (∏ i : Fin m, f (pairLeft i) * f (pairRight i)) = ∏ i, f i := by
  simpa only [Fintype.prod_prod_type, Fin.prod_univ_two, pairLeft, pairRight] using
    finProdFinEquiv.prod_comp f

lemma piCongrLeft_const_apply {α : Type*} [MeasurableSpace α] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) σ) x = x ∘ σ.symm := by
  ext i
  obtain ⟨j, rfl⟩ := σ.surjective i
  simp [MeasurableEquiv.coe_piCongrLeft]

lemma integral_alternating_times_perm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {n : ℕ} (F G : (Fin n → α) → ℂ)
    (hF : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x)
    (σ : Equiv.Perm (Fin n)) :
    (∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ)) =
      (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ).integral_comp'
    (fun x => F x * G (x ∘ σ))
  simp only [piCongrLeft_const_apply] at h
  change (∫ x, F (x ∘ σ.symm) * G ((x ∘ σ.symm) ∘ σ) ∂Measure.pi (fun _ => μ)) = _ at h
  have hc (x : Fin n → α) : (x ∘ σ.symm) ∘ σ = x := by ext i; simp
  simp only [hc, hF, Equiv.Perm.sign_symm, mul_assoc, integral_const_mul] at h
  exact h.symm

lemma integrable_alternating_times_perm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {n : ℕ} (F G : (Fin n → α) → ℂ)
    (hF : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x)
    (hi : Integrable (fun x => F x * G x) (Measure.pi (fun _ => μ)))
    (σ : Equiv.Perm (Fin n)) :
    Integrable (fun x => F x * G (x ∘ σ)) (Measure.pi (fun _ => μ)) := by
  apply ((measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ).integrable_comp_emb
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) σ).measurableEmbedding).mp
  have hc (x : Fin n → α) : (x ∘ σ.symm) ∘ σ = x := by ext i; simp
  simp only [Function.comp_def, piCongrLeft_const_apply]
  change Integrable (fun x => F (x ∘ σ.symm) * G ((x ∘ σ.symm) ∘ σ)) _
  simp only [hc, hF, mul_assoc]
  exact hi.const_mul _

lemma doubleMomentMatrix_skew {α : Type*} [MeasurableSpace α] {n : ℕ} (μ : Measure α)
    [SigmaFinite μ] (φ : Fin n → α → ℂ) (k : α → α → ℂ)
    (hk : ∀ r s, k s r = -k r s) (i j : Fin n) :
    doubleMomentMatrix μ φ k j i = -doubleMomentMatrix μ φ k i j := by
  unfold doubleMomentMatrix
  rw [← integral_prod_swap (doubleIntegrand φ k j i), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with rs
  simp only [doubleIntegrand, Prod.fst_swap, Prod.snd_swap]
  rw [hk rs.1 rs.2]
  ring

lemma evaluationMatrix_det_perm {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det = (Equiv.Perm.sign σ : ℂ) * (evaluationMatrix φ x).det := by
  exact Matrix.det_permute' σ (evaluationMatrix φ x)

lemma product_doubleIntegrand {α : Type*} {m : ℕ} (φ : Fin (m*2) → α → ℂ)
    (k : α → α → ℂ) (σ : Equiv.Perm (Fin (m*2))) (x : Fin (m*2) → α) :
    (∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i)) (σ (pairRight i))
      (x (pairLeft i), x (pairRight i))) =
      (∏ i : Fin (m*2), φ (σ i) (x i)) * pairEntries (fun i j => k (x i) (x j)) := by
  unfold doubleIntegrand pairEntries
  rw [← prod_pairs (fun i => φ (σ i) (x i))]
  simp only [Finset.prod_mul_distrib]
  ring

lemma determinant_times_pairs {α : Type*} {m : ℕ} (φ : Fin (m*2) → α → ℂ)
    (k : α → α → ℂ) (x : Fin (m*2) → α) :
    (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j)) =
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i)) (σ (pairRight i))
          (x (pairLeft i), x (pairRight i)) := by
  rw [Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [product_doubleIntegrand]
  simp only [evaluationMatrix, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  ring

lemma integrable_determinant_times_pairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    Integrable (fun x => (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j)))
      (Measure.pi (fun _ => μ)) := by
  simp only [determinant_times_pairs]
  exact integrable_finsetSum _ (fun σ _ => (integrable_pair_product μ m (fun i => hi _ _)).const_mul _)

lemma integral_determinant_times_pairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    (∫ x, (evaluationMatrix φ x).det * pairEntries (fun i j => k (x i) (x j))
      ∂Measure.pi (fun _ => μ)) =
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        pairEntries (fun i j => doubleMomentMatrix μ φ k (σ i) (σ j)) := by
  simp only [determinant_times_pairs]
  rw [integral_finsetSum _ (fun σ _ => (integrable_pair_product μ m (fun i => hi _ _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [integral_const_mul, integral_pair_product]
  rfl

 

theorem deBruijn_even {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (φ : Fin (m*2) → α → ℂ) (k : α → α → ℂ)
    (hk : ∀ r s, k s r = -k r s)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ)) :
    (∫ x, (evaluationMatrix φ x).det * pfaffian (m*2) (fun i j => k (x i) (x j))
      ∂Measure.pi (fun _ => μ)) =
        (Nat.factorial (m*2) : ℂ) * pfaffian (m*2) (doubleMomentMatrix μ φ k) := by
  let F : (Fin (m*2) → α) → ℂ := fun x => (evaluationMatrix φ x).det
  let G : (Fin (m*2) → α) → ℂ := fun x => pairEntries (fun i j => k (x i) (x j))
  have hF (σ : Equiv.Perm (Fin (m*2))) (x : Fin (m*2) → α) :
      F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x := evaluationMatrix_det_perm φ σ x
  have hI := integrable_determinant_times_pairs μ φ k hi
  have hII (σ : Equiv.Perm (Fin (m*2))) :
      Integrable (fun x => F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)))
        (Measure.pi (fun _ => μ)) := by
    have h := (integrable_alternating_times_perm μ F G hF hI σ).const_mul (Equiv.Perm.sign σ : ℂ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    ring
  have hpoint (x : Fin (m*2) → α) :
      F x * pfaffian (m*2) (fun i j => k (x i) (x j)) =
        ((1/2:ℂ)^m / m.factorial) *
          ∑ σ : Equiv.Perm (Fin (m*2)), F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) := by
    rw [pfaffian_permutation_expansion m _ (fun i j => hk _ _)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [F, G, Function.comp_def]
    ring
  change (∫ x, F x * pfaffian (m*2) _ ∂Measure.pi (fun _ => μ)) = _
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hII σ)]
  have he (σ : Equiv.Perm (Fin (m*2))) :
      (∫ x, F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) ∂Measure.pi (fun _ => μ)) =
        ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
    calc
      _ = (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ) := by
        rw [← integral_const_mul]
        congr 1
        ext x
        ring
      _ = _ := by
        rw [integral_alternating_times_perm μ F G hF, ← mul_assoc]
        have hs : (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
          have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
            congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
          exact_mod_cast hs
        rw [hs, one_mul]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    pfaffian_permutation_expansion m _ (doubleMomentMatrix_skew μ φ k hk),
    ← integral_determinant_times_pairs μ φ k hi]
  dsimp [F,G]
  ring


 


lemma borderLinear_eq_topCoord {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) :
    borderLinear A u = topCoord n (twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u) / (n/2).factorial := by
  have hn' : 2*(n/2)+1 = n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hhom : twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u ∈
      ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hn'] using SetLike.mul_mem_graded (twoForm_pow_mem A (n/2))
      (show ExteriorAlgebra.ι ℂ u ∈ ExteriorAlgebra.exteriorPower ℂ 1 (Vec n) from by
        simpa only [ExteriorAlgebra.exteriorPower, pow_one] using
          (LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) u))
  change topCoord (n+1) (ExteriorAlgebra.map (embedMap n) (twoForm A) ^ (n/2) *
    (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n+1) (Fin.last n))) / _ = _
  rw [← mul_assoc, ← ExteriorAlgebra.map_apply_ι, ← map_pow, ← map_mul,
    topCoord_embed_mul_last _ hhom]

lemma wedge_snoc {n l : ℕ} (v : Fin l → Vec n) (u : Vec n) :
    ExteriorAlgebra.ιMulti ℂ l v * ExteriorAlgebra.ι ℂ u =
      ExteriorAlgebra.ιMulti ℂ (l+1) (Fin.snoc v u) := by
  simp only [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ', List.prod_concat,
    Fin.snoc_castSucc, Fin.snoc_last]

lemma twoForm_pow_mul_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (m : ℕ) :
    twoForm A ^ m * ExteriorAlgebra.ι ℂ u =
      (1/2:ℂ)^m • ∑ v : Fin (m*2+1) → Fin n,
      ((∏ k : Fin m, A (v (pairLeft k).castSucc) (v (pairRight k).castSucc)) *
         u (v (Fin.last (m*2)))) •
        ExteriorAlgebra.ιMulti ℂ (m*2+1) (standardBasis n ∘ v) := by
  rw [twoForm_pow_expansion A hA m, ← generator_expansion n u, smul_mul_assoc,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_smul_comm, generator, wedge_snoc]
  congr 1
  rw [← Fintype.sum_prod_type (f := fun p : (Fin (m*2) → Fin n) × Fin n =>
    ((∏ k : Fin m, A (p.1 (pairLeft k)) (p.1 (pairRight k)))*u p.2) •
      ExteriorAlgebra.ιMulti ℂ (m*2+1) (Fin.snoc (standardBasis n ∘ p.1) (standardBasis n p.2)))]
  apply Fintype.sum_equiv ((Equiv.prodComm _ _).trans
    (Fin.snocEquiv (fun _ : Fin (m*2+1) => Fin n)))
  intro p
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def]

 
theorem pfaffian_border_permutation_expansion (m : ℕ)
    (A : Matrix (Fin (m*2+1)) (Fin (m*2+1)) ℂ) (hA : ∀ i j, A j i = -A i j)
    (u : Fin (m*2+1) → ℂ) :
    pfaffian (m*2+2) (border A u) = ((1/2:ℂ)^m / m.factorial) *
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        oddPairEntries (fun i j => A (σ i) (σ j)) (u ∘ σ) := by
  have hn : Odd (m*2+1) := ⟨m, by omega⟩
  rw [pfaffian_border hn A hA u, borderLinear_eq_topCoord hn,
    show (m*2+1)/2=m by omega, twoForm_pow_mul_expansion A hA u m,
    map_smul, map_sum]
  simp only [map_smul, topCoord_wedge, smul_eq_mul]
  rw [sum_basis_determinant]
  unfold oddPairEntries
  simp only [Function.comp_apply, mul_comm ((∏ i : Fin m, _) * _) (Equiv.Perm.sign _ : ℂ)]
  ring

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open MeasureTheory Set
lemma integral_pair_single_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (f : Fin m → α × α → ℂ) (g : α → ℂ) :
    (∫ x : Fin (m*2+1) → α, (∏ i : Fin m,
      f i (x (pairLeft i).castSucc, x (pairRight i).castSucc)) * g (x (Fin.last (m*2)))
      ∂Measure.pi (fun _ => μ)) = (∏ i, ∫ rs, f i rs ∂μ.prod μ) * ∫ t, g t ∂μ := by
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m*2+1) => μ)
    (Fin.last (m*2))).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_last, Fin.snoc_castSucc, Fin.snoc_last, cast_eq]
  simp_rw [mul_comm _ (g _)]
  rw [integral_prod_mul (μ := μ) (ν := Measure.pi (fun _ : Fin (m*2) => μ)) g
    (fun x : Fin (m*2) → α => ∏ i, f i (x (pairLeft i), x (pairRight i))),
    integral_pair_product, mul_comm]

lemma integrable_pair_single_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) {f : Fin m → α × α → ℂ} {g : α → ℂ}
    (hf : ∀ i, Integrable (f i) (μ.prod μ)) (hg : Integrable g μ) :
    Integrable (fun x : Fin (m*2+1) → α => (∏ i : Fin m,
      f i (x (pairLeft i).castSucc, x (pairRight i).castSucc)) * g (x (Fin.last (m*2))))
      (Measure.pi (fun _ => μ)) := by
  apply (((measurePreserving_piFinSuccAbove (fun _ : Fin (m*2+1) => μ)
    (Fin.last (m*2))).symm).integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m*2+1) => α)
        (Fin.last (m*2))).symm.measurableEmbedding).mp
  simp only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last,
    Fin.snoc_castSucc, Fin.snoc_last, cast_eq]
  simp_rw [mul_comm _ (g _)]
  exact hg.mul_prod (integrable_pair_product μ m hf)

lemma product_double_singleIntegrand {α : Type*} {m : ℕ} (φ : Fin (m*2+1) → α → ℂ)
    (k : α → α → ℂ) (g : α → ℂ) (σ : Equiv.Perm (Fin (m*2+1))) (x : Fin (m*2+1) → α) :
    (∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc)
      (x (pairLeft i).castSucc, x (pairRight i).castSucc)) *
        (φ (σ (Fin.last (m*2))) (x (Fin.last (m*2))) * g (x (Fin.last (m*2)))) =
      (∏ i : Fin (m*2+1), φ (σ i) (x i)) *
        oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x) := by
  unfold doubleIntegrand oddPairEntries
  rw [Fin.prod_univ_castSucc, ← prod_pairs (fun i => φ (σ i.castSucc) (x i.castSucc))]
  simp only [Finset.prod_mul_distrib, Function.comp_apply]
  ring

lemma determinant_times_oddPairs {α : Type*} {m : ℕ} (φ : Fin (m*2+1) → α → ℂ)
    (k : α → α → ℂ) (g : α → ℂ) (x : Fin (m*2+1) → α) :
    (evaluationMatrix φ x).det * oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x) =
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        ((∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc)
          (x (pairLeft i).castSucc, x (pairRight i).castSucc)) *
        (φ (σ (Fin.last (m*2))) (x (Fin.last (m*2))) * g (x (Fin.last (m*2))))) := by
  rw [Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [product_double_singleIntegrand]
  simp only [evaluationMatrix, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  ring

lemma integrable_determinant_times_oddPairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    Integrable (fun x => (evaluationMatrix φ x).det *
      oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)) (Measure.pi (fun _ => μ)) := by
  simp only [determinant_times_oddPairs]
  exact integrable_finsetSum _ (fun σ _ =>
    (integrable_pair_single_product μ m (fun i => hi _ _) (hs _)).const_mul _)

lemma integral_determinant_times_oddPairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    (∫ x, (evaluationMatrix φ x).det * oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)
      ∂Measure.pi (fun _ => μ)) =
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        oddPairEntries (fun i j => doubleMomentMatrix μ φ k (σ i) (σ j))
          (singleMoment μ φ g ∘ σ) := by
  simp only [determinant_times_oddPairs]
  rw [integral_finsetSum _ (fun σ _ =>
    (integrable_pair_single_product μ m (fun i => hi _ _) (hs _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [integral_const_mul]
  congr 1
  exact integral_pair_single_product μ m
    (fun i => doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc))
    (fun t => φ (σ (Fin.last (m*2))) t * g t)

 

theorem deBruijn_odd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hk : ∀ r s, k s r = -k r s)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    (∫ x, (evaluationMatrix φ x).det *
      pfaffian (m*2+2) (border (fun i j => k (x i) (x j)) (g ∘ x))
      ∂Measure.pi (fun _ => μ)) =
        (Nat.factorial (m*2+1) : ℂ) * pfaffian (m*2+2)
          (border (doubleMomentMatrix μ φ k) (singleMoment μ φ g)) := by
  let F : (Fin (m*2+1) → α) → ℂ := fun x => (evaluationMatrix φ x).det
  let G : (Fin (m*2+1) → α) → ℂ := fun x => oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)
  have hF (σ : Equiv.Perm (Fin (m*2+1))) (x : Fin (m*2+1) → α) :
      F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x := evaluationMatrix_det_perm φ σ x
  have hI := integrable_determinant_times_oddPairs μ φ k g hi hs
  have hII (σ : Equiv.Perm (Fin (m*2+1))) :
      Integrable (fun x => F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)))
        (Measure.pi (fun _ => μ)) := by
    have h := (integrable_alternating_times_perm μ F G hF hI σ).const_mul (Equiv.Perm.sign σ : ℂ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    ring
  have hpoint (x : Fin (m*2+1) → α) :
      F x * pfaffian (m*2+2) (border (fun i j => k (x i) (x j)) (g ∘ x)) =
        ((1/2:ℂ)^m / m.factorial) *
          ∑ σ : Equiv.Perm (Fin (m*2+1)), F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) := by
    rw [pfaffian_border_permutation_expansion m _ (fun i j => hk _ _)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [F, G, Function.comp_def]
    ring
  change (∫ x, F x * pfaffian (m*2+2) _ ∂Measure.pi (fun _ => μ)) = _
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hII σ)]
  have he (σ : Equiv.Perm (Fin (m*2+1))) :
      (∫ x, F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) ∂Measure.pi (fun _ => μ)) =
        ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
    calc
      _ = (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ) := by
        rw [← integral_const_mul]
        congr 1
        ext x
        ring
      _ = _ := by
        rw [integral_alternating_times_perm μ F G hF, ← mul_assoc]
        have hs : (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
          have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
            congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
          exact_mod_cast hs
        rw [hs, one_mul]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    pfaffian_border_permutation_expansion m _ (doubleMomentMatrix_skew μ φ k hk),
    ← integral_determinant_times_oddPairs μ φ k g hi hs]
  dsimp [F,G]
  ring

end
end StripPfaffian

 

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

lemma laguerreDomain_subset_positive (n : ℕ) :
    laguerreDomain n ⊆ univ.pi (fun _ : Fin n => Ioi (0 : ℝ)) :=
  fun _ hr i _ => hr.2 i

lemma positive_product_restrict_chamber (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ₊)).restrict (laguerreDomain n) =
      volume.restrict (laguerreDomain n) := by
  rw [← Measure.restrict_pi_pi, ← volume_pi,
    Measure.restrict_restrict (isOpen_laguerreDomain n).measurableSet,
    inter_eq_left.mpr (laguerreDomain_subset_positive n)]

lemma ae_positive_product (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ => μ₊), ∀ i, 0 < x i := by
  rw [← Measure.restrict_pi_pi, ← volume_pi]
  exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)).mono
    fun _ hx i => hx i (mem_univ i)

lemma sum_ordered_indicator {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬Function.Injective x → F x = 0)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    (∑ σ : Equiv.Perm (Fin n), (laguerreDomain n).indicator F (x ∘ σ)) = F x := by
  classical
  by_cases hi : Function.Injective x
  · have hs : x ∘ Tuple.sort x ∈ laguerreDomain n :=
      ⟨(Tuple.monotone_sort x).strictMono_of_injective (hi.comp (Tuple.sort x).injective),
        fun i => hx _⟩
    rw [Finset.sum_eq_single (Tuple.sort x)]
    · rw [indicator_of_mem hs, hperm]
    · intro σ hσ hne
      apply indicator_of_notMem
      intro hσs
      apply hne
      apply Equiv.ext
      intro i
      exact hi (congrFun (Tuple.unique_monotone hσs.1.monotone (Tuple.monotone_sort x)) i)
    · simp
  · rw [hzero x hi]
    apply Finset.sum_eq_zero
    intro σ hσ
    by_cases hm : x ∘ σ ∈ laguerreDomain n
    · rw [indicator_of_mem hm, hperm, hzero x hi]
    · exact indicator_of_notMem hm _

 

lemma integral_symmetric_ordered {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬Function.Injective x → F x = 0)
    (hint : IntegrableOn F (laguerreDomain n)) :
    (∫ x, F x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * ∫ x in laguerreDomain n, F x := by
  classical
  let G := (laguerreDomain n).indicator F
  have hi : Integrable G (Measure.pi (fun _ : Fin n => μ₊)) := by
    rw [integrable_indicator_iff (isOpen_laguerreDomain n).measurableSet]
    simpa only [IntegrableOn, positive_product_restrict_chamber] using hint
  have his (σ : Equiv.Perm (Fin n)) :
      Integrable (fun x => G (x ∘ σ)) (Measure.pi (fun _ : Fin n => μ₊)) := by
    simpa only [Function.comp_def, piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin n => μ₊) σ.symm).integrable_comp_of_integrable hi
  have heq (σ : Equiv.Perm (Fin n)) :
      (∫ x, G (x ∘ σ) ∂Measure.pi (fun _ : Fin n => μ₊)) =
        ∫ x in laguerreDomain n, F x := by
    have he := (measurePreserving_piCongrLeft (fun _ : Fin n => μ₊) σ.symm).integral_comp' G
    simp only [piCongrLeft_const_apply, Equiv.symm_symm] at he
    rw [he, integral_indicator (isOpen_laguerreDomain n).measurableSet,
      positive_product_restrict_chamber]
  calc
    _ = ∫ x, ∑ σ : Equiv.Perm (Fin n), G (x ∘ σ) ∂Measure.pi (fun _ => μ₊) := by
      apply integral_congr_ae
      exact (ae_positive_product n).mono fun x hx => (sum_ordered_indicator F hperm hzero x hx).symm
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ x, G (x ∘ σ) ∂Measure.pi (fun _ => μ₊) :=
      integral_finsetSum _ (fun σ _ => his σ)
    _ = _ := by simp only [heq, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end
end CriticalStrip

namespace StripPfaffian
noncomputable section
open scoped BigOperators
open MeasureTheory Set

lemma permMap_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Vec n) :
    permMap n σ u = u ∘ σ.symm := by
  have hu : ∑ i : Fin n, u i • standardBasis n i = u := by
    simpa only [standardBasis, Pi.basisFun_repr] using (standardBasis n).sum_repr u
  calc
    _ = ∑ i : Fin n, u i • standardBasis n (σ i) := by
      conv_lhs => rw [← hu]
      simp only [map_sum, map_smul, permMap_basis]
    _ = ∑ i : Fin n, u (σ.symm i) • standardBasis n i := by
      apply Fintype.sum_equiv σ
      intro i
      simp
    _ = _ := by simpa only [standardBasis, Pi.basisFun_repr, Function.comp_apply] using
      (standardBasis n).sum_repr (u ∘ σ.symm)

lemma pfaffian_border_perm {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (u : Vec n)
    (σ : Equiv.Perm (Fin n)) :
    pfaffian (n+1) (border (fun i j => A (σ.symm i) (σ.symm j)) (u ∘ σ.symm)) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian (n+1) (border A u) := by
  have hn' : 2*(n/2)+1 = n := by obtain ⟨k, hk⟩ := hn; omega
  have hhom : twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u ∈
      ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hn'] using SetLike.mul_mem_graded (twoForm_pow_mem A (n/2))
      (show ExteriorAlgebra.ι ℂ u ∈ ExteriorAlgebra.exteriorPower ℂ 1 (Vec n) from by
        simpa only [ExteriorAlgebra.exteriorPower, pow_one] using
          (LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) u))
  erw [pfaffian_border hn _ (fun i j => hA _ _), pfaffian_border hn A hA,
    borderLinear_eq_topCoord hn, borderLinear_eq_topCoord hn,
    ← twoForm_perm A hA σ, ← permMap_apply σ u, ← ExteriorAlgebra.map_apply_ι,
    ← map_pow, ← map_mul, topCoord_map _ _ _ hhom, permMap_det]
  ring

lemma perm_sign_mul_self {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
  have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
    congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
  exact_mod_cast hs

lemma determinantPfaffian_symmetric_even {α : Type*} {n : ℕ} (hn : Even n)
    (φ : Fin n → α → ℂ) (k : α → α → ℂ) (hk : ∀ r s, k s r = -k r s)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det * pfaffian n (fun i j => k (x (σ i)) (x (σ j))) =
      (evaluationMatrix φ x).det * pfaffian n (fun i j => k (x i) (x j)) := by
  rw [evaluationMatrix_det_perm]
  have hp := pfaffian_perm n hn (fun i j => k (x i) (x j)) (fun i j => hk _ _) σ.symm
  simp only [Equiv.symm_symm, Equiv.Perm.sign_symm] at hp
  erw [hp]
  calc
    _ = ((Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ)) *
      ((evaluationMatrix φ x).det * pfaffian n (fun i j => k (x i) (x j))) := by ring
    _ = _ := by rw [perm_sign_mul_self, one_mul]

lemma determinantPfaffian_symmetric_odd {α : Type*} {n : ℕ} (hn : Odd n)
    (φ : Fin n → α → ℂ) (k : α → α → ℂ) (g : α → ℂ) (hk : ∀ r s, k s r = -k r s)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det * pfaffian (n+1)
      (border (fun i j => k (x (σ i)) (x (σ j))) (g ∘ x ∘ σ)) =
      (evaluationMatrix φ x).det * pfaffian (n+1)
        (border (fun i j => k (x i) (x j)) (g ∘ x)) := by
  rw [evaluationMatrix_det_perm]
  have hp := pfaffian_border_perm hn (fun i j => k (x i) (x j))
    (fun i j => hk _ _) (g ∘ x) σ.symm
  simp only [Equiv.symm_symm, Equiv.Perm.sign_symm] at hp
  erw [hp]
  calc
    _ = ((Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ)) *
      ((evaluationMatrix φ x).det * pfaffian (n+1)
        (border (fun i j => k (x i) (x j)) (g ∘ x))) := by ring
    _ = _ := by rw [perm_sign_mul_self, one_mul]

lemma evaluationMatrix_det_of_not_injective {α : Type*} {n : ℕ}
    (φ : Fin n → α → ℂ) {x : Fin n → α} (hx : ¬Function.Injective x) :
    (evaluationMatrix φ x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (φ r) hij)

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

lemma laguerreWeight_shift_nat (a : ℝ) (i : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerreWeight (a+i) x = laguerreWeight a x * x^i := by
  unfold laguerreWeight
  rw [show a+(i:ℝ)-1=(a-1)+(i:ℝ) by ring, Real.rpow_add hx, Real.rpow_natCast]
  ring

lemma laguerre_evaluation_determinant {n : ℕ} (a : ℝ) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) :
    (evaluationMatrix (laguerrePhi n a) x).det =
      (∏ i, (laguerreWeight a (x i) : ℂ)) *
        ∏ i, ∏ j ∈ Finset.Ioi i, ((x j : ℂ) - (x i : ℂ)) := by
  have he : evaluationMatrix (laguerrePhi n a) x =
      Matrix.of (fun i j => (laguerreWeight a (x j) : ℂ) *
        (Matrix.vandermonde (fun i => (x i : ℂ))).transpose i j) := by
    ext i j
    simp only [evaluationMatrix, laguerrePhi, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.vandermonde_apply, laguerreWeight_shift_nat a i.val (hx j),
      Complex.ofReal_mul, Complex.ofReal_pow]
  rw [he, Matrix.det_mul_row, Matrix.det_transpose, Matrix.det_vandermonde]

lemma vandermonde_schur_density (n : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    ((∏ i, (laguerreWeight a (x i) : ℂ)) *
      ∏ i, ∏ j ∈ Finset.Ioi i, ((x j : ℂ) - (x i : ℂ))) *
        schurProduct (fun i => (x i : ℂ)) = (laguerreDensity n a x : ℂ) := by
  simp only [laguerreDensity, Complex.ofReal_mul, Complex.ofReal_prod, mul_assoc, schurProduct]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [schurEntry, pairKernel, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_add]
  rw [add_comm (x j : ℂ) (x i : ℂ)]
  ring

lemma laguerreEvenIntegrand_eq {n : ℕ} (hn : Even n) (a : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) :
    laguerreEvenIntegrand n a x = laguerreDensity n a x := by
  have hd (i j : Fin n) : (x i : ℂ) + (x j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hx.2 i) (hx.2 j)).ne'
  have hi : Function.Injective (fun i => (x i : ℂ)) := Complex.ofReal_injective.comp hx.1.injective
  rw [laguerreEvenIntegrand, pfaffian_schur_even n hn _ hd hi,
    laguerre_evaluation_determinant a hx.2, vandermonde_schur_density]

lemma laguerreOddIntegrand_eq {n : ℕ} (hn : Odd n) (a : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) :
    laguerreOddIntegrand n a x = laguerreDensity n a x := by
  have hd (i j : Fin n) : (x i : ℂ) + (x j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hx.2 i) (hx.2 j)).ne'
  have hi : Function.Injective (fun i => (x i : ℂ)) := Complex.ofReal_injective.comp hx.1.injective
  rw [laguerreOddIntegrand, pfaffian_schur_odd n hn _ hd hi,
    laguerre_evaluation_determinant a hx.2, vandermonde_schur_density]

lemma integral_laguerreEvenIntegrand {n : ℕ} (hn : Even n) {a : ℝ} (ha : 0 < a) :
    (∫ x, laguerreEvenIntegrand n a x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * (laguerreNormalizer n a : ℂ) := by
  have he : ∀ᵐ x ∂volume.restrict (laguerreDomain n),
      laguerreEvenIntegrand n a x = (laguerreDensity n a x : ℂ) :=
    (ae_restrict_mem (isOpen_laguerreDomain n).measurableSet).mono
      fun x hx => laguerreEvenIntegrand_eq hn a hx
  rw [integral_symmetric_ordered _
    (fun σ x => determinantPfaffian_symmetric_even hn _
      (fun r s : ℝ => schurEntry r s) (fun r s => schurEntry_swap _ _) σ x)
    (fun x hx => by
      unfold laguerreEvenIntegrand
      rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul])
    (by
      have hi := (integrableOn_laguerreDensity n ha).ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (he.mono fun _ h => h.symm))]
  rw [integral_congr_ae he, integral_complex_ofReal]
  rfl

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaguerreNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian
local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))
lemma integral_laguerreOddIntegrand {n : ℕ} (hn : Odd n) {a : ℝ} (ha : 0 < a) :
    (∫ x, laguerreOddIntegrand n a x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * (laguerreNormalizer n a : ℂ) := by
  have he : ∀ᵐ x ∂volume.restrict (laguerreDomain n),
      laguerreOddIntegrand n a x = (laguerreDensity n a x : ℂ) :=
    (ae_restrict_mem (isOpen_laguerreDomain n).measurableSet).mono
      fun x hx => laguerreOddIntegrand_eq hn a hx
  rw [integral_symmetric_ordered _
    (fun σ x => determinantPfaffian_symmetric_odd hn _
      (fun r s : ℝ => schurEntry r s) (fun _ => 1) (fun r s => schurEntry_swap _ _) σ x)
    (fun x hx => by
      unfold laguerreOddIntegrand
      rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul])
    (by
      have hi := (integrableOn_laguerreDensity n ha).ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (he.mono fun _ h => h.symm))]
  rw [integral_congr_ae he, integral_complex_ofReal]
  rfl

lemma laguerre_doubleIntegrand_eq {n : ℕ} (a : ℝ) (i j : Fin n) (rs : ℝ × ℝ) :
    doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j rs =
      (gammaSkewIntegrand (a+i.val) (a+j.val) rs : ℂ) := by
  simp only [doubleIntegrand, laguerrePhi, gammaSkewIntegrand, schurEntry,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]
  rw [add_comm (rs.2 : ℂ) (rs.1 : ℂ)]
  ring

lemma integrable_laguerre_doubleIntegrand {n : ℕ} {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    Integrable (doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j)
      (μ₊.prod μ₊) := by
  have he : doubleIntegrand (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) i j =
      fun rs => (gammaSkewIntegrand (a+i.val) (a+j.val) rs : ℂ) :=
    funext (laguerre_doubleIntegrand_eq a i j)
  rw [he]
  simpa only [RCLike.ofReal_eq_complex_ofReal] using
    (laguerre_double_moment ha i.val j.val).1.ofReal (𝕜 := ℂ)

lemma laguerre_doubleMomentMatrix_eq {a : ℝ} (n : ℕ) :
    doubleMomentMatrix μ₊ (laguerrePhi n a) (fun r s : ℝ => schurEntry r s) =
      laguerreMomentMatrix n a := by
  ext i j
  simp only [doubleMomentMatrix, laguerre_doubleIntegrand_eq, integral_complex_ofReal,
    laguerreMomentMatrix]

lemma laguerre_singleMoment_eq (n : ℕ) (a : ℝ) :
    singleMoment μ₊ (laguerrePhi n a) (fun _ => 1) = laguerreMomentColumn n a := by
  ext i
  simp only [singleMoment, laguerrePhi, mul_one, integral_complex_ofReal, laguerreMomentColumn]

 

theorem laguerreNormalizer_eq_product (n : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreNormalizer n a = laguerreNormalizerProduct n a := by
  apply Complex.ofReal_injective
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2 := by omega
    clear hm
    subst n
    have he : Even (m*2) := ⟨m, by omega⟩
    have h := deBruijn_even μ₊ m (laguerrePhi (m*2) a)
      (fun r s : ℝ => schurEntry r s) (fun r s => schurEntry_swap _ _)
        (integrable_laguerre_doubleIntegrand ha)
    change (∫ x, laguerreEvenIntegrand (m*2) a x ∂Measure.pi (fun _ => μ₊)) = _ at h
    rw [integral_laguerreEvenIntegrand he ha, laguerre_doubleMomentMatrix_eq,
      laguerreMomentMatrix_pfaffian_even ha _ he] at h
    exact mul_left_cancel₀ (show ((m*2).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2)) h
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2+1 := by omega
    clear hm
    subst n
    have he : Odd (m*2+1) := ⟨m, by omega⟩
    have hs (i : Fin (m*2+1)) : Integrable (fun t => laguerrePhi (m*2+1) a i t * 1) μ₊ := by
      simpa only [IntegrableOn, laguerrePhi, mul_one, RCLike.ofReal_eq_complex_ofReal] using
        (integrableOn_laguerreWeight (show 0 < a+i.val by positivity)).ofReal (𝕜 := ℂ)
    have h := deBruijn_odd μ₊ m (laguerrePhi (m*2+1) a)
      (fun r s : ℝ => schurEntry r s) (fun _ => 1) (fun r s => schurEntry_swap _ _)
        (integrable_laguerre_doubleIntegrand ha) hs
    change (∫ x, laguerreOddIntegrand (m*2+1) a x ∂Measure.pi (fun _ => μ₊)) = _ at h
    rw [integral_laguerreOddIntegrand he ha, laguerre_doubleMomentMatrix_eq,
      laguerre_singleMoment_eq] at h
    rw [laguerreMomentMatrix_pfaffian_odd ha _ he] at h
    exact mul_left_cancel₀ (show ((m*2+1).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2+1)) h

end
end CriticalStrip

 

namespace Matrix
open scoped _root_.Matrix
noncomputable section
open scoped BigOperators

 
lemma sum_det_updateRow_mul {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (f : ι → R) :
    (∑ i, (A.updateRow i (fun j => A i j * f j)).det) = A.det * ∑ j, f j := by
  calc
    _ = ∑ i, ∑ j, A.adjugate j i * (A i j * f j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← _root_.Matrix.cramer_transpose_apply, _root_.Matrix.cramer_eq_adjugate_mulVec, ← _root_.Matrix.adjugate_transpose]
      rfl
    _ = ∑ j, (∑ i, A.adjugate j i * A i j) * f j := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ j, A.det * f j := by
      apply Finset.sum_congr rfl
      intro j _
      change (A.adjugate * A) j j * f j = _
      rw [_root_.Matrix.adjugate_mul]
      simp
    _ = _ := by rw [Finset.mul_sum]

end
end Matrix

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

lemma gammaSchurProduct_eq {n : ℕ} (q : Fin n → ℝ) :
    (gammaSchurProduct q : ℂ) =
      (∏ i, (Real.Gamma (q i) : ℂ)) * schurProduct (fun i => (q i : ℂ)) := by
  simp only [gammaSchurProduct, Complex.ofReal_mul, Complex.ofReal_prod, schurProduct,
    schurEntry, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]

lemma gammaPhi_doubleIntegrand_eq {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (rs : ℝ × ℝ) :
    doubleIntegrand (gammaPhi q) (fun r s : ℝ => schurEntry r s) i j rs =
      (gammaSkewIntegrand (q i) (q j) rs : ℂ) := by
  simp only [doubleIntegrand, gammaPhi, gammaSkewIntegrand, schurEntry,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add]
  rw [add_comm (rs.2 : ℂ) (rs.1 : ℂ)]
  ring

lemma gammaPhi_doubleMomentMatrix_eq {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 < q i) :
    doubleMomentMatrix μ₊ (gammaPhi q) (fun r s : ℝ => schurEntry r s) =
      fun i j => (Real.Gamma (q i) : ℂ) * schurEntry (q i) (q j) * (Real.Gamma (q j) : ℂ) := by
  ext i j
  unfold doubleMomentMatrix
  rw [funext (gammaPhi_doubleIntegrand_eq q i j), integral_complex_ofReal,
    integral_gammaSkewIntegrand (hq i) (hq j)]
  simp only [schurEntry, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_add]
  ring

lemma integrable_gammaPhi_doubleIntegrand {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 < q i)
    (i j : Fin n) :
    Integrable (doubleIntegrand (gammaPhi q) (fun r s : ℝ => schurEntry r s) i j)
      (μ₊.prod μ₊) := by
  simp only [funext (gammaPhi_doubleIntegrand_eq q i j)]
  simpa only [RCLike.ofReal_eq_complex_ofReal] using
    (integrable_gammaSkewIntegrand (hq i) (hq j)).ofReal (𝕜 := ℂ)

lemma gammaPhi_singleMoment_eq {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 < q i) :
    singleMoment μ₊ (gammaPhi q) (fun _ => 1) = fun i => (Real.Gamma (q i) : ℂ) := by
  ext i
  simp only [singleMoment, gammaPhi, mul_one, integral_complex_ofReal,
    integral_laguerreWeight (hq i)]

 

theorem integral_gamma_determinant_schur {n : ℕ} {q : Fin n → ℝ}
    (hq : ∀ i, 0 < q i) (hqi : Function.Injective q)
    (f : (Fin n → ℝ) → ℝ) (hint : IntegrableOn f (laguerreDomain n))
    (heq : ∀ x ∈ laguerreDomain n,
      (evaluationMatrix (gammaPhi q) x).det * schurProduct (fun i => (x i : ℂ)) = (f x : ℂ)) :
    (∫ x in laguerreDomain n, f x) = gammaSchurProduct q := by
  have hdq (i j : Fin n) : (q i : ℂ) + (q j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hq i) (hq j)).ne'
  have hqic : Function.Injective (fun i => (q i : ℂ)) := Complex.ofReal_injective.comp hqi
  have hdx {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) (i j : Fin n) :
      (x i : ℂ) + (x j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hx.2 i) (hx.2 j)).ne'
  have hxic {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) :
      Function.Injective (fun i => (x i : ℂ)) := Complex.ofReal_injective.comp hx.1.injective
  apply Complex.ofReal_injective
  rw [gammaSchurProduct_eq, ← integral_complex_ofReal]
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2 := by omega
    clear hm
    subst n
    have he : Even (m*2) := ⟨m, by omega⟩
    let F := fun x => (evaluationMatrix (gammaPhi q) x).det *
      pfaffian (m*2) (schurMatrix (fun i => (x i : ℂ)))
    have hF : ∀ᵐ x ∂volume.restrict (laguerreDomain (m*2)), F x = (f x : ℂ) := by
      filter_upwards [ae_restrict_mem (isOpen_laguerreDomain (m*2)).measurableSet] with x hx
      dsimp [F]
      rw [pfaffian_schur_even _ he _ (hdx hx) (hxic hx)]
      exact heq x hx
    have hFi : IntegrableOn F (laguerreDomain (m*2)) := by
      have hi := hint.ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (hF.mono fun _ h => h.symm)
    have hy := integral_symmetric_ordered F
      (fun σ x => determinantPfaffian_symmetric_even he _ _
        (fun r s : ℝ => schurEntry_swap (r:ℂ) s) σ x)
      (fun x hx => by dsimp [F]; rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul]) hFi
    have hb := deBruijn_even μ₊ m (gammaPhi q) (fun r s : ℝ => schurEntry r s)
      (fun r s => schurEntry_swap _ _) (integrable_gammaPhi_doubleIntegrand hq)
    change (∫ x, F x ∂Measure.pi (fun _ => μ₊)) = _ at hb
    rw [hy, integral_congr_ae hF, gammaPhi_doubleMomentMatrix_eq hq,
      pfaffian_weighted_schur_even _ he _ _ hdq hqic] at hb
    exact mul_left_cancel₀ (show ((m*2).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2)) hb
  · obtain ⟨m, hm⟩ := hn
    have hn : n = m*2+1 := by omega
    clear hm
    subst n
    have he : Odd (m*2+1) := ⟨m, by omega⟩
    let F := fun x => (evaluationMatrix (gammaPhi q) x).det *
      pfaffian (m*2+2) (border (schurMatrix (fun i => (x i : ℂ))) (fun _ => 1))
    have hF : ∀ᵐ x ∂volume.restrict (laguerreDomain (m*2+1)), F x = (f x : ℂ) := by
      filter_upwards [ae_restrict_mem (isOpen_laguerreDomain (m*2+1)).measurableSet] with x hx
      dsimp [F]
      rw [pfaffian_schur_odd _ he _ (hdx hx) (hxic hx)]
      exact heq x hx
    have hFi : IntegrableOn F (laguerreDomain (m*2+1)) := by
      have hi := hint.ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (hF.mono fun _ h => h.symm)
    have hy := integral_symmetric_ordered F
      (fun σ x => determinantPfaffian_symmetric_odd he _ _ (fun _ => 1)
        (fun r s : ℝ => schurEntry_swap (r:ℂ) s) σ x)
      (fun x hx => by dsimp [F]; rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul]) hFi
    have hs (i : Fin (m*2+1)) : Integrable (fun t => gammaPhi q i t * 1) μ₊ := by
      simpa only [IntegrableOn, gammaPhi, mul_one, RCLike.ofReal_eq_complex_ofReal] using
        (integrableOn_laguerreWeight (hq i)).ofReal (𝕜 := ℂ)
    have hb := deBruijn_odd μ₊ m (gammaPhi q) (fun r s : ℝ => schurEntry r s) (fun _ => 1)
      (fun r s => schurEntry_swap _ _) (integrable_gammaPhi_doubleIntegrand hq) hs
    change (∫ x, F x ∂Measure.pi (fun _ => μ₊)) = _ at hb
    rw [hy, integral_congr_ae hF, gammaPhi_doubleMomentMatrix_eq hq, gammaPhi_singleMoment_eq hq,
      pfaffian_weighted_schur_odd _ he _ _ hdq hqic] at hb
    exact mul_left_cancel₀ (show ((m*2+1).factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero (m*2+1)) hb

end

noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian


lemma inverseExponents_pos {n : ℕ} {a : ℝ} (ha : 1 < a) :
    ∀ i : Fin (n+1), 0 < inverseExponents n a i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [inverseExponents, Fin.cons_zero] using sub_pos.mpr ha
  · simp only [inverseExponents, Fin.cons_succ]
    positivity

lemma inverseExponents_strictMono (n : ℕ) (a : ℝ) : StrictMono (inverseExponents n a) := by
  rw [inverseExponents, Fin.strictMono_cons]
  constructor
  · intro i
    have hi : (0 : ℝ) ≤ i.val := by positivity
    linarith
  · intro i j hij
    have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
    linarith

lemma laguerreWeight_add_one (a : ℝ) {x : ℝ} (hx : 0 < x) :
    laguerreWeight (a+1) x = laguerreWeight a x * x := by
  simpa using laguerreWeight_shift_nat a 1 hx

lemma inverseExponents_determinant {n : ℕ} (a : ℝ) {x : Fin (n+1) → ℝ}
    (hx : ∀ i, 0 < x i) :
    (evaluationMatrix (gammaPhi (inverseExponents n a)) x).det =
      (evaluationMatrix (laguerrePhi (n+1) a) x).det * ∑ i, (x i : ℂ)⁻¹ := by
  classical
  let A := evaluationMatrix (laguerrePhi (n+1) a) x
  have he : evaluationMatrix (gammaPhi (inverseExponents n a)) x =
      A.updateRow 0 (fun j => A 0 j * (x j : ℂ)⁻¹) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Matrix.updateRow_self, evaluationMatrix, gammaPhi, inverseExponents,
        Fin.cons_zero, A, laguerrePhi, Fin.val_zero, Nat.cast_zero, add_zero]
      have h := laguerreWeight_add_one (a-1) (hx j)
      rw [sub_add_cancel] at h
      rw [h, Complex.ofReal_mul, mul_inv_cancel_right₀ (by exact_mod_cast (hx j).ne')]
    · simp only [Matrix.updateRow_ne (Fin.succ_ne_zero i), evaluationMatrix, gammaPhi,
        inverseExponents, Fin.cons_succ, A, laguerrePhi, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have hs (i : Fin n) : (A.updateRow i.succ (fun j => A i.succ j * (x j : ℂ)⁻¹)).det = 0 := by
    have hr : (fun j => A i.succ j * (x j : ℂ)⁻¹) = A i.castSucc := by
      ext j
      dsimp [A, evaluationMatrix, laguerrePhi]
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, laguerreWeight_add_one _ (hx j),
        Complex.ofReal_mul, mul_inv_cancel_right₀ (by exact_mod_cast (hx j).ne')]
    rw [hr]
    apply Matrix.det_updateRow_eq_zero
    exact fun h => by have hv := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_succ] at hv; omega
  rw [he]
  have h := Matrix.sum_det_updateRow_mul A (fun i => (x i : ℂ)⁻¹)
  simpa only [Fin.sum_univ_succ, hs, Finset.sum_const_zero, add_zero] using h

lemma integrableOn_laguerre_inverseSum {n : ℕ} {a : ℝ} (ha : 1 < a) :
    IntegrableOn (fun r : Fin n → ℝ => (∑ i, (r i)⁻¹) * laguerreDensity n a r)
      (laguerreDomain n) := by
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  simpa only [IntegrableOn, Real.rpow_neg_one] using integrableOn_laguerre_inverse_coordinate
    (by linarith : 0<a) i (p := 1) (by
      have h : (0 : ℝ) ≤ i.val := by positivity
      linarith)

lemma integral_laguerre_inverseSum_eq_gammaProduct {n : ℕ} {a : ℝ} (ha : 1 < a) :
    (∫ x in laguerreDomain (n+1), (∑ i, (x i)⁻¹) * laguerreDensity (n+1) a x) =
      gammaSchurProduct (inverseExponents n a) := by
  apply integral_gamma_determinant_schur (inverseExponents_pos ha)
    (inverseExponents_strictMono n a).injective _ (integrableOn_laguerre_inverseSum ha)
  intro x hx
  rw [inverseExponents_determinant a hx.2, laguerre_evaluation_determinant a hx.2]
  rw [mul_comm _ (∑ i, (x i : ℂ)⁻¹), mul_assoc, vandermonde_schur_density]
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_inv]



lemma orderedPairProduct_cons {α M : Type*} [CommMonoid M] (k : α → α → M)
    {n : ℕ} (x : α) (r : Fin n → α) :
    (∏ i : Fin (n+1), ∏ j ∈ Finset.Ioi i, k ((Fin.cons x r : Fin (n+1) → α) i) ((Fin.cons x r : Fin (n+1) → α) j)) =
      (∏ j, k x (r j)) * ∏ i, ∏ j ∈ Finset.Ioi i, k (r i) (r j) := by
  classical
  have he {m : ℕ} (s : Fin m → α) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, k (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then k (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    ↓reduceIte, Fin.succ_pos, Fin.not_lt_zero, Fin.succ_lt_succ_iff, one_mul]

lemma gammaSchurProduct_cons {n : ℕ} (r : ℝ) (q : Fin n → ℝ) :
    gammaSchurProduct (Fin.cons r q) =
      Real.Gamma r * (∏ i, (q i - r)/(r + q i)) * gammaSchurProduct q := by
  unfold gammaSchurProduct
  rw [orderedPairProduct_cons (fun r s : ℝ => (s-r)/(r+s))]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

lemma gammaSchurProduct_laguerre (n : ℕ) (a : ℝ) :
    gammaSchurProduct (fun i : Fin n => a+i.val) = laguerreNormalizerProduct n a := by
  unfold gammaSchurProduct laguerreNormalizerProduct
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  congr 1 <;> ring

lemma laguerreNormalizer_succ_product (n : ℕ) {a : ℝ} (ha : 0 < a) :
    laguerreNormalizer (n+1) a = Real.Gamma a *
      (∏ i : Fin n, ((i.val:ℝ)+1)/(2*a+i.val+1)) * laguerreNormalizer n (a+1) := by
  rw [laguerreNormalizer_eq_product _ ha,
    ← gammaSchurProduct_laguerre, laguerreNormalizer_eq_product _ (by linarith : 0<a+1),
    ← gammaSchurProduct_laguerre]
  have hq : (fun i : Fin (n+1) => a+i.val) = Fin.cons a (fun i => (a+1)+i.val) := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp only [Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring
  rw [hq, gammaSchurProduct_cons]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  congr 1 <;> ring

lemma gammaSchurProduct_inverse (n : ℕ) {a : ℝ} (ha : 1 < a) :
    gammaSchurProduct (inverseExponents n a) = Real.Gamma (a-1) *
      (∏ i : Fin n, ((i.val:ℝ)+2)/(2*a+i.val)) * laguerreNormalizer n (a+1) := by
  have he : inverseExponents n a = Fin.cons (a-1) (fun i => (a+1)+i.val) := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · simp only [inverseExponents, Fin.cons_succ]
      ring
  rw [he, gammaSchurProduct_cons, gammaSchurProduct_laguerre,
    laguerreNormalizer_eq_product _ (by linarith : 0 < a+1)]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  congr 1 <;> ring

lemma telescoping_inverse_product (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∏ i : Fin n, ((i.val:ℝ)+2)/(b+i.val)) =
      ((n:ℝ)+1)*(b+n)/b * (∏ i : Fin n, ((i.val:ℝ)+1)/(b+i.val+1)) := by
  induction n with
  | zero => simp [hb.ne']
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    have hn : b+(n:ℝ) ≠ 0 := by positivity
    have hn1 : b+(n:ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring

 
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian
theorem laguerreExpectation_inverseSum (n : ℕ) {a : ℝ} (ha : 1 < a) :
    laguerreExpectation n a (fun r => ∑ i, (r i)⁻¹) =
      (n:ℝ)*(2*a+n-1)/(2*a*(a-1)) := by
  cases n with
  | zero => simp [laguerreExpectation]
  | succ n =>
    have ha0 : 0 < a := by linarith
    unfold laguerreExpectation
    rw [integral_laguerre_inverseSum_eq_gammaProduct ha,
      gammaSchurProduct_inverse n ha, laguerreNormalizer_succ_product n ha0,
      telescoping_inverse_product n (mul_pos (by norm_num : (0:ℝ)<2) ha0)]
    have hg := Real.Gamma_add_one (show a-1 ≠ 0 by linarith)
    rw [sub_add_cancel] at hg
    rw [hg]
    have hG : Real.Gamma (a-1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < a-1)).ne'
    have hZ : laguerreNormalizer n (a+1) ≠ 0 := (laguerreNormalizer_pos n (by linarith)).ne'
    have hP : (∏ i : Fin n, ((i.val:ℝ)+1)/(2*a+i.val+1)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      positivity
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring






lemma minTilt_nonneg {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) : 0 ≤ minTilt s r := by
  exact div_nonneg (sq_nonneg _) (by positivity)

lemma minTilt_le_one {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) : minTilt s r ≤ 1 := by
  have ht : 0 ≤ s/r := div_nonneg hs hr.le
  have hm : 0 ≤ max (1-s/r) 0 := le_max_right _ _
  have hm1 : max (1-s/r) 0 ≤ 1 := max_le (by linarith) zero_le_one
  apply (div_le_one (by positivity : 0 < 1+s/r)).2
  nlinarith [mul_self_le_mul_self hm hm1]

lemma minTilt_eq_zero {s r : ℝ} (hr : 0 < r) (hrs : r ≤ s) : minTilt s r = 0 := by
  have ht : 1 ≤ s/r := (le_div_iff₀ hr).2 (by simpa using hrs)
  simp [minTilt, max_eq_right (by linarith : 1-s/r ≤ 0)]

lemma minTilt_eq_pair {s r : ℝ} (hs : 0 < s) (hrs : s < r) :
    minTilt s r = pairKernel s r / r := by
  have hr := hs.trans hrs
  rw [minTilt, max_eq_left (by rw [sub_nonneg]; exact (div_le_one hr).2 hrs.le)]
  unfold pairKernel
  field_simp

lemma one_sub_minTilt_le {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    1-minTilt s r ≤ 3*s/r := by
  by_cases hrs : r ≤ s
  · rw [minTilt_eq_zero hr hrs]
    have ht : 1 ≤ s/r := (le_div_iff₀ hr).2 (by simpa using hrs)
    have he : 3*s/r = 3*(s/r) := by ring
    rw [he]
    linarith
  · have ht : 0 ≤ s/r := div_nonneg hs hr.le
    have ht1 : s/r ≤ 1 := (div_le_one hr).2 (le_of_not_ge hrs)
    rw [minTilt, max_eq_left (by linarith : 0 ≤ 1-s/r)]
    have hd : 0 < 1+s/r := by positivity
    have he : 3*s/r = 3*(s/r) := by ring
    rw [he]
    have hh : 1-3*(s/r) ≤ (1-s/r)^2/(1+s/r) := by
      apply (le_div_iff₀ hd).2
      nlinarith [sq_nonneg (s/r)]
    linarith

lemma measurable_minTilt (s : ℝ) : Measurable (minTilt s) := by unfold minTilt; fun_prop

lemma minTiltProduct_nonneg {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    0 ≤ minTiltProduct n s r := Finset.prod_nonneg fun i _ => minTilt_nonneg hs (hr i)

lemma minTiltProduct_le_one {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    minTiltProduct n s r ≤ 1 := Finset.prod_le_one (fun i _ => minTilt_nonneg hs (hr i))
      (fun i _ => minTilt_le_one hs (hr i))

lemma minTiltProduct_eq_zero {n : ℕ} {s : ℝ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (h : ¬∀ i, s < r i) : minTiltProduct n s r = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (minTilt_eq_zero (hr i) (not_lt.mp hi))

lemma minTiltProduct_pair {n : ℕ} {s : ℝ} (hs : 0 < s) {r : Fin n → ℝ}
    (hr : ∀ i, s < r i) :
    (∏ i, r i) * minTiltProduct n s r = ∏ i, pairKernel s (r i) := by
  unfold minTiltProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [minTilt_eq_pair hs (hr i), mul_div_cancel₀ _ (hs.trans (hr i)).ne']

lemma laguerreDensity_cons_tilt {n : ℕ} {s : ℝ} (hs : 0 < s)
    {r : Fin n → ℝ} (hr : r ∈ laguerreDomain n) (hsr : ∀ i, s < r i) (a : ℝ) :
    laguerreDensity (n+1) a (Fin.cons s r) =
      laguerreWeight a s * minTiltProduct n s r * laguerreDensity n (a+1) r := by
  rw [laguerreDensity_cons, laguerreDensity_succ_parameter _ _ hr.2]
  calc
    _ = laguerreWeight a s * laguerreDensity n a r *
        ((∏ i, r i) * minTiltProduct n s r) := by rw [minTiltProduct_pair hs hsr]
    _ = _ := by ring

lemma measurable_minTiltProduct (n : ℕ) (s : ℝ) : Measurable (minTiltProduct n s) := by
  apply Finset.measurable_prod
  intro i _
  exact (measurable_minTilt s).comp (measurable_pi_apply i)

lemma integrable_laguerreLaw_inverseSum {n : ℕ} {a : ℝ} (ha : 1 < a) :
    Integrable (inverseSum n) (laguerreLaw n a) :=
  integrable_laguerreLaw (by linarith) (integrableOn_laguerre_inverseSum ha)

lemma integrable_laguerreLaw_minTiltProduct (n : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    Integrable (minTiltProduct n s) (laguerreLaw n a) := by
  let := laguerreLaw_isProbabilityMeasure n ha
  apply (integrable_const (1 : ℝ)).mono' (measurable_minTiltProduct n s).aestronglyMeasurable
  filter_upwards [ae_laguerreDomain n a] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (minTiltProduct_nonneg hs hr.2)]
  exact minTiltProduct_le_one hs hr.2



lemma laguerre_indicator_cons_tilt (n : ℕ) (a : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (s : ℝ) (r : Fin n → ℝ) :
    (laguerreDomain (n+1)).indicator (fun x => f x * laguerreDensity (n+1) a x) (Fin.cons s r) =
      (Ioi 0).indicator (laguerreWeight a) s * (laguerreDomain n).indicator
        (fun r => f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r) r := by
  classical
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    by_cases hr : r ∈ laguerreDomain n
    · rw [indicator_of_mem hr]
      by_cases hsr : ∀ i, s < r i
      · rw [indicator_of_mem ((laguerreDomain_cons_iff s r).2 ⟨hs,hr,hsr⟩),
          laguerreDensity_cons_tilt hs hr hsr a]
        ring
      · have hx : Fin.cons s r ∉ laguerreDomain (n+1) := by
          intro hx
          exact hsr ((laguerreDomain_cons_iff s r).1 hx).2.2
        rw [indicator_of_notMem hx, minTiltProduct_eq_zero hr.2 hsr]
        ring
    · have hx : Fin.cons s r ∉ laguerreDomain (n+1) := by
        intro hx
        exact hr ((laguerreDomain_cons_iff s r).1 hx).2.1
      simp only [indicator_of_notMem hx, indicator_of_notMem hr, mul_zero]
  · have hx : Fin.cons s r ∉ laguerreDomain (n+1) := by
      intro hx
      exact hs ((laguerreDomain_cons_iff s r).1 hx).1
    simp only [indicator_of_notMem hx, indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs), zero_mul]

lemma integral_laguerre_splitMin (n : ℕ) (a : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : IntegrableOn (fun x => f x * laguerreDensity (n+1) a x) (laguerreDomain (n+1))) :
    (∫ x in laguerreDomain (n+1), f x * laguerreDensity (n+1) a x) =
      ∫ s in Ioi 0, laguerreWeight a s *
        ∫ r in laguerreDomain n, f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r := by
  have hi := (integrable_indicator_iff (isOpen_laguerreDomain (n+1)).measurableSet).2 hf
  rw [← integral_indicator (isOpen_laguerreDomain (n+1)).measurableSet, integral_fin_cons_eq]
  calc
    _ = ∫ s, ∫ r : Fin n → ℝ, (laguerreDomain (n+1)).indicator
        (fun x => f x * laguerreDensity (n+1) a x) (Fin.cons s r) :=
      integral_prod _ (integrable_fin_cons hi)
    _ = _ := by
      simp_rw [laguerre_indicator_cons_tilt, integral_const_mul,
        integral_indicator (isOpen_laguerreDomain n).measurableSet]
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s =>
        (indicator_mul_left (Ioi 0) (laguerreWeight a)
          (fun s => ∫ r in laguerreDomain n,
            f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r)).symm

lemma integrable_laguerre_splitMin (n : ℕ) (a : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : IntegrableOn (fun x => f x * laguerreDensity (n+1) a x) (laguerreDomain (n+1))) :
    IntegrableOn (fun s => laguerreWeight a s *
        ∫ r in laguerreDomain n, f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r)
      (Ioi 0) := by
  have hi := (integrable_indicator_iff (isOpen_laguerreDomain (n+1)).measurableSet).2 hf
  have hj := (integrable_fin_cons hi).integral_prod_left
  simp_rw [laguerre_indicator_cons_tilt, integral_const_mul,
    integral_indicator (isOpen_laguerreDomain n).measurableSet] at hj
  have he : (fun s => (Ioi 0).indicator (laguerreWeight a) s *
      ∫ r in laguerreDomain n, f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r) =
      (Ioi 0).indicator (fun s => laguerreWeight a s *
      ∫ r in laguerreDomain n, f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r) := by
    ext s
    exact (indicator_mul_left (Ioi 0) (laguerreWeight a)
      (fun s => ∫ r in laguerreDomain n,
        f (Fin.cons s r) * minTiltProduct n s r * laguerreDensity n (a+1) r)).symm
  rw [he] at hj
  exact (integrable_indicator_iff measurableSet_Ioi).1 hj

end



end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_QuarterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory





lemma reciprocal_product_two_succ (n : ℕ) :
    (∏ i : Fin n, ((i.val:ℝ)+1)/(i.val+3)) = 2/((n+1)*(n+2)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [ih]
    have h1 : (n:ℝ)+1 ≠ 0 := by positivity
    have h2 : (n:ℝ)+2 ≠ 0 := by positivity
    have h3 : (n:ℝ)+3 ≠ 0 := by positivity
    field_simp
    ring

lemma laguerreNormalizer_one_step (n : ℕ) :
    laguerreNormalizer (n+1) 1 =
      2/((n+1)*(n+2)) * laguerreNormalizer n 2 := by
  rw [laguerreNormalizer_succ_product n (by norm_num : (0:ℝ)<1)]
  norm_num only [Real.Gamma_one]
  have he : (fun i : Fin n => ((i.val:ℝ)+1)/(2+i.val+1)) =
      (fun i : Fin n => ((i.val:ℝ)+1)/(i.val+3)) := by ext i; congr 1; ring
  rw [he, reciprocal_product_two_succ]
  ring

lemma laguerreNormalizer_one_ratio (n : ℕ) :
    laguerreNormalizer n 2 / laguerreNormalizer (n+1) 1 = ((n:ℝ)+1)*(n+2)/2 := by
  rw [laguerreNormalizer_one_step]
  have hz : laguerreNormalizer n 2 ≠ 0 := (laguerreNormalizer_pos n (by norm_num)).ne'
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  field_simp

lemma minTiltProduct_lower {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    1-3*s*inverseSum n r ≤ minTiltProduct n s r := by
  have h := abs_one_sub_prod_le Finset.univ (fun i : Fin n => minTilt s (r i))
    (fun i _ => by rw [abs_of_nonneg (minTilt_nonneg hs (hr i))]; exact minTilt_le_one hs (hr i))
  have hp := minTiltProduct_le_one hs hr
  change |1-minTiltProduct n s r| ≤ ∑ i, |1-minTilt s (r i)| at h
  rw [abs_of_nonneg (by linarith)] at h
  have hsum : (∑ i, |1-minTilt s (r i)|) ≤ 3*s*inverseSum n r := by
    unfold inverseSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_of_nonneg (sub_nonneg.mpr (minTilt_le_one hs (hr i))), ← div_eq_mul_inv]
    exact one_sub_minTilt_le hs (hr i)
  linarith

lemma laguerre_minTiltProduct_lower (n : ℕ) {a s : ℝ} (ha : 1 < a) (hs : 0 ≤ s) :
    1-3*s*((n:ℝ)*(2*a+n-1)/(2*a*(a-1))) ≤
      ∫ r, minTiltProduct n s r ∂laguerreLaw n a := by
  have ha0 : 0 < a := by linarith
  let := laguerreLaw_isProbabilityMeasure n ha0
  have hi := (integrable_laguerreLaw_inverseSum (n := n) ha).const_mul (3*s)
  have h := integral_mono_ae ((integrable_const 1).sub hi)
    (integrable_laguerreLaw_minTiltProduct n ha0 hs) (show
      (fun r => 1-3*s*inverseSum n r) ≤ᵐ[laguerreLaw n a] minTiltProduct n s from by
      filter_upwards [ae_laguerreDomain n a] with r hr
      exact minTiltProduct_lower hs hr.2)
  have he : (∫ r, inverseSum n r ∂laguerreLaw n a) = (n:ℝ)*(2*a+n-1)/(2*a*(a-1)) := by
    rw [integral_laguerreLaw n ha0]
    exact laguerreExpectation_inverseSum n ha
  change (∫ r, 1-3*s*inverseSum n r ∂laguerreLaw n a) ≤ _ at h
  rw [integral_sub (integrable_const 1) hi, integral_const_mul, he,
    integral_const, probReal_univ, one_smul] at h
  exact h

lemma laguerre_minTiltProduct_two_lower (n : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ 1/(12*((n:ℝ)+1)^2)) :
    laguerreNormalizer n 2 / 2 ≤
      ∫ r in laguerreDomain n, minTiltProduct n s r * laguerreDensity n 2 r := by
  have hn : 0 ≤ (n:ℝ) := by positivity
  have ht : 0 < ((n:ℝ)+1)^2 := by positivity
  have hs2 : s * ((n:ℝ)+1)^2 ≤ 1/12 := by
    have h := (le_div_iff₀ (by positivity : 0 < 12*((n:ℝ)+1)^2)).1 hs'
    nlinarith
  have he : (n:ℝ)*(2*2+n-1)/(2*2*(2-1)) ≤ ((n:ℝ)+1)^2 := by norm_num; nlinarith
  have h := laguerre_minTiltProduct_lower n (by norm_num : (1:ℝ)<2) hs
  have hh : (1/2:ℝ) ≤ ∫ r, minTiltProduct n s r ∂laguerreLaw n 2 := by
    have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 3*s)
    nlinarith
  rw [integral_laguerreLaw _ (by norm_num), laguerreExpectation] at hh
  have H := (le_div_iff₀ (laguerreNormalizer_pos n (by norm_num))).1 hh
  linarith

lemma smallCoordinate_scale_lower (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ 1/(12*((n:ℝ)+1)^2)) :
    ((n:ℝ)+1)^(1/2:ℝ) ≤ s^(-(1/4:ℝ)) := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have ht : 0 < ((n:ℝ)+1)^2 := by positivity
  have hle : s ≤ 1/((n:ℝ)+1)^2 := by
    exact hs'.trans (one_div_le_one_div_of_le ht (by nlinarith))
  have H := Real.rpow_le_rpow_of_nonpos hs hle (by norm_num : -(1/4:ℝ)≤0)
  rw [one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le,
    neg_neg, ← Real.rpow_natCast_mul hn.le] at H
  norm_num only at H
  exact H

 

theorem laguerre_least_inverseQuarter_lower_oai (n : ℕ) :
    (Real.exp (-1)/48) * ((n:ℝ)+1)^(1/2:ℝ) ≤
      laguerreExpectation (n+1) 1 (fun r => (r 0)^(-(1/4:ℝ))) := by
  let t : ℝ := 1/(12*((n:ℝ)+1)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 12*((n:ℝ)+1)^2)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  let F := fun s : ℝ => laguerreWeight 1 s *
    ∫ r in laguerreDomain n, s^(-(1/4:ℝ)) * minTiltProduct n s r * laguerreDensity n 2 r
  have hi := integrableOn_laguerre_inverse_coordinate (N := n+1) (by norm_num : (0:ℝ)<1)
    (0 : Fin (n+1)) (p := 1/4) (by norm_num)
  have hf : IntegrableOn F (Ioi 0) := by
    simpa only [Fin.cons_zero, one_add_one_eq_two] using integrable_laguerre_splitMin n 1
      (fun r => (r 0)^(-(1/4:ℝ))) hi
  have hnonneg (s : ℝ) (hs : 0 < s) : 0 ≤ F s := by
    apply mul_nonneg (laguerreWeight_pos 1 hs).le
    apply setIntegral_nonneg (isOpen_laguerreDomain n).measurableSet
    intro r hr
    exact mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hs _).le
      (minTiltProduct_nonneg hs.le hr.2)) (laguerreDensity_pos 2 hr).le
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 t) :
      ((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1) * (laguerreNormalizer n 2 /2) ≤ F s := by
    have he : Real.exp (-1) ≤ laguerreWeight 1 s := by
      simp only [laguerreWeight, sub_self, Real.rpow_zero, one_mul]
      exact Real.exp_le_exp.2 (by have : s ≤ 1 := hs.2.le.trans ht1; linarith)
    have hp := smallCoordinate_scale_lower n hs.1 hs.2.le
    have hl := laguerre_minTiltProduct_two_lower n hs.1.le hs.2.le
    have hz : 0 < laguerreNormalizer n 2 := laguerreNormalizer_pos n (by norm_num)
    dsimp only [F]
    simp_rw [mul_assoc (s^(-(1/4:ℝ))) _ _]
    rw [integral_const_mul]
    calc
      _ ≤ Real.exp (-1) * (s^(-(1/4:ℝ))*(laguerreNormalizer n 2/2)) := by
        nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg (Real.exp_nonneg (-1)) (by positivity : 0 ≤ laguerreNormalizer n 2/2))]
      _ ≤ laguerreWeight 1 s * (s^(-(1/4:ℝ)) *
          ∫ r in laguerreDomain n, minTiltProduct n s r * laguerreDensity n 2 r) := by
        exact mul_le_mul he (mul_le_mul_of_nonneg_left hl (Real.rpow_pos_of_pos hs.1 _).le)
          (mul_nonneg (Real.rpow_pos_of_pos hs.1 _).le (by positivity)) (laguerreWeight_pos 1 hs.1).le
  have hmass :
      t * (((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1) * (laguerreNormalizer n 2/2)) ≤ ∫ s in Ioi 0, F s := by
    calc
      _ = ∫ s in Ioo 0 t, ((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1) * (laguerreNormalizer n 2/2) := by
        rw [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        simp
      _ ≤ ∫ s in Ioo 0 t, F s := by
        apply setIntegral_mono_on (integrableOn_const (by simp : volume (Ioo 0 t) ≠ ⊤))
          (hf.mono_set Ioo_subset_Ioi_self) measurableSet_Ioo hbound
      _ ≤ _ := setIntegral_mono_set hf (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hnonneg s hs) (Filter.Eventually.of_forall Ioo_subset_Ioi_self)
  have hiEq : (∫ r in laguerreDomain (n+1), (r 0)^(-(1/4:ℝ))*laguerreDensity (n+1) 1 r) =
      ∫ s in Ioi 0, F s := by
    simpa only [Fin.cons_zero, one_add_one_eq_two] using integral_laguerre_splitMin n 1
      (fun r => (r 0)^(-(1/4:ℝ))) hi
  unfold laguerreExpectation
  rw [hiEq]
  apply (div_le_div_of_nonneg_right hmass (laguerreNormalizer_pos (n+1) (by norm_num)).le).trans'
  have hz : 0 < laguerreNormalizer (n+1) 1 := laguerreNormalizer_pos (n+1) (by norm_num)
  have he : t * (((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1) * (laguerreNormalizer n 2/2)) /
      laguerreNormalizer (n+1) 1 =
      (((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1)) * ((n:ℝ)+2)/(48*((n:ℝ)+1)) := by
    calc
      _ = (t * (((n:ℝ)+1)^(1/2:ℝ) * Real.exp (-1))/2) *
          (laguerreNormalizer n 2/laguerreNormalizer (n+1) 1) := by ring
      _ = _ := by
        rw [laguerreNormalizer_one_ratio]
        dsimp only [t]
        have hn : (n:ℝ)+1 ≠ 0 := by positivity
        field_simp
        ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 48*((n:ℝ)+1))).2
  have hr : 0 ≤ ((n:ℝ)+1)^(1/2:ℝ) := Real.rpow_nonneg (by positivity) _
  nlinarith [mul_nonneg hr (Real.exp_nonneg (-1))]

end



end CriticalStrip

end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.laguerre_least_inverseQuarter_lower_oai := @OAI.CriticalStrip.laguerre_least_inverseQuarter_lower_oai
