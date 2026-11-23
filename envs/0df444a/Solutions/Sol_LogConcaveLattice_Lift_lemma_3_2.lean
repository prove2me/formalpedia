-- Prove2me | solution 1 for LogConcaveLattice.Lift.lemma_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:47:06.646395+00:00
-- url     : https://prove2.me/submissions/77ed76c5-45cd-478d-90ea-87e62e2d35af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Gaussian
import Theorems.Thm_LogConcaveLattice_Lift_lemma_3_1
import Theorems.Thm_LogConcaveLattice_Lift_lemma_3_3

open scoped RealInnerProductSpace Matrix
open MeasureTheory LogConcaveLattice.Lift

namespace AuxLemma32

lemma mat_mul_apply {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (v : V n) :
    mat (M * N) v = mat M (mat N v) := by
  ext i
  simp [mat, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

lemma mat_one_apply {n : ℕ} (v : V n) :
    mat (1 : Matrix (Fin n) (Fin n) ℝ) v = v := by
  ext i
  simp [mat]

lemma inner_mat_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (u v : V n) :
    ⟪u, mat M v⟫ = ⟪mat M u, v⟫ := by
  have hMT : Mᵀ = M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hM.eq
  simp only [mat, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, dotProduct, Matrix.mulVec]
  calc
    ∑ i : Fin n, (∑ j : Fin n, M i j * v j) * u i
        = ∑ i : Fin n, ∑ j : Fin n, M i j * v j * u i := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
    _ = ∑ j : Fin n, ∑ i : Fin n, M i j * v j * u i := Finset.sum_comm
    _ = ∑ j : Fin n, v j * ∑ i : Fin n, Mᵀ j i * u i := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by simp [Matrix.transpose_apply]; ring
    _ = ∑ j : Fin n, v j * ∑ i : Fin n, M j i * u i := by rw [hMT]

lemma posDef_quad_vec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {v : V n} (hv : v ≠ 0) : 0 < ⟪v, mat A v⟫ := by
  let f : Fin n →₀ ℝ := Finsupp.equivFunOnFinite.symm (fun i => v i)
  have hfv : ∀ k : Fin n, f k = v k := fun _ => rfl
  have hf : f ≠ 0 := by
    intro h0
    apply hv
    ext i
    have hi : f i = 0 := by rw [h0]; rfl
    rwa [hfv] at hi
  have hpos := hA.2 hf
  have hq : (f.sum fun i xi => f.sum fun j xj => star xi * A i j * xj) = ⟪v, mat A v⟫ := by
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    have hinner : ∀ i : Fin n,
        (f.sum fun j xj => star (f i) * A i j * xj) =
          ∑ j : Fin n, star (f i) * A i j * f j :=
      fun i => Finsupp.sum_fintype _ _ (fun _ => by simp)
    simp_rw [hinner, hfv]
    simp only [star_trivial, mat, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rwa [← hq]

lemma inv_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (A⁻¹).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_eq_transpose_of_trivial, hA.eq]

lemma pinv_eq_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    pinv A = A⁻¹ := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hImA : matIm A = ⊤ := by
    ext v
    refine ⟨fun _ => trivial, fun _ => ⟨mat A⁻¹ v, ?_⟩⟩
    rw [← mat_mul_apply, Matrix.mul_nonsing_inv A hunit, mat_one_apply]
  have hImAinv : matIm A⁻¹ = ⊤ := by
    ext v
    refine ⟨fun _ => trivial, fun _ => ⟨mat A v, ?_⟩⟩
    rw [← mat_mul_apply, Matrix.nonsing_inv_mul A hunit, mat_one_apply]
  have hproj_id : ∀ u : V n, (matIm A).starProjection u = u := by
    intro u
    exact Submodule.starProjection_eq_self_iff.mpr (by rw [hImA]; trivial)
  have hp : IsPseudoinverse A A⁻¹ := by
    refine ⟨inv_isHermitian hA.isHermitian, by rw [hImAinv, hImA], ?_, ?_⟩
    · intro x
      rw [Matrix.mul_nonsing_inv A hunit, mat_one_apply, hproj_id]
    · intro x
      rw [Matrix.nonsing_inv_mul A hunit, mat_one_apply, hproj_id]
  have hex : ∃ B, IsPseudoinverse A B := ⟨A⁻¹, hp⟩
  simp only [pinv, dif_pos hex]
  have hB : IsPseudoinverse A hex.choose := hex.choose_spec
  apply Matrix.toEuclideanLin.injective
  ext v : 1
  calc
    mat hex.choose v = mat hex.choose (mat (A * A⁻¹) v) := by
      rw [Matrix.mul_nonsing_inv A hunit, mat_one_apply]
    _ = mat (hex.choose * A) (mat A⁻¹ v) := by
      rw [mat_mul_apply, mat_mul_apply]
    _ = (matIm A).starProjection (mat A⁻¹ v) := hB.2.2.2 _
    _ = mat A⁻¹ v := hproj_id _

lemma rho_eq_exp {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (z : V n) :
    rho A z = Real.exp (-Real.pi * ⟪z, mat A⁻¹ z⟫) := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hmem : z ∈ matIm A := ⟨mat A⁻¹ z, by
    rw [← mat_mul_apply, Matrix.mul_nonsing_inv A hunit, mat_one_apply]⟩
  simp [rho, if_pos hmem, pinv_eq_inv hA]

lemma exists_coercive_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V n, c * ‖v‖ ^ 2 ≤ ⟪v, mat A⁻¹ v⟫ := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hinv_pos : ∀ v : V n, v ≠ 0 → 0 < ⟪v, mat A⁻¹ v⟫ := by
    intro v hv
    let w := mat A⁻¹ v
    have hw : w ≠ 0 := by
      intro h0
      apply hv
      calc
        v = mat (A * A⁻¹) v := by rw [Matrix.mul_nonsing_inv A hunit, mat_one_apply]
        _ = mat A w := mat_mul_apply A A⁻¹ v
        _ = 0 := by rw [h0, map_zero]
    have hvw : v = mat A w := by
      rw [← mat_mul_apply, Matrix.mul_nonsing_inv A hunit, mat_one_apply]
    have hinner : ⟪v, mat A⁻¹ v⟫ = ⟪w, mat A w⟫ := by
      change ⟪v, w⟫ = ⟪w, mat A w⟫
      rw [hvw]
      exact (inner_mat_symm hA.isHermitian w w).symm
    rw [hinner]
    exact posDef_quad_vec hA hw
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, zero_lt_one, fun v => ?_⟩
    have hv0 : v = 0 := Subsingleton.elim v 0
    subst hv0
    simp
  · let S : Set (V n) := Metric.sphere 0 1
    have hScpt : IsCompact S := isCompact_sphere 0 1
    have hSne : S.Nonempty := by
      refine ⟨EuclideanSpace.single ⟨0, hn⟩ 1, ?_⟩
      simp [S]
    let g : V n → ℝ := fun u => ⟪u, mat A⁻¹ u⟫
    have hg_cont : Continuous g :=
      continuous_id.inner (LinearMap.continuous_of_finiteDimensional (mat A⁻¹))
    obtain ⟨u₀, hu₀S, hu₀min⟩ := hScpt.exists_isMinOn hSne hg_cont.continuousOn
    have hu₀norm : ‖u₀‖ = 1 := by simpa [S] using hu₀S
    have hu₀ne : u₀ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hu₀norm; norm_num at hu₀norm
    refine ⟨g u₀, hinv_pos u₀ hu₀ne, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp
    · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let u := ‖v‖⁻¹ • v
      have huS : u ∈ S := by
        rw [Metric.mem_sphere, dist_zero_right]
        exact norm_smul_inv_norm hv
      have hle : g u₀ ≤ g u := hu₀min huS
      have hgu : g u = (‖v‖ ^ 2)⁻¹ * g v := by
        simp only [g, u, map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
      rw [hgu] at hle
      have hsq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hvn
      have hsq_ne : ‖v‖ ^ 2 ≠ 0 := ne_of_gt hsq
      calc
        g u₀ * ‖v‖ ^ 2 ≤ ((‖v‖ ^ 2)⁻¹ * g v) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hsq)
        _ = g v * ((‖v‖ ^ 2)⁻¹ * ‖v‖ ^ 2) := by ring
        _ = g v := by rw [inv_mul_cancel₀ hsq_ne, mul_one]

lemma summable_int_exp_neg_sq {β : ℝ} (hβ : 0 < β) :
    Summable (fun m : ℤ => Real.exp (-β * (m : ℝ) ^ 2)) := by
  let r := Real.exp (-β)
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hint_geom : Summable (fun m : ℤ => r ^ m.natAbs) := by
    refine Summable.of_nat_of_neg (f := fun m : ℤ => r ^ m.natAbs) ?_ ?_
    · simpa using hgeom
    · simpa using hgeom
  refine Summable.of_nonneg_of_le (fun _ => le_of_lt (Real.exp_pos _)) (fun m => ?_) hint_geom
  have hm_sq : (m.natAbs : ℝ) ≤ (m : ℝ) ^ 2 := by
    have hnat : m.natAbs ≤ m.natAbs ^ 2 := Nat.le_self_pow two_ne_zero m.natAbs
    have hreal : (m.natAbs : ℝ) ≤ ((m.natAbs : ℝ) ^ 2) := by exact_mod_cast hnat
    have habs : ((m.natAbs : ℝ) ^ 2) = (m : ℝ) ^ 2 := by
      cases m with
      | ofNat k => simp
      | negSucc k => simp; ring
    linarith
  have hexp_le : -β * (m : ℝ) ^ 2 ≤ -β * (m.natAbs : ℝ) := by nlinarith
  calc
    Real.exp (-β * (m : ℝ) ^ 2) ≤ Real.exp (-β * (m.natAbs : ℝ)) :=
      Real.exp_le_exp.mpr hexp_le
    _ = Real.exp ((m.natAbs : ℝ) * (-β)) := by ring_nf
    _ = r ^ m.natAbs := Real.exp_nat_mul (-β) m.natAbs

lemma summable_pi_int_exp_neg_sum_sq : ∀ (m : ℕ) {β : ℝ}, 0 < β →
    Summable (fun k : Fin m → ℤ => Real.exp (-β * ∑ i : Fin m, (k i : ℝ) ^ 2))
  | 0, β, _ => (hasSum_fintype _).summable
  | m + 1, β, hβ => by
      have ih := summable_pi_int_exp_neg_sum_sq m hβ
      have s1 := summable_int_exp_neg_sq hβ
      have hprod : Summable (fun p : ℤ × (Fin m → ℤ) =>
          Real.exp (-β * (p.1 : ℝ) ^ 2) * Real.exp (-β * ∑ i : Fin m, (p.2 i : ℝ) ^ 2)) :=
        Summable.mul_of_nonneg s1 ih (fun _ => le_of_lt (Real.exp_pos _))
          (fun _ => le_of_lt (Real.exp_pos _))
      let e : ℤ × (Fin m → ℤ) ≃ (Fin (m + 1) → ℤ) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun k => (k 0, Fin.tail k)
          left_inv := fun ⟨a, f⟩ => by simp
          right_inv := fun k => Fin.cons_self_tail k }
      rw [← e.summable_iff]
      convert hprod using 1
      ext ⟨k₀, k'⟩
      simp only [Function.comp_apply, e, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero,
        Fin.cons_succ, ← Real.exp_add]
      ring_nf

lemma summable_lattice_gaussian {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {α : ℝ} (hα : 0 < α) (z : V n) :
    Summable (fun l : Λ => Real.exp (-α * ‖z + (l : V n)‖ ^ 2)) := by
  let b₀ := Module.Free.chooseBasis ℤ Λ
  let B₀ := b₀.ofZLatticeBasis ℝ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = n := by
    rw [← Module.finrank_eq_card_basis B₀, finrank_euclideanSpace_fin]
  let idx : Fin n ≃ Module.Free.ChooseBasisIndex ℤ Λ :=
    (Fintype.equivFinOfCardEq hcard).symm
  let bZ : Module.Basis (Fin n) ℤ Λ := b₀.reindex idx.symm
  let B : Module.Basis (Fin n) ℝ (V n) := bZ.ofZLatticeBasis ℝ Λ
  let L_repr : V n →L[ℝ] (Fin n → ℝ) := B.equivFun.toLinearMap.toContinuousLinearMap
  let K : ℝ := ‖L_repr‖ + 1
  have hKpos : 0 < K := by positivity
  let M : ℝ := (n : ℝ) * K ^ 2 + 1
  have hMpos : 0 < M := by positivity
  have hcoord_le : ∀ v : V n, ∑ i : Fin n, (B.repr v i) ^ 2 ≤ M * ‖v‖ ^ 2 := by
    intro v
    have hterm : ∀ i : Fin n, (B.repr v i) ^ 2 ≤ (K * ‖v‖) ^ 2 := by
      intro i
      have hi : |L_repr v i| ≤ K * ‖v‖ := by
        calc
          |L_repr v i| = ‖L_repr v i‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖L_repr v‖ := norm_le_pi_norm (L_repr v) i
          _ ≤ ‖L_repr‖ * ‖v‖ := L_repr.le_opNorm v
          _ ≤ K * ‖v‖ := mul_le_mul_of_nonneg_right (by simp [K]) (norm_nonneg v)
      have hrepr_eq : B.repr v i = L_repr v i := rfl
      have hsq_abs : (B.repr v i) ^ 2 = |L_repr v i| ^ 2 := by rw [hrepr_eq, sq_abs]
      rw [hsq_abs]
      nlinarith [hi, abs_nonneg (L_repr v i), norm_nonneg v, hKpos]
    calc
      ∑ i : Fin n, (B.repr v i) ^ 2 ≤ ∑ _i : Fin n, (K * ‖v‖) ^ 2 :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (n : ℝ) * K ^ 2 * ‖v‖ ^ 2 := by simp; ring
      _ ≤ M * ‖v‖ ^ 2 := by simp [M]; nlinarith [sq_nonneg ‖v‖]
  let eZ : (Fin n → ℤ) ≃ Λ :=
    { toFun := fun k => ∑ i : Fin n, k i • bZ i
      invFun := fun l => fun i => bZ.repr l i
      left_inv := fun k => by
        ext i
        dsimp only
        rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
        simp [Module.Basis.repr_self, Finsupp.single_apply]
      right_inv := fun l => bZ.sum_repr l }
  rw [← eZ.summable_iff]
  let β : ℝ := α / (2 * M)
  have hβ : 0 < β := by positivity
  have hdom : Summable (fun k : Fin n → ℤ =>
      Real.exp (α * ‖z‖ ^ 2) * Real.exp (-β * ∑ i : Fin n, (k i : ℝ) ^ 2)) :=
    (summable_pi_int_exp_neg_sum_sq n hβ).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => le_of_lt (Real.exp_pos _)) (fun k => ?_) hdom
  let v : V n := (eZ k : V n)
  have hvB : v = ∑ i : Fin n, (k i : ℝ) • B i := by
    change ((∑ i : Fin n, k i • bZ i : Λ) : V n) = _
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℝ]
    simp [B]
  have hv_repr : ∀ i : Fin n, B.repr v i = (k i : ℝ) := by
    intro i
    rw [hvB, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    simp [map_smul, Module.Basis.repr_self, Finsupp.single_apply]
  have hsum_k : ∑ i : Fin n, (k i : ℝ) ^ 2 ≤ M * ‖v‖ ^ 2 := by
    simpa [hv_repr] using hcoord_le v
  have hpar := parallelogram_law_with_norm ℝ (z + v) z
  have hsub : z + v - z = v := add_sub_cancel_left z v
  rw [hsub] at hpar
  have hv_le : ‖v‖ ^ 2 ≤ 2 * ‖z + v‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
    have hnn : 0 ≤ ‖z + v + z‖ ^ 2 := sq_nonneg _
    linarith [hpar]
  have hk_le : ∑ i : Fin n, (k i : ℝ) ^ 2 ≤ 2 * M * ‖z + v‖ ^ 2 + 2 * M * ‖z‖ ^ 2 := by
    nlinarith [hsum_k, hv_le]
  have hexp_ineq : -α * ‖z + v‖ ^ 2 ≤ α * ‖z‖ ^ 2 + (-β * ∑ i : Fin n, (k i : ℝ) ^ 2) := by
    have hdiv : (∑ i : Fin n, (k i : ℝ) ^ 2) / (2 * M) ≤ ‖z + v‖ ^ 2 + ‖z‖ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hk_le]
    have hmul := mul_le_mul_of_nonneg_left hdiv (le_of_lt hα)
    have hβ_eq : α * ((∑ i : Fin n, (k i : ℝ) ^ 2) / (2 * M)) =
        β * ∑ i : Fin n, (k i : ℝ) ^ 2 := by
      simp only [β]
      ring
    linarith
  change Real.exp (-α * ‖z + v‖ ^ 2) ≤ _
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr hexp_ineq

lemma summable_rho_coset {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (z : V n) :
    Summable (fun l : Λ => rho A (z + l)) := by
  obtain ⟨c, hcpos, hcoerc⟩ := exists_coercive_inv hA
  have hdom := summable_lattice_gaussian Λ (mul_pos Real.pi_pos hcpos) z
  refine Summable.of_nonneg_of_le (fun l => by rw [rho_eq_exp hA]; positivity) (fun l => ?_) hdom
  rw [rho_eq_exp hA]
  apply Real.exp_le_exp.mpr
  have h := hcoerc (z + l)
  nlinarith [Real.pi_pos]

lemma summable_norm_sq_mul_rho {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (z : V n) :
    Summable (fun l : Λ => ‖z + (l : V n)‖ ^ 2 * rho A (z + l)) := by
  obtain ⟨c, hcpos, hcoerc⟩ := exists_coercive_inv hA
  let α := Real.pi * c
  have hα : 0 < α := mul_pos Real.pi_pos hcpos
  have hdom : Summable (fun l : Λ =>
      (2 / α) * Real.exp (-(α / 2) * ‖z + (l : V n)‖ ^ 2)) :=
    (summable_lattice_gaussian Λ (by positivity) z).mul_left _
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (sq_nonneg _) (by rw [rho_eq_exp hA]; positivity)) (fun l => ?_) hdom
  rw [rho_eq_exp hA]
  have h1 : ⟪z + (l : V n), mat A⁻¹ (z + (l : V n))⟫ ≥ c * ‖z + (l : V n)‖ ^ 2 := hcoerc _
  have hexp1 : Real.exp (-Real.pi * ⟪z + (l : V n), mat A⁻¹ (z + (l : V n))⟫) ≤
      Real.exp (-α * ‖z + (l : V n)‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have ht : (α / 2) * ‖z + (l : V n)‖ ^ 2 ≤
      Real.exp ((α / 2) * ‖z + (l : V n)‖ ^ 2) := by
    linarith [Real.add_one_le_exp ((α / 2) * ‖z + (l : V n)‖ ^ 2)]
  have ht' : ‖z + (l : V n)‖ ^ 2 ≤ (2 / α) * Real.exp ((α / 2) * ‖z + (l : V n)‖ ^ 2) := by
    have : ‖z + (l : V n)‖ ^ 2 * (α / 2) ≤ Real.exp ((α / 2) * ‖z + (l : V n)‖ ^ 2) := by
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hα]
    linarith
  calc
    ‖z + (l : V n)‖ ^ 2 * Real.exp (-Real.pi * ⟪z + (l : V n), mat A⁻¹ (z + (l : V n))⟫)
        ≤ ‖z + (l : V n)‖ ^ 2 * Real.exp (-α * ‖z + (l : V n)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hexp1 (sq_nonneg _)
    _ ≤ ((2 / α) * Real.exp ((α / 2) * ‖z + (l : V n)‖ ^ 2)) *
          Real.exp (-α * ‖z + (l : V n)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right ht' (le_of_lt (Real.exp_pos _))
    _ = (2 / α) * Real.exp (-(α / 2) * ‖z + (l : V n)‖ ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1; congr 1; ring

lemma rhoCoset_pos {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (z : V n) :
    0 < rhoCoset A Λ z := by
  have hsum := summable_rho_coset Λ hA z
  have h0 : 0 < rho A (z + ((0 : Λ) : V n)) := by rw [rho_eq_exp hA]; positivity
  have hle : rho A (z + ((0 : Λ) : V n)) ≤ ∑' l : Λ, rho A (z + l) :=
    hsum.le_tsum (0 : Λ) (fun l _ => by rw [rho_eq_exp hA]; positivity)
  exact lt_of_lt_of_le h0 hle

lemma dgCov_nonneg_origin {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (v : V n) :
    0 ≤ ⟪v, mat (dgCov A Λ 0) v⟫ := by
  let Z := rhoCoset A Λ 0
  have hZpos : 0 < Z := rhoCoset_pos Λ hA 0
  let p : Λ → ℝ := fun l => rho A (0 + l) / Z
  have hp_nonneg : ∀ l : Λ, 0 ≤ p l := fun l =>
    div_nonneg (by rw [rho_eq_exp hA]; positivity) (le_of_lt hZpos)
  have hp_sum : Summable p := (summable_rho_coset Λ hA 0).div_const Z
  have hp_tsum : ∑' l : Λ, p l = 1 := by
    simp only [p, tsum_div_const]
    exact div_self (ne_of_gt hZpos)
  have hdom_sq : Summable (fun l : Λ => ‖(0 : V n) + (l : V n)‖ ^ 2 * p l) := by
    have hs := (summable_norm_sq_mul_rho Λ hA 0).div_const Z
    have heq : (fun l : Λ => ‖(0 : V n) + (l : V n)‖ ^ 2 * rho A (0 + l) / Z) =
        (fun l : Λ => ‖(0 : V n) + (l : V n)‖ ^ 2 * p l) := by
      ext l; dsimp only [p]; ring
    rwa [heq] at hs
  have hdom_1sq : Summable (fun l : Λ => (1 + ‖(0 : V n) + (l : V n)‖ ^ 2) * p l) := by
    have hs := hp_sum.add hdom_sq
    have heq : (fun l : Λ => p l + ‖(0 : V n) + (l : V n)‖ ^ 2 * p l) =
        (fun l : Λ => (1 + ‖(0 : V n) + (l : V n)‖ ^ 2) * p l) := by
      ext l; ring
    rwa [heq] at hs
  have hsum_1 : ∀ i : Fin n, Summable (fun l : Λ => p l * ((0 + (l : V n)) i)) := by
    intro i
    refine Summable.of_norm_bounded hdom_1sq fun l => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp_nonneg l)]
    have hci : |(0 + (l : V n)) i| ≤ ‖(0 : V n) + (l : V n)‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le (0 + (l : V n)) i
    have h1 : ‖(0 : V n) + (l : V n)‖ ≤ 1 + ‖(0 : V n) + (l : V n)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖(0 : V n) + (l : V n)‖ - 1)]
    nlinarith [hp_nonneg l]
  have hsum_2 : ∀ i j : Fin n,
      Summable (fun l : Λ => p l * (((0 + (l : V n)) i) * ((0 + (l : V n)) j))) := by
    intro i j
    refine Summable.of_norm_bounded hdom_sq fun l => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hp_nonneg l)]
    have hci : |(0 + (l : V n)) i| ≤ ‖(0 : V n) + (l : V n)‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le (0 + (l : V n)) i
    have hcj : |(0 + (l : V n)) j| ≤ ‖(0 : V n) + (l : V n)‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le (0 + (l : V n)) j
    have hmul : |(0 + (l : V n)) i| * |(0 + (l : V n)) j| ≤ ‖(0 : V n) + (l : V n)‖ ^ 2 := by
      rw [sq]
      exact mul_le_mul hci hcj (abs_nonneg _) (norm_nonneg _)
    nlinarith [hp_nonneg l]
  have hsum_ip1 : Summable (fun l : Λ => p l * ⟪v, 0 + (l : V n)⟫) := by
    have hdom : Summable (fun l : Λ => ‖v‖ * ((1 + ‖(0 : V n) + (l : V n)‖ ^ 2) * p l)) :=
      hdom_1sq.mul_left ‖v‖
    refine Summable.of_norm_bounded hdom fun l => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp_nonneg l)]
    have hip : |⟪v, 0 + (l : V n)⟫| ≤ ‖v‖ * ‖(0 : V n) + (l : V n)‖ :=
      abs_real_inner_le_norm v _
    have h1 : ‖(0 : V n) + (l : V n)‖ ≤ 1 + ‖(0 : V n) + (l : V n)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖(0 : V n) + (l : V n)‖ - 1)]
    calc
      p l * |⟪v, 0 + (l : V n)⟫|
          ≤ p l * (‖v‖ * ‖(0 : V n) + (l : V n)‖) :=
            mul_le_mul_of_nonneg_left hip (hp_nonneg l)
      _ ≤ p l * (‖v‖ * (1 + ‖(0 : V n) + (l : V n)‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg v)) (hp_nonneg l)
      _ = ‖v‖ * ((1 + ‖(0 : V n) + (l : V n)‖ ^ 2) * p l) := by ring
  have hsum_ip2 : Summable (fun l : Λ => p l * ⟪v, 0 + (l : V n)⟫ ^ 2) := by
    have hdom : Summable (fun l : Λ => ‖v‖ ^ 2 * (‖(0 : V n) + (l : V n)‖ ^ 2 * p l)) :=
      hdom_sq.mul_left (‖v‖ ^ 2)
    refine Summable.of_norm_bounded hdom fun l => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp_nonneg l), abs_of_nonneg (sq_nonneg _)]
    have hip : |⟪v, 0 + (l : V n)⟫| ≤ ‖v‖ * ‖(0 : V n) + (l : V n)‖ :=
      abs_real_inner_le_norm v _
    have hsq : ⟪v, 0 + (l : V n)⟫ ^ 2 ≤ ‖v‖ ^ 2 * ‖(0 : V n) + (l : V n)‖ ^ 2 := by
      have : |⟪v, 0 + (l : V n)⟫| ^ 2 ≤ (‖v‖ * ‖(0 : V n) + (l : V n)‖) ^ 2 := by
        nlinarith [hip, abs_nonneg ⟪v, 0 + (l : V n)⟫, norm_nonneg v, norm_nonneg ((0 : V n) + l)]
      rwa [sq_abs, mul_pow] at this
    nlinarith [hp_nonneg l]
  let μ := ∑' l : Λ, p l * ⟪v, 0 + (l : V n)⟫
  have hμ_coord : ∑ i : Fin n, (∑' l : Λ, p l * (0 + (l : V n)) i) * v i = μ := by
    have hpull : ∀ i : Fin n, (∑' l : Λ, p l * (0 + (l : V n)) i) * v i =
        ∑' l : Λ, (p l * (0 + (l : V n)) i) * v i := by
      intro i
      rw [← tsum_mul_right]
    simp_rw [hpull]
    rw [← Summable.tsum_finsetSum (fun i _ => (hsum_1 i).mul_right (v i))]
    congr 1; ext l
    have hinner_v : ∑ i : Fin n, (0 + (l : V n)) i * v i = ⟪v, 0 + (l : V n)⟫ := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    calc
      ∑ i : Fin n, (p l * (0 + (l : V n)) i) * v i
          = p l * ∑ i : Fin n, (0 + (l : V n)) i * v i := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ = p l * ⟪v, 0 + (l : V n)⟫ := by rw [hinner_v]
  have h2_coord : ∑ i : Fin n, (∑ j : Fin n,
      (∑' l : Λ, p l * ((0 + (l : V n)) i * (0 + (l : V n)) j)) * v j) * v i =
      ∑' l : Λ, p l * ⟪v, 0 + (l : V n)⟫ ^ 2 := by
    have hpull_j : ∀ i : Fin n, (∑ j : Fin n,
        (∑' l : Λ, p l * ((0 + (l : V n)) i * (0 + (l : V n)) j)) * v j) * v i =
        ∑' l : Λ, p l * ((0 + (l : V n)) i * v i) * ⟪v, 0 + (l : V n)⟫ := by
      intro i
      have hj : ∀ j : Fin n, (∑' l : Λ, p l * ((0 + (l : V n)) i * (0 + (l : V n)) j)) * v j =
          ∑' l : Λ, p l * ((0 + (l : V n)) i * ((0 + (l : V n)) j * v j)) := by
        intro j; rw [← tsum_mul_right]; congr 1; ext l; ring
      simp_rw [hj]
      have hsj : ∀ j : Fin n, Summable (fun l : Λ =>
          p l * ((0 + (l : V n)) i * ((0 + (l : V n)) j * v j))) := by
        intro j
        have hs := (hsum_2 i j).mul_right (v j)
        have heq : (fun l : Λ => p l * ((0 + (l : V n)) i * (0 + (l : V n)) j) * v j) =
            (fun l : Λ => p l * ((0 + (l : V n)) i * ((0 + (l : V n)) j * v j))) := by
          ext l; ring
        rwa [heq] at hs
      rw [← Summable.tsum_finsetSum (fun j _ => hsj j), ← tsum_mul_right]
      congr 1; ext l
      have hinner_v : ∑ j : Fin n, (0 + (l : V n)) j * v j = ⟪v, 0 + (l : V n)⟫ := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
      calc
        (∑ j : Fin n, p l * ((0 + (l : V n)) i * ((0 + (l : V n)) j * v j))) * v i
            = p l * ((0 + (l : V n)) i * v i) * ∑ j : Fin n, (0 + (l : V n)) j * v j := by
              rw [Finset.sum_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by ring
        _ = p l * ((0 + (l : V n)) i * v i) * ⟪v, 0 + (l : V n)⟫ := by rw [hinner_v]
    simp_rw [hpull_j]
    have hsi : ∀ i : Fin n, Summable (fun l : Λ =>
        p l * ((0 + (l : V n)) i * v i) * ⟪v, 0 + (l : V n)⟫) := by
      intro i
      have hdom : Summable (fun l : Λ =>
          (|v i| * ‖v‖) * (‖(0 : V n) + (l : V n)‖ ^ 2 * p l)) :=
        hdom_sq.mul_left _
      refine Summable.of_norm_bounded hdom fun l => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hp_nonneg l)]
      have hci : |(0 + (l : V n)) i| ≤ ‖(0 : V n) + (l : V n)‖ := by
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le (0 + (l : V n)) i
      have hip : |⟪v, 0 + (l : V n)⟫| ≤ ‖v‖ * ‖(0 : V n) + (l : V n)‖ :=
        abs_real_inner_le_norm v _
      have hprod1 : |(0 + (l : V n)) i| * |v i| ≤ |v i| * ‖(0 : V n) + (l : V n)‖ := by
        nlinarith [hci, abs_nonneg (v i)]
      have hprod2 : (|(0 + (l : V n)) i| * |v i|) * |⟪v, 0 + (l : V n)⟫| ≤
          |v i| * ‖v‖ * ‖(0 : V n) + (l : V n)‖ ^ 2 := by
        calc
          (|(0 + (l : V n)) i| * |v i|) * |⟪v, 0 + (l : V n)⟫|
              ≤ (|v i| * ‖(0 : V n) + (l : V n)‖) * (‖v‖ * ‖(0 : V n) + (l : V n)‖) :=
                mul_le_mul hprod1 hip (by positivity) (by positivity)
          _ = |v i| * ‖v‖ * ‖(0 : V n) + (l : V n)‖ ^ 2 := by ring
      nlinarith [hp_nonneg l]
    rw [← Summable.tsum_finsetSum (fun i _ => hsi i)]
    congr 1; ext l
    have hinner_v : ∑ i : Fin n, (0 + (l : V n)) i * v i = ⟪v, 0 + (l : V n)⟫ := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    calc
      ∑ i : Fin n, p l * ((0 + (l : V n)) i * v i) * ⟪v, 0 + (l : V n)⟫
          = p l * (∑ i : Fin n, (0 + (l : V n)) i * v i) * ⟪v, 0 + (l : V n)⟫ := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = p l * ⟪v, 0 + (l : V n)⟫ ^ 2 := by rw [hinner_v]; ring
  have hcov_eq : ⟪v, mat (dgCov A Λ 0) v⟫ =
      (∑' l : Λ, p l * ⟪v, 0 + (l : V n)⟫ ^ 2) - μ ^ 2 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    simp only [mat, Matrix.toLpLin_apply, Matrix.mulVec, dgCov, Matrix.of_apply]
    let a : Fin n → Fin n → ℝ := fun i j =>
      ∑' l : Λ, p l * ((0 + (l : V n)) i * (0 + (l : V n)) j)
    let b : Fin n → ℝ := fun i => ∑' l : Λ, p l * (0 + (l : V n)) i
    change ∑ i : Fin n, (∑ j : Fin n, (a i j - b i * b j) * v j) * v i = _
    have hsplit : ∑ i : Fin n, (∑ j : Fin n, (a i j - b i * b j) * v j) * v i =
        (∑ i : Fin n, (∑ j : Fin n, a i j * v j) * v i) -
        (∑ i : Fin n, b i * v i) * (∑ j : Fin n, b j * v j) := by
      have inner_split : ∀ i : Fin n,
          (∑ j : Fin n, (a i j - b i * b j) * v j) * v i =
          (∑ j : Fin n, a i j * v j) * v i - (b i * v i) * (∑ j : Fin n, b j * v j) := by
        intro i
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib, sub_mul]
        congr 1
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp_rw [inner_split, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hsplit, h2_coord, hμ_coord, sq]
  rw [hcov_eq]
  have hvar_nn : 0 ≤ ∑' l : Λ, p l * (⟪v, 0 + (l : V n)⟫ - μ) ^ 2 :=
    tsum_nonneg fun l => mul_nonneg (hp_nonneg l) (sq_nonneg _)
  have hvar_eq : ∑' l : Λ, p l * (⟪v, 0 + (l : V n)⟫ - μ) ^ 2 =
      (∑' l : Λ, p l * ⟪v, 0 + (l : V n)⟫ ^ 2) - μ ^ 2 := by
    have hexp : (fun l : Λ => p l * (⟪v, 0 + (l : V n)⟫ - μ) ^ 2) =
        (fun l : Λ => (p l * ⟪v, 0 + (l : V n)⟫ ^ 2 - (2 * μ) * (p l * ⟪v, 0 + (l : V n)⟫)) +
          μ ^ 2 * p l) := by ext l; ring
    rw [hexp,
        Summable.tsum_add (hsum_ip2.sub (hsum_ip1.mul_left (2 * μ))) (hp_sum.mul_left (μ ^ 2)),
        Summable.tsum_sub hsum_ip2 (hsum_ip1.mul_left (2 * μ)),
        tsum_mul_left, tsum_mul_left, hp_tsum]
    change (∑' l : Λ, p l * ⟪v, 0 + (l : V n)⟫ ^ 2) - 2 * μ * μ + μ ^ 2 * 1 = _
    ring
  linarith

lemma quad_parallelogram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (a b : V n) :
    ⟪a + b, mat B (a + b)⟫ + ⟪a - b, mat B (a - b)⟫ =
      2 * ⟪a, mat B a⟫ + 2 * ⟪b, mat B b⟫ := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

lemma second_deriv_nonneg_of_min_zero {h h' : ℝ → ℝ} {h''0 : ℝ}
    (hh0 : h 0 = 0) (hh_nn : ∀ t : ℝ, 0 ≤ h t)
    (hd1 : ∀ t : ℝ, HasDerivAt h (h' t) t)
    (hd2 : HasDerivAt h' h''0 0) :
    0 ≤ h''0 := by
  have hmin : IsLocalMin h 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    rw [hh0]
    exact hh_nn t
  have hderiv0 : deriv h 0 = 0 := hmin.deriv_eq_zero
  have hh'0 : h' 0 = 0 := by
    rw [← (hd1 0).deriv]
    exact hderiv0
  have h_ex : ∀ k : ℕ, ∃ c : ℝ, 0 < c ∧ c < 1 / ((k : ℝ) + 1) ∧ 0 ≤ h' c := by
    intro k
    let δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    have hcont : ContinuousOn h (Set.Icc 0 δ) :=
      fun t _ => (hd1 t).continuousAt.continuousWithinAt
    have hdiff : ∀ t ∈ Set.Ioo 0 δ, HasDerivAt h (h' t) t := fun t _ => hd1 t
    obtain ⟨c, ⟨hc0, hcδ⟩, hslope⟩ := exists_hasDerivAt_eq_slope h h' hδ hcont hdiff
    refine ⟨c, hc0, hcδ, ?_⟩
    rw [hslope, hh0, sub_zero, sub_zero]
    exact div_nonneg (hh_nn δ) (le_of_lt hδ)
  choose c hc0 hc_ub hc_nn using h_ex
  have hc_tendsto0 : Filter.Tendsto c Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun k => le_of_lt (hc0 k)) (fun k => le_of_lt (hc_ub k)) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hc_nhds : Filter.Tendsto c Filter.atTop (nhdsWithin 0 ({0}ᶜ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hc_tendsto0, Filter.Eventually.of_forall fun k => ne_of_gt (hc0 k)⟩
  have hslope_tendsto : Filter.Tendsto (fun t => (h' t - h' 0) / (t - 0))
      (nhdsWithin 0 ({0}ᶜ)) (nhds h''0) := by
    have hd := hasDerivAt_iff_tendsto_slope.mp hd2
    convert hd using 1
    ext t
    simp [slope_def_field]
  have hseq := hslope_tendsto.comp hc_nhds
  refine ge_of_tendsto' hseq fun k => ?_
  simp only [Function.comp_apply, hh'0, sub_zero]
  exact div_nonneg (hc_nn k) (le_of_lt (hc0 k))

lemma line_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g (z + s • w)) (fderiv ℝ g (z + t • w) w) t ∧
      HasDerivAt (fun s : ℝ => fderiv ℝ g (z + s • w) w)
        (fderiv ℝ (fderiv ℝ g) (z + t • w) w w) t := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
  have hg_fd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) :=
    hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hg2 : Differentiable ℝ (fderiv ℝ g) := hg_fd.differentiable (by simp)
  have hlin : HasDerivAt (fun s : ℝ => z + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add z
  refine ⟨(hg1 (z + t • w)).hasFDerivAt.comp_hasDerivAt t hlin, ?_⟩
  let ev : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ w
  have hev := (ev.hasFDerivAt (x := fderiv ℝ g (z + t • w))).comp_hasDerivAt t
    ((hg2 (z + t • w)).hasFDerivAt.comp_hasDerivAt t hlin)
  exact hev

lemma hessian_shift_ineq_abstract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : E) (hg_ineq : ∀ y : E, 0 ≤ g (x + y) + g (x - y) - 2 * g x - 2 * g y + 2 * g 0)
    (u : E) :
    0 ≤ 2 * fderiv ℝ (fderiv ℝ g) x u u - 2 * fderiv ℝ (fderiv ℝ g) 0 u u := by
  have hline_d1 : ∀ (z w : E) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (z + s • w)) (fderiv ℝ g (z + t • w) w) t :=
    fun z w t => (line_hasDerivAt hg_smooth z w t).1
  have hline_d2 : ∀ (z w : E) (t : ℝ),
      HasDerivAt (fun s : ℝ => fderiv ℝ g (z + s • w) w)
        (fderiv ℝ (fderiv ℝ g) (z + t • w) w w) t :=
    fun z w t => (line_hasDerivAt hg_smooth z w t).2
  let h : ℝ → ℝ := fun t =>
    g (x + t • u) + g (x + t • (-u)) - 2 * g (0 + t • u) - 2 * g x + 2 * g 0
  let h' : ℝ → ℝ := fun t =>
    fderiv ℝ g (x + t • u) u + fderiv ℝ g (x + t • (-u)) (-u) -
      2 * fderiv ℝ g (0 + t • u) u
  let h''0 : ℝ :=
    fderiv ℝ (fderiv ℝ g) x u u + fderiv ℝ (fderiv ℝ g) x (-u) (-u) -
      2 * fderiv ℝ (fderiv ℝ g) 0 u u
  have hh0 : h 0 = 0 := by simp [h]; ring
  have hh_nn : ∀ t : ℝ, 0 ≤ h t := by
    intro t
    have hsub : x + t • (-u) = x - t • u := by rw [smul_neg, sub_eq_add_neg]
    have h0add : (0 : E) + t • u = t • u := zero_add _
    dsimp only [h]
    rw [hsub, h0add]
    linarith [hg_ineq (t • u)]
  have hd1 : ∀ t : ℝ, HasDerivAt h (h' t) t := by
    intro t
    have d1 := hline_d1 x u t
    have d2 := hline_d1 x (-u) t
    have d3 := (hline_d1 0 u t).const_mul 2
    have d4 := (((d1.add d2).sub d3).sub (hasDerivAt_const t (2 * g x))).add
      (hasDerivAt_const t (2 * g 0))
    have h_eq : h = (((((fun s : ℝ => g (x + s • u)) + fun s => g (x + s • -u)) -
        fun y => 2 * g (0 + y • u)) - fun _ => 2 * g x) + fun _ => 2 * g 0) := rfl
    have h'_eq : h' t = (fderiv ℝ g (x + t • u)) u + (fderiv ℝ g (x + t • -u)) (-u) -
        2 * (fderiv ℝ g (0 + t • u)) u - 0 + 0 := by dsimp [h']; ring
    rw [h_eq, h'_eq]
    exact d4
  have hd2 : HasDerivAt h' h''0 0 := by
    have d1 : HasDerivAt (fun s : ℝ => fderiv ℝ g (x + s • u) u)
        (fderiv ℝ (fderiv ℝ g) x u u) 0 := by simpa using hline_d2 x u 0
    have d2 : HasDerivAt (fun s : ℝ => fderiv ℝ g (x + s • (-u)) (-u))
        (fderiv ℝ (fderiv ℝ g) x (-u) (-u)) 0 := by simpa using hline_d2 x (-u) 0
    have d3 : HasDerivAt (fun s : ℝ => 2 * fderiv ℝ g (0 + s • u) u)
        (2 * fderiv ℝ (fderiv ℝ g) 0 u u) 0 := by simpa using (hline_d2 0 u 0).const_mul 2
    have d4 := (d1.add d2).sub d3
    have h'_eq : h' = (((fun s : ℝ => (fderiv ℝ g (x + s • u)) u) +
        fun s => (fderiv ℝ g (x + s • -u)) (-u)) -
        fun s => 2 * (fderiv ℝ g (0 + s • u)) u) := rfl
    rw [h'_eq]
    exact d4
  have h2_nn : 0 ≤ h''0 := second_deriv_nonneg_of_min_zero hh0 hh_nn hd1 hd2
  have hneg_bilin : fderiv ℝ (fderiv ℝ g) x (-u) (-u) = fderiv ℝ (fderiv ℝ g) x u u := by
    simp [map_neg]
  simp only [h''0, hneg_bilin] at h2_nn
  linarith

end AuxLemma32

theorem solution (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (x : V n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    LoewnerLE 0 (mat (dgCov A Λ 0)) ∧ LoewnerLE (mat (dgCov A Λ 0)) (mat (dgCov A Λ x)) := by
  refine ⟨?_, ?_⟩
  · intro v
    simpa using AuxLemma32.dgCov_nonneg_origin Λ hA v
  · intro v
    obtain ⟨hf_smooth, hhess⟩ := LogConcaveLattice.Lift.lemma_3_3 n Λ A hA
    have hcov_pos : 0 < ZLattice.covolume Λ := ZLattice.covolume_pos Λ volume
    have hrho_pos : ∀ y : V n, 0 < rho A y := fun y => by
      rw [AuxLemma32.rho_eq_exp hA]; positivity
    have hZ_pos : ∀ y : V n, 0 < rhoCoset A Λ y := AuxLemma32.rhoCoset_pos Λ hA
    have hf_pos : ∀ y : V n, 0 < liftDensity A Λ y := fun y => by
      unfold liftDensity
      have := hrho_pos y
      have := hZ_pos y
      positivity
    let g : V n → ℝ := fun y => -Real.log (liftDensity A Λ y)
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
      (hf_smooth.log fun y => ne_of_gt (hf_pos y)).neg
    have hg_eq : ∀ y : V n,
        g y = Real.log (ZLattice.covolume Λ) + Real.pi * ⟪y, mat A⁻¹ y⟫ +
          Real.log (rhoCoset A Λ y) := by
      intro y
      have hc := hcov_pos
      have hr := hrho_pos y
      have hz := hZ_pos y
      simp only [g, liftDensity]
      rw [Real.log_mul (by positivity) (by positivity),
          Real.log_div one_ne_zero (ne_of_gt hc),
          Real.log_div (ne_of_gt hr) (ne_of_gt hz),
          Real.log_one, AuxLemma32.rho_eq_exp hA, Real.log_exp]
      ring
    have hg_ineq : ∀ y : V n, 0 ≤ g (x + y) + g (x - y) - 2 * g x - 2 * g y + 2 * g 0 := by
      intro y
      have hpar := AuxLemma32.quad_parallelogram A⁻¹ x y
      have hl31 := LogConcaveLattice.Lift.lemma_3_1 n Λ A hA x y
      have hlhs_pos : 0 < rhoCoset A Λ x ^ 2 * rhoCoset A Λ y ^ 2 := by
        have := hZ_pos x; have := hZ_pos y; positivity
      have hlog_le := Real.log_le_log hlhs_pos hl31
      rw [Real.log_mul (by have := hZ_pos x; positivity) (by have := hZ_pos y; positivity),
          Real.log_pow, Real.log_pow,
          Real.log_mul (by have := hZ_pos 0; have := hZ_pos (x + y); positivity)
            (ne_of_gt (hZ_pos (x - y))),
          Real.log_mul (by have := hZ_pos 0; positivity) (ne_of_gt (hZ_pos (x + y))),
          Real.log_pow] at hlog_le
      simp only [hg_eq, map_zero, inner_zero_right, mul_zero]
      push_cast at hlog_le
      nlinarith [hpar, hlog_le, Real.pi_pos]
    let u : V n := mat A v
    have h2_nn := AuxLemma32.hessian_shift_ineq_abstract g hg_smooth x hg_ineq u
    have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
    have hAinv_u : mat A⁻¹ u = v := by
      simp only [u, ← AuxLemma32.mat_mul_apply, Matrix.nonsing_inv_mul A hunit,
        AuxLemma32.mat_one_apply]
    have hquad_id : ∀ z : V n, ⟪u, mat (A⁻¹ * dgCov A Λ z * A⁻¹) u⟫ =
        ⟪v, mat (dgCov A Λ z) v⟫ := by
      intro z
      rw [AuxLemma32.mat_mul_apply (A⁻¹ * dgCov A Λ z) A⁻¹,
          AuxLemma32.mat_mul_apply A⁻¹ (dgCov A Λ z),
          AuxLemma32.inner_mat_symm (AuxLemma32.inv_isHermitian hA.isHermitian),
          hAinv_u]
    change 0 ≤ 2 * fderiv ℝ (fderiv ℝ (fun y => -Real.log (liftDensity A Λ y))) x u u -
      2 * fderiv ℝ (fderiv ℝ (fun y => -Real.log (liftDensity A Λ y))) 0 u u at h2_nn
    rw [hhess x u u, hhess 0 u u, hquad_id x, hquad_id 0] at h2_nn
    have hpi2 : 0 < 8 * Real.pi ^ 2 := by positivity
    nlinarith [h2_nn, hpi2]
