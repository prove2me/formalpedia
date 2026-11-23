-- Prove2me | solution 1 for LogConcaveLattice.Lift.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:49:32.658659+00:00
-- url     : https://prove2.me/submissions/1a87bfe1-029d-47ff-9bde-b9b53c2951d3

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Gaussian

open scoped RealInnerProductSpace Matrix ENNReal
open LogConcaveLattice.Lift

namespace AuxLemma31

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

lemma summable_coord_gaussian {n : ℕ} (b : Fin n → V n) (hb : LinearIndependent ℝ b)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) {α : ℝ} (hα : 0 < α) (z : V n) :
    Summable (fun k : Fin n → ℤ => Real.exp (-α * ‖z + ∑ i : Fin n, k i • b i‖ ^ 2)) := by
  let B : Module.Basis (Fin n) ℝ (V n) := Module.Basis.mk hb (by rw [hspan])
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
  let β : ℝ := α / (2 * M)
  have hβ : 0 < β := by positivity
  have hdom : Summable (fun k : Fin n → ℤ =>
      Real.exp (α * ‖z‖ ^ 2) * Real.exp (-β * ∑ i : Fin n, (k i : ℝ) ^ 2)) :=
    (summable_pi_int_exp_neg_sum_sq n hβ).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => le_of_lt (Real.exp_pos _)) (fun k => ?_) hdom
  let v : V n := ∑ i : Fin n, k i • b i
  have hvB : v = ∑ i : Fin n, (k i : ℝ) • B i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    simp [B, Module.Basis.mk_apply]
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
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr hexp_ineq

lemma sqrt_exp (r : ℝ) : Real.sqrt (Real.exp r) = Real.exp (r / 2) := by
  rw [Real.sqrt_eq_iff_eq_sq (le_of_lt (Real.exp_pos r)) (le_of_lt (Real.exp_pos (r / 2))),
      sq, ← Real.exp_add]
  ring_nf

lemma quad_parallelogram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (a b : V n) :
    ⟪a, mat B a⟫ + ⟪b, mat B b⟫ =
      (1 / 2 : ℝ) * ⟪a + b, mat B (a + b)⟫ + (1 / 2 : ℝ) * ⟪a - b, mat B (a - b)⟫ := by
  have h1 : ⟪a + b, mat B (a + b)⟫ = ⟪a, mat B a⟫ + ⟪a, mat B b⟫ + ⟪b, mat B a⟫ + ⟪b, mat B b⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  have h2 : ⟪a - b, mat B (a - b)⟫ = ⟪a, mat B a⟫ - ⟪a, mat B b⟫ - ⟪b, mat B a⟫ + ⟪b, mat B b⟫ := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [h1, h2]
  ring

lemma rho_mul_eq_sqrt_mul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (a b : V n) :
    rho A a * rho A b = Real.sqrt (rho A (a + b)) * Real.sqrt (rho A (a - b)) := by
  rw [rho_eq_exp hA a, rho_eq_exp hA b, rho_eq_exp hA (a + b), rho_eq_exp hA (a - b)]
  rw [sqrt_exp, sqrt_exp, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hp := quad_parallelogram A⁻¹ a b
  nlinarith [hp, Real.pi_pos]

lemma sqrt_rho_mul_eq_rho_mul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (z u v : V n) :
    Real.sqrt (rho A (z + (u + v))) * Real.sqrt (rho A (z + (u - v))) =
      rho A (z + u) * rho A v := by
  have h1 : (z + u) + v = z + (u + v) := add_assoc z u v
  have h2 : (z + u) - v = z + (u - v) := add_sub_assoc z u v
  rw [← h1, ← h2, ← rho_mul_eq_sqrt_mul hA (z + u) v]

def cVec {n : ℕ} (r : Fin n → Fin 2) : Fin n → ℤ := fun i => ((r i : ℕ) : ℤ)

def parityEquiv (n : ℕ) :
    ((Fin n → Fin 2) × ((Fin n → ℤ) × (Fin n → ℤ))) ≃ ((Fin n → ℤ) × (Fin n → ℤ)) where
  toFun t :=
    (fun i => cVec t.1 i + t.2.1 i + t.2.2 i,
     fun i => t.2.1 i - t.2.2 i)
  invFun p :=
    (fun i => ⟨((p.1 i + p.2 i) % 2).toNat, by
        have h0 : 0 ≤ (p.1 i + p.2 i) % 2 := Int.emod_nonneg _ (by decide)
        have h2 : (p.1 i + p.2 i) % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
        omega⟩,
     (fun i => (p.1 i + p.2 i) / 2,
      fun i => (p.1 i - p.2 i) / 2))
  left_inv := by
    rintro ⟨r, q₁, q₂⟩
    refine Prod.ext (funext fun i => Fin.ext ?_) (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · have hr := (r i).isLt
      dsimp only [cVec]
      omega
    · have hr := (r i).isLt
      dsimp only [cVec]
      omega
    · have hr := (r i).isLt
      dsimp only [cVec]
      omega
  right_inv := by
    rintro ⟨k₁, k₂⟩
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · dsimp only [cVec]
      omega
    · dsimp only [cVec]
      omega

lemma summable_prod_of_nonneg {ι κ : Type*} {f : ι → ℝ} {g : κ → ℝ}
    (hf : Summable f) (hg : Summable g) (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ j, 0 ≤ g j) :
    Summable (fun p : ι × κ => f p.1 * g p.2) :=
  Summable.mul_of_nonneg hf hg hf0 hg0

lemma tsum_mul_tsum_nonneg {ι κ : Type*} {f : ι → ℝ} {g : κ → ℝ}
    (hf : Summable f) (hg : Summable g) (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ j, 0 ≤ g j) :
    (∑' x, f x) * (∑' y, g y) = ∑' p : ι × κ, f p.1 * g p.2 := by
  have hprod := summable_prod_of_nonneg hf hg hf0 hg0
  rw [hprod.tsum_prod]
  simp_rw [tsum_mul_left, ← tsum_mul_right]

lemma sqrt_rF_mul_eq {n : ℕ} {rF : V n → ℝ}
    (hpar : ∀ a b : V n, rF a * rF b = Real.sqrt (rF (a + b)) * Real.sqrt (rF (a - b)))
    (z u v : V n) :
    Real.sqrt (rF (z + (u + v))) * Real.sqrt (rF (z + (u - v))) = rF (z + u) * rF v := by
  rw [← add_assoc z u v, ← add_sub_assoc z u v, ← hpar (z + u) v]

lemma exists_parityEquiv (n : ℕ) :
    ∃ Φ : ((Fin n → Fin 2) × ((Fin n → ℤ) × (Fin n → ℤ))) ≃ ((Fin n → ℤ) × (Fin n → ℤ)),
      (∀ r (q₁ q₂ : Fin n → ℤ),
        (Φ (r, (q₁, q₂))).1 + (Φ (r, (q₁, q₂))).2 = fun i => cVec r i + 2 * q₁ i) ∧
      (∀ r (q₁ q₂ : Fin n → ℤ),
        (Φ (r, (q₁, q₂))).1 - (Φ (r, (q₁, q₂))).2 = fun i => cVec r i + 2 * q₂ i) := by
  refine ⟨parityEquiv n, ?_, ?_⟩
  · intro r q₁ q₂; ext i; simp [parityEquiv]; ring
  · intro r q₁ q₂; ext i; simp [parityEquiv]; ring

lemma coset_parallelogram_abstract {n : ℕ} (rF : V n → ℝ) (Lmap : (Fin n → ℤ) → V n)
    (hLmap_add : ∀ k₁ k₂, Lmap (k₁ + k₂) = Lmap k₁ + Lmap k₂)
    (hLmap_sub : ∀ k₁ k₂, Lmap (k₁ - k₂) = Lmap k₁ - Lmap k₂)
    (hrF_nn : ∀ w, 0 ≤ rF w)
    (hpar : ∀ a b, rF a * rF b = Real.sqrt (rF (a + b)) * Real.sqrt (rF (a - b)))
    (hsum_rho : ∀ z, Summable (fun k : Fin n → ℤ => rF (z + Lmap k)))
    (hsum_sqrt : ∀ z, Summable (fun k : Fin n → ℤ => Real.sqrt (rF (z + Lmap k))))
    (x y : V n) :
    (∑' k : Fin n → ℤ, rF (x + Lmap k)) ^ 2 * (∑' k : Fin n → ℤ, rF (y + Lmap k)) ^ 2 ≤
      (∑' k : Fin n → ℤ, rF (0 + Lmap k)) ^ 2 *
      (∑' k : Fin n → ℤ, rF ((x + y) + Lmap k)) *
      (∑' k : Fin n → ℤ, rF ((x - y) + Lmap k)) := by
  let S : V n → (Fin n → Fin 2) → ℝ := fun z r =>
    ∑' q : Fin n → ℤ, Real.sqrt (rF (z + Lmap (fun i => cVec r i + 2 * q i)))
  have hsum_S : ∀ (z : V n) (r : Fin n → Fin 2),
      Summable (fun q : Fin n → ℤ =>
        Real.sqrt (rF (z + Lmap (fun i => cVec r i + 2 * q i)))) := by
    intro z r
    have hinj : Function.Injective (fun q : Fin n → ℤ => fun i => cVec r i + 2 * q i) := by
      intro q₁ q₂ hq
      ext i
      have hi : cVec r i + 2 * q₁ i = cVec r i + 2 * q₂ i := congrFun hq i
      omega
    exact (hsum_sqrt z).comp_injective hinj
  obtain ⟨Φ, hΦ_add, hΦ_sub⟩ := exists_parityEquiv n
  have hid1 : (∑' k, rF (x + Lmap k)) * (∑' k, rF (y + Lmap k)) =
      ∑ r : Fin n → Fin 2, S (x + y) r * S (x - y) r := by
    rw [tsum_mul_tsum_nonneg (hsum_rho x) (hsum_rho y)
      (fun _ => hrF_nn _) (fun _ => hrF_nn _)]
    have hsum_prod := summable_prod_of_nonneg (hsum_rho x) (hsum_rho y)
      (fun _ => hrF_nn _) (fun _ => hrF_nn _)
    rw [← Φ.tsum_eq]
    have hsum_Φ := Φ.summable_iff.mpr hsum_prod
    have htsum_Φ : (∑' c, rF (x + Lmap (Φ c).1) * rF (y + Lmap (Φ c).2)) =
        ∑' r : Fin n → Fin 2, ∑' q : (Fin n → ℤ) × (Fin n → ℤ),
          rF (x + Lmap (Φ (r, q)).1) * rF (y + Lmap (Φ (r, q)).2) := hsum_Φ.tsum_prod
    rw [htsum_Φ, tsum_fintype]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hinner_eq : (fun q : (Fin n → ℤ) × (Fin n → ℤ) =>
          rF (x + Lmap (Φ (r, q)).1) * rF (y + Lmap (Φ (r, q)).2)) =
        (fun q : (Fin n → ℤ) × (Fin n → ℤ) =>
          Real.sqrt (rF ((x + y) + Lmap (fun i => cVec r i + 2 * q.1 i))) *
          Real.sqrt (rF ((x - y) + Lmap (fun i => cVec r i + 2 * q.2 i)))) := by
      ext ⟨q₁, q₂⟩
      rw [hpar]
      have ha : (x + Lmap (Φ (r, (q₁, q₂))).1) + (y + Lmap (Φ (r, (q₁, q₂))).2) =
          (x + y) + Lmap (fun i => cVec r i + 2 * q₁ i) := by
        rw [add_add_add_comm, ← hLmap_add, hΦ_add]
      have hb : (x + Lmap (Φ (r, (q₁, q₂))).1) - (y + Lmap (Φ (r, (q₁, q₂))).2) =
          (x - y) + Lmap (fun i => cVec r i + 2 * q₂ i) := by
        rw [add_sub_add_comm, ← hLmap_sub, hΦ_sub]
      rw [ha, hb]
    rw [hinner_eq, ← tsum_mul_tsum_nonneg (hsum_S (x + y) r) (hsum_S (x - y) r)
      (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)]
  have hid2 : ∀ z : V n, ∑ r : Fin n → Fin 2, S z r ^ 2 =
      (∑' k, rF (z + Lmap k)) * (∑' k, rF (0 + Lmap k)) := by
    intro z
    rw [tsum_mul_tsum_nonneg (hsum_rho z) (hsum_rho 0)
      (fun _ => hrF_nn _) (fun _ => hrF_nn _)]
    have hsum_prod := summable_prod_of_nonneg (hsum_rho z) (hsum_rho 0)
      (fun _ => hrF_nn _) (fun _ => hrF_nn _)
    rw [← Φ.tsum_eq]
    have hsum_Φ := Φ.summable_iff.mpr hsum_prod
    have htsum_Φ : (∑' c, rF (z + Lmap (Φ c).1) * rF (0 + Lmap (Φ c).2)) =
        ∑' r : Fin n → Fin 2, ∑' q : (Fin n → ℤ) × (Fin n → ℤ),
          rF (z + Lmap (Φ (r, q)).1) * rF (0 + Lmap (Φ (r, q)).2) := hsum_Φ.tsum_prod
    rw [htsum_Φ, tsum_fintype]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [sq, tsum_mul_tsum_nonneg (hsum_S z r) (hsum_S z r)
      (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)]
    congr 1
    ext ⟨q₁, q₂⟩
    rw [← hΦ_add r q₁ q₂, ← hΦ_sub r q₁ q₂, hLmap_add, hLmap_sub,
        sqrt_rF_mul_eq hpar z, zero_add]
  calc
    (∑' k, rF (x + Lmap k)) ^ 2 * (∑' k, rF (y + Lmap k)) ^ 2
        = ((∑' k, rF (x + Lmap k)) * (∑' k, rF (y + Lmap k))) ^ 2 := by ring
    _ = (∑ r : Fin n → Fin 2, S (x + y) r * S (x - y) r) ^ 2 := by rw [hid1]
    _ ≤ (∑ r : Fin n → Fin 2, S (x + y) r ^ 2) * (∑ r : Fin n → Fin 2, S (x - y) r ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = ((∑' k, rF ((x + y) + Lmap k)) * (∑' k, rF (0 + Lmap k))) *
        ((∑' k, rF ((x - y) + Lmap k)) * (∑' k, rF (0 + Lmap k))) := by
        rw [hid2 (x + y), hid2 (x - y)]
    _ = (∑' k, rF (0 + Lmap k)) ^ 2 *
        (∑' k, rF ((x + y) + Lmap k)) *
        (∑' k, rF ((x - y) + Lmap k)) := by ring

lemma exists_coord_basis {n : ℕ} (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (b : Fin n → V n) (eZ : (Fin n → ℤ) ≃ Λ),
      LinearIndependent ℝ b ∧
      Submodule.span ℝ (Set.range b) = ⊤ ∧
      ∀ k : Fin n → ℤ, (eZ k : V n) = ∑ i : Fin n, k i • b i := by
  let b₀ := Module.Free.chooseBasis ℤ Λ
  let B₀ := b₀.ofZLatticeBasis ℝ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = n := by
    rw [← Module.finrank_eq_card_basis B₀, finrank_euclideanSpace_fin]
  let idx : Fin n ≃ Module.Free.ChooseBasisIndex ℤ Λ :=
    (Fintype.equivFinOfCardEq hcard).symm
  let bZ : Module.Basis (Fin n) ℤ Λ := b₀.reindex idx.symm
  let B : Module.Basis (Fin n) ℝ (V n) := bZ.ofZLatticeBasis ℝ Λ
  let b : Fin n → V n := fun i => (bZ i : V n)
  have hb_eq_B : ∀ i : Fin n, b i = B i := fun i => by simp [b, B]
  have hb_li : LinearIndependent ℝ b := by
    have hB : b = ⇑B := funext hb_eq_B
    rw [hB]; exact B.linearIndependent
  have hb_span : Submodule.span ℝ (Set.range b) = ⊤ := by
    have hB : b = ⇑B := funext hb_eq_B
    rw [hB]; exact B.span_eq
  let eZ : (Fin n → ℤ) ≃ Λ :=
    { toFun := fun k => ∑ i : Fin n, k i • bZ i
      invFun := fun l => fun i => bZ.repr l i
      left_inv := fun k => by
        ext i
        dsimp only
        rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
        simp [Module.Basis.repr_self, Finsupp.single_apply]
      right_inv := fun l => bZ.sum_repr l }
  refine ⟨b, eZ, hb_li, hb_span, fun k => ?_⟩
  change ((∑ i : Fin n, k i • bZ i : Λ) : V n) = ∑ i : Fin n, k i • b i
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl

end AuxLemma31

theorem solution (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (x y : V n) :
    rhoCoset A Λ x ^ 2 * rhoCoset A Λ y ^ 2 ≤
      rhoCoset A Λ 0 ^ 2 * rhoCoset A Λ (x + y) * rhoCoset A Λ (x - y) := by
  obtain ⟨b, eZ, hb_li, hb_span, heZ_val⟩ := AuxLemma31.exists_coord_basis Λ
  let Lmap : (Fin n → ℤ) → V n := fun k => ∑ i : Fin n, k i • b i
  have hLmap_add : ∀ k₁ k₂ : Fin n → ℤ, Lmap (k₁ + k₂) = Lmap k₁ + Lmap k₂ := by
    intro k₁ k₂
    simp only [Lmap, Pi.add_apply, add_zsmul, Finset.sum_add_distrib]
  have hLmap_sub : ∀ k₁ k₂ : Fin n → ℤ, Lmap (k₁ - k₂) = Lmap k₁ - Lmap k₂ := by
    intro k₁ k₂
    simp only [Lmap, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ (k₁ i - k₂ i),
        ← Int.cast_smul_eq_zsmul ℝ (k₁ i),
        ← Int.cast_smul_eq_zsmul ℝ (k₂ i)]
    push_cast
    exact sub_smul (k₁ i : ℝ) (k₂ i : ℝ) (b i)
  obtain ⟨c, hcpos, hcoerc⟩ := AuxLemma31.exists_coercive_inv hA
  have hrho_nn : ∀ w : V n, 0 ≤ rho A w := fun w => by
    rw [AuxLemma31.rho_eq_exp hA]; positivity
  have hsum_rho : ∀ z : V n, Summable (fun k : Fin n → ℤ => rho A (z + Lmap k)) := by
    intro z
    have hdom := AuxLemma31.summable_coord_gaussian b hb_li hb_span
      (mul_pos Real.pi_pos hcpos) z
    refine Summable.of_nonneg_of_le (fun k => hrho_nn _) (fun k => ?_) hdom
    rw [AuxLemma31.rho_eq_exp hA]
    apply Real.exp_le_exp.mpr
    have h := hcoerc (z + Lmap k)
    nlinarith [Real.pi_pos]
  have hsum_sqrt : ∀ z : V n, Summable (fun k : Fin n → ℤ => Real.sqrt (rho A (z + Lmap k))) := by
    intro z
    have hdom := AuxLemma31.summable_coord_gaussian b hb_li hb_span
      (by positivity : 0 < Real.pi * c / 2) z
    refine Summable.of_nonneg_of_le (fun _ => Real.sqrt_nonneg _) (fun k => ?_) hdom
    rw [AuxLemma31.rho_eq_exp hA, AuxLemma31.sqrt_exp]
    apply Real.exp_le_exp.mpr
    have h := hcoerc (z + Lmap k)
    nlinarith [Real.pi_pos]
  have hcoset_eq : ∀ z : V n, rhoCoset A Λ z = ∑' k : Fin n → ℤ, rho A (z + Lmap k) := by
    intro z
    simp only [rhoCoset]
    rw [← eZ.tsum_eq]
    congr 1
    ext k
    rw [heZ_val]
  rw [hcoset_eq x, hcoset_eq y, hcoset_eq 0, hcoset_eq (x + y), hcoset_eq (x - y)]
  exact AuxLemma31.coset_parallelogram_abstract (rho A) Lmap hLmap_add hLmap_sub
    hrho_nn (AuxLemma31.rho_mul_eq_sqrt_mul hA) hsum_rho hsum_sqrt x y
