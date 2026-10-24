-- Prove2me | solution 1 for OAI.PermanentBorder.permanent_border_cubic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T20:03:24.881588+00:00
-- url     : https://prove2.me/submissions/cd4dd0cc-f987-4f11-a55a-66ba654cbcff

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_OAIQWPB000
import Theorems.Thm_OAI_PermanentBorder_HasBorderDeterminant_coefficientPolynomial
import Theorems.Thm_OAI_PermanentBorder_Polar_HasBorderDeterminant_smooth_lower_bound
import Theorems.Thm_OAI_PermanentBorder_exists_effective_critical_bound

section
-- module Solutions.OAIQW_PermanentBorder.Multigraded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

lemma project_mul {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (g : MvPolynomial σ K) (d : G) :
    weightedHomogeneousComponent w d (a * g) =
      a * weightedHomogeneousComponent w (d-e) g := by
  classical
  ext z
  simp only [coeff_weightedHomogeneousComponent, coeff_mul]
  have hi : (if Finsupp.weight w z = d then
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z, a.coeff xy.1 * g.coeff xy.2 else 0) =
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z,
        if Finsupp.weight w z = d then a.coeff xy.1 * g.coeff xy.2 else 0 := by
    rw [Finset.sum_ite_irrel]
    simp
  rw [hi]
  apply Finset.sum_congr rfl
  rintro ⟨x,y⟩ hxy
  have hsum : x+y=z := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
  by_cases hx : a.coeff x = 0
  · simp [hx]
  · have hwe : Finsupp.weight w x = e := ha hx
    have hcond : Finsupp.weight w z = d ↔ Finsupp.weight w y = d-e := by
      rw [← hsum, map_add, hwe]
      rw [eq_sub_iff_add_eq, add_comm]
    simp only [hcond]
    split_ifs <;> simp

end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SmoothSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

lemma homogeneous_aeval_scale {K L σ : Type*} [CommSemiring K] [CommSemiring L]
    [Algebra K L] {f : MvPolynomial σ K} {r : ℕ} (hf : f.IsHomogeneous r)
    (a : L) (x : σ → L) :
    aeval (fun i => a * x i) f = a^r * aeval x f := by
  classical
  conv_lhs => rw [← f.support_sum_monomial_coeff]
  conv_rhs => rw [← f.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hf.degree_eq_sum_deg_support hs]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma variable_power_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) (j : σ) :
    ∃ n : ℕ, (X j : MvPolynomial σ K)^n ∈ I := by
  have hx : (X j : MvPolynomial σ K) ∈ vanishingIdeal K (zeroLocus L I) := by
    intro y hy
    rw [hz y hy]
    simp
  rw [vanishingIdeal_zeroLocus_eq_radical] at hx
  exact hx

lemma monomial_mem_of_variable_powers {K σ : Type*} [CommSemiring K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (N : σ → ℕ)
    (hN : ∀ j, (X j : MvPolynomial σ K)^(N j) ∈ I)
    (s : σ →₀ ℕ) (c : K) (hs : (∑ j, N j) < s.degree) : monomial s c ∈ I := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, N j ≤ s j := by
    by_contra h
    have hle (j : σ) : s j ≤ N j := le_of_lt (not_le.mp (not_exists.mp h j))
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hle j)
    have hd : s.degree = ∑ j, s j := by
      exact Finsupp.sum_fintype s (fun _ n => n) (fun _ => rfl)
    rw [hd] at hs
    exact (not_le_of_gt hs) hh
  have he : Finsupp.single j (N j) + (s - Finsupp.single j (N j)) = s :=
    add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hj)
  rw [← he, monomial_single_add]
  exact I.mul_mem_right _ (hN j)

theorem homogeneous_piece_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) :
    ∃ D : ℕ, ∀ f : MvPolynomial σ K, f.IsHomogeneous D → f ∈ I := by
  classical
  choose N hN using variable_power_certificate I hz
  refine ⟨(∑ j, N j)+1, ?_⟩
  intro f hf
  rw [← f.support_sum_monomial_coeff]
  apply I.sum_mem
  intro s hs
  apply monomial_mem_of_variable_powers I N hN
  have hd : s.degree = (∑ j, N j)+1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hs)
  omega

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma intWeight_homogeneous {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f.IsHomogeneous d := by
  intro s hs
  change Finsupp.weight (fun _ : σ => (1 : ℕ)) s = d
  rw [← Finsupp.degree_eq_weight_one]
  exact_mod_cast (intWeight_degree s ▸ hf hs)

lemma homogeneous_ext_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    {f g : MvPolynomial σ K} {d : ℤ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d)
    (hg : g.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d)
    (h : ∀ s : DegreeIndex σ d, f.coeff s.val = g.coeff s.val) : f = g := by
  rw [homogeneous_sum_degree hf, homogeneous_sum_degree hg]
  exact Finset.sum_congr rfl (fun s _ => congrArg (monomial s.val) (h s))

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

lemma coeff_macaulayCombination (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) (s : DegreeIndex σ D) :
    (macaulayCombination e F D b).coeff s.val = (macaulayMatrix e F D).mulVec b s := by
  classical
  simp only [macaulayCombination, coeff_sum, coeff_smul, smul_eq_mul,
    macaulayMatrix, Matrix.mulVec, dotProduct, mul_comm]

lemma macaulayCombination_mem (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) :
    macaulayCombination e F D b ∈ Ideal.span (Set.range F) := by
  apply Ideal.sum_mem
  intro t _
  exact Submodule.smul_mem ((Ideal.span (Set.range F)).restrictScalars K) _
    (Ideal.mul_mem_right _ _ Ideal.mem_span_range_self)

lemma macaulayCombination_homogeneous (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) :
    (macaulayCombination e F D b).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D := by
  apply IsWeightedHomogeneous.sum
  intro t _
  apply (weightedHomogeneousSubmodule K (fun _ : σ => (1 : ℤ)) D).smul_mem
  have hm : (monomial t.2.val (1 : K)).IsWeightedHomogeneous
      (fun _ : σ => (1 : ℤ)) (D-e t.1) :=
    isWeightedHomogeneous_monomial _ _ _ ((intWeight_degree t.2.val).trans t.2.property)
  rw [mem_weightedHomogeneousSubmodule]
  simpa only [add_sub_cancel] using (hF t.1).mul hm

omit [Finite σ] [Fintype ι] in
lemma macaulayMatrix_map {L : Type*} [CommRing L] (φ : K →+* L)
    (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ) :
    macaulayMatrix e (fun i => map φ (F i)) D = (macaulayMatrix e F D).map φ := by
  classical
  ext s t
  change (map φ (F t.1) * monomial t.2.val 1).coeff s.val =
    φ ((F t.1 * monomial t.2.val 1).coeff s.val)
  rw [← coeff_map, map_mul, map_monomial, φ.map_one]

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

theorem macaulay_surjective_iff (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℤ) :
    Function.Surjective (macaulayMatrix e F D).mulVec ↔
      ∀ f : MvPolynomial σ K,
        f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D →
          f ∈ Ideal.span (Set.range F) := by
  classical
  constructor
  · intro hs f hf
    obtain ⟨b,hb⟩ := hs (fun s => f.coeff s.val)
    have he : macaulayCombination e F D b = f := by
      apply homogeneous_ext_degree (macaulayCombination_homogeneous e F hF D b) hf
      intro s
      rw [coeff_macaulayCombination, hb]
    rw [← he]
    exact macaulayCombination_mem e F D b
  · intro hs b
    let f := ∑ t : DegreeIndex σ D, monomial t.val (b t)
    have hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D :=
      sum_degree_homogeneous D b
    obtain ⟨g,hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs f hf)
    let g' := fun i => weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) (D-e i) (g i)
    have hg'h (i : ι) : (g' i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (D-e i) :=
      weightedHomogeneousComponent_mem _ _ _
    have he : ∑ i, F i * g' i = f := by
      simp_rw [g', ← PermanentBorder.Multigraded.project_mul _ (hF _)]
      rw [← map_sum]
      simp_rw [mul_comm (F _) _]
      rw [hg, weightedHomogeneousComponent_eq_self hf]
    let c : (Σ i : ι, DegreeIndex σ (D-e i)) → K := fun t => (g' t.1).coeff t.2.val
    have hc : macaulayCombination e F D c = f := by
      rw [macaulayCombination, Fintype.sum_sigma]
      rw [← he]
      apply Finset.sum_congr rfl
      intro i _
      rw [homogeneous_sum_degree (hg'h i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      change (g' i).coeff s.val • (F i * monomial s.val 1) =
        F i * monomial s.val ((g' i).coeff s.val)
      rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
    refine ⟨c, ?_⟩
    ext s
    rw [← coeff_macaulayCombination, hc]
    exact coeff_sum_degree D b s

end Surjectivity
end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.RankTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma exists_matrix_right_inverse {K α β : Type*} [Field K] [Fintype α] [Fintype β] [DecidableEq α]
    (A : Matrix α β K) (hA : Function.Surjective A.mulVec) :
    ∃ B : Matrix β α K, A * B = 1 := by
  classical
  choose b hb using fun i : α => hA (Pi.single i 1)
  refine ⟨fun j i => b i j, ?_⟩
  ext i j
  change (A.mulVec (b j)) i = (1 : Matrix α α K) i j
  rw [hb]
  simp [Matrix.one_apply, Pi.single_apply]

theorem integer_polynomial_rank_transfer {K L σ α β : Type*}
    [Field K] [Field L] [CharZero L] [Infinite L] [Fintype α] [Fintype β]
    (P : Matrix α β (MvPolynomial σ ℤ)) (x : σ → K)
    (hP : Function.Surjective (P.map (eval₂Hom (Int.castRingHom K) x)).mulVec) :
    ∃ y : σ → L,
      Function.Surjective (P.map (eval₂Hom (Int.castRingHom L) y)).mulVec := by
  classical
  let τ := σ ⊕ (β × α)
  let A : Matrix α β (MvPolynomial τ ℤ) := P.map (rename Sum.inl)
  let B : Matrix β α (MvPolynomial τ ℤ) := fun i j => X (Sum.inr (i,j))
  let p : MvPolynomial τ ℤ := (A*B).det
  obtain ⟨b,hb⟩ := exists_matrix_right_inverse _ hP
  let z : τ → K := Sum.elim x (fun ij => b ij.1 ij.2)
  let φ : MvPolynomial τ ℤ →+* K := eval₂Hom (Int.castRingHom K) z
  have hA : A.map φ = P.map (eval₂Hom (Int.castRingHom K) x) := by
    ext i j
    simp [A, φ, z, Matrix.map_apply, eval₂_rename, Function.comp_def]
  have hB : B.map φ = b := by
    ext i j
    change φ (X (Sum.inr (i,j))) = b i j
    exact eval₂_X _ _ _
  have hp : φ p = 1 := by
    rw [show φ p = (φ.mapMatrix (A*B)).det from RingHom.map_det φ (A*B)]
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, hA, hB, hb]
    exact Matrix.det_one
  have hpn : p ≠ 0 := by
    intro h
    have : (0 : K) = 1 := by simpa only [h, map_zero] using hp
    exact zero_ne_one this
  let pL : MvPolynomial τ L := map (Int.castRingHom L) p
  have hpLn : pL ≠ 0 := by
    simpa only [map_zero] using
      (MvPolynomial.map_injective (Int.castRingHom L) Int.cast_injective).ne hpn
  obtain ⟨w,hw⟩ : ∃ w : τ → L, eval w pL ≠ 0 := by
    by_contra h
    apply hpLn
    apply MvPolynomial.funext
    intro w
    simp only [map_zero]
    exact not_not.mp (not_exists.mp h w)
  let ψ : MvPolynomial τ ℤ →+* L := eval₂Hom (Int.castRingHom L) w
  have hψ : ψ p ≠ 0 := by
    simpa only [pL, eval_map, ψ, coe_eval₂Hom] using hw
  have hu : IsUnit ((A*B).map ψ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.mpr hψ
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  refine ⟨fun i => w (Sum.inl i), ?_⟩
  have hAL : A.map ψ = P.map (eval₂Hom (Int.castRingHom L) (fun i => w (Sum.inl i))) := by
    ext i j
    simp [A, ψ, Matrix.map_apply, eval₂_rename, Function.comp_def]
  intro v
  obtain ⟨t,ht⟩ := hs v
  refine ⟨(B.map ψ).mulVec t, ?_⟩
  rw [← hAL, Matrix.mulVec_mulVec]
  simpa only [Matrix.map_mul] using ht

end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

theorem support_subset_exponentCube {P : Poly σ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    P.support ⊆ exponentCube n := by
  intro d hd
  rw [mem_exponentCube]
  intro i
  exact (monomial_le_degreeOf i hd).trans ((degreeOf_le_totalDegree P i).trans hP)

theorem sum_over_exponentCube {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) :
    P = ∑ d ∈ exponentCube n, monomial d (P.coeff d) := by
  calc
    P = ∑ d ∈ P.support, monomial d (P.coeff d) := MvPolynomial.as_sum P
    _ = _ := ?_
  apply Finset.sum_subset hP
  intro d _ hd
  simp only [notMem_support_iff.mp hd, map_zero]

theorem coeff_linear_map_cube (F : Poly σ →ₗ[ℂ] Poly τ) {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) (e : τ →₀ ℕ) :
    (F P).coeff e = ∑ d ∈ exponentCube n,
      P.coeff d * (F (monomial d 1)).coeff e := by
  conv_lhs => rw [sum_over_exponentCube hP]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by simp [smul_monomial],
    map_smul, coeff_smul, smul_eq_mul]

theorem support_subset_cube_of_limit {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    p.support ⊆ exponentCube n := by
  classical
  intro d hd
  by_contra hn
  have hz : ∀ j, (P j).coeff d = 0 := by
    intro j
    apply notMem_support_iff.mp
    exact fun hj => hn (hP j hj)
  have ht : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (p.coeff d)) := by
    simpa only [hz] using hp d
  have he : p.coeff d = 0 := (tendsto_nhds_unique tendsto_const_nhds ht).symm
  exact mem_support_iff.mp hd he

theorem coefficientwise_linear_map_limit (F : Poly σ →ₗ[ℂ] Poly τ)
    {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    ∀ e, Tendsto (fun j => (F (P j)).coeff e) atTop (𝓝 ((F p).coeff e)) := by
  intro e
  have hc := support_subset_cube_of_limit hP hp
  have ht := tendsto_finsetSum (exponentCube (σ := σ) n)
    (fun d _ => (hp d).mul (tendsto_const_nhds (x := (F (monomial d 1)).coeff e)))
  convert ht using 1
  · funext j
    exact coeff_linear_map_cube F (hP j) e
  · congr 1
    exact coeff_linear_map_cube F hc e
end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

theorem degree_affine_form (b : ℂ) (a : σ → ℂ) :
    (C b + ∑ v : σ, C (a v) * X v : Poly σ).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro v _
    exact (totalDegree_mul _ _).trans (by simp)

theorem degree_affineMatrixPolynomial (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    (affineMatrixPolynomial n A₀ A).totalDegree ≤ n := by
  classical
  unfold affineMatrixPolynomial
  have he := Matrix.det_apply (show Matrix (Fin n) (Fin n) (Poly σ) from
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  rw [he]
  apply totalDegree_finsetSum_le
  intro s _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun i _ => degree_affine_form _ _
    _ = n := by simp
end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem affineSubstitution_matrix (b : σ → ℂ) (B : σ → τ → ℂ)
    (n : ℕ) (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    affineSubstitution b B (affineMatrixPolynomial n A₀ A) =
      affineMatrixPolynomial n
        (fun i j => A₀ i j + ∑ v : σ, A v i j * b v)
        (fun w i j => ∑ v : σ, A v i j * B v w) := by
  classical
  unfold affineMatrixPolynomial
  have he := RingHom.map_det (affineSubstitution b B).toRingHom
    (show Matrix (Fin n) (Fin n) (Poly σ) from
      fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  refine he.trans ?_
  apply congrArg Matrix.det
  funext i j
  change (affineSubstitution b B) (C (A₀ i j) + ∑ v, C (A v i j) * X v) =
    C (A₀ i j + ∑ v, A v i j * b v) + ∑ w, C (∑ v, A v i j * B v w) * X w
  simp only [affineSubstitution, map_add, map_sum, map_mul,
    aeval_C, aeval_X, algebraMap_eq]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, ← map_mul]
  rw [← add_assoc]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, map_mul, mul_assoc]

theorem HasBorderDeterminant.affineSubstitution {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (b : σ → ℂ) (B : σ → τ → ℂ) :
    HasBorderDeterminant n (affineSubstitution b B p) := by
  classical
  obtain ⟨hn, A₀, A, hlim⟩ := h
  refine ⟨hn,
    (fun l i j => A₀ l i j + ∑ v : σ, A l v i j * b v),
    (fun l w i j => ∑ v : σ, A l v i j * B v w), ?_⟩
  have hf := coefficientwise_linear_map_limit (PermanentBorder.affineSubstitution b B).toLinearMap
    (fun l => support_subset_exponentCube (degree_affineMatrixPolynomial n (A₀ l) (A l))) hlim
  intro e
  simpa only [AlgHom.toLinearMap_apply, affineSubstitution_matrix] using hf e
end AffineSubstitution
end PermanentBorder

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Selector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [CommSemiring R]
 theorem sumRingEquiv_monomial (d : A →₀ ℕ) (e : B →₀ ℕ) (r : R) :
    sumRingEquiv R A B (monomial (d.sumElim e) r) = monomial d (monomial e r) := by
  simp [sumRingEquiv, monomial]
 theorem coeff_nested (p : MvPolynomial (A ⊕ B) R) (d : A →₀ ℕ) (e : B →₀ ℕ) :
    p.coeff (d.sumElim e) = ((sumRingEquiv R A B p).coeff d).coeff e := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [MvPolynomial.coeff_add, Finsupp.add_apply, map_add, hp, hq]
  | monomial f r =>
    obtain ⟨⟨a, b⟩, rfl⟩ := Finsupp.sumFinsuppAddEquivProdFinsupp.symm.surjective f
    have hab : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b) = a.sumElim b := by
      ext x; cases x <;> rfl
    rw [hab, sumRingEquiv_monomial]
    simp only [coeff_monomial]
    have habde : a.sumElim b = d.sumElim e ↔ a = d ∧ b = e := by
      constructor
      · intro h; constructor
        · ext x; exact congrArg (fun f => f (Sum.inl x)) h
        · ext x; exact congrArg (fun f => f (Sum.inr x)) h
      · rintro ⟨rfl, rfl⟩; rfl
    simp only [habde]
    by_cases ha : a = d <;> by_cases hb : b = e <;> simp [ha, hb]
end PermanentBorder.Selector

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.HomogeneousPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]
 theorem weight_one_sumElim (d : A →₀ ℕ) (e : B →₀ ℕ) :
    Finsupp.weight (1 : A ⊕ B → ℕ) (d.sumElim e) =
      Finsupp.weight (1 : A → ℕ) d + Finsupp.weight (1 : B → ℕ) e := by
  simp only [Finsupp.weight_eq_sum, Pi.one_apply, smul_eq_mul, mul_one,
    Fintype.sum_sum_type, Finsupp.sumElim_inl, Finsupp.sumElim_inr]

 theorem homogeneous_coefficient {p : MvPolynomial (A ⊕ B) R} {r : ℕ}
    (hp : p.IsHomogeneous r) (d : A →₀ ℕ) :
    ((sumRingEquiv R A B p).coeff d).IsHomogeneous
      (r - Finsupp.weight (1 : A → ℕ) d) := by
  intro e he
  rw [← coeff_nested] at he
  have hh := hp he
  rw [weight_one_sumElim] at hh
  omega

variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem universalHomogeneousPencil_permanent (θ : I → R) :
    (universalHomogeneousPencil θ).permanent.IsHomogeneous (Fintype.card I) := by
  classical
  unfold Matrix.permanent
  apply IsHomogeneous.sum
  intro σ _
  convert IsHomogeneous.prod Finset.univ
    (fun i => universalHomogeneousPencil θ (σ i) i) (fun _ => 1) ?_ using 1 <;> try simp
  intro i _
  apply IsHomogeneous.add (isHomogeneous_X _ _)
  split_ifs
  · exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)
  · exact isHomogeneous_zero _ _ _

 theorem coefficientPolynomial_homogeneous (θ : I → R) (q : ℕ) :
    (diagonalCoefficient (Matrix.of fun i j => (X (i,j) : MvPolynomial (I × I) R))
      (fun i => C (θ i)) q).IsHomogeneous (Fintype.card I - 2*q) := by
  classical
  have hm : sumRingEquiv R (Fin 2) (I × I) (universalHomogeneousPencil θ).permanent =
      ((Matrix.of fun i j => C (X (i,j))) +
        Matrix.diagonal (fun i => X (0 : Fin 2) + C (C (θ i))*X 1)).permanent := by
    unfold Matrix.permanent
    simp only [map_sum, map_prod]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : σ i = i
    · simp [universalHomogeneousPencil, hi]
    · simp [universalHomogeneousPencil, hi]
  have hw : Finsupp.weight (1 : Fin 2 → ℕ) (countIndex q) = 2*q := by
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, countIndex]
  have h := homogeneous_coefficient (universalHomogeneousPencil_permanent θ) (countIndex q)
  rw [hm, hw] at h
  exact h
end PermanentBorder.Selector

namespace PermanentBorder
open MvPolynomial

 theorem coefficientPolynomial_homogeneous (k q : ℕ) (θ : Fin k → ℂ) :
    (coefficientPolynomial k q θ).IsHomogeneous (k-2*q) := by
  simpa only [coefficientPolynomial,Fintype.card_fin] using
    Selector.coefficientPolynomial_homogeneous θ q

end PermanentBorder
namespace PermanentBorder.Selector
open MvPolynomial

lemma diagonalCoefficient_map {I R S : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (M : Matrix I I R) (θ : I → R) (q : ℕ) :
    φ (diagonalCoefficient M θ q) =
      diagonalCoefficient (fun i j => φ (M i j)) (fun i => φ (θ i)) q := by
  classical
  unfold diagonalCoefficient
  rw [← coeff_map]
  apply congrArg (fun polynomial : MvPolynomial (Fin 2) S => polynomial.coeff (countIndex q))
  unfold Matrix.permanent
  simp only [map_sum,map_prod]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.prod_congr rfl
  intro i _
  simp only [Matrix.add_apply, Matrix.of_apply,Matrix.diagonal_apply,map_add,map_C]
  split_ifs <;> simp

lemma integralCoefficientFamily_homogeneous (k q : ℕ) :
    (integralCoefficientFamily k q).IsHomogeneous (k-2*q) := by
  simpa only [integralCoefficientFamily,Fintype.card_fin] using
    coefficientPolynomial_homogeneous (fun i : Fin k => (X i : MvPolynomial (Fin k) ℤ)) q

lemma integralCoefficientFamily_specialize {K : Type*} [CommRing K]
    (k q : ℕ) (θ : Fin k → K) :
    map (eval₂Hom (Int.castRingHom K) θ) (integralCoefficientFamily k q) =
      diagonalCoefficient (Matrix.of fun i j => (X (i,j) : MvPolynomial (Variables k) K))
        (fun i => C (θ i)) q := by
  unfold integralCoefficientFamily
  rw [diagonalCoefficient_map]
  simp only [Matrix.of_apply,map_X,map_C,eval₂Hom_X']
  rfl

lemma integralCoefficientFamily_complex (k q : ℕ) (θ : Fin k → ℂ) :
    map (eval₂Hom (Int.castRingHom ℂ) θ) (integralCoefficientFamily k q) =
      coefficientPolynomial k q θ := by
  exact integralCoefficientFamily_specialize k q θ
end PermanentBorder.Selector

namespace PermanentBorder.AlgebraicDimension

open Order

theorem krullDim_le_of_injective_integral {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (hi : f.IsIntegral) :
    ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hi⟩
  change (⨆ l : LTSeries (PrimeSpectrum R), (l.length : WithBot ℕ∞)) ≤ _
  apply iSup_le
  intro l
  have h0 : (⊥ : Ideal S).comap (algebraMap R S) ≤ l.head.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    change RingHom.ker f ≤ _
    rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
    exact bot_le
  obtain ⟨P, _, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    l.head.asIdeal (⊥ : Ideal S) h0
  let : P.IsPrime := hP
  let : P.LiesOver l.head.asIdeal := ⟨hPc.symm⟩
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_krullDim_iff.mpr ⟨L, hlen⟩

universe u

theorem trdeg_le_of_krullDim_le {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (n : ℕ) (h : ringKrullDim A ≤ n) :
    Algebra.trdeg K A ≤ (n : Cardinal) := by
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  let : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq fun k => (g.commutes k).symm
  let : Algebra.IsIntegral R A := ⟨hint⟩
  have hs : s ≤ n := by
    have hd := (krullDim_le_of_injective_integral g.toRingHom hg hint).trans h
    simpa using hd
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  have ht : Algebra.trdeg K A = s := by
    rw [← trdeg_add_eq K R (A := A), trdeg_eq_zero (R := R), add_zero]
    simp [R]
  rw [ht]
  exact_mod_cast hs

theorem field_image_trdeg_le {K A L : Type u} [Field K] [CommRing A]
    [Field L] [Algebra K A] [Algebra K L] [Algebra.FiniteType K A]
    (n : ℕ) (h : ringKrullDim A ≤ n) (f : A →ₐ[K] L) :
    Algebra.trdeg K f.range ≤ (n : Cardinal) := by
  let : Algebra.FiniteType K f.range := Algebra.FiniteType.of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  have hd : ringKrullDim f.range ≤ ringKrullDim A :=
    ringKrullDim_le_of_surjective f.rangeRestrict.toRingHom f.rangeRestrict_surjective
  exact trdeg_le_of_krullDim_le n (hd.trans h)

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem point_field_trdeg_le {K L : Type u} [Field K] [Field L] [Algebra K L]
    {v : ℕ} (I : Ideal (MvPolynomial (Fin v) K)) (n : ℕ)
    (h : ringKrullDim (MvPolynomial (Fin v) K ⧸ I) ≤ n)
    (x : Fin v → L) (hx : ∀ p ∈ I, MvPolynomial.aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤ (n : Cardinal) := by
  let f := Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) hx
  have hr : f.range = Algebra.adjoin K (Set.range x) := by
    rw [← MvPolynomial.aeval_range]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨Ideal.Quotient.mk I p, rfl⟩
  have ht := field_image_trdeg_le n h f
  rw [hr] at ht
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact ht

end PermanentBorder.AlgebraicDimension

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

open scoped IntermediateField.algebraAdjoinAdjoin in
lemma field_adjoin_trdeg_le {κ : Type*} [Fintype κ] (x : κ → L) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) ≤
      (Fintype.card κ : Cardinal) := by
  let A := Algebra.adjoin K (Set.range x)
  let y : κ → A := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have htop : Algebra.adjoin K (Set.range y) = ⊤ := by
    apply Subalgebra.map_injective (show Function.Injective A.val from Subtype.val_injective)
    rw [AlgHom.map_adjoin, Algebra.map_top, A.range_val, ← Set.range_comp]
    rfl
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range y)) A := by
    constructor
    intro a
    have ha : a ∈ Algebra.adjoin K (Set.range y) := by rw [htop]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin K (Set.range y)) ⟨a, ha⟩
  have hA : Algebra.trdeg K A ≤ (Fintype.card κ : Cardinal) := by
    calc
      Algebra.trdeg K A ≤ Cardinal.mk (Set.range y) :=
        Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range y)
      _ ≤ Fintype.card κ := by
        simpa using (Cardinal.mk_range_le_lift (f := y))
  rw [← trdeg_add_eq K A, trdeg_eq_zero (R := A), add_zero]
  exact hA

lemma add_parameters {κ : Type*} [Fintype κ] (F : IntermediateField K L)
    (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal)) (z : κ → L) :
    ∃ E : IntermediateField K L,
      F ≤ E ∧ (∀ i, z i ∈ E) ∧
      Algebra.trdeg K E ≤ (n + Fintype.card κ : ℕ) := by
  let E := IntermediateField.adjoin F (Set.range z)
  let : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).mpr
    (algebraMap F E).injective
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨E.restrictScalars K, ?_, ?_, ?_⟩
  · intro x hx
    exact E.algebraMap_mem ⟨x, hx⟩
  · intro i
    exact IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
  · change Algebra.trdeg K E ≤ _
    rw [← trdeg_add_eq K F]
    exact (add_le_add hF (field_adjoin_trdeg_le (K := F) z)).trans_eq (by simp)

lemma independent_card_le {κ : Type*} [Fintype κ] (H : κ → L)
    (hH : AlgebraicIndependent K H) (F : IntermediateField K L)
    (hF : ∀ i, H i ∈ F) (n : ℕ) (ht : Algebra.trdeg K F ≤ (n : Cardinal)) :
    Fintype.card κ ≤ n := by
  let x : κ → F := fun i => ⟨H i, hF i⟩
  have hx : AlgebraicIndependent K x := hH.of_comp F.val
  have hc := hx.lift_cardinalMk_le_trdeg.trans (Cardinal.lift_le.mpr ht)
  simpa using hc

end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Transcendence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma aeval_mem_field {v : ℕ} (F : IntermediateField K L)
    (x : Fin v → L) (hx : ∀ i, x i ∈ F) (p : MvPolynomial (Fin v) K) :
    aeval x p ∈ F := by
  have h : (aeval (R := K) x).range ≤ F.toSubalgebra := by
    rw [aeval_range, Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hx i
  exact h ⟨p, rfl⟩

lemma pivot_mem {ι : Type*} [Fintype ι] (F : IntermediateField K L)
    (a b : ι → L) (j : ι) (ha : ∀ i, a i ∈ F) (hj : a j ≠ 0)
    (hb : ∀ i, i ≠ j → b i ∈ F) (hs : (∑ i, a i * b i) ∈ F) :
    b j ∈ F := by
  classical
  have he : (∑ i ∈ Finset.univ.erase j, a i * b i) ∈ F := by
    apply F.sum_mem
    intro i hi
    exact F.mul_mem (ha i) (hb i (Finset.mem_erase.mp hi).1)
  have hp : a j * b j ∈ F := by
    have hh := F.sub_mem hs he
    convert hh using 1
    symm
    exact sub_eq_of_eq_add (by
      simpa only [add_comm] using (Finset.sum_erase_add Finset.univ
        (fun i => a i * b i) (Finset.mem_univ j)).symm)
  simpa [mul_div_cancel_left₀, hj] using F.div_mem hp (ha j)

theorem normalized_avoidance {v d n : ℕ}
    (I : Ideal (MvPolynomial (Fin v) K))
    (hdim : ringKrullDim (MvPolynomial (Fin v) K ⧸ I) ≤ n)
    (hn : n + d < v)
    (H : Fin v × Fin (d+1) → L) (hH : AlgebraicIndependent K H)
    (x : Fin v → L) (y : Fin (d+1) → L) (j : Fin (d+1)) (hyj : y j = 1)
    (hxy : ∀ i, ∑ c, y c * H (i,c) = x i)
    (hx : ∀ p ∈ I, aeval x p = 0) : False := by
  classical
  let C := {c : Fin (d+1) // c ≠ j}
  let κ := C ⊕ (Fin v × C)
  let z : κ → L := Sum.elim (fun c => y c.val) (fun ic => H (ic.1,ic.2.val))
  let F := IntermediateField.adjoin K (Set.range x)
  have hF : Algebra.trdeg K F ≤ (n : Cardinal) :=
    AlgebraicDimension.point_field_trdeg_le I n hdim x hx
  obtain ⟨E, hFE, hz, ht⟩ := add_parameters F n hF z
  have hxE (i : Fin v) : x i ∈ E :=
    hFE (IntermediateField.subset_adjoin K _ (Set.mem_range_self i))
  have hyE (c : Fin (d+1)) : y c ∈ E := by
    by_cases hc : c = j
    · rw [hc, hyj]
      exact E.one_mem
    · exact hz (Sum.inl ⟨c,hc⟩)
  have hHE (ic : Fin v × Fin (d+1)) : H ic ∈ E := by
    obtain ⟨i,c⟩ := ic
    by_cases hc : c = j
    · subst c
      apply pivot_mem E y (fun c => H (i,c)) j hyE
      · simp [hyj]
      · intro a ha
        exact hz (Sum.inr (i,⟨a,ha⟩))
      · rw [hxy]
        exact hxE i
    · exact hz (Sum.inr (i,⟨c,hc⟩))
  have hC : Fintype.card C = d := by
    simp [C, Fintype.card_subtype_compl]
  have hκ : Fintype.card κ = d + v*d := by
    simp [κ, hC]
  have hc := independent_card_le H hH E hHE _ ht
  simp only [Fintype.card_prod, Fintype.card_fin, hκ] at hc
  nlinarith

end PermanentBorder.SliceParameters

namespace PermanentBorder.ParameterBounds
open Algebra MvPolynomial
universe u
variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]

theorem trdeg_lt_of_relation {n : ℕ} (x : Fin n → A)
    [Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A]
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hx : aeval x p = 0) :
    Algebra.trdeg K A < (n : Cardinal) := by
  by_contra! ht
  have ht' : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤
      Cardinal.lift.{0} (Algebra.trdeg K A) := by simpa using ht
  have hi := (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K x ht').1
  apply hp
  exact hi (by simpa using hx)

theorem adjoin_trdeg_lt_of_relation {n : ℕ} (x : Fin n → A)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hx : aeval x p = 0) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range x)) < (n : Cardinal) := by
  let B := Algebra.adjoin K (Set.range x)
  let y : Fin n → B := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have htop : Algebra.adjoin K (Set.range y) = ⊤ := by
    apply Subalgebra.map_injective (show Function.Injective B.val from Subtype.val_injective)
    rw [AlgHom.map_adjoin, Algebra.map_top, B.range_val, ← Set.range_comp]
    rfl
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range y)) B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin K (Set.range y) := by rw [htop]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin K (Set.range y)) ⟨b, hb⟩
  apply trdeg_lt_of_relation y p hp
  apply (show Function.Injective B.val from Subtype.val_injective)
  rw [map_zero, MvPolynomial.comp_aeval_apply]
  exact hx

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_lt_of_relation {L : Type u} [Field L] [Algebra K L]
    {n : ℕ} (x : Fin n → L) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) < (n : Cardinal) := by
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact adjoin_trdeg_lt_of_relation x p hp hx

end PermanentBorder.ParameterBounds

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem normalized_tangency_impossible {v d : ℕ}
    (f : MvPolynomial (Fin (v+1)) K) (hf : f ≠ 0)
    (H : Fin (v+1) × Fin (d+1) → L) (hH : AlgebraicIndependent K H)
    (x : Fin (v+1) → L) (y : Fin (d+1) → L) (j : Fin (d+1)) (hyj : y j = 1)
    (hxy : ∀ i, ∑ c, y c * H (i,c) = x i)
    (hfx : aeval x f = 0)
    (i₀ : Fin (v+1)) (hp : aeval x (pderiv i₀ f) ≠ 0)
    (horth : ∀ c, ∑ i, aeval x (pderiv i f) * H (i,c) = 0) : False := by
  classical
  let C := {c : Fin (d+1) // c ≠ j}
  let R := {i : Fin (v+1) // i ≠ i₀}
  let κ := C ⊕ (R × C)
  let z : κ → L := Sum.elim (fun c => y c.val) (fun ic => H (ic.1.val,ic.2.val))
  let F := IntermediateField.adjoin K (Set.range x)
  have hF : Algebra.trdeg K F ≤ (v : Cardinal) := by
    apply Cardinal.lt_natCast_add_one_iff.mp
    simpa only [Nat.cast_add, Nat.cast_one] using
      ParameterBounds.field_adjoin_trdeg_lt_of_relation x f hf hfx
  obtain ⟨E, hFE, hz, ht⟩ := add_parameters F v hF z
  have hxE (i : Fin (v+1)) : x i ∈ E :=
    hFE (IntermediateField.subset_adjoin K _ (Set.mem_range_self i))
  have hyE (c : Fin (d+1)) : y c ∈ E := by
    by_cases hc : c = j
    · rw [hc, hyj]
      exact E.one_mem
    · exact hz (Sum.inl ⟨c,hc⟩)
  have hpE (i : Fin (v+1)) : aeval x (pderiv i f) ∈ E :=
    aeval_mem_field E x hxE _
  have hHother (i : Fin (v+1)) (c : Fin (d+1)) (hc : c ≠ j) : H (i,c) ∈ E := by
    by_cases hi : i = i₀
    · subst i
      apply pivot_mem E (fun i => aeval x (pderiv i f)) (fun i => H (i,c)) i₀ hpE hp
      · intro a ha
        exact hz (Sum.inr (⟨a,ha⟩,⟨c,hc⟩))
      · rw [horth]
        exact E.zero_mem
    · exact hz (Sum.inr (⟨i,hi⟩,⟨c,hc⟩))
  have hHE (ic : Fin (v+1) × Fin (d+1)) : H ic ∈ E := by
    obtain ⟨i,c⟩ := ic
    by_cases hc : c = j
    · subst c
      apply pivot_mem E y (fun c => H (i,c)) j hyE
      · simp [hyj]
      · exact hHother i
      · rw [hxy]
        exact hxE i
    · exact hHother i c hc
  have hC : Fintype.card C = d := by
    simp [C, Fintype.card_subtype_compl]
  have hR : Fintype.card R = v := by
    simp [R, Fintype.card_subtype_compl]
  have hκ : Fintype.card κ = d + v*d := by
    simp [κ, hC, hR]
  have hc := independent_card_le H hH E hHE _ ht
  simp only [Fintype.card_prod, Fintype.card_fin, hκ] at hc
  nlinarith

theorem generic_normalized_slice {v d n : ℕ}
    (f : MvPolynomial (Fin (v+1)) K) (hf : f ≠ 0)
    (hdim : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i f))) ≤ n)
    (hn : n + d < v+1)
    (H : Fin (v+1) × Fin (d+1) → L) (hH : AlgebraicIndependent K H)
    (y : Fin (d+1) → L) (j : Fin (d+1)) (hyj : y j = 1) :
    let x := fun i => ∑ c, y c * H (i,c)
    aeval x f = 0 → ¬ ∀ c, ∑ i, aeval x (pderiv i f) * H (i,c) = 0 := by
  intro x hf0 ho
  by_cases hp : ∀ i, aeval x (pderiv i f) = 0
  · apply normalized_avoidance (Ideal.span (Set.range (fun i => pderiv i f)))
      hdim hn H hH x y j hyj (fun _ => rfl)
    have hker : Ideal.span (Set.range (fun i => pderiv i f)) ≤
        RingHom.ker (aeval x) := by
      rw [Ideal.span_le, Set.range_subset_iff]
      exact hp
    exact fun p h => hker h
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hp
    exact normalized_tangency_impossible f hf H hH x y j hyj (fun _ => rfl) hf0 i₀ hi₀ ho

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem generic_homogeneous_slice {v d n r : ℕ}
    (f : MvPolynomial (Fin (v+1)) K) (hf : f ≠ 0) (hhom : f.IsHomogeneous r)
    (hdim : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i f))) ≤ n)
    (hn : n + d < v+1)
    (H : Fin (v+1) × Fin (d+1) → L) (hH : AlgebraicIndependent K H)
    (y : Fin (d+1) → L)
    (hzero : aeval (fun i => ∑ c, y c * H (i,c)) f = 0)
    (htangent : ∀ c, ∑ i,
      aeval (fun i => ∑ c, y c * H (i,c)) (pderiv i f) * H (i,c) = 0) : y = 0 := by
  classical
  by_contra hy
  obtain ⟨j,hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    apply hy
    ext j
    exact not_not.mp (not_exists.mp h j)
  let a := (y j)⁻¹
  let y' := fun c => a * y c
  have hj' : y' j = 1 := inv_mul_cancel₀ hj
  have hscale : (fun i => ∑ c, y' c * H (i,c)) =
      (fun i => a * (∑ c, y c * H (i,c))) := by
    ext i
    simp [y', Finset.mul_sum, mul_assoc]
  apply generic_normalized_slice f hf hdim hn H hH y' j hj'
  · rw [hscale, homogeneous_aeval_scale hhom, hzero, mul_zero]
  · intro c
    rw [hscale]
    simp_rw [homogeneous_aeval_scale hhom.pderiv, mul_assoc, ← Finset.mul_sum]
    rw [htangent c, mul_zero]

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
variable {K α β : Type*} [CommRing K] [Fintype β]

lemma sectionForm_homogeneous (H : α × β → K) (i : α) :
    (sectionForm H i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro c _
  exact isHomogeneous_C_mul_X _ _

lemma linearSection_homogeneous (H : α × β → K) {f : MvPolynomial α K} {r : ℕ}
    (hf : f.IsHomogeneous r) : (linearSection H f).IsHomogeneous r := by
  simpa only [one_mul, linearSection] using hf.aeval (sectionForm H) (sectionForm_homogeneous H)

variable [Fintype α]

lemma pderiv_linearSection (H : α × β → K) (f : MvPolynomial α K) (c : β) :
    pderiv c (linearSection H f) =
      ∑ i, C (H (i,c)) * linearSection H (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [linearSection]
  | add p q hp hq => simp [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp [map_mul, hp, pderiv_X, Pi.single_apply, apply_ite, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, mul_comm, add_comm]
    apply Finset.sum_congr rfl
    intro i _
    ring

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma singularSystem_homogeneous {R β : Type*} [CommRing R] {f : MvPolynomial β R} {r : ℕ}
    (hf : f.IsHomogeneous r) (j : Option β) :
    (singularSystem f j).IsWeightedHomogeneous (fun _ : β => (1 : ℤ))
      (singularDegrees r j) := by
  cases j with
  | none => exact homogeneous_intWeight hf
  | some i => exact homogeneous_intWeight hf.pderiv

theorem generic_slice_certificate {v d n r : ℕ}
    (f : MvPolynomial (Fin (v+1)) K) (hf : f ≠ 0) (hhom : f.IsHomogeneous r)
    (hdim : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i f))) ≤ n)
    (hn : n+d < v+1) [IsAlgClosed L]
    (H : Fin (v+1) × Fin (d+1) → L) (hH : AlgebraicIndependent K H) :
    ∃ D : ℕ, Function.Surjective
      (macaulayMatrix (singularDegrees r)
        (singularSystem (linearSection H (map (algebraMap K L) f))) D).mulVec := by
  classical
  let g := linearSection H (map (algebraMap K L) f)
  have hg : g.IsHomogeneous r := linearSection_homogeneous H (hhom.map _)
  have hz : ∀ y ∈ zeroLocus L (Ideal.span (Set.range (singularSystem g))), y = 0 := by
    intro y hy
    have hh (j : Option (Fin (d+1))) : eval y (singularSystem g j) = 0 := by
      exact hy _ Ideal.mem_span_range_self
    apply generic_homogeneous_slice f hf hhom hdim hn H hH y
    · have h := hh none
      simpa only [singularSystem, g, eval_linearSection, eval_map, aeval_def] using h
    · intro c
      have h := hh (some c)
      simp only [singularSystem, g, pderiv_linearSection, map_sum, map_mul, eval_C,
        eval_linearSection, pderiv_map, eval_map] at h
      simpa only [mul_comm, aeval_def] using h
  obtain ⟨D,hD⟩ := homogeneous_piece_certificate
    (Ideal.span (Set.range (singularSystem g))) hz
  refine ⟨D, (macaulay_surjective_iff _ _ (singularSystem_homogeneous hg) D).mpr ?_⟩
  intro p hp
  exact hD p (intWeight_homogeneous hp)

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma linearSection_map {K L α β : Type*} [CommRing K] [CommRing L] [Fintype β]
    (φ : K →+* L) (H : α × β → K) (f : MvPolynomial α K) :
    map φ (linearSection H f) = linearSection (fun i => φ (H i)) (map φ f) := by
  apply MvPolynomial.induction_on f
  · intro a
    simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro p i hp
    simp only [map_mul, linearSection_X, hp, map_X,
      sectionForm, map_sum, map_C]

end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConditionalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma singularSystem_map {K L β : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (f : MvPolynomial β K) (j : Option β) :
    map φ (singularSystem f j) = singularSystem (map φ f) j := by
  cases j with
  | none => rfl
  | some i => exact pderiv_map.symm

lemma universalSection_specialize {K σ α β : Type*} [CommRing K] [Fintype β]
    (F : MvPolynomial α (MvPolynomial σ ℤ)) (θ : σ → K) (H : α × β → K) :
    map (eval₂Hom (Int.castRingHom K) (Sum.elim θ H)) (universalSection F) =
      linearSection H (map (eval₂Hom (Int.castRingHom K) θ) F) := by
  rw [universalSection, linearSection_map, map_map]
  have he : (eval₂Hom (Int.castRingHom K) (Sum.elim θ H)).comp (rename (R := ℤ) (fun i : σ => (Sum.inl i : σ ⊕ (α × β)))).toRingHom =
      eval₂Hom (Int.castRingHom K) θ := by
    ext i <;> simp
  rw [he]
  have hH : (fun i : α × β =>
      eval₂Hom (Int.castRingHom K) (Sum.elim θ H) (X (Sum.inr i))) = H := by
    funext i
    exact eval₂_X _ _ _
  rw [hH]

lemma universalSection_macaulay_map {M σ α β : Type*} [Field M] [Fintype β]
    (F : MvPolynomial α (MvPolynomial σ ℤ)) (r D : ℕ)
    (t : σ → M) (A : α × β → M) :
    (macaulayMatrix (singularDegrees r)
      (singularSystem (universalSection (β := β) F)) D).map
        (eval₂Hom (Int.castRingHom M) (Sum.elim t A)) =
      macaulayMatrix (singularDegrees r)
        (singularSystem (linearSection A (map (eval₂Hom (Int.castRingHom M) t) F))) D := by
  rw [← macaulayMatrix_map]
  apply congrArg (fun Q => macaulayMatrix (singularDegrees r) Q D)
  funext j
  rw [singularSystem_map, universalSection_specialize]

theorem transfer_section_certificate {K L σ α β : Type*}
    [Field K] [Field L] [CharZero L] [Infinite L] [Fintype β]
    (F : MvPolynomial α (MvPolynomial σ ℤ)) (r D : ℕ)
    (θ : σ → K) (H : α × β → K)
    (h : Function.Surjective
      (macaulayMatrix (singularDegrees r)
        (singularSystem (linearSection H
          (map (eval₂Hom (Int.castRingHom K) θ) F))) D).mulVec) :
    ∃ θ' : σ → L, ∃ H' : α × β → L,
      Function.Surjective
        (macaulayMatrix (singularDegrees r)
          (singularSystem (linearSection H'
            (map (eval₂Hom (Int.castRingHom L) θ') F))) D).mulVec := by
  classical
  let P := macaulayMatrix (singularDegrees r) (singularSystem (universalSection (β := β) F)) D
  have hp : Function.Surjective
      (P.map (eval₂Hom (Int.castRingHom K) (Sum.elim θ H))).mulVec := by
    dsimp only [P]
    rwa [universalSection_macaulay_map]
  obtain ⟨w,hw⟩ := integer_polynomial_rank_transfer (L := L) P (Sum.elim θ H) hp
  refine ⟨fun i => w (Sum.inl i), fun i => w (Sum.inr i), ?_⟩
  have hw' : Sum.elim (fun i => w (Sum.inl i)) (fun i => w (Sum.inr i)) = w := by
    funext i
    cases i <;> rfl
  dsimp only [P] at hw
  rw [← universalSection_macaulay_map, hw']
  exact hw

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma macaulay_no_nonzero_zero {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι]
    (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℕ)
    (h : Function.Surjective (macaulayMatrix e F D).mulVec)
    (y : σ → K) (hy : ∀ i, eval y (F i) = 0) : y = 0 := by
  classical
  have hz : y ∈ zeroLocus K (Ideal.span (Set.range F)) := by
    rw [zeroLocus_span]
    rintro _ ⟨i,rfl⟩
    exact hy i
  have hD := (macaulay_surjective_iff e F hF D).mp h
  ext j
  have hx : (X j : MvPolynomial σ K)^D ∈ Ideal.span (Set.range F) :=
    hD _ (homogeneous_intWeight (by simpa only [one_mul] using (isHomogeneous_X K j).pow D))
  have hv : y j ^ D = 0 := by simpa using hz _ hx
  by_contra hj
  exact pow_ne_zero D hj hv

theorem certificate_smooth_equations {K β : Type*} [Field K] [Fintype β]
    (g : MvPolynomial β K) (r D : ℕ) (hg : g.IsHomogeneous r)
    (h : Function.Surjective
      (macaulayMatrix (singularDegrees r) (singularSystem g) D).mulVec) :
    ∀ y : β → K, eval y g = 0 → (∀ j, eval y (pderiv j g) = 0) → y = 0 := by
  intro y hy hd
  apply macaulay_no_nonzero_zero _ _ (singularSystem_homogeneous hg) D h y
  intro j
  cases j with
  | none => exact hy
  | some j => exact hd j

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
universe u v
variable (K : Type u) [Field K] (ι : Type v)

lemma independentParameters_independent : AlgebraicIndependent K (independentParameters K ι) := by
  let R := MvPolynomial ι K
  let Q := FractionRing R
  have hQ : AlgebraicIndependent K (fun i : ι => algebraMap R Q (X i)) :=
    (MvPolynomial.algebraicIndependent_X ι K).map'
      (f := IsScalarTower.toAlgHom K R Q) (IsFractionRing.injective R Q)
  exact hQ.map' (f := IsScalarTower.toAlgHom K Q (GenericClosed K ι))
    (RingHom.injective (algebraMap Q (GenericClosed K ι)))

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
universe u v

lemma specialize_tower {K L σ α : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (F : MvPolynomial α (MvPolynomial σ ℤ)) (θ : σ → K) :
    map φ (map (eval₂Hom (Int.castRingHom K) θ) F) =
      map (eval₂Hom (Int.castRingHom L) (fun i => φ (θ i))) F := by
  rw [map_map]
  apply congrArg (fun ψ : MvPolynomial σ ℤ →+* L => map ψ F)
  ext i <;> simp

theorem exists_complex_smooth_section {K : Type u} [Field K] {σ : Type v}
    {v d n r : ℕ} (F : MvPolynomial (Fin (v+1)) (MvPolynomial σ ℤ))
    (hF : F.IsHomogeneous r) (θ : σ → K)
    (hf : map (eval₂Hom (Int.castRingHom K) θ) F ≠ 0)
    (hdim : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (map (eval₂Hom (Int.castRingHom K) θ) F)))) ≤ n)
    (hn : n+d < v+1) :
    ∃ θ' : σ → ℂ, ∃ H' : Fin (v+1) × Fin (d+1) → ℂ,
      let g := linearSection H' (map (eval₂Hom (Int.castRingHom ℂ) θ') F)
      g ≠ 0 ∧ g.IsHomogeneous r ∧
      (∀ y : Fin (d+1) → ℂ, eval y g = 0 →
        (∀ j, eval y (pderiv j g) = 0) → y = 0) := by
  classical
  let M := GenericClosed K (Fin (v+1) × Fin (d+1))
  let H := independentParameters K (Fin (v+1) × Fin (d+1))
  obtain ⟨D,hD⟩ := generic_slice_certificate
    (L := M) _ hf (hF.map _) hdim hn H (independentParameters_independent K _)
  rw [specialize_tower] at hD
  obtain ⟨t,A,hA⟩ := transfer_section_certificate (L := ℂ) F r D
    (fun i => algebraMap K M (θ i)) H hD
  refine ⟨t,A, ?_⟩
  let g := linearSection A (map (eval₂Hom (Int.castRingHom ℂ) t) F)
  have hg : g.IsHomogeneous r := linearSection_homogeneous A (hF.map _)
  have hs := certificate_smooth_equations g r D hg hA
  refine ⟨?_,hg,hs⟩
  intro h
  change g = 0 at h
  have hzero := hs (fun _ => 1) (by rw [h, map_zero]) (by
    intro j
    rw [h, map_zero, map_zero])
  exact one_ne_zero (congrFun hzero (0 : Fin (d+1)))

end PermanentBorder.SliceParameters
namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma gradientIdeal_rename {K α β : Type*} [CommRing K]
    (e : α ≃ β) (f : MvPolynomial α K) :
    Ideal.span (Set.range (fun j => pderiv j (rename e f))) =
      (Ideal.span (Set.range (fun i => pderiv i f))).map
        (renameEquiv K e).toRingEquiv.toRingHom := by
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨pderiv (e.symm j) f,⟨e.symm j,rfl⟩,?_⟩
    change rename e (pderiv (e.symm j) f) = pderiv j (rename e f)
    rw [← pderiv_rename e.injective,e.apply_symm_apply]
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨e i,pderiv_rename e.injective i f⟩

lemma gradientDimension_rename {K α β : Type*} [CommRing K]
    (e : α ≃ β) (f : MvPolynomial α K) :
    ringKrullDim (MvPolynomial β K ⧸ Ideal.span (Set.range (fun j => pderiv j (rename e f)))) =
      ringKrullDim (MvPolynomial α K ⧸ Ideal.span (Set.range (fun i => pderiv i f))) := by
  exact ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv _ _ (renameEquiv K e).toRingEquiv (gradientIdeal_rename e f)).symm

lemma nonzero_of_gradientDimension {K α : Type*} [Field K] [Fintype α]
    (f : MvPolynomial α K) (n : ℕ)
    (hdim : ringKrullDim (MvPolynomial α K ⧸
      Ideal.span (Set.range (fun i => pderiv i f))) ≤ n)
    (hn : n < Fintype.card α) : f ≠ 0 := by
  intro h
  rw [h] at hdim
  have hz : Ideal.span (Set.range (fun i : α => pderiv i (0 : MvPolynomial α K))) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simp
  rw [hz,ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing] at hdim
  have hdim' : ((Fintype.card α : ℕ) : WithBot ℕ∞) ≤ n := by simpa using hdim
  have hi : Fintype.card α ≤ n := by exact_mod_cast hdim'
  omega

theorem exists_complex_smooth_section_finite {K α σ : Type} [Field K] [Fintype α]
    {v d n r : ℕ} (hv : Fintype.card α = v+1)
    (F : MvPolynomial α (MvPolynomial σ ℤ)) (hF : F.IsHomogeneous r) (θ : σ → K)
    (hf : map (eval₂Hom (Int.castRingHom K) θ) F ≠ 0)
    (hdim : ringKrullDim (MvPolynomial α K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (map (eval₂Hom (Int.castRingHom K) θ) F)))) ≤ n)
    (hn : n+d < v+1) :
    ∃ θ' : σ → ℂ, ∃ H' : α × Fin (d+1) → ℂ,
      let g := linearSection H' (map (eval₂Hom (Int.castRingHom ℂ) θ') F)
      g ≠ 0 ∧ g.IsHomogeneous r ∧
      (∀ y : Fin (d+1) → ℂ, eval y g = 0 →
        (∀ j, eval y (pderiv j g) = 0) → y = 0) := by
  classical
  let e : α ≃ Fin (v+1) := Fintype.equivFinOfCardEq hv
  let F' := rename e F
  have he (L : Type) [CommRing L] (t : σ → L) :
      map (eval₂Hom (Int.castRingHom L) t) F' =
        rename e (map (eval₂Hom (Int.castRingHom L) t) F) := by
    exact map_rename _ _ _
  have hf' : map (eval₂Hom (Int.castRingHom K) θ) F' ≠ 0 := by
    rw [he]
    exact fun h => hf ((rename_injective _ e.injective).eq_iff.mp (h.trans (map_zero _).symm))
  have hd' : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (map (eval₂Hom (Int.castRingHom K) θ) F')))) ≤ n := by
    rw [he,gradientDimension_rename]
    exact hdim
  obtain ⟨t,H,hh⟩ := exists_complex_smooth_section F' hF.rename_isHomogeneous θ hf' hd' hn
  refine ⟨t,(fun ij => H (e ij.1,ij.2)),?_⟩
  have hl (f : MvPolynomial α ℂ) :
      linearSection H (rename e f) = linearSection (fun ij => H (e ij.1,ij.2)) f := by
    have hhom : (linearSection H).comp (rename e) =
        linearSection (fun ij => H (e ij.1,ij.2)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply,rename_X,linearSection_X]
      rfl
    exact DFunLike.congr_fun hhom f
  rw [he,hl] at hh
  exact hh
end PermanentBorder.SliceParameters

namespace PermanentBorder.Parameters

theorem size_bound {m : ℕ} (hm : 1408 ≤ m) :
    128 ≤ auxiliarySize m ∧ (m : ℝ) / 12 ≤ auxiliarySize m ∧
    11 * auxiliarySize m ≤ m := by
  dsimp [auxiliarySize]
  have h : m ≤ 12 * (m / 11) := by omega
  refine ⟨by omega, ?_, by omega⟩
  have hr : (m : ℝ) ≤ 12 * (m / 11 : ℕ) := by exact_mod_cast h
  linarith

theorem index_bounds {k : ℕ} (hk : 128 ≤ k) :
    (k : ℝ) / 4 ≤ selectorIndex k ∧ selectorIndex k ≤ k / 2 ∧
    (k : ℝ) / 4 ≤ (selectorDegree k - 1 : ℕ) ∧
    2 ≤ selectorDegree k := by
  have hq : k ≤ 4 * selectorIndex k := by dsimp [selectorIndex]; omega
  have hr : k ≤ 4 * (selectorDegree k - 1) := by
    dsimp [selectorDegree, selectorIndex]; omega
  refine ⟨?_, by dsimp [selectorIndex]; omega, ?_, ?_⟩
  · have hc : (k : ℝ) ≤ 4 * selectorIndex k := by exact_mod_cast hq
    linarith
  · have hc : (k : ℝ) ≤ 4 * (selectorDegree k - 1 : ℕ) := by exact_mod_cast hr
    linarith
  · dsimp [selectorDegree, selectorIndex]; omega

end PermanentBorder.Parameters

namespace PermanentBorder
open MvPolynomial
lemma SliceParameters.linearSection_eq_affineSubstitution {α β : Type*}
    [Fintype β] (H : α × β → ℂ) :
    SliceParameters.linearSection H = affineSubstitution (fun _ => 0) (fun i j => H (i,j)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [SliceParameters.linearSection,SliceParameters.sectionForm,affineSubstitution]

theorem HasBorderDeterminant.selector_lower_of_critical_dimension
    {K : Type} [Field K] {m n k q d B : ℕ}
    (h : HasBorderDeterminant n (permanentPolynomial m))
    (hk : 0 < k) (hq : q ≤ k) (hr : 2 ≤ k-2*q) (hd : 2 ≤ d)
    (hm : 11*k-2*q ≤ m) (θ : Fin k → K)
    (hdim : ringKrullDim (MvPolynomial (Variables k) K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (Selector.diagonalCoefficient
          (Matrix.of fun a b => (X (a,b) : MvPolynomial (Variables k) K))
          (fun i => C (θ i)) q)))) ≤ B)
    (hB : B+(d-1) < k^2) :
    (((k-2*q-1 : ℕ) : ℝ) * ((d-1 : ℕ) : ℝ)) / (4*Real.exp 1) ≤ n := by
  classical
  have hk2 : 0 < k^2 := pow_pos hk _
  have hc : Fintype.card (Variables k) = k^2 := by simp [Variables,pow_two]
  have hv : Fintype.card (Variables k) = (k^2-1)+1 := by omega
  let F : MvPolynomial (Variables k) (MvPolynomial (Fin k) ℤ) :=
    Selector.integralCoefficientFamily k q
  have hd' : ringKrullDim (MvPolynomial (Variables k) K ⧸
      Ideal.span (Set.range (fun i => pderiv i
        (map (eval₂Hom (Int.castRingHom K) θ) F)))) ≤ B := by
    rw [show map (eval₂Hom (Int.castRingHom K) θ) F =
      Selector.diagonalCoefficient
        (Matrix.of fun a b => (X (a,b) : MvPolynomial (Variables k) K))
        (fun i => C (θ i)) q from Selector.integralCoefficientFamily_specialize k q θ]
    exact hdim
  have hFne := SliceParameters.nonzero_of_gradientDimension
    (map (eval₂Hom (Int.castRingHom K) θ) F) B hd' (by omega : B < Fintype.card (Variables k))
  obtain ⟨t,H,hs⟩ := SliceParameters.exists_complex_smooth_section_finite hv F
    (Selector.integralCoefficientFamily_homogeneous k q) θ hFne hd'
    (by omega : B+(d-1) < (k^2-1)+1)
  have hb := (h.coefficientPolynomial hq hm t).affineSubstitution
    (fun _ => 0) (fun i j => H (i,j))
  rw [← SliceParameters.linearSection_eq_affineSubstitution,
    ← Selector.integralCoefficientFamily_complex] at hb
  have he := Polar.HasBorderDeterminant.smooth_lower_bound hb
    (by simpa only [Fintype.card_fin] using (show 2 ≤ d-1+1 by omega)) hr hs.2.1 hs.2.2
  simpa only [Fintype.card_fin,Nat.add_sub_cancel] using he
end PermanentBorder

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.EffectiveParameters
open PermanentBorder.Parameters

lemma sectionSize_bounds {k : ℕ} (hk : 128 ≤ k) :
    2 ≤ sectionSize k ∧ sectionSize k ≤ k^2 ∧
      (k : ℝ)^2 / 330 ≤ ((sectionSize k-1 : ℕ) : ℝ) := by
  let q := selectorIndex k
  let T := (q+2).choose 2
  let d := sectionSize k
  have hq : 3*q ≤ k-1 ∧ k ≤ 3*(q+1) := by
    dsimp [q,selectorIndex]
    omega
  have hq40 : 40 ≤ q := by omega
  have hT : 2*T=(q+2)*(q+1) := by
    dsimp [T]
    have heven : 2 ∣ (q+2)*(q+1) := by
      simpa [Nat.add_assoc,mul_comm] using (Nat.even_mul_succ_self (q+1)).two_dvd
    rw [Nat.choose_two_right,show q+2-1=q+1 by omega,Nat.mul_div_cancel' heven]
  have hTlarge : 36 ≤ T := by nlinarith
  have hd2 : 2 ≤ d := by dsimp [d,sectionSize]; change 2 ≤ T/18; omega
  have hTd : T < 18*(d+1) := by dsimp [T,d,sectionSize,q]; omega
  have hdT : d ≤ T := by dsimp [T,d,sectionSize,q]; omega
  have hTk : T ≤ k^2 := by
    have hh := Nat.mul_le_mul (show q+2≤k by omega) (show q+1≤k by omega)
    nlinarith
  have hdR : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hTkR : (k : ℝ) ≤ 3*((q : ℝ)+1) := by exact_mod_cast hq.2
  have hTdR : (T : ℝ) ≤ 18*((d : ℝ)+1) := by exact_mod_cast Nat.le_of_lt hTd
  have hTR : 2*(T : ℝ)=((q : ℝ)+2)*((q : ℝ)+1) := by exact_mod_cast hT
  have hkR : (128 : ℝ) ≤ k := by exact_mod_cast hk
  have hTlower : (k : ℝ)*((k : ℝ)+3) ≤ 18*T := by
    have hm := mul_le_mul hTkR (by linarith : (k : ℝ)+3 ≤ 3*((q : ℝ)+2))
      (by positivity : (0:ℝ) ≤ (k : ℝ)+3) (by positivity : (0:ℝ) ≤ 3*((q : ℝ)+1))
    nlinarith
  refine ⟨hd2,hdT.trans hTk,?_⟩
  change (k : ℝ)^2/330 ≤ ((d-1 : ℕ) : ℝ)
  rw [hdR]
  have hk2 : (16384 : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  nlinarith

lemma degree_effective_bound {k : ℕ} (hk : 128 ≤ k) :
    (33 : ℝ)*(k : ℝ)/100 ≤ ((k-2*selectorIndex k-1 : ℕ) : ℝ) := by
  have hq : 3*selectorIndex k ≤ k-1 := by dsimp [selectorIndex]; omega
  have hqk : 2*selectorIndex k+1 ≤ k := by omega
  have he : ((k-2*selectorIndex k-1 : ℕ) : ℝ) = (k : ℝ)-2*(selectorIndex k : ℝ)-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    norm_cast
  have hqR : 3*(selectorIndex k : ℝ) ≤ (k : ℝ)-1 := by
    have : 3*selectorIndex k+1 ≤ k := by omega
    have hh : 3*(selectorIndex k : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast this
    linarith
  have hkR : (128 : ℝ) ≤ k := by exact_mod_cast hk
  rw [he]
  linarith

theorem explicit_constant {m : ℕ} (hm : 1408 ≤ m) :
    (m : ℝ)^3 / (5529600 * Real.exp 1) ≤
      (((auxiliarySize m-2*selectorIndex (auxiliarySize m)-1 : ℕ) : ℝ)*
        ((sectionSize (auxiliarySize m)-1 : ℕ) : ℝ)) / (4*Real.exp 1) := by
  let k := auxiliarySize m
  have hk : 128 ≤ k := (Parameters.size_bound hm).1
  have hr := degree_effective_bound hk
  have hd := (sectionSize_bounds hk).2.2
  have hprod : (k : ℝ)^3/1000 ≤
      ((k-2*selectorIndex k-1 : ℕ) : ℝ)*((sectionSize k-1 : ℕ) : ℝ) := by
    have hmul := mul_le_mul hr hd (by positivity : (0:ℝ) ≤ (k : ℝ)^2/330)
      (by positivity : (0:ℝ) ≤ ((k-2*selectorIndex k-1 : ℕ) : ℝ))
    nlinarith
  have hmkN : m ≤ 11*k+10 := by dsimp [k,auxiliarySize]; omega
  have hkR : (128 : ℝ) ≤ k := by exact_mod_cast hk
  have hmk : (m : ℝ) ≤ 111*(k : ℝ)/10 := by
    have : (m : ℝ) ≤ 11*(k : ℝ)+10 := by exact_mod_cast hmkN
    linarith
  have hcubes : (m : ℝ)^3 ≤ (111*(k : ℝ)/10)^3 :=
    pow_le_pow_left₀ (by positivity) hmk 3
  have he := Real.exp_pos (1 : ℝ)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  change (m : ℝ)^3*(4*Real.exp 1) ≤ _
  dsimp [k] at hprod hcubes ⊢
  nlinarith [show (0:ℝ) ≤ (auxiliarySize m : ℝ)^3 by positivity]

end PermanentBorder.EffectiveParameters

namespace PermanentBorder
open Parameters EffectiveParameters SpectralDimension MvPolynomial

theorem permanent_border_cubic_lower_bound_oai (m n : ℕ) (hm : 1408 ≤ m)
    (h : HasBorderDeterminant n (permanentPolynomial m)) :
    (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ) := by
  let k := auxiliarySize m
  have hk : 128 ≤ k := (Parameters.size_bound hm).1
  obtain ⟨θ,hdim⟩ := exists_effective_critical_bound (K := AlgebraicClosure (ZMod 2)) hk
  have hs := EffectiveParameters.sectionSize_bounds hk
  have hi := Parameters.index_bounds hk
  have hB : k^2-sectionSize k+(sectionSize k-1) < k^2 := by omega
  apply (EffectiveParameters.explicit_constant hm).trans
  exact h.selector_lower_of_critical_dimension
    (by omega : 0 < k) (by have := Nat.div_le_self k 2; omega : selectorIndex k ≤ k)
    hi.2.2.2 hs.1 (by have := (Parameters.size_bound hm).2.2; omega)
    θ hdim hB

end PermanentBorder

end OAI
end

theorem solution : type_of% @OAI.PermanentBorder.permanent_border_cubic_lower_bound_oai := @OAI.PermanentBorder.permanent_border_cubic_lower_bound_oai
