-- Prove2me | solution 1 for OAI.PermanentBorder.HasBorderDeterminant.coefficientPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:57:37.440057+00:00
-- url     : https://prove2.me/submissions/5733c6cc-cd99-491d-9e4a-6f9e5f9a3767

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_OAIQWPB000

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

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section ScalarNormalization
variable {σ : Type*} [Fintype σ]

theorem affineMatrixPolynomial_scaleRow (n : ℕ) (i₀ : Fin n) (a : ℂ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    affineMatrixPolynomial n (A₀.updateRow i₀ (a • A₀ i₀))
      (fun v => (A v).updateRow i₀ (a • A v i₀)) =
    a • affineMatrixPolynomial n A₀ A := by
  classical
  let M : Matrix (Fin n) (Fin n) (Poly σ) :=
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v
  let M' : Matrix (Fin n) (Fin n) (Poly σ) := fun i j =>
    C ((A₀.updateRow i₀ (a • A₀ i₀)) i j) +
      ∑ v, C (((A v).updateRow i₀ (a • A v i₀)) i j) * X v
  have hM : M' = M.updateRow i₀ ((C a : Poly σ) • M i₀) := by
    funext i j
    change C ((A₀.updateRow i₀ (a • A₀ i₀)) i j) + (∑ v,
      C (((A v).updateRow i₀ (a • A v i₀)) i j) * X v) = _
    by_cases hi : i = i₀
    · subst i
      rw [Matrix.updateRow_self, Matrix.updateRow_self]
      simp only [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, map_mul]
      change _ = C a * (C (A₀ i₀ j) + ∑ v, C (A v i₀ j) * X v)
      simp only [mul_add, Finset.mul_sum, mul_assoc]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi]
      simp only [Matrix.updateRow_ne hi]
      rfl
  change M'.det = a • M.det
  rw [hM]
  rw [Matrix.det_updateRow_smul]
  rw [Matrix.updateRow_eq_self]
  exact (MvPolynomial.smul_eq_C_mul M.det a).symm

theorem HasBorderDeterminant.smul {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (a : ℂ) : HasBorderDeterminant n (a • p) := by
  classical
  obtain ⟨hn, A₀, A, hlim⟩ := h
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨hn, (fun l => (A₀ l).updateRow i₀ (a • A₀ l i₀)),
    (fun l v => (A l v).updateRow i₀ (a • A l v i₀)), ?_⟩
  intro e
  simp only [affineMatrixPolynomial_scaleRow, coeff_smul, smul_eq_mul]
  exact tendsto_const_nhds.mul (hlim e)

end ScalarNormalization
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
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]

omit [Fintype n] in
 theorem occupancy_left (S : Finset (n × n)) (i : n) :
    occupancy S (.inl i) = (S.filter (fun e => e.1 = i)).card := by
  classical
  rw [Finset.card_filter]
  simp only [occupancy, Finsupp.finsetSum_apply, edgeExponent, Finsupp.add_apply,
    Finsupp.single_apply, Sum.inl.injEq, Sum.inr_ne_inl,
    ite_false, add_zero]

omit [Fintype n] in
 theorem occupancy_right (S : Finset (n × n)) (j : n) :
    occupancy S (.inr j) = (S.filter (fun e => e.2 = j)).card := by
  classical
  rw [Finset.card_filter]
  simp only [occupancy, Finsupp.finsetSum_apply, edgeExponent, Finsupp.add_apply,
    Finsupp.single_apply, Sum.inr.injEq, Sum.inl_ne_inr,
    ite_false, zero_add]

 theorem permGraph_injective : Function.Injective (permGraph (n := n)) := by
  intro σ τ h
  ext j
  have hmem : (σ j,j) ∈ permGraph σ := by simp
  rw [h] at hmem
  exact (mem_permGraph τ _ _).mp hmem |>.symm

 theorem occupancy_permGraph (σ : Equiv.Perm n) :
    occupancy (permGraph σ) = allOnes (n ⊕ n) := by
  classical
  ext v
  cases v with
  | inl i =>
    rw [occupancy_left, allOnes_apply]
    apply Finset.card_eq_one.mpr
    refine ⟨(i,σ.symm i), ?_⟩
    ext ⟨r,c⟩
    simp only [Finset.mem_filter, mem_permGraph, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h₁,h₂⟩
      exact ⟨h₂, σ.injective ((h₁.trans h₂).trans (σ.apply_symm_apply i).symm)⟩
    · rintro ⟨rfl,rfl⟩
      simp
  | inr j =>
    rw [occupancy_right, allOnes_apply]
    apply Finset.card_eq_one.mpr
    refine ⟨(σ j,j), ?_⟩
    ext ⟨r,c⟩
    simp only [Finset.mem_filter, mem_permGraph, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h₁,rfl⟩
      exact ⟨h₁.symm,rfl⟩
    · rintro ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩

 theorem unique_column {S : Finset (n × n)}
    (h : occupancy S = allOnes (n ⊕ n)) (j : n) :
    ∃! i, (i,j) ∈ S := by
  have hc : (S.filter (fun e => e.2 = j)).card = 1 := by
    rw [← occupancy_right, h, allOnes_apply]
  obtain ⟨⟨r,c⟩, hset⟩ := Finset.card_eq_one.mp hc
  have hm : (r,c) ∈ S.filter (fun e => e.2 = j) := by simp [hset]
  obtain ⟨hr, rfl⟩ := Finset.mem_filter.mp hm
  refine ⟨r, hr, ?_⟩
  intro i hi
  have hmem : (i,c) ∈ S.filter (fun e => e.2 = c) := by simp [hi]
  rw [hset] at hmem
  exact congrArg Prod.fst (Finset.mem_singleton.mp hmem)

 theorem unique_row {S : Finset (n × n)}
    (h : occupancy S = allOnes (n ⊕ n)) (i : n) :
    ∃! j, (i,j) ∈ S := by
  have hc : (S.filter (fun e => e.1 = i)).card = 1 := by
    rw [← occupancy_left, h, allOnes_apply]
  obtain ⟨⟨r,c⟩, hset⟩ := Finset.card_eq_one.mp hc
  have hm : (r,c) ∈ S.filter (fun e => e.1 = i) := by simp [hset]
  obtain ⟨hmem0, rfl⟩ := Finset.mem_filter.mp hm
  refine ⟨c, hmem0, ?_⟩
  intro j hj
  have hmem : (r,j) ∈ S.filter (fun e => e.1 = r) := by simp [hj]
  rw [hset] at hmem
  exact congrArg Prod.snd (Finset.mem_singleton.mp hmem)

 theorem occupancy_eq_iff {S : Finset (n × n)} :
    occupancy S = allOnes (n ⊕ n) ↔ ∃ σ : Equiv.Perm n, S = permGraph σ := by
  classical
  constructor
  · intro h
    choose f hf hfu using unique_column h
    have hinj : Function.Injective f := by
      intro i j hij
      obtain ⟨c,hc,hcu⟩ := unique_row h (f i)
      exact (hcu i (hf i)).trans (hcu j (hij ▸ hf j)).symm
    have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
    let σ : Equiv.Perm n := Equiv.ofBijective f ⟨hinj,hsurj⟩
    refine ⟨σ, ?_⟩
    ext ⟨r,c⟩
    rw [mem_permGraph]
    change (r,c) ∈ S ↔ f c = r
    constructor
    · intro hr
      exact (hfu c r hr).symm
    · rintro rfl
      exact hf c
  · rintro ⟨σ,rfl⟩
    exact occupancy_permGraph σ

omit [DecidableEq n] in
 theorem edgeProduct_expansion (M : Matrix n n R) :
    edgeProduct M = ∑ S : Finset (n × n),
      monomial (occupancy S) (∏ e ∈ S, M e.1 e.2) := by
  classical
  simp only [edgeProduct, add_comm (1 : MvPolynomial (n ⊕ n) R)]
  rw [Finset.prod_add_one]
  simp only [← monomial_sum_prod, occupancy, Finset.powerset_univ]

 theorem edgeProduct_permanent (M : Matrix n n R) :
    (edgeProduct M).coeff (allOnes (n ⊕ n)) = M.permanent := by
  classical
  rw [edgeProduct_expansion, coeff_sum]
  simp only [coeff_monomial]
  let good := Finset.univ.filter (fun S : Finset (n × n) => occupancy S = allOnes (n ⊕ n))
  have hgood : good = Finset.univ.image (permGraph (n := n)) := by
    ext S
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, occupancy_eq_iff]
    exact ⟨fun ⟨σ,h⟩ => ⟨σ,h.symm⟩, fun ⟨σ,h⟩ => ⟨σ,h.symm⟩⟩
  calc
    (∑ S : Finset (n × n), if occupancy S = allOnes (n ⊕ n) then ∏ e ∈ S, M e.1 e.2 else 0) =
        ∑ S ∈ good, ∏ e ∈ S, M e.1 e.2 := by rw [Finset.sum_filter]
    _ = ∑ σ : Equiv.Perm n, ∏ e ∈ permGraph σ, M e.1 e.2 := by
      rw [hgood, Finset.sum_image]
      exact fun σ _ τ _ h => permGraph_injective h
    _ = M.permanent := by
      unfold Matrix.permanent
      apply Finset.sum_congr rfl
      intro σ _
      unfold permGraph
      rw [Finset.prod_image]
      intro i _ j _ hij
      exact congrArg Prod.snd hij
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I J R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

 theorem coeff_separate_univariate (p : I → Polynomial R) (d : I →₀ ℕ) :
    (∏ i, Polynomial.eval₂ C (X i) (p i) : MvPolynomial I R).coeff d =
      ∏ i, (p i).coeff (d i) := by
  classical
  have hexp (i : I) : Polynomial.eval₂ C (X i) (p i) =
      ∑ k ∈ (p i).support, C ((p i).coeff k) * X i ^ k := by
    conv_lhs => rw [Polynomial.as_sum_support (p i)]
    simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  simp_rw [hexp]
  rw [Finset.prod_univ_sum, coeff_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, coeff_C_mul, coeff_prod_X_pow]
  have heq (k : I → ℕ) : d = Finsupp.indicator Finset.univ (fun i _ => k i) ↔ k = d := by
    simp only [Finsupp.ext_iff, Finsupp.indicator_of_mem (Finset.mem_univ _),
      _root_.funext_iff, eq_comm]
  simp_rw [heq]
  rw [Finset.sum_eq_single (fun i => d i)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hd
    have hnot : ¬ ∀ i, d i ∈ (p i).support := by
      simpa only [Fintype.mem_piFinset] using hd
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    simp only [Polynomial.mem_support_iff, not_not] at hi
    simp only [ite_true, mul_one]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact hi

 theorem coeff_one_edge_factors (s : Finset J) (a : J → R) :
    (∏ j ∈ s, (1 + Polynomial.C (a j) * Polynomial.X)).coeff 1 = ∑ j ∈ s, a j := by
  classical
  have hzero (t : Finset J) :
      (∏ j ∈ t, (1 + Polynomial.C (a j) * Polynomial.X)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_prod]
    simp [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_one, Polynomial.coeff_X]
  induction s using Finset.induction_on with
  | empty => norm_num [Polynomial.coeff_one]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, add_mul, one_mul,
      Polynomial.coeff_add, mul_assoc, mul_comm Polynomial.X,
      ← mul_assoc, Polynomial.coeff_mul_X, Polynomial.coeff_C_mul, hzero, ih, mul_one]
    exact add_comm _ _

 theorem coeff_row_edge_product [Fintype J] (a : I → J → R) :
    (∏ i, ∏ j, (1 + C (a i j) * X i) : MvPolynomial I R).coeff
        (Finsupp.equivFunOnFinite.symm (fun _ => 1)) =
      ∏ i, ∑ j, a i j := by
  classical
  let p : I → Polynomial R := fun i => ∏ j, (1 + Polynomial.C (a i j) * Polynomial.X)
  have hp (i : I) : Polynomial.eval₂ C (X i) (p i) = ∏ j, (1 + C (a i j) * X i) := by
    simp only [p, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add, Polynomial.eval₂_one,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [← show (∏ i, Polynomial.eval₂ C (X i) (p i)) =
      (∏ i, ∏ j, (1 + C (a i j) * X i)) from Finset.prod_congr rfl (fun i _ => hp i),
      coeff_separate_univariate]
  apply Finset.prod_congr rfl
  intro i _
  exact coeff_one_edge_factors Finset.univ (a i)
end PermanentBorder.Selector

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

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
omit [DecidableEq I] in
 theorem edgeProduct_nested (M : Matrix I I R) :
    sumRingEquiv R I I (edgeProduct M) =
      ∏ i, ∏ j, (1 + C (C (M i j)*X j)*X i) := by
  classical
  have hm (i j : I) : monomial (edgeExponent (i,j)) (M i j) =
      C (M i j)*X (.inl i)*X (.inr j) := by
    rw [C_mul_X_eq_monomial, X, MvPolynomial.monomial_mul]
    simp only [mul_one, edgeExponent]
  simp only [edgeProduct, map_prod, map_add, map_one]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [hm]
  simp [mul_comm, mul_left_comm]

 theorem row_product_permanent (M : Matrix I I R) :
    (∏ i, ∑ j, C (M i j)*X j).coeff (allOnes I) = M.permanent := by
  rw [← edgeProduct_permanent]
  have hones : allOnes (I ⊕ I) = (allOnes I).sumElim (allOnes I) := by
    ext i; cases i <;> rfl
  rw [hones, coeff_nested, edgeProduct_nested]
  exact congrArg (fun (p : MvPolynomial I R) => p.coeff (allOnes I))
    (coeff_row_edge_product (fun i j => C (M i j)*X j)).symm

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I E R : Type*} [Fintype I] [Fintype E] [DecidableEq I] [CommSemiring R]

 theorem graph_row_sum (src dst : E → I) (w : E → R) (i : I) :
    (∑ e, if src e = i then C (w e)*X (dst e) else 0 : MvPolynomial I R) =
      ∑ j, C (graphMatrix src dst w i j)*X j := by
  classical
  simp only [graphMatrix, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : src e = i
  · simp only [h, true_and, apply_ite, map_zero, ite_mul, zero_mul]
    simp
  · simp [h]

 theorem coeff_graph_edges (src dst : E → I) (w : E → R) :
    (∏ e, (1 + monomial (edgeExponent (src e,dst e)) (w e))).coeff
      (allOnes (I ⊕ I)) = (graphMatrix src dst w).permanent := by
  classical
  have hm (e : E) : monomial (edgeExponent (src e,dst e)) (w e) =
      C (w e)*X (.inl (src e))*X (.inr (dst e)) := by
    rw [C_mul_X_eq_monomial, X, MvPolynomial.monomial_mul]
    simp only [mul_one, edgeExponent]
  have hones : allOnes (I ⊕ I) = (allOnes I).sumElim (allOnes I) := by
    ext x; cases x <;> rfl
  rw [hones, coeff_nested]
  simp only [map_prod, map_add, map_one, hm, map_mul,
    sumRingEquiv_C, sumRingEquiv_X_inl, sumRingEquiv_X_inr]
  have hf (e : E) : (1 + C (C (w e))*X (src e)*C (X (dst e)) :
      MvPolynomial I (MvPolynomial I R)) =
      ∏ i, (1 + C (if src e = i then C (w e)*X (dst e) else 0)*X i) := by
    rw [Finset.prod_eq_single (src e)]
    · simp [map_mul, mul_comm, mul_left_comm]
    · intro i hi hie
      simp [Ne.symm hie]
    · simp
  simp_rw [hf]
  rw [Finset.prod_comm]
  change (((_ : MvPolynomial I (MvPolynomial I R)).coeff
    (Finsupp.equivFunOnFinite.symm (fun _ => 1))).coeff (allOnes I)) = _
  rw [coeff_row_edge_product]
  simp_rw [graph_row_sum]
  exact row_product_permanent _
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {R : Type*} [CommRing R]

 theorem coeff_gadgetAfterRows (a b c d : R) :
    (gadgetAfterRows a b c d).coeff threeOnes = -2 + a*b*c*d := by
  classical
  unfold gadgetAfterRows
  ring_nf
  have h2 : (2 : MvPolynomial (Fin 3) R) = C (2 : R) := (map_ofNat C 2).symm
  have h3 : (3 : MvPolynomial (Fin 3) R) = C (3 : R) := (map_ofNat C 3).symm
  simp only [h2, h3, MvPolynomial.coeff_add, Finsupp.add_apply, coeff_sub,
    X, C_apply, monomial_pow, MvPolynomial.monomial_mul, coeff_monomial]
  have heq (x y : Fin 3 →₀ ℕ) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
    rw [Finsupp.ext_iff]
    simp [Fin.forall_fin_succ]
  simp only [threeOnes, heq, Finsupp.add_apply, Finsupp.zero_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [h01, h01.symm, h02, h02.symm, h12, h12.symm]
  ring
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {R : Type*} [CommRing R]

 theorem gadgetNested_rows (a b c d : R) :
    (gadgetNested a b c d).coeff (Finsupp.equivFunOnFinite.symm (fun _ => 1)) =
      gadgetAfterRows a b c d := by
  classical
  rw [gadgetNested, coeff_C_mul, coeff_row_edge_product]
  simp only [Fin.prod_univ_succ, Fintype.prod_empty, mul_one, Fintype.sum_option,
    gadgetRowEntries, Fin.sum_univ_succ, Fintype.sum_empty, add_zero]
  simp [gadgetH, gadgetAfterRows]
  ring

 theorem gadgetEdges_nested (a b c d : R) :
    sumRingEquiv R (Fin 3) (Fin 3) (gadgetEdges a b c d) = gadgetNested a b c d := by
  classical
  simp [gadgetEdges, gadgetNested, map_prod, Fintype.prod_option, gadgetRowEntries,
    map_mul, mul_assoc]

 theorem gadgetEdges_coefficient (a b c d : R) :
    (gadgetEdges a b c d).coeff (threeOnes.sumElim threeOnes) = -2 + a*b*c*d := by
  rw [coeff_nested, gadgetEdges_nested]
  have hones : threeOnes = Finsupp.equivFunOnFinite.symm (fun _ => 1) := by
    ext i; fin_cases i <;> simp [threeOnes]
  rw [hones, gadgetNested_rows, ← hones, coeff_gadgetAfterRows]

end PermanentBorder.Selector

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Gates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {I J R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

omit [Fintype I] in
 theorem mapDomain_block_apply (d : J →₀ ℕ) (i k : I) (j : J) :
    d.mapDomain (fun j => (i,j)) (k,j) = if i = k then d j else 0 := by
  classical
  by_cases h : i = k
  · subst k
    simpa using Finsupp.mapDomain_apply (fun a b h => congrArg Prod.snd h) d j
  · rw [ite_eq_right h]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact h (congrArg Prod.fst ha)

 @[simp] theorem blockExponent_apply (d : I → J →₀ ℕ) (i : I) (j : J) :
    blockExponent d (i,j) = d i j := by
  classical
  simp only [blockExponent, Finsupp.finsetSum_apply, mapDomain_block_apply]
  simp

 theorem blockExponent_injective : Function.Injective (blockExponent (I := I) (J := J)) := by
  intro d e h
  funext i
  ext j
  simpa using congrArg (fun a : I × J →₀ ℕ => a (i,j)) h

 theorem coeff_independent_blocks (p : I → MvPolynomial J R) (d : I → J →₀ ℕ) :
    (∏ i, rename (fun j => (i,j)) (p i)).coeff (blockExponent d) =
      ∏ i, (p i).coeff (d i) := by
  classical
  have hexp (i : I) : rename (fun j => (i,j)) (p i) =
      ∑ k ∈ (p i).support, monomial (k.mapDomain (fun j => (i,j))) ((p i).coeff k) := by
    conv_lhs => rw [MvPolynomial.as_sum (p i)]
    simp only [map_sum, rename_monomial]
  simp_rw [hexp]
  rw [Finset.prod_univ_sum, coeff_sum]
  simp_rw [← monomial_sum_prod, coeff_monomial]
  change (∑ k ∈ Fintype.piFinset (fun i => (p i).support),
    if blockExponent k = blockExponent d then ∏ i, (p i).coeff (k i) else 0) = _
  simp only [blockExponent_injective.eq_iff]
  rw [Finset.sum_eq_single d]
  · simp
  · intro k _ h; simp [h]
  · intro hd
    have hnot : ¬ ∀ i, d i ∈ (p i).support := by
      simpa only [Fintype.mem_piFinset] using hd
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    simp only [mem_support_iff, not_not] at hi
    simp only [ite_true]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

 theorem eliminate_gadget_network (outside : R) (w a b c d : I → R) :
    (C outside * ∏ i, rename (fun j => (i,j))
      (gadgetEdges (-2*w i*a i) (b i) (c i) (d i))).coeff
        (blockExponent (fun (_ : I) => threeOnes.sumElim threeOnes)) =
      outside * (-2 : R) ^ Fintype.card I * ∏ i, (1 + w i*a i*b i*c i*d i) := by
  rw [coeff_C_mul, coeff_independent_blocks]
  simp_rw [gadgetEdges_coefficient]
  have h (i : I) : (-2 + (-2*w i*a i)*b i*c i*d i) =
      (-2:R) * (1 + w i*a i*b i*c i*d i) := by ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_assoc]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I G E R : Type*} [Fintype E] [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] [CommRing R]

 theorem allOnes_map_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    (allOnes A).mapDomain e = allOnes B := by
  classical
  ext b
  obtain ⟨a,rfl⟩ := e.surjective b
  rw [Finsupp.mapDomain_apply e.injective]
  rfl

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 theorem split_edge (i j : ExpandedVertex I G) (a : R) :
    splitPolynomial (1 + monomial (edgeExponent (i,j)) a) =
    1 + splitPolynomial (C a) * splitPolynomial (X (.inl i)) * splitPolynomial (X (.inr j)) := by
  have hm : monomial (edgeExponent (i,j)) a = C a * X (.inl i) * X (.inr j) := by
    rw [C_mul_X_eq_monomial, X, MvPolynomial.monomial_mul]
    simp only [edgeExponent,mul_one]
  rw [hm, map_add, map_one, map_mul, map_mul]

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 theorem gadget_factors (g : G) (w : R) (a b c d : I) :
    (∏ x : Fin 2,
        (1 + C (C (if x = 0 then -2 * w else 1)) * C (X (Sum.inl (if x = 0 then a else b))) *
            X (g, Sum.inr (x.castLE (by decide))))) *
      ((∏ x : Fin 3, (1 + C (C (if x = 2 then 0 else 1)) * X (g, Sum.inl x) *
          C (X (Sum.inr (if x = 0 then c else d))))) *
        ∏ x : Fin 3, ∏ y : Fin 3, (1 + C (C (gadgetH x y : R)) * X (g, Sum.inl x) * X (g, Sum.inr y))) =
    rename (fun z => (g,z))
      (gadgetEdges (-2*C w*X (.inl a)) (X (.inl b)) (X (.inr c)) (X (.inr d))) := by
  classical
  simp only [gadgetEdges, map_mul, map_prod, map_add, map_one, rename_C, rename_X]
  rw [Finset.prod_mul_distrib]
  apply congrArg₂ (·*·)
  · simp [Fin.prod_univ_succ, map_mul, mul_assoc, map_ofNat, neg_mul]
    ring
  · apply congrArg₂ (·*·)
    · apply Finset.prod_congr rfl
      intro i _
      fin_cases i <;> simp [mul_comm]
    · apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      have hc : C (gadgetH i j : R) = (gadgetH i j : MvPolynomial (I ⊕ I) R) := by
        fin_cases i <;> fin_cases j <;> simp [gadgetH]
      rw [hc]
      ac_rfl

omit [Fintype I] [DecidableEq I] [DecidableEq G] in
 theorem split_expanded_edges (src dst : E → I) (ω : E → R) (w : G → R) (u₁ u₂ v₁ v₂ : G → I) :
    splitPolynomial (∏ e, (1 + monomial
      (edgeExponent (expandedSrc src u₁ u₂ e, expandedDst dst v₁ v₂ e)) (expandedWeight ω w e))) =
    C (baseEdges src dst ω) * ∏ g, rename (fun z => (g,z))
      (gadgetEdges (-2*C (w g)*X (.inl (u₁ g))) (X (.inl (u₂ g)))
        (X (.inr (v₁ g))) (X (.inr (v₂ g)))) := by
  classical
  simp only [map_prod, map_mul, Fintype.prod_sum_type, Fintype.prod_prod_type,
    split_edge, expandedSrc, expandedDst, expandedWeight, splitPolynomial_C,
    splitPolynomial_outer_left, splitPolynomial_outer_right,
    splitPolynomial_inner_left, splitPolynomial_inner_right]
  congr 1
  · simp only [baseEdges, map_prod, map_add, map_one]
    apply Finset.prod_congr rfl
    intro e _
    have hm : monomial (edgeExponent (src e,dst e)) (ω e) =
        C (ω e)*X (.inl (src e))*X (.inr (dst e)) := by
      rw [C_mul_X_eq_monomial, X, MvPolynomial.monomial_mul]
      simp only [edgeExponent, mul_one]
    rw [hm, map_mul, map_mul]
  · apply Finset.prod_congr rfl
    intro g _
    exact gadget_factors g (w g) (u₁ g) (u₂ g) (v₁ g) (v₂ g)

 theorem block_three_ones : blockExponent (fun (_ : G) => threeOnes.sumElim threeOnes) =
    allOnes (InternalVertex G) := by
  classical
  ext ⟨g,i⟩
  simp only [blockExponent, Finsupp.finsetSum_apply, mapDomain_block_apply]
  rw [Finset.sum_eq_single g]
  · simp only
    cases i with
    | inl i => fin_cases i <;> simp [threeOnes, allOnes]
    | inr i => fin_cases i <;> simp [threeOnes, allOnes]
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq I] [DecidableEq G] in
 theorem splitPolynomial_top_coefficient
    (p : MvPolynomial (ExpandedVertex I G ⊕ ExpandedVertex I G) R) :
    p.coeff (allOnes _) = ((splitPolynomial p).coeff (allOnes (InternalVertex G))).coeff
      (allOnes (I ⊕ I)) := by
  have h := coeff_rename_mapDomain vertexSplit vertexSplit.injective p (allOnes _)
  rw [allOnes_map_equiv] at h
  rw [← h]
  have ho : allOnes (InternalVertex G ⊕ (I ⊕ I)) =
      (allOnes (InternalVertex G)).sumElim (allOnes (I ⊕ I)) := by
    ext x; cases x <;> rfl
  rw [ho, coeff_nested]
  rfl

 theorem expanded_permanent (src dst : E → I) (ω : E → R) (w : G → R) (u₁ u₂ v₁ v₂ : G → I) :
    (expandedMatrix src dst ω w u₁ u₂ v₁ v₂).permanent =
      (-2:R)^Fintype.card G * (baseEdges src dst ω * ∏ g,
      (1 + C (w g)*X (.inl (u₁ g))*X (.inl (u₂ g))*
        X (.inr (v₁ g))*X (.inr (v₂ g)))).coeff (allOnes (I ⊕ I)) := by
  rw [expandedMatrix, ← coeff_graph_edges, splitPolynomial_top_coefficient,
    split_expanded_edges, ← block_three_ones]
  rw [eliminate_gadget_network]
  have hc : (-2 : MvPolynomial (I ⊕ I) R)^Fintype.card G = C ((-2:R)^Fintype.card G) := by simp only [map_pow, map_neg, map_ofNat]
  rw [hc, mul_comm (baseEdges src dst ω), mul_assoc, coeff_C_mul]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

 theorem colored_diagonal_edges (M : Matrix I I R) (s t : I → R) :
    (edgeProduct M * (∏ i, (1 + C (s i)*X (.inl i)*X (.inr i))) *
      (∏ i, (1 + C (t i)*X (.inl i)*X (.inr i)))).coeff (allOnes (I ⊕ I)) =
      (M + Matrix.diagonal (fun i => s i+t i)).permanent := by
  classical
  let src : (I × I) ⊕ (I ⊕ I) → I
    | .inl (i,_) => i
    | .inr (.inl i) => i
    | .inr (.inr i) => i
  let dst : (I × I) ⊕ (I ⊕ I) → I
    | .inl (_,j) => j
    | .inr (.inl i) => i
    | .inr (.inr i) => i
  let w : (I × I) ⊕ (I ⊕ I) → R
    | .inl (i,j) => M i j
    | .inr (.inl i) => s i
    | .inr (.inr i) => t i
  have hm (i : I) (r : R) : monomial (edgeExponent (i,i)) r =
      C r*X (.inl i)*X (.inr i) := by
    rw [C_mul_X_eq_monomial, X, MvPolynomial.monomial_mul]
    simp only [edgeExponent,mul_one]
  have hpoly : (∏ e, (1 + monomial (edgeExponent (src e,dst e)) (w e))) =
      edgeProduct M * (∏ i, (1 + C (s i)*X (.inl i)*X (.inr i))) *
      (∏ i, (1 + C (t i)*X (.inl i)*X (.inr i))) := by
    simp only [Fintype.prod_sum_type, src,dst,w,hm,edgeProduct,mul_assoc]
  rw [← hpoly, coeff_graph_edges]
  congr 1
  ext i j
  simp only [graphMatrix, Fintype.sum_sum_type, Fintype.sum_prod_type, src,dst,w,
    Matrix.add_apply, Matrix.diagonal_apply]
  by_cases hij : i=j
  · subst j
    simp [and_self, ite_and]
  · simp [hij, ite_and]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [CommSemiring R]
 theorem coeff_commAlgEquiv (p : MvPolynomial A (MvPolynomial B R))
    (d : A →₀ ℕ) (e : B →₀ ℕ) :
    ((commAlgEquiv R A B p).coeff e).coeff d = (p.coeff d).coeff e := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, MvPolynomial.coeff_add, Finsupp.add_apply, hp,hq]
  | monomial f r =>
    induction r using MvPolynomial.induction_on' with
    | add r s hr hs => simp only [map_add, MvPolynomial.coeff_add, Finsupp.add_apply, hr,hs]
    | monomial g x =>
      have h : commAlgEquiv R A B (monomial f (monomial g x)) =
          monomial g (monomial f x) := by
        exact AddMonoidAlgebra.commAlgEquiv_single_single ..
      rw [h]
      by_cases hf : f=d <;> by_cases hg : g=e <;> simp [coeff_monomial, hf,hg]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R S : Type*} [CommSemiring R] [CommSemiring S]
 theorem commAlgEquiv_map_C (p : MvPolynomial A R) :
    commAlgEquiv R A B (map C p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp,hq]
  | mul_X p i hp => simp [hp]

 theorem edgeProduct_map {I : Type*} [Fintype I] (M : Matrix I I R) (f : R →+* S) :
    edgeProduct (Matrix.of fun i j => f (M i j)) = map f (edgeProduct M) := by
  simp [edgeProduct, map_prod, Matrix.of_apply]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

omit [DecidableEq I] in
 theorem swap_colored_edge_product (M : Matrix I I R) (θ : I → R) :
    commAlgEquiv R (I ⊕ I) (Fin 2)
      (edgeProduct (Matrix.of fun i j => C (M i j)) *
        (∏ i, (1 + C (X 0)*X (.inl i)*X (.inr i))) *
        (∏ i, (1 + C (C (θ i)*X 1)*X (.inl i)*X (.inr i)))) =
    C (edgeProduct M) * (∏ i, (1 + C (X (.inl i)*X (.inr i))*X 0)) *
      (∏ i, (1 + C (C (θ i)*X (.inl i)*X (.inr i))*X 1)) := by
  rw [edgeProduct_map, map_mul, map_mul, commAlgEquiv_map_C]
  simp only [map_prod]
  apply congrArg₂ (·*·)
  · apply congrArg (C (edgeProduct M) * ·)
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_add, map_one, map_mul, commAlgEquiv_C_X, commAlgEquiv_X]
    ring
  · apply Finset.prod_congr rfl
    intro i _
    simp only [map_add, map_one, map_mul, commAlgEquiv_C, map_mul, map_C,
      map_X, commAlgEquiv_X]
    ring

omit [DecidableEq I] in
 theorem two_color_coefficient (e : R) (a b : I → R) (q : ℕ) :
    (C e * (∏ i, (1 + C (a i)*X 0)) * (∏ i, (1 + C (b i)*X 1)) :
      MvPolynomial (Fin 2) R).coeff (countIndex q) =
    e * elementaryBoundary a q * elementaryBoundary b q := by
  let p : Fin 2 → Polynomial R :=
    ![∏ i, (1 + Polynomial.C (a i)*Polynomial.X),
      ∏ i, (1 + Polynomial.C (b i)*Polynomial.X)]
  have h : (∏ x, Polynomial.eval₂ C (X x) (p x)) =
      (∏ i, (1 + C (a i)*X (0:Fin 2))) * (∏ i, (1 + C (b i)*X 1)) := by
    simp [p, Fin.prod_univ_succ, Polynomial.eval₂_finsetProd]
  rw [mul_assoc, ← h, coeff_C_mul, coeff_separate_univariate]
  simp [p, Fin.prod_univ_succ, elementaryBoundary, countIndex, mul_assoc]

 theorem diagonalCoefficient_boundary (M : Matrix I I R) (θ : I → R) (q : ℕ) :
    diagonalCoefficient M θ q =
    (edgeProduct M * elementaryBoundary (fun i => X (.inl i)*X (.inr i)) q *
      elementaryBoundary (fun i => C (θ i)*X (.inl i)*X (.inr i)) q).coeff (allOnes (I ⊕ I)) := by
  have h := colored_diagonal_edges (Matrix.of fun i j => C (M i j) : Matrix I I (MvPolynomial (Fin 2) R))
    (fun _ => X 0) (fun i => C (θ i)*X 1)
  apply_fun (fun p : MvPolynomial (Fin 2) R => p.coeff (countIndex q)) at h
  rw [← coeff_commAlgEquiv, swap_colored_edge_product, two_color_coefficient] at h
  simpa only [diagonalCoefficient] using h.symm
end PermanentBorder.Selector

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

 theorem coeff_gate_half (s : Finset I) (h : ℕ) :
    ((∑ i, X i : MvPolynomial I R)^h).coeff (subsetExponent s) =
      if s.card = h then (h.factorial : R) else 0 := by
  rw [coeff_sum_X_pow_of_fintype, subsetExponent_degree, subsetExponent_multinomial]
  split_ifs with hs
  · rw [hs]
  · simp
end PermanentBorder.Selector.Gates
namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {A B R : Type*} [CommSemiring R]
 theorem sumRingEquiv_monomial (d : A →₀ ℕ) (e : B →₀ ℕ) (r : R) :
    sumRingEquiv R A B (monomial (d.sumElim e) r) = monomial d (monomial e r) := by
  simp [sumRingEquiv, monomial]
 theorem coeff_nested (p : MvPolynomial (A ⊕ B) R) (d : A →₀ ℕ) (e : B →₀ ℕ) :
    p.coeff (d.sumElim e) = ((sumRingEquiv R A B p).coeff d).coeff e := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [MvPolynomial.coeff_add, Finsupp.add_apply, map_add, hp, hq]
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
end PermanentBorder.Selector.Gates

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.GateCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {A B R : Type*} [CommSemiring R]
 theorem sumRingEquiv_rename_inl (p : MvPolynomial A R) :
    sumRingEquiv R A B (rename Sum.inl p) = map C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]
 theorem sumRingEquiv_rename_inr (p : MvPolynomial B R) :
    sumRingEquiv R A B (rename Sum.inr p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]
 theorem coeff_sum_product (p : MvPolynomial A R) (q : MvPolynomial B R)
    (d : A →₀ ℕ) (e : B →₀ ℕ) :
    (rename Sum.inl p * rename Sum.inr q).coeff (d.sumElim e) = p.coeff d * q.coeff e := by
  rw [coeff_nested, map_mul, sumRingEquiv_rename_inl, sumRingEquiv_rename_inr,
    mul_comm, coeff_C_mul, coeff_map, mul_comm, coeff_C_mul]
end PermanentBorder.Selector.Gates
namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I J R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

 theorem coeff_separate_univariate (p : I → Polynomial R) (d : I →₀ ℕ) :
    (∏ i, Polynomial.eval₂ C (X i) (p i) : MvPolynomial I R).coeff d =
      ∏ i, (p i).coeff (d i) := by
  classical
  have hexp (i : I) : Polynomial.eval₂ C (X i) (p i) =
      ∑ k ∈ (p i).support, C ((p i).coeff k) * X i ^ k := by
    conv_lhs => rw [Polynomial.as_sum_support (p i)]
    simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  simp_rw [hexp]
  rw [Finset.prod_univ_sum, coeff_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, coeff_C_mul, coeff_prod_X_pow]
  have heq (k : I → ℕ) : d = Finsupp.indicator Finset.univ (fun i _ => k i) ↔ k = d := by
    simp only [Finsupp.ext_iff, Finsupp.indicator_of_mem (Finset.mem_univ _),
      _root_.funext_iff, eq_comm]
  simp_rw [heq]
  rw [Finset.sum_eq_single (fun i => d i)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hd
    have hnot : ¬ ∀ i, d i ∈ (p i).support := by
      simpa only [Fintype.mem_piFinset] using hd
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    simp only [Polynomial.mem_support_iff, not_not] at hi
    simp only [ite_true, mul_one]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact hi

 theorem coeff_one_edge_factors (s : Finset J) (a : J → R) :
    (∏ j ∈ s, (1 + Polynomial.C (a j) * Polynomial.X)).coeff 1 = ∑ j ∈ s, a j := by
  classical
  have hzero (t : Finset J) :
      (∏ j ∈ t, (1 + Polynomial.C (a j) * Polynomial.X)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_prod]
    simp [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_one, Polynomial.coeff_X]
  induction s using Finset.induction_on with
  | empty => norm_num [Polynomial.coeff_one]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, add_mul, one_mul,
      Polynomial.coeff_add, mul_assoc, mul_comm Polynomial.X,
      ← mul_assoc, Polynomial.coeff_mul_X, Polynomial.coeff_C_mul, hzero, ih, mul_one]
    exact add_comm _ _

 theorem coeff_row_edge_product [Fintype J] (a : I → J → R) :
    (∏ i, ∏ j, (1 + C (a i j) * X i) : MvPolynomial I R).coeff
        (Finsupp.equivFunOnFinite.symm (fun _ => 1)) =
      ∏ i, ∑ j, a i j := by
  classical
  let p : I → Polynomial R := fun i => ∏ j, (1 + Polynomial.C (a i j) * Polynomial.X)
  have hp (i : I) : Polynomial.eval₂ C (X i) (p i) = ∏ j, (1 + C (a i j) * X i) := by
    simp only [p, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add, Polynomial.eval₂_one,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [← show (∏ i, Polynomial.eval₂ C (X i) (p i)) =
      (∏ i, ∏ j, (1 + C (a i j) * X i)) from Finset.prod_congr rfl (fun i _ => hp i),
      coeff_separate_univariate]
  apply Finset.prod_congr rfl
  intro i _
  exact coeff_one_edge_factors Finset.univ (a i)
end PermanentBorder.Selector.Gates

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

 theorem coeff_gateOuter (s : Finset I) (h : ℕ) :
    (gateOuter (R := R) h).coeff ((subsetExponent s).sumElim (subsetExponent s)) =
      if s.card = h then (h.factorial : R)^2 else 0 := by
  rw [gateOuter, coeff_sum_product, coeff_gate_half]
  split_ifs <;> simp [pow_two]

omit [DecidableEq I] in
 theorem gateCrossEdges_coefficient (h : ℕ) :
    (gateCrossEdges (I := I) (R := R) h).coeff
      (Finsupp.equivFunOnFinite.symm (fun _ => 1)) = gateOuter h := by
  rw [gateCrossEdges, coeff_row_edge_product]
  simp [Fintype.prod_sum_type, gateCrossEntries, gateOuter, map_pow, map_sum, mul_comm]

 theorem subsetExponent_add_compl (s : Finset I) :
    subsetExponent sᶜ + subsetExponent s = subsetExponent Finset.univ := by
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

 theorem coeff_gate_prescribed_distinguished (s : Finset I) (h : ℕ) :
    ((gateOuter (R := R) h) *
      monomial ((subsetExponent s).sumElim (subsetExponent s)) 1).coeff
      ((subsetExponent Finset.univ).sumElim (subsetExponent Finset.univ)) =
        if Fintype.card I - s.card = h then (h.factorial : R)^2 else 0 := by
  have heq : (subsetExponent Finset.univ).sumElim (subsetExponent Finset.univ) =
      ((subsetExponent sᶜ).sumElim (subsetExponent sᶜ)) +
      ((subsetExponent s).sumElim (subsetExponent s)) := by
    rw [← subsetExponent_add_compl s]
    ext i; cases i <;> rfl
  rw [heq, coeff_mul_monomial, mul_one, coeff_gateOuter, Finset.card_compl]
end PermanentBorder.Selector.Gates
namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
omit [Fintype I] in
 theorem sum_pairedExponent (s : Finset I) :
    (∑ i ∈ s, pairedExponent i) = (subsetExponent s).sumElim (subsetExponent s) := by
  classical
  ext v
  cases v with
  | inl i => simp [pairedExponent, Finsupp.finsetSum_apply, Finsupp.sumElim_inl,
      Finsupp.single_apply, eq_comm]
  | inr i => simp [pairedExponent, Finsupp.finsetSum_apply, Finsupp.sumElim_inr,
      Finsupp.single_apply, eq_comm]

 theorem independent_boundary_expansion (a : I → R) :
    (∏ i, (1 + monomial (pairedExponent i) (a i))) =
      ∑ s : Finset I, monomial ((subsetExponent s).sumElim (subsetExponent s)) (∏ i ∈ s, a i) := by
  classical
  simp only [add_comm (1 : MvPolynomial (I ⊕ I) R)]
  rw [Finset.prod_add_one]
  simp only [← monomial_sum_prod, sum_pairedExponent, Finset.powerset_univ]

omit [DecidableEq I] in
 theorem univariate_boundary_coefficient (a : I → R) (q : ℕ) :
    (∏ i, (1 + Polynomial.C (a i) * Polynomial.X)).coeff q =
      ∑ s : Finset I, if s.card = q then ∏ i ∈ s, a i else 0 := by
  classical
  simp only [add_comm (1 : Polynomial R)]
  rw [Finset.prod_add_one]
  simp only [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, Polynomial.finsetSum_coeff,
    eq_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.powerset_univ]

 theorem gate_filters_prescribed_count (a : I → R) (q : ℕ) (hq : q ≤ Fintype.card I) :
    (gateOuter (Fintype.card I-q) * ∏ i, (1 + monomial (pairedExponent i) (a i))).coeff
      ((subsetExponent Finset.univ).sumElim (subsetExponent Finset.univ)) =
      ((Fintype.card I-q).factorial : R)^2 *
        (∏ i, (1 + Polynomial.C (a i) * Polynomial.X)).coeff q := by
  classical
  rw [independent_boundary_expansion, Finset.mul_sum, coeff_sum,
    univariate_boundary_coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hm (e : I ⊕ I →₀ ℕ) (a : R) : monomial e a = C a * monomial e 1 := by simp only [C_mul_monomial, mul_one]
  rw [hm, ← mul_assoc, mul_comm (gateOuter _), mul_assoc, coeff_C_mul,
    coeff_gate_prescribed_distinguished]
  have hcard : s.card ≤ Fintype.card I := Finset.card_le_univ s
  have heq : Fintype.card I - s.card = Fintype.card I - q ↔ s.card = q := by omega
  simp only [heq]
  split_ifs <;> simp [mul_comm]
end PermanentBorder.Selector.Gates

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {A B I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
 theorem allOnes_map_equiv [Fintype A] [Fintype B] (e : A ≃ B) :
    (allOnes A).mapDomain e = allOnes B := by
  classical
  ext b
  obtain ⟨a,rfl⟩ := e.surjective b
  rw [Finsupp.mapDomain_apply e.injective]
  rfl
 theorem allOnes_sum [Fintype A] [Fintype B] :
    allOnes (A ⊕ B) = (allOnes A).sumElim (allOnes B) := by
  ext v; cases v <;> rfl
 theorem subset_univ_ones : subsetExponent (Finset.univ : Finset I) = allOnes I := by
  ext i
  simp [allOnes]

 theorem full_gate_split (a : I → R) (h : ℕ) :
    sumRingEquiv R (Fin h ⊕ Fin h) (I ⊕ I)
      (rename sumSquareSplit (fullGateEdges a h)) =
    gateCrossEdges h * C (∏ i, (1 + monomial (pairedExponent i) (a i))) := by
  classical
  simp only [fullGateEdges, map_mul, map_prod, map_add, map_one, rename_X, rename_C]
  simp only [sumSquareSplit, Equiv.coe_fn_mk, sumRingEquiv_X_inl, sumRingEquiv_X_inr, sumRingEquiv_C]
  apply congrArg₂ (·*·)
  · simp only [gateCrossEdges, Fintype.prod_sum_type, gateCrossEntries]
    rw [mul_comm]
    apply congrArg₂ (·*·)
    · apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro i _
      rw [mul_comm]
    · exact Finset.prod_comm
  · apply Finset.prod_congr rfl
    intro i _
    have hm : monomial (pairedExponent i) (a i) = C (a i)*X (.inl i)*X (.inr i) := by
      rw [C_mul_X_eq_monomial, X, MvPolynomial.monomial_mul]
      congr 1
      · ext v; cases v; simp [pairedExponent]
      · simp
    rw [hm, map_mul, map_mul]

 theorem full_gate_count (a : I → R) (q : ℕ) (hq : q ≤ Fintype.card I) :
    (fullGateEdges a (Fintype.card I-q)).coeff (allOnes _) =
    (((Fintype.card I-q).factorial : R)^2) *
      (∏ i, (1 + Polynomial.C (a i)*Polynomial.X)).coeff q := by
  have hr := coeff_rename_mapDomain sumSquareSplit sumSquareSplit.injective
    (fullGateEdges a (Fintype.card I-q)) (allOnes _)
  rw [allOnes_map_equiv] at hr
  have hc : (gateCrossEdges (I := I) (R := R) (Fintype.card I-q)).coeff
      (allOnes _) = gateOuter (Fintype.card I-q) := gateCrossEdges_coefficient _
  rw [← hr, allOnes_sum, coeff_nested, full_gate_split, mul_comm, coeff_C_mul, hc, mul_comm]
  rw [allOnes_sum, ← subset_univ_ones]
  exact gate_filters_prescribed_count a q hq
end PermanentBorder.Selector.Gates

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.AffineSelectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

omit [DecidableEq I] in
 theorem selectorSplit_coeff (h : ℕ) (p : MvPolynomial (SelectorOuter I h ⊕ SelectorOuter I h) R) :
    p.coeff (allOnes _) = ((selectorSplit h p).coeff (allOnes (SelectorGateVars I h))).coeff (allOnes (I ⊕ I)) := by
  have hr := coeff_rename_mapDomain (selectorSplitEquiv h) (selectorSplitEquiv h).injective p (allOnes _)
  rw [allOnes_map_equiv] at hr
  rw [← hr]
  have ho : allOnes (SelectorGateVars I h ⊕ (I ⊕ I)) =
    (allOnes (SelectorGateVars I h)).sumElim (allOnes (I ⊕ I)) := by ext v; cases v <;> rfl
  rw [ho, coeff_nested]
  rfl

omit [DecidableEq I] in
 theorem selectorSplit_base (M : Matrix I I R) (h : ℕ) :
    selectorSplit h (baseEdges (selectorSrc h) (selectorDst h) (selectorBaseWeight M h)) =
    C (edgeProduct M) * ∏ c : Fin 2,
      ((∏ i : I, ∏ j : Fin h, (1 + X (c,.inl (.inl i))*X (c,.inr (.inr j)))) *
       (∏ j : Fin h, ∏ i : I, (1 + X (c,.inl (.inr j))*X (c,.inr (.inl i))))) := by
  classical
  have hm (i j : SelectorOuter I h) (r : R) : monomial (edgeExponent (i,j)) r =
      C r * X (.inl i) * X (.inr j) := by
    rw [C_mul_X_eq_monomial, X, MvPolynomial.monomial_mul]
    simp only [edgeExponent, mul_one]
  simp only [baseEdges, hm, map_prod, map_add, map_one, map_mul, Fintype.prod_sum_type,
    Fintype.prod_prod_type, selectorSrc, selectorDst, selectorBaseWeight,
    selectorSplit_C, selectorSplit_main_left, selectorSplit_main_right,
    selectorSplit_gate_left, selectorSplit_gate_right, one_mul]
  apply congrArg₂ (·*·)
  · simp only [edgeProduct, Fintype.prod_prod_type, map_prod, map_add, map_one]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    have hx : monomial (edgeExponent (i,j)) (M i j) = C (M i j)*X (.inl i)*X (.inr j) := by
      rw [C_mul_X_eq_monomial, X, MvPolynomial.monomial_mul]
      simp only [edgeExponent, mul_one]
    rw [hx, map_mul, map_mul]
  · simp only

omit [DecidableEq I] in
 theorem selectorSplit_choices (θ : I → R) (h : ℕ) :
    selectorSplit h (∏ g : Fin 2 × I, (1 + C (selectorWeight θ g) *
      X (.inl (selectorMain h g))*X (.inl (selectorGate h g))*
      X (.inr (selectorMain h g))*X (.inr (selectorGate h g)))) =
    ∏ c : Fin 2, ∏ i : I, (1 + C (selectorBoundaryWeight θ c i)*
      X (c,.inl (.inl i))*X (c,.inr (.inl i))) := by
  simp only [map_prod, map_add, map_one, map_mul, Fintype.prod_prod_type,
    selectorMain, selectorGate, selectorSplit_C, selectorSplit_main_left,
    selectorSplit_main_right, selectorSplit_gate_left, selectorSplit_gate_right,
    selectorBoundaryWeight]
  apply Finset.prod_congr rfl
  intro c _
  apply Finset.prod_congr rfl
  intro i _
  ring

omit [DecidableEq I] in
 theorem selectorSplit_boundary (M : Matrix I I R) (θ : I → R) (h : ℕ) :
    selectorSplit h (selectorBoundary M θ h) =
    C (edgeProduct M) * ∏ c : Fin 2, rename (fun v => (c,v))
      (Gates.fullGateEdges (selectorBoundaryWeight θ c) h) := by
  rw [selectorBoundary, map_mul, selectorSplit_base, selectorSplit_choices, mul_assoc,
    ← Finset.prod_mul_distrib]
  apply congrArg (C (edgeProduct M)*·)
  apply Finset.prod_congr rfl
  intro c _
  simp only [Gates.fullGateEdges, map_mul, map_prod, map_add, map_one, rename_X, rename_C]
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
 theorem allOnes_block {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] :
    allOnes (A × B) = blockExponent (fun _ : A => allOnes B) := by
  ext ⟨a,b⟩
  simp

 theorem two_gates_count (a : Fin 2 → I → R) (q : ℕ) (hq : q ≤ Fintype.card I) :
    (∏ c : Fin 2, rename (fun v => (c,v))
      (Gates.fullGateEdges (a c) (Fintype.card I-q))).coeff (allOnes _) =
    (((Fintype.card I-q).factorial : R)^4) *
      (elementaryBoundary (a 0) q * elementaryBoundary (a 1) q) := by
  rw [allOnes_block, coeff_independent_blocks]
  have hc (c : Fin 2) : (Gates.fullGateEdges (a c) (Fintype.card I-q)).coeff (allOnes _) =
    (((Fintype.card I-q).factorial : R)^2) * elementaryBoundary (a c) q :=
      Gates.full_gate_count (a c) q hq
  simp_rw [hc]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.succ_zero_eq_one]
  ring

 theorem selector_boundary_coeff (M : Matrix I I R) (θ : I → R) (q : ℕ)
    (hq : q ≤ Fintype.card I) :
    (selectorBoundary M θ (Fintype.card I-q)).coeff (allOnes _) =
      (((Fintype.card I-q).factorial : R)^4) * diagonalCoefficient M θ q := by
  rw [selectorSplit_coeff, selectorSplit_boundary, coeff_C_mul, two_gates_count _ q hq]
  have h0 : selectorBoundaryWeight θ 0 = fun i => X (.inl i)*X (.inr i) := by
    funext i; simp [selectorBoundaryWeight, selectorWeight]
  have h1 : selectorBoundaryWeight θ 1 = fun i => C (θ i)*X (.inl i)*X (.inr i) := by
    funext i; simp [selectorBoundaryWeight, selectorWeight]
  rw [h0,h1]
  have hc : (((Fintype.card I-q).factorial : MvPolynomial (I ⊕ I) R)^4) =
    C (((Fintype.card I-q).factorial : R)^4) := by simp only [map_pow, map_natCast]
  rw [hc]
  have hp (p a b : MvPolynomial (I ⊕ I) R) (c : R) : p * (C c * (a*b)) = C c * (p*a*b) := by ring
  rw [hp, coeff_C_mul, ← diagonalCoefficient_boundary]

 theorem selector_matrix_permanent (M : Matrix I I R) (θ : I → R) (q : ℕ)
    (hq : q ≤ Fintype.card I) :
    (selectorMatrix M θ (Fintype.card I-q)).permanent =
    ((-2:R)^(2 * Fintype.card I) * ((Fintype.card I-q).factorial : R)^4) *
      diagonalCoefficient M θ q := by
  rw [selectorMatrix, expanded_permanent]
  change (-2:R)^Fintype.card (Fin 2 × I) *
    (selectorBoundary M θ (Fintype.card I-q)).coeff (allOnes _) = _
  rw [selector_boundary_coeff M θ q hq]
  simp only [Fintype.card_prod, Fintype.card_fin, mul_assoc]

omit [DecidableEq I] in
 theorem selector_matrix_card (q : ℕ) (hq : q ≤ Fintype.card I) :
    Fintype.card (ExpandedVertex (SelectorOuter I (Fintype.card I-q)) (Fin 2 × I)) =
      11 * Fintype.card I - 2*q := by
  simp only [ExpandedVertex, SelectorOuter, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [CommSemiring R]
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
 theorem rename_inner (p : MvPolynomial A R) :
    sumRingEquiv R A B (rename Sum.inl p) = map C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
 theorem rename_outer (p : MvPolynomial B R) :
    sumRingEquiv R A B (rename Sum.inr p) = C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp]

 theorem permanent_block_diagonal (P : Matrix A A R) (Q : Matrix B B R) :
    (Matrix.fromBlocks P 0 0 Q).permanent = P.permanent * Q.permanent := by
  rw [← row_product_permanent]
  have hp : (∏ i, ∑ j, C (Matrix.fromBlocks P 0 0 Q i j) * X j) =
      rename Sum.inl (∏ i, ∑ j, C (P i j)*X j) *
      rename Sum.inr (∏ i, ∑ j, C (Q i j)*X j) := by
    simp [Fintype.prod_sum_type, Fintype.sum_sum_type, Matrix.fromBlocks]
  rw [hp]
  have hones : allOnes (A ⊕ B) = (allOnes A).sumElim (allOnes B) := by
    ext i; cases i <;> rfl
  rw [hones, coeff_nested, map_mul, rename_inner, rename_outer, mul_comm, coeff_C_mul,
    coeff_map, mul_comm, coeff_C_mul, row_product_permanent, row_product_permanent]

 theorem permanent_reindex_equiv (P : Matrix A A R) (e : B ≃ A) :
    (P.submatrix e e).permanent = P.permanent := by
  classical
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ ?_
  intro σ
  simpa only [Matrix.submatrix_apply, Equiv.permCongr_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply] using
    (e.prod_comp (fun i => P ((Equiv.permCongr e σ) i) i))
end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

 theorem selectorMatrix_affine (M : Matrix I I R) (θ : I → R) (h : ℕ)
    (r c : SelectorVertex I h) :
    selectorMatrix M θ h r c = selectorMatrix 0 θ h r c + selectorLinearEntries M h r c := by
  classical
  simp only [selectorMatrix, expandedMatrix, graphMatrix, Fintype.sum_sum_type,
    Fintype.sum_prod_type, expandedWeight, selectorBaseWeight, expandedSrc, expandedDst,
    selectorSrc, selectorDst]
  rcases r with (a|a)|a <;> rcases c with (b|b)|b <;>
    simp [selectorLinearEntries, ite_and]
end PermanentBorder.Selector
namespace PermanentBorder.Selector
open MvPolynomial
variable {I R S : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]

 theorem gadgetH_map (f : R →+* S) (r c : Fin 3) :
    f (gadgetH (R := R) r c) = gadgetH r c := by
  fin_cases r <;> fin_cases c <;> simp [gadgetH]

 theorem selectorMatrix_map (f : R →+* S) (M : Matrix I I R) (θ : I → R) (h : ℕ)
    (r c : SelectorVertex I h) :
    selectorMatrix (M.map f) (fun i => f (θ i)) h r c = f (selectorMatrix M θ h r c) := by
  classical
  simp only [selectorMatrix, expandedMatrix, graphMatrix, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [apply_ite f, map_zero]
  split_ifs
  · rcases e with (⟨i,j⟩|⟨c,⟨i,j⟩|⟨j,i⟩⟩)|⟨g,b|r|⟨r,c⟩⟩ <;>
      simp only [expandedWeight, selectorBaseWeight, Matrix.map_apply, selectorWeight] <;>
      (try split_ifs) <;> simp_all [gadgetH_map, map_ofNat]
  · rfl

 theorem selectorLinearEntries_sum (M : Matrix I I R) (h : ℕ)
    (r c : SelectorVertex I h) :
    selectorLinearEntries M h r c = ∑ ij, selectorCoefficientMatrix h ij r c * M ij.1 ij.2 := by
  classical
  rcases r with (a|a)|a <;> rcases c with (b|b)|b <;>
    simp [selectorLinearEntries, selectorCoefficientMatrix, Fintype.sum_prod_type, ite_and]

 theorem selector_polynomial_affine (θ : I → R) (h : ℕ) (r c : SelectorVertex I h) :
    selectorMatrix (Matrix.of fun i j => X (i,j)) (fun i => C (θ i)) h r c =
      C (selectorMatrix 0 θ h r c) +
        ∑ ij : I × I, C (selectorCoefficientMatrix h ij r c) * X ij := by
  rw [selectorMatrix_affine]
  have hm : (0 : Matrix I I R).map (C : R →+* MvPolynomial (I × I) R) = 0 := by ext; simp
  rw [← hm, selectorMatrix_map]
  congr 1
  rw [selectorLinearEntries_sum]
  apply Finset.sum_congr rfl
  intro ij _
  unfold selectorCoefficientMatrix
  split_ifs <;> simp_all
end PermanentBorder.Selector

namespace PermanentBorder
open MvPolynomial
variable {σ V T : Type*} [Fintype σ] [Fintype V] [DecidableEq V]

 theorem affineSubstitution_permanent (m : ℕ) (b : Variables m → ℂ)
    (B : Variables m → σ → ℂ) :
    affineSubstitution b B (permanentPolynomial m) =
      (Matrix.of fun i j => C (b (i,j)) + ∑ w, C (B (i,j) w)*X w).permanent := by
  classical
  unfold permanentPolynomial affineSubstitution
  simp only [map_sum, map_prod, aeval_X]
  exact Matrix.permanent_transpose
    (Matrix.of fun i j => C (b (i,j)) + ∑ w, C (B (i,j) w)*X w)

omit [Fintype V] [DecidableEq V] in
 theorem polynomial_fromBlocks_affine [Fintype T] [DecidableEq T]
    (P : Matrix V V (Poly σ)) (A₀ : Matrix V V ℂ) (A : σ → Matrix V V ℂ)
    (hP : ∀ i j, P i j = C (A₀ i j) + ∑ w, C (A w i j)*X w)
    (i j : V ⊕ T) :
    Matrix.fromBlocks P 0 0 1 i j =
      C (Matrix.fromBlocks A₀ 0 0 (1 : Matrix T T ℂ) i j) +
      ∑ w, C (Matrix.fromBlocks (A w) 0 0 (0 : Matrix T T ℂ) i j)*X w := by
  classical
  rcases i with i|i <;> rcases j with j|j
  · exact hP i j
  · simp [Matrix.fromBlocks]
  · simp [Matrix.fromBlocks]
  · simp [Matrix.fromBlocks, Matrix.one_apply]

 theorem exists_affine_permanent_padding (m : ℕ) (hm : Fintype.card V ≤ m)
    (P : Matrix V V (Poly σ)) (A₀ : Matrix V V ℂ) (A : σ → Matrix V V ℂ)
    (hP : ∀ i j, P i j = C (A₀ i j) + ∑ w, C (A w i j)*X w) :
    ∃ (b : Variables m → ℂ) (B : Variables m → σ → ℂ),
      affineSubstitution b B (permanentPolynomial m) = P.permanent := by
  classical
  let T := V ⊕ Fin (m-Fintype.card V)
  let e : Fin m ≃ T := Fintype.equivOfCardEq (by
    simp only [T, Fintype.card_fin, Fintype.card_sum]
    omega)
  let C₀ : Matrix T T ℂ := Matrix.fromBlocks A₀ 0 0 1
  let A' : σ → Matrix T T ℂ := fun w => Matrix.fromBlocks (A w) 0 0 0
  let P' : Matrix T T (Poly σ) := Matrix.fromBlocks P 0 0 1
  let b : Variables m → ℂ := fun ij => C₀ (e ij.1) (e ij.2)
  let B : Variables m → σ → ℂ := fun ij w => A' w (e ij.1) (e ij.2)
  refine ⟨b,B,?_⟩
  rw [affineSubstitution_permanent]
  have he : (Matrix.of fun i j => C (b (i,j)) + ∑ w, C (B (i,j) w)*X w) =
      P'.submatrix e e := by
    funext i j
    exact (polynomial_fromBlocks_affine P A₀ A hP (e i) (e j)).symm
  rw [he, Selector.permanent_reindex_equiv, Selector.permanent_block_diagonal,
    Matrix.permanent_one, mul_one]
end PermanentBorder

namespace PermanentBorder
open MvPolynomial

 theorem selectorScalar_ne_zero (k q : ℕ) : selectorScalar k q ≠ 0 := by
  unfold selectorScalar
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

 theorem exists_selector_affine_projection (k q m : ℕ) (hq : q ≤ k)
    (hm : 11*k-2*q ≤ m) (θ : Fin k → ℂ) :
    ∃ (b : Variables m → ℂ) (B : Variables m → Variables k → ℂ),
      affineSubstitution b B (permanentPolynomial m) =
        selectorScalar k q • coefficientPolynomial k q θ := by
  classical
  let V := Selector.SelectorVertex (Fin k) (Fintype.card (Fin k)-q)
  let P : Matrix V V (Poly (Variables k)) :=
    Selector.selectorMatrix (Matrix.of fun i j => X (i,j)) (fun i => C (θ i)) (Fintype.card (Fin k)-q)
  have hcard : Fintype.card V = 11*k-2*q := by
    simpa only [V, Selector.SelectorVertex, Fintype.card_fin] using
      (Selector.selector_matrix_card (I := Fin k) q (by simpa using hq))
  obtain ⟨b,B,h⟩ := exists_affine_permanent_padding m (by omega : Fintype.card V ≤ m) P
    (Selector.selectorMatrix 0 θ (Fintype.card (Fin k)-q)) (Selector.selectorCoefficientMatrix (Fintype.card (Fin k)-q))
    (Selector.selector_polynomial_affine θ (Fintype.card (Fin k)-q))
  refine ⟨b,B,h.trans ?_⟩
  have he := Selector.selector_matrix_permanent
    (Matrix.of fun i j : Fin k => (X (i,j) : Poly (Variables k)))
    (fun i => C (θ i)) q (by simpa using hq)
  simp only [Fintype.card_fin] at he
  change P.permanent = _ at he
  rw [he, smul_eq_C_mul]
  simp only [selectorScalar, coefficientPolynomial, map_mul, map_pow, map_neg,
    map_ofNat, map_natCast]

 theorem HasBorderDeterminant.coefficientPolynomial_oai {k q m n : ℕ}
    (h : HasBorderDeterminant n (permanentPolynomial m)) (hq : q ≤ k)
    (hm : 11*k-2*q ≤ m) (θ : Fin k → ℂ) :
    HasBorderDeterminant n (coefficientPolynomial k q θ) := by
  obtain ⟨b,B,hproj⟩ := exists_selector_affine_projection k q m hq hm θ
  have hg := (h.affineSubstitution b B).smul (selectorScalar k q)⁻¹
  rw [hproj, smul_smul, inv_mul_cancel₀ (selectorScalar_ne_zero k q), one_smul] at hg
  exact hg
end PermanentBorder

end OAI
end

theorem solution : type_of% @OAI.PermanentBorder.HasBorderDeterminant.coefficientPolynomial_oai := @OAI.PermanentBorder.HasBorderDeterminant.coefficientPolynomial_oai
