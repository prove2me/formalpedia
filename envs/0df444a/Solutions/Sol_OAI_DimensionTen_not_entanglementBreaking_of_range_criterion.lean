-- Prove2me | solution 1 for OAI.DimensionTen.not_entanglementBreaking_of_range_criterion
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T11:00:55.233976+00:00
-- url     : https://prove2.me/submissions/2bca520b-8596-411d-8c5a-64047920b62b

import Mathlib
import Definitions.Def_DimensionTenPair

open Matrix Complex
open scoped Matrix ComplexOrder Kronecker
open OAI.DimensionTen

/-- The unnormalized maximally entangled matrix `Ω` on `ℂ^a ⊗ ℂ^a`. -/
noncomputable def omegaMat_dt (a : ℕ) : Matrix (Fin a × Fin a) (Fin a × Fin a) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (1 : ℂ) else 0

lemma omegaMat_dt_posSemidef (a : ℕ) : (omegaMat_dt a).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self
    (Matrix.of fun (_ : Fin 1) (p : Fin a × Fin a) => if p.1 = p.2 then (1 : ℂ) else 0)
  convert h using 1
  ext p q
  simp only [omegaMat_dt, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_one]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2]

lemma amplify_omega_dt {a b : ℕ} (F : Mat a → Mat b) :
    amplify F a (omegaMat_dt a) = choi F := by
  ext u v
  simp only [amplify, choi]
  congr 2

lemma kron_mulVec_product_dt {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (x : m → ℂ) (y : n → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun p : m × n => x p.1 * y p.2) = fun p => (A *ᵥ x) p.1 * (B *ᵥ y) p.2 := by
  ext ⟨p, q⟩
  simp only [Matrix.mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A positive semidefinite matrix annihilates every vector with vanishing quadratic form. -/
lemma psd_mulVec_eq_zero_of_form_zero_dt {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (z : n → ℂ)
    (h0 : star z ⬝ᵥ (M *ᵥ z) = 0) : M *ᵥ z = 0 := by
  obtain ⟨hH, hnn⟩ := posSemidef_iff_dotProduct_mulVec.mp hM
  by_contra hne
  set y := M *ᵥ z with hy
  -- the two real quantities
  have hcc : 0 ≤ star y ⬝ᵥ y := dotProduct_star_self_nonneg y
  have hdd : 0 ≤ star y ⬝ᵥ (M *ᵥ y) := hnn y
  obtain ⟨hcre, hcim⟩ := Complex.nonneg_iff.mp hcc
  obtain ⟨hdre, hdim⟩ := Complex.nonneg_iff.mp hdd
  set c : ℝ := (star y ⬝ᵥ y).re with hc
  set d : ℝ := (star y ⬝ᵥ (M *ᵥ y)).re with hd
  have hcC : star y ⬝ᵥ y = (c : ℂ) := Complex.ext (by simp [hc]) (by simp [← hcim])
  have hdC : star y ⬝ᵥ (M *ᵥ y) = (d : ℂ) := Complex.ext (by simp [hd]) (by simp [← hdim])
  have hcpos : 0 < c := by
    rcases lt_or_eq_of_le hcre with h | h
    · exact h
    · exfalso; apply hne
      apply dotProduct_star_self_eq_zero.mp
      rw [hcC, ← h]; simp
  -- cross terms
  have hcross1 : star y ⬝ᵥ (M *ᵥ z) = (c : ℂ) := by rw [← hy, hcC]
  have hcross2 : star z ⬝ᵥ (M *ᵥ y) = (c : ℂ) := by
    rw [dotProduct_mulVec, ← hH.eq, ← star_mulVec, ← hy, hcC]
  -- evaluate the form at z - t y
  set t : ℝ := c / (d + 1) with ht
  have htpos : 0 < t := by positivity
  have hform := hnn (z - (t : ℂ) • y)
  have hval : star (z - (t : ℂ) • y) ⬝ᵥ (M *ᵥ (z - (t : ℂ) • y)) =
      ((-2 * t * c + t ^ 2 * d : ℝ) : ℂ) := by
    rw [star_sub, star_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
      dotProduct_sub, dotProduct_sub, smul_dotProduct, smul_dotProduct, dotProduct_smul,
      dotProduct_smul, h0, hcross1, hcross2, hdC]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    push_cast
    ring
  rw [hval] at hform
  have hre := (Complex.nonneg_iff.mp hform).1
  simp only [Complex.ofReal_re] at hre
  -- but -2tc + t²d < 0
  have hd1 : 0 < d + 1 := by linarith
  have : -2 * t * c + t ^ 2 * d = -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
    rw [ht]; field_simp; ring
  rw [this] at hre
  have hneg : -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos _ (by positivity)
    nlinarith
  linarith

/-- A positive semidefinite summand's range is contained in the range of the sum. -/
lemma exists_mulVec_eq_of_psd_sum {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*}
    (s : Finset ι) (K : ι → Matrix n n ℂ) (hK : ∀ i ∈ s, (K i).PosSemidef)
    (i : ι) (hi : i ∈ s) (x : n → ℂ) :
    ∃ w, (∑ j ∈ s, K j) *ᵥ w = K i *ᵥ x := by
  set S := ∑ j ∈ s, K j with hSdef
  have hS : S.PosSemidef := posSemidef_sum s hK
  have hH : S.IsHermitian := hS.1
  set T := Matrix.toEuclideanLin S with hT
  have hsym : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hH
  have hadj : LinearMap.adjoint T = T := by
    rw [← LinearMap.star_eq_adjoint]
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint T).mp hsym
  have hrange : T.kerᗮ = LinearMap.range T := by
    rw [LinearMap.orthogonal_ker, hadj]
  -- the kernel of S is contained in the kernel of each summand
  have hker : ∀ z : n → ℂ, S *ᵥ z = 0 → K i *ᵥ z = 0 := by
    intro z hz
    have hsum : ∑ j ∈ s, star z ⬝ᵥ (K j *ᵥ z) = 0 := by
      have : star z ⬝ᵥ (S *ᵥ z) = 0 := by rw [hz, dotProduct_zero]
      rw [hSdef, Matrix.sum_mulVec, dotProduct_sum] at this
      exact this
    have hnn : ∀ j ∈ s, 0 ≤ star z ⬝ᵥ (K j *ᵥ z) :=
      fun j hj => (posSemidef_iff_dotProduct_mulVec.mp (hK j hj)).2 z
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i hi
    exact psd_mulVec_eq_zero_of_form_zero_dt (hK i hi) z hzero
  -- the target vector lies in the orthogonal complement of the kernel
  have hmem : (WithLp.toLp 2 (K i *ᵥ x) : EuclideanSpace ℂ n) ∈ LinearMap.range T := by
    rw [← hrange, Submodule.mem_orthogonal]
    intro z hz
    have hz' : S *ᵥ z.ofLp = 0 := by
      have h0 : T z = 0 := hz
      have := congrArg (fun v : EuclideanSpace ℂ n => v.ofLp) h0
      simpa [hT, Matrix.toEuclideanLin_apply] using this
    have hKz := hker z.ofLp hz'
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm, dotProduct_mulVec, ← (hK i hi).1.eq, ← star_mulVec, hKz]
    simp
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w.ofLp, ?_⟩
  have := congrArg (fun v : EuclideanSpace ℂ n => v.ofLp) hw
  simpa [hT, Matrix.toEuclideanLin_apply] using this

theorem solution {a b : ℕ} (F : Mat a → Mat b) (hne : choi F ≠ 0)
    (hr : ∀ u v w, choi F *ᵥ w = productVector u v → u = 0 ∨ v = 0) :
    ¬ EntanglementBreaking F := by
  intro hEB
  obtain ⟨_, hsep⟩ := hEB
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso; apply hne; subst h; ext u; exact u.1.elim0
    · exact h
  obtain ⟨r, A, B, hAB, hZ⟩ := hsep a ha (omegaMat_dt a) (omegaMat_dt_posSemidef a)
  rw [amplify_omega_dt] at hZ
  have hex : ∃ i, A i ⊗ₖ B i ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    rw [hZ]
    exact Finset.sum_eq_zero (fun i _ => h i)
  obtain ⟨i, hi⟩ := hex
  have hA : A i ≠ 0 := fun h => hi (by rw [h, Matrix.zero_kronecker])
  have hB : B i ≠ 0 := fun h => hi (by rw [h, Matrix.kronecker_zero])
  -- nonzero matrices move some vector
  have hvec : ∀ {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ), M ≠ 0 →
      ∃ x, M *ᵥ x ≠ 0 := by
    intro m _ _ M hM
    by_contra h
    push Not at h
    apply hM
    ext p q
    have := congrFun (h (Pi.single q 1)) p
    simpa [Matrix.mulVec_single_one] using this
  obtain ⟨x, hx⟩ := hvec (A i) hA
  obtain ⟨y, hy⟩ := hvec (B i) hB
  obtain ⟨w, hw⟩ := exists_mulVec_eq_of_psd_sum Finset.univ (fun j => A j ⊗ₖ B j)
    (fun j _ => ((hAB j).1).kronecker ((hAB j).2)) i (Finset.mem_univ _)
    (fun p => x p.1 * y p.2)
  simp only [Matrix.kronecker] at hZ
  rw [← hZ, kron_mulVec_product_dt] at hw
  rcases hr (A i *ᵥ x) (B i *ᵥ y) w hw with h | h
  · exact hx h
  · exact hy h
