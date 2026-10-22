-- Prove2me | solution 1 for HTInsensBW.PhaseType.lemma_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T23:17:15.143877+00:00
-- url     : https://prove2.me/submissions/896618a2-b832-4c42-917a-8ea2f8df244f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct
import Theorems.Thm_HTInsensBW_PhaseType_lemma_11

namespace HTInsensBWL5

open HTInsensBW.PhaseType Matrix MeasureTheory NormedSpace Finset

lemma subgen_mulVec_apply (D : PhaseTypeD) (v : Phase D → ℝ) (b : Fin D.B) (i : Fin (D.len b)) :
    (subgen D *ᵥ v) ⟨b, i⟩ =
      D.rate b * ((if h : (i : ℕ) + 1 < D.len b then v ⟨b, ⟨i + 1, h⟩⟩ else 0) - v ⟨b, i⟩) := by
  simp only [mulVec, dotProduct, subgen, Matrix.of_apply]
  rw [Fintype.sum_sigma, Finset.sum_eq_single b]
  · have e : ∀ j : Fin (D.len b),
        ((if b = b ∧ (j : ℕ) = i then -D.rate b
          else if b = b ∧ (j : ℕ) = i + 1 then D.rate b else 0) * v ⟨b, j⟩) =
        (if j = i then -D.rate b * v ⟨b, j⟩ else 0) +
        (if (j : ℕ) = i + 1 then D.rate b * v ⟨b, j⟩ else 0) := by
      intro j
      by_cases h1 : j = i
      · subst h1; simp
      · have h1' : (j : ℕ) ≠ i := fun h => h1 (Fin.ext h)
        simp [h1, h1']
    simp only [true_and] at e ⊢
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_ite_eq' ]
    simp only [Finset.mem_univ, if_true]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i + 1, h⟩]
      · simp; ring
      · intro j _ hj
        have : (j : ℕ) ≠ i + 1 := fun h' => hj (Fin.ext h')
        simp [this]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · rw [Finset.sum_eq_zero]
      · ring
      · intro j _
        have : (j : ℕ) ≠ i + 1 := by
          intro h'; apply h; rw [← h']; exact j.2
        simp [this]
  · intro b' _ hne
    apply Finset.sum_eq_zero
    intro j _
    have : ¬ (b = b') := fun h => hne h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- the expected-remaining-work vector `(-S)^{-1} 1` -/
noncomputable def cvec (D : PhaseTypeD) : Phase D → ℝ :=
  fun k => ((D.len k.1 : ℝ) - (k.2 : ℕ)) / D.rate k.1

lemma cvec_nonneg (D : PhaseTypeD) (k : Phase D) : 0 ≤ cvec D k := by
  unfold cvec
  have h1 : ((k.2 : ℕ) : ℝ) ≤ D.len k.1 := by exact_mod_cast k.2.2.le
  exact div_nonneg (by linarith) (D.rate_pos _).le

lemma subgen_cvec (D : PhaseTypeD) : subgen D *ᵥ cvec D = fun _ => -1 := by
  funext ⟨b, i⟩
  rw [subgen_mulVec_apply]
  have hμ := (D.rate_pos b).ne'
  split_ifs with h
  · simp only [cvec]; push_cast; field_simp; ring
  · have hi : (i : ℕ) + 1 = D.len b := by have := i.2; omega
    simp only [cvec]
    have : (D.len b : ℝ) = (i : ℕ) + 1 := by exact_mod_cast hi.symm
    rw [this]; field_simp; ring

lemma subgen_ker (D : PhaseTypeD) (v : Phase D → ℝ) (hv : subgen D *ᵥ v = 0) : v = 0 := by
  funext ⟨b, i⟩
  have hrec : ∀ i : Fin (D.len b),
      v ⟨b, i⟩ = if h : (i : ℕ) + 1 < D.len b then v ⟨b, ⟨i + 1, h⟩⟩ else 0 := by
    intro i
    have := congrFun hv ⟨b, i⟩
    rw [subgen_mulVec_apply] at this
    simp only [Pi.zero_apply, mul_eq_zero, (D.rate_pos b).ne', false_or] at this
    linarith
  have key : ∀ d : ℕ, ∀ i : Fin (D.len b), D.len b - 1 - (i : ℕ) = d → v ⟨b, i⟩ = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi
      rw [hrec i, dif_neg]
      omega
    | succ d ih =>
      intro i hi
      have h : (i : ℕ) + 1 < D.len b := by omega
      rw [hrec i, dif_pos h]
      exact ih ⟨i + 1, h⟩ (by simp; omega)
  exact key _ i rfl

lemma subgen_injective (D : PhaseTypeD) : Function.Injective (subgen D).mulVec := by
  intro v w h
  have : subgen D *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 h
  exact sub_eq_zero.1 (subgen_ker D _ this)

lemma neg_subgen_isUnit (D : PhaseTypeD) : IsUnit (-subgen D) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w h
  apply subgen_injective D
  have : -(subgen D *ᵥ v) = -(subgen D *ᵥ w) := by
    rw [← Matrix.neg_mulVec, ← Matrix.neg_mulVec]; exact h
  exact neg_injective this

lemma inv_one_eq_cvec (D : PhaseTypeD) : (-subgen D)⁻¹ *ᵥ (fun _ => (1 : ℝ)) = cvec D := by
  have hu := neg_subgen_isUnit D
  have hc : (-subgen D) *ᵥ cvec D = fun _ => 1 := by
    rw [Matrix.neg_mulVec, subgen_cvec]; funext; simp
  rw [← hc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
    Matrix.one_mulVec]

lemma meanSize_eq (D : PhaseTypeD) : meanSize D = D.init ⬝ᵥ cvec D := by
  rw [meanSize, inv_one_eq_cvec]

lemma cvec_pos (D : PhaseTypeD) (k : Phase D) : 0 < cvec D k := by
  unfold cvec
  have h1 : ((k.2 : ℕ) : ℝ) < D.len k.1 := by exact_mod_cast k.2.2
  exact div_pos (by linarith) (D.rate_pos _)

lemma pow_entries_nonneg {K : Type*} [Fintype K] [DecidableEq K] (B : Matrix K K ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (n : ℕ) : ∀ i j, 0 ≤ (B ^ n) i j := by
  induction n with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hB l j))

set_option backward.isDefEq.respectTransparency false in
open scoped Norms.Operator in
lemma exp_ge_one {K : Type*} [Fintype K] [DecidableEq K] (B : Matrix K K ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (i j : K) : (1 : Matrix K K ℝ) i j ≤ NormedSpace.exp B i j := by
  have hs : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • B ^ n)) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) B
  have hsi : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • B ^ n) i) := Pi.summable.1 hs i
  have hsij : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • B ^ n) i j) := Pi.summable.1 hsi j
  have e : NormedSpace.exp B i j = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • B ^ n) i j := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    show (∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • B ^ n)) i j = _
    rw [tsum_apply hs, tsum_apply hsi]
  rw [e]
  have h0 : ((((0 : ℕ).factorial : ℝ))⁻¹ • B ^ 0) i j = (1 : Matrix K K ℝ) i j := by simp
  rw [← h0]
  apply hsij.le_tsum 0
  intro n _
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (by positivity) (pow_entries_nonneg B hB n i j)

lemma exitRate_eq (D : PhaseTypeD) (k : Phase D) :
    exitRate D k = -(subgen D *ᵥ (fun _ => (1 : ℝ))) k := by
  simp [exitRate, mulVec, dotProduct]

lemma exitRate_nonneg (D : PhaseTypeD) (k : Phase D) : 0 ≤ exitRate D k := by
  obtain ⟨b, i⟩ := k
  rw [exitRate_eq, subgen_mulVec_apply]
  have := D.rate_pos b
  split_ifs <;> nlinarith

lemma subgen_offdiag_nonneg (D : PhaseTypeD) (k₁ k₂ : Phase D) (h : k₁ ≠ k₂) :
    0 ≤ subgen D k₁ k₂ := by
  obtain ⟨b, i⟩ := k₁
  obtain ⟨b', j⟩ := k₂
  simp only [subgen, Matrix.of_apply]
  split_ifs with h1 h2
  · exfalso; apply h
    obtain ⟨rfl, h1⟩ := h1
    have : j = i := Fin.ext h1
    rw [this]
  · exact (D.rate_pos _).le
  · exact le_rfl


/-- a uniform upper bound on the block rates -/
noncomputable def rmax (D : PhaseTypeD) : ℝ := ∑ b, D.rate b

lemma rate_le_rmax (D : PhaseTypeD) (b : Fin D.B) : D.rate b ≤ rmax D :=
  Finset.single_le_sum (f := D.rate) (fun b _ => (D.rate_pos b).le) (Finset.mem_univ b)

lemma metzler_nonneg (D : PhaseTypeD) (σ : ℝ) (hσ : 0 ≤ σ) (k k' : Phase D) :
    0 ≤ (σ • (subgen D + rmax D • (1 : Matrix (Phase D) (Phase D) ℝ))) k k' := by
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
  apply mul_nonneg hσ
  by_cases h : k = k'
  · subst h
    have : subgen D k k = -D.rate k.1 := by
      simp [subgen]
    rw [this, if_pos rfl, mul_one]
    linarith [rate_le_rmax D k.1]
  · rw [if_neg h, mul_zero, add_zero]
    exact subgen_offdiag_nonneg D k k' h

set_option backward.isDefEq.respectTransparency false in
lemma exp_subgen_apply (D : PhaseTypeD) (σ : ℝ) (i j : Phase D) :
    NormedSpace.exp (σ • subgen D) i j = Real.exp (-(σ * rmax D)) *
      NormedSpace.exp (σ • (subgen D + rmax D • (1 : Matrix (Phase D) (Phase D) ℝ))) i j := by
  set A := σ • (subgen D + rmax D • (1 : Matrix (Phase D) (Phase D) ℝ)) with hA
  set c := -(σ * rmax D) with hc
  have e1 : σ • subgen D = c • (1 : Matrix (Phase D) (Phase D) ℝ) + A := by
    rw [hA, hc, smul_add, smul_smul]; ext a b; simp [Matrix.one_apply]
  have hcomm : Commute (c • (1 : Matrix (Phase D) (Phase D) ℝ)) A :=
    (Commute.one_left A).smul_left c
  rw [e1, Matrix.exp_add_of_commute _ _ hcomm]
  have e2 : NormedSpace.exp (c • (1 : Matrix (Phase D) (Phase D) ℝ)) =
      Real.exp c • (1 : Matrix (Phase D) (Phase D) ℝ) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1
    funext k
    rw [Pi.coe_exp, Real.exp_eq_exp_ℝ]
  rw [e2, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]

lemma exp_subgen_diag (D : PhaseTypeD) (σ : ℝ) (hσ : 0 ≤ σ) (i j : Phase D) :
    Real.exp (-(σ * rmax D)) * (1 : Matrix (Phase D) (Phase D) ℝ) i j ≤
      NormedSpace.exp (σ • subgen D) i j := by
  rw [exp_subgen_apply]
  exact mul_le_mul_of_nonneg_left (exp_ge_one _ (metzler_nonneg D σ hσ) i j) (Real.exp_pos _).le

lemma neg_subgen_inv_commute (D : PhaseTypeD) (σ : ℝ) :
    Commute (-subgen D)⁻¹ (NormedSpace.exp (σ • subgen D)) := by
  have hu := neg_subgen_isUnit D
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : Commute (-subgen D)⁻¹ (-subgen D) := by
    unfold Commute SemiconjBy
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]
  have h2 : Commute (-subgen D)⁻¹ (σ • subgen D) := by
    have := h1.neg_right
    rw [neg_neg] at this
    exact this.smul_right σ
  exact h2.exp_right

lemma denom_pos (D : PhaseTypeD) (σ : ℝ) (hσ : 0 ≤ σ) : 0 < denom D σ := by
  unfold denom Pvec
  rw [Matrix.mulVec_mulVec, (neg_subgen_inv_commute D σ).eq, ← Matrix.mulVec_mulVec,
    inv_one_eq_cvec]
  set E := NormedSpace.exp (σ • subgen D) with hE
  have hEnn : ∀ i j, 0 ≤ E i j := fun i j =>
    le_trans (mul_nonneg (Real.exp_pos _).le (by simp only [Matrix.one_apply]; split_ifs <;> norm_num))
      (exp_subgen_diag D σ hσ i j)
  have hrow : ∀ k, Real.exp (-(σ * rmax D)) * cvec D k ≤ (E *ᵥ cvec D) k := by
    intro k
    simp only [mulVec, dotProduct]
    have h1 : E k k * cvec D k ≤ ∑ j, E k j * cvec D j :=
      Finset.single_le_sum (f := fun j => E k j * cvec D j)
        (fun j _ => mul_nonneg (hEnn k j) (cvec_pos D j).le) (Finset.mem_univ k)
    have h2 : Real.exp (-(σ * rmax D)) ≤ E k k := by
      have := exp_subgen_diag D σ hσ k k
      simpa using this
    nlinarith [cvec_pos D k]
  obtain ⟨k, hk⟩ : ∃ k, 0 < D.init k := by
    by_contra h
    push_neg at h
    have : ∑ k, D.init k ≤ 0 := Finset.sum_nonpos (fun k _ => h k)
    linarith [D.init_sum]
  simp only [dotProduct]
  apply Finset.sum_pos' (fun j _ => mul_nonneg (D.init_nonneg j)
    (le_trans (mul_nonneg (Real.exp_pos _).le (cvec_pos D j).le) (hrow j)))
  refine ⟨k, Finset.mem_univ k, mul_pos hk ?_⟩
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (cvec_pos D k)) (hrow k)


set_option backward.isDefEq.respectTransparency false in
open scoped Norms.Operator in
lemma P_hasDeriv (D : PhaseTypeD) (k : Phase D) (σ : ℝ) :
    HasDerivAt (fun t => Pvec D t k) ((subgen D *ᵥ Pvec D σ) k) σ := by
  let L : Matrix (Phase D) (Phase D) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => (M *ᵥ fun _ => (1 : ℝ)) k
      map_add' := fun A B => by simp [Matrix.add_mulVec]
      map_smul' := fun c A => by simp [Matrix.smul_mulVec] }
  have hL := (LinearMap.toContinuousLinearMap L).hasFDerivAt (x := NormedSpace.exp (σ • subgen D))
  have h := hL.comp_hasDerivAt σ (hasDerivAt_exp_smul_const' (subgen D) σ)
  have h2 := h.congr_deriv (show (LinearMap.toContinuousLinearMap L)
      (subgen D * NormedSpace.exp (σ • subgen D)) = (subgen D *ᵥ Pvec D σ) k by
    simp [L, Pvec, Matrix.mulVec_mulVec])
  exact h2

lemma Pvec_zero (D : PhaseTypeD) : Pvec D 0 = fun _ => 1 := by
  unfold Pvec
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]

variable {L R : ℕ}

end HTInsensBWL5

open HTInsensBW.PhaseType HTInsensBWL5 Matrix MeasureTheory Finset Filter Topology

theorem solution {L R : ℕ} (N : BWNetwork L R)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r) :
    ∀ r, (1 / N.κ r) • (phaseLoad (N.D r) (N.lam0 r) ᵥ* (Mr N r * (-subgen (N.D r))ᵀ)) =
      fun _ => (1 : ℝ) := by
  intro r
  have hint := ((lemma_11 N hκ hlam0).1 r).1
  set D := N.D r with hD
  set lam := N.lam0 r with hlamdef
  set κ := N.κ r with hκdef
  have hlam : 0 < lam := hlam0 r
  have hκ0 : 0 < κ := hκ r
  set ρ := phaseLoad D lam with hρ
  -- the key identity ρ ⬝ P = λ denom
  have hρP : ∀ σ, ρ ⬝ᵥ Pvec D σ = lam * denom D σ := by
    intro σ
    simp only [hρ, phaseLoad, denom, smul_dotProduct, smul_eq_mul]
    rw [Matrix.dotProduct_mulVec]
  have hsumM : ∀ (k₂ : Phase D) (σ : ℝ), 0 < σ →
      ∑ k₁, ρ k₁ * Mintegrand D k₁ k₂ σ = lam * Pvec D σ k₂ := by
    intro k₂ σ hσ
    have hd := (denom_pos D σ hσ.le).ne'
    simp only [Mintegrand]
    have : ∑ k₁, ρ k₁ * (Pvec D σ k₁ * Pvec D σ k₂ / denom D σ) =
        (ρ ⬝ᵥ Pvec D σ) * Pvec D σ k₂ / denom D σ := by
      simp only [dotProduct, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [this, hρP]
    field_simp
  -- integrability of P_k
  have hPint : ∀ k₂, IntegrableOn (fun σ => Pvec D σ k₂) (Set.Ioi 0) := by
    intro k₂
    have h1 : IntegrableOn (fun σ => (1 / lam) * ∑ k₁, ρ k₁ * Mintegrand D k₁ k₂ σ) (Set.Ioi 0) := by
      apply Integrable.const_mul
      exact integrable_finset_sum _ (fun k₁ _ => (hint k₁ k₂).const_mul _)
    refine h1.congr_fun (fun σ hσ => ?_) measurableSet_Ioi
    simp only
    rw [hsumM k₂ σ hσ]
    field_simp
  -- (ρᵀ M)_{k₂} = κ ∫ P_{k₂}
  have hρM : ∀ k₂, (ρ ᵥ* Mr N r) k₂ = κ * ∫ σ in Set.Ioi 0, Pvec D σ k₂ := by
    intro k₂
    simp only [vecMul, dotProduct, Mr, Matrix.of_apply]
    have e1 : ∑ k₁, ρ k₁ * (κ / lam * ∫ σ in Set.Ioi 0, Mintegrand D k₁ k₂ σ) =
        κ / lam * ∫ σ in Set.Ioi 0, ∑ k₁, ρ k₁ * Mintegrand D k₁ k₂ σ := by
      rw [integral_finset_sum _ (fun k₁ _ => (hint k₁ k₂).const_mul _), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₁ _
      rw [integral_const_mul]; ring
    rw [e1]
    have e2 : ∫ σ in Set.Ioi 0, ∑ k₁, ρ k₁ * Mintegrand D k₁ k₂ σ =
        ∫ σ in Set.Ioi 0, lam * Pvec D σ k₂ :=
      setIntegral_congr_fun measurableSet_Ioi (fun σ hσ => hsumM k₂ σ hσ)
    rw [e2, integral_const_mul]
    field_simp
  -- FTC for each k
  funext k
  set f : ℝ → ℝ := fun σ => Pvec D σ k with hf
  set f' : ℝ → ℝ := fun σ => (subgen D *ᵥ Pvec D σ) k with hf'
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt f (f' x) x := fun x _ => P_hasDeriv D k x
  have f'int : IntegrableOn f' (Set.Ioi 0) := by
    have : f' = fun σ => ∑ j, subgen D k j * Pvec D σ j := by
      funext σ; simp [hf', mulVec, dotProduct]
    rw [this]
    exact integrable_finset_sum _ (fun j _ => (hPint j).const_mul _)
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hderiv f'int (hPint k)
  have hcont : ContinuousWithinAt f (Set.Ici 0) 0 := (P_hasDeriv D k 0).continuousAt.continuousWithinAt
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv f'int hlim
  have hf0 : f 0 = 1 := by simp [hf, Pvec_zero]
  rw [hf0] at hFTC
  -- assemble
  rw [Pi.smul_apply, smul_eq_mul, ← Matrix.vecMul_vecMul]
  have e3 : ((ρ ᵥ* Mr N r) ᵥ* (-subgen D)ᵀ) k = κ * -∫ σ in Set.Ioi 0, f' σ := by
    rw [show (ρ ᵥ* Mr N r) = fun k₂ => κ * ∫ σ in Set.Ioi 0, Pvec D σ k₂ from funext hρM]
    simp only [vecMul, dotProduct, Matrix.transpose_apply]
    have : ∫ σ in Set.Ioi 0, f' σ = ∑ j, subgen D k j * ∫ σ in Set.Ioi 0, Pvec D σ j := by
      have : f' = fun σ => ∑ j, subgen D k j * Pvec D σ j := by
        funext σ; simp [hf', mulVec, dotProduct]
      rw [this, integral_finset_sum _ (fun j _ => (hPint j).const_mul _)]
      apply Finset.sum_congr rfl; intro j _; rw [integral_const_mul]
    rw [this, ← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    simp only [Matrix.neg_apply]; ring
  rw [e3, hFTC]
  field_simp
  ring
