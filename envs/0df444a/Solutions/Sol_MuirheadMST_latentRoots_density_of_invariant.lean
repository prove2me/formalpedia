-- Prove2me | solution 1 for MuirheadMST.latentRoots_density_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:11:59.070794+00:00
-- url     : https://prove2.me/submissions/9c8242e8-4fa0-4d1e-9ae1-20621b1b7c95

import Mathlib
import Definitions.Def_MuirheadMST_Wishart
import Theorems.Thm_MuirheadMST_measurable_latentRoots
import Theorems.Thm_MuirheadMST_lintegral_latentRoots_border
import Theorems.Thm_MuirheadMST_lintegral_latentRoots_border_diag
import Theorems.Thm_MuirheadMST_dixonAnderson_half

open MeasureTheory ProbabilityTheory MuirheadMST
open scoped Matrix

namespace WeylParent

noncomputable def cW (m : ℕ) : ℝ := Real.pi ^ ((m : ℝ) ^ 2 / 2) / multivariateGamma m ((m : ℝ) / 2)

lemma mvGamma_succ (m : ℕ) (a : ℝ) :
    multivariateGamma (m + 1) a =
      Real.pi ^ ((m : ℝ) / 2) * Real.Gamma a * multivariateGamma m (a - 1 / 2) := by
  unfold multivariateGamma
  rw [Fin.prod_univ_succ]
  have hπ : Real.pi ^ (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) / 4) =
      Real.pi ^ ((m : ℝ) / 2) * Real.pi ^ ((m : ℝ) * ((m : ℝ) - 1) / 4) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; push_cast; ring
  have hG : ∀ i : Fin m, Real.Gamma (a - ((i.succ : Fin (m + 1)) : ℝ) / 2) =
      Real.Gamma (a - 1 / 2 - (i : ℝ) / 2) := by
    intro i; congr 1; simp only [Fin.val_succ]; push_cast; ring
  simp only [hπ, hG, Fin.val_zero, CharP.cast_eq_zero, zero_div, sub_zero]
  ring

lemma cW_succ (m : ℕ) :
    cW (m + 1) = cW m * (Real.pi ^ (((m : ℝ) + 1) / 2) / Real.Gamma (((m : ℝ) + 1) / 2)) := by
  unfold cW
  rw [mvGamma_succ]
  have h1 : ((m + 1 : ℕ) : ℝ) / 2 - 1 / 2 = (m : ℝ) / 2 := by push_cast; ring
  have hπ : Real.pi ^ (((m + 1 : ℕ) : ℝ) ^ 2 / 2) =
      Real.pi ^ ((m : ℝ) / 2) * (Real.pi ^ ((m : ℝ) ^ 2 / 2) * Real.pi ^ (((m : ℝ) + 1) / 2)) := by
    rw [← Real.rpow_add Real.pi_pos, ← Real.rpow_add Real.pi_pos]; congr 1; push_cast; ring
  have hne : Real.pi ^ ((m : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  rw [h1, hπ, mul_assoc (Real.pi ^ ((m : ℝ) / 2)), mul_div_mul_left _ _ hne]
  push_cast
  ring

lemma cW_nonneg (m : ℕ) : 0 ≤ cW m := by
  unfold cW multivariateGamma
  refine div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
    (Finset.prod_nonneg fun i _ => (Real.Gamma_pos_of_pos ?_).le))
  have := i.isLt
  have : (i : ℝ) + 1 ≤ m := by exact_mod_cast this
  linarith

lemma vandermondeProd_nonneg {m : ℕ} {l : Fin m → ℝ} (hl : StrictAnti l) : 0 ≤ vandermondeProd l := by
  unfold vandermondeProd
  refine Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => ?_
  split_ifs with h
  · exact sub_nonneg.2 (hl h).le
  · exact zero_le_one

lemma measurable_vandermondeProd (m : ℕ) : Measurable (vandermondeProd : (Fin m → ℝ) → ℝ) := by
  unfold vandermondeProd
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  split_ifs <;> fun_prop

lemma measurableSet_strictAnti (m : ℕ) : MeasurableSet {l : Fin m → ℝ | StrictAnti l} := by
  have : {l : Fin m → ℝ | StrictAnti l} = ⋂ i, ⋂ j, ⋂ (_ : i < j), {l | l j < l i} := by
    ext l; simp [StrictAnti]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

lemma measurable_symC (m : ℕ) : Measurable (fun (a : {p : Fin m × Fin m // p.1 ≤ p.2} → ℝ) (i j : Fin m) =>
    if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), le_of_not_ge h⟩) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  by_cases h : i ≤ j <;> simp only [h, dite_true, dite_false] <;> exact measurable_pi_apply _

lemma measurable_diagArray (m : ℕ) : Measurable (diagArray : (Fin m → ℝ) → Fin m → Fin m → ℝ) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold diagArray
  by_cases h : i = j <;> simp only [h, if_true, if_false] <;> fun_prop

lemma ae_isHermitian (m : ℕ) : ∀ᵐ A ∂(symVolume m), (Matrix.of A).IsHermitian := by
  have hS : MeasurableSet {A : Fin m → Fin m → ℝ | (Matrix.of A).IsHermitian} := by
    have : {A : Fin m → Fin m → ℝ | (Matrix.of A).IsHermitian} = ⋂ i, ⋂ j, {A | A j i = A i j} := by
      ext A; simp [Matrix.IsSymm.ext_iff]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
  unfold symVolume
  rw [ae_map_iff (measurable_symC m).aemeasurable hS]
  refine ae_of_all _ fun a => ?_
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.le, not_le.2 h]
  · simp
  · simp [h.le, not_le.2 h]

lemma weyl_zero (h : (Fin 0 → ℝ) → ENNReal) :
    ∫⁻ A, h (latentRoots A) ∂(symVolume 0) =
      ∫⁻ l, (if StrictAnti l then ENNReal.ofReal (cW 0 * vandermondeProd l) else 0) * h l := by
  have hc : ∀ A : Fin 0 → Fin 0 → ℝ, h (latentRoots A) = h 0 := fun A => congrArg h (Subsingleton.elim _ _)
  have hr : ∀ l : Fin 0 → ℝ,
      (if StrictAnti l then ENNReal.ofReal (cW 0 * vandermondeProd l) else 0) * h l = h 0 := by
    intro l
    rw [Subsingleton.elim l 0, if_pos (Subsingleton.strictAnti _)]
    simp [cW, multivariateGamma, vandermondeProd]
  simp_rw [hc, hr, lintegral_const]
  unfold symVolume
  rw [Measure.map_apply (measurable_symC 0) MeasurableSet.univ]
  simp [volume_pi]


lemma eq_diag_of_invariant {m : ℕ} (f : (Fin m → Fin m → ℝ) → ENNReal)
    (hinv : ∀ H ∈ Matrix.orthogonalGroup (Fin m) ℝ, ∀ A,
      f (Matrix.of.symm (H * Matrix.of A * H.transpose)) = f A)
    (A : Fin m → Fin m → ℝ) (hA : (Matrix.of A).IsHermitian) :
    f A = f (diagArray (latentRoots A)) := by
  set U : Matrix (Fin m) (Fin m) ℝ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) with hUdef
  let σ : Fin m ≃ Fin m :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))).symm.trans (finCongr (Fintype.card_fin m))
  have hev : hA.eigenvalues = latentRoots A ∘ σ := by
    funext i
    simp only [Function.comp_apply, latentRoots, dif_pos hA]
    simp [Matrix.IsHermitian.eigenvalues, σ]
  set H := U.submatrix id σ.symm with hHdef
  have hU : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).1 hA.eigenvectorUnitary.2
  have hH : H ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff (Fin m) ℝ, hHdef, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv, hU]
    simp
  have hUH : U = H.submatrix id σ := by ext i j; simp [H]
  have hD : Matrix.of (diagArray (latentRoots A)) = Matrix.diagonal (latentRoots A) := by
    ext i j; simp [diagArray, Matrix.diagonal_apply]
  have key : Matrix.of A = H * Matrix.of (diagArray (latentRoots A)) * Hᵀ := by
    have hs := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp, hev,
      ← Matrix.submatrix_diagonal_equiv] at hs
    rw [hs, hD, ← hUdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      hUH, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp
  have := hinv H hH (diagArray (latentRoots A))
  rw [← key] at this
  simpa using this

/-- The secular density of `lintegral_latentRoots_border_diag`. -/
noncomputable def ρ {m : ℕ} (μ : Fin m → ℝ) (l : Fin (m + 1) → ℝ) : ENNReal :=
  if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
    ENNReal.ofReal (vandermondeProd l * ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
  else 0

/-- The density `cW m · V(l)` on decreasing `l`, zero elsewhere. -/
noncomputable def wt (m : ℕ) (l : Fin m → ℝ) : ENNReal :=
  if StrictAnti l then ENNReal.ofReal (cW m * vandermondeProd l) else 0

lemma measurable_wt (m : ℕ) : Measurable (wt m) :=
  Measurable.ite (measurableSet_strictAnti m)
    (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_vandermondeProd m))) measurable_const

lemma measurableSet_interlace (m : ℕ) :
    MeasurableSet {p : (Fin m → ℝ) × (Fin (m + 1) → ℝ) |
      ∀ i : Fin m, p.1 i < p.2 i.castSucc ∧ p.2 i.succ < p.1 i} := by
  have : {p : (Fin m → ℝ) × (Fin (m + 1) → ℝ) |
      ∀ i : Fin m, p.1 i < p.2 i.castSucc ∧ p.2 i.succ < p.1 i} =
      ⋂ i, ({p | p.1 i < p.2 i.castSucc} ∩ {p | p.2 i.succ < p.1 i}) := by
    ext; simp
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_lt (by fun_prop) (by fun_prop)).inter (measurableSet_lt (by fun_prop) (by fun_prop))

lemma measurable_secularProd (m : ℕ) : Measurable fun p : (Fin m → ℝ) × (Fin (m + 1) → ℝ) =>
    ∏ i : Fin m, ∏ j : Fin (m + 1), |p.1 i - p.2 j| ^ (-(1 : ℝ) / 2) :=
  Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => by fun_prop

lemma measurable_ρ (m : ℕ) : Measurable fun p : (Fin m → ℝ) × (Fin (m + 1) → ℝ) => ρ p.1 p.2 := by
  unfold ρ
  exact Measurable.ite (measurableSet_interlace m)
    (ENNReal.measurable_ofReal.comp
      (((measurable_vandermondeProd _).comp measurable_snd).mul (measurable_secularProd m)))
    measurable_const

/-- The Dixon-Anderson integrand in `μ`, for fixed `l`. -/
lemma measurable_dixonAnderson (m : ℕ) (l : Fin (m + 1) → ℝ) : Measurable fun μ : Fin m → ℝ =>
    if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
      ENNReal.ofReal (vandermondeProd μ * ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
    else 0 := by
  refine Measurable.ite ?_ ?_ measurable_const
  · have : {μ : Fin m → ℝ | ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i} =
        ⋂ i, ({μ | μ i < l i.castSucc} ∩ {μ | l i.succ < μ i}) := by
      ext; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt (by fun_prop) (by fun_prop)).inter (measurableSet_lt (by fun_prop) (by fun_prop))
  · exact ENNReal.measurable_ofReal.comp ((measurable_vandermondeProd _).mul
      (Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => by fun_prop))

lemma interlace_strictAnti {m : ℕ} {μ : Fin m → ℝ} {l : Fin (m + 1) → ℝ}
    (h : ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i) : StrictAnti l ∧ StrictAnti μ := by
  have hl : StrictAnti l := Fin.strictAnti_iff_succ_lt.2 fun i => (h i).2.trans (h i).1
  refine ⟨hl, fun i j hij => ?_⟩
  calc μ j < l j.castSucc := (h j).1
    _ ≤ l i.succ := hl.antitone (Fin.succ_le_castSucc_iff.2 hij)
    _ < μ i := (h i).2

lemma secularProd_nonneg {m : ℕ} (μ : Fin m → ℝ) (l : Fin (m + 1) → ℝ) :
    0 ≤ ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2) :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

/-- The Weyl formula for real symmetric matrices, as an identity of integrals. -/
lemma weyl (m : ℕ) : ∀ (h : (Fin m → ℝ) → ENNReal), Measurable h →
    ∫⁻ A, h (latentRoots A) ∂(symVolume m) = ∫⁻ l, wt m l * h l := by
  induction m with
  | zero => intro h _; exact weyl_zero h
  | succ m ih =>
    intro h hh
    rw [lintegral_latentRoots_border m h hh]
    have hSA : ∀ᵐ A ∂(symVolume m), StrictAnti (latentRoots A) := by
      have hS := measurableSet_strictAnti m
      have hi : Measurable ({l : Fin m → ℝ | StrictAnti l}ᶜ.indicator (1 : (Fin m → ℝ) → ENNReal)) :=
        measurable_one.indicator hS.compl
      have hm := hi.comp (measurable_latentRoots m)
      have h0 := ih _ hi
      have hr : ∫⁻ l, wt m l * ({l | StrictAnti l}ᶜ.indicator 1 l) = 0 := by
        rw [← lintegral_zero]
        refine lintegral_congr fun l => ?_
        by_cases hl : StrictAnti l <;> simp [wt, hl]
      rw [hr] at h0
      have h1 := (lintegral_eq_zero_iff hm).1 h0
      filter_upwards [h1] with A hA
      by_contra hne
      simp [Set.indicator, hne] at hA
    have hG : (fun A => ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots
          ((Fin.cons (Fin.cons p.2 p.1 : Fin (m + 1) → ℝ)
            (fun i => (Fin.cons (p.1 i) (diagArray (latentRoots A) i) : Fin (m + 1) → ℝ)) :
              Fin (m + 1) → Fin (m + 1) → ℝ)))) =ᵐ[symVolume m]
        fun A => ∫⁻ l, ρ (latentRoots A) l * h l := by
      filter_upwards [hSA] with A hA
      exact lintegral_latentRoots_border_diag m _ hA h hh
    have hjoint : Measurable fun p : (Fin m → ℝ) × (Fin (m + 1) → ℝ) => ρ p.1 p.2 * h p.2 :=
      (measurable_ρ m).mul (hh.comp measurable_snd)
    have hmeas : Measurable fun μ : Fin m → ℝ => ∫⁻ l, ρ μ l * h l := hjoint.lintegral_prod_right'
    rw [lintegral_congr_ae hG, ih _ hmeas]
    have hc : ∀ μ, wt m μ ≠ ⊤ := by intro μ; unfold wt; split_ifs <;> simp
    calc ∫⁻ μ, wt m μ * ∫⁻ l, ρ μ l * h l
        = ∫⁻ μ, ∫⁻ l, wt m μ * (ρ μ l * h l) :=
          lintegral_congr fun μ => (lintegral_const_mul' _ _ (hc μ)).symm
      _ = ∫⁻ l, ∫⁻ μ, wt m μ * (ρ μ l * h l) :=
          lintegral_lintegral_swap (((measurable_wt m).comp measurable_fst).mul hjoint).aemeasurable
      _ = ∫⁻ l, wt (m + 1) l * h l := lintegral_congr fun l => ?_
    by_cases hl : StrictAnti l
    · set DA : (Fin m → ℝ) → ENNReal := fun μ =>
        if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
          ENNReal.ofReal (vandermondeProd μ * ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
        else 0
      have hpt : ∀ μ, wt m μ * (ρ μ l * h l) =
          ENNReal.ofReal (cW m) * ENNReal.ofReal (vandermondeProd l) * h l * DA μ := by
        intro μ
        by_cases hi : ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i
        · have hμ := (interlace_strictAnti hi).2
          simp only [wt, ρ, DA, if_pos hμ, if_pos hi]
          rw [ENNReal.ofReal_mul (cW_nonneg m), ENNReal.ofReal_mul (vandermondeProd_nonneg hl),
            ENNReal.ofReal_mul (vandermondeProd_nonneg hμ)]
          ring
        · simp [ρ, DA, hi]
      have hD : 0 ≤ Real.pi ^ (((m : ℝ) + 1) / 2) / Real.Gamma (((m : ℝ) + 1) / 2) :=
        div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.Gamma_pos_of_pos (by positivity)).le
      rw [lintegral_congr hpt, lintegral_const_mul _ (measurable_dixonAnderson m l),
        dixonAnderson_half m l hl, wt, if_pos hl, cW_succ, ENNReal.ofReal_mul (mul_nonneg (cW_nonneg m) hD),
        ENNReal.ofReal_mul (cW_nonneg m)]
      ring
    · have h0 : ∀ μ, wt m μ * (ρ μ l * h l) = 0 := by
        intro μ
        have : ρ μ l = 0 := by
          unfold ρ
          rw [if_neg]
          exact fun hi => hl (interlace_strictAnti hi).1
        simp [this]
      simp only [h0, lintegral_zero]
      simp [wt, hl]

lemma of_diagArray {m : ℕ} (l : Fin m → ℝ) : Matrix.of (diagArray l) = Matrix.diagonal l := by
  ext i j; simp [diagArray, Matrix.diagonal_apply]

end WeylParent

open WeylParent in
open scoped Classical in
theorem solution (m : ℕ) (f : (Fin m → Fin m → ℝ) → ENNReal)
    (hf : Measurable f) (hpd : ∀ A, ¬(Matrix.of A).PosDef → f A = 0)
    (hinv : ∀ H ∈ Matrix.orthogonalGroup (Fin m) ℝ, ∀ A,
      f (Matrix.of.symm (H * Matrix.of A * H.transpose)) = f A) :
    ((symVolume m).withDensity f).map latentRoots =
      (volume : Measure (Fin m → ℝ)).withDensity fun l =>
        if StrictAnti l ∧ ∀ i, 0 < l i then
          ENNReal.ofReal (Real.pi ^ ((m : ℝ) ^ 2 / 2) / multivariateGamma m ((m : ℝ) / 2) *
            vandermondeProd l) * f (diagArray l)
        else 0 := by
  ext s hs
  rw [Measure.map_apply (measurable_latentRoots m) hs,
    withDensity_apply _ (measurable_latentRoots m hs), withDensity_apply _ hs]
  have hgm : Measurable fun l => s.indicator 1 l * f (diagArray l) :=
    (measurable_one.indicator hs).mul (hf.comp (measurable_diagArray m))
  have hL : ∫⁻ A in latentRoots ⁻¹' s, f A ∂symVolume m =
      ∫⁻ A, s.indicator 1 (latentRoots A) * f (diagArray (latentRoots A)) ∂symVolume m := by
    rw [← lintegral_indicator (measurable_latentRoots m hs)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_isHermitian m] with A hA
    rw [← eq_diag_of_invariant f hinv A hA]
    by_cases h : latentRoots A ∈ s <;> simp [Set.indicator, h]
  rw [hL, weyl m _ hgm, ← lintegral_indicator hs]
  refine lintegral_congr fun l => ?_
  by_cases hl : l ∈ s
  · by_cases ha : StrictAnti l
    · by_cases hp : ∀ i, 0 < l i
      · simp [Set.indicator, hl, ha, hp, wt, cW]
      · have : f (diagArray l) = 0 := hpd _ (by rw [of_diagArray, Matrix.posDef_diagonal_iff]; exact hp)
        simp [Set.indicator, hl, ha, hp, wt, this]
    · simp [Set.indicator, hl, ha, wt]
  · simp [Set.indicator, hl]
