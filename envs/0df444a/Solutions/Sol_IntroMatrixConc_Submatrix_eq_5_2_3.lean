-- Prove2me | solution 1 for IntroMatrixConc.Submatrix.eq_5_2_3
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T04:31:55.112021+00:00
-- url     : https://prove2.me/submissions/e2062c9f-fe12-4189-8bbb-a1e30de82df6

import Mathlib
import Definitions.Def_IntroMatrixConc_Submatrix_Defs
import Theorems.Thm_IntroMatrixConc_Submatrix_eq_5_1_8
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TroppMatrixConcentration IntroMatrixConc.Submatrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace TroppSelectorTransport

noncomputable def oneBool (x : ℝ) : Bool := if x = 1 then true else false

def boolReal (b : Bool) : ℝ := if b then 1 else 0

lemma oneBool_meas : Measurable oneBool := by
  exact Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const

lemma boolReal_oneBool (x : ℝ) (hx : x = 0 ∨ x = 1) : boolReal (oneBool x) = x := by
  rcases hx with rfl | rfl <;> simp [oneBool, boolReal]

lemma finite_integrable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure A) [IsFiniteMeasure ν] (f : A → ℝ) : Integrable f ν := by
  classical
  apply (integrable_const (∑ a : A, ‖f a‖)).mono' (measurable_of_finite f).aestronglyMeasurable
  exact Eventually.of_forall (fun a => Finset.single_le_sum (fun b hb => norm_nonneg _) (Finset.mem_univ a))

lemma finite_comp_integrable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (μ : Measure Ω) [IsFiniteMeasure μ]
    (v : Ω → A) (hv : Measurable v) (f : A → ℝ) : Integrable (fun ω => f (v ω)) μ := by
  have hi := finite_integrable (μ.map v) f
  exact (integrable_map_measure (measurable_of_finite f).aestronglyMeasurable hv.aemeasurable).mp hi

lemma finite_independent_integral {Ω A C : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → A) (v : Ω → C)
    (hu : Measurable u) (hv : Measurable v) (hind : IndepFun u v μ) (F : A × C → ℝ) :
    (∫ ω, F (u ω, v ω) ∂μ) = ∫ a, (∫ ω, F (a, v ω) ∂μ) ∂μ.map u := by
  have hj := hind.map_prod_eq_prod_map_map hu.aemeasurable hv.aemeasurable
  rw [← integral_map (hu.prodMk hv).aemeasurable (measurable_of_finite F).aestronglyMeasurable,
    hj, integral_prod _ (finite_integrable _ F)]
  congr 1
  funext a
  exact integral_map hv.aemeasurable (measurable_of_finite (fun c => F (a,c))).aestronglyMeasurable

lemma masks_independent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {d n : ℕ} (δ : Fin d → Ω → ℝ) (ξ : Fin n → Ω → ℝ)
    (hδ : ∀ j, Measurable (δ j)) (hξ : ∀ k, Measurable (ξ k))
    (hind : iIndepFun (Sum.elim δ ξ) μ) :
    IndepFun (fun ω j => oneBool (δ j ω)) (fun ω k => oneBool (ξ k ω)) μ := by
  classical
  let S : Finset (Fin d ⊕ Fin n) := Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩
  let T : Finset (Fin d ⊕ Fin n) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  have hST : Disjoint S T := by
    simp only [S, T, Finset.disjoint_left, Finset.mem_map, Finset.mem_univ, true_and]
    intro x ⟨i,hi⟩ ⟨j,hj⟩
    exact Sum.inl_ne_inr (hi.trans hj.symm)
  have hf : ∀ i, Measurable ((Sum.elim δ ξ) i) := by intro i; cases i <;> simp_all
  have H := hind.indepFun_finset S T hST hf
  let row : (S → ℝ) → (Fin d → Bool) := fun v j => oneBool (v ⟨Sum.inl j, by simp [S]⟩)
  let col : (T → ℝ) → (Fin n → Bool) := fun v k => oneBool (v ⟨Sum.inr k, by simp [T]⟩)
  have hr : Measurable row := measurable_pi_lambda _ (fun j => oneBool_meas.comp (measurable_pi_apply _))
  have hc : Measurable col := measurable_pi_lambda _ (fun k => oneBool_meas.comp (measurable_pi_apply _))
  exact H.comp hr hc

lemma bernoulli_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (q : ℝ) (h : IsBernoulli μ g q) : Integrable g μ := by
  apply (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
  filter_upwards [h.1] with ω hω
  rcases hω with he | he <;> simp [he]

lemma bernoulli_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (q : ℝ) (h : IsBernoulli μ g q) : (∫ ω, g ω ∂μ) = q := by
  have hs : MeasurableSet {ω | g ω = 1} := hg (measurableSet_singleton 1)
  have he : g =ᵐ[μ] ({ω | g ω = 1}.indicator (fun _ => (1 : ℝ))) := by
    filter_upwards [h.1] with ω hω
    rcases hω with he | he <;> simp [he]
  rw [integral_congr_ae he, integral_indicator_const _ hs]
  simpa only [smul_eq_mul, mul_one, Measure.real] using h.2

lemma max_eq_norm_of_psd {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hp : A.PosSemidef) : lambdaMax A = ‖A‖ := by
  unfold lambdaMax
  have hf : (spectrum ℝ A).Finite := by
    rw [hp.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hn := CStarAlgebra.norm_mem_spectrum_of_nonneg hp.nonneg
  apply le_antisymm
  · apply csSup_le ⟨‖A‖, hn⟩
    intro x hx
    have hx' := (spectrum.algebraMap_mem_iff ℂ).mpr hx
    have hb := spectrum.norm_le_norm_of_mem hx'
    have hb' : |x| ≤ ‖A‖ := by simpa using hb
    exact (le_abs_self x).trans hb'
  · exact le_csSup hf.bddAbove hn

lemma min_nonneg_of_psd {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hp : A.PosSemidef) : 0 ≤ lambdaMin A := by
  unfold lambdaMin
  rw [hp.isHermitian.spectrum_real_eq_range_eigenvalues]
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨i,rfl⟩
  exact (hp.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hp) i

lemma max_le_trace_of_psd {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hp : A.PosSemidef) : lambdaMax A ≤ (Matrix.trace A).re := by
  have he : lambdaMax A ∈ Set.range hp.isHermitian.eigenvalues := by
    unfold lambdaMax
    rw [hp.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)
  obtain ⟨i, hi⟩ := he
  rw [← hi, hp.isHermitian.trace_eq_sum_eigenvalues]
  have hr : (∑ j : Fin d, (hp.isHermitian.eigenvalues j : ℂ)).re =
      ∑ j : Fin d, (hp.isHermitian.eigenvalues j : ℂ).re :=
    map_sum Complex.reAddGroupHom _ _
  change hp.isHermitian.eigenvalues i ≤ (∑ j : Fin d, (hp.isHermitian.eigenvalues j : ℂ)).re
  rw [hr]
  simp only [Complex.ofReal_re]
  exact Finset.single_le_sum
    (fun j hj => (hp.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hp) j) (Finset.mem_univ i)

def columnOuter {d n : ℕ} (C : Matrix (Fin d) (Fin n) ℂ) (k : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec (fun i => C i k) (star (fun i => C i k))

lemma columnOuter_psd {d n : ℕ} (C : Matrix (Fin d) (Fin n) ℂ) (k : Fin n) :
    (columnOuter C k).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _

lemma columnOuter_trace {d n : ℕ} (C : Matrix (Fin d) (Fin n) ℂ) (k : Fin n) :
    (Matrix.trace (columnOuter C k)).re = ∑ i, ‖C i k‖ ^ 2 := by
  simp [columnOuter, Matrix.trace, Matrix.vecMulVec_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]

lemma columnOuter_sum {d n : ℕ} (C : Matrix (Fin d) (Fin n) ℂ) :
    (∑ k, columnOuter C k) = C * C.conjTranspose := by
  ext i j
  simp [columnOuter, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply]

lemma columnOuter_bound {d n : ℕ} [NeZero d] (C : Matrix (Fin d) (Fin n) ℂ) (k : Fin n) :
    lambdaMax (columnOuter C k) ≤ maxColumnSq C := by
  apply (max_le_trace_of_psd _ (columnOuter_psd C k)).trans
  rw [columnOuter_trace]
  unfold maxColumnSq
  have hb : BddAbove (Set.range (fun k : Fin n => ∑ i : Fin d, ‖C i k‖ ^ 2)) :=
    (Set.finite_range _).bddAbove
  exact le_ciSup hb k

lemma gram_selection {d n : ℕ} (C : Matrix (Fin d) (Fin n) ℂ) (v : Fin n → ℝ)
    (hv : ∀ k, v k = 0 ∨ v k = 1) :
    (C * Matrix.diagonal (fun k => (v k : ℂ))) *
      (C * Matrix.diagonal (fun k => (v k : ℂ))).conjTranspose = ∑ k, v k • columnOuter C k := by
  have hc (i : Fin d) (k : Fin n) :
      (C * Matrix.diagonal (fun k => (v k : ℂ))) i k = C i k * (v k : ℂ) :=
    Matrix.mul_diagonal _ _ _ _
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hc, Matrix.sum_apply, Matrix.smul_apply,
    columnOuter, Matrix.vecMulVec_apply, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rcases hv k with he | he <;> simp [he]

lemma gram_max_norm_sq {d n : ℕ} [NeZero d] (C : Matrix (Fin d) (Fin n) ℂ) :
    lambdaMax (C * C.conjTranspose) = spectralNorm C ^ 2 := by
  rw [max_eq_norm_of_psd _ (Matrix.posSemidef_self_mul_conjTranspose C)]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self C.conjTranspose
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, pow_two, TroppMatrixConcentration.spectralNorm] using h

lemma fixed_columns {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d n : ℕ} [NeZero d] [NeZero n] (C : Matrix (Fin d) (Fin n) ℂ)
    (ξ : Fin n → Ω → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hξm : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ μ)
    (hξ : ∀ k, IsBernoulli μ (ξ k) q) :
    Integrable (fun ω => spectralNorm (selectedColumns C ξ ω) ^ 2) μ ∧
      (∫ ω, spectralNorm (selectedColumns C ξ ω) ^ 2 ∂μ) ≤
        (1.72 : ℝ) * q * lambdaMax (C * C.conjTranspose) + Real.log d * maxColumnSq C := by
  classical
  let X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ := fun k ω => ξ k ω • columnOuter C k
  let Y := fun ω => ∑ k, X k ω
  have hL : 0 ≤ maxColumnSq C := by
    unfold maxColumnSq
    have hb : BddAbove (Set.range (fun k : Fin n => ∑ i : Fin d, ‖C i k‖ ^ 2)) := (Set.finite_range _).bddAbove
    exact (Finset.sum_nonneg (fun i hi => sq_nonneg _)).trans (le_ciSup hb ⟨0,NeZero.pos n⟩)
  have hXm : ∀ k, Measurable (X k) := by intro k; unfold X; fun_prop
  have hXi : ∀ k, Integrable (X k) μ := fun k => (bernoulli_integrable μ _ (hξm k) q (hξ k)).smul_const _
  have hXh : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian := by
    intro k
    filter_upwards [(hξ k).1] with ω he
    rcases he with he | he
    · simp [X, he]
    · simpa [X, he] using (columnOuter_psd C k).isHermitian
  have hXb : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ maxColumnSq C := by
    intro k
    filter_upwards [(hξ k).1] with ω he
    rcases he with he | he
    · simpa [X, he, lambdaMin, lambdaMax, spectrum.zero_eq] using hL
    · simpa [X, he] using And.intro (min_nonneg_of_psd _ (columnOuter_psd C k)) (columnOuter_bound C k)
  have hInd : iIndepFun X μ := hind.comp (fun k t => t • columnOuter C k) (by intro k; fun_prop)
  have H := IntroMatrixConc.Submatrix.eq_5_1_8 μ X (maxColumnSq C) hL hXm hInd hXh hXb
  change Integrable (fun ω => lambdaMax (Y ω)) μ ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤ (1.72 : ℝ) * lambdaMax (∫ ω, Y ω ∂μ) + maxColumnSq C * Real.log d at H
  have heY : (∫ ω, Y ω ∂μ) = q • (C * C.conjTranspose) := by
    unfold Y
    rw [integral_finset_sum _ (fun k hk => hXi k)]
    simp only [X, integral_smul_const]
    simp_rw [bernoulli_mean μ _ (hξm _) q (hξ _)]
    rw [← Finset.smul_sum, columnOuter_sum]
  have hmean : lambdaMax (q • (C * C.conjTranspose)) = q * lambdaMax (C * C.conjTranspose) := by
    rw [max_eq_norm_of_psd _ ((Matrix.posSemidef_self_mul_conjTranspose C).smul hq),
      max_eq_norm_of_psd _ (Matrix.posSemidef_self_mul_conjTranspose C), norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
  have he : (fun ω => spectralNorm (selectedColumns C ξ ω) ^ 2) =ᵐ[μ] (fun ω => lambdaMax (Y ω)) := by
    filter_upwards [ae_all_iff.mpr (fun k => (hξ k).1)] with ω hw
    have hg := gram_selection C (fun k => ξ k ω) hw
    unfold selectedColumns
    rw [← gram_max_norm_sq, hg]
  refine ⟨H.1.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  rw [heY, hmean] at H
  nlinarith [H.2]

def mask {Ω : Type*} {m : ℕ} (v : Fin m → Ω → ℝ) (ω : Ω) (j : Fin m) : Bool := oneBool (v j ω)

def rows {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) (a : Fin d → Bool) :=
  Matrix.diagonal (fun j => (boolReal (a j) : ℂ)) * B

def cols {d n : ℕ} (C : Matrix (Fin d) (Fin n) ℂ) (b : Fin n → Bool) :=
  C * Matrix.diagonal (fun k => (boolReal (b k) : ℂ))

lemma mask_meas {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (v : Fin m → Ω → ℝ)
    (hv : ∀ j, Measurable (v j)) : Measurable (mask v) :=
  measurable_pi_lambda _ (fun j => oneBool_meas.comp (hv j))

lemma encode_rows {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ)
    (hδ : ∀ j, ∀ᵐ ω ∂μ, δ j ω = 0 ∨ δ j ω = 1) :
    (fun ω => selectedRows B δ ω) =ᵐ[μ] (fun ω => rows B (mask δ ω)) := by
  filter_upwards [ae_all_iff.mpr hδ] with ω hw
  unfold selectedRows rows
  have he : (fun j => (δ j ω : ℂ)) = (fun j => (boolReal (mask δ ω j) : ℂ)) := by
    funext j
    exact congrArg (fun x : ℝ => (x : ℂ)) (boolReal_oneBool _ (hw j)).symm
  rw [he]

lemma encode_cols {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {d n : ℕ} (C : Matrix (Fin d) (Fin n) ℂ) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ k, ∀ᵐ ω ∂μ, ξ k ω = 0 ∨ ξ k ω = 1) :
    (fun ω => selectedColumns C ξ ω) =ᵐ[μ] (fun ω => cols C (mask ξ ω)) := by
  filter_upwards [ae_all_iff.mpr hξ] with ω hw
  unfold selectedColumns cols
  have he : (fun k => (ξ k ω : ℂ)) = (fun k => (boolReal (mask ξ ω k) : ℂ)) := by
    funext k
    exact congrArg (fun x : ℝ => (x : ℂ)) (boolReal_oneBool _ (hw k)).symm
  rw [he]

lemma encode_submatrix {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ) (ξ : Fin n → Ω → ℝ)
    (hδ : ∀ j, ∀ᵐ ω ∂μ, δ j ω = 0 ∨ δ j ω = 1)
    (hξ : ∀ k, ∀ᵐ ω ∂μ, ξ k ω = 0 ∨ ξ k ω = 1) :
    (fun ω => selectedSubmatrix B δ ξ ω) =ᵐ[μ]
      (fun ω => cols (rows B (mask δ ω)) (mask ξ ω)) := by
  filter_upwards [encode_rows μ B δ hδ, ae_all_iff.mpr hξ] with ω hr hw
  unfold selectedSubmatrix cols
  rw [hr]
  have he : (fun k => (ξ k ω : ℂ)) = (fun k => (boolReal (mask ξ ω k) : ℂ)) := by
    funext k
    exact congrArg (fun x : ℝ => (x : ℂ)) (boolReal_oneBool _ (hw k)).symm
  rw [he]

end TroppSelectorTransport

open TroppSelectorTransport

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d n : ℕ} [NeZero d] [NeZero n]
    (B : Matrix (Fin d) (Fin n) ℂ) (δ : Fin d → Ω → ℝ)
    (ξ : Fin n → Ω → ℝ) (p r : ℝ)
    (hp0 : 0 ≤ p) (hpd : p ≤ (d : ℝ))
    (hr0 : 0 ≤ r) (hrn : r ≤ (n : ℝ))
    (hδMeas : ∀ j, Measurable (δ j)) (hξMeas : ∀ k, Measurable (ξ k))
    (hIndep : iIndepFun (Sum.elim δ ξ) μ)
    (hδ : ∀ j, IsBernoulli μ (δ j) (p / (d : ℝ)))
    (hξ : ∀ k, IsBernoulli μ (ξ k) (r / (n : ℝ))) :
    Integrable (fun ω => spectralNorm (selectedSubmatrix B δ ξ ω) ^ 2) μ ∧
    Integrable (fun ω => lambdaMax (selectedRows B δ ω * (selectedRows B δ ω).conjTranspose)) μ ∧
    Integrable (fun ω => maxSelectedColumnSq B δ ω) μ ∧
    (∫ ω, spectralNorm (selectedSubmatrix B δ ξ ω) ^ 2 ∂μ) ≤
      (1.72 : ℝ) * (r / (n : ℝ)) *
        (∫ ω, lambdaMax (selectedRows B δ ω * (selectedRows B δ ω).conjTranspose) ∂μ) +
      Real.log d * (∫ ω, maxSelectedColumnSq B δ ω ∂μ) := by
  classical
  let A := Fin d → Bool
  let C := Fin n → Bool
  let u : Ω → A := mask δ
  let v : Ω → C := mask ξ
  let F : A × C → ℝ := fun z => spectralNorm (cols (rows B z.1) z.2) ^ 2
  let G : A → ℝ := fun a => lambdaMax (rows B a * (rows B a).conjTranspose)
  let M : A → ℝ := fun a => maxColumnSq (rows B a)
  have hu : Measurable u := mask_meas δ hδMeas
  have hv : Measurable v := mask_meas ξ hξMeas
  have hδ01 : ∀ j, ∀ᵐ ω ∂μ, δ j ω = 0 ∨ δ j ω = 1 := fun j => (hδ j).1
  have hξ01 : ∀ k, ∀ᵐ ω ∂μ, ξ k ω = 0 ∨ ξ k ω = 1 := fun k => (hξ k).1
  have hF : (fun ω => spectralNorm (selectedSubmatrix B δ ξ ω) ^ 2) =ᵐ[μ] (fun ω => F (u ω,v ω)) := by
    filter_upwards [encode_submatrix μ B δ ξ hδ01 hξ01] with ω he
    simp only [he, F, u, v]
  have hG : (fun ω => lambdaMax (selectedRows B δ ω * (selectedRows B δ ω).conjTranspose)) =ᵐ[μ]
      (fun ω => G (u ω)) := by
    filter_upwards [encode_rows μ B δ hδ01] with ω he
    simp only [he, G, u]
  have hM : (fun ω => maxSelectedColumnSq B δ ω) =ᵐ[μ] (fun ω => M (u ω)) := by
    filter_upwards [encode_rows μ B δ hδ01] with ω he
    change maxColumnSq (selectedRows B δ ω) = maxColumnSq (rows B (u ω))
    rw [he]
  have hiF := finite_comp_integrable μ (fun ω => (u ω,v ω)) (hu.prodMk hv) F
  have hiG := finite_comp_integrable μ u hu G
  have hiM := finite_comp_integrable μ u hu M
  refine ⟨hiF.congr hF.symm, hiG.congr hG.symm, hiM.congr hM.symm, ?_⟩
  rw [integral_congr_ae hF, integral_congr_ae hG, integral_congr_ae hM]
  have hind : IndepFun u v μ := masks_independent μ δ ξ hδMeas hξMeas hIndep
  rw [finite_independent_integral μ u v hu hv hind F]
  have hξind : iIndepFun ξ μ := by
    simpa only [Sum.elim_inr] using hIndep.precomp (g := Sum.inr) Sum.inr_injective
  have hpoint (a : A) : (∫ ω, F (a,v ω) ∂μ) ≤
      (1.72 : ℝ) * (r / (n : ℝ)) * G a + Real.log d * M a := by
    have H := fixed_columns μ (rows B a) ξ (r / (n : ℝ)) (div_nonneg hr0 (Nat.cast_nonneg n)) hξMeas hξind hξ
    have he : (fun ω => spectralNorm (selectedColumns (rows B a) ξ ω) ^ 2) =ᵐ[μ]
        (fun ω => F (a,v ω)) := by
      filter_upwards [encode_cols μ (rows B a) ξ hξ01] with ω he
      simp only [he, F, v]
    rw [integral_congr_ae he] at H
    exact H.2
  have houter := integral_mono (finite_integrable (μ.map u) (fun a => ∫ ω, F (a,v ω) ∂μ))
    (finite_integrable (μ.map u) (fun a => (1.72 : ℝ) * (r / (n : ℝ)) * G a + Real.log d * M a)) hpoint
  have hg : Integrable G (μ.map u) := finite_integrable _ _
  have hm : Integrable M (μ.map u) := finite_integrable _ _
  rw [integral_add (f := fun a => (1.72 : ℝ) * (r / (n : ℝ)) * G a)
      (g := fun a => Real.log d * M a) (hg.const_mul _) (hm.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_map hu.aemeasurable (measurable_of_finite G).aestronglyMeasurable,
    integral_map hu.aemeasurable (measurable_of_finite M).aestronglyMeasurable] at houter
  exact houter

#print axioms solution
