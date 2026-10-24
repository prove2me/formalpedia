-- Prove2me | solution 1 for KLTNuclear.Oracle.basic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T13:06:43.033638+00:00
-- url     : https://prove2.me/submissions/c470746b-51bb-4490-bb59-f2527a2a126e

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
Koltchinskii–Lounici–Tsybakov, arXiv:1011.6256v4, p.7 basic inequality.
The trace-duality dependency below is Harry_Xu's accepted proof of target
8cdc73ca-52b9-4c4c-8956-e2d787701754, submission dbfe1e91-df64-4c57-8503-2afbd13fcf99.
Only its final declaration is renamed from solution to matrix_trace_duality_inequality.
Alexander Richard Towell / queelius, with substantial OpenAI Codex assistance:
conditional-expectation centering, integrability, polarization, and estimator comparison.
-/

/-!
C1 — von Neumann / matrix trace-duality inequality:
  `matrixInner A B ≤ spectralNorm A * nuclearNorm B`.

Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2 first inequality
(von Neumann's trace inequality, 1937; see also Mirsky 1975).

Proof outline (built from Mathlib's self-adjoint spectral theorem; the SVD
reconstruction `B = Σ σ_k u_k v_k^T` is NOT available ready-made in this env's
Mathlib, so it is constructed here):
  * `T := toEuclideanLin B`, `G := Tᵀ∘T` symmetric and PSD.
  * `v_k := eigenvectorBasis G` orthonormal, eigenvalues `μ_k ≥ 0`,
    `σ_k = √μ_k = singularValues T k`.
  * `⟪T v_i, T v_j⟫ = ⟪G v_i, v_j⟫ = μ_i δ_ij`, so `‖T v_k‖ = σ_k`.
  * Frobenius inner product = Hilbert–Schmidt inner `∑_j ⟪S e_j, T e_j⟫`,
    which is `trace(Sᵀ∘T)` — basis-independent — hence `= ∑_k ⟪S v_k, T v_k⟫`.
  * `⟪S v_k, T v_k⟫ ≤ ‖S v_k‖·‖T v_k‖ ≤ ‖S‖·1·σ_k`; sum gives `‖S‖·Σσ_k`.
  * `Σ σ_k = nuclearNorm B`, `‖S‖ = spectralNorm A`.
-/

open Module InnerProductSpace LinearMap Matrix
open scoped BigOperators

/-! ### Operator-level SVD reconstruction & von Neumann inequality. -/

namespace SVDProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev gram (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := adjoint T ∘ₗ T

theorem gram_symm (T : E →ₗ[ℝ] F) : (gram T).IsSymmetric :=
  T.isSymmetric_adjoint_comp_self

theorem gram_pos (T : E →ₗ[ℝ] F) : (gram T).IsPositive :=
  T.isPositive_adjoint_comp_self

noncomputable def rsv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) :
    OrthonormalBasis (Fin n) ℝ E :=
  (gram_symm T).eigenvectorBasis hn

noncomputable def evals (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) : Fin n → ℝ :=
  (gram_symm T).eigenvalues hn

theorem evals_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ evals T hn k :=
  (gram_pos T).nonneg_eigenvalues hn k

theorem inner_Tv (T : E →ₗ[ℝ] F) (a b : E) :
    inner ℝ (T a) (T b) = inner ℝ (gram T a) b := by
  unfold gram
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]

theorem inner_Tv_eig (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T (rsv T hn i)) (T (rsv T hn j))
      = if i = j then evals T hn i else 0 := by
  rw [inner_Tv]
  unfold gram rsv evals
  rw [show (adjoint T ∘ₗ T) ((gram_symm T).eigenvectorBasis hn i)
        = (gram T) ((gram_symm T).eigenvectorBasis hn i) from rfl]
  rw [(gram_symm T).apply_eigenvectorBasis hn i]
  rw [inner_smul_left]
  rw [orthonormal_iff_ite.mp ((gram_symm T).eigenvectorBasis hn).orthonormal i j]
  simp only [conj_trivial]
  by_cases h : i = j
  · subst h; rw [if_pos rfl, if_pos rfl, mul_one, RCLike.ofReal_real_eq_id]; rfl
  · rw [if_neg h, if_neg h, mul_zero]

noncomputable def sval (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) : ℝ :=
  T.singularValues k

theorem sval_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ sval T hn k := T.singularValues_nonneg k

theorem sval_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    sval T hn k ^ 2 = evals T hn k := by
  unfold sval evals
  rw [T.sq_singularValues_fin hn k]

theorem norm_Tv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    ‖T (rsv T hn k)‖ = sval T hn k := by
  have heig : inner ℝ (T (rsv T hn k)) (T (rsv T hn k)) = evals T hn k := by
    have h := inner_Tv_eig T hn k k
    rw [if_pos rfl] at h
    exact h
  have h2 : ‖T (rsv T hn k)‖ ^ 2 = sval T hn k ^ 2 := by
    rw [@norm_sq_eq_re_inner ℝ, heig, sval_sq, RCLike.re_to_real]
  have hnn := sval_nonneg T hn k
  nlinarith [norm_nonneg (T (rsv T hn k)), h2, hnn]

theorem hsInner_eq_trace {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    (∑ j, inner ℝ (S (b j)) (T (b j))) = (adjoint S ∘ₗ T).trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right S (b j) (T (b j))]

theorem hsInner_basis_indep {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ (S (b j)) (T (b j)))
      = ∑ k, inner ℝ (S (rsv T hn k)) (T (rsv T hn k)) := by
  rw [hsInner_eq_trace S T b, hsInner_eq_trace S T (rsv T hn)]

theorem vonNeumann_op {ι : Type*} [Fintype ι] (S : E →L[ℝ] F) (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ ((S : E →ₗ[ℝ] F) (b j)) (T (b j))) ≤ ‖S‖ * ∑ k, sval T hn k := by
  rw [hsInner_basis_indep (S : E →ₗ[ℝ] F) T b hn]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hSle : ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ ≤ ‖S‖ * ‖(rsv T hn k : E)‖ := S.le_opNorm _
  calc inner ℝ ((S : E →ₗ[ℝ] F) (rsv T hn k)) (T (rsv T hn k))
      ≤ ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ * ‖T (rsv T hn k)‖ := real_inner_le_norm _ _
    _ ≤ (‖S‖ * ‖(rsv T hn k : E)‖) * ‖T (rsv T hn k)‖ := by
          apply mul_le_mul_of_nonneg_right hSle (norm_nonneg _)
    _ = ‖S‖ * sval T hn k := by
          rw [(rsv T hn).orthonormal.1 k, norm_Tv]; ring

end SVDProbe

/-! ### Matrix specialization to the platform statement. -/

namespace MatrixCompletion

open SVDProbe

variable {n1 n2 : ℕ}

theorem matrixInner_eq_hsInner (A B : RealMatrix n1 n2) :
    matrixInner A B
      = ∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                      ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)) := by
  unfold matrixInner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply]
  simp only [toEuclideanLin_apply]
  have hcol : ∀ (C : RealMatrix n1 n2),
      (C *ᵥ (EuclideanSpace.single j (1:ℝ)).ofLp) i = C i j := by
    intro C
    simp only [Matrix.mulVec, EuclideanSpace.ofLp_single, dotProduct_single, mul_one]
  rw [hcol A, hcol B]
  rw [show (⟪A i j, B i j⟫_ℝ : ℝ) = B i j * (starRingEnd ℝ) (A i j) from RCLike.inner_apply _ _,
      conj_trivial]; ring

theorem nuclearNorm_eq_sum_sval (B : RealMatrix n1 n2)
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2) :
    nuclearNorm B = ∑ k, sval (toEuclideanLin B) hn k := by
  unfold nuclearNorm sval
  set T := toEuclideanLin B
  rw [Finsupp.sum_of_support_subset T.singularValues
      (s := Finset.range n2) ?_ (fun _ x => x) (by intro _ _; rfl)]
  · rw [Finset.sum_range fun k => T.singularValues k]
  · intro k hk
    rw [Finset.mem_range]
    by_contra hge
    push_neg at hge
    have hz : T.singularValues k = 0 := by
      apply T.singularValues_of_finrank_le
      rw [hn]; exact hge
    rw [Finsupp.mem_support_iff] at hk
    exact hk hz

theorem trace_duality_C1 (A B : RealMatrix n1 n2) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  rw [matrixInner_eq_hsInner A B, nuclearNorm_eq_sum_sval B hn]
  show (∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                     ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)))
      ≤ spectralNorm A * ∑ k, sval (toEuclideanLin B) hn k
  unfold spectralNorm
  exact vonNeumann_op (LinearMap.toContinuousLinearMap (toEuclideanLin A))
    (toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ) hn

end MatrixCompletion

open MatrixCompletion
open scoped BigOperators

/-- C1 — von Neumann / matrix trace-duality inequality.
Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2, first inequality
(von Neumann's trace inequality 1937; Mirsky 1975). -/
theorem matrix_trace_duality_inequality {n₁ n₂ : ℕ} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B :=
  MatrixCompletion.trace_duality_C1 A B

open MeasureTheory MatrixCompletion
open scoped BigOperators
namespace KLTWork

lemma inner_comm {m k : ℕ} (A B : RealMatrix m k) : matrixInner A B = matrixInner B A := by
  simp [matrixInner, mul_comm]
lemma inner_sub_left {m k : ℕ} (A B D : RealMatrix m k) :
    matrixInner (A - B) D = matrixInner A D - matrixInner B D := by
  simp [matrixInner, sub_mul, Finset.sum_sub_distrib]
lemma inner_sub_right {m k : ℕ} (A B D : RealMatrix m k) :
    matrixInner A (B - D) = matrixInner A B - matrixInner A D := by
  simp [matrixInner, mul_sub, Finset.sum_sub_distrib]
lemma inner_smul_left {m k : ℕ} (c : ℝ) (A B : RealMatrix m k) :
    matrixInner (c • A) B = c * matrixInner A B := by
  simp [matrixInner, Finset.mul_sum, mul_assoc]
lemma inner_sum_left {m k : ℕ} {ι : Type*} [Fintype ι] (A : ι → RealMatrix m k) (B : RealMatrix m k) :
    matrixInner (∑ i, A i) B = ∑ i, matrixInner (A i) B := by
  simp only [matrixInner, Matrix.sum_apply, Finset.sum_mul]
  calc
    (∑ a, ∑ b, ∑ i, A i a b * B a b) = ∑ a, ∑ i, ∑ b, A i a b * B a b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

open KLTNuclear.Oracle
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n m k : ℕ}
  {X : Fin n → Ω → RealMatrix m k} {Y : Fin n → Ω → ℝ}
lemma inner_memLp (hreg : SampleRegularity P X Y) (A : RealMatrix m k) (i : Fin n) :
    MemLp (fun ω => matrixInner A (X i ω)) 2 P := by
  exact memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun l _ =>
    (hreg.2.2.1 i j l).const_mul (A j l)
lemma inner_product_integrable (hreg : SampleRegularity P X Y) (A B : RealMatrix m k) (i : Fin n) :
    Integrable (fun ω => matrixInner A (X i ω) * matrixInner B (X i ω)) P :=
  (inner_memLp hreg A i).integrable_mul (inner_memLp hreg B i)

lemma centered_entry [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (i : Fin n) (j : Fin m) (l : Fin k) :
    expectYX P X Y i j l = ∫ ω, matrixInner A₀ (X i ω) * X i ω j l ∂P := by
  let g : Ω → Fin m → Fin k → ℝ := fun ω j l => X i ω j l
  have hx : Measurable g := measurable_pi_lambda _ fun a =>
    measurable_pi_lambda _ fun b => hreg.1 i a b
  have hs : MeasurableSpace.comap g inferInstance ≤ ‹MeasurableSpace Ω› := hx.comap_le
  have hx_s : @Measurable Ω (Fin m → Fin k → ℝ)
      (MeasurableSpace.comap g inferInstance) _ g := measurable_iff_comap_le.mpr le_rfl
  have he : @Measurable Ω ℝ (MeasurableSpace.comap g inferInstance) _ (fun ω => X i ω j l) :=
    (measurable_pi_apply l).comp ((measurable_pi_apply j).comp hx_s)
  have hc := condExp_mul_of_stronglyMeasurable_right (μ := P)
    he.stronglyMeasurable (hreg.2.2.2.2 i j l) (hreg.2.2.2.1 i)
  unfold expectYX
  calc
    _ = ∫ ω, P[(fun ω => Y i ω * X i ω j l) | MeasurableSpace.comap g inferInstance] ω ∂P :=
      (integral_condExp hs).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hc, hmodel i] with ω h1 h2
      change P[Y i | MeasurableSpace.comap g inferInstance] ω = matrixInner A₀ (X i ω) at h2
      change P[(fun ω => Y i ω * X i ω j l) | MeasurableSpace.comap g inferInstance] ω =
        P[Y i | MeasurableSpace.comap g inferInstance] ω * X i ω j l at h1
      rw [h2] at h1
      exact h1

lemma l2_square_sub (hreg : SampleRegularity P X Y) (A B : RealMatrix m k) :
    l2NormSq P X (A - B) = l2NormSq P X A - 2 * l2Inner P X A B + l2NormSq P X B := by
  unfold l2NormSq l2Inner
  have hi (i : Fin n) :
      (∫ ω, matrixInner (A-B) (X i ω) * matrixInner (A-B) (X i ω) ∂P) =
      (∫ ω, matrixInner A (X i ω) * matrixInner A (X i ω) ∂P) -
        2 * (∫ ω, matrixInner A (X i ω) * matrixInner B (X i ω) ∂P) +
        (∫ ω, matrixInner B (X i ω) * matrixInner B (X i ω) ∂P) := by
    simp_rw [inner_sub_left]
    have he (ω : Ω) : (matrixInner A (X i ω) - matrixInner B (X i ω)) *
        (matrixInner A (X i ω) - matrixInner B (X i ω)) =
        matrixInner A (X i ω) * matrixInner A (X i ω) -
          2 * (matrixInner A (X i ω) * matrixInner B (X i ω)) +
          matrixInner B (X i ω) * matrixInner B (X i ω) := by ring
    simp_rw [he]
    have hAA := inner_product_integrable hreg A A i
    have hAB := (inner_product_integrable hreg A B i).const_mul 2
    have hBB := inner_product_integrable hreg B B i
    have hsum := integral_add (hAA.sub hAB) hBB
    have hsub := integral_sub hAA hAB
    simp only [Pi.sub_apply] at hsum
    rw [hsum, hsub, integral_const_mul]

  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
lemma integral_inner (F : Ω → RealMatrix m k)
    (hF : ∀ j l, Integrable (fun ω => F ω j l) P) (B : RealMatrix m k) :
    matrixInner (fun j l => ∫ ω, F ω j l ∂P) B = ∫ ω, matrixInner (F ω) B ∂P := by
  unfold matrixInner
  simp_rw [← integral_mul_const]
  symm
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun l _ =>
    (hF j l).mul_const (B j l))]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_finsetSum _ (fun l _ => (hF j l).mul_const (B j l))

lemma centered_inner [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (i : Fin n) (B : RealMatrix m k) :
    matrixInner (expectYX P X Y i) B =
      ∫ ω, matrixInner A₀ (X i ω) * matrixInner B (X i ω) ∂P := by
  have he : expectYX P X Y i = fun j l =>
      ∫ ω, matrixInner A₀ (X i ω) * X i ω j l ∂P := by
    funext j l
    exact centered_entry hreg A₀ hmodel i j l
  rw [he]
  have hi (j : Fin m) (l : Fin k) :
      Integrable (fun ω => matrixInner A₀ (X i ω) * X i ω j l) P :=
    (inner_memLp hreg A₀ i).integrable_mul (hreg.2.2.1 i j l)
  calc
    _ = ∫ ω, matrixInner (matrixInner A₀ (X i ω) • X i ω) B ∂P := by
      simpa only [Matrix.smul_apply, smul_eq_mul] using
        integral_inner (fun ω => matrixInner A₀ (X i ω) • X i ω) hi B
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [inner_smul_left, inner_comm (X i ω) B]

lemma empirical_pairing [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (ω : Ω) (B : RealMatrix m k) :
    matrixInner (empiricalYX X Y ω) B =
      2 * matrixInner (noiseMatrix P X Y ω) B + 2 * l2Inner P X A₀ B := by
  simp only [empiricalYX, noiseMatrix, inner_smul_left, inner_sum_left,
    inner_sub_left, centered_inner hreg A₀ hmodel, l2Inner, Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv, one_mul]
  ring

lemma l2_comm (A B : RealMatrix m k) : l2Inner P X A B = l2Inner P X B A := by
  unfold l2Inner
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext ω
  exact mul_comm _ _
end KLTWork

open MeasureTheory MatrixCompletion KLTNuclear.Oracle

/-- Proof of Theorem 1 (p. 7), display after "which implies, due to the trace duality":
the basic inequality, with Δ = ‖𝐌‖∞. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat) :
    ∀ A ∈ 𝔸, l2NormSq P X (Ahat - A₀) ≤
      l2NormSq P X (A - A₀) + 2 * spectralNorm (noiseMatrix P X Y ω) * nuclearNorm (Ahat - A) +
        lam * (nuclearNorm A - nuclearNorm Ahat)  := by
  intro A hA
  have hopt := hAhat.2 A hA
  unfold Ln at hopt
  rw [KLTWork.empirical_pairing hreg A₀ hmodel ω Ahat,
      KLTWork.empirical_pairing hreg A₀ hmodel ω A] at hopt
  have hdual := matrix_trace_duality_inequality (noiseMatrix P X Y ω) (Ahat - A)
  rw [KLTWork.inner_sub_right] at hdual
  rw [KLTWork.l2_square_sub hreg Ahat A₀, KLTWork.l2_square_sub hreg A A₀,
      KLTWork.l2_comm Ahat A₀, KLTWork.l2_comm A A₀]
  linarith

#print axioms solution
