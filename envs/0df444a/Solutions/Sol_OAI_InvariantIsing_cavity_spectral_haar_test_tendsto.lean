-- Prove2me | solution 1 for OAI.InvariantIsing.cavity_spectral_haar_test_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:15:57.006658+00:00
-- url     : https://prove2.me/submissions/bd69187c-040f-4ae5-94d6-f5041b86c1c7

import Mathlib
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004

section
-- module Solutions.OAIQ258_II.Compat
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `Measurable.eval_matrix` (q258). -/
lemma _root_.Measurable.eval_matrix {m n α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {i : m} {j : n} {M : β → Matrix m n α} (hM : Measurable M) : Measurable (M · i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)
/-- d13f23b's `Matrix.measurable_apply` (q258). -/
protected lemma _root_.Matrix.measurable_apply {m n α : Type*} [MeasurableSpace α] {i : m} {j : n} :
    Measurable (fun M : Matrix m n α => M i j) := measurable_id.eval_matrix
/-- d13f23b's `HasLaw.memLp_comp` (InvariantIsing CavityGaussianRows, q251). -/
theorem _root_.ProbabilityTheory.HasLaw.memLp_comp {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure 𝓧} {X : Ω → 𝓧} {f : 𝓧 → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hf : MeasureTheory.MemLp f p μ) :
    MeasureTheory.MemLp (f ∘ X) p P := by
  have h : MeasureTheory.MemLp f p (P.map X) := hX.map_eq ▸ hf
  exact (MeasureTheory.memLp_map_measure_iff h.aestronglyMeasurable hX.aemeasurable).1 h
/-- d13f23b's `HasLaw.memLp`: a variable whose law has `id` in `L^p` is in `L^p`. -/
theorem _root_.ProbabilityTheory.HasLaw.memLp {Ω E : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
    [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure E} {X : Ω → E}
    {p : ENNReal} (hX : ProbabilityTheory.HasLaw X μ P) (hμ : MeasureTheory.MemLp id p μ) :
    MeasureTheory.MemLp X p P := hX.memLp_comp hμ
/-- d13f23b's `HasLaw.integrable_comp` (InvariantIsing CavityGaussianRows, q251). -/
theorem _root_.ProbabilityTheory.HasLaw.integrable_comp {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω}
    {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup E] {P : MeasureTheory.Measure Ω}
    {μ : MeasureTheory.Measure 𝓧} {X : Ω → 𝓧} {f : 𝓧 → E} (hX : ProbabilityTheory.HasLaw X μ P)
    (hf : MeasureTheory.Integrable f μ) : MeasureTheory.Integrable (f ∘ X) P := by
  have h : MeasureTheory.Integrable f (P.map X) := hX.map_eq ▸ hf
  exact (MeasureTheory.integrable_map_measure h.aestronglyMeasurable hX.aemeasurable).1 h
end OAICompat434
open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction in
open scoped Topology in
/-- Mathlib d13f23b's `tendstoInDistribution_iff_forall_integral_rclike_tendsto` (InvariantIsing, q258). -/
theorem _root_.MeasureTheory.tendstoInDistribution_iff_forall_integral_rclike_tendsto
    {ι E Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mE : MeasurableSpace E} {X : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}
    [TopologicalSpace E] (𝕜 : Type*) [RCLike 𝕜] [OpensMeasurableSpace E]
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ f : E →ᵇ 𝕜, Tendsto (fun i ↦ ∫ ω, f (X i ω) ∂(μ i)) l (𝓝 (∫ ω, f (Z ω) ∂μ')) := by
  have h_map (i) (f : E →ᵇ 𝕜) :
      ∫ x, f x ∂(μ i).map (X i) = ∫ ω, f (X i ω) ∂(μ i) := integral_map (hX i) (by fun_prop)
  have h_map' (f : E →ᵇ 𝕜) :
      ∫ x, f x ∂μ'.map Z = ∫ ω, f (Z ω) ∂μ' := integral_map hZ (by fun_prop)
  refine ⟨fun h f ↦ ?_, fun h ↦ ⟨hX, hZ, ?_⟩⟩
  · have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).mp h.tendsto f
    simpa [h_map, h_map'] using hf
  · apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto (Ω := E) 𝕜).mpr
    intro f
    simpa [h_map, h_map'] using h f

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRows
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian rows used to generate the finite fresh frames. Their empirical
Gram matrices converge almost surely to the identity at fixed frame width. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

lemma cavityGaussianRow_eval_law {q : ℕ} (i : Fin q) :
    HasLaw (fun x : Fin q → ℝ => x i) (gaussianReal 0 1) (cavityGaussianRow q) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval (fun _ : Fin q => gaussianReal 0 1) i).map_eq⟩

lemma cavityGaussianRow_product_integrable {q : ℕ} (i j : Fin q) :
    Integrable (fun x : Fin q → ℝ => x i * x j) (cavityGaussianRow q) := by
  have hi : MemLp (fun x : Fin q → ℝ => x i) 2 (cavityGaussianRow q) := by
    simpa using (cavityGaussianRow_eval_law i).memLp (memLp_id_gaussianReal 2)
  have hj : MemLp (fun x : Fin q → ℝ => x j) 2 (cavityGaussianRow q) := by
    simpa using (cavityGaussianRow_eval_law j).memLp (memLp_id_gaussianReal 2)
  exact hi.integrable_mul hj

lemma cavityGaussianRow_product_integral {q : ℕ} (i j : Fin q) :
    (∫ x : Fin q → ℝ, x i * x j ∂cavityGaussianRow q) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hvar := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [variance_eq_integral measurable_id.aemeasurable] at hvar
    simp only [id_eq, integral_id_gaussianReal, sub_zero, NNReal.coe_one] at hvar
    have hl := (cavityGaussianRow_eval_law i).integral_comp
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
    simpa only [pow_two, Function.comp_apply, ite_true, if_true] using hl.trans hvar
  · have hi : iIndepFun (fun k : Fin q => fun x : Fin q → ℝ => x k) (cavityGaussianRow q) :=
      iIndepFun_pi (fun _ => aemeasurable_id)
    have h := (hi.indepFun hij).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
    have hm k : (∫ x : Fin q → ℝ, x k ∂cavityGaussianRow q) = 0 := by
      simpa only [Function.comp_apply, integral_id_gaussianReal] using
        (cavityGaussianRow_eval_law k).integral_comp (f := fun x : ℝ => x) (by fun_prop)
    simpa only [hm, zero_mul, ite_eq_right hij] using h

lemma cavityGaussianRows_eval_law (q n : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ => x n) (cavityGaussianRow q) (cavityGaussianRows q) := by
  refine ⟨(measurable_pi_apply n).aemeasurable, ?_⟩
  exact Measure.infinitePi_map_eval (fun _ : ℕ => cavityGaussianRow q) n

/-- The fixed-width Gaussian Gram matrix tends to the identity. -/
theorem cavityGaussianRows_gram_tendsto (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun n i j => (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ))
        atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hp (i j : Fin q) : ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun n => (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ))
        atTop (𝓝 (if i = j then 1 else 0)) := by
    let f := fun x : Fin q → ℝ => x i * x j
    have hf : Measurable f := by fun_prop
    have hind : iIndepFun (fun k => fun x : ℕ → Fin q → ℝ => f (x k)) (cavityGaussianRows q) :=
      iIndepFun_infinitePi (fun _ => hf)
    have hid (k : ℕ) : IdentDistrib (fun x : ℕ → Fin q → ℝ => x k)
        (fun x : ℕ → Fin q → ℝ => x 0) (cavityGaussianRows q) (cavityGaussianRows q) :=
      ⟨(cavityGaussianRows_eval_law q k).aemeasurable,
        (cavityGaussianRows_eval_law q 0).aemeasurable,
        (cavityGaussianRows_eval_law q k).map_eq.trans (cavityGaussianRows_eval_law q 0).map_eq.symm⟩
    have hmean : (∫ x, f (x 0) ∂cavityGaussianRows q) = if i = j then 1 else 0 := by
      exact ((cavityGaussianRows_eval_law q 0).integral_comp hf.aestronglyMeasurable).trans
        (cavityGaussianRow_product_integral i j)
    have h := strong_law_ae_real (fun k (x : ℕ → Fin q → ℝ) => f (x k))
      ((cavityGaussianRows_eval_law q 0).integrable_comp (cavityGaussianRow_product_integrable i j))
      (fun k l hkl => hind.indepFun hkl) (fun k => (hid k).comp hf)
    simpa only [hmean, f] using h
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hp i))] with x hx
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [Matrix.one_apply] using hx i j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGram
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eventual nondegeneracy of the Gaussian Gram matrix used to construct
fresh orthonormal directions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma cavityEmpiricalGram_posSemidef {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    (cavityEmpiricalGram x n).PosSemidef := by
  have he : cavityEmpiricalGram x n =
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Matrix.vecMulVec (x k) (x k) := by
    ext i j
    simp only [cavityEmpiricalGram, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he]
  apply (Matrix.posSemidef_sum (Finset.range n) (fun k _ => ?_)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (x k)

lemma cavity_posDef_of_posSemidef_det_ne_zero {q : ℕ}
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef) (hdet : G.det ≠ 0) :
    G.PosDef := by
  apply hG.1.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hprod : (∏ j, hG.1.eigenvalues j) ≠ 0 := by
    rw [hG.1.det_eq_prod_eigenvalues] at hdet
    exact hdet
  have hi : hG.1.eigenvalues i ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hG.eigenvalues_nonneg i) hi.symm

lemma cavityEmpiricalGram_tendsto (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (cavityEmpiricalGram x) atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) :=
  cavityGaussianRows_gram_tendsto q

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGramProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nondegenerate Gaussian frames have probability tending to one.
This also supplies the positive mass needed to condition the finite frame
construction, without any assertion about zero sets of polynomials. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma continuous_cavityEmpiricalGram (q n : ℕ) :
    Continuous (fun x : ℕ → Fin q → ℝ => cavityEmpiricalGram x n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold cavityEmpiricalGram
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditioning on the nondegenerate Gram event does not change the
limit of bounded observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_conditioning_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (f : Ω → Ω') (hf : Measurable f)
    (s : Set Ω') (hs : MeasurableSet s) :
    (cond μ (f ⁻¹' s)).map f = cond (μ.map f) s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.map_smul, Measure.map_apply hf hs,
    Measure.restrict_map hf hs]

lemma cavity_conditioning_invariant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω) (hT : Measurable T) (hμ : μ.map T = μ)
    (s : Set Ω) (hs : MeasurableSet s) (hinv : T ⁻¹' s = s) :
    (cond μ s).map T = cond μ s := by
  have hr : (μ.restrict s).map T = μ.restrict s := by
    calc
      (μ.restrict s).map T = (μ.restrict (T ⁻¹' s)).map T := by rw [hinv]
      _ = (μ.map T).restrict s := (Measure.restrict_map hT hs).symm
      _ = μ.restrict s := by rw [hμ]
  rw [ProbabilityTheory.cond, Measure.map_smul, hr]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gaussian frame construction: normalize the column Gram
matrix by its positive square root. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityGaussianMatrix_gram {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    (cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n =
      cavityEmpiricalGram x n := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cavityGaussianMatrix]
  simp_rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  rw [← Finset.sum_div]
  change (∑ k : Fin n, x k i * x k j) / (n : ℝ) =
    (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ)
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => x k i * x k j) n

lemma cavity_sqrt_det_isUnit {q : ℕ} (G : Matrix (Fin q) (Fin q) ℝ)
    (hG : G.PosDef) : IsUnit (CFC.sqrt G).det := by
  apply isUnit_iff_ne_zero.mpr
  have he : (CFC.sqrt G).det * (CFC.sqrt G).det = G.det := by
    rw [← Matrix.det_mul, CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  intro hz
  rw [hz, zero_mul] at he
  exact hG.det_pos.ne' he.symm

theorem cavityNormalizeFrame_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hG : (A.transpose * A).PosDef) :
    (cavityNormalizeFrame A).transpose * cavityNormalizeFrame A = 1 := by
  let G : Matrix (Fin q) (Fin q) ℝ := A.transpose * A
  let S : Matrix (Fin q) (Fin q) ℝ := CFC.sqrt G
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hs : S.transpose = S :=
    Matrix.isHermitian_iff_isSymm.mp hS.isHermitian
  have hss : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hu : IsUnit S.det := cavity_sqrt_det_isUnit G hG
  change (A * S⁻¹).transpose * (A * S⁻¹) = 1
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hs]
  calc
    S⁻¹ * A.transpose * (A * S⁻¹) = S⁻¹ * G * S⁻¹ := by
      simp only [G, Matrix.mul_assoc]
    _ = S⁻¹ * (S * S) * S⁻¹ := by rw [hss]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hu,
        Matrix.one_mul, Matrix.mul_nonsing_inv S hu]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameTransitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient orthogonal group acts transitively on finite orthonormal
frames. This identifies the orbit on which the conditioned Gaussian frame
law will be compared with Haar measure. -/

noncomputable section
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_orthonormal_transitive {n q : ℕ}
    (v w : Fin q → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w) :
    ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ i, U (v i) = w i := by
  classical
  let bv := OrthonormalBasis.span hv Finset.univ
  let bw := OrthonormalBasis.span hw Finset.univ
  let L := (Submodule.subtypeₗᵢ _).comp
    (bv.equiv bw (Equiv.refl _)).toLinearIsometry
  let U := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  refine ⟨U, fun i => ?_⟩
  have hv' : (bv ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = v i :=
    OrthonormalBasis.span_apply hv _ _
  have hw' : (bw ⟨i, Finset.mem_univ i⟩ : EuclideanSpace ℝ (Fin n)) = w i :=
    OrthonormalBasis.span_apply hw _ _
  change L.extend (v i) = w i
  rw [← hv', LinearIsometry.extend_apply]
  change ((bv.equiv bw (Equiv.refl _)) (bv ⟨i, Finset.mem_univ i⟩) :
    EuclideanSpace ℝ (Fin n)) = w i
  rw [OrthonormalBasis.equiv_apply_basis]
  exact hw'

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameOrbit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix form of transitivity and continuity of the frame orbit action. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

lemma cavityRotationMatrix_apply {n : ℕ} (U : Rotation n)
    (x : EuclideanSpace ℝ (Fin n)) : matrixRotation (cavityRotationMatrix U) x = U x := by
  have h := U.toLinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis x
  ext i
  exact congrFun h i

lemma cavity_orthonormal_of_gram {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) :
    Orthonormal ℝ (fun j : Fin q =>
      (WithLp.toLp 2 (fun i : Fin n => A i j) : EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrArg (fun B : Matrix (Fin q) (Fin q) ℝ => B i j) hA
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

theorem cavityFrame_transitive {n q : ℕ} (A B : Matrix (Fin n) (Fin q) ℝ)
    (hA : A.transpose * A = 1) (hB : B.transpose * B = 1) :
    ∃ U : Orthogonal n, (U : Matrix (Fin n) (Fin n) ℝ) * A = B := by
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive _ _
    (cavity_orthonormal_of_gram A hA) (cavity_orthonormal_of_gram B hB)
  refine ⟨cavityRotationMatrix U, ?_⟩
  ext i j
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (hU j)
  rw [← cavityRotationMatrix_apply U] at h
  exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameLimit
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The correction used to orthonormalize a fixed number of Gaussian
columns converges to the identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gram_sqrt_tendsto {q : ℕ} (G : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hG : ∀ n, (G n).PosSemidef) (hlim : Tendsto G atTop (𝓝 1)) :
    Tendsto (fun n => CFC.sqrt (G n)) atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hw : Tendsto G atTop (𝓝[{A : Matrix (Fin q) (Fin q) ℝ | 0 ≤ A}] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => (hG n).nonneg)⟩
  have hOne : (0 : Matrix (Fin q) (Fin q) ℝ) ≤ 1 := Matrix.PosSemidef.one.nonneg
  have hc := (CFC.continuousOn_sqrt (A := Matrix (Fin q) (Fin q) ℝ)).continuousWithinAt hOne
  have ht := hc.tendsto.comp hw
  change Tendsto (fun n => CFC.sqrt (G n)) atTop
    (𝓝 (CFC.sqrt (1 : Matrix (Fin q) (Fin q) ℝ))) at ht
  simpa only [CFC.sqrt_one] using ht

lemma cavity_gram_correction_tendsto {q : ℕ} (G : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hG : ∀ n, (G n).PosSemidef) (hlim : Tendsto G atTop (𝓝 1)) :
    Tendsto (fun n => (CFC.sqrt (G n))⁻¹) atTop
      (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hc : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _) 1 := by
    have hr : ContinuousAt (Ring.inverse : ℝ → ℝ) 1 := by
      simpa only [Units.val_one] using NormedRing.inverse_continuousAt (1 : ℝˣ)
    exact continuousAt_matrix_inv _ (by simpa only [Matrix.det_one] using hr)
  have ht := hc.tendsto.comp (cavity_gram_sqrt_tendsto G hG hlim)
  change Tendsto (fun n => (CFC.sqrt (G n))⁻¹) atTop
    (𝓝 ((1 : Matrix (Fin q) (Fin q) ℝ)⁻¹)) at ht
  simpa only [inv_one] using ht

theorem cavityGaussian_correction_tendsto (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun n => (CFC.sqrt (cavityEmpiricalGram x n))⁻¹) atTop
        (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  filter_upwards [cavityEmpiricalGram_tendsto q] with x hx
  exact cavity_gram_correction_tendsto (cavityEmpiricalGram x)
    (cavityEmpiricalGram_posSemidef x) hx

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFiniteGaussian
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-dimensional laws of the independent Gaussian array used
in the fresh-frame construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

lemma cavityGaussianRows_coordinate_law {q : ℕ} (k : ℕ) (i : Fin q) :
    HasLaw (fun x : ℕ → Fin q → ℝ => x k i) (gaussianReal 0 1)
      (cavityGaussianRows q) :=
  (cavityGaussianRow_eval_law i).fun_comp (cavityGaussianRows_eval_law q k)

lemma cavityGaussianRows_coordinates_independent (q : ℕ) :
    iIndepFun (fun p : ℕ × Fin q => fun x : ℕ → Fin q → ℝ => x p.1 p.2)
      (cavityGaussianRows q) := by
  simpa only [cavityGaussianRows, cavityGaussianRow, Measure.infinitePi_eq_pi] using
    iIndepFun_uncurry_infinitePi' (fun (_ : ℕ) (_ : Fin q) => gaussianReal 0 1)
      (X := fun _ _ x => x) (fun _ _ => measurable_id)

lemma cavityGaussianRows_finite_array_law (n q : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ => fun p : Fin n × Fin q => x p.1 p.2)
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1))
      (cavityGaussianRows q) := by
  have hinj : Function.Injective (fun p : Fin n × Fin q => ((p.1 : ℕ), p.2)) := by
    intro p r h
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Fin q => z.1) h))
      (congrArg (fun z : ℕ × Fin q => z.2) h)
  have hind : iIndepFun
      (fun p : Fin n × Fin q => fun x : ℕ → Fin q → ℝ => x p.1 p.2)
      (cavityGaussianRows q) := (cavityGaussianRows_coordinates_independent q).precomp hinj
  refine ⟨(measurable_pi_iff.mpr (fun p =>
    (measurable_pi_apply p.2).comp (measurable_pi_apply (p.1 : ℕ)))).aemeasurable, ?_⟩
  have hm := hind.map_fun_eq_pi_map (fun (p : Fin n × Fin q) =>
    (cavityGaussianRows_coordinate_law (p.1 : ℕ) p.2).aemeasurable)
  simpa only [(cavityGaussianRows_coordinate_law _ _).map_eq] using hm

theorem cavityGaussianRows_finite_standard_law (n q : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ =>
      (WithLp.toLp 2 (fun p : Fin n × Fin q => x p.1 p.2) :
        EuclideanSpace ℝ (Fin n × Fin q)))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))) (cavityGaussianRows q) := by
  have ht : HasLaw (WithLp.toLp 2 : (Fin n × Fin q → ℝ) →
      EuclideanSpace ℝ (Fin n × Fin q))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)))
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) :=
    ⟨(by fun_prop), map_pi_eq_stdGaussian⟩
  exact ht.fun_comp (cavityGaussianRows_finite_array_law n q)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameMeasurable
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the finite Gram normalization, including its
arbitrary singular-matrix values. -/

noncomputable section
open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_matrix_inverse_measurable {q : ℕ} :
    Measurable (Inv.inv : Matrix (Fin q) (Fin q) ℝ → Matrix (Fin q) (Fin q) ℝ) := by
  have he (A : Matrix (Fin q) (Fin q) ℝ) : A⁻¹ = A.det⁻¹ • A.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp_rw [show (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _) =
    (fun A => A.det⁻¹ • A.adjugate) from funext he]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

lemma measurable_cavityNormalizeFrame (n q : ℕ) :
    Measurable (cavityNormalizeFrame : Matrix (Fin n) (Fin q) ℝ → Matrix (Fin n) (Fin q) ℝ) := by
  have hg : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => A.transpose * A) := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => ∑ k, A k i * A k j)
    exact Finset.measurable_sum _ (fun k _ =>
      (Matrix.measurable_apply (i := k) (j := i)).mul
        (Matrix.measurable_apply (i := k) (j := j)))
  have hs : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => CFC.sqrt (A.transpose * A)) :=
    CFC.measurable_sqrt.comp hg
  have hi : Measurable (fun A : Matrix (Fin n) (Fin q) ℝ =>
      (CFC.sqrt (A.transpose * A))⁻¹) := cavity_matrix_inverse_measurable.comp hs
  unfold cavityNormalizeFrame
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ =>
    ∑ k, A i k * ((CFC.sqrt (A.transpose * A))⁻¹) k j)
  exact Finset.measurable_sum _ (fun k _ =>
    (Matrix.measurable_apply (i := i) (j := k)).mul (hi.eval_matrix))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal equivariance of the Gaussian frame normalization. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavityGram_left_orthogonal {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    (U * A).transpose * (U * A) = A.transpose * A := by
  rw [Matrix.transpose_mul]
  calc
    A.transpose * U.transpose * (U * A) = A.transpose * (U.transpose * U) * A := by
      simp only [Matrix.mul_assoc]
    _ = A.transpose * A := by rw [hU, Matrix.mul_one]

lemma cavityNormalizeFrame_left_orthogonal {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    cavityNormalizeFrame (U * A) = U * cavityNormalizeFrame A := by
  simp only [cavityNormalizeFrame, cavityGram_left_orthogonal A U hU, Matrix.mul_assoc]


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal invariance of the finite Gaussian array, expressed as a
simultaneous rotation of all its columns. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InvariantIsing

lemma cavityColumnRotation_apply {n q : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n × Fin q)) (k : Fin n) (j : Fin q) :
    cavityColumnRotation q U x (k, j) =
      U (WithLp.toLp 2 (fun i : Fin n => x (i, j))) k := rfl

theorem cavityColumnRotation_gaussian {n q : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))).map (cavityColumnRotation q U) =
      stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) :=
  stdGaussian_map (cavityColumnRotation q U)

lemma cavityArrayMatrix_rotation {n q : ℕ} (U : Orthogonal n)
    (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    cavityArrayMatrix n q (cavityColumnRotation q (matrixRotation U) z) =
      (U : Matrix (Fin n) (Fin n) ℝ) * cavityArrayMatrix n q z := by
  ext k j
  simp only [cavityArrayMatrix, cavityColumnRotation_apply, matrixRotation_apply,
    Matrix.mul_apply, Finset.sum_div, mul_div_assoc]

lemma cavityArrayFrame_rotation {n q : ℕ} (U : Orthogonal n)
    (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    cavityNormalizeFrame (cavityArrayMatrix n q (cavityColumnRotation q (matrixRotation U) z)) =
      (U : Matrix (Fin n) (Fin n) ℝ) * cavityNormalizeFrame (cavityArrayMatrix n q z) := by
  rw [cavityArrayMatrix_rotation]
  exact cavityNormalizeFrame_left_orthogonal _ _
    ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityConditionedFrame
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite conditioned Gaussian construction is an orthonormal frame
and has an exactly orthogonally invariant law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityArrayMatrix (n q : ℕ) :
    Measurable (cavityArrayMatrix n q) := by
  unfold cavityArrayMatrix
  fun_prop

lemma measurableSet_cavityArrayGood (n q : ℕ) : MeasurableSet (cavityArrayGood n q) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
      (cavityArrayMatrix n q z).transpose * cavityArrayMatrix n q z) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cavityArrayMatrix]
    fun_prop
  exact measurableSet_lt measurable_const hc.matrix_det.measurable

lemma cavityArrayGood_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityColumnRotation q (matrixRotation U)) ⁻¹' cavityArrayGood n q =
      cavityArrayGood n q := by
  ext z
  simp only [Set.mem_preimage, cavityArrayGood, Set.mem_ofPred_eq, cavityArrayMatrix_rotation,
    cavityGram_left_orthogonal _ _
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property)]

lemma cavityArrayGood_probability (n q : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) =
      cavityGaussianRows q (cavityGoodGram q n) := by
  rw [← (cavityGaussianRows_finite_standard_law n q).map_eq,
    Measure.map_apply_of_aemeasurable (cavityGaussianRows_finite_standard_law n q).aemeasurable
      (measurableSet_cavityArrayGood n q)]
  congr 1
  ext x
  change 0 < ((cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n).det ↔ _
  rw [cavityGaussianMatrix_gram]
  rfl

lemma cavityConditionedFrameLaw_of_rows (n q : ℕ) :
    (cond (cavityGaussianRows q) (cavityGoodGram q n)).map
      (fun x => cavityNormalizeFrame (cavityGaussianMatrix x n)) =
        cavityConditionedFrameLaw n q := by
  let f := fun x : ℕ → Fin q → ℝ => (WithLp.toLp 2
    (fun p : Fin n × Fin q => x p.1 p.2) : EuclideanSpace ℝ (Fin n × Fin q))
  have hf : Measurable f := (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.mpr (fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply (p.1 : ℕ))))
  have hpre : f ⁻¹' cavityArrayGood n q = cavityGoodGram q n := by
    ext x
    change 0 < ((cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n).det ↔ _
    rw [cavityGaussianMatrix_gram]
    rfl
  have hmap := cavity_conditioning_map (cavityGaussianRows q) f hf
    (cavityArrayGood n q) (measurableSet_cavityArrayGood n q)
  rw [hpre, (cavityGaussianRows_finite_standard_law n q).map_eq] at hmap
  rw [cavityConditionedFrameLaw, ← hmap]
  rw [Measure.map_map (show Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)) from
      (measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)) hf]
  rfl

lemma cavityConditionedFrameLaw_probability {n q : ℕ}
    (hp : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0) :
    IsProbabilityMeasure (cavityConditionedFrameLaw n q) := by
  let := cond_isProbabilityMeasure hp
  unfold cavityConditionedFrameLaw
  first | exact Measure.isProbabilityMeasure_map ((measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)).aemeasurable | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem cavityConditionedFrameLaw_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityConditionedFrameLaw n q).map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) =
      cavityConditionedFrameLaw n q := by
  let f := fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)
  let act := fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A
  let R := cavityColumnRotation q (matrixRotation U)
  have hf : Measurable f := (measurable_cavityNormalizeFrame n q).comp
    (measurable_cavityArrayMatrix n q)
  have ha : Measurable act :=
    ((continuous_cavityFrameAction n q).comp (continuous_const.prodMk continuous_id)).measurable
  have hR : Measurable R := R.continuous.measurable
  have he : act ∘ f = f ∘ R := funext (fun z => (cavityArrayFrame_rotation U z).symm)
  have hinv := cavity_conditioning_invariant (stdGaussian _) R hR
    (cavityColumnRotation_gaussian (matrixRotation U)) (cavityArrayGood n q)
    (measurableSet_cavityArrayGood n q) (cavityArrayGood_rotation U)
  change ((cond (stdGaussian _) (cavityArrayGood n q)).map f).map act =
    (cond (stdGaussian _) (cavityArrayGood n q)).map f
  rw [Measure.map_map ha hf, he, ← Measure.map_map hf hR, hinv]

theorem cavityConditionedFrameLaw_orthonormal (n q : ℕ) :
    ∀ᵐ A ∂cavityConditionedFrameLaw n q, A.transpose * A = 1 := by
  have hf : Measurable (fun z => cavityNormalizeFrame (cavityArrayMatrix n q z)) :=
    (measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)
  have hs : MeasurableSet {A : Matrix (Fin n) (Fin q) ℝ | A.transpose * A = 1} :=
    (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id)
      continuous_const).measurableSet
  rw [cavityConditionedFrameLaw, ae_map_iff hf.aemeasurable hs]
  apply ae_cond_of_forall_mem (measurableSet_cavityArrayGood n q)
  intro z hz
  apply cavityNormalizeFrame_gram
  apply cavity_posDef_of_posSemidef_det_ne_zero
  · simpa using Matrix.posSemidef_conjTranspose_mul_self (cavityArrayMatrix n q z)
  · exact ne_of_gt hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityFrameHaar
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness of the invariant frame law, proved by averaging bounded
continuous tests over the compact orthogonal group. -/

noncomputable section
open MeasureTheory
open scoped Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityFrame_eq_haar_orbit {n q : ℕ}
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Matrix (Fin n) (Fin q) ℝ)) [IsProbabilityMeasure ν]
    (hinv : ∀ U : Orthogonal n,
      ν.map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) = ν)
    (hframe : ∀ᵐ A ∂ν, A.transpose * A = 1)
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1) :
    ν = μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) := by
  let : HasOuterApproxClosed (Matrix (Fin n) (Fin q) ℝ) :=
    inferInstanceAs (HasOuterApproxClosed (Fin n → Fin q → ℝ))
  let : SecondCountableTopology (Matrix (Fin n) (Fin q) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin q → ℝ))
  have hact := continuous_cavityFrameAction n q
  have hfix (U : Orthogonal n) :
      Continuous (fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A) :=
    hact.comp (continuous_const.prodMk continuous_id)
  have horbit : Continuous (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) :=
    hact.comp (continuous_id.prodMk continuous_const)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  have hi : Integrable (fun p : Orthogonal n × Matrix (Fin n) (Fin q) ℝ =>
      F ((p.1 : Matrix (Fin n) (Fin n) ℝ) * p.2)) (μ.prod ν) :=
    Integrable.of_bound (F.continuous.comp hact).aestronglyMeasurable ‖F‖
      (ae_of_all _ (fun p => F.norm_coe_le_norm _))
  have hrow (U : Orthogonal n) :
      (∫ A, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂ν) = ∫ A, F A ∂ν := by
    rw [← integral_map (hfix U).aemeasurable F.continuous.aestronglyMeasurable, hinv U]
  have hcol : ∀ᵐ A ∂ν,
      (∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂μ) =
        ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
    filter_upwards [hframe] with A hA
    obtain ⟨V, hV⟩ := cavityFrame_transitive A₀ A hA₀ hA
    rw [← hV]
    simp only [← Matrix.mul_assoc]
    change (∫ U, F (((U * V : Orthogonal n) : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ) = _
    exact integral_mul_right_eq_self (μ := μ)
      (fun U : Orthogonal n => F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀)) V
  calc
    (∫ A, F A ∂ν) = ∫ U, ∫ A, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂ν ∂μ := by
      simp only [hrow]
      simp
    _ = ∫ A, ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂μ ∂ν :=
      integral_integral_swap hi
    _ = ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
      rw [integral_congr_ae hcol]
      simp
    _ = ∫ A, F A ∂μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) :=
      (integral_map horbit.aemeasurable F.continuous.aestronglyMeasurable).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianImage
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular Gaussian images, used for finitely many replica
projections of a fresh frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_rectangular_adjoint {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (B : Matrix a b ℝ) :
    B.toEuclideanLin.toContinuousLinearMap.adjoint =
      B.transpose.toEuclideanLin.toContinuousLinearMap := by
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

theorem cavity_standardGaussian_image {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (B : Matrix a b ℝ) :
    (stdGaussian (EuclideanSpace ℝ b)).map B.toEuclideanLin.toContinuousLinearMap =
      multivariateGaussian 0 (B * B.transpose) := by
  let L := B.toEuclideanLin.toContinuousLinearMap
  have hB : (B * B.transpose).PosSemidef := by
    simpa using
      Matrix.posSemidef_self_mul_conjTranspose B
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian, map_zero, integral_id_multivariateGaussian]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id L, covarianceBilin_stdGaussian,
      innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left,
      covarianceBilin_multivariateGaussian hB]
    have he : L (L.adjoint v) = (B * B.transpose).toEuclideanLin v := by
      rw [show L.adjoint = B.transpose.toEuclideanLin.toContinuousLinearMap from
        cavity_rectangular_adjoint B]
      ext i
      change (B *ᵥ (B.transpose *ᵥ fun j => v j)) i =
        ((B * B.transpose) *ᵥ fun j => v j) i
      rw [Matrix.mulVec_mulVec]
    rw [he]
    exact Matrix.inner_toEuclideanCLM (B * B.transpose) u v

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak continuity of the finite Gaussian marks in their covariance,
including singular limiting covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace InvariantIsing

variable {a : Type*} [Fintype a] [DecidableEq a]

lemma cavity_sqrt_tendsto (S : ℕ → Matrix a a ℝ)
    (S₀ : Matrix a a ℝ) (hS : ∀ n, (S n).PosSemidef)
    (hS₀ : S₀.PosSemidef) (hlim : Tendsto S atTop (𝓝 S₀)) :
    Tendsto (fun n => CFC.sqrt (S n)) atTop (𝓝 (CFC.sqrt S₀)) := by
  have hw : Tendsto S atTop (𝓝[{A : Matrix a a ℝ | 0 ≤ A}] S₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => (hS n).nonneg)⟩
  have hc := (CFC.continuousOn_sqrt (A := Matrix a a ℝ)).continuousWithinAt
    hS₀.nonneg
  exact hc.tendsto.comp hw

lemma cavity_matrix_action_continuous (x : EuclideanSpace ℝ a) :
    Continuous (fun A : Matrix a a ℝ => A.toEuclideanLin x) := by
  change Continuous (fun A : Matrix a a ℝ =>
    WithLp.toLp 2 (fun i => ∑ j, A i j * x j))
  fun_prop

theorem cavity_multivariateGaussian_integral_tendsto 
    (S : ℕ → Matrix a a ℝ) (S₀ : Matrix a a ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀))
    (F : EuclideanSpace ℝ a →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F x ∂multivariateGaussian 0 (S n)) atTop
      (𝓝 (∫ x, F x ∂multivariateGaussian 0 S₀)) := by
  have hrep (A : Matrix a a ℝ) :
      (∫ x, F x ∂multivariateGaussian 0 A) =
      ∫ x : EuclideanSpace ℝ a, F ((CFC.sqrt A).toEuclideanLin x) ∂stdGaussian _ := by
    rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
    simp only [zero_add]
    rfl
  simp_rw [hrep]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.comp
      (CFC.sqrt (S n)).toEuclideanLin.continuous_of_finiteDimensional).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun x => F.norm_coe_le_norm _)
  · exact ae_of_all _ (fun x => F.continuous.tendsto _ |>.comp
      ((cavity_matrix_action_continuous x).tendsto _ |>.comp
        (cavity_sqrt_tendsto S S₀ hS hS₀ hlim)))

theorem cavity_multivariateGaussian_weak_tendsto 
    (S : ℕ → Matrix a a ℝ) (S₀ : Matrix a a ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀)) :
    Tendsto (fun n => (⟨multivariateGaussian 0 (S n), inferInstance⟩ :
      ProbabilityMeasure (EuclideanSpace ℝ a))) atTop
      (nhds (X := ProbabilityMeasure (EuclideanSpace ℝ a))
        ⟨multivariateGaussian 0 S₀, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact cavity_multivariateGaussian_integral_tendsto S S₀ hS hS₀ hlim

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianJointTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint weak continuity of Gaussian marks and their finite overlap
labels, including singular covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace InvariantIsing

variable {a L : Type*} [Fintype a] [DecidableEq a] [MetricSpace L]

lemma cavity_gaussian_joint_test_tendsto
    (l : ℕ → L) (l₀ : L) (hl : Tendsto l atTop (𝓝 l₀))
    (S : ℕ → Matrix a a ℝ) (S₀ : Matrix a a ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀)) (F : L × EuclideanSpace ℝ a →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, F (l n, z) ∂multivariateGaussian 0 (S n)) atTop
      (𝓝 (∫ z, F (l₀, z) ∂multivariateGaussian 0 S₀)) := by
  have hrep (x : L) (A : Matrix a a ℝ) :
      (∫ z, F (x, z) ∂multivariateGaussian 0 A) =
        ∫ z : EuclideanSpace ℝ a, F (x, (CFC.sqrt A).toEuclideanLin z) ∂stdGaussian _ := by
    rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
    simp only [zero_add]
    rfl
  simp_rw [hrep]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.comp (continuous_const.prodMk
      (CFC.sqrt (S n)).toEuclideanLin.continuous_of_finiteDimensional)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun z => F.norm_coe_le_norm _)
  · exact ae_of_all _ fun z => F.continuous.tendsto _ |>.comp
      (hl.prodMk_nhds ((cavity_matrix_action_continuous z).tendsto _ |>.comp
        (cavity_sqrt_tendsto S S₀ hS hS₀ hlim)))

lemma cavity_gaussian_joint_test_extension (F : L × EuclideanSpace ℝ a →ᵇ ℝ) :
    ∃ G : L × Matrix a a ℝ →ᵇ ℝ, ∀ l S, S.PosSemidef →
      G (l, S) = ∫ z, F (l, z) ∂multivariateGaussian 0 S := by
  let s : Set (L × Matrix a a ℝ) := {p | p.2.PosSemidef}
  have hs : IsClosed s := Matrix.posSemidef_is_closed.preimage continuous_snd
  let g : s → ℝ := fun p => ∫ z, F (p.1.1, z) ∂multivariateGaussian 0 p.1.2
  have hg : Continuous g := by
    apply continuous_iff_seqContinuous.mpr
    intro p p₀ hp
    exact cavity_gaussian_joint_test_tendsto (fun n => (p n).1.1) p₀.1.1
      ((continuous_fst.comp continuous_subtype_val).tendsto _ |>.comp hp)
      (fun n => (p n).1.2) p₀.1.2 (fun n => (p n).2) p₀.2
      ((continuous_snd.comp continuous_subtype_val).tendsto _ |>.comp hp) F
  have hgb (p : s) : ‖g p‖ ≤ ‖F‖ := by
    have hb := norm_integral_le_of_norm_le_const
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ a) p.1.2)
      (f := fun z => F (p.1.1, z)) (C := ‖F‖)
      (ae_of_all _ fun z => F.norm_coe_le_norm _)
    simpa only [probReal_univ, mul_one] using hb
  let b : s →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g hg ‖F‖ hgb
  obtain ⟨G, _, hG⟩ := b.exists_norm_eq_domRestrict_eq_of_closed hs
  refine ⟨G, fun l S hS => ?_⟩
  exact congrArg (fun f : s →ᵇ ℝ => f ⟨(l, S), hS⟩) hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Gaussian law before orthonormalization. Different fresh
axes are independent; replica covariance is the normalized Gram matrix
of the projected replica vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityProjectionMatrix_covariance {n r q : ℕ}
    (v : Fin r → Fin n → ℝ) (a b : Fin r × Fin q) :
    (cavityProjectionMatrix (q := q) v * (cavityProjectionMatrix (q := q) v).transpose) a b =
      if a.2 = b.2 then (∑ k, v a.1 k * v b.1 k) / (n : ℝ) else 0 := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hs (k : Fin n) :
      (∑ j : Fin q, cavityProjectionMatrix (q := q) v a (k, j) *
        (cavityProjectionMatrix (q := q) v).transpose (k, j) b) =
      if a.2 = b.2 then v a.1 k * v b.1 k / (n : ℝ) else 0 := by
    by_cases hab : a.2 = b.2
    · simp only [cavityProjectionMatrix, Matrix.transpose_apply]
      rw [hab]
      simp only [ite_mul_ite, mul_zero, ite_true, if_true, div_mul_div_comm,
        Real.mul_self_sqrt (Nat.cast_nonneg n)]
      simp
    · have hz (j : Fin q) : cavityProjectionMatrix (q := q) v a (k, j) *
          (cavityProjectionMatrix (q := q) v).transpose (k, j) b = 0 := by
        by_cases haj : a.2 = j
        · have hbj : b.2 ≠ j := fun h => hab (haj.trans h.symm)
          simp [cavityProjectionMatrix, Matrix.transpose_apply, haj, hbj]
        · simp [cavityProjectionMatrix, Matrix.transpose_apply, haj]
      simp only [hz, Finset.sum_const_zero, ite_eq_right hab]
  simp_rw [hs]
  split_ifs <;> simp [Finset.sum_div]

lemma cavityRawProjection_apply {n r q : ℕ} (v : Fin r → Fin n → ℝ)
    (x : ℕ → Fin q → ℝ) (a : Fin r × Fin q) :
    cavityRawProjection v x a =
      ∑ k : Fin n, v a.1 k * cavityGaussianMatrix x n k a.2 := by
  classical
  change (∑ b : Fin n × Fin q, cavityProjectionMatrix (q := q) v a b * x b.1 b.2) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simp only [cavityProjectionMatrix, ite_mul, zero_mul]
  simp [cavityGaussianMatrix, div_mul_eq_mul_div, mul_div_assoc]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRank
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-sure nonsingularity of the fixed-width iid Gaussian block. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma gaussian_pi_extract_law {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (f : J → I) (hf : Function.Injective f) :
    (Measure.pi (fun _ : I => gaussianReal 0 1)).map
      (fun x j => x (f j)) = Measure.pi (fun _ : J => gaussianReal 0 1) := by
  have hi : iIndepFun (fun i : I => fun x : I → ℝ => x i)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have he := (hi.precomp hf).map_fun_eq_pi_map (fun j =>
    (measurable_pi_apply (f j)).aemeasurable)
  simpa only [(measurePreserving_eval (fun _ : I => gaussianReal 0 1) _).map_eq] using he

/-- Replacing one coordinate by a fresh standard Gaussian preserves the
finite iid Gaussian law. The unused old coordinate causes no problem. -/
private lemma gaussian_pi_update_law {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    ((Measure.pi (fun _ : I => gaussianReal 0 1)).prod (gaussianReal 0 1)).map
      (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) =
        Measure.pi (fun _ : I => gaussianReal 0 1) := by
  have hm : Measurable (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) :=
    measurable_update'
  symm
  apply Measure.pi_eq
  intro s hs
  have hpre : (fun p : (I → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j; simp
        · simpa only [Function.update_of_ne hji] using hp j
      · simpa only [Function.update_self] using hp i
    · rintro ⟨hp, hi⟩ j
      by_cases hji : j = i
      · subst j; simpa only [Function.update_self] using hi
      · simpa only [Function.update_of_ne hji] using hp j
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi]
  have he : (fun j => (gaussianReal 0 1) (Function.update s i Set.univ j)) =
      Function.update (fun j => (gaussianReal 0 1) (s j)) i 1 := by
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hji]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using
    (Finset.prod_erase_mul (s := Finset.univ)
      (f := fun j => (gaussianReal 0 1) (s j)) (Finset.mem_univ i))

private lemma determinant_update_corner_affine (n : ℕ)
    (x : Fin (n + 1) × Fin (n + 1) → ℝ) :
    ∃ c : ℝ, ∀ t : ℝ,
      Matrix.det (fun i j => Function.update x (0, 0) t (i, j)) =
        t * Matrix.det (fun i j : Fin n => x (i.succ, j.succ)) + c := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => x (i, j)
  refine ⟨∑ j : Fin n, (-1 : ℝ) ^ (j.succ : ℕ) * A 0 j.succ *
    Matrix.det (A.submatrix Fin.succ j.succ.succAbove), ?_⟩
  intro t
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => Function.update x (0, 0) t (i, j)
  have hb (j : Fin (n + 1)) : B.submatrix Fin.succ j.succAbove =
      A.submatrix Fin.succ j.succAbove := by
    ext a b
    change Function.update x (0, 0) t (a.succ, j.succAbove b) = x (a.succ, j.succAbove b)
    exact Function.update_of_ne
      (show (a.succ, j.succAbove b) ≠ (0, 0) from
        fun h => Fin.succ_ne_zero a (congrArg Prod.fst h)) t x
  change B.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp_rw [hb]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  have h00 : B 0 0 = t := by simp [B]
  have h0j (j : Fin n) : B 0 j.succ = A 0 j.succ := by simp [B, A]
  rw [h00]
  simp_rw [h0j]
  rfl

private lemma gaussian_affine_ne_zero (a c : ℝ) (ha : a ≠ 0) :
    ∀ᵐ t ∂gaussianReal 0 1, t * a + c ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hn : ∀ᵐ t ∂gaussianReal 0 1, t ≠ -c / a := by
    exact compl_mem_ae_iff.mpr (measure_singleton (-c / a))
  filter_upwards [hn] with t ht
  intro he
  apply ht
  apply (eq_div_iff ha).mpr
  linarith

/-- A square matrix with independent standard Gaussian entries is
nonsingular almost surely, including the empty-matrix convention. -/
theorem cavityGaussianSquare_det_ne_zero (n : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1),
      Matrix.det (fun i j => x (i, j)) ≠ 0 := by
  induction n with
  | zero =>
    apply ae_of_all
    intro x
    have h : Matrix.det (show Matrix (Fin 0) (Fin 0) ℝ from fun i j => x (i, j)) = 1 :=
      Matrix.det_isEmpty
    exact h.trans_ne one_ne_zero
  | succ n ih =>
    let μ := Measure.pi (fun _ : Fin (n + 1) × Fin (n + 1) => gaussianReal 0 1)
    let corner : Fin (n + 1) × Fin (n + 1) := (0, 0)
    let f : Fin n × Fin n → Fin (n + 1) × Fin (n + 1) := fun p => (p.1.succ, p.2.succ)
    have hf : Function.Injective f := by
      intro p q h
      exact Prod.ext (Fin.succ_inj.mp (congrArg Prod.fst h))
        (Fin.succ_inj.mp (congrArg Prod.snd h))
    have hminor : ∀ᵐ x ∂μ, Matrix.det (fun i j : Fin n => x (i.succ, j.succ)) ≠ 0 := by
      have hh : ∀ᵐ y ∂μ.map (fun x j => x (f j)),
          Matrix.det (fun i j : Fin n => y (i, j)) ≠ 0 := by
        rw [gaussian_pi_extract_law f hf]
        exact ih
      exact ae_of_ae_map
        (show AEMeasurable (fun x j => x (f j)) μ from (by fun_prop : Measurable _).aemeasurable) hh
    have hpair : ∀ᵐ p ∂μ.prod (gaussianReal 0 1),
        Matrix.det (fun i j => Function.update p.1 corner p.2 (i, j)) ≠ 0 := by
      have hm : Measurable (fun p : (Fin (n + 1) × Fin (n + 1) → ℝ) × ℝ =>
          Matrix.det (fun i j => Function.update p.1 corner p.2 (i, j))) := by
        unfold corner
        fun_prop
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const).compl).mpr
      filter_upwards [hminor] with x hx
      obtain ⟨c, hc⟩ := determinant_update_corner_affine n x
      filter_upwards [gaussian_affine_ne_zero _ c hx] with t ht
      simpa only [corner, hc] using ht
    rw [← gaussian_pi_update_law corner]
    apply (ae_map_iff (by fun_prop)
      (measurableSet_eq_fun (by fun_prop) measurable_const).compl).mpr
    exact hpair

/-- The concrete first `q` iid Gaussian rows used by the frame construction
are full rank almost surely. -/
theorem cavityGaussianRows_square_det_ne_zero (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Matrix.det (fun i j : Fin q => x i j) ≠ 0 := by
  have hh : ∀ᵐ y ∂(cavityGaussianRows q).map
      (fun x : ℕ → Fin q → ℝ => fun p : Fin q × Fin q => x p.1 p.2),
      Matrix.det (fun i j : Fin q => y (i, j)) ≠ 0 := by
    rw [(cavityGaussianRows_finite_array_law q q).map_eq]
    exact cavityGaussianSquare_det_ne_zero q
  exact ae_of_ae_map (cavityGaussianRows_finite_array_law q q).aemeasurable hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityProjectionLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gram correction leaves the Gaussian projection limit unchanged.
The Slutsky step allows arbitrary dependence between the raw projections
and their normalizing Gram matrix. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityGaussian_correction_measurable (q n : ℕ) :
    Measurable (fun x : ℕ → Fin q → ℝ => (CFC.sqrt (cavityEmpiricalGram x n))⁻¹) :=
  cavity_matrix_inverse_measurable.comp
    (CFC.measurable_sqrt.comp (continuous_cavityEmpiricalGram q n).measurable)

lemma cavityCorrectProjection_raw_apply {n r q : ℕ}
    (v : Fin r → Fin n → ℝ) (x : ℕ → Fin q → ℝ) (a : Fin r × Fin q) :
    cavityCorrectProjection (cavityRawProjection v x)
      ((CFC.sqrt (cavityEmpiricalGram x n))⁻¹) a =
      ∑ k : Fin n, v a.1 k * cavityNormalizeFrame (cavityGaussianMatrix x n) k a.2 := by
  change (∑ j, cavityRawProjection v x (a.1, j) *
      ((CFC.sqrt (cavityEmpiricalGram x n))⁻¹) j a.2) = _
  simp_rw [cavityRawProjection_apply]
  unfold cavityNormalizeFrame
  rw [cavityGaussianMatrix_gram]
  exact congrArg (fun M : Matrix (Fin r) (Fin q) ℝ => M a.1 a.2)
    (Matrix.mul_assoc v (cavityGaussianMatrix x n) ((CFC.sqrt (cavityEmpiricalGram x n))⁻¹))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGaussianRankGram
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive definiteness of finite Gaussian and normalized-frame windows. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator NNReal

namespace InvariantIsing

lemma cavity_gram_posDef_of_minor {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (f : Fin q → Fin N) (hdet : (A.submatrix f id).det ≠ 0) :
    (A.transpose * A).PosDef := by
  have hB : Function.Injective (A.submatrix f id).mulVec :=
    Matrix.mulVec_injective_iff.mpr
      ((Matrix.nonsingular_iff_det_ne_zero.mpr hdet).linearIndependent_col)
  have hA : Function.Injective A.mulVec := by
    intro x y hxy
    apply hB
    funext i
    simpa only [Matrix.mulVec, Matrix.submatrix_apply, id_eq, dotProduct] using
      congrFun hxy (f i)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self A hA

/-- Positive definiteness holds at every admissible finite row count. -/
theorem cavityGaussianRows_gram_posDef (N q : ℕ) (hqN : q ≤ N) :
    ∀ᵐ x ∂cavityGaussianRows q, (cavityEmpiricalGram x N).PosDef := by
  by_cases hq : q = 0
  · subst q
    apply ae_of_all
    intro x
    exact cavity_posDef_of_posSemidef_det_ne_zero
      (cavityEmpiricalGram_posSemidef x N)
      (by
        have h : (cavityEmpiricalGram x N).det = 1 := Matrix.det_isEmpty
        exact h.trans_ne one_ne_zero)
  have hN : 0 < N := by omega
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.mpr hN))
  filter_upwards [cavityGaussianRows_square_det_ne_zero q] with x hx
  let A := cavityGaussianMatrix x N
  let f : Fin q → Fin N := Fin.castLE hqN
  let B : Matrix (Fin q) (Fin q) ℝ := fun i j => x i j
  have he : A.submatrix f id = (Real.sqrt (N : ℝ))⁻¹ • B := by
    ext i j
    change x i j / Real.sqrt (N : ℝ) = (Real.sqrt (N : ℝ))⁻¹ * x i j
    ring
  have hdet : (A.submatrix f id).det ≠ 0 := by
    rw [he, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hsqrt)) hx
  rw [← cavityGaussianMatrix_gram]
  exact cavity_gram_posDef_of_minor A f hdet

lemma cavityGoodGram_probability_one (N q : ℕ) (hqN : q ≤ N) :
    cavityGaussianRows q (cavityGoodGram q N) = 1 := by
  have hae : cavityGoodGram q N =ᵐ[cavityGaussianRows q] Set.univ := by
    filter_upwards [cavityGaussianRows_gram_posDef N q hqN] with x hx
    change (0 < (cavityEmpiricalGram x N).det) = True
    exact propext (iff_true_intro hx.det_pos)
  rw [measure_congr hae, measure_univ]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupGaussian
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent Gaussian arrays for the finitely many spectral groups.
The finite restrictions are exactly standard Gaussian vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

lemma cavityGroupGaussian_eval_law {m q : ℕ} (a : Fin m) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ => x a) (cavityGaussianRows q)
      (cavityGroupGaussianRows m q) :=
  ⟨(measurable_pi_apply a).aemeasurable,
    (measurePreserving_eval (fun _ : Fin m => cavityGaussianRows q) a).map_eq⟩

lemma cavityGroupGaussian_row_law {m q : ℕ} (a : Fin m) (k : ℕ) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ => x a k) (cavityGaussianRow q)
      (cavityGroupGaussianRows m q) :=
  (cavityGaussianRows_eval_law q k).fun_comp (cavityGroupGaussian_eval_law a)

lemma cavityGroupGaussian_coordinate_law {m q : ℕ} (a : Fin m) (k : ℕ) (j : Fin q) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ => x a k j) (gaussianReal 0 1)
      (cavityGroupGaussianRows m q) :=
  (cavityGaussianRow_eval_law j).fun_comp (cavityGroupGaussian_row_law a k)

lemma cavityGroupGaussian_coordinates_independent (m q : ℕ) :
    iIndepFun (fun p : (Fin m × ℕ) × Fin q =>
      fun x : Fin m → ℕ → Fin q → ℝ => x p.1.1 p.1.2 p.2)
      (cavityGroupGaussianRows m q) := by
  have hrows : iIndepFun (fun p : Fin m × ℕ =>
      fun x : Fin m → ℕ → Fin q → ℝ => x p.1 p.2) (cavityGroupGaussianRows m q) := by
    simpa only [cavityGroupGaussianRows, cavityGaussianRows, Measure.infinitePi_eq_pi] using
      iIndepFun_uncurry_infinitePi' (fun (_ : Fin m) (_ : ℕ) => cavityGaussianRow q)
        (X := fun _ _ x => x) (fun _ _ => measurable_id)
  apply iIndepFun_uncurry' (fun _ _ => by fun_prop) hrows
  intro p
  exact (iIndepFun_iff_hasLaw_pi_pi
    (fun j => cavityGroupGaussian_coordinate_law p.1 p.2 j)).mpr
      (cavityGroupGaussian_row_law p.1 p.2)

lemma cavityGroupGaussian_finite_array_law {m q : ℕ} (N : Fin m → ℕ) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ =>
      fun p : (a : Fin m) × (Fin (N a) × Fin q) => x p.1 p.2.1 p.2.2)
      (Measure.pi (fun _ : (a : Fin m) × (Fin (N a) × Fin q) => gaussianReal 0 1))
      (cavityGroupGaussianRows m q) := by
  have hinj : Function.Injective (fun p : (a : Fin m) × (Fin (N a) × Fin q) =>
      ((p.1, (p.2.1 : ℕ)), p.2.2)) := by
    intro p r h
    cases p with | mk a p =>
      cases r with | mk b r =>
        have hab : a = b := congrArg (fun z : (Fin m × ℕ) × Fin q => z.1.1) h
        subst b
        congr 1
        exact Prod.ext (Fin.ext (congrArg (fun z : (Fin m × ℕ) × Fin q => z.1.2) h))
          (congrArg (fun z : (Fin m × ℕ) × Fin q => z.2) h)
  exact iIndepFun.hasLaw_pi
    (fun p => cavityGroupGaussian_coordinate_law p.1 p.2.1 p.2.2)
    ((cavityGroupGaussian_coordinates_independent m q).precomp hinj)

theorem cavityGroupGaussian_finite_standard_law {m q : ℕ} (N : Fin m → ℕ) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ =>
      (WithLp.toLp 2 (fun p : (a : Fin m) × (Fin (N a) × Fin q) =>
        x p.1 p.2.1 p.2.2) : EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q))))
      (stdGaussian (EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q))))
      (cavityGroupGaussianRows m q) := by
  have h : HasLaw (WithLp.toLp 2 : (((a : Fin m) × (Fin (N a) × Fin q)) → ℝ) →
      EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q)))
      (stdGaussian (EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q))))
      (Measure.pi (fun _ : (a : Fin m) × (Fin (N a) × Fin q) => gaussianReal 0 1)) :=
    ⟨(by fun_prop), map_pi_eq_stdGaussian⟩
  exact h.fun_comp (cavityGroupGaussian_finite_array_law N)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupProjection
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint projections in the independent spectral groups. The output index
retains the group, replica, and fresh-axis coordinates, so the limiting
Gaussian law records independence between different groups. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityGroupRawProjection_apply {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (x : Fin m → ℕ → Fin q → ℝ) (i : Fin m × (Fin r × Fin q)) :
    cavityGroupRawProjection v x i =
      ∑ k : Fin (N i.1), v i.1 i.2.1 k * cavityGaussianMatrix (x i.1) (N i.1) k i.2.2 := by
  classical
  change (∑ j : (a : Fin m) × (Fin (N a) × Fin q),
    cavityGroupProjectionMatrix v i j * x j.1 j.2.1 j.2.2) = _
  rw [Fintype.sum_sigma]
  simp only [cavityGroupProjectionMatrix, Fintype.sum_prod_type, ite_mul, zero_mul,
    ite_and]
  simp [cavityGaussianMatrix, div_mul_eq_mul_div, mul_div_assoc]

theorem cavityGroupRawProjection_hasLaw {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    HasLaw (cavityGroupRawProjection (q := q) v)
      (multivariateGaussian 0 (cavityGroupProjectionMatrix (q := q) v *
        (cavityGroupProjectionMatrix (q := q) v).transpose)) (cavityGroupGaussianRows m q) := by
  have hL : HasLaw (cavityGroupProjectionMatrix (q := q) v).toEuclideanLin.toContinuousLinearMap
      (multivariateGaussian 0 (cavityGroupProjectionMatrix (q := q) v *
        (cavityGroupProjectionMatrix (q := q) v).transpose))
      (stdGaussian (EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q)))) :=
    ⟨(by fun_prop), cavity_standardGaussian_image _⟩
  exact hL.fun_comp (cavityGroupGaussian_finite_standard_law N)

lemma cavityGroupGaussian_correction_measurable {m q : ℕ} (N : Fin m → ℕ) :
    Measurable (fun x : Fin m → ℕ → Fin q → ℝ =>
      fun a => (CFC.sqrt (cavityEmpiricalGram (x a) (N a)))⁻¹) := by
  apply Measurable.of_eval
  intro a
  exact (cavityGaussian_correction_measurable q (N a)).comp (measurable_pi_apply a)

lemma cavityGroupGaussian_correction_inMeasure {m q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop) :
    TendstoInMeasure (cavityGroupGaussianRows m q)
      (fun k x a => (CFC.sqrt (cavityEmpiricalGram (x a) (N k a)))⁻¹) atTop
      (fun _ _ => (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun k => (cavityGroupGaussian_correction_measurable (N k)).aestronglyMeasurable)
  have ha (a : Fin m) : ∀ᵐ x ∂cavityGroupGaussianRows m q,
      Tendsto (fun k => (CFC.sqrt (cavityEmpiricalGram (x a) (N k a)))⁻¹) atTop
        (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
    filter_upwards [(measurePreserving_eval (fun _ : Fin m => cavityGaussianRows q) a).quasiMeasurePreserving.ae
      (cavityGaussian_correction_tendsto q)] with x hx
    exact hx.comp (hN a)
  filter_upwards [ae_all_iff.mpr ha] with x hx
  exact tendsto_pi_nhds.mpr hx

lemma continuous_cavityGroupCorrectProjection (m r q : ℕ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) ×
      (Fin m → Matrix (Fin q) (Fin q) ℝ) => cavityGroupCorrectProjection p.1 p.2) := by
  unfold cavityGroupCorrectProjection
  fun_prop

lemma cavityGroupCorrectProjection_raw {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) (x : Fin m → ℕ → Fin q → ℝ) :
    cavityGroupCorrectProjection (cavityGroupRawProjection v x)
      (fun a => (CFC.sqrt (cavityEmpiricalGram (x a) (N a)))⁻¹) =
      cavityGroupFrameProjection v x := by
  ext i
  change (∑ j, cavityGroupRawProjection v x (i.1, i.2.1, j) *
      ((CFC.sqrt (cavityEmpiricalGram (x i.1) (N i.1)))⁻¹) j i.2.2) = _
  simp_rw [cavityGroupRawProjection_apply]
  change (∑ j, (∑ k, v i.1 i.2.1 k *
      cavityGaussianMatrix (x i.1) (N i.1) k j) * _) = _
  simpa only [cavityCorrectProjection, cavityRawProjection_apply, cavityGroupFrameProjection]
    using cavityCorrectProjection_raw_apply (v i.1) (x i.1) i.2

theorem cavityGroupRawProjection_tendstoInDistribution {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (S : Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)
    (hS : S.PosSemidef)
    (hcov : Tendsto (fun k => cavityGroupProjectionMatrix (q := q) (v k) *
      (cavityGroupProjectionMatrix (q := q) (v k)).transpose) atTop (𝓝 S)) :
    TendstoInDistribution (fun k => cavityGroupRawProjection (v k)) atTop id
      (fun _ => cavityGroupGaussianRows m q) (multivariateGaussian 0 S) := by
  refine ⟨fun k => (cavityGroupRawProjection_hasLaw (v k)).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  have hp (k : ℕ) : (cavityGroupProjectionMatrix (q := q) (v k) *
      (cavityGroupProjectionMatrix (q := q) (v k)).transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose (cavityGroupProjectionMatrix (q := q) (v k))
  have h := cavity_multivariateGaussian_weak_tendsto _ S hp hS hcov
  simp only [Measure.map_id]
  apply h.congr'
  filter_upwards [] with k
  apply Subtype.ext
  exact (cavityGroupRawProjection_hasLaw (v k)).map_eq.symm

/-- Joint normalization does not alter the multigroup Gaussian limit.
No independence between projections and their Gram corrections is needed. -/
theorem cavityGroupFrameProjection_tendstoInDistribution {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (S : Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ)
    (hS : S.PosSemidef)
    (hcov : Tendsto (fun k => cavityGroupProjectionMatrix (q := q) (v k) *
      (cavityGroupProjectionMatrix (q := q) (v k)).transpose) atTop (𝓝 S)) :
    TendstoInDistribution (fun k => cavityGroupFrameProjection (v k)) atTop id
      (fun _ => cavityGroupGaussianRows m q) (multivariateGaussian 0 S) := by
  have h := (cavityGroupRawProjection_tendstoInDistribution N v S hS hcov).continuous_comp_prodMk_of_tendstoInMeasure_const
      (continuous_cavityGroupCorrectProjection m r q)
      (cavityGroupGaussian_correction_inMeasure N hN)
      (fun k => (cavityGroupGaussian_correction_measurable (N k)).aemeasurable)
  simpa only [cavityGroupCorrectProjection_raw, cavityGroupCorrectProjection_one] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupCovariance
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance identification for the joint spectral-group projection.
Off-group and off-axis covariances vanish, while replica covariances are
the normalized Gram matrices in each eigenspace. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityGroupProjectionMatrix_covariance {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (i j : Fin m × (Fin r × Fin q)) :
    (cavityGroupProjectionMatrix (q := q) v * (cavityGroupProjectionMatrix (q := q) v).transpose) i j =
      if i.1 = j.1 ∧ i.2.2 = j.2.2 then
        (∑ k, v i.1 i.2.1 k * v i.1 j.2.1 k) / (N i.1 : ℝ) else 0 := by
  classical
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    have he : (cavityGroupProjectionMatrix (q := q) v * (cavityGroupProjectionMatrix (q := q) v).transpose)
        (a, i) (a, j) =
        (cavityProjectionMatrix (q := q) (v a) * (cavityProjectionMatrix (q := q) (v a)).transpose) i j := by
      simp only [Matrix.mul_apply, Fintype.sum_sigma, cavityGroupProjectionMatrix,
        Matrix.transpose_apply, ite_and]
      simp only [ite_mul_ite, mul_zero]
      simp [cavityProjectionMatrix]
    rw [he, cavityProjectionMatrix_covariance]
    simp
  · rw [Matrix.mul_apply, Fintype.sum_sigma]
    have hz (c : Fin m) (k : Fin (N c) × Fin q) :
        cavityGroupProjectionMatrix (q := q) v (a, i) ⟨c, k⟩ *
          (cavityGroupProjectionMatrix (q := q) v).transpose ⟨c, k⟩ (b, j) = 0 := by
      by_cases hac : a = c
      · have hbc : b ≠ c := fun h => hab (hac.trans h.symm)
        simp [cavityGroupProjectionMatrix, Matrix.transpose_apply, hbc]
      · simp [cavityGroupProjectionMatrix, hac]
    simp only [hz, Finset.sum_const_zero]
    simp [hab]

lemma cavityGroupProjection_covariance_tendsto {m r q : ℕ}
    (N : ℕ → Fin m → ℕ)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k a i j => (∑ l, v k a i l * v k a j l) / (N k a : ℝ))
      atTop (𝓝 Q)) :
    Tendsto (fun k => cavityGroupProjectionMatrix (q := q) (v k) *
      (cavityGroupProjectionMatrix (q := q) (v k)).transpose) atTop
      (𝓝 (cavityGroupReplicaCovariance q Q)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [cavityGroupProjectionMatrix_covariance, cavityGroupReplicaCovariance]
  by_cases hij : i.1 = j.1 ∧ i.2.2 = j.2.2
  · simp only [ite_eq_left hij]
    exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hQ i.1) i.2.1)) j.2.1
  · simp only [ite_eq_right hij]
    exact tendsto_const_nhds

/-- All spectral groups converge jointly to the Gaussian array prescribed
by their replica Gram limits, including singular limiting arrays. -/
theorem cavityGroupFrameProjection_tendsto_of_replicaGram {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k a i j => (∑ l, v k a i l * v k a j l) / (N k a : ℝ))
      atTop (𝓝 Q)) :
    TendstoInDistribution (fun k => cavityGroupFrameProjection (q := q) (v k)) atTop id
      (fun _ => cavityGroupGaussianRows m q)
      (multivariateGaussian 0 (cavityGroupReplicaCovariance q Q)) := by
  have hcov := cavityGroupProjection_covariance_tendsto (q := q) N v Q hQ
  have hS : (cavityGroupReplicaCovariance q Q).PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hcov (Eventually.of_forall (fun k => by
      simpa using Matrix.posSemidef_self_mul_conjTranspose
        (cavityGroupProjectionMatrix (q := q) (v k))))
  exact cavityGroupFrameProjection_tendstoInDistribution N hN v _ hS hcov

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArraySynchronization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron


lemma isClosed_setOf_posSemidef (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j = A j i} ∩ {A | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    constructor
    · intro h
      refine ⟨?_, fun v => by simpa using h.dotProduct_mulVec_nonneg v⟩
      intro i j
      have he := congrFun (congrFun h.1 i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he.symm
    · rintro ⟨hs, hq⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · ext i j; exact hs j i
      · intro v; simpa using hq v
  rw [he]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (by unfold dotProduct Matrix.mulVec; fun_prop)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGG
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multivariate monomial GG closure for the finite vector of spectral overlaps. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_spectralBlockView (m n : ℕ) : Continuous (spectralBlockView m n) := by
  unfold spectralBlockView
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma ae_closed_of_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {L : ℕ → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hL : Tendsto L atTop (𝓝 μ)) {S : Set X} (hS : IsClosed S)
    (hA : ∀ k, ∀ᵐ x ∂(L k : Measure X), x ∈ S) : ∀ᵐ x ∂(μ : Measure X), x ∈ S := by
  have he : ∀ k, (L k : Measure X) S = 1 := fun k => by
    simpa using (ae_iff_measure_eq (μ := (L k : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mp (hA k)
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hL hS
  simp only [he,limsup_const] at hh
  apply (ae_iff_measure_eq (μ := (μ : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mpr
  rw [measure_univ]
  exact le_antisymm prob_le_one hh

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram structure and replica symmetry for spectral arrays retaining common disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma isClosed_spectralGram (m : ℕ) : IsClosed {x : SpectralArray m | SpectralGram x} := by
  unfold SpectralGram
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun n =>
    (isClosed_setOf_posSemidef n).preimage (by unfold spectralCoordinateArray; fun_prop)

lemma spectralArray_limit_gram {m : ℕ} {L : ℕ → ProbabilityMeasure (SpectralArray m)}
    {Q : ProbabilityMeasure (SpectralArray m)} (hL : Tendsto L atTop (𝓝 Q))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure (SpectralArray m)), SpectralGram x) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x :=
  ae_closed_of_weak_limit hL (isClosed_spectralGram m) hG

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralGaussianTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian marking limit keeps every overlap label in the finite
spectral block, rather than retaining only an averaged covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_spectral_gaussian_test_tendsto {m r : ℕ}
    {a : Type*} [Fintype a] [DecidableEq a]
    (P : ℕ → ProbabilityMeasure (SpectralArray m))
    (P₀ : ProbabilityMeasure (SpectralArray m)) (hP : Tendsto P atTop (𝓝 P₀))
    (C : SpectralBlock m r → Matrix a a ℝ) (hC : Continuous C)
    (hS : ∀ n, ∀ᵐ x ∂(P n : Measure (SpectralArray m)),
      (C (spectralBlockView m r x)).PosSemidef)
    (hS₀ : ∀ᵐ x ∂(P₀ : Measure (SpectralArray m)),
      (C (spectralBlockView m r x)).PosSemidef)
    (F : SpectralBlock m r × EuclideanSpace ℝ a →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, ∫ z, F (spectralBlockView m r x, z)
        ∂multivariateGaussian 0 (C (spectralBlockView m r x))
        ∂(P n : Measure (SpectralArray m))) atTop
      (𝓝 (∫ x, ∫ z, F (spectralBlockView m r x, z)
        ∂multivariateGaussian 0 (C (spectralBlockView m r x))
        ∂(P₀ : Measure (SpectralArray m)))) := by
  obtain ⟨G, hG⟩ := cavity_gaussian_joint_test_extension F
  let b := spectralBlockView m r
  have hb : Continuous b := continuous_spectralBlockView m r
  let f : SpectralArray m →ᵇ ℝ :=
    G.compContinuous ⟨fun x => (b x, C (b x)), hb.prodMk (hC.comp hb)⟩
  have he (Q : ProbabilityMeasure (SpectralArray m))
      (hQ : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), (C (b x)).PosSemidef) :
      (∫ x, ∫ z, F (b x, z) ∂multivariateGaussian 0 (C (b x))
        ∂(Q : Measure (SpectralArray m))) = ∫ x, f x ∂(Q : Measure (SpectralArray m)) := by
    apply integral_congr_ae
    filter_upwards [hQ] with x hx
    exact (hG (b x) (C (b x)) hx).symm
  change Tendsto (fun n => ∫ x, ∫ z, F (b x, z) ∂multivariateGaussian 0 (C (b x))
      ∂(P n : Measure (SpectralArray m))) _
    (𝓝 (∫ x, ∫ z, F (b x, z) ∂multivariateGaussian 0 (C (b x))
      ∂(P₀ : Measure (SpectralArray m))))
  simp_rw [he _ hS₀, he _ (hS _)]
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP f

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupCovariancePositive
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the actual block covariance for all spectral groups
and all fresh axes. No invertibility is needed. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix

namespace InvariantIsing

lemma continuous_cavityGroupReplicaCovariance {m r : ℕ} (q : ℕ) :
    Continuous (cavityGroupReplicaCovariance (m := m) (r := r) q) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i.1 = j.1 ∧ i.2.2 = j.2.2
  · simpa only [cavityGroupReplicaCovariance, ite_eq_left h] using
      (show Continuous (fun Q : Fin m → Matrix (Fin r) (Fin r) ℝ => Q i.1 i.2.1 j.2.1) from by fun_prop)
  · simp only [cavityGroupReplicaCovariance, ite_eq_right h]
    exact continuous_const

lemma cavityGroupReplicaCovariance_posSemidef {m r q : ℕ}
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ) (hQ : ∀ a, (Q a).PosSemidef) :
    (cavityGroupReplicaCovariance q Q).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    rintro ⟨a, i, t⟩ ⟨b, j, s⟩
    by_cases hab : a = b
    · subst b
      by_cases hts : t = s
      · subst s
        simpa only [cavityGroupReplicaCovariance, and_self, ite_true, if_true, star_trivial] using
          (hQ a).isHermitian.apply i j
      · simp [cavityGroupReplicaCovariance, hts, Ne.symm hts]
    · simp [cavityGroupReplicaCovariance, hab, Ne.symm hab]
  · intro v
    have hm (a : Fin m) (i : Fin r) (t : Fin q) :
        (cavityGroupReplicaCovariance q Q *ᵥ v) (a, i, t) =
          ∑ j, Q a i j * v (a, j, t) := by
      simp [Matrix.mulVec, dotProduct, cavityGroupReplicaCovariance,
        Fintype.sum_prod_type, ite_and, ite_mul]
    have he : star v ⬝ᵥ (cavityGroupReplicaCovariance q Q *ᵥ v) =
        ∑ a : Fin m, ∑ t : Fin q,
          star (fun i : Fin r => v (a, i, t)) ⬝ᵥ (Q a *ᵥ fun i => v (a, i, t)) := by
      simp only [dotProduct, Pi.star_apply, star_trivial, Fintype.sum_prod_type]
      simp_rw [hm]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    rw [he]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun t _ =>
      (hQ a).dotProduct_mulVec_nonneg (fun i => v (a, i, t))

lemma continuous_cavitySpectralBlockCovariance {m r : ℕ} (q : ℕ) (ρ : Fin m → ℝ) :
    Continuous (cavitySpectralBlockCovariance (r := r) q ρ) := by
  apply (continuous_cavityGroupReplicaCovariance q).comp
  fun_prop

lemma cavitySpectralBlockCovariance_posSemidef {m r q : ℕ}
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (x : SpectralArray (m + 1)) (hx : SpectralGram x) :
    (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x)).PosSemidef := by
  apply cavityGroupReplicaCovariance_posSemidef
  intro a
  have hh := (hx a.castSucc r).smul (inv_nonneg.mpr (hρ a))
  have he : (fun i j : Fin r => (spectralBlockView (m + 1) r x i j a.castSucc : ℝ) / ρ a) =
      (ρ a)⁻¹ • (fun i j : Fin r => spectralCoordinateArray a.castSucc x i j) := by
    ext i j
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm,
      spectralBlockView, spectralCoordinateArray]
  rw [he]
  exact hh

theorem cavity_spectral_frame_gaussian_test_tendsto {m r q : ℕ}
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (P : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (P₀ : ProbabilityMeasure (SpectralArray (m + 1))) (hP : Filter.Tendsto P Filter.atTop (𝓝 P₀))
    (hG : ∀ n, ∀ᵐ x ∂(P n : Measure (SpectralArray (m + 1))), SpectralGram x)
    (hG₀ : ∀ᵐ x ∂(P₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Filter.Tendsto (fun n => ∫ x, ∫ z, F (spectralBlockView (m + 1) r x, z)
      ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
      ∂(P n : Measure (SpectralArray (m + 1)))) Filter.atTop
      (𝓝 (∫ x, ∫ z, F (spectralBlockView (m + 1) r x, z)
      ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
      ∂(P₀ : Measure (SpectralArray (m + 1))))) :=
  cavity_spectral_gaussian_test_tendsto P P₀ hP _ (continuous_cavitySpectralBlockCovariance q ρ)
    (fun n => (hG n).mono fun x hx => cavitySpectralBlockCovariance_posSemidef ρ hρ x hx)
    (hG₀.mono fun x hx => cavitySpectralBlockCovariance_posSemidef ρ hρ x hx) F

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarCompression
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar cavity compressions converge to their spectral proportions.
The proof transfers the almost sure Gaussian Gram limit through the
exact conditioned frame law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
  BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityGaussianNormalizedFrame (q N : ℕ) :
    Measurable (fun x : ℕ → Fin q → ℝ =>
      cavityNormalizeFrame (cavityGaussianMatrix x N)) := by
  apply (measurable_cavityNormalizeFrame N q).comp
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_pi_apply j).comp (measurable_pi_apply (i : ℕ))).div_const _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupHaarProjection
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint Gaussian projection limit for independent Haar frames in
all spectral groups. The exact finite-dimensional law is obtained before
taking limits; no conditional independence is assumed as an extra input. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavityGoodGram_cond_eq (n q : ℕ) (hqn : q ≤ n) :
    cond (cavityGaussianRows q) (cavityGoodGram q n) = cavityGaussianRows q := by
  have hae : ∀ᵐ x ∂cavityGaussianRows q, x ∈ cavityGoodGram q n :=
    (cavityGaussianRows_gram_posDef n q hqn).mono (fun _ hx => hx.det_pos)
  rw [ProbabilityTheory.cond, cavityGoodGram_probability_one n q hqn,
    inv_one, one_smul, Measure.restrict_eq_self_of_ae_mem hae]

lemma cavityGaussianNormalizedFrame_eq_haar {n q : ℕ} (hqn : q ≤ n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1) :
    (cavityGaussianRows q).map (fun x => cavityNormalizeFrame (cavityGaussianMatrix x n)) =
      μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) := by
  have hp : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0 := by
    rw [cavityArrayGood_probability, cavityGoodGram_probability_one n q hqn]
    exact one_ne_zero
  let := cavityConditionedFrameLaw_probability hp
  rw [← cavityGoodGram_cond_eq n q hqn, cavityConditionedFrameLaw_of_rows]
  exact cavityFrame_eq_haar_orbit μ (cavityConditionedFrameLaw n q)
    cavityConditionedFrameLaw_rotation (cavityConditionedFrameLaw_orthonormal n q) A₀ hA₀

lemma measurable_cavityGroupNormalizedFrames {m q : ℕ} (N : Fin m → ℕ) :
    Measurable (cavityGroupNormalizedFrames (q := q) N) := by
  exact Measurable.of_eval (fun a => (measurable_cavityGaussianNormalizedFrame q (N a)).comp
    (measurable_pi_apply a))

theorem cavityGroupNormalizedFrames_eq_haar {m q : ℕ} (N : Fin m → ℕ)
    (hN : ∀ a, q ≤ N a) (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) :
    (cavityGroupGaussianRows m q).map (cavityGroupNormalizedFrames N) =
      (Measure.pi μ).map (cavityGroupHaarFrames A₀) := by
  unfold cavityGroupGaussianRows cavityGroupNormalizedFrames cavityGroupHaarFrames
  rw [Measure.pi_map_pi (fun a => (measurable_cavityGaussianNormalizedFrame q (N a)).aemeasurable),
    Measure.pi_map_pi (μ := μ)
      (f := fun a (U : Orthogonal (N a)) => (U : Matrix (Fin (N a)) (Fin (N a)) ℝ) * A₀ a)
      (fun a => ((continuous_cavityFrameAction (N a) q).comp
        (continuous_id.prodMk continuous_const)).measurable.aemeasurable)]
  congr 1
  funext a
  exact cavityGaussianNormalizedFrame_eq_haar (hN a) (μ a) (A₀ a) (hA₀ a)

lemma continuous_cavityGroupMatrixProjection {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    Continuous (cavityGroupMatrixProjection (q := q) v) := by
  unfold cavityGroupMatrixProjection
  fun_prop

lemma cavityGroupFrame_integral_eq_haar {m r q : ℕ} (N : Fin m → ℕ)
    (hN : ∀ a, q ≤ N a) (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1)
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (F : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    (∫ x, F (cavityGroupFrameProjection v x) ∂cavityGroupGaussianRows m q) =
      ∫ U, F (cavityGroupMatrixProjection v (cavityGroupHaarFrames A₀ U)) ∂Measure.pi μ := by
  let : OpensMeasurableSpace ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace ((a : Fin m) → Fin (N a) → Fin q → ℝ))
  let f := fun A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ =>
    F (cavityGroupMatrixProjection v A)
  have hf : Continuous f := F.continuous.comp (continuous_cavityGroupMatrixProjection v)
  have he := congrArg (fun ν => ∫ A, f A ∂ν)
    (cavityGroupNormalizedFrames_eq_haar N hN μ A₀ hA₀)
  rw [integral_map (measurable_cavityGroupNormalizedFrames N).aemeasurable hf.aestronglyMeasurable,
    integral_map (measurable_cavityGroupHaarFrames A₀).aemeasurable
      hf.aestronglyMeasurable] at he
  exact he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityGroupProjectionUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformity over all bounded spectral-group replica Gram arrays. This
allows the fresh frames to be averaged against the base Gibbs measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

lemma cavityGroupReplicaGram_covariance {m r q : ℕ} {N : Fin m → ℕ}
    (v : (a : Fin m) → Fin r → Fin (N a) → ℝ) :
    cavityGroupReplicaCovariance q (cavityGroupReplicaGram v) =
      cavityGroupProjectionMatrix (q := q) v * (cavityGroupProjectionMatrix (q := q) v).transpose := by
  ext i j
  exact (cavityGroupProjectionMatrix_covariance v i j).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarJointTest
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint fresh-frame Gaussian limit with converging finite overlap
labels. The same Gaussian marks are retained across all replicas. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavityGroupHaarFrame_labeled_integral_tendsto {m r q : ℕ}
    {L : Type*} [NormedAddCommGroup L] [MeasurableSpace L]
    [BorelSpace L] [SecondCountableTopology L]
    (l : ℕ → L) (l₀ : L) (hl : Tendsto l atTop (𝓝 l₀))
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (v : (k : ℕ) → (a : Fin m) → Fin r → Fin (N k a) → ℝ)
    (Q : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hQ : Tendsto (fun k a i j => (∑ t, v k a i t * v k a j t) / (N k a : ℝ))
      atTop (𝓝 Q))
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (l k, cavityGroupMatrixProjection (v k)
      (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)) atTop
      (𝓝 (∫ y, F (l₀, y) ∂multivariateGaussian 0 (cavityGroupReplicaCovariance q Q))) := by
  have hd := cavityGroupFrameProjection_tendsto_of_replicaGram (q := q) N hN v Q hQ
  have ht : TendstoInMeasure (cavityGroupGaussianRows m q) (fun k _ => l k) atTop (fun _ => l₀) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ => hl)
  have hp := hd.prodMk_of_tendstoInMeasure_const _ _ _ ht (fun _ => aemeasurable_const)
  let G : (EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) × L →ᵇ ℝ :=
    F.compContinuous ⟨Prod.swap, continuous_swap⟩
  have hu := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hp.forall_aemeasurable hp.aemeasurable_limit).mp hp G
  apply (show Tendsto (fun k => ∫ x, F (l k, cavityGroupFrameProjection (v k) x)
    ∂cavityGroupGaussianRows m q) atTop _ from hu).congr'
  have hn : ∀ᶠ k in atTop, ∀ a, q ≤ N k a := by
    apply eventually_all.mpr
    intro a
    exact (hN a).eventually (eventually_ge_atTop q)
  filter_upwards [hn] with k hk
  exact cavityGroupFrame_integral_eq_haar (N k) hk (μ k) (A₀ k) (hA₀ k) (v k)
    (F.compContinuous ⟨fun z => (l k, z), continuous_const.prodMk continuous_id⟩)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarJointUniform
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeNonempty
attribute [-simp] _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fresh-frame Gaussian approximation uniformly over compact finite
labels and bounded replica Gram matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityGroupHaarFrame_labeled_uniform {m r q : ℕ}
    {L : Type*} [NormedAddCommGroup L] [MeasurableSpace L]
    [BorelSpace L] [SecondCountableTopology L]
    (K : Set L) (hK : IsCompact K)
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) (C : ℝ) :
    ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ (v : (a : Fin m) → Fin r → Fin (N k a) → ℝ) (l : L), l ∈ K →
      (∀ a i j, |cavityGroupReplicaGram v a i j| ≤ C) →
      |(∫ U, F (l, cavityGroupMatrixProjection v (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k)) -
        ∫ y, F (l, y) ∂multivariateGaussian 0
          (cavityGroupReplicaCovariance q (cavityGroupReplicaGram v))| < ε := by
  classical
  let : FirstCountableTopology (Fin m → Matrix (Fin r) (Fin r) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin m → Fin r → Fin r → ℝ))
  intro ε hε
  by_contra hbad
  have hf : ∃ᶠ k in atTop, ∃ (v : (a : Fin m) → Fin r → Fin (N k a) → ℝ) (l : L),
      l ∈ K ∧ (∀ a i j, |cavityGroupReplicaGram v a i j| ≤ C) ∧
      ε ≤ |(∫ U, F (l, cavityGroupMatrixProjection v (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k)) -
        ∫ y, F (l, y) ∂multivariateGaussian 0
          (cavityGroupReplicaCovariance q (cavityGroupReplicaGram v))| := by
    simpa only [Filter.not_eventually, not_forall, _root_.not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hf
  choose v l hl hv he using hφbad
  let Qs : ℕ → Fin m → Matrix (Fin r) (Fin r) ℝ := fun k => cavityGroupReplicaGram (v k)
  have hmem k : (l k, Qs k) ∈ K ×ˢ Set.pi Set.univ
      (fun _ : Fin m => (Icc (-C) C).matrix) := by
    refine ⟨hl k, fun a _ i j => ?_⟩
    exact abs_le.mp (hv k a i j)
  obtain ⟨p, _, ψ, hψ, hlim⟩ :=
    (hK.prod (isCompact_univ_pi (fun _ : Fin m => isCompact_Icc.matrix))).tendsto_subseq hmem
  let τ := φ ∘ ψ
  have hτ : StrictMono τ := hφ.comp hψ
  have hsubN : ∀ a, Tendsto (fun k => N (τ k) a) atTop atTop :=
    fun a => (hN a).comp hτ.tendsto_atTop
  have hlabel : Tendsto (fun k => l (ψ k)) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hlim
  have hgram : Tendsto (fun k => Qs (ψ k)) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hlim
  have hHaar := cavityGroupHaarFrame_labeled_integral_tendsto (fun k => l (ψ k)) p.1 hlabel
    (fun k => N (τ k)) hsubN (fun k => v (ψ k)) p.2 hgram
    (fun k => μ (τ k)) (fun k => A₀ (τ k)) (fun k => hA₀ (τ k)) F
  have hcov := cavityGroupProjection_covariance_tendsto (q := q)
    (fun k => N (τ k)) (fun k => v (ψ k)) p.2 hgram
  have hp (k : ℕ) : (cavityGroupProjectionMatrix (q := q) (v (ψ k)) *
      (cavityGroupProjectionMatrix (q := q) (v (ψ k))).transpose).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose (cavityGroupProjectionMatrix (q := q) (v (ψ k)))
  have hQ : (cavityGroupReplicaCovariance q p.2).PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hcov (Eventually.of_forall hp)
  have hGaussian := cavity_gaussian_joint_test_tendsto (fun k => l (ψ k)) p.1 hlabel
    (fun k => cavityGroupProjectionMatrix (q := q) (v (ψ k)) *
      (cavityGroupProjectionMatrix (q := q) (v (ψ k))).transpose)
    (cavityGroupReplicaCovariance q p.2) hp hQ hcov F
  simp_rw [← cavityGroupReplicaGram_covariance] at hGaussian
  have hz := (hHaar.sub hGaussian).abs
  simp only [sub_self, abs_zero] at hz
  have hsmall := hz.eventually (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_le_of_gt hk) (he (ψ k))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityHaarSpectralLabels
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Keep the complete finite spectral overlap block in the Haar
approximation, using its canonical compact embedding into real coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma continuous_spectralBlockReal {m r : ℕ} :
    Continuous (spectralBlockReal (m := m) (r := r)) := by
  unfold spectralBlockReal
  fun_prop

lemma continuous_spectralBlockClamp {m r : ℕ} :
    Continuous (spectralBlockClamp (m := m) (r := r)) := by
  unfold spectralBlockClamp
  fun_prop

theorem cavityGroupHaarFrame_spectral_uniform {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ)
    (C : ℝ) :
    ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ (v : (a : Fin m) → Fin r → Fin (N k a) → ℝ) (x : SpectralBlock (m + 1) r),
      (∀ a i j, |cavityGroupReplicaGram v a i j| ≤ C) →
      |(∫ U, F (x, cavityGroupMatrixProjection v (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k)) -
        ∫ y, F (x, y) ∂multivariateGaussian 0
          (cavityGroupReplicaCovariance q (cavityGroupReplicaGram v))| < ε := by
  let G : (Fin r → Fin r → Fin (m + 1) → ℝ) ×
      EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ :=
    F.compContinuous ⟨fun p => (spectralBlockClamp p.1, p.2),
      (continuous_spectralBlockClamp.comp continuous_fst).prodMk continuous_snd⟩
  have hK : IsCompact (Set.range (spectralBlockReal (m := m + 1) (r := r))) :=
    isCompact_range continuous_spectralBlockReal
  intro ε hε
  have hu := cavityGroupHaarFrame_labeled_uniform _ hK N hN μ A₀ hA₀ G C ε hε
  filter_upwards [hu] with k hk
  intro v x hv
  simpa only [G, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    spectralBlockClamp_real] using hk v (spectralBlockReal x) (Set.mem_range_self x) hv

lemma measurable_cavityGroupHaarFrame_spectral_mean {m r q : ℕ}
    {X : Type*} [MeasurableSpace X] (N : Fin m → ℕ)
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (l : X → SpectralBlock (m + 1) r) (hl : Measurable l)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ) (hv : Measurable v)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Measurable (fun x => ∫ U, F (l x, cavityGroupMatrixProjection (v x)
      (cavityGroupHaarFrames A₀ U)) ∂Measure.pi μ) := by
  let : OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)) :=
    inferInstanceAs (OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Fin (N a) → Fin q → ℝ)))
  have hcont : Continuous (fun p :
      ((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) =>
      cavityGroupMatrixProjection p.1 p.2) := by
    unfold cavityGroupMatrixProjection
    fun_prop
  have hm := F.continuous.measurable.comp
    ((hl.comp measurable_fst).prodMk (hcont.measurable.comp
      ((hv.comp measurable_fst).prodMk ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavityMovingGroupMass
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.spectralBlockClamp_real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from finite spectral-group proportions to their positive
limits in the joint Gaussian marking of the overlap array. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavitySpectralBlockCovariance_tendsto {m r q : ℕ}
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρ0 : ∀ a, ρ a ≠ 0)
    (x : ℕ → SpectralBlock (m + 1) r) (x₀ : SpectralBlock (m + 1) r)
    (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun k => cavitySpectralBlockCovariance q (ρs k) (x k)) atTop
      (𝓝 (cavitySpectralBlockCovariance q ρ x₀)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hij : i.1 = j.1 ∧ i.2.2 = j.2.2
  · simp only [cavitySpectralBlockCovariance, cavityGroupReplicaCovariance, ite_eq_left hij]
    have hentry : Tendsto (fun k => (x k i.2.1 j.2.1 i.1.castSucc : ℝ)) atTop
        (𝓝 (x₀ i.2.1 j.2.1 i.1.castSucc : ℝ)) :=
      (by fun_prop : Continuous (fun y : SpectralBlock (m + 1) r =>
        (y i.2.1 j.2.1 i.1.castSucc : ℝ))).continuousAt.tendsto.comp hx
    exact hentry.div (tendsto_pi_nhds.mp hρ i.1) (hρ0 i.1)
  · simp only [cavitySpectralBlockCovariance, cavityGroupReplicaCovariance, ite_eq_right hij]
    exact tendsto_const_nhds

theorem cavity_spectral_gaussian_mass_uniform {m r q : ℕ}
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k a, 0 < ρs k a) (hρ0 : ∀ a, 0 < ρ a)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ x : SpectralArray (m + 1), SpectralGram x →
      |(∫ y, F (spectralBlockView (m + 1) r x, y) ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r x))) -
        ∫ y, F (spectralBlockView (m + 1) r x, y) ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))| < ε := by
  classical
  intro ε hε
  by_contra hbad
  have hf : ∃ᶠ k in atTop, ∃ x : SpectralArray (m + 1), SpectralGram x ∧
      ε ≤ |(∫ y, F (spectralBlockView (m + 1) r x, y) ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r x))) -
        ∫ y, F (spectralBlockView (m + 1) r x, y) ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))| := by
    simpa only [Filter.not_eventually, not_forall, _root_.not_imp, not_lt, exists_prop] using hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hf
  choose x hx he using hφbad
  obtain ⟨x₀, _, ψ, hψ, hlim⟩ :=
    (isCompact_univ : IsCompact (univ : Set (SpectralArray (m + 1)))).tendsto_subseq
      (fun k => mem_univ (x k))
  have hb := (continuous_spectralBlockView (m + 1) r).continuousAt.tendsto.comp hlim
  have hr : Tendsto (fun k => ρs (φ (ψ k))) atTop (𝓝 ρ) :=
    hρ.comp (hφ.comp hψ).tendsto_atTop
  let S₀ := cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x₀)
  have hS := cavitySpectralBlockCovariance_tendsto (q := q) _ ρ hr
    (fun a => ne_of_gt (hρ0 a)) _ _ hb
  have hT := cavitySpectralBlockCovariance_tendsto (q := q) (fun _ => ρ) ρ
    tendsto_const_nhds (fun a => ne_of_gt (hρ0 a)) _ _ hb
  have hs k : (cavitySpectralBlockCovariance q (ρs (φ (ψ k)))
      (spectralBlockView (m + 1) r (x (ψ k)))).PosSemidef :=
    cavitySpectralBlockCovariance_posSemidef _ (fun a => (hρs _ a).le) _ (hx _)
  have ht k : (cavitySpectralBlockCovariance q ρ
      (spectralBlockView (m + 1) r (x (ψ k)))).PosSemidef :=
    cavitySpectralBlockCovariance_posSemidef _ (fun a => (hρ0 a).le) _ (hx _)
  have hs₀ : S₀.PosSemidef :=
    Matrix.posSemidef_is_closed.mem_of_tendsto hT (Eventually.of_forall ht)
  have hleft := cavity_gaussian_joint_test_tendsto _ _ hb _ S₀ hs hs₀ hS F
  have hright := cavity_gaussian_joint_test_tendsto _ _ hb _ S₀ ht hs₀ hT F
  have hz := (hleft.sub hright).abs
  simp only [sub_self, abs_zero] at hz
  obtain ⟨k, hk⟩ := (hz.eventually (Iio_mem_nhds hε)).exists
  exact (not_le_of_gt hk) (he (ψ k))

theorem cavity_spectral_moving_mass_test_tendsto {m r q : ℕ}
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k a, 0 < ρs k a) (hρ0 : ∀ a, 0 < ρ a)
    (P : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (P₀ : ProbabilityMeasure (SpectralArray (m + 1))) (hP : Tendsto P atTop (𝓝 P₀))
    (hG : ∀ k, ∀ᵐ x ∂(P k : Measure (SpectralArray (m + 1))), SpectralGram x)
    (hG₀ : ∀ᵐ x ∂(P₀ : Measure (SpectralArray (m + 1))), SpectralGram x)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, ∫ y, F (spectralBlockView (m + 1) r x, y)
      ∂multivariateGaussian 0
        (cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r x))
      ∂(P k : Measure (SpectralArray (m + 1)))) atTop
      (𝓝 (∫ x, ∫ y, F (spectralBlockView (m + 1) r x, y)
        ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
        ∂(P₀ : Measure (SpectralArray (m + 1))))) := by
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let b := spectralBlockView (m + 1) r
  let f (ρ' : Fin m → ℝ) : SpectralArray (m + 1) →ᵇ ℝ :=
    G.compContinuous ⟨fun x => (b x, cavitySpectralBlockCovariance q ρ' (b x)),
      (continuous_spectralBlockView _ _).prodMk
        ((continuous_cavitySpectralBlockCovariance q ρ').comp (continuous_spectralBlockView _ _))⟩
  have he (ρ' : Fin m → ℝ) (hρ' : ∀ a, 0 ≤ ρ' a) (x : SpectralArray (m + 1))
      (hx : SpectralGram x) :
      f ρ' x = ∫ y, F (b x, y) ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ' (b x)) :=
    hExt _ _ (cavitySpectralBlockCovariance_posSemidef ρ' hρ' x hx)
  have herror : Tendsto (fun k => ∫ x, (f (ρs k) x - f ρ x)
      ∂(P k : Measure (SpectralArray (m + 1)))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hu := cavity_spectral_gaussian_mass_uniform ρs ρ hρ hρs hρ0 F (ε / 2) (half_pos hε)
    filter_upwards [hu] with k hk
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
    have hb := norm_integral_le_of_norm_le_const
      (μ := (P k : Measure (SpectralArray (m + 1)))) (f := fun x => f (ρs k) x - f ρ x)
      (C := ε / 2) ((hG k).mono fun x hx => by
        rw [Real.norm_eq_abs, he _ (fun a => (hρs k a).le) x hx,
          he _ (fun a => (hρ0 a).le) x hx]
        exact (hk x hx).le)
    exact lt_of_le_of_lt (by simpa only [probReal_univ, mul_one] using hb) (half_lt_self hε)
  have hi (k : ℕ) (ρ' : Fin m → ℝ) (hρ' : ∀ a, 0 ≤ ρ' a) :
      (∫ x, f ρ' x ∂(P k : Measure (SpectralArray (m + 1)))) =
        ∫ x, ∫ y, F (b x, y)
          ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ' (b x))
          ∂(P k : Measure (SpectralArray (m + 1))) :=
    integral_congr_ae ((hG k).mono fun x hx => he ρ' hρ' x hx)
  have hdiff : Tendsto (fun k =>
      (∫ x, ∫ y, F (b x, y)
        ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q (ρs k) (b x))
        ∂(P k : Measure (SpectralArray (m + 1)))) -
      ∫ x, ∫ y, F (b x, y)
        ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q ρ (b x))
        ∂(P k : Measure (SpectralArray (m + 1)))) atTop (𝓝 0) := by
    convert herror using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    rw [integral_sub ((f (ρs k)).integrable _) ((f ρ).integrable _),
      hi k (ρs k) (fun a => (hρs k a).le), hi k ρ (fun a => (hρ0 a).le)]
  have hconst := cavity_spectral_frame_gaussian_test_tendsto ρ (fun a => (hρ0 a).le)
    P P₀ hP hG hG₀ F
  convert hdiff.add hconst using 1 <;> first | (with_reducible_and_instances rfl) | (simp [b])

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Cavity_CavitySpectralHaarLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.spectralLinearLaw_probability _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.planeRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fresh-Haar finite-replica limit under the base Gibbs law. The
only limiting datum is its spectral overlap-array law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_spectral_haar_test_tendsto_oai {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (X : ℕ → Type*) [∀ k, MeasurableSpace (X k)]
    (P : (k : ℕ) → Measure (X k)) [∀ k, IsProbabilityMeasure (P k)]
    (a : (k : ℕ) → X k → SpectralArray (m + 1)) (ha : ∀ k, Measurable (a k))
    (hGram : ∀ k x, SpectralGram (a k x))
    (v : (k : ℕ) → X k → (j : Fin m) → Fin r → Fin (N k j) → ℝ)
    (hvM : ∀ k, Measurable (v k)) (C : ℝ)
    (hv : ∀ k x j i l, |cavityGroupReplicaGram (v k x) j i l| ≤ C)
    (ρs : ℕ → Fin m → ℝ) (ρ : Fin m → ℝ)
    (hρ : Tendsto ρs atTop (𝓝 ρ)) (hρs : ∀ k j, 0 < ρs k j) (hρ0 : ∀ j, 0 < ρ j)
    (hcov : ∀ k x, cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x)) =
      cavitySpectralBlockCovariance q (ρs k) (spectralBlockView (m + 1) r (a k x)))
    (Q : ℕ → ProbabilityMeasure (SpectralArray (m + 1)))
    (Q₀ : ProbabilityMeasure (SpectralArray (m + 1)))
    (hQ : ∀ k, (Q k : Measure (SpectralArray (m + 1))) = (P k).map (a k))
    (hlim : Tendsto Q atTop (𝓝 Q₀))
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, ∫ U,
      F (spectralBlockView (m + 1) r (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U))
      ∂Measure.pi (μ k) ∂P k) atTop
      (𝓝 (∫ x, ∫ y, F (spectralBlockView (m + 1) r x, y)
        ∂multivariateGaussian 0
          (cavitySpectralBlockCovariance q ρ (spectralBlockView (m + 1) r x))
        ∂(Q₀ : Measure (SpectralArray (m + 1))))) := by
  have hQG k : ∀ᵐ x ∂(Q k : Measure (SpectralArray (m + 1))), SpectralGram x := by
    rw [hQ k, ae_map_iff (ha k).aemeasurable (isClosed_spectralGram _).measurableSet]
    exact ae_of_all _ (hGram k)
  have hQG₀ := spectralArray_limit_gram hlim hQG
  have hGaussian := cavity_spectral_moving_mass_test_tendsto ρs ρ hρ hρs hρ0
    Q Q₀ hlim hQG hQG₀ F
  obtain ⟨G, hExt⟩ := cavity_gaussian_joint_test_extension F
  let b := spectralBlockView (m + 1) r
  let g k : SpectralArray (m + 1) →ᵇ ℝ :=
    G.compContinuous ⟨fun x => (b x, cavitySpectralBlockCovariance q (ρs k) (b x)),
      (continuous_spectralBlockView _ _).prodMk
        ((continuous_cavitySpectralBlockCovariance q (ρs k)).comp (continuous_spectralBlockView _ _))⟩
  let H k x := ∫ U, F (b (a k x),
      cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U)) ∂Measure.pi (μ k)
  have hHM k : Measurable (H k) :=
    measurable_cavityGroupHaarFrame_spectral_mean (N k) (μ k) (A₀ k) _
      ((continuous_spectralBlockView _ _).measurable.comp (ha k)) (v k) (hvM k) F
  have hHI k : Integrable (H k) (P k) := by
    apply integrable_of_measurable_abs_le (hHM k) (c := ‖F‖)
    intro x
    rw [← Real.norm_eq_abs]
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := Measure.pi (μ k)) (C := ‖F‖) (f := fun U => F (b (a k x),
        cavityGroupMatrixProjection (v k x) (cavityGroupHaarFrames (A₀ k) U)))
      (ae_of_all _ fun U => F.norm_coe_le_norm _)
  have hgI k : Integrable (fun x => g k (a k x)) (P k) :=
    integrable_of_measurable_abs_le ((g k).continuous.measurable.comp (ha k))
      (fun x => by simpa only [← Real.norm_eq_abs] using (g k).norm_coe_le_norm (a k x))
  have hgEq k x : g k (a k x) = ∫ y, F (b (a k x), y)
      ∂multivariateGaussian 0 (cavityGroupReplicaCovariance q (cavityGroupReplicaGram (v k x))) := by
    rw [hcov k x]
    exact hExt _ _ (cavitySpectralBlockCovariance_posSemidef _
      (fun j => (hρs k j).le) _ (hGram k x))
  have hgMap k : (∫ x, g k (a k x) ∂P k) =
      ∫ x, ∫ y, F (b x, y) ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q (ρs k) (b x))
        ∂(Q k : Measure (SpectralArray (m + 1))) := by
    rw [← integral_map (ha k).aemeasurable (g k).continuous.aestronglyMeasurable, ← hQ k]
    exact integral_congr_ae ((hQG k).mono fun x hx => hExt _ _
      (cavitySpectralBlockCovariance_posSemidef _ (fun j => (hρs k j).le) _ hx))
  have herror : Tendsto (fun k => ∫ x, (H k x - g k (a k x)) ∂P k) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hu := cavityGroupHaarFrame_spectral_uniform N hN μ A₀ hA₀ F C (ε / 2) (half_pos hε)
    filter_upwards [hu] with k hk
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
    have hb := norm_integral_le_of_norm_le_const (μ := P k) (C := ε / 2)
      (f := fun x => H k x - g k (a k x)) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, hgEq k x]
        exact (hk (v k x) (b (a k x)) (hv k x)).le)
    exact lt_of_le_of_lt (by simpa only [probReal_univ, mul_one] using hb) (half_lt_self hε)
  have he k : (∫ x, (H k x - g k (a k x)) ∂P k) =
      (∫ x, H k x ∂P k) - ∫ x, ∫ y, F (b x, y)
        ∂multivariateGaussian 0 (cavitySpectralBlockCovariance q (ρs k) (b x))
        ∂(Q k : Measure (SpectralArray (m + 1))) := by
    rw [integral_sub (hHI k) (hgI k), hgMap k]
  simp_rw [he] at herror
  convert herror.add hGaussian using 1 <;> first | (with_reducible_and_instances rfl) | (simp [H, b])

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.cavity_spectral_haar_test_tendsto_oai.{u_1} := @OAI.InvariantIsing.cavity_spectral_haar_test_tendsto_oai.{u_1}
