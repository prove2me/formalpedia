-- Prove2me | solution 1 for OAI.InvariantIsing.gaussianPatternStieltjes_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:27:17.771642+00:00
-- url     : https://prove2.me/submissions/1bf1a6a8-3c36-4970-aac2-c89da7693639

import Mathlib
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Order.Disjointed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258004

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive real resolvent of the physical Gaussian Gram matrix. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianPatternCoupling_posSemidef {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (gaussianPatternCoupling 1 z).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (gaussianPatternArray z)
  simpa only [gaussianPatternCoupling,Matrix.conjTranspose_eq_transpose_of_trivial] using
    h.smul (show 0 ≤ (1 : ℝ)/N by positivity)

lemma gaussianGramShift_posDef {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 z).PosDef :=
  ((Matrix.PosDef.one).smul ht).add_posSemidef (gaussianPatternCoupling_posSemidef z)

lemma gaussianGramResolvent_posDef {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : (gaussianGramResolvent t z).PosDef :=
  (gaussianGramShift_posDef ht z).inv

lemma gaussianGramResolvent_identity {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    t • gaussianGramResolvent t z+gaussianPatternCoupling 1 z*gaussianGramResolvent t z = 1 := by
  have hd := (gaussianGramShift_posDef ht z).det_pos
  have h := Matrix.mul_nonsing_inv (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 z)
    (isUnit_iff_ne_zero.mpr hd.ne')
  simpa only [gaussianGramResolvent,add_mul,smul_mul_assoc,one_mul] using h

lemma gaussianGramResolvent_trace_identity {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    t*(gaussianGramResolvent t z).trace+
      (gaussianPatternCoupling 1 z*gaussianGramResolvent t z).trace = N := by
  have h := congrArg Matrix.trace (gaussianGramResolvent_identity ht z)
  simpa only [Matrix.trace_add,Matrix.trace_smul,smul_eq_mul,Matrix.trace_one,Fintype.card_fin] using h

lemma gaussianGramStieltjes_nonneg {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : 0 ≤ gaussianGramStieltjes t z :=
  div_nonneg (gaussianGramResolvent_posDef ht z).posSemidef.trace_nonneg (Nat.cast_nonneg N)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact column decomposition and the positive leave-one-column Gram matrix. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma gaussianPatternCoupling_column_sum {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling 1 z = (1/(N : ℝ)) •
      ∑ j : Fin m, vecMulVec (gaussianGramRawColumn z j) (gaussianGramRawColumn z j) := by
  ext i k
  simp only [gaussianPatternCoupling,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,
    Matrix.transpose_apply,gaussianPatternArray,Matrix.sum_apply,Matrix.vecMulVec_apply,
    gaussianGramRawColumn]

lemma gaussianGramLeaveOneOut_posSemidef {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : (gaussianGramLeaveOneOut z j).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (by positivity : (0 : ℝ) ≤ 1/N)
  apply Matrix.posSemidef_sum
  intro l _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (gaussianGramRawColumn z l)

lemma gaussianGramLeaveOneOut_decomposition {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : gaussianPatternCoupling 1 z = gaussianGramLeaveOneOut z j+
      (1/(N : ℝ)) • vecMulVec (gaussianGramRawColumn z j) (gaussianGramRawColumn z j) := by
  rw [gaussianPatternCoupling_column_sum,gaussianGramLeaveOneOut,← smul_add]
  congr 1
  exact (Finset.sum_erase_add Finset.univ
    (fun l => vecMulVec (gaussianGramRawColumn z l) (gaussianGramRawColumn z l))
    (Finset.mem_univ j)).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianColumnProductLaw
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical Gaussian matrix as independent Gaussian columns. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma gaussianColumnArray_hasLaw (N m : ℕ) :
    HasLaw (gaussianColumnArray (N := N) (m := m)) (stdGaussian _)
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) := by
  let μ := gaussianReal 0 1
  have hc : HasLaw (MeasurableEquiv.curry (Fin m) (Fin N) ℝ).symm
      (Measure.pi (fun _ : Fin m × Fin N => μ))
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => μ))) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).symm.measurable.aemeasurable,?_⟩
    simpa only [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_curry_symm (fun (_ : Fin m) (_ : Fin N) => μ)
  have hs := (measurePreserving_piCongrLeft (fun _ : Fin N × Fin m => μ)
    (Equiv.prodComm (Fin m) (Fin N))).hasLaw
  have hz : HasLaw (WithLp.toLp 2 : (Fin N × Fin m → ℝ) → EuclideanSpace ℝ (Fin N × Fin m))
      (stdGaussian _) (Measure.pi (fun _ : Fin N × Fin m => μ)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N × Fin m => ℝ)).measurable.aemeasurable,
      map_pi_eq_stdGaussian⟩
  convert hz.comp (hs.comp hc) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma gaussianColumnArray_column {N m : ℕ} (g : Fin m → Fin N → ℝ) (j : Fin m) :
    gaussianGramRawColumn (gaussianColumnArray g) j = g j := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveRankOneInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive rank-one inverse identity used by the Gaussian leave-one-column resolvent. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma positive_rankOne_inverse {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef)
    (x : Fin N → ℝ) :
    (A+vecMulVec x x)⁻¹ = A⁻¹-(1+x ⬝ᵥ (A⁻¹ *ᵥ x))⁻¹ •
      vecMulVec (A⁻¹ *ᵥ x) (A⁻¹ *ᵥ x) := by
  let R := A⁻¹
  let u := R *ᵥ x
  let q := x ⬝ᵥ u
  have hq : 0 < 1+q := by
    have h := hA.inv.posSemidef.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at h
    change 0 ≤ q at h
    linarith
  have hR : Rᵀ = R := by
    simpa only [R,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hA.inv.isHermitian
  have hxR : x ᵥ* R = u := by
    calc
      _ = x ᵥ* Rᵀ := congrArg (fun M => x ᵥ* M) hR.symm
      _ = _ := Matrix.vecMul_transpose R x
  have hAR : A*R = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hAx : A *ᵥ u = x := by
    change A *ᵥ (R *ᵥ x) = x
    rw [Matrix.mulVec_mulVec,hAR,Matrix.one_mulVec]
  have h₁ : (A+vecMulVec x x)*R = 1+vecMulVec x u := by
    rw [add_mul,hAR,Matrix.vecMulVec_mul,hxR]
  have h₂ : (A+vecMulVec x x)*vecMulVec u u = (1+q) • vecMulVec x u := by
    rw [add_mul,Matrix.mul_vecMulVec,hAx,Matrix.vecMulVec_mul_vecMulVec,Matrix.vecMulVec_smul]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    dsimp only [q]
    ring
  apply Matrix.inv_eq_right_inv
  change (A+vecMulVec x x)*(R-(1+q)⁻¹ • vecMulVec u u) = 1
  rw [mul_sub,mul_smul_comm,h₁,h₂,smul_smul,inv_mul_cancel₀ hq.ne',one_smul]
  exact add_sub_cancel_right 1 (vecMulVec x u)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveRankOneQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact quadratic and trace increments of a positive rank-one resolvent update. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma positive_rankOne_quadratic {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef)
    (x : Fin N → ℝ) :
    x ⬝ᵥ ((A+vecMulVec x x)⁻¹ *ᵥ x) = (x ⬝ᵥ (A⁻¹ *ᵥ x))/(1+x ⬝ᵥ (A⁻¹ *ᵥ x)) := by
  let u := A⁻¹ *ᵥ x
  let q := x ⬝ᵥ u
  have hq : 0 < 1+q := by
    have hh := hA.inv.posSemidef.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hh
    change 0 ≤ q at hh
    linarith
  have hh : vecMulVec u u *ᵥ x = q • u := by
    ext i
    simp only [Matrix.mulVec,Matrix.vecMulVec_apply,dotProduct,Pi.smul_apply,smul_eq_mul]
    dsimp only [q]
    simp only [dotProduct]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [positive_rankOne_inverse A hA x,Matrix.sub_mulVec,Matrix.smul_mulVec]
  change x ⬝ᵥ (u-(1+q)⁻¹ • (vecMulVec u u *ᵥ x)) = q/(1+q)
  rw [hh,dotProduct_sub,dotProduct_smul,dotProduct_smul]
  change q-(1+q)⁻¹*(q*q) = q/(1+q)
  field_simp [hq.ne']
  ring

lemma positive_rankOne_trace_difference {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef)
    (x : Fin N → ℝ) :
    A⁻¹.trace-(A+vecMulVec x x)⁻¹.trace =
      ((A⁻¹ *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ x))/(1+x ⬝ᵥ (A⁻¹ *ᵥ x)) := by
  rw [positive_rankOne_inverse A hA x,Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_vecMulVec]
  simp only [smul_eq_mul]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianLeaveOneColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact leave-one-column identities at the physical Gaussian normalization. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianPatternScaledColumn_outer {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) :
    vecMulVec (gaussianPatternScaledColumn z j) (gaussianPatternScaledColumn z j) =
      (1/(N : ℝ)) • vecMulVec (gaussianGramRawColumn z j) (gaussianGramRawColumn z j) := by
  have he : ((Real.sqrt (N : ℝ))⁻¹)^2 = 1/(N : ℝ) := by
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N),one_div]
  ext i k
  simp only [gaussianPatternScaledColumn,Matrix.vecMulVec_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ = ((Real.sqrt (N : ℝ))⁻¹)^2*(gaussianGramRawColumn z j i*gaussianGramRawColumn z j k) := by ring
    _ = _ := by rw [he]

lemma gaussianGramLeaveShift_posDef {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianGramLeaveOneOut z j).PosDef :=
  (Matrix.PosDef.one.smul ht).add_posSemidef (gaussianGramLeaveOneOut_posSemidef z j)

lemma gaussianGramLeaveResolvent_quadratic {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    let x := gaussianPatternScaledColumn z j
    x ⬝ᵥ (gaussianGramResolvent t z *ᵥ x) =
      (x ⬝ᵥ (gaussianGramLeaveResolvent t z j *ᵥ x))/(1+x ⬝ᵥ (gaussianGramLeaveResolvent t z j *ᵥ x)) := by
  have h := positive_rankOne_quadratic _ (gaussianGramLeaveShift_posDef ht z j)
    (gaussianPatternScaledColumn z j)
  rw [gaussianPatternScaledColumn_outer,add_assoc,← gaussianGramLeaveOneOut_decomposition] at h
  exact h

lemma gaussianGramLeaveResolvent_trace {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    let x := gaussianPatternScaledColumn z j
    (gaussianGramLeaveResolvent t z j).trace-(gaussianGramResolvent t z).trace =
      ((gaussianGramLeaveResolvent t z j *ᵥ x) ⬝ᵥ (gaussianGramLeaveResolvent t z j *ᵥ x))/
        (1+x ⬝ᵥ (gaussianGramLeaveResolvent t z j *ᵥ x)) := by
  have h := positive_rankOne_trace_difference _ (gaussianGramLeaveShift_posDef ht z j)
    (gaussianPatternScaledColumn z j)
  rw [gaussianPatternScaledColumn_outer,add_assoc,← gaussianGramLeaveOneOut_decomposition] at h
  exact h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResolventEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite-dimensional leave-one-column equation for the physical Gram transform. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma gaussianPatternCoupling_scaled_column_sum {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling 1 z = ∑ j : Fin m,
      vecMulVec (gaussianPatternScaledColumn z j) (gaussianPatternScaledColumn z j) := by
  simp_rw [gaussianPatternScaledColumn_outer]
  rw [← Finset.smul_sum,gaussianPatternCoupling_column_sum]

lemma trace_rankOne_mul {N : ℕ} (x : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    (vecMulVec x x*A).trace = x ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.trace_mul_comm,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]

lemma gaussianGramColumnQuadratic_nonneg {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) : 0 ≤ gaussianGramColumnQuadratic t z j := by
  have h := (gaussianGramLeaveShift_posDef ht z j).inv.posSemidef.dotProduct_mulVec_nonneg
    (gaussianPatternScaledColumn z j)
  simpa only [gaussianGramColumnQuadratic,gaussianGramLeaveResolvent,star_trivial] using h

lemma gaussianGramResolvent_column_trace {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    t*(gaussianGramResolvent t z).trace+
      ∑ j : Fin m, gaussianGramColumnQuadratic t z j/(1+gaussianGramColumnQuadratic t z j) = N := by
  have he := gaussianGramResolvent_trace_identity ht z
  rw [gaussianPatternCoupling_scaled_column_sum,Finset.sum_mul,Matrix.trace_sum] at he
  simp_rw [trace_rankOne_mul,gaussianGramLeaveResolvent_quadratic ht z] at he
  exact he

theorem gaussianGramStieltjes_column_equation {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    1-t*gaussianGramStieltjes t z = (1/(N : ℝ))*
      ∑ j : Fin m, gaussianGramColumnQuadratic t z j/(1+gaussianGramColumnQuadratic t z j) := by
  have h := gaussianGramResolvent_column_trace ht z
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold gaussianGramStieltjes
  rw [one_div_mul_eq_div]
  apply (eq_div_iff hn).mpr
  field_simp
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternEigenvalueMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual sorted Gaussian Gram spectrum, including repeated zero roots. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology Matrix.Norms.L2Operator
namespace InvariantIsing

lemma continuous_gaussianPatternCoupling (N m : ℕ) (c : ℝ) :
    Continuous (gaussianPatternCoupling (N := N) (m := m) c) := by
  unfold gaussianPatternCoupling gaussianPatternArray
  fun_prop

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianCoordinateNorm
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact second moments and the square-root dimension bound for coordinate Gaussian norms. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma gaussianCoordinate_memLp (i : ι) :
    MemLp (fun g : ι → ℝ => g i) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw.memLp
    (IsGaussian.memLp_id _ 2 (by norm_num))

lemma gaussianCoordinateVector_sq_integrable (e : κ → ι) :
    Integrable (fun g => ‖gaussianCoordinateVector e g‖^2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simpa only [gaussianCoordinateVector,EuclideanSpace.real_norm_sq_eq,PiLp.toLp_apply]
    using integrable_finsetSum Finset.univ (fun j _ => (gaussianCoordinate_memLp (e j)).integrable_sq)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianFourthMoment
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar Gaussian polynomial moments needed for the quadratic leave-one-column estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma gaussianReal_pow_integrable (p : ℕ) :
    Integrable (fun x : ℝ => x^p) (gaussianReal 0 1) := by
  have hi := (IsGaussian.memLp_id (gaussianReal 0 1) p (by simp)).integrable_norm_pow'
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq,Real.norm_eq_abs,abs_pow] using hi

lemma gaussianReal_second_moment : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [id_eq,integral_id_gaussianReal,sub_zero,NNReal.coe_one] using h

lemma gaussianReal_fourth_moment : (∫ x : ℝ, x^4 ∂gaussianReal 0 1) = 3 := by
  have h := gaussian_integration_by_parts
    (f := fun x : ℝ => x^3) (f' := fun x => 3*x^2)
    (fun x => by simpa using hasDerivAt_pow 3 x)
    (gaussianReal_pow_integrable 3) ((gaussianReal_pow_integrable 2).const_mul 3)
    (by convert gaussianReal_pow_integrable 4 using 1; funext x; ring)
  have he : (fun x : ℝ => x*x^3) = fun x => x^4 := by funext x; ring
  rw [he,integral_const_mul,gaussianReal_second_moment,mul_one] at h
  exact h

lemma gaussianReal_square_memLp : MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussianReal_pow_integrable 4

lemma gaussianReal_square_variance : variance (fun x : ℝ => x^2) (gaussianReal 0 1) = 2 := by
  rw [variance_eq_sub gaussianReal_square_memLp,gaussianReal_second_moment]
  change (∫ x : ℝ, (x^2)^2 ∂gaussianReal 0 1)-1^2 = 2
  have hp : (fun x : ℝ => (x^2)^2) = fun x => x^4 := by funext x; ring
  rw [hp,gaussianReal_fourth_moment]
  norm_num

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianDiagonalQuadratic
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact mean and variance of a diagonal Gaussian quadratic form. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

lemma gaussianDiagonalQuadratic_mean {N : ℕ} (a : Fin N → ℝ) :
    (∫ g, gaussianDiagonalQuadratic a g ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) = ∑ i, a i := by
  unfold gaussianDiagonalQuadratic
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    have h := (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).hasLaw.integral_comp
      (f := fun x : ℝ => x^2) (by fun_prop)
    simpa only [Function.comp_def,Function.eval,gaussianReal_second_moment,mul_one] using
      congrArg (fun x : ℝ => a i*x) h
  · intro i _
    exact ((gaussianReal_square_memLp.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i)).const_mul (a i)).integrable (by norm_num)

lemma gaussianDiagonalQuadratic_variance {N : ℕ} (a : Fin N → ℝ) :
    variance (gaussianDiagonalQuadratic a) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      2*∑ i, (a i)^2 := by
  have h := variance_sum_pi (μ := fun _ : Fin N => gaussianReal 0 1)
    (X := fun i x => a i*x^2) (fun i => gaussianReal_square_memLp.const_mul (a i))
  have he : (∑ i : Fin N, fun g : Fin N → ℝ => a i*(g i)^2) = gaussianDiagonalQuadratic a := by
    funext g
    simp only [Finset.sum_apply,gaussianDiagonalQuadratic]
  rw [he] at h
  rw [h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [variance_const_mul,gaussianReal_square_variance]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_HermitianQuadraticCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real quadratic form in its actual orthonormal eigenvector coordinates. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma hermitian_quadratic_coordinates {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin N)) :
    ⟪x,A.toEuclideanLin x⟫ =
      ∑ i, hA.eigenvalues i*(hA.eigenvectorBasis.repr x i)^2 := by
  let b := hA.eigenvectorBasis
  have he (i : Fin N) : A.toEuclideanLin (b i) = hA.eigenvalues i • b i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hx : A.toEuclideanLin x = ∑ i, (b.repr x i*hA.eigenvalues i) • b i := by
    nth_rw 1 [← b.sum_repr x]
    rw [map_sum]
    simp_rw [map_smul,he,smul_smul]
  rw [hx,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right]
  have hi : ⟪x,b i⟫ = b.repr x i := by
    exact (real_inner_comm x (b i)).symm.trans (b.repr_apply_apply x i).symm
  calc
    _ = (b.repr x i*hA.eigenvalues i)*(b.repr x i) := congrArg _ hi
    _ = _ := by dsimp only [b] <;> ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_HermitianGaussianQuadratic
attribute [-instance] _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Gaussian quadratic mean and variance in finite dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma gaussianQuadraticForm_continuous {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    Continuous (gaussianQuadraticForm A) := by unfold gaussianQuadraticForm; fun_prop

lemma gaussianQuadraticForm_abs_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin N)) :
    |gaussianQuadraticForm A x| ≤ ‖A.toEuclideanLin.toContinuousLinearMap‖*‖x‖^2 := by
  calc
    _ ≤ ‖x‖*‖A.toEuclideanLin x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖A.toEuclideanLin.toContinuousLinearMap‖*‖x‖) :=
      mul_le_mul_of_nonneg_left (A.toEuclideanLin.toContinuousLinearMap.le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

lemma gaussianQuadraticForm_memLp {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    MemLp (gaussianQuadraticForm A) 2 (stdGaussian _) := by
  have hi := (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin N))) 4 (by norm_num)).integrable_norm_pow'
  apply (memLp_two_iff_integrable_sq (gaussianQuadraticForm_continuous A).aestronglyMeasurable).mpr
  apply (hi.const_mul (‖A.toEuclideanLin.toContinuousLinearMap‖^2)).mono'
    ((gaussianQuadraticForm_continuous A).pow 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hh := (sq_le_sq₀ (abs_nonneg (gaussianQuadraticForm A x))
    (mul_nonneg (norm_nonneg _) (sq_nonneg ‖x‖))).2 (gaussianQuadraticForm_abs_le A x)
  simpa only [sq_abs,mul_pow,← pow_mul,Pi.pow_apply,id_eq] using hh

lemma hermitianGaussianQuadratic_mean {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    (∫ x, gaussianQuadraticForm A x ∂stdGaussian _) = A.trace := by
  let b := hA.eigenvectorBasis
  let F (g : Fin N → ℝ) := b.repr.symm (WithLp.toLp 2 g)
  have he : HasLaw b.repr.symm (stdGaussian _) (stdGaussian _) :=
    ⟨b.repr.symm.continuous.measurable.aemeasurable,stdGaussian_map b.repr.symm⟩
  have hz : HasLaw (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N))
      (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have hF : HasLaw F (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := he.comp hz
  have hdiag (g : Fin N → ℝ) : gaussianQuadraticForm A (F g) = gaussianDiagonalQuadratic hA.eigenvalues g := by
    rw [gaussianQuadraticForm,hermitian_quadratic_coordinates]
    simp only [F,b,LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [← hF.integral_comp (gaussianQuadraticForm_continuous A).aestronglyMeasurable]
  simp_rw [Function.comp_def,hdiag]
  rw [gaussianDiagonalQuadratic_mean,hA.trace_eq_sum_eigenvalues]
  simp

lemma hermitianGaussianQuadratic_variance {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    variance (gaussianQuadraticForm A) (stdGaussian _) = 2*∑ i, (hA.eigenvalues i)^2 := by
  let b := hA.eigenvectorBasis
  let F (g : Fin N → ℝ) := b.repr.symm (WithLp.toLp 2 g)
  have he : HasLaw b.repr.symm (stdGaussian _) (stdGaussian _) :=
    ⟨b.repr.symm.continuous.measurable.aemeasurable,stdGaussian_map b.repr.symm⟩
  have hz : HasLaw (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N))
      (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have hF : HasLaw F (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := he.comp hz
  have hdiag : gaussianQuadraticForm A ∘ F = gaussianDiagonalQuadratic hA.eigenvalues := by
    funext g
    change ⟪F g,A.toEuclideanLin (F g)⟫ = _
    rw [hermitian_quadratic_coordinates]
    simp only [F,b,LinearIsometryEquiv.apply_symm_apply]
    rfl
  calc
    _ = variance (gaussianQuadraticForm A ∘ F) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := by
      rw [← hF.map_eq]
      exact variance_map ((gaussianQuadraticForm_continuous A).measurable.aemeasurable) hF.aemeasurable
    _ = _ := by rw [hdiag,gaussianDiagonalQuadratic_variance]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianColumnDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deleting a column removes all dependence on that Gaussian coordinate. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma gaussianGramLeaveOneOut_congr {N m : ℕ} (g h : Fin m → Fin N → ℝ) (j : Fin m)
    (he : ∀ l, l ≠ j → g l = h l) :
    gaussianGramLeaveOneOut (gaussianColumnArray g) j =
      gaussianGramLeaveOneOut (gaussianColumnArray h) j := by
  unfold gaussianGramLeaveOneOut
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [gaussianColumnArray_column,gaussianColumnArray_column,he l (Finset.mem_erase.mp hl).1]

lemma gaussianGramLeaveOneOut_insertNth {N m : ℕ} (j : Fin (m+1))
    (x y : Fin N → ℝ) (g : Fin m → Fin N → ℝ) :
    gaussianGramLeaveOneOut (gaussianColumnArray (j.insertNth x g)) j =
      gaussianGramLeaveOneOut (gaussianColumnArray (j.insertNth y g)) j := by
  apply gaussianGramLeaveOneOut_congr
  intro l hl
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hl
  simp only [Fin.insertNth_apply_succAbove]

lemma gaussianGramColumnQuadratic_eq {N m : ℕ} (t : ℝ) (g : Fin m → Fin N → ℝ) (j : Fin m) :
    gaussianGramColumnQuadratic t (gaussianColumnArray g) j =
      (1/(N : ℝ))*gaussianQuadraticForm
        (gaussianGramLeaveResolvent t (gaussianColumnArray g) j) (WithLp.toLp 2 (g j)) := by
  have he : ((Real.sqrt (N : ℝ))⁻¹)^2 = 1/(N : ℝ) := by
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N),one_div]
  unfold gaussianGramColumnQuadratic gaussianPatternScaledColumn
  rw [gaussianColumnArray_column,Matrix.mulVec_smul,dotProduct_smul,smul_dotProduct]
  simp only [smul_eq_mul]
  unfold gaussianQuadraticForm
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]
  change _ = (1/(N : ℝ))*((gaussianGramLeaveResolvent t (gaussianColumnArray g) j *ᵥ g j) ⬝ᵥ g j)
  calc
    _ = ((Real.sqrt (N : ℝ))⁻¹)^2*((gaussianGramLeaveResolvent t (gaussianColumnArray g) j *ᵥ g j) ⬝ᵥ g j) := by ring
    _ = _ := by rw [he]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveResolventSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral bounds for the positive resolvents occurring after deletion of a column. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma positiveResolvent_eigenvalues {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (i : Fin N) :
    0 ≤ (positiveResolvent_posDef ht hB).isHermitian.eigenvalues i ∧
    (positiveResolvent_posDef ht hB).isHermitian.eigenvalues i ≤ 1/t := by
  let R := positiveResolvent t B
  let hR : R.PosDef := positiveResolvent_posDef ht hB
  let u := hR.isHermitian.eigenvectorBasis i
  let a := hR.isHermitian.eigenvalues i
  have hu : u.ofLp ⬝ᵥ u.ofLp = 1 := by
    change ⟪u,u⟫ = 1
    rw [real_inner_self_eq_norm_sq]
    simp only [u,hR.isHermitian.eigenvectorBasis.orthonormal.1 i,one_pow]
  have ha : 0 ≤ a := by
    dsimp only [a]
    rw [hR.isHermitian.eigenvalues_eq]
    simpa only [star_trivial,RCLike.re_to_real] using hR.posSemidef.dotProduct_mulVec_nonneg u.ofLp
  have hq : 0 ≤ u.ofLp ⬝ᵥ (B *ᵥ u.ofLp) := by
    simpa only [star_trivial] using hB.dotProduct_mulVec_nonneg u.ofLp
  have hinv : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B)*R = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (((Matrix.PosDef.one.smul ht).add_posSemidef hB).det_pos.ne'))
  have heig : R *ᵥ u.ofLp = a • u.ofLp := hR.isHermitian.mulVec_eigenvectorBasis i
  have hh : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) *ᵥ (R *ᵥ u.ofLp) = u.ofLp := by
    rw [Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec]
  rw [heig,Matrix.mulVec_smul,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at hh
  have hd := congrArg (fun y => u.ofLp ⬝ᵥ y) hh
  rw [dotProduct_smul,dotProduct_add,dotProduct_smul,hu] at hd
  simp only [smul_eq_mul,mul_one] at hd
  constructor
  · exact ha
  · apply (le_div_iff₀ ht).mpr
    nlinarith [mul_nonneg ha hq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveResolventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform trace and quadratic bounds for positive resolvents. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma positiveResolvent_trace_le {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    (positiveResolvent t B).trace ≤ (N : ℝ)/t := by
  have he := (positiveResolvent_posDef ht hB).isHermitian.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id,id_eq] at he
  rw [he]
  calc
    _ ≤ ∑ _ : Fin N, 1/t := Finset.sum_le_sum (fun i _ => (positiveResolvent_eigenvalues ht hB i).2)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

lemma positiveResolvent_quadratic_le {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (x : EuclideanSpace ℝ (Fin N)) :
    gaussianQuadraticForm (positiveResolvent t B) x ≤ ‖x‖^2/t := by
  let hR := (positiveResolvent_posDef ht hB).isHermitian
  rw [gaussianQuadraticForm,hermitian_quadratic_coordinates _ hR]
  calc
    _ ≤ ∑ i, (1/t)*(hR.eigenvectorBasis.repr x i)^2 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (positiveResolvent_eigenvalues ht hB i).2 (sq_nonneg _))
    _ = (1/t)*‖hR.eigenvectorBasis.repr x‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

lemma positiveResolvent_quadratic_nonneg {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (x : EuclideanSpace ℝ (Fin N)) :
    0 ≤ gaussianQuadraticForm (positiveResolvent t B) x := by
  rw [gaussianQuadraticForm,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]
  exact (positiveResolvent_posDef ht hB).posSemidef.dotProduct_mulVec_nonneg x.ofLp

lemma positiveResolvent_normalized_abs_bound {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (x : EuclideanSpace ℝ (Fin N)) :
    |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x-
      (positiveResolvent t B).trace/N| ≤ (1/((N : ℝ)*t))*‖x‖^2+1/t := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := positiveResolvent_quadratic_nonneg ht hB x
  have htr := (positiveResolvent_posDef ht hB).posSemidef.trace_nonneg
  calc
    _ ≤ |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x|+
        |(positiveResolvent t B).trace/N| := abs_sub _ _
    _ = (1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x+
        (positiveResolvent t B).trace/N := by rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    _ ≤ (1/(N : ℝ))*(‖x‖^2/t)+((N : ℝ)/t)/N := add_le_add
      (mul_le_mul_of_nonneg_left (positiveResolvent_quadratic_le ht hB x) (by positivity))
      (div_le_div_of_nonneg_right (positiveResolvent_trace_le ht hB) hn.le)
    _ = _ := by field_simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianColumnResolventContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual deleted-column resolvent observables. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma continuous_gaussianGramLeaveOneOut {N m : ℕ} (j : Fin m) :
    Continuous (gaussianGramLeaveOneOut (N := N) · j) := by
  apply continuous_matrix
  intro i k
  simp only [gaussianGramLeaveOneOut,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.vecMulVec_apply,gaussianGramRawColumn,smul_eq_mul]
  fun_prop

lemma continuous_gaussianGramLeaveResolvent {N m : ℕ} {t : ℝ} (ht : 0 < t) (j : Fin m) :
    Continuous (gaussianGramLeaveResolvent (N := N) t · j) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hi := continuousAt_matrix_inv
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianGramLeaveOneOut z j)
    (show ContinuousAt Ring.inverse _ from by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
        (gaussianGramLeaveShift_posDef ht z j).det_pos.ne')
  exact hi.comp (f := fun w : EuclideanSpace ℝ (Fin N × Fin m) =>
    t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianGramLeaveOneOut w j)
    ((continuous_const.add (continuous_gaussianGramLeaveOneOut j)).continuousAt)

lemma continuous_gaussianGramColumnQuadratic {N m : ℕ} {t : ℝ} (ht : 0 < t) (j : Fin m) :
    Continuous (gaussianGramColumnQuadratic (N := N) t · j) := by
  have hr := continuous_gaussianGramLeaveResolvent (N := N) ht j
  simp only [gaussianGramColumnQuadratic,gaussianPatternScaledColumn,gaussianGramRawColumn,
    Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul]
  fun_prop

lemma continuous_gaussianColumnArray {N m : ℕ} :
    Continuous (gaussianColumnArray (N := N) (m := m)) := by
  unfold gaussianColumnArray
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin m => ℝ)).comp
    (continuous_pi (fun p => (continuous_apply p.1).comp (continuous_apply p.2)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_RestrictedPressureFluctuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform mean absolute fluctuations for constrained Haar pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

lemma integral_abs_sub_mean_le_sqrt_variance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (variance f μ) := by
  let g := fun x => f x-∫ y, f y ∂μ
  have hg : MemLp g 2 μ := hf.sub (memLp_const _)
  have hga : MemLp (fun x => |g x|) 2 μ := by simpa only [Real.norm_eq_abs] using hg.norm
  have hv := variance_nonneg (fun x => |g x|) μ
  rw [variance_eq_sub hga] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have he : (∫ x, g x^2 ∂μ)=variance f μ :=
    (variance_eq_integral hf.aemeasurable).symm
  rw [he] at hv
  apply (sq_le_sq₀ (integral_nonneg (fun _ => abs_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (variance_nonneg f μ)]
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveResolventVariance
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dimension-explicit Gaussian quadratic variance bound for a positive resolvent. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma positiveResolvent_quadratic_variance {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    variance (gaussianQuadraticForm (positiveResolvent t B)) (stdGaussian _) ≤ 2*N/t^2 := by
  rw [hermitianGaussianQuadratic_variance _ (positiveResolvent_posDef ht hB).isHermitian]
  have hs : (∑ i, ((positiveResolvent_posDef ht hB).isHermitian.eigenvalues i)^2) ≤
      (N : ℝ)*(1/t)^2 := by
    calc
      _ ≤ ∑ _ : Fin N, (1/t)^2 := Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (positiveResolvent_eigenvalues ht hB i).1 (by positivity)).2
          (positiveResolvent_eigenvalues ht hB i).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  calc
    _ ≤ 2*((N : ℝ)*(1/t)^2) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

lemma positiveResolvent_normalized_variance {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    variance (fun x => (1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x) (stdGaussian _) ≤
      2/((N : ℝ)*t^2) := by
  rw [variance_const_mul]
  have h := mul_le_mul_of_nonneg_left (positiveResolvent_quadratic_variance ht hB) (sq_nonneg (1/(N : ℝ)))
  apply h.trans_eq
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp [hn]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveResolventFluctuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Gaussian mean absolute fluctuations of a normalized resolvent quadratic form. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

lemma positiveResolvent_normalized_mean {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    (∫ x, (1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x ∂stdGaussian _) =
      (positiveResolvent t B).trace / N := by
  rw [integral_const_mul,hermitianGaussianQuadratic_mean _ (positiveResolvent_posDef ht hB).isHermitian]
  ring

lemma positiveResolvent_normalized_fluctuation {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    (∫ x, |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x-
      (positiveResolvent t B).trace / N| ∂stdGaussian _) ≤ Real.sqrt (2/((N : ℝ)*t^2)) := by
  have hf := (gaussianQuadraticForm_memLp (positiveResolvent t B)).const_mul (1/(N : ℝ))
  have h := integral_abs_sub_mean_le_sqrt_variance (stdGaussian _)
    (fun x => (1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x) hf
  rw [positiveResolvent_normalized_mean ht hB] at h
  exact h.trans (Real.sqrt_le_sqrt (positiveResolvent_normalized_variance hN ht hB))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianColumnDeviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the actual leave-one-column quadratic deviation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

lemma continuous_gaussianGramColumnDeviation {N m : ℕ} {t : ℝ} (ht : 0 < t) (j : Fin m) :
    Continuous (gaussianGramColumnDeviation (N := N) t · j) :=
  ((continuous_gaussianGramColumnQuadratic ht j).sub
    ((continuous_gaussianGramLeaveResolvent ht j).matrix_trace.div_const _)).abs

lemma gaussianGramColumnDeviation_bound {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (g : Fin m → Fin N → ℝ) (j : Fin m) :
    gaussianGramColumnDeviation t (gaussianColumnArray g) j ≤
      (1/((N : ℝ)*t))*‖WithLp.toLp 2 (g j)‖^2+1/t := by
  unfold gaussianGramColumnDeviation
  rw [gaussianGramColumnQuadratic_eq]
  exact positiveResolvent_normalized_abs_bound hN ht
    (gaussianGramLeaveOneOut_posSemidef (gaussianColumnArray g) j) _

lemma gaussianGramColumnDeviation_integrable {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (j : Fin m) : Integrable (fun g : Fin m → Fin N → ℝ =>
      gaussianGramColumnDeviation t (gaussianColumnArray g) j)
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) := by
  have hi := (measurePreserving_eval
    (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1)) j).hasLaw.integrable_comp
      (gaussianCoordinateVector_sq_integrable (id : Fin N → Fin N))
  have hm : AEStronglyMeasurable (fun g : Fin m → Fin N → ℝ =>
      gaussianGramColumnDeviation t (gaussianColumnArray g) j)
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) :=
    ((continuous_gaussianGramColumnDeviation (N := N) ht j).comp
    (continuous_gaussianColumnArray (N := N) (m := m))).aestronglyMeasurable
  apply ((hi.const_mul (1/((N : ℝ)*t))).add (integrable_const (1/t))).mono' hm
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ gaussianGramColumnDeviation t (gaussianColumnArray g) j from abs_nonneg _)]
  exact gaussianGramColumnDeviation_bound hN ht g j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianColumnDeviationMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional Gaussian quadratic fluctuation, averaged over the actual remaining columns. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

lemma gaussianGramColumnDeviation_insert_integral {N m : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) (j : Fin (m+1)) (g : Fin m → Fin N → ℝ) :
    (∫ x : Fin N → ℝ, gaussianGramColumnDeviation t (gaussianColumnArray (j.insertNth x g)) j
      ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) ≤ Real.sqrt (2/((N : ℝ)*t^2)) := by
  let B := gaussianGramLeaveOneOut (gaussianColumnArray (j.insertNth 0 g)) j
  have hB : B.PosSemidef := gaussianGramLeaveOneOut_posSemidef _ j
  have he (x : Fin N → ℝ) :
      gaussianGramColumnDeviation t (gaussianColumnArray (j.insertNth x g)) j =
      |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) (WithLp.toLp 2 x)-
        (positiveResolvent t B).trace/N| := by
    unfold gaussianGramColumnDeviation
    rw [gaussianGramColumnQuadratic_eq]
    simp only [Fin.insertNth_apply_same,gaussianGramLeaveResolvent,
      gaussianGramLeaveOneOut_insertNth j x 0 g,positiveResolvent,B]
  simp_rw [he]
  have hz : HasLaw (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N))
      (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have htrans : (∫ x : Fin N → ℝ, |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B)
      (WithLp.toLp 2 x)-(positiveResolvent t B).trace/N| ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x, |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x-
        (positiveResolvent t B).trace/N| ∂stdGaussian _ := by
    simpa only [Function.comp_def] using (hz.integral_comp
        (f := fun x => |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x-
          (positiveResolvent t B).trace/N|)
        (((gaussianQuadraticForm_continuous _).const_mul _).sub continuous_const).abs.aestronglyMeasurable)
  rw [htrans]
  exact positiveResolvent_normalized_fluctuation hN ht hB

theorem gaussianGramColumnDeviation_mean_le {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (j : Fin (m+1)) :
    (∫ g : Fin (m+1) → Fin N → ℝ, gaussianGramColumnDeviation t (gaussianColumnArray g) j
      ∂Measure.pi (fun _ : Fin (m+1) => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) ≤
      Real.sqrt (2/((N : ℝ)*t^2)) := by
  let μ := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin (m+1) => μ)
  let ρ := Measure.pi (fun _ : Fin m => μ)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => Fin N → ℝ) j).symm
  let F := fun g : Fin (m+1) → Fin N → ℝ => gaussianGramColumnDeviation t (gaussianColumnArray g) j
  have hm : MeasurePreserving e (μ.prod ρ) ν := (measurePreserving_piFinSuccAbove (fun _ => μ) j).symm
  have hi : Integrable F ν := gaussianGramColumnDeviation_integrable hN ht j
  have hip : Integrable (F ∘ e) (μ.prod ρ) := hm.hasLaw.integrable_comp hi
  calc
    _ = ∫ p, F (e p) ∂μ.prod ρ := (hm.integral_comp' F).symm
    _ = ∫ g, ∫ x, F (e (x,g)) ∂μ ∂ρ := integral_prod_symm _ hip
    _ ≤ ∫ _ : Fin m → Fin N → ℝ, Real.sqrt (2/((N : ℝ)*t^2)) ∂ρ := by
      apply integral_mono hip.integral_prod_right (integrable_const _)
      intro g
      exact gaussianGramColumnDeviation_insert_integral hN ht j g
    _ = _ := by simp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResolventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds and measurability for the physical positive resolvent. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianGramResolvent_mixed_trace_nonneg {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    0 ≤ (gaussianPatternCoupling 1 z*gaussianGramResolvent t z).trace := by
  have hp := ((gaussianGramResolvent_posDef ht z).posSemidef.conjTranspose_mul_mul_same
    (gaussianPatternArray z)).trace_nonneg
  rw [gaussianPatternCoupling,smul_mul_assoc,Matrix.trace_smul,smul_eq_mul]
  apply mul_nonneg (by positivity)
  rw [Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hp

lemma gaussianGramStieltjes_le {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : gaussianGramStieltjes t z ≤ 1/t := by
  by_cases hN : N = 0
  · subst N
    simp only [gaussianGramStieltjes,Nat.cast_zero,div_zero]
    exact (one_div_pos.mpr ht).le
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hi := gaussianGramResolvent_trace_identity ht z
  have hp := gaussianGramResolvent_mixed_trace_nonneg ht z
  apply (div_le_iff₀ hN').mpr
  calc
    _ ≤ (N : ℝ)/t := (le_div_iff₀ ht).mpr (by nlinarith)
    _ = 1/t*N := by ring

lemma continuous_gaussianGramResolvent {N m : ℕ} {t : ℝ} (ht : 0 < t) :
    Continuous (gaussianGramResolvent (N := N) (m := m) t) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hdet := (gaussianGramShift_posDef ht z).det_pos
  have hi := continuousAt_matrix_inv
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 z)
    (show ContinuousAt Ring.inverse _ from by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet.ne')
  change ContinuousAt (fun w : EuclideanSpace ℝ (Fin N × Fin m) =>
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 w)⁻¹) z
  exact hi.comp (f := fun w : EuclideanSpace ℝ (Fin N × Fin m) =>
    t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianPatternCoupling 1 w)
    ((continuous_const.add (continuous_gaussianPatternCoupling N m 1)).continuousAt)

lemma continuous_gaussianGramStieltjes {N m : ℕ} {t : ℝ} (ht : 0 < t) :
    Continuous (gaussianGramStieltjes (N := N) (m := m) t) := by
  exact (continuous_gaussianGramResolvent ht).matrix_trace.div_const _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_PositiveResolventContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dimension-free quadratic contraction for positive resolvents. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma positiveResolvent_quadratic_contraction {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (x : Fin N → ℝ) :
    t*((positiveResolvent t B *ᵥ x) ⬝ᵥ (positiveResolvent t B *ᵥ x)) ≤
      x ⬝ᵥ (positiveResolvent t B *ᵥ x) := by
  let y := positiveResolvent t B *ᵥ x
  have hinv : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B)*positiveResolvent t B = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (((Matrix.PosDef.one.smul ht).add_posSemidef hB).det_pos.ne'))
  have hy : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) *ᵥ y = x := by
    change (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) *ᵥ (positiveResolvent t B *ᵥ x) = x
    rw [Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec]
  have hp : 0 ≤ y ⬝ᵥ (B *ᵥ y) := by
    simpa only [star_trivial] using hB.dotProduct_mulVec_nonneg y
  have hh := congrArg (fun z => y ⬝ᵥ z) hy
  rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul] at hh
  simp only [smul_eq_mul] at hh
  rw [dotProduct_comm x y]
  change t*(y ⬝ᵥ y) ≤ y ⬝ᵥ x
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramTraceGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one physical Gaussian column changes the normalized transform by at most 1/(Nt). -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianGramLeaveResolvent_trace_gap {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    0 ≤ (gaussianGramLeaveResolvent t z j).trace-(gaussianGramResolvent t z).trace ∧
    (gaussianGramLeaveResolvent t z j).trace-(gaussianGramResolvent t z).trace ≤ 1/t := by
  rw [gaussianGramLeaveResolvent_trace ht z j]
  let x := gaussianPatternScaledColumn z j
  let y := gaussianGramLeaveResolvent t z j *ᵥ x
  have hq := gaussianGramColumnQuadratic_nonneg ht z j
  change 0 ≤ x ⬝ᵥ y at hq
  have hd : 0 < 1+x ⬝ᵥ y := by linarith
  have hy : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i))
  have hc := positiveResolvent_quadratic_contraction ht (gaussianGramLeaveOneOut_posSemidef z j) x
  change t*(y ⬝ᵥ y) ≤ x ⬝ᵥ y at hc
  constructor
  · exact div_nonneg hy hd.le
  · apply (div_le_div_iff₀ hd ht).mpr
    nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramQuadraticError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing a leave-one-column quadratic form by the full normalized trace. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma gaussianGramColumnQuadratic_error {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    |gaussianGramColumnQuadratic t z j-gaussianGramStieltjes t z| ≤
      gaussianGramColumnDeviation t z j+1/((N : ℝ)*t) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hg := gaussianGramLeaveResolvent_trace_gap ht z j
  have he : (gaussianGramLeaveResolvent t z j).trace/N-gaussianGramStieltjes t z =
      ((gaussianGramLeaveResolvent t z j).trace-(gaussianGramResolvent t z).trace)/N := by
    unfold gaussianGramStieltjes
    ring
  have hd : |(gaussianGramLeaveResolvent t z j).trace/N-gaussianGramStieltjes t z| ≤
      1/((N : ℝ)*t) := by
    rw [he,abs_of_nonneg (div_nonneg hg.1 hn.le)]
    calc
      _ ≤ (1/t)/N := div_le_div_of_nonneg_right hg.2 hn.le
      _ = _ := by ring
  exact (abs_sub_le (gaussianGramColumnQuadratic t z j)
    ((gaussianGramLeaveResolvent t z j).trace/N) (gaussianGramStieltjes t z)).trans
    (add_le_add le_rfl hd)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_MarchenkoPasturTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unique nonnegative solution of the real Marchenko--Pastur transform equation. -/
noncomputable section
namespace InvariantIsing

lemma marchenkoPasturTransform_pos {t α : ℝ} (ht : 0 < t) : 0 < marchenkoPasturTransform t α := by
  have hs : (t+α-1)^2 < (t+α-1)^2+4*t := by linarith
  have ha := Real.lt_sqrt_of_sq_lt hs
  unfold marchenkoPasturTransform
  exact div_pos (by linarith) (by positivity)

lemma marchenkoPasturTransform_polynomial {t α : ℝ} (ht : 0 < t) :
    t*(marchenkoPasturTransform t α)^2+(t+α-1)*marchenkoPasturTransform t α-1 = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ (t+α-1)^2+4*t by positivity)
  rw [show 4*t=t*4 by ring] at hs
  unfold marchenkoPasturTransform
  field_simp [ht.ne']
  nlinarith

lemma marchenkoPasturTransform_equation {t α : ℝ} (ht : 0 < t) :
    marchenkoPasturResidual t α (marchenkoPasturTransform t α) = 0 := by
  have hp := marchenkoPasturTransform_polynomial (α := α) ht
  have hm := marchenkoPasturTransform_pos (α := α) ht
  unfold marchenkoPasturResidual
  apply (sub_eq_zero.mpr ?_)
  rw [← mul_div_assoc]
  apply (eq_div_iff (by linarith : 1+marchenkoPasturTransform t α ≠ 0)).mpr
  nlinarith

lemma nonnegative_fraction_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    u/(1+u) ≤ v/(1+v) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

lemma nonnegative_fraction_lipschitz {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |u/(1+u)-v/(1+v)| ≤ |u-v| := by
  have hd : 0 < (1+u)*(1+v) := mul_pos (by linarith) (by linarith)
  have he : u/(1+u)-v/(1+v) = (u-v)/((1+u)*(1+v)) := by field_simp <;> ring
  rw [he,abs_div,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hd1 : 1 ≤ (1+u)*(1+v) := by nlinarith [mul_nonneg hu hv]
  nlinarith [abs_nonneg (u-v)]

lemma marchenkoPasturTransform_error {t α u : ℝ} (ht : 0 < t) (hα : 0 ≤ α) (hu : 0 ≤ u) :
    |u-marchenkoPasturTransform t α| ≤ |marchenkoPasturResidual t α u|/t := by
  let v := marchenkoPasturTransform t α
  have hv : 0 ≤ v := (marchenkoPasturTransform_pos ht).le
  have he : 1-t*v-α*(v/(1+v)) = 0 := marchenkoPasturTransform_equation ht
  apply (le_div_iff₀ ht).mpr
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonpos (sub_nonpos.mpr huv)]
    have hf := mul_le_mul_of_nonneg_left (nonnegative_fraction_mono hu huv) hα
    have hr : 0 ≤ marchenkoPasturResidual t α u := by
      unfold marchenkoPasturResidual
      nlinarith
    rw [abs_of_nonneg hr]
    unfold marchenkoPasturResidual
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    have hf := mul_le_mul_of_nonneg_left (nonnegative_fraction_mono hv hvu) hα
    have hr : marchenkoPasturResidual t α u ≤ 0 := by
      unfold marchenkoPasturResidual
      nlinarith
    rw [abs_of_nonpos hr]
    unfold marchenkoPasturResidual
    nlinarith

lemma marchenkoPasturResidual_coefficient {t α β u : ℝ} (hu : 0 ≤ u) :
    |marchenkoPasturResidual t α u| ≤ |marchenkoPasturResidual t β u|+|α-β| := by
  have hf : |u/(1+u)| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hu (by linarith))]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have he : marchenkoPasturResidual t α u =
      marchenkoPasturResidual t β u+(β-α)*(u/(1+u)) := by
    unfold marchenkoPasturResidual
    ring
  rw [he]
  calc
    _ ≤ |marchenkoPasturResidual t β u|+|(β-α)*(u/(1+u))| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_sub_comm β α]
      exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hf (abs_nonneg (α-β))).trans_eq (mul_one _))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResidualBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A pathwise residual bound for the finite Gaussian Gram transform equation. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

theorem gaussianGramResidual_bound {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    |marchenkoPasturResidual t ((m : ℝ)/N) (gaussianGramStieltjes t z)| ≤
      (1/(N : ℝ))*∑ j : Fin m, (gaussianGramColumnDeviation t z j+1/((N : ℝ)*t)) := by
  let u := gaussianGramStieltjes t z
  let q := fun j : Fin m => gaussianGramColumnQuadratic t z j
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 0 ≤ u := gaussianGramStieltjes_nonneg ht z
  have hq : ∀ j, 0 ≤ q j := gaussianGramColumnQuadratic_nonneg ht z
  have he := gaussianGramStieltjes_column_equation hN ht z
  have hsum : marchenkoPasturResidual t ((m : ℝ)/N) u =
      (1/(N : ℝ))*∑ j : Fin m, (q j/(1+q j)-u/(1+u)) := by
    unfold marchenkoPasturResidual
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change 1-t*u = (1/(N : ℝ))*∑ j, q j/(1+q j) at he
    rw [he]
    ring
  rw [hsum,abs_mul,abs_of_pos (one_div_pos.mpr hn)]
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr hn).le
  calc
    _ ≤ ∑ j, |q j/(1+q j)-u/(1+u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |q j-u| := Finset.sum_le_sum (fun j _ => nonnegative_fraction_lipschitz (hq j) hu)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => gaussianGramColumnQuadratic_error hN ht z j)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResidualIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundedness and integrability of the finite transform-equation residual. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma continuous_gaussianGramResidual {N m : ℕ} {t : ℝ} (ht : 0 < t) (α : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      marchenkoPasturResidual t α (gaussianGramStieltjes t z)) := by
  have hu := continuous_gaussianGramStieltjes (N := N) (m := m) ht
  apply (continuous_const.sub (continuous_const.mul hu)).sub
  apply continuous_const.mul
  exact hu.div (continuous_const.add hu) (fun z => ne_of_gt (by
    have h := gaussianGramStieltjes_nonneg ht z
    linarith))

lemma gaussianGramResidual_abs_le {N m : ℕ} {t α : ℝ} (ht : 0 < t) (hα : 0 ≤ α)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    |marchenkoPasturResidual t α (gaussianGramStieltjes t z)| ≤ 1+α := by
  let u := gaussianGramStieltjes t z
  have hu : 0 ≤ u := gaussianGramStieltjes_nonneg ht z
  have hu1 : t*u ≤ 1 := by
    have h := (le_div_iff₀ ht).mp (gaussianGramStieltjes_le ht z)
    nlinarith
  have hf : 0 ≤ u/(1+u) := div_nonneg hu (by linarith)
  have hf1 : u/(1+u) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  change |1-t*u-α*(u/(1+u))| ≤ 1+α
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hf1 hα]
  · nlinarith [mul_nonneg ht.le hu,mul_nonneg hα hf]

lemma gaussianGramResidual_abs_integrable {N m : ℕ} {t α : ℝ} (ht : 0 < t) (hα : 0 ≤ α) :
    Integrable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      |marchenkoPasturResidual t α (gaussianGramStieltjes t z)|) (stdGaussian _) := by
  apply (integrable_const (1+α)).mono'
    (continuous_gaussianGramResidual ht α).abs.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_abs]
    exact gaussianGramResidual_abs_le ht hα z)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramResidualMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit mean error bound for the actual Gaussian Gram transform equation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace InvariantIsing

lemma gaussianGramColumnDeviation_mean_le_all {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (j : Fin m) :
    (∫ g : Fin m → Fin N → ℝ, gaussianGramColumnDeviation t (gaussianColumnArray g) j
      ∂Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) ≤
      Real.sqrt (2/((N : ℝ)*t^2)) := by
  cases m with
  | zero => exact Fin.elim0 j
  | succ m => exact gaussianGramColumnDeviation_mean_le hN ht j

theorem gaussianGramResidual_mean_le {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    (∫ z : EuclideanSpace ℝ (Fin N × Fin m),
      |marchenkoPasturResidual t ((m : ℝ)/N) (gaussianGramStieltjes t z)| ∂stdGaussian _) ≤
      ((m : ℝ)/N)*(Real.sqrt (2/((N : ℝ)*t^2))+1/((N : ℝ)*t)) := by
  let μ := Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin N => gaussianReal 0 1))
  have hi (j : Fin m) : Integrable (fun g : Fin m → Fin N → ℝ =>
      gaussianGramColumnDeviation t (gaussianColumnArray g) j+1/((N : ℝ)*t)) μ :=
    (gaussianGramColumnDeviation_integrable hN ht j).add (integrable_const _)
  have hf := (gaussianColumnArray_hasLaw N m).integrable_comp
    (gaussianGramResidual_abs_integrable ht (show 0 ≤ (m : ℝ)/N by positivity))
  have hμ : IsProbabilityMeasure μ := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  rw [← (gaussianColumnArray_hasLaw N m).integral_comp
    (continuous_gaussianGramResidual ht ((m : ℝ)/N)).abs.aestronglyMeasurable]
  calc
    _ ≤ ∫ g, (1/(N : ℝ))*∑ j : Fin m,
        (gaussianGramColumnDeviation t (gaussianColumnArray g) j+1/((N : ℝ)*t)) ∂μ := by
      apply integral_mono hf ((integrable_finsetSum Finset.univ (fun j _ => hi j)).const_mul _)
      intro g
      exact gaussianGramResidual_bound hN ht (gaussianColumnArray g)
    _ = (1/(N : ℝ))*∑ j : Fin m, ∫ g,
        (gaussianGramColumnDeviation t (gaussianColumnArray g) j+1/((N : ℝ)*t)) ∂μ := by
      rw [integral_const_mul,integral_finsetSum _ (fun j _ => hi j)]
    _ ≤ (1/(N : ℝ))*∑ _ : Fin m, (Real.sqrt (2/((N : ℝ)*t^2))+1/((N : ℝ)*t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      rw [integral_add (gaussianGramColumnDeviation_integrable hN ht j) (integrable_const _)]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      exact add_le_add (gaussianGramColumnDeviation_mean_le_all hN ht j) le_rfl
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramTransformError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative mean convergence of the actual Gram resolvent to the MP equation's root. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma gaussianGramTransform_error_integrable {N m : ℕ} {t : ℝ} (ht : 0 < t) (α : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      |gaussianGramStieltjes t z-marchenkoPasturTransform t α|) (stdGaussian _) := by
  apply (integrable_const (1/t+|marchenkoPasturTransform t α|)).mono'
    ((continuous_gaussianGramStieltjes ht).sub continuous_const).abs.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs,abs_abs]
  exact (abs_sub _ _).trans (add_le_add (by
    rw [abs_of_nonneg (gaussianGramStieltjes_nonneg ht z)]
    exact gaussianGramStieltjes_le ht z) le_rfl)

theorem gaussianGramTransform_mean_error {N m : ℕ} (hN : 0 < N) {t α : ℝ}
    (ht : 0 < t) (hα : 0 ≤ α) :
    (∫ z : EuclideanSpace ℝ (Fin N × Fin m),
      |gaussianGramStieltjes t z-marchenkoPasturTransform t α| ∂stdGaussian _) ≤
      (((m : ℝ)/N)*(Real.sqrt (2/((N : ℝ)*t^2))+1/((N : ℝ)*t))+|(m : ℝ)/N-α|)/t := by
  have hi := gaussianGramResidual_abs_integrable (N := N) (m := m) ht
    (show 0 ≤ (m : ℝ)/N by positivity)
  calc
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin N × Fin m),
        (|marchenkoPasturResidual t ((m : ℝ)/N) (gaussianGramStieltjes t z)|+|(m : ℝ)/N-α|)/t
        ∂stdGaussian _ := by
      apply integral_mono (gaussianGramTransform_error_integrable ht α)
        ((hi.add (integrable_const _)).div_const t)
      intro z
      apply (marchenkoPasturTransform_error ht hα (gaussianGramStieltjes_nonneg ht z)).trans
      apply div_le_div_of_nonneg_right _ ht.le
      dsimp only [Pi.add_apply]
      simpa only [abs_sub_comm α ((m : ℝ)/N)] using
        marchenkoPasturResidual_coefficient (t := t) (α := α) (β := (m : ℝ)/N)
          (gaussianGramStieltjes_nonneg ht z)
    _ = ((∫ z : EuclideanSpace ℝ (Fin N × Fin m),
        |marchenkoPasturResidual t ((m : ℝ)/N) (gaussianGramStieltjes t z)| ∂stdGaussian _)+
        |(m : ℝ)/N-α|)/t := by
      rw [integral_div,integral_add hi (integrable_const _)]
      simp
    _ ≤ _ := div_le_div_of_nonneg_right (add_le_add (gaussianGramResidual_mean_le hN ht) le_rfl) ht.le

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianPatternAspect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual integer Gaussian pattern counts and their aspect-ratio limits. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma gaussianPatternCount_le {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
    (gaussianPatternCount α N : ℝ) ≤ α*N := by
  unfold gaussianPatternCount
  exact Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg _))

lemma gaussianPatternCount_ratio_tendsto {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun k : ℕ => (gaussianPatternCount α (k+1) : ℝ)/(k+1)) atTop (𝓝 α) := by
  have he (k : ℕ) : 0 ≤ α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) ∧
      α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) ≤ 1/(k+1) := by
    have hk : (0 : ℝ) < k+1 := by positivity
    have hl := gaussianPatternCount_le hα (k+1)
    have hu : α*(k+1) < (gaussianPatternCount α (k+1) : ℝ)+1 := by
      simpa only [gaussianPatternCount,Nat.cast_add,Nat.cast_one] using
        Nat.lt_floor_add_one (α*(k+1 : ℝ))
    have hr : α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) =
        (α*(k+1)-(gaussianPatternCount α (k+1) : ℝ))/(k+1) := by field_simp
    rw [hr]
    constructor
    · apply div_nonneg _ hk.le
      simpa only [Nat.cast_add,Nat.cast_one] using sub_nonneg.mpr hl
    · apply div_le_div_of_nonneg_right _ hk.le
      linarith
  have ht := squeeze_zero (fun k => (he k).1) (fun k => (he k).2)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := (tendsto_const_nhds (x := α)).sub ht
  simpa only [sub_zero,sub_sub_cancel] using h

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramTransformLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the actual positive Gram transforms at every positive real argument. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

lemma gaussianGramTransform_error_bound_tendsto {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    Tendsto (fun k : ℕ =>
      (((gaussianPatternCount α (k+1) : ℝ)/(k+1))*(Real.sqrt (2/((k+1 : ℝ)*t^2))+
        1/((k+1 : ℝ)*t))+|(gaussianPatternCount α (k+1) : ℝ)/(k+1)-α|)/t)
      atTop (𝓝 0) := by
  have hn : Tendsto (fun k : ℕ => (k+1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hq : Tendsto (fun k : ℕ => (2 : ℝ)/((k+1 : ℝ)*t^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.atTop_mul_const (sq_pos_of_pos ht))
  have hr : Tendsto (fun k : ℕ => (1 : ℝ)/((k+1 : ℝ)*t)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.atTop_mul_const ht)
  have hs := (Real.continuous_sqrt.tendsto 0).comp hq
  have ha := gaussianPatternCount_ratio_tendsto hα
  simpa only [Function.comp_def,Real.sqrt_zero,mul_zero,add_zero,zero_add,sub_self,abs_zero,zero_div] using
    ((ha.mul (hs.add hr)).add ((ha.sub (tendsto_const_nhds (x := α))).abs)).div_const t

theorem gaussianGramTransform_mean_tendsto {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    Tendsto (fun k : ℕ => ∫ z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))),
      |gaussianGramStieltjes t z-marchenkoPasturTransform t α| ∂stdGaussian _) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun k => ?_) (gaussianGramTransform_error_bound_tendsto hα ht)
  simpa only [Nat.cast_add,Nat.cast_one] using gaussianGramTransform_mean_error
    (N := k+1) (m := gaussianPatternCount α (k+1)) (Nat.succ_pos k) ht hα

theorem gaussianPatternStieltjes_L1 {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    Tendsto (fun k : ℕ => ∫ ω, |gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α| ∂P)
      atTop (𝓝 0) := by
  have he (k : ℕ) : (∫ ω, |gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α| ∂P) =
      ∫ z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))),
        |gaussianGramStieltjes t z-marchenkoPasturTransform t α| ∂stdGaussian _ := by
    simpa only [Function.comp_def,Pi.sub_apply] using (hZ (k+1)).integral_comp
      (((continuous_gaussianGramStieltjes ht).sub continuous_const).abs.aestronglyMeasurable)
  simp_rw [he]
  exact gaussianGramTransform_mean_tendsto hα ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Gaussian_GaussianGramTransformProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence in probability of the physical Gaussian Gram resolvents. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace InvariantIsing

theorem gaussianPatternStieltjes_tendsto_oai {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => gaussianGramStieltjes t (Z (k+1) ω)) atTop
      (fun _ => marchenkoPasturTransform t α) := by
  have hi (k : ℕ) : Integrable (fun ω =>
      gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α) P := by
    have hm : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
          gaussianGramStieltjes t z-marchenkoPasturTransform t α) (stdGaussian _) :=
      ((continuous_gaussianGramStieltjes (N := k+1)
      (m := gaussianPatternCount α (k+1)) ht).sub continuous_const).aestronglyMeasurable
    have hh : Integrable (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
        gaussianGramStieltjes t z-marchenkoPasturTransform t α) (stdGaussian _) :=
      (integrable_norm_iff hm).mp (by
        simpa only [Real.norm_eq_abs] using gaussianGramTransform_error_integrable ht α)
    exact (hZ (k+1)).integrable_comp hh
  have he (k : ℕ) : eLpNorm ((fun ω => gaussianGramStieltjes t (Z (k+1) ω))-
      (fun _ => marchenkoPasturTransform t α)) 1 P =
      ENNReal.ofReal (∫ ω, |gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α| ∂P) := by
    change eLpNorm (fun ω => gaussianGramStieltjes t (Z (k+1) ω)-marchenkoPasturTransform t α) 1 P = _
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi k)]
    simp only [Real.norm_eq_abs]
  apply tendstoInMeasure_of_tendsto_eLpNorm (hf := fun k => by first | exact ((hi k).aestronglyMeasurable.add (aestronglyMeasurable_const (b := marchenkoPasturTransform t α))).congr (Filter.Eventually.of_forall fun ω => by simp) | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  simpa only [he,ENNReal.ofReal_zero,Function.comp_def] using
    (ENNReal.continuous_ofReal.tendsto 0).comp (gaussianPatternStieltjes_L1 hα ht P Z hZ)

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.gaussianPatternStieltjes_tendsto_oai.{u_1} := @OAI.InvariantIsing.gaussianPatternStieltjes_tendsto_oai.{u_1}
