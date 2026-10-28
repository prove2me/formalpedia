-- Prove2me | solution 1 for OAI.CoulombAtom.actual_shell_number
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:44:13.063567+00:00
-- url     : https://prove2.me/submissions/e975bb8a-8589-4d7a-94d2-f7723b5985b1

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakDerivative
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section WeakDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]

variable [IsLocallyFiniteMeasure (volume : Measure E)]

lemma IsWeakDerivative.unique {v : E} {f g g' : E → ℂ}
    (h : IsWeakDerivative v f g) (h' : IsWeakDerivative v f g')
    (hg : MemLp g 2) (hg' : MemLp g' 2) : g =ᵐ[volume] g' := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (hg.locallyIntegrable (by norm_num)) (hg'.locallyIntegrable (by norm_num))
  intro φ hφ hcφ
  have hh := neg_injective ((h φ hφ hcφ).symm.trans (h' φ hφ hcφ))
  simpa only [Complex.real_smul, mul_comm] using hh

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma weakGraphValue_injective (v : ι → E) : Function.Injective (weakGraphValue v) := by
  intro F G hFG
  apply Subtype.ext
  apply PiLp.ext
  intro j
  cases j with
  | none => exact hFG
  | some i =>
    have hF := (mem_weakGraph v F).mp F.property i
    have hG := (mem_weakGraph v G).mp G.property i
    have hv : (F.val none : E → ℂ) =ᵐ[volume] (G.val none : E → ℂ) := by
      change F.val none = G.val none at hFG
      rw [hFG]
    have hF' := hF.congr_ae hv (EventuallyEq.refl _ _)
    exact Lp.ext (hF'.unique hG (Lp.memLp _) (Lp.memLp _))

end WeakDerivative

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakChangeVariables
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

lemma sectorGraphValue_injective (N : ℕ) : Function.Injective (sectorGraphValue N) := by
  intro F G hFG
  apply PiLp.ext
  intro s
  apply weakGraphValue_injective (sectorDirections N)
  exact congrArg (fun h : SectorHilbert N => h s) hFG

lemma fermionGraphValue_injective (N : ℕ) : Function.Injective (fermionGraphValue N) := by
  intro F G hFG
  apply Subtype.ext
  apply sectorGraphValue_injective N
  exact congrArg Subtype.val hFG

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FermionicDensity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

lemma sectorGraphPermutation_value {N : ℕ} (π : Equiv.Perm (Fin N)) (F : SectorGraph N) :
    sectorGraphValue N (sectorGraphPermutation π F) = fermionPermutation π (sectorGraphValue N F) := by
  rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_FullCoulomb
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

lemma gram_inner {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : V →L[ℂ] H) (u : V) : (⟪u, T.adjoint.comp T u⟫_ℂ).re = ‖T u‖ ^ 2 := by
  rw [ContinuousLinearMap.comp_apply, T.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

lemma graphNuclear_norm_sq {N : ℕ} (s : Spins N) (i : Fin N) (F : fermionGraph N) :
    ‖graphNuclear s i F‖ ^ 2 = ∫ x, ‖(graphFormVector F).value s x‖ ^ 2 / ‖x i‖ :=
  rootCoulombLp_norm_sq (sectorDirections N) (ContinuousLinearMap.proj i) (fun a => (i, a))
    (by intro a; simp [sectorDirections, direction]) (F.val s)

lemma graphPair_norm_sq {N : ℕ} (s : Spins N) (i j : Fin N) (hij : i ≠ j) (F : fermionGraph N) :
    ‖graphPair s i j hij F‖ ^ 2 = ∫ x, ‖(graphFormVector F).value s x‖ ^ 2 / ‖x i - x j‖ :=
  rootCoulombLp_norm_sq (sectorDirections N) (electronProjection i - electronProjection j)
    (fun a => (i, a)) (by
      intro a
      change direction i a i - direction i a j = EuclideanSpace.single a 1
      simp [direction, Ne.symm hij]) (F.val s)

attribute [local irreducible] graphComponent graphNuclear graphPair

lemma coulombFormOperator_inner (Z : ℝ) (N : ℕ) (F : fermionGraph N) :
    (⟪F, coulombFormOperator Z N F⟫_ℂ).re = formEnergy Z (graphFormVector F) := by
  have ht : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  unfold coulombFormOperator formEnergy
  simp only [ht, add_apply, sub_apply, smul_apply, sum_apply, inner_add_right, inner_sub_right,
    inner_smul_right, inner_sum, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
  simp only [gram_inner, graphNuclear_norm_sq]
  congr 1
  · congr 1
    congr 1
    simp only [lp_norm_sq, graphComponent_apply, graphFormVector]
  · apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · rw [gram_inner, graphPair_norm_sq]
    · simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoulombCoercivity

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

end CoulombCoercivity

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_IteratedReduction
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution


open Filter
open scoped Topology InnerProductSpace

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace

lemma complex_ims_identity (p d : ℝ) (a b : ℂ) :
    ‖(p : ℂ) * a + (d : ℂ) * b‖ ^ 2 -
      (⟪(p : ℂ) * ((p : ℂ) * a + (d : ℂ) * b) +
        (d : ℂ) * ((p : ℂ) * b), a⟫_ℂ).re = d ^ 2 * ‖b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, RCLike.inner_apply,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_L2
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
namespace CoulombAtom
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma l2_norm_sq (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  rw [integral_ofReal]
  rfl

lemma l2_inner_re (f g : Lp ℂ 2 μ) :
    (⟪f, g⟫_ℂ).re = ∫ x, (⟪f x, g x⟫_ℂ).re ∂μ := by
  rw [L2.inner_def]
  exact (integral_re (L2.integrable_inner (𝕜 := ℂ) f g)).symm

lemma l2_multiplier_pairing (p : α → ℝ) (f g h : Lp ℂ 2 μ)
    (hg : (g : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * f x)
    (hh : (h : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * g x) :
    (⟪h, f⟫_ℂ).re = ‖g‖ ^ 2 := by
  rw [l2_inner_re, l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hg, hh] with x hx hy
  rw [hy, hx]
  simp only [Complex.sq_norm, Complex.normSq_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma l2_ims_identity (p d : α → ℝ) (a b v w : Lp ℂ 2 μ)
    (hv : (v : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * a x + (d x : ℂ) * b x)
    (hw : (w : α → ℂ) =ᵐ[μ] fun x => (p x : ℂ) * v x +
      (d x : ℂ) * ((p x : ℂ) * b x)) :
    ‖v‖ ^ 2 - (⟪w, a⟫_ℂ).re = ∫ x, (d x) ^ 2 * ‖b x‖ ^ 2 ∂μ := by
  rw [l2_norm_sq, l2_inner_re]
  have hi : Integrable (fun x => ‖v x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp v).aestronglyMeasurable).mp (Lp.memLp v)
  have hj : Integrable (fun x => (⟪w x, a x⟫_ℂ).re) μ :=
    (L2.integrable_inner (𝕜 := ℂ) w a).re
  rw [← integral_sub hi hj]
  apply integral_congr_ae
  filter_upwards [hv, hw] with x hx hy
  rw [hy, hx]
  exact complex_ims_identity (p x) (d x) (a x) (b x)

end CoulombAtom

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Multiplier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
namespace CoulombAtom
section Multiplier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma SmoothMultiplier.apply_gradient {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) (i : ι) :
    ((p.apply F).val (some i) : E → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * F.val (some i) x +
        Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x :=
  (p.gradient_memLp F i).coeFn_toLp

end Multiplier

lemma FermionMultiplier.apply_value {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (graphComponent s none (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s none F x :=
  p.toSmoothMultiplier.apply_value (F.val s)

lemma graphNuclear_ae {N : ℕ} (s : Spins N) (i : Fin N) (F : fermionGraph N) :
    (graphNuclear s i F : Configuration N → ℂ) =ᵐ[volume]
      fun x => graphComponent s none F x / (Real.sqrt ‖x i‖ : ℂ) := by
  exact (rootCoulombFn_memLp (sectorDirections N) (ContinuousLinearMap.proj i)
    (fun a => (i, a)) (by intro a; simp [sectorDirections, direction]) (F.val s)).coeFn_toLp

lemma graphPair_ae {N : ℕ} (s : Spins N) (i j : Fin N) (hij : i ≠ j)
    (F : fermionGraph N) :
    (graphPair s i j hij F : Configuration N → ℂ) =ᵐ[volume]
      fun x => graphComponent s none F x / (Real.sqrt ‖x i - x j‖ : ℂ) := by
  exact (rootCoulombFn_memLp (sectorDirections N) (electronProjection i - electronProjection j)
    (fun a => (i, a)) (by
      intro a
      change direction i a i - direction i a j = EuclideanSpace.single a 1
      simp [direction, Ne.symm hij]) (F.val s)).coeFn_toLp

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

lemma FermionMultiplier.apply_nuclear {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (graphNuclear s i (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphNuclear s i F x := by
  filter_upwards [graphNuclear_ae s i (p.apply F), graphNuclear_ae s i F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma FermionMultiplier.apply_pair {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (graphPair s i j hij (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphPair s i j hij F x := by
  filter_upwards [graphPair_ae s i j hij (p.apply F), graphPair_ae s i j hij F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma coulombFormOperator_pairing (Z : ℝ) (N : ℕ) (F G : fermionGraph N) :
    (⟪G, coulombFormOperator Z N F⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i, a)) G, graphComponent s (some (i, a)) F⟫_ℂ).re) -
      Z * (∑ s : Spins N, ∑ i : Fin N,
        (⟪graphNuclear s i G, graphNuclear s i F⟫_ℂ).re) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
        if hij : i < j then (⟪graphPair s i j (ne_of_lt hij) G,
          graphPair s i j (ne_of_lt hij) F⟫_ℂ).re else 0) := by
  have ht : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  unfold coulombFormOperator
  simp only [ht, add_apply, sub_apply, smul_apply, sum_apply, inner_add_right, inner_sub_right,
    inner_smul_right, inner_sum, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [ContinuousLinearMap.adjoint_inner_right]

attribute [local irreducible] fermionGraphValue coulombFormOperator

lemma graphValue_pairing {N : ℕ} (F G : fermionGraph N) :
    (⟪fermionGraphValue N G, fermionGraphValue N F⟫_ℂ).re =
      ∑ s : Spins N, (⟪graphComponent s none G, graphComponent s none F⟫_ℂ).re := by
  change (⟪(fermionGraphValue N G).val, (fermionGraphValue N F).val⟫_ℂ).re = _
  have hi := PiLp.inner_apply (𝕜 := ℂ)
    (x := (fermionGraphValue N G).val) (y := (fermionGraphValue N F).val)
  have he := congrArg Complex.re hi
  rw [Complex.re_sum] at he
  have hc (U : fermionGraph N) (s : Spins N) :
      (fermionGraphValue N U).val s = graphComponent s none U := by
    unfold fermionGraphValue graphComponent
    rfl
  simpa only [hc] using he

attribute [local irreducible] formEnergy graphFormVector

lemma coulombFormOperator_diagonal (Z : ℝ) (N : ℕ) (G : fermionGraph N) :
    (⟪G, coulombFormOperator Z N G⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ‖graphComponent s (some (i, a)) G‖ ^ 2) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i G‖ ^ 2) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
        if hij : i < j then ‖graphPair s i j (ne_of_lt hij) G‖ ^ 2 else 0) := by
  rw [coulombFormOperator_pairing Z N G G]
  have hs (u : Lp ℂ 2 (volume : Measure (Configuration N))) :
      (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  simp only [hs]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Multiplier2
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom
section Multiplier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma LipschitzMultiplier.apply_gradient {v : ι → E} (p : LipschitzMultiplier v)
    (F : weakGraph v) (i : ι) :
    ((p.apply F).val (some i) : E → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * F.val (some i) x +
        Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x :=
  (p.gradient_memLp F i).coeFn_toLp

end Multiplier

lemma FermionLipschitzMultiplier.apply_value {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (graphComponent s none (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s none F x :=
  p.toLipschitzMultiplier.apply_value (F.val s)

lemma FermionLipschitzMultiplier.apply_gradient {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphComponent s (some (i, a)) (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s (some (i, a)) F x +
        Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * graphComponent s none F x :=
  p.toLipschitzMultiplier.apply_gradient (F.val s) (i, a)

attribute [local irreducible] graphNuclear graphPair graphComponent FermionLipschitzMultiplier.apply

lemma FermionLipschitzMultiplier.apply_nuclear {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (graphNuclear s i (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphNuclear s i F x := by
  filter_upwards [graphNuclear_ae s i (p.apply F), graphNuclear_ae s i F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma FermionLipschitzMultiplier.apply_pair {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (graphPair s i j hij (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphPair s i j hij F x := by
  filter_upwards [graphPair_ae s i j hij (p.apply F), graphPair_ae s i j hij F,
    p.apply_value F s] with x hx hy hz
  exact hx.trans ((congrArg (fun z : ℂ => z / _) hz).trans
    ((mul_div_assoc (p.value x : ℂ) _ _).trans (congrArg (fun z : ℂ => (p.value x : ℂ) * z) hy.symm)))

lemma FermionLipschitzMultiplier.gradient_ims {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    ‖graphComponent s (some (i, a)) (p.apply F)‖ ^ 2 -
      (⟪graphComponent s (some (i, a)) (p.apply (p.apply F)),
        graphComponent s (some (i, a)) F⟫_ℂ).re =
      ∫ x, (lineDeriv ℝ p.value x (direction i a)) ^ 2 *
        ‖graphComponent s none F x‖ ^ 2 := by
  apply l2_ims_identity p.value (fun x => lineDeriv ℝ p.value x (direction i a))
    (graphComponent s (some (i, a)) F) (graphComponent s none F)
  · exact p.apply_gradient F s i a
  · filter_upwards [p.apply_gradient (p.apply F) s i a, p.apply_value F s] with x hx hy
    exact hx.trans (congrArg (fun z : ℂ =>
      (p.value x : ℂ) * graphComponent s (some (i, a)) (p.apply F) x +
        Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * z) hy)

lemma FermionLipschitzMultiplier.value_pairing {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) :
    (⟪fermionGraphValue N (p.apply (p.apply F)), fermionGraphValue N F⟫_ℂ).re =
      ‖fermionGraphValue N (p.apply F)‖ ^ 2 := by
  rw [graphValue_pairing, graphValue_norm_sq]
  apply Finset.sum_congr rfl
  intro s _
  exact l2_multiplier_pairing p.value (graphComponent s none F)
    (graphComponent s none (p.apply F)) (graphComponent s none (p.apply (p.apply F)))
    (p.apply_value F s) (p.apply_value (p.apply F) s)

attribute [local irreducible] formEnergy graphFormVector fermionGraphValue coulombFormOperator

lemma FermionLipschitzMultiplier.nuclear_pairing {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (⟪graphNuclear s i (p.apply (p.apply F)), graphNuclear s i F⟫_ℂ).re =
      ‖graphNuclear s i (p.apply F)‖ ^ 2 :=
  l2_multiplier_pairing p.value _ _ _ (p.apply_nuclear F s i)
    (p.apply_nuclear (p.apply F) s i)

lemma FermionLipschitzMultiplier.pair_pairing {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (⟪graphPair s i j hij (p.apply (p.apply F)), graphPair s i j hij F⟫_ℂ).re =
      ‖graphPair s i j hij (p.apply F)‖ ^ 2 :=
  l2_multiplier_pairing p.value _ _ _ (p.apply_pair F s i j hij)
    (p.apply_pair (p.apply F) s i j hij)

lemma FermionLipschitzMultiplier.kinetic_ims {N : ℕ} (p : FermionLipschitzMultiplier N)
    (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ‖graphComponent s (some (i, a)) (p.apply F)‖ ^ 2) -
    (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      (⟪graphComponent s (some (i, a)) (p.apply (p.apply F)),
        graphComponent s (some (i, a)) F⟫_ℂ).re) =
    ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x, (lineDeriv ℝ p.value x (direction i a)) ^ 2 *
        ‖graphComponent s none F x‖ ^ 2 := by
  simp only [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun a _ => p.gradient_ims F s i a

lemma FermionLipschitzMultiplier.operator_pairing {N : ℕ} (p : FermionLipschitzMultiplier N)
    (Z : ℝ) (F : fermionGraph N) :
    (⟪p.apply (p.apply F), coulombFormOperator Z N F⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i, a)) (p.apply (p.apply F)),
          graphComponent s (some (i, a)) F⟫_ℂ).re) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i (p.apply F)‖ ^ 2) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
        if hij : i < j then ‖graphPair s i j (ne_of_lt hij) (p.apply F)‖ ^ 2 else 0) := by
  calc
    _ = _ := coulombFormOperator_pairing Z N F (p.apply (p.apply F))
    _ = _ := by simp only [p.nuclear_pairing, p.pair_pairing]

private lemma lipschitz_ims_arithmetic (K L A B R : ℝ) (h : K - L = R) :
    (1 / 2 * K - A + B) - (1 / 2 * L - A + B) = 1 / 2 * R := by
  rw [← h]
  ring

lemma FermionLipschitzMultiplier.form_ims {N : ℕ} (p : FermionLipschitzMultiplier N)
    (Z : ℝ) (F : fermionGraph N) :
    formEnergy Z (graphFormVector (p.apply F)) -
      (⟪p.apply (p.apply F), coulombFormOperator Z N F⟫_ℂ).re =
      (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, (lineDeriv ℝ p.value x (direction i a)) ^ 2 *
          ‖graphComponent s none F x‖ ^ 2) := by
  calc
    _ = _ := congrArg (fun t : ℝ => t -
      (⟪p.apply (p.apply F), coulombFormOperator Z N F⟫_ℂ).re)
        (coulombFormOperator_inner Z N (p.apply F)).symm
    _ = _ := congrArg₂ (fun a b : ℝ => a - b)
      (coulombFormOperator_diagonal Z N (p.apply F)) (p.operator_pairing Z F)
    _ = _ := lipschitz_ims_arithmetic _ _ _ _ _ (p.kinetic_ims F)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_SqrtMultiplier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SqrtMultiplier_scope

open Filter Set
open scoped Topology NNReal

lemma lineDeriv_sqrt_of_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hx : 0 < f x) (v : E) :
    lineDeriv ℝ (fun y => Real.sqrt (f y)) x v =
      (fderiv ℝ f x v)/(2*Real.sqrt (f x)) := by
  rw [((hf.hasFDerivAt.sqrt (ne_of_gt hx)).hasLineDerivAt v).lineDeriv]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma lineDeriv_sqrt_of_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (_hn : ∀ x, 0 ≤ f x) {x : E} (hx : f x = 0) (v : E) :
    lineDeriv ℝ (fun y => Real.sqrt (f y)) x v = 0 := by
  have hm : IsLocalMin (fun y => Real.sqrt (f y)) x := by
    apply Filter.Eventually.of_forall
    intro y
    change Real.sqrt (f x) ≤ Real.sqrt (f y)
    rw [hx, Real.sqrt_zero]
    exact Real.sqrt_nonneg _
  exact congrFun hm.lineDeriv_eq_zero v

end Work_SqrtMultiplier_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_MultiplierError
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
namespace CoulombAtom

lemma graph_value_components_ext {N : ℕ} {F G : fermionGraph N}
    (h : ∀ s, graphComponent s none F = graphComponent s none G) : F = G := by
  apply fermionGraphValue_injective N
  apply Subtype.ext
  apply PiLp.ext
  intro s
  exact h s

attribute [local irreducible] FermionMultiplier.apply graphComponent
  fermionGraphValue coulombFormOperator graphFormVector formEnergy

end CoulombAtom

open MeasureTheory Filter Set
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_LipschitzResidualBase
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LipschitzResidualBase_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

lemma sectorExcessOperator_pair {N : ℕ} (Z : ℝ) (G F : fermionGraph N) :
    (⟪G,sectorExcessOperator Z N F⟫_ℂ).re =
      (⟪G,coulombFormOperator Z N F⟫_ℂ).re-
        energy Z N*(⟪fermionGraphValue N G,fermionGraphValue N F⟫_ℂ).re := by
  simp only [sectorExcessOperator,sub_apply,
    smul_apply,inner_sub_right,inner_smul_right,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

attribute [local irreducible] sectorExcessOperator

end Work_LipschitzResidualBase_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionLipschitzMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Slices
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

theorem SobolevFermion.ae_coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (t : Spins M) :
    ∀ᵐ y, SobolevFermion (coreSlice ψ t y) := by
  have hv (s : Spins N) : ∀ᵐ y, MemLp ((coreSlice ψ t y).value s) 2 := by
    have hh := (hψ.1 (joinLists s t)).comp_measurePreserving (configurationJoin_preserving N M)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using memLp_slice_left hh
  have hg (s : Spins N) (i : Fin N) (a : Fin 3) :
      ∀ᵐ y, MemLp ((coreSlice ψ t y).gradient s i a) 2 := by
    have hh := (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).comp_measurePreserving
      (configurationJoin_preserving N M)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using memLp_slice_left hh
  have hw (s : Spins N) (i : Fin N) (a : Fin 3) :
      ∀ᵐ y, IsWeakDerivative (direction i a) ((coreSlice ψ t y).value s)
        ((coreSlice ψ t y).gradient s i a) := by
    have hh := (hψ.2.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).pullback
      (configurationJoin N M) (configurationJoin_preserving N M) (configurationJoin_direction i a)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using hh.slice_left
      ((hψ.1 (joinLists s t)).comp_measurePreserving (configurationJoin_preserving N M))
      ((hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).comp_measurePreserving
        (configurationJoin_preserving N M))
  have ha (π : Equiv.Perm (Fin N)) (s : Spins N) : ∀ᵐ y, ∀ᵐ x,
      (coreSlice ψ t y).value (s ∘ π) (x ∘ π) =
        (((Equiv.Perm.sign π : ℤ) : ℂ) * (coreSlice ψ t y).value s x) := by
    have hh := (configurationJoin_preserving N M).quasiMeasurePreserving.ae
      (hψ.2.2.2 (corePerm M π) (joinLists s t))
    have hh' : ∀ᵐ z : Configuration N × Configuration M,
        (coreSlice ψ t z.2).value (s ∘ π) (z.1 ∘ π) =
          (((Equiv.Perm.sign π : ℤ) : ℂ) * (coreSlice ψ t z.2).value s z.1) := by
      filter_upwards [hh] with z hz
      rcases z with ⟨x,y⟩
      simpa only [configurationJoin_apply, joinLists_corePerm, corePerm_sign, coreSlice] using hz
    rw [Measure.volume_eq_prod] at hh'
    exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hh')

  filter_upwards [ae_all_iff.mpr hv, ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun i => ae_all_iff.mpr (hg s i))), ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun i => ae_all_iff.mpr (hw s i))), ae_all_iff.mpr (fun π => ae_all_iff.mpr (ha π))]
    with y hyv hyg hyw hya
  exact ⟨hyv,hyg,hyw,hya⟩

theorem conditional_core_energy {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (t : Spins M) {Z : ℝ} (hZ : 0 ≤ Z) :
    ∀ᵐ y, energy Z N * formMass (coreSlice ψ t y) ≤ formEnergy Z (coreSlice ψ t y) :=
  (hψ.ae_coreSlice t).mono fun _ hy => hy.energy_mul_mass_le hZ


open Set Filter Topology InnerProductSpace Laplacian

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinJoinEquiv
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace CoulombAtom

lemma coreSlice_mass_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (t : Spins M) :
    Integrable (fun y => formMass (coreSlice ψ t y)) := by
  apply integrable_finsetSum
  intro s _
  simpa only [coreSlice] using
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).integral_prod_right

lemma coreSlice_energy_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) (Z : ℝ) (t : Spins M) :
    Integrable (fun y => formEnergy Z (coreSlice ψ t y)) := by
  have hk (s : Spins N) (i : Fin N) (a : Fin 3) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).gradient s i a x‖ ^ 2) := by
    exact (integrable_join (N := N) (M := M)
      (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).norm.integrable_sq).integral_prod_right
  have hn (s : Spins N) (i : Fin N) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖ ^ 2 / ‖x i‖) := by
    have hh := (integrable_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2.1 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  have hp (s : Spins N) (i j : Fin N) (hij : i < j) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖ ^ 2 / ‖x i-x j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun he => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective he))
    have hh := (integrable_join (N := N) (M := M)
      (pair_integrable (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) hne
        (hψ.1 (joinLists s t)) (hψ.2.1 (joinLists s t) _) (hψ.2.2.1 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  unfold formEnergy
  apply Integrable.add
  · apply Integrable.sub
    · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun a _ => hk s i a)))).const_mul _
    · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
        hn s i))).const_mul _
  · apply integrable_finsetSum; intro s _
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp s i j hij
    · exact integrable_zero _ _ _

theorem weighted_core_energy {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) {Z : ℝ} (hZ : 0 ≤ Z)
    (w : Configuration M → ℝ) (hw : AEStronglyMeasurable w)
    (hw0 : ∀ᵐ y, 0 ≤ w y) {C : ℝ} (hwC : ∀ᵐ y, ‖w y‖ ≤ C) :
    energy Z N * (∑ t : Spins M, ∫ y, w y * formMass (coreSlice ψ t y)) ≤
      ∑ t : Spins M, ∫ y, w y * formEnergy Z (coreSlice ψ t y) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← integral_const_mul]
  apply integral_mono_ae (((coreSlice_mass_integrable hψ t).bdd_mul hw hwC).const_mul _)
    ((coreSlice_energy_integrable hψ Z t).bdd_mul hw hwC)
  filter_upwards [conditional_core_energy hψ t hZ, hw0] with y hy hy0
  simpa only [mul_left_comm (energy Z N) (w y)] using
    mul_le_mul_of_nonneg_left hy hy0

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_ApproximateEventTilt
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom
open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

lemma quantum_lipschitz_ims_residual {N : ℕ} (Z : ℝ) (F : fermionGraph N)
    (p : FermionLipschitzMultiplier N) :
    formEnergy Z (graphFormVector (p.apply F)) -
      energy Z N * ‖fermionGraphValue N (p.apply F)‖^2 =
      (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, (lineDeriv ℝ p.value x (direction i a))^2 *
          ‖graphComponent s none F x‖^2) +
        (⟪p.apply (p.apply F), sectorExcessOperator Z N F⟫_ℂ).re := by
  have hi := FermionLipschitzMultiplier.form_ims (N := N) p Z F
  have hr := sectorExcessOperator_pair Z (p.apply (p.apply F)) F
  have hr' := hr.trans (congrArg (fun u : ℝ =>
    (⟪p.apply (p.apply F),coulombFormOperator Z N F⟫_ℂ).re-energy Z N*u)
    (FermionLipschitzMultiplier.value_pairing (N := N) p F))
  linarith only [hr',hi]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ActualMasterCenterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma graphFormVector_sobolev {N : ℕ} (F : fermionGraph N) :
    SobolevFermion (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_⟩
  · intro s i a
    exact (mem_weakGraph _ _).mp (F.val s).property (i,a)
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s

lemma formMass_graph {N : ℕ} (F : fermionGraph N) :
    formMass (graphFormVector F) = ‖fermionGraphValue N F‖^2 := by
  rw [←formRawDensity_integral (graphFormVector_sobolev F).sobolevVector]
  exact graphRawDensity_integral F

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingBase
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators

section

lemma sectorGraphPermutation_fixed {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) : sectorGraphPermutation π F.val = F.val := by
  apply sectorGraphValue_injective N
  rw [sectorGraphPermutation_value]
  exact (mem_fermionSpace _).mp F.property π

lemma sectorGraphPermutation_component {N : ℕ} (F : SectorGraph N)
    (π : Equiv.Perm (Fin N)) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    ((sectorGraphPermutation π F) s).val k = (((Equiv.Perm.sign π : ℤ) : ℂ)) •
      Lp.compMeasurePreserving (permuteConfiguration π) (permuteConfiguration_preserving π)
        ((F (s ∘ π)).val (k.map fun j => (π.symm j.1,j.2))) := rfl

lemma complex_sign_norm {N : ℕ} (π : Equiv.Perm (Fin N)) :
    ‖(((Equiv.Perm.sign π : ℤ) : ℂ))‖ = 1 := by
  have hs := congrArg norm (complex_sign_sq π)
  rw [norm_pow, norm_one] at hs
  nlinarith [norm_nonneg (((Equiv.Perm.sign π : ℤ) : ℂ))]

lemma graphComponent_permutation_norm {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    ∀ᵐ x : Configuration N, ‖graphComponent (s ∘ π)
      (k.map fun j => (π.symm j.1,j.2)) F (x ∘ π)‖ = ‖graphComponent s k F x‖ := by
  have he := congrArg (fun G : SectorGraph N => (G s).val k)
    (sectorGraphPermutation_fixed F π)
  rw [sectorGraphPermutation_component] at he
  have ha := Lp.coeFn_smul (((Equiv.Perm.sign π : ℤ) : ℂ))
    (Lp.compMeasurePreserving (permuteConfiguration π) (permuteConfiguration_preserving π)
      ((F.val (s ∘ π)).val (k.map fun j => (π.symm j.1,j.2))))
  have hb := Lp.coeFn_compMeasurePreserving
    ((F.val (s ∘ π)).val (k.map fun j => (π.symm j.1,j.2))) (permuteConfiguration_preserving π)
  rw [he] at ha
  filter_upwards [ha, hb] with x hx hy
  simp only [graphComponent_apply]
  rw [hx, Pi.smul_apply, norm_smul, complex_sign_norm, one_mul, hy]
  simp only [Function.comp_apply, permuteConfiguration_apply]

lemma graphComponent_permutation_integral {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (s : Spins N) (k : Option (Fin N × Fin 3))
    (w : Configuration N → ℝ) :
    (∫ x, w x * ‖graphComponent (s ∘ π) (k.map fun j => (π.symm j.1,j.2)) F x‖ ^ 2) =
      ∫ x, w (x ∘ π) * ‖graphComponent s k F x‖ ^ 2 := by
  rw [← (permuteConfiguration_preserving π).integral_comp
    (permuteConfiguration π).toHomeomorph.measurableEmbedding
    (fun x => w x * ‖graphComponent (s ∘ π) (k.map fun j => (π.symm j.1,j.2)) F x‖ ^ 2)]
  apply integral_congr_ae
  filter_upwards [graphComponent_permutation_norm F π s k] with x hx
  simp only [permuteConfiguration_apply, hx]

lemma sum_spins_permutation {N : ℕ} (π : Equiv.Perm (Fin N)) (f : Spins N → ℝ) :
    (∑ s : Spins N, f (s ∘ π)) = ∑ s, f s := by
  let e : Spins N ≃ Spins N :=
    { toFun := fun s => s ∘ π
      invFun := fun s => s ∘ π.symm
      left_inv := fun s => by funext i; simp
      right_inv := fun s => by funext i; simp }
  exact Equiv.sum_comp e f

lemma graphComponent_permutation_sum_integral {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (k : Option (Fin N × Fin 3))
    (w : Configuration N → ℝ) :
    (∑ s : Spins N, ∫ x, w x *
      ‖graphComponent s (k.map fun j => (π.symm j.1,j.2)) F x‖ ^ 2) =
      ∑ s : Spins N, ∫ x, w (x ∘ π) * ‖graphComponent s k F x‖ ^ 2 := by
  rw [← sum_spins_permutation π (fun s => ∫ x, w x *
    ‖graphComponent s (k.map fun j => (π.symm j.1,j.2)) F x‖ ^ 2)]
  exact Finset.sum_congr rfl (fun s _ => graphComponent_permutation_integral F π s k w)

lemma SobolevFermion.quantumEnergyDensity_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N) :
    Integrable (quantumEnergyDensity Z ψ s) := by
  classical
  have hn (i : Fin N) := nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)
  have hp (i j : Fin N) (hij : i ≠ j) := pair_integrable i j hij (hψ.1 s)
    (hψ.2.1 s i) (hψ.2.2.1 s i)
  apply Integrable.add
  · exact ((integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun a _ => (hψ.2.1 s i a).norm.integrable_sq))).const_mul _).sub
      ((integrable_finsetSum _ (fun i _ => hn i)).const_mul _)
  · apply Integrable.const_mul
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp i j hij
    · exact integrable_zero _ _ _

lemma formEnergy_eq_density {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ) (Z : ℝ) :
    formEnergy Z ψ = ∑ s, ∫ x, quantumEnergyDensity Z ψ s x := by
  classical
  have hn (s : Spins N) (i : Fin N) := nuclear_integrable i (hψ.1 s)
    (hψ.2.1 s i) (hψ.2.2.1 s i)
  have hp (s : Spins N) (i j : Fin N) : Integrable (fun x =>
      if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) := by
    split_ifs with hij
    · exact pair_integrable i j hij (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)
    · exact integrable_zero _ _ _
  have hk (s : Spins N) := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun a _ => (hψ.2.1 s i a).norm.integrable_sq))
  have hns (s : Spins N) := integrable_finsetSum Finset.univ (fun i _ => hn s i)
  have hps (s : Spins N) := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hp s i j))
  have he (s : Spins N) : (∫ x, quantumEnergyDensity Z ψ s x) =
      (1/2:ℝ) * (∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∑ i, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖) +
      (1/2:ℝ) * (∑ i, ∑ j, ∫ x,
        if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) := by
    unfold quantumEnergyDensity
    have hsum := integral_add (((hk s).const_mul (1/2:ℝ)).sub ((hns s).const_mul Z))
      ((hps s).const_mul (1/2:ℝ))
    have hsub := integral_sub ((hk s).const_mul (1/2:ℝ)) ((hns s).const_mul Z)
    simp only [Pi.sub_apply] at hsum hsub
    rw [hsum, hsub]
    simp only [integral_const_mul]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ =>
      (hψ.2.1 s i a).norm.integrable_sq)), integral_finsetSum _ (fun i _ => hn s i),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hp s i j))]
    simp_rw [integral_finsetSum _ (fun a _ => (hψ.2.1 s _ a).norm.integrable_sq),
      integral_finsetSum _ (fun j _ => hp s _ j)]
  simp_rw [he]
  have hint (s : Spins N) (i j : Fin N) :
      (∫ x, if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) =
      if i ≠ j then (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖) else 0 := by
    split_ifs <;> simp
  simp_rw [hint]
  have hs (s : Spins N) (i j : Fin N) :
      (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖) =
      ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x j-x i‖ := by simp only [norm_sub_rev]
  simp_rw [← sum_pairs_half _ (hs _) ]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

lemma SobolevFermion.quantumCoreDensity_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (i : Fin N) (s : Spins N) :
    Integrable (quantumCoreDensity Z ψ i s) := by
  classical
  have hk : Integrable (fun x => ∑ j, if j ≠ i then ∑ a, ‖ψ.gradient s j a x‖ ^ 2 else 0) := by
    apply integrable_finsetSum; intro j _
    split_ifs
    · exact integrable_finsetSum _ (fun a _ => (hψ.2.1 s j a).norm.integrable_sq)
    · exact integrable_zero _ _ _
  have hn : Integrable (fun x => ∑ j, if j ≠ i then ‖ψ.value s x‖ ^ 2 / ‖x j‖ else 0) := by
    apply integrable_finsetSum; intro j _
    split_ifs
    · exact nuclear_integrable j (hψ.1 s) (hψ.2.1 s j) (hψ.2.2.1 s j)
    · exact integrable_zero _ _ _
  have hp : Integrable (fun x => ∑ j, ∑ k,
      if j ≠ i ∧ k ≠ i ∧ j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0) := by
    apply integrable_finsetSum; intro j _
    apply integrable_finsetSum; intro k _
    split_ifs with hij
    · exact pair_integrable j k hij.2.2 (hψ.1 s) (hψ.2.1 s j) (hψ.2.2.1 s j)
    · exact integrable_zero _ _ _
  exact ((hk.const_mul _).sub (hn.const_mul _)).add (hp.const_mul _)

lemma exteriorCoordinates_join {N M : ℕ} (x : Configuration N) (y : Configuration M) :
    exteriorCoordinates (joinLists x y) = y := by
  funext j
  exact joinLists_right x y j

lemma exteriorCoordinates_continuous {N M : ℕ} :
    Continuous (@exteriorCoordinates N M) := by
  apply continuous_pi; intro j
  exact continuous_apply _

lemma weighted_integral_join {N M : ℕ} {f : Configuration (N+M) → ℝ}
    (hf : Integrable f) (w : Configuration M → ℝ) (hw : Continuous w)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    (∫ y : Configuration M, w y * ∫ x : Configuration N, f (joinLists x y)) =
      ∫ z, w (exteriorCoordinates z) * f z := by
  have hg : Integrable (fun z => w (exteriorCoordinates z) * f z) :=
    hf.bdd_mul (hw.comp exteriorCoordinates_continuous).aestronglyMeasurable
      (Eventually.of_forall fun z => hwC _)
  rw [← integral_join (N := N) (M := M) hg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [exteriorCoordinates_join, integral_const_mul]

lemma weighted_sum_integral_join {N M : ℕ} {f : Spins (N+M) → Configuration (N+M) → ℝ}
    (hf : ∀ u, Integrable (f u)) (w : Configuration M → ℝ) (hw : Continuous w)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    (∑ t : Spins M, ∫ y, w y * (∑ s : Spins N, ∫ x, f (joinLists s t) (joinLists x y))) =
      ∑ u : Spins (N+M), ∫ z, w (exteriorCoordinates z) * f u z := by
  have hi (s : Spins N) (t : Spins M) :
      Integrable (fun y : Configuration M => w y * ∫ x : Configuration N,
        f (joinLists s t) (joinLists x y)) :=
    (integrable_join (hf (joinLists s t))).integral_prod_right.bdd_mul
      hw.aestronglyMeasurable (Eventually.of_forall hwC)
  simp_rw [Finset.mul_sum, integral_finsetSum _ (fun s _ => hi s _),
    weighted_integral_join (hf _) w hw hwC]
  exact sum_spin_join (fun u => ∫ z, w (exteriorCoordinates z) * f u z)

lemma quantumCoreDensity_last {N : ℕ} (Z : ℝ) (ψ : FormVector (N+1))
    (s : Spins N) (t : Spins 1) (x : Configuration N) (y : Configuration 1) :
    quantumCoreDensity Z ψ (Fin.last N) (joinLists s t) (joinLists x y) =
      quantumEnergyDensity Z (coreSlice ψ t y) s x := by
  classical
  unfold quantumCoreDensity quantumEnergyDensity
  simp only [Fin.sum_univ_castSucc, ne_eq, not_true_eq_false, ite_false, Fin.castSucc_ne_last,
    not_false_eq_true, ite_true, add_zero, and_false, and_true, Fin.castSucc_inj]
  simp only [true_and, false_and, ite_false, Finset.sum_const_zero, add_zero]
  have hl (i : Fin N) : joinLists x y i.castSucc = x i := joinLists_left x y i
  simp only [hl, coreSlice, finSumFinEquiv_apply_left]
  rfl

lemma coreSlice_energy_weighted_reconstruction {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : SobolevFermion ψ) (Z : ℝ) (w : Configuration 1 → ℝ) (hw : Continuous w)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    (∑ t : Spins 1, ∫ y, w y * formEnergy Z (coreSlice ψ t y)) =
      ∑ s : Spins (N+1), ∫ z, w (exteriorCoordinates z) * quantumCoreDensity Z ψ (Fin.last N) s z := by
  rw [← weighted_sum_integral_join
    (fun s => hψ.quantumCoreDensity_integrable Z (Fin.last N) s) w hw hwC]
  apply Finset.sum_congr rfl
  intro t _
  apply integral_congr_ae
  filter_upwards [hψ.ae_coreSlice t] with y hy
  rw [formEnergy_eq_density hy]
  simp only [quantumCoreDensity_last]

lemma coreSlice_mass_weighted_reconstruction {N : ℕ} {ψ : FormVector (N+1)}
    (hψ : SobolevFermion ψ) (w : Configuration 1 → ℝ) (hw : Continuous w)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    (∑ t : Spins 1, ∫ y, w y * formMass (coreSlice ψ t y)) =
      ∑ s : Spins (N+1), ∫ z, w (exteriorCoordinates z) * ‖ψ.value s z‖ ^ 2 := by
  exact weighted_sum_integral_join (fun s => (hψ.1 s).norm.integrable_sq) w hw hwC

lemma weighted_core_last {N : ℕ} {ψ : FormVector (N+1)} (hψ : SobolevFermion ψ)
    {Z : ℝ} (hZ : 0 ≤ Z) (w : Configuration 1 → ℝ) (hw : Continuous w)
    (hw0 : ∀ y, 0 ≤ w y) {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    energy Z N * (∑ s, ∫ z, w (exteriorCoordinates z) * ‖ψ.value s z‖ ^ 2) ≤
      ∑ s, ∫ z, w (exteriorCoordinates z) * quantumCoreDensity Z ψ (Fin.last N) s z := by
  rw [← coreSlice_mass_weighted_reconstruction hψ w hw hwC,
    ← coreSlice_energy_weighted_reconstruction hψ Z w hw hwC]
  exact weighted_core_energy hψ hZ w hw.aestronglyMeasurable
    (Eventually.of_forall hw0) (Eventually.of_forall hwC)

lemma graphFormVector_value_eq {N : ℕ} (F : fermionGraph N) (s : Spins N) (x : Configuration N) :
    (graphFormVector F).value s x = graphComponent s none F x := rfl

lemma graphFormVector_gradient_eq {N : ℕ} (F : fermionGraph N) (s : Spins N)
    (i : Fin N) (a : Fin 3) (x : Configuration N) :
    (graphFormVector F).gradient s i a x = graphComponent s (some (i,a)) F x := rfl

attribute [local irreducible] graphComponent graphFormVector

lemma sum_excluding_perm {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (i : α) (f : α → ℝ) :
    (∑ j, if j ≠ i then f (π j) else 0) = ∑ j, if j ≠ π i then f j else 0 := by
  rw [← Equiv.sum_comp π (fun j => if j ≠ π i then f j else 0)]
  simp only [ne_eq, π.injective.eq_iff]

lemma sum_pairs_excluding_perm {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) (i : α) (f : α → α → ℝ) :
    (∑ j, ∑ k, if j ≠ i ∧ k ≠ i ∧ j ≠ k then f (π j) (π k) else 0) =
      ∑ j, ∑ k, if j ≠ π i ∧ k ≠ π i ∧ j ≠ k then f j k else 0 := by
  rw [← Equiv.sum_comp π (fun j => ∑ k,
    if j ≠ π i ∧ k ≠ π i ∧ j ≠ k then f j k else 0)]
  apply Finset.sum_congr rfl; intro j _
  rw [← Equiv.sum_comp π (fun k =>
    if π j ≠ π i ∧ k ≠ π i ∧ π j ≠ k then f (π j) k else 0)]
  simp only [ne_eq, π.injective.eq_iff]

lemma quantumCoreDensity_reindex {N : ℕ} (Z : ℝ) (ψ φ : FormVector N)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (s t : Spins N) (x y : Configuration N)
    (hv : ‖φ.value t y‖ = ‖ψ.value s x‖)
    (hg : ∀ j a, ‖φ.gradient t j a y‖ = ‖ψ.gradient s (π j) a x‖)
    (hc : ∀ j, y j = x (π j)) :
    quantumCoreDensity Z φ i t y = quantumCoreDensity Z ψ (π i) s x := by
  classical
  unfold quantumCoreDensity
  simp only [hg, hv, hc]
  rw [sum_excluding_perm π i (fun j => ∑ a, ‖ψ.gradient s j a x‖ ^ 2),
    sum_excluding_perm π i (fun j => ‖ψ.value s x‖ ^ 2 / ‖x j‖),
    sum_pairs_excluding_perm π i (fun j k => ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖)]

lemma graphFormVector_permutation_norm {N : ℕ} (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (s : Spins N) :
    ∀ᵐ x : Configuration N,
      ‖(graphFormVector F).value (s ∘ π) (x ∘ π)‖ = ‖(graphFormVector F).value s x‖ ∧
      ∀ j a, ‖(graphFormVector F).gradient (s ∘ π) j a (x ∘ π)‖ =
        ‖(graphFormVector F).gradient s (π j) a x‖ := by
  have hg (j : Fin N) (a : Fin 3) : ∀ᵐ x : Configuration N,
      ‖(graphFormVector F).gradient (s ∘ π) j a (x ∘ π)‖ =
        ‖(graphFormVector F).gradient s (π j) a x‖ := by
    simpa only [graphFormVector_gradient_eq, Option.map_some, Equiv.symm_apply_apply]
      using graphComponent_permutation_norm F π s (some (π j,a))
  have hv : ∀ᵐ x : Configuration N,
      ‖(graphFormVector F).value (s ∘ π) (x ∘ π)‖ = ‖(graphFormVector F).value s x‖ := by
    simpa only [graphFormVector_value_eq, Option.map_none] using graphComponent_permutation_norm F π s none
  exact hv.and (ae_all_iff.mpr fun j => ae_all_iff.mpr fun a => hg j a)

lemma quantumCoreDensity_permutation {N : ℕ} (Z : ℝ) (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (s : Spins N) :
    ∀ᵐ x : Configuration N,
      quantumCoreDensity Z (graphFormVector F) i (s ∘ π) (x ∘ π) =
      quantumCoreDensity Z (graphFormVector F) (π i) s x := by
  filter_upwards [graphFormVector_permutation_norm F π s] with x hx
  exact quantumCoreDensity_reindex Z _ _ π i s (s ∘ π) x (x ∘ π) hx.1 hx.2 (fun _ => rfl)

lemma weighted_core_permutation {N : ℕ} (Z : ℝ) (F : fermionGraph N)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (w : Space → ℝ) :
    (∑ s, ∫ x, w (x i) * quantumCoreDensity Z (graphFormVector F) i s x) =
      ∑ s, ∫ x, w (x (π i)) * quantumCoreDensity Z (graphFormVector F) (π i) s x := by
  rw [← sum_spins_permutation π (fun s => ∫ x, w (x i) *
    quantumCoreDensity Z (graphFormVector F) i s x)]
  apply Finset.sum_congr rfl; intro s _
  rw [← (permuteConfiguration_preserving π).integral_comp
    (permuteConfiguration π).toHomeomorph.measurableEmbedding
    (fun x => w (x i) * quantumCoreDensity Z (graphFormVector F) i (s ∘ π) x)]
  apply integral_congr_ae
  filter_upwards [quantumCoreDensity_permutation Z F π i s] with x hx
  simp only [permuteConfiguration_apply, Function.comp_apply, hx]

lemma weighted_core_coordinate {N : ℕ} (F : fermionGraph (N+1)) {Z : ℝ} (hZ : 0 ≤ Z)
    (i : Fin (N+1)) (w : Space → ℝ) (hw : Continuous w) (hw0 : ∀ y, 0 ≤ w y)
    {C : ℝ} (hwC : ∀ y, ‖w y‖ ≤ C) :
    energy Z N * (∑ s, ∫ x, w (x i) * ‖graphComponent s none F x‖ ^ 2) ≤
      ∑ s, ∫ x, w (x i) * quantumCoreDensity Z (graphFormVector F) i s x := by
  classical
  have hh := weighted_core_last (graphFormVector_sobolev F) hZ
    (fun y => w (y 0)) (hw.comp (continuous_apply 0)) (fun y => hw0 (y 0))
    (fun y => hwC (y 0))
  have he (x : Configuration (N+1)) : exteriorCoordinates x 0 = x (Fin.last N) := rfl
  simp only [he, graphFormVector_value_eq] at hh
  let π : Equiv.Perm (Fin (N+1)) := Equiv.swap (Fin.last N) i
  have hi : π (Fin.last N) = i := Equiv.swap_apply_left _ _
  rw [weighted_core_permutation Z F π (Fin.last N) w, hi] at hh
  have hm := graphComponent_permutation_sum_integral F π none
    (fun x => w (x (Fin.last N)))
  simp only [Option.map_none, Function.comp_apply, hi] at hm
  rw [hm] at hh
  exact hh

end

lemma sum_excluding_add {α : Type*} [Fintype α] [DecidableEq α] (i : α) (f : α → ℝ) :
    (∑ j, if j ≠ i then f j else 0) + f i = ∑ j, f j := by
  have hh (j : α) : (if j ≠ i then f j else 0) + (if j = i then f j else 0) = f j := by
    by_cases h : j = i <;> simp [h]
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hh j)

lemma pairs_excluding_add {α : Type*} [Fintype α] [DecidableEq α] (i : α)
    (f : α → α → ℝ) (hs : ∀ j k, f j k = f k j) (hii : f i i = 0) :
    (∑ j, ∑ k, if j ≠ i ∧ k ≠ i then f j k else 0) + 2 * (∑ k, f i k) =
      ∑ j, ∑ k, f j k := by
  have hinner (j : α) : (∑ k, if k ≠ i then f j k else 0) + f j i = ∑ k, f j k :=
    sum_excluding_add i (f j)
  have houter := sum_excluding_add i (fun j => ∑ k, if k ≠ i then f j k else 0)
  have hr := sum_excluding_add i (f i)
  rw [hii, add_zero] at hr
  have hc : (∑ j, f j i) = ∑ j, f i j := Finset.sum_congr rfl (fun j _ => hs j i)
  have hd : (∑ j, if j ≠ i then ∑ k, if k ≠ i then f j k else 0 else 0) =
      ∑ j, ∑ k, if j ≠ i ∧ k ≠ i then f j k else 0 := by
    apply Finset.sum_congr rfl; intro j _
    by_cases h : j = i <;> simp [h]
  rw [hd, hr] at houter
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hinner j)
  rw [Finset.sum_add_distrib, hc] at he
  linarith

lemma quantumEnergyDensity_delete {N : ℕ} (Z : ℝ) (ψ : FormVector N)
    (i : Fin N) (s : Spins N) (x : Configuration N) :
    quantumEnergyDensity Z ψ s x = quantumCoreDensity Z ψ i s x +
      (1/2:ℝ) * (∑ a, ‖ψ.gradient s i a x‖ ^ 2) - Z * (‖ψ.value s x‖ ^ 2 / ‖x i‖) +
      (∑ j, if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0) := by
  classical
  have hk := sum_excluding_add i (fun j => ∑ a, ‖ψ.gradient s j a x‖ ^ 2)
  have hn := sum_excluding_add i (fun j => ‖ψ.value s x‖ ^ 2 / ‖x j‖)
  let f := fun j k : Fin N => if j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0
  have hs (j k : Fin N) : f j k = f k j := by
    dsimp [f]
    by_cases h : j = k
    · simp [h]
    · simp [h, Ne.symm h, norm_sub_rev]
  have hp := pairs_excluding_add i f hs (by simp [f])
  have he (j k : Fin N) : (if j ≠ i ∧ k ≠ i then f j k else 0) =
      if j ≠ i ∧ k ≠ i ∧ j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0 := by
    simp only [f]; split_ifs <;> simp_all
  simp only [he] at hp
  unfold quantumEnergyDensity quantumCoreDensity
  change _ = _
  dsimp only [f] at hp
  rw [← hk, ← hn, ← hp]
  ring


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Sum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace


open MeasureTheory Filter
open scoped Topology BigOperators

lemma l2_coe_finset_sum {X α : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset α) (f : α → Lp ℂ 2 μ) :
    ((∑ i ∈ s, f i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    exact hx
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hx hy
    simp only [Pi.add_apply] at hx
    rw [hx, hy]

section Sum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι α : Type*} [Fintype ι] [Fintype α] {v : ι → E}

omit [Fintype ι] in
lemma SmoothMultiplier.sumSquares_apply (p : α → SmoothMultiplier v) (F : weakGraph v) :
    (SmoothMultiplier.sumSquares p).apply F = ∑ i, (p i).apply ((p i).apply F) := by
  apply weakGraphValue_injective v
  rw [map_sum]
  apply Lp.ext
  have ha : ∀ᵐ x : E, ∀ i : α,
      ((p i).apply ((p i).apply F)).val none x =
        ((p i).value x : ℂ) * ((p i).value x : ℂ) * F.val none x := by
    apply ae_all_iff.mpr; intro i
    filter_upwards [(p i).apply_value ((p i).apply F), (p i).apply_value F] with x hx hy
    rw [hx, hy, mul_assoc]
  filter_upwards [(SmoothMultiplier.sumSquares p).apply_value F, ha,
    l2_coe_finset_sum volume Finset.univ
      (fun i => weakGraphValue v ((p i).apply ((p i).apply F)))] with x hx hy hz
  change ((SmoothMultiplier.sumSquares p).apply F).val none x = _
  rw [hx, hz]
  change (((∑ i, (p i).value x ^ 2 : ℝ) : ℂ) * F.val none x) = _
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  change ((p i).value x : ℂ) ^ 2 * F.val none x =
    ((p i).apply ((p i).apply F)).val none x
  rw [hy i, pow_two]

omit [Fintype ι] in
lemma weakGraph_sum_component (G : α → weakGraph v) (k : Option ι) :
    (∑ i, G i).val k = ∑ i, (G i).val k := by
  rw [Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply]

end Sum


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ComplexRealWeightPairing
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
section

lemma complex_real_weight_pairing (w : ℝ) (a : ℂ) :
    (⟪(w : ℂ) * a, a⟫_ℂ).re = w * ‖a‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma l2_real_weight_pairing {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (w : X → ℝ) (f g : Lp ℂ 2 μ)
    (hg : (g : X → ℂ) =ᵐ[μ] fun x => (w x : ℂ) * f x) :
    (⟪g, f⟫_ℂ).re = ∫ x, w x * ‖f x‖ ^ 2 ∂μ := by
  rw [l2_inner_re]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx, complex_real_weight_pairing]

lemma norm_div_sqrt_real_sq (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ‖a / (Real.sqrt r : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / r := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr]

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

lemma FermionMultiplier.nuclear_weighted_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (⟪graphNuclear s i (p.apply F), graphNuclear s i F⟫_ℂ).re =
      ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖) := by
  rw [l2_real_weight_pairing p.value _ _ (p.apply_nuclear F s i)]
  apply integral_congr_ae
  filter_upwards [graphNuclear_ae s i F] with x hx
  rw [hx, norm_div_sqrt_real_sq _ (norm_nonneg _)]

lemma FermionMultiplier.pair_weighted_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (⟪graphPair s i j hij (p.apply F), graphPair s i j hij F⟫_ℂ).re =
      ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖) := by
  rw [l2_real_weight_pairing p.value _ _ (p.apply_pair F s i j hij)]
  apply integral_congr_ae
  filter_upwards [graphPair_ae s i j hij F] with x hx
  rw [hx, norm_div_sqrt_real_sq _ (norm_nonneg _)]

end

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

lemma weighted_integrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {w : X → ℝ} (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    Integrable (fun x => w x * f x) μ :=
  hf.bdd_mul hw.aestronglyMeasurable (Eventually.of_forall hC)

lemma integral_weighted_quantumDensity {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (1/2:ℝ) * (∑ i, ∑ a, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∑ i, ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (1/2:ℝ) * (∑ i, ∑ j, ∫ x, w x *
        (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
  classical
  have hk (i : Fin N) (a : Fin 3) := weighted_integrable (hψ.2.1 s i a).norm.integrable_sq hw hC
  have hn (i : Fin N) := weighted_integrable
    (nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
  have hp (i j : Fin N) : Integrable (fun x => w x *
      (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    split_ifs with hij
    · exact weighted_integrable (pair_integrable i j hij (hψ.1 s)
        (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
    · simp only [mul_zero]; exact integrable_zero _ _ _
  have hks := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun a _ => hk i a))
  have hns := integrable_finsetSum Finset.univ (fun i _ => hn i)
  have hps := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hp i j))
  have hleft : (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      ∫ x, (1/2:ℝ) * (∑ i, ∑ a, w x * ‖ψ.gradient s i a x‖ ^ 2) -
        Z * (∑ i, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
        (1/2:ℝ) * (∑ i, ∑ j, w x *
          (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [quantumEnergyDensity, mul_add, mul_sub, mul_left_comm (w x) (1/2:ℝ),
        mul_left_comm (w x) Z, Finset.mul_sum]
  have ha := integral_add ((hks.const_mul (1/2:ℝ)).sub (hns.const_mul Z))
    (hps.const_mul (1/2:ℝ))
  have hb := integral_sub (hks.const_mul (1/2:ℝ)) (hns.const_mul Z)
  simp only [Pi.sub_apply] at ha hb
  rw [hleft, ha, hb]
  simp only [integral_const_mul]
  simp_rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hk i a)),
    integral_finsetSum _ (fun a _ => hk _ a), integral_finsetSum _ (fun i _ => hn i),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hp i j)),
    integral_finsetSum _ (fun j _ => hp _ j)]


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingPairApproxIntegral
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

section

lemma integral_weighted_deletedDensity {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N) (i : Fin N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (∫ x, w x * quantumCoreDensity Z ψ i s x) +
      (1/2:ℝ) * (∑ a : Fin 3, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (∑ j : Fin N, ∫ x, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
  classical
  have hc := weighted_integrable (hψ.quantumCoreDensity_integrable Z i s) hw hC
  have hk (a : Fin 3) := weighted_integrable (hψ.2.1 s i a).norm.integrable_sq hw hC
  have hn := weighted_integrable
    (nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
  have hp (j : Fin N) : Integrable (fun x => w x *
      (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    split_ifs with hij
    · exact weighted_integrable (pair_integrable i j hij (hψ.1 s)
        (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
    · simp only [mul_zero]; exact integrable_zero _ _ _
  have hks := integrable_finsetSum Finset.univ (fun a _ => hk a)
  have hps := integrable_finsetSum Finset.univ (fun j _ => hp j)
  have he : (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      ∫ x, w x * quantumCoreDensity Z ψ i s x +
        (1/2:ℝ) * (∑ a : Fin 3, w x * ‖ψ.gradient s i a x‖ ^ 2) -
        Z * (w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
        (∑ j : Fin N, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [quantumEnergyDensity_delete Z ψ i s x]
      simp only [mul_add, mul_sub, mul_left_comm (w x) (1/2:ℝ),
        mul_left_comm (w x) Z, Finset.mul_sum]
  have ha := integral_add ((hc.add (hks.const_mul (1/2:ℝ))).sub (hn.const_mul Z)) hps
  have hb := integral_sub (hc.add (hks.const_mul (1/2:ℝ))) (hn.const_mul Z)
  have hd := integral_add hc (hks.const_mul (1/2:ℝ))
  simp only [Pi.sub_apply, Pi.add_apply] at ha hb hd
  rw [he, ha, hb, hd]
  simp only [integral_const_mul]
  rw [integral_finsetSum _ (fun a _ => hk a), integral_finsetSum _ (fun j _ => hp j)]

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply

end
section

attribute [local irreducible] graphNuclear graphPair graphComponent graphFormVector FermionMultiplier.apply coulombFormOperator fermionGraph weakGraph fermionGraphValue

lemma integral_weighted_quantumDensity_ordered {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (1/2:ℝ) * (∑ i : Fin N, ∑ a : Fin 3, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∑ i : Fin N, ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (∑ i : Fin N, ∑ j : Fin N, if i < j then (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  classical
  have hp (i j : Fin N) : (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) =
      ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x j-x i‖) := by simp only [norm_sub_rev]
  have hi (i j : Fin N) :
      (∫ x, w x * (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) =
      if i ≠ j then (∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i-x j‖)) else 0 := by
    split_ifs <;> simp
  rw [integral_weighted_quantumDensity hψ Z s w hw hC]
  simp only [hi]
  rw [← sum_pairs_half _ hp]

lemma FermionMultiplier.density_weighted_identity {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) =
      (1/2:ℝ) * (∑ i : Fin N, ∑ a : Fin 3, ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2) -
      Z * (∑ i : Fin N, ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  let C : ℝ := Classical.choose p.toSmoothMultiplier.bound
  have hC : ∀ x, |p.value x| ≤ C := Classical.choose_spec p.toSmoothMultiplier.bound
  have hCp (x : Configuration N) : ‖p.value x‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x
  simpa only [graphFormVector_value_eq, graphFormVector_gradient_eq] using
    integral_weighted_quantumDensity_ordered (graphFormVector_sobolev F) Z s p.value p.regular.continuous hCp

lemma FermionMultiplier.operator_weighted_pairing {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i,a)) (p.apply F), graphComponent s (some (i,a)) F⟫_ℂ).re) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  have hh := coulombFormOperator_pairing Z N F (p.apply F)
  simpa only [p.nuclear_weighted_pairing, p.pair_weighted_pairing, dite_eq_ite] using hh

lemma weighted_form_algebra (Z K G V W D A : ℝ)
    (hd : D = (1/2:ℝ)*K-Z*V+W) (ha : A = (1/2:ℝ)*G-Z*V+W) :
    A = D+(1/2:ℝ)*(G-K) := by rw [hd, ha]; ring

lemma FermionMultiplier.density_weighted_sum {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (∑ s : Spins N, ∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) =
      (1/2:ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2) -
      Z * (∑ s : Spins N, ∑ i : Fin N,
        ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)) +
      (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N, if i < j then
        (∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖)) else 0) := by
  classical
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun s _ => p.density_weighted_identity Z F s)
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using he

lemma FermionMultiplier.form_weighted_identity {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      (∑ s : Spins N, ∫ x, p.value x * quantumEnergyDensity Z (graphFormVector F) s x) +
      (1/2:ℝ) * ((∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (⟪graphComponent s (some (i,a)) (p.apply F), graphComponent s (some (i,a)) F⟫_ℂ).re) -
        (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, p.value x * ‖graphComponent s (some (i,a)) F x‖ ^ 2)) := by
  exact weighted_form_algebra Z _ _ _ _ _ _ (p.density_weighted_sum Z F) (p.operator_weighted_pairing Z F)

end

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WeightedMass
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply coulombFormOperator fermionGraph weakGraph fermionGraphValue

lemma weightedMass_nonneg {N : ℕ} (F : fermionGraph N) {w : Configuration N → ℝ}
    (hw : ∀ x, 0 ≤ w x) : 0 ≤ weightedMass F w := by
  exact Finset.sum_nonneg fun s _ => integral_nonneg fun x => mul_nonneg (hw x) (sq_nonneg _)

lemma weightedFullDensity_delete {N : ℕ} (Z : ℝ) (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    weightedFullDensity Z F w = weightedCoreDensity Z F i w +
      (1/2:ℝ) * weightedGradient F w i - Z * weightedNuclear F i w + weightedPairs F i w := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun s _ => integral_weighted_deletedDensity (graphFormVector_sobolev F) Z s i w hw hC)
  simpa only [weightedFullDensity, weightedCoreDensity, weightedGradient, weightedNuclear, weightedPairs,
    graphFormVector_value_eq, graphFormVector_gradient_eq,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using h

lemma FermionMultiplier.value_weighted_pairing {N : ℕ} (F : fermionGraph N) (p : FermionMultiplier N) :
    (⟪fermionGraphValue N (p.apply F), fermionGraphValue N F⟫_ℂ).re = weightedMass F p.value := by
  rw [graphValue_pairing]
  apply Finset.sum_congr rfl; intro s _
  exact l2_real_weight_pairing p.value _ _ (p.apply_value F s)

attribute [local irreducible] bindingTotalMultiplier graphNuclear graphPair
  weightedMass weightedGradient weightedFullDensity weightedCoreDensity weightedNuclear weightedPairs

lemma sum_rotate_three {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℝ) : (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

attribute [local irreducible] weightedKinetic graphKineticPair

lemma weightedKinetic_expand {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) :
    weightedKinetic F w =
      ∑ s, ∑ i, ∑ a, ∫ x, w x * ‖graphComponent s (some (i,a)) F x‖ ^ 2 := by
  unfold weightedKinetic weightedGradient
  exact Finset.sum_comm

lemma FermionMultiplier.form_weighted_packed {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      weightedFullDensity Z F p.value + (1/2:ℝ)*
        (graphKineticPair (p.apply F) F-weightedKinetic F p.value) := by
  simpa only [weightedKinetic_expand, weightedFullDensity, graphKineticPair] using
    p.form_weighted_identity Z F

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingNuclearSum
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue bindingTotalMultiplier
  bindingApprox bindingPairApprox

lemma graph_nuclear_integrable {N : ℕ} (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    Integrable (fun x => ‖graphComponent s none F x‖ ^ 2 / ‖x i‖) := by
  have h := graphFormVector_sobolev F
  simpa only [graphFormVector_value_eq] using nuclear_integrable i (h.1 s)
    (h.2.1 s i) (h.2.2.1 s i)

lemma graph_pair_integrable {N : ℕ} (F : fermionGraph N) (s : Spins N)
    (i j : Fin N) (hij : i ≠ j) :
    Integrable (fun x => ‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖) := by
  have h := graphFormVector_sobolev F
  simpa only [graphFormVector_value_eq] using pair_integrable i j hij (h.1 s)
    (h.2.1 s i) (h.2.2.1 s i)

attribute [local irreducible] bindingNuclearSum bindingPairSum bindingCappedSum

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom

lemma oneBodySquareTotal_component {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    graphComponent s k ((oneBodySquareTotal p).apply F) =
      ∑ i, ((p.oneBody i).apply ((p.oneBody i).apply (F.val s))).val k := by
  change ((SmoothMultiplier.sumSquares p.oneBody).apply (F.val s)).val k = _
  rw [SmoothMultiplier.sumSquares_apply, weakGraph_sum_component]

lemma SmoothMultiplier.square_integrable (p : SmoothMultiplier spaceDirections)
    {N : ℕ} (i : Fin N) {f : Configuration N → ℝ} (hf : Integrable f) :
    Integrable (fun x => p.value (x i)^2*f x) := by
  obtain ⟨C,hC⟩ := p.bound
  apply weighted_integrable hf ((p.regular.continuous.comp (continuous_apply i)).pow 2)
  intro x
  change ‖p.value (x i)^2‖ ≤ C^2
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hC (x i)) 2

lemma oneBodySquareTotal_integral {N : ℕ} (p : SmoothMultiplier spaceDirections)
    {f : Configuration N → ℝ} (hf : Integrable f) :
    (∫ x, (oneBodySquareTotal p).value x*f x) = ∑ i, ∫ x,p.value (x i)^2*f x := by
  simp only [oneBodySquareTotal_value, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => p.square_integrable i hf)

lemma oneBody_pairing_off {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : weakGraph (sectorDirections N)) (i j : Fin N) (hij : i ≠ j) (a : Fin 3) :
    (⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (j,a)),
      F.val (some (j,a))⟫_ℂ).re = ∫ x,p.value (x i)^2*‖F.val (some (j,a)) x‖^2 := by
  apply l2_real_weight_pairing
  have hd (x : Configuration N) : lineDeriv ℝ (p.oneBody i).value x
      (sectorDirections N (j,a)) = 0 := by
    simp only [SmoothMultiplier.oneBody,sectorDirections,oneBody_coordinate_derivative,
      ite_eq_right (Ne.symm hij)]
  filter_upwards [(p.oneBody i).apply_gradient ((p.oneBody i).apply F) (j,a),
    (p.oneBody i).apply_gradient F (j,a)] with x hx hy
  rw [hd,Complex.ofReal_zero,zero_mul,add_zero] at hx hy
  rw [hx,hy]
  simp only [SmoothMultiplier.oneBody,Complex.ofReal_pow]
  ring

lemma oneBody_kinetic_error {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : weakGraph (sectorDirections N)) (i : Fin N) :
    -(∑ a : Fin 3, ∫ x, (lineDeriv ℝ p.value (x i) (spaceDirections a))^2*
      ‖F.val none x‖^2) ≤ ∑ a : Fin 3,
      (⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (i,a)),
        F.val (some (i,a))⟫_ℂ).re := by
  have hi (a : Fin 3) : ‖((p.oneBody i).apply F).val (some (i,a))‖^2 -
      (⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (i,a)),
        F.val (some (i,a))⟫_ℂ).re =
      ∫ x, (lineDeriv ℝ p.value (x i) (spaceDirections a))^2*‖F.val none x‖^2 := by
    have hh := l2_ims_identity (p.oneBody i).value
      (fun x => lineDeriv ℝ (p.oneBody i).value x (sectorDirections N (i,a)))
      (F.val (some (i,a))) (F.val none) (((p.oneBody i).apply F).val (some (i,a)))
      (((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (i,a)))
      ((p.oneBody i).apply_gradient F (i,a))
    have hh' := hh (by
      filter_upwards [(p.oneBody i).apply_gradient ((p.oneBody i).apply F) (i,a),
        (p.oneBody i).apply_value F] with x hx hy
      rw [hx,hy])
    simpa only [SmoothMultiplier.oneBody,sectorDirections,oneBody_coordinate_derivative,
      ite_eq_left rfl,ite_true] using hh'
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun a _ => hi a)
  have hn : 0 ≤ ∑ a : Fin 3, ‖((p.oneBody i).apply F).val (some (i,a))‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Finset.sum_sub_distrib] at hs
  linarith

lemma oneBody_kinetic_lower {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : weakGraph (sectorDirections N)) (i : Fin N) :
    (∑ j,∑ a,∫ x,p.value (x i)^2*‖F.val (some (j,a)) x‖^2) -
      (∑ a,∫ x,p.value (x i)^2*‖F.val (some (i,a)) x‖^2) -
      (∑ a,∫ x,(lineDeriv ℝ p.value (x i) (spaceDirections a))^2*‖F.val none x‖^2) ≤
    ∑ j,∑ a,(⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val (some (j,a)),
      F.val (some (j,a))⟫_ℂ).re := by
  classical
  let A (j : Fin N) := ∑ a,∫ x,p.value (x i)^2*‖F.val (some (j,a)) x‖^2
  let B (j : Fin N) := ∑ a,(⟪((p.oneBody i).apply ((p.oneBody i).apply F)).val
    (some (j,a)),F.val (some (j,a))⟫_ℂ).re
  have he : (∑ j,if j ≠ i then B j else 0) = ∑ j,if j ≠ i then A j else 0 := by
    apply Finset.sum_congr rfl; intro j _
    split_ifs with hji
    · apply Finset.sum_congr rfl; intro a _
      exact oneBody_pairing_off p F i j hji.symm a
    · rfl
  have ha := sum_excluding_add i A
  have hb := sum_excluding_add i B
  have hp := oneBody_kinetic_error p F i
  change -_ ≤ B i at hp
  change (∑ j,A j)-A i-_ ≤ ∑ j,B j
  rw [he] at hb
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_dShellForm
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section Reused_ShellForm

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  graphNuclear weightedMass weightedNuclear weightedPairs weightedCoreDensity
  oneBodySquareTotal SmoothMultiplier.oneBody weightedKinetic weightedGradient
  weightedFullDensity graphKineticPair sectorExcessOperator

attribute [local irreducible] oneBodyGradientError

lemma oneBodySquareTotal_mass {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) :
    weightedMass F (oneBodySquareTotal p).value =
      ∑ i,weightedMass F (fun x => p.value (x i)^2) := by
  unfold weightedMass
  simp only [oneBodySquareTotal_integral p (Lp.memLp _).norm.integrable_sq]
  exact Finset.sum_comm

lemma oneBodySquareTotal_full {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z : ℝ) (F : fermionGraph N) :
    weightedFullDensity Z F (oneBodySquareTotal p).value =
      ∑ i,weightedFullDensity Z F (fun x => p.value (x i)^2) := by
  unfold weightedFullDensity
  simp only [oneBodySquareTotal_integral p
    ((graphFormVector_sobolev F).quantumEnergyDensity_integrable Z _)]
  exact Finset.sum_comm

lemma oneBodySquareTotal_kinetic {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) :
    weightedKinetic F (oneBodySquareTotal p).value =
      ∑ s,∑ i,∑ j,∑ a,∫ x,p.value (x i)^2*‖graphComponent s (some (j,a)) F x‖^2 := by
  rw [weightedKinetic_expand]
  simp only [oneBodySquareTotal_integral p (Lp.memLp _).norm.integrable_sq]
  apply Finset.sum_congr rfl; intro s _
  exact sum_rotate_three _

lemma oneBody_graphkinetic_lower {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (∑ j,∑ a,∫ x,p.value (x i)^2*‖graphComponent s (some (j,a)) F x‖^2) -
      (∑ a,∫ x,p.value (x i)^2*‖graphComponent s (some (i,a)) F x‖^2) -
      (∑ a,∫ x,(lineDeriv ℝ p.value (x i) (spaceDirections a))^2*
        ‖graphComponent s none F x‖^2) ≤
    ∑ j,∑ a,(⟪((p.oneBody i).apply ((p.oneBody i).apply (F.val s))).val (some (j,a)),
      graphComponent s (some (j,a)) F⟫_ℂ).re := by
  simpa only [graphComponent_apply] using oneBody_kinetic_lower p (F.val s) i

lemma oneBodySquareTotal_pairing_pack {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) :
    (∑ s,∑ i,∑ j,∑ a,(⟪((p.oneBody i).apply ((p.oneBody i).apply (F.val s))).val
      (some (j,a)),graphComponent s (some (j,a)) F⟫_ℂ).re) =
      graphKineticPair ((oneBodySquareTotal p).apply F) F := by
  unfold graphKineticPair
  simp only [oneBodySquareTotal_component,sum_inner,Complex.re_sum]
  apply Finset.sum_congr rfl; intro s _
  exact (sum_rotate_three _).symm

lemma shell_kinetic_sum_arithmetic {S I : Type*} [Fintype S] [Fintype I]
    (K D E G : S → I → ℝ) (Kt Dt Et Gt : ℝ)
    (hK : Kt=∑ s,∑ i,K s i) (hD : Dt=∑ s,∑ i,D s i)
    (hE : Et=∑ s,∑ i,E s i) (hG : Gt=∑ s,∑ i,G s i)
    (h : ∀ s i,K s i-D s i-E s i ≤ G s i) : Kt-Dt-Et ≤ Gt := by
  rw [hK,hD,hE,hG]
  simp only [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i _ => h s i

lemma oneBodySquareTotal_kinetic_lower {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) :
    weightedKinetic F (oneBodySquareTotal p).value -
      (∑ i,weightedGradient F (fun x => p.value (x i)^2) i) -
      oneBodyGradientError p F ≤ graphKineticPair ((oneBodySquareTotal p).apply F) F := by
  apply shell_kinetic_sum_arithmetic _ _ _ _ _ _ _ _
    (oneBodySquareTotal_kinetic p F) _ (show oneBodyGradientError p F = _ by
      unfold oneBodyGradientError; rfl) (oneBodySquareTotal_pairing_pack p F).symm
    (oneBody_graphkinetic_lower p F)
  unfold weightedGradient
  exact Finset.sum_comm

lemma shell_form_sum_arithmetic {ι : Type*} [Fintype ι]
    (D C K V P : ι → ℝ) (Z W G A Dt err : ℝ)
    (hD : ∀ i,D i=C i+(1/2:ℝ)*K i-Z*V i+P i)
    (hG : W-(∑ i,K i)-err ≤ G) (hDt : Dt=∑ i,D i)
    (hA : A=Dt+(1/2:ℝ)*(G-W)) :
    (∑ i,(C i-Z*V i+P i)) ≤ A+(1/2:ℝ)*err := by
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hD i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hs ⊢
  linarith

lemma oneBody_form_lower {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z : ℝ) (F : fermionGraph N) :
    (∑ i,(weightedCoreDensity Z F i (fun x => p.value (x i)^2) -
      Z*weightedNuclear F i (fun x => p.value (x i)^2) +
      weightedPairs F i (fun x => p.value (x i)^2))) ≤
      (⟪(oneBodySquareTotal p).apply F,coulombFormOperator Z N F⟫_ℂ).re +
        (1/2:ℝ)*oneBodyGradientError p F := by
  let C := p.bound.choose
  have hC : ∀ y, |p.value y| ≤ C := p.bound.choose_spec
  have hc (i : Fin N) : Continuous (fun x : Configuration N => p.value (x i)^2) :=
    (p.regular.continuous.comp (continuous_apply i)).pow 2
  have hb (i : Fin N) (x : Configuration N) : ‖p.value (x i)^2‖ ≤ C^2 := by
    rw [norm_pow,Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC (x i)) 2
  exact shell_form_sum_arithmetic _ _ _ _ _ Z _ _ _ _ _
    (fun i => weightedFullDensity_delete Z F i (fun x => p.value (x i)^2) (hc i) (hb i))
    (oneBodySquareTotal_kinetic_lower p F) (oneBodySquareTotal_full p Z F)
    ((oneBodySquareTotal p).form_weighted_packed Z F)

lemma energy_oneBody_core_price_le {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph (N+1))
    (hstep : energy Z (N+1)+lam ≤ energy Z N) (i : Fin (N+1)) :
    (energy Z (N+1)+lam)*weightedMass F (fun x => p.value (x i)^2) ≤
      weightedCoreDensity Z F i (fun x => p.value (x i)^2) := by
  obtain ⟨C,hC⟩ := p.bound
  have hm := weightedMass_nonneg F (fun x : Configuration (N+1) => sq_nonneg (p.value (x i)))
  have hb (y : Space) : ‖p.value y^2‖ ≤ C^2 := by
    rw [norm_pow,Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC y) 2
  have hi := weighted_core_coordinate F hZ i (fun y => p.value y^2)
    (p.regular.continuous.pow 2) (fun y => sq_nonneg _) hb
  apply (mul_le_mul_of_nonneg_right hstep hm).trans
  simpa only [weightedMass,weightedCoreDensity] using hi

lemma shell_residual_cancellation {ι : Type*} [Fintype ι]
    (C V P M : ι → ℝ) (E lam Z A Mt r err : ℝ)
    (hC : ∀ i,(E+lam)*M i ≤ C i) (hM : Mt=∑ i,M i)
    (hA : r=A-E*Mt) (hL : (∑ i,(C i-Z*V i+P i)) ≤ A+(1/2:ℝ)*err) :
    (∑ i,P i)+lam*Mt ≤ Z*(∑ i,V i)+(1/2:ℝ)*err+r := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hC i
  rw [← Finset.mul_sum,← hM] at hs
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hL
  nlinarith

theorem quantum_oneBody_residual {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph (N+1))
    (hstep : energy Z (N+1)+lam ≤ energy Z N) :
    (∑ i,weightedPairs F i (fun x => p.value (x i)^2)) +
      lam*weightedMass F (oneBodySquareTotal p).value ≤
    Z*(∑ i,weightedNuclear F i (fun x => p.value (x i)^2)) +
      (1/2:ℝ)*oneBodyGradientError p F +
      (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  have he := sectorExcessOperator_pair Z ((oneBodySquareTotal p).apply F) F
  have hp := FermionMultiplier.value_weighted_pairing F (oneBodySquareTotal p)
  have he' := he.trans (congrArg (fun t : ℝ =>
    (⟪(oneBodySquareTotal p).apply F,coulombFormOperator Z (N+1) F⟫_ℂ).re-
      energy Z (N+1)*t) hp)
  exact shell_residual_cancellation _ _ _ _ _ _ _ _ _ _ _
    (fun i => energy_oneBody_core_price_le hZ p F hstep i)
    (oneBodySquareTotal_mass p F) he' (oneBody_form_lower p Z F)

end CoulombAtom
end Reused_ShellForm

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_dShellInnerField
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section Reused_ShellInnerField

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  graphNuclear weightedMass weightedNuclear weightedPairs weightedCoreDensity
  oneBodySquareTotal SmoothMultiplier.oneBody weightedKinetic weightedGradient
  weightedFullDensity graphKineticPair sectorExcessOperator oneBodyGradientError

lemma graph_pair_integrable_all {N : ℕ} (F : fermionGraph N) (s : Spins N)
    (i j : Fin N) :
    Integrable (fun x => ‖graphComponent s none F x‖^2/‖x i-x j‖) := by
  by_cases hij : i=j
  · subst j; simp only [sub_self,norm_zero,div_zero]; exact integrable_zero _ _ _
  · exact graph_pair_integrable F s i j hij

lemma weightedInnerPairs_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (h : ℝ) (s : Spins N) (i j : Fin N) :
    Integrable (fun x => if ‖x j‖ < h then
      p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i-x j‖) else 0) := by
  exact (p.square_integrable i (graph_pair_integrable_all F s i j)).indicator
    (isOpen_lt (continuous_apply j |>.norm) continuous_const).measurableSet

lemma weightedInnerPairs_le {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (h : ℝ) (i : Fin N) :
    weightedInnerPairs p F h i ≤ weightedPairs F i (fun x => p.value (x i)^2) := by
  unfold weightedInnerPairs weightedPairs
  apply Finset.sum_le_sum; intro s _
  apply Finset.sum_le_sum; intro j _
  by_cases hij : i=j
  · subst j
    simp only [ne_eq,not_true_eq_false,sub_self,norm_zero,div_zero,mul_zero,
      ite_self,integral_zero,le_refl]
  · simp only [ite_eq_left hij]
    apply integral_mono (weightedInnerPairs_integrable p F h s i j)
      (p.square_integrable i (graph_pair_integrable F s i j hij))
    intro x
    dsimp only
    split_ifs
    · rfl
    · positivity

lemma innerField_density_arithmetic {I : Type*} [Fintype I]
    (w k : I → ℝ) (P : I → Prop) [DecidablePred P] (L : I → I → ℝ) (Z b : ℝ) :
    (∑ i,w i*(Z*k i-∑ j,if P j then L i j else 0))*b =
      ∑ i,(Z*(w i*(b*k i)) - ∑ j,if P j then w i*(b*L i j) else 0) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [mul_sub,sub_mul,Finset.mul_sum,Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl; intro j _
    split_ifs <;> ring

lemma oneBodyInnerField_density {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (F : fermionGraph N) (s : Spins N) (x : Configuration N) :
    oneBodyInnerField p Z h x*‖graphComponent s none F x‖^2 =
      ∑ i,(Z*(p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i‖)) -
        ∑ j,if ‖x j‖ < h then
          p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i-x j‖) else 0) := by
  simpa only [oneBodyInnerField,rawInnerField,div_eq_mul_inv] using
    innerField_density_arithmetic (fun i => p.value (x i)^2) (fun i => (‖x i‖)⁻¹)
      (fun j => ‖x j‖ < h) (fun i j => (‖x i-x j‖)⁻¹) Z (‖graphComponent s none F x‖^2)

lemma oneBodyInnerField_density_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (F : fermionGraph N) (s : Spins N) :
    Integrable (fun x => oneBodyInnerField p Z h x*‖graphComponent s none F x‖^2) := by
  simp_rw [oneBodyInnerField_density p Z h F s]
  apply integrable_finsetSum; intro i _
  exact ((p.square_integrable i (graph_nuclear_integrable F s i)).const_mul Z).sub
    (integrable_finsetSum Finset.univ (fun j _ => weightedInnerPairs_integrable p F h s i j))

lemma integral_sum_sub_sum {X I : Type*} [MeasurableSpace X] [Fintype I]
    {μ : Measure X} (f : I → X → ℝ) (g : I → I → X → ℝ)
    (hf : ∀ i, Integrable (f i) μ) (hg : ∀ i j, Integrable (g i j) μ) (Z : ℝ) :
    (∫ x,∑ i,(Z*f i x-∑ j,g i j x) ∂μ) =
      ∑ i,(Z*(∫ x,f i x ∂μ)-∑ j,∫ x,g i j x ∂μ) := by
  have hi (i : I) : Integrable (fun x => Z*f i x-∑ j,g i j x) μ :=
    (hf i |>.const_mul Z).sub (integrable_finsetSum Finset.univ (fun j _ => hg i j))
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_sub (hf i |>.const_mul Z)
    (integrable_finsetSum Finset.univ (fun j _ => hg i j)),integral_const_mul,
    integral_finsetSum Finset.univ (fun j _ => hg i j)]

lemma oneBodyInnerField_density_integral {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (F : fermionGraph N) (s : Spins N) :
    (∫ x,oneBodyInnerField p Z h x*‖graphComponent s none F x‖^2) =
      ∑ i,(Z*(∫ x,p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i‖)) -
        ∑ j,∫ x,if ‖x j‖ < h then
          p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i-x j‖) else 0) := by
  simp_rw [oneBodyInnerField_density p Z h F s]
  exact integral_sum_sub_sum _ _
    (fun i => p.square_integrable i (graph_nuclear_integrable F s i))
    (fun i j => weightedInnerPairs_integrable p F h s i j) Z

lemma oneBodyInnerField_raw_integral {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (F : fermionGraph N) :
    (∫ x,oneBodyInnerField p Z h x ∂formRawLaw (graphFormVector F)) =
      Z*(∑ i,weightedNuclear F i (fun x => p.value (x i)^2)) -
        ∑ i,weightedInnerPairs p F h i := by
  rw [formRawLaw_integral (graphFormVector_sobolev F).sobolevVector]
  simp only [formRawDensity,graphFormVector_value_eq,Finset.sum_mul]
  simp_rw [mul_comm (‖graphComponent _ none F _‖^2)]
  rw [integral_finsetSum _ (fun s _ => oneBodyInnerField_density_integrable p Z h F s)]
  simp only [oneBodyInnerField_density_integral p Z h F,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  congr 1
  · congr 1
    unfold weightedNuclear
    exact Finset.sum_comm
  · unfold weightedInnerPairs
    exact Finset.sum_comm

theorem quantum_shell_inner_field_residual {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (p : SmoothMultiplier spaceDirections) (F : fermionGraph (N+1)) (h : ℝ)
    (hstep : energy Z (N+1)+lam ≤ energy Z N) :
    lam*weightedMass F (oneBodySquareTotal p).value ≤
      (1/2:ℝ)*oneBodyGradientError p F +
      (∫ x,oneBodyInnerField p Z h x ∂formRawLaw (graphFormVector F)) +
      (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  have hh := quantum_oneBody_residual hZ p F hstep
  have hl := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    weightedInnerPairs_le p F h i
  have he := oneBodyInnerField_raw_integral p Z h F
  exact (show ∀ a b c d r z k : ℝ, a+b ≤ c+d+r → k≤a → z=c-k →
    b≤d+z+r by intros; linarith) _ _ _ _ _ _ _ hh hl he

end CoulombAtom
end Reused_ShellInnerField

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ClosedInnerStatistic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom

lemma rawInnerField_le_closed {N : ℕ} {h H : ℝ} (hh : h < H) (Z : ℝ)
    (x : Configuration N) (y : Space) : rawInnerField Z H x y ≤ closedRawInnerField Z h x y := by
  unfold rawInnerField closedRawInnerField rawWeightedCount
  apply sub_le_sub_left
  apply Finset.sum_le_sum
  intro i _
  unfold innerParticleWeight
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact False.elim (h2 (lt_of_le_of_lt h1 hh))
  · positivity
  · exact le_rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ShellMeanStatistic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom
attribute [local irreducible] oneBodySquareTotal graphFormVector fermionGraph

lemma oneBodySquareTotal_mul_shellMeanField {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (x : Configuration N) :
    (oneBodySquareTotal p).value x*shellMeanField p Z h x = closedShellField p Z h x := by
  unfold shellMeanField
  by_cases hs : (oneBodySquareTotal p).value x = 0
  · have hi : ∀ i, p.value (x i) = 0 := by
      intro i
      have hh := Finset.single_le_sum (f := fun j : Fin N => p.value (x j)^2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [←oneBodySquareTotal_value] at hh
      rw [hs] at hh
      nlinarith only [hh,sq_nonneg (p.value (x i))]
    simp only [hs,zero_mul,closedShellField,hi,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
  · exact mul_div_cancel₀ _ hs
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellBias
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff InnerProductSpace NNReal ENNReal

lemma shellBias_value_sq {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (x : Configuration N) :
    (shellBiasMultiplier p hc).value x^2 = (oneBodySquareTotal p).value x := by
  change Real.sqrt ((oneBodySquareTotal p).value x)^2 = _
  apply Real.sq_sqrt
  change 0 ≤ ∑ i, p.value (x i)^2
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (p.value (x i)))

lemma shellBias_deriv_sq_le {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (x : Configuration N) (i : Fin N) (a : Fin 3) :
    (lineDeriv ℝ (shellBiasMultiplier p hc).value x (direction i a))^2 ≤
      (lineDeriv ℝ p.value (x i) (spaceDirections a))^2 := by
  let S := fun x : Configuration N => (oneBodySquareTotal p).value x
  have hS (x : Configuration N) : 0 ≤ S x := by
    change 0 ≤ ∑ i, p.value (x i)^2
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd : fderiv ℝ S x (direction i a) =
      2*p.value (x i)*lineDeriv ℝ p.value (x i) (spaceDirections a) := by
    rw [←DifferentiableAt.lineDeriv_eq_fderiv ((oneBodySquareTotal p).regular.differentiable (by simp) x)]
    change lineDeriv ℝ (fun y => ∑ j : Fin N, (p.oneBody j).value y^2) x (direction i a) = _
    rw [lineDeriv_sumSquares]
    simp only [SmoothMultiplier.oneBody,oneBody_coordinate_derivative]
    simp
  change (lineDeriv ℝ (fun y => Real.sqrt (S y)) x (direction i a))^2 ≤ _
  by_cases hx : S x = 0
  · rw [CoulombObservation.lineDeriv_sqrt_of_zero hS hx,zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · have hp : 0 < S x := (hS x).lt_of_ne' hx
    rw [CoulombObservation.lineDeriv_sqrt_of_pos ((oneBodySquareTotal p).regular.differentiable (by simp) x) hp,hd]
    have hi : p.value (x i)^2 ≤ S x := by
      change p.value (x i)^2 ≤ ∑ j : Fin N, p.value (x j)^2
      exact Finset.single_le_sum (fun j _ => sq_nonneg (p.value (x j))) (Finset.mem_univ i)
    have hs := Real.sq_sqrt (hS x)
    have hpos := Real.sqrt_pos.2 hp
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : 0 < (2*Real.sqrt (S x))^2)).2
    simp only [mul_pow,hs]
    nlinarith only [mul_le_mul_of_nonneg_right hi (sq_nonneg (lineDeriv ℝ p.value (x i) (spaceDirections a)))]

end
open MeasureTheory Set Filter
open scoped ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellBiasEnergy
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
noncomputable section
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier

lemma shellBias_double_apply {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) :
    (shellBiasMultiplier p hc).apply ((shellBiasMultiplier p hc).apply F) = (oneBodySquareTotal p).apply F := by
  apply graph_value_components_ext
  intro s
  apply Lp.ext
  filter_upwards [(shellBiasMultiplier p hc).apply_value ((shellBiasMultiplier p hc).apply F) s,
    (shellBiasMultiplier p hc).apply_value F s,(oneBodySquareTotal p).apply_value F s] with x h1 h2 h3
  have hsq : ((shellBiasMultiplier p hc).value x : ℂ) *
      ((shellBiasMultiplier p hc).value x : ℂ) = ((oneBodySquareTotal p).value x : ℂ) := by
    rw [←sq,←Complex.ofReal_pow,shellBias_value_sq p hc x]
  calc
    _ = ((shellBiasMultiplier p hc).value x : ℂ) *
        (((shellBiasMultiplier p hc).value x : ℂ) * graphComponent s none F x) :=
      h1.trans (congrArg (fun z : ℂ => ((shellBiasMultiplier p hc).value x : ℂ)*z) h2)
    _ = ((oneBodySquareTotal p).value x : ℂ)*graphComponent s none F x := by rw [←mul_assoc,hsq]
    _ = _ := h3.symm

lemma rawFormPair_shellBias {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) (f : Configuration N → ℝ) :
    rawFormPair (graphFormVector ((shellBiasMultiplier p hc).apply F)) f =
      rawFormPair (graphFormVector F) (fun x => f x*(oneBodySquareTotal p).value x) := by
  unfold rawFormPair
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [(shellBiasMultiplier p hc).apply_value F s] with x hx
  simp only [graphFormVector_value_eq,hx,scaled_norm_sq,shellBias_value_sq,mul_assoc]

lemma formMass_shellBias {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) :
    formMass (graphFormVector ((shellBiasMultiplier p hc).apply F)) =
      weightedMass F (oneBodySquareTotal p).value := by
  have hh := rawFormPair_shellBias p hc F (fun _ => 1)
  simpa only [rawFormPair,one_mul,formMass,weightedMass,graphFormVector_value_eq] using hh

lemma oneBody_deriv_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    Integrable (fun x => (lineDeriv ℝ p.value (x i) (spaceDirections a))^2 * ‖graphComponent s none F x‖^2) := by
  obtain ⟨C,hC⟩ := p.gradient_bound a
  have hd : Continuous (fun x : Configuration N => lineDeriv ℝ p.value (x i) (spaceDirections a)) :=
    (smooth_lineDeriv_continuous p.regular (spaceDirections a)).comp (continuous_apply i)
  apply (Lp.memLp (graphComponent s none F)).norm.integrable_sq.bdd_mul (c := C^2) (hd.pow 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖(lineDeriv ℝ p.value (x i) (spaceDirections a))^2‖ ≤ C^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC (x i)) 2

lemma shellBias_gradient_le {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, (lineDeriv ℝ (shellBiasMultiplier p hc).value x (direction i a))^2 *
          ‖graphComponent s none F x‖^2) ≤ oneBodyGradientError p F := by
  unfold oneBodyGradientError
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro a _
  have hh := oneBody_deriv_integrable p F s i a
  have hn (x : Configuration N) : 0 ≤ (lineDeriv ℝ (shellBiasMultiplier p hc).value x (direction i a))^2 *
          ‖graphComponent s none F x‖^2 := by positivity
  have hb (x : Configuration N) := mul_le_mul_of_nonneg_right (shellBias_deriv_sq_le p hc x i a)
    (sq_nonneg ‖graphComponent s none F x‖)
  have hm := ((aestronglyMeasurable_lineDeriv (𝕜 := ℝ) (v := direction i a) (shellBiasMultiplier p hc).lipschitz.continuous volume).pow 2).mul
    ((Lp.memLp (graphComponent s none F)).aestronglyMeasurable.norm.pow 2)
  apply integral_mono (hh.mono' hm (ae_of_all _ (fun x => by change ‖(lineDeriv ℝ (shellBiasMultiplier p hc).value x (direction i a))^2 * ‖graphComponent s none F x‖^2‖ ≤ _; rw [Real.norm_of_nonneg (hn x)]; exact hb x))) hh
  exact hb

lemma shellBias_price_excess_le {Z lam : ℝ} {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) :
    corePriceExcess Z lam (graphFormVector ((shellBiasMultiplier p hc).apply F)) ≤
      (1/2:ℝ)*oneBodyGradientError p F+
        (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z N F⟫_ℂ).re := by
  have hh := quantum_lipschitz_ims_residual Z F (shellBiasMultiplier p hc)
  have hpair := congrArg (fun T : fermionGraph N => (⟪T,sectorExcessOperator Z N F⟫_ℂ).re)
    (shellBias_double_apply p hc F)
  have hmass := formMass_graph ((shellBiasMultiplier p hc).apply F)
  dsimp only [corePriceExcess]
  have hprice := priceEnergy_eq_of_minimizes hN
  have hg := shellBias_gradient_le p hc F
  have hpr := congrArg (fun t : ℝ => t*formMass (graphFormVector ((shellBiasMultiplier p hc).apply F))) hprice
  have hmul := congrArg (fun t : ℝ => energy Z N*t) hmass
  nlinarith only [hh,hg,hpair,hpr,hmul]

lemma corePriceExcess_scale {N : ℕ} (Z lam c : ℝ) (psi : FormVector N) :
    corePriceExcess Z lam (scaleForm c psi) = c^2*corePriceExcess Z lam psi := by
  unfold corePriceExcess
  rw [formEnergy_scale,formMass_scale]
  ring
lemma rawFormPair_scale {N : ℕ} (c : ℝ) (psi : FormVector N) (f : Configuration N → ℝ) :
    rawFormPair (scaleForm c psi) f = c^2*rawFormPair psi f := by
  unfold rawFormPair
  simp only [scaleForm,scaled_norm_sq,mul_left_comm _ (c^2),integral_const_mul,Finset.mul_sum]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ShellBiasField
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
noncomputable section
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier

lemma shellInnerField_le_closed {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z : ℝ) {h H : ℝ} (hh : h < H) (x : Configuration N) :
    oneBodyInnerField p Z H x ≤ closedShellField p Z h x := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (rawInnerField_le_closed hh Z x (x i)) (sq_nonneg _)

lemma closedShellField_density_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z : ℝ) {h a : ℝ} (ha : 0 < a) (hh : h ≤ a)
    (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖) (F : fermionGraph N) (s : Spins N) :
    Integrable (fun x => closedShellField p Z h x*‖graphComponent s none F x‖^2) := by
  obtain ⟨B,hB⟩ := (oneBodySquareTotal (N := N) p).bound
  have hC : 0 ≤ |Z|/(2*a)+(N:ℝ)/a := by positivity
  have hb (x : Configuration N) : ‖closedShellField p Z h x‖ ≤ (|Z|/(2*a)+(N:ℝ)/a)*B := by
    rw [Real.norm_eq_abs]
    exact (closedShellField_bound p Z ha hh hp x).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hB x)) hC)
  exact (Lp.memLp (graphComponent s none F)).norm.integrable_sq.bdd_mul
    (closedShellField_measurable N p Z h).aestronglyMeasurable (ae_of_all _ hb)

lemma shellInnerIntegral_le_biasPair {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (Z : ℝ) {h H a : ℝ} (ha : 0 < a) (hh : h ≤ a)
    (hH : h < H) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖) (F : fermionGraph N) :
    (∫ x, oneBodyInnerField p Z H x ∂formRawLaw (graphFormVector F)) ≤
      rawFormPair (graphFormVector ((shellBiasMultiplier p hc).apply F)) (shellMeanField p Z h) := by
  rw [rawFormPair_shellBias p hc F]
  have he (x : Configuration N) : shellMeanField p Z h x*(oneBodySquareTotal p).value x = closedShellField p Z h x := by
    rw [mul_comm,oneBodySquareTotal_mul_shellMeanField]
  simp_rw [he]
  rw [formRawLaw_integral (graphFormVector_sobolev F).sobolevVector]
  simp only [formRawDensity,graphFormVector_value_eq,Finset.sum_mul]
  simp_rw [mul_comm (‖graphComponent _ none F _‖^2)]
  rw [integral_finsetSum _ (fun s _ => oneBodyInnerField_density_integrable p Z H F s)]
  unfold rawFormPair
  simp only [graphFormVector_value_eq]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono (oneBodyInnerField_density_integrable p Z H F s)
    (closedShellField_density_integrable p Z ha hh hp F s)
  intro x
  exact mul_le_mul_of_nonneg_right (shellInnerField_le_closed p Z hH x) (sq_nonneg _)

lemma shellBias_normalized_excess {Z lam D : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (F : fermionGraph N)
    (p : SmoothMultiplier spaceDirections) (hc : HasCompactSupport p.value)
    (hm : 0 < formMass (graphFormVector ((shellBiasMultiplier p hc).apply F)))
    (he : corePriceExcess Z lam (graphFormVector ((shellBiasMultiplier p hc).apply F)) ≤
      D*formMass (graphFormVector ((shellBiasMultiplier p hc).apply F))) :
    max (corePriceExcess Z lam (scaleForm (Real.sqrt (formMass
      (graphFormVector ((shellBiasMultiplier p hc).apply F))))⁻¹
        (graphFormVector ((shellBiasMultiplier p hc).apply F)))) 0 ≤ D := by
  let psi := graphFormVector ((shellBiasMultiplier p hc).apply F)
  have hn := corePriceExcess_nonneg (graphFormVector_sobolev ((shellBiasMultiplier p hc).apply F)) hZ hlam
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_left (hn.trans he) hm
  apply max_le _ hD
  rw [corePriceExcess_scale,inv_pow,Real.sq_sqrt hm.le]
  have hi := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hm.le)
  calc
    _ ≤ (formMass psi)⁻¹*(D*formMass psi) := hi
    _ = D := by rw [mul_comm D (formMass psi),←mul_assoc,inv_mul_cancel₀ (show formMass psi ≠ 0 from hm.ne'),one_mul]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellAbsorptionNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

lemma innerScale_price_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    innerScale (1/s^4) s + (1/s^4)^2 ≤ 4*(1/s^4)^2 := by
  have h82 : s^8 ≤ s^2 := pow_le_pow_of_le_one hs.le hs1 (by omega)
  have h85 : s^8 ≤ s^5 := pow_le_pow_of_le_one hs.le hs1 (by omega)
  have h2 := one_div_le_one_div_of_le (pow_pos hs 8) h82
  have h5 := one_div_le_one_div_of_le (pow_pos hs 8) h85
  have he : (1/s^4)/s = 1/s^5 := by field_simp
  have he2 : (1/s^4)^2 = 1/s^8 := by field_simp
  dsimp only [innerScale]
  rw [he,he2]
  linarith

lemma shellMean_price_absorb_bound {C R s u : ℝ} (hC : 1 ≤ C)
    (hR : 16*Real.sqrt C ≤ R) (hs : 0 < s) (hs1 : s ≤ 1) (hu : R*s ≤ u) :
    (4*s/u)*Real.sqrt (C*(innerScale (1/s^4) s+(1/s^4)^2)) ≤ (1/s^4)/2 := by
  have hCp : 0 < C := by linarith
  have hsq : 0 < Real.sqrt C := Real.sqrt_pos.2 hCp
  have hRp : 0 < R := (mul_pos (by norm_num : (0:ℝ)<16) hsq).trans_le hR
  have hup : 0 < u := (mul_pos hRp hs).trans_le hu
  have hlam : 0 < 1/s^4 := by positivity
  have hh := mul_le_mul_of_nonneg_left (innerScale_price_le hs hs1) hCp.le
  have he : Real.sqrt (C*(4*(1/s^4)^2)) = 2*Real.sqrt C*(1/s^4) := by
    have hsqr : (2*Real.sqrt C*(1/s^4))^2 = C*(4*(1/s^4)^2) := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hCp.le]
      ring
    rw [←hsqr,Real.sqrt_sq (by positivity)]
  calc
    _ ≤ (4*s/u)*Real.sqrt (C*(4*(1/s^4)^2)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hh) (by positivity)
    _ = (8*Real.sqrt C*s/u)*(1/s^4) := by rw [he]; ring
    _ ≤ (1/2:ℝ)*(1/s^4) := by
      apply mul_le_mul_of_nonneg_right _ hlam.le
      apply (div_le_iff₀ hup).2
      have h1 := mul_le_mul_of_nonneg_right hR hs.le
      linarith
    _ = _ := by ring

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier
  rawFormPair formMass weightedMass oneBodyGradientError corePriceExcess shellMeanField innerScale

lemma actualShellRadius_ge : 16 ≤ actualShellRadius := le_max_left _ _

lemma shellBias_pair_absorb {Z s u : ℝ} {N : ℕ} (hZ : 0 ≤ Z)
    (hs : 0 < s) (hs1 : s ≤ 1) (hu : actualShellRadius*s ≤ u)
    (F : fermionGraph N) (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value)
    (hp : ∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u)
    (hm : 0 < formMass (graphFormVector ((shellBiasMultiplier p hc).apply F)))
    (hex : corePriceExcess Z (1/s^4) (graphFormVector ((shellBiasMultiplier p hc).apply F)) ≤
      (1/s^4)*formMass (graphFormVector ((shellBiasMultiplier p hc).apply F))) :
    rawFormPair (graphFormVector ((shellBiasMultiplier p hc).apply F)) (shellMeanField p Z s) ≤
      formMass (graphFormVector ((shellBiasMultiplier p hc).apply F))*((1/s^4)/2) := by
  let C := Classical.choose exists_actual_shellMean_constant
  have hC : 1 ≤ C := (Classical.choose_spec exists_actual_shellMean_constant).1
  have hmean := (Classical.choose_spec exists_actual_shellMean_constant).2
  have hlam : 0 < 1/s^4 := by positivity
  have hsu : 16*s ≤ u := (mul_le_mul_of_nonneg_right actualShellRadius_ge hs.le).trans hu
  have hsa : s < u/4 := by linarith
  let psi := graphFormVector ((shellBiasMultiplier p hc).apply F)
  let m := formMass psi
  let phi := scaleForm (Real.sqrt m)⁻¹ psi
  have hphi : FormAdmissible phi := (graphFormVector_sobolev _).normalize hm
  have hphim : formMass phi = 1 := by unfold formMass; exact hphi.2.2.2.2.1
  have he : max (corePriceExcess Z (1/s^4) phi) 0 ≤ 1/s^4 :=
    shellBias_normalized_excess hZ hlam F p hc hm hex
  have hb := hmean Z (1/s^4) N phi hphi.sobolevFermion hphim
    hZ hlam (1/s^4) s u hlam.le hs hsa he p hp
  have hn := shellMean_price_absorb_bound hC (le_max_right 16 (16*Real.sqrt C)) hs hs1 hu
  have hb' : rawFormPair phi (shellMeanField p Z s) ≤ (1/s^4)/2 := hb.trans hn
  have heq : rawFormPair phi (shellMeanField p Z s) = m⁻¹*rawFormPair psi (shellMeanField p Z s) := by
    rw [rawFormPair_scale,inv_pow,Real.sq_sqrt hm.le]
  have hi := mul_le_mul_of_nonneg_left hb' hm.le
  rw [heq,←mul_assoc,mul_inv_cancel₀ hm.ne',one_mul] at hi
  exact hi

 theorem actual_shell_number_oai {Z s u : ℝ} {N : ℕ} (hZ : 0 ≤ Z)
    (hs : 0 < s) (hs1 : s ≤ 1) (hu : actualShellRadius*s ≤ u)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (F : fermionGraph (N+1)) (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value)
    (hp : ∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) :
    (1/s^4)*weightedMass F (oneBodySquareTotal p).value ≤ oneBodyGradientError p F+
      2*(⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  have hlam : 0 < 1/s^4 := by positivity
  have hsu : 16*s ≤ u := (mul_le_mul_of_nonneg_right actualShellRadius_ge hs.le).trans hu
  let psi := graphFormVector ((shellBiasMultiplier p hc).apply F)
  let m := formMass psi
  let X := (1/2:ℝ)*oneBodyGradientError p F+
    (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re
  have hX : corePriceExcess Z (1/s^4) psi ≤ X := shellBias_price_excess_le hN p hc F
  have hXn : 0 ≤ X := (corePriceExcess_nonneg (graphFormVector_sobolev _) hZ hlam).trans hX
  have hmass : m = weightedMass F (oneBodySquareTotal p).value := formMass_shellBias p hc F
  have hmasslam := congrArg (fun t : ℝ => (1/s^4)*t) hmass
  have hgoal : (1/s^4)*m ≤ 2*X := by
    by_contra hfalse
    have hlt : 2*X < (1/s^4)*m := lt_of_not_ge hfalse
    have hm : 0 < m := (mul_pos_iff_of_pos_left hlam).mp
      (lt_of_le_of_lt (by linarith : (0:ℝ) ≤ 2*X) hlt)
    have hb := shellBias_pair_absorb hZ hs hs1 hu F p hc hp hm (hX.trans (by linarith))
    have hfield := shellInnerIntegral_le_biasPair p hc Z (by linarith : 0 < u/4)
      (by linarith : s ≤ u/4) (by linarith : s < 2*s) (fun y hy => by linarith [(hp y hy).1]) F
    have hstep : energy Z (N+1)+(1/s^4) ≤ energy Z N := by
      have hh := hN N
      rw [Nat.cast_add,Nat.cast_one] at hh
      nlinarith only [hh]
    have hshell := quantum_shell_inner_field_residual hZ p F (2*s) hstep
    have hf := hfield.trans hb
    change _ ≤ m*((1/s^4)/2) at hf
    dsimp only [X] at hlt
    nlinarith only [hshell,hf,hlt,hmasslam]
  dsimp only [X] at hgoal
  linarith only [hgoal,hmasslam]

end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.actual_shell_number_oai := @OAI.CoulombAtom.actual_shell_number_oai
