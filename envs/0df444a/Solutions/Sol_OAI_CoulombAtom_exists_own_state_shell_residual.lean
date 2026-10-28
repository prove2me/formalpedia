-- Prove2me | solution 1 for OAI.CoulombAtom.exists_own_state_shell_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:49:25.995972+00:00
-- url     : https://prove2.me/submissions/13ded7bb-82c9-42fc-a036-f33ee198b3f8

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_exists_actual_own_probability_tail_tilt_state

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

lemma weakGraph_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    {ι : Type*} [Fintype ι] (v : ι → E) (F : weakGraph v) :
    ‖F‖ ^ 2 = ‖F.val none‖ ^ 2 + ∑ i : ι, ‖F.val (some i)‖ ^ 2 := by
  change ‖F.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option]

lemma fermionGraph_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖F‖ ^ 2 = ‖fermionGraphValue N F‖ ^ 2 +
      ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ‖graphComponent s (some (i, a)) F‖ ^ 2 := by
  have hF : ‖F‖ ^ 2 = ∑ s : Spins N, ‖F.val s‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hv : ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖(F.val s).val none‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  rw [hF, hv]
  simp only [weakGraph_norm_sq, Fintype.sum_prod_type, Finset.sum_add_distrib,
    graphComponent_apply]

lemma graphNuclear_bound {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (F : fermionGraph N)
    (s : Spins N) (i : Fin N) :
    Z * ‖graphNuclear s i F‖ ^ 2 ≤
      (1 / 4 : ℝ) * (∑ a : Fin 3, ‖graphComponent s (some (i, a)) F‖ ^ 2) +
        Z ^ 2 * ‖graphComponent s none F‖ ^ 2 := by
  have hh := linear_coulomb_bound (ContinuousLinearMap.proj i) (fun a => direction i a)
    (by intro a; simp [direction]) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hZ)
    (Lp.memLp ((F.val s).val none)) (fun a => Lp.memLp ((F.val s).val (some (i, a))))
    (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  simp only [ContinuousLinearMap.proj_apply, ← lp_norm_sq] at hh
  have hn := graphNuclear_norm_sq s i F
  change ‖graphNuclear s i F‖ ^ 2 = ∫ x, ‖(F.val s).val none x‖ ^ 2 / ‖x i‖ at hn
  rw [← hn] at hh
  change 2 * (2 * Z) * ‖graphNuclear s i F‖ ^ 2 ≤
    (∑ a : Fin 3, ‖graphComponent s (some (i, a)) F‖ ^ 2) +
      (2 * Z) ^ 2 * ‖graphComponent s none F‖ ^ 2 at hh
  nlinarith

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

lemma nuclear_sum_arithmetic {S : Type*} [Fintype S] {N : ℕ} (Z : ℝ)
    (A : S → Fin N → ℝ) (K : S → Fin N → Fin 3 → ℝ) (M : S → ℝ)
    (h : ∀ s i, Z * A s i ≤ (1 / 4 : ℝ) * (∑ a, K s i a) + Z ^ 2 * M s) :
    Z * (∑ s, ∑ i, A s i) ≤ (1 / 4 : ℝ) * (∑ s, ∑ i, ∑ a, K s i a) +
      (N : ℝ) * Z ^ 2 * ∑ s, M s := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ => h s i
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_comm (Z ^ 2) (N : ℝ)] using hs

lemma graphNuclear_sum_bound {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (F : fermionGraph N) :
    Z * (∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i F‖ ^ 2) ≤
      (1 / 4 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ‖graphComponent s (some (i, a)) F‖ ^ 2) +
      (N : ℝ) * Z ^ 2 * ‖fermionGraphValue N F‖ ^ 2 := by
  have hs := nuclear_sum_arithmetic Z (fun s i => ‖graphNuclear s i F‖ ^ 2)
    (fun s i a => ‖graphComponent s (some (i, a)) F‖ ^ 2)
    (fun s => ‖graphComponent s none F‖ ^ 2) (graphNuclear_bound hZ F)
  exact hs.trans_eq (congrArg (fun M : ℝ =>
    (1 / 4 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ‖graphComponent s (some (i, a)) F‖ ^ 2) + (N : ℝ) * Z ^ 2 * M)
      (graphValue_norm_sq F).symm)

lemma coulombFormOperator_inner_lower {N : ℕ} (Z : ℝ) (F : fermionGraph N) :
    (1 / 2 : ℝ) * (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ‖graphComponent s (some (i, a)) F‖ ^ 2) -
      Z * (∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i F‖ ^ 2) ≤
        (⟪F, coulombFormOperator Z N F⟫_ℂ).re := by
  have hk : (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x, ‖(graphFormVector F).gradient s i a x‖ ^ 2) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ‖graphComponent s (some (i, a)) F‖ ^ 2 := by
    simp only [lp_norm_sq, graphComponent_apply, graphFormVector]
  have hn : (∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖(graphFormVector F).value s x‖ ^ 2 / ‖x i‖) =
      ∑ s : Spins N, ∑ i : Fin N, ‖graphNuclear s i F‖ ^ 2 := by
    simp only [graphNuclear_norm_sq]
  conv_rhs => rw [coulombFormOperator_inner]; unfold formEnergy; rw [hk, hn]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact integral_nonneg fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)
  · exact le_rfl

lemma coercivity_arithmetic {K M A E C : ℝ} (hM : 0 ≤ M)
    (hA : A ≤ 1 / 4 * K + C * M) (hE : 1 / 2 * K - A ≤ E) :
    1 / 4 * (M + K) ≤ E + (C + 1) * M := by nlinarith

lemma coulombFormOperator_coercive_bound {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (F : fermionGraph N) :
    (1 / 4 : ℝ) * ‖F‖ ^ 2 ≤ (⟪F, coulombFormOperator Z N F⟫_ℂ).re +
      ((N : ℝ) * Z ^ 2 + 1) * ‖fermionGraphValue N F‖ ^ 2 := by
  conv_lhs => rw [fermionGraph_norm_sq F]
  exact coercivity_arithmetic (sq_nonneg _) (graphNuclear_sum_bound hZ F)
    (coulombFormOperator_inner_lower Z F)

end CoulombCoercivity

end CoulombAtom

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

lemma sectorExcessOperator_diagonal {N : ℕ} (Z : ℝ) (F : fermionGraph N) :
    (⟪F,sectorExcessOperator Z N F⟫_ℂ).re =
      formEnergy Z (graphFormVector F)-energy Z N*‖fermionGraphValue N F‖^2 := by
  have hv : (⟪fermionGraphValue N F,fermionGraphValue N F⟫_ℂ).re =
      ‖fermionGraphValue N F‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (fermionGraphValue N F)).symm
  exact (sectorExcessOperator_pair Z F F).trans
    (congrArg₂ (fun u v => u-energy Z N*v) (coulombFormOperator_inner Z N F) hv)

lemma near_minimizer_graph_bound {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2=1)
    (hF : formEnergy Z (graphFormVector F) ≤ energy Z N+1) :
    ‖F‖^2 ≤ 4*(|energy Z N| + (N:ℝ)*Z^2+2) := by
  have hc := coulombFormOperator_coercive_bound hZ F
  rw [coulombFormOperator_inner Z N F,hn] at hc
  nlinarith [le_abs_self (energy Z N)]

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
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellResidualControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue sectorExcessOperator

lemma shellGraphConstant_nonneg (N : ℕ) (r : ℝ) : 0 ≤ shellGraphConstant N r := by
  unfold shellGraphConstant; positivity

end
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue sectorExcessOperator
  weightedMass oneBodyGradientError graphRawLaw

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OwnStateResidual
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
  fermionGraphValue formEnergy energy sectorExcessOperator

lemma OwnProbabilityTailTiltState.mono_error {Z lam r δ δ' : ℝ} {N K : ℕ}
    {p₀ : Fin (K+1) → ℝ} {F : fermionGraph N}
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ δ F) (hδ : δ ≤ δ') :
    OwnProbabilityTailTiltState Z lam r K p₀ δ' F := by
  refine ⟨hF.1,hF.2.1.trans (add_le_add le_rfl hδ),?_⟩
  intro j A hA hp
  obtain ⟨G,hGn,hGlaw,hGE⟩ := hF.2.2 j A hA hp
  exact ⟨G,hGn,hGlaw,hGE.trans (by unfold dyadicUniformEventBudget; exact add_le_add le_rfl hδ)⟩

lemma normalized_sector_excess_le {Z η : ℝ} {N : ℕ} (F : fermionGraph N)
    (hFn : ‖fermionGraphValue N F‖^2 = 1)
    (hFE : formEnergy Z (graphFormVector F) ≤ energy Z N+η) :
    (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η := by
  have he := sectorExcessOperator_diagonal Z F
  have hev : energy Z N * ‖fermionGraphValue N F‖^2 = energy Z N :=
    (congrArg (fun t : ℝ => energy Z N*t) hFn).trans (mul_one _)
  exact he.le.trans ((sub_le_sub_left hev.ge _).trans
    (sub_le_iff_le_add.mpr (by linarith only [hFE])))

lemma exists_small_error_product {A : ℝ} (hA : 0 ≤ A) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η*A ≤ 1 := by
  let η := min 1 (A+1)⁻¹
  have hη : 0 < η := lt_min zero_lt_one (inv_pos.2 (by linarith))
  refine ⟨η,hη,min_le_left _ _,?_⟩
  have hh := mul_le_mul_of_nonneg_right (min_le_right 1 (A+1)⁻¹) (by linarith : 0 ≤ A+1)
  have he : (A+1)⁻¹*(A+1) = 1 := inv_mul_cancel₀ (by linarith)
  change η*(A+1) ≤ _ at hh
  rw [he] at hh
  nlinarith only [hh,hη.le]

lemma own_state_graph_bound {Z lam r η : ℝ} {N K : ℕ}
    {p₀ : Fin (K+1) → ℝ} (hZ : 0 ≤ Z) (hη : η ≤ 1) (F : fermionGraph N)
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ η F) :
    ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) := by
  exact near_minimizer_graph_bound hZ F hF.1
    (hF.2.1.trans (add_le_add le_rfl hη))

lemma smallSectorResidual_of_own {Z lam r η : ℝ} {N K : ℕ}
    {p₀ : Fin (K+1) → ℝ} (hZ : 0 ≤ Z) (hη : η ≤ 1) (F : fermionGraph N)
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ η F) : SmallSectorResidual Z η F :=
  ⟨normalized_sector_excess_le F hF.1 hF.2.1, own_state_graph_bound hZ hη F hF⟩

lemma exists_own_state_small_residual {Z lam r η : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hr : 0 < r) (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : PriceMinimizes (energy Z) lam N) (K : ℕ) (p₀ : Fin (K+1) → ℝ)
    (h₀ : ∀ j, 0 < p₀ j) :
    ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z lam r K p₀ 1 F ∧
      SmallSectorResidual Z η F := by
  obtain ⟨F,hF⟩ := exists_actual_own_probability_tail_tilt_state hZ hr hN K p₀ h₀ hη
  exact ⟨F,hF.mono_error hη1,smallSectorResidual_of_own hZ hη1 F hF⟩

lemma exists_own_state_shell_residual_oai {Z lam r v : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hr : 0 < r) (_hv : 0 < v)
    (hN : PriceMinimizes (energy Z) lam N) (K : ℕ) (p₀ : Fin (K+1) → ℝ)
    (h₀ : ∀ j, 0 < p₀ j) :
    ∃ (F : fermionGraph N) (η : ℝ),
      OwnProbabilityTailTiltState Z lam r K p₀ 1 F ∧ 0 ≤ η ∧ SmallSectorResidual Z η F ∧
      η*(‖sectorExcessOperator Z N‖*shellGraphConstant N v*
        (4*(|energy Z N|+(N:ℝ)*Z^2+2))) ≤ 1^2 := by
  let B := 4*(|energy Z N|+(N:ℝ)*Z^2+2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let A := ‖sectorExcessOperator Z N‖*shellGraphConstant N v*B
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (norm_nonneg _) (shellGraphConstant_nonneg N v)) hB
  obtain ⟨η,hη,hη1,hηA⟩ := exists_small_error_product hA
  obtain ⟨F,hF,hres⟩ := exists_own_state_small_residual hZ hr hη hη1 hN K p₀ h₀
  refine ⟨F,η,hF,hη.le,hres,?_⟩
  exact hηA.trans_eq (by norm_num)
end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.exists_own_state_shell_residual_oai := @OAI.CoulombAtom.exists_own_state_shell_residual_oai
