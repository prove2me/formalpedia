-- Prove2me | solution 1 for OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:46:50.271506+00:00
-- url     : https://prove2.me/submissions/16a80e42-bd37-4ce1-bdab-8a868aab9524

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WeightedVariance
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
namespace CoulombAtom

theorem sector_energies_bddBelow (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) :
    BddBelow {e | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} := by
  refine ⟨-(N : ℝ) * Z ^ 2 / 2, ?_⟩
  rintro e ⟨ψ, hψ, rfl⟩
  exact formEnergy_lower_bound hZ hψ

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

lemma gram_selfAdjoint {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : V →L[ℂ] H) : IsSelfAdjoint (T.adjoint.comp T) :=
  T.isPositive_adjoint_comp_self.isSelfAdjoint

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

lemma coulombFormOperator_selfAdjoint (Z : ℝ) (N : ℕ) : IsSelfAdjoint (coulombFormOperator Z N) := by
  unfold coulombFormOperator
  apply IsSelfAdjoint.add (R := fermionGraph N →L[ℂ] fermionGraph N)
  · apply IsSelfAdjoint.sub (R := fermionGraph N →L[ℂ] fermionGraph N)
    · apply IsSelfAdjoint.smul (R := ℂ) (A := fermionGraph N →L[ℂ] fermionGraph N)
      · norm_num [IsSelfAdjoint]
      · apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro s _
        apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro i _
        apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro a _
        exact gram_selfAdjoint _
    · apply IsSelfAdjoint.smul (R := ℂ) (A := fermionGraph N →L[ℂ] fermionGraph N)
      · exact Complex.conj_ofReal Z
      · apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro s _
        apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
        intro i _
        exact gram_selfAdjoint _
  · apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
    intro s _
    apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
    intro i _
    apply isSelfAdjoint_sum (R := fermionGraph N →L[ℂ] fermionGraph N)
    intro j _
    split_ifs
    · exact gram_selfAdjoint _
    · exact IsSelfAdjoint.zero _

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

lemma graphFormVector_admissible {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖ ^ 2 = 1) : FormAdmissible (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    exact ((mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property
      (i, a)) φ hφ hcφ
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s
  · have hmass := graphValue_norm_sq F
    rw [hn] at hmass
    simpa only [lp_norm_sq, graphComponent_apply, graphFormVector] using hmass.symm
  · intro s i
    exact nuclear_integrable i (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  · intro s i j hij
    exact pair_integrable i j hij (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))

lemma graphFormVector_admissibleGraph_value {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (s : Spins N) :
    (graphFormVector (admissibleGraph ψ hψ)).value s =ᵐ[volume] ψ.value s := by
  simpa only [graphFormVector, admissibleGraph, WithLp.ofLp_toLp,
    admissibleWeakGraph_value] using (hψ.1 s).coeFn_toLp

lemma graphFormVector_admissibleGraph_gradient {N : ℕ} (ψ : FormVector N)
    (hψ : FormAdmissible ψ) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphFormVector (admissibleGraph ψ hψ)).gradient s i a =ᵐ[volume] ψ.gradient s i a := by
  simpa only [graphFormVector, admissibleGraph, WithLp.ofLp_toLp,
    admissibleWeakGraph_gradient] using (hψ.2.1 s i a).coeFn_toLp

lemma admissibleGraph_norm {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ) :
    ‖fermionGraphValue N (admissibleGraph ψ hψ)‖ ^ 2 = 1 := by
  calc
    _ = ∑ s : Spins N, ∫ x, ‖(graphFormVector (admissibleGraph ψ hψ)).value s x‖ ^ 2 := by
      rw [graphValue_norm_sq]
      simp only [lp_norm_sq, graphComponent_apply, graphFormVector]
    _ = ∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      apply integral_congr_ae
      filter_upwards [graphFormVector_admissibleGraph_value ψ hψ s] with x hx
      rw [hx]
    _ = 1 := hψ.2.2.2.2.1

lemma formEnergy_congr_ae {N : ℕ} (Z : ℝ) (ψ φ : FormVector N)
    (hv : ∀ s, ψ.value s =ᵐ[volume] φ.value s)
    (hg : ∀ s i a, ψ.gradient s i a =ᵐ[volume] φ.gradient s i a) :
    formEnergy Z ψ = formEnergy Z φ := by
  have hk : (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖φ.gradient s i a x‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    apply integral_congr_ae
    filter_upwards [hg s i a] with x hx
    rw [hx]
  have hn : (∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖) =
      ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖φ.value s x‖ ^ 2 / ‖x i‖ := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hv s] with x hx
    rw [hx]
  have hp : (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖ else 0) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then ∫ x, ‖φ.value s x‖ ^ 2 / ‖x i - x j‖ else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · apply integral_congr_ae
      filter_upwards [hv s] with x hx
      rw [hx]
    · rfl
  unfold formEnergy
  rw [hk, hn, hp]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormBottom
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
namespace CoulombAtom
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace V] [CompleteSpace H] in
lemma form_lower_of_unit (j : V →L[ℂ] H) (hj : Function.Injective j)
    (A : V →L[ℂ] V) {b : ℝ}
    (hb : ∀ u, ‖j u‖ ^ 2 = 1 → b ≤ (⟪u, A u⟫_ℂ).re) (u : V) :
    b * ‖j u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re := by
  by_cases hz : j u = 0
  · have hu : u = 0 := hj (hz.trans (map_zero j).symm)
    simp [hu]
  have hn : 0 < ‖j u‖ := norm_pos_iff.mpr hz
  let v : V := (‖j u‖⁻¹ : ℂ) • u
  have hnv : ‖j v‖ ^ 2 = 1 := by
    simp [v, norm_smul, hn.ne']
  have hv := hb v hnv
  have he : (⟪v, A v⟫_ℂ).re = (‖j u‖ ^ 2)⁻¹ * (⟪u, A u⟫_ℂ).re := by
    simp [v, Complex.mul_re, pow_two]
    ring
  rw [he] at hv
  simpa only [mul_comm] using (le_inv_mul_iff₀ (sq_pos_of_pos hn)).mp hv

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

lemma energy_le_graphForm {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hF : ‖fermionGraphValue N F‖ ^ 2 = 1) :
    energy Z N ≤ (⟪F, coulombFormOperator Z N F⟫_ℂ).re := by
  rw [coulombFormOperator_inner]
  unfold energy
  split_ifs with hN
  · subst N
    simp [formEnergy]
  · exact csInf_le (sector_energies_bddBelow Z hZ N)
      ⟨graphFormVector F, graphFormVector_admissible F hF, rfl⟩

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumRawLaw_scope

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CoulombAtom

attribute [local irreducible] graphComponent fermionGraphValue

lemma graphRawDensity_measurable {N : ℕ} (F : fermionGraph N) :
    Measurable (graphRawDensity F) := by
  apply Finset.measurable_sum
  intro s _
  exact (Lp.stronglyMeasurable (graphComponent s none F)).measurable.norm.pow_const 2

lemma graphRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ, hn, ENNReal.ofReal_one]

lemma graphRawLaw_integral {N : ℕ} (F : fermionGraph N) (g : Configuration N → ℝ) :
    (∫ x, g x ∂graphRawLaw F) = ∫ x, graphRawDensity F x * g x := by
  rw [graphRawLaw, integral_withDensity_eq_integral_toReal_smul
    (graphRawDensity_measurable F).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (graphRawDensity_nonneg F _), smul_eq_mul]

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ArraySymmetry
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

lemma flatRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (flatRawLaw F) := by
  let := graphRawLaw_probability F hn
  unfold flatRawLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma quantumEventProbability_eq_flat {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)}
    (hs : MeasurableSet s) :
    quantumEventProbability F b s = ∫ x, arrayLikelihood b s x ∂flatRawLaw F := by
  symm
  exact integral_map (flattenConfiguration N).measurable.aemeasurable
    ((arrayLikelihood_contDiff b hs (n := 1)).continuous.measurable.aestronglyMeasurable)

lemma quantumEventLikelihood_nonneg {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration N) : 0 ≤ quantumEventLikelihood b s x :=
  arrayLikelihood_nonneg b hs _

lemma quantumEventLikelihood_measurable {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s) :
    Measurable (quantumEventLikelihood b s) :=
  (arrayLikelihood_contDiff b hs (n := 1)).continuous.measurable.comp
    (flattenConfiguration N).measurable

end CoulombAtom

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

lemma sqrtArrayLikelihood_lineDeriv_sq {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ)
    {k : ℕ} (hk : 0 < k) :
    (∑ i, (lineDeriv ℝ (fun y => Real.sqrt (arrayLikelihood b s y)) x
      (Pi.single i 1))^2) ≤
      (observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(1-(k:ℝ)⁻¹) := by
  classical
  have hp := arrayLikelihood_nonneg b hs x
  have hC := observationMomentConstant_pos
  by_cases hzero : arrayLikelihood b s x = 0
  · have hz (v : I → ℝ) : lineDeriv ℝ (fun y => Real.sqrt (arrayLikelihood b s y)) x v = 0 :=
      lineDeriv_sqrt_of_zero (arrayLikelihood_nonneg b hs) hzero v
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero]
    positivity
  have hpos : 0 < arrayLikelihood b s x := lt_of_le_of_ne hp (Ne.symm hzero)
  have hd := (arrayLikelihood_contDiff b hs (n := 1)).differentiable one_ne_zero x
  simp only [lineDeriv_sqrt_of_pos hd hpos, arrayLikelihood_fderiv b hs,
    Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', Finset.mem_univ, ite_true,
    div_pow, neg_sq, mul_pow, Real.sq_sqrt hp]
  rw [← sum_div]
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^2*arrayLikelihood b s x)).mpr
  calc
    _ ≤ observationMomentConstant * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(2-(k:ℝ)⁻¹) := arrayScore_sq b hs x hk
    _ = (observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(1-(k:ℝ)⁻¹) * ((2:ℝ)^2*arrayLikelihood b s x) := by
      rw [show (2-(k:ℝ)⁻¹) = (1-(k:ℝ)⁻¹)+1 by ring,
        Real.rpow_add hpos, Real.rpow_one]
      ring

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationIntegral
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
section Work_ObservationIntegral_scope

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

lemma integrable_bounded_probability {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {q : Ω → ℝ} (hq : Measurable q)
    (hn : ∀ x, 0 ≤ q x) (hb : ∀ x, q x ≤ 1) : Integrable q μ := by
  apply (integrable_const (1:ℝ)).mono' hq.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn x)] using hb x)

lemma bounded_probability_rpow_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {q : Ω → ℝ} (hq : Measurable q)
    (hn : ∀ x, 0 ≤ q x) (hb : ∀ x, q x ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x => q x ^ a) μ := by
  apply integrable_bounded_probability (hq.pow_const a)
  · exact fun x => Real.rpow_nonneg (hn x) _
  · exact fun x => Real.rpow_le_one (hn x) (hb x) ha

lemma integral_bounded_probability_rpow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {q : Ω → ℝ} (hq : Measurable q)
    (hn : ∀ x, 0 ≤ q x) (hb : ∀ x, q x ≤ 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ x, q x ^ a ∂μ) ≤ (∫ x, q x ∂μ)^a := by
  apply (Real.concaveOn_rpow ha ha1).le_map_integral
  · exact (Real.continuous_rpow_const ha).continuousOn
  · exact isClosed_Ici
  · exact ae_of_all _ hn
  · exact integrable_bounded_probability hq hn hb
  · exact bounded_probability_rpow_integrable hq hn hb ha

lemma eventMomentOrder_pos (p : ℝ) : 0 < eventMomentOrder p := by
  unfold eventMomentOrder; omega

lemma eventMomentOrder_bound {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (eventMomentOrder p : ℝ) ≤ 2*(1-Real.log p) := by
  have hl := Real.log_nonpos hp.le hp1
  have hc := Nat.ceil_lt_add_one (show 0 ≤ -Real.log p by linarith)
  dsimp [eventMomentOrder]
  push_cast
  linarith

lemma eventMomentOrder_rpow_bound {p : ℝ} (hp : 0 < p) :
    p ^ (-((eventMomentOrder p : ℝ)⁻¹)) ≤ Real.exp 1 := by
  rw [Real.rpow_def_of_pos hp, Real.exp_le_exp]
  have hk : (0:ℝ) < eventMomentOrder p := by exact_mod_cast eventMomentOrder_pos p
  have hc := Nat.le_ceil (-Real.log p)
  have hle : -Real.log p ≤ (eventMomentOrder p : ℝ) := by
    dsimp [eventMomentOrder]; push_cast; linarith
  rw [mul_neg, ← neg_mul, ← div_eq_mul_inv, div_le_iff₀ hk]
  simpa using hle

lemma eventMomentOrder_integral_bound {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (eventMomentOrder p : ℝ)^5 * p^(1-(eventMomentOrder p:ℝ)⁻¹) ≤
      (32*Real.exp 1)*(1-Real.log p)^5*p := by
  have hl : 0 ≤ 1-Real.log p := by linarith [Real.log_nonpos hp.le hp1]
  have hk : 0 ≤ (eventMomentOrder p : ℝ) := Nat.cast_nonneg _
  have hpow := pow_le_pow_left₀ hk (eventMomentOrder_bound hp hp1) 5
  have hprod := mul_le_mul hpow (eventMomentOrder_rpow_bound hp)
    (Real.rpow_nonneg hp.le _) (by positivity : 0 ≤ (2*(1-Real.log p))^5)
  rw [sub_eq_add_neg, Real.rpow_add hp, Real.rpow_one]
  calc
    _ = ((eventMomentOrder p : ℝ)^5 * p^(-((eventMomentOrder p:ℝ)⁻¹)))*p := by ring
    _ ≤ (2*(1-Real.log p))^5 * Real.exp 1 * p := mul_le_mul_of_nonneg_right hprod hp.le
    _ = _ := by ring

lemma eventLog_eq {p : ℝ} (hp : 0 < p) : Real.log (Real.exp 1/p) = 1-Real.log p := by
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hp), Real.log_exp]

end Work_ObservationIntegral_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

lemma arrayFisher_nonneg {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (x : I → ℝ) : 0 ≤ arrayFisher b s x :=
  sum_nonneg (fun _ _ => sq_nonneg _)

lemma arrayFisher_measurable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) :
    Measurable (arrayFisher b s) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_lineDeriv (sqrtArrayLikelihood_lipschitz b hs).continuous).pow_const 2

lemma reciprocal_moment_sub_one_nonneg {k : ℕ} (hk : 0 < k) : 0 ≤ 1-(k:ℝ)⁻¹ := by
  have hh : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hi : (k:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hh
  linarith

lemma arrayFisher_integrable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s)
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] : Integrable (arrayFisher b s) μ := by
  have hC := observationMomentConstant_pos
  have hbound (x : I → ℝ) : arrayFisher b s x ≤
      (observationMomentConstant/4) * ∑ j, (b j)^2 := by
    simpa [arrayFisher] using sqrtArrayLikelihood_lineDeriv_sq b hs x (k := 1) (by decide)
  apply (integrable_const ((observationMomentConstant/4) * ∑ j, (b j)^2)).mono'
    (arrayFisher_measurable b hs).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (arrayFisher_nonneg b s x)] using hbound x

lemma arrayFisher_integral_moment {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s)
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k) :
    (∫ x, arrayFisher b s x ∂μ) ≤
      (observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (∫ x, arrayLikelihood b s x ∂μ)^(1-(k:ℝ)⁻¹) := by
  have ha := reciprocal_moment_sub_one_nonneg hk
  have ha1 : 1-(k:ℝ)⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hq := (arrayLikelihood_contDiff b hs (n := 1)).continuous.measurable
  have hC := observationMomentConstant_pos
  have hj := integral_bounded_probability_rpow (μ := μ) hq
    (arrayLikelihood_nonneg b hs) (arrayLikelihood_le_one b hs) ha ha1
  calc
    _ ≤ ∫ x, (observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(1-(k:ℝ)⁻¹) ∂μ := by
      apply integral_mono (arrayFisher_integrable b hs μ)
        ((bounded_probability_rpow_integrable hq (arrayLikelihood_nonneg b hs)
          (arrayLikelihood_le_one b hs) ha).const_mul _)
      exact fun x => sqrtArrayLikelihood_lineDeriv_sq b hs x hk
    _ = ((observationMomentConstant/4) * (k:ℝ)^5 * (∑ j, (b j)^2)) *
        ∫ x, (arrayLikelihood b s x)^(1-(k:ℝ)⁻¹) ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hj (by positivity)

lemma observationFisherConstant_pos : 0 < observationFisherConstant := by
  unfold observationFisherConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) observationMomentConstant_pos

theorem arrayFisher_integral_log {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s)
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hp : 0 < ∫ x, arrayLikelihood b s x ∂μ) :
    (∫ x, arrayFisher b s x ∂μ) ≤
      observationFisherConstant * (∑ j, (b j)^2) *
        (Real.log (Real.exp 1/(∫ x, arrayLikelihood b s x ∂μ)))^5 *
        (∫ x, arrayLikelihood b s x ∂μ) := by
  let p := ∫ x, arrayLikelihood b s x ∂μ
  have hp1 : p ≤ 1 := by
    have h := integral_mono
      (integrable_bounded_probability (μ := μ) ((arrayLikelihood_contDiff b hs (n:=1)).continuous.measurable)
        (arrayLikelihood_nonneg b hs) (arrayLikelihood_le_one b hs))
      (integrable_const (1:ℝ)) (arrayLikelihood_le_one b hs)
    simpa [p] using h
  have hC := observationMomentConstant_pos
  have hb : 0 ≤ ∑ j, (b j)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound := arrayFisher_integral_moment b hs μ (eventMomentOrder_pos p)
  have hlog := mul_le_mul_of_nonneg_left (eventMomentOrder_integral_bound hp hp1)
    (show 0 ≤ observationMomentConstant/4 * ∑ j, (b j)^2 by positivity)
  change _ ≤ observationFisherConstant * (∑ j, (b j)^2) * Real.log (Real.exp 1/p)^5 * p
  rw [eventLog_eq hp]
  calc
    _ ≤ (observationMomentConstant/4) * (eventMomentOrder p:ℝ)^5 * (∑ j, (b j)^2) *
        p^(1-(eventMomentOrder p:ℝ)⁻¹) := hbound
    _ = (observationMomentConstant/4 * ∑ j, (b j)^2) *
        ((eventMomentOrder p:ℝ)^5 * p^(1-(eventMomentOrder p:ℝ)⁻¹)) := by ring
    _ ≤ (observationMomentConstant/4 * ∑ j, (b j)^2) *
        ((32*Real.exp 1)*(1-Real.log p)^5*p) := hlog
    _ = _ := by dsimp [observationFisherConstant]; ring

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_QuantumEventMultiplier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

lemma quantumEventMultiplier_sq {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) {p : ℝ} (hp : 0 < p) (x : Configuration N) :
    (quantumEventMultiplier b hs hsy p).value x ^ 2 =
      p⁻¹ * quantumEventLikelihood b s x := by
  rw [quantumEventMultiplier_value, mul_pow, inv_pow, Real.sq_sqrt hp.le,
    Real.sq_sqrt (quantumEventLikelihood_nonneg b hs x)]

lemma quantumEventMultiplier_lineDeriv {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (p : ℝ) (x : Configuration N) (i : Fin N) (a : Fin 3) :
    lineDeriv ℝ (quantumEventMultiplier b hs hsy p).value x (direction i a) =
      (Real.sqrt p)⁻¹ * lineDeriv ℝ (fun y => Real.sqrt (arrayLikelihood b s y))
        (flattenConfiguration N x) (Pi.single (i,a) 1) := by
  change deriv (fun t => (Real.sqrt p)⁻¹ *
    Real.sqrt (quantumEventLikelihood b s (x + t • direction i a))) 0 = _
  rw [deriv_const_mul_field]
  exact congrArg ((Real.sqrt p)⁻¹ * ·)
    (lineDeriv_flattenConfiguration (fun y => Real.sqrt (arrayLikelihood b s y)) x i a)

lemma quantumEventMultiplier_fisher {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) {p : ℝ} (hp : 0 < p) (x : Configuration N) :
    (∑ q : Fin N × Fin 3,
      (lineDeriv ℝ (quantumEventMultiplier b hs hsy p).value x (direction q.1 q.2))^2) =
    p⁻¹ * arrayFisher b s (flattenConfiguration N x) := by
  simp only [quantumEventMultiplier_lineDeriv, mul_pow, inv_pow, Real.sq_sqrt hp.le,
    arrayFisher, mul_sum]

lemma quantumEventMultiplier_fisher_integral {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (hp : 0 < quantumEventProbability F b s) :
    (∫ x, ∑ q : Fin N × Fin 3,
      (lineDeriv ℝ (quantumEventMultiplier b hs hsy (quantumEventProbability F b s)).value x
        (direction q.1 q.2))^2 ∂graphRawLaw F) ≤
      observationFisherConstant * (∑ j, (b j)^2) *
        (Real.log (Real.exp 1/quantumEventProbability F b s))^5 := by
  let := flatRawLaw_probability F hn
  simp only [quantumEventMultiplier_fisher b hs hsy hp]
  rw [integral_const_mul, ← integral_map (flattenConfiguration N).measurable.aemeasurable
    (arrayFisher_measurable b hs).aestronglyMeasurable]
  have hp' := hp
  rw [quantumEventProbability_eq_flat F b hs] at hp'
  have hh := arrayFisher_integral_log b hs (flatRawLaw F) hp'
  rw [← quantumEventProbability_eq_flat F b hs] at hh
  calc
    _ ≤ (quantumEventProbability F b s)⁻¹ *
        (observationFisherConstant * (∑ j, (b j)^2) *
          (Real.log (Real.exp 1/quantumEventProbability F b s))^5 *
            quantumEventProbability F b s) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumMultiplierLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumMultiplierLaw_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom

lemma finite_product_integral {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    (μ : Measure α) (f : ι → α → ℝ) (g : κ → α → ℝ)
    (hi : ∀ i k, Integrable (fun x => f i x * g k x) μ) :
    (∑ k, ∑ i, ∫ x, f i x * g k x ∂μ) =
      ∫ x, (∑ k, g k x) * (∑ i, f i x) ∂μ := by
  have he (x : α) : (∑ k, g k x) * (∑ i, f i x) = ∑ k, ∑ i, f i x * g k x := by
    rw [sum_mul]
    simp only [mul_sum]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp only [he]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => hi i k))]
  apply sum_congr rfl
  intro k _
  exact (integral_finsetSum _ (fun i _ => hi i k)).symm

attribute [local irreducible] graphComponent fermionGraphValue FermionLipschitzMultiplier.apply

lemma FermionLipschitzMultiplier.apply_rawDensity {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    graphRawDensity (p.apply F) =ᵐ[volume] fun x => (p.value x)^2 * graphRawDensity F x := by
  have ha : ∀ᵐ x, ∀ s : Spins N,
      graphComponent s none (p.apply F) x = (p.value x : ℂ) * graphComponent s none F x :=
    ae_all_iff.mpr (fun s => p.apply_value F s)
  filter_upwards [ha] with x hx
  simp only [graphRawDensity, hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, mul_sum]

lemma FermionLipschitzMultiplier.apply_rawLaw {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    graphRawLaw (p.apply F) = (graphRawLaw F).withDensity (fun x => ENNReal.ofReal ((p.value x)^2)) := by
  unfold graphRawLaw
  rw [← withDensity_mul volume (graphRawDensity_measurable F).ennreal_ofReal
    (p.lipschitz.continuous.measurable.pow_const 2).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [p.apply_rawDensity F] with x hx
  rw [hx, ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

lemma FermionLipschitzMultiplier.apply_norm_sq {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    ‖fermionGraphValue N (p.apply F)‖^2 = ∫ x, (p.value x)^2 ∂graphRawLaw F := by
  rw [← graphRawDensity_integral, graphRawLaw_integral]
  apply integral_congr_ae
  filter_upwards [p.apply_rawDensity F] with x hx
  exact hx.trans (mul_comm _ _)

lemma FermionLipschitzMultiplier.deriv_component_integrable {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    Integrable (fun x => (lineDeriv ℝ p.value x (direction i a))^2 *
      ‖graphComponent s none F x‖^2) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable
    (graphComponent s none F))).mp (Lp.memLp _)
  have hb (x : Configuration N) :
      ‖(lineDeriv ℝ p.value x (direction i a))^2‖ ≤ (p.constant * ‖direction i a‖)^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hd := norm_lineDeriv_le_of_lipschitz ℝ p.lipschitz (x₀ := x) (v := direction i a)
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hd 2
  exact hi.bdd_mul ((measurable_lineDeriv p.lipschitz.continuous).pow_const 2).aestronglyMeasurable
    (ae_of_all _ hb)

lemma FermionLipschitzMultiplier.gradient_rawLaw {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x, (lineDeriv ℝ p.value x (direction i a))^2 * ‖graphComponent s none F x‖^2) =
    ∫ x, ∑ q : Fin N × Fin 3, (lineDeriv ℝ p.value x (direction q.1 q.2))^2
      ∂graphRawLaw F := by
  rw [graphRawLaw_integral]
  have hh := finite_product_integral volume
    (fun (q : Fin N × Fin 3) (x : Configuration N) =>
      (lineDeriv ℝ p.value x (direction q.1 q.2))^2)
    (fun (s : Spins N) (x : Configuration N) => ‖graphComponent s none F x‖^2)
    (fun q s => p.deriv_component_integrable F s q.1 q.2)
  simpa only [graphRawDensity, Fintype.sum_prod_type] using hh

end CoulombAtom

end Work_QuantumMultiplierLaw_scope

section Work_EventPosterior_scope

open MeasureTheory Set
open scoped ENNReal

namespace CoulombObservation

lemma event_raw_marginal {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {A : Set (α × β)} (hA : MeasurableSet A) :
    Measure.map Prod.fst ((μ.prod ν).restrict A) =
      μ.withDensity (fun x => ν (Prod.mk x ⁻¹' A)) := by
  ext t ht
  rw [Measure.map_apply measurable_fst ht, Measure.restrict_apply (measurable_fst ht),
    Measure.prod_apply ((measurable_fst ht).inter hA), withDensity_apply _ ht,
    ← lintegral_indicator ht]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ t
  · have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' t ∩ A) = Prod.mk x ⁻¹' A := by
      ext y
      simp [hx]
    rw [he, indicator_of_mem hx]
  · have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' t ∩ A) = ∅ := by
      ext y
      simp [hx]
    rw [he, measure_empty, indicator_of_notMem hx]

end CoulombObservation

end Work_EventPosterior_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

lemma quantumObservationEvent_measurable {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (quantumObservationEvent b s) := by
  apply hs.preimage
  exact (((observationPlacement b).measurable.comp (flattenConfiguration N).measurable).comp
    measurable_fst).add measurable_snd

lemma quantumEventLikelihood_ofReal {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration N) :
    ENNReal.ofReal (quantumEventLikelihood b s x) =
      (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))
        (Prod.mk x ⁻¹' quantumObservationEvent b s) := by
  unfold quantumEventLikelihood
  rw [arrayLikelihood_eq_probability b hs]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

lemma quantumEventProbability_ofReal {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s) :
    ENNReal.ofReal (quantumEventProbability F b s) =
      ((graphRawLaw F).prod (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw)))
        (quantumObservationEvent b s) := by
  let := graphRawLaw_probability F hn
  have hi := integrable_bounded_probability (μ := graphRawLaw F)
    (quantumEventLikelihood_measurable b hs) (quantumEventLikelihood_nonneg b hs)
    (quantumEventLikelihood_le_one b hs)
  rw [quantumEventProbability, ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (quantumEventLikelihood_nonneg b hs)),
    Measure.prod_apply (quantumObservationEvent_measurable b hs)]
  exact lintegral_congr (quantumEventLikelihood_ofReal b hs)

lemma quantumEventMultiplier_rawLaw {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)}
    (hs : MeasurableSet s) (hsy : QuantumEventSymmetric s)
    (hp : 0 < quantumEventProbability F b s) :
    graphRawLaw ((quantumEventMultiplier b hs hsy (quantumEventProbability F b s)).apply F) =
      (ENNReal.ofReal (quantumEventProbability F b s))⁻¹ •
        Measure.map Prod.fst
          (((graphRawLaw F).prod
            (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
              (quantumObservationEvent b s)) := by
  rw [FermionLipschitzMultiplier.apply_rawLaw,
    event_raw_marginal _ _ (quantumObservationEvent_measurable b hs)]
  simp only [quantumEventMultiplier_sq b hs hsy hp,
    ENNReal.ofReal_mul (inv_nonneg.mpr hp.le), ENNReal.ofReal_inv_of_pos hp,
    ← quantumEventLikelihood_ofReal b hs]
  exact withDensity_smul _ (quantumEventLikelihood_measurable b hs).ennreal_ofReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_QuantumEventTilt
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

lemma quantumEventMultiplier_normalized {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)}
    (hs : MeasurableSet s) (hsy : QuantumEventSymmetric s)
    (hp : 0 < quantumEventProbability F b s) :
    ‖fermionGraphValue N
      ((quantumEventMultiplier b hs hsy (quantumEventProbability F b s)).apply F)‖^2 = 1 := by
  rw [FermionLipschitzMultiplier.apply_norm_sq]
  simp only [quantumEventMultiplier_sq b hs hsy hp]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ hp.ne'

end CoulombAtom

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

attribute [local irreducible] FermionMultiplier.apply graphComponent
  fermionGraphValue coulombFormOperator graphFormVector formEnergy

lemma quantum_form_above_sector {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ} (F : fermionGraph N) :
    energy Z N * ‖fermionGraphValue N F‖ ^ 2 ≤ formEnergy Z (graphFormVector F) := by
  rw [← coulombFormOperator_inner]
  exact form_lower_of_unit (fermionGraphValue N) (fermionGraphValue_injective N)
    (coulombFormOperator Z N) (fun U hU => energy_le_graphForm hZ U hU) F

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

lemma positive_map_cauchy_re {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (hB : B.IsPositive) (F G : V) :
    (⟪G, B F⟫_ℂ).re ^ 2 ≤ (⟪F, B F⟫_ℂ).re * (⟪G, B G⟫_ℂ).re := by
  have hs : (⟪F, B G⟫_ℂ).re = (⟪G, B F⟫_ℂ).re := by
    have hh := hB.isSymmetric F G
    change ⟪B F,G⟫_ℂ = ⟪F,B G⟫_ℂ at hh
    rw [← hh]
    exact inner_re_symm (𝕜 := ℂ) _ _
  have hp (t : ℝ) : 0 ≤ (⟪F, B F⟫_ℂ).re +
      2*t*(⟪G, B F⟫_ℂ).re+t*t*(⟪G, B G⟫_ℂ).re := by
    have hh := hB.re_inner_nonneg_right (F+(t:ℂ) • G)
    change 0 ≤ (⟪F+(t:ℂ) • G,B (F+(t:ℂ) • G)⟫_ℂ).re at hh
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, hs] at hh
    nlinarith
  have hd := discrim_le_zero (a := (⟪G,B G⟫_ℂ).re)
    (b := 2*(⟪G,B F⟫_ℂ).re) (c := (⟪F,B F⟫_ℂ).re) (fun t => by
      nlinarith [hp t])
  dsimp [discrim] at hd
  nlinarith

lemma shifted_form_positive {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (j : V →L[ℂ] H) (A : V →L[ℂ] V) (hs : IsSelfAdjoint A) (E : ℝ)
    (hlow : ∀ F, E*‖j F‖^2 ≤ (⟪F,A F⟫_ℂ).re) :
    (A-(E:ℂ) • (j.adjoint.comp j)).IsPositive := by
  have hBs : IsSelfAdjoint (A-(E:ℂ) • (j.adjoint.comp j)) :=
    IsSelfAdjoint.sub (R := V →L[ℂ] V) hs
      (IsSelfAdjoint.smul (R := ℂ) (A := V →L[ℂ] V)
        (Complex.conj_ofReal E) j.isPositive_adjoint_comp_self.isSelfAdjoint)
  refine ⟨hBs.isSymmetric,fun F => ?_⟩
  change 0 ≤ (⟪(A-(E:ℂ) • (j.adjoint.comp j)) F,F⟫_ℂ).re
  have hre : (⟪(A-(E:ℂ) • (j.adjoint.comp j)) F,F⟫_ℂ).re =
      (⟪F,(A-(E:ℂ) • (j.adjoint.comp j)) F⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hre]
  simp only [sub_apply,smul_apply,inner_sub_right,inner_smul_right,
    ContinuousLinearMap.comp_apply,j.adjoint_inner_right,
    Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  have hv := norm_sq_eq_re_inner (𝕜 := ℂ) (j F)
  change ‖j F‖^2 = (⟪j F,j F⟫_ℂ).re at hv
  rw [← hv]
  exact sub_nonneg.mpr (hlow F)

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

lemma graphForm_lower {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ} (F : fermionGraph N) :
    energy Z N * ‖fermionGraphValue N F‖ ^ 2 ≤
      (⟪F, coulombFormOperator Z N F⟫_ℂ).re := by
  rw [coulombFormOperator_inner Z N F]
  exact quantum_form_above_sector hZ F

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

lemma sectorExcessOperator_positive {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) :
    (sectorExcessOperator Z N).IsPositive := by
  unfold sectorExcessOperator
  exact shifted_form_positive (fermionGraphValue N) (coulombFormOperator Z N)
    (coulombFormOperator_selfAdjoint Z N) (energy Z N) (graphForm_lower hZ)

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

lemma l2_real_multiplier_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g : Lp ℂ 2 μ) (p : X → ℝ) {C : ℝ} (hC : ∀ x, |p x| ≤ C)
    (hg : (g : X → ℂ) =ᵐ[μ] fun x => (p x : ℂ)*f x) :
    ‖g‖^2 ≤ C^2*‖f‖^2 := by
  rw [l2_norm_sq,l2_norm_sq,← integral_const_mul]
  apply integral_mono_ae (Lp.memLp g).norm.integrable_sq
    ((Lp.memLp f).norm.integrable_sq.const_mul _)
  filter_upwards [hg] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hC x) 2) (sq_nonneg _)

lemma complex_two_weight_bound (p q : ℝ) (a b : ℂ) {C D : ℝ}
    (hC : |p| ≤ C) (hD : |q| ≤ D) :
    ‖(p:ℂ)*a+(q:ℂ)*b‖^2 ≤ 2*C^2*‖a‖^2+2*D^2*‖b‖^2 := by
  have hh := norm_add_le ((p:ℂ)*a) ((q:ℂ)*b)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs] at hh
  have hp2 := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hC 2) (sq_nonneg ‖a‖)
  have hq2 := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hD 2) (sq_nonneg ‖b‖)
  have ht := sq_nonneg (|p| * ‖a‖-|q| * ‖b‖)
  have hu : 0 ≤ |p| * ‖a‖+|q| * ‖b‖ := by positivity
  nlinarith [sq_le_sq₀ (norm_nonneg ((p:ℂ)*a+(q:ℂ)*b)) hu |>.2 hh]

lemma l2_two_multiplier_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g h : Lp ℂ 2 μ) (p q : X → ℝ) {C D : ℝ}
    (hC : ∀ x, |p x| ≤ C) (hD : ∀ x, |q x| ≤ D)
    (hh : (h : X → ℂ) =ᵐ[μ] fun x => (p x:ℂ)*f x+(q x:ℂ)*g x) :
    ‖h‖^2 ≤ 2*C^2*‖f‖^2+2*D^2*‖g‖^2 := by
  rw [l2_norm_sq,l2_norm_sq,l2_norm_sq,← integral_const_mul,← integral_const_mul,
    ← integral_add ((Lp.memLp f).norm.integrable_sq.const_mul _)
      ((Lp.memLp g).norm.integrable_sq.const_mul _)]
  apply integral_mono_ae (Lp.memLp h).norm.integrable_sq
    (((Lp.memLp f).norm.integrable_sq.const_mul _).add
      ((Lp.memLp g).norm.integrable_sq.const_mul _))
  filter_upwards [hh] with x hx
  rw [hx]
  exact complex_two_weight_bound _ _ _ _ (hC x) (hD x)

attribute [local irreducible] graphComponent graphFormVector FermionLipschitzMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

lemma FermionLipschitzMultiplier.mass_bound {N : ℕ} (p : FermionLipschitzMultiplier N)
    {C : ℝ} (hC : ∀ x, |p.value x| ≤ C) (F : fermionGraph N) :
    ‖fermionGraphValue N (p.apply F)‖^2 ≤ C^2*‖fermionGraphValue N F‖^2 := by
  rw [graphValue_norm_sq,graphValue_norm_sq,Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => l2_real_multiplier_bound _ _ p.value hC
    (p.apply_value F s)

lemma FermionLipschitzMultiplier.kinetic_bound {N : ℕ} (p : FermionLipschitzMultiplier N)
    {C : ℝ} (hC : ∀ x, |p.value x| ≤ C) (D : Fin N × Fin 3 → ℝ)
    (hD : ∀ i a x, |lineDeriv ℝ p.value x (direction i a)| ≤ D (i,a))
    (F : fermionGraph N) :
    (∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) (p.apply F)‖^2) ≤
      2*C^2*(∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2)+
        2*(∑ i,∑ a,D (i,a)^2)*‖fermionGraphValue N F‖^2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun a _ =>
      l2_two_multiplier_bound (graphComponent s (some (i,a)) F)
        (graphComponent s none F) (graphComponent s (some (i,a)) (p.apply F))
        p.value (fun x => lineDeriv ℝ p.value x (direction i a)) hC (hD i a)
        (p.apply_gradient F s i a)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul] at hh
  rw [graphValue_norm_sq]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl

lemma graph_multiplier_arithmetic {M K M' K' f f' C S : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hm : M' ≤ C^2*M) (hk : K' ≤ 2*C^2*K+2*S*M)
    (he : f=M+K) (he' : f'=M'+K') : f' ≤ (3*C^2+2*S)*f := by
  nlinarith [mul_nonneg (sq_nonneg C) hK,mul_nonneg hS hK,
    mul_nonneg (sq_nonneg C) hM]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_QuantumSectorNearMinimizer
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
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

theorem quantum_sector_near_minimizer (Z : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖ ^ 2 = 1 ∧
      formEnergy Z (graphFormVector F) < energy Z N + ε := by
  have hex : ∃ ψ : FormVector N, FormAdmissible ψ ∧
      formEnergy Z ψ < energy Z N + ε := by
    by_cases hN : N = 0
    · subst N
      obtain ⟨ψ, hψ⟩ := formDomain_nonempty 0
      refine ⟨ψ, hψ, ?_⟩
      simpa only [formEnergy, Fin.sum_univ_zero, Finset.sum_const_zero,
        mul_zero, sub_zero, add_zero, energy, ↓reduceIte, zero_add] using hε
    · have hh : sInf {e | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} <
          energy Z N + ε := by
        simpa only [energy, ite_eq_right hN] using (lt_add_of_pos_right (energy Z N) hε)
      obtain ⟨e, ⟨ψ, hψ, he⟩, he'⟩ := exists_lt_of_csInf_lt (formValues_nonempty Z N) hh
      exact ⟨ψ, hψ, he ▸ he'⟩
  obtain ⟨ψ, hψ, he⟩ := hex
  refine ⟨admissibleGraph ψ hψ, admissibleGraph_norm ψ hψ, ?_⟩
  have heq := formEnergy_congr_ae Z (graphFormVector (admissibleGraph ψ hψ)) ψ
    (graphFormVector_admissibleGraph_value ψ hψ)
    (graphFormVector_admissibleGraph_gradient ψ hψ)
  exact heq ▸ he

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ApproximateLipschitz
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

lemma continuous_form_re_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (G : V) :
    (⟪G,B G⟫_ℂ).re ≤ ‖B‖*‖G‖^2 := by
  calc
    _ ≤ ‖⟪G,B G⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖G‖*‖B G‖ := norm_inner_le_norm _ _
    _ ≤ ‖G‖*(‖B‖*‖G‖) := mul_le_mul_of_nonneg_left (B.le_opNorm G) (norm_nonneg _)
    _ = _ := by ring

lemma positive_form_residual_bound {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (hB : B.IsPositive)
    (F G : V) {η C K : ℝ} (hη : 0 ≤ η)
    (hF : (⟪F,B F⟫_ℂ).re ≤ η) (hG : ‖G‖^2 ≤ C*K) :
    (⟪G,B F⟫_ℂ).re^2 ≤ η*(‖B‖*C*K) := by
  have hGn : 0 ≤ (⟪G,B G⟫_ℂ).re := hB.re_inner_nonneg_right G
  calc
    _ ≤ (⟪F,B F⟫_ℂ).re*(⟪G,B G⟫_ℂ).re := positive_map_cauchy_re B hB F G
    _ ≤ η*(⟪G,B G⟫_ℂ).re := mul_le_mul_of_nonneg_right hF hGn
    _ ≤ η*(‖B‖*(C*K)) := mul_le_mul_of_nonneg_left
      ((continuous_form_re_le B G).trans (mul_le_mul_of_nonneg_left hG (norm_nonneg _))) hη
    _ = _ := by ring

attribute [local irreducible] graphComponent graphFormVector FermionLipschitzMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  sectorExcessOperator

lemma quantum_sector_excess_near_minimizer {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2=1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η := by
  have hm : 0 < min 1 η := lt_min zero_lt_one hη
  have hex := quantum_sector_near_minimizer Z N hm
  rcases hex with ⟨F,hn,hF⟩
  have hb : formEnergy Z (graphFormVector F) ≤ energy Z N+1 :=
    hF.le.trans (add_le_add le_rfl (min_le_left _ _))
  have hk := near_minimizer_graph_bound hZ F hn hb
  refine ⟨F,hn,hk,?_⟩
  have he := sectorExcessOperator_diagonal Z F
  have hp : formEnergy Z (graphFormVector F) ≤ energy Z N+η :=
    hF.le.trans (add_le_add le_rfl (min_le_right _ _))
  have hev : energy Z N * ‖fermionGraphValue N F‖^2 = energy Z N :=
    (congrArg (fun t : ℝ => energy Z N*t) hn).trans (mul_one _)
  exact he.le.trans ((sub_le_sub_left hev.ge _).trans (sub_le_iff_le_add.mpr (by linarith only [hp])))

end CoulombAtom

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_DyadicObservation
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombObservation

lemma dyadicObservationWidth_pos {r : ℝ} (hr : 0 < r) (k : ℕ) :
    0 < dyadicObservationWidth r k := Real.rpow_pos_of_pos (by positivity) _

lemma dyadicObservationWidth_inv_sq {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (dyadicObservationWidth r k)⁻¹^2 =
      r^(-2.02:ℝ) * ((2:ℝ)^(-2.02:ℝ))^k := by
  unfold dyadicObservationWidth
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity), ← Real.rpow_mul (by positivity)]
  norm_num
  rw [Real.mul_rpow (by positivity) hr.le, ← Real.rpow_pow_comm (by norm_num)]
  ring

lemma dyadicObservationRatio_nonneg : 0 ≤ (2:ℝ)^(-2.02:ℝ) := Real.rpow_nonneg (by norm_num) _

lemma dyadicObservationRatio_le_half : (2:ℝ)^(-2.02:ℝ) ≤ 1/2 := by
  calc
    _ ≤ (2:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = _ := by norm_num

end CoulombObservation

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombObservation

lemma scaleObservationArray_reindex {J I : Type*} [Fintype J] [Fintype I]
    (ell : J → ℝ) (e : Equiv.Perm I) (u : J × I → ℝ) :
    scaleObservationArray ell (arrayReindex e u) = arrayReindex e (scaleObservationArray ell u) := by
  ext q
  simp only [scaleObservationArray_apply, arrayReindex_apply]

end CoulombObservation
namespace CoulombAtom
open CoulombObservation

lemma scaledObservationEvent_symmetric {N : ℕ} {J : Type*} [Fintype J]
    (ell : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hsy : QuantumEventSymmetric s) :
    QuantumEventSymmetric (scaleObservationArray ell ⁻¹' s) := by
  intro π u
  change scaleObservationArray ell (arrayReindex (π.prodCongr (Equiv.refl (Fin 3))) u) ∈ s ↔
    scaleObservationArray ell u ∈ s
  rw [scaleObservationArray_reindex]
  exact hsy π _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

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
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_UniformFormResidual
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

lemma approximate_uniform_positive_form {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (hB : B.IsPositive)
    (Q : V → Prop) (K : ℝ)
    (hne : ∀ η : ℝ, 0 < η → ∃ F, Q F ∧ ‖F‖^2 ≤ K ∧ (⟪F,B F⟫_ℂ).re ≤ η)
    {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ) :
    ∃ F, Q F ∧ ‖F‖^2 ≤ K ∧ (⟪F,B F⟫_ℂ).re ≤ δ ∧
      ∀ G : V, ‖G‖^2 ≤ H → (⟪G,B F⟫_ℂ).re ≤ δ := by
  let A : ℝ := ‖B‖*H
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) hH
  let η : ℝ := min δ (δ^2/(A+1))
  have hη : 0 < η := lt_min hδ (div_pos (sq_pos_of_pos hδ) (by linarith))
  have hq : δ^2/(A+1)*(A+1) = δ^2 := div_mul_cancel₀ _ (by linarith : A+1 ≠ 0)
  have hηA : η*A ≤ δ^2 := by
    have h1 := mul_le_mul_of_nonneg_right (min_le_right δ (δ^2/(A+1)))
      (by linarith : 0 ≤ A+1)
    change η*(A+1) ≤ _ at h1
    nlinarith
  obtain ⟨F,hF,hK,he⟩ := hne η hη
  refine ⟨F,hF,hK,he.trans (min_le_left _ _),fun G hG => ?_⟩
  have hr := positive_form_residual_bound B hB F G hη.le he
    (C := H) (K := 1) (hG.trans_eq (mul_one H).symm)
  simp only [mul_one] at hr
  change (⟪G,B F⟫_ℂ).re^2 ≤ η*A at hr
  nlinarith

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

lemma sectorExcessOperator_diagonal_normalized {N : ℕ} (Z : ℝ) (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) :
    (⟪F,sectorExcessOperator Z N F⟫_ℂ).re = formEnergy Z (graphFormVector F)-energy Z N := by
  have he := sectorExcessOperator_diagonal Z F
  have hev : energy Z N*‖fermionGraphValue N F‖^2 = energy Z N :=
    (congrArg (fun t : ℝ => energy Z N*t) hn).trans (mul_one _)
  exact he.trans (congrArg (fun t : ℝ => formEnergy Z (graphFormVector F)-t) hev)

theorem quantum_uniform_form_residual {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ G : fermionGraph N, ‖G‖^2 ≤ H →
        (⟪G,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ := by
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ ∧
      ∀ G : fermionGraph N, ‖G‖^2 ≤ H →
        (⟪G,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ)
  · intro F h
    refine ⟨h.1,h.2.1,?_,h.2.2.2⟩
    have hdiag := sectorExcessOperator_diagonal_normalized Z F h.1
    have he := h.2.2.1
    linarith only [he,hdiag]
  · exact approximate_uniform_positive_form
      (sectorExcessOperator Z N) (sectorExcessOperator_positive hZ N)
      (fun F : fermionGraph N => ‖fermionGraphValue N F‖^2 = 1)
      (4*(|energy Z N|+(N:ℝ)*Z^2+2))
      (fun _ hη => quantum_sector_excess_near_minimizer hZ N hη) hH hδ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedSelectedMaster
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

lemma priced_graph_tilt_excess {Z lam e : ℝ} {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) (G : fermionGraph N)
    (hn : ‖fermionGraphValue N G‖^2 = 1)
    (hE : formEnergy Z (graphFormVector G) ≤ energy Z N+e) :
    corePriceExcess Z lam (graphFormVector G) ≤ e := by
  rw [corePriceExcess,formMass_graph,hn,mul_one,mul_one,priceEnergy_eq_of_minimizes hN]
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UniformEventGraph
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
open scoped Topology BigOperators InnerProductSpace NNReal

namespace CoulombAtom
open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

lemma FermionLipschitzMultiplier.quantitative_graph_bound {N : ℕ}
    (p : FermionLipschitzMultiplier N) {C : ℝ} (hC : ∀ x, |p.value x| ≤ C)
    (D : Fin N × Fin 3 → ℝ)
    (hD : ∀ i a x, |lineDeriv ℝ p.value x (direction i a)| ≤ D (i,a))
    (F : fermionGraph N) :
    ‖p.apply F‖^2 ≤ (3*C^2+2*(∑ i, ∑ a, D (i,a)^2))*‖F‖^2 := by
  have hm := FermionLipschitzMultiplier.mass_bound (N := N) p hC F
  have hk := FermionLipschitzMultiplier.kinetic_bound (N := N) p hC D hD F
  have hS : 0 ≤ ∑ i : Fin N,∑ a : Fin 3,D (i,a)^2 := by positivity
  have hkin : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 := by positivity
  exact graph_multiplier_arithmetic (sq_nonneg _) hkin hS hm hk
    (fermionGraph_norm_sq F) (fermionGraph_norm_sq (p.apply F))

lemma observationGraphFactor_nonneg (N : ℕ) {J : Type*} [Fintype J]
    (b : J → ℝ) (p₀ : ℝ) : 0 ≤ observationGraphFactor N b p₀ := by
  unfold observationGraphFactor
  positivity

lemma quantumEventMultiplier_uniform_bounds {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) {p₀ p : ℝ} (h₀ : 0 < p₀) (hp : p₀ ≤ p) :
    (∀ x, |(quantumEventMultiplier b hs hsy p).value x| ≤ (Real.sqrt p₀)⁻¹) ∧
    ∀ i a x, |lineDeriv ℝ (quantumEventMultiplier b hs hsy p).value x (direction i a)| ≤
      (Real.sqrt p₀)⁻¹ *
        ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ) *
          ‖flattenConfiguration N‖) * ‖direction i a‖ := by
  have hpinv : (Real.sqrt p)⁻¹ ≤ (Real.sqrt p₀)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr h₀) (Real.sqrt_le_sqrt hp)
  have hpb : 0 ≤ (Real.sqrt p)⁻¹ := by positivity
  constructor
  · intro x
    rw [quantumEventMultiplier_value,abs_of_nonneg (by positivity)]
    have hx : Real.sqrt (quantumEventLikelihood b s x) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (quantumEventLikelihood_le_one b hs x)
    exact (mul_le_of_le_one_right hpb hx).trans hpinv
  · intro i a x
    let m := quantumEventMultiplier b hs hsy p
    have hd : |lineDeriv ℝ m.value x (direction i a)| ≤ (m.constant:ℝ)*‖direction i a‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_lineDeriv_le_of_lipschitz ℝ m.lipschitz (x₀ := x) (v := direction i a))
    have hc : (m.constant:ℝ) ≤ (Real.sqrt p₀)⁻¹ *
        ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ)*‖flattenConfiguration N‖) := by
      change ‖(Real.sqrt p)⁻¹‖ *
        ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ)*‖flattenConfiguration N‖) ≤ _
      rw [Real.norm_of_nonneg hpb]
      exact mul_le_mul_of_nonneg_right hpinv (by positivity)
    exact hd.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

attribute [local irreducible] quantumEventMultiplier

theorem quantumEventMultiplier_uniform_graph {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) {p₀ p : ℝ} (h₀ : 0 < p₀) (hp : p₀ ≤ p)
    (F : fermionGraph N) :
    ‖(quantumEventMultiplier b hs hsy p).apply F‖^2 ≤
      observationGraphFactor N b p₀ * ‖F‖^2 := by
  have hd := quantumEventMultiplier_uniform_bounds b hs hsy h₀ hp
  unfold observationGraphFactor
  exact FermionLipschitzMultiplier.quantitative_graph_bound (N := N)
    (quantumEventMultiplier b hs hsy p) hd.1
    (fun ia => (Real.sqrt p₀)⁻¹ *
      ((sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b : ℝ)*‖flattenConfiguration N‖) *
      ‖direction ia.1 ia.2‖) hd.2 F

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UniformApproximateEvent
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
open scoped Topology BigOperators InnerProductSpace NNReal

namespace CoulombAtom
open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

lemma quantum_observation_event_tilt_bounded_residual {Z δ : ℝ} {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    {J : Type*} [Fintype J] (b : J → ℝ)
    {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (hp : 0 < quantumEventProbability F b s)
    (hr : let p := quantumEventMultiplier b hs hsy (quantumEventProbability F b s)
      (⟪p.apply (p.apply F),sectorExcessOperator Z N F⟫_ℂ).re ≤ δ) :
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G =
        (ENNReal.ofReal (quantumEventProbability F b s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent b s)) ∧
      formEnergy Z (graphFormVector G) ≤ energy Z N +
        (observationFisherConstant/2) * (∑ j, (b j)^2) *
          (Real.log (Real.exp 1/quantumEventProbability F b s))^5 + δ := by
  let p := quantumEventMultiplier b hs hsy (quantumEventProbability F b s)
  refine ⟨p.apply F,quantumEventMultiplier_normalized F b hs hsy hp,
    quantumEventMultiplier_rawLaw F b hs hsy hp,?_⟩
  have hid := quantum_lipschitz_ims_residual Z F p
  have hnorm : energy Z N * ‖fermionGraphValue N (p.apply F)‖^2 = energy Z N :=
    (congrArg (fun u : ℝ => energy Z N*u)
      (quantumEventMultiplier_normalized F b hs hsy hp)).trans (mul_one _)
  have hgrad := FermionLipschitzMultiplier.gradient_rawLaw (N := N) p F
  have hc := quantumEventMultiplier_fisher_integral F hn b hs hsy hp
  change formEnergy Z (graphFormVector (p.apply F)) ≤ _
  linarith only [hid,hnorm,hgrad,hc,hr]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UniformDyadicEvent
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
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

lemma physicalObservationProbability_le_one {N K : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) (ell : Fin K → ℝ)
    (A : Set (Fin K × (Fin N × Fin 3) → ℝ)) :
    physicalObservationProbability F ell A ≤ 1 := by
  let := graphRawLaw_probability F hn
  exact measureReal_le_one

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierEventSymmetryBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set

namespace CoulombAtom
open CoulombObservation

lemma arrayUnorderedConfiguration_measurable {N K : ℕ} (k : Fin K) :
    Measurable (arrayUnorderedConfiguration (N := N) k) := by
  apply unorderedConfiguration_measurable.comp
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact measurable_pi_apply (k,i,a)

lemma arrayUnorderedConfiguration_reindex {N K : ℕ} (k : Fin K)
    (π : Equiv.Perm (Fin N)) (u : Fin K × (Fin N × Fin 3) → ℝ) :
    arrayUnorderedConfiguration k (arrayReindex (π.prodCongr (Equiv.refl (Fin 3))) u) =
      arrayUnorderedConfiguration k u := by
  apply Quotient.sound
  refine ⟨π.symm, ?_⟩
  intro i
  ext a
  simp [arrayObservedConfiguration, arrayReindex_apply]

lemma arrayObservationInformation_le (N K j : ℕ) :
    arrayObservationInformation N K j ≤
      (inferInstance : MeasurableSpace (Fin K × (Fin N × Fin 3) → ℝ)) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (arrayUnorderedConfiguration_measurable k).comap_le
  · exact bot_le

lemma observationInformation_eq_arrayComap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j =
      (arrayObservationInformation N K j).comap (physicalObservationArray ell) := by
  unfold observationInformation arrayObservationInformation
  rw [MeasurableSpace.comap_iSup]
  congr 1
  funext k
  split_ifs
  · rw [MeasurableSpace.comap_comp]
    rfl
  · exact MeasurableSpace.comap_bot.symm

lemma arrayObservationInformation_le_symmetric (N K j : ℕ) :
    arrayObservationInformation N K j ≤ symmetricArraySpace N K := by
  apply iSup_le
  intro k
  split_ifs
  · intro A hA
    obtain ⟨B, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    intro π u
    change arrayUnorderedConfiguration k (arrayReindex _ u) ∈ B ↔
      arrayUnorderedConfiguration k u ∈ B
    rw [arrayUnorderedConfiguration_reindex]
  · exact bot_le

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPosteriorCapBarrier
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
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma dyadicUniformEventBudget_nonneg {r p₀ δ : ℝ}
    (hr : 0 < r) (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (hδ : 0 ≤ δ) :
    0 ≤ dyadicUniformEventBudget r p₀ δ := by
  have hlog : 0 ≤ Real.log (Real.exp 1/p₀) := by
    rw [eventLog_eq hp]
    linarith [Real.log_nonpos hp.le hp1]
  unfold dyadicUniformEventBudget
  exact add_nonneg (mul_nonneg (mul_nonneg observationFisherConstant_pos.le
    (Real.rpow_nonneg hr.le _)) (pow_nonneg hlog _)) hδ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_TailObservationEventBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set

namespace CoulombAtom
open CoulombObservation

lemma arrayObservationInformation_le_tailInvariant (N K j : ℕ) :
    arrayObservationInformation N K j ≤ tailInvariantArraySpace N K j := by
  apply iSup_le
  intro k
  split_ifs with hk
  · intro A hA
    obtain ⟨B,_,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    intro u v huv
    have he : arrayUnorderedConfiguration k u = arrayUnorderedConfiguration k v := by
      apply congrArg unorderedConfiguration
      funext i
      ext a
      exact huv k hk i a
    exact congrArg (· ∈ B) he |>.to_iff
  · exact bot_le

lemma observation_event_tail_representation {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    ∃ B : Set (Fin K × (Fin N × Fin 3) → ℝ),
      MeasurableSet[arrayObservationInformation N K j] B ∧ physicalObservationEvent ell B = A := by
  rw [observationInformation_eq_arrayComap] at hA
  exact MeasurableSpace.measurableSet_comap.mp hA

lemma tail_physicalObservationEvent_eq {N K : ℕ}
    (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k) (j : ℕ)
    {B : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hB : MeasurableSet[arrayObservationInformation N K j] B) :
    quantumObservationEvent (tailObservationCoefficient ell j) (scaleObservationArray ell ⁻¹' B) =
      physicalObservationEvent ell B := by
  ext z
  apply arrayObservationInformation_le_tailInvariant N K j B hB
  intro k hk i a
  simp only [scaleObservationArray_apply,Pi.add_apply,observationPlacement_apply,
    flattenConfiguration_apply,physicalObservationArray,tailObservationCoefficient,ite_eq_left hk]
  rw [mul_add,←mul_assoc,mul_inv_cancel₀ (hell k).ne',one_mul]

lemma tail_quantumEventProbability_eq_physical {N K : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k) (j : ℕ)
    {B : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hB : MeasurableSet[arrayObservationInformation N K j] B) :
    quantumEventProbability F (tailObservationCoefficient ell j) (scaleObservationArray ell ⁻¹' B) =
      physicalObservationProbability F ell B := by
  have hm := (arrayObservationInformation_le N K j B hB).preimage (scaleObservationArray ell).measurable
  have he := quantumEventProbability_ofReal F hn (tailObservationCoefficient ell j) hm
  rw [tail_physicalObservationEvent_eq ell hell j hB] at he
  exact (ENNReal.toReal_ofReal (integral_nonneg (quantumEventLikelihood_nonneg _ hm))).symm.trans
    (congrArg ENNReal.toReal he)
end CoulombAtom

open MeasureTheory Set Finset
open scoped BigOperators

namespace CoulombObservation
lemma geometric_tail_sum_le_two {q : ℝ} (hq : 0 ≤ q) (hq2 : q ≤ 1/2) (j K : ℕ) :
    (∑ k : Fin K, if j ≤ k.val then q^k.val else 0) ≤ 2*q^j := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if j ≤ k then q^k else 0) K,
    ←Finset.sum_filter]
  have he : (range K).filter (fun k => j ≤ k) = Finset.Ico j K := by
    ext k
    simp only [mem_filter,Finset.mem_range,Finset.mem_Ico]
    tauto
  rw [he]
  have hh := geom_sum_Ico_le_of_lt_one (m := j) (n := K) hq (by linarith : q < 1)
  apply hh.trans
  apply (div_le_iff₀ (by linarith : 0 < 1-q)).mpr
  nlinarith [pow_nonneg hq j,mul_le_mul_of_nonneg_right hq2 (pow_nonneg hq j)]
end CoulombObservation
namespace CoulombAtom
open CoulombObservation

lemma tail_dyadicObservation_inv_sq_sum {r : ℝ} (hr : 0 < r) (j K : ℕ) :
    (∑ k : Fin K, (tailObservationCoefficient (fun k => dyadicObservationWidth r k) j k)^2) ≤
      2*((2:ℝ)^j*r)^(-2.02:ℝ) := by
  have he (k : Fin K) : (tailObservationCoefficient (fun k => dyadicObservationWidth r k) j k)^2 =
      r^(-2.02:ℝ)*(if j ≤ k.val then ((2:ℝ)^(-2.02:ℝ))^k.val else 0) := by
    unfold tailObservationCoefficient
    split_ifs
    · exact dyadicObservationWidth_inv_sq hr k
    · simp
  simp_rw [he]
  rw [←mul_sum]
  have hh := mul_le_mul_of_nonneg_left
    (geometric_tail_sum_le_two dyadicObservationRatio_nonneg dyadicObservationRatio_le_half j K)
    (Real.rpow_nonneg hr.le (-2.02))
  apply hh.trans_eq
  rw [Real.mul_rpow (by positivity) hr.le,←Real.rpow_pow_comm (by norm_num)]
  ring

lemma tail_observationTiltEnergyCost_dyadic {r p : ℝ} (hr : 0 < r) (hp : 0 < p)
    (hp1 : p ≤ 1) (j K : ℕ) :
    (observationFisherConstant/2)*
      (∑ k : Fin K, (tailObservationCoefficient (fun k => dyadicObservationWidth r k) j k)^2)*
      (Real.log (Real.exp 1/p))^5 ≤
      observationFisherConstant*((2:ℝ)^j*r)^(-2.02:ℝ)*(Real.log (Real.exp 1/p))^5 := by
  have hlog : 0 ≤ (Real.log (Real.exp 1/p))^5 := by
    apply pow_nonneg
    rw [eventLog_eq hp]
    linarith [Real.log_nonpos hp.le hp1]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (tail_dyadicObservation_inv_sq_sum hr j K)
      (show 0 ≤ observationFisherConstant/2 by linarith [observationFisherConstant_pos])) hlog
  exact hh.trans_eq (by ring)
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_UniformFamilyEventBarrier
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
section Work_UniformFamilyEvent_barrier_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

theorem quantum_uniform_near_minimizer_family_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {I J : Type*} [Fintype I] [Fintype J] (b : I → J → ℝ)
    {p₀ δ : ℝ} (h₀ : 0 < p₀) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (i : I) (s : Set (J × (Fin N × Fin 3) → ℝ)) (_hs : MeasurableSet s)
        (_hsy : QuantumEventSymmetric s), p₀ ≤ quantumEventProbability F (b i) s →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (quantumEventProbability F (b i) s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent (b i) s)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N +
          (observationFisherConstant/2) * (∑ j, (b i j)^2) *
            (Real.log (Real.exp 1/quantumEventProbability F (b i) s))^5 + δ := by
  classical
  let C : ℝ := ∑ i, observationGraphFactor N (b i) p₀
  let K : ℝ := 4*(|energy Z N|+(N:ℝ)*Z^2+2)
  let H : ℝ := C*C*K
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => observationGraphFactor_nonneg N (b i) p₀)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg hC hC) hK
  have hi (i : I) : observationGraphFactor N (b i) p₀ ≤ C :=
    Finset.single_le_sum (fun k _ => observationGraphFactor_nonneg N (b k) p₀) (Finset.mem_univ i)
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧ ‖F‖^2 ≤ K ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ G : fermionGraph N, ‖G‖^2 ≤ H →
        (⟪G,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ)
  · intro F h
    refine ⟨h.1,h.2.2.1,fun i s hs hsy hp => ?_⟩
    let p := quantumEventMultiplier (b i) hs hsy (quantumEventProbability F (b i) s)
    have hb (G : fermionGraph N) : ‖p.apply G‖^2 ≤ C*‖G‖^2 :=
      (quantumEventMultiplier_uniform_graph (b i) hs hsy h₀ hp G).trans
        (mul_le_mul_of_nonneg_right (hi i) (sq_nonneg _))
    have htest : ‖p.apply (p.apply F)‖^2 ≤ H := calc
      _ ≤ C*‖p.apply F‖^2 := hb (p.apply F)
      _ ≤ C*(C*‖F‖^2) := mul_le_mul_of_nonneg_left (hb F) hC
      _ ≤ C*(C*K) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h.2.1 hC) hC
      _ = H := by dsimp only [H]; ring
    exact quantum_observation_event_tilt_bounded_residual F h.1 (b i) hs hsy (h₀.trans_le hp)
      (h.2.2.2 (p.apply (p.apply F)) htest)
  · exact quantum_uniform_form_residual hZ N hH hδ

end Work_UniformFamilyEvent_barrier_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace NNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

theorem quantum_uniform_near_minimizer_family_variable_event_tilt {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] (b : I → J → ℝ)
    (p₀ : I → ℝ) {δ : ℝ} (h₀ : ∀ i, 0 < p₀ i) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (i : I) (s : Set (J × (Fin N × Fin 3) → ℝ)) (_hs : MeasurableSet s)
        (_hsy : QuantumEventSymmetric s), p₀ i ≤ quantumEventProbability F (b i) s →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (quantumEventProbability F (b i) s))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent (b i) s)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N +
          (observationFisherConstant/2) * (∑ j, (b i j)^2) *
            (Real.log (Real.exp 1/quantumEventProbability F (b i) s))^5 + δ := by
  classical
  let p := Finset.univ.inf' Finset.univ_nonempty p₀
  have hp : 0 < p := (Finset.lt_inf'_iff _).mpr (fun i _ => h₀ i)
  have hle (i : I) : p ≤ p₀ i := Finset.inf'_le p₀ (Finset.mem_univ i)
  obtain ⟨F,hFn,hFE,hTilt⟩ := quantum_uniform_near_minimizer_family_event_tilt hZ N b hp hδ
  exact ⟨F,hFn,hFE,fun i s hs hsy hp => hTilt i s hs hsy ((hle i).trans hp)⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_UniformVariableTailEventBarrier
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
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator quantumEventMultiplier

theorem quantum_uniform_near_minimizer_variable_tail_event_tilt {Z r : ℝ} (hZ : 0 ≤ Z)
    (hr : 0 < r) (N K : ℕ) (p₀ : Fin (K+1) → ℝ) {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (j : Fin (K+1)) (A : Set (Fin K × (Fin N × Fin 3) → ℝ))
        (_hA : MeasurableSet[arrayObservationInformation N K j] A),
        p₀ j ≤ physicalObservationProbability F (fun k : Fin K => dyadicObservationWidth r k) A →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F
          (fun k : Fin K => dyadicObservationWidth r k) A))⁻¹ •
          Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
            (physicalObservationEvent (fun k : Fin K => dyadicObservationWidth r k) A)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N+
          observationFisherConstant*((2:ℝ)^j.val*r)^(-2.02:ℝ)*
            (Real.log (Real.exp 1/physicalObservationProbability F
              (fun k : Fin K => dyadicObservationWidth r k) A))^5+δ := by
  let ell : Fin K → ℝ := fun k : Fin K => dyadicObservationWidth r k
  let b : Fin (K+1) → Fin K → ℝ := fun j => tailObservationCoefficient ell j
  have hell k : 0 < ell k := dyadicObservationWidth_pos hr k
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ (i : Fin (K+1)) (A : Set (Fin K × (Fin N × Fin 3) → ℝ))
        (_hA : MeasurableSet A) (_hsy : QuantumEventSymmetric A),
        p₀ i ≤ quantumEventProbability F (b i) A →
      ∃ G : fermionGraph N,
        ‖fermionGraphValue N G‖^2 = 1 ∧
        graphRawLaw G = (ENNReal.ofReal (quantumEventProbability F (b i) A))⁻¹ •
          Measure.map Prod.fst
            (((graphRawLaw F).prod
              (Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))).restrict
                (quantumObservationEvent (b i) A)) ∧
        formEnergy Z (graphFormVector G) ≤ energy Z N +
          (observationFisherConstant/2)*(∑ k, (b i k)^2)*
            (Real.log (Real.exp 1/quantumEventProbability F (b i) A))^5+δ)
  · intro F h
    refine ⟨h.1,h.2.1,?_⟩
    intro j A hA hp
    have hm := arrayObservationInformation_le N K j A hA
    have hsy := arrayObservationInformation_le_symmetric N K j A hA
    have hm' := hm.preimage (scaleObservationArray ell).measurable
    have hid := tail_quantumEventProbability_eq_physical F h.1 ell hell j hA
    have hp' : p₀ j ≤ quantumEventProbability F (b j) (scaleObservationArray ell ⁻¹' A) := by
      rwa [hid]
    obtain ⟨G,hG,hlaw,hcost⟩ := h.2.2 j _ hm' (scaledObservationEvent_symmetric ell hsy) hp'
    change quantumEventProbability F (b j) _ = _ at hid
    rw [hid,tail_physicalObservationEvent_eq ell hell j hA] at hlaw
    rw [hid] at hcost
    refine ⟨G,hG,hlaw,hcost.trans ?_⟩
    have hc := tail_observationTiltEnergyCost_dyadic hr ((h₀ j).trans_le hp)
      (physicalObservationProbability_le_one F h.1 ell A) j K
    exact add_le_add (add_le_add le_rfl hc) le_rfl
  · exact quantum_uniform_near_minimizer_family_variable_event_tilt hZ N b p₀ h₀ hδ
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityTailTiltBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem exists_actual_own_probability_tail_tilt_state_oai {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hr : 0 < r) {N : ℕ} (hN : PriceMinimizes (energy Z) lam N)
    (K : ℕ) (p₀ : Fin (K+1) → ℝ) {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z lam r K p₀ δ F := by
  obtain ⟨F,hFn,hFE,hTilt⟩ := quantum_uniform_near_minimizer_variable_tail_event_tilt hZ hr N K p₀ h₀ hδ
  refine ⟨F,hFn,hFE,?_⟩
  intro j A hA hp
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  obtain ⟨B,hB,hBA⟩ := observation_event_tail_representation ell j hA
  have hpB : physicalObservationProbability F ell B =
      ((physicalObservationLaw (graphRawLaw F) K) A).toReal := by
    change ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal = _
    rw [hBA]
  have hp' : p₀ j ≤ physicalObservationProbability F ell B := by rwa [hpB]
  obtain ⟨G,hGn,hlaw,hGE⟩ := hTilt j B hB hp'
  change formEnergy Z (graphFormVector G) ≤ energy Z N+
    observationFisherConstant*((2:ℝ)^j.val*r)^(-2.02:ℝ)*
      (Real.log (Real.exp 1/physicalObservationProbability F ell B))^5+δ at hGE
  rw [hpB] at hGE
  refine ⟨G,hGn,?_,?_⟩
  · rwa [hpB,hBA] at hlaw
  · have hrj : 0 < (2:ℝ)^j.val*r := by positivity
    apply max_le
    · simpa only [dyadicUniformEventBudget] using
        priced_graph_tilt_excess hN G hGn (by simpa only [add_assoc] using hGE)
    · exact dyadicUniformEventBudget_nonneg hrj ((h₀ j).trans_le hp)
        (hpB ▸ physicalObservationProbability_le_one F hFn ell B) hδ.le

end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state_oai := @OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state_oai
