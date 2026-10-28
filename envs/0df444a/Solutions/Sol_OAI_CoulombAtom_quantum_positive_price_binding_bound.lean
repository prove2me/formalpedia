-- Prove2me | solution 1 for OAI.CoulombAtom.quantum_positive_price_binding_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:19.106491+00:00
-- url     : https://prove2.me/submissions/cf992ede-1d74-4cf9-8f15-0021bfd28842

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C008
import Definitions.Def_OAIQ071C009
import Theorems.Thm_OAI_CoulombAtom_quantum_binding_residual

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

lemma FermionMultiplier.apply_gradient {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphComponent s (some (i, a)) (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s (some (i, a)) F x +
        Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * graphComponent s none F x :=
  p.toSmoothMultiplier.apply_gradient (F.val s) (i, a)

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

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

attribute [local irreducible] formEnergy graphFormVector

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

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

lemma graphFormVector_value_eq {N : ℕ} (F : fermionGraph N) (s : Spins N) (x : Configuration N) :
    (graphFormVector F).value s x = graphComponent s none F x := rfl

attribute [local irreducible] graphComponent graphFormVector

end

lemma sum_excluding_add {α : Type*} [Fintype α] [DecidableEq α] (i : α) (f : α → ℝ) :
    (∑ j, if j ≠ i then f j else 0) + f i = ∑ j, f j := by
  have hh (j : α) : (if j ≠ i then f j else 0) + (if j = i then f j else 0) = f j := by
    by_cases h : j = i <;> simp [h]
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hh j)


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Weighted
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

lemma bindingWeight_le_radius {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    bindingWeight R ε x ≤ regularizedRadius ε x := by
  have ht := regularizedRadius_pos hε x
  unfold bindingWeight
  apply (div_le_iff₀ (by positivity : 0 < R + regularizedRadius ε x)).mpr
  nlinarith [sq_nonneg (regularizedRadius ε x)]


open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Sum
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

lemma bindingTotalMultiplier_value {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (x : Configuration N) : (bindingTotalMultiplier hR hε).value x =
      ∑ i, bindingWeight R ε (x i) := by
  change (∑ i, bindingRoot R ε (x i) ^ 2) = _
  simp only [bindingRoot_sq hR hε]


open MeasureTheory Filter
open scoped Topology BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

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

lemma approximate_positive_form {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (hB : B.IsPositive)
    (p : V → V) (hpB : ∃ C : ℝ, 0 ≤ C ∧ ∀ F, ‖p F‖^2 ≤ C*‖F‖^2)
    (Q : V → Prop) {K : ℝ} (hK : 0 ≤ K)
    (hne : ∀ η : ℝ, 0 < η → ∃ F, Q F ∧ ‖F‖^2 ≤ K ∧ (⟪F,B F⟫_ℂ).re ≤ η)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ F, Q F ∧ ‖F‖^2 ≤ K ∧ (⟪p F,B F⟫_ℂ).re ≤ δ := by
  obtain ⟨C,hC,hp⟩ := hpB
  let A : ℝ := ‖B‖*C*K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let η : ℝ := δ^2/(A+1)
  have hη : 0 < η := div_pos (sq_pos_of_pos hδ) (by linarith)
  have hηA : η*(A+1)=δ^2 := div_mul_cancel₀ _ (by linarith : A+1 ≠ 0)
  obtain ⟨F,hQ,hFK,hq⟩ := hne η hη
  refine ⟨F,hQ,hFK,?_⟩
  have hG : ‖p F‖^2 ≤ C*K := (hp F).trans (mul_le_mul_of_nonneg_left hFK hC)
  have hr := positive_form_residual_bound B hB F (p F) hη.le hq hG
  change (⟪p F,B F⟫_ℂ).re^2 ≤ η*A at hr
  nlinarith

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ComplexRealWeightPairing
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

lemma weighted_integrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {w : X → ℝ} (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    Integrable (fun x => w x * f x) μ :=
  hf.bdd_mul hw.aestronglyMeasurable (Eventually.of_forall hC)


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingWeightContinuous
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

lemma bindingWeight_continuous {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    Continuous (bindingWeight R ε) := by
  have he : bindingWeight R ε = fun x => bindingRoot R ε x ^ 2 := by
    funext x; exact (bindingRoot_sq hR hε x).symm
  rw [he]
  exact (bindingRoot_smooth hR hε).continuous.pow 2

lemma bindingWeight_integrable {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i : Fin N) {f : Configuration N → ℝ} (hf : Integrable f) :
    Integrable (fun x => bindingWeight R ε (x i) * f x) := by
  apply weighted_integrable hf ((bindingWeight_continuous hR hε).comp (continuous_apply i))
  intro x
  change ‖bindingWeight R ε (x i)‖ ≤ R
  rw [Real.norm_of_nonneg (bindingWeight_pos hR hε (x i)).le]
  exact bindingWeight_le hR hε (x i)

lemma bindingTotal_integral {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    {f : Configuration N → ℝ} (hf : Integrable f) :
    (∫ x, (bindingTotalMultiplier hR hε).value x * f x) =
      ∑ i, ∫ x, bindingWeight R ε (x i) * f x := by
  simp only [bindingTotalMultiplier_value hR hε, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => bindingWeight_integrable hR hε i hf)


open MeasureTheory Filter
open scoped Topology BigOperators

lemma regularizedRadius_le_add {ε : ℝ} (hε : 0 ≤ ε) (x : Space) :
    regularizedRadius ε x ≤ ‖x‖ + ε := by
  unfold regularizedRadius
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [norm_nonneg x]

lemma configuration_pair_ne {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ x : Configuration N, x i ≠ x j := by
  classical
  let L : Configuration N →ₗ[ℝ] Space := LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Space) i -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Space) j
  have hL : L ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Space)
    intro hh
    have he := congrArg (fun M : Configuration N →ₗ[ℝ] Space => M (Function.update (fun _ => 0) i v)) hh
    simp only [L, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.zero_apply,
      Function.update_self, Function.update_of_ne hij.symm, sub_zero] at he
    exact hv he
  have hk : LinearMap.ker L ≠ ⊤ := fun h => hL (LinearMap.ker_eq_top.mp h)
  have hh := Measure.addHaar_submodule volume (LinearMap.ker L) hk
  have hm : volume {x : Configuration N | x i = x j} = 0 := by
    convert hh using 2
    all_goals try with_reducible_and_instances rfl
    ext x
    change (x i = x j) ↔ L x = 0
    simp only [L, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero]
  exact ae_iff.mpr (by simpa only [not_not] using hm)


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BindingBounds
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
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom

lemma capped_radius_sum {R a b d : ℝ} (hR : 0 < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (ht : d ≤ a+b) :
    R*d/(R+d) ≤ R*a/(R+a)+R*b/(R+b) := by
  calc
    _ ≤ R*(a+b)/(R+a+b) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr ht)]
    _ = R*a/(R+a+b)+R*b/(R+a+b) := by ring
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left (mul_nonneg hR.le ha) (by positivity) (by linarith))
      (div_le_div_of_nonneg_left (mul_nonneg hR.le hb) (by positivity) (by linarith))

lemma bindingWeight_pair_lower {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (x y : Space) (hxy : x ≠ y) :
    1 ≤ (bindingWeight R ε x+bindingWeight R ε y)/‖x-y‖+
      (bindingWeight R ε x+bindingWeight R ε y)/R := by
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h := capped_radius_sum hR (regularizedRadius_pos hε x).le
    (regularizedRadius_pos hε y).le hd
    ((norm_sub_le x y).trans (add_le_add (norm_le_regularizedRadius ε x)
      (norm_le_regularizedRadius ε y)))
  change R*‖x-y‖/(R+‖x-y‖) ≤ bindingWeight R ε x+bindingWeight R ε y at h
  have hh := (div_le_iff₀ (by positivity : 0 < R+‖x-y‖)).mp h
  rw [div_add_div _ _ hd.ne' hR.ne']
  exact (le_div_iff₀ (mul_pos hd hR)).mpr (by nlinarith)

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  bindingTotalMultiplier

lemma bindingWeight_pair_integral {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i j : Fin N) (hij : i ≠ j) {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hp : Integrable (fun x => ‖f x‖^2/‖x i-x j‖)) :
    (∫ x, ‖f x‖^2) ≤
      ((∫ x, bindingWeight R ε (x i)*(‖f x‖^2/‖x i-x j‖))+
        R⁻¹*(∫ x, bindingWeight R ε (x i)*‖f x‖^2))+
      ((∫ x, bindingWeight R ε (x j)*(‖f x‖^2/‖x j-x i‖))+
        R⁻¹*(∫ x, bindingWeight R ε (x j)*‖f x‖^2)) := by
  have hpr : Integrable (fun x => ‖f x‖^2/‖x j-x i‖) := by
    simpa only [norm_sub_rev (a := _)] using hp
  have hi := bindingWeight_integrable hR hε i hp
  have hj := bindingWeight_integrable hR hε j hpr
  have hmi := bindingWeight_integrable hR hε i hf.norm.integrable_sq
  have hmj := bindingWeight_integrable hR hε j hf.norm.integrable_sq
  rw [← integral_const_mul,← integral_const_mul,← integral_add hi (hmi.const_mul R⁻¹),
    ← integral_add hj (hmj.const_mul R⁻¹)]
  rw [← integral_add
    (f := fun x => bindingWeight R ε (x i)*(‖f x‖^2/‖x i-x j‖)+R⁻¹*(bindingWeight R ε (x i)*‖f x‖^2))
    (g := fun x => bindingWeight R ε (x j)*(‖f x‖^2/‖x j-x i‖)+R⁻¹*(bindingWeight R ε (x j)*‖f x‖^2))
    (hi.add (hmi.const_mul R⁻¹)) (hj.add (hmj.const_mul R⁻¹))]
  apply integral_mono_ae hf.norm.integrable_sq
    ((hi.add (hmi.const_mul R⁻¹)).add (hj.add (hmj.const_mul R⁻¹)))
  filter_upwards [configuration_pair_ne i j hij] with x hx
  have hh := mul_le_mul_of_nonneg_right (bindingWeight_pair_lower hR hε (x i) (x j) hx)
    (sq_nonneg ‖f x‖)
  dsimp only [Pi.add_apply]
  rw [norm_sub_rev (x j)]
  convert hh using 1 <;> ring

lemma bindingWeight_nuclear_integral {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i : Fin N) {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hn : Integrable (fun x => ‖f x‖^2/‖x i‖)) :
    (∫ x, bindingWeight R ε (x i)*(‖f x‖^2/‖x i‖)) ≤
      (∫ x, ‖f x‖^2)+ε*(∫ x, ‖f x‖^2/‖x i‖) := by
  rw [← integral_const_mul,← integral_add hf.norm.integrable_sq (hn.const_mul ε)]
  apply integral_mono (bindingWeight_integrable hR hε i hn)
    (hf.norm.integrable_sq.add (hn.const_mul ε))
  intro x
  dsimp only [Pi.add_apply]
  have hb := (bindingWeight_le_radius hR hε (x i)).trans (regularizedRadius_le_add hε.le (x i))
  by_cases hx : ‖x i‖=0
  · simp only [hx,div_zero,mul_zero,add_zero]
    positivity
  · have hx0 : 0 < ‖x i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have hm := mul_le_mul_of_nonneg_right hb (div_nonneg (sq_nonneg ‖f x‖) hx0.le)
    have hcancel : ‖x i‖*(‖f x‖^2/‖x i‖)=‖f x‖^2 := mul_div_cancel₀ _ hx
    nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingPairApproxIntegral
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

lemma sum_pair_bound {α : Type*} [Fintype α] (A B : α → α → ℝ)
    (h : ∀ i j, B i j ≤ A i j + A j i) :
    (∑ i, ∑ j, B i j) ≤ 2*(∑ i, ∑ j, A i j) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => h i j))
  simp only [Finset.sum_add_distrib] at hh
  have hc : (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j := Finset.sum_comm
  rw [hc] at hh
  linarith

lemma sum_excluding_const {N : ℕ} (i : Fin (N+1)) (c : ℝ) :
    (∑ j : Fin (N+1), if i ≠ j then c else 0) = (N:ℝ)*c := by
  have hh := sum_excluding_add i (fun _ => c)
  simp only [ne_eq, ne_comm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hh
  linarith


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

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

attribute [local irreducible] bindingTotalMultiplier graphNuclear graphPair
  weightedMass weightedGradient weightedFullDensity weightedCoreDensity weightedNuclear weightedPairs

attribute [local irreducible] weightedKinetic graphKineticPair

lemma bindingTotal_mass {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    weightedMass F (bindingTotalMultiplier hR hε).value =
      ∑ i, weightedMass F (fun x => bindingWeight R ε (x i)) := by
  unfold weightedMass
  simp only [bindingTotal_integral hR hε (Lp.memLp _).norm.integrable_sq]
  rw [Finset.sum_comm]

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

lemma graph_mass_integral {N : ℕ} (F : fermionGraph N) :
    (∑ s, ∫ x, ‖graphComponent s none F x‖ ^ 2) = ‖fermionGraphValue N F‖ ^ 2 := by
  rw [graphValue_norm_sq]
  simp only [lp_norm_sq]

attribute [local irreducible] bindingNuclearSum bindingPairSum bindingCappedSum

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_BindingSums
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
section Work_CurrentBindingSums_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  bindingTotalMultiplier graphNuclear weightedMass weightedNuclear weightedPairs

lemma graphNuclearSum_bound {N : ℕ} (F : fermionGraph N) :
    graphNuclearSum F ≤ ((N:ℝ)+1)*‖F‖^2 := by
  have hi (s : Spins N) (i : Fin N) :
      (∫ x, ‖graphComponent s none F x‖^2/‖x i‖) ≤
        (1/4:ℝ)*(∑ a, ‖graphComponent s (some (i,a)) F‖^2)+
          ‖graphComponent s none F‖^2 := by
    have hh := graphNuclear_bound (Z := 1) (by norm_num) F s i
    simpa only [one_mul,one_pow,graphNuclear_norm_sq,graphFormVector_value_eq] using hh
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ => hi s i
  have hm := graphValue_norm_sq F
  have hg := fermionGraph_norm_sq F
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  rw [← hm] at hs
  have hk : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  change graphNuclearSum F ≤ _ at hs
  nlinarith [mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hk,
    sq_nonneg ‖fermionGraphValue N F‖]

lemma binding_nuclear_sum_bound {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    (∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i))) ≤
      (N:ℝ)*‖fermionGraphValue N F‖^2+ε*((N:ℝ)+1)*‖F‖^2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun s _ =>
      bindingWeight_nuclear_integral hR hε i (Lp.memLp (graphComponent s none F))
        (graph_nuclear_integrable F s i)
  have hn := mul_le_mul_of_nonneg_left (graphNuclearSum_bound F) hε.le
  have he : (∑ i : Fin N,∑ s : Spins N,
      ((∫ x, ‖graphComponent s none F x‖^2)+
        ε*(∫ x, ‖graphComponent s none F x‖^2/‖x i‖))) =
      (N:ℝ)*‖fermionGraphValue N F‖^2+ε*graphNuclearSum F := by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,graph_mass_integral,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold graphNuclearSum
    rw [Finset.sum_comm]
  have hs' : (∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i))) ≤
      (N:ℝ)*‖fermionGraphValue N F‖^2+ε*graphNuclearSum F := by
    simpa only [weightedNuclear] using hs.trans_eq he
  exact hs'.trans (by nlinarith only [hn])

lemma sum_pair_tail_bound {N : ℕ} (P : Fin (N+1) → Fin (N+1) → ℝ)
    (W : Fin (N+1) → ℝ) (m c : ℝ)
    (hp : ∀ i j, i ≠ j → m ≤ (P i j+c*W i)+(P j i+c*W j)) :
    ((N:ℝ)+1)*(N:ℝ)*m ≤
      2*(∑ i,∑ j,if i ≠ j then P i j else 0)+2*(N:ℝ)*c*(∑ i,W i) := by
  classical
  let A (i j : Fin (N+1)) : ℝ := if i ≠ j then P i j+c*W i else 0
  let B (i j : Fin (N+1)) : ℝ := if i ≠ j then m else 0
  have hh : ∀ i j, B i j ≤ A i j+A j i := by
    intro i j
    by_cases hij : i ≠ j
    · simpa only [A,B,ite_eq_left hij,ite_eq_left hij.symm] using hp i j hij
    · obtain rfl := not_ne_iff.mp hij
      simp only [A,B,ne_eq,not_true_eq_false,ite_false,add_zero,le_refl]
  have hs := sum_pair_bound A B hh
  have hB : (∑ i,∑ j,B i j)=((N:ℝ)+1)*(N:ℝ)*m := by
    simp only [B,sum_excluding_const,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    ring
  have hA (i : Fin (N+1)) : (∑ j,A i j)=
      (∑ j,if i ≠ j then P i j else 0)+(N:ℝ)*c*W i := by
    calc
      _ = ∑ j,((if i ≠ j then P i j else 0)+(if i ≠ j then c*W i else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [A]
        split_ifs <;> simp
      _ = _ := by rw [Finset.sum_add_distrib,sum_excluding_const]; ring
  rw [hB] at hs
  simp only [hA,Finset.sum_add_distrib,← Finset.mul_sum] at hs
  linarith

lemma binding_pair_sum_bound {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph (N+1)) :
    ((N:ℝ)+1)*(N:ℝ)*‖fermionGraphValue (N+1) F‖^2 ≤
      2*(∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
        2*(N:ℝ)/R*weightedMass F (bindingTotalMultiplier hR hε).value := by
  classical
  let P (s : Spins (N+1)) (i j : Fin (N+1)) : ℝ :=
    ∫ x,bindingWeight R ε (x i)*(‖graphComponent s none F x‖^2/‖x i-x j‖)
  let W (s : Spins (N+1)) (i : Fin (N+1)) : ℝ :=
    ∫ x,bindingWeight R ε (x i)*‖graphComponent s none F x‖^2
  have hb (s : Spins (N+1)) := sum_pair_tail_bound (P s) (W s)
    (∫ x,‖graphComponent s none F x‖^2) R⁻¹
    (fun i j hij => bindingWeight_pair_integral hR hε i j hij (Lp.memLp _)
      (graph_pair_integrable F s i j hij))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ => hb s
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,graph_mass_integral] at hs
  have hP : (∑ s,∑ i,∑ j,if i ≠ j then P s i j else 0)=
      ∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)) := by
    unfold weightedPairs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [P]
    split_ifs <;> simp
  have hW : (∑ s,∑ i,W s i)=weightedMass F (bindingTotalMultiplier hR hε).value := by
    rw [bindingTotal_mass hR hε]
    unfold weightedMass
    exact Finset.sum_comm
  have ht := congrArg₂ (fun u v => 2*u+2*(N:ℝ)*R⁻¹*v) hP hW
  have he : 2*(∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
      2*(N:ℝ)*R⁻¹*weightedMass F (bindingTotalMultiplier hR hε).value =
      2*(∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
        2*(N:ℝ)/R*weightedMass F (bindingTotalMultiplier hR hε).value := by ring
  exact hs.trans_eq (ht.trans he)

end Work_CurrentBindingSums_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

lemma FermionMultiplier.mass_bound {N : ℕ} (p : FermionMultiplier N)
    {C : ℝ} (hC : ∀ x, |p.value x| ≤ C) (F : fermionGraph N) :
    ‖fermionGraphValue N (p.apply F)‖^2 ≤ C^2*‖fermionGraphValue N F‖^2 := by
  rw [graphValue_norm_sq,graphValue_norm_sq,Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => l2_real_multiplier_bound _ _ p.value hC
    (p.apply_value F s)

lemma FermionMultiplier.kinetic_bound {N : ℕ} (p : FermionMultiplier N)
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

theorem FermionMultiplier.graph_bound {N : ℕ} (p : FermionMultiplier N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : fermionGraph N, ‖p.apply F‖^2 ≤ C*‖F‖^2 := by
  classical
  obtain ⟨C,hC⟩ := p.bound
  choose D hD using p.gradient_bound
  let S : ℝ := ∑ i : Fin N,∑ a : Fin 3,D (i,a)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  refine ⟨3*C^2+2*S,by positivity,fun F => ?_⟩
  have hm := p.mass_bound hC F
  have hk := p.kinetic_bound hC D (fun i a x => hD (i,a) x) F
  have hkin : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  exact graph_multiplier_arithmetic (sq_nonneg _) hkin hS hm hk
    (fermionGraph_norm_sq F) (fermionGraph_norm_sq (p.apply F))

theorem quantum_approximate_multiplier {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    (p : FermionMultiplier N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2=1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪p.apply F,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ := by
  exact approximate_positive_form (sectorExcessOperator Z N)
    (sectorExcessOperator_positive hZ N) p.apply (FermionMultiplier.graph_bound p)
    (fun F => ‖fermionGraphValue N F‖^2=1) (by positivity)
    (fun _ hη => quantum_sector_excess_near_minimizer hZ N hη) hδ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ActualPricedParticleBound
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
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  bindingTotalMultiplier graphNuclear sectorExcessOperator
  weightedMass weightedPairs weightedNuclear weightedCoreDensity

theorem quantum_positive_price_binding_bound_oai {Z lam : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N : ℕ}
    (hstep : energy Z (N+1)+lam ≤ energy Z N) : (N:ℝ) ≤ 2*Z := by
  let R : ℝ := ((N:ℝ)+1)/lam
  have hR : 0 < R := div_pos (by positivity) hlam
  have hRl : R*lam = (N:ℝ)+1 := div_mul_cancel₀ _ hlam.ne'
  have htail : 2*(N:ℝ)/R ≤ 2*lam := by
    apply (div_le_iff₀ hR).mpr
    nlinarith only [hRl]
  let K : ℝ := 4*(|energy Z (N+1)|+((N+1:ℕ):ℝ)*Z^2+2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hεlim (ε : ℝ) (hε : 0 < ε) :
      ((N:ℝ)+1)*(N:ℝ) ≤ 2*Z*(((N:ℝ)+1)+ε*((N:ℝ)+2)*K) := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨F,hn,hFK,hr⟩ := quantum_approximate_multiplier hZ (N+1)
      (bindingTotalMultiplier hR hε) (half_pos hδ)
    change ‖F‖^2 ≤ K at hFK
    have hp := binding_pair_sum_bound hR hε F
    have hv := binding_nuclear_sum_bound hR hε F
    have hb := quantum_binding_residual hZ F hstep hR hε
    have hm : 0 ≤ weightedMass F (bindingTotalMultiplier hR hε).value := by
      apply weightedMass_nonneg
      intro x
      rw [bindingTotalMultiplier_value]
      exact Finset.sum_nonneg fun i _ => (bindingWeight_pos hR hε (x i)).le
    have ht := mul_le_mul_of_nonneg_right htail hm
    have hkn := mul_le_mul_of_nonneg_left hFK
      (show 0 ≤ ε*((N:ℝ)+2) by positivity)
    simp only [hn,mul_one,Nat.cast_add,Nat.cast_one] at hp hv
    have hv' : (∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i))) ≤
        ((N:ℝ)+1)+ε*((N:ℝ)+2)*K := by nlinarith only [hv,hkn]
    have hzv := mul_le_mul_of_nonneg_left hv' hZ
    nlinarith only [hp,ht,hb,hr,hzv]
  have hfinal : ((N:ℝ)+1)*(N:ℝ) ≤ 2*Z*((N:ℝ)+1) := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let C : ℝ := 2*Z*((N:ℝ)+2)*K
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let ε : ℝ := δ/(C+1)
    have hε : 0 < ε := div_pos hδ (by linarith)
    have he : ε*(C+1)=δ := div_mul_cancel₀ _ (by linarith : C+1 ≠ 0)
    have hh := hεlim ε hε
    have hCe : C*ε ≤ δ := by nlinarith only [he,hε]
    dsimp only [C] at hCe
    nlinarith only [hh,hCe]
  have hnpos : 0 < (N:ℝ)+1 := by positivity
  nlinarith only [hfinal,hnpos]

end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.quantum_positive_price_binding_bound_oai := @OAI.CoulombAtom.quantum_positive_price_binding_bound_oai
