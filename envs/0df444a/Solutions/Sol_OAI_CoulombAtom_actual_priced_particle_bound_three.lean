-- Prove2me | solution 1 for OAI.CoulombAtom.actual_priced_particle_bound_three
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:37:00.476142+00:00
-- url     : https://prove2.me/submissions/aaae0e07-d126-48b5-bc45-0321a9ecf153

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C008
import Definitions.Def_OAIQ071C009

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

lemma FermionMultiplier.apply_gradient {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    (graphComponent s (some (i, a)) (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s (some (i, a)) F x +
        Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * graphComponent s none F x :=
  p.toSmoothMultiplier.apply_gradient (F.val s) (i, a)

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

lemma linear_hardy_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / (4 * ‖P x‖ ^ 2)) ∧
      (∫ x, ‖f x‖ ^ 2 / (4 * ‖P x‖ ^ 2)) ≤ ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  obtain ⟨hi,hb⟩ := linear_hardy_integrable_bound P v hPv hf hg hweak
  have he : (fun x => ‖f x‖^2/(4*‖P x‖^2)) =
      fun x => (1/4:ℝ)*(‖f x‖^2/‖P x‖^2) := by funext x; ring
  rw [he]
  refine ⟨hi.const_mul _,?_⟩
  rw [integral_const_mul]
  linarith

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
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma SmoothMultiplier.weighted_kinetic_nonneg (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) (p : SmoothMultiplier v)
    (hp : ∀ x, (∑ a : Fin 3, (lineDeriv ℝ p.value x (v a)) ^ 2) ≤
      (p.value x) ^ 2 / (4 * ‖P x‖ ^ 2)) (F : weakGraph v) :
    0 ≤ ∑ a : Fin 3, (⟪(p.apply (p.apply F)).val (some a), F.val (some a)⟫_ℂ).re := by
  have hh := linear_hardy_bound P v hPv (Lp.memLp ((p.apply F).val none))
    (fun a => Lp.memLp ((p.apply F).val (some a)))
    ((mem_weakGraph v (p.apply F).val).mp (p.apply F).property)
  have hi (a : Fin 3) : Integrable (fun x =>
      (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2) := by
    obtain ⟨C,hC⟩ := p.gradient_bound a
    apply (Lp.memLp (F.val none)).norm.integrable_sq.bdd_mul (c := C ^ 2)
      ((p.derivative_continuous a).pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖lineDeriv ℝ p.value x (v a) ^ 2‖ ≤ C ^ 2
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  have hims (a : Fin 3) : ‖(p.apply F).val (some a)‖ ^ 2 -
      (⟪(p.apply (p.apply F)).val (some a), F.val (some a)⟫_ℂ).re =
        ∫ x, (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2 := by
    apply l2_ims_identity p.value (fun x => lineDeriv ℝ p.value x (v a))
      (F.val (some a)) (F.val none) ((p.apply F).val (some a))
      ((p.apply (p.apply F)).val (some a)) (p.apply_gradient F a)
    filter_upwards [p.apply_gradient (p.apply F) a, p.apply_value F] with x hx hy
    rw [hx, hy]
  have hl : (∑ a : Fin 3, ∫ x, (lineDeriv ℝ p.value x (v a)) ^ 2 * ‖F.val none x‖ ^ 2) ≤
      ∫ x, ‖(p.apply F).val none x‖ ^ 2 / (4 * ‖P x‖ ^ 2) := by
    rw [← integral_finsetSum _ fun a _ => hi a]
    apply integral_mono_ae (integrable_finsetSum _ fun a _ => hi a) hh.1
    filter_upwards [p.apply_value F] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      ← Finset.sum_mul]
    have h := mul_le_mul_of_nonneg_right (hp x) (sq_nonneg ‖F.val none x‖)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsum := hl.trans hh.2
  simp_rw [← hims, ← l2_norm_sq] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  linarith

end

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

lemma bindingWeight_le_radius {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    bindingWeight R ε x ≤ regularizedRadius ε x := by
  have ht := regularizedRadius_pos hε x
  unfold bindingWeight
  apply (div_le_iff₀ (by positivity : 0 < R + regularizedRadius ε x)).mpr
  nlinarith [sq_nonneg (regularizedRadius ε x)]

lemma bindingRoot_hardy_control {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    (∑ a : Fin 3, (fderiv ℝ (bindingRoot R ε) x (EuclideanSpace.single a 1)) ^ 2) ≤
      bindingRoot R ε x ^ 2 / (4 * ‖x‖ ^ 2) := by
  simp only [bindingRoot_derivative hR hε, div_pow, mul_pow,
    ← Finset.sum_div, ← Finset.mul_sum, sum_coordinate_sq]
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let t := regularizedRadius ε x
  have ht : 0 < t := regularizedRadius_pos hε x
  have hnt : ‖x‖ ≤ t := norm_le_regularizedRadius ε x
  change bindingRoot R ε x ^ 2 * R^2 * ‖x‖^2 /
    (2^2 * (t^2)^2 * (R+t)^2) ≤ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hfour : ‖x‖^4 ≤ t^4 := pow_le_pow_left₀ (norm_nonneg _) hnt 4
  have hRs : R^2 ≤ (R+t)^2 := by nlinarith
  have hm := mul_le_mul hfour hRs (sq_nonneg R) (pow_nonneg ht.le 4)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 * bindingRoot R ε x ^ 2 by positivity)
  nlinarith [sq_nonneg (bindingRoot R ε x)]


open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Restriction
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
namespace CoulombAtom
section Restriction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
lemma SmoothMultiplier.restrict_apply {v : ι → E} (p : SmoothMultiplier v)
    (j : κ → ι) (F : weakGraph v) :
    (p.restrict j).apply (restrictWeakGraph v j F) = restrictWeakGraph v j (p.apply F) := by
  apply weakGraphValue_injective (v ∘ j)
  apply Lp.ext
  exact (p.restrict j).apply_value (restrictWeakGraph v j F) |>.trans (p.apply_value F).symm

omit [Fintype ι] in
lemma SmoothMultiplier.projected_kinetic_nonneg {v : ι → E}
    (P : E →L[ℝ] Space) (j : Fin 3 → ι)
    (hP : ∀ a, P (v (j a)) = EuclideanSpace.single a 1) (p : SmoothMultiplier v)
    (hp : ∀ x, (∑ a : Fin 3, (lineDeriv ℝ p.value x (v (j a))) ^ 2) ≤
      p.value x ^ 2 / (4 * ‖P x‖ ^ 2)) (F : weakGraph v) :
    0 ≤ ∑ a : Fin 3, (⟪(p.apply (p.apply F)).val (some (j a)), F.val (some (j a))⟫_ℂ).re := by
  have hh := (p.restrict j).weighted_kinetic_nonneg P (v ∘ j) hP hp
    (restrictWeakGraph v j F)
  rw [p.restrict_apply, p.restrict_apply] at hh
  exact hh

end Restriction

lemma bindingMultiplier_kinetic_nonneg {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i : Fin N) (F : weakGraph (sectorDirections N)) :
    0 ≤ ∑ a : Fin 3, (⟪((bindingMultiplier hR hε i).apply
      ((bindingMultiplier hR hε i).apply F)).val (some (i,a)), F.val (some (i,a))⟫_ℂ).re := by
  apply (bindingMultiplier hR hε i).projected_kinetic_nonneg (electronProjection i)
    (fun a => (i,a))
  · intro a
    simp [sectorDirections, direction, electronProjection]
  · intro x
    simpa [bindingMultiplier, sectorDirections, lineDeriv_binding_coordinate hR hε,
      electronProjection] using bindingRoot_hardy_control hR hε (x i)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

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

lemma bindingTotalMultiplier_component {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) (s : Spins N) (k : Option (Fin N × Fin 3)) :
    graphComponent s k ((bindingTotalMultiplier hR hε).apply F) =
      ∑ i, ((bindingMultiplier hR hε i).apply ((bindingMultiplier hR hε i).apply (F.val s))).val k := by
  change ((SmoothMultiplier.sumSquares (bindingMultiplier hR hε)).apply (F.val s)).val k = _
  rw [SmoothMultiplier.sumSquares_apply, weakGraph_sum_component]


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

lemma binding_pairing_off {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : weakGraph (sectorDirections N)) (i j : Fin N) (hij : i ≠ j) (a : Fin 3) :
    (⟪((bindingMultiplier hR hε i).apply ((bindingMultiplier hR hε i).apply F)).val
      (some (j,a)), F.val (some (j,a))⟫_ℂ).re =
      ∫ x, bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2 := by
  apply l2_real_weight_pairing
  have hd (x : Configuration N) : lineDeriv ℝ (bindingMultiplier hR hε i).value x
      (sectorDirections N (j,a)) = 0 := by
    simp only [bindingMultiplier, sectorDirections, lineDeriv_binding_coordinate hR hε,
      ite_eq_right (Ne.symm hij)]
  filter_upwards [(bindingMultiplier hR hε i).apply_gradient
    ((bindingMultiplier hR hε i).apply F) (j,a),
    (bindingMultiplier hR hε i).apply_gradient F (j,a)] with x hx hy
  rw [hd, Complex.ofReal_zero, zero_mul, add_zero] at hx hy
  rw [hx, hy]
  change (bindingRoot R ε (x i) : ℂ) * ((bindingRoot R ε (x i) : ℂ) * _) = _
  rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, bindingRoot_sq hR hε]

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

lemma bindingKinetic_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : weakGraph (sectorDirections N)) (i : Fin N) :
    (∑ j, ∑ a, ∫ x, bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2) -
      (∑ a, ∫ x, bindingWeight R ε (x i) * ‖F.val (some (i,a)) x‖ ^ 2) ≤
    ∑ j, ∑ a, (⟪((bindingMultiplier hR hε i).apply
      ((bindingMultiplier hR hε i).apply F)).val (some (j,a)), F.val (some (j,a))⟫_ℂ).re := by
  classical
  let A (j : Fin N) := ∑ a, ∫ x,
    bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2
  let B (j : Fin N) := ∑ a, (⟪((bindingMultiplier hR hε i).apply
    ((bindingMultiplier hR hε i).apply F)).val (some (j,a)), F.val (some (j,a))⟫_ℂ).re
  have hoff (j : Fin N) (hji : j ≠ i) : B j = A j := by
    apply Finset.sum_congr rfl; intro a _
    exact binding_pairing_off hR hε F i j hji.symm a
  have he : (∑ j, if j ≠ i then B j else 0) = ∑ j, if j ≠ i then A j else 0 := by
    apply Finset.sum_congr rfl; intro j _
    split_ifs with hji
    · exact hoff j hji
    · rfl
  have ha := sum_excluding_add i A
  have hb := sum_excluding_add i B
  have hp : 0 ≤ B i := bindingMultiplier_kinetic_nonneg hR hε i F
  change (∑ j, A j) - A i ≤ ∑ j, B j
  rw [he] at hb
  linarith


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

lemma binding_total_kinetic_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ((∑ j : Fin N, ∑ a : Fin 3, ∫ x, bindingWeight R ε (x i) *
        ‖graphComponent s (some (j,a)) F x‖ ^ 2) -
      (∑ a : Fin 3, ∫ x, bindingWeight R ε (x i) * ‖graphComponent s (some (i,a)) F x‖ ^ 2))) ≤
      ∑ s : Spins N, ∑ j : Fin N, ∑ a : Fin 3, (⟪graphComponent s (some (j,a)) ((bindingTotalMultiplier hR hε).apply F),
        graphComponent s (some (j,a)) F⟫_ℂ).re := by
  classical
  have h (s : Spins N) := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => bindingKinetic_lower hR hε (F.val s) i)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun s _ => h s)
  simp only [← graphComponent_apply] at hs
  apply le_trans hs
  apply le_of_eq
  apply Finset.sum_congr rfl; intro s _
  simp only [bindingTotalMultiplier_component, sum_inner, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]

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

lemma bindingTotal_full {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (Z : ℝ) (F : fermionGraph N) :
    weightedFullDensity Z F (bindingTotalMultiplier hR hε).value =
      ∑ i, weightedFullDensity Z F (fun x => bindingWeight R ε (x i)) := by
  unfold weightedFullDensity
  simp only [bindingTotal_integral hR hε ((graphFormVector_sobolev F).quantumEnergyDensity_integrable Z _)]
  exact Finset.sum_comm

lemma bindingTotal_kinetic {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    weightedKinetic F (bindingTotalMultiplier hR hε).value =
      ∑ s, ∑ j, ∑ i, ∑ a, ∫ x, bindingWeight R ε (x j) *
        ‖graphComponent s (some (i,a)) F x‖ ^ 2 := by
  rw [weightedKinetic_expand]
  simp only [bindingTotal_integral hR hε (Lp.memLp _).norm.integrable_sq]
  apply Finset.sum_congr rfl; intro s _
  exact sum_rotate_three (fun i a j => ∫ x, bindingWeight R ε (x j) *
    ‖graphComponent s (some (i,a)) F x‖ ^ 2)

lemma sum_sub_le_transport {α β : Type*} [Fintype α] [Fintype β]
    (a b : α → β → ℝ) (G W K : ℝ)
    (ha : (∑ s, ∑ i, a s i) = W) (hb : (∑ s, ∑ i, b s i) = K)
    (hc : (∑ s, ∑ i, (a s i-b s i)) ≤ G) : W-K ≤ G := by
  rw [← ha, ← hb]
  simpa only [Finset.sum_sub_distrib] using hc

lemma bindingTotal_kinetic_diagonal {N : ℕ} (F : fermionGraph N) (R ε : ℝ) :
    (∑ s, ∑ i, ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (i,a)) F x‖ ^ 2) =
      ∑ i, weightedGradient F (fun x => bindingWeight R ε (x i)) i := by
  unfold weightedGradient
  exact Finset.sum_comm

lemma bindingTotal_kinetic_lower_packed {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    weightedKinetic F (bindingTotalMultiplier hR hε).value -
      (∑ i, weightedGradient F (fun x => bindingWeight R ε (x i)) i) ≤
      graphKineticPair ((bindingTotalMultiplier hR hε).apply F) F := by
  exact sum_sub_le_transport
    (fun s i => ∑ j, ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (j,a)) F x‖ ^ 2)
    (fun s i => ∑ a, ∫ x, bindingWeight R ε (x i) *
      ‖graphComponent s (some (i,a)) F x‖ ^ 2)
    _ _ _ (bindingTotal_kinetic hR hε F).symm
    (bindingTotal_kinetic_diagonal F R ε) (by
      unfold graphKineticPair
      exact binding_total_kinetic_lower hR hε F)

lemma FermionMultiplier.form_weighted_packed {N : ℕ} (Z : ℝ) (p : FermionMultiplier N)
    (F : fermionGraph N) :
    (⟪p.apply F, coulombFormOperator Z N F⟫_ℂ).re =
      weightedFullDensity Z F p.value + (1/2:ℝ)*
        (graphKineticPair (p.apply F) F-weightedKinetic F p.value) := by
  simpa only [weightedKinetic_expand, weightedFullDensity, graphKineticPair] using
    p.form_weighted_identity Z F

lemma binding_form_sum_arithmetic {ι : Type*} [Fintype ι]
    (D C K V P : ι → ℝ) (Z W G A Dt : ℝ)
    (hD : ∀ i, D i = C i + (1/2:ℝ)*K i - Z*V i + P i)
    (hG : W-(∑ i, K i) ≤ G) (hDt : Dt = ∑ i, D i)
    (hA : A = Dt+(1/2:ℝ)*(G-W)) :
    (∑ i, (C i-Z*V i+P i)) ≤ A := by
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hD i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs ⊢
  linarith

lemma binding_form_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (Z : ℝ) (F : fermionGraph N) :
    (∑ i : Fin N, (weightedCoreDensity Z F i (fun x => bindingWeight R ε (x i)) -
      Z * weightedNuclear F i (fun x => bindingWeight R ε (x i)) +
      weightedPairs F i (fun x => bindingWeight R ε (x i)))) ≤
      (⟪(bindingTotalMultiplier hR hε).apply F, coulombFormOperator Z N F⟫_ℂ).re := by
  let w : Fin N → Configuration N → ℝ := fun i x => bindingWeight R ε (x i)
  have hc (i : Fin N) : Continuous (w i) :=
    (bindingWeight_continuous hR hε).comp (continuous_apply i)
  have hb (i : Fin N) (x : Configuration N) : ‖w i x‖ ≤ R := by
    change ‖bindingWeight R ε (x i)‖ ≤ R
    rw [Real.norm_of_nonneg (bindingWeight_pos hR hε (x i)).le]
    exact bindingWeight_le hR hε (x i)
  exact binding_form_sum_arithmetic _ _ _ _ _ Z _ _ _ _
    (fun i => weightedFullDensity_delete Z F i (w i) (hc i) (hb i))
    (bindingTotal_kinetic_lower_packed hR hε F) (bindingTotal_full hR hε Z F)
    ((bindingTotalMultiplier hR hε).form_weighted_packed Z F)

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingResidual
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

lemma energy_weighted_core_price_le {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hstep : energy Z (N+1)+lam ≤ energy Z N)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (i : Fin (N+1)) :
    (energy Z (N+1)+lam)*weightedMass F (fun x => bindingWeight R ε (x i)) ≤
      weightedCoreDensity Z F i (fun x => bindingWeight R ε (x i)) := by
  have hm := weightedMass_nonneg F (fun x => (bindingWeight_pos hR hε (x i)).le)
  have hb (y : Space) : ‖bindingWeight R ε y‖ ≤ R := by
    rw [Real.norm_of_nonneg (bindingWeight_pos hR hε y).le]
    exact bindingWeight_le hR hε y
  have hi := weighted_core_coordinate F hZ i (bindingWeight R ε)
    (bindingWeight_continuous hR hε) (fun y => (bindingWeight_pos hR hε y).le) hb
  apply (mul_le_mul_of_nonneg_right hstep hm).trans
  simpa only [weightedMass,weightedCoreDensity] using hi

lemma binding_residual_cancellation {ι : Type*} [Fintype ι]
    (C V P M : ι → ℝ) (E lam Z A Mt r : ℝ)
    (hC : ∀ i, (E+lam)*M i ≤ C i) (hM : Mt=∑ i,M i)
    (hA : r=A-E*Mt) (hL : (∑ i,(C i-Z*V i+P i)) ≤ A) :
    (∑ i,P i)+lam*Mt ≤ Z*(∑ i,V i)+r := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hC i
  rw [← Finset.mul_sum,← hM] at hs
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hL
  nlinarith

lemma quantum_binding_residual {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph (N+1)) (hstep : energy Z (N+1)+lam ≤ energy Z N)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    (∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
      lam*weightedMass F (bindingTotalMultiplier hR hε).value ≤
    Z*(∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i)))+
      (⟪(bindingTotalMultiplier hR hε).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re := by
  have he := sectorExcessOperator_pair Z ((bindingTotalMultiplier hR hε).apply F) F
  have hp := FermionMultiplier.value_weighted_pairing F (bindingTotalMultiplier hR hε)
  have he' := he.trans (congrArg (fun t : ℝ =>
    (⟪(bindingTotalMultiplier hR hε).apply F,coulombFormOperator Z (N+1) F⟫_ℂ).re-
      energy Z (N+1)*t) hp)
  exact binding_residual_cancellation _ _ _ _ _ _ _ _ _ _
    (fun i => energy_weighted_core_price_le hZ F hstep hR hε i)
    (bindingTotal_mass hR hε F) he' (binding_form_lower hR hε Z F)

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

theorem quantum_positive_price_binding_bound {Z lam : ℝ} (hZ : 0 ≤ Z)
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

theorem actual_priced_particle_bound {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) : (N:ℝ) ≤ 2*Z+1 := by
  cases N with
  | zero => simp only [Nat.cast_zero]; positivity
  | succ n =>
    have hs := hN n
    simp only [Nat.cast_add,Nat.cast_one] at hs ⊢
    have hstep : energy Z (n+1)+lam ≤ energy Z n := by nlinarith only [hs]
    have hh := quantum_positive_price_binding_bound hZ hlam hstep
    linarith only [hh]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ActualSectorPlateau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
attribute [local irreducible] fermionGraph fermionGraphValue graphFormVector
  formEnergy energy

theorem actual_priced_particle_bound_three_oai (Z : ℕ) (hZ : 1 ≤ Z)
    {lam : ℝ} (hlam : 0 < lam) {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) : N ≤ 3*Z := by
  have h := actual_priced_particle_bound (Nat.cast_nonneg Z) hlam hN
  have hz : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hh : (N:ℝ) ≤ 3*Z := by linarith only [h,hz]
  exact_mod_cast hh

end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.actual_priced_particle_bound_three_oai := @OAI.CoulombAtom.actual_priced_particle_bound_three_oai
