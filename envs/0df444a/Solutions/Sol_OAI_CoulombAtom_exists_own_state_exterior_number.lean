-- Prove2me | solution 1 for OAI.CoulombAtom.exists_own_state_exterior_number
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:49:24.940017+00:00
-- url     : https://prove2.me/submissions/38bfcd1e-edd4-431e-bcad-52dd460990a8

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_actual_shell_number
import Theorems.Thm_OAI_CoulombAtom_exists_actual_own_probability_tail_tilt_state
import Theorems.Thm_OAI_CoulombAtom_exists_own_state_shell_residual

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

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

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

lemma graph_value_components_ext {N : ℕ} {F G : fermionGraph N}
    (h : ∀ s, graphComponent s none F = graphComponent s none G) : F = G := by
  apply fermionGraphValue_injective N
  apply Subtype.ext
  apply PiLp.ext
  intro s
  exact h s

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
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialInside
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
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma radialCut_inner {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : ‖x-y‖ ≤ t) :
    (radialCut y ht hb 0).value x = 1 ∧ (radialCut y ht hb 1).value x = 0 := by
  simp [radialCut, radialInside, radialOutside, radialPhase_zero ht hb hx]

end CoulombAtom

open scoped BigOperators

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

lemma graphRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ, hn, ENNReal.ofReal_one]

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

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

lemma formRawLaw_graph {N : ℕ} (F : fermionGraph N) :
    formRawLaw (graphFormVector F) = graphRawLaw F := rfl

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

lemma graphFormVector_value_eq {N : ℕ} (F : fermionGraph N) (s : Spins N) (x : Configuration N) :
    (graphFormVector F).value s x = graphComponent s none F x := rfl

attribute [local irreducible] graphComponent graphFormVector

end


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

attribute [local irreducible] sectorExcessOperator

lemma sectorExcessOperator_positive {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) :
    (sectorExcessOperator Z N).IsPositive := by
  unfold sectorExcessOperator
  exact shifted_form_positive (fermionGraphValue N) (coulombFormOperator Z N)
    (coulombFormOperator_selfAdjoint Z N) (energy Z N) (graphForm_lower hZ)

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
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_GraphWeightIntegral
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma weightedMass_eq_integral {N : ℕ} (F : fermionGraph N)
    (w : Configuration N → ℝ) (hm : Measurable w) {A : ℝ} (hb : ∀ x, ‖w x‖ ≤ A) :
    weightedMass F w = ∫ x, w x ∂graphRawLaw F := by
  have hh := rawFormPair_eq_integral (graphFormVector_sobolev F).sobolevVector hm hb
  simpa only [rawFormPair,weightedMass,graphFormVector_value_eq,formRawLaw_graph] using hh

lemma graph_weight_integrable {N : ℕ} (F : fermionGraph N)
    (w : Configuration N → ℝ) (hm : Measurable w) {A : ℝ} (hb : ∀ x, ‖w x‖ ≤ A) :
    Integrable w (graphRawLaw F) :=
  Integrable.of_bound hm.aestronglyMeasurable A (ae_of_all _ hb)

lemma gradientError_eq_weightedMass {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) : oneBodyGradientError p F =
      ∑ i : Fin N,∑ a : Fin 3,weightedMass F (fun x =>
        (lineDeriv ℝ p.value (x i) (spaceDirections a))^2) := by
  unfold oneBodyGradientError weightedMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

lemma rawGradientWeight_nonneg {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) : 0 ≤ rawGradientWeight p x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma rawGradientWeight_measurable {N : ℕ} (p : SmoothMultiplier spaceDirections) :
    Measurable (rawGradientWeight (N := N) p) :=
  Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun a _ =>
    (((smooth_lineDeriv_continuous p.regular (spaceDirections a)).comp (continuous_apply i)).pow 2).measurable))
lemma rawGradientWeight_le {N : ℕ} (p : SmoothMultiplier spaceDirections) {D : ℝ}
    (hD : ∀ a x, |lineDeriv ℝ p.value x (spaceDirections a)| ≤ D) (x : Configuration N) :
    rawGradientWeight p x ≤ 3*N*D^2 := by
  calc
    _ ≤ ∑ _i : Fin N, ∑ _a : Fin 3, D^2 := Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun a _ => by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hD a (x i)) 2
    _ = _ := by simp; ring
lemma rawGradientWeight_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) {D : ℝ} (hD : ∀ a x, |lineDeriv ℝ p.value x (spaceDirections a)| ≤ D) :
    Integrable (rawGradientWeight p) (graphRawLaw F) :=
  graph_weight_integrable F _ (rawGradientWeight_measurable p) (fun x => by
    rw [Real.norm_of_nonneg (rawGradientWeight_nonneg p x)]; exact rawGradientWeight_le p hD x)

lemma gradientError_eq_integral {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) {D : ℝ} (hD : ∀ a x, |lineDeriv ℝ p.value x (spaceDirections a)| ≤ D) :
    oneBodyGradientError p F = ∫ x, rawGradientWeight p x ∂graphRawLaw F := by
  have hm (i : Fin N) (a : Fin 3) : Measurable (fun x : Configuration N =>
      (lineDeriv ℝ p.value (x i) (spaceDirections a))^2) :=
    (((smooth_lineDeriv_continuous p.regular (spaceDirections a)).comp (continuous_apply i)).pow 2).measurable
  have hb (i : Fin N) (a : Fin 3) (x : Configuration N) :
      ‖(lineDeriv ℝ p.value (x i) (spaceDirections a))^2‖ ≤ D^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hD a (x i)) 2
  have hi (i : Fin N) (a : Fin 3) := graph_weight_integrable F _ (hm i a) (hb i a)
  rw [gradientError_eq_weightedMass]
  simp_rw [weightedMass_eq_integral F _ (hm _ _) (hb _ _)]
  unfold rawGradientWeight
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hi i a))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum _ (fun a _ => hi i a)).symm

end
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent fermionGraph weakGraph FermionMultiplier.apply

lemma graph_sum_value {α : Type*} {N : ℕ} (T : Finset α) (G : α → fermionGraph N) (s : Spins N) :
    ∀ᵐ x, graphComponent s none (∑ k ∈ T, G k) x = ∑ k ∈ T, graphComponent s none (G k) x := by
  have he := map_sum (graphComponent s none) G T
  rw [he]
  exact l2_coe_finset_sum volume T (fun k => graphComponent s none (G k))

lemma graph_sub_value {N : ℕ} (F G : fermionGraph N) (s : Spins N) :
    ∀ᵐ x, graphComponent s none (F-G) x = graphComponent s none F x-graphComponent s none G x := by
  have he := map_sub (graphComponent s none) F G
  rw [he]
  exact Lp.coeFn_sub _ _

lemma finite_apply_sum_value {α : Type*} {N : ℕ} (T : Finset α)
    (p : α → FermionMultiplier N) (F : fermionGraph N) (s : Spins N) :
    ∀ᵐ x, graphComponent s none (∑ k ∈ T, (p k).apply F) x =
      ((∑ k ∈ T, (p k).value x : ℝ) : ℂ)*graphComponent s none F x := by
  classical
  have ha : ∀ᵐ x : Configuration N, ∀ k ∈ T,
      graphComponent s none ((p k).apply F) x = ((p k).value x : ℂ)*graphComponent s none F x := by
    apply (ae_ball_iff T.finite_toSet.countable).mpr
    intro k hk
    exact (p k).apply_value F s
  filter_upwards [ha,graph_sum_value T (fun k => (p k).apply F) s] with x ha hx
  calc
    _ = ∑ k ∈ T, graphComponent s none ((p k).apply F) x := hx
    _ = ∑ k ∈ T, ((p k).value x : ℂ)*graphComponent s none F x := Finset.sum_congr rfl ha
    _ = (∑ k ∈ T, ((p k).value x : ℂ))*graphComponent s none F x := (Finset.sum_mul ..).symm
    _ = _ := congrArg (fun z : ℂ => z*graphComponent s none F x) (Complex.ofReal_sum _ _).symm

lemma ofReal_sub_mul_complex (a b : ℝ) (z : ℂ) :
    ((a-b:ℝ):ℂ)*z = (a:ℂ)*z-(b:ℂ)*z := by rw [Complex.ofReal_sub,sub_mul]

lemma finite_apply_sum_eq_sub {α : Type*} {N : ℕ} (T : Finset α)
    (p : α → FermionMultiplier N) (q t : FermionMultiplier N)
    (he : ∀ x, (∑ k ∈ T, (p k).value x) = q.value x-t.value x) (F : fermionGraph N) :
    (∑ k ∈ T, (p k).apply F) = q.apply F-t.apply F := by
  classical
  apply graph_value_components_ext
  intro s
  apply Lp.ext
  filter_upwards [finite_apply_sum_value T p F s,
    graph_sub_value (q.apply F) (t.apply F) s,q.apply_value F s,t.apply_value F s] with x hx hs hq ht
  calc
    _ = ((∑ k ∈ T, (p k).value x : ℝ) : ℂ)*graphComponent s none F x := hx
    _ = ((q.value x-t.value x : ℝ) : ℂ)*graphComponent s none F x := congrArg (fun z : ℝ => (z:ℂ)*graphComponent s none F x) (he x)
    _ = (q.value x : ℂ)*graphComponent s none F x-(t.value x : ℂ)*graphComponent s none F x := ofReal_sub_mul_complex _ _ _
    _ = graphComponent s none ((q.apply F)-(t.apply F)) x := (congrArg₂ (fun a b : ℂ => a-b) hq ht).symm.trans hs.symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_AnnularCellGeometryBarrier
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
section Work_AnnularCellGeometry_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombObservation CoulombBarrier

lemma rawAnnularMoment_nonneg {N : ℕ} (psi : FormVector N) (a b : ℝ) : 0 ≤ rawAnnularMoment psi a b := by
  unfold rawAnnularMoment rawFormPair
  positivity

end Work_AnnularCellGeometry_barrier_scope

open MeasureTheory Set Metric

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_AnnularFirst
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy

lemma probability_first_le_sqrt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Integrable (fun x => f x^2) μ)
    (hn : ∀ x, 0 ≤ f x) : (∫ x, f x ∂μ) ≤ Real.sqrt (∫ x, f x^2 ∂μ) := by
  have hh := sum_integral_sqrt_mul_sqrt_le (ι := Unit) (fun _ => μ)
    (fun _ x => f x^2) (fun _ _ => (1:ℝ)) (fun _ => hf) (fun _ => integrable_const _)
    (fun _ x => sq_nonneg (f x)) (fun _ _ => zero_le_one)
  simpa only [Fintype.sum_unique,Real.sqrt_sq (hn _),Real.sqrt_one,mul_one,integral_const,
    Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] using hh

lemma actual_annular_first_bound {Z lam D r : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hD : 0 ≤ D) (hr : 0 < r)
    (hN : PriceMinimizes (energy Z) lam N) (F : fermionGraph N)
    (hFn : ‖fermionGraphValue N F‖^2 = 1)
    (hFE : formEnergy Z (graphFormVector F) ≤ energy Z N+D) :
    (∫ x, rawAnnularCount r (2*r) x ∂graphRawLaw F) ≤
      (Classical.choose (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one))*
        annularOffsetMass D r := by
  let C := Classical.choose (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)
  have hC : 1 ≤ C := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).1
  have hm : formMass (graphFormVector F) = 1 := (formMass_graph F).trans hFn
  have he : max (corePriceExcess Z lam (graphFormVector F)) 0 ≤ D :=
    max_le (priced_graph_tilt_excess hN F hFn hFE) hD
  have hh := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).2
    Z lam N (graphFormVector F) (graphFormVector_sobolev F) hm hZ hlam D r hD hr he
  have hh' : rawAnnularMoment (graphFormVector F) r (2*r) ≤ C*1*(annularOffsetMass D r)^2 := by
    calc _ = rawAnnularMoment (graphFormVector F) (1*r) (2*r) := by congr 1; ring
         _ ≤ C*(annularOffsetMass D r)^2 := hh
         _ = _ := by ring
  have hs' := sqrt_count_scale (rawAnnularMoment_nonneg (graphFormVector F) r (2*r)) hC (by norm_num : (0:ℝ)≤1)
    (le_trans zero_le_one (annularOffsetMass_one_le D r)) hh'
  have hs : Real.sqrt (rawAnnularMoment (graphFormVector F) r (2*r)) ≤ C*annularOffsetMass D r :=
    hs'.trans_eq (by rw [Real.sqrt_one]; ring)
  let := graphRawLaw_probability F hFn
  have hi : Integrable (fun x => rawAnnularCount r (2*r) x^2) (graphRawLaw F) :=
    graph_weight_integrable F _ ((rawAnnularCount_measurable _ _).pow_const 2) (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (rawAnnularCount_nonneg _ _ _) (rawAnnularCount_le _ _ _) 2)
  have hf := probability_first_le_sqrt (rawAnnularCount r (2*r)) hi (rawAnnularCount_nonneg _ _)
  rw [rawAnnularMoment_eq_integral (graphFormVector_sobolev F).sobolevVector,formRawLaw_graph] at hs
  exact hf.trans hs
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

open MeasureTheory Set Filter
open scoped ContDiff

lemma shellCutoff_support {u : ℝ} (hu : 0 < u) (x : Space)
    (hx : (shellCutoff hu).value x ≠ 0) : u ≤ ‖x‖ ∧ ‖x‖ ≤ 4*u := by
  constructor
  · by_contra h
    have hh := (radialCut_inner hu.le hu (y := 0) (x := x) (by simpa using (le_of_lt (lt_of_not_ge h)))).2
    apply hx
    change (radialOutside 0 hu.le hu).value x*_ = 0
    change (radialOutside 0 hu.le hu).value x = 0 at hh
    rw [hh,zero_mul]
  · by_contra h
    have hh := (radialCut_outer (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) (y := 0) (x := x) (by simp only [sub_zero]; linarith)).1
    apply hx
    change _*(radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x = 0
    change (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x = 0 at hh
    rw [hh,mul_zero]

lemma shellCutoff_compact {u : ℝ} (hu : 0 < u) : HasCompactSupport (shellCutoff hu).value := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (4*u))
  intro x hx
  by_contra hh
  exact hx (by simpa only [Metric.mem_closedBall,dist_zero_right] using (shellCutoff_support hu x hh).2)

lemma shellCutoff_partition {u : ℝ} (hu : 0 < u) (x : Space) :
    (shellCutoff hu).value x^2 =
      (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x^2 -
        (radialInside 0 hu.le hu).value x^2 := by
  have hsum := radialCut_partition 0 hu.le hu x
  simp only [Fin.sum_univ_two,radialCut,Matrix.cons_val_zero,Matrix.cons_val_one] at hsum
  by_cases hx : ‖x‖ ≤ 2*u
  · have hh := (radialCut_inner (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) (y := 0) (x := x) (by simpa using hx)).1
    change (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x = 1 at hh
    change ((radialOutside 0 hu.le hu).value x*(radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x)^2 = _
    rw [hh,mul_one]
    linarith only [hsum]
  · have hh := radialCut_outer hu.le hu (y := 0) (x := x) (by simp only [sub_zero]; linarith [lt_of_not_ge hx])
    change (radialInside 0 hu.le hu).value x = 0 ∧ (radialOutside 0 hu.le hu).value x = 1 at hh
    change ((radialOutside 0 hu.le hu).value x*(radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x)^2 = _
    rw [hh.1,hh.2,one_mul,zero_pow (by decide : 2 ≠ 0),sub_zero]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellCutoffBounds
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators ContDiff
noncomputable section
namespace CoulombAtom

lemma shellCutoff_deriv_le {u : ℝ} (hu : 0 < u) (x : Space) (a : Fin 3) :
    |lineDeriv ℝ (shellCutoff hu).value x (spaceDirections a)| ≤
      2*(Real.pi*smoothTransitionBound)/u := by
  change |lineDeriv ℝ (fun y => (radialOutside 0 hu.le hu).value y*
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value y) x _| ≤ _
  rw [smooth_lineDeriv_mul (radialOutside 0 hu.le hu).regular
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).regular]
  have hA : 0 < Real.pi*smoothTransitionBound := mul_pos Real.pi_pos smoothTransitionBound_pos
  have h1 := radialOutside_deriv_le 0 hu.le hu x a
  have h2 := radialInside_deriv_le 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) x a
  have h3 := radialOutside_abs_le 0 hu.le hu x
  have h4 := radialInside_abs_le 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) x
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  have hh1 := mul_le_mul h1 h4 (abs_nonneg _) (by positivity : 0 ≤ Real.pi*smoothTransitionBound/u)
  have hh2 := mul_le_mul h3 h2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hc : 0 ≤ Real.pi*smoothTransitionBound := by positivity
  have hd : Real.pi*smoothTransitionBound/(2*u) ≤ Real.pi*smoothTransitionBound/u :=
    div_le_div_of_nonneg_left hc hu (by linarith)
  calc
    _ ≤ Real.pi*smoothTransitionBound/u+Real.pi*smoothTransitionBound/(2*u) := by simpa only [mul_one,one_mul] using add_le_add hh1 hh2
    _ ≤ Real.pi*smoothTransitionBound/u+Real.pi*smoothTransitionBound/u := add_le_add_right hd _
    _ = _ := by ring

lemma shellCutoff_deriv_zero {u : ℝ} (hu : 0 < u) (x : Space)
    (hx : ‖x‖ < u) (a : Fin 3) :
    lineDeriv ℝ (shellCutoff hu).value x (spaceDirections a) = 0 := by
  have h1 : lineDeriv ℝ (radialOutside 0 hu.le hu).value x (spaceDirections a) = 0 := by
    change lineDeriv ℝ (fun z => Real.sin (radialPhase 0 u u z)) x _ = _
    rw [radial_sin_derivative,radialPhase_derivative_zero_off_collar hu.le hu (by simp only [sub_zero]; exact fun h => (not_le_of_gt hx) h.1),mul_zero]
  have h2 : (radialOutside 0 hu.le hu).value x = 0 := by
    exact (radialCut_inner hu.le hu (y := 0) (x := x) (by simpa using hx.le)).2
  change lineDeriv ℝ (fun y => (radialOutside 0 hu.le hu).value y*
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value y) x _ = _
  rw [smooth_lineDeriv_mul (radialOutside 0 hu.le hu).regular
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).regular,h1,h2,zero_mul,zero_mul,add_zero]

lemma dyadic_shell_deriv_sum {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Space) (a : Fin 3) :
    (∑ k ∈ Finset.range K,
      (lineDeriv ℝ (shellCutoff (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr)).value x (spaceDirections a))^2) ≤
      (8*(Real.pi*smoothTransitionBound)^2/r^2)*(if r ≤ ‖x‖ then 1 else 0) := by
  classical
  by_cases hx : r ≤ ‖x‖
  · rw [ite_eq_left hx,mul_one]
    have hpoint (k : ℕ) :
        (lineDeriv ℝ (shellCutoff (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr)).value x (spaceDirections a))^2 ≤
          (4*(Real.pi*smoothTransitionBound)^2/r^2)*(1/4:ℝ)^k := by
      have hh := pow_le_pow_left₀ (abs_nonneg _) (shellCutoff_deriv_le (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr) x a) 2
      rw [sq_abs] at hh
      apply hh.trans_eq
      simp only [div_pow,mul_pow,one_div,inv_pow,←pow_mul]
      have hk : (2:ℝ)^(k*2) = 4^k := by rw [Nat.mul_comm,pow_mul]; norm_num
      rw [hk]
      ring
    have hg : (∑ k ∈ Finset.range K, (1/4:ℝ)^k) ≤ 2 := by
      have hh : (∑ k ∈ Finset.range K, (1/4:ℝ)^k) ≤ 2-2*(1/4:ℝ)^K := by
        induction K with
        | zero => norm_num
        | succ K ih =>
          rw [Finset.sum_range_succ,pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/4) K]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/4) K]
    calc
      _ ≤ ∑ k ∈ Finset.range K, (4*(Real.pi*smoothTransitionBound)^2/r^2)*(1/4:ℝ)^k :=
        Finset.sum_le_sum fun k _ => hpoint k
      _ = (4*(Real.pi*smoothTransitionBound)^2/r^2)*(∑ k ∈ Finset.range K, (1/4:ℝ)^k) := (Finset.mul_sum ..).symm
      _ ≤ (4*(Real.pi*smoothTransitionBound)^2/r^2)*2 := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  · rw [ite_eq_right hx,mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k hk
    rw [shellCutoff_deriv_zero _ x (lt_of_lt_of_le (lt_of_not_ge hx)
      (le_mul_of_one_le_left hr.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2)))) a,zero_pow (by decide : 2≠0)]
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellTelescoping
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

section
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma dyadicShell_partition {r : ℝ} (hr : 0 < r) (k : ℕ) (x : Space) :
    (dyadicShell hr k).value x^2 = (dyadicInside hr (k+1)).value x^2-(dyadicInside hr k).value x^2 := by
  have hh := shellCutoff_partition (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr) x
  convert hh using 1 <;> simp only [dyadicShell,dyadicInside,pow_succ,mul_left_comm,mul_comm]

lemma dyadicShell_sum {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Space) :
    (∑ k ∈ Finset.range K, (dyadicShell hr k).value x^2) =
      (dyadicInside hr K).value x^2-(dyadicInside hr 0).value x^2 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih,dyadicShell_partition]; ring

lemma dyadicShell_total_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Configuration N) :
    (∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).value x) =
      (oneBodySquareTotal (dyadicInside hr K)).value x-(oneBodySquareTotal (dyadicInside hr 0)).value x := by
  simp only [oneBodySquareTotal_value]
  rw [Finset.sum_comm]
  simp_rw [dyadicShell_sum]
  rw [Finset.sum_sub_distrib]

lemma dyadicShell_graph_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (F : fermionGraph N) :
    (∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).apply F) =
      (oneBodySquareTotal (dyadicInside hr K)).apply F-(oneBodySquareTotal (dyadicInside hr 0)).apply F := by
  exact finite_apply_sum_eq_sub (Finset.range K) (fun k => oneBodySquareTotal (dyadicShell hr k))
    (oneBodySquareTotal (dyadicInside hr K)) (oneBodySquareTotal (dyadicInside hr 0))
    (dyadicShell_total_sum hr K) F

lemma real_inner_sum_left {V α : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : Finset α) (f : α → V) (G : V) :
    (∑ k ∈ T, (⟪f k,G⟫_ℂ).re) = (⟪∑ k ∈ T, f k,G⟫_ℂ).re := by
  rw [sum_inner]
  exact (Complex.re_sum _ _).symm

end

attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma oneBodySquareTotal_deriv {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) (j : Fin N) (a : Fin 3) :
    lineDeriv ℝ (oneBodySquareTotal p).value x (direction j a) =
      2*p.value (x j)*lineDeriv ℝ p.value (x j) (spaceDirections a) := by
  classical
  unfold oneBodySquareTotal
  change lineDeriv ℝ (fun y => ∑ i, (p.oneBody i).value y^2) x _ = _
  rw [lineDeriv_sumSquares]
  simp only [SmoothMultiplier.oneBody,oneBody_coordinate_derivative,mul_ite,mul_zero]
  simp

lemma oneBodySquareTotal_bound_one {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) (x : Configuration N) :
    |(oneBodySquareTotal p).value x| ≤ N := by
  rw [oneBodySquareTotal_value,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum fun i _ => by
      simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hp (x i)) 2
    _ = _ := by simp

lemma FermionMultiplier.graph_bound_explicit {N : ℕ} (p : FermionMultiplier N)
    {C D : ℝ} (hC : ∀ x, |p.value x| ≤ C)
    (hD : ∀ i a x, |lineDeriv ℝ p.value x (direction i a)| ≤ D) (F : fermionGraph N) :
    ‖p.apply F‖^2 ≤ (3*C^2+6*(N:ℝ)*D^2)*‖F‖^2 := by
  have hm := p.mass_bound hC F
  have hk := p.kinetic_bound hC (fun _ => D) hD F
  have hkin : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hS : 0 ≤ ∑ i : Fin N,∑ a : Fin 3,D^2 := by positivity
  have hh := graph_multiplier_arithmetic (sq_nonneg _) hkin hS hm hk
    (fermionGraph_norm_sq F) (fermionGraph_norm_sq (p.apply F))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma radialInside_square_graph_bound {N : ℕ} {r u : ℝ} (hr : 0 < r)
    (hu : r ≤ u) (F : fermionGraph N) :
    ‖(oneBodySquareTotal (radialInside 0 (hr.trans_le hu).le (hr.trans_le hu))).apply F‖^2 ≤
      (3*(N:ℝ)^2+6*(N:ℝ)*(2*(Real.pi*smoothTransitionBound)/r)^2)*‖F‖^2 := by
  let p := radialInside 0 (hr.trans_le hu).le (hr.trans_le hu)
  apply FermionMultiplier.graph_bound_explicit _ (oneBodySquareTotal_bound_one p (fun x => radialInside_abs_le 0 (hr.trans_le hu).le (hr.trans_le hu) x))
  intro i a x
  rw [oneBodySquareTotal_deriv,abs_mul,abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hc : 0 ≤ Real.pi*smoothTransitionBound := (mul_pos Real.pi_pos smoothTransitionBound_pos).le
  have hd := (radialInside_deriv_le 0 (hr.trans_le hu).le (hr.trans_le hu) (x i) a).trans
    (div_le_div_of_nonneg_left hc hr hu)
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (radialInside_abs_le 0 (hr.trans_le hu).le (hr.trans_le hu) (x i)) (by norm_num : (0:ℝ)≤2)) hd
    (abs_nonneg _) (by norm_num : (0:ℝ)≤2*1)
  simpa only [mul_one,mul_div_assoc] using hh

end
open MeasureTheory Filter
open scoped BigOperators
open CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma rawExteriorCount_nonneg {N : ℕ} (r : ℝ) (x : Configuration N) : 0 ≤ rawExteriorCount r x := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num
lemma rawExteriorCount_le {N : ℕ} (r : ℝ) (x : Configuration N) : rawExteriorCount r x ≤ N := by
  calc _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
       _ = _ := by simp
lemma rawExteriorCount_measurable {N : ℕ} (r : ℝ) : Measurable (rawExteriorCount (N := N) r) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.ite (measurableSet_le measurable_const (continuous_norm.measurable.comp (measurable_pi_apply i))) measurable_const
lemma rawExteriorCount_integrable {N : ℕ} (F : fermionGraph N) (r : ℝ) :
    Integrable (rawExteriorCount r) (graphRawLaw F) :=
  graph_weight_integrable F _ (rawExteriorCount_measurable r) (fun x => by
    rw [Real.norm_of_nonneg (rawExteriorCount_nonneg r x)]; exact rawExteriorCount_le r x)

lemma smoothExteriorWeight_nonneg {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    0 ≤ smoothExteriorWeight hr x := by
  rw [smoothExteriorWeight,oneBodySquareTotal_value]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma smoothExteriorWeight_measurable {N : ℕ} {r : ℝ} (hr : 0 < r) :
    Measurable (smoothExteriorWeight (N := N) hr) :=
  (oneBodySquareTotal (radialOutside 0 hr.le hr)).regular.continuous.measurable
lemma smoothExteriorWeight_bound {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    ‖smoothExteriorWeight hr x‖ ≤ N := by
  exact oneBodySquareTotal_bound_one (radialOutside 0 hr.le hr) (radialOutside_abs_le 0 hr.le hr) x
lemma smoothExteriorWeight_integrable {N : ℕ} {r : ℝ} (hr : 0 < r) (F : fermionGraph N) :
    Integrable (smoothExteriorWeight hr) (graphRawLaw F) :=
  graph_weight_integrable F _ (smoothExteriorWeight_measurable hr) (smoothExteriorWeight_bound hr)

lemma exterior_count_le_smooth_annulus {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    rawExteriorCount r x ≤ smoothExteriorWeight hr x+rawAnnularCount r (2*r) x := by
  unfold rawExteriorCount rawAnnularCount
  rw [smoothExteriorWeight,oneBodySquareTotal_value]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : r ≤ ‖x i‖
  · rw [ite_eq_left hi]
    by_cases hj : ‖x i‖ ≤ 2*r
    · rw [ite_eq_left ⟨hi,hj⟩]; linarith [sq_nonneg ((radialOutside 0 hr.le hr).value (x i))]
    · have he := (radialCut_outer hr.le hr (y := 0) (x := x i) (by simp only [sub_zero]; linarith)).2
      change (radialOutside 0 hr.le hr).value (x i) = 1 at he
      rw [he,one_pow,ite_eq_right (by tauto),add_zero]
  · rw [ite_eq_right hi,ite_eq_right (by tauto),add_zero]
    exact sq_nonneg _
lemma outer_count_le_smooth {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    rawExteriorCount (2*r) x ≤ smoothExteriorWeight hr x := by
  rw [rawExteriorCount,smoothExteriorWeight,oneBodySquareTotal_value]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · have he := (radialCut_outer hr.le hr (y := 0) (x := x i) (by simp only [sub_zero]; linarith)).2
    change (radialOutside 0 hr.le hr).value (x i) = 1 at he
    rw [he,one_pow]
  · exact sq_nonneg _

lemma dyadic_gradient_weight_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Configuration N) :
    (∑ k ∈ Finset.range K, rawGradientWeight (dyadicShell hr k) x) ≤
      (24*(Real.pi*smoothTransitionBound)^2/r^2)*rawExteriorCount r x := by
  unfold rawGradientWeight
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin N, ∑ a : Fin 3,
        (8*(Real.pi*smoothTransitionBound)^2/r^2)*(if r ≤ ‖x i‖ then 1 else 0) := by
      apply Finset.sum_le_sum; intro i _
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum (fun a _ => dyadic_shell_deriv_sum hr K (x i) a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,rawExteriorCount]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma dyadic_gradient_error_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (F : fermionGraph N) :
    (∑ k ∈ Finset.range K, oneBodyGradientError (dyadicShell hr k) F) ≤
      (24*(Real.pi*smoothTransitionBound)^2/r^2)*∫ x, rawExteriorCount r x ∂graphRawLaw F := by
  have hD (k : ℕ) (a : Fin 3) (x : Space) := shellCutoff_deriv_le
    (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr) x a
  have hi (k : ℕ) := rawGradientWeight_integrable (dyadicShell hr k) F (hD k)
  simp_rw [gradientError_eq_integral (dyadicShell hr _) F (hD _)]
  rw [←integral_finsetSum _ (fun k _ => hi k),←integral_const_mul]
  exact integral_mono (integrable_finsetSum _ (fun k _ => hi k))
    ((rawExteriorCount_integrable F r).const_mul _) (dyadic_gradient_weight_sum hr K)

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

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier
  rawFormPair formMass weightedMass oneBodyGradientError corePriceExcess shellMeanField innerScale

lemma actualShellRadius_ge : 16 ≤ actualShellRadius := le_max_left _ _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellResidualControl
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma norm_sub_square_bound {V : Type*} [SeminormedAddCommGroup V] (v w : V) :
    ‖v-w‖^2 ≤ 2*‖v‖^2+2*‖w‖^2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le v w) 2
  nlinarith [sq_nonneg (‖v‖-‖w‖)]

lemma shellGraphConstant_nonneg (N : ℕ) (r : ℝ) : 0 ≤ shellGraphConstant N r := by
  unfold shellGraphConstant; positivity

lemma dyadicShell_sum_graph_bound {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (F : fermionGraph N) :
    ‖(∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).apply F)‖^2 ≤
      shellGraphConstant N r*‖F‖^2 := by
  have hu : r ≤ (2:ℝ)^K*r := le_mul_of_one_le_left hr.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hK := radialInside_square_graph_bound hr hu F
  have h0 := radialInside_square_graph_bound hr (le_rfl : r ≤ r) F
  have hsub := norm_sub_square_bound ((oneBodySquareTotal (dyadicInside hr K)).apply F)
    ((oneBodySquareTotal (dyadicInside hr 0)).apply F)
  change ‖(oneBodySquareTotal (dyadicInside hr K)).apply F‖^2 ≤ _ at hK
  have hz : dyadicInside hr 0 = radialInside 0 hr.le hr := by simp only [dyadicInside,pow_zero,one_mul]
  rw [hz] at hsub
  have hbound : ‖(oneBodySquareTotal (dyadicInside hr K)).apply F-
      (oneBodySquareTotal (dyadicInside hr 0)).apply F‖^2 ≤ shellGraphConstant N r*‖F‖^2 := by
    rw [hz]
    dsimp only [shellGraphConstant]
    linarith only [hK,h0,hsub]
  exact (congrArg (fun H : fermionGraph N => ‖H‖^2) (dyadicShell_graph_sum hr K F)).le.trans hbound

lemma dyadicShell_residual_square {Z r η B : ℝ} {N : ℕ} (hZ : 0 ≤ Z) (hr : 0 < r)
    (hη : 0 ≤ η) (F : fermionGraph N) (hF : (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η)
    (hB : ‖F‖^2 ≤ B) (K : ℕ) :
    (∑ k ∈ Finset.range K, (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,
      sectorExcessOperator Z N F⟫_ℂ).re)^2 ≤ η*(‖sectorExcessOperator Z N‖*shellGraphConstant N r*B) := by
  have hG := (dyadicShell_sum_graph_bound hr K F).trans
    (mul_le_mul_of_nonneg_left hB (shellGraphConstant_nonneg N r))
  have hh := positive_form_residual_bound (sectorExcessOperator Z N)
    (sectorExcessOperator_positive hZ N) F (∑ k ∈ Finset.range K,
      (oneBodySquareTotal (dyadicShell hr k)).apply F) hη hF hG
  exact (congrArg (fun t : ℝ => t^2) (real_inner_sum_left (Finset.range K)
    (fun k => (oneBodySquareTotal (dyadicShell hr k)).apply F) (sectorExcessOperator Z N F))).le.trans hh

lemma dyadicShell_residual_le {Z r η B ε : ℝ} {N : ℕ} (hZ : 0 ≤ Z) (hr : 0 < r)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (F : fermionGraph N) (hF : (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η)
    (hB : ‖F‖^2 ≤ B) (ha : η*(‖sectorExcessOperator Z N‖*shellGraphConstant N r*B) ≤ ε^2) (K : ℕ) :
    (∑ k ∈ Finset.range K, (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,
      sectorExcessOperator Z N F⟫_ℂ).re) ≤ ε := by
  have hh := (dyadicShell_residual_square hZ hr hη F hF hB K).trans ha
  nlinarith only [hh,sq_nonneg ((∑ k ∈ Finset.range K,
    (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,sectorExcessOperator Z N F⟫_ℂ).re)+ε),hε]

end
section
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma multiplier_weight_integrable {N : ℕ} (F : fermionGraph N) (p : FermionMultiplier N) :
    Integrable p.value (graphRawLaw F) := by
  obtain ⟨A,hA⟩ := p.bound
  exact graph_weight_integrable F _ p.regular.continuous.measurable hA
lemma multiplier_weightedMass_eq_integral {N : ℕ} (F : fermionGraph N) (p : FermionMultiplier N) :
    weightedMass F p.value = ∫ x, p.value x ∂graphRawLaw F := by
  obtain ⟨A,hA⟩ := p.bound
  exact weightedMass_eq_integral F _ p.regular.continuous.measurable hA
lemma weightedMass_finite_sum {α : Type*} {N : ℕ} (T : Finset α)
    (p : α → FermionMultiplier N) (F : fermionGraph N) :
    (∑ k ∈ T, weightedMass F (p k).value) = ∫ x, (∑ k ∈ T, (p k).value x) ∂graphRawLaw F := by
  simp_rw [multiplier_weightedMass_eq_integral]
  exact (integral_finsetSum _ (fun k _ => multiplier_weight_integrable F (p k))).symm

lemma smoothExteriorWeight_count_sub {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    smoothExteriorWeight hr x = (N:ℝ)-(oneBodySquareTotal (dyadicInside hr 0)).value x := by
  have hz : dyadicInside hr 0 = radialInside 0 hr.le hr := by simp only [dyadicInside,pow_zero,one_mul]
  rw [smoothExteriorWeight,oneBodySquareTotal_value,hz,oneBodySquareTotal_value]
  have hh (i : Fin N) : (radialOutside 0 hr.le hr).value (x i)^2 =
      1-(radialInside 0 hr.le hr).value (x i)^2 := by
    have hp := radialCut_partition 0 hr.le hr (x i)
    simp only [Fin.sum_univ_two,radialCut,Matrix.cons_val_zero,Matrix.cons_val_one] at hp
    linarith only [hp]
  simp_rw [hh]
  rw [Finset.sum_sub_distrib]; simp

lemma dyadicShell_total_sum_nonneg {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Configuration N) :
    0 ≤ ∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).value x := by
  simp only [oneBodySquareTotal_value]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma dyadicShell_total_sum_bound {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Configuration N) :
    ‖∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).value x‖ ≤ N := by
  rw [Real.norm_of_nonneg (dyadicShell_total_sum_nonneg hr K x),dyadicShell_total_sum]
  have hn : 0 ≤ (oneBodySquareTotal (dyadicInside hr 0)).value x := by
    rw [oneBodySquareTotal_value]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK := (le_abs_self ((oneBodySquareTotal (dyadicInside hr K)).value x)).trans
    (oneBodySquareTotal_bound_one (dyadicInside hr K) (radialInside_abs_le 0 _ _) x)
  linarith only [hn,hK]
lemma dyadicInside_tendsto {r : ℝ} (hr : 0 < r) (x : Space) :
    Tendsto (fun K => (dyadicInside hr K).value x) atTop (nhds 1) := by
  have ht : Tendsto (fun K : ℕ => (2:ℝ)^K*r) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hr
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_atTop.1 ht) ‖x‖] with K hK
  exact (radialCut_inner (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) K) hr).le
    (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) K) hr) (y := 0) (x := x) (by simpa using hK)).1.symm
lemma dyadicShell_total_sum_tendsto {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    Tendsto (fun K => ∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).value x)
      atTop (nhds (smoothExteriorWeight hr x)) := by
  simp_rw [dyadicShell_total_sum,oneBodySquareTotal_value]
  rw [smoothExteriorWeight_count_sub,oneBodySquareTotal_value]
  have hh := tendsto_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (fun i _ => (dyadicInside_tendsto hr (x i)).pow 2)
  simp only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
  exact hh.sub_const _

lemma dyadicShell_mass_sum_tendsto {N : ℕ} {r : ℝ} (hr : 0 < r) (F : fermionGraph N) :
    Tendsto (fun K => ∑ k ∈ Finset.range K, weightedMass F (oneBodySquareTotal (dyadicShell hr k)).value)
      atTop (nhds (∫ x, smoothExteriorWeight hr x ∂graphRawLaw F)) := by
  simp_rw [weightedMass_finite_sum]
  apply tendsto_integral_of_dominated_convergence (fun _ => (N:ℝ))
    (fun K => (Finset.measurable_sum _ (fun k _ => (oneBodySquareTotal (dyadicShell hr k)).regular.continuous.measurable)).aestronglyMeasurable)
    (integrable_const _) (fun K => ae_of_all _ (dyadicShell_total_sum_bound hr K))
    (ae_of_all _ (dyadicShell_total_sum_tendsto hr))

end
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue sectorExcessOperator
  weightedMass oneBodyGradientError graphRawLaw

lemma sum_linear_inequality {α : Type*} (T : Finset α) (a b c : α → ℝ) (t : ℝ)
    (h : ∀ k ∈ T, t*a k ≤ b k+2*c k) :
    t*(∑ k ∈ T, a k) ≤ (∑ k ∈ T, b k)+2*(∑ k ∈ T, c k) := by
  calc _ = ∑ k ∈ T, t*a k := Finset.mul_sum ..
       _ ≤ ∑ k ∈ T, (b k+2*c k) := Finset.sum_le_sum h
       _ = _ := by rw [Finset.sum_add_distrib,Finset.mul_sum]

theorem actual_smooth_exterior_number {Z s r η B ε : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hr : 0 < r)
    (hR : actualShellRadius*s ≤ r)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (F : fermionGraph (N+1))
    (hF : (⟪F,sectorExcessOperator Z (N+1) F⟫_ℂ).re ≤ η)
    (hB : ‖F‖^2 ≤ B)
    (ha : η*(‖sectorExcessOperator Z (N+1)‖*shellGraphConstant (N+1) r*B) ≤ ε^2) :
    (1/s^4)*(∫ x, smoothExteriorWeight hr x ∂graphRawLaw F) ≤
      (24*(Real.pi*smoothTransitionBound)^2/r^2)*
        (∫ x, rawExteriorCount r x ∂graphRawLaw F)+2*ε := by
  have hh (K : ℕ) : (1/s^4)*(∑ k ∈ Finset.range K,
      weightedMass F (oneBodySquareTotal (dyadicShell hr k)).value) ≤
      (24*(Real.pi*smoothTransitionBound)^2/r^2)*
        (∫ x, rawExteriorCount r x ∂graphRawLaw F)+2*ε := by
    have hsum := sum_linear_inequality (Finset.range K)
      (fun k => weightedMass F (oneBodySquareTotal (dyadicShell hr k)).value)
      (fun k => oneBodyGradientError (dyadicShell hr k) F)
      (fun k => (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re)
      (1/s^4) (fun k _ =>
      actual_shell_number hZ hs hs1 (hR.trans (le_mul_of_one_le_left hr.le
        (one_le_pow₀ (by norm_num : (1:ℝ)≤2)))) hN F (dyadicShell hr k)
        (shellCutoff_compact (mul_pos (pow_pos (by norm_num) k) hr))
        (fun y hy => by
          have h := shellCutoff_support (mul_pos (pow_pos (by norm_num) k) hr) y hy
          exact ⟨by linarith [mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr],h.2⟩))
    exact hsum.trans (add_le_add (dyadic_gradient_error_sum hr K F)
      (mul_le_mul_of_nonneg_left (dyadicShell_residual_le hZ hr hη hε F hF hB ha K) (by norm_num)))
  exact le_of_tendsto ((dyadicShell_mass_sum_tendsto hr F).const_mul (1/s^4))
    (Eventually.of_forall hh)

lemma rawAnnularCount_graph_integrable {N : ℕ} (F : fermionGraph N) (a b : ℝ) :
    Integrable (rawAnnularCount a b) (graphRawLaw F) :=
  graph_weight_integrable F _ (rawAnnularCount_measurable a b) (fun x => by
    rw [Real.norm_of_nonneg (rawAnnularCount_nonneg a b x)]; exact rawAnnularCount_le a b x)

theorem actual_exterior_number_absorbed {Z s r η B ε : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hr : 0 < r)
    (hR : actualShellRadius*s ≤ r)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (F : fermionGraph (N+1))
    (hF : (⟪F,sectorExcessOperator Z (N+1) F⟫_ℂ).re ≤ η)
    (hB : ‖F‖^2 ≤ B)
    (ha : η*(‖sectorExcessOperator Z (N+1)‖*shellGraphConstant (N+1) r*B) ≤ ε^2)
    (hab : 2*(24*(Real.pi*smoothTransitionBound)^2/r^2) ≤ 1/s^4) :
    (1/s^4)*(∫ x, rawExteriorCount (2*r) x ∂graphRawLaw F) ≤
      2*(24*(Real.pi*smoothTransitionBound)^2/r^2)*
        (∫ x, rawAnnularCount r (2*r) x ∂graphRawLaw F)+4*ε := by
  have hh := actual_smooth_exterior_number hZ hs hs1 hr hR hN hη hε F hF hB ha
  have hk := integral_mono (rawExteriorCount_integrable F r)
    ((smoothExteriorWeight_integrable hr F).add (rawAnnularCount_graph_integrable F r (2*r)))
    (exterior_count_le_smooth_annulus hr)
  simp only [Pi.add_apply] at hk
  rw [integral_add (smoothExteriorWeight_integrable hr F)
    (rawAnnularCount_graph_integrable F r (2*r))] at hk
  have hout := integral_mono (rawExteriorCount_integrable F (2*r))
    (smoothExteriorWeight_integrable hr F) (outer_count_le_smooth hr)
  have hn : 0 ≤ ∫ x, smoothExteriorWeight hr x ∂graphRawLaw F :=
    integral_nonneg (smoothExteriorWeight_nonneg hr)
  have hc : 0 ≤ 24*(Real.pi*smoothTransitionBound)^2/r^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hk hc
  have hmul' := mul_le_mul_of_nonneg_right hab hn
  have hmul'' := mul_le_mul_of_nonneg_left hout (by positivity : 0 ≤ 1/s^4)
  nlinarith only [hh,hmul,hmul',hmul'']

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExteriorScreenNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

lemma exteriorGradientConstant_nonneg : 0 ≤ exteriorGradientConstant := by unfold exteriorGradientConstant; positivity

lemma actualScreenRadius_ge : actualShellRadius ≤ actualScreenRadius := le_max_left _ _
lemma actualScreenRadius_ge16 : 16 ≤ actualScreenRadius := actualShellRadius_ge.trans actualScreenRadius_ge
lemma actualScreenRadius_pos : 0 < actualScreenRadius := lt_of_lt_of_le (by norm_num) actualScreenRadius_ge16
lemma actualScreenRadius_square : 2*exteriorGradientConstant ≤ actualScreenRadius^2 := by
  have hh := le_max_right actualShellRadius (Real.sqrt (2*exteriorGradientConstant)+1)
  change Real.sqrt (2*exteriorGradientConstant)+1 ≤ actualScreenRadius at hh
  have hn := Real.sqrt_nonneg (2*exteriorGradientConstant)
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) exteriorGradientConstant_nonneg)
  nlinarith only [hh,hn,hs,sq_nonneg (actualScreenRadius-Real.sqrt (2*exteriorGradientConstant))]

lemma exterior_price_gradient_absorb {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    2*(exteriorGradientConstant/(actualScreenRadius*s)^2) ≤ 1/s^4 := by
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos actualScreenRadius_pos hs)) (pow_pos hs 4)).2
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le hs1 (by omega : 2 ≤ 4))
    (mul_nonneg (by norm_num : (0:ℝ)≤2) exteriorGradientConstant_nonneg)
  have hb := mul_le_mul_of_nonneg_right actualScreenRadius_square (sq_nonneg s)
  nlinarith only [hh,hb]

lemma annularOffsetMass_one_small_two {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    annularOffsetMass 1 r ≤ 2/r^3 := by
  have hi : 1 ≤ 1/r^3 := (le_div_iff₀ (pow_pos hr 3)).2 (by simpa using pow_le_one₀ hr.le hr1 (n := 3))
  have hs : Real.sqrt r ≤ 1 := by simpa using Real.sqrt_le_sqrt hr1
  unfold annularOffsetMass
  rw [one_mul,max_eq_left hi]
  have he : 2/r^3 = 2*(1/r^3) := by ring
  rw [he]
  linarith only [hi,hs]

lemma exterior_bound_scale {R L C s v : ℝ} (hR : 0 < R) (hs : 0 < s) (hs1 : s ≤ 1)
    (hv : (1/s^4)*v ≤ 2*(L/(R*s)^2)*(C*(2/(R*s)^3))+4) :
    v ≤ (4*L*C/R^5+4)/s := by
  have hh := mul_le_mul_of_nonneg_left hv (pow_nonneg hs.le 4)
  have he : s^4*((1/s^4)*v) = v := by field_simp
  have he' : s^4*(2*(L/(R*s)^2)*(C*(2/(R*s)^3))+4) = (4*L*C/R^5)/s+4*s^4 := by field_simp; ring
  rw [he,he'] at hh
  have hpow : s^4 ≤ 1/s := (le_div_iff₀ hs).2 (by simpa [←pow_succ] using pow_le_one₀ hs.le hs1 (n := 5))
  calc v ≤ (4*L*C/R^5)/s+4*s^4 := hh
       _ ≤ (4*L*C/R^5)/s+4*(1/s) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤4))
       _ = _ := by ring

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator graphRawLaw

lemma actualScreenConstant_nonneg : 0 ≤ actualScreenConstant := by
  have hC := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).1
  have hn := exteriorGradientConstant_nonneg
  have hr := actualScreenRadius_pos
  unfold actualScreenConstant
  positivity

lemma exists_own_state_exterior_number_succ {Z s r : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hRs : actualScreenRadius*s ≤ 1) (hr : 0 < r)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (K : ℕ) (p₀ : Fin (K+1) → ℝ) (h₀ : ∀ j, 0 < p₀ j) :
    ∃ F : fermionGraph (N+1), OwnProbabilityTailTiltState Z (1/s^4) r K p₀ 1 F ∧
      (∫ x, rawExteriorCount (2*(actualScreenRadius*s)) x ∂graphRawLaw F) ≤ actualScreenConstant/s := by
  have hv : 0 < actualScreenRadius*s := mul_pos actualScreenRadius_pos hs
  obtain ⟨F,η,hF,hη,hsmall,hres⟩ := exists_own_state_shell_residual hZ hr hv hN K p₀ h₀
  refine ⟨F,hF,?_⟩
  have hbound := actual_exterior_number_absorbed hZ hs hs1 hv
    (mul_le_mul_of_nonneg_right actualScreenRadius_ge hs.le) hN hη zero_le_one F hsmall.1 hsmall.2 hres
    (exterior_price_gradient_absorb hs hs1)
  have hann := actual_annular_first_bound hZ (by positivity : 0 < 1/s^4) zero_le_one hv hN F hF.1 hF.2.1
  have hC := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).1
  have hmoment := hann.trans (mul_le_mul_of_nonneg_left (annularOffsetMass_one_small_two hv hRs) (le_trans zero_le_one hC))
  apply exterior_bound_scale actualScreenRadius_pos hs hs1
  apply hbound.trans
  exact add_le_add (mul_le_mul_of_nonneg_left hmoment (by
    change 0 ≤ 2*(exteriorGradientConstant/(actualScreenRadius*s)^2)
    exact mul_nonneg (by norm_num) (div_nonneg exteriorGradientConstant_nonneg (sq_nonneg _)))) (by norm_num)

lemma exists_own_state_exterior_number_oai {Z s r : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hRs : actualScreenRadius*s ≤ 1) (hr : 0 < r)
    (hN : PriceMinimizes (energy Z) (1/s^4) N)
    (K : ℕ) (p₀ : Fin (K+1) → ℝ) (h₀ : ∀ j, 0 < p₀ j) :
    ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z (1/s^4) r K p₀ 1 F ∧
      (∫ x, rawExteriorCount (2*(actualScreenRadius*s)) x ∂graphRawLaw F) ≤ actualScreenConstant/s := by
  cases N with
  | zero =>
    obtain ⟨F,hF⟩ := exists_actual_own_probability_tail_tilt_state hZ hr hN K p₀ h₀ zero_lt_one
    refine ⟨F,hF,?_⟩
    have hc (x : Configuration 0) : rawExteriorCount (2*(actualScreenRadius*s)) x = 0 := by simp [rawExteriorCount]
    simp_rw [hc,integral_zero]
    exact div_nonneg actualScreenConstant_nonneg hs.le
  | succ N => exact exists_own_state_exterior_number_succ hZ hs hs1 hRs hr hN K p₀ h₀
end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.exists_own_state_exterior_number_oai := @OAI.CoulombAtom.exists_own_state_exterior_number_oai
