-- Prove2me | solution 1 for OAI.CoulombAtom.quantum_binding_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:34.807475+00:00
-- url     : https://prove2.me/submissions/ca6b6240-3ecd-4c9d-ae7c-fa9ba44f231c

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C008
import Definitions.Def_OAIQ071C009
import Theorems.Thm_OAI_CoulombAtom_binding_form_lower

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

lemma l2_inner_re (f g : Lp ℂ 2 μ) :
    (⟪f, g⟫_ℂ).re = ∫ x, (⟪f x, g x⟫_ℂ).re ∂μ := by
  rw [L2.inner_def]
  exact (integral_re (L2.integrable_inner (𝕜 := ℂ) f g)).symm

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

lemma FermionMultiplier.apply_value {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) :
    (graphComponent s none (p.apply F) : Configuration N → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ) * graphComponent s none F x :=
  p.toSmoothMultiplier.apply_value (F.val s)

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

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


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

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

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

end

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


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace


open MeasureTheory Filter
open scoped Topology BigOperators

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

lemma FermionMultiplier.value_weighted_pairing {N : ℕ} (F : fermionGraph N) (p : FermionMultiplier N) :
    (⟪fermionGraphValue N (p.apply F), fermionGraphValue N F⟫_ℂ).re = weightedMass F p.value := by
  rw [graphValue_pairing]
  apply Finset.sum_congr rfl; intro s _
  exact l2_real_weight_pairing p.value _ _ (p.apply_value F s)

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

lemma quantum_binding_residual_oai {Z lam : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
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

theorem solution : type_of% @OAI.CoulombAtom.quantum_binding_residual_oai := @OAI.CoulombAtom.quantum_binding_residual_oai
