-- Prove2me | solution 1 for OAI.HardSphere.spatial_spectral_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:37:07.524993+00:00
-- url     : https://prove2.me/submissions/61497a23-befa-4d21-958d-316dd6b454c7

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoordinateLine
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

open scoped ComplexConjugate

lemma coordDerivative_conj {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (p : Direction N) :
    coordDerivative N L (fun X ↦ conj (f X)) p = fun X ↦ conj (coordDerivative N L f p X) := by
  funext X
  unfold coordDerivative
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (representative N L X)
    (hf _).hasFDerivAt
  exact congrArg (fun A : LiftedConfiguration N →L[ℝ] ℂ ↦
    A (Pi.single p.1 (Pi.single p.2 1))) h.fderiv

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Energy
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

omit [InnerProductSpace ℂ H] in
lemma energy_nonneg (u : H × (J → H)) : 0 ≤ energy u :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma energy_smul (c : ℂ) (u : H × (J → H)) :
    energy (c • u) = ‖c‖ ^ 2 * energy u := by
  simp [energy, norm_smul, mul_pow, Finset.mul_sum]

theorem rayleigh (M : Submodule ℂ (H × (J → H))) (u : H × (J → H))
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  by_cases hz : ‖v.1‖ = 0
  · simpa [hz] using energy_nonneg v
  · let c : ℂ := ((‖v.1‖ : ℂ))⁻¹
    have hc : ‖c‖ = ‖v.1‖⁻¹ := by simp [c, Complex.norm_real]
    have hv' : ‖(c • v).1‖ = 1 := by
      simp only [Prod.smul_fst, norm_smul, hc]
      exact inv_mul_cancel₀ hz
    have h := hmin (c • v) (M.smul_mem c hv) hv'
    rw [energy_smul, hc] at h
    calc
      energy u * ‖v.1‖ ^ 2 ≤ (‖v.1‖⁻¹ ^ 2 * energy v) * ‖v.1‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = energy v := by field_simp

end HardSphere.Variational

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Basic
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere

lemma bosonic_iff_pullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic ψ ↔ ∀ σ, permutationPullback σ ψ = ψ := by
  have hae (σ : Equiv.Perm (Fin N)) :
      (permutationPullback σ ψ : Configuration N L → ℂ) =ᵐ[volume]
        fun X ↦ ψ (permuteConfiguration σ X) :=
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_permute σ)
  constructor
  · intro h σ
    exact Lp.ext ((hae σ).trans (h σ))
  · intro h σ
    have hh := hae σ
    rw [h σ] at hh
    exact hh.symm

section

attribute [local instance] scalarL2_normedAddCommGroup scalarL2_module

@[simp] lemma mem_bosonicSubmodule {N : ℕ} {L : Length} {ψ : ScalarL2 N L} :
    ψ ∈ bosonicSubmodule N L ↔ bosonic ψ := by
  simp only [bosonicSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact (bosonic_iff_pullback ψ).symm

end

@[simp] lemma mem_groundFormSubmodule {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L} :
    u ∈ groundFormSubmodule N L a ↔ u ∈ dirichletDomain N L a ∧ bosonic u.1 := by
  simp [groundFormSubmodule]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FirstVariation
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
namespace HardSphere

theorem IsGroundVector.rayleigh {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) (hb : bosonic v.1) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  exact Variational.rayleigh (groundFormSubmodule N L a) u
    (fun w hw hn ↦ hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn) v
    (mem_groundFormSubmodule.mpr ⟨hv, hb⟩)

lemma SmoothTest.jet_permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) :
    (f.permute σ).jet = permutationJet σ f.jet := by
  apply Prod.ext
  · apply Lp.ext
    exact (MemLp.coeFn_toLp (f.permute σ).memLp).trans
      ((Lp.coeFn_compMeasurePreserving f.jet.1 (measurePreserving_permute σ)).trans
        ((measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
          (MemLp.coeFn_toLp f.memLp))).symm
  · funext p
    apply Lp.ext
    have h := (measurePreserving_permute (L := L) σ).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (f.partial_memLp (σ.symm p.1, p.2)))
    refine (MemLp.coeFn_toLp ((f.permute σ).partial_memLp p)).trans ?_
    change coordDerivative N L (f.toFun ∘ permuteConfiguration σ) p =ᵐ[volume] _
    rw [coordDerivative_permute]
    exact ((Lp.coeFn_compMeasurePreserving _ (measurePreserving_permute σ)).trans h).symm

lemma energy_permutationJet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (u : Jet N L) : energy (permutationJet σ u) = energy u := by
  change (∑ p : Direction N, ‖Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (u.2 (σ.symm p.1, p.2))‖ ^ 2) = _
  simp only [Lp.norm_compMeasurePreserving]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ ‖u.2 p‖ ^ 2)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ConfigurationPath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace L2Multiplier
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma coe_clm (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    clm f hf u =ᵐ[μ] fun x ↦ f x * u x := coe_apply f hf u

end L2Multiplier

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqIntegral
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace IndicatorStrong
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re]
  · congr 1
    ext x
    simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  · exact L2.integrable_inner f f

end IndicatorStrong

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Slice
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Filter Set

lemma smoothTest_norm_sq {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) :
    ‖f.jet.1‖^2=∫ X : Configuration n L, ‖f.toFun X‖^2 := by
  rw [IndicatorStrong.norm_sq_integral]
  exact integral_congr_ae ((MemLp.coeFn_toLp f.memLp).fun_comp (fun z : ℂ ↦ ‖z‖^2))

lemma smoothTest_partial_norm_sq {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (p : Direction n) :
    ‖f.jet.2 p‖^2=∫ X : Configuration n L, ‖coordDerivative n L f.toFun p X‖^2 := by
  rw [IndicatorStrong.norm_sq_integral]
  exact integral_congr_ae ((MemLp.coeFn_toLp (f.partial_memLp p)).fun_comp (fun z : ℂ ↦ ‖z‖^2))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_IntegrableCompInsertNth
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Filter Set

lemma integrable_comp_insertNth {n : ℕ} {L : Length} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Configuration (n+1) L → E}
    (hF : Integrable F volume) (j : Fin (n+1)) :
    Integrable (fun z : Torus L × Configuration n L ↦ F (j.insertNth z.1 z.2)) (volume.prod volume) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) j
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) j).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Function.comp_def,MeasureTheory.Measure.volume_eq_prod] using hi

lemma integral_configuration_insertNth {n : ℕ} {L : Length} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Configuration (n+1) L → E)
    (hF : Integrable F volume) (j : Fin (n+1)) :
    ∫ X, F X = ∫ x : Torus L, ∫ Y : Configuration n L, F (j.insertNth x Y) := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) j).symm
  rw [← he.integral_comp' F]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk]
  exact integral_prod _ (integrable_comp_insertNth hF j)

lemma SmoothTest.slice_norm_sq_integrable {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) :
    Integrable (fun x : Torus L ↦ ‖(f.slice j x).jet.1‖^2) volume := by
  simp only [smoothTest_norm_sq,SmoothTest.slice]
  exact (integrable_comp_insertNth (f.memLp.integrable_norm_pow (by decide : (2:ℕ)≠0)) j).integral_prod_left

lemma SmoothTest.integral_slice_norm_sq {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) :
    (∫ x : Torus L, ‖(f.slice j x).jet.1‖^2)=‖f.jet.1‖^2 := by
  simp only [smoothTest_norm_sq,SmoothTest.slice]
  exact (integral_configuration_insertNth _ (f.memLp.integrable_norm_pow (by decide : (2:ℕ)≠0)) j).symm

lemma SmoothTest.slice_partial_integrable {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) (p : Direction n) :
    Integrable (fun x : Torus L ↦ ‖(f.slice j x).jet.2 p‖^2) volume := by
  simp only [smoothTest_partial_norm_sq,SmoothTest.slice,coordDerivative_slice]
  exact (integrable_comp_insertNth ((f.partial_memLp (j.succAbove p.1,p.2)).integrable_norm_pow
    (by decide : (2:ℕ)≠0)) j).integral_prod_left

lemma SmoothTest.integral_slice_partial {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) (p : Direction n) :
    (∫ x : Torus L, ‖(f.slice j x).jet.2 p‖^2)=‖f.jet.2 (j.succAbove p.1,p.2)‖^2 := by
  simp only [smoothTest_partial_norm_sq,SmoothTest.slice,coordDerivative_slice]
  exact (integral_configuration_insertNth _ ((f.partial_memLp (j.succAbove p.1,p.2)).integrable_norm_pow
    (by decide : (2:ℕ)≠0)) j).symm

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Failure
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace SineProduct

lemma one_failure_le {I : Type*} [DecidableEq I] (s : Finset I) (h : I → ℝ)
    (h0 : ∀ i∈s, 0≤h i) (h1 : ∀ i∈s, h i≤1) :
    (∑ i∈s, (1-h i)*∏ j∈s.erase i, h j)+(∏ i∈s, h i)≤1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hp : ∀ i∈s, 0≤h i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have hq : ∀ i∈s, h i≤1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
    have hh := ih hp hq
    have hn : 0≤∑ i∈s, (1-h i)*∏ j∈s.erase i,h j := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (sub_nonneg.mpr (hq i hi))
        (Finset.prod_nonneg fun j hj ↦ hp j (Finset.mem_of_mem_erase hj))
    have he : (∑ i∈insert a s, (1-h i)*∏ j∈(insert a s).erase i, h j)=
        (1-h a)*(∏ j∈s,h j)+h a*(∑ i∈s, (1-h i)*∏ j∈s.erase i,h j) := by
      rw [Finset.sum_insert ha,Finset.erase_insert ha,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i≠a := fun he ↦ ha (he ▸ hi)
      rw [Finset.erase_insert_of_ne hia.symm,Finset.prod_insert (by simp [ha])]
      ring
    rw [he,Finset.prod_insert ha]
    nlinarith [mul_le_mul_of_nonneg_right (h1 a (Finset.mem_insert_self a s)) hn]

lemma coefficients_sq_le {I : Type*} [DecidableEq I] (s : Finset I) (θ : I → ℝ) :
    ∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))^2≤1 := by
  have h := one_failure_le s (fun i ↦ Real.sin (θ i)^2) (fun _ _ ↦ sq_nonneg _)
    (fun i _ ↦ by nlinarith [Real.sin_sq_add_cos_sq (θ i),sq_nonneg (Real.cos (θ i))])
  have he : (∑ i∈s, (1-Real.sin (θ i)^2)*∏ j∈s.erase i,Real.sin (θ j)^2)=
      ∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow,← Finset.prod_pow]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq (θ i)]
  rw [he] at h
  exact le_trans (le_add_of_nonneg_right (Finset.prod_nonneg fun _ _ ↦ sq_nonneg _)) h

lemma contraction_sq {I : Type*} [DecidableEq I] (s : Finset I) (θ d : I → ℝ) :
    (∑ i∈s, (Real.cos (θ i)*∏ j∈s.erase i,Real.sin (θ j))*d i)^2≤∑ i∈s,d i^2 := by
  exact (Finset.sum_mul_sq_le_sq_mul_sq s _ d).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (coefficients_sq_le s θ)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))

lemma fderiv_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [DecidableEq I] (s : Finset I) (θ : I → E → ℝ) (x v : E)
    (hd : ∀ i∈s, DifferentiableAt ℝ (θ i) x) :
    (fderiv ℝ (fun y ↦ ∏ i∈s,Real.sin (θ i y)) x v)^2≤
      ∑ i∈s,(fderiv ℝ (θ i) x v)^2 := by
  have hp := HasFDerivAt.finsetProd (u := s) (fun i hi ↦ (hd i hi).hasFDerivAt.sin)
  rw [hp.fderiv,sum_apply]
  simp only [smul_apply,smul_eq_mul]
  convert contraction_sq s (fun i ↦ θ i x) (fun i ↦ fderiv ℝ (θ i) x v) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SineProduct

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ChordLift
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff

variable (L : ℝ) [hL : Fact (0<L)]

lemma chord_continuous : Continuous (chord L) := by
  apply (QuotientAddGroup.isOpenMap_coe.isQuotientMap (AddCircle.continuous_mk' L) QuotientAddGroup.mk_surjective).continuous_iff.mpr
  simpa only [Function.comp_def,chord_coe] using (chordLift_smooth L).continuous

lemma chordLift_derivative (x : ℝ) : HasDerivAt (chordLift L)
    (2*(L/Real.pi*Real.sin (Real.pi/L*x))*Real.cos (Real.pi/L*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (Real.pi/L)).sin.const_mul (L/Real.pi)).pow 2
  apply h.congr_deriv
  dsimp
  field_simp [ne_of_gt hL.out, Real.pi_ne_zero]

lemma chordLift_derivative_sq_le (x : ℝ) :
    (deriv (chordLift L) x)^2 ≤ 4*chordLift L x := by
  rw [(chordLift_derivative L x).deriv]
  have hc : Real.cos (Real.pi/L*x)^2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/L*x),sq_nonneg (Real.sin (Real.pi/L*x))]
  simpa only [chordLift] using (show
    (2*(L/Real.pi*Real.sin (Real.pi/L*x))*Real.cos (Real.pi/L*x))^2≤
      4*(L/Real.pi*Real.sin (Real.pi/L*x))^2 by
        nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (2*(L/Real.pi*Real.sin (Real.pi/L*x))))])

lemma centered_representative (x : AddCircle L) :
    ∃ t : ℝ, (t : AddCircle L)=x ∧ |t|≤L/2 ∧ ‖x‖=|t| := by
  let t := (AddCircle.equivIco L (-L/2) x).val
  have ht : (t : AddCircle L)=x := AddCircle.coe_equivIco
  have hb : |t|≤L/2 := by
    apply abs_le.mpr
    constructor
    · simpa only [neg_div] using (AddCircle.equivIco L (-L/2) x).property.1
    · have hu := (AddCircle.equivIco L (-L/2) x).property.2
      dsimp [t]
      linarith
  exact ⟨t,ht,hb,ht ▸ ((AddCircle.norm_coe_eq_abs_iff L (ne_of_gt hL.out)).mpr
    (by simpa only [abs_of_pos hL.out] using hb))⟩

lemma chord_nonneg (x : AddCircle L) : 0 ≤ chord L x := by
  obtain ⟨t,rfl,_,_⟩ := centered_representative L x
  exact sq_nonneg _

lemma chord_le_norm_sq (x : AddCircle L) : chord L x≤‖x‖^2 := by
  obtain ⟨t,rfl,ht,hx⟩ := centered_representative L x
  rw [chord_coe,hx]
  have h : |L/Real.pi*Real.sin (Real.pi/L*t)|≤|t| := by
    rw [abs_mul,abs_of_pos (div_pos hL.out Real.pi_pos)]
    calc
      L/Real.pi*|Real.sin (Real.pi/L*t)|≤L/Real.pi*|Real.pi/L*t| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (le_of_lt (div_pos hL.out Real.pi_pos))
      _ = |t| := by
        rw [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)]
        field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  dsimp [chordLift]
  calc
    _ = |L/Real.pi*Real.sin (Real.pi/L*t)|^2 := (sq_abs _).symm
    _ ≤ |t|^2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h

lemma norm_sq_le_chord (x : AddCircle L) : ‖x‖^2≤(Real.pi/2)^2*chord L x := by
  obtain ⟨t,rfl,ht,hx⟩ := centered_representative L x
  have ha : |Real.pi/L*t|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)]
    calc
      Real.pi/L*|t|≤Real.pi/L*(L/2) := mul_le_mul_of_nonneg_left ht (le_of_lt (div_pos Real.pi_pos hL.out))
      _ = Real.pi/2 := by field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
  have hb : |t|≤Real.pi/2*|L/Real.pi*Real.sin (Real.pi/L*t)| := by
    have h := mul_le_mul_of_nonneg_left (Real.mul_abs_le_abs_sin ha)
      (show 0≤L/2 from (div_pos hL.out (by norm_num)).le)
    simp only [abs_mul,abs_of_pos (div_pos Real.pi_pos hL.out)] at h
    rw [abs_mul,abs_of_pos (div_pos hL.out Real.pi_pos)]
    have he : L/2*(2/Real.pi*(Real.pi/L*|t|))=|t| := by
      field_simp [ne_of_gt hL.out, Real.pi_ne_zero]
    rw [he] at h
    convert h using 1 <;> first | rfl | (field_simp [ne_of_gt hL.out, Real.pi_ne_zero])
  rw [chord_coe,hx]
  dsimp [chordLift]
  calc
    _ ≤ (Real.pi/2*|L/Real.pi*Real.sin (Real.pi/L*t)|)^2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).mpr hb
    _ = _ := by rw [mul_pow,sq_abs]

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_TransitionDerivative
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff

lemma transition_derivative (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt

lemma transition_deriv_eq_zero {x : ℝ} (hx : x∉Icc (0:ℝ) 1) :
    deriv Real.smoothTransition x=0 := by
  have he : (Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ (Real.smoothTransition x)) := by
    rcases not_and_or.mp hx with h | h
    · have hx : x<0 := lt_of_not_ge h
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      rw [Real.smoothTransition.zero_of_nonpos hy.le,Real.smoothTransition.zero_of_nonpos hx.le]
    · have hx : 1<x := lt_of_not_ge h
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      rw [Real.smoothTransition.one_of_one_le hy.le,Real.smoothTransition.one_of_one_le hx.le]
  exact ((hasDerivAt_const x (Real.smoothTransition x)).congr_of_eventuallyEq he).deriv

lemma exists_transition_bound : ∃ M : ℝ, 0<M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x|≤M := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)).continuousOn
      (s := Icc (0:ℝ) 1)
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x ↦ ?_⟩
  by_cases hx : x∈Icc (0:ℝ) 1
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [transition_deriv_eq_zero hx,abs_zero]
    exact (zero_le_one : (0:ℝ)≤1).trans (le_max_right _ _)

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_ThreeTorus
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

omit hL in
lemma box_measurable (R : ℝ) (x : ThreeTorus L) : MeasurableSet (box L R x) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_closedBall)

lemma box_volume_le {R : ℝ} (hR : 0≤R) (x : ThreeTorus L) :
    volume.real (box L R x)≤(2*R)^3 := by
  have he : volume (box L R x)=ENNReal.ofReal (min L (2*R))^3 := by
    rw [volume_pi,box,Measure.pi_pi]
    simp_rw [AddCircle.volume_closedBall]
    simp
  rw [measureReal_def,he,ENNReal.toReal_pow,ENNReal.toReal_ofReal
    (le_min hL.out.le (mul_nonneg (by norm_num) hR))]
  exact pow_le_pow_left₀ (le_min hL.out.le (mul_nonneg (by norm_num) hR)) (min_le_right _ _) 3

lemma pairQ_continuous : Continuous (fun p : ThreeTorus L × ThreeTorus L ↦ pairQ L p.1 p.2) := by
  unfold pairQ
  apply continuous_finsetSum
  intro j _
  exact (chord_continuous L).comp (by fun_prop)

lemma pairQ_le (y x : ThreeTorus L) : pairQ L y x≤∑ j : Fin 3,dist (y j) (x j)^2 := by
  apply Finset.sum_le_sum
  intro j _
  simpa only [dist_eq_norm] using chord_le_norm_sq L (y j-x j)

lemma not_mem_box_pairQ {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L}
    (hx : y∉box L (Real.pi*r) x) : 4*r^2<pairQ L y x := by
  obtain ⟨j,hj⟩ : ∃ j, Real.pi*r<dist (y j) (x j) := by
    by_contra! hn
    exact hx (by simpa only [box,Set.mem_univ_pi,Metric.mem_closedBall] using hn)
  have hq := norm_sq_le_chord L (y j-x j)
  have hs : chord L (y j-x j)≤pairQ L y x :=
    Finset.single_le_sum (fun i _ ↦ chord_nonneg L (y i-x i)) (Finset.mem_univ j)
  rw [← dist_eq_norm] at hq
  have hd2 : (Real.pi*r)^2<dist (y j) (x j)^2 :=
    (sq_lt_sq₀ (mul_nonneg Real.pi_pos.le hr.le) dist_nonneg).mpr hj
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.pi/2)),sq_pos_of_pos Real.pi_pos]

lemma angle_zero {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L} (hq : pairQ L y x≤2*r^2) :
    angle L r y x=0 := by
  unfold angle
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) (by positivity)),mul_zero]

lemma angle_one {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L} (hq : 4*r^2≤pairQ L y x) :
    angle L r y x=Real.pi/2 := by
  unfold angle
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity)).mpr (by nlinarith)),mul_one]

lemma angle_one_outside {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L}
    (hx : y∉box L (Real.pi*r) x) : angle L r y x=Real.pi/2 :=
  angle_one L hr (not_mem_box_pairQ L hr hx).le

omit hL in
lemma angleLift_derivative (r : ℝ) (z : Fin 3 → ℝ → ℝ)
    (d : Fin 3 → ℝ) (t : ℝ) (hd : ∀ j, HasDerivAt (z j) (d j) t) :
    HasDerivAt (fun s ↦ angleLift L r (fun j ↦ z j s))
      (∑ j : Fin 3, anglePartial L r (fun k ↦ z k t) j*d j) t := by
  have hc j := ((chordLift_smooth L).differentiable (by simp) (z j t)).hasDerivAt.comp t (hd j)
  have hq := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3))) (fun j _ ↦ hc j)
  have h := ((transition_derivative ((qLift L (fun j ↦ z j t)-2*r^2)/(2*r^2))).comp t
    ((hq.sub_const (2*r^2)).div_const (2*r^2))).const_mul (Real.pi/2)
  apply h.congr_deriv
  dsimp [anglePartial,angleFactor]
  calc
    _ = (Real.pi/(4*r^2)*deriv Real.smoothTransition ((qLift L (fun j ↦ z j t)-2*r^2)/(2*r^2)))*
        ∑ j : Fin 3, deriv (chordLift L) (z j t)*d j := by ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

omit hL in
lemma chordLift_le_qLift (z : Fin 3 → ℝ) (j : Fin 3) : chordLift L (z j)≤qLift L z :=
  Finset.single_le_sum (fun k _ ↦ sq_nonneg (L/Real.pi*Real.sin (Real.pi/L*z k))) (Finset.mem_univ j)

omit hL in
lemma angleFactor_eq_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc (2*r^2) (4*r^2)) : angleFactor L r z=0 := by
  have ht : (qLift L z-2*r^2)/(2*r^2)∉Icc (0:ℝ) 1 := by
    intro hc
    apply hz
    have h0 := (le_div_iff₀ (show 0<2*r^2 by positivity)).mp hc.1
    have h1 := (div_le_iff₀ (show 0<2*r^2 by positivity)).mp hc.2
    constructor <;> nlinarith
  simp only [angleFactor,transition_deriv_eq_zero ht,mul_zero]

omit hL in
lemma anglePartial_eq_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc (2*r^2) (4*r^2)) (j : Fin 3) : anglePartial L r z j=0 := by
  rw [anglePartial,angleFactor_eq_zero L hr hz,zero_mul]

lemma anglePartial_sq_le {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (z : Fin 3 → ℝ) (j : Fin 3) :
    anglePartial L r z j^2 ≤ Real.pi^2*M^2/r^2 := by
  by_cases hz : qLift L z∈Icc (2*r^2) (4*r^2)
  · have hc : (deriv (chordLift L) (z j))^2≤16*r^2 := by
      have hs := chordLift_le_qLift L z j
      have hd := chordLift_derivative_sq_le L (z j)
      nlinarith [hz.2]
    have ht : (deriv Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2)))^2≤M^2 := by
      rw [← sq_abs (deriv Real.smoothTransition _)]
      exact (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb _)
    calc
      _ = (Real.pi/(4*r^2))^2*((deriv Real.smoothTransition ((qLift L z-2*r^2)/(2*r^2)))^2*
          (deriv (chordLift L) (z j))^2) := by dsimp [anglePartial,angleFactor]; ring
      _ ≤ (Real.pi/(4*r^2))^2*(M^2*(16*r^2)) := by gcongr
      _ = _ := by field_simp [hr.ne']; ring
  · rw [anglePartial_eq_zero L hr hz j,zero_pow (by norm_num)]
    positivity

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothMultiplier
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma SmoothTest.jet_multiply {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) (g : SmoothTest N L a) :
    (g.multiply f).jet = f.onJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (g.multiply f).memLp, MemLp.coeFn_toLp g.memLp,
      L2Multiplier.coe_clm f.toFun f.memLp_top g.jet.1] with X h1 h2 h3
    change _ = (f.onScalar g.jet.1) X
    exact h1.trans (by simpa only [SmoothTest.multiply, Pi.mul_apply, SmoothTest.jet,
      SmoothMultiplier.onScalar, h2] using h3.symm)
  · funext p
    apply Lp.ext
    have hder := coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp)) p
    filter_upwards [MemLp.coeFn_toLp ((g.multiply f).partial_memLp p),
      MemLp.coeFn_toLp g.memLp, MemLp.coeFn_toLp (g.partial_memLp p),
      L2Multiplier.coe_clm f.toFun f.memLp_top (g.jet.2 p),
      L2Multiplier.coe_clm _ (f.partial_memLp_top p) g.jet.1,
      Lp.coeFn_add (f.onScalar (g.jet.2 p))
        (L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1)] with X h1 h2 h3 h4 h5 h6
    change _ = (f.onScalar (g.jet.2 p) + L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1) X
    rw [h6, Pi.add_apply, SmoothMultiplier.onScalar, h4, h5]
    simp only [SmoothTest.jet]
    rw [h1]
    change coordDerivative N L (f.toFun * g.toFun) p X = _
    rw [hder]
    simp only [Pi.add_apply, Pi.mul_apply, h2, h3]
    ring

lemma SmoothMultiplier.onJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    f.onJet u ∈ dirichletDomain N L a := by
  apply map_mem_closure f.onJet.continuous hu
  rintro _ ⟨g, rfl⟩
  exact ⟨g.multiply f, g.jet_multiply f⟩

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoordinateLineConsSucc
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma coordinateLine_cons_succ {n : ℕ} {L : Length} (x : Torus L)
    (Y : Configuration n L) (i : Fin n) (j : Fin 3) (t : AddCircle L.val) :
    coordinateLine (Fin.cons x Y) (i.succ,j) t=Fin.cons x (coordinateLine Y (i,j) t) := by
  funext k q
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp [coordinateLine]
  · by_cases h : k=i
    · subst k; simp [coordinateLine]
    · simp [coordinateLine,Pi.single_eq_of_ne h,Pi.single_eq_of_ne (fun e ↦ h (Fin.succ_injective _ e))]

lemma SmoothMultiplier.hasDerivAt_fiberIntegral {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (Y : Configuration n L) (i : Fin n) (j : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ ∫ x : Torus L,
      f.toFun (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val))))
      (∫ x : Torus L, coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)) 0 := by
  let F : ℝ → Torus L → ℂ := fun t x ↦
    f.toFun (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val)))
  let D : ℝ → Torus L → ℂ := fun t x ↦
    coordDerivative (n+1) L f.toFun (i.succ,j)
      (Fin.cons x (coordinateLine Y (i,j) (t : AddCircle L.val)))
  have cF (t) : Continuous (F t) :=
    (continuous_of_continuous_lift f.smooth.continuous).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ coordinateLine Y (i,j) (t : AddCircle L.val))))
  have cD (t) : Continuous (D t) :=
    (continuous_coordDerivative f.smooth (i.succ,j)).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ coordinateLine Y (i,j) (t : AddCircle L.val))))
  let d : C(Configuration (n+1) L,ℂ) :=
    ⟨_,continuous_coordDerivative f.smooth (i.succ,j)⟩
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (μ := (volume : Measure (Torus L))) (s := Set.univ) (x₀ := 0)
    (bound := fun _ ↦ ‖d‖) univ_mem
    (Eventually.of_forall fun t ↦ (cF t).aestronglyMeasurable)
    ((cF 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (cD 0).aestronglyMeasurable
    (Eventually.of_forall fun x t _ ↦ d.norm_coe_le_norm _)
    (integrable_const _) (Eventually.of_forall fun x t _ ↦ by
      have hh := hasDerivAt_coordinateLine (f.smooth.differentiable (by simp))
        (Fin.cons x Y) (i.succ,j) t
      simpa only [coordinateLine_cons_succ] using hh)
  simpa only [F,D,Complex.ofReal_zero,AddCircle.coe_zero,coordinateLine,Pi.single_zero,add_zero] using h.2

lemma SmoothMultiplier.insertion_orthogonal {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (i : Fin n) (j : Fin 3) (Y : Configuration n L) :
    ∫ x : Torus L, conj (f.toFun (Fin.cons x Y))*
      coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0 := by
  have he (X) : f.toFun X*f.toFun X = ((‖f.toFun X‖^2 : ℝ) : ℂ) := by
    calc
      _ = f.toFun X*conj (f.toFun X) := by rw [hr]
      _ = _ := by rw [Complex.mul_conj,Complex.sq_norm]
  have hc (Y) : (∫ x : Torus L, (f.mul f).toFun (Fin.cons x Y))=1 := by
    simp only [SmoothMultiplier.mul,Pi.mul_apply,he]
    rw [integral_complex_ofReal,hn,Complex.ofReal_one]
  have h := (f.mul f).hasDerivAt_fiberIntegral Y i j
  simp only [hc] at h
  have hz := h.unique (hasDerivAt_const (0:ℝ) (1:ℂ))
  have hd := coordDerivative_mul (f.smooth.differentiable (by simp))
    (f.smooth.differentiable (by simp)) (i.succ,j)
  change (∫ x : Torus L, coordDerivative (n+1) L (f.toFun*f.toFun) (i.succ,j) (Fin.cons x Y))=0 at hz
  rw [hd] at hz
  have hfactor : (∫ x : Torus L,
      (f.toFun * coordDerivative (n+1) L f.toFun (i.succ,j) +
        f.toFun * coordDerivative (n+1) L f.toFun (i.succ,j)) (Fin.cons x Y))=
      (2:ℂ)*(∫ x : Torus L, conj (f.toFun (Fin.cons x Y))*
      coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by simp only [Pi.add_apply,Pi.mul_apply,hr]; ring
  rw [hfactor] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_ConfigurationTailLp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma coe_configurationTailCLM {n : ℕ} {L : Length} (u : ScalarL2 n L) :
    configurationTailCLM n L u =ᵐ[volume] fun X ↦ u (Fin.tail X) := coe_configurationTailLp u

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma coe_insertionScalar {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L) :
    f.insertionScalar u =ᵐ[volume] fun X ↦ f.toFun X*u (Fin.tail X) := by
  filter_upwards [coe_configurationTailCLM u,L2Multiplier.coe_clm f.toFun f.memLp_top (configurationTailCLM n L u)]
    with X h1 h2
  exact h2.trans (by rw [h1])

lemma coe_insertionJet_zero {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (u : Jet n L) (j : Fin 3) :
    (f.insertionJet u).2 (0,j) =ᵐ[volume]
      fun X ↦ coordDerivative (n+1) L f.toFun (0,j) X*u.1 (Fin.tail X) := by
  change (f.insertionScalar 0+L2Multiplier.clm _ (f.partial_memLp_top (0,j))
    (configurationTailCLM n L u.1)) =ᵐ[volume] _
  rw [map_zero,zero_add]
  filter_upwards [coe_configurationTailCLM u.1,
    L2Multiplier.coe_clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1)] with X h1 h2
  exact h2.trans (by rw [h1])

lemma coe_insertionJet_succ {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (u : Jet n L) (i : Fin n) (j : Fin 3) :
    (f.insertionJet u).2 (i.succ,j) =ᵐ[volume]
      fun X ↦ f.toFun X*u.2 (i,j) (Fin.tail X)+
        coordDerivative (n+1) L f.toFun (i.succ,j) X*u.1 (Fin.tail X) := by
  change (f.insertionScalar (u.2 (i,j))+L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j))
    (configurationTailCLM n L u.1)) =ᵐ[volume] _
  filter_upwards [coe_insertionScalar f (u.2 (i,j)),coe_configurationTailCLM u.1,
    L2Multiplier.coe_clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1),
    Lp.coeFn_add (f.insertionScalar (u.2 (i,j)))
      (L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1))]
      with X h1 h2 h3 h4
  rw [h4,Pi.add_apply,h1,h3,h2]

lemma SmoothTest.jet_insert {n : ℕ} {L : Length} {a : ℝ} (g : SmoothTest n L a)
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f) :
    (g.insert f hc).jet=f.insertionJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (g.insert f hc).memLp,
      (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
      coe_insertionScalar f g.jet.1] with X h1 h2 h3
    dsimp only [Function.comp_def] at h2
    change ((g.insert f hc).jet.1) X=(f.insertionScalar g.jet.1) X
    rw [h3]
    dsimp only [SmoothTest.jet]
    rw [h1,h2]
    rfl
  · funext p
    rcases p with ⟨i,j⟩
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((g.insert f hc).partial_memLp (0,j)),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
        coe_insertionJet_zero f g.jet j] with X h1 h2 h3
      dsimp only [Function.comp_def] at h2
      rw [h3]
      dsimp only [SmoothTest.jet]
      rw [h1]
      change coordDerivative (n+1) L (f.toFun*(fun X ↦ g.toFun (Fin.tail X))) (0,j) X=_
      rw [coordDerivative_mul (f.smooth.differentiable (by simp))
        ((smooth_tail g.smooth).differentiable (by simp)),
        coordDerivative_tail_zero (g.smooth.differentiable (by simp))]
      simp only [Pi.add_apply,Pi.mul_apply,Pi.zero_apply,mul_zero,zero_add,h2]
      ring
    · apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((g.insert f hc).partial_memLp (k.succ,j)),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp g.memLp),
        (configurationTail_quasiPreserving n L).ae_eq_comp (MemLp.coeFn_toLp (g.partial_memLp (k,j))),
        coe_insertionJet_succ f g.jet k j] with X h1 h2 h3 h4
      dsimp only [Function.comp_def] at h2 h3
      rw [h4]
      dsimp only [SmoothTest.jet]
      rw [h1]
      change coordDerivative (n+1) L (f.toFun*(fun X ↦ g.toFun (Fin.tail X))) (k.succ,j) X=_
      rw [coordDerivative_mul (f.smooth.differentiable (by simp))
        ((smooth_tail g.smooth).differentiable (by simp)),
        coordDerivative_tail_succ (g.smooth.differentiable (by simp))]
      simp only [Pi.add_apply,Pi.mul_apply,h2,h3]
      ring

lemma SmoothMultiplier.insertionJet_mem_domain {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    f.insertionJet u∈dirichletDomain (n+1) L a := by
  apply map_mem_closure f.insertionJet.continuous hu
  rintro _ ⟨g,rfl⟩
  exact ⟨g.insert f hc,g.jet_insert f hc⟩

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusLiftBox
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma SmoothMultiplier.normalization_real {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) (X) :
    conj ((f.normalization hr hp).toFun X)=(f.normalization hr hp).toFun X := by
  change conj (f.toFun X/(Real.sqrt (f.fiberMass (Fin.tail X)) : ℂ))=_
  rw [map_div₀,Complex.conj_ofReal,hr]
  rfl

lemma SmoothMultiplier.normalization_norm {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hp : ∀ Y, 0<f.fiberMass Y) (Y : Configuration n L) :
    ∫ x : Torus L, ‖(f.normalization hr hp).toFun (Fin.cons x Y)‖^2=1 := by
  change (∫ x : Torus L, ‖f.toFun (Fin.cons x Y)/(Real.sqrt (f.fiberMass Y) : ℂ)‖^2)=1
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),div_pow,Real.sq_sqrt (hp Y).le]
  rw [integral_div]
  exact div_self (hp Y).ne'

lemma SmoothMultiplier.normalization_clearance {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hp : ∀ Y, 0<f.fiberMass Y) (hc : InsertionClearance a f) :
    InsertionClearance a (f.normalization hr hp) := by
  apply Set.Subset.trans (b := tsupport f.toFun) _ hc
  change tsupport (fun X ↦ f.toFun X/(Real.sqrt (f.fiberMass (Fin.tail X)) : ℂ))⊆_
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

lemma integral_norm_add_sq_orthogonal {A : Type*} [TopologicalSpace A] [CompactSpace A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    {μ : Measure A} [IsFiniteMeasure μ] {f g : A → ℂ} (hf : Continuous f) (hg : Continuous g)
    (ho : ∫ x, conj (f x)*g x ∂μ=0) :
    ∫ x, ‖f x+g x‖^2 ∂μ=(∫ x, ‖f x‖^2 ∂μ)+(∫ x, ‖g x‖^2 ∂μ) := by
  have hi {E : Type} [NormedAddCommGroup E] {h : A → E} (hc : Continuous h) : Integrable h μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : A) : ‖f x+g x‖^2=‖f x‖^2+2*(conj (f x)*g x).re+‖g x‖^2 := by
    simpa only [RCLike.inner_apply',RCLike.re_to_complex] using @norm_add_sq ℂ ℂ _ _ _ (f x) (g x)
  simp_rw [he]
  have hf2 : Integrable (fun x ↦ ‖f x‖^2) μ := hi (hf.norm.pow 2)
  have hg2 : Integrable (fun x ↦ ‖g x‖^2) μ := hi (hg.norm.pow 2)
  have hcross : Integrable (fun x ↦ conj (f x)*g x) μ := hi ((Complex.continuous_conj.comp hf).mul hg)
  have hre : Integrable (fun x ↦ 2*(conj (f x)*g x).re) μ := hcross.re.const_mul 2
  have hRe : (∫ x, (conj (f x)*g x).re ∂μ)=(∫ x, conj (f x)*g x ∂μ).re := by
    simpa only [RCLike.re_to_complex] using integral_re hcross
  rw [integral_add (f := fun x ↦ ‖f x‖^2+2*(conj (f x)*g x).re)
      (g := fun x ↦ ‖g x‖^2) (hf2.add hre) hg2, integral_add hf2 hre, integral_const_mul,
    hRe,ho]
  simp

lemma SmoothMultiplier.fiber_derivative_mul_tail_le {n : ℕ} {L : Length}
    (g : SmoothMultiplier (n+1) L) (r : SmoothMultiplier n L)
    (hr : ∀ X, conj (g.toFun X)=g.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖g.toFun (Fin.cons x Y)‖^2=1)
    (p : Direction (n+1)) (Y : Configuration n L) :
    ‖r.toFun Y‖^2 * (∫ x : Torus L, ‖coordDerivative (n+1) L g.toFun p (Fin.cons x Y)‖^2) ≤
      ∫ x : Torus L, ‖coordDerivative (n+1) L (fun X ↦ g.toFun X*r.toFun (Fin.tail X)) p
        (Fin.cons x Y)‖^2 := by
  have hd := coordDerivative_mul (g := fun X : Configuration (n+1) L ↦ r.toFun (Fin.tail X))
    (g.smooth.differentiable (by simp))
    ((smooth_tail r.smooth).differentiable (by simp)) p
  have hc : Continuous (fun x : Torus L ↦ (Fin.cons x Y : Configuration (n+1) L)) :=
    (continuous_id : Continuous (id : Torus L → Torus L)).finCons
      (continuous_const : Continuous (fun _ : Torus L ↦ Y))
  have hg := (continuous_of_continuous_lift g.smooth.continuous).comp hc
  have hdg := (continuous_coordDerivative g.smooth p).comp hc
  have hs := r.smooth.differentiable (by simp)
  rcases p with ⟨i,j⟩
  induction i using Fin.cases with
  | zero =>
    simp only [coordDerivative_tail_zero hs j,mul_zero,zero_add] at hd
    rw [show (fun X ↦ g.toFun X*r.toFun (Fin.tail X))=g.toFun*(fun X ↦ r.toFun (Fin.tail X)) from rfl,hd]
    simp only [Pi.mul_apply,Fin.tail_cons,norm_mul,mul_pow]
    rw [integral_const_mul]
  | succ k =>
    have he := g.insertion_orthogonal hr hn k j Y
    have ho : (∫ x : Torus L,
        conj (g.toFun (Fin.cons x Y)*coordDerivative n L r.toFun (k,j) Y)*
          (r.toFun Y*coordDerivative (n+1) L g.toFun (k.succ,j) (Fin.cons x Y)))=0 := by
      calc
        _ = (conj (coordDerivative n L r.toFun (k,j) Y)*r.toFun Y)*
            ∫ x : Torus L, conj (g.toFun (Fin.cons x Y))*
              coordDerivative (n+1) L g.toFun (k.succ,j) (Fin.cons x Y) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Eventually.of_forall fun x ↦ by simp only [map_mul]; ring
        _ = 0 := by rw [he,mul_zero]
    have heq := integral_norm_add_sq_orthogonal (hg.mul continuous_const) (continuous_const.mul hdg) ho
    simp only [Pi.mul_apply,Function.comp_def] at heq
    have hd' := coordDerivative_mul (g := fun X : Configuration (n+1) L ↦ r.toFun (Fin.tail X))
      (g.smooth.differentiable (by simp))
      ((smooth_tail r.smooth).differentiable (by simp)) (k.succ,j)
    rw [coordDerivative_tail_succ hs k j] at hd'
    rw [show (fun X ↦ g.toFun X*r.toFun (Fin.tail X))=g.toFun*(fun X ↦ r.toFun (Fin.tail X)) from rfl,hd']
    simp only [Pi.mul_apply,Pi.add_apply,Fin.tail_cons]
    rw [heq]
    simp only [norm_mul,mul_pow]
    rw [integral_const_mul]
    exact le_add_of_nonneg_left (integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RawAngleLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open PeriodicCutoff
open scoped ComplexConjugate

lemma rawCutoff_real (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    conj ((rawCutoff n L r).toFun X)=(rawCutoff n L r).toFun X := Complex.conj_ofReal _

lemma rawCutoff_norm_sq (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    ‖(rawCutoff n L r).toFun X‖^2=rawCutoffReal n L r X^2 := by
  change ‖(rawCutoffReal n L r X : ℂ)‖^2=_
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma rawCutoff_clearance (n : ℕ) (L : Length) {r : ℝ} (hr : 0 < r) :
    InsertionClearance r (rawCutoff n L r) := by
  intro X hX i
  have hs : tsupport (rawCutoff n L r).toFun ⊆
      {X | 2*r^2≤pairQ L.val (X 0) (X i.succ)} := by
    have hc : Continuous (fun X : Configuration (n+1) L ↦ pairQ L.val (X 0) (X i.succ)) :=
      by
        have hp : Continuous (fun X : Configuration (n+1) L ↦ (X 0,X i.succ)) := by fun_prop
        exact (pairQ_continuous L.val).comp hp
    apply closure_minimal ?_ (isClosed_le continuous_const hc)
    intro R hR
    by_contra hn
    have hz : (rawCutoff n L r).toFun R=0 := by
      change ((∏ k : Fin n,Real.sin (angle L.val r (R 0) (R k.succ)) : ℝ) : ℂ)=0
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [angle_zero L.val hr (not_le.mp hn).le,Real.sin_zero]),Complex.ofReal_zero]
    exact hR hz
  have hQ : 2*r^2≤pairQ L.val (X 0) (X i.succ) := hs hX
  have he : torusDistance L (X 0) (X i.succ)^2=
      ∑ j : Fin 3,dist (X 0 j) (X i.succ j)^2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hl := pairQ_le L.val (X 0) (X i.succ)
  have hd : 0≤torusDistance L (X 0) (X i.succ) := Real.sqrt_nonneg _
  nlinarith [sq_pos_of_pos hr]

end HardSphere

namespace HardSphere
open PeriodicCutoff

lemma torus_volume_real (L : Length) : volume.real (Set.univ : Set (Torus L))=L.val^3 := by
  rw [measureReal_def,volume_pi,Measure.pi_univ]
  simp only [AddCircle.measure_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal L.property.le]

lemma rawCutoff_mass_pointwise (n : ℕ) (L : Length) {r : ℝ} (hr : 0 < r)
    (y : Torus L) (Y : Configuration n L) :
    1≤‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2+
      ∑ i : Fin n, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  rw [rawCutoff_norm_sq]
  have hb (i : Fin n) : 0≤(box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  by_cases hh : ∃ i, y∈box L.val (Real.pi*r) (Y i)
  · obtain ⟨i,hi⟩ := hh
    have hs := Finset.single_le_sum (f := fun i : Fin n ↦
      (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y) (fun i _ ↦ hb i) (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi] at hs
    exact hs.trans (le_add_of_nonneg_left (sq_nonneg _))
  · have ha (i : Fin n) : angle L.val r y (Y i)=Real.pi/2 :=
      angle_one_outside L.val hr (fun hi ↦ hh ⟨i,hi⟩)
    have he : rawCutoffReal n L r (Fin.cons y Y)=1 := by
      simp only [rawCutoffReal,Fin.cons_zero,Fin.cons_succ,ha,Real.sin_pi_div_two,Finset.prod_const_one]
    rw [he,one_pow]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hb i))

lemma rawCutoff_mass_lower (n : ℕ) (L : Length) {r : ℝ} (hr : 0 < r)
    (Y : Configuration n L) : L.val^3-(n:ℝ)*(2*Real.pi*r)^3≤(rawCutoff n L r).fiberMass Y := by
  have hc : Continuous (fun y : Torus L ↦ ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2) :=
    (((continuous_of_continuous_lift (rawCutoff n L r).smooth.continuous).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm).pow 2
  have hf : Integrable (fun y : Torus L ↦ ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2) volume :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (i : Fin n) : Integrable ((box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ))) volume :=
    (integrable_const (1:ℝ)).indicator (box_measurable L.val _ _)
  have hh := integral_mono (integrable_const (1:ℝ)) (hf.add (integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)))
    (fun y ↦ rawCutoff_mass_pointwise n L hr y Y)
  dsimp only [Pi.add_apply] at hh
  rw [integral_const,smul_eq_mul,mul_one,torus_volume_real,
    integral_add hf (integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)),
    integral_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ ↦ hi i)] at hh
  have hv : (∑ i : Fin n, ∫ y : Torus L, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y)≤
      (n:ℝ)*(2*Real.pi*r)^3 := by
    calc
      _ = ∑ i : Fin n, volume.real (box L.val (Real.pi*r) (Y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_indicator_one (box_measurable L.val _ _)
      _ ≤ ∑ i : Fin n, (2*(Real.pi*r))^3 := Finset.sum_le_sum (fun i _ ↦ box_volume_le L.val (by positivity) (Y i))
      _ = _ := by simp [mul_assoc]
  change L.val^3-(n:ℝ)*(2*Real.pi*r)^3≤∫ y : Torus L, ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2
  linarith

lemma rawAngleLift_fderiv (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R v : LiftedConfiguration (n+1)) :
    fderiv ℝ (rawAngleLift n L r i) R v =
      ∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j*(v 0 j-v i.succ j) := by
  have hd : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hf := (((rawAngleLift_smooth n L r i).differentiable (by simp)) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  have ha := angleLift_derivative L.val r
    (fun j t ↦ (R 0 j+t*v 0 j)-(R i.succ j+t*v i.succ j))
    (fun j ↦ v 0 j-v i.succ j) 0 (fun j ↦ by
      convert (((hasDerivAt_id (0:ℝ)).mul_const (v 0 j)).const_add (R 0 j)).sub
        (((hasDerivAt_id (0:ℝ)).mul_const (v i.succ j)).const_add (R i.succ j)) using 1 <;> first | rfl | simp only [one_mul])
  have he : (rawAngleLift n L r i ∘ fun t : ℝ ↦ R+t • v)=
      (fun t : ℝ ↦ angleLift L.val r (fun j ↦ (R 0 j+t*v 0 j)-(R i.succ j+t*v i.succ j))) := rfl
  rw [he] at hf
  convert hf.unique ha using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_mul,add_zero]
  rfl

lemma rawAngleLift_fderiv_coord (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R : LiftedConfiguration (n+1)) (p : Direction (n+1)) :
    fderiv ℝ (rawAngleLift n L r i) R (Pi.single p.1 (Pi.single p.2 1)) =
      ((if p.1=0 then (1:ℝ) else 0)-(if p.1=i.succ then 1 else 0))*
        anglePartial L.val r (R 0-R i.succ) p.2 := by
  rw [rawAngleLift_fderiv]
  by_cases h0 : p.1=0 <;> by_cases hi : p.1=i.succ
  · exact False.elim (Fin.succ_ne_zero i (hi.symm.trans h0))
  · simp [h0,Pi.single_apply,eq_comm,Finset.sum_ite_eq',mul_comm]
  · simp [hi,Pi.single_apply,eq_comm,Finset.sum_ite_eq',mul_comm]
  · simp [h0,hi,Ne.symm h0,Ne.symm hi]

lemma rawCutoff_derivative_sq_le (n : ℕ) (L : Length) (r : ℝ)
    (X : Configuration (n+1) L) (p : Direction (n+1)) :
    ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2≤
      ∑ i : Fin n, (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
        (Pi.single p.1 (Pi.single p.2 1)))^2 := by
  let R := representative (n+1) L X
  let v : LiftedConfiguration (n+1) := Pi.single p.1 (Pi.single p.2 1)
  have he : (fun Y : LiftedConfiguration (n+1) ↦ (rawCutoff n L r).toFun (project (n+1) L Y))=
      Complex.ofRealCLM ∘ (fun Y : LiftedConfiguration (n+1) ↦ ∏ i : Fin n, Real.sin (rawAngleLift n L r i Y)) := by
    funext Y
    change (rawCutoffReal n L r (project (n+1) L Y) : ℂ)=_
    simp only [rawCutoffReal,angle_project,Function.comp_apply,Complex.ofRealCLM_apply]
  have hd := (rawCutoffReal_smooth n L r).differentiable (by simp)
  simp only [rawCutoffReal,angle_project] at hd
  change ‖fderiv ℝ (fun Y ↦ (rawCutoff n L r).toFun (project (n+1) L Y)) R v‖^2≤_
  rw [he,fderiv_comp R Complex.ofRealCLM.differentiableAt (hd R),Complex.ofRealCLM.fderiv]
  simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact SineProduct.fderiv_sq_le Finset.univ (rawAngleLift n L r) R v
    (fun i _ ↦ (rawAngleLift_smooth n L r i).differentiable (by simp) R)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_RawAngleLiftSumSquares
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open PeriodicCutoff

lemma rawAngleLift_sum_squares (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R : LiftedConfiguration (n+1)) :
    (∑ p : Direction (n+1), (fderiv ℝ (rawAngleLift n L r i) R
      (Pi.single p.1 (Pi.single p.2 1)))^2)=
      2*∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j^2 := by
  simp only [rawAngleLift_fderiv_coord]
  rw [Fintype.sum_prod_type,Fin.sum_univ_succ]
  simp only [Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero i),ite_true,ite_false,sub_zero,one_mul,
    Fin.succ_inj,zero_sub,neg_mul,neg_sq]
  have he : (∑ k : Fin n, ∑ j : Fin 3,
      ((if k=i then (1:ℝ) else 0)*anglePartial L.val r (R 0-R i.succ) j)^2)=
      ∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp
  rw [he]
  ring

lemma pairQ_representative (n : ℕ) (L : Length) (i : Fin n) (X : Configuration (n+1) L) :
    pairQ L.val (X 0) (X i.succ)=qLift L.val
      (representative (n+1) L X 0-representative (n+1) L X i.succ) := by
  calc
    _ = pairQ L.val (project (n+1) L (representative (n+1) L X) 0)
      (project (n+1) L (representative (n+1) L X) i.succ) := by rw [project_representative]
    _ = _ := pairQ_coe L.val _ _

lemma rawAngleLift_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (i : Fin n) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
      (Pi.single p.1 (Pi.single p.2 1)))^2)≤
      (6*Real.pi^2*M^2/r^2)*(box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  rw [rawAngleLift_sum_squares]
  by_cases hx : X 0∈box L.val (Real.pi*r) (X i.succ)
  · rw [Set.indicator_of_mem hx,mul_one]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ ↦ anglePartial_sq_le L.val hr hM hb
        (representative (n+1) L X 0-representative (n+1) L X i.succ) j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    calc
      _ ≤ 2*((3:ℝ)*(Real.pi^2*M^2/r^2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx,mul_zero]
    have hq := not_mem_box_pairQ L.val hr hx
    rw [pairQ_representative] at hq
    have hz : qLift L.val (representative (n+1) L X 0-representative (n+1) L X i.succ)∉Icc (2*r^2) (4*r^2) :=
      fun hs ↦ (not_lt.mpr hs.2) hq
    simp [anglePartial_eq_zero L.val hr hz]

lemma rawCutoff_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2)≤
      (6*Real.pi^2*M^2/r^2)*∑ i : Fin n,
        (box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  calc
    _ ≤ ∑ p : Direction (n+1), ∑ i : Fin n,
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 :=
      Finset.sum_le_sum fun p _ ↦ rawCutoff_derivative_sq_le n L r X p
    _ = ∑ i : Fin n, ∑ p : Direction (n+1),
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 := by rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin n, (6*Real.pi^2*M^2/r^2)*
        (box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) :=
      Finset.sum_le_sum fun i _ ↦ rawAngleLift_gradient_le n L hr hM hb i X
    _ = _ := (Finset.mul_sum ..).symm

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_IntegralConfigurationCons
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma integral_configuration_cons {n : ℕ} {L : Length} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Configuration (n+1) L → E)
    (hF : Integrable F volume) :
    ∫ X, F X = ∫ Y : Configuration n L, ∫ x : Torus L, F (Fin.cons x Y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  rw [← he.integral_comp' F]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero', Function.comp_def] at hi ⊢
  exact integral_prod_symm _ hi

lemma coe_weightedTail {n : ℕ} {L : Length} (h : Configuration (n+1) L → ℂ)
    (hh : MemLp h ∞ volume) (u : ScalarL2 n L) :
    L2Multiplier.clm h hh (configurationTailCLM n L u) =ᵐ[volume] fun X ↦ h X*u (Fin.tail X) := by
  filter_upwards [coe_configurationTailCLM u,
    L2Multiplier.coe_clm h hh (configurationTailCLM n L u)] with X h1 h2
  exact h2.trans (by rw [h1])

lemma weightedTail_pairing {n : ℕ} {L : Length}
    (f g : Configuration (n+1) L → ℂ) (hf : MemLp f ∞ volume) (hg : MemLp g ∞ volume)
    (u v : ScalarL2 n L) :
    inner ℂ (L2Multiplier.clm f hf (configurationTailCLM n L u))
      (L2Multiplier.clm g hg (configurationTailCLM n L v)) =
      ∫ Y : Configuration n L, (conj (u Y)*v Y)*
        ∫ x : Torus L, conj (f (Fin.cons x Y))*g (Fin.cons x Y) := by
  have hfm : MemLp (fun X : Configuration (n+1) L ↦ f X*u (Fin.tail X)) 2 volume :=
    (memLp_configurationTail (Lp.memLp u)).mul hf
  have hgm : MemLp (fun X : Configuration (n+1) L ↦ g X*v (Fin.tail X)) 2 volume :=
    (memLp_configurationTail (Lp.memLp v)).mul hg
  have hi : Integrable (fun X : Configuration (n+1) L ↦
      conj (f X*u (Fin.tail X))*(g X*v (Fin.tail X))) volume := by
    have h := (hfm.inner_const (𝕜 := ℂ) (1:ℂ)).integrable_mul hgm
    exact h.congr (Eventually.of_forall fun X ↦ by
      dsimp only [Pi.mul_apply]
      rw [RCLike.inner_apply,one_mul])
  rw [L2.inner_def]
  calc
    _ = ∫ X : Configuration (n+1) L, conj (f X*u (Fin.tail X))*(g X*v (Fin.tail X)) := by
      apply integral_congr_ae
      filter_upwards [coe_weightedTail f hf u,coe_weightedTail g hg v] with X h1 h2
      simp only [h1,h2,RCLike.inner_apply']
    _ = ∫ Y : Configuration n L, ∫ x : Torus L,
        conj (f (Fin.cons x Y)*u Y)*(g (Fin.cons x Y)*v Y) := by
      simpa only [Fin.tail_cons] using integral_configuration_cons _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun Y ↦ by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by simp only [map_mul]; ring

lemma norm_weightedTail_sq {n : ℕ} {L : Length}
    (f : Configuration (n+1) L → ℂ) (hf : MemLp f ∞ volume) (u : ScalarL2 n L) :
    ‖L2Multiplier.clm f hf (configurationTailCLM n L u)‖^2 =
      ∫ Y : Configuration n L, ‖u Y‖^2 * ∫ x : Torus L, ‖f (Fin.cons x Y)‖^2 := by
  have hm : MemLp (fun X : Configuration (n+1) L ↦ f X*u (Fin.tail X)) 2 volume :=
    (memLp_configurationTail (Lp.memLp u)).mul hf
  rw [IndicatorStrong.norm_sq_integral]
  calc
    _ = ∫ X : Configuration (n+1) L, ‖f X*u (Fin.tail X)‖^2 := by
      exact integral_congr_ae ((coe_weightedTail f hf u).mono fun _ h ↦ by dsimp only at h ⊢; rw [h])
    _ = ∫ Y : Configuration n L, ∫ x : Torus L, ‖f (Fin.cons x Y)*u Y‖^2 := by
      simpa only [Fin.tail_cons] using integral_configuration_cons _ (hm.integrable_norm_pow (by decide : (2:ℕ)≠0))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun Y ↦ by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by dsimp only; rw [norm_mul,mul_pow,mul_comm]

lemma SmoothMultiplier.norm_insertionScalar_sq {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (u : ScalarL2 n L) : ‖f.insertionScalar u‖^2=‖u‖^2 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    norm_weightedTail_sq,IndicatorStrong.norm_sq_integral]
  simp only [hn,mul_one]

lemma SmoothMultiplier.norm_insertionScalar {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (u : ScalarL2 n L) : ‖f.insertionScalar u‖=‖u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (f.norm_insertionScalar_sq hn u)

lemma SmoothMultiplier.insertion_cross_zero {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (p : Direction (n+1))
    (ho : ∀ Y : Configuration n L, ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun p (Fin.cons x Y)=0)
    (u v : ScalarL2 n L) :
    inner ℂ (f.insertionScalar u)
      (L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L v))=0 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    weightedTail_pairing]
  simp only [ho,mul_zero,integral_zero]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_EnergyInsertionJet
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.energy_insertionJet {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (u : Jet n L) :
    energy (f.insertionJet u)=energy u + ∑ p : Direction (n+1),
      ‖L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L u.1)‖^2 := by
  have hz (j : Fin 3) : (f.insertionJet u).2 (0,j)=
      L2Multiplier.clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1) := by
    change f.insertionScalar 0 + _ = _
    rw [map_zero,zero_add]
    rfl
  have hs (i : Fin n) (j : Fin 3) : ‖(f.insertionJet u).2 (i.succ,j)‖^2=
      ‖u.2 (i,j)‖^2+
      ‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 := by
    change ‖f.insertionScalar (u.2 (i,j)) +
      L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 = _
    rw [@norm_add_sq ℂ, f.insertion_cross_zero (i.succ,j) (ho i j),map_zero,
      mul_zero,add_zero,f.norm_insertionScalar hn]
  unfold energy
  simp only [Fintype.sum_prod_type,Fin.sum_univ_succ,hz,hs,Finset.sum_add_distrib]
  ring

lemma SmoothMultiplier.insertion_derivative_integrable {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L) (p : Direction (n+1)) :
    Integrable (fun Y : Configuration n L ↦ ‖u Y‖^2 *
      ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2) volume := by
  have hm := ((memLp_configurationTail (Lp.memLp u)).mul (f.partial_memLp_top p)).integrable_norm_pow
    (by decide : (2:ℕ)≠0)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hm
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_zero',Function.comp_def,Pi.mul_apply,Fin.tail_cons] at hi
  convert hi.integral_prod_right using 1
  all_goals try with_reducible_and_instances rfl
  funext Y
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by dsimp only; rw [norm_mul,mul_pow,mul_comm]

lemma SmoothMultiplier.energy_insertionJet_integral {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (u : Jet n L) :
    energy (f.insertionJet u)=energy u + ∫ Y : Configuration n L,
      ‖u.1 Y‖^2 * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
  rw [f.energy_insertionJet hn ho]
  simp_rw [norm_weightedTail_sq,Finset.mul_sum]
  rw [integral_finsetSum _ (fun p _ ↦ f.insertion_derivative_integrable u.1 p)]

lemma SmoothMultiplier.energy_insertionJet_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (C : ℝ) (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    (u : Jet n L) : energy (f.insertionJet u)≤energy u + C*‖u.1‖^2 := by
  rw [f.energy_insertionJet_integral hn ho,IndicatorStrong.norm_sq_integral,← integral_const_mul]
  apply add_le_add_right
  apply integral_mono
  · simpa only [Finset.mul_sum] using integrable_finsetSum _
      (fun p _ ↦ f.insertion_derivative_integrable u.1 p)
  · exact (Lp.memLp u.1).integrable_norm_pow (by decide : (2:ℕ)≠0) |>.const_mul C
  · intro Y
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hC Y) (sq_nonneg ‖u.1 Y‖)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_NormalizedInsertion
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.normalized_insertion {n : ℕ} {L : Length} {a C : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    f.insertionJet u∈dirichletDomain (n+1) L a ∧
      ‖(f.insertionJet u).1‖=‖u.1‖ ∧ energy (f.insertionJet u)≤energy u+C*‖u.1‖^2 := by
  refine ⟨f.insertionJet_mem_domain hc hu,?_,?_⟩
  · exact f.norm_insertionScalar hn u.1
  · exact f.energy_insertionJet_le hn (f.insertion_orthogonal hr hn) C hC u
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormalizationDerivative
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.normalization_derivative_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hp : ∀ Y, 0<f.fiberMass Y) (p : Direction (n+1)) (Y : Configuration n L) :
    f.fiberMass Y * (∫ x : Torus L,
      ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2) ≤
      ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
  have he : (fun X ↦ (f.normalization hr hp).toFun X *
      (f.massRoot hr hp).toFun (Fin.tail X))=f.toFun := by
    funext X
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp _)).ne')
  have hh := (f.normalization hr hp).fiber_derivative_mul_tail_le (f.massRoot hr hp)
    (f.normalization_real hr hp) (f.normalization_norm hr hp) p Y
  rw [he] at hh
  have hn : ‖(f.massRoot hr hp).toFun Y‖^2=f.fiberMass Y := by
    change ‖(Real.sqrt (f.fiberMass Y) : ℂ)‖^2=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hp Y).le]
  rwa [hn] at hh

lemma SmoothMultiplier.insertion_from_raw {n : ℕ} {L : Length} {a C z : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hz : 0<z)
    (hZ : ∀ Y : Configuration n L, z≤f.fiberMass Y)
    (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    {u : Jet n L} (hu : u∈dirichletDomain n L a) :
    ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L a ∧
      ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C/z)*‖u.1‖^2 := by
  have hp : ∀ Y, 0<f.fiberMass Y := fun Y ↦ hz.trans_le (hZ Y)
  refine ⟨(f.normalization hr hp).insertionJet u,?_⟩
  refine (f.normalization hr hp).normalized_insertion (f.normalization_clearance hr hp hc)
    (f.normalization_real hr hp) (f.normalization_norm hr hp) ?_ hu
  intro Y
  rw [le_div_iff₀ hz,mul_comm]
  calc
    z * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2 ≤
      f.fiberMass Y * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (f.normalization hr hp).toFun p (Fin.cons x Y)‖^2 := by
      apply mul_le_mul_of_nonneg_right (hZ Y)
      exact Finset.sum_nonneg fun p _ ↦ integral_nonneg fun x ↦ sq_nonneg _
    _ ≤ ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun p _ ↦ f.normalization_derivative_le hr hp p Y
    _ ≤ C := hC Y

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_RawCutoffGradientIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open PeriodicCutoff

lemma rawCutoff_gradient_integral_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (Y : Configuration n L) :
    (∑ p : Direction (n+1), ∫ y : Torus L,
      ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2)≤
      48*Real.pi^5*M^2*(n:ℝ)*r := by
  have hf (p : Direction (n+1)) : Integrable (fun y : Torus L ↦
      ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2) volume := by
    have hc : Continuous (fun y : Torus L ↦
        ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p (Fin.cons y Y)‖^2) :=
      (((continuous_coordDerivative (rawCutoff n L r).smooth p).comp
        ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
          (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm).pow 2
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (i : Fin n) : Integrable ((box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ))) volume :=
    (integrable_const (1:ℝ)).indicator (box_measurable L.val _ _)
  have hh := integral_mono (integrable_finsetSum Finset.univ (fun p _ ↦ hf p))
    ((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul (6*Real.pi^2*M^2/r^2))
    (fun y : Torus L ↦ rawCutoff_gradient_le n L hr hM hb (Fin.cons y Y))
  rw [integral_finsetSum _ (fun p _ ↦ hf p),integral_const_mul,
    integral_finsetSum _ (fun i _ ↦ hi i)] at hh
  have hv : (∑ i : Fin n, ∫ y : Torus L, (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y)≤
      (n:ℝ)*(2*Real.pi*r)^3 := by
    calc
      _ = ∑ i : Fin n, volume.real (box L.val (Real.pi*r) (Y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_indicator_one (box_measurable L.val _ _)
      _ ≤ ∑ i : Fin n, (2*(Real.pi*r))^3 := Finset.sum_le_sum (fun i _ ↦ box_volume_le L.val (by positivity) (Y i))
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ (6*Real.pi^2*M^2/r^2)*∑ i : Fin n, ∫ y : Torus L,
        (box L.val (Real.pi*r) (Y i)).indicator (fun _ ↦ (1:ℝ)) y := hh
    _ ≤ (6*Real.pi^2*M^2/r^2)*((n:ℝ)*(2*Real.pi*r)^3) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by field_simp [hr.ne']; ring

lemma uniform_insertion : ∃ C : ℝ, 0<C ∧ ∀ (n : ℕ) (L : Length) (r : ℝ), 0 < r →
    (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
      ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧
        ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C*(n:ℝ)*r/L.val^3)*‖u.1‖^2 := by
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  refine ⟨96*Real.pi^5*M^2,by positivity,fun n L r hr hs u hu ↦ ?_⟩
  have hL := L.property
  have hZ (Y : Configuration n L) : L.val^3/2≤(rawCutoff n L r).fiberMass Y := by
    linarith [rawCutoff_mass_lower n L hr Y]
  obtain ⟨v,hv,hn,he⟩ := (rawCutoff n L r).insertion_from_raw
    (rawCutoff_clearance n L hr) (rawCutoff_real n L r) (show 0<L.val^3/2 by positivity)
    hZ (rawCutoff_gradient_integral_le n L hr hM.le hb) hu
  refine ⟨v,hv,hn,?_⟩
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqLpIntegral
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma norm_sq_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,← integral_re]
  · apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,inner_self_eq_norm_sq]
  · exact L2.integrable_inner _ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_Regularize
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HilbertRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt {ε : ℝ} (hε : 0<ε) (z : E) :
    HasFDerivAt (regularize ε) (differential ε z) z := by
  have hn : ‖z‖^2+ε^2≠0 := by positivity
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε^2)).sqrt hn).sub_const ε)
  have hd : differential ε z = Complex.ofRealCLM.comp
      ((1/(2*Real.sqrt (‖z‖^2+ε^2))) • (2 • innerSL ℝ z)) := by
    ext w
    simp [differential,two_smul,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hd]
  exact h

omit [InnerProductSpace ℝ E] in
lemma sqroot_ge_norm (ε : ℝ) (z : E) : ‖z‖≤Real.sqrt (‖z‖^2+ε^2) :=
  (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith [sq_nonneg ε])

lemma differential_apply_le (ε : ℝ) (z w : E) : ‖differential ε z w‖≤‖w‖ := by
  by_cases hz : z=0
  · simp [hz,differential]
  have hp : 0<Real.sqrt (‖z‖^2+ε^2) :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz) (sqroot_ge_norm ε z)
  simp only [differential,smul_apply,ContinuousLinearMap.comp_apply,norm_smul,
    Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos hp,innerSL_apply_apply]
  change _*‖inner ℝ z w‖≤_
  apply le_trans (mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) z w) (by positivity :
    0≤(Real.sqrt (‖z‖^2+ε^2))⁻¹))
  rw [← div_eq_inv_mul,div_le_iff₀ hp]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (sqroot_ge_norm ε z) (norm_nonneg w)

lemma differential_le (ε : ℝ) (z : E) : ‖differential ε z‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simpa only [one_mul] using differential_apply_le ε z w

lemma fderiv_eq {ε : ℝ} (hε : 0<ε) (z : E) :
    fderiv ℝ (regularize ε) z=differential ε z := (hasFDerivAt hε z).fderiv

lemma lipschitz {ε : ℝ} (hε : 0<ε) : LipschitzWith 1 (regularize (E := E) ε) :=
  lipschitzWith_of_nnnorm_fderiv_le ((smooth hε).differentiable (by simp))
    (fun z ↦ by rw [fderiv_eq hε]; exact NNReal.coe_le_coe.mp (differential_le ε z))

lemma norm_le {ε : ℝ} (hε : 0<ε) (z : E) : ‖regularize ε z‖≤‖z‖ := by
  simpa only [zero hε.le,sub_zero,NNReal.coe_one,one_mul] using
    (lipschitz hε).norm_sub_le z 0

omit [InnerProductSpace ℝ E] in
lemma tendsto_regularize (z : E) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ regularize (e n) z) atTop (𝓝 (‖z‖ : ℂ)) := by
  have h : Tendsto (fun n ↦ Real.sqrt (‖z‖^2+e n^2)-e n) atTop (𝓝 ‖z‖) := by
    have h := (((tendsto_const_nhds (x := ‖z‖^2)).add (he.pow 2)).sqrt.sub he)
    simpa only [zero_pow (by norm_num : 2≠0),add_zero,sub_zero,Real.sqrt_sq (norm_nonneg _)] using h
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp h

end HilbertRegularization

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TestVector
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
section

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

lemma testVector_continuous (F : I → SmoothTest N L a) : Continuous (testVector F) :=
  continuous_of_continuous_lift (testVector_smooth F).continuous

lemma testVector_derivative (F : I → SmoothTest N L a) (X : Configuration N L) (p : Direction N) (i : I) :
    (fderiv ℝ (fun R : LiftedConfiguration N ↦ testVector F (project N L R)) (representative N L X)
      (Pi.single p.1 (Pi.single p.2 1))) i = coordDerivative N L (F i).toFun p X := by
  have hF := (testVector_smooth F).differentiable (by simp) (representative N L X)
  have hi := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2
    (testVector F (project N L (representative N L X))) i).comp (representative N L X) hF.hasFDerivAt).fderiv
  exact (congrArg (fun d ↦ d (Pi.single p.1 (Pi.single p.2 1))) hi).symm

lemma rmsTest_derivative_le (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε)
    (X : Configuration N L) (p : Direction N) :
    ‖coordDerivative N L (SmoothTest.rms F hε).toFun p X‖^2≤
      ∑ i : I, ‖coordDerivative N L (F i).toFun p X‖^2 := by
  have he : (fun R : LiftedConfiguration N ↦ (SmoothTest.rms F hε).toFun (project N L R))=
      HilbertRegularization.regularize ε ∘ (fun R ↦ testVector F (project N L R)) := rfl
  change ‖fderiv ℝ (fun R ↦ (SmoothTest.rms F hε).toFun (project N L R)) (representative N L X)
    (Pi.single p.1 (Pi.single p.2 1))‖^2≤_
  rw [he,fderiv_comp _ ((HilbertRegularization.smooth hε).differentiable (by simp)).differentiableAt
    ((testVector_smooth F).differentiable (by simp)).differentiableAt,
    HilbertRegularization.fderiv_eq hε,ContinuousLinearMap.comp_apply,project_representative]
  calc
    _ ≤ ‖fderiv ℝ (fun R ↦ testVector F (project N L R)) (representative N L X)
        (Pi.single p.1 (Pi.single p.2 1))‖^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (HilbertRegularization.differential_apply_le ε _ _) 2
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]; simp only [testVector_derivative]

end

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

lemma rmsTest_energy_le (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    energy (SmoothTest.rms F hε).jet ≤ ∑ i,energy (F i).jet := by
  classical
  change (∑ p, ‖(SmoothTest.rms F hε).jet.2 p‖^2)≤∑ i,∑ p,‖(F i).jet.2 p‖^2
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  simp only [SmoothTest.jet,norm_sq_toLp_eq_integral]
  rw [← integral_finsetSum (f := fun i X ↦ ‖coordDerivative N L (F i).toFun p X‖^2) Finset.univ (fun i _ ↦ ((F i).continuous_partial p).norm.pow 2 |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  apply integral_mono
  · exact ((SmoothTest.rms F hε).continuous_partial p).norm.pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_finsetSum _ (fun i _ ↦ ((F i).continuous_partial p).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro X
    exact rmsTest_derivative_le F hε X p

lemma rmsTest_norm_limit (F : I → SmoothTest N L a) {e : ℕ → ℝ}
    (he : ∀ k,0<e k) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖(SmoothTest.rms F (he k)).jet.1‖^2) atTop
      (𝓝 (∑ i,‖(F i).jet.1‖^2)) := by
  classical
  have hint : Integrable (fun X ↦ ‖testVector F X‖^2) (volume : Measure (Configuration N L)) :=
    ((testVector_continuous F).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlim := tendsto_integral_of_dominated_convergence (fun X ↦ ‖testVector F X‖^2)
    (fun k ↦ ((SmoothTest.rms F (he k)).continuous.norm.pow 2).aestronglyMeasurable)
    hint (fun k ↦ ae_of_all _ (fun X ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (HilbertRegularization.norm_le (he k) (testVector F X)) 2))
    (ae_of_all _ (fun X ↦ (HilbertRegularization.tendsto_regularize (testVector F X) he0).norm.pow 2))
  have hI : (∫ X : Configuration N L, ‖(‖testVector F X‖ : ℂ)‖^2) =
      ∑ i,‖(F i).jet.1‖^2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    simp only [EuclideanSpace.norm_sq_eq,testVector]
    rw [integral_finsetSum (f := fun i X ↦ ‖(F i).toFun X‖^2) Finset.univ (fun i _ ↦ ((F i).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    simp only [SmoothTest.jet,norm_sq_toLp_eq_integral]
  rw [hI] at hlim
  simp only [SmoothTest.jet,norm_sq_toLp_eq_integral,SmoothTest.rms,rmsTestFun] at hlim ⊢
  exact hlim
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_RmsPermuteFunBosonic
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
variable {N : ℕ} {L : Length} {a : ℝ}

lemma rmsPermute_fun_bosonic (f : SmoothTest N L a) (ε : ℝ) (τ : Equiv.Perm (Fin N))
    (X : Configuration N L) :
    rmsTestFun (fun σ ↦ f.permute σ) ε (permuteConfiguration τ X)=
      rmsTestFun (fun σ ↦ f.permute σ) ε X := by
  unfold rmsTestFun HilbertRegularization.regularize
  have hsum : ‖testVector (fun σ ↦ f.permute σ) (permuteConfiguration τ X)‖^2=
      ‖testVector (fun σ ↦ f.permute σ) X‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,testVector,SmoothTest.permute,Function.comp_apply]
    exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ ↦ ‖f.toFun (permuteConfiguration σ X)‖^2)
  rw [hsum]

lemma rmsPermute_bosonic (f : SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    bosonic (SmoothTest.rms (fun σ ↦ f.permute σ) hε).jet.1 := by
  intro τ
  let g := SmoothTest.rms (fun σ ↦ f.permute σ) hε
  have hg : (g.jet.1 : Configuration N L → ℂ)=ᵐ[volume] g.toFun := g.memLp.coeFn_toLp
  have hgt := (measurePreserving_permute τ).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hgt,hg] with X hX hY
  exact hX.trans ((rmsPermute_fun_bosonic f ε τ X).trans hY.symm)

lemma IsGroundVector.rayleigh_smooth_all {u : Jet N L} (hu : IsGroundVector N L a u)
    (f : SmoothTest N L a) : energy u*‖f.jet.1‖^2≤energy f.jet := by
  classical
  let e : ℕ → ℝ := fun k ↦ 1/((k:ℝ)+1)
  have he (k) : 0<e k := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hle (k : ℕ) : energy u*‖(SmoothTest.rms (fun σ ↦ f.permute σ) (he k)).jet.1‖^2≤
      ∑ σ : Equiv.Perm (Fin N), energy (f.permute σ).jet :=
    (hu.rayleigh _ (subset_closure (Set.mem_range_self _)) (rmsPermute_bosonic f (he k))).trans
      (rmsTest_energy_le _ (he k))
  have hl := le_of_tendsto ((rmsTest_norm_limit (fun σ ↦ f.permute σ) he he0).const_mul (energy u))
    (Eventually.of_forall hle)
  have hn (σ : Equiv.Perm (Fin N)) : ‖(f.permute σ).jet.1‖=‖f.jet.1‖ := by
    rw [f.jet_permute]
    exact Lp.norm_compMeasurePreserving _ _
  simp only [hn] at hl
  simp only [SmoothTest.jet_permute,energy_permutationJet,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hl
  have hc : 0<(Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith

lemma IsGroundVector.rayleigh_all {u : Jet N L} (hu : IsGroundVector N L a u)
    (v : Jet N L) (hv : v∈dirichletDomain N L a) : energy u*‖v.1‖^2≤energy v := by
  have hc : IsClosed {w : Jet N L | energy u*‖w.1‖^2≤energy w} := by
    apply isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2))
    exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  apply closure_minimal ?_ hc hv
  rintro _ ⟨f,rfl⟩
  exact hu.rayleigh_smooth_all f
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_IteratedInsertion
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere

lemma iterated_insertion (C : ℝ) (_hC : 0<C)
    (hins : ∀ (n : ℕ) (L : Length) (r : ℝ), 0 < r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
      ∀ u : Jet n L, u∈dirichletDomain n L r →
      ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧
        ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C*(n:ℝ)*r/L.val^3)*‖u.1‖^2)
    (n m : ℕ) (L : Length) {r : ℝ} (hr : 0 < r)
    (hs : ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ∃ v : Jet (n+m) L, v∈dirichletDomain (n+m) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v≤energy u+(∑ j∈Finset.range m,C*((n+j:ℕ):ℝ)*r/L.val^3)*‖u.1‖^2 := by
  induction m with
  | zero => exact ⟨u,hu,rfl,by simp⟩
  | succ m ih =>
    have hs' : ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 := by
      exact (mul_le_mul_of_nonneg_right
        (show ((n+m:ℕ):ℝ)≤((n+(m+1):ℕ):ℝ) by exact_mod_cast Nat.le_succ (n+m))
        (by positivity)).trans hs
    obtain ⟨v,hv,hn,he⟩ := ih hs'
    obtain ⟨w,hw,hnw,hew⟩ := hins (n+m) L r hr hs' v hv
    refine ⟨w,hw,hnw.trans hn,?_⟩
    rw [hn] at hew
    rw [Finset.sum_range_succ]
    nlinarith

lemma ground_energy_removal : ∃ C : ℝ, 0<C ∧
    ∀ (n m : ℕ) (L : Length) (r : ℝ), 0 < r →
    ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet (n+m) L, IsGroundVector (n+m) L r u →
    ∀ v : Jet n L, v∈dirichletDomain n L r →
      (energy u-C*(m:ℝ)*((n+m:ℕ):ℝ)*r/L.val^3)*‖v.1‖^2≤energy v := by
  obtain ⟨C,hC,hins⟩ := uniform_insertion
  refine ⟨C,hC,fun n m L r hr hs u hu v hv ↦ ?_⟩
  have hL : 0<L.val := L.property
  obtain ⟨w,hw,hn,he⟩ := iterated_insertion C hC hins n m L hr hs v hv
  have hmin := hu.rayleigh_all w hw
  rw [hn] at hmin
  have hsum : (∑ j∈Finset.range m,C*((n+j:ℕ):ℝ)*r/L.val^3)≤
      C*(m:ℝ)*((n+m:ℕ):ℝ)*r/L.val^3 := by
    calc
      _ ≤ ∑ _j∈Finset.range m,C*((n+m:ℕ):ℝ)*r/L.val^3 := by
        apply Finset.sum_le_sum
        intro j hj
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hr.le
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt (Finset.mem_range.mp hj)) n
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
  have := mul_le_mul_of_nonneg_right hsum (sq_nonneg ‖v.1‖)
  nlinarith
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_InnerClmRealRight
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal
lemma SmoothMultiplier.partial_real {N : ℕ} {L : Length} (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) (p : Direction N) (X : Configuration N L) :
    conj (coordDerivative N L f.toFun p X) = coordDerivative N L f.toFun p X := by
  have he : (fun X ↦ conj (f.toFun X)) = f.toFun := funext hf
  rw [← congrFun (coordDerivative_conj (f.smooth.differentiable (by simp)) p) X, he]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoeScalar
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.coe_onScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    f.onScalar u =ᵐ[volume] fun X ↦ f.toFun X*u X := L2Multiplier.coe_clm _ _ _

lemma SmoothMultiplier.coe_derivativeScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (p : Direction n) (u : ScalarL2 n L) :
    f.derivativeScalar p u =ᵐ[volume] fun X ↦ coordDerivative n L f.toFun p X*u X :=
  L2Multiplier.coe_clm _ _ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FinsetProd
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partial_finsetProd {S : Type*} [DecidableEq S] {n : ℕ} {L : Length}
    (A : Finset S) (w : S → SmoothMultiplier n L) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (SmoothMultiplier.finsetProd A w).toFun p X=
      ∑ s∈A, (∏ z∈A.erase s, (w z).toFun X)*coordDerivative n L (w s).toFun p X := by
  unfold coordDerivative
  change (fderiv ℝ (fun Y ↦ ∏ s∈A, (w s).toFun (project n L Y)) _) _ = _
  rw [fderiv_finsetProd (fun s _ ↦ (w s).smooth.differentiable (by simp) _),sum_apply]
  simp only [smul_apply,smul_eq_mul,project_representative]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LabelLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partial_liftLabel {L : Length} (w : SmoothMultiplier 1 L)
    (n : ℕ) (i : Fin n) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (w.liftLabel n i).toFun p X=
      if p.1=i then coordDerivative 1 L w.toFun (0,p.2) (fun _ ↦ X i) else 0 := by
  classical
  have h := (w.smooth.differentiable (by simp)
    (labelLift n i (representative n L X))).hasFDerivAt.comp
    (representative n L X) (labelLift n i).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration 1 ↦ w.toFun (project 1 L Y)) ∘ labelLift n i)
    (representative n L X)) (Pi.single p.1 (Pi.single p.2 1))=_
  rw [h.fderiv,ContinuousLinearMap.comp_apply]
  by_cases hp : p.1=i
  · rw [ite_eq_left hp]
    have hd : labelLift n i (Pi.single p.1 (Pi.single p.2 1))=Pi.single 0 (Pi.single p.2 1) := by
      ext k j
      have hk : k=0 := Subsingleton.elim _ _
      subst k
      simp [labelLift,hp]
    rw [hd]
    rfl
  · rw [ite_eq_right hp]
    have hd : labelLift n i (Pi.single p.1 (Pi.single p.2 1))=0 := by
      ext k j
      simp [labelLift,Ne.symm hp]
    rw [hd,map_zero]

lemma SmoothMultiplier.partial_sum {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (SmoothMultiplier.sum w).toFun p X=∑ s, coordDerivative n L (w s).toFun p X := by
  unfold coordDerivative
  change (fderiv ℝ (fun Y ↦ ∑ s, (w s).toFun (project n L Y)) _) _ = _
  rw [fderiv_fun_sum (fun s _ ↦ (w s).smooth.differentiable (by simp) _),sum_apply]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ScalarPartitionIms
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma scalar_partition_ims {S : Type*} [Fintype S] (w d : S → ℂ) (u v : ℂ)
    (hp : ∑ s, ‖w s‖^2=1) (hc : ∑ s, w s*conj (d s)=0) :
    (∑ s, ‖w s*v+d s*u‖^2)=‖v‖^2+∑ s, ‖d s*u‖^2 := by
  have hc' : (∑ s, (w s*v*conj (d s*u)).re)=0 := by
    rw [← Complex.re_sum]
    have hs : (∑ s, w s*v*conj (d s*u))=(v*conj u)*(∑ s, w s*conj (d s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [map_mul]
      ring
    rw [hs,hc,mul_zero,Complex.zero_re]
  simp_rw [← Complex.normSq_eq_norm_sq,Complex.normSq_add]
  simp_rw [Complex.normSq_mul,Complex.normSq_eq_norm_sq]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul,
    ← Finset.mul_sum,hc',mul_zero,add_zero]

lemma real_norm_sq (z : ℂ) (hz : conj z=z) : ‖z‖^2=(z*z).re := by
  have he := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z:=z))
  simpa only [hz,Complex.ofReal_re,Complex.normSq_eq_norm_sq] using he

lemma SmoothMultiplier.partition_derivative {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1)
    (p : Direction n) (X : Configuration n L) :
    (∑ s, (w s).toFun X*coordDerivative n L (w s).toFun p X)=0 := by
  let f := SmoothMultiplier.sum (fun s ↦ (w s).mul (w s))
  have hf : f.toFun=fun _ ↦ 1 := funext hp
  have hd : coordDerivative n L f.toFun p X=0 := by
    rw [hf]
    simp [coordDerivative]
  rw [SmoothMultiplier.partial_sum] at hd
  have he (s : S) : coordDerivative n L ((w s).mul (w s)).toFun p X=
      2*((w s).toFun X*coordDerivative n L (w s).toFun p X) := by
    change coordDerivative n L ((w s).toFun*(w s).toFun) p X=_
    rw [coordDerivative_mul ((w s).smooth.differentiable (by simp))
      ((w s).smooth.differentiable (by simp))]
    change (w s).toFun X*_+_*_= _
    ring
  simp_rw [he] at hd
  rw [← Finset.mul_sum] at hd
  exact (mul_eq_zero.mp hd).resolve_left (by norm_num)

lemma SmoothMultiplier.partition_norm {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hr : ∀ s X, conj ((w s).toFun X)=(w s).toFun X)
    (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1) (X : Configuration n L) :
    (∑ s, ‖(w s).toFun X‖^2)=1 := by
  simp_rw [real_norm_sq _ (hr _ _)]
  rw [← Complex.re_sum,hp,Complex.one_re]

lemma SmoothMultiplier.partition_scalar_norm {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hr : ∀ s X, conj ((w s).toFun X)=(w s).toFun X)
    (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1) (u : ScalarL2 n L) :
    (∑ s, ‖(w s).onScalar u‖^2)=‖u‖^2 := by
  simp_rw [IndicatorStrong.norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun s _ ↦
    (Lp.memLp ((w s).onScalar u)).integrable_norm_pow (by norm_num))]
  apply integral_congr_ae
  have hc : ∀ᵐ X ∂volume, ∀ s, ((w s).onScalar u) X=(w s).toFun X*u X :=
    ae_all_iff.mpr (fun s ↦ (w s).coe_onScalar u)
  filter_upwards [hc] with X hX
  simp_rw [hX,norm_mul,mul_pow]
  rw [← Finset.sum_mul,SmoothMultiplier.partition_norm w hr hp,one_mul]

lemma SmoothMultiplier.partition_direction_ims {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hr : ∀ s X, conj ((w s).toFun X)=(w s).toFun X)
    (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1) (u : Jet n L) (p : Direction n) :
    (∑ s, ‖((w s).onJet u).2 p‖^2)=‖u.2 p‖^2+∑ s, ‖(w s).derivativeScalar p u.1‖^2 := by
  have hi (s : S) : Integrable (fun X ↦ ‖((w s).derivativeScalar p u.1) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  simp_rw [IndicatorStrong.norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun s _ ↦
    (Lp.memLp (((w s).onJet u).2 p)).integrable_norm_pow (by norm_num)),
    ← integral_finsetSum Finset.univ (fun s _ ↦ hi s),
    ← integral_add ((Lp.memLp (u.2 p)).integrable_norm_pow (by norm_num)) (integrable_finsetSum _ (fun s _ ↦ hi s))]
  apply integral_congr_ae
  have hc (s : S) : ∀ᵐ X ∂volume,
      (((w s).onJet u).2 p) X=(w s).toFun X*(u.2 p) X+coordDerivative n L (w s).toFun p X*u.1 X := by
    filter_upwards [(w s).coe_onScalar (u.2 p),(w s).coe_derivativeScalar p u.1,
      Lp.coeFn_add ((w s).onScalar (u.2 p)) ((w s).derivativeScalar p u.1)] with X h1 h2 h3
    change (((w s).onScalar (u.2 p)+(w s).derivativeScalar p u.1) : ScalarL2 n L) X=_
    rw [h3,Pi.add_apply,h1,h2]
  have hd : ∀ᵐ X ∂volume, ∀ s, ((w s).derivativeScalar p u.1) X=coordDerivative n L (w s).toFun p X*u.1 X :=
    ae_all_iff.mpr (fun s ↦ (w s).coe_derivativeScalar p u.1)
  filter_upwards [ae_all_iff.mpr hc,hd] with X hX hY
  simp_rw [hX,hY]
  apply scalar_partition_ims _ _ _ _ (SmoothMultiplier.partition_norm w hr hp X)
  simp_rw [(w _).partial_real (hr _) p X]
  exact SmoothMultiplier.partition_derivative w hp p X

theorem SmoothMultiplier.partition_ims {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (hr : ∀ s X, conj ((w s).toFun X)=(w s).toFun X)
    (hp : ∀ X, ∑ s, (w s).toFun X*(w s).toFun X=1) (u : Jet n L) :
    (∑ s, energy ((w s).onJet u))=energy u+∑ p : Direction n, ∑ s, ‖(w s).derivativeScalar p u.1‖^2 := by
  change (∑ s, ∑ p, ‖((w s).onJet u).2 p‖^2)=_
  rw [Finset.sum_comm]
  simp_rw [SmoothMultiplier.partition_direction_ims w hr hp u]
  rw [Finset.sum_add_distrib]
  rfl

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma productPartition_apply (n : ℕ) (L : Length) (a c : SmoothMultiplier 1 L)
    (σ : Fin n → Bool) (X : Configuration n L) :
    (productPartition n L a c σ).toFun X=∏ i, (cond (σ i) a c).orbital (X i) := rfl

lemma productPartition_real {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (σ : Fin n → Bool) (X : Configuration n L) :
    conj ((productPartition n L a c σ).toFun X)=(productPartition n L a c σ).toFun X := by
  simp only [productPartition_apply,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp only [Bool.cond_false,Bool.cond_true,SmoothMultiplier.orbital,ha,hc]

lemma productPartition_unity {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (X : Configuration n L) :
    (∑ σ : Fin n → Bool, (productPartition n L a c σ).toFun X*(productPartition n L a c σ).toFun X)=1 := by
  simp_rw [productPartition_apply,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) ↦
    (cond b a c).orbital (X i)*(cond b a c).orbital (X i))]
  simp only [Fintype.sum_bool,Bool.cond_true,Bool.cond_false,hp,Finset.prod_const_one]

lemma productPartition_partial {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (σ : Fin n → Bool) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (productPartition n L a c σ).toFun p X=
      (∏ i∈Finset.univ.erase p.1, (cond (σ i) a c).orbital (X i))*
      coordDerivative 1 L (cond (σ p.1) a c).toFun (0,p.2) (fun _ ↦ X p.1) := by
  classical
  rw [productPartition,SmoothMultiplier.partial_finsetProd]
  simp_rw [SmoothMultiplier.partial_liftLabel]
  rw [Finset.sum_eq_single p.1]
  · rw [ite_eq_left rfl]
    rfl
  · intro i _ hi
    rw [ite_eq_right (Ne.symm hi),mul_zero]
  · simp

lemma binary_product_sum {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Bool → ℝ) (d : Bool → ℝ) (j : I)
    (hf : ∀ i, f i true+f i false=1) :
    (∑ σ : I → Bool, (∏ i∈Finset.univ.erase j, f i (σ i))*d (σ j))=d true+d false := by
  let g (i : I) (b : Bool) := if i=j then d b else f i b
  have he (σ : I → Bool) : (∏ i∈Finset.univ.erase j, f i (σ i))*d (σ j)=∏ i, g i (σ i) := by
    rw [← Finset.prod_erase_mul Finset.univ (fun i ↦ g i (σ i)) (Finset.mem_univ j)]
    dsimp only [g]
    rw [ite_eq_left rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.mem_erase.mp hi).1]
  simp_rw [he]
  rw [← Fintype.prod_sum,Finset.prod_eq_single j]
  · simp [g]
  · intro i _ hi
    simpa only [g,ite_eq_right hi,Fintype.sum_bool] using hf i
  · simp

lemma productPartition_gradient_partition {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (p : Direction n) (X : Configuration n L) :
    (∑ σ : Fin n → Bool, ‖coordDerivative n L (productPartition n L a c σ).toFun p X‖^2)=
      ‖coordDerivative 1 L a.toFun (0,p.2) (fun _ ↦ X p.1)‖^2+
      ‖coordDerivative 1 L c.toFun (0,p.2) (fun _ ↦ X p.1)‖^2 := by
  have hnorm (i : Fin n) : ‖a.orbital (X i)‖^2+‖c.orbital (X i)‖^2=1 := by
    rw [real_norm_sq (a.orbital (X i)) (ha (fun _ ↦ X i)),
      real_norm_sq (c.orbital (X i)) (hc (fun _ ↦ X i)),← Complex.add_re,hp,Complex.one_re]
  simp_rw [productPartition_partial,norm_mul,mul_pow,norm_prod,← Finset.prod_pow]
  exact binary_product_sum (fun i b ↦ ‖(cond b a c).orbital (X i)‖^2)
    (fun b ↦ ‖coordDerivative 1 L (cond b a c).toFun (0,p.2) (fun _ ↦ X p.1)‖^2) p.1 hnorm

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PartitionErrorIntegral
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partition_error_integral {S : Type*} [Fintype S] {n : ℕ} {L : Length}
    (w : S → SmoothMultiplier n L) (u : ScalarL2 n L) :
    (∑ p : Direction n, ∑ s, ‖(w s).derivativeScalar p u‖^2)=
      ∫ X, (∑ p : Direction n, ∑ s, ‖coordDerivative n L (w s).toFun p X‖^2)*‖u X‖^2 := by
  simp_rw [IndicatorStrong.norm_sq_integral]
  have hi (p : Direction n) (s : S) :
      Integrable (fun X ↦ ‖((w s).derivativeScalar p u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  simp_rw [← integral_finsetSum Finset.univ (fun s _ ↦ hi _ s)]
  rw [← integral_finsetSum Finset.univ (fun p _ ↦ integrable_finsetSum _ (fun s _ ↦ hi p s))]
  have hc : ∀ᵐ X ∂volume, ∀ p s, ((w s).derivativeScalar p u) X=
      coordDerivative n L (w s).toFun p X*u X :=
    ae_all_iff.mpr (fun p ↦ ae_all_iff.mpr (fun s ↦ (w s).coe_derivativeScalar p u))
  apply integral_congr_ae
  filter_upwards [hc] with X hX
  simp_rw [hX,norm_mul,mul_pow]
  simp only [Finset.sum_mul]

theorem productPartition_ims {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1) (u : Jet n L) :
    (∑ σ : Fin n → Bool, energy ((productPartition n L a c σ).onJet u))=
      energy u+∫ X, (∑ i : Fin n, ∑ j : Fin 3,
        (‖coordDerivative 1 L a.toFun (0,j) (fun _ ↦ X i)‖^2+
         ‖coordDerivative 1 L c.toFun (0,j) (fun _ ↦ X i)‖^2))*‖u.1 X‖^2 := by
  rw [SmoothMultiplier.partition_ims _ (productPartition_real a c ha hc)
    (productPartition_unity a c hp),SmoothMultiplier.partition_error_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun X ↦ by
    simp_rw [productPartition_gradient_partition a c ha hc hp]
    rw [Fintype.sum_prod_type]

lemma productPartition_norm_partition {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1) (u : ScalarL2 n L) :
    (∑ σ : Fin n → Bool, ‖(productPartition n L a c σ).onScalar u‖^2)=‖u‖^2 :=
  SmoothMultiplier.partition_scalar_norm _ (productPartition_real a c ha hc)
    (productPartition_unity a c hp) u

lemma binary_product_membership {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Bool → ℝ) (j : I) (hf : ∀ i, f i true+f i false=1) :
    (∑ σ : I → Bool, (if σ j then (1:ℝ) else 0)*(∏ i, f i (σ i)))=f j true := by
  have he (σ : I → Bool) : (if σ j then (1:ℝ) else 0)*(∏ i, f i (σ i))=
      (∏ i∈Finset.univ.erase j, f i (σ i))*(if σ j then f j true else 0) := by
    rw [← Finset.prod_erase_mul Finset.univ (fun i ↦ f i (σ i)) (Finset.mem_univ j)]
    cases σ j <;> simp
  simp_rw [he]
  simpa using binary_product_sum f (fun b ↦ if b then f j true else 0) j hf

lemma productPartition_selected_probability {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (X : Configuration n L) (i : Fin n) :
    (∑ σ : Fin n → Bool, (if σ i then (1:ℝ) else 0)*‖(productPartition n L a c σ).toFun X‖^2)=
      ‖a.orbital (X i)‖^2 := by
  simp_rw [productPartition_apply,norm_prod,← Finset.prod_pow]
  apply binary_product_membership (fun j b ↦ ‖(cond b a c).orbital (X j)‖^2) i
  intro j
  change ‖a.orbital (X j)‖^2+‖c.orbital (X j)‖^2=1
  rw [real_norm_sq (a.orbital (X j)) (ha (fun _ ↦ X j)),
    real_norm_sq (c.orbital (X j)) (hc (fun _ ↦ X j)),← Complex.add_re,hp,Complex.one_re]

theorem productPartition_removal_cost {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1) (u : ScalarL2 n L) :
    (∑ σ : Fin n → Bool, (∑ i : Fin n, if σ i then (1:ℝ) else 0)*
      ‖(productPartition n L a c σ).onScalar u‖^2)=
      ∫ X, (∑ i : Fin n, ‖a.orbital (X i)‖^2)*‖u X‖^2 := by
  simp_rw [IndicatorStrong.norm_sq_integral,← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun σ _ ↦
    ((Lp.memLp ((productPartition n L a c σ).onScalar u)).integrable_norm_pow (by norm_num)).const_mul _)]
  have hcoe : ∀ᵐ X ∂volume, ∀ σ, ((productPartition n L a c σ).onScalar u) X=
      (productPartition n L a c σ).toFun X*u X :=
    ae_all_iff.mpr (fun _ ↦ SmoothMultiplier.coe_onScalar _ _)
  apply integral_congr_ae
  filter_upwards [hcoe] with X hX
  simp_rw [hX,norm_mul,mul_pow,← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [productPartition_selected_probability a c ha hc hp]

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

lemma continuous_selectedEnergy {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] :
    Continuous (selectedEnergy (L:=L) p) :=
  continuous_finsetSum _ (fun i _ ↦ continuous_finsetSum _
    (fun q _ ↦ ((continuous_apply (i.val,q)).comp continuous_snd).norm.pow 2))

lemma selectedEnergy_all {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i, p i) (u : Jet n L) : selectedEnergy p u=energy u := by
  rw [selectedEnergy,energy,Fintype.sum_prod_type]
  exact Fintype.sum_equiv (selectedAllEquiv p hp) _ _ (fun _ ↦ rfl)

lemma SmoothTest.selected_slice_integrable {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (p : Fin n → Prop) [DecidablePred p] (j : Fin (n+1)) :
    Integrable (fun x : Torus L ↦ selectedEnergy p (f.slice j x).jet) volume :=
  integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun q _ ↦ f.slice_partial_integrable j (i.val,q)))

lemma SmoothTest.integral_selected_slice {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (p : Fin (n+1) → Prop) [DecidablePred p]
    (j : Fin (n+1)) (hj : ¬p j) :
    (∫ x : Torus L, selectedEnergy (fun i ↦ p (j.succAbove i)) (f.slice j x).jet)=selectedEnergy p f.jet := by
  simp only [selectedEnergy]
  rw [integral_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun q _ ↦ f.slice_partial_integrable j (i.val,q)))]
  simp_rw [integral_finsetSum _ (fun q _ ↦ f.slice_partial_integrable j (_,q)),
    f.integral_slice_partial]
  exact Fintype.sum_equiv (selectedDeleteEquiv p j hj) _ _ (fun _ ↦ rfl)

theorem selected_rayleigh (n : ℕ) :
    ∀ (k : ℕ) (L : Length) (a c : ℝ),
      (∀ v : Jet k L, v∈dirichletDomain k L a → c*‖v.1‖^2≤energy v) →
    ∀ (p : Fin n → Prop) [DecidablePred p], Fintype.card {i // p i}=k →
    ∀ u : Jet n L, u∈dirichletDomain n L a → c*‖u.1‖^2≤ selectedEnergy p u := by
  induction n with
  | zero =>
    intro k L a c h p _ hp u hu
    have hk : k=0 := by simpa using hp.symm
    rw [hk] at h
    simpa [selectedEnergy,energy,Direction] using h u hu
  | succ n ih =>
    intro k L a c h p _ hp u hu
    by_cases hall : ∀ i, p i
    · have hk : k=n+1 := by
        rw [←hp,Fintype.card_congr (selectedAllEquiv p hall),Fintype.card_fin]
      rw [hk] at h
      rw [selectedEnergy_all p hall]
      exact h u hu
    · obtain ⟨j,hj⟩ := not_forall.mp hall
      have hk : Fintype.card {i : Fin n // p (j.succAbove i)}=k :=
        (Fintype.card_congr (selectedDeleteEquiv p j hj)).trans hp
      have htest (f : SmoothTest (n+1) L a) : c*‖f.jet.1‖^2≤ selectedEnergy p f.jet := by
        have hh := integral_mono ((f.slice_norm_sq_integrable j).const_mul c)
          (f.selected_slice_integrable (fun i ↦ p (j.succAbove i)) j)
          (fun x ↦ ih k L a c h (fun i ↦ p (j.succAbove i)) hk
            (f.slice j x).jet (subset_closure ⟨f.slice j x,rfl⟩))
        rw [integral_const_mul,f.integral_slice_norm_sq,f.integral_selected_slice p j hj] at hh
        exact hh
      have hc : IsClosed {u : Jet (n+1) L | c*‖u.1‖^2≤ selectedEnergy p u} :=
        isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2)) (continuous_selectedEnergy p)
      exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact htest f) hu

theorem selected_ground_removal : ∃ C : ℝ, 0<C ∧
    ∀ (n : ℕ) (L : Length) (r : ℝ), 0 < r → (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (p : Fin n → Prop) [DecidablePred p],
    ∀ u : Jet n L, u∈dirichletDomain n L r →
      (energy g-C*((n-Fintype.card {i // p i}:ℕ):ℝ)*(n:ℝ)*r/L.val^3)*‖u.1‖^2≤ selectedEnergy p u := by
  obtain ⟨C,hC,hrem⟩ := ground_energy_removal
  refine ⟨C,hC,?_⟩
  intro n L r hr hs g hg p _ u hu
  let k := Fintype.card {i // p i}
  have hk : k≤n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun i : {i // p i} ↦ i.val) Subtype.val_injective
  have he : k+(n-k)=n := Nat.add_sub_of_le hk
  have h := hrem k (n-k) L r hr
  rw [he] at h
  exact selected_rayleigh n k L r _ (h hs g hg) p rfl u hu

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SelectedEnergyAddCompl
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma selectedEnergy_add_compl {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] (u : Jet n L) :
    selectedEnergy p u+selectedEnergy (fun i ↦ ¬p i) u=energy u := by
  rw [selectedEnergy,selectedEnergy,energy,Fintype.sum_prod_type]
  exact Fintype.sum_subtype_add_sum_subtype p (fun i ↦ ∑ j : Fin 3, ‖u.2 (i,j)‖^2)

lemma complement_removed_card {n : ℕ} (σ : Fin n → Bool) :
    ((n-Fintype.card {i : Fin n // ¬σ i=true} : ℕ):ℝ)=∑ i : Fin n, if σ i then (1:ℝ) else 0 := by
  have hc : Fintype.card {i : Fin n // σ i=true}≤n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun i : {i : Fin n // σ i=true} ↦ i.val) Subtype.val_injective
  rw [Fintype.card_subtype_compl,Fintype.card_fin,Nat.sub_sub_self hc,Fintype.card_subtype]
  symm
  simpa only [Finset.mem_univ,ite_true] using
    (Finset.sum_boole (R:=ℝ) (fun i : Fin n ↦ σ i=true) (Finset.univ : Finset (Fin n)))

theorem productPartition_spectral_localization : ∃ C : ℝ, 0<C ∧
    ∀ (n : ℕ) (L : Length) (r : ℝ), 0 < r → (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (a c : SmoothMultiplier 1 L),
      (∀ X, conj (a.toFun X)=a.toFun X) → (∀ X, conj (c.toFun X)=c.toFun X) →
      (∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1) →
    ∀ (u : Jet n L), u∈dirichletDomain n L r →
      (∑ σ : Fin n → Bool, selectedEnergy (fun i ↦ σ i=true) ((productPartition n L a c σ).onJet u))
        -C*(n:ℝ)*r/L.val^3*(∫ X, (∑ i : Fin n, ‖a.orbital (X i)‖^2)*‖u.1 X‖^2)
        -(∫ X, (∑ i : Fin n, ∑ j : Fin 3,
          (‖coordDerivative 1 L a.toFun (0,j) (fun _ ↦ X i)‖^2+
           ‖coordDerivative 1 L c.toFun (0,j) (fun _ ↦ X i)‖^2))*‖u.1 X‖^2)
        ≤energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,hC,hrem⟩ := selected_ground_removal
  refine ⟨C,hC,?_⟩
  intro n L r hr hs g hg a c ha hc hp u hu
  let K := C*(n:ℝ)*r/L.val^3
  have hσ (σ : Fin n → Bool) :
      selectedEnergy (fun i ↦ σ i=true) ((productPartition n L a c σ).onJet u)+
      energy g*‖(productPartition n L a c σ).onScalar u.1‖^2-
      K*((∑ i : Fin n, if σ i then (1:ℝ) else 0)*‖(productPartition n L a c σ).onScalar u.1‖^2)
        ≤energy ((productPartition n L a c σ).onJet u) := by
    have hh := hrem n L r hr hs g hg (fun i ↦ ¬σ i=true)
      ((productPartition n L a c σ).onJet u) ((productPartition n L a c σ).onJet_mem_domain hu)
    rw [complement_removed_card] at hh
    have he := selectedEnergy_add_compl (fun i ↦ σ i=true) ((productPartition n L a c σ).onJet u)
    change (energy g-C*(∑ i : Fin n, if σ i then (1:ℝ) else 0)*(n:ℝ)*r/L.val^3)*
      ‖(productPartition n L a c σ).onScalar u.1‖^2≤_ at hh
    have heq : C*(∑ i : Fin n, if σ i then (1:ℝ) else 0)*(n:ℝ)*r/L.val^3=
        K*(∑ i : Fin n, if σ i then (1:ℝ) else 0) := by dsimp [K]; ring
    rw [heq,sub_mul] at hh
    linarith only [hh,he]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Bool))) (fun σ _ ↦ hσ σ)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  rw [productPartition_norm_partition a c ha hc hp,productPartition_removal_cost a c ha hc hp,
    productPartition_ims a c ha hc hp] at hsum
  dsimp [K] at hsum
  linarith only [hsum]

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

lemma lipschitz_spatialProject (L : Length) : LipschitzWith 1 (spatialProject L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0≤dist x y)).mpr
  intro j
  calc
    dist ((x j : ℝ) : AddCircle L.val) ((y j : ℝ) : AddCircle L.val)
      = ‖((x j-y j : ℝ) : AddCircle L.val)‖ := by rw [dist_eq_norm,QuotientAddGroup.mk_sub]
    _ ≤ ‖x j-y j‖ := QuotientAddGroup.norm_mk_le_norm
    _ ≤ dist x y := by rw [←dist_eq_norm]; exact dist_le_pi_dist x y j

lemma torusMollify_integrable (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    (f : Torus L → ℝ) (hf : Continuous f) (x : Torus L) :
    Integrable (fun y : SpatialLift ↦ φ.normed volume y*f (x-spatialProject L y)) volume :=
  (φ.continuous_normed.mul (hf.comp (continuous_const.sub (continuous_spatialProject L)))).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.mul_right)

lemma torusMollify_lipschitz (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    {f : Torus L → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (torusMollify L φ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,torusMollify,torusMollify,← integral_sub
    (torusMollify_integrable L φ f hf.continuous x) (torusMollify_integrable L φ f hf.continuous y)]
  calc
    _ ≤ ∫ z : SpatialLift, φ.normed volume z*((C:ℝ)*dist x y) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) (Eventually.of_forall ?_)
      intro z
      rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa only [←dist_eq_norm,dist_sub_right] using hf.dist_le_mul
        (x-spatialProject L z) (y-spatialProject L z)
    _ = (C:ℝ)*dist x y := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma torusMollify_approximation (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    {f : Torus L → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (x : Torus L) :
    dist (torusMollify L φ f x) (f x) ≤ (C:ℝ)*φ.rOut := by
  obtain ⟨z,hz⟩ : ∃ z : SpatialLift, spatialProject L z=x := by
    refine ⟨fun j ↦ ((AddCircle.equivIco L.val 0) (x j)).val,?_⟩
    ext j
    exact AddCircle.coe_equivIco
  rw [← hz,show torusMollify L φ f (spatialProject L z)=
    (φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun y ↦ f (spatialProject L y))) z from congrFun (torusMollify_lift L φ f) z]
  apply φ.dist_normed_convolution_le (hf.continuous.comp (continuous_spatialProject L)).aestronglyMeasurable
  intro y hy
  have hh : dist (f (spatialProject L y)) (f (spatialProject L z)) ≤ (C:ℝ)*dist y z := by
    simpa only [mul_one,Function.comp_apply] using (hf.comp (lipschitz_spatialProject L)).dist_le_mul y z
  exact hh.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le C.coe_nonneg)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RealComp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.partial_realComp {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ)
    (hf : ∀ X, conj (f.toFun X)=f.toFun X) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (f.realComp φ hφ).toFun p X=
      ((deriv φ (f.toFun X).re : ℝ) : ℂ)*coordDerivative n L f.toFun p X := by
  let R := representative n L X
  let v : LiftedConfiguration n := Pi.single p.1 (Pi.single p.2 (1:ℝ))
  have hline : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hdf := (f.smooth.differentiable (by simp) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hdφ := (hφ.differentiable (by simp) (f.toFun (project n L R)).re).hasDerivAt
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hdf
  have hchain := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hdφ.comp_of_eq 0 hreal (by simp))
  have hnew := ((f.realComp φ hφ).smooth.differentiable (by simp) R).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have he := hnew.unique hchain
  change coordDerivative n L (f.realComp φ hφ).toFun p X = _ at he
  simp only [Complex.ofRealCLM_apply,Complex.reCLM_apply] at he
  rw [show project n L R=X from project_representative n L X] at he
  have hder : ((coordDerivative n L f.toFun p X).re : ℂ)=coordDerivative n L f.toFun p X := by
    apply Complex.ext
    · rfl
    · have h := congrArg Complex.im (f.partial_real hf p X)
      simp only [Complex.conj_im] at h
      simp only [Complex.ofReal_im]
      linarith
  change _ = ((deriv φ (f.toFun X).re * (coordDerivative n L f.toFun p X).re : ℝ) : ℂ) at he
  rw [Complex.ofReal_mul,hder] at he
  exact he

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Profile
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma profile_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : 2*h ≤ t) : profile h t=0 := by
  rw [profile,Real.smoothTransition.one_of_one_le (by have hd := (le_div_iff₀ hh).mpr ht; linarith)]
  ring

lemma profile_deriv (h t : ℝ) : deriv (profile h) t= -deriv Real.smoothTransition (t/h-1)/h := by
  have hd := (transition_derivative (t/h-1)).comp t (((hasDerivAt_id t).div_const h).sub_const 1)
  have he := hd.const_sub 1
  have heq : (fun x : ℝ ↦ 1 - (Real.smoothTransition ∘ fun x : ℝ ↦ id x / h - 1) x) = profile h := rfl
  rw [heq] at he
  rw [he.deriv]
  ring

lemma profile_deriv_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t∉Icc h (2*h)) :
    deriv (profile h) t=0 := by
  rw [profile_deriv,transition_deriv_eq_zero]
  · simp
  · intro hc
    apply ht
    constructor
    · have hd := hc.1
      have hv : 1 ≤ t/h := by linarith
      exact (one_le_div hh).mp hv
    · have hv : t/h ≤ 2 := by linarith [hc.2]
      exact (div_le_iff₀ hh).mp hv

lemma profile_deriv_bound {h M : ℝ} (hh : 0<h) (_hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (t : ℝ) :
    |deriv (profile h) t| ≤ M/h := by
  rw [profile_deriv,abs_div,abs_neg,abs_of_pos hh]
  exact div_le_div_of_nonneg_right (hb _) hh.le

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EuclideanTorus
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

lemma spatialMetricConstant_pos : 0<(spatialMetricConstant:ℝ) := by
  unfold spatialMetricConstant
  positivity

lemma spatialSiteDistance_nonneg (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    0≤ spatialSiteDistance L A x := Metric.infDist_nonneg

lemma smoothSpatialDistance_lipschitz (L : Length) (A : Finset (Torus L)) :
    LipschitzWith spatialMetricConstant (smoothSpatialDistance L A) :=
  torusMollify_lipschitz L _ (spatialSiteDistance_lipschitz L A)

lemma smoothSpatialDistance_approximation (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    |smoothSpatialDistance L A x-spatialSiteDistance L A x|≤1 := by
  apply (torusMollify_approximation L spatialDistanceBump (spatialSiteDistance_lipschitz L A) x).trans
  change (spatialMetricConstant:ℝ)*(1/((spatialMetricConstant:ℝ)+1))≤1
  rw [mul_one_div,(div_le_one (by positivity : 0<(spatialMetricConstant:ℝ)+1))]
  linarith

lemma spatialDistanceMultiplier_apply (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    (spatialDistanceMultiplier L A).toFun X=(smoothSpatialDistance L A (X 0):ℂ) := rfl

lemma spatialDistanceMultiplier_real (L : Length) (A : Finset (Torus L)) (X : Configuration 1 L) :
    conj ((spatialDistanceMultiplier L A).toFun X)=(spatialDistanceMultiplier L A).toFun X := by
  rw [spatialDistanceMultiplier_apply,Complex.conj_ofReal]

lemma spatialDistanceMultiplier_partial_bound (L : Length) (A : Finset (Torus L))
    (p : Direction 1) (X : Configuration 1 L) :
    ‖coordDerivative 1 L (spatialDistanceMultiplier L A).toFun p X‖≤ spatialMetricConstant := by
  have hLip : LipschitzWith spatialMetricConstant
      (fun Y : LiftedConfiguration 1 ↦ (spatialDistanceMultiplier L A).toFun (project 1 L Y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro Y Z
    change dist ((smoothSpatialDistance L A (spatialProject L (Y 0))):ℂ)
      ((smoothSpatialDistance L A (spatialProject L (Z 0))):ℂ)≤_
    rw [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,←Real.dist_eq]
    apply ((smoothSpatialDistance_lipschitz L A).dist_le_mul _ _).trans
    apply mul_le_mul_of_nonneg_left _ spatialMetricConstant.coe_nonneg
    exact ((lipschitz_spatialProject L).dist_le_mul (Y 0) (Z 0)).trans
      (by simpa using dist_le_pi_dist Y Z 0)
  unfold coordDerivative
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hv : ‖(Pi.single p.1 (Pi.single p.2 (1:ℝ)) : LiftedConfiguration 1)‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases hi : i=p.1
    · subst i
      simp only [Pi.single_eq_same]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro j
      by_cases hj : j=p.2
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj]
    · simp [Pi.single_eq_of_ne hi]
  exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by
    simpa only [mul_one] using norm_fderiv_le_of_lipschitz ℝ hLip)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma spatialAngle_hasDerivAt (H t : ℝ) :
    HasDerivAt (spatialAngle H) (Real.pi/2*deriv (CellOrbital.profile 1) (t-H)) t := by
  have hd := (((CellOrbital.profile_smooth 1).differentiable (by simp)) (t-H)).hasDerivAt
  convert (hd.comp t ((hasDerivAt_id t).sub_const H)).const_mul (Real.pi/2) using 1 <;>
    first | rfl | simp only [mul_one]

lemma spatialSine_deriv (H t : ℝ) : deriv (spatialSine H) t=
    Real.cos (spatialAngle H t)*(Real.pi/2*deriv (CellOrbital.profile 1) (t-H)) :=
  (spatialAngle_hasDerivAt H t).sin.deriv
lemma spatialCosine_deriv (H t : ℝ) : deriv (spatialCosine H) t=
    -Real.sin (spatialAngle H t)*(Real.pi/2*deriv (CellOrbital.profile 1) (t-H)) :=
  (spatialAngle_hasDerivAt H t).cos.deriv

lemma spatialInside_apply (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    (spatialInside L A H).toFun X=(spatialSine H (smoothSpatialDistance L A (X 0)):ℂ) := rfl
lemma spatialOutside_apply (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    (spatialOutside L A H).toFun X=(spatialCosine H (smoothSpatialDistance L A (X 0)):ℂ) := rfl
lemma spatialInside_real (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    conj ((spatialInside L A H).toFun X)=(spatialInside L A H).toFun X := by
  rw [spatialInside_apply,Complex.conj_ofReal]
lemma spatialOutside_real (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    conj ((spatialOutside L A H).toFun X)=(spatialOutside L A H).toFun X := by
  rw [spatialOutside_apply,Complex.conj_ofReal]

lemma spatialPartition_unity (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) :
    (spatialInside L A H).orbital x*(spatialInside L A H).orbital x+
      (spatialOutside L A H).orbital x*(spatialOutside L A H).orbital x=1 := by
  change (Real.sin (spatialAngle H (smoothSpatialDistance L A x)):ℂ)*
    (Real.sin (spatialAngle H (smoothSpatialDistance L A x)):ℂ)+
    (Real.cos (spatialAngle H (smoothSpatialDistance L A x)):ℂ)*
    (Real.cos (spatialAngle H (smoothSpatialDistance L A x)):ℂ)=1
  have h := Real.sin_sq_add_cos_sq (spatialAngle H (smoothSpatialDistance L A x))
  exact_mod_cast (show Real.sin (spatialAngle H (smoothSpatialDistance L A x))*
    Real.sin (spatialAngle H (smoothSpatialDistance L A x))+
    Real.cos (spatialAngle H (smoothSpatialDistance L A x))*Real.cos (spatialAngle H (smoothSpatialDistance L A x))=1 by nlinarith only [h])

lemma spatialInside_norm_le (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) :
    ‖(spatialInside L A H).orbital x‖≤1 := by
  change ‖(Real.sin (spatialAngle H (smoothSpatialDistance L A x)):ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

lemma spatialInside_zero (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L)
    (hx : H+3≤ spatialSiteDistance L A x) : (spatialInside L A H).orbital x=0 := by
  have hm := (abs_le.mp (smoothSpatialDistance_approximation L A x)).1
  have h : 2*1≤ smoothSpatialDistance L A x-H := by linarith
  change (Real.sin (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A x-H)):ℂ)=0
  rw [CellOrbital.profile_zero (by norm_num : (0:ℝ)<1) h,mul_zero,Real.sin_zero,Complex.ofReal_zero]

lemma spatialInside_partial (L : Length) (A : Finset (Torus L)) (H : ℝ)
    (p : Direction 1) (X : Configuration 1 L) :
    coordDerivative 1 L (spatialInside L A H).toFun p X=
      ((deriv (spatialSine H) (smoothSpatialDistance L A (X 0)):ℝ):ℂ)*
        coordDerivative 1 L (spatialDistanceMultiplier L A).toFun p X := by
  rw [spatialInside,SmoothMultiplier.partial_realComp _ _ _ (spatialDistanceMultiplier_real L A)]
  rfl
lemma spatialOutside_partial (L : Length) (A : Finset (Torus L)) (H : ℝ)
    (p : Direction 1) (X : Configuration 1 L) :
    coordDerivative 1 L (spatialOutside L A H).toFun p X=
      ((deriv (spatialCosine H) (smoothSpatialDistance L A (X 0)):ℝ):ℂ)*
        coordDerivative 1 L (spatialDistanceMultiplier L A).toFun p X := by
  rw [spatialOutside,SmoothMultiplier.partial_realComp _ _ _ (spatialDistanceMultiplier_real L A)]
  rfl

lemma spatialPartition_partial_zero (L : Length) (A : Finset (Torus L)) (H : ℝ)
    (p : Direction 1) (X : Configuration 1 L) (hx : H+3 < spatialSiteDistance L A (X 0)) :
    coordDerivative 1 L (spatialInside L A H).toFun p X=0 ∧
      coordDerivative 1 L (spatialOutside L A H).toFun p X=0 := by
  have hm := (abs_le.mp (smoothSpatialDistance_approximation L A (X 0))).1
  have hz : deriv (CellOrbital.profile 1) (smoothSpatialDistance L A (X 0)-H)=0 :=
    CellOrbital.profile_deriv_zero (by norm_num) (by intro hh; have := hh.2; linarith)
  rw [spatialInside_partial,spatialOutside_partial,spatialSine_deriv,spatialCosine_deriv,hz]
  simp

theorem spatialPartition_partial_bound : ∃ B : ℝ, 0<B ∧
    ∀ (L : Length) (A : Finset (Torus L)) (H : ℝ) (p : Direction 1) (X : Configuration 1 L),
      ‖coordDerivative 1 L (spatialInside L A H).toFun p X‖≤B ∧
      ‖coordDerivative 1 L (spatialOutside L A H).toFun p X‖≤B := by
  obtain ⟨M,hM,hb⟩ := PeriodicCutoff.exists_transition_bound
  let B := Real.pi/2*M*(spatialMetricConstant:ℝ)
  refine ⟨B,by dsimp [B]; exact mul_pos (mul_pos (div_pos Real.pi_pos (by norm_num)) hM) spatialMetricConstant_pos,?_⟩
  intro L A H p X
  have ht := CellOrbital.profile_deriv_bound (h:=1) (by norm_num) hM.le hb (smoothSpatialDistance L A (X 0)-H)
  simp only [div_one] at ht
  have hd := spatialDistanceMultiplier_partial_bound L A p X
  have hs : |deriv (spatialSine H) (smoothSpatialDistance L A (X 0))|≤Real.pi/2*M := by
    rw [spatialSine_deriv,abs_mul,abs_mul,abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (mul_nonneg (by positivity) (abs_nonneg _))).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_left ht (by positivity : 0≤Real.pi/2))
  have hc : |deriv (spatialCosine H) (smoothSpatialDistance L A (X 0))|≤Real.pi/2*M := by
    rw [spatialCosine_deriv,abs_mul,abs_neg,abs_mul,abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (mul_nonneg (by positivity) (abs_nonneg _))).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_left ht (by positivity : 0≤Real.pi/2))
  rw [spatialInside_partial,spatialOutside_partial,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  exact ⟨mul_le_mul hs hd (norm_nonneg _) (by positivity),mul_le_mul hc hd (norm_nonneg _) (by positivity)⟩

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadiusLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory

lemma radiusLaw_tail_eq {t : ℝ} (ht : 0≤t) : radiusLaw.real (Ici t)=Real.exp (-t) := by
  have h := measureReal_compl (μ:=radiusLaw) (s:=Iic t) measurableSet_Iic
  rw [compl_Iic,probReal_univ,←cdf_eq_real,radiusLaw,cdf_expMeasure_eq (by norm_num),ite_eq_left ht,one_mul] at h
  have he : radiusLaw.real (Ici t)=radiusLaw.real (Ioi t) := by
    unfold Measure.real
    rw [measure_congr (Ioi_ae_eq_Ici (μ:=radiusLaw) (a:=t))]
  rw [he]
  change (expMeasure 1).real (Ioi t)=_
  rw [h]
  ring

lemma radiusLaw_tail (t : ℝ) : radiusLaw.real (Ici t)≤Real.exp (-t) := by
  by_cases ht : 0≤t
  · exact (radiusLaw_tail_eq ht).le
  · calc
      _ ≤ radiusLaw.real univ := measureReal_mono (subset_univ _)
      _ = 1 := probReal_univ
      _ ≤ Real.exp (-t) := Real.one_le_exp (by linarith)

lemma radius_integral_bound {f : ℝ → ℝ} {B d : ℝ} (hB : 0≤B)
    (hf : Measurable f) (hn : ∀ H, 0≤f H) (hb : ∀ H, f H≤B)
    (hz : ∀ H, H+3<d → f H=0) :
    Integrable f radiusLaw ∧ (∫ H, f H ∂radiusLaw)≤B*Real.exp 3*Real.exp (-d) := by
  have hi : Integrable f radiusLaw := (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun H ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hn H)]; exact hb H))
  refine ⟨hi,?_⟩
  have hdom (H : ℝ) : f H≤(Ici (d-3)).indicator (fun _ ↦ B) H := by
    by_cases hm : H∈Ici (d-3)
    · rw [Set.indicator_of_mem hm]; exact hb H
    · rw [Set.indicator_of_notMem hm,hz H (by have hnot : ¬ d-3≤H := hm; have := lt_of_not_ge hnot; linarith)]
  have hh := integral_mono hi ((integrable_const B).indicator measurableSet_Ici) hdom
  rw [integral_indicator_const _ measurableSet_Ici,smul_eq_mul] at hh
  apply hh.trans
  calc
    radiusLaw.real (Ici (d-3))*B ≤ Real.exp (-(d-3))*B := mul_le_mul_of_nonneg_right (radiusLaw_tail _) hB
    _ = B*Real.exp 3*Real.exp (-d) := by rw [show -(d-3)=3+(-d) by ring,Real.exp_add]; ring

lemma spatialSine_deriv_continuous_radius (t : ℝ) : Continuous (fun H ↦ deriv (spatialSine H) t) := by
  simp_rw [spatialSine_deriv,spatialAngle]
  have hp := (CellOrbital.profile_smooth 1).continuous
  have hd := (CellOrbital.profile_smooth 1).continuous_deriv (by simp)
  exact (Real.continuous_cos.comp (continuous_const.mul (hp.comp (continuous_const.sub continuous_id)))).mul
    (continuous_const.mul (hd.comp (continuous_const.sub continuous_id)))

lemma spatialCosine_deriv_continuous_radius (t : ℝ) : Continuous (fun H ↦ deriv (spatialCosine H) t) := by
  simp_rw [spatialCosine_deriv,spatialAngle]
  have hp := (CellOrbital.profile_smooth 1).continuous
  have hd := (CellOrbital.profile_smooth 1).continuous_deriv (by simp)
  exact (Real.continuous_sin.comp (continuous_const.mul (hp.comp (continuous_const.sub continuous_id)))).neg.mul
    (continuous_const.mul (hd.comp (continuous_const.sub continuous_id)))

lemma spatialEnergyError_nonneg (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) :
    0≤ spatialEnergyError L A H x := Finset.sum_nonneg (fun _ _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma spatialEnergyError_continuous_radius (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    Continuous (fun H ↦ spatialEnergyError L A H x) := by
  unfold spatialEnergyError
  apply continuous_finsetSum
  intro j _
  simp_rw [spatialInside_partial,spatialOutside_partial]
  exact ((Complex.continuous_ofReal.comp (spatialSine_deriv_continuous_radius _)).mul continuous_const).norm.pow 2 |>.add
    (((Complex.continuous_ofReal.comp (spatialCosine_deriv_continuous_radius _)).mul continuous_const).norm.pow 2)

lemma spatialInside_average (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    Integrable (fun H ↦ ‖(spatialInside L A H).orbital x‖^2) radiusLaw ∧
    (∫ H, ‖(spatialInside L A H).orbital x‖^2 ∂radiusLaw)≤Real.exp 3*Real.exp (-spatialSiteDistance L A x) := by
  have hmeas : Measurable (fun H ↦ ‖(spatialInside L A H).orbital x‖^2) := by
    change Measurable (fun H ↦ ‖(Real.sin (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A x-H)):ℂ)‖^2)
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_const.mul ((CellOrbital.profile_smooth 1).continuous.comp
      (continuous_const.sub continuous_id))))).norm.pow 2 |>.measurable
  simpa only [one_mul] using radius_integral_bound (B:=1) (d:=spatialSiteDistance L A x) (by norm_num) hmeas
    (fun H ↦ sq_nonneg _) (fun H ↦ by nlinarith only [spatialInside_norm_le L A H x,norm_nonneg ((spatialInside L A H).orbital x)])
    (fun H hH ↦ by rw [spatialInside_zero L A H x hH.le]; simp)

theorem spatialEnergyError_average : ∃ C : ℝ, 0<C ∧
    ∀ (L : Length) (A : Finset (Torus L)) (x : Torus L),
      Integrable (fun H ↦ spatialEnergyError L A H x) radiusLaw ∧
      (∫ H, spatialEnergyError L A H x ∂radiusLaw)≤C*Real.exp (-spatialSiteDistance L A x) := by
  obtain ⟨B,hB,hbound⟩ := spatialPartition_partial_bound
  refine ⟨6*B^2*Real.exp 3,by positivity,?_⟩
  intro L A x
  apply radius_integral_bound (by positivity) (spatialEnergyError_continuous_radius L A x).measurable
    (fun H ↦ spatialEnergyError_nonneg L A H x)
  · intro H
    calc
      _ ≤ ∑ j : Fin 3, (2*B^2) := by
        apply Finset.sum_le_sum
        intro j _
        obtain ⟨h1,h2⟩ := hbound L A H (0,j) (fun _ ↦ x)
        nlinarith only [sq_le_sq₀ (norm_nonneg _) hB.le |>.mpr h1,
          sq_le_sq₀ (norm_nonneg _) hB.le |>.mpr h2]
      _ = 6*B^2 := by simp; ring
  · intro H hH
    unfold spatialEnergyError
    apply Finset.sum_eq_zero
    intro j _
    obtain ⟨h1,h2⟩ := spatialPartition_partial_zero L A H (0,j) (fun _ ↦ x) hH
    rw [h1,h2]; simp

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

lemma L2_bounded_weight_integrable {n : ℕ} {L : Length} (u : ScalarL2 n L)
    {v : Configuration n L → ℝ} {B : ℝ} (hv : Measurable v) (hb : ∀ X, |v X|≤B) :
    Integrable (fun X ↦ v X*‖u X‖^2) volume := by
  have hi := ((Lp.memLp u).integrable_norm_pow (by norm_num)).const_mul B
  apply hi.mono' (hv.mul ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2)).aestronglyMeasurable
  exact Eventually.of_forall fun X ↦ by
    change ‖v X*‖u X‖^2‖≤B*‖u X‖^2
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u X‖)]
    exact mul_le_mul_of_nonneg_right (hb X) (sq_nonneg _)

lemma radius_configuration_bound {n : ℕ} {L : Length} (u : ScalarL2 n L)
    {f : ℝ → Configuration n L → ℝ} {B M : ℝ} {v : Configuration n L → ℝ}
    (hf : Measurable (Function.uncurry f)) (hb : ∀ H X, |f H X|≤B)
    (hv : Measurable v) (hM : ∀ X, |v X|≤M)
    (havg : ∀ X, (∫ H, f H X ∂radiusLaw)≤v X) :
    Integrable (fun H ↦ ∫ X, f H X*‖u X‖^2) radiusLaw ∧
    (∫ H, (∫ X, f H X*‖u X‖^2) ∂radiusLaw)≤∫ X, v X*‖u X‖^2 := by
  have hd := ((Lp.memLp u).integrable_norm_pow (by norm_num)).comp_snd radiusLaw
  have hprod : Integrable (fun z : ℝ×Configuration n L ↦ f z.1 z.2*‖u z.2‖^2) (radiusLaw.prod volume) := by
    apply (hd.const_mul B).mono'
      (hf.mul (((Lp.stronglyMeasurable u).measurable.comp measurable_snd).norm.pow_const 2)).aestronglyMeasurable
    exact Eventually.of_forall fun z ↦ by
      change ‖f z.1 z.2*‖u z.2‖^2‖≤B*‖u z.2‖^2
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u z.2‖)]
      exact mul_le_mul_of_nonneg_right (hb z.1 z.2) (sq_nonneg _)
  refine ⟨hprod.integral_prod_left,?_⟩
  rw [integral_integral_swap hprod]
  apply integral_mono hprod.integral_prod_right (L2_bounded_weight_integrable u hv hM)
  intro X
  change (∫ H, f H X*‖u X‖^2 ∂radiusLaw)≤v X*‖u X‖^2
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (havg X) (sq_nonneg _)

lemma spatialInside_joint_continuous (L : Length) (A : Finset (Torus L)) :
    Continuous (fun z : ℝ×Torus L ↦ (spatialInside L A z.1).orbital z.2) := by
  change Continuous (fun z : ℝ×Torus L ↦
    (Real.sin (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A z.2-z.1)):ℂ))
  exact Complex.continuous_ofReal.comp (Real.continuous_sin.comp
    (continuous_const.mul ((CellOrbital.profile_smooth 1).continuous.comp
      (((smoothSpatialDistance_lipschitz L A).continuous.comp continuous_snd).sub continuous_fst))))

lemma spatialEnergyError_joint_continuous (L : Length) (A : Finset (Torus L)) :
    Continuous (fun z : ℝ×Torus L ↦ spatialEnergyError L A z.1 z.2) := by
  unfold spatialEnergyError
  apply continuous_finsetSum
  intro j _
  simp_rw [spatialInside_partial,spatialOutside_partial,spatialSine_deriv,spatialCosine_deriv,spatialAngle]
  have hh : Continuous (fun z : ℝ×Torus L ↦ smoothSpatialDistance L A z.2-z.1) :=
    ((smoothSpatialDistance_lipschitz L A).continuous.comp continuous_snd).sub continuous_fst
  have hp := (CellOrbital.profile_smooth 1).continuous.comp hh
  have hd := ((CellOrbital.profile_smooth 1).continuous_deriv (by simp)).comp hh
  have hc : Continuous (fun z : ℝ×Torus L ↦ coordDerivative 1 L (spatialDistanceMultiplier L A).toFun (0,j) (fun _ ↦ z.2)) :=
    (continuous_coordDerivative (spatialDistanceMultiplier L A).smooth (0,j)).comp (continuous_pi fun _ ↦ continuous_snd)
  exact ((Complex.continuous_ofReal.comp ((Real.continuous_cos.comp (continuous_const.mul hp)).mul
    (continuous_const.mul hd))).mul hc).norm.pow 2 |>.add
    (((Complex.continuous_ofReal.comp ((Real.continuous_sin.comp (continuous_const.mul hp)).neg.mul
    (continuous_const.mul hd))).mul hc).norm.pow 2)

lemma weightedSiteCount_nonneg {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    0≤ weightedSiteCount L A X := by
  unfold weightedSiteCount
  split_ifs <;> positivity

lemma weightedSiteCount_le {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    weightedSiteCount L A X≤(n:ℝ) := by
  unfold weightedSiteCount
  split_ifs
  · calc
      _ ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum (fun i _ ↦ Real.exp_le_one_iff.mpr (neg_nonpos.mpr (spatialSiteDistance_nonneg L A _)))
      _ = _ := by simp
  · positivity

lemma weightedSiteCount_continuous {n : ℕ} (L : Length) (A : Finset (Torus L)) :
    Continuous (weightedSiteCount (n:=n) L A) := by
  unfold weightedSiteCount
  split_ifs
  · exact continuous_finsetSum _ (fun i _ ↦ Real.continuous_exp.comp
      (((spatialSiteDistance_lipschitz L A).continuous.comp (continuous_apply i)).neg))
  · exact continuous_const

lemma spatialInside_configuration_average {n : ℕ} (L : Length) (A : Finset (Torus L))
    (hA : A.Nonempty) (u : ScalarL2 n L) :
    Integrable (fun H ↦ ∫ X, (∑ i : Fin n, ‖(spatialInside L A H).orbital (X i)‖^2)*‖u X‖^2) radiusLaw ∧
    (∫ H, (∫ X, (∑ i : Fin n, ‖(spatialInside L A H).orbital (X i)‖^2)*‖u X‖^2) ∂radiusLaw)≤
      Real.exp 3*(∫ X, weightedSiteCount L A X*‖u X‖^2) := by
  rw [← integral_const_mul]
  simp_rw [← mul_assoc]
  apply radius_configuration_bound u (B:=(n:ℝ)) (M:=Real.exp 3*(n:ℝ))
  · exact (continuous_finsetSum _ (fun i _ ↦ ((spatialInside_joint_continuous L A).comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))).norm.pow 2)).measurable
  · intro H X
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
    calc
      _ ≤ ∑ _i : Fin n, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith only [spatialInside_norm_le L A H (X i),norm_nonneg ((spatialInside L A H).orbital (X i))]
      _ = _ := by simp
  · exact (continuous_const.mul (weightedSiteCount_continuous L A)).measurable
  · intro X
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (weightedSiteCount_nonneg L A X))]
    exact mul_le_mul_of_nonneg_left (weightedSiteCount_le L A X) (Real.exp_pos _).le
  · intro X
    rw [integral_finsetSum Finset.univ (fun i _ ↦ (spatialInside_average L A (X i)).1),weightedSiteCount,ite_eq_left hA,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ (spatialInside_average L A (X i)).2)

theorem spatialEnergyError_configuration_average : ∃ C : ℝ, 0<C ∧
    ∀ (n : ℕ) (L : Length) (A : Finset (Torus L)), A.Nonempty → ∀ (u : ScalarL2 n L),
    Integrable (fun H ↦ ∫ X, (∑ i : Fin n, spatialEnergyError L A H (X i))*‖u X‖^2) radiusLaw ∧
    (∫ H, (∫ X, (∑ i : Fin n, spatialEnergyError L A H (X i))*‖u X‖^2) ∂radiusLaw)≤
      C*(∫ X, weightedSiteCount L A X*‖u X‖^2) := by
  obtain ⟨C,hC,havg⟩ := spatialEnergyError_average
  obtain ⟨B,hB,hbound⟩ := spatialPartition_partial_bound
  refine ⟨C,hC,?_⟩
  intro n L A hA u
  rw [← integral_const_mul]
  simp_rw [← mul_assoc]
  apply radius_configuration_bound u (B:=(n:ℝ)*6*B^2) (M:=C*(n:ℝ))
  · exact (continuous_finsetSum _ (fun i _ ↦ (spatialEnergyError_joint_continuous L A).comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))).measurable
  · intro H X
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ ↦ spatialEnergyError_nonneg L A H (X i)))]
    calc
      _ ≤ ∑ _i : Fin n, 6*B^2 := by
        apply Finset.sum_le_sum
        intro i _
        unfold spatialEnergyError
        calc
          _ ≤ ∑ j : Fin 3, 2*B^2 := by
            apply Finset.sum_le_sum
            intro j _
            obtain ⟨h1,h2⟩ := hbound L A H (0,j) (fun _ ↦ X i)
            nlinarith only [sq_le_sq₀ (norm_nonneg _) hB.le |>.mpr h1,
              sq_le_sq₀ (norm_nonneg _) hB.le |>.mpr h2]
          _ = _ := by simp; ring
      _ = _ := by simp; ring
  · exact (continuous_const.mul (weightedSiteCount_continuous L A)).measurable
  · intro X
    rw [abs_of_nonneg (mul_nonneg hC.le (weightedSiteCount_nonneg L A X))]
    exact mul_le_mul_of_nonneg_left (weightedSiteCount_le L A X) hC.le
  · intro X
    rw [integral_finsetSum Finset.univ (fun i _ ↦ (havg L A (X i)).1),weightedSiteCount,ite_eq_left hA,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ (havg L A (X i)).2)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SpatialPartitionEnergy
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ENNReal

lemma spatialPartitionEnergy_nonneg {n : ℕ} (L : Length) (A : Finset (Torus L)) (H : ℝ) (u : Jet n L) :
    0≤ spatialPartitionEnergy L A H u := by
  unfold spatialPartitionEnergy selectedEnergy
  exact Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))

theorem spatial_spectral_average_oai : ∃ C D : ℝ, 0<C ∧ 0<D ∧
    ∀ (n : ℕ) (L : Length) (r : ℝ), 0 < r → (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), A.Nonempty → ∀ (u : Jet n L), u∈dirichletDomain n L r →
    (∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw)≤
      ENNReal.ofReal (energy u-energy g*‖u.1‖^2+
        (C*(n:ℝ)*r/L.val^3+D)*(∫ X, weightedSiteCount L A X*‖u.1 X‖^2)) := by
  obtain ⟨K,hK,hloc⟩ := productPartition_spectral_localization
  obtain ⟨D,hD,herr⟩ := spatialEnergyError_configuration_average
  refine ⟨K*Real.exp 3,D,mul_pos hK (Real.exp_pos _),hD,?_⟩
  intro n L r hr hs g hg A hA u hu
  let R : ℝ → ℝ := fun H ↦ ∫ X, (∑ i : Fin n, ‖(spatialInside L A H).orbital (X i)‖^2)*‖u.1 X‖^2
  let E : ℝ → ℝ := fun H ↦ ∫ X, (∑ i : Fin n, spatialEnergyError L A H (X i))*‖u.1 X‖^2
  let c := K*(n:ℝ)*r/L.val^3
  let F : ℝ → ℝ := fun H ↦ energy u-energy g*‖u.1‖^2+c*R H+E H
  obtain ⟨hRi,hRb⟩ := spatialInside_configuration_average L A hA u.1
  obtain ⟨hEi,hEb⟩ := herr n L A hA u.1
  change Integrable R radiusLaw at hRi
  change Integrable E radiusLaw at hEi
  have hFi : Integrable F radiusLaw := ((integrable_const _).add (hRi.const_mul c)).add hEi
  have hpoint (H : ℝ) : spatialPartitionEnergy L A H u≤ F H := by
    have h := hloc n L r hr hs g hg (spatialInside L A H) (spatialOutside L A H)
      (spatialInside_real L A H) (spatialOutside_real L A H) (spatialPartition_unity L A H) u hu
    change spatialPartitionEnergy L A H u-c*R H-E H≤energy u-energy g*‖u.1‖^2 at h
    dsimp [F]
    linarith only [h]
  have hFn (H : ℝ) : 0≤F H := (spatialPartitionEnergy_nonneg L A H u).trans (hpoint H)
  calc
    _ ≤ ∫⁻ H, ENNReal.ofReal (F H) ∂radiusLaw :=
      lintegral_mono (fun H ↦ ENNReal.ofReal_le_ofReal (hpoint H))
    _ = ENNReal.ofReal (∫ H, F H ∂radiusLaw) :=
      (ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hFn)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      change (∫ H, energy u-energy g*‖u.1‖^2+c*R H+E H ∂radiusLaw)≤_
      have hCi : Integrable (fun _ : ℝ ↦ energy u-energy g*‖u.1‖^2) radiusLaw := integrable_const _
      have hCRi : Integrable (fun H ↦ energy u-energy g*‖u.1‖^2+c*R H) radiusLaw := hCi.add (hRi.const_mul c)
      rw [integral_add hCRi hEi,integral_add hCi (hRi.const_mul c),integral_const_mul,integral_const]
      simp only [probReal_univ,one_smul]
      have hc : 0 ≤ c := div_nonneg (mul_nonneg (mul_nonneg hK.le (Nat.cast_nonneg _)) hr.le) (pow_nonneg L.property.le _)
      have hRb' := mul_le_mul_of_nonneg_left hRb hc
      change c*(∫ H,R H ∂radiusLaw) ≤ c*(Real.exp 3*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2)) at hRb'
      change (∫ H,E H ∂radiusLaw)≤D*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2) at hEb
      have he : c*(Real.exp 3*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2))+
          D*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2)=
          (K*Real.exp 3*(n:ℝ)*r/L.val^3+D)*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2) := by dsimp [c]; ring
      linarith only [hRb',hEb,he]

end HardSphere

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.spatial_spectral_average_oai := @OAI.HardSphere.spatial_spectral_average_oai
