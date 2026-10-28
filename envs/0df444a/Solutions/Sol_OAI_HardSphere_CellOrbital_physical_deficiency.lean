-- Prove2me | solution 1 for OAI.HardSphere.CellOrbital.physical_deficiency
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:02:46.096098+00:00
-- url     : https://prove2.me/submissions/db3e3736-edb7-4e34-8ce7-08077465ac5b

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

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

lemma continuous_coordinateLine {N : ℕ} {L : Length}
    (X : Configuration N L) (p : Direction N) : Continuous (coordinateLine X p) := by
  unfold coordinateLine
  apply Continuous.add continuous_const
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hi : i = p.1 <;> by_cases hj : j = p.2 <;>
    simp only [Pi.single_apply, hi, hj, ↓reduceIte]
  · exact continuous_id
  all_goals exact continuous_const

open scoped ComplexConjugate

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_IntegralConfigurationCons
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

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusLiftBox
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
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

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
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_SafeMass
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

lemma safeMass_eq {z : ℝ} (hz : 1/2≤z) : safeMass z=z := by
  rw [safeMass,Real.smoothTransition.zero_of_nonpos (by linarith),add_zero]

lemma SmoothMultiplier.localNormalization_real {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (X) :
    conj ((f.localNormalization hr).toFun X)=(f.localNormalization hr).toFun X := by
  change conj (f.toFun X/(Real.sqrt (safeMass (f.fiberMass (Fin.tail X))) : ℂ))=_
  rw [map_div₀,Complex.conj_ofReal,hr]
  rfl

lemma SmoothMultiplier.localNormalization_mass {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (Y : Configuration n L) :
    (f.localNormalization hr).fiberMass Y=f.fiberMass Y/safeMass (f.fiberMass Y) := by
  change (∫ x : Torus L, ‖f.toFun (Fin.cons x Y)/(Real.sqrt (safeMass (f.fiberMass Y)) : ℂ)‖^2)=_
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),div_pow,Real.sq_sqrt (safeMass_pos (f.fiberMass_nonneg Y)).le]
  exact integral_div _ _

lemma SmoothMultiplier.localNormalization_mass_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (Y : Configuration n L) :
    (f.localNormalization hr).fiberMass Y≤1 := by
  rw [f.localNormalization_mass hr,div_le_one (safeMass_pos (f.fiberMass_nonneg Y))]
  exact safeMass_ge _

lemma SmoothMultiplier.localNormalization_mass_eq {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (Y : Configuration n L)
    (hY : 1/2≤f.fiberMass Y) : (f.localNormalization hr).fiberMass Y=1 := by
  rw [f.localNormalization_mass hr,safeMass_eq hY]
  exact div_self (by linarith)

lemma SmoothMultiplier.localNormalization_clearance {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (hc : InsertionClearance a f) : InsertionClearance a (f.localNormalization hr) := by
  apply Set.Subset.trans (b := tsupport f.toFun) _ hc
  change tsupport (fun X ↦ f.toFun X/(Real.sqrt (safeMass (f.fiberMass (Fin.tail X))) : ℂ))⊆_
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

lemma SmoothMultiplier.insertion_orthogonal_local {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (i : Fin n) (j : Fin 3) (Y : Configuration n L)
    (hn : ∀ᶠ Z in 𝓝 Y, f.fiberMass Z=1) :
    ∫ x : Torus L, conj (f.toFun (Fin.cons x Y))*
      coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0 := by
  have he (X) : f.toFun X*f.toFun X = ((‖f.toFun X‖^2 : ℝ) : ℂ) := by
    calc
      _ = f.toFun X*conj (f.toFun X) := by rw [hr]
      _ = _ := by rw [Complex.mul_conj,Complex.sq_norm]
  have hc : ∀ᶠ Z in 𝓝 Y, (∫ x : Torus L, (f.mul f).toFun (Fin.cons x Z))=1 := by
    filter_upwards [hn] with Z hZ
    simp only [SmoothMultiplier.mul,Pi.mul_apply,he]
    rw [integral_complex_ofReal]
    change ((f.fiberMass Z : ℝ) : ℂ)=1
    rw [hZ,Complex.ofReal_one]
  have ht : Tendsto (fun t : ℝ ↦ coordinateLine Y (i,j) (t : AddCircle L.val)) (𝓝 0) (𝓝 Y) := by
    have cc : Continuous (fun t : ℝ ↦ coordinateLine Y (i,j) (t : AddCircle L.val)) :=
      (continuous_coordinateLine Y (i,j)).comp (AddCircle.continuous_mk' L.val)
    simpa only [AddCircle.coe_zero,coordinateLine,Pi.single_zero,add_zero] using cc.tendsto (0:ℝ)
  have h := (f.mul f).hasDerivAt_fiberIntegral Y i j
  have hz := h.unique ((hasDerivAt_const (0:ℝ) (1:ℂ)).congr_of_eventuallyEq (ht.eventually hc))
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

lemma SmoothMultiplier.localNormalization_mass_eventually {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X) (Y : Configuration n L)
    (hY : 1/2<f.fiberMass Y) : ∀ᶠ Z in 𝓝 Y, (f.localNormalization hr).fiberMass Z=1 := by
  have hc := continuous_of_continuous_lift (f.smooth_fiberMass hr).continuous
  filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds hY)] with Z hZ
  exact f.localNormalization_mass_eq hr Z hZ.le

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_FiberDerivativeMulTailLocal
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

lemma SmoothMultiplier.fiber_derivative_mul_tail_le_local {n : ℕ} {L : Length}
    (g : SmoothMultiplier (n+1) L) (r : SmoothMultiplier n L)
    (hr : ∀ X, conj (g.toFun X)=g.toFun X)
    (p : Direction (n+1)) (Y : Configuration n L)
    (hn : ∀ᶠ Z in 𝓝 Y, g.fiberMass Z=1) :
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
    have he := g.insertion_orthogonal_local hr k j Y hn
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

lemma SmoothMultiplier.localNormalization_derivative_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (p : Direction (n+1)) (Y : Configuration n L) (hY : 1/2<f.fiberMass Y) :
    f.fiberMass Y * (∫ x : Torus L,
      ‖coordDerivative (n+1) L (f.localNormalization hr).toFun p (Fin.cons x Y)‖^2) ≤
      ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
  have he : (fun X ↦ (f.localNormalization hr).toFun X *
      (f.safeRoot hr).toFun (Fin.tail X))=f.toFun := by
    funext X
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (safeMass_pos (f.fiberMass_nonneg _))).ne')
  have hh := (f.localNormalization hr).fiber_derivative_mul_tail_le_local (f.safeRoot hr)
    (f.localNormalization_real hr) p Y (f.localNormalization_mass_eventually hr Y hY)
  rw [he] at hh
  have hn : ‖(f.safeRoot hr).toFun Y‖^2=f.fiberMass Y := by
    change ‖(Real.sqrt (safeMass (f.fiberMass Y)) : ℂ)‖^2=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (safeMass_pos (f.fiberMass_nonneg _)).le,safeMass_eq hY.le]
  rwa [hn] at hh

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_InsertionMassIntegrable
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

lemma SmoothMultiplier.insertion_mass_integrable {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L) :
    Integrable (fun Y : Configuration n L ↦ ‖u Y‖^2 * f.fiberMass Y) volume := by
  have hm := ((memLp_configurationTail (Lp.memLp u)).mul f.memLp_top).integrable_norm_pow
    (by decide : (2:ℕ)≠0)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hm
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_zero',Function.comp_def,Pi.mul_apply,Fin.tail_cons] at hi
  convert hi.integral_prod_right using 1
  all_goals try with_reducible_and_instances rfl
  funext Y
  rw [SmoothMultiplier.fiberMass,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by dsimp only; rw [norm_mul,mul_pow,mul_comm]

lemma SmoothMultiplier.norm_insertionScalar_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hn : ∀ Y, f.fiberMass Y≤1) (u : ScalarL2 n L) :
    ‖f.insertionScalar u‖^2≤‖u‖^2 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    norm_weightedTail_sq,IndicatorStrong.norm_sq_integral]
  exact integral_mono (f.insertion_mass_integrable u)
    ((Lp.memLp u).integrable_norm_pow (by decide : (2:ℕ)≠0))
    (fun Y ↦ mul_le_of_le_one_right (sq_nonneg _) (hn Y))

lemma SmoothMultiplier.norm_insertionScalar_local {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L)
    (hn : ∀ᵐ Y ∂volume, u Y≠0 → f.fiberMass Y=1) :
    ‖f.insertionScalar u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    norm_weightedTail_sq,IndicatorStrong.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hn] with Y hY
  by_cases hz : u Y=0
  · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),zero_mul]
  · change ‖u Y‖^2*f.fiberMass Y=_
    rw [hY hz,mul_one]

lemma SmoothMultiplier.insertion_cross_zero_local {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (p : Direction (n+1)) (u v : ScalarL2 n L)
    (ho : ∀ᵐ Y ∂volume, v Y≠0 → ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun p (Fin.cons x Y)=0) :
    inner ℂ (f.insertionScalar u)
      (L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L v))=0 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    weightedTail_pairing]
  apply integral_eq_zero_of_ae
  filter_upwards [ho] with Y hY
  simp only [Pi.zero_apply]
  by_cases hz : v Y=0
  · rw [hz,mul_zero,zero_mul]
  · rw [hY hz,mul_zero]

lemma SmoothMultiplier.energy_insertionJet_local_le_sum {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : Jet n L)
    (hn : ∀ Y, f.fiberMass Y≤1)
    (ho : ∀ (i : Fin n) (j : Fin 3), ∀ᵐ Y ∂volume, u.1 Y≠0 → ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0) :
    energy (f.insertionJet u)≤energy u + ∑ p : Direction (n+1),
      ‖L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L u.1)‖^2 := by
  have hz (j : Fin 3) : (f.insertionJet u).2 (0,j)=
      L2Multiplier.clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1) := by
    change f.insertionScalar 0 + _ = _
    rw [map_zero,zero_add]
    rfl
  have hs (i : Fin n) (j : Fin 3) : ‖(f.insertionJet u).2 (i.succ,j)‖^2≤
      ‖u.2 (i,j)‖^2+
      ‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 := by
    change ‖f.insertionScalar (u.2 (i,j)) +
      L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 ≤ _
    rw [@norm_add_sq ℂ, f.insertion_cross_zero_local (i.succ,j) (u.2 (i,j)) u.1 (ho i j),map_zero,
      mul_zero,add_zero]
    exact add_le_add_left (f.norm_insertionScalar_le hn (u.2 (i,j)))
      (‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2)
  simp only [energy,Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ (f := fun i : Fin (n+1) ↦ ∑ j : Fin 3, ‖(f.insertionJet u).2 (i,j)‖^2),
    Fin.sum_univ_succ (f := fun i : Fin (n+1) ↦ ∑ j : Fin 3,
      ‖L2Multiplier.clm _ (f.partial_memLp_top (i,j)) (configurationTailCLM n L u.1)‖^2)]
  simp only [hz]
  calc
    _ ≤ (∑ j : Fin 3, ‖L2Multiplier.clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1)‖^2)+
        ∑ i : Fin n, ∑ j : Fin 3, (‖u.2 (i,j)‖^2+
        ‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2) := by
      exact add_le_add_right (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hs i j) _
    _ = _ := by simp only [Finset.sum_add_distrib]; ring

lemma SmoothMultiplier.energy_insertionJet_local_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : Jet n L)
    (hn : ∀ Y, f.fiberMass Y≤1)
    (ho : ∀ (i : Fin n) (j : Fin 3), ∀ᵐ Y ∂volume, u.1 Y≠0 → ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (C : ℝ) (hC : ∀ᵐ Y ∂volume, u.1 Y≠0 →
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C) :
    energy (f.insertionJet u)≤energy u+C*‖u.1‖^2 := by
  apply (f.energy_insertionJet_local_le_sum u hn ho).trans
  apply add_le_add_right
  simp_rw [norm_weightedTail_sq]
  rw [← integral_finsetSum _ (fun p _ ↦ f.insertion_derivative_integrable u.1 p),
    IndicatorStrong.norm_sq_integral,← integral_const_mul]
  apply integral_mono_ae
  · exact integrable_finsetSum _ (fun p _ ↦ f.insertion_derivative_integrable u.1 p)
  · exact (Lp.memLp u.1).integrable_norm_pow (by decide : (2:ℕ)≠0) |>.const_mul C
  · filter_upwards [hC] with Y hY
    rw [← Finset.mul_sum]
    by_cases hz : u.1 Y=0
    · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_mul,le_refl]
    · simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hY hz) (sq_nonneg ‖u.1 Y‖)

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

omit hL in
lemma chordLift_le_qLift (z : Fin 3 → ℝ) (j : Fin 3) : chordLift L (z j)≤qLift L z :=
  Finset.single_le_sum (fun k _ ↦ sq_nonneg (L/Real.pi*Real.sin (Real.pi/L*z k))) (Finset.mem_univ j)

end PeriodicCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Near
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set
noncomputable section

variable (L : ℝ) [hL : Fact (0<L)]

lemma near_measurable (r : ℝ) (x : ThreeTorus L) : MeasurableSet (near L r x) :=
  (isClosed_le ((pairQ_continuous L).comp (continuous_id.prodMk continuous_const)) continuous_const).measurableSet

lemma distance_sum_le_pairQ (y x : ThreeTorus L) :
    (∑ j : Fin 3, dist (y j) (x j)^2) ≤ (Real.pi/2)^2*pairQ L y x := by
  rw [pairQ,Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ by simpa only [dist_eq_norm] using norm_sq_le_chord L (y j-x j)

lemma near_distance_sum {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L}
    (hy : y∈near L r x) : (∑ j : Fin 3, dist (y j) (x j)^2) < (2*r)^2 := by
  have hp : Real.pi^2<10 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hq := distance_sum_le_pairQ L y x
  have hs := mul_le_mul_of_nonneg_left hy (sq_nonneg (Real.pi/2))
  have hh := mul_lt_mul_of_pos_right hp (sq_pos_of_pos hr)
  nlinarith

lemma near_subset_box {r : ℝ} (hr : 0 < r) (x : ThreeTorus L) : near L r x⊆box L (2*r) x := by
  intro y hy
  simp only [box,Set.mem_univ_pi,Metric.mem_closedBall]
  intro j
  have hs := Finset.single_le_sum (f := fun j : Fin 3 ↦ dist (y j) (x j)^2)
    (fun j _ ↦ sq_nonneg _) (Finset.mem_univ j)
  have hh := near_distance_sum L hr hy
  exact (sq_le_sq₀ dist_nonneg (by positivity)).mp (hs.trans hh.le)

lemma near_volume_le {r : ℝ} (hr : 0 < r) (x : ThreeTorus L) :
    volume.real (near L r x)≤(4*r)^3 := by
  calc
    _ ≤ volume.real (box L (2*r) x) := measureReal_mono (near_subset_box L hr x)
    _ ≤ (2*(2*r))^3 := box_volume_le L (by positivity) x
    _ = _ := by ring

lemma near_distance {K : Length} {r : ℝ} (hr : 0 < r) {y x : Torus K}
    (hy : y∈near K.val r x) : torusDistance K y x≤2*r := by
  have h := near_distance_sum K.val hr hy
  exact Real.sqrt_le_iff.mpr ⟨by positivity,h.le⟩

end
end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
noncomputable section
variable (L : ℝ) [hL : Fact (0<L)]

lemma angle_bounds (r : ℝ) (y x : ThreeTorus L) : 0≤angle L r y x ∧ angle L r y x≤Real.pi/2 := by
  constructor
  · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg _)
  · simpa only [angle,mul_one] using mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _)
      (show 0≤Real.pi/2 by positivity)

lemma angle_zero {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L} (hq : pairQ L y x≤(5/4)*r^2) :
    angle L r y x=0 := by
  unfold angle
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) (by positivity)),mul_zero]

lemma angle_one {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L} (hq : (3/2)*r^2≤pairQ L y x) :
    angle L r y x=Real.pi/2 := by
  unfold angle
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity)).mpr (by nlinarith)),mul_one]

lemma angle_one_outside {r : ℝ} (hr : 0 < r) {y x : ThreeTorus L}
    (hx : y∉near L r x) : angle L r y x=Real.pi/2 :=
  angle_one L hr (not_le.mp hx).le
end
end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
variable (L : ℝ) [hL : Fact (0<L)]

omit hL in
lemma angleLift_derivative (r : ℝ) (z : Fin 3 → ℝ → ℝ)
    (d : Fin 3 → ℝ) (t : ℝ) (hd : ∀ j, HasDerivAt (z j) (d j) t) :
    HasDerivAt (fun s ↦ angleLift L r (fun j ↦ z j s))
      (∑ j : Fin 3, anglePartial L r (fun k ↦ z k t) j*d j) t := by
  have hc j := ((chordLift_smooth L).differentiable (by simp) (z j t)).hasDerivAt.comp t (hd j)
  have hq := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3))) (fun j _ ↦ hc j)
  have h := ((transition_derivative ((qLift L (fun j ↦ z j t)-(5/4)*r^2)/((1/4)*r^2))).comp t
    ((hq.sub_const ((5/4)*r^2)).div_const ((1/4)*r^2))).const_mul (Real.pi/2)
  apply h.congr_deriv
  dsimp [anglePartial,angleFactor]
  calc
    _ = (2*Real.pi/r^2*deriv Real.smoothTransition ((qLift L (fun j ↦ z j t)-(5/4)*r^2)/((1/4)*r^2)))*
        ∑ j : Fin 3, deriv (chordLift L) (z j t)*d j := by ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

omit hL in
lemma angleFactor_eq_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc ((5/4)*r^2) ((3/2)*r^2)) : angleFactor L r z=0 := by
  have ht : (qLift L z-(5/4)*r^2)/((1/4)*r^2)∉Icc (0:ℝ) 1 := by
    intro hc
    apply hz
    have h0 := (le_div_iff₀ (show 0<(1/4)*r^2 by positivity)).mp hc.1
    have h1 := (div_le_iff₀ (show 0<(1/4)*r^2 by positivity)).mp hc.2
    constructor <;> nlinarith
  simp only [angleFactor,transition_deriv_eq_zero ht,mul_zero]

omit hL in
lemma anglePartial_eq_zero {r : ℝ} (hr : 0 < r) {z : Fin 3 → ℝ}
    (hz : qLift L z∉Icc ((5/4)*r^2) ((3/2)*r^2)) (j : Fin 3) : anglePartial L r z j=0 := by
  rw [anglePartial,angleFactor_eq_zero L hr hz,zero_mul]

lemma anglePartial_sq_le {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (z : Fin 3 → ℝ) (j : Fin 3) :
    anglePartial L r z j^2 ≤ 24*Real.pi^2*M^2/r^2 := by
  by_cases hz : qLift L z∈Icc ((5/4)*r^2) ((3/2)*r^2)
  · have hc : (deriv (chordLift L) (z j))^2≤6*r^2 := by
      have hs := chordLift_le_qLift L z j
      have hd := chordLift_derivative_sq_le L (z j)
      nlinarith [hz.2]
    have ht : (deriv Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2)))^2≤M^2 := by
      rw [← sq_abs (deriv Real.smoothTransition _)]
      exact (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb _)
    calc
      _ = (2*Real.pi/r^2)^2*((deriv Real.smoothTransition ((qLift L z-(5/4)*r^2)/((1/4)*r^2)))^2*
          (deriv (chordLift L) (z j))^2) := by dsimp [anglePartial,angleFactor]; ring
      _ ≤ (2*Real.pi/r^2)^2*(M^2*(6*r^2)) := by gcongr
      _ = _ := by field_simp [hr.ne']; ring
  · rw [anglePartial_eq_zero L hr hz j,zero_pow (by norm_num)]
    positivity

end HardSphere.TightCutoff

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_RawAngleLift
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
namespace HardSphere.TightCutoff
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
      {X | (5/4)*r^2≤pairQ L.val (X 0) (X i.succ)} := by
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
  have hQ : (5/4)*r^2≤pairQ L.val (X 0) (X i.succ) := hs hX
  have he : torusDistance L (X 0) (X i.succ)^2=
      ∑ j : Fin 3,dist (X 0 j) (X i.succ j)^2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hl := pairQ_le L.val (X 0) (X i.succ)
  have hd : 0≤torusDistance L (X 0) (X i.succ) := Real.sqrt_nonneg _
  nlinarith [sq_pos_of_pos hr]

end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff
lemma rawCutoffReal_bounds (n : ℕ) (L : Length) (r : ℝ) (X : Configuration (n+1) L) :
    0 ≤ rawCutoffReal n L r X ∧ rawCutoffReal n L r X≤1 := by
  have hs (i : Fin n) : 0≤Real.sin (angle L.val r (X 0) (X i.succ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (angle_bounds L.val r _ _).1
      ((angle_bounds L.val r _ _).2.trans (by linarith [Real.pi_pos]))
  exact ⟨Finset.prod_nonneg (fun i _ ↦ hs i),Finset.prod_le_one (fun i _ ↦ hs i) (fun _ _ ↦ Real.sin_le_one _)⟩

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
      (144*Real.pi^2*M^2/r^2)*(near L.val r (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  rw [rawAngleLift_sum_squares]
  by_cases hx : X 0∈near L.val r (X i.succ)
  · rw [Set.indicator_of_mem hx,mul_one]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ ↦ anglePartial_sq_le L.val hr hM hb
        (representative (n+1) L X 0-representative (n+1) L X i.succ) j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    calc
      _ ≤ 2*((3:ℝ)*(24*Real.pi^2*M^2/r^2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx,mul_zero]
    have hq : (3/2)*r^2<pairQ L.val (X 0) (X i.succ) := not_le.mp hx
    rw [pairQ_representative] at hq
    have hz : qLift L.val (representative (n+1) L X 0-representative (n+1) L X i.succ)∉Icc ((5/4)*r^2) ((3/2)*r^2) :=
      fun hs ↦ (not_lt.mpr hs.2) hq
    simp [anglePartial_eq_zero L.val hr hz]

lemma rawCutoff_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2)≤
      (144*Real.pi^2*M^2/r^2)*∑ i : Fin n,
        (near L.val r (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  calc
    _ ≤ ∑ p : Direction (n+1), ∑ i : Fin n,
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 :=
      Finset.sum_le_sum fun p _ ↦ rawCutoff_derivative_sq_le n L r X p
    _ = ∑ i : Fin n, ∑ p : Direction (n+1),
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 := by rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin n, (144*Real.pi^2*M^2/r^2)*
        (near L.val r (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) :=
      Finset.sum_le_sum fun i _ ↦ rawAngleLift_gradient_le n L hr hM hb i X
    _ = _ := (Finset.mul_sum ..).symm

end HardSphere.TightCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HeadLift
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

lemma headLift_direction_zero (n : ℕ) (j : Fin 3) :
    headLift n (Pi.single 0 (Pi.single j 1))=Pi.single 0 (Pi.single j 1) := by
  ext i k
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  simp [headLift]

lemma headLift_direction_succ (n : ℕ) (i : Fin n) (j : Fin 3) :
    headLift n (Pi.single i.succ (Pi.single j 1))=0 := by
  ext k q
  simp [headLift]

lemma SmoothMultiplier.orbital_le_bound {L : Length} (w : SmoothMultiplier 1 L) (x : Torus L) :
    ‖w.orbital x‖^2≤w.orbitalBound := by
  exact pow_le_pow_left₀ (norm_nonneg _) ((⟨w.orbital,w.orbital_continuous⟩ : C(Torus L,ℂ)).norm_coe_le_norm x) 2

lemma SmoothMultiplier.coordDerivative_liftHead_zero {L : Length}
    (w : SmoothMultiplier 1 L) (n : ℕ) (j : Fin 3) :
    coordDerivative (n+1) L (w.liftHead n).toFun (0,j)=
      fun X ↦ coordDerivative 1 L w.toFun (0,j) (fun _ ↦ X 0) := by
  funext X
  have h := (w.smooth.differentiable (by simp)
    (headLift n (representative (n+1) L X))).hasFDerivAt.comp
    (representative (n+1) L X) (headLift n).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration 1 ↦ w.toFun (project 1 L Y)) ∘ headLift n)
    (representative (n+1) L X)) (Pi.single 0 (Pi.single j 1))=_
  rw [h.fderiv,ContinuousLinearMap.comp_apply,headLift_direction_zero]
  rfl

lemma SmoothMultiplier.coordDerivative_liftHead_succ {L : Length}
    (w : SmoothMultiplier 1 L) (n : ℕ) (i : Fin n) (j : Fin 3) :
    coordDerivative (n+1) L (w.liftHead n).toFun (i.succ,j)=0 := by
  funext X
  have h := (w.smooth.differentiable (by simp)
    (headLift n (representative (n+1) L X))).hasFDerivAt.comp
    (representative (n+1) L X) (headLift n).hasFDerivAt
  change (fderiv ℝ ((fun Y : LiftedConfiguration 1 ↦ w.toFun (project 1 L Y)) ∘ headLift n)
    (representative (n+1) L X)) (Pi.single i.succ (Pi.single j 1))=0
  rw [h.fderiv,ContinuousLinearMap.comp_apply,headLift_direction_succ,map_zero]

lemma SmoothMultiplier.liftHead_gradient_sum {L : Length}
    (w : SmoothMultiplier 1 L) (n : ℕ) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (w.liftHead n).toFun p X‖^2)=
      ∑ j : Fin 3, ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ X 0)‖^2 := by
  rw [Fintype.sum_prod_type,Fin.sum_univ_succ]
  simp only [w.coordDerivative_liftHead_zero,w.coordDerivative_liftHead_succ,
    Pi.zero_apply,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_CloseLabels
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
namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set Filter
open scoped ComplexConjugate

lemma mem_closeLabels_of_near {n : ℕ} {L : Length} {r : ℝ} (hr : 0 < r)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) {y : Torus L} (hy : w.orbital y≠0)
    (i : Fin n) (hi : y∈near L.val r (Y i)) : i∈closeLabels r w Y := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,subset_tsupport w.orbital hy,near_distance hr hi⟩

lemma orbitalCutoff_real {L : Length} (n : ℕ) (r : ℝ) (w : SmoothMultiplier 1 L)
    (hw : ∀ X, conj (w.toFun X)=w.toFun X) (X : Configuration (n+1) L) :
    conj ((orbitalCutoff n r w).toFun X)=(orbitalCutoff n r w).toFun X := by
  change conj (w.orbital (X 0)*(rawCutoff n L r).toFun X)=_
  rw [map_mul,rawCutoff_real]
  change conj (w.toFun (fun _ ↦ X 0)) * _ = _
  rw [hw]
  rfl

lemma orbitalCutoff_clearance {L : Length} (n : ℕ) {r : ℝ} (hr : 0 < r) (w : SmoothMultiplier 1 L) :
    InsertionClearance r (orbitalCutoff n r w) :=
  Set.Subset.trans tsupport_mul_subset_right (rawCutoff_clearance n L hr)

lemma weighted_near_le {n : ℕ} {L : Length} {r : ℝ} (hr : 0 < r)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) (y : Torus L) :
    ‖w.orbital y‖^2 * ∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y ≤
      w.orbitalBound * ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  classical
  have hb (i : Fin n) : 0≤(near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  by_cases hy : w.orbital y=0
  · simp only [hy,norm_zero,zero_pow (by decide : 2≠0),zero_mul]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ hb i)
  · have he : (∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y)=
        ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact Set.indicator_of_notMem (fun hh ↦ hi (mem_closeLabels_of_near hr w Y hy i hh)) _
    rw [he]
    exact mul_le_mul_of_nonneg_right (w.orbital_le_bound y) (Finset.sum_nonneg fun i _ ↦ hb i)

lemma rawCutoff_mass_pointwise (n : ℕ) (L : Length) {r : ℝ} (hr : 0 < r)
    (y : Torus L) (Y : Configuration n L) :
    1≤‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2+
      ∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  rw [rawCutoff_norm_sq]
  have hb (i : Fin n) : 0≤(near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  by_cases hh : ∃ i, y∈near L.val r (Y i)
  · obtain ⟨i,hi⟩ := hh
    have hs := Finset.single_le_sum (f := fun i : Fin n ↦
      (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y) (fun i _ ↦ hb i) (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi] at hs
    exact hs.trans (le_add_of_nonneg_left (sq_nonneg _))
  · have ha (i : Fin n) : angle L.val r y (Y i)=Real.pi/2 :=
      angle_one_outside L.val hr (fun hi ↦ hh ⟨i,hi⟩)
    have he : rawCutoffReal n L r (Fin.cons y Y)=1 := by
      simp only [rawCutoffReal,Fin.cons_zero,Fin.cons_succ,ha,Real.sin_pi_div_two,Finset.prod_const_one]
    rw [he,one_pow]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hb i))

lemma localized_mass_pointwise {n : ℕ} {L : Length} {r : ℝ} (hr : 0 < r)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) (y : Torus L) :
    ‖w.orbital y‖^2≤‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2+
      w.orbitalBound * ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  have h := mul_le_mul_of_nonneg_left (rawCutoff_mass_pointwise n L hr y Y) (sq_nonneg ‖w.orbital y‖)
  simp only [mul_one,mul_add] at h
  have he : ‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2=
      ‖w.orbital y‖^2 * ‖(rawCutoff n L r).toFun (Fin.cons y Y)‖^2 := by
    change ‖w.orbital y*(rawCutoff n L r).toFun (Fin.cons y Y)‖^2=_
    rw [norm_mul,mul_pow]
  rw [he]
  exact h.trans (add_le_add_right (weighted_near_le hr w Y y) _)

lemma near_sum_integral_le {n : ℕ} {L : Length} {r : ℝ} (hr : 0 < r)
    (Y : Configuration n L) (J : Finset (Fin n)) :
    (∫ y : Torus L, ∑ i ∈ J, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y)≤
      (J.card:ℝ)*(4*r)^3 := by
  rw [integral_finsetSum _ (fun i _ ↦ (integrable_const (1:ℝ)).indicator (near_measurable L.val r (Y i)))]
  calc
    _ = ∑ i ∈ J, volume.real (near L.val r (Y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_indicator_one (near_measurable L.val _ _)
    _ ≤ ∑ i ∈ J, (4*r)^3 := Finset.sum_le_sum fun i _ ↦ near_volume_le L.val hr (Y i)
    _ = _ := by simp

lemma localized_mass_lower {n : ℕ} {L : Length} {r : ℝ} (hr : 0 < r)
    (w : SmoothMultiplier 1 L) (hw : ∫ y : Torus L, ‖w.orbital y‖^2=1)
    (Y : Configuration n L) :
    1-64*w.orbitalBound*(closeLabels r w Y).card*r^3≤(orbitalCutoff n r w).fiberMass Y := by
  have hf : Integrable (fun y : Torus L ↦ ‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2) volume :=
    (((continuous_of_continuous_lift (orbitalCutoff n r w).smooth.continuous).comp
      ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
        (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hw' : Integrable (fun y : Torus L ↦ ‖w.orbital y‖^2) volume :=
    (w.orbital_continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun y : Torus L ↦ ∑ i ∈ closeLabels r w Y,
      (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y) volume :=
    integrable_finsetSum _ (fun i _ ↦ (integrable_const (1:ℝ)).indicator (near_measurable L.val r (Y i)))
  have h := integral_mono hw' (hf.add (hi.const_mul w.orbitalBound)) (localized_mass_pointwise hr w Y)
  change (∫ y : Torus L, ‖w.orbital y‖^2) ≤ ∫ y : Torus L,
    ‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2+
    w.orbitalBound * ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y at h
  rw [hw,integral_add hf (hi.const_mul w.orbitalBound),integral_const_mul] at h
  have hh := mul_le_mul_of_nonneg_left (near_sum_integral_le hr Y (closeLabels r w Y)) (show 0≤w.orbitalBound from sq_nonneg _)
  change 1-64*w.orbitalBound*(closeLabels r w Y).card*r^3≤∫ y : Torus L, ‖(orbitalCutoff n r w).toFun (Fin.cons y Y)‖^2
  nlinarith

end HardSphere.TightCutoff

namespace HardSphere.TightCutoff
open PeriodicCutoff MeasureTheory Set Filter

lemma norm_add_sq_le_two (z v : ℂ) : ‖z+v‖^2≤2*‖z‖^2+2*‖v‖^2 := by
  have h := norm_add_le z v
  have h' := sq_nonneg (‖z‖-‖v‖)
  nlinarith [norm_nonneg (z+v),norm_nonneg z,norm_nonneg v]

lemma orbitalCutoff_derivative_le {n : ℕ} {L : Length} (r : ℝ)
    (w : SmoothMultiplier 1 L) (X : Configuration (n+1) L) (p : Direction (n+1)) :
    ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p X‖^2≤
      2*‖w.orbital (X 0)‖^2*‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2+
      2*‖coordDerivative (n+1) L (w.liftHead n).toFun p X‖^2 := by
  change ‖coordDerivative (n+1) L ((w.liftHead n).toFun*(rawCutoff n L r).toFun) p X‖^2≤_
  rw [coordDerivative_mul ((w.liftHead n).smooth.differentiable (by simp))
    ((rawCutoff n L r).smooth.differentiable (by simp))]
  simp only [Pi.add_apply,Pi.mul_apply]
  have hh := norm_add_sq_le_two
    ((w.liftHead n).toFun X*coordDerivative (n+1) L (rawCutoff n L r).toFun p X)
    ((rawCutoff n L r).toFun X*coordDerivative (n+1) L (w.liftHead n).toFun p X)
  simp only [norm_mul,mul_pow] at hh
  have hb : ‖(rawCutoff n L r).toFun X‖^2≤1 := by
    rw [rawCutoff_norm_sq]
    nlinarith [(rawCutoffReal_bounds n L r X).1,(rawCutoffReal_bounds n L r X).2]
  have hc := mul_le_mul_of_nonneg_left hb
    (sq_nonneg ‖coordDerivative (n+1) L (w.liftHead n).toFun p X‖)
  change ‖coordDerivative (n+1) L (w.liftHead n).toFun p X‖^2 * ‖(rawCutoff n L r).toFun X‖^2≤_ at hc
  change _≤2*‖(w.liftHead n).toFun X‖^2*‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2+_
  nlinarith

lemma localized_gradient_pointwise {n : ℕ} {L : Length} {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) (y : Torus L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons y Y)‖^2)≤
      2*(∑ j : Fin 3, ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ y)‖^2)+
      (288*Real.pi^2*M^2/r^2)*w.orbitalBound *
        ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Direction (n+1))))
    (fun p _ ↦ orbitalCutoff_derivative_le r w (Fin.cons y Y) p)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,w.liftHead_gradient_sum,Fin.cons_zero] at hs
  have hg := rawCutoff_gradient_le n L hr hM hb (Fin.cons y Y)
  simp only [Fin.cons_zero,Fin.cons_succ] at hg
  have h1 := mul_le_mul_of_nonneg_left hg (show 0≤2*‖w.orbital y‖^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (weighted_near_le hr w Y y)
    (show 0≤288*Real.pi^2*M^2/r^2 by positivity)
  have he : 2*‖w.orbital y‖^2 * (144*Real.pi^2*M^2/r^2 *
      ∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y)=
      (288*Real.pi^2*M^2/r^2) * (‖w.orbital y‖^2 *
      ∑ i : Fin n, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y) := by ring
  rw [he] at h1
  have hh := h1.trans h2
  rw [← mul_assoc] at hh
  linarith

lemma derivative_fiber_integrable {n : ℕ} {L : Length} (f : SmoothMultiplier (n+1) L)
    (Y : Configuration n L) (p : Direction (n+1)) :
    Integrable (fun y : Torus L ↦ ‖coordDerivative (n+1) L f.toFun p (Fin.cons y Y)‖^2) volume := by
  exact (((continuous_coordDerivative f.smooth p).comp
    ((continuous_id : Continuous (id : Torus L → Torus L)).finCons
      (continuous_const : Continuous (fun _ : Torus L ↦ Y)))).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

lemma orbital_derivative_integrable {L : Length} (w : SmoothMultiplier 1 L) (j : Fin 3) :
    Integrable (fun y : Torus L ↦ ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ y)‖^2) volume :=
  (((continuous_coordDerivative w.smooth (0,j)).comp (continuous_pi fun _ ↦ continuous_id)).norm.pow 2
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma localized_gradient_integral_le {n : ℕ} {L : Length} {r M : ℝ} (hr : 0 < r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (w : SmoothMultiplier 1 L) (Y : Configuration n L) :
    (∑ p : Direction (n+1), ∫ y : Torus L,
      ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons y Y)‖^2)≤
      2*w.orbitalEnergy+18432*Real.pi^2*M^2*w.orbitalBound*(closeLabels r w Y).card*r := by
  have hf := derivative_fiber_integrable (orbitalCutoff n r w) Y
  have hw := orbital_derivative_integrable w
  have hi : Integrable (fun y : Torus L ↦ ∑ i ∈ closeLabels r w Y,
      (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y) volume :=
    integrable_finsetSum _ (fun i _ ↦ (integrable_const (1:ℝ)).indicator (near_measurable L.val r (Y i)))
  have h := integral_mono (integrable_finsetSum Finset.univ (fun p _ ↦ hf p))
    (((integrable_finsetSum Finset.univ (fun j _ ↦ hw j)).const_mul 2).add
      (hi.const_mul ((288*Real.pi^2*M^2/r^2)*w.orbitalBound)))
    (localized_gradient_pointwise hr hM hb w Y)
  change (∫ y : Torus L, ∑ p : Direction (n+1),
    ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons y Y)‖^2)≤
    ∫ y : Torus L, 2*(∑ j : Fin 3, ‖coordDerivative 1 L w.toFun (0,j) (fun _ ↦ y)‖^2)+
      (288*Real.pi^2*M^2/r^2)*w.orbitalBound *
        ∑ i ∈ closeLabels r w Y, (near L.val r (Y i)).indicator (fun _ ↦ (1:ℝ)) y at h
  rw [integral_finsetSum _ (fun p _ ↦ hf p),integral_add
    ((integrable_finsetSum Finset.univ (fun j _ ↦ hw j)).const_mul 2)
    (hi.const_mul ((288*Real.pi^2*M^2/r^2)*w.orbitalBound)),
    integral_const_mul,integral_const_mul,integral_finsetSum _ (fun j _ ↦ hw j)] at h
  have hh := mul_le_mul_of_nonneg_left (near_sum_integral_le hr Y (closeLabels r w Y))
    (show 0≤(288*Real.pi^2*M^2/r^2)*w.orbitalBound from mul_nonneg (by positivity) (sq_nonneg _))
  have he : (288*Real.pi^2*M^2/r^2)*w.orbitalBound*((closeLabels r w Y).card*(4*r)^3)=
      18432*Real.pi^2*M^2*w.orbitalBound*(closeLabels r w Y).card*r := by
    field_simp [hr.ne']
    ring
  rw [he] at hh
  exact h.trans (add_le_add_right hh _)

end HardSphere.TightCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_LocalInsertion
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
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate
noncomputable section

lemma SmoothMultiplier.insertion_from_raw_local_value {n : ℕ} {L : Length} {a C z : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hz : 1/2<z)
    {u : Jet n L} (hu : u∈dirichletDomain n L a)
    (hZ : ∀ᵐ Y ∂volume, u.1 Y≠0 → z≤f.fiberMass Y)
    (hC : ∀ᵐ Y ∂volume, u.1 Y≠0 →
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C) :
    let v := (f.localNormalization hr).insertionJet u
    v∈dirichletDomain (n+1) L a ∧
      ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C/z)*‖u.1‖^2 := by
  refine ⟨?_,?_,?_⟩
  · exact (f.localNormalization hr).insertionJet_mem_domain (f.localNormalization_clearance hr hc) hu
  · apply (f.localNormalization hr).norm_insertionScalar_local
    filter_upwards [hZ] with Y hY
    intro hne
    exact f.localNormalization_mass_eq hr Y (hz.le.trans (hY hne))
  · apply (f.localNormalization hr).energy_insertionJet_local_le u (f.localNormalization_mass_le hr)
    · intro i j
      filter_upwards [hZ] with Y hY
      intro hne
      exact (f.localNormalization hr).insertion_orthogonal_local (f.localNormalization_real hr)
        i j Y (f.localNormalization_mass_eventually hr Y (hz.trans_le (hY hne)))
    · filter_upwards [hZ,hC] with Y hY hCY
      intro hne
      have hz0 : 0<z := by linarith
      rw [le_div_iff₀ hz0,mul_comm]
      calc
        z * ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L (f.localNormalization hr).toFun p (Fin.cons x Y)‖^2 ≤
          f.fiberMass Y * ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L (f.localNormalization hr).toFun p (Fin.cons x Y)‖^2 := by
          apply mul_le_mul_of_nonneg_right (hY hne)
          exact Finset.sum_nonneg fun p _ ↦ integral_nonneg fun x ↦ sq_nonneg _
        _ ≤ ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun p _ ↦ f.localNormalization_derivative_le hr p Y (hz.trans_le (hY hne))
        _ ≤ C := hCY hne

lemma SmoothMultiplier.localNormalization_insertion_support {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (u : Jet n L) :
    ∀ᵐ X ∂volume, ((f.localNormalization hr).insertionJet u).1 X≠0 →
      u.1 (Fin.tail X)≠0 ∧ f.toFun X≠0 := by
  filter_upwards [coe_insertionScalar (f.localNormalization hr) u.1] with X hX
  intro hne
  change (f.localNormalization hr).insertionScalar u.1 X≠0 at hne
  rw [hX] at hne
  have hp := mul_ne_zero_iff.mp hne
  refine ⟨hp.2,?_⟩
  have hf := hp.1
  change f.toFun X/(Real.sqrt (safeMass (f.fiberMass (Fin.tail X))):ℂ)≠0 at hf
  exact fun hz ↦ hf (by rw [hz,zero_div])

end
end HardSphere
namespace HardSphere
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate
noncomputable section

lemma local_insertion_supported : ∃ C : ℝ, 0<C ∧ ∀ (n : ℕ) (L : Length) (r : ℝ), 0 < r →
    ∀ (w : SmoothMultiplier 1 L), (∀ X, conj (w.toFun X)=w.toFun X) →
    (∫ y : Torus L, ‖w.orbital y‖^2)=1 → ∀ (k : ℕ),
    C*w.orbitalBound*k*r^3≤1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → (closeLabels r w Y).card≤k) →
    ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v≤energy u+C*(w.orbitalEnergy+w.orbitalBound*k*r)*‖u.1‖^2 ∧
      (∀ᵐ X ∂volume, v.1 X≠0 → u.1 (Fin.tail X)≠0 ∧ w.orbital (X 0)≠0) := by
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  let C : ℝ := 50000*(1+Real.pi^2*M^2)
  have hC : 0<C := by dsimp [C]; positivity
  have hC64 : 64≤C := by dsimp [C]; nlinarith [sq_nonneg (Real.pi*M)]
  have hCB {L : Length} (w : SmoothMultiplier 1 L) : 0≤w.orbitalBound := sq_nonneg _
  refine ⟨C,hC,fun n L r hr w hw hn k hs u hu hk ↦ ?_⟩
  have hwB := hCB w
  have hZ : ∀ᵐ Y ∂volume, u.1 Y≠0 → (3/4:ℝ)≤(orbitalCutoff n r w).fiberMass Y := by
    filter_upwards [hk] with Y hY
    intro hne
    have hj : ((closeLabels r w Y).card:ℝ)≤k := by exact_mod_cast hY hne
    have h1 := mul_le_mul_of_nonneg_right hC64 (show 0≤w.orbitalBound*k*r^3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hj (show 0≤64*w.orbitalBound*r^3 by positivity)
    have hz := localized_mass_lower hr w hn Y
    nlinarith
  have hcost : ∀ᵐ Y ∂volume, u.1 Y≠0 →
      ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons x Y)‖^2≤
      2*w.orbitalEnergy+18432*Real.pi^2*M^2*w.orbitalBound*k*r := by
    filter_upwards [hk] with Y hY
    intro hne
    apply (localized_gradient_integral_le hr hM.le hb w Y).trans
    have hj : ((closeLabels r w Y).card:ℝ)≤k := by exact_mod_cast hY hne
    have hh := mul_le_mul_of_nonneg_left hj
      (show 0≤18432*Real.pi^2*M^2*w.orbitalBound*r from mul_nonneg
        (mul_nonneg (by positivity) (hCB w)) hr.le)
    nlinarith
  let f := orbitalCutoff n r w
  let v := (f.localNormalization (orbitalCutoff_real n r w hw)).insertionJet u
  obtain ⟨hv,hvnorm,hven⟩ := (orbitalCutoff n r w).insertion_from_raw_local_value
    (orbitalCutoff_clearance n hr w) (orbitalCutoff_real n r w hw)
    (by norm_num : (1/2:ℝ)<3/4) hu hZ hcost
  have hsupport : ∀ᵐ X ∂volume, v.1 X≠0 → u.1 (Fin.tail X)≠0 ∧ w.orbital (X 0)≠0 := by
    filter_upwards [f.localNormalization_insertion_support (orbitalCutoff_real n r w hw) u] with X hX
    intro hnz
    obtain ⟨hOld,hRaw⟩ := hX hnz
    refine ⟨hOld,?_⟩
    change w.orbital (X 0)*(TightCutoff.rawCutoff n L r).toFun X≠0 at hRaw
    exact (mul_ne_zero_iff.mp hRaw).1
  refine ⟨v,hv,hvnorm,hven.trans ?_,hsupport⟩
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have he : 0≤w.orbitalEnergy := Finset.sum_nonneg fun j _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  have hk0 : 0≤w.orbitalBound*k*r := by exact mul_nonneg (mul_nonneg (hCB w) (Nat.cast_nonneg k)) hr.le
  have h1 : (2:ℝ)/(3/4)≤C := by linarith
  have h2 : (18432*Real.pi^2*M^2)/(3/4)≤C := by
    dsimp [C]
    nlinarith [sq_nonneg (Real.pi*M)]
  have he1 := mul_le_mul_of_nonneg_right h1 he
  have he2 := mul_le_mul_of_nonneg_right h2 hk0
  nlinarith

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
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_InsertionCount
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
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate
open scoped Classical

lemma closeLabels_cons {n : ℕ} {L : Length} (r : ℝ) (w : SmoothMultiplier 1 L)
    (x : Torus L) (Y : Configuration n L) :
    (closeLabels r w (Fin.cons x Y)).card=(closeLabels r w Y).card+
      (if ∃ y∈tsupport w.orbital, torusDistance L y x ≤ 2*r then 1 else 0) := by
  classical
  simp only [closeLabels,Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  exact Nat.add_comm _ _

lemma closeLabels_insert_le {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} (r : ℝ)
    (w : S → SmoothMultiplier 1 L)
    (hsep : ∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r)
    (v z : S) (X : Configuration (n+1) L) (hx : (w v).orbital (X 0)≠0) :
    (closeLabels r (w z) X).card ≤ (closeLabels r (w z) (Fin.tail X)).card+(if v=z then 1 else 0) := by
  classical
  have he : Fin.cons (X 0) (Fin.tail X)=X := by funext i; cases i using Fin.cases <;> rfl
  rw [←he,closeLabels_cons]
  simp only [Fin.tail_cons]
  by_cases hvz : v=z
  · subst v
    simp only [ite_true]
    split_ifs <;> omega
  · have hzv : z≠v := Ne.symm hvz
    rw [ite_eq_right hvz,ite_eq_right (hsep z v hzv (X 0) hx)]

lemma insertionCount_zero {S : Type*} [DecidableEq S] (site : ℕ → S) (z : S) :
    insertionCount site 0 z=0 := by simp [insertionCount]

lemma insertionCount_succ {S : Type*} [DecidableEq S] (site : ℕ → S) (t : ℕ) (z : S) :
    insertionCount site (t+1) z=insertionCount site t z+(if site t=z then 1 else 0) := by
  simp only [insertionCount,Finset.card_filter,Finset.sum_range_succ]

lemma insertionCount_mono {S : Type*} [DecidableEq S] (site : ℕ → S) {t T : ℕ} (ht : t ≤ T) (z : S) :
    insertionCount site t z ≤ insertionCount site T z := by
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hiz⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le ht),hiz⟩

lemma local_insertion_iterated : ∃ C : ℝ, 0<C ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (r : ℝ), 0 < r →
    ∀ (w : S → SmoothMultiplier 1 L),
    (∀ z X, conj ((w z).toFun X)=(w z).toFun X) →
    (∀ z, (∫ y : Torus L, ‖(w z).orbital y‖^2)=1) →
    (∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r) →
    ∀ (T k m : ℕ) (site : ℕ → S) (B E : ℝ),
    (∀ z, (w z).orbitalBound ≤ B) → (∀ z, (w z).orbitalEnergy ≤ E) →
    (∀ z, insertionCount site T z ≤ m) → C*B*(k+m)*r^3 ≤ 1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → ∀ z, (closeLabels r (w z) Y).card ≤ k) →
    ∃ v : Jet (n+T) L, v∈dirichletDomain (n+T) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v ≤ energy u+T*(C*(E+B*(k+m)*r))*‖u.1‖^2 := by
  obtain ⟨C,hC,hins⟩ := local_insertion_supported
  refine ⟨C,hC,?_⟩
  intro S _ n L r hr w hw hn hsep T k m site B E hB hE hct hs u hu hk
  have hrec (t : ℕ) (ht : t ≤ T) : ∃ v : Jet (n+t) L,
      v∈dirichletDomain (n+t) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v ≤ energy u+t*(C*(E+B*(k+m)*r))*‖u.1‖^2 ∧
      (∀ᵐ X ∂volume, v.1 X≠0 → ∀ z,
        (closeLabels r (w z) X).card ≤ k+insertionCount site t z) := by
    induction t with
    | zero =>
      refine ⟨u,hu,rfl,?_,?_⟩
      · simp only [Nat.cast_zero,zero_mul,add_zero,le_refl]
      · simpa only [insertionCount_zero,Nat.add_zero] using hk
    | succ t ih =>
      obtain ⟨v,hv,hvn,hve,hvk⟩ := ih (Nat.le_trans (Nat.le_succ t) ht)
      have hmass : C*(w (site t)).orbitalBound*(k+m:ℕ)*r^3 ≤ 1/4 := by
        apply le_trans _ hs
        simp only [Nat.cast_add]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hB _) hC.le
      have hbudget : ∀ᵐ X ∂volume, v.1 X≠0 → (closeLabels r (w (site t)) X).card ≤ k+m := by
        filter_upwards [hvk] with X hX
        intro hne
        exact (hX hne (site t)).trans (Nat.add_le_add_left
          ((insertionCount_mono site (Nat.le_trans (Nat.le_succ t) ht) _).trans (hct _)) k)
      obtain ⟨v',hv',hvn',hve',hvs⟩ := hins (n+t) L r hr (w (site t)) (hw _) (hn _) (k+m) hmass v hv hbudget
      refine ⟨v',hv',hvn'.trans hvn,?_,?_⟩
      · have hbound : C*((w (site t)).orbitalEnergy+(w (site t)).orbitalBound*(k+m:ℕ)*r) ≤
            C*(E+B*(k+m)*r) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply add_le_add (hE _)
          rw [Nat.cast_add]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB _) (by positivity)) hr.le
        rw [hvn] at hve'
        have he := hve'.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hbound (sq_nonneg _)))
        rw [Nat.cast_add,Nat.cast_one]
        nlinarith
      · filter_upwards [hvs,(configurationTail_quasiPreserving (n+t) L).ae hvk] with X hX hOld
        intro hne z
        obtain ⟨hOldne,hOrb⟩ := hX hne
        have hh := closeLabels_insert_le r w hsep (site t) z X hOrb
        have hh' := hOld hOldne z
        rw [insertionCount_succ]
        omega
  obtain ⟨v,hv,hvn,hve,_⟩ := hrec T le_rfl
  exact ⟨v,hv,hvn,hve⟩

end HardSphere

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

lemma SmoothTest.slice_energy_integrable {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) :
    Integrable (fun x : Torus L ↦ energy (f.slice j x).jet) volume :=
  integrable_finsetSum _ (fun p _ ↦ f.slice_partial_integrable j p)

lemma SmoothTest.integral_slice_energy {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) :
    (∫ x : Torus L, energy (f.slice j x).jet)=
      energy f.jet - ∑ q : Fin 3, ‖f.jet.2 (j,q)‖^2 := by
  simp only [energy]
  rw [integral_finsetSum _ (fun p _ ↦ f.slice_partial_integrable j p)]
  simp only [f.integral_slice_partial,Fintype.sum_prod_type]
  rw [Fin.sum_univ_succAbove (fun i : Fin (n+1) ↦ ∑ q : Fin 3, ‖f.jet.2 (i,q)‖^2) j]
  ring

lemma rayleigh_successor {n : ℕ} {L : Length} {a c : ℝ} (hn : 0 < n)
    (h : ∀ u : Jet n L, u∈dirichletDomain n L a → c*(n:ℝ)*‖u.1‖^2≤energy u) :
    ∀ v : Jet (n+1) L, v∈dirichletDomain (n+1) L a → c*((n+1:ℕ):ℝ)*‖v.1‖^2≤energy v := by
  have htest (f : SmoothTest (n+1) L a) : c*((n+1:ℕ):ℝ)*‖f.jet.1‖^2≤energy f.jet := by
    have hi (j : Fin (n+1)) : c*(n:ℝ)*‖f.jet.1‖^2≤energy f.jet-∑ q : Fin 3, ‖f.jet.2 (j,q)‖^2 := by
      have hh := integral_mono ((f.slice_norm_sq_integrable j).const_mul (c*(n:ℝ)))
        (f.slice_energy_integrable j) (fun x ↦ h (f.slice j x).jet (subset_closure ⟨f.slice j x,rfl⟩))
      rw [integral_const_mul,f.integral_slice_norm_sq,f.integral_slice_energy] at hh
      exact hh
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n+1)))) (fun j _ ↦ hi j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Finset.sum_sub_distrib] at hs
    have he : (∑ j : Fin (n+1), ∑ q : Fin 3, ‖f.jet.2 (j,q)‖^2)=energy f.jet := by
      rw [energy,Fintype.sum_prod_type]
    rw [he] at hs
    rw [Nat.cast_add,Nat.cast_one] at hs ⊢
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    nlinarith
  intro v hv
  have hc : IsClosed {v : Jet (n+1) L | c*((n+1:ℕ):ℝ)*‖v.1‖^2≤energy v} := by
    apply isClosed_le
    · exact continuous_const.mul (continuous_fst.norm.pow 2)
    · exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact htest f) hv

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
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_RayleighLarger
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

lemma rayleigh_larger {n m : ℕ} {L : Length} {a c : ℝ} (hn : 0 < n) (hnm : n ≤ m)
    (h : ∀ u : Jet n L, u∈dirichletDomain n L a → c*(n:ℝ)*‖u.1‖^2≤energy u) :
    ∀ v : Jet m L, v∈dirichletDomain m L a → c*(m:ℝ)*‖v.1‖^2≤energy v := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m hnm ih => exact rayleigh_successor (hn.trans_le hnm) ih

lemma IsGroundVector.rayleigh_larger {n m : ℕ} {L : Length} {a : ℝ}
    {u : Jet n L} (hu : IsGroundVector n L a u) (hn : 0 < n) (hnm : n ≤ m)
    (v : Jet m L) (hv : v∈dirichletDomain m L a) :
    (energy u/(n:ℝ))*(m:ℝ)*‖v.1‖^2≤energy v := by
  apply HardSphere.rayleigh_larger hn hnm (c := energy u/(n:ℝ)) ?_ v hv
  intro w hw
  rw [div_mul_cancel₀ _ (by exact_mod_cast hn.ne')]
  exact hu.rayleigh_all w hw

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_DeficiencyPenalty
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
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma deficiency_penalty : ∃ C : ℝ, 0<C ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (r : ℝ), 0 < r → 0<n →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (w : S → SmoothMultiplier 1 L),
    (∀ z X, conj ((w z).toFun X)=(w z).toFun X) →
    (∀ z, (∫ y : Torus L, ‖(w z).orbital y‖^2)=1) →
    (∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r) →
    ∀ (T k m : ℕ) (site : ℕ → S) (B E : ℝ),
    (∀ z, (w z).orbitalBound ≤ B) → (∀ z, (w z).orbitalEnergy ≤ E) →
    (∀ z, insertionCount site T z ≤ m) → C*B*(k+m)*r^3 ≤ 1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → ∀ z, (closeLabels r (w z) Y).card ≤ k) →
    T*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))*‖u.1‖^2 ≤ energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,hC,hins⟩ := local_insertion_iterated
  refine ⟨C,hC,?_⟩
  intro S _ n L r hr hn g hg w hw hwN hsep T k m site B E hB hE hct hs u hu hk
  obtain ⟨v,hv,hvn,hve⟩ := hins S n L r hr w hw hwN hsep T k m site B E hB hE hct hs u hu hk
  have hlow := hg.rayleigh_larger hn (Nat.le_add_right n T) v hv
  rw [hvn] at hlow
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : (energy g/(n:ℝ))*((n+T:ℕ):ℝ)=energy g+(T:ℝ)*(energy g/(n:ℝ)) := by
    rw [Nat.cast_add,div_mul_eq_mul_div,mul_add,add_div,mul_div_cancel_right₀ _ hn0]
    ring
  rw [he] at hlow
  nlinarith

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_BalancedInsertion
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
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma exists_balanced_insertion (S : Type) [Fintype S] [Nonempty S] [DecidableEq S] (m : ℕ) :
    ∃ site : ℕ → S, ∀ z, insertionCount site (m*Fintype.card S) z=m := by
  classical
  let T := m*Fintype.card S
  let e : Fin T ≃ Fin m × S := Fintype.equivOfCardEq (by simp [T])
  let site : ℕ → S := fun i ↦ if h : i<T then (e ⟨i,h⟩).2 else Classical.choice ‹Nonempty S›
  refine ⟨site,?_⟩
  intro z
  let A := (Finset.range T).filter (fun i ↦ site i=z)
  have hl (i : A) : i.val<T := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
  have hz (i : A) : (e ⟨i.val,hl i⟩).2=z := by
    have h := (Finset.mem_filter.mp i.property).2
    simpa only [site,dite_eq_left (hl i)] using h
  let f : A → Fin m := fun i ↦ (e ⟨i.val,hl i⟩).1
  let g : Fin m → A := fun j ↦ ⟨(e.symm (j,z)).val,by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (e.symm (j,z)).isLt,?_⟩
    simp only [site,dite_eq_left (e.symm (j,z)).isLt,e.apply_symm_apply]⟩
  have hg (j : Fin m) : f (g j)=j := by
    change (e (e.symm (j,z))).1=j
    rw [e.apply_symm_apply]
  have hf (i : A) : g (f i)=i := by
    apply Subtype.ext
    change (e.symm ((e ⟨i.val,hl i⟩).1,z)).val=i.val
    rw [←hz i]
    simp only [Prod.mk.eta,e.symm_apply_apply]
  let q : A ≃ Fin m := ⟨f,g,hf,hg⟩
  have hc := Fintype.card_congr q
  simpa only [Fintype.card_coe,Fintype.card_fin,insertionCount,A,T] using hc

lemma deficiency_penalty_cells : ∃ C : ℝ, 0<C ∧
    ∀ (S : Type) [Fintype S] [Nonempty S] [DecidableEq S]
      (n : ℕ) (L : Length) (r : ℝ), 0 < r → 0<n →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (w : S → SmoothMultiplier 1 L),
    (∀ z X, conj ((w z).toFun X)=(w z).toFun X) →
    (∀ z, (∫ y : Torus L, ‖(w z).orbital y‖^2)=1) →
    (∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r) →
    ∀ (k m : ℕ) (B E : ℝ),
    (∀ z, (w z).orbitalBound ≤ B) → (∀ z, (w z).orbitalEnergy ≤ E) →
    C*B*(k+m)*r^3 ≤ 1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → ∀ z, (closeLabels r (w z) Y).card ≤ k) →
    m*Fintype.card S*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))*‖u.1‖^2 ≤
      energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,hC,hdef⟩ := deficiency_penalty
  refine ⟨C,hC,?_⟩
  intro S _ _ _ n L r hr hn g hg w hw hwN hsep k m B E hB hE hs u hu hk
  obtain ⟨site,hsite⟩ := exists_balanced_insertion S m
  simpa only [Nat.cast_mul] using hdef S n L r hr hn g hg w hw hwN hsep (m*Fintype.card S) k m site B E hB hE
    (fun z ↦ le_of_eq (hsite z)) hs u hu hk

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Bump
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
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma bump_continuous (L : Length) (δ : ℝ) (x : Torus L) : Continuous (bump L δ x) := by
  unfold bump TightCutoff.angle
  exact Real.continuous_cos.comp (continuous_const.mul (Real.smoothTransition.continuous.comp
    (((pairQ_continuous L.val).comp (continuous_id.prodMk continuous_const)).sub
      continuous_const |>.div_const _)))

lemma bump_bounds (L : Length) (δ : ℝ) (x y : Torus L) : 0 ≤ bump L δ x y ∧ bump L δ x y ≤ 1 := by
  refine ⟨?_,Real.cos_le_one _⟩
  apply Real.cos_nonneg_of_mem_Icc
  exact ⟨by linarith [(TightCutoff.angle_bounds L.val δ y x).1,Real.pi_pos],
    (TightCutoff.angle_bounds L.val δ y x).2⟩

lemma bump_eq_one {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) {y : Torus L}
    (hy : y∈box L.val (δ/2) x) : bump L δ x y=1 := by
  have hd j : dist (y j) (x j) ≤ δ/2 := (Set.mem_univ_pi.mp hy) j
  have hq := pairQ_le L.val y x
  have hs : (∑ j : Fin 3, dist (y j) (x j)^2) ≤ 3*(δ/2)^2 := by
    calc
      _ ≤ ∑ _j : Fin 3, (δ/2)^2 := Finset.sum_le_sum fun j _ ↦
        (sq_le_sq₀ dist_nonneg (by positivity)).mpr (hd j)
      _ = _ := by simp
  unfold bump
  rw [TightCutoff.angle_zero L.val hδ (by nlinarith), Real.cos_zero]

lemma bump_eq_zero {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) {y : Torus L}
    (hy : y∉TightCutoff.near L.val δ x) : bump L δ x y=0 := by
  rw [bump,TightCutoff.angle_one_outside L.val hδ hy,Real.cos_pi_div_two]

lemma box_volume_eq {L : Length} {b : ℝ} (hb : 0 ≤ b) (hbL : 2*b ≤ L.val) (x : Torus L) :
    volume.real (box L.val b x)=(2*b)^3 := by
  have he : volume (box L.val b x)=ENNReal.ofReal (min L.val (2*b))^3 := by
    rw [volume_pi,box,Measure.pi_pi]
    simp_rw [AddCircle.volume_closedBall]
    simp
  rw [measureReal_def,he,min_eq_right hbL,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)]

lemma mass_lower {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x : Torus L) :
    δ^3 ≤ mass L δ x := by
  have hi : Integrable (fun y : Torus L ↦ (bump L δ x y)^2) volume :=
    ((bump_continuous L δ x).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  calc
    _ = volume.real (box L.val (δ/2) x) := by rw [box_volume_eq (by positivity) (by linarith)]; ring
    _ = ∫ y in box L.val (δ/2) x, (bump L δ x y)^2 := by
      rw [setIntegral_congr_fun (box_measurable _ _ _) (fun y hy ↦ by rw [bump_eq_one hδ x hy])]
      simp
    _ ≤ mass L δ x := setIntegral_le_integral hi (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)

lemma mass_pos {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x : Torus L) :
    0 < mass L δ x := lt_of_lt_of_le (by positivity) (mass_lower hδ hδL x)

lemma raw_fderiv (L : Length) (δ : ℝ) (x : Torus L) (R v : LiftedConfiguration 1) :
    fderiv ℝ (fun R ↦ (raw L δ x).toFun (project 1 L R)) R v =
      ((-Real.sin (TightCutoff.angleLift L.val δ (R 0-centerLift L x)) *
        ∑ j : Fin 3, TightCutoff.anglePartial L.val δ (R 0-centerLift L x) j*v 0 j : ℝ) : ℂ) := by
  have hd : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hf := ((((raw L δ x).smooth).differentiable (by simp)) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  have ha := TightCutoff.angleLift_derivative L.val δ
    (fun j t ↦ R 0 j+t*v 0 j-centerLift L x j) (fun j ↦ v 0 j) 0 (fun j ↦ by
      convert ((((hasDerivAt_id (0:ℝ)).mul_const (v 0 j)).const_add (R 0 j)).sub_const (centerLift L x j)) using 1 <;> first | rfl | simp only [one_mul])
  have hb := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ha.cos
  have he : ((fun R ↦ (raw L δ x).toFun (project 1 L R)) ∘ fun t : ℝ ↦ R+t • v) =
      (fun t : ℝ ↦ (Real.cos (TightCutoff.angleLift L.val δ
        (fun j ↦ R 0 j+t*v 0 j-centerLift L x j)) : ℂ)) := by
    funext t
    exact congrArg Complex.ofReal (bump_project L δ x (R+t • v))
  rw [he] at hf
  convert hf.unique hb using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_mul,add_zero,Complex.ofRealCLM_apply]
  rfl

lemma raw_partial (L : Length) (δ : ℝ) (x y : Torus L) (j : Fin 3) :
    coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)=
      ((-Real.sin (TightCutoff.angleLift L.val δ (centerLift L y-centerLift L x)) *
        TightCutoff.anglePartial L.val δ (centerLift L y-centerLift L x) j : ℝ) : ℂ) := by
  rw [coordDerivative,raw_fderiv]
  change (Complex.ofReal (-Real.sin _ * ∑ k : Fin 3, _ * (Pi.single j (1:ℝ)) k)) = _
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

lemma raw_partial_sq_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x y : Torus L) (j : Fin 3) :
    ‖coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)‖^2 ≤ 24*Real.pi^2*M^2/δ^2 := by
  rw [raw_partial,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,neg_sq]
  calc
    _ ≤ 1*(TightCutoff.anglePartial L.val δ (centerLift L y-centerLift L x) j)^2 := by
      gcongr
      exact Real.sin_sq_le_one _
    _ ≤ _ := by simpa using TightCutoff.anglePartial_sq_le L.val hδ hM hb (centerLift L y-centerLift L x) j

lemma raw_partial_zero {L : Length} {δ : ℝ} (hδ : 0<δ) (x y : Torus L) (j : Fin 3)
    (hy : y∉TightCutoff.near L.val δ x) :
    coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)=0 := by
  have he : qLift L.val (centerLift L y-centerLift L x)=pairQ L.val y x := by
    rw [← pairQ_coe,centerLift_coe,centerLift_coe]
  have hn : qLift L.val (centerLift L y-centerLift L x)∉Icc ((5/4)*δ^2) ((3/2)*δ^2) := by
    rw [he]
    exact fun h ↦ hy h.2
  rw [raw_partial,TightCutoff.anglePartial_eq_zero L.val hδ hn,mul_zero,Complex.ofReal_zero]

lemma raw_energy_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x : Torus L) :
    (raw L δ x).orbitalEnergy ≤ 3*(24*Real.pi^2*M^2/δ^2)*(4*δ)^3 := by
  have hpart (j : Fin 3) :
      (∫ y : Torus L, ‖coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)‖^2) ≤
        (24*Real.pi^2*M^2/δ^2)*(4*δ)^3 := by
    let f := fun y : Torus L ↦ ‖coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y)‖^2
    have hf : Continuous f := ((continuous_coordDerivative (raw L δ x).smooth (0,j)).comp
      (continuous_pi fun _ ↦ continuous_id)).norm.pow 2
    have hi : Integrable f volume := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have he : (∫ y, f y) = ∫ y in TightCutoff.near L.val δ x, f y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      simp [f,raw_partial_zero hδ x y j hy]
    rw [he]
    calc
      _ ≤ ∫ _y in TightCutoff.near L.val δ x, (24*Real.pi^2*M^2/δ^2) :=
        setIntegral_mono_on hi.integrableOn (integrableOn_const) (TightCutoff.near_measurable _ _ _)
          (fun y _ ↦ raw_partial_sq_le hδ hM hb x y j)
      _ = volume.real (TightCutoff.near L.val δ x)*(24*Real.pi^2*M^2/δ^2) := by simp
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right (TightCutoff.near_volume_le L.val hδ x)
          (show 0 ≤ 24*Real.pi^2*M^2/δ^2 by positivity)
  unfold SmoothMultiplier.orbitalEnergy
  calc
    _ ≤ ∑ _j : Fin 3, (24*Real.pi^2*M^2/δ^2)*(4*δ)^3 := Finset.sum_le_sum fun j _ ↦ hpart j
    _ = _ := by simp; ring

lemma normalized_real (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration 1 L) :
    conj ((normalized L δ x).toFun X)=(normalized L δ x).toFun X := by
  simp [normalized,raw,SmoothMultiplier.ofSmooth]

lemma normalized_norm_sq {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x y : Torus L) :
    ‖(normalized L δ x).orbital y‖^2=(mass L δ x)⁻¹*(bump L δ x y)^2 := by
  change ‖(((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(bump L δ x y : ℂ)‖^2 = _
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    inv_pow,Real.sq_sqrt (mass_pos hδ hδL x).le]

lemma normalized_mass {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x : Torus L) :
    (∫ y : Torus L, ‖(normalized L δ x).orbital y‖^2)=1 := by
  simp_rw [normalized_norm_sq hδ hδL]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (mass_pos hδ hδL x).ne'

lemma normalized_support {L : Length} {δ : ℝ} (hδ : 0<δ) (x : Torus L) :
    tsupport (normalized L δ x).orbital ⊆ TightCutoff.near L.val δ x := by
  apply closure_minimal
  · intro y hy
    by_contra hn
    apply hy
    change (((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(bump L δ x y : ℂ)=0
    rw [bump_eq_zero hδ x hn,Complex.ofReal_zero,mul_zero]
  · exact isClosed_le ((pairQ_continuous L.val).comp
      (continuous_id.prodMk continuous_const)) continuous_const

lemma normalized_bound {L : Length} {δ : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val) (x : Torus L) :
    (normalized L δ x).orbitalBound ≤ (δ^3)⁻¹ := by
  have hs : 0<Real.sqrt (mass L δ x) := Real.sqrt_pos.mpr (mass_pos hδ hδL x)
  have hb : ‖(⟨(normalized L δ x).orbital,(normalized L δ x).orbital_continuous⟩ : C(Torus L,ℂ))‖ ≤
      (Real.sqrt (mass L δ x))⁻¹ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro y
    change ‖(((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(bump L δ x y : ℂ)‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (bump_bounds L δ x y).1]
    exact mul_le_of_le_one_right (by positivity) (bump_bounds L δ x y).2
  calc
    _ ≤ ((Real.sqrt (mass L δ x))⁻¹)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
    _ = (mass L δ x)⁻¹ := by rw [inv_pow,Real.sq_sqrt (mass_pos hδ hδL x).le]
    _ ≤ _ := inv_anti₀ (by positivity) (mass_lower hδ hδL x)

lemma normalized_partial (L : Length) (δ : ℝ) (x y : Torus L) (j : Fin 3) :
    coordDerivative 1 L (normalized L δ x).toFun (0,j) (fun _ ↦ y)=
      (((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*coordDerivative 1 L (raw L δ x).toFun (0,j) (fun _ ↦ y) := by
  unfold coordDerivative
  change (fderiv ℝ (fun R ↦ (((Real.sqrt (mass L δ x))⁻¹ : ℝ) : ℂ)*(raw L δ x).toFun (project 1 L R)) _) _ = _
  rw [fderiv_const_mul (((raw L δ x).smooth.differentiable (by simp)) _)]
  rfl

lemma normalized_energy_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hδL : δ ≤ L.val)
    (hM : 0 ≤ M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x : Torus L) :
    (normalized L δ x).orbitalEnergy ≤ (δ^3)⁻¹*(3*(24*Real.pi^2*M^2/δ^2)*(4*δ)^3) := by
  have he : (normalized L δ x).orbitalEnergy=(mass L δ x)⁻¹*(raw L δ x).orbitalEnergy := by
    unfold SmoothMultiplier.orbitalEnergy
    simp_rw [normalized_partial,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      inv_pow,Real.sq_sqrt (mass_pos hδ hδL x).le,integral_const_mul]
    rw [Finset.mul_sum]
  rw [he]
  apply mul_le_mul
  · exact inv_anti₀ (by positivity) (mass_lower hδ hδL x)
  · exact raw_energy_le hδ hM hb x
  · exact Finset.sum_nonneg fun j _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  · positivity

theorem uniform_orbitals : ∃ B E : ℝ, 0<B ∧ 0<E ∧
    ∀ L : Length, (1:ℝ)/100 ≤ L.val → ∀ x : Torus L,
    (∀ X, conj ((normalized L (1/100) x).toFun X)=(normalized L (1/100) x).toFun X) ∧
    (∫ y : Torus L, ‖(normalized L (1/100) x).orbital y‖^2)=1 ∧
    (normalized L (1/100) x).orbitalBound ≤ B ∧
    (normalized L (1/100) x).orbitalEnergy ≤ E ∧
    tsupport (normalized L (1/100) x).orbital ⊆ TightCutoff.near L.val (1/100) x := by
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  refine ⟨((1/100:ℝ)^3)⁻¹,((1/100:ℝ)^3)⁻¹*(3*(24*Real.pi^2*M^2/(1/100:ℝ)^2)*(4*(1/100:ℝ))^3),
    by positivity,by positivity,?_⟩
  intro L hL x
  exact ⟨normalized_real L _ x,normalized_mass (by norm_num) hL x,
    normalized_bound (by norm_num) hL x,normalized_energy_le (by norm_num) hL hM.le hb x,
    normalized_support (by norm_num) x⟩

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Chi
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
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma dist_coord_le_torusDistance (L : Length) (x y : Torus L) (j : Fin 3) :
    dist (x j) (y j) ≤ torusDistance L x y := by
  calc
    _ = Real.sqrt (dist (x j) (y j)^2) := (Real.sqrt_sq (dist_nonneg)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum
      (fun k _ ↦ sq_nonneg (dist (x k) (y k))) (Finset.mem_univ j))

lemma chi_bounds (L : Length) (δ : ℝ) (x y : Torus L) : 0 ≤ chi L δ x y ∧ chi L δ x y ≤ 1 := by
  constructor
  · exact sq_nonneg _
  · change bump L (8*δ) x y ^ 2 ≤ 1
    nlinarith [(bump_bounds L (8*δ) x y).1,(bump_bounds L (8*δ) x y).2]

lemma chi_eq_one_of_reaches {L : Length} {δ r : ℝ} (hδ : 0<δ) (hrδ : r ≤ δ)
    (x z : Torus L) (hz : ∃ y∈tsupport (normalized L δ x).orbital, torusDistance L y z ≤ 2*r) :
    chi L δ x z=1 := by
  obtain ⟨y,hy,hyz⟩ := hz
  have hyn := TightCutoff.near_subset_box L.val hδ x (normalized_support hδ x hy)
  have hbox : z∈box L.val ((8*δ)/2) x := by
    intro j _
    change dist (z j) (x j) ≤ (8*δ)/2
    have hb : dist (y j) (x j) ≤ 2*δ := (Set.mem_univ_pi.mp hyn) j
    have hg := (dist_coord_le_torusDistance L y z j).trans hyz
    have ht := dist_triangle (z j) (y j) (x j)
    rw [dist_comm (z j) (y j)] at ht
    linarith
  rw [chi,bump_eq_one (by positivity) x hbox,one_pow]

lemma closeLabels_card_le_count {n : ℕ} {L : Length} {δ r : ℝ} (hδ : 0<δ) (hrδ : r ≤ δ)
    (x : Torus L) (X : Configuration n L) :
    ((closeLabels r (normalized L δ x) X).card : ℝ) ≤ count L δ x X := by
  classical
  calc
    _ = ∑ i∈closeLabels r (normalized L δ x) X, chi L δ x (X i) := by
      rw [Finset.sum_eq_card_nsmul (b:= (1:ℝ)) (fun i hi ↦ ?_)]
      · simp
      · exact chi_eq_one_of_reaches hδ hrδ x (X i) (Finset.mem_filter.mp hi).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ ↦ (chi_bounds L δ x (X j)).1)

lemma orbitals_separated {S : Type*} {L : Length} {r : ℝ} (hr : r ≤ 1/100)
    (c : S → Torus L) (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v)) :
    ∀ z v : S, z≠v → ∀ x : Torus L, (normalized L (1/100) (c v)).orbital x≠0 →
      ¬ ∃ y∈tsupport (normalized L (1/100) (c z)).orbital, torusDistance L y x ≤ 2*r := by
  intro z v hzv x hx ⟨y,hy,hyx⟩
  have hxb := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<1/100) (c v)
    (normalized_support (by norm_num) (c v) (subset_closure hx))
  have hyb := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<1/100) (c z)
    (normalized_support (by norm_num) (c z) hy)
  have hd : dist (c z) (c v) ≤ (6:ℝ)/100 := by
    apply (dist_pi_le_iff (by norm_num)).mpr
    intro j
    have hxj : dist (x j) (c v j) ≤ 2*(1/100) := Set.mem_univ_pi.mp hxb j
    have hyj : dist (y j) (c z j) ≤ 2*(1/100) := Set.mem_univ_pi.mp hyb j
    have hyxj := (dist_coord_le_torusDistance L y x j).trans hyx
    have ht := dist_triangle4 (c z j) (y j) (x j) (c v j)
    rw [dist_comm (c z j) (y j)] at ht
    linarith
  linarith [hc z v hzv]

theorem physical_deficiency_oai : ∃ C B E : ℝ, 0<C ∧ 0<B ∧ 0<E ∧
    ∀ (S : Type) [Fintype S] [Nonempty S] [DecidableEq S]
      (n : ℕ) (L : Length) (r : ℝ), 0 < r → r ≤ 1/100 → 0<n → 1/100 ≤ L.val →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ (k m : ℕ), C*B*(k+m)*r^3 ≤ 1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ X ∂volume, u.1 X≠0 → ∀ z, count L (1/100) (c z) X ≤ k) →
    m*Fintype.card S*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))*‖u.1‖^2 ≤
      energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,hC,hdef⟩ := deficiency_penalty_cells
  obtain ⟨B,E,hB,hE,hw⟩ := uniform_orbitals
  refine ⟨C,B,E,hC,hB,hE,?_⟩
  intro S _ _ _ n L r hr hrδ hn hL g hg c hc k m hs u hu hk
  apply hdef S n L r hr hn g hg (fun z ↦ normalized L (1/100) (c z))
    (fun z ↦ (hw L hL (c z)).1) (fun z ↦ (hw L hL (c z)).2.1)
    (orbitals_separated hrδ c hc) k m B E
    (fun z ↦ (hw L hL (c z)).2.2.1) (fun z ↦ (hw L hL (c z)).2.2.2.1) hs u hu
  filter_upwards [hk] with X hX huX z
  exact_mod_cast (closeLabels_card_le_count (by norm_num) hrδ (c z) X).trans (hX huX z)

end HardSphere.CellOrbital

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.CellOrbital.physical_deficiency_oai := @OAI.HardSphere.CellOrbital.physical_deficiency_oai
