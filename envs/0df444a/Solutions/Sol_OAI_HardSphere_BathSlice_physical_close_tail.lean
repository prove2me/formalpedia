-- Prove2me | solution 1 for OAI.HardSphere.BathSlice.physical_close_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:07:17.153437+00:00
-- url     : https://prove2.me/submissions/e6888294-9bf5-4b08-8917-3689ed07eb6b

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_spatial_localized_form

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

lemma norm_add_real_smul_sq (x y : H) (t : ℝ) :
    ‖x + (t : ℂ) • y‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * t * (inner ℂ x y).re + t ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow]
  simp [Complex.norm_real, sq_abs, mul_assoc]

lemma energy_add_real_smul (u v : H × (J → H)) (t : ℝ) :
    energy (u + (t : ℂ) • v) =
      energy u + 2 * t * (gradientPairing u v).re + t ^ 2 * energy v := by
  change (∑ i, ‖u.2 i + (t : ℂ) • v.2 i‖ ^ 2) = _
  simp_rw [norm_add_real_smul_sq]
  simp only [energy, gradientPairing, Finset.sum_add_distrib, Finset.mul_sum,
    Complex.re_sum]

lemma linear_term_zero {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t) : b = 0 := by
  have hd : 0 < a + 1 := by linarith
  have hh := mul_nonneg (h (-b / (a + 1))) (sq_nonneg (a + 1))
  have heq : (a * (-b / (a + 1)) ^ 2 + 2 * b * (-b / (a + 1))) *
      (a + 1) ^ 2 = -(a + 2) * b ^ 2 := by
    field_simp
    ring
  rw [heq] at hh
  have hb := sq_nonneg b
  have hprod := mul_nonneg ha hb
  nlinarith

theorem ground_pairing (M : Submodule ℂ (H × (J → H)))
    (u : H × (J → H)) (hu : u ∈ M) (hnorm : ‖u.1‖ = 1)
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    gradientPairing u v = (energy u : ℂ) * inner ℂ u.1 v.1 := by
  have hre (w : H × (J → H)) (hw : w ∈ M) :
      (gradientPairing u w).re = energy u * (inner ℂ u.1 w.1).re := by
    have ha : 0 ≤ energy w - energy u * ‖w.1‖ ^ 2 :=
      sub_nonneg.mpr (rayleigh M u hmin w hw)
    have hpoly (t : ℝ) : 0 ≤
        (energy w - energy u * ‖w.1‖ ^ 2) * t ^ 2 +
          2 * ((gradientPairing u w).re - energy u * (inner ℂ u.1 w.1).re) * t := by
      have h := rayleigh M u hmin (u + (t : ℂ) • w) (M.add_mem hu (M.smul_mem _ hw))
      rw [energy_add_real_smul] at h
      simp only [Prod.fst_add, Prod.smul_fst, norm_add_real_smul_sq, hnorm, one_pow] at h
      nlinarith
    exact sub_eq_zero.mp (linear_term_zero ha hpoly)
  have hI := hre (Complex.I • v) (M.smul_mem _ hv)
  have hr := hre v hv
  apply Complex.ext
  · simpa using hr
  · simpa [gradientPairing, inner_smul_right, ← Finset.mul_sum, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.mul_im] using hI

end HardSphere.Variational

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_EnergyParallelogram
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

lemma energy_parallelogram (u v : H × (J → H)) :
    energy (u + v) + energy (u - v) = 2 * (energy u + energy v) := by
  change (∑ i, ‖u.2 i + v.2 i‖ ^ 2) + (∑ i, ‖u.2 i - v.2 i‖ ^ 2) = _
  rw [← Finset.sum_add_distrib]
  simp_rw [parallelogram_law_with_norm ℂ]
  simp only [energy, Finset.mul_sum, Finset.sum_add_distrib, mul_add]

theorem minimizer_eq_of_scalar_eq (M : Submodule ℂ (H × (J → H)))
    (u : H × (J → H)) (hu : u ∈ M) (hnorm : ‖u.1‖ = 1)
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) (hscalar : v.1 = u.1)
    (henergy : energy v ≤ energy u) : v = u := by
  have hnormsum : ‖(u + v).1‖ ^ 2 = 4 := by
    have he : (u + v).1 = (2 : ℂ) • u.1 := by simp [hscalar, two_smul]
    rw [he, norm_smul, hnorm]
    norm_num
  have hr := rayleigh M u hmin (u + v) (M.add_mem hu hv)
  rw [hnormsum] at hr
  have hd : energy (u - v) = 0 := by
    have hp := energy_parallelogram u v
    have hn := energy_nonneg (u - v)
    linarith
  apply Prod.ext hscalar
  funext i
  have hi : ‖u.2 i - v.2 i‖ ^ 2 ≤ energy (u - v) :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖u.2 j - v.2 j‖) (Finset.mem_univ i)
  rw [hd] at hi
  have hz : ‖u.2 i - v.2 i‖ = 0 := by nlinarith [norm_nonneg (u.2 i - v.2 i)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

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

theorem IsGroundVector.first_variation {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) (hb : bosonic v.1) :
    (∑ p : Direction N, inner ℂ (u.2 p) (v.2 p)) =
      (energy u : ℂ) * inner ℂ u.1 v.1 := by
  apply Variational.ground_pairing (groundFormSubmodule N L a) u
  · exact mem_groundFormSubmodule.mpr ⟨hu.1, hu.2.1⟩
  · exact hu.2.2.1
  · intro w hw hn
    exact hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn
  · exact mem_groundFormSubmodule.mpr ⟨hv, hb⟩

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

lemma permutationJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (σ : Equiv.Perm (Fin N)) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    permutationJet σ u ∈ dirichletDomain N L a := by
  apply map_mem_closure (permutationJet σ).continuous hu
  rintro _ ⟨f, rfl⟩
  exact ⟨f.permute σ, f.jet_permute σ⟩

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
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PermutationPullbackComp
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
namespace HardSphere

lemma permutationPullback_comp {N : ℕ} {L : Length}
    (σ τ : Equiv.Perm (Fin N)) (ψ : ScalarL2 N L) :
    permutationPullback σ (permutationPullback τ ψ) = permutationPullback (σ * τ) ψ := by
  change Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (Lp.compMeasurePreserving _ (measurePreserving_permute τ) ψ) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  rfl

lemma inner_permutationPullback {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (ψ φ : ScalarL2 N L) :
    inner ℂ (permutationPullback σ ψ) (permutationPullback σ φ) = inner ℂ ψ φ :=
  (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_permute σ)).inner_map_map ψ φ

lemma gradientPairing_permutationJet {N : ℕ} {L : Length}
    (σ : Equiv.Perm (Fin N)) (u v : Jet N L) :
    Variational.gradientPairing (permutationJet σ u) (permutationJet σ v) =
      Variational.gradientPairing u v := by
  change (∑ p : Direction N, inner ℂ (permutationPullback σ (u.2 (σ.symm p.1, p.2)))
    (permutationPullback σ (v.2 (σ.symm p.1, p.2)))) = _
  simp only [inner_permutationPullback]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ inner ℂ (u.2 p) (v.2 p))

theorem IsGroundVector.permutationInvariant {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (σ : Equiv.Perm (Fin N)) :
    permutationJet σ u = u := by
  have hs : (permutationJet σ u).1 = u.1 := (bosonic_iff_pullback u.1).mp hu.2.1 σ
  have hv : permutationJet σ u ∈ groundFormSubmodule N L a := by
    rw [mem_groundFormSubmodule]
    exact ⟨permutationJet_mem_domain σ hu.1, hs ▸ hu.2.1⟩
  exact Variational.minimizer_eq_of_scalar_eq (groundFormSubmodule N L a) u
    (mem_groundFormSubmodule.mpr ⟨hu.1, hu.2.1⟩) hu.2.2.1
    (fun w hw hn ↦ hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn)
    (permutationJet σ u) hv hs (le_of_eq (energy_permutationJet σ u))

lemma bosonic_sum_permutationPullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic (∑ σ : Equiv.Perm (Fin N), permutationPullback σ ψ) := by
  rw [bosonic_iff_pullback]
  intro τ
  simp only [map_sum, permutationPullback_comp]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ ↦ permutationPullback σ ψ)

lemma gradientPairing_sum_right {N : ℕ} {L : Length} {I : Type*} [Fintype I]
    (u : Jet N L) (v : I → Jet N L) :
    Variational.gradientPairing u (∑ i, v i) =
      ∑ i, Variational.gradientPairing u (v i) := by
  simp only [Variational.gradientPairing, Prod.snd_sum, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

theorem IsGroundVector.full_first_variation {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) :
    (∑ p : Direction N, inner ℂ (u.2 p) (v.2 p)) =
      (energy u : ℂ) * inner ℂ u.1 v.1 := by
  let w : Jet N L := ∑ σ : Equiv.Perm (Fin N), permutationJet σ v
  have hwd : w ∈ dirichletDomain N L a := by
    change w ∈ dirichletSubmodule N L a
    exact Submodule.sum_mem _ fun σ _ ↦ permutationJet_mem_domain σ hv
  have hwb : bosonic w.1 := by
    dsimp only [w]
    rw [Prod.fst_sum]
    exact bosonic_sum_permutationPullback v.1
  have hgp (σ : Equiv.Perm (Fin N)) :
      Variational.gradientPairing u (permutationJet σ v) = Variational.gradientPairing u v := by
    calc
      _ = Variational.gradientPairing (permutationJet σ u) (permutationJet σ v) := by
        rw [hu.permutationInvariant σ]
      _ = _ := gradientPairing_permutationJet σ u v
  have hip (σ : Equiv.Perm (Fin N)) :
      inner ℂ u.1 (permutationJet σ v).1 = inner ℂ u.1 v.1 := by
    calc
      _ = inner ℂ (permutationPullback σ u.1) (permutationPullback σ v.1) := by
        rw [(bosonic_iff_pullback u.1).mp hu.2.1 σ]; rfl
      _ = _ := inner_permutationPullback σ u.1 v.1
  have he := hu.first_variation w hwd hwb
  change Variational.gradientPairing u w = _ at he
  simp only [w, gradientPairing_sum_right, hgp, Prod.fst_sum, inner_sum, hip,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hc
  change (Fintype.card (Equiv.Perm (Fin N)) : ℂ) * Variational.gradientPairing u v = _
  rw [he]
  ring

end HardSphere

end
end
end
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

lemma clm_mul (f g : α → ℂ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ)
    (u : Lp ℂ 2 μ) : clm (f * g) (hg.mul hf) u = clm f hf (clm g hg u) := by
  apply Lp.ext
  filter_upwards [coe_clm (f * g) (hg.mul hf) u, coe_clm f hf (clm g hg u),
    coe_clm g hg u] with x h1 h2 h3
  simp only [h1, h2, h3, Pi.mul_apply, mul_assoc]

lemma inner_clm_right (f : α → ℂ) (hf : MemLp f ∞ μ) (u v : Lp ℂ 2 μ) :
    inner ℂ u (clm f hf v) = inner ℂ (clm (fun x ↦ conj (f x)) hf.star u) v := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_clm f hf v, coe_clm (fun x ↦ conj (f x)) hf.star u] with x h1 h2
  simp only [h1, h2, RCLike.inner_apply, map_mul, starRingEnd_self_apply]
  ring

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
namespace L2Multiplier
open MeasureTheory
open scoped ComplexConjugate ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma inner_clm_real_right (f : α → ℂ) (hf : MemLp f ∞ μ)
    (hreal : ∀ x, conj (f x) = f x) (u v : Lp ℂ 2 μ) :
    inner ℂ u (clm f hf v) = inner ℂ (clm f hf u) v := by
  simpa only [show (fun x ↦ conj (f x)) = f from funext hreal] using
    inner_clm_right f hf u v

lemma clm_comm (f g : α → ℂ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ)
    (u : Lp ℂ 2 μ) : clm f hf (clm g hg u) = clm g hg (clm f hf u) := by
  rw [← clm_mul, ← clm_mul]
  congr 2
  exact mul_comm f g

end L2Multiplier
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal
lemma SmoothMultiplier.partial_real {N : ℕ} {L : Length} (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) (p : Direction N) (X : Configuration N L) :
    conj (coordDerivative N L f.toFun p X) = coordDerivative N L f.toFun p X := by
  have he : (fun X ↦ conj (f.toFun X)) = f.toFun := funext hf
  rw [← congrFun (coordDerivative_conj (f.smooth.differentiable (by simp)) p) X, he]

lemma SmoothMultiplier.inner_onScalar_right {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (hf : ∀ X, conj (f.toFun X) = f.toFun X)
    (u v : ScalarL2 N L) : inner ℂ u (f.onScalar v) = inner ℂ (f.onScalar u) v :=
  L2Multiplier.inner_clm_real_right _ _ hf u v

lemma SmoothMultiplier.onScalar_derivativeScalar_comm {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (p : Direction N) (u : ScalarL2 N L) :
    f.onScalar (f.derivativeScalar p u) = f.derivativeScalar p (f.onScalar u) :=
  L2Multiplier.clm_comm _ _ _ _ u

theorem IsGroundVector.smooth_multiplier_identity {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) :
    energy (f.onJet u) - energy u * ‖f.onScalar u.1‖ ^ 2 =
      ∑ p : Direction N, ‖f.derivativeScalar p u.1‖ ^ 2 := by
  have hv := f.onJet_mem_domain (f.onJet_mem_domain hu.1)
  have he := hu.full_first_variation (f.onJet (f.onJet u)) hv
  have hnorm (x : ScalarL2 N L) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  have hpair (p : Direction N) :
      (inner ℂ (u.2 p) ((f.onJet (f.onJet u)).2 p)).re =
        ‖f.onScalar (u.2 p)‖ ^ 2 +
          2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re := by
    rw [f.onJet_snd, f.onJet_snd, f.onJet_fst, map_add,
      inner_add_right, inner_add_right, ← f.onScalar_derivativeScalar_comm,
      f.inner_onScalar_right hf (u.2 p) (f.onScalar (u.2 p)),
      f.inner_onScalar_right hf (u.2 p) (f.derivativeScalar p u.1)]
    simp only [Complex.add_re, hnorm]
    ring
  have hs : (inner ℂ u.1 (f.onJet (f.onJet u)).1).re = ‖f.onScalar u.1‖ ^ 2 := by
    rw [f.onJet_fst, f.onJet_fst, f.inner_onScalar_right hf, hnorm]
  have her := congrArg Complex.re he
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hs, hpair] at her
  change (∑ p, ‖(f.onJet u).2 p‖ ^ 2) - energy u * ‖f.onScalar u.1‖ ^ 2 = _
  simp only [f.onJet_snd, norm_add_sq (𝕜 := ℂ)]
  rw [← her]
  change (∑ p, (‖f.onScalar (u.2 p)‖ ^ 2 +
      2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re +
      ‖f.derivativeScalar p u.1‖ ^ 2)) -
    (∑ p, (‖f.onScalar (u.2 p)‖ ^ 2 +
      2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re)) = _
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

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

lemma SmoothMultiplier.gradient_norm_le {S : Type*} {n : ℕ} {L : Length}
    (A : Finset S) (f : SmoothMultiplier n L) (g : S → SmoothMultiplier n L) (C : ℝ)
    (hfg : ∀ X, (∑ p : Direction n, ‖coordDerivative n L f.toFun p X‖^2) ≤
      C*∑ s∈A, ‖(g s).toFun X‖^2) (u : ScalarL2 n L) :
    (∑ p : Direction n, ‖f.derivativeScalar p u‖^2) ≤ C*∑ s∈A, ‖(g s).onScalar u‖^2 := by
  have hi (p : Direction n) : Integrable (fun X ↦ ‖(f.derivativeScalar p u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  have hj (s : S) : Integrable (fun X ↦ ‖((g s).onScalar u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  simp_rw [IndicatorStrong.norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun p _ ↦ hi p),
    ← integral_finsetSum A (fun s _ ↦ hj s),← integral_const_mul]
  apply integral_mono_ae (integrable_finsetSum _ (fun p _ ↦ hi p))
    ((integrable_finsetSum _ (fun s _ ↦ hj s)).const_mul C)
  have hd : ∀ᵐ X ∂volume, ∀ p, (f.derivativeScalar p u) X=coordDerivative n L f.toFun p X*u X :=
    ae_all_iff.mpr (fun p ↦ f.coe_derivativeScalar p u)
  have hg : ∀ᵐ X ∂volume, ∀ s∈A, ((g s).onScalar u) X=(g s).toFun X*u X :=
    (ae_ball_iff A.countable_toSet).mpr (fun s _ ↦ (g s).coe_onScalar u)
  filter_upwards [hd,hg] with X hX hY
  simp_rw [hX,norm_mul,mul_pow]
  have he : (∑ s∈A, ‖((g s).onScalar u) X‖^2)=
      (∑ s∈A, ‖(g s).toFun X‖^2)*‖u X‖^2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s hs ↦ by rw [hY s hs,norm_mul,mul_pow]
  rw [he,← Finset.sum_mul,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hfg X) (sq_nonneg _)

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

lemma norm_sq_sum_of_disjoint {S : Type*} [DecidableEq S] (A : Finset S) (f : S → ℂ)
    (hf : ∀ s∈A, ∀ z∈A, s≠z → f s=0 ∨ f z=0) : ‖∑ s∈A, f s‖^2=∑ s∈A, ‖f s‖^2 := by
  by_cases h : ∃ s∈A, f s≠0
  · obtain ⟨s,hs,hfs⟩ := h
    have hz : ∀ z∈A, z≠s → f z=0 := by
      intro z hz hzs
      exact (hf z hz s hs hzs).resolve_right hfs
    rw [Finset.sum_eq_single s (fun z hza hzs ↦ hz z hza hzs) (by simp_all)]
    rw [Finset.sum_eq_single s (fun z hza hzs ↦ by rw [hz z hza hzs,norm_zero]; norm_num) (by simp_all)]
  · push Not at h
    rw [Finset.sum_eq_zero (fun s hs ↦ h s hs)]
    simp only [norm_zero,zero_pow (by norm_num : 2≠0)]
    symm
    exact Finset.sum_eq_zero fun s hs ↦ by rw [h s hs,norm_zero]; norm_num

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

lemma profile_one {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t ≤ h) : profile h t=1 := by
  rw [profile,Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos]; exact (div_le_one hh).mpr ht)]
  ring

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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

lemma euclideanTorusPoint_dist (L : Length) (x y : Torus L) :
    dist (euclideanTorusPoint L x) (euclideanTorusPoint L y)=torusDistance L x y :=
  PiLp.dist_eq_of_L2 _ _

lemma spatialSiteDistance_nonneg (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    0≤ spatialSiteDistance L A x := Metric.infDist_nonneg

lemma spatialSiteDistance_le (L : Length) (A : Finset (Torus L)) (x y : Torus L) (hy : y∈A) :
    spatialSiteDistance L A x≤torusDistance L x y := by
  rw [←euclideanTorusPoint_dist]
  exact Metric.infDist_le_dist_of_mem ⟨y,hy,rfl⟩

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadiusLaw
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

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

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridActivePenalty
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma coordinate_distance_le (L : Length) (x y : Torus L) (q : Fin 3) :
    dist (x q) (y q)≤torusDistance L x y := by
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun t _ ↦ sq_nonneg (dist (x t) (y t))) (Finset.mem_univ q)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalizedNearLabels
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter
open scoped ENNReal

lemma measurable_close_predicate {n : ℕ} {L : Length} (s : ℝ) (i k : Fin n) :
    MeasurableSet {X : Configuration n L | torusDistance L (X k) (X i)≤2*s} := by
  have hc : Continuous (fun X : Configuration n L ↦ torusDistance L (X k) (X i)) :=
    by unfold torusDistance; fun_prop
  exact measurableSet_le hc.measurable measurable_const

lemma measurable_localized_near_predicate {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) (i : Fin n) :
    MeasurableSet {X : Configuration n L | A.Nonempty ∧ spatialSiteDistance L A (X i)≤6 ∧
      ∃ k : Fin n, k≠i ∧ torusDistance L (X k) (X i)≤2*s} := by
  simp only [Set.ofPred_exists,Set.ofPred_and]
  refine (MeasurableSet.const _).inter ((measurableSet_le
    ((spatialSiteDistance_lipschitz L A).continuous.comp (continuous_apply i)).measurable measurable_const).inter ?_)
  exact MeasurableSet.iUnion (fun k ↦ (MeasurableSet.const _).inter (measurable_close_predicate s i k))

lemma localizedNearLabels_card_measurable {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) :
    Measurable (fun X : Configuration n L ↦ (localizedNearLabels L A s X).card) := by
  classical
  have h (i : Fin n) : Measurable (fun X : Configuration n L ↦
      if A.Nonempty ∧ spatialSiteDistance L A (X i)≤6 ∧
        ∃ k : Fin n, k≠i ∧ torusDistance L (X k) (X i)≤2*s then (1:ℕ) else 0) :=
    Measurable.ite (measurable_localized_near_predicate L A s i) measurable_const measurable_const
  have hh := Finset.measurable_sum (s:=Finset.univ) (fun i _ ↦ h i)
  simpa only [localizedNearLabels,Finset.card_eq_sum_ones,Finset.sum_filter] using hh

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_LatticeExponentialSum
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal
noncomputable section

lemma latticeExponential_summable : Summable (fun z : ℤ ↦ Real.exp (-|(z:ℝ)|/3)) := by
  have h : Summable (fun n : ℕ ↦ Real.exp (-(n:ℝ)/3)) := by
    have hg := summable_geometric_of_abs_lt_one (r:=Real.exp (-1/3)) (by
      rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; norm_num)
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  apply Summable.of_nat_of_neg
  · simpa using h
  · simpa using h

lemma latticeExponentialSum_pos : 0<latticeExponentialSum := by
  have h := latticeExponential_summable.le_tsum 0 (fun _ _ ↦ (Real.exp_pos _).le)
  simp only [Int.cast_zero,abs_zero,neg_zero,zero_div,Real.exp_zero] at h
  exact lt_of_lt_of_le zero_lt_one h

lemma periodicLatticeIndex_injective {K : ℕ} {L : Length} (x : AddCircle L.val) :
    Function.Injective (periodicLatticeIndex (K:=K) L x) := by
  intro v w hvw
  have h := congrArg (fun z : ℤ ↦ (z+⌊((AddCircle.equivIco L.val 0) x).val-1/2⌋)%(K:ℤ)) hvw
  simp only [periodicLatticeIndex,sub_add_cancel,Int.sub_mul_emod_self_right] at h
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast v.isLt),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast w.isLt)] at h
  exact Fin.ext (by exact_mod_cast h)

lemma periodicLatticeIndex_bound {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (x : AddCircle L.val) (v : Fin K) :
    |(periodicLatticeIndex L x v:ℝ)|≤dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x+1 := by
  let t := ((AddCircle.equivIco L.val 0) x).val
  let δ := t-1/2-(⌊t-1/2⌋:ℝ)
  have hδ0 : 0≤δ := Int.fract_nonneg (t-1/2)
  have hδ1 : δ<1 := Int.fract_lt_one (t-1/2)
  have hδ : |δ|≤1 := by rw [abs_of_nonneg hδ0]; exact hδ1.le
  have hd : dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x=
      |(periodicLatticeIndex L x v:ℝ)-δ| := by
    conv_lhs => rw [←(show (t:AddCircle L.val)=x from AddCircle.coe_equivIco)]
    rw [dist_eq_norm,←QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    congr 1
    dsimp [periodicLatticeIndex,δ,t]
    push_cast
    rw [←hL]
    simp only [Int.fract]
    ring
  rw [hd]
  calc
    _ = |((periodicLatticeIndex L x v:ℝ)-δ)+δ| := by congr 1; ring
    _ ≤ |(periodicLatticeIndex L x v:ℝ)-δ|+|δ| := abs_add_le _ _
    _ ≤ _ := add_le_add le_rfl hδ

lemma circle_lattice_exponential_bound {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (x : AddCircle L.val) :
    (∑ v : Fin K, Real.exp (-dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x/3))≤
      Real.exp (1/3)*latticeExponentialSum := by
  classical
  calc
    _ ≤ ∑ v : Fin K, Real.exp (1/3)*Real.exp (-|(periodicLatticeIndex L x v:ℝ)|/3) := by
      apply Finset.sum_le_sum
      intro v _
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := periodicLatticeIndex_bound hL x v
      linarith only [h]
    _ = Real.exp (1/3)*∑ v : Fin K, Real.exp (-|(periodicLatticeIndex L x v:ℝ)|/3) := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [←Finset.sum_image (f:=fun z : ℤ ↦ Real.exp (-|(z:ℝ)|/3)) (s:=Finset.univ) (periodicLatticeIndex_injective x).injOn]
      exact latticeExponential_summable.sum_le_tsum _ (fun _ _ ↦ (Real.exp_pos _).le)

lemma torus_exp_le_coordinate_exp (L : Length) (x y : Torus L) :
    Real.exp (-torusDistance L x y)≤Real.exp (-dist (x 0) (y 0)/3)*
      Real.exp (-dist (x 1) (y 1)/3)*Real.exp (-dist (x 2) (y 2)/3) := by
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h0 := coordinate_distance_le L x y 0
  have h1 := coordinate_distance_le L x y 1
  have h2 := coordinate_distance_le L x y 2
  linarith only [h0,h1,h2]

theorem unitGrid_exponential_bound : ∃ C : ℝ, 0<C ∧
    ∀ (K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ x : Torus L,
      (∑ v : CubeCell K, Real.exp (-torusDistance L (unitCenter L v) x))≤C := by
  let B := Real.exp (1/3)*latticeExponentialSum
  have hB : 0<B := mul_pos (Real.exp_pos _) latticeExponentialSum_pos
  refine ⟨B^3,pow_pos hB _,?_⟩
  intro K L hL x
  let f := fun (j : Fin 3) (v : Fin K) ↦ Real.exp (-dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) (x j)/3)
  have hb (j : Fin 3) : (∑ v, f j v)≤B := circle_lattice_exponential_bound hL (x j)
  have hn (j : Fin 3) : 0≤∑ v, f j v := Finset.sum_nonneg (fun _ _ ↦ (Real.exp_pos _).le)
  calc
    _ ≤ ∑ v : CubeCell K, f 0 v.1*f 1 v.2.1*f 2 v.2.2 := by
      apply Finset.sum_le_sum
      intro v _
      exact torus_exp_le_coordinate_exp L (unitCenter L v) x
    _ = (∑ v, f 0 v)*(∑ v, f 1 v)*(∑ v, f 2 v) := by
      simp_rw [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul]
      rw [←Fintype.sum_mul_sum]
    _ ≤ B*B*B := mul_le_mul (mul_le_mul (hb 0) (hb 1) (hn 1) hB.le) (hb 2) (hn 2) (mul_nonneg hB.le hB.le)
    _ = B^3 := by ring

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
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_FinsetSeparatedNet
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma finset_separated_net {ι : Type*} [DecidableEq ι] (A : Finset ι) (d : ι → ι → ℝ)
    (hd : ∀ i j, d i j=d j i) (hdiag : ∀ i, d i i=0) {R : ℝ} (hR : 0<R) :
    ∃ B : Finset ι, B⊆A ∧ (∀ i∈B, ∀ j∈B, i≠j → R≤d i j) ∧
      ∀ i∈A, ∃ j∈B, d i j<R := by
  classical
  let P : Finset ι → Prop := fun B ↦ ∀ i∈B, ∀ j∈B, i≠j → R≤d i j
  let S := A.powerset.filter P
  have hS : S.Nonempty := ⟨∅,by simp [S,P]⟩
  obtain ⟨B,hBS,hmax⟩ := S.exists_max_image Finset.card hS
  have hBA : B⊆A := Finset.mem_powerset.mp (Finset.mem_filter.mp hBS).1
  have hBP : P B := (Finset.mem_filter.mp hBS).2
  refine ⟨B,hBA,hBP,?_⟩
  intro i hi
  by_contra hn
  have hall : ∀ j∈B, R≤d i j := by
    intro j hj
    by_contra hlt
    exact hn ⟨j,hj,lt_of_not_ge hlt⟩
  have hin : i∉B := by
    intro hiB
    have hh := hall i hiB
    rw [hdiag] at hh
    exact (not_le_of_gt hR) hh
  have hPi : P (insert i B) := by
    intro j hj k hk hjk
    rcases Finset.mem_insert.mp hj with hji | hjB
    · subst j
      rcases Finset.mem_insert.mp hk with hki | hkB
      · exact (hjk hki.symm).elim
      · exact hall k hkB
    · rcases Finset.mem_insert.mp hk with hki | hkB
      · subst k
        rw [hd j i]
        exact hall j hjB
      · exact hBP j hjB k hkB hjk
  have hmem : insert i B∈S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hBA),hPi⟩
  have hh := hmax (insert i B) hmem
  rw [Finset.card_insert_of_notMem hin] at hh
  omega

theorem unitGrid_separated_subset : ∃ Q : ℕ, 0<Q ∧
    ∀ (K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ A : Finset (CubeCell K),
      ∃ B : Finset (CubeCell K), B⊆A ∧
        (∀ v∈B, ∀ w∈B, v≠w → 20≤torusDistance L (unitCenter L v) (unitCenter L w)) ∧
        (A.card:ℝ)≤(Q:ℝ)*(B.card:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := unitGrid_exponential_bound
  let Q : ℕ := ⌈Real.exp 20*C⌉₊+1
  have hQ : 0<Q := Nat.succ_pos _
  have hQB : Real.exp 20*C≤(Q:ℝ) := by
    exact (Nat.le_ceil _).trans (by dsimp [Q]; push_cast; linarith)
  refine ⟨Q,hQ,?_⟩
  intro K L hL A
  obtain ⟨B,hBA,hB,hcover⟩ := finset_separated_net A
    (fun v w ↦ torusDistance L (unitCenter L v) (unitCenter L w))
    (fun v w ↦ torusDistance_comm L _ _) (fun v ↦ by simp [torusDistance]) (by norm_num : (0:ℝ)<20)
  refine ⟨B,hBA,hB,?_⟩
  have hpoint (v : CubeCell K) (hv : v∈A) :
      1≤Real.exp 20*∑ w∈B, Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)) := by
    obtain ⟨w,hw,hd⟩ := hcover v hv
    calc
      _ ≤ Real.exp (20-torusDistance L (unitCenter L v) (unitCenter L w)) :=
        Real.one_le_exp (by linarith only [hd])
      _ = Real.exp 20*Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)) := by
        rw [sub_eq_add_neg,Real.exp_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f:=fun w : CubeCell K ↦ Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)))
          (fun _ _ ↦ (Real.exp_pos _).le) hw) (Real.exp_pos 20).le
  calc
    _ = ∑ _v∈A, (1:ℝ) := by simp
    _ ≤ ∑ v∈A, Real.exp 20*∑ w∈B, Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)) :=
      Finset.sum_le_sum hpoint
    _ = Real.exp 20*∑ w∈B, ∑ v∈A, Real.exp (-torusDistance L (unitCenter L v) (unitCenter L w)) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ Real.exp 20*∑ _w∈B, C := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 20).le
      apply Finset.sum_le_sum
      intro w _
      exact (Finset.sum_le_univ_sum_of_nonneg (fun v : CubeCell K ↦ (Real.exp_pos (-torusDistance L (unitCenter L v) (unitCenter L w))).le)).trans (hbound K L hL _)
    _ = (Real.exp 20*C)*(B.card:ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hQB (Nat.cast_nonneg _)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_NormalizedNearestSeparated
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma normalized_nearest_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : x≠0) (hy : y≠0) (hxy : ‖x‖≤‖x-y‖) (hyx : ‖y‖≤‖x-y‖) :
    1≤‖‖x‖⁻¹ • x-‖y‖⁻¹ • y‖ := by
  have aux {x y : E} (hx : x≠0) (hy : y≠0) (h : ‖y‖≤‖x‖) (hd : ‖x‖≤‖x-y‖) :
      1≤‖‖x‖⁻¹ • x-‖y‖⁻¹ • y‖ := by
    have hx0 : 0<‖x‖ := norm_pos_iff.mpr hx
    have hy0 : 0<‖y‖ := norm_pos_iff.mpr hy
    have he : x-y=‖y‖ • (‖x‖⁻¹ • x-‖y‖⁻¹ • y)+(‖x‖-‖y‖) • (‖x‖⁻¹ • x) := by
      rw [smul_sub,sub_smul,smul_smul,smul_smul,smul_smul,
        mul_inv_cancel₀ hy0.ne',mul_inv_cancel₀ hx0.ne',one_smul,one_smul]
      abel
    have ht := norm_add_le (‖y‖ • (‖x‖⁻¹ • x-‖y‖⁻¹ • y)) ((‖x‖-‖y‖) • (‖x‖⁻¹ • x))
    rw [←he,norm_smul,norm_smul,Real.norm_of_nonneg hy0.le,
      Real.norm_of_nonneg (sub_nonneg.mpr h)] at ht
    have hn : ‖‖x‖⁻¹ • x‖=1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hx0.le),inv_mul_cancel₀ hx0.ne']
    rw [hn,mul_one] at ht
    nlinarith only [ht,hd,hy0]
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact aux hx hy h hxy
  · have hd : ‖y‖≤‖y-x‖ := by simpa only [norm_sub_rev] using hyx
    simpa only [norm_sub_rev] using aux hy hx h hd

lemma nearest_incoming_card {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (I : Finset ι) (v : ι→E)
    (h0 : ∀ i∈I, v i≠0)
    (hne : ∀ i∈I, ∀ j∈I, i≠j → ‖v i‖≤‖v i-v j‖) :
    I.card≤5^Module.finrank ℝ E := by
  classical
  let d : ι→E := fun i ↦ ‖v i‖⁻¹ • v i
  have hsep : ∀ i∈I, ∀ j∈I, i≠j → 1≤‖d i-d j‖ := by
    intro i hi j hj hij
    exact normalized_nearest_separated (h0 i hi) (h0 j hj) (hne i hi j hj hij)
      (by simpa only [norm_sub_rev] using hne j hj i hi hij.symm)
  have hinj : Set.InjOn d I := by
    intro i hi j hj hd
    by_contra hn
    have hh := hsep i hi j hj hn
    rw [hd,sub_self,norm_zero] at hh
    norm_num at hh
  rw [←Finset.card_image_of_injOn hinj]
  apply Besicovitch.card_le_of_separated
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    dsimp [d]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr (h0 i hi))]
    norm_num
  · intro x hx y hy hxy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    exact hsep i hi j hj (fun hij ↦ hxy (congrArg d hij))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CenteredCircleLift
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma centeredCircleLift_coe (L : Length) (x : AddCircle L.val) :
    (centeredCircleLift L x : AddCircle L.val)=x := by
  unfold centeredCircleLift
  rw [AddCircle.coe_sub,←zsmul_eq_mul,AddCircle.coe_zsmul,AddCircle.coe_period,zsmul_zero,sub_zero]
  exact AddCircle.coe_equivIco

lemma centeredCircleLift_abs (L : Length) (x : AddCircle L.val) :
    |centeredCircleLift L x|=‖x‖ := by
  conv_rhs => rw [←(show ((((AddCircle.equivIco L.val 0) x).val):AddCircle L.val)=x from AddCircle.coe_equivIco)]
  exact (AddCircle.norm_eq L.val).symm

lemma centeredTorusVector_norm (L : Length) (x c : Torus L) :
    ‖centeredTorusVector L x c‖=torusDistance L x c := by
  rw [EuclideanSpace.norm_eq]
  unfold torusDistance
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  change ‖centeredCircleLift L (x q-c q)‖^2=dist (x q) (c q)^2
  rw [Real.norm_eq_abs,centeredCircleLift_abs,dist_eq_norm]

lemma centeredTorusVector_coe (L : Length) (x c : Torus L) (q : Fin 3) :
    ((centeredTorusVector L x c q):AddCircle L.val)=x q-c q :=
  centeredCircleLift_coe L _

lemma centeredTorusVector_distance (L : Length) (x y c : Torus L) :
    torusDistance L x y≤‖centeredTorusVector L x c-centeredTorusVector L y c‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold torusDistance
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro q _
  have hcoe : (((centeredTorusVector L x c q-centeredTorusVector L y c q):ℝ):AddCircle L.val)=x q-y q := by
    rw [AddCircle.coe_sub,centeredTorusVector_coe,centeredTorusVector_coe]
    abel
  have hnorm : dist (x q) (y q)≤‖centeredTorusVector L x c q-centeredTorusVector L y c q‖ := by
    rw [dist_eq_norm,←hcoe]
    exact QuotientAddGroup.norm_mk_le_norm
  exact (sq_le_sq₀ dist_nonneg (norm_nonneg _)).mpr hnorm

theorem torus_nearest_incoming_card {ι : Type*} [DecidableEq ι]
    (L : Length) (X : ι→Torus L) (c : Torus L) (I : Finset ι)
    (h0 : ∀ i∈I, X i≠c)
    (hne : ∀ i∈I, ∀ j∈I, i≠j → torusDistance L (X i) c≤torusDistance L (X i) (X j)) :
    I.card≤125 := by
  have hz : ∀ i∈I, centeredTorusVector L (X i) c≠0 := by
    intro i hi he
    apply h0 i hi
    funext q
    have h := centeredTorusVector_coe L (X i) c q
    rw [he] at h
    exact sub_eq_zero.mp (by simpa using h.symm)
  have hsep : ∀ i∈I, ∀ j∈I, i≠j →
      ‖centeredTorusVector L (X i) c‖≤‖centeredTorusVector L (X i) c-centeredTorusVector L (X j) c‖ := by
    intro i hi j hj hij
    rw [centeredTorusVector_norm]
    exact (hne i hi j hj hij).trans (centeredTorusVector_distance L (X i) (X j) c)
  have h := nearest_incoming_card I (fun i ↦ centeredTorusVector L (X i) c) hz hsep
  simpa using h

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma nearestLabel_fiber_card (L : Length) (X : ι→Torus L) (hX : Function.Injective X) (k : ι) :
    (Finset.univ.filter (fun i ↦ nearestLabel L X i=k)).card≤125 := by
  apply torus_nearest_incoming_card L X (X k)
  · intro i hi
    have hik : i≠k := by
      intro he
      have hm := nearestLabel_ne L X i
      exact hm ((Finset.mem_filter.mp hi).2.trans he.symm)
    exact fun he ↦ hik (hX he)
  · intro i hi j _ hij
    have hm := nearestParticleDistance_le L X i j hij.symm
    simpa only [nearestParticleDistance,(Finset.mem_filter.mp hi).2] using hm

lemma torusDistance_triangle' (L : Length) (x y z : Torus L) :
    torusDistance L x z≤torusDistance L x y+torusDistance L y z := by
  simpa only [euclideanTorusPoint_dist] using dist_triangle
    (euclideanTorusPoint L x) (euclideanTorusPoint L y) (euclideanTorusPoint L z)

lemma nearestParticleDistance_sub_le (L : Length) (X Y : ι→Torus L) (i : ι) :
    nearestParticleDistance L Y i-nearestParticleDistance L X i≤
      torusDistance L (X i) (Y i)+torusDistance L (X (nearestLabel L X i)) (Y (nearestLabel L X i)) := by
  have hm := nearestParticleDistance_le L Y i (nearestLabel L X i) (nearestLabel_ne L X i)
  have ht := torusDistance_triangle' L (Y i) (X i) (Y (nearestLabel L X i))
  have ht' := torusDistance_triangle' L (X i) (X (nearestLabel L X i)) (Y (nearestLabel L X i))
  have hs : torusDistance L (Y i) (X i)=torusDistance L (X i) (Y i) := by
    simp only [torusDistance,dist_comm]
  rw [hs] at ht
  dsimp [nearestParticleDistance]
  dsimp [nearestParticleDistance] at hm
  linarith only [hm,ht,ht']

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_FiniteFiberSum
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma finite_fiber_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι→ι) (a : ι→ℝ) (C : ℕ) (ha : ∀ i, 0≤a i)
    (hc : ∀ k, (Finset.univ.filter (fun i ↦ f i=k)).card≤C) :
    (∑ i, a (f i))≤(C:ℝ)*∑ i, a i := by
  rw [←Finset.sum_fiberwise Finset.univ f (fun i ↦ a (f i)),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  calc
    _ = ∑ i∈Finset.univ.filter (fun i ↦ f i=k), a k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ((Finset.univ.filter (fun i ↦ f i=k)).card:ℝ)*a k := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc k) (ha k)

theorem nearestParticleDistance_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (L : Length) (X Y : ι→Torus L) (hX : Function.Injective X) (hY : Function.Injective Y) :
    (∑ i, (nearestParticleDistance L Y i-nearestParticleDistance L X i)^2)≤
      502*∑ i, torusDistance L (X i) (Y i)^2 := by
  let δ : ι→ℝ := fun i ↦ torusDistance L (X i) (Y i)
  have hδ (i : ι) : 0≤δ i := Real.sqrt_nonneg _
  have hpoint (i : ι) : (nearestParticleDistance L Y i-nearestParticleDistance L X i)^2≤
      2*(δ i)^2+2*(δ (nearestLabel L X i))^2+2*(δ (nearestLabel L Y i))^2 := by
    have hp := nearestParticleDistance_sub_le L X Y i
    have hm := nearestParticleDistance_sub_le L Y X i
    have hs (j : ι) : torusDistance L (Y j) (X j)=δ j := by simp only [δ,torusDistance,dist_comm]
    change nearestParticleDistance L Y i-nearestParticleDistance L X i≤δ i+δ (nearestLabel L X i) at hp
    simp only [hs] at hm
    by_cases h : 0≤nearestParticleDistance L Y i-nearestParticleDistance L X i
    · have hsq := (sq_le_sq₀ h (add_nonneg (hδ i) (hδ _))).mpr hp
      nlinarith only [hsq,sq_nonneg (δ i-δ (nearestLabel L X i)),sq_nonneg (δ (nearestLabel L Y i))]
    · have h' : 0≤nearestParticleDistance L X i-nearestParticleDistance L Y i := by linarith only [h]
      have hsq := (sq_le_sq₀ h' (add_nonneg (hδ i) (hδ _))).mpr hm
      nlinarith only [hsq,sq_nonneg (δ i-δ (nearestLabel L Y i)),sq_nonneg (δ (nearestLabel L X i))]
  have hSX := finite_fiber_sum_le (nearestLabel L X) (fun i ↦ (δ i)^2) 125
    (fun _ ↦ sq_nonneg _) (nearestLabel_fiber_card L X hX)
  have hSY := finite_fiber_sum_le (nearestLabel L Y) (fun i ↦ (δ i)^2) 125
    (fun _ ↦ sq_nonneg _) (nearestLabel_fiber_card L Y hY)
  calc
    _ ≤ ∑ i, (2*(δ i)^2+2*(δ (nearestLabel L X i))^2+2*(δ (nearestLabel L Y i))^2) :=
      Finset.sum_le_sum (fun i _ ↦ hpoint i)
    _ = 2*(∑ i, (δ i)^2)+2*(∑ i, (δ (nearestLabel L X i))^2)+2*(∑ i, (δ (nearestLabel L Y i))^2) := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ 502*∑ i, (δ i)^2 := by norm_num at hSX hSY; linarith only [hSX,hSY]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_InjectiveNear
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma exists_injective_near {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MetricSpace E] [PerfectSpace E] (X : ι→E) {ε : ℝ} (hε : 0<ε) :
    ∃ Y : ι→E, Function.Injective Y ∧ ∀ i, dist (Y i) (X i)<ε := by
  classical
  have aux (I : Finset ι) : ∃ Y : ι→E, Set.InjOn Y I ∧ ∀ i∈I, dist (Y i) (X i)<ε := by
    induction I using Finset.induction_on with
    | empty => exact ⟨X,by simp [Set.InjOn],by simp⟩
    | @insert a I ha ih =>
      obtain ⟨Y,hinj,hclose⟩ := ih
      have hd := dense_univ.sdiff_finset (I.image Y)
      obtain ⟨y,hy,hball⟩ := hd.exists_mem_open Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
      refine ⟨Function.update Y a y,?_,?_⟩
      · intro i hi j hj he
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst i
          rcases Finset.mem_insert.mp hj with hj | hj
          · exact hj.symm
          · have hja : j≠a := fun h ↦ ha (h ▸ hj)
            rw [Function.update_self,Function.update_of_ne hja] at he
            exact (hy.2 (by rw [he]; exact Finset.mem_image.mpr ⟨j,hj,rfl⟩)).elim
        · rcases Finset.mem_insert.mp hj with hj | hj
          · subst j
            have hia : i≠a := fun h ↦ ha (h ▸ hi)
            rw [Function.update_self,Function.update_of_ne hia] at he
            exact (hy.2 (Finset.mem_image.mpr ⟨i,hi,he⟩)).elim
          · have hia : i≠a := fun h ↦ ha (h ▸ hi)
            have hja : j≠a := fun h ↦ ha (h ▸ hj)
            rw [Function.update_of_ne hia,Function.update_of_ne hja] at he
            exact hinj hi hj he
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa using hball
        · rw [Function.update_of_ne (show i≠a from fun h ↦ ha (h ▸ hi))]
          exact hclose i hi
  obtain ⟨Y,hi,hc⟩ := aux Finset.univ
  exact ⟨Y,fun i j h ↦ hi (Finset.mem_univ _) (Finset.mem_univ _) h,fun i ↦ hc i (Finset.mem_univ _)⟩

lemma dense_injective_configurations {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MetricSpace E] [PerfectSpace E] : Dense {X : ι→E | Function.Injective X} := by
  apply Metric.dense_iff.mpr
  intro X ε hε
  obtain ⟨Y,hY,hclose⟩ := exists_injective_near X hε
  refine ⟨Y,?_,hY⟩
  exact (dist_pi_lt_iff hε).mpr hclose

lemma torus_nontrivial (L : Length) : Nontrivial (Torus L) := by
  let hc : Nontrivial (AddCircle L.val) := by
    refine ⟨⟨((L.val/2:ℝ):AddCircle L.val),0,?_⟩⟩
    intro he
    have hh := AddCircle.norm_half_period_eq L.val
    rw [he,norm_zero,abs_of_pos L.property] at hh
    linarith only [L.property,hh]
  let := hc
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

attribute [local irreducible] torusDistance nearestParticleDistance

lemma nearestDifference_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (L : Length) : Continuous (fun p : (ι→Torus L)×(ι→Torus L) ↦
      ∑ i, (nearestParticleDistance L p.2 i-nearestParticleDistance L p.1 i)^2) := by
  apply continuous_finsetSum
  intro i _
  exact (((nearestParticleDistance_continuous L i).comp continuous_snd).sub
    ((nearestParticleDistance_continuous L i).comp continuous_fst)).pow 2

lemma torusMotion_continuous {ι : Type*} [Fintype ι] (L : Length) :
    Continuous (fun p : (ι→Torus L)×(ι→Torus L) ↦ 502*∑ i, torusDistance L (p.1 i) (p.2 i)^2) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply Continuous.pow
  exact (torusDistance_continuous_pair L).comp
    (f := fun p : (ι→Torus L)×(ι→Torus L) ↦ (p.1 i,p.2 i))
    (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd))

theorem nearestParticleDistance_sum_sq_all {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (L : Length) (X Y : ι→Torus L) :
    (∑ i, (nearestParticleDistance L Y i-nearestParticleDistance L X i)^2)≤
      502*∑ i, torusDistance L (X i) (Y i)^2 := by
  let := torus_nontrivial L
  let S : Set (ι→Torus L) := {X | Function.Injective X}
  have hd : Dense (S×ˢS) := dense_injective_configurations.prod dense_injective_configurations
  have hc : IsClosed {p : (ι→Torus L)×(ι→Torus L) |
      (∑ i, (nearestParticleDistance L p.2 i-nearestParticleDistance L p.1 i)^2)≤
        502*∑ i, torusDistance L (p.1 i) (p.2 i)^2} :=
    isClosed_le (nearestDifference_continuous L) (torusMotion_continuous L)
  exact closure_minimal (fun p hp ↦ nearestParticleDistance_sum_sq L p.1 p.2 hp.1 hp.2) hc (hd (X,Y))

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

lemma closeRamp_nonneg (t : ℝ) : 0 ≤ closeRamp t := le_max_left _ _
lemma closeRamp_le_one (t : ℝ) : closeRamp t≤1 := max_le zero_le_one (min_le_left _ _)
lemma closeRamp_one {t : ℝ} (ht : 1≤t) : closeRamp t=1 := by simp [closeRamp,min_eq_left ht]
lemma closeRamp_zero {t : ℝ} (ht : t≤0) : closeRamp t=0 := by
  exact max_eq_left ((min_le_right 1 t).trans ht)

lemma closeRamp_sub_le (x y : ℝ) : |closeRamp x-closeRamp y|≤|x-y| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using closeRamp_lipschitz.dist_le_mul x y

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma localCloseRoot_sq (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) :
    localCloseRoot L s v X^2=localCloseSmoothCount L s v X :=
  EuclideanSpace.real_norm_sq_eq _

lemma closeAmplitude_nonneg (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) (i : ι) :
    0 ≤ closeAmplitude L s v X i := mul_nonneg (closeRamp_nonneg _) (closeRamp_nonneg _)
lemma closeAmplitude_le_one (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) (i : ι) :
    closeAmplitude L s v X i≤1 :=
  (mul_le_of_le_one_left (closeRamp_nonneg _) (closeRamp_le_one _)).trans
    (closeRamp_le_one _)

lemma closeAmplitude_one (L : Length) {s : ℝ} (hs : 0 < s) (v : Torus L) (X : ι→Torus L) (i : ι)
    (hv : torusDistance L (X i) v≤5) (hc : nearestParticleDistance L X i ≤ s) :
    closeAmplitude L s v X i=1 := by
  unfold closeAmplitude
  have hd : nearestParticleDistance L X i/s≤1 := (div_le_one hs).mpr hc
  rw [closeRamp_one (by linarith only [hv]),closeRamp_one (by linarith only [hd]),mul_one]

lemma closeAmplitude_zero_of_far (L : Length) (s : ℝ) (v : Torus L) (X : ι→Torus L) (i : ι)
    (hv : 6≤torusDistance L (X i) v) : closeAmplitude L s v X i=0 := by
  unfold closeAmplitude
  rw [closeRamp_zero (by linarith only [hv]),zero_mul]

lemma closeAmplitude_zero_of_isolated (L : Length) {s : ℝ} (hs : 0 < s) (v : Torus L) (X : ι→Torus L) (i : ι)
    (hc : 2*s≤nearestParticleDistance L X i) : closeAmplitude L s v X i=0 := by
  unfold closeAmplitude
  have hd : 2≤nearestParticleDistance L X i/s := (le_div_iff₀ hs).mpr hc
  rw [closeRamp_zero (t := 2-nearestParticleDistance L X i/s) (by linarith only [hd]),mul_zero]

lemma torusDistance_sub_le (L : Length) (x y v : Torus L) :
    |torusDistance L x v-torusDistance L y v|≤torusDistance L x y := by
  simpa only [euclideanTorusPoint_dist] using abs_dist_sub_le
    (euclideanTorusPoint L x) (euclideanTorusPoint L y) (euclideanTorusPoint L v)

lemma unit_product_sub_le {a b c d : ℝ} (ha : 0≤a) (_hb : 0≤b) (_hc : 0 ≤ c) (hd : 0≤d)
    (hA : a≤1) (_hB : b≤1) (_hC : c≤1) (hD : d≤1) :
    |a*b-c*d|≤|a-c|+|b-d| := by
  calc
    _ = |a*(b-d)+(a-c)*d| := by congr 1; ring
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ = a*|b-d|+|a-c| *d := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hd]
    _ ≤ 1*|b-d|+|a-c| *1 := add_le_add
      (mul_le_mul_of_nonneg_right hA (abs_nonneg _)) (mul_le_mul_of_nonneg_left hD (abs_nonneg _))
    _ = _ := by ring

lemma closeAmplitude_sub_le (L : Length) {s : ℝ} (hs : 0 < s) (v : Torus L) (X Y : ι→Torus L) (i : ι) :
    |closeAmplitude L s v Y i-closeAmplitude L s v X i|≤
      torusDistance L (X i) (Y i)+|nearestParticleDistance L Y i-nearestParticleDistance L X i|/s := by
  unfold closeAmplitude
  apply (unit_product_sub_le (closeRamp_nonneg _) (closeRamp_nonneg _) (closeRamp_nonneg _) (closeRamp_nonneg _)
    (closeRamp_le_one _) (closeRamp_le_one _) (closeRamp_le_one _) (closeRamp_le_one _)).trans
  apply add_le_add
  · apply (closeRamp_sub_le _ _).trans
    have he : (6-torusDistance L (Y i) v)-(6-torusDistance L (X i) v)=
        torusDistance L (X i) v-torusDistance L (Y i) v := by ring
    rw [he]
    exact torusDistance_sub_le L (X i) (Y i) v
  · apply (closeRamp_sub_le _ _).trans_eq
    rw [show (2-nearestParticleDistance L Y i/s)-(2-nearestParticleDistance L X i/s)=
      -(nearestParticleDistance L Y i-nearestParticleDistance L X i)/s by ring,
      abs_div,abs_neg,abs_of_pos hs]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SqTwiceSqAbs
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma sq_le_twice_sq_of_abs_le {a b c : ℝ} (h : |a|≤b+c) : a^2≤2*b^2+2*c^2 := by
  have hn : 0≤b+c := (abs_nonneg a).trans h
  have hh := (sq_le_sq₀ (abs_nonneg a) hn).mpr h
  rw [sq_abs] at hh
  nlinarith only [hh,sq_nonneg (b-c)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma closeAmplitude_sum_sq (L : Length) {s : ℝ} (hs : 0 < s) (v : Torus L) (X Y : ι→Torus L) :
    (∑ i, (closeAmplitude L s v Y i-closeAmplitude L s v X i)^2)≤
      (2+1004/s^2)*∑ i, torusDistance L (X i) (Y i)^2 := by
  have hp (i : ι) := sq_le_twice_sq_of_abs_le (closeAmplitude_sub_le L hs v X Y i)
  simp only [div_pow,sq_abs] at hp
  have hn := nearestParticleDistance_sum_sq_all L X Y
  calc
    _ ≤ ∑ i, (2*torusDistance L (X i) (Y i)^2+
        2*((nearestParticleDistance L Y i-nearestParticleDistance L X i)^2/s^2)) :=
      Finset.sum_le_sum (fun i _ ↦ hp i)
    _ = 2*(∑ i, torusDistance L (X i) (Y i)^2)+
        (2/s^2)*∑ i, (nearestParticleDistance L Y i-nearestParticleDistance L X i)^2 := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum,mul_div_assoc,div_mul_eq_mul_div]
    _ ≤ 2*(∑ i, torusDistance L (X i) (Y i)^2)+
        (2/s^2)*(502*∑ i, torusDistance L (X i) (Y i)^2) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hn (by positivity)) _
    _ = _ := by ring

lemma localCloseRoot_difference_sq (L : Length) {s : ℝ} (hs : 0 < s) (v : Torus L) (X Y : ι→Torus L) :
    (localCloseRoot L s v Y-localCloseRoot L s v X)^2≤
      (2+1004/s^2)*∑ i, torusDistance L (X i) (Y i)^2 := by
  let a : EuclideanSpace ℝ ι := WithLp.toLp 2 (closeAmplitude L s v Y)
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (closeAmplitude L s v X)
  have h := abs_norm_sub_norm_le a b
  have hh := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg (a-b))).mpr h
  rw [sq_abs,EuclideanSpace.real_norm_sq_eq] at hh
  exact hh.trans (closeAmplitude_sum_sq L hs v X Y)

theorem localCloseRoot_difference (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : s≤1)
    (v : Torus L) (X Y : ι→Torus L) :
    |localCloseRoot L s v Y-localCloseRoot L s v X|≤
      (32/s)*Real.sqrt (∑ i, torusDistance L (X i) (Y i)^2) := by
  have hsum : 0≤∑ i, torusDistance L (X i) (Y i)^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hsq := localCloseRoot_difference_sq L hs v X Y
  have hs2 : s^2≤1 := by nlinarith only [hs1,hs]
  have hC : 2+1004/s^2≤(32/s)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
    field_simp
    nlinarith only [hs2]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt hsum]
  exact hsq.trans (mul_le_mul_of_nonneg_right hC hsum)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

lemma euclideanProject_surjective {ι : Type*} (L : Length) : Function.Surjective (euclideanProject (ι:=ι) L) := by
  intro X
  refine ⟨WithLp.toLp 2 (fun p ↦ (AddCircle.equivIco L.val 0 (X p.1 p.2)).val),?_⟩
  ext i q
  exact AddCircle.coe_equivIco

lemma euclideanProject_total_sq {ι : Type*} [Fintype ι] (L : Length) (x y : EuclideanConfiguration ι) :
    (∑ i, torusDistance L (euclideanProject L x i) (euclideanProject L y i)^2)≤dist x y^2 := by
  have ht (i : ι) : torusDistance L (euclideanProject L x i) (euclideanProject L y i)^2=
      ∑ q : Fin 3, dist ((x (i,q):ℝ):AddCircle L.val) ((y (i,q):ℝ):AddCircle L.val)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  simp_rw [ht]
  rw [dist_eq_norm,EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro q _
  have hn : dist ((x (i,q):ℝ):AddCircle L.val) ((y (i,q):ℝ):AddCircle L.val)≤|x (i,q)-y (i,q)| := by
    rw [dist_eq_norm,←AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have hh := (sq_le_sq₀ dist_nonneg (abs_nonneg _)).mpr hn
  simpa only [sq_abs,PiLp.sub_apply] using hh

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

theorem localCloseRoot_euclidean_lipschitz (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : s≤1) (v : Torus L) :
    LipschitzWith ⟨32/s,by positivity⟩
      (fun x : EuclideanConfiguration ι ↦ localCloseRoot L s v (euclideanProject L x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,abs_sub_comm]
  apply (localCloseRoot_difference L hs hs1 v (euclideanProject L x) (euclideanProject L y)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Real.sqrt_le_sqrt (euclideanProject_total_sq L x y)).trans_eq (Real.sqrt_sq dist_nonneg)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalCloseLabels
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

variable {n : ℕ} [Nontrivial (Fin n)]

lemma localCloseSmoothCount_covers (L : Length) {s : ℝ} (hs : 0 < s) (v : Torus L) (X : Configuration n L) :
    ((localCloseLabels L s v X).card:ℝ)≤localCloseSmoothCount L s v X := by
  classical
  calc
    _ = ∑ _i∈localCloseLabels L s v X, (1:ℝ) := by simp
    _ = ∑ i∈localCloseLabels L s v X, closeAmplitude L s v X i^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      rw [closeAmplitude_one L hs v X i hh.1 hh.2]
      norm_num
    _ ≤ ∑ i, closeAmplitude L s v X i^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)

lemma closeAmplitude_ne_zero_imp (L : Length) {s : ℝ} (hs : 0 < s) (v : Torus L) (X : Configuration n L) (i : Fin n)
    (h : closeAmplitude L s v X i≠0) :
    torusDistance L (X i) v<6 ∧ nearestParticleDistance L X i<2*s :=
  ⟨lt_of_not_ge (fun he ↦ h (closeAmplitude_zero_of_far L s v X i he)),
    lt_of_not_ge (fun he ↦ h (closeAmplitude_zero_of_isolated L hs v X i he))⟩

lemma closeAmplitude_mem_localized (L : Length) {s : ℝ} (hs : 0 < s) (A : Finset (Torus L))
    (v : Torus L) (hv : v∈A) (X : Configuration n L) (i : Fin n) (hi : closeAmplitude L s v X i≠0) :
    i∈localizedNearLabels L A s X := by
  classical
  have hh := closeAmplitude_ne_zero_imp L hs v X i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,⟨⟨v,hv⟩,
    (spatialSiteDistance_le L A (X i) v hv).trans hh.1.le,nearestLabel L X i,nearestLabel_ne L X i,?_⟩⟩
  have hs' : torusDistance L (X (nearestLabel L X i)) (X i)=nearestParticleDistance L X i := by
    simp only [nearestParticleDistance,torusDistance,dist_comm]
  rw [hs']
  exact hh.2.le

lemma closeAmplitude_unique_site (L : Length) (s : ℝ) (A : Finset (Torus L))
    (hA : ∀ v∈A, ∀ w∈A, v≠w → 12<torusDistance L v w)
    (X : Configuration n L) (i : Fin n) {v w : Torus L} (hv : v∈A) (hw : w∈A)
    (hvi : closeAmplitude L s v X i≠0) (hwi : closeAmplitude L s w X i≠0) : v=w := by
  by_contra he
  have hdv : torusDistance L (X i) v<6 := lt_of_not_ge (fun h ↦ hvi (closeAmplitude_zero_of_far L s v X i h))
  have hdw : torusDistance L (X i) w<6 := lt_of_not_ge (fun h ↦ hwi (closeAmplitude_zero_of_far L s w X i h))
  have ht := torusDistance_triangle' L v (X i) w
  have hs' : torusDistance L v (X i)=torusDistance L (X i) v := by simp only [torusDistance,dist_comm]
  rw [hs'] at ht
  linarith only [hdv,hdw,ht,hA v hv w hw he]

theorem localCloseSmoothCount_sum_le (L : Length) {s : ℝ} (hs : 0 < s) (A : Finset (Torus L))
    (hA : ∀ v∈A, ∀ w∈A, v≠w → 12<torusDistance L v w) (X : Configuration n L) :
    (∑ v∈A, localCloseSmoothCount L s v X)≤((localizedNearLabels L A s X).card:ℝ) := by
  classical
  simp only [localCloseSmoothCount]
  rw [Finset.sum_comm]
  have hp (i : Fin n) : (∑ v∈A, closeAmplitude L s v X i^2)≤
      if i∈localizedNearLabels L A s X then (1:ℝ) else 0 := by
    by_cases he : ∃ v∈A, closeAmplitude L s v X i≠0
    · obtain ⟨v,hv,hvi⟩ := he
      rw [ite_eq_left (closeAmplitude_mem_localized L hs A v hv X i hvi)]
      rw [Finset.sum_eq_single v]
      · exact (pow_le_pow_left₀ (closeAmplitude_nonneg L s v X i) (closeAmplitude_le_one L s v X i) 2).trans_eq (by norm_num)
      · intro w hw hwv
        have hz : closeAmplitude L s w X i=0 := by
          by_contra hwi
          exact hwv (closeAmplitude_unique_site L s A hA X i hw hv hwi hvi)
        rw [hz]; norm_num
      · exact fun hn ↦ (hn hv).elim
    · rw [Finset.sum_eq_zero (fun v hv ↦ ?_)]
      · split_ifs <;> norm_num
      · have hz : closeAmplitude L s v X i=0 := not_ne_iff.mp (fun h ↦ he ⟨v,hv,h⟩)
        rw [hz]; norm_num
  calc
    _ ≤ ∑ i, if i∈localizedNearLabels L A s X then (1:ℝ) else 0 := Finset.sum_le_sum (fun i _ ↦ hp i)
    _ = _ := by simp

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

variable {ι : Type*} [Fintype ι]

lemma configurationMollify_integrable (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) (hf : Continuous f) (X : ι→Torus L) :
    Integrable (fun y : EuclideanConfiguration ι ↦ φ.normed volume y*f (X-euclideanProject L y)) volume :=
  (φ.continuous_normed.mul (hf.comp (continuous_const.sub (euclideanProject_continuous L)))).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.mul_right)

lemma configurationMollify_nonneg (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    (f : (ι→Torus L)→ℝ) (hf : ∀ X, 0≤f X) (X : ι→Torus L) :
    0 ≤ configurationMollify L φ f X :=
  integral_nonneg (fun y ↦ mul_nonneg (φ.nonneg_normed y) (hf _))

lemma configurationMollify_lipschitz (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    {f : (ι→Torus L)→ℝ} (hf : Continuous f) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x : EuclideanConfiguration ι ↦ f (euclideanProject L x))) :
    LipschitzWith C (fun x : EuclideanConfiguration ι ↦ configurationMollify L φ f (euclideanProject L x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,configurationMollify,configurationMollify,←integral_sub
    (configurationMollify_integrable L φ f hf _) (configurationMollify_integrable L φ f hf _)]
  calc
    _ ≤ ∫ z : EuclideanConfiguration ι, φ.normed volume z*((C:ℝ)*dist x y) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) (Eventually.of_forall ?_)
      intro z
      rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      have h := hLip.dist_le_mul (x-z) (y-z)
      simpa only [euclideanProject_sub,dist_sub_right,Real.dist_eq,Real.norm_eq_abs] using h
    _ = (C:ℝ)*dist x y := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma configurationMollify_approximation (L : Length) (φ : ContDiffBump (0 : EuclideanConfiguration ι))
    {f : (ι→Torus L)→ℝ} (hf : Continuous f) {C : ℝ≥0}
    (hLip : LipschitzWith C (fun x : EuclideanConfiguration ι ↦ f (euclideanProject L x))) (X : ι→Torus L) :
    dist (configurationMollify L φ f X) (f X)≤(C:ℝ)*φ.rOut := by
  obtain ⟨x,rfl⟩ := euclideanProject_surjective L X
  rw [show configurationMollify L φ f (euclideanProject L x)=
    (φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun y ↦ f (euclideanProject L y))) x from
    congrFun (configurationMollify_lift L φ f) x]
  apply φ.dist_normed_convolution_le (hf.comp (euclideanProject_continuous L)).aestronglyMeasurable
  intro y hy
  exact (hLip.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le C.coe_nonneg)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FlattenLinear
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

lemma euclideanFlatten_apply (n : ℕ) (X : LiftedConfiguration n) (p : Direction n) :
    euclideanFlatten n X p=X p.1 p.2 := rfl

lemma euclideanFlatten_project (n : ℕ) (L : Length) (X : LiftedConfiguration n) :
    euclideanProject L (euclideanFlatten n X)=project n L X := rfl

lemma euclideanFlatten_single (n : ℕ) (p : Direction n) :
    euclideanFlatten n (Pi.single p.1 (Pi.single p.2 1))=EuclideanSpace.basisFun (Direction n) ℝ p := by
  ext q
  by_cases h1 : q.1=p.1 <;> by_cases h2 : q.2=p.2 <;>
    simp [euclideanFlatten_apply,EuclideanSpace.basisFun_apply,Prod.ext_iff,h1,h2]

lemma coordDerivative_real_euclidean {n : ℕ} (L : Length) (f : Configuration n L→ℝ)
    (hf : Differentiable ℝ (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x)))
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (fun Y ↦ (f Y:ℂ)) p X=
      ((fderiv ℝ (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x))
        (euclideanFlatten n (representative n L X)) (EuclideanSpace.basisFun (Direction n) ℝ p)):ℂ) := by
  have hh := (Complex.ofRealCLM.hasFDerivAt.comp _ (hf _).hasFDerivAt).comp
    (representative n L X) (euclideanFlatten n).hasFDerivAt
  have he : ((Complex.ofRealCLM ∘ (fun x : EuclideanConfiguration (Fin n) ↦ f (euclideanProject L x))) ∘ euclideanFlatten n)=
      (fun x : LiftedConfiguration n ↦ (f (project n L x):ℂ)) := by
    funext x
    rfl
  rw [he] at hh
  unfold coordDerivative
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply,euclideanFlatten_single,Complex.ofRealCLM_apply]

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma clippedNearest_le (L : Length) (X Y : ι→Torus L) (i k : ι) (t : ℝ)
    (hi : X i=Y i) (hrest : ∀ j, j≠k → X j=Y j)
    (hfar : t≤torusDistance L (Y i) (Y k)) :
    min (nearestParticleDistance L X i) t≤nearestParticleDistance L Y i := by
  by_cases he : nearestLabel L Y i=k
  · simpa only [nearestParticleDistance,he] using (min_le_right (nearestParticleDistance L X i) t).trans hfar
  · have hn := nearestParticleDistance_le L X i (nearestLabel L Y i) (nearestLabel_ne L Y i)
    rw [hi,hrest _ he] at hn
    exact (min_le_left _ _).trans hn

lemma clippedNearest_eq (L : Length) (X Y : ι→Torus L) (i k : ι) (t : ℝ)
    (hi : X i=Y i) (hrest : ∀ j, j≠k → X j=Y j)
    (hXfar : t≤torusDistance L (X i) (X k)) (hYfar : t≤torusDistance L (Y i) (Y k)) :
    min (nearestParticleDistance L X i) t=min (nearestParticleDistance L Y i) t :=
  le_antisymm (le_min (clippedNearest_le L X Y i k t hi hrest hYfar) (min_le_right _ _))
    (le_min (clippedNearest_le L Y X i k t hi.symm (fun j h ↦ (hrest j h).symm) hXfar) (min_le_right _ _))

lemma closeRamp_clipped {s d : ℝ} (hs : 0 < s) :
    closeRamp (2-d/s)=closeRamp (2-min d (2*s)/s) := by
  by_cases h : d≤2*s
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
    have hd : 2≤d/s := (le_div_iff₀ hs).mpr (le_of_not_ge h)
    rw [closeRamp_zero (t:=2-d/s) (by linarith only [hd])]
    have he : 2-2*s/s=0 := by field_simp; ring
    rw [he,closeRamp_zero le_rfl]

lemma far_from_near_separated (L : Length) (a b v : Torus L) (hnear : torusDistance L a v<6)
    (hfar : 7≤torusDistance L b v) : 1≤torusDistance L a b := by
  have ht := torusDistance_triangle' L b a v
  have he : torusDistance L b a=torusDistance L a b := by simp only [torusDistance,dist_comm]
  rw [he] at ht
  linarith only [hnear,hfar,ht]

theorem closeAmplitude_away_eq (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (v : Torus L) (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 7≤torusDistance L (X k) v) (hYfar : 7≤torusDistance L (Y k) v) (i : ι) :
    closeAmplitude L s v X i=closeAmplitude L s v Y i := by
  by_cases hik : i=k
  · subst i
    rw [closeAmplitude_zero_of_far L s v X k (by linarith only [hXfar]),
      closeAmplitude_zero_of_far L s v Y k (by linarith only [hYfar])]
  · have hi := hrest i hik
    by_cases hv : torusDistance L (X i) v<6
    · have hxf := hs1.trans (far_from_near_separated L (X i) (X k) v hv hXfar)
      have hyv : torusDistance L (Y i) v<6 := hi ▸ hv
      have hyf := hs1.trans (far_from_near_separated L (Y i) (Y k) v hyv hYfar)
      have he := clippedNearest_eq L X Y i k (2*s) hi hrest hxf hyf
      unfold closeAmplitude
      rw [hi,closeRamp_clipped (d:=nearestParticleDistance L X i) hs,
        closeRamp_clipped (d:=nearestParticleDistance L Y i) hs,he]
    · have hxv : 6≤torusDistance L (X i) v := le_of_not_gt hv
      have hyv : 6≤torusDistance L (Y i) v := hi ▸ hxv
      rw [closeAmplitude_zero_of_far L s v X i hxv,closeAmplitude_zero_of_far L s v Y i hyv]

lemma localCloseSmoothCount_away_eq (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (v : Torus L) (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 7≤torusDistance L (X k) v) (hYfar : 7≤torusDistance L (Y k) v) :
    localCloseSmoothCount L s v X=localCloseSmoothCount L s v Y := by
  apply Finset.sum_congr rfl
  intro i _
  rw [closeAmplitude_away_eq L hs hs1 v X Y k hrest hXfar hYfar i]

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped Convolution NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma mollifiedCloseRoot_nonneg (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (X : ι→Torus L) :
    0 ≤ mollifiedCloseRoot L s v φ X :=
  configurationMollify_nonneg L φ _ (fun _ ↦ norm_nonneg _) X

lemma mollifiedCloseRoot_lipschitz (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : s≤1) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) :
    LipschitzWith ⟨32/s,by positivity⟩ (fun x : EuclideanConfiguration ι ↦ mollifiedCloseRoot L s v φ (euclideanProject L x)) :=
  configurationMollify_lipschitz L φ (localCloseRoot_continuous L s v)
    (localCloseRoot_euclidean_lipschitz L hs hs1 v)

lemma mollifiedCloseRoot_approximation (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : s≤1) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (X : ι→Torus L) :
    |mollifiedCloseRoot L s v φ X-localCloseRoot L s v X|≤(32/s)*φ.rOut := by
  exact configurationMollify_approximation L φ (localCloseRoot_continuous L s v)
    (localCloseRoot_euclidean_lipschitz L hs hs1 v) X

lemma self_gradient_square_of_lipschitz {κ : Type*} [Fintype κ] {C : ℝ≥0}
    {f : EuclideanSpace ℝ κ→ℝ} (hf : LipschitzWith C f) {x : EuclideanSpace ℝ κ}
    (hx : DifferentiableAt ℝ f x) :
      (∑ p, (fderiv ℝ (fun y ↦ f y^2) x (EuclideanSpace.basisFun κ ℝ p))^2)≤
        (4*(C:ℝ)^2)*f x^2 := by
  rw [←(EuclideanSpace.basisFun κ ℝ).norm_dual,fderiv_fun_pow 2 hx]
  simp only [Nat.reduceSub,pow_one,nsmul_eq_mul,Nat.cast_ofNat,norm_smul,Real.norm_eq_abs]
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀:=x) hf
  have hsq := (sq_le_sq₀ (norm_nonneg _) C.coe_nonneg).mpr hb
  calc
    _ = (4*f x^2)*‖fderiv ℝ f x‖^2 := by rw [mul_pow,sq_abs]; ring
    _ ≤ (4*f x^2)*(C:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

lemma mollifiedCloseCount_gradient (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : s≤1) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (x : EuclideanConfiguration ι) :
      (∑ p, (fderiv ℝ (fun y ↦ mollifiedCloseCount L s v φ (euclideanProject L y)) x
        (EuclideanSpace.basisFun (ι×Fin 3) ℝ p))^2)≤
          (4096/s^2)*mollifiedCloseCount L s v φ (euclideanProject L x) := by
  have h := self_gradient_square_of_lipschitz (mollifiedCloseRoot_lipschitz L hs hs1 v φ)
    ((mollifiedCloseRoot_smooth L s v φ).differentiable (by simp) x)
  have hc : (4:ℝ)*(32/s)^2=4096/s^2 := by ring
  rw [←hc]
  exact h

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_MollifiedCloseCountMultiplier
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
variable {n : ℕ} [Nontrivial (Fin n)]

lemma mollifiedCloseCountMultiplier_apply (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    (mollifiedCloseCountMultiplier L s v φ).toFun X=(mollifiedCloseCount L s v φ X:ℂ) := rfl

lemma mollifiedCloseCountMultiplier_real (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    conj ((mollifiedCloseCountMultiplier L s v φ).toFun X)=(mollifiedCloseCountMultiplier L s v φ).toFun X :=
  Complex.conj_ofReal _

lemma mollifiedCloseCountMultiplier_gradient (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : s≤1) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (mollifiedCloseCountMultiplier L s v φ).toFun p X‖^2)≤
      (4096/s^2)*mollifiedCloseCount L s v φ X := by
  change (∑ p : Direction n, ‖coordDerivative n L (fun Y ↦ (mollifiedCloseCount L s v φ Y:ℂ)) p X‖^2)≤_
  simp_rw [coordDerivative_real_euclidean L _
    ((mollifiedCloseCount_smooth L s v φ).differentiable (by simp)),
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have h := mollifiedCloseCount_gradient L hs hs1 v φ (euclideanFlatten n (representative n L X))
  simpa only [euclideanFlatten_project,project_representative] using h

lemma closeHighProfile_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t≤h) : closeHighProfile h t=0 := by
  rw [closeHighProfile,CellOrbital.profile_one hh ht,sub_self]
lemma closeHighProfile_one {h : ℝ} (hh : 0<h) {t : ℝ} (ht : 2*h≤t) : closeHighProfile h t=1 := by
  rw [closeHighProfile,CellOrbital.profile_zero hh ht,sub_zero]

lemma closeHighProfile_deriv (h t : ℝ) : deriv (closeHighProfile h) t= -deriv (CellOrbital.profile h) t := by
  exact ((CellOrbital.profile_smooth h).differentiable (by simp) t).hasDerivAt.const_sub 1 |>.deriv

lemma closeHighProfile_deriv_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t∉Icc h (2*h)) :
    deriv (closeHighProfile h) t=0 := by
  rw [closeHighProfile_deriv,CellOrbital.profile_deriv_zero hh ht,neg_zero]

lemma closeHighProfile_deriv_bound {h M : ℝ} (hh : 0<h) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (t : ℝ) :
    |deriv (closeHighProfile h) t|≤M/h := by
  rw [closeHighProfile_deriv,abs_neg]
  exact CellOrbital.profile_deriv_bound hh hM hb t

lemma mollifiedCloseCutoff_apply (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (X : Configuration n L) :
    (mollifiedCloseCutoff L s v φ h).toFun X=(closeHighProfile h (mollifiedCloseCount L s v φ X):ℂ) := by
  change (closeHighProfile h ((mollifiedCloseCountMultiplier L s v φ).toFun X).re:ℂ)=_
  rw [mollifiedCloseCountMultiplier_apply,Complex.ofReal_re]

lemma mollifiedCloseCutoff_partial (L : Length) (s : ℝ) (v : Torus L)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X=
      ((deriv (closeHighProfile h) (mollifiedCloseCount L s v φ X):ℝ):ℂ)*
        coordDerivative n L (mollifiedCloseCountMultiplier L s v φ).toFun p X := by
  rw [mollifiedCloseCutoff,SmoothMultiplier.partial_realComp _ _ _ (mollifiedCloseCountMultiplier_real L s v φ),
    mollifiedCloseCountMultiplier_apply,Complex.ofReal_re]

theorem mollifiedCloseCutoff_gradient (L : Length) {s h M : ℝ} (hs : 0 < s) (hs1 : s≤1)
    (hh : 0<h) (hM : 0≤M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X‖^2)≤
      8192*M^2/(h*s^2) := by
  by_cases ht : mollifiedCloseCount L s v φ X∈Icc h (2*h)
  · simp_rw [mollifiedCloseCutoff_partial,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [←Finset.mul_sum]
    have hb2 : (deriv (closeHighProfile h) (mollifiedCloseCount L s v φ X))^2≤(M/h)^2 := by
      rw [←sq_abs (deriv _ _)]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (closeHighProfile_deriv_bound hh hM hb _)
    calc
      _ ≤ (M/h)^2*((4096/s^2)*mollifiedCloseCount L s v φ X) :=
        mul_le_mul hb2 (mollifiedCloseCountMultiplier_gradient L hs hs1 v φ X)
          (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
      _ ≤ (M/h)^2*((4096/s^2)*(2*h)) := by
        gcongr
        exact ht.2
      _ = _ := by field_simp; ring
  · simp_rw [mollifiedCloseCutoff_partial,closeHighProfile_deriv_zero hh ht,Complex.ofReal_zero,zero_mul,
      norm_zero,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero]
    positivity

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma euclideanProject_move_one_le (L : Length) (X : ι→Torus L)
    (y : EuclideanConfiguration ι) (k : ι) :
    torusDistance L (X k) ((X-euclideanProject L y) k)≤‖y‖ := by
  obtain ⟨x,rfl⟩ := euclideanProject_surjective L X
  have hsingle := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun i ↦ torusDistance L (euclideanProject L x i) (euclideanProject L (x-y) i)^2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ k)
  have h := hsingle.trans (euclideanProject_total_sq L x (x-y))
  simp only [euclideanProject_sub,dist_eq_norm,sub_sub_cancel] at h
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg y)).mp h

variable [Nontrivial ι]

lemma localCloseRoot_away_eq (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (v : Torus L) (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 7≤torusDistance L (X k) v) (hYfar : 7≤torusDistance L (Y k) v) :
    localCloseRoot L s v X=localCloseRoot L s v Y := by
  apply (sq_eq_sq₀ (show 0≤localCloseRoot L s v X from norm_nonneg _)
    (show 0≤localCloseRoot L s v Y from norm_nonneg _)).mp
  rw [localCloseRoot_sq,localCloseRoot_sq,localCloseSmoothCount_away_eq L hs hs1 v X Y k hrest hXfar hYfar]

lemma mollifiedCloseRoot_away_eq (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (hφ : φ.rOut≤1)
    (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 8≤torusDistance L (X k) v) (hYfar : 8≤torusDistance L (Y k) v) :
    mollifiedCloseRoot L s v φ X=mollifiedCloseRoot L s v φ Y := by
  unfold mollifiedCloseRoot configurationMollify
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  by_cases hy : φ.normed volume y=0
  · simp only [hy,zero_mul]
  · have hyball : y∈Metric.ball (0 : EuclideanConfiguration ι) φ.rOut := by
      rw [←φ.support_normed_eq (μ:=volume)]
      exact hy
    have hyn : ‖y‖≤1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hyball : ‖y‖<φ.rOut).le.trans hφ
    have hfar (Z : ι→Torus L) (hz : 8≤torusDistance L (Z k) v) :
        7≤torusDistance L ((Z-euclideanProject L y) k) v := by
      have ht := torusDistance_triangle' L (Z k) ((Z-euclideanProject L y) k) v
      have hm := (euclideanProject_move_one_le L Z y k).trans hyn
      linarith only [ht,hm,hz]
    rw [localCloseRoot_away_eq L hs hs1 v (X-euclideanProject L y) (Y-euclideanProject L y) k
      (fun i hi ↦ by simp only [Pi.sub_apply,hrest i hi]) (hfar X hXfar) (hfar Y hYfar)]

lemma mollifiedCloseCount_away_eq (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration ι)) (hφ : φ.rOut≤1)
    (X Y : ι→Torus L) (k : ι) (hrest : ∀ i, i≠k → X i=Y i)
    (hXfar : 8≤torusDistance L (X k) v) (hYfar : 8≤torusDistance L (Y k) v) :
    mollifiedCloseCount L s v φ X=mollifiedCloseCount L s v φ Y := by
  unfold mollifiedCloseCount
  rw [mollifiedCloseRoot_away_eq L hs hs1 v φ hφ X Y k hrest hXfar hYfar]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_CoordDerivativeParticleLocality
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
open scoped Topology

attribute [local irreducible] torusDistance

lemma coordDerivative_zero_of_particle_locality {n : ℕ} (L : Length) (f : Configuration n L→ℂ)
    (hf : Differentiable ℝ (fun x : LiftedConfiguration n ↦ f (project n L x)))
    (v : Torus L) (r : ℝ)
    (hloc : ∀ (X Y : Configuration n L) (k : Fin n), (∀ i, i≠k → X i=Y i) → r≤torusDistance L (X k) v →
      r≤torusDistance L (Y k) v → f X=f Y)
    (p : Direction n) (X : Configuration n L) (hfar : r<torusDistance L (X p.1) v) :
    coordDerivative n L f p X=0 := by
  let w : LiftedConfiguration n := Pi.single p.1 (Pi.single p.2 1)
  let Y : ℝ → Configuration n L := fun t ↦ project n L (representative n L X+t • w)
  have hY0 : Y 0=X := by simp only [Y,zero_smul,add_zero,project_representative]
  have hY : Continuous Y := by
    apply (continuous_project n L).comp
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hdcont : Continuous (fun t : ℝ ↦ torusDistance L (Y t p.1) v) :=
    (torusDistance_continuous_pair L).comp (((continuous_apply p.1).comp hY).prodMk continuous_const)
  have hevent : ∀ᶠ t in 𝓝 (0:ℝ), r<torusDistance L (Y t p.1) v :=
    hdcont.continuousAt.eventually_const_lt (by simpa only [hY0] using hfar)
  have hrest (t : ℝ) (i : Fin n) (hi : i≠p.1) : X i=Y t i := by
    have he : Y t i=project n L (representative n L X) i := by
      ext j
      simp only [Y,project,Pi.add_apply,Pi.smul_apply,w,Pi.single_eq_of_ne hi,Pi.zero_apply,
        smul_zero,add_zero]
    rw [he,project_representative]
  have heq : (fun t : ℝ ↦ f (Y t))=ᶠ[𝓝 (0:ℝ)] (fun _ ↦ f X) := by
    filter_upwards [hevent] with t ht
    exact (hloc X (Y t) p.1 (hrest t) hfar.le ht.le).symm
  have hz : HasDerivAt (fun t : ℝ ↦ f (Y t)) 0 0 :=
    (hasDerivAt_const 0 (f X)).congr_of_eventuallyEq heq
  have hline := (hasFDerivAt_const (𝕜:=ℝ) (representative n L X) (0:ℝ)).add
    ((hasFDerivAt_id (𝕜:=ℝ) (0:ℝ)).smul_const w)
  have hf0 : HasFDerivAt (fun x : LiftedConfiguration n ↦ f (project n L x))
      (fderiv ℝ (fun x : LiftedConfiguration n ↦ f (project n L x)) (representative n L X))
      (representative n L X+(0:ℝ) • w) := by
    simpa only [zero_smul,add_zero] using (hf (representative n L X)).hasFDerivAt
  have hd := (hf0.comp 0 hline).hasDerivAt
  have he := hd.unique hz
  simpa only [coordDerivative,w,ContinuousLinearMap.comp_apply,add_apply,zero_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul,zero_add] using he

variable {n : ℕ} [Nontrivial (Fin n)]

lemma mollifiedCloseCountMultiplier_partial_zero (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : φ.rOut≤1)
    (p : Direction n) (X : Configuration n L) (hfar : 8<torusDistance L (X p.1) v) :
    coordDerivative n L (mollifiedCloseCountMultiplier L s v φ).toFun p X=0 := by
  apply coordDerivative_zero_of_particle_locality L _
    ((mollifiedCloseCountMultiplier L s v φ).smooth.differentiable (by simp)) v 8 _ p X hfar
  intro X Y k hr hx hy
  simp only [mollifiedCloseCountMultiplier_apply,
    mollifiedCloseCount_away_eq L hs hs1 v φ hφ X Y k hr hx hy]

lemma mollifiedCloseCutoff_partial_zero (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : φ.rOut≤1)
    (h : ℝ) (p : Direction n) (X : Configuration n L) (hfar : 8<torusDistance L (X p.1) v) :
    coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X=0 := by
  rw [mollifiedCloseCutoff_partial,mollifiedCloseCountMultiplier_partial_zero L hs hs1 v φ hφ p X hfar,mul_zero]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_MollifiedCloseJoint
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
variable {n : ℕ} [Nontrivial (Fin n)]

lemma mollifiedCloseCutoff_partials_disjoint (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (v w : Torus L) (hvw : 20≤torusDistance L v w)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : φ.rOut≤1)
    (h : ℝ) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X=0 ∨
    coordDerivative n L (mollifiedCloseCutoff L s w φ h).toFun p X=0 := by
  by_cases hv : 8<torusDistance L (X p.1) v
  · exact Or.inl (mollifiedCloseCutoff_partial_zero L hs hs1 v φ hφ h p X hv)
  · apply Or.inr
    apply mollifiedCloseCutoff_partial_zero L hs hs1 w φ hφ h p X
    have ht := torusDistance_triangle' L v (X p.1) w
    rw [torusDistance_comm L v (X p.1)] at ht
    linarith only [ht,hvw,le_of_not_gt hv]

lemma mollifiedCloseJoint_apply (L : Length) (s : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (A : Finset (Torus L)) (X : Configuration n L) :
    (mollifiedCloseJoint L s φ h A).toFun X=∏ v∈A, (closeHighProfile h (mollifiedCloseCount L s v φ X):ℂ) := by
  change (∏ v∈A, (mollifiedCloseCutoff L s v φ h).toFun X)=_
  simp_rw [mollifiedCloseCutoff_apply]

lemma mollifiedCloseJoint_real (L : Length) (s : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (A : Finset (Torus L)) (X : Configuration n L) :
    conj ((mollifiedCloseJoint L s φ h A).toFun X)=(mollifiedCloseJoint L s φ h A).toFun X := by
  simp only [mollifiedCloseJoint_apply,map_prod,Complex.conj_ofReal]

lemma mollifiedCloseJoint_partial (L : Length) (s : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (h : ℝ) (A : Finset (Torus L))
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (mollifiedCloseJoint L s φ h A).toFun p X=
      ∑ v∈A, (mollifiedCloseJoint L s φ h (A.erase v)).toFun X*
        coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X := by
  classical
  exact SmoothMultiplier.partial_finsetProd A _ p X

theorem mollifiedCloseJoint_gradient (L : Length) {s h M : ℝ} (hs : 0 < s) (hs1 : 2*s≤1)
    (hh : 0<h) (hM : 0≤M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : φ.rOut≤1)
    (A : Finset (Torus L)) (hA : ∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (mollifiedCloseJoint L s φ h A).toFun p X‖^2)≤
      (8192*M^2/(h*s^2))*∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).toFun X‖^2 := by
  classical
  have he (p : Direction n) :
      ‖coordDerivative n L (mollifiedCloseJoint L s φ h A).toFun p X‖^2=
        ∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).toFun X‖^2*
          ‖coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X‖^2 := by
    rw [mollifiedCloseJoint_partial,norm_sq_sum_of_disjoint]
    · simp_rw [norm_mul,mul_pow]
    · intro v hv w hw hvw
      rcases mollifiedCloseCutoff_partials_disjoint L hs hs1 v w (hA v hv w hw hvw) φ hφ h p X with h1 | h2
      · exact Or.inl (by rw [h1,mul_zero])
      · exact Or.inr (by rw [h2,mul_zero])
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  calc
    _ ≤ ‖(mollifiedCloseJoint L s φ h (A.erase v)).toFun X‖^2*(8192*M^2/(h*s^2)) :=
      mul_le_mul_of_nonneg_left (mollifiedCloseCutoff_gradient L hs (by linarith only [hs1,hs]) hh hM hb v φ X) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ} [Nontrivial (Fin n)]

lemma closeCount_mollified_comparison (L : Length) {s : ℝ} (hs : 0 < s) (hs1 : s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (X : Configuration n L) :
    mollifiedCloseCount L s v φ X≤2*localCloseSmoothCount L s v X+2*((32/s)*φ.rOut)^2 ∧
    localCloseSmoothCount L s v X≤2*mollifiedCloseCount L s v φ X+2*((32/s)*φ.rOut)^2 := by
  have he := mollifiedCloseRoot_approximation L hs hs1 v φ X
  have hr : 0≤localCloseRoot L s v X := norm_nonneg _
  have hm := mollifiedCloseRoot_nonneg L s v φ X
  have h1 : |mollifiedCloseRoot L s v φ X|≤localCloseRoot L s v X+(32/s)*φ.rOut := by
    rw [abs_of_nonneg hm]
    have hu := (le_abs_self _).trans he
    linarith only [hu]
  have h2 : |localCloseRoot L s v X|≤ mollifiedCloseRoot L s v φ X+(32/s)*φ.rOut := by
    rw [abs_of_nonneg hr]
    have hu := (neg_le_abs _).trans he
    linarith only [hu]
  have hh1 := sq_le_twice_sq_of_abs_le h1
  have hh2 := sq_le_twice_sq_of_abs_le h2
  rw [localCloseRoot_sq] at hh1 hh2
  exact ⟨hh1,hh2⟩

lemma mollifiedCloseCutoff_nonzero_count (L : Length) {s h : ℝ} (hs : 0 < s) (hs1 : s≤1) (hh : 0<h)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n)))
    (hφ : ((32/s)*φ.rOut)^2≤h/4) (X : Configuration n L)
    (hn : (mollifiedCloseCutoff L s v φ h).toFun X≠0) :
    h/4≤localCloseSmoothCount L s v X := by
  have hm : h< mollifiedCloseCount L s v φ X := by
    by_contra hle
    have hz := closeHighProfile_zero hh (le_of_not_gt hle)
    rw [mollifiedCloseCutoff_apply,hz,Complex.ofReal_zero] at hn
    exact hn rfl
  have he := (closeCount_mollified_comparison L hs hs1 v φ X).1
  linarith only [hm,he,hφ]

lemma mollifiedCloseCutoff_covers (L : Length) {s h : ℝ} (hs : 0 < s) (hs1 : s≤1) (hh : 0<h)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n)))
    (hφ : ((32/s)*φ.rOut)^2≤h/4) (X : Configuration n L)
    (hn : 8*h≤((localCloseLabels L s v X).card:ℝ)) :
    (mollifiedCloseCutoff L s v φ h).toFun X=1 := by
  have hm := hn.trans (localCloseSmoothCount_covers L hs v X)
  have he := (closeCount_mollified_comparison L hs hs1 v φ X).2
  have ht : 2*h≤ mollifiedCloseCount L s v φ X := by linarith only [hm,he,hφ,hh]
  rw [mollifiedCloseCutoff_apply,closeHighProfile_one hh ht,Complex.ofReal_one]

lemma mollifiedCloseJoint_covers (L : Length) {s h : ℝ} (hs : 0 < s) (hs1 : s≤1) (hh : 0<h)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : ((32/s)*φ.rOut)^2≤h/4)
    (A : Finset (Torus L)) (X : Configuration n L)
    (hclose : ∀ v∈A, 8*h≤((localCloseLabels L s v X).card:ℝ)) :
    (mollifiedCloseJoint L s φ h A).toFun X=1 := by
  change (∏ v∈A, (mollifiedCloseCutoff L s v φ h).toFun X)=1
  exact Finset.prod_eq_one (fun v hv ↦ mollifiedCloseCutoff_covers L hs hs1 hh v φ hφ X (hclose v hv))

lemma mollifiedCloseJoint_nonzero_count (L : Length) {s h : ℝ} (hs : 0 < s) (hs1 : s≤1) (hh : 0<h)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : ((32/s)*φ.rOut)^2≤h/4)
    (A : Finset (Torus L)) (hA : ∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w)
    (X : Configuration n L) (hne : (mollifiedCloseJoint L s φ h A).toFun X≠0) :
    (h/4)*(A.card:ℝ)≤((localizedNearLabels L A s X).card:ℝ) := by
  classical
  have hn : ∀ v∈A, (mollifiedCloseCutoff L s v φ h).toFun X≠0 := Finset.prod_ne_zero_iff.mp hne
  calc
    _ = ∑ _v∈A, h/4 := by simp [mul_comm]
    _ ≤ ∑ v∈A, localCloseSmoothCount L s v X :=
      Finset.sum_le_sum (fun v hv ↦ mollifiedCloseCutoff_nonzero_count L hs hs1 hh v φ hφ X (hn v hv))
    _ ≤ _ := localCloseSmoothCount_sum_le L hs A (fun v hv w hw hvw ↦ lt_of_lt_of_le (by norm_num : (12:ℝ)<20) (hA v hv w hw hvw)) X

omit [Nontrivial (Fin n)] in
lemma exists_close_mollifier (s h : ℝ) (hs : 0 < s) (hh : 0<h) :
    ∃ φ : ContDiffBump (0 : EuclideanConfiguration (Fin n)), φ.rOut≤1 ∧ ((32/s)*φ.rOut)^2≤h/4 := by
  let δ : ℝ := min (1/2) (s*Real.sqrt h/128)
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  let φ : ContDiffBump (0 : EuclideanConfiguration (Fin n)) := ⟨δ/2,δ,by positivity,by linarith only [hδ]⟩
  refine ⟨φ, (min_le_left _ _).trans (by norm_num),?_⟩
  have he : (32/s)*φ.rOut≤Real.sqrt h/4 := by
    change (32/s)*δ≤_
    calc
      _ ≤ (32/s)*(s*Real.sqrt h/128) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by field_simp; ring
  have he' := (sq_le_sq₀ (mul_nonneg (by positivity) φ.rOut_pos.le) (by positivity)).mpr he
  have hhroot := Real.sq_sqrt hh.le
  nlinarith only [he',hhroot,hh]

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
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_WeightedUnitPairCount
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma localizedNearLabels_integrable {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) (u : ScalarL2 n L) :
    Integrable (fun X ↦ ((localizedNearLabels L A s X).card:ℝ)*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ))).comp (localizedNearLabels_card_measurable L A s))
    (B:=(n:ℝ)) (fun X ↦ by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast (show (localizedNearLabels L A s X).card≤n by simpa using (localizedNearLabels L A s X).card_le_univ))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SpatialScalarSquare
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma weightedSiteCount_integrable {n : ℕ} (L : Length) (A : Finset (Torus L)) (u : ScalarL2 n L) :
    Integrable (fun X ↦ weightedSiteCount L A X*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u (weightedSiteCount_continuous L A).measurable
    (fun X ↦ by rw [abs_of_nonneg (weightedSiteCount_nonneg L A X)]; exact weightedSiteCount_le L A X)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FinsetEraseRecursion2
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

lemma finset_erase_recursion_on {S : Type*} [DecidableEq S] (a : Finset S → ℝ)
    (P : Finset S → Prop) (hP : ∀ A s, P A → P (A.erase s)) (q : ℝ)
    (hq : 0≤q) (h0 : a ∅≤1)
    (hr : ∀ A : Finset S, P A → A.Nonempty → (A.card:ℝ)*a A≤q*∑ s∈A, a (A.erase s)) :
    ∀ A : Finset S, P A → a A≤q^A.card := by
  intro A
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro hPA
    by_cases hA : A.Nonempty
    · have hc : 0<(A.card:ℝ) := by exact_mod_cast hA.card_pos
      have hs : (∑ s∈A, a (A.erase s))≤(A.card:ℝ)*q^(A.card-1) := by
        calc
          _ ≤ ∑ _s∈A, q^(A.card-1) := Finset.sum_le_sum fun s hs ↦ by
            have hh := ih (A.erase s) (Finset.erase_ssubset hs) (hP A s hPA)
            rwa [Finset.card_erase_of_mem hs] at hh
          _ = _ := by simp
      have he : q*((A.card:ℝ)*q^(A.card-1))=(A.card:ℝ)*q^A.card := by
        rw [show q^A.card=q^(A.card-1)*q by
          conv_lhs => rw [←Nat.sub_add_cancel hA.card_pos]
          rw [pow_succ]]
        ring
      have ht := (hr A hPA hA).trans ((mul_le_mul_of_nonneg_left hs hq).trans_eq he)
      exact (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_comm (A.card:ℝ)] using ht)
    · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simpa [he] using h0

variable {n : ℕ} [Nontrivial (Fin n)]

lemma mollifiedCloseJoint_empty_onScalar (L : Length) (s h : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (u : ScalarL2 n L) :
    (mollifiedCloseJoint L s φ h ∅).onScalar u=u := by
  apply Lp.ext
  filter_upwards [(mollifiedCloseJoint L s φ h ∅).coe_onScalar u] with X hX
  simpa only [mollifiedCloseJoint_apply,Finset.prod_empty,one_mul] using hX

lemma groundPositionLaw_le_closeJoint (L : Length) {s h : ℝ} (hs : 0 < s) (hs1 : s≤1) (hh : 0<h)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : ((32/s)*φ.rOut)^2≤h/4)
    (A : Finset (Torus L)) (g : Jet n L) (T : Set (Configuration n L)) (hT : MeasurableSet T)
    (hcount : ∀ X∈T, ∀ v∈A, 8*h≤((localCloseLabels L s v X).card:ℝ)) :
    groundPositionLaw n L g T≤ENNReal.ofReal (‖(mollifiedCloseJoint L s φ h A).onScalar g.1‖^2) := by
  rw [groundPositionLaw,withDensity_apply _ hT,
    ←ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp g.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integrableOn
      (Eventually.of_forall fun X ↦ sq_nonneg ‖g.1 X‖),IndicatorStrong.norm_sq_integral]
  apply ENNReal.ofReal_le_ofReal
  have hi : Integrable (fun X ↦ ‖((mollifiedCloseJoint L s φ h A).onScalar g.1) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  calc
    _ = ∫ X in T, ‖((mollifiedCloseJoint L s φ h A).onScalar g.1) X‖^2 ∂volume := by
      apply setIntegral_congr_ae hT
      filter_upwards [(mollifiedCloseJoint L s φ h A).coe_onScalar g.1] with X hX hXT
      rw [hX,mollifiedCloseJoint_covers L hs hs1 hh φ hφ A X (hcount X hXT),one_mul]
    _ ≤ _ := setIntegral_le_integral hi (ae_of_all _ fun X ↦ sq_nonneg _)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma close_support_integral {n : ℕ} {L : Length} (A : Finset (Torus L))
    {s C c b D h : ℝ} (hc : 0 < c) (hb : 0<b)
    (hcoef : (C+1)*D ≤ c/b^3*(h/4))
    (f : SmoothMultiplier n L) (g : ScalarL2 n L)
    (hsupport : ∀ X, f.toFun X≠0 → (h/4)*(A.card:ℝ)≤((localizedNearLabels L A s X).card:ℝ)) :
    D*(A.card:ℝ)*‖f.onScalar g‖^2≤
      ∫ X, (weightedSiteCount L A X-C*D*(A.card:ℝ)+
        c/b^3*((localizedNearLabels L A s X).card:ℝ))*‖(f.onScalar g) X‖^2 := by
  have hn : Integrable (fun X ↦ ‖(f.onScalar g) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  have hf := weightedSiteCount_integrable L A (f.onScalar g)
  have hk := localizedNearLabels_integrable L A s (f.onScalar g)
  have hi : Integrable (fun X ↦ (weightedSiteCount L A X-C*D*(A.card:ℝ)+
      c/b^3*((localizedNearLabels L A s X).card:ℝ))*‖(f.onScalar g) X‖^2) volume := by
    have he : (fun X ↦ (weightedSiteCount L A X-C*D*(A.card:ℝ)+
        c/b^3*((localizedNearLabels L A s X).card:ℝ))*‖(f.onScalar g) X‖^2) =
        fun X ↦ (weightedSiteCount L A X*‖(f.onScalar g) X‖^2-
          (C*D*(A.card:ℝ))*‖(f.onScalar g) X‖^2)+
          (c/b^3)*(((localizedNearLabels L A s X).card:ℝ)*‖(f.onScalar g) X‖^2) := by
      funext X
      ring
    rw [he]
    exact (hf.sub (hn.const_mul (C*D*(A.card:ℝ)))).add (hk.const_mul (c/b^3))
  rw [IndicatorStrong.norm_sq_integral,←integral_const_mul]
  apply integral_mono_ae (hn.const_mul _) hi
  filter_upwards [f.coe_onScalar g] with X hX
  by_cases hz : f.toFun X=0
  · simp only [hX,hz,zero_mul,norm_zero,zero_pow (by omega : (2:ℕ)≠0),mul_zero,le_rfl]
  · have hkX := mul_le_mul_of_nonneg_left (hsupport X hz) (by positivity : 0 ≤ c/b^3)
    have hcX := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg A.card : (0:ℝ)≤A.card)
    have hw := weightedSiteCount_nonneg L A X
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith only [hkX,hcX,hw]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_SpatialCloseScale
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma spatialCloseScale_pos {D b : ℝ} (hD : 0< D) (hb : 0< b) : 0< spatialCloseScale D b :=
  mul_pos hb (Real.rpow_pos_of_pos hD _)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_SpatialSeparatedCloseJoint
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

theorem spatial_separated_close_joint : ∃ C c G : ℝ, 0<C ∧ 0 < c ∧ 0<G ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r b D h : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0 < r → 0<b → 0<h →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 → (C+1)*D ≤ c/b^3*(h/4) →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))), φ.rOut≤1 →
      ((32/spatialCloseScale D b)*φ.rOut)^2≤h/4 →
    ∀ (A : Finset (Torus L)), (∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w) →
      ‖(mollifiedCloseJoint L (spatialCloseScale D b) φ h A).onScalar g.1‖^2≤
        (G/(h*(spatialCloseScale D b)^2)/((D*r)*D))^A.card := by
  obtain ⟨C,c,hC,hc,hform⟩ := spatial_localized_form
  obtain ⟨M,hM,hderiv⟩ := PeriodicCutoff.exists_transition_bound
  let G : ℝ := 8192*M^2
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨C,c,G,hC,hc,hG,?_⟩
  intro n K _ L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef g hg φ hφ hφe
  let s : ℝ := spatialCloseScale D b
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hs : 0 < s := spatialCloseScale_pos hDpos hb
  have hs' : s≤1 := by dsimp [s]; linarith only [hs1]
  let q : ℝ := G/(h*s^2)/((D*r)*D)
  have hq : 0≤q := by dsimp [q]; positivity
  have hγ : 0<(D*r)*D := by positivity
  let P : Finset (Torus L) → Prop := fun A ↦ ∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w
  have hP (A : Finset (Torus L)) (v : Torus L) (hA : P A) : P (A.erase v) := by
    intro x hx y hy hxy
    exact hA x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
  apply finset_erase_recursion_on (fun A ↦ ‖(mollifiedCloseJoint L s φ h A).onScalar g.1‖^2) P hP q hq
  · rw [mollifiedCloseJoint_empty_onScalar,hg.2.2.1]
    norm_num
  · intro A hA _hAnonempty
    let f := mollifiedCloseJoint L s φ h A
    let u := f.onJet g
    have hu : u∈dirichletDomain n L r := f.onJet_mem_domain hg.1
    have hsupport := close_support_integral A hc hb hcoef f g.1
      (mollifiedCloseJoint_nonzero_count L hs hs' hh φ hφe A hA)
    have hformA := hform n K L hL r b D hDeq hD hα hr hb hs1 hsL hsmall g hg A u hu
    have hm := hg.smooth_multiplier_identity f (mollifiedCloseJoint_real L s φ h A)
    have hbnd := SmoothMultiplier.gradient_norm_le A f
      (fun v ↦ mollifiedCloseJoint L s φ h (A.erase v)) (G/(h*s^2))
      (mollifiedCloseJoint_gradient L hs hs1 hh hM.le hderiv φ hφ A hA) g.1
    have hpen : ((D*r)*D)*((A.card:ℝ)*‖f.onScalar g.1‖^2)≤
        (G/(h*s^2))*∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).onScalar g.1‖^2 := by
      calc
        _ = (D*r)*(D*(A.card:ℝ)*‖f.onScalar g.1‖^2) := by ring
        _ ≤ (D*r)*(∫ X, (weightedSiteCount L A X-C*D*(A.card:ℝ)+
            c/b^3*((localizedNearLabels L A s X).card:ℝ))*‖(f.onScalar g.1) X‖^2) :=
          mul_le_mul_of_nonneg_left hsupport (by positivity)
        _ ≤ energy u-energy g*‖u.1‖^2 := hformA
        _ = ∑ p : Direction n, ‖f.derivativeScalar p g.1‖^2 := hm
        _ ≤ _ := hbnd
    have hdiv := (le_div_iff₀ hγ).mpr (by simpa only [mul_comm ((D*r)*D)] using hpen)
    have he : ((G/(h*s^2))*∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).onScalar g.1‖^2)/((D*r)*D)=
        q*∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).onScalar g.1‖^2 := by
      dsimp [q]
      ring
    simpa only [he] using hdiv

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PairCloseLabels
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

lemma localCloseLabels_eq_pairCloseLabels {m : ℕ} [Nontrivial (Fin m)]
    (L : Length) (s : ℝ) (v : Torus L) (Y : Configuration m L) :
    localCloseLabels L s v Y=pairCloseLabels L s v Y := by
  classical
  ext i
  simp only [localCloseLabels,pairCloseLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hv,hi⟩
    exact ⟨hv,nearestLabel L Y i,nearestLabel_ne L Y i,hi⟩
  · rintro ⟨hv,j,hji,hj⟩
    exact ⟨hv,(nearestParticleDistance_le L Y i j hji).trans hj⟩

lemma pairCloseLabels_restrict_card_le {m n : ℕ} [Nontrivial (Fin n)]
    (L : Length) (s : ℝ) (v : Torus L) (e : Fin m ↪ Fin n) (X : Configuration n L) :
    (pairCloseLabels L s v (fun i ↦ X (e i))).card≤(localCloseLabels L s v X).card := by
  classical
  have hsub : (pairCloseLabels L s v (fun i ↦ X (e i))).map e⊆localCloseLabels L s v X := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨hv,k,hkj,hk⟩ := (Finset.mem_filter.1 hj).2
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _,hv,?_⟩
    exact (nearestParticleDistance_le L X (e j) (e k) (fun he ↦ hkj (e.injective he))).trans hk
  simpa only [Finset.card_map] using Finset.card_le_card hsub

attribute [local irreducible] torusDistance nearestParticleDistance

lemma pairCloseLabels_measurable {m : ℕ} (L : Length) (s : ℝ) (v : Torus L) :
    Measurable (fun Y : Configuration m L ↦ ((pairCloseLabels L s v Y).card:ℝ)) := by
  classical
  simp only [pairCloseLabels,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro i _
  have hd : Continuous (fun Y : Configuration m L ↦ torusDistance L (Y i) v) :=
    (torusDistance_continuous_pair L).comp
      ((continuous_apply i).prodMk (continuous_const : Continuous (fun _ : Configuration m L ↦ v)))
  have hp : MeasurableSet {Y : Configuration m L | ∃ j, j≠i ∧ torusDistance L (Y i) (Y j)≤ s} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    have hc : Continuous (fun Y : Configuration m L ↦ torusDistance L (Y i) (Y j)) :=
      (torusDistance_continuous_pair L).comp ((show Continuous (fun Y : Configuration m L ↦ Y i) from continuous_apply i).prodMk
        (show Continuous (fun Y : Configuration m L ↦ Y j) from continuous_apply j))
    by_cases hji : j≠i
    · convert measurableSet_le hc.measurable (show Measurable (fun _ : Configuration m L ↦ s) from measurable_const) using 1
      all_goals try with_reducible_and_instances rfl
      ext Y
      exact and_iff_right hji
    · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Configuration m L))) using 1
      all_goals try with_reducible_and_instances rfl
      ext Y
      exact iff_false_intro (fun h ↦ hji h.1)
  exact Measurable.ite ((measurableSet_le hd.measurable measurable_const).inter hp)
    measurable_const measurable_const

theorem closeBath_marginal_le {m n : ℕ} [Nontrivial (Fin n)] {S : Type*}
    (L : Length) (s h : ℝ) (e : Fin m ↪ Fin n) (μ : Measure (Configuration n L))
    (v : S → Torus L) (A : Finset S) :
    (μ.map (fun X i ↦ X (e i))) {Y | ∀ a∈A, h≤((pairCloseLabels L s (v a) Y).card:ℝ)}≤
      μ {X | ∀ a∈A, h≤((localCloseLabels L s (v a) X).card:ℝ)} := by
  classical
  have hm : Measurable (fun X : Configuration n L ↦ (fun i : Fin m ↦ X (e i))) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  have hT : MeasurableSet {Y : Configuration m L | ∀ a∈A, h≤((pairCloseLabels L s (v a) Y).card:ℝ)} := by
    simpa only [Set.ofPred_forall] using Finset.measurableSet_biInter A (fun a _ ↦
      measurableSet_le (show Measurable (fun _ : Configuration m L ↦ h) from measurable_const)
        (pairCloseLabels_measurable L s (v a)))
  rw [Measure.map_apply hm hT]
  apply measure_mono
  intro X hX a ha
  exact (hX a ha).trans (by exact_mod_cast pairCloseLabels_restrict_card_le L s (v a) e X)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalCloseLabelsMeasurable
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

variable {n : ℕ} [Nontrivial (Fin n)]

attribute [local irreducible] torusDistance nearestParticleDistance

lemma localCloseLabels_measurable (L : Length) (s : ℝ) (v : Torus L) :
    Measurable (fun X : Configuration n L ↦ ((localCloseLabels L s v X).card:ℝ)) := by
  classical
  simp only [localCloseLabels,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro i _
  have hd : Continuous (fun X : Configuration n L ↦ torusDistance L (X i) v) :=
    (torusDistance_continuous_pair L).comp
      ((continuous_apply i).prodMk (continuous_const : Continuous (fun _ : Configuration n L ↦ v)))
  exact Measurable.ite ((measurableSet_le hd.measurable measurable_const).inter
    (measurableSet_le (nearestParticleDistance_continuous L i).measurable measurable_const))
    measurable_const measurable_const

theorem spatial_separated_close_probability : ∃ C c G : ℝ, 0<C ∧ 0 < c ∧ 0<G ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r b D h : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0 < r → 0<b → 0<h →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 → (C+1)*D ≤ c/b^3*(h/4) →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), (∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w) →
      groundPositionLaw n L g {X | ∀ v∈A, 8*h≤((localCloseLabels L (spatialCloseScale D b) v X).card:ℝ)}≤
        ENNReal.ofReal ((G/(h*(spatialCloseScale D b)^2)/((D*r)*D))^A.card) := by
  obtain ⟨C,c,G,hC,hc,hG,hjoint⟩ := spatial_separated_close_joint
  refine ⟨C,c,G,hC,hc,hG,?_⟩
  intro n K _ L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef g hg A hA
  have hs := spatialCloseScale_pos (zero_lt_one.trans_le hD) hb
  obtain ⟨φ,hφ,hφe⟩ := exists_close_mollifier (n:=n) (spatialCloseScale D b) h hs hh
  let T : Set (Configuration n L) := {X | ∀ v∈A, 8*h≤((localCloseLabels L (spatialCloseScale D b) v X).card:ℝ)}
  have hT : MeasurableSet T := by
    simpa only [T,Set.ofPred_forall] using Finset.measurableSet_biInter A (fun v _ ↦
      measurableSet_le (show Measurable (fun _ : Configuration n L ↦ 8*h) from measurable_const)
        (localCloseLabels_measurable L (spatialCloseScale D b) v))
  have ht := groundPositionLaw_le_closeJoint L hs (by linarith only [hs1]) hh φ hφe A g T hT (fun _ hX ↦ hX)
  exact ht.trans (ENNReal.ofReal_le_ofReal (hjoint n K L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef g hg φ hφ hφe A hA))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SpatialGridCloseProbability
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

theorem spatial_grid_close_probability : ∃ Q : ℕ, 0<Q ∧ ∃ C c G : ℝ, 0<C ∧ 0 < c ∧ 0<G ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r b D h : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0 < r → 0<b → 0<h →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 → (C+1)*D ≤ c/b^3*(h/4) →
      G/(h*(spatialCloseScale D b)^2)/((D*r)*D)≤1 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ A : Finset (CubeCell K),
      groundPositionLaw n L g {X | ∀ v∈A, 8*h≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v) X).card:ℝ)}≤
        ENNReal.ofReal ((Real.rpow (G/(h*(spatialCloseScale D b)^2)/((D*r)*D)) (1/(Q:ℝ)))^A.card) := by
  obtain ⟨C,c,G,hC,hc,hG,hsep⟩ := spatial_separated_close_probability
  obtain ⟨Q,hQ,hsubset⟩ := unitGrid_separated_subset
  refine ⟨Q,hQ,C,c,G,hC,hc,hG,?_⟩
  intro n K _ L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef hbase g hg A
  classical
  obtain ⟨B,hBA,hB,hcard⟩ := hsubset K L hL A
  let q : ℝ := G/(h*(spatialCloseScale D b)^2)/((D*r)*D)
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hs : 0 < spatialCloseScale D b := spatialCloseScale_pos hDpos hb
  have hq : 0<q := by dsimp [q]; positivity
  have hQpos : 0<(Q:ℝ) := by exact_mod_cast hQ
  have hinj : Set.InjOn (unitCenter L) (B : Set (CubeCell K)) := by
    intro v hv w hw heq
    by_contra hvw
    have hd := hB v hv w hw hvw
    rw [heq] at hd
    simp only [torusDistance,dist_self,zero_pow (by omega : (2:ℕ)≠0),Finset.sum_const_zero,Real.sqrt_zero] at hd
    norm_num at hd
  have hbcard : (B.image (unitCenter L)).card=B.card := Finset.card_image_of_injOn hinj
  have hbsep : ∀ v∈B.image (unitCenter L), ∀ w∈B.image (unitCenter L), v≠w → 20≤torusDistance L v w := by
    intro v hv w hw hvw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    exact hB i hi j hj (fun he ↦ hvw (congrArg (unitCenter L) he))
  have hp := hsep n K L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef g hg (B.image (unitCenter L)) hbsep
  have hpow : q^B.card≤(Real.rpow q (1/(Q:ℝ)))^A.card := by
    change q^B.card≤(q^(1/(Q:ℝ)))^A.card
    rw [←Real.rpow_natCast q B.card,←Real.rpow_mul_natCast hq.le (1/(Q:ℝ)) A.card]
    apply Real.rpow_le_rpow_of_exponent_ge hq hbase
    have hh : (A.card:ℝ)/(Q:ℝ)≤(B.card:ℝ) := (div_le_iff₀ hQpos).mpr (by simpa only [mul_comm] using hcard)
    simpa only [one_div,div_eq_mul_inv,mul_one,mul_comm] using hh
  apply (measure_mono (show
      {X : Configuration n L | ∀ v∈A, 8*h≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v) X).card:ℝ)} ⊆
      {X : Configuration n L | ∀ v∈B.image (unitCenter L), 8*h≤((localCloseLabels L (spatialCloseScale D b) v X).card:ℝ)} by
    intro X hX v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact hX i (hBA hi))).trans
  exact hp.trans (ENNReal.ofReal_le_ofReal (by simpa only [hbcard] using hpow))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_SpatialCloseScale2
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
noncomputable section

lemma spatialCloseScale_le {D b : ℝ} (hD : 1≤D) (hb : 0≤b) : spatialCloseScale D b≤b := by
  unfold spatialCloseScale
  calc
    _ ≤ b*1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hD (by norm_num)) hb
    _ = _ := mul_one _

lemma spatialCloseScale_square {D b : ℝ} (hD : 0<D) :
    (spatialCloseScale D b)^2*D^2=b^2*D^(4/3:ℝ) := by
  unfold spatialCloseScale
  rw [mul_pow,←Real.rpow_mul_natCast hD.le]
  calc
    _ = b^2*(D^((-1/3:ℝ)*2)*D^(2:ℝ)) := by rw [Real.rpow_ofNat]; ring_nf
    _ = b^2*D^(((-1/3:ℝ)*2)+2) := by rw [Real.rpow_add hD]
    _ = _ := by norm_num

lemma spatial_close_base_bound {G θ D b r : ℝ} (hG : 0≤G) (hθ : 0<θ) (hD : 0<D)
    (hb : 0<b) (hα : 1≤D*r) :
    G/((θ*D/8)*(spatialCloseScale D b)^2)/((D*r)*D)≤
      ((8*G/θ)/b^2)*D^(-(4/3):ℝ) := by
  have hs := spatialCloseScale_pos hD hb
  have hden : D≤(D*r)*D := by nlinarith only [mul_le_mul_of_nonneg_right hα hD.le]
  have heq := spatialCloseScale_square (b:=b) hD
  have hrpow : 0<D^(4/3:ℝ) := Real.rpow_pos_of_pos hD _
  have hinv : D^(-(4/3):ℝ)=(D^(4/3:ℝ))⁻¹ := Real.rpow_neg hD.le _
  calc
    _ ≤ G/((θ*D/8)*(spatialCloseScale D b)^2)/D :=
      div_le_div_of_nonneg_left (by positivity) hD hden
    _ = ((8*G/θ)/b^2)*D^(-(4/3):ℝ) := by
      rw [hinv]
      field_simp
      linear_combination -G*heq

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
noncomputable section

lemma exists_close_scale {C c θ : ℝ} (hC : 0<C) (hc : 0 < c) (hθ : 0<θ) :
    ∃ b : ℝ, 0<b ∧ b≤1/4 ∧ (C+1) ≤ c/b^3*(θ/32) := by
  let b := min (1/4) (c*θ/(64*(C+1)))
  have hb : 0<b := lt_min (by norm_num) (by positivity)
  have hb1 : b≤1/4 := min_le_left _ _
  have hbsmall : b*(64*(C+1)) ≤ c*θ := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hpow : b^3≤b := by
    have hb01 : b≤1 := by linarith only [hb1]
    have hsq : b^2≤b := by nlinarith only [mul_le_mul_of_nonneg_left hb01 hb.le]
    nlinarith only [mul_le_mul_of_nonneg_left hsq hb.le,hsq]
  have hcoef : (C+1)*(32*b^3) ≤ c*θ := by
    have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0≤32*(C+1))
    nlinarith only [hmul,hbsmall,mul_nonneg hb.le (by positivity : 0≤C+1)]
  refine ⟨b,hb,hb1,?_⟩
  have he : c/b^3*(θ/32)=c*θ/(32*b^3) := by ring
  rw [he]
  exact (le_div_iff₀ (by positivity)).mpr hcoef

theorem spatial_scaled_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r D : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0 < r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
      (Gθ/b^2)*D^(-(4/3):ℝ)≤1 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ A : Finset (CubeCell K),
      groundPositionLaw n L g {X | ∀ v∈A, θ*D≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v) X).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,C,c,G,hC,hc,hG,hgrid⟩ := spatial_grid_close_probability
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,hb,hb1,hcoef⟩ := exists_close_scale hC hc hθ
  let Gθ : ℝ := 8*G/θ
  have hGθ : 0<Gθ := by dsimp [Gθ]; positivity
  refine ⟨b,Gθ,hb,hb1,hGθ,?_⟩
  intro n K _ L hL r D hL100 hDeq hD hα hr hsmall hbase g hg A
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hs := spatialCloseScale_pos hDpos hb
  have hsb := (spatialCloseScale_le hD hb.le).trans hb1
  have hh : 0<θ*D/8 := by positivity
  have hcD : (C+1)*D ≤ c/b^3*((θ*D/8)/4) := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hDpos.le
    have he : (c/b^3*(θ/32))*D=c/b^3*((θ*D/8)/4) := by ring
    rwa [he] at hmul
  have hq := spatial_close_base_bound hG.le hθ hDpos hb hα
  have hp := hgrid n K L hL r b D (θ*D/8) hDeq hD hα hr hb hh
    (by linarith only [hsb]) (by linarith only [hsb,hL100]) hsmall hcD (hq.trans hbase) g hg A
  have ht : 8*(θ*D/8)=θ*D := by ring
  simp only [ht,Real.rpow_eq_pow] at hp
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _)
  apply Real.rpow_le_rpow (by positivity) hq
  positivity

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
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_CloseTailBaseTendsto
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

lemma closeTailBase_tendsto_zero (G b : ℝ) :
    Tendsto (fun D : ℝ ↦ (G/b^2)*D^(-(4/3):ℝ)) atTop (𝓝 0) := by
  simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<4/3)).const_mul (G/b^2)

lemma closeTailProbability_tendsto_zero (G b : ℝ) {Q : ℕ} (hQ : 0<Q) :
    Tendsto (fun D : ℝ ↦ ((G/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) := by
  have hQpos : (0:ℝ)<Q := by exact_mod_cast hQ
  have he : (0:ℝ)<1/(Q:ℝ) := by positivity
  have hc := (Real.continuous_rpow_const he.le).continuousAt.tendsto.comp (closeTailBase_tendsto_zero G b)
  simpa only [Function.comp_def,Real.zero_rpow he.ne'] using hc

lemma smallness_of_large_density {n : ℕ} (L : Length) {D α αmax : ℝ}
    (hDeq : D=(n:ℝ)/L.val^3) (hD : 1≤D) (hα : 0≤α) (hαmax : α≤αmax)
    (hlarge : 2*(2*Real.pi*αmax)^3≤D) :
    (n:ℝ)*(2*Real.pi*(α/D))^3≤L.val^3/2 := by
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hL3 : 0<L.val^3 := pow_pos L.property _
  have hn : (n:ℝ)=D*L.val^3 := ((eq_div_iff hL3.ne').mp hDeq).symm
  have halpha : (2*Real.pi*α)^3≤(2*Real.pi*αmax)^3 := by gcongr
  have hDsq : D≤D^2 := by nlinarith only [mul_le_mul_of_nonneg_left hD hDpos.le]
  have hratio : (2*Real.pi*α)^3/D^2≤1/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hDpos)).mpr
    nlinarith only [halpha,hlarge,hDsq]
  calc
    _ = L.val^3*((2*Real.pi*α)^3/D^2) := by rw [hn]; field_simp
    _ ≤ L.val^3*(1/2) := mul_le_mul_of_nonneg_left hratio hL3.le
    _ = _ := by ring

theorem spatial_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g → ∀ A : Finset (CubeCell K),
      groundPositionLaw n L g {X | ∀ v∈A, θ*D≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v) X).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,htail⟩ := spatial_scaled_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,closeTailProbability_tendsto_zero Gθ b hQ,?_⟩
  intro αmax
  have hev : ∀ᶠ D : ℝ in atTop, (Gθ/b^2)*D^(-(4/3):ℝ)<1 :=
    (tendsto_order.1 (closeTailBase_tendsto_zero Gθ b)).2 1 zero_lt_one
  obtain ⟨D₁,hD₁⟩ := eventually_atTop.1 hev
  let D₀ : ℝ := max 1 (max D₁ (2*(2*Real.pi*αmax)^3))
  refine ⟨D₀,le_max_left _ _,?_⟩
  intro n K _ L hL D α hL100 hDeq hD₀ hα hαmax g hg A
  have hD : 1≤D := (le_max_left _ _).trans hD₀
  have hD1 : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD₀)
  have hlarge : 2*(2*Real.pi*αmax)^3≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD₀)
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hαpos : 0<α := zero_lt_one.trans_le hα
  have hprod : D*(α/D)=α := by field_simp
  exact hfin n K L hL (α/D) D hL100 hDeq hD (by rwa [hprod]) (by positivity)
    (smallness_of_large_density L hDeq hD hαpos.le hαmax hlarge) (hD₁ D hD1).le g hg A

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_DensityForcesTwoParticles
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

lemma density_forces_two_particles {n : ℕ} (L : Length) {D : ℝ}
    (hL : 100≤L.val) (hDeq : D=(n:ℝ)/L.val^3) (hD : 1≤D) : 2≤n := by
  have hLp : 0<L.val^3 := pow_pos L.property _
  have hn : L.val^3≤(n:ℝ) := by
    have hh : 1≤(n:ℝ)/L.val^3 := by rwa [←hDeq]
    simpa only [one_mul] using (le_div_iff₀ hLp).mp hh
  have hlarge : (100:ℝ)^3≤L.val^3 := by gcongr
  have hn2 : (2:ℝ)≤n := by linarith only [hn,hlarge]
  exact_mod_cast hn2

theorem spatial_full_and_bath_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g → ∀ A : Finset (CubeCell K),
      (groundPositionLaw n L g {X | ∀ v∈A, θ*D≤((pairCloseLabels L (spatialCloseScale D b) (unitCenter L v) X).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card))) ∧
      ∀ (m : ℕ) (e : Fin m ↪ Fin n),
      ((groundPositionLaw n L g).map (fun X i ↦ X (e i)))
        {Y | ∀ v∈A, θ*D≤((pairCloseLabels L (spatialCloseScale D b) (unitCenter L v) Y).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,htail⟩ := spatial_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,hlim,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hDfin⟩ := hfin αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K L hL D α hL100 hDeq hD hα hαmax g hg A
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr
    (density_forces_two_particles L hL100 hDeq (hD₀.trans hD))
  have hfull := hDfin n K L hL D α hL100 hDeq hD hα hαmax g hg A
  constructor
  · simpa only [localCloseLabels_eq_pairCloseLabels] using hfull
  · intro m e
    exact (closeBath_marginal_le L (spatialCloseScale D b) (θ*D) e
      (groundPositionLaw n L g) (unitCenter L) A).trans hfull

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SiteCube
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open MeasureTheory Set Filter HardSphere.Lattice

lemma unitCenter_siteCube {K : ℕ} [NeZero K] (L : Length) (v : DiscreteTorus K) :
    unitCenter L (siteCube v) = siteCenter L v := by
  funext j
  fin_cases j <;> rfl

lemma spatial_event_siteCube {m K : ℕ} [NeZero K] (L : Length) (s T : ℝ)
    (A : Finset (DiscreteTorus K)) :
    {Y : Configuration m L | ∀ v ∈ A.map siteCubeEmbedding,
      T ≤ ((pairCloseLabels L s (unitCenter L v) Y).card : ℝ)} =
    {Y : Configuration m L | A ⊆ closeSet L s T Y} := by
  classical
  ext Y
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, siteCubeEmbedding,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, unitCenter_siteCube,
    Set.mem_ofPred_eq, Finset.subset_iff, closeSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem physical_close_tail_oai : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [NeZero K] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), HardSphere.IsGroundVector n L (α/D) g →
    ∀ (m : ℕ) (e : Fin m ↪ Fin n) (A : Finset (DiscreteTorus K)),
      ((groundPositionLaw n L g).map (fun X i ↦ X (e i)))
        {Y | A ⊆ closeSet L (spatialCloseScale D b) (θ*D) Y} ≤
        (ENNReal.ofReal (((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))))^A.card := by
  obtain ⟨Q,hQ,htail⟩ := spatial_full_and_bath_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,hlim,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hDfin⟩ := hfin αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K _ L hL D α hL100 hDeq hD hα hαmax g hg m e A
  have hDp : 0<D := lt_of_lt_of_le (by norm_num) (hD₀.trans hD)
  have h := (hDfin n K L hL D α hL100 hDeq hD hα hαmax g hg
    (A.map siteCubeEmbedding)).2 m e
  rw [spatial_event_siteCube, Finset.card_map, ENNReal.ofReal_pow (by positivity)] at h
  exact h

end HardSphere.BathSlice

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.BathSlice.physical_close_tail_oai := @OAI.HardSphere.BathSlice.physical_close_tail_oai
