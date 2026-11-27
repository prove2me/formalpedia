-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.finite_setOf_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:27.66717+00:00
-- url     : https://prove2.me/submissions/3502c0a0-a9b8-46b2-a14b-fb16fd6e5904

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_finiteDimensional_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_Equiv_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_subtypeL_mem_intertwiners
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f)))
    {ι : Type*} {V : ι → Submodule ℂ H} [∀ i, CompleteSpace (V i)]
    (hinv : ∀ i, π.IsInvariant (V i))
    (hV : OrthogonalFamily ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ)
    {σ : UnitaryRep G K} (hσ : σ.IsIrreducible) :
    {i | (π.restrict (V i) (hinv i)).IsEquivalent σ}.Finite := by
  classical
  have := finiteDimensional_intertwiners hcpt hσ
  set J := {i | (π.restrict (V i) (hinv i)).IsEquivalent σ}
  let T : J → K →L[ℂ] H := fun i =>
    (V i).subtypeL ∘L ((i.2.some.symm.toLinearIsometryEquiv : K ≃ₗᵢ[ℂ] V i) : K →L[ℂ] V i)
  have hT : ∀ i, T i ∈ σ.intertwiners π := fun i =>
    comp_mem_intertwiners (subtypeL_mem_intertwiners π (V i) (hinv i)) i.2.some.symm.mem_intertwiners
  have hTV : ∀ (i : J) x, T i x ∈ V i := fun i x =>
    ((i.2.some.symm.toLinearIsometryEquiv : K ≃ₗᵢ[ℂ] V i) x).2
  have hTnorm : ∀ (i : J) x, ‖T i x‖ = ‖x‖ := fun i x =>
    ((V i).subtypeₗᵢ.norm_map _).trans (LinearIsometryEquiv.norm_map _ x)
  have := hσ.1
  obtain ⟨k, hk⟩ := exists_ne (0 : K)
  let t : J → σ.intertwiners π := fun i => ⟨T i, hT i⟩
  have hli : LinearIndependent ℂ t := by
    rw [linearIndependent_iff']
    intro u g hg j hj
    have h1 := congrArg (fun S : σ.intertwiners π => ⟪T j k, (S : K →L[ℂ] H) k⟫_ℂ) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, FunLike.coe_sum,
      Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, inner_sum,
      inner_smul_right, ZeroMemClass.coe_zero, zero_apply, inner_zero_right, t] at h1
    rw [Finset.sum_eq_single j] at h1
    · rw [inner_self_eq_norm_sq_to_K, hTnorm] at h1
      have : (‖k‖ : ℂ) ^ 2 ≠ 0 := by simpa using hk
      exact (mul_eq_zero.1 h1).resolve_right this
    · intro i _ hij
      have hne : (i : ι) ≠ j := fun h => hij (Subtype.ext h)
      have := hV hne.symm (⟨T j k, hTV j k⟩ : V j) (⟨T i k, hTV i k⟩ : V i)
      have h0 : ⟪T j k, T i k⟫_ℂ = 0 := this
      rw [h0, mul_zero]
    · intro hj'; exact absurd hj hj'
  have : Finite J := hli.finite
  exact Set.toFinite J
end GroundTheory.Automorphic.UnitaryRep
