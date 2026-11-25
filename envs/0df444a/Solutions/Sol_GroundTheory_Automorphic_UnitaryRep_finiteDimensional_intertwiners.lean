-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.finiteDimensional_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:48.744817+00:00
-- url     : https://prove2.me/submissions/880d0af1-a6d0-498c-9841-9811d7f81bcc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isSymmetric_absSqOp
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_absSqOp_apply_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_absSqOp_of_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_exists_integrated_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsIrreducible_exists_eq_smul_one
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_adjoint_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isInvariant_ker
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
    {σ : UnitaryRep G K} (hσ : σ.IsIrreducible) :
    FiniteDimensional ℂ (σ.intertwiners π) := by
  classical
  by_cases h0 : σ.intertwiners π = ⊥
  · rw [h0]; infer_instance
  obtain ⟨T₀, hT₀, hT₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0

  obtain ⟨c, hc⟩ := hσ.exists_eq_smul_one
    (comp_mem_intertwiners (adjoint_mem_intertwiners hT₀) hT₀)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hT₀ne
    refine ContinuousLinearMap.ext fun k => ?_
    have h := congrArg (fun A : K →L[ℂ] K => ⟪k, A k⟫_ℂ) hc
    simp only [comp_apply, adjoint_inner_right, zero_smul, zero_apply, inner_zero_right,
      inner_self_eq_zero] at h
    simpa using h
  have := hσ.1
  obtain ⟨k, hk⟩ := exists_ne (0 : K)
  obtain ⟨f, hf⟩ := exists_integrated_ne_zero σ μ hk
  set A := σ.absSqOp μ (ccToL1 μ f) with hA
  set B := π.absSqOp μ (ccToL1 μ f) with hB
  have hBc : IsCompactOperator B := IsCompactOperator.absSqOp π μ (hcpt f)
  have hint : ∀ T ∈ σ.intertwiners π, T ∘L A = B ∘L T := fun T hT =>
    comp_absSqOp_of_mem_intertwiners hT _

  have hAeq' : adjoint T₀ ∘L (B ∘L T₀) = c • A := by
    rw [← hint T₀ hT₀, ← ContinuousLinearMap.comp_assoc, hc, smul_comp]
    congr 1
  have hAeq : A = c⁻¹ • (adjoint T₀ ∘L (B ∘L T₀)) := by
    rw [hAeq', smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hAc : IsCompactOperator A := by
    rw [hAeq]
    exact ((hBc.comp_clm T₀).clm_comp (adjoint T₀)).smul c⁻¹
  have hAs : (A : K →ₗ[ℂ] K).IsSymmetric := σ.isSymmetric_absSqOp μ _
  have hA0 : A ≠ 0 := fun h => absSqOp_apply_ne_zero σ μ hf (by rw [← hA, h, zero_apply])
  obtain ⟨lam, hlam, hlam0⟩ : ∃ lam, HasEigenvalue (A : K →ₗ[ℂ] K) lam ∧ lam ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hA0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hAc hAs).1 h')
  obtain ⟨e, he1, he0⟩ := hlam.exists_hasEigenvector
  have he : A e = lam • e := by simpa using mem_eigenspace_iff.1 he1
  set E := eigenspace (B : H →ₗ[ℂ] H) lam with hE
  have hEfin : FiniteDimensional ℂ E :=
    ContinuousLinearMap.finite_dimensional_eigenspace hBc lam hlam0
  have hmem : ∀ T : σ.intertwiners π, (T : K →L[ℂ] H) e ∈ E := fun T => by
    rw [hE, mem_eigenspace_iff, ContinuousLinearMap.coe_coe]
    have := congrArg (fun S : K →L[ℂ] H => S e) (hint T T.2)
    simp only [comp_apply, he, map_smul] at this
    exact this.symm
  let Φ : σ.intertwiners π →ₗ[ℂ] E :=
    { toFun := fun T => ⟨(T : K →L[ℂ] H) e, hmem T⟩
      map_add' := fun S T => Subtype.ext (by simp)
      map_smul' := fun a T => Subtype.ext (by simp) }
  refine Module.Finite.of_injective Φ fun S T hST => ?_
  rw [← sub_eq_zero]
  have h1 : ((S - T : σ.intertwiners π) : K →L[ℂ] H) e = 0 := by
    have := congrArg Subtype.val hST
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    simp [this]
  set D := S - T with hD
  have hker : LinearMap.ker ((D : K →L[ℂ] H) : K →ₗ[ℂ] H) = ⊤ := by
    rcases hσ.2 _ (D : K →L[ℂ] H).isClosed_ker (isInvariant_ker D.2) with h | h
    · exfalso
      have : e ∈ LinearMap.ker ((D : K →L[ℂ] H) : K →ₗ[ℂ] H) := by
        simpa using h1
      rw [h, Submodule.mem_bot] at this
      exact he0 this
    · exact h
  refine Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  have : x ∈ LinearMap.ker ((D : K →L[ℂ] H) : K →ₗ[ℂ] H) := by rw [hker]; trivial
  simpa using this
end GroundTheory.Automorphic.UnitaryRep
