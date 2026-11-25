-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.exists_prodExp_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:24.114257+00:00
-- url     : https://prove2.me/submissions/b7bda9ee-02c3-4300-af48-9e0d09428197

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_prodExpVal_zero
import Theorems.Thm_GroundTheory_Automorphic_contDiff_prodExpVal
import Theorems.Thm_GroundTheory_Automorphic_contDiffOn_prodExpCoord
import Theorems.Thm_GroundTheory_Automorphic_isOpen_prodExpCoord_domain
import Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_prodExpCoord_zero
import Theorems.Thm_GroundTheory_Automorphic_contDiffAt_prodExpCoord_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ (S T : Set (Fin d → ℝ)) (ψ : (Fin d → ℝ) → (Fin d → ℝ)), IsOpen S ∧ IsOpen T ∧
      (0 : Fin d → ℝ) ∈ S ∧ MapsTo (prodExpCoord b) S T ∧ MapsTo ψ T S ∧
      (∀ z ∈ S, ψ (prodExpCoord b z) = z) ∧ (∀ w ∈ T, prodExpCoord b (ψ w) = w) ∧
      ContDiffOn ℝ ∞ ψ T ∧ (∀ z ∈ S, prodExpVal (fun i => (b i : 𝔸)) z ∈ h.nhdOne) := by
  set Φ := prodExpCoord b with hΦdef
  set U := {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} with hUdef
  have hU : IsOpen U := isOpen_prodExpCoord_domain b
  have hΦU : ContDiffOn ℝ ∞ Φ U := contDiffOn_prodExpCoord b
  let F₀ := (contDiffAt_prodExpCoord_zero b).toOpenPartialHomeomorph Φ
    (hasFDerivAt_prodExpCoord_zero b) (by simp)
  have hcont : ContinuousOn (fderiv ℝ Φ) U := hΦU.continuousOn_fderiv_of_isOpen hU (by simp)
  have hS₁ : IsOpen (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) :=
    hcont.isOpen_inter_preimage hU Units.isOpen
  have hN : IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} :=
    h.isOpen_nhdOne.preimage (contDiff_prodExpVal _).continuous
  set S₂ := (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) ∩
    {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} with hS₂def
  have hS₂ : IsOpen S₂ := hS₁.inter hN
  let F := F₀.restrOpen S₂ hS₂
  have hF : (F : (Fin d → ℝ) → (Fin d → ℝ)) = Φ := rfl
  refine ⟨F.source, F.target, F.symm, F.open_source, F.open_target, ?_, ?_, F.mapsTo_symm,
    fun z hz => F.left_inv hz, fun w hw => F.right_inv hw, ?_, ?_⟩
  · refine ⟨(contDiffAt_prodExpCoord_zero b).mem_toOpenPartialHomeomorph_source _ _, ?_⟩
    have h0 : prodExpVal (fun i => (b i : 𝔸)) 0 = 1 := prodExpVal_zero _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ (expPartialHomeomorph ℝ 𝔸).target
      rw [h0]; exact one_mem_expPartialHomeomorph_target ℝ 𝔸
    · show IsUnit (fderiv ℝ Φ 0)
      rw [(hasFDerivAt_prodExpCoord_zero b).fderiv]
      exact isUnit_one
    · show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ h.nhdOne
      rw [h0]; exact h.one_mem_nhdOne
  · intro z hz; rw [← hF]; exact F.map_source hz
  · intro w hw
    apply ContDiffAt.contDiffWithinAt
    have hz : F.symm w ∈ F.source := F.map_target hw
    have hzS : F.symm w ∈ S₂ := hz.2
    have hu : IsUnit (fderiv ℝ Φ (F.symm w)) := hzS.1.2
    have hΦz : ContDiffAt ℝ ∞ Φ (F.symm w) := hΦU.contDiffAt (hU.mem_nhds hzS.1.1)
    have hdiff : HasFDerivAt Φ (fderiv ℝ Φ (F.symm w)) (F.symm w) :=
      (hΦz.differentiableAt (by simp)).hasFDerivAt
    have key : ((ContinuousLinearEquiv.unitsEquiv ℝ (Fin d → ℝ) hu.unit :
        (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) =
        fderiv ℝ Φ (F.symm w) := by
      ext x; simp
    exact F.contDiffAt_symm hw (key ▸ hdiff) hΦz
  · intro z hz; exact hz.2.2
end GroundTheory.Automorphic.IsExpLieAlgebra
