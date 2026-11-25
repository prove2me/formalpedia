-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.orthogonal_iSup_iInf_eigenspaces_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:00.698616+00:00
-- url     : https://prove2.me/submissions/40fd63cd-c50f-4cf8-a9af-5a8b3695e853

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.CompactSelfAdjoint
open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable [CompleteSpace E]
namespace GroundTheory.Automorphic.CompactSelfAdjoint
theorem _root_.solution {ι : Type*} (T : ι → E →L[𝕜] E)
    (hT : ∀ i, IsCompactOperator (T i)) (hS : ∀ i, (T i : E →ₗ[𝕜] E).IsSymmetric)
    (hC : ∀ i j, Commute (T i) (T j)) :
    (⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i : E →ₗ[𝕜] E) (χ i))ᗮ = ⊥ := by
  set M := ⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i : E →ₗ[𝕜] E) (χ i) with hMdef
  have hcomm : ∀ i j v, T j (T i v) = T i (T j v) := fun i j v => by
    simpa using congrArg (fun g : E →L[𝕜] E => g v) (hC j i)
  have hJinv : ∀ (χ : ι → 𝕜) i, ∀ v ∈ ⨅ j, eigenspace (T j : E →ₗ[𝕜] E) (χ j),
      T i v ∈ ⨅ j, eigenspace (T j : E →ₗ[𝕜] E) (χ j) := by
    intro χ i v hv
    rw [Submodule.mem_iInf] at hv ⊢
    intro j
    have h := mem_eigenspace_iff.1 (hv j)
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hcomm, h, map_smul]
  have hMinv : ∀ i, ∀ v ∈ M, T i v ∈ M := by
    intro i v hv
    refine Submodule.iSup_induction _ (motive := fun v => T i v ∈ M) hv
      (fun χ x hx => Submodule.mem_iSup_of_mem χ (hJinv χ i x hx)) (by simp) ?_
    intro x y hx hy
    simpa only [map_add] using add_mem hx hy
  have hNinv : ∀ i, ∀ v ∈ Mᗮ, T i v ∈ Mᗮ := by
    intro i v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    have h := hS i u v
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h]
    exact hv _ (hMinv i u hu)
  by_contra hne
  suffices h : ∃ w ∈ Mᗮ, w ≠ 0 ∧ w ∈ M by
    obtain ⟨w, hwN, hw0, hwM⟩ := h
    have hw : w ∈ M ⊓ Mᗮ := ⟨hwM, hwN⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hw
    exact hw0 hw
  by_cases hz : ∀ i, ∀ v ∈ Mᗮ, T i v = 0
  · obtain ⟨w, hwN, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨w, hwN, hw0, Submodule.mem_iSup_of_mem (fun _ => 0) ?_⟩
    rw [Submodule.mem_iInf]
    intro i
    rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hz i w hwN, zero_smul]
  push Not at hz
  obtain ⟨k, v, hvN, hvk⟩ := hz
  let S : Mᗮ →L[𝕜] Mᗮ := (T k).restrict (hNinv k)
  have hS_compact : IsCompactOperator S := (hT k).restrict' (hNinv k)
  have hS_symm : (S : Mᗮ →ₗ[𝕜] Mᗮ).IsSymmetric := (hS k).restrict_invariant (hNinv k)
  have hS0 : S ≠ 0 := by
    intro h
    apply hvk
    have := congrArg (fun g : Mᗮ →L[𝕜] Mᗮ => ((g ⟨v, hvN⟩ : Mᗮ) : E)) h
    simpa [S] using this
  obtain ⟨μ, hμ, hμ0⟩ : ∃ μ, HasEigenvalue (S : Mᗮ →ₗ[𝕜] Mᗮ) μ ∧ μ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hS0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact
      hS_symm).1 h')
  obtain ⟨u, hu1, hu2⟩ := hμ.exists_hasEigenvector
  have huk : T k u = μ • (u : E) := by
    have := congrArg Subtype.val (mem_eigenspace_iff.1 hu1)
    simpa [S] using this
  set U : Submodule 𝕜 E := eigenspace (T k : E →ₗ[𝕜] E) μ ⊓ Mᗮ with hUdef
  have : FiniteDimensional 𝕜 (eigenspace (T k : E →ₗ[𝕜] E) μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace (hT k) μ hμ0
  have : FiniteDimensional 𝕜 U := Submodule.finiteDimensional_of_le inf_le_left
  have hUinv : ∀ i, ∀ x ∈ U, (T i : E →ₗ[𝕜] E) x ∈ U := by
    intro i x hx
    refine ⟨?_, hNinv i x hx.2⟩
    have h := mem_eigenspace_iff.1 hx.1
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [SetLike.mem_coe, mem_eigenspace_iff, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe, hcomm, h, map_smul]
  let R : ι → Module.End 𝕜 U := fun i => (T i : E →ₗ[𝕜] E).restrict (hUinv i)
  have hRs : ∀ i, (R i).IsSymmetric := fun i => (hS i).restrict_invariant (hUinv i)
  have hRc : Pairwise (Function.onFun Commute R) := by
    intro i j _
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [R, LinearMap.restrict_apply, hcomm]
  have huU : (u : E) ∈ U := ⟨mem_eigenspace_iff.2 (by simpa using huk), u.2⟩
  have hUne : (⊤ : Submodule 𝕜 U) ≠ ⊥ := by
    intro h
    have : (⟨u, huU⟩ : U) ∈ (⊥ : Submodule 𝕜 U) := h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at this
    exact hu2 (Subtype.ext (by simpa using congrArg Subtype.val this))
  rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hRs hRc, ne_eq, iSup_eq_bot] at hUne
  push Not at hUne
  obtain ⟨χ, hχ⟩ := hUne
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  refine ⟨w, w.2.2, fun h => hw0 (Subtype.ext h), Submodule.mem_iSup_of_mem χ ?_⟩
  rw [Submodule.mem_iInf] at hw ⊢
  intro i
  have := congrArg Subtype.val (mem_eigenspace_iff.1 (hw i))
  rw [mem_eigenspace_iff]
  simpa [R, LinearMap.restrict_apply] using this
end GroundTheory.Automorphic.CompactSelfAdjoint
