-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.avg_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:03.931856+00:00
-- url     : https://prove2.me/submissions/36be94d9-078c-48e6-9a53-50d3ff554d55

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_single
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_fixed
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeTransfer
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}
namespace GlobalTheory.CompanionTheory.HeckeTransfer
theorem _root_.solution {E : H →L[ℂ] H} (hA : IsAvg σ K E) (hv : ∀ k ∈ K, σ k v = v) (g : G) (T : Hk K)
    (S : Finset (G ⧸ K)) (hS : (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K))
    (hT : (T : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) :
    E (σ g v) = phi K σ v ((((S.card : ℂ)⁻¹ • T : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  have hcard : (S.card : ℂ) ≠ 0 := by
    have hmem : (g : G ⧸ K) ∈ S := by
      have : (g : G ⧸ K) ∈ (↑S : Set (G ⧸ K)) := by
        rw [hS]
        exact MulAction.mem_orbit_self _
      exact Finset.mem_coe.1 this
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨_, hmem⟩).ne'
  have hterm : ∀ y ∈ S, E (phi K σ v (Finsupp.single y 1)) = E (σ g v) := by
    intro y hy
    have hy' : y ∈ MulAction.orbit K (g : G ⧸ K) := by
      rw [← hS]
      exact hy
    obtain ⟨k, rfl⟩ := hy'
    show E (phi K σ v (Finsupp.single (((k : G) * g : G) : G ⧸ K) 1)) = E (σ g v)
    rw [phi_single hv, one_smul, map_mul,
      ContinuousLinearMap.mul_apply, hA.2.2 _ _ k.2]
  have hfix := phi_fixed hv (((S.card : ℂ)⁻¹ • T : Hk K))
  rw [← hA.2.1 _ hfix, Subalgebra.coe_smul, LinearMap.smul_apply, hT]
  simp only [map_smul, map_sum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]
end GlobalTheory.CompanionTheory.HeckeTransfer
