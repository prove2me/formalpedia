-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.t_zx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:27.527479+00:00
-- url     : https://prove2.me/submissions/0c7a9d07-2b38-4ae9-8ba2-635c9a2b5efb

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_first_basis_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_riemannRochSpace_iff_regularAt_everywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
namespace GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
private theorem sup_H0_eq_top_of_e0_mem {K : Type} [Field K] {m : ℕ} (M : Submodule K (Fin (m + 1) → K)) (h : e0 K m ∈ M) :
    M ⊔ H0 K m = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • e0 K m + (x - x 0 • e0 K m) := (add_sub_cancel _ _).symm
  rw [hx]
  refine Submodule.add_mem_sup (M.smul_mem _ h) ?_
  rw [mem_riemannRochSpace_iff_regularAt_everywhere]
  simp [e0]
private theorem span_e0_inf_H0_eq_bot {K : Type} [Field K] {m : ℕ} : Submodule.span K {e0 K m} ⊓ H0 K m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, Submodule.mem_span_singleton, mem_riemannRochSpace_iff_regularAt_everywhere] at hx
  obtain ⟨⟨c, rfl⟩, h0⟩ := hx
  have hc : c = 0 := by simpa [e0] using h0
  rw [hc, zero_smul]
  exact Submodule.zero_mem _
private theorem finrank_H0 {K : Type} [Field K] {m : ℕ} : Module.finrank K ↥(H0 K m) = m := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {e0 K m}) (H0 K m)
  rw [sup_H0_eq_top_of_e0_mem _ (Submodule.mem_span_singleton_self _), span_e0_inf_H0_eq_bot,
    finrank_span_singleton first_basis_ne_zero] at h1
  simp at h1
  omega
private theorem finrank_inf_H0_add_one_of_e0_mem {K : Type} [Field K] {m : ℕ} (M : Submodule K (Fin (m + 1) → K)) (h : e0 K m ∈ M) :
    Module.finrank K ↥(M ⊓ H0 K m) + 1 = Module.finrank K M := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq M (H0 K m)
  rw [sup_H0_eq_top_of_e0_mem M h, finrank_H0] at h1
  simp at h1
  omega
private theorem finrank_sup_span_e0_of_le_H0 {K : Type} [Field K] {m : ℕ} (N : Submodule K (Fin (m + 1) → K)) (hN : N ≤ H0 K m) :
    Module.finrank K ↥(N ⊔ Submodule.span K {e0 K m}) = Module.finrank K N + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq N (Submodule.span K {e0 K m})
  have h2 : N ⊓ Submodule.span K {e0 K m} = ⊥ := by
    refine eq_bot_iff.mpr (le_trans ?_ (span_e0_inf_H0_eq_bot (K := K) (m := m)).le)
    rw [inf_comm]
    exact inf_le_inf_left _ hN
  rw [h2, finrank_span_singleton first_basis_ne_zero] at h1
  simp at h1
  omega
end GlobalTheory.CompanionTheory.GapOpMain
end
end

set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
namespace GlobalTheory.CompanionTheory.GapOpMain
theorem _root_.solution (hD : LatData k n B red ρ t v) (j : ℕ) :
    t (zx v (e0 k n) j) = ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => M ≤ H0 k n ∧ Module.finrank k M + (j + 1) = n + 1), v M := by
  unfold zx
  rw [map_sum]
  refine Finset.sum_nbij' (fun M => M ⊓ H0 k n) (fun N => N ⊔ Submodule.span k {e0 k n}) ?_ ?_ ?_ ?_ ?_
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    refine ⟨inf_le_right, ?_⟩
    have h3 := finrank_inf_H0_add_one_of_e0_mem M hM.1
    omega
  · intro N hN
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hN ⊢
    refine ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), ?_⟩
    have h3 := finrank_sup_span_e0_of_le_H0 N hN.1
    omega
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    apply le_antisymm
    · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hM.1)
    · intro x hx
      have hx' : x = (x - x 0 • e0 k n) + x 0 • e0 k n := (sub_add_cancel _ _).symm
      rw [hx']
      refine Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨M.sub_mem hx (M.smul_mem _ hM.1), ?_⟩)
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      rw [mem_riemannRochSpace_iff_regularAt_everywhere]
      simp [e0]
  · intro N hN
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hN
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hy0 : y 0 = 0 := (mem_riemannRochSpace_iff_regularAt_everywhere y).mp (hN.1 hy)
      rw [mem_riemannRochSpace_iff_regularAt_everywhere] at hx2
      have hc : c = 0 := by simpa [e0, hy0] using hx2
      rw [hc, zero_smul, add_zero]
      exact hy
    · exact le_inf le_sup_left hN.1
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    exact hD.step M hM.1
end GlobalTheory.CompanionTheory.GapOpMain
