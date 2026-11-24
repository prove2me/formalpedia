-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:44.020457+00:00
-- url     : https://prove2.me/submissions/7353e8d4-7773-43d0-8452-160889c5d984

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_zx_map
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_finsum_conv
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_card_ne_zero_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_exists_GL_first_basis_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_gmap_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
namespace GlobalTheory.CompanionTheory.GapOpMain
theorem _root_.solution (hD : LatData k n B red ρ t v) (lam : ℕ → ℂ)
    (hl : ∀ j ≤ n + 1, ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : Module.finrank k M + j = n + 1), v M = lam j • v ⊤)
    {j : ℕ} (hj : j ≤ n + 1) :
    ((Fintype.card k : ℂ) ^ (n + 1) - 1) * B (zx v (e0 k n) j) (v ⊤) =
      ((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) * lam j * B (v ⊤) (v ⊤) := by
  have hconst : ∀ x : Fin (n + 1) → k, x ≠ 0 → B (zx v x j) (v ⊤) = B (zx v (e0 k n) j) (v ⊤) := by
    intro x hx
    obtain ⟨g, hg⟩ := exists_GL_first_basis_eq x hx
    obtain ⟨γ, rfl⟩ := hD.surj g
    have htop : ρ γ (v ⊤) = v ⊤ := by rw [hD.equiv, gmap_top]
    calc B (zx v x j) (v ⊤) = B (ρ γ (zx v (e0 k n) j)) (ρ γ (v ⊤)) := by rw [htop, zx_map hD, hg]
      _ = B (zx v (e0 k n) j) (v ⊤) := hD.unit γ _ _
  have hfs : ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + j = n + 1), v M = lam j • v ⊤ := by
    rw [← hl j hj, finsum_conv]
  have hswap : ∀ (x : Fin (n + 1) → k) (M : Submodule k (Fin (n + 1) → k)),
      x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ (⊤ : Submodule k (Fin (n + 1) → k))) ∧
        M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => x ∈ M ∧ Module.finrank k M + j = n + 1) ↔
      x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ M) ∧
        M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + j = n + 1) := by
    intro x M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_top, and_true]
    tauto
  have hsum : ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ (⊤ : Submodule k (Fin (n + 1) → k))),
      zx v x j = (((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) * lam j) • v ⊤ := by
    unfold zx
    rw [Finset.sum_comm' hswap]
    simp_rw [Finset.sum_const]
    rw [Finset.sum_congr rfl (g := fun M => ((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) • v M)]
    · rw [← Finset.smul_sum, hfs, smul_smul]
    · intro M hM
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      rw [← Nat.cast_smul_eq_nsmul ℂ, card_ne_zero_mem M, show Module.finrank k M = n + 1 - j by omega]
  have hcard := card_ne_zero_mem (k := k) (n := n) ⊤
  rw [finrank_top, Module.finrank_fin_fun] at hcard
  have e1 : ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ (⊤ : Submodule k (Fin (n + 1) → k))),
      B (zx v x j) (v ⊤) = ((Fintype.card k : ℂ) ^ (n + 1) - 1) * B (zx v (e0 k n) j) (v ⊤) := by
    rw [Finset.sum_congr rfl (fun x hx => hconst x (Finset.mem_filter.mp hx).2.1), Finset.sum_const,
      nsmul_eq_mul, hcard]
  have e2 : ∑ x ∈ Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ (⊤ : Submodule k (Fin (n + 1) → k))),
      B (zx v x j) (v ⊤) = ((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) * lam j * B (v ⊤) (v ⊤) := by
    rw [← LinearMap.sum_apply, ← map_sum, hsum, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← e1, e2]
end GlobalTheory.CompanionTheory.GapOpMain
