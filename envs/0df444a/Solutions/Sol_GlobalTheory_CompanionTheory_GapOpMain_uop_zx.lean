-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.uop_zx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:16:02.828914+00:00
-- url     : https://prove2.me/submissions/60ab3b63-a768-40ad-b471-ca37fdda3ec3

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_uop_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_finsum_conv
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_t_zx
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_sum_hyperplanes_complement_flags
import Theorems.Thm_GlobalTheory_T_card_functionals_vanishing_subspace


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
theorem _root_.solution (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    (lam : ℕ → ℂ)
    (hl : ∀ j ≤ n + 1, ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : Module.finrank k M + j = n + 1), v M = lam j • v ⊤)
    {j : ℕ} (hj : j ≤ n) :
    uop ρ t gam (zx v (e0 k n) j) = (Fintype.card k : ℂ) ^ j • (lam (j + 1) • v ⊤ - zx v (e0 k n) (j + 1)) := by
  have hXne : ∀ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1), a ≠ 0 := by
    intro a ha h0
    rw [h0] at ha
    simp at ha
  have hfs : ∑ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + (j + 1) = n + 1), v M = lam (j + 1) • v ⊤ := by
    rw [← hl (j + 1) (by omega), finsum_conv]
  have hswap : ∀ (a : Fin (n + 1) → k) (M : Submodule k (Fin (n + 1) → k)),
      a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1) ∧
        M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) =>
          (∀ x ∈ M, a ⬝ᵥ x = 0) ∧ Module.finrank k M + (j + 1) = n + 1) ↔
      a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0) ∧
        M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + (j + 1) = n + 1) := by
    intro a M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hterm : ∀ M ∈ Finset.univ.filter
      (fun M : Submodule k (Fin (n + 1) → k) => Module.finrank k M + (j + 1) = n + 1),
      (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card • v M =
      (if e0 k n ∈ M then (0 : ℂ) else (Fintype.card k : ℂ) ^ j) • v M := by
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    by_cases he : e0 k n ∈ M
    · have h0 : (Finset.univ.filter
          (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro a _ ha
        have h3 := ha.2 _ he
        rw [ha.1] at h3
        exact one_ne_zero h3
      rw [h0, if_pos he, zero_smul, zero_smul]
    · rw [if_neg he, ← Nat.cast_smul_eq_nsmul ℂ, GlobalTheory.T.card_functionals_vanishing_subspace k n j M he hM, Nat.cast_pow]
  rw [uop_apply]
  unfold ux
  rw [t_zx hD j]
  refine (Finset.sum_congr rfl (fun a ha => sum_hyperplanes_complement_flags hD hc (hXne a ha) j)).trans ?_
  rw [Finset.sum_comm' hswap]
  simp only [Finset.sum_const]
  refine (Finset.sum_congr rfl hterm).trans ?_
  rw [← hfs]
  unfold zx
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, smul_sub, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h1 : Module.finrank k M + (j + 1) = n + 1 <;> by_cases h2 : e0 k n ∈ M <;> simp [h1, h2]
end GlobalTheory.CompanionTheory.GapOpMain
