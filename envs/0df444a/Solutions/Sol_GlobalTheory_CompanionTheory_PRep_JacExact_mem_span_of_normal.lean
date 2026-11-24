-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PRep.JacExact.mem_span_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:09:42.545719+00:00
-- url     : https://prove2.me/submissions/00d99a1f-5bb6-4a68-a70e-aafe0c361d73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_avg_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_avg_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.JacExact
variable {L V W : Type} [Group L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.PRep.JacExact
theorem _root_.solution (ρ : Representation ℂ L V) (σ : Representation ℂ L W) (χ : L →* ℂˣ)
    (M : Subgroup L) [M.Normal] [Finite (L ⧸ M)] (hχ : M ≤ χ.ker)
    (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (hfi : ∀ g v, f (ρ g v) = σ g (f v))
    (v : V) (hfv : f v ∈ Submodule.span ℂ
      {y | ∃ (n : L) (w : W), (∀ m ∈ M, σ m w = w) ∧ y = σ n w - ((χ n : ℂˣ) : ℂ) • w}) :
    v ∈ Submodule.span ℂ {y | ∃ (n : L) (u : V), y = ρ n u - ((χ n : ℂˣ) : ℂ) • u} := by
  haveI := Fintype.ofFinite (L ⧸ M)
  set S := Submodule.span ℂ {y | ∃ (n : L) (u : V), y = ρ n u - ((χ n : ℂˣ) : ℂ) • u} with hS
  have h1 : f (avg ρ χ M v) = avg σ χ M (f v) := by
    simp only [avg_apply, map_sum, map_smul, hfi]
  have h2 : avg σ χ M (f v) = 0 := by
    have hle : Submodule.span ℂ
        {y | ∃ (n : L) (w : W), (∀ m ∈ M, σ m w = w) ∧ y = σ n w - ((χ n : ℂˣ) : ℂ) • w}
        ≤ LinearMap.ker (avg σ χ M) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨n, w, hw, rfl⟩
      show avg σ χ M _ = 0
      rw [map_sub, avg_translate σ χ M hχ w hw, map_smul, sub_self]
    exact hle hfv
  have h3 : avg ρ χ M v = 0 := hf (by rw [h1, h2, map_zero])
  have h4 : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) • v - avg ρ χ M v ∈ S := by
    have : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) • v - avg ρ χ M v
        = ∑ q : L ⧸ M, (-(((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
            (ρ (Quotient.out q) v - ((χ (Quotient.out q) : ℂˣ) : ℂ) • v) := by
      have hq : ∀ q : L ⧸ M, (-(((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
            (ρ (Quotient.out q) v - ((χ (Quotient.out q) : ℂˣ) : ℂ) • v)
          = v - (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • ρ (Quotient.out q) v := by
        intro q
        rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
          neg_smul, one_smul]
        abel
      rw [Finset.sum_congr rfl (fun q _ => hq q), Finset.sum_sub_distrib, avg_apply]
      simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
  rw [h3, sub_zero] at h4
  have hc : ((Fintype.card (L ⧸ M) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (Submodule.smul_mem_iff _ hc).1 h4
end GlobalTheory.CompanionTheory.PRep.JacExact
