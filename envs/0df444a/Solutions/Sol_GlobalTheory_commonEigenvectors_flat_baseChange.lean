-- Prove2me | solution 1 for GlobalTheory.commonEigenvectors_flat_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:33.970237+00:00
-- url     : https://prove2.me/submissions/e59b3f70-95a8-4506-8176-d473dccfe64a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange
import Theorems.Thm_GlobalTheory_EigFlat_exact_iff
import Theorems.Thm_GlobalTheory_EigFlat_injective_iff
import Theorems.Thm_GlobalTheory_EigFlat_exists_matrix
import Theorems.Thm_GlobalTheory_EigFlat_eig_iff
import Theorems.Thm_GlobalTheory_EigFlat_sum_eq
import Theorems.Thm_GlobalTheory_EigFlat_eig_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open EigFlat
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] (I : Type) (g m : ℕ) (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A), (∀ (R : Type) [CommRing R] [Algebra A R] [Module.FaithfullyFlat A R] [IsNoetherianRing A] (u : Fin m → Fin g → A), (∀ k i, u k ᵥ* M i = ρ i • u k) → (∀ w : Fin g → R, (∀ i, w ᵥ* (M i).map (algebraMap A R) = algebraMap A R (ρ i) • w) → ∃! cf : Fin m → R, w = ∑ k, cf k • (fun j => algebraMap A R (u k j))) → ∀ (S : Type) [CommRing S] [Algebra A S] [Module.Flat A S] (w : Fin g → S), (∀ i, w ᵥ* (M i).map (algebraMap A S) = algebraMap A S (ρ i) • w) → ∃! cf : Fin m → S, w = ∑ k, cf k • (fun j => algebraMap A S (u k j))) ∧ ∀ [IsDomain A] [IsPrincipalIdealRing A], ∃ (n : ℕ) (u : Fin n → Fin g → A), (∀ k i, u k ᵥ* M i = ρ i • u k) ∧ ∀ w : Fin g → A, (∀ i, w ᵥ* M i = ρ i • w) → ∃! cf : Fin n → A, w = ∑ k, cf k • u k := by
  intro A _ I g m M ρ
  constructor
  · intro R _ _ _ _ u hu hR S _ _ _ w hw
    obtain ⟨n, H, hH⟩ := exists_matrix (fun i => M i - ρ i • (1 : Matrix (Fin g) (Fin g) A))
    simp only [eig_iff] at hH
    simp only [sum_eq] at hR ⊢
    have hexR : Function.Exact (LinearMap.lTensor R (Matrix.of u).vecMulLinear)
        (LinearMap.lTensor R H.vecMulLinear) := by
      rw [exact_iff]
      intro v
      rw [hH]
      constructor
      · intro hv
        obtain ⟨cf, hcf, -⟩ := hR v hv
        exact ⟨cf, hcf.symm⟩
      · rintro ⟨cf, rfl⟩ i
        exact eig_map u (M i) (ρ i) (fun k => hu k i) R cf
    have hinjR : Function.Injective (LinearMap.lTensor R (Matrix.of u).vecMulLinear) := by
      rw [injective_iff]
      intro c₁ c₂ hc
      exact (hR _ (fun i => eig_map u (M i) (ρ i) (fun k => hu k i) R c₁)).unique rfl hc
    have hex := (Module.FaithfullyFlat.lTensor_exact_iff_exact A R _ _).mp hexR
    have hinj := (Module.FaithfullyFlat.lTensor_injective_iff_injective A R _).mp hinjR
    have hexS := (exact_iff _ _ S).mp (Module.Flat.lTensor_exact S hex)
    have hinjS := (injective_iff _ S).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ hinj)
    obtain ⟨cf, hcf⟩ := (hexS w).mp ((hH S w).mpr hw)
    exact ⟨cf, hcf.symm, fun c' hc' => hinjS (hc'.symm.trans hcf.symm)⟩
  · intro _ _
    let N : Submodule A (Fin g → A) :=
      { carrier := {w | ∀ i, w ᵥ* M i = ρ i • w}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy i
          rw [Matrix.add_vecMul, hx i, hy i, smul_add]
        smul_mem' := by
          intro r x hx i
          rw [Matrix.smul_vecMul, hx i, smul_comm] }
    obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun A (Fin g)) N
    refine ⟨n, fun k => (b k : Fin g → A), fun k i => (b k).2 i, fun w hw => ?_⟩
    have key : ∀ cf : Fin n → A, (∑ k, cf k • (b k : Fin g → A))
        = ((b.equivFun.symm cf : N) : Fin g → A) := by
      intro cf
      rw [Module.Basis.equivFun_symm_apply]
      simp
    refine ⟨b.equivFun ⟨w, hw⟩, ?_, fun cf hcf => ?_⟩
    · beta_reduce
      rw [key]; simp
    · beta_reduce at hcf
      rw [key] at hcf
      have : (⟨w, hw⟩ : N) = b.equivFun.symm cf := Subtype.ext hcf
      exact ((congrArg b.equivFun this).trans (b.equivFun.apply_symm_apply cf)).symm
end GlobalTheory
