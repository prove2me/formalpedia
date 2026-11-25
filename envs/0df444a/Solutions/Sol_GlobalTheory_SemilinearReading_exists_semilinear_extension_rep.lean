-- Prove2me | solution 1 for GlobalTheory.SemilinearReading.exists_semilinear_extension_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:49.458696+00:00
-- url     : https://prove2.me/submissions/bf1283a4-cf48-4f43-b807-f7fe93298804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSemilinearExtensionOfFormWithTransportedRe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.SemilinearReading
namespace GlobalTheory.SemilinearReading
theorem _root_.solution :
    ∀ {K LL Cs W G : Type} [Field K] [Field LL] [Algebra K LL] [AddCommGroup Cs] [Module K Cs] [AddCommGroup W] [Module ℂ W] [Group G] {n m : ℕ} (σ₀ : K →+* ℂ) (σ : LL →+* ℂ), (∀ a, σ (algebraMap K LL a) = σ₀ a) → ∀ (cu : Cs →ₗ[K] (Fin n → LL)) (b : Fin m → Cs), Submodule.span K (Set.range b) = ⊤ → LinearIndependent LL (fun k => cu (b k)) → Submodule.span LL (Set.range fun k => cu (b k)) = ⊤ → ∀ (R : Cs →ₛₗ[σ₀] W), LinearIndependent ℂ (fun k => R (b k)) → Submodule.span ℂ (Set.range R) = ⊤ → ∀ (ρL : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))), ∃ (f : (Fin n → LL) →ₛₗ[σ] W) (ρ : Representation ℂ G W), (∀ F, f (cu F) = R F) ∧ (∀ g w, ρ g (f w) = f (ρL g w)) ∧ (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  intro K LL Cs W G _ _ _ _ _ _ _ _ n m σ₀ σ hσ cu b hbs hbi hbt R hR hRs ρL
  classical
  let B : Basis (Fin m) LL (Fin n → LL) := Basis.mk hbi hbt.ge
  have hB : ∀ k, B k = cu (b k) := fun k => Basis.mk_apply _ _ _
  let f : (Fin n → LL) →ₛₗ[σ] W :=
    { toFun := fun w => ∑ k, σ (B.repr w k) • R (b k)
      map_add' := by
        intro x y
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp [Finset.smul_sum, mul_smul] }
  have hfB : ∀ k, f (B k) = R (b k) := by
    intro k
    change ∑ j, σ (B.repr (B k) j) • R (b j) = _
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj.symm]
    · simp
  have hcu : ∀ F, f (cu F) = R F := by
    intro F
    have hF : F ∈ Submodule.span K (Set.range b) := by rw [hbs]; trivial
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hF
    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ R, ← hB, ← algebraMap_smul LL (a k) (B k), map_smulₛₗ f, hσ, hfB]
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun k => R (b k)) := by
    rw [← hRs, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    rw [← hcu]
    change ∑ j, σ (B.repr (cu F) j) • R (b j) ∈ _
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let C : Basis (Fin m) ℂ W := Basis.mk hR hsp
  have hC : ∀ k, C k = f (B k) := fun k => by rw [hfB]; exact Basis.mk_apply _ _ _
  let r : G → W →ₗ[ℂ] W := fun g => C.constr ℂ fun k => f (ρL g (B k))
  have hr : ∀ g w, r g (f w) = f (ρL g w) := by
    intro g w
    conv_lhs => rw [← B.sum_repr w]
    conv_rhs => rw [← B.sum_repr w]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ f, map_smul, map_smul, map_smulₛₗ f, ← hC]
    simp [r]
  let ρ : Representation ℂ G W :=
    { toFun := r
      map_one' := C.ext fun k => by rw [hC, hr]; simp
      map_mul' := fun g h => C.ext fun k => by
        rw [hC, Module.End.mul_apply, hr, hr, hr, map_mul]; rfl }
  refine ⟨f, ρ, hcu, hr, ?_, ?_⟩
  · have hmn : m = n := by
      simpa using (Module.finrank_eq_card_basis B).symm
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · refine hsp.trans ?_
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      change R (b k) ∈ _
      rw [← hfB, ← (Pi.basisFun LL (Fin n)).sum_repr (B k), map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smulₛₗ f, Pi.basisFun_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Module.finrank_eq_card_basis C, hmn]
  · rw [eq_top_iff]
    refine hsp.trans (Submodule.span_mono ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨B k, hfB k⟩
end GlobalTheory.SemilinearReading
