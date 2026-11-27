-- Prove2me | solution 1 for GlobalTheory.existsUnique_algEquiv_of_compatible_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:18.309815+00:00
-- url     : https://prove2.me/submissions/7751aa34-c7ca-4774-b8eb-f33a9db5afd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_existsUnique_algHom_of_compatible_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (A ⧸ (I ^ n).map (algebraMap R A)) ≃ₐ[R] B ⧸ (I ^ n).map (algebraMap R B))
    (hf : ∀ n x, adicQuotTransition I B n (f (n + 1) x) = f n (adicQuotTransition I A n x)) :
    ∃! g : A ≃ₐ[R] B, ∀ n a, Ideal.Quotient.mk _ (g a) = f n (Ideal.Quotient.mk _ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_quotient I (fun n ↦ (f n).toAlgHom) hf
  obtain ⟨g', hg', -⟩ := existsUnique_algHom_of_compatible_quotient I
    (fun n ↦ (f n).symm.toAlgHom) fun n x ↦ by
      apply (f n).injective
      simpa using (hf n ((f (n + 1)).symm x)).symm
  have hA := (existsUnique_algHom_of_compatible_quotient I (A := A) (B := A)
    (fun n ↦ .id _ _) fun _ _ ↦ rfl).unique (y₁ := g'.comp g) (y₂ := .id _ _)
    (fun n a ↦ by simp [hg, hg']) fun _ _ ↦ rfl
  have hB := (existsUnique_algHom_of_compatible_quotient I (A := B) (B := B)
    (fun n ↦ .id _ _) fun _ _ ↦ rfl).unique (y₁ := g.comp g') (y₂ := .id _ _)
    (fun n a ↦ by simp [hg, hg']) fun _ _ ↦ rfl
  exact ⟨.ofAlgHom g g' hB hA, hg,
    fun e he ↦ AlgEquiv.coe_algHom_injective (hu e.toAlgHom he)⟩
end GlobalTheory
