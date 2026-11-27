-- Prove2me | solution 1 for GlobalTheory.existsUnique_bialgEquiv_of_compatible_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:27.100818+00:00
-- url     : https://prove2.me/submissions/1f0ec5e4-81b4-49e9-a7fd-143c634a68cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_eq_of_forall_one_tmul_quotient_eq
import Theorems.Thm_GlobalTheory_existsUnique_algEquiv_of_compatible_tensor
import Theorems.Thm_GlobalTheory_existsUnique_bialgHom_of_compatible_tensor

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
variable [IsNoetherianRing R] [IsAdicComplete I R]
variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A ≃ₐc[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A ≃ₐc[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_bialgHom_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n).toBialgHom) hf
  obtain ⟨e, he, -⟩ := existsUnique_algEquiv_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n).toAlgEquiv) hf
  have hge : ⇑g = e := funext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ (hg n a).trans (he n a).symm
  exact ⟨.ofBijective g (hge ▸ e.bijective), hg,
    fun g' hg' ↦ BialgEquiv.ext fun a ↦ congr($(hu g' hg') a)⟩
end GlobalTheory
