-- Prove2me | solution 1 for GlobalTheory.comul_one_tmul_eq_distribBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:29.576824+00:00
-- url     : https://prove2.me/submissions/8846aee0-8f0b-4f1a-af26-7a62f31bc3fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient

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
omit [IsNoetherianRing R] [IsAdicComplete I R]
namespace GlobalTheory
theorem _root_.solution (S : Type*) [CommRing S] [Algebra R S] {A : Type*}
    [AddCommGroup A] [Module R A] [Coalgebra R A] (a : A) :
    Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] a) =
      AlgebraTensorModule.distribBaseChange R S A A (1 ⊗ₜ Coalgebra.comul a) := by
  rw [TensorProduct.comul_tmul]
  induction (Coalgebra.comul a : A ⊗[R] A) with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
end GlobalTheory
