-- Prove2me | solution 1 for GlobalTheory.ProjModFinIso.finrank_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:50.379647+00:00
-- url     : https://prove2.me/submissions/6e4bfed7-7948-41ff-9909-21ccf0ed19a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModFinIso
theorem _root_.solution (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R (M × N) = Module.finrank R M + Module.finrank R N := by
  have h1 := (TensorProduct.isBaseChange R (M × N) (FractionRing R)).finrank_eq
  have h2 := (TensorProduct.isBaseChange R M (FractionRing R)).finrank_eq
  have h2' := (TensorProduct.isBaseChange R N (FractionRing R)).finrank_eq
  have h3 := (TensorProduct.prodRight R (FractionRing R) (FractionRing R) M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']
end GlobalTheory.ProjModFinIso
