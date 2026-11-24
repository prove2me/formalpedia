-- Prove2me | solution 1 for GlobalTheory.ProductLeftMaps.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:29.758719+00:00
-- url     : https://prove2.me/submissions/0d4d0fcf-17c8-4229-84cb-b04c515aa353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdLeftEqMaps
import Theorems.Thm_GlobalTheory_ProductLeftMaps_prodLeft_eq_maps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ProductLeftMaps
open TensorProduct
namespace GlobalTheory.ProductLeftMaps
theorem _root_.solution : ∀ {F A B E : Type} [inst : Field F] [inst_1 : CommRing A] [inst_2 : CommRing B]
    [inst_3 : CommRing E] [inst_4 : Algebra F A] [inst_5 : Algebra F B] [inst_6 : Algebra F E]
    (z : TensorProduct F (A × B) E),
    (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F A E) z = (0 : TensorProduct F A E) →
    (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F B E) z = (0 : TensorProduct F B E) →
    z = (0 : TensorProduct F (A × B) E) := by
  intro F A B E _ _ _ _ _ _ _ z h1 h2
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [prodLeft_eq_maps, h1, h2, map_zero]
  rfl
end GlobalTheory.ProductLeftMaps
