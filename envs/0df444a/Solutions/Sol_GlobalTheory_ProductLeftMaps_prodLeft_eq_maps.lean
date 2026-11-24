-- Prove2me | solution 1 for GlobalTheory.ProductLeftMaps.prodLeft_eq_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:25.618701+00:00
-- url     : https://prove2.me/submissions/e5434ce2-324a-418d-a0f6-55048ba76539

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdLeftEqMaps

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
theorem _root_.solution {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : TensorProduct F (A × B) E) :
    TensorProduct.prodLeft F F A B E z =
      ((Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F A E) z,
       (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F B E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul x e =>
    obtain ⟨a, b⟩ := x
    simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, map_add]
    rfl
end GlobalTheory.ProductLeftMaps
