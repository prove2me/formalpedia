-- Prove2me | solution 1 for GlobalTheory.PDivGroup.baseChangeMap_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:32:38.396888+00:00
-- url     : https://prove2.me/submissions/7621c662-dbcd-4740-bde1-e4bd8fef4d76

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
variable (G H K : PDivGroup p O) (O') [Algebra O O']
variable {G H K}
namespace GlobalTheory.PDivGroup
theorem _root_.solution (f g : G ⟶ H) :
    baseChangeMap O' (f + g) = baseChangeMap O' f + baseChangeMap O' g :=
  baseChange_hom_ext fun n a => by
    have h1 := map_mul ((toBaseChange O O' (H.A n)).pts (O' ⊗[O] G.A n) fun _ => rfl)
      (toPts ((baseChangeMap O' f).conv n)) (toPts ((baseChangeMap O' g).conv n))
    have h2 := map_mul (ptsPush (H.A n)
      (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] O' ⊗[O] G.A n))
      (toPts (f.conv n)) (toPts (g.conv n))
    exact DFunLike.congr_fun (congrArg ofConv (h2.trans h1.symm)) a
end GlobalTheory.PDivGroup
