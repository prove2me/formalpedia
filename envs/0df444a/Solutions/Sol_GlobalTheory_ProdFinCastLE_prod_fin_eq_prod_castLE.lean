-- Prove2me | solution 1 for GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:14.894822+00:00
-- url     : https://prove2.me/submissions/090ef8f9-698b-4948-93e7-c2b57d9e9450

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ProdFinEqProdCastLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ProdFinCastLE
namespace GlobalTheory.ProdFinCastLE
theorem _root_.solution {a b : ℕ} {M : Type} [CommMonoid M] (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ r : Fin b, a ≤ (r : ℕ) → f r = 1) :
    ∏ r : Fin b, f r = ∏ r : Fin a, f (Fin.castLE h r) := by
  symm
  rw [show (∏ r : Fin a, f (Fin.castLE h r)) =
      ∏ x ∈ Finset.univ.map ⟨Fin.castLE h, Fin.castLE_injective h⟩, f x by
    rw [Finset.prod_map]
    rfl]
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => hf x ?_
  by_contra hlt
  push Not at hlt
  exact hx (Finset.mem_map.2 ⟨⟨x, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
end GlobalTheory.ProdFinCastLE
