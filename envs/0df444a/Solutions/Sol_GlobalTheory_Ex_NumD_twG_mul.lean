-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twG_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:23.686412+00:00
-- url     : https://prove2.me/submissions/4d133715-edc9-4d8d-87e9-85e656894fa4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) :
    N.twG β u g l hl * N.twG β u g' l' hl' =
      N.twG β u (g * g') (fun z => l z + l' z) (fun a b => by rw [hl, hl']; ring) := by
  refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
  show g.s z * u ^ l z * (g'.s z * u ^ l' z) / N.θ (N.c z) g.b g'.b =
    g.s z * g'.s z / N.θ (N.c z) g.b g'.b * u ^ (l z + l' z)
  rw [zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel
end GlobalTheory.Ex.NumD
