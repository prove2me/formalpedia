-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twist_vt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:17.701797+00:00
-- url     : https://prove2.me/submissions/d0e222f4-915a-422c-8022-d233f49c7275

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
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (m : ℕ) (χ : N.X) :
    (N.twist β u).vt (N.twG β u g l hl ^ m) χ = (u ^ (β.be χ χ / 2 + l χ * m) : Oˣ) * N.vt (g ^ m) χ := by
  obtain ⟨h1, h2⟩ := N.twG_pow β u g l hl m
  show ((N.ψ χ * u ^ (β.be χ χ / 2) * (N.twG β u g l hl ^ m).s χ : Oˣ) : O) *
    N.th (N.c χ * (show N.A from (N.twG β u g l hl ^ m).b)) = _ * (((N.ψ χ * (g ^ m).s χ : Oˣ) : O) * N.th (N.c χ * (g ^ m).b))
  rw [h1, h2, ← mul_assoc (_ : O), ← Units.val_mul, zpow_add]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul]; abel
end GlobalTheory.Ex.NumD
