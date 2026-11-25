-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.phi_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:42:19.761732+00:00
-- url     : https://prove2.me/submissions/9cdd7b49-099e-43f5-bf69-8fc12cdc55a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Theorems.Thm_GlobalTheory_Ex_NumD_QT_pow_b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
namespace GlobalTheory.Ex.TateInh
theorem _root_.solution (N : NumD O) {k : ℕ} (p : N.QT k) (h : N.Gt) (α : N.X) :
    h.s (p.1.1.toAdd + α) * N.uV k (N.c α) p.1.2.b h.b * p.1.2.s α =
      h.s p.1.1.toAdd * cubN N.θ k 1 p.1.2.b h.b * (h * p.1.2).s α := by
  have a := congrArg Additive.ofMul (h.mult p.1.1.toAdd α)
  rw [NumB.uV, N.cub.N_split k (N.c α), N.QT_pow_b, NumD.Gt.mul_s, N.cub.s01 (N.c α) (N.c _) h.b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) a
end GlobalTheory.Ex.TateInh
