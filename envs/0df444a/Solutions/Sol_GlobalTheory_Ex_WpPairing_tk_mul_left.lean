-- Prove2me | solution 1 for GlobalTheory.Ex.WpPairing.tk_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:50.176493+00:00
-- url     : https://prove2.me/submissions/131c7764-aa5d-4aab-887c-28fca31b92b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Theorems.Thm_GlobalTheory_Ex_NumD_QT_pow_b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add


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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.WpPairing
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.WpPairing
theorem _root_.solution {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by
  have e := N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b
  rw [N.cub.face, mul_one, one_mul, N.QT_pow_b] at e
  change (p.1.2 * p'.1.2).s p''.1.1.toAdd * cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _
  rw [NumD.Gt.mul_s, NumD.tk, NumD.tk]
  apply Additive.ofMul.injective
  replace e := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_div] at e ⊢
  linear_combination (norm := abel) e
end GlobalTheory.Ex.WpPairing
