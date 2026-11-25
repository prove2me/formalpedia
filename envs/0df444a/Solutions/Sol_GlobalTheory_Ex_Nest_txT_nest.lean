-- Prove2me | solution 1 for GlobalTheory.Ex.Nest.txT_nest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:21:31.316906+00:00
-- url     : https://prove2.me/submissions/467d2a92-d0b1-402b-b4e7-e109313b06ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationSeriesTermsNest
import Theorems.Thm_GlobalTheory_Ex_Nest_wQ_nest
import Theorems.Thm_GlobalTheory_T_mulq_dbl_cubN_relations


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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Nest
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.Nest
theorem _root_.solution : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n m : ℕ), Odd n → Odd m → ∀ (p'' : N.QT ((n * m) ^ 2)) (p : N.QT (m ^ 2)), p''.1.1 = p.1.1 ^ n → p.1.2 = p''.1.2 ^ n → ∀ χ, N.txT (n * m) p'' χ = N.txT m p χ := by
  intro O _ N n m hn hm p'' p hy hg χ
  have hw := wQ_nest N hm.pow (hn.mul hm).pow (by ring) p'' p hy hg
  have hq := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m n p''.1.2.b p''.1.2.b).1
  rw [mul_comm m n] at hq
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hu : N.wQ p'' / mulq N.θ N.σ (n * m) p''.1.2.b = N.wQ p / mulq N.θ N.σ m p.1.2.b := by
    rw [← hw, hq, hb, mul_div_mul_right_eq_div]
  simp only [NumD.txT]
  rw [hu, hg, ← pow_mul]
end GlobalTheory.Ex.Nest
