-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.wp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:49.534209+00:00
-- url     : https://prove2.me/submissions/d54e8a21-f07d-4730-8224-312b5187e8b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_s_cubN_eq

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
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
namespace GlobalTheory.Ex.NumD.Hom
theorem _root_.solution {k : ℕ} (p q : N.QT k) (p' q' : N'.QT k) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) (eq : q'.1.1.toAdd = I.e q.1.1.toAdd) (hq : I.Rel q.1.2 q'.1.2) :
    N'.wp p' q' = F (N.wp p q) := by
  have a := I.s_cubN_eq q hp
  have b := I.s_cubN_eq p hq
  rw [mul_comm p.1.2.b] at b
  simp only [wp, tk, ep, eq, hp.1, hq.1, map_div]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  simp only [ofMul_mul, ofMul_div] at a b ⊢
  linear_combination (norm := abel) a - b
end GlobalTheory.Ex.NumD.Hom
