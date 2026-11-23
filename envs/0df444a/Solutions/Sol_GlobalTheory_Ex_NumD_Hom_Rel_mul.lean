-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.Rel.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:58.459014+00:00
-- url     : https://prove2.me/submissions/c19871f8-e5c8-4e60-81cf-b13a81af7d66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport

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
variable {I}
namespace GlobalTheory.Ex.NumD.Hom
namespace Rel
theorem _root_.solution {g h : N.Gt} {g' h' : N'.Gt} (hg : I.Rel g g') (hh : I.Rel h h') : I.Rel (g * h) (g' * h') := by
  refine ⟨by rw [Gt.mul_b, Gt.mul_b, hg.1, hh.1, map_mul], fun χ => ?_⟩
  have a := I.θ_eq (N.c χ) g.b h.b
  have b := hg.2 χ
  have c := hh.2 χ
  rw [Gt.mul_s, Gt.mul_s, Gt.mul_b, hg.1, hh.1, I.c_eq, ← mul_assoc, map_div, map_mul]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div] at a b c ⊢
  linear_combination (norm := abel) b + c - a
end Rel
end GlobalTheory.Ex.NumD.Hom
