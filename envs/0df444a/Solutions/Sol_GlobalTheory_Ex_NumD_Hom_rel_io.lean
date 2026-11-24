-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.rel_io
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:25.609029+00:00
-- url     : https://prove2.me/submissions/e0498188-253d-4406-8b68-6e00a750220f

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
namespace GlobalTheory.Ex.NumD.Hom
theorem _root_.solution (y : N.X) : I.Rel (N.io y) (N'.io (I.e y)) := by
  refine ⟨I.c_eq y, fun χ => ?_⟩
  have a := I.ψ_eq (y + χ)
  have b := I.ψ_eq y
  have c := I.ψ_eq χ
  rw [N.c_add, map_add, mul_comm (N.c y)] at a
  simp only [io_s, io_b, τ, map_div]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div] at a b c ⊢
  linear_combination (norm := abel) a - b - c
end GlobalTheory.Ex.NumD.Hom
