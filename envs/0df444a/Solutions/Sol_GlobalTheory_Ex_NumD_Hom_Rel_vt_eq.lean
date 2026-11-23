-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.Rel.vt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:27.718892+00:00
-- url     : https://prove2.me/submissions/484af80a-6b27-40de-bd69-fc174ad1bbb4

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
theorem _root_.solution {g : N.Gt} {g' : N'.Gt} (hg : I.Rel g g') (χ : N.X) :
    N'.vt g' (I.e χ) = (I.lam * I.h g.b : O'ˣ) * f (N.vt g χ) := by
  have a := hg.2 χ
  have d := I.ψ_eq χ
  have key : N'.ψ (I.e χ) * g'.s (I.e χ) * (I.lam * I.h (N.c χ * g.b)) = I.lam * I.h g.b * F (N.ψ χ * g.s χ) := by
    rw [map_mul]
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace d := congrArg Additive.ofMul d
    simp only [ofMul_mul] at a d ⊢
    linear_combination (norm := abel) a + d
  rw [vt, vt, I.c_eq, hg.1, ← map_mul, I.th_eq, ← mul_assoc, ← Units.val_mul, key, map_mul f, Units.val_mul,
    mul_assoc]
  rfl
end Rel
end GlobalTheory.Ex.NumD.Hom
