-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.s_cubN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:24.126124+00:00
-- url     : https://prove2.me/submissions/2e94ee5f-632b-48c4-a455-239245e04670

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_cubN_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
private theorem cb {k : ℕ} (p : N.QT k) : N.c p.1.1.toAdd = p.1.2.b ^ k := by
  have h : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
  rw [← Gt.pow_b, h, io_b]
end GlobalTheory.Ex.NumD.Hom
end
end

set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
namespace GlobalTheory.Ex.NumD.Hom
theorem _root_.solution {k : ℕ} (q : N.QT k) {g : N.Gt} {g' : N'.Gt} (hg : I.Rel g g') :
    g'.s (I.e q.1.1.toAdd) * cubN N'.θ k 1 (I.φ q.1.2.b) (I.φ g.b) * I.h (q.1.2.b * g.b) ^ k =
      F (g.s q.1.1.toAdd * cubN N.θ k 1 q.1.2.b g.b) * I.h q.1.2.b ^ k * I.h g.b ^ k := by
  have a := hg.2 q.1.1.toAdd
  have b := I.cubN_eq k q.1.2.b g.b
  rw [cb] at a
  rw [map_mul]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  simp only [ofMul_mul] at a b ⊢
  linear_combination (norm := abel) a + b
end GlobalTheory.Ex.NumD.Hom
