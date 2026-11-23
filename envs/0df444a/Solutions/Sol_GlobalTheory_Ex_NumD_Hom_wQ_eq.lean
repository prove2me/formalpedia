-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.wQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:51.180778+00:00
-- url     : https://prove2.me/submissions/ecfe4898-088a-413c-8666-7bd7639835a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_dbl_eq
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_mulq_eq
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_s_cubN_eq
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
theorem _root_.solution {k : ℕ} (hk : Odd k) (p : N.QT k) (p' : N'.QT k) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) : N'.wQ p' * I.h p.1.2.b ^ k = F (N.wQ p) := by
  have a := I.s_cubN_eq p hp
  have b := I.dbl_eq p.1.2.b
  have c := I.mulq_eq k p.1.2.b
  have d := I.ψ_eq p.1.1.toAdd
  rw [cb] at d
  obtain ⟨j, rfl⟩ := hk
  have e : (2 * j + 1 - 1) / 2 = j := by omega
  simp only [wQ, NumB.wS, ep, hp.1, map_div, map_mul, map_pow, e] at a ⊢
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  replace d := congrArg Additive.ofMul d
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b c d ⊢
  linear_combination (norm := module) d + c - j • a + (j * (2 * j + 1)) • b
end GlobalTheory.Ex.NumD.Hom
