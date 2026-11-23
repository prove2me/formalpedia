-- Prove2me | solution 1 for GlobalTheory.CechDR.SemiHom.oneFormMap_eq_kaehlerDifferential_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:25.011164+00:00
-- url     : https://prove2.me/submissions/02763e6b-eb24-4c45-bf5c-7aa38b6c31e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
variable {σ : R →+* R'} {α : B →+* B'}
variable {τ : R' →+* R''} {β : B' →+* B''} {ρ : R →+* R''} {γ : B →+* B''}
namespace GlobalTheory.CechDR
namespace SemiHom
theorem _root_.solution [Algebra R B'] [Algebra B B'] [IsScalarTower R B B'] {τ : R →+* R}
    {β : B →+* B'} (h : SemiHom τ β) (e : ∀ b, β b = algebraMap B B' b) (ω : Ω[B⁄R]) :
    h.m1 ω = KaehlerDifferential.map R R B B' ω := by
  induction ω using ind1 with
  | h b c => simp [e, KaehlerDifferential.map_D]
  | h0 => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
end SemiHom
end GlobalTheory.CechDR
