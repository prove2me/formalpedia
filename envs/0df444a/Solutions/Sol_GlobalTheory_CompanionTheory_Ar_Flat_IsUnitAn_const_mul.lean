-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.IsUnitAn.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:39.573+00:00
-- url     : https://prove2.me/submissions/e40c8be5-8944-48d5-9c9b-6f06feb37abf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsConstMul
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsLineGenOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_IsFlatAn_const_mul
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {Xo : Moduli D l} {c : Coeff l}
variable {O : Type} [CommRing O] {β : O →+* c.F}
attribute [instance] CptOver.field CptOver.acg CptOver.mod
namespace GlobalTheory.CompanionTheory.Ar.Flat
namespace IsUnitAn
theorem _root_.solution {τ : E →+* ℂ} {σ : c.F →+* ℂ} {Φ : CFn Xo c} (h : IsUnitAn τ σ Φ) {k : ℂ}
    (hk : ‖k‖ = 1) : IsUnitAn τ σ (fun y v w => k * Φ y v w) where
  ne y v w hf := mul_ne_zero (by rintro rfl; simp at hk) (h.ne y v w hf)
  chg y v w v' w' A B h1 h2 h3 h4 := by rw [_root_.mul_assoc, _root_.mul_assoc, h.chg y v w v' w' A B h1 h2 h3 h4]
  norm y v w Γ Δ h1 h2 h3 := by rw [norm_mul, hk, _root_.one_mul]; exact h.norm y v w Γ Δ h1 h2 h3
  hol R _ x vR wR m B ψ v w h1 h2 h3 := (h.hol R x vR wR m B ψ v w h1 h2 h3).const_mul k
end IsUnitAn
end GlobalTheory.CompanionTheory.Ar.Flat
