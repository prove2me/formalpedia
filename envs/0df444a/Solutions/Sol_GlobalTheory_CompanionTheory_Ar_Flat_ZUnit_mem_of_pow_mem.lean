-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.ZUnit.mem_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:16.385636+00:00
-- url     : https://prove2.me/submissions/0e1f0571-7241-4a6c-ac98-a7117c809952

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ZUnit_of_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
open GlobalTheory.CompanionTheory.Ar.Flat.ZUnit
variable {p : Cpt ξ} {a b : Ω}
namespace GlobalTheory.CompanionTheory.Ar.Flat.ZUnit
theorem _root_.solution (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : a ^ n ∈ regAt ξ p) : a ∈ regAt ξ p :=
  hN p a (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (isIntegral_algebraMap (x := (⟨a ^ n, h⟩ : regAt ξ p))))
end GlobalTheory.CompanionTheory.Ar.Flat.ZUnit
