-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.ZUnit.of_pow_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:19.112305+00:00
-- url     : https://prove2.me/submissions/38de6109-793a-47b6-b64c-9787d67530cd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ZUnit_of_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ZUnit_mem_of_pow_mem

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
theorem _root_.solution (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a :=
  of_pow (mem_of_pow_mem hN hn h.2.1) hn h
end GlobalTheory.CompanionTheory.Ar.Flat.ZUnit
