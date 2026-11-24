-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CxVal.zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:41.566798+00:00
-- url     : https://prove2.me/submissions/5bb99f58-1642-4a85-9249-eadacdb5b944

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CxVal_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CxVal_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable {z : Spec (CommRingCat.of ℂ) ⟶ X}
open GlobalTheory.CompanionTheory.Ar.CxVal
namespace GlobalTheory.CompanionTheory.Ar.CxVal
theorem _root_.solution {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  have hn : ∀ n : ℕ, ValAt ξ z (a ^ n) (r ^ n) := fun n => by
    induction n with
    | zero => simpa using one h.1
    | succ n ih => rw [pow_succ, pow_succ]; exact mul ih h
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using hn n
  · simpa using inv (hn n) (pow_ne_zero _ hr)
end GlobalTheory.CompanionTheory.Ar.CxVal
