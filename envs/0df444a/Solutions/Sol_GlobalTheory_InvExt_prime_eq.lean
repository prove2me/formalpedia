-- Prove2me | solution 1 for GlobalTheory.InvExt.prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:57:11.865864+00:00
-- url     : https://prove2.me/submissions/2f6b5197-cc65-44c1-b69b-13b42d170b74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
import Theorems.Thm_GlobalTheory_InvExt_exists_common_residue
import Theorems.Thm_GlobalTheory_InvExt_natCast_kb
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.InvExt
variable (C : Core)
variable {C}
namespace GlobalTheory.InvExt
theorem _root_.solution {X : Scheme.{0}} {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (α : Sp (OO p) ⟶ X) (β : Sp (OO q) ⟶ X) (h : α (cPt p) = β (cPt q)) : p = q := by
  obtain ⟨K, _, _, v, v', -⟩ := exists_common_residue α β h
  have h1 : (p : K) = 0 := by
    rw [← map_natCast (Spec.preimage v).hom]
    exact (congrArg _ (natCast_kb p)).trans (map_zero _)
  have h2 : (q : K) = 0 := by
    rw [← map_natCast (Spec.preimage v').hom]
    exact (congrArg _ (natCast_kb q)).trans (map_zero _)
  have := (CharP.charP_iff_prime_eq_zero hp.out).mpr h1
  have := (CharP.charP_iff_prime_eq_zero hq.out).mpr h2
  exact CharP.eq K ‹CharP K p› ‹CharP K q›
end GlobalTheory.InvExt
