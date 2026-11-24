-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.sq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:30.05607+00:00
-- url     : https://prove2.me/submissions/de0c2427-6107-4cfd-86f7-a1f71ba35d4f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Ring R] [Algebra ℂ R]
omit [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.KoszulBd
theorem _root_.solution (L A : ι → R) (hLL : ∀ i j, Commute (L i) (L j)) (hLA : ∀ i j, Commute (L i) (A j))
    (hAA : ∀ i j, A i * A j + A j * A i = 0) : (∑ i, L i * A i) * (∑ i, L i * A i) = 0 := by
  have key : (∑ i, L i * A i) * (∑ i, L i * A i) = ∑ i, ∑ j, L i * L j * (A i * A j) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, mul_assoc, ← mul_assoc (A i) (L j) (A j), ← (hLA j i).eq, mul_assoc]
  have hS : ∑ i, ∑ j, L i * L j * (A i * A j) + ∑ i, ∑ j, L i * L j * (A j * A i) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_add, hAA i j, mul_zero]
  have hS' : ∑ i, ∑ j, L i * L j * (A j * A i) = ∑ i, ∑ j, L i * L j * (A i * A j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(hLL j i).eq]
  rw [key]
  rw [hS'] at hS
  have h2 : (2 : ℂ) • ∑ i, ∑ j, L i * L j * (A i * A j) = 0 := by
    rw [two_smul]
    exact hS
  have h3 := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
  simpa [smul_smul] using h3
end GlobalTheory.CompanionTheory.KoszulBd
