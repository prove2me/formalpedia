-- Prove2me | solution 1 for GlobalTheory.T.sum_local_inv_eq_zero_of_unramified_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:15.700847+00:00
-- url     : https://prove2.me/submissions/c18729f5-f392-4654-acbf-6d51574a0c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumInvEqZeroOfUnramifiedCocycle
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumInvEqZeroOfUnramifiedCocycleStatement
import Theorems.Thm_GlobalTheory_sum_inv_eq_zero_of_unramified_cocycle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ζ : Ω), IsPrimitiveRoot ζ (l ^ 1) → ∃ inv : InvFam F Ω l 1, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l 1), (∀ g h : G F Ω, ∀ n ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ n' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * n, h * n') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l 1 (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  first | exact @GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle | exact GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle | (intros; apply GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle <;> assumption)
end _root_.GlobalTheory.T
