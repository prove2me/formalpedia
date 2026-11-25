-- Prove2me | solution 1 for GlobalTheory.s_points_kpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:26.095072+00:00
-- url     : https://prove2.me/submissions/5769f7b0-4b23-4f83-b0c1-aa4eb7d93eff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BoundedPowersOrExistsValuationSubringDvdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDomaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPoints
import Theorems.Thm_GlobalTheory_perfectRing_valuationSubring_of_isAlgClosed
import Theorems.Thm_GlobalTheory_T_adicCompletion_principal_perfect
import Theorems.Thm_GlobalTheory_T_adicCompletion_valuationRing_complete_valuationDomain
import Theorems.Thm_GlobalTheory_T_pow_dvd_bound_or_exists_valuationSubring_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 →
    u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) →
    (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) →
    ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by
  intro l _ R _ u x hl hu hrad H M
  rcases GlobalTheory.T.pow_dvd_bound_or_exists_valuationSubring_dvd R u x M hu hrad with h | ⟨L, _, _, V, f, hfu, hfnu, hdvd⟩
  · exact h
  exfalso
  haveI : CharP V l := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast f, hl, map_zero])
  haveI : PerfectRing V l := perfectRing_valuationSubring_of_isAlgClosed l V
  obtain ⟨hdom, hpre, hne, hnu, hcomp⟩ := GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain V (f u) hfu hfnu
  obtain ⟨hl', hbij⟩ := GlobalTheory.T.adicCompletion_principal_perfect l V (f u)
  set O := AdicCompletion (Ideal.span {f u}) V
  haveI : IsDomain O := hdom
  haveI : ValuationRing O := { toPreValuationRing := hpre }
  haveI : CharP O l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl'
  haveI : PerfectRing O l := ⟨hbij⟩
  let g : R →+* O := (algebraMap V O).comp f
  have hgx : g x = 0 := H O g hne hnu hcomp
  have hd : g x ∣ g u ^ M := by
    simpa [g, map_pow] using map_dvd (algebraMap V O) hdvd
  rw [hgx, zero_dvd_iff] at hd
  exact hne (by_contra fun h => pow_ne_zero M h hd)
end GlobalTheory
