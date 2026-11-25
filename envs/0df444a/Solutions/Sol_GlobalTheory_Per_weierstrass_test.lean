-- Prove2me | solution 1 for GlobalTheory.Per.weierstrass_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:22:36.522339+00:00
-- url     : https://prove2.me/submissions/adfb705f-50c6-49e4-9816-e056625d075f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProdPrimePowDvd
import Theorems.Thm_GlobalTheory_Per_ev_C
import Theorems.Thm_GlobalTheory_Per_X_dvd_ev_iff
import Theorems.Thm_GlobalTheory_Per_X_pow_dvd_ev_iff
import Theorems.Thm_GlobalTheory_Per_prime_X_sub_C
import Theorems.Thm_GlobalTheory_Per_prod_prime_pow_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Per
namespace GlobalTheory.Per
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O], ∀ (LL : Type) [Field LL] [Algebra O LL] [IsFractionRing O LL] (ι : Type) [Fintype ι] (x : ι → O) (m : ι → ℕ), Function.Injective x → (∀ k, ¬ IsUnit (x k)) → ∀ (ev : ι → (PowerSeries O →ₐ[O] PowerSeries LL)), (∀ k, ∃ w : PowerSeries LL, IsUnit w ∧ ev k PowerSeries.X = PowerSeries.C (algebraMap O LL (x k)) + PowerSeries.X * w) → ∀ a : PowerSeries O, (∀ k, PowerSeries.X ^ m k ∣ ev k a) ↔ (∏ k, (PowerSeries.X - PowerSeries.C (x k)) ^ m k) ∣ a := by
  intro O _ _ _ _ LL _ _ _ ι _ x m hxinj hxu ev hev a
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have key : ∀ k, PowerSeries.X ^ m k ∣ ev k a ↔
      (PowerSeries.X - PowerSeries.C (x k)) ^ m k ∣ a := by
    intro k
    obtain ⟨w, hw, hwk⟩ := hev k
    exact X_pow_dvd_ev_iff hinj (hxu k) (ev k) hw hwk (m k) a
  simp_rw [key]
  constructor
  · intro h
    refine prod_prime_pow_dvd (fun k => PowerSeries.X - PowerSeries.C (x k)) m ?_ ?_ a h
      Finset.univ
    · intro k
      obtain ⟨w, -, hwk⟩ := hev k
      exact prime_X_sub_C hinj (hxu k) (ev k) hwk
    · intro j k hjk
      obtain ⟨w, -, hwj⟩ := hev j
      have h1 := (X_dvd_ev_iff hinj (hxu j) (ev j) hwj _).2 hjk
      rw [map_sub, hwj, ev_C, PowerSeries.X_dvd_iff] at h1
      have h2 : algebraMap O LL (x j) = algebraMap O LL (x k) := by
        simpa [sub_eq_zero] using h1
      exact hxinj (hinj h2)
  · intro h k
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans h
end GlobalTheory.Per
