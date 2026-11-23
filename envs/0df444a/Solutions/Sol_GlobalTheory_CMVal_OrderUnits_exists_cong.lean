-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.exists_cong
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:13.453355+00:00
-- url     : https://prove2.me/submissions/b8a3921a-4251-4f77-90e4-895ac11fda14

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_ball_mem_nhds
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_val_int_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution {c : Ideal (OF E)} (v : HeightOneSpectrum (OF E)) (n : ℕ) (hn : v.asIdeal ^ n ∣ c)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P ∈ S, Over P v) {z : Af E} (hz : z ∈ hatO c) :
    ∃ a : OF E, ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
  have hev : ∀ P : HeightOneSpectrum (𝓞 E), Continuous fun z : Af E => z P := fun P =>
    RestrictedProduct.continuous_eval P
  have hU : ∀ᶠ x : Af E in 𝓝 z, ∀ P ∈ S, Valued.v (x P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [Filter.eventually_all_finset]
    intro P _
    exact (hev P).tendsto z (ball_mem_nhds P n (z P))
  have hz1 : z ∈ closure (((orderC c).map (algebraMap E (Af E)) : Subring (Af E)) : Set (Af E)) := hz
  obtain ⟨x, ⟨k, hk, rfl⟩, hx⟩ := ((mem_closure_iff_frequently.1 hz1).and_eventually hU).exists
  obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hk
  refine ⟨a, fun P hP => ?_⟩
  have hb' : b ∈ P.asIdeal ^ n := by
    have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ n := by
      refine (Ideal.map_mono (Ideal.le_of_dvd hn)).trans ?_
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      exact (hS P hP).ge
    exact h1 hb
  have h2 := val_int_le P n b hb'
  have h3 := hx P hP
  rw [map_add] at h3
  have h4 : algebraMap E (Af E) (algebraMap (OF E) E a) P - z P =
      ((algebraMap E (Af E) (algebraMap (OF E) E a) + algebraMap E (Af E) (algebraMap (𝓞 E) E b)) P - z P) -
        algebraMap E (Af E) (algebraMap (𝓞 E) E b) P := by
    change _ = (algebraMap E (Af E) (algebraMap (OF E) E a) P + algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z P) - _
    ring
  rw [h4]
  exact Valuation.map_sub_le _ h3 h2
end GlobalTheory.CMVal.OrderUnits
