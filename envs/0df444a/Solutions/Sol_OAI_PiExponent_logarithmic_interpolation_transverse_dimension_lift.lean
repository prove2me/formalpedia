-- Prove2me | solution 1 for OAI.PiExponent.logarithmic_interpolation_transverse_dimension_lift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T16:59:45.90677+00:00
-- url     : https://prove2.me/submissions/3755bd4a-ae98-4ea0-8d43-fea200d76ff6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_logarithmic_interpolation_volume_bounds_of_eventual
import Theorems.Thm_OAI_PiExponent_separated_weight_log_interpolation_of_volume_bounds

open scoped BigOperators

theorem solution
    (m K : ℕ) (hm : 0 < m) (hK : 0 < K)
    (w0 v0 alpha theta : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    (hmargin : theta ^ (m + 1) < alpha ^ m)
    (hbase :
      ∃ S : List ℕ → ℕ,
        ∀ w : Fin m → ℕ, (∀ i, 0 < w i) →
          OAI.PiExponent.separatedWeights S w →
          ∀ c : Fin K → Fin m → ℂ,
            (∀ i : Fin m, Function.Injective (fun j : Fin K => c j i)) →
            OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    ∃ S : List ℕ → ℕ,
      ∀ w : Fin (m + 1) → ℕ, (∀ i, 0 < w i) →
        OAI.PiExponent.separatedWeights S w →
        ∀ c : Fin K → Fin (m + 1) → ℂ,
          (∀ i : Fin (m + 1), Function.Injective (fun j : Fin K => c j i)) →
          OAI.PiExponent.eventualLogJetSurjective (m + 1) K w0 v0 theta w c := by
  have hvol :=
    OAI.PiExponent.logarithmic_interpolation_volume_bounds_of_eventual
      m K hm hK w0 v0 alpha hw0 hv0 halpha halpha1 hbase
  have hKpos : (0 : ℚ) < (K : ℚ) := by exact_mod_cast hK
  have hwratio : 0 < w0 / v0 := div_pos hw0 hv0
  have hvolTheta : (K : ℚ) * theta ^ (m + 1) < 1 := by
    calc
      (K : ℚ) * theta ^ (m + 1) < (K : ℚ) * alpha ^ m :=
        mul_lt_mul_of_pos_left hmargin hKpos
      _ ≤ 1 := hvol.1
  have hvolFull : (K : ℚ) * (w0 / v0) * theta ^ (m + 1) < 1 := by
    calc
      (K : ℚ) * (w0 / v0) * theta ^ (m + 1) <
          (K : ℚ) * (w0 / v0) * alpha ^ m :=
        mul_lt_mul_of_pos_left hmargin (mul_pos hKpos hwratio)
      _ ≤ 1 := hvol.2
  exact OAI.PiExponent.separated_weight_log_interpolation_of_volume_bounds
    (m + 1) K (Nat.succ_pos m) hK w0 v0 theta hw0 hv0 htheta htheta1
    hvolTheta hvolFull
