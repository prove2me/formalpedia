-- Prove2me | solution 2 for LittleCharity.MMS.mms_le_average
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:36:44.005437+00:00
-- url     : https://prove2.me/submissions/5eaaded7-7661-425d-b340-e72eaf74b554

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

set_option autoImplicit false
open LittleCharity.MMS

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (i : Fin n) (k : ℕ) (hk : 0 < k) (S : Finset (Fin m)) :
    mms (v i) k S ≤ v i S / (k : ℝ) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  unfold mms
  apply ciSup_le
  intro f
  set a : Fin k → ℝ := fun j => v i (S.filter (fun g => f g = j)) with ha
  have hsum : ∑ j : Fin k, a j = v i S := by
    rw [hadd.1 i S]
    have : ∀ j : Fin k, a j = ∑ g ∈ S.filter (fun g => f g = j), v i {g} := fun j => hadd.1 i _
    simp_rw [this]
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  have hle : ∀ j, (⨅ j', a j') ≤ a j := fun j => ciInf_le (Set.finite_range _).bddBelow j
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hk']
  calc (⨅ j', a j') * k = ∑ _j : Fin k, (⨅ j', a j') := by simp [mul_comm]
    _ ≤ ∑ j, a j := Finset.sum_le_sum (fun j _ => hle j)
    _ = v i S := hsum
