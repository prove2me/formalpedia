-- Prove2me | solution 1 for LittleCharity.MMS.mms_le_average
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T09:04:39.400989+00:00
-- url     : https://prove2.me/submissions/c1d69c5c-cb8f-4740-913d-509e591b2855

-- Research direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Argument: Bhaskar Ray Chaudhury, Telikepalli Kavitha, Kurt Mehlhorn, Alkmini Sgouritsa, arXiv:1907.04596v3.
-- Platform formulation: mikedeng1; review: Shuze Chen.
import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
set_option autoImplicit false
open scoped BigOperators
open LittleCharity.MMS

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (i : Fin n) (k : ℕ) (hk : 0 < k) (S : Finset (Fin m)) :
    mms (v i) k S ≤ v i S / (k : ℝ) := by
  classical
  have : NeZero k := ⟨Nat.ne_of_gt hk⟩
  unfold mms
  apply ciSup_le
  intro f
  have hsum : (∑ j : Fin k, v i (S.filter (fun g => f g = j))) = v i S := by
    calc
      _ = ∑ j : Fin k, ∑ g ∈ S.filter (fun g => f g = j), v i {g} :=
        Finset.sum_congr rfl (fun j _ => hadd.1 i _)
      _ = ∑ g ∈ S, v i {g} := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        simp
      _ = v i S := (hadd.1 i S).symm
  have hbound : (↑k : ℝ) * (⨅ j : Fin k, v i (S.filter (fun g => f g = j))) ≤ v i S := by
    rw [← hsum]
    calc
      _ = ∑ j : Fin k, (⨅ j : Fin k, v i (S.filter (fun g => f g = j))) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => ciInf_le (Finite.bddBelow_range _) j)
  apply (le_div_iff₀ (by exact_mod_cast hk)).mpr
  simpa [mul_comm] using hbound

