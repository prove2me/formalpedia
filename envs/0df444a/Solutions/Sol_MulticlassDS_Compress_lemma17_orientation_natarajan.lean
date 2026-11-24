-- Prove2me | solution 1 for MulticlassDS.Compress.lemma17_orientation_natarajan
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T12:33:30.518328+00:00
-- url     : https://prove2.me/submissions/6d82c9f6-dc39-4d61-8636-81d63044c0fd

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_OneInclusion
import Theorems.Thm_MulticlassDS_Compress_cor28_orientation_expDim
import Theorems.Thm_MulticlassDS_Compress_lemma29_expDim_le

open MulticlassDS.Compress

theorem solution {n p : ℕ} (H : Set (Fin n → Fin p)) (dN : ℕ)
    (hN : natarajanDim H = dN) :
    ∃ σ : Orientation H, ∀ v ∈ H, (outdeg σ v : ℝ) ≤ 20 * dN * Real.logb 2 p := by
  have hle : expDim H ≤ ((p ^ n : ℕ) : ℕ∞) := by
    unfold expDim
    refine iSup_le fun k => iSup_le fun S => iSup_le fun hk => ?_
    have hH : H.encard ≤ ((p ^ n : ℕ) : ℕ∞) := by
      calc H.encard ≤ (Set.univ : Set (Fin n → Fin p)).encard :=
            Set.encard_le_encard (Set.subset_univ H)
        _ = ((p ^ n : ℕ) : ℕ∞) := by
            rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
            simp
    have h1 : ((2 ^ k : ℕ) : ℕ∞) ≤ ((p ^ n : ℕ) : ℕ∞) := by
      push_cast
      exact hk.trans ((Set.encard_image_le _ _).trans hH)
    have h2 : 2 ^ k ≤ p ^ n := Nat.cast_le.mp h1
    have h3 : k < 2 ^ k := k.lt_two_pow_self
    exact Nat.cast_le.mpr (by omega)
  obtain ⟨dE, hdE⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) hle)
  obtain ⟨σ, hσ⟩ := cor28_orientation_expDim H dE hdE.symm
  have h29 := lemma29_expDim_le H dN dE hN hdE.symm
  refine ⟨σ, fun v hv => ?_⟩
  have h' : (outdeg σ v : ℝ) ≤ 4 * dE := by exact_mod_cast hσ v hv
  linarith
