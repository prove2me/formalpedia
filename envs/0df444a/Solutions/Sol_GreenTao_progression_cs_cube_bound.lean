-- Prove2me | solution 1 for GreenTao.progression_cs_cube_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:38:23.841569+00:00
-- url     : https://prove2.me/submissions/b43be834-36cc-44b3-ae96-8148f6d05eeb

import Theorems.Thm_GreenTao_coordinate_cauchy_schwarz
import Theorems.Thm_GreenTao_iterated_cauchy_schwarz
import Theorems.Thm_GreenTao_cs_stage_factorization
import Theorems.Thm_GreenTao_cs_endpoint_identities
import Mathlib

open scoped BigOperators
open GreenTao

theorem solution
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ+) (hm : Nat.Prime (m : ℕ)) (hdm : d < (m : ℕ))
    (μ : ZMod (m : ℕ) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (j : Fin (d + 1)) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ)
    (hF : ∀ i x, |F i x| ≤ μ x) :
    |GreenTao.mixedAPAvg (d + 1) F| ^ (2 ^ d) ≤
      GreenTao.csFactor d j μ *
        GreenTao.weightedCubeAvg d (GreenTao.csWeight d j μ) (F j) := by
  classical
  let J : ℕ → ℝ := fun l => csStage d j μ F l
  let P : ℕ → ℝ := fun l => if hl : l < d then csStepFactor d j μ ⟨l, hl⟩ else 0
  have hstep (l : ℕ) (hl : l < d) : |J l| ^ 2 ≤ P l * J (l + 1) := by
    obtain ⟨G, w, H, hb, hJ, hP, hJnext⟩ := cs_stage_factorization d m μ hμ j F hF ⟨l, hl⟩
    have h := coordinate_cauchy_schwarz G w H (fun a => (hb a).1) (fun a => (hb a).2)
    rw [← hJ, ← hP, ← hJnext] at h
    simpa only [J, P, dif_pos hl, sq_abs] using h
  have hprod : (∏ l ∈ Finset.range d, P l ^ (2 ^ (d - 1 - l))) = csFactor d j μ := by
    rw [← Fin.prod_univ_eq_prod_range (fun l => P l ^ (2 ^ (d - 1 - l))) d]
    unfold csFactor
    apply Finset.prod_congr rfl
    intro l _
    simp [P, l.isLt]
  have h := iterated_cauchy_schwarz d (by omega) J P hstep
  obtain ⟨h₀, hd'⟩ := cs_endpoint_identities d hd m hm hdm μ hμ j F
  change |csStage d j μ F 0| ^ (2 ^ d) ≤ csStage d j μ F d * _ at h
  rw [h₀, hd', hprod] at h
  simpa only [mul_comm] using h
