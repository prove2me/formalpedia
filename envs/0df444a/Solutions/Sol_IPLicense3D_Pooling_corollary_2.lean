-- Prove2me | solution 1 for IPLicense3D.Pooling.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:28:00.163503+00:00
-- url     : https://prove2.me/submissions/7e9ebb53-4ff4-49c8-bd8a-f32c657113c3

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

open IPLicense3D.Pooling
open Model in
theorem solution {n : ℕ} (M : Model n) (hM : M.Standing) (i : Fin n) (f r : ℝ)
    (hf : 0 ≤ f) (hr : 0 ≤ r) :
    M.profitA i f r + M.surplus i f r ≤ M.maxSurplus i := by
  obtain ⟨hh, hw, hp, hkA, _, hlA, _, hz, hlam⟩ := hM
  have hli := hlam i
  unfold Model.profitA Model.maxSurplus Model.surplus Model.surplusL surplusF costAF
  have hX : 0 ≤ M.lam i * M.ellA + M.z * Real.sqrt (M.lam i * M.ellA) := by positivity
  have hsq : Real.sqrt (2 * M.h * (0 + M.p) * M.lam i * M.kA) ≤
      Real.sqrt (2 * M.h * (r + M.p) * M.lam i * M.kA) := by
    apply Real.sqrt_le_sqrt
    have : 0 ≤ 2 * M.h * M.lam i * M.kA := by positivity
    nlinarith
  have hrX : 0 ≤ M.h * r * (M.lam i * M.ellA + M.z * Real.sqrt (M.lam i * M.ellA)) := by
    positivity
  nlinarith
