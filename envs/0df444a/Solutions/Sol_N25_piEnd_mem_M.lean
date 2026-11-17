-- Prove2me | solution 1 for N25.piEnd_mem_M
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:08.265971+00:00
-- url     : https://prove2.me/submissions/cb53fb0e-bd6e-4864-a0fd-0700ab482c1b

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm

set_option autoImplicit false

noncomputable section

namespace N25

private theorem gamma_mem_fixed {x : N25.J} (hx : x ∈ N25.M) : N25.gamma x ∈ N25.M := by
  change ∀ σ : N25.Gal, σ • x = x at hx
  change ∀ σ : N25.Gal, σ • N25.gamma x = N25.gamma x
  intro σ
  have h := ModularCurve.galois_smul_genOpH_comm 25 N25.H25 (∅ : Set ℕ) σ
    (.dia (ZMod.unitOfCoprime 13 (by decide))) x
  change σ • N25.gamma x = N25.gamma (σ • x) at h
  rw [h, hx σ]

/-- The norm polynomial in the diamond operator preserves arithmetic fixed points. -/
theorem _root_.solution {x : N25.J} (hx : x ∈ N25.M) : N25.piEnd x ∈ N25.M := by
  have hg : N25.gamma x ∈ N25.M := gamma_mem_fixed hx
  have hgg : N25.gamma (N25.gamma x) ∈ N25.M := gamma_mem_fixed hg
  change 2 • x + 4 • N25.gamma x + N25.gamma (N25.gamma x) ∈ N25.M
  exact N25.M.add_mem (N25.M.add_mem (N25.M.nsmul_mem hx 2) (N25.M.nsmul_mem hg 4)) hgg

end N25
