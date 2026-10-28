-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.hPis0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:19:00.940609+00:00
-- url     : https://prove2.me/submissions/2ad0bcc5-955d-41c2-9aad-b76e3295c037
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_hPis0_Dm
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetFB
open IntMul.Kappa.R8.Bit.Oppbank

theorem ptsL_eq_pts (T k : ℕ) : ptsL T k = ProjB.pts T k := rfl

theorem triL_eq_tri (T : ℕ) : triL T = ProjB.tri T := by
  simp only [triL, ProjB.tri, ptsL_eq_pts]

theorem tvQ_eq (T : ℕ) : tvQ T = ProjB.tvQ T := by
  funext p; simp only [tvQ, ProjB.tvQ, triL_eq_tri]

theorem yv_eq (T : ℕ) : yv T = ProjB.yv T := by
  funext p; simp only [yv, ProjB.yv, tvQ_eq]

theorem xv_eq (T : ℕ) : xv T = ProjB.xv T := by
  simp only [xv, ProjB.xv, tvQ_eq]

theorem Pl_eq_ProjB (T : ℕ) : Pl T = ProjB.Pl T := by
  simp only [Pl, ProjB.Pl, xv_eq, yv_eq]

theorem solution : ∀ A ∈ Pis0, A * A = A := by
  intro A hA
  have hA' : A ∈ idxD.image (fun p => Dm p.1 p.2) ∨ A ∈ (range 1771).image Pl := by
    simpa [Pis0, mem_union] using hA
  rcases hA' with hDm | hPl
  · exact hPis0_Dm A hDm
  · obtain ⟨T, hT, rfl⟩ := mem_image.1 hPl
    have hT' : T < 1771 := mem_range.1 hT
    have h := Pl_idem (T := T) hT'
    simpa [Pl_eq_ProjB] using h
