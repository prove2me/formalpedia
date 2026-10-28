-- Prove2me | solution 1 for H65K.Edge.hAH
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:42:30.799649+00:00
-- url     : https://prove2.me/submissions/21b1987c-0d4d-4490-ad1e-ec067e56cdf4

import Theorems.Thm_H65K_Edge_piece00
import Theorems.Thm_H65K_Edge_piece01
import Theorems.Thm_H65K_Edge_piece02
import Theorems.Thm_H65K_Edge_piece03
import Theorems.Thm_H65K_Edge_piece04
import Theorems.Thm_H65K_Edge_piece05
import Theorems.Thm_H65K_Edge_piece06
import Theorems.Thm_H65K_Edge_piece07
import Theorems.Thm_H65K_Edge_piece08
import Theorems.Thm_H65K_Edge_piece09
import Theorems.Thm_H65K_Edge_piece10
import Theorems.Thm_H65K_Edge_piece11
import Theorems.Thm_H65K_Edge_piece12
import Theorems.Thm_H65K_Edge_piece13
import Theorems.Thm_H65K_Edge_piece14
import Theorems.Thm_H65K_Edge_piece15
import Theorems.Thm_H65K_Edge_piece16
import Theorems.Thm_H65K_Edge_piece17
import Theorems.Thm_H65K_Edge_piece18
import Theorems.Thm_H65K_Edge_piece19
import Theorems.Thm_H65K_Edge_piece20
import Theorems.Thm_H65K_Edge_piece21
import Theorems.Thm_H65K_Edge_piece22
import Theorems.Thm_H65K_Edge_piece23
import Theorems.Thm_H65K_Edge_piece24
import Theorems.Thm_H65K_Edge_piece25
import Theorems.Thm_H65K_Edge_piece26
import Theorems.Thm_H65K_Edge_piece27
import Theorems.Thm_H65K_Edge_piece28
import Theorems.Thm_H65K_Edge_piece29
import Theorems.Thm_H65K_Edge_piece30
import Theorems.Thm_H65K_Edge_piece31
import Theorems.Thm_H65K_Edge_piece32
import Theorems.Thm_H65K_Edge_piece33
import Theorems.Thm_H65K_Edge_piece34
import Theorems.Thm_H65K_Edge_piece35
import Theorems.Thm_H65K_Edge_piece36
import Theorems.Thm_H65K_Edge_piece37
import Theorems.Thm_H65K_Edge_piece38
import Theorems.Thm_H65K_Edge_piece39
import Theorems.Thm_H65K_Edge_piece40
import Theorems.Thm_H65K_Edge_restHead
import Theorems.Thm_H65K_Edge_restBox0
import Theorems.Thm_H65K_Edge_restBox1
import Theorems.Thm_H65K_Edge_restTailLo
import Theorems.Thm_H65K_Edge_restTailHi
import Theorems.Thm_H11K_edge_sound_of_split
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem solution :
    DiffractionCore.argChangeHoriz riemannZeta (65000 : ℝ) 2 (-1) ∈
      Set.Icc H65K.Edge.E.Lo.val H65K.Edge.E.Hi.val := by
  have hrest : H11K.edgeRest H65K.Edge.E = true := by
    unfold H11K.edgeRest
    simpa only [H65K.Edge.restBox0, H65K.Edge.restBox1, H65K.Edge.restTailLo,
      H65K.Edge.restTailHi, Bool.and_true] using H65K.Edge.restHead
  have hpieces : ∀ j, j < H65K.Edge.E.m → H11K.pieceJ H65K.Edge.E j = true := by
    intro j hj
    have hm : H65K.Edge.E.m = 41 := rfl
    rw [hm] at hj
    interval_cases j
    · exact H65K.Edge.piece00
    · exact H65K.Edge.piece01
    · exact H65K.Edge.piece02
    · exact H65K.Edge.piece03
    · exact H65K.Edge.piece04
    · exact H65K.Edge.piece05
    · exact H65K.Edge.piece06
    · exact H65K.Edge.piece07
    · exact H65K.Edge.piece08
    · exact H65K.Edge.piece09
    · exact H65K.Edge.piece10
    · exact H65K.Edge.piece11
    · exact H65K.Edge.piece12
    · exact H65K.Edge.piece13
    · exact H65K.Edge.piece14
    · exact H65K.Edge.piece15
    · exact H65K.Edge.piece16
    · exact H65K.Edge.piece17
    · exact H65K.Edge.piece18
    · exact H65K.Edge.piece19
    · exact H65K.Edge.piece20
    · exact H65K.Edge.piece21
    · exact H65K.Edge.piece22
    · exact H65K.Edge.piece23
    · exact H65K.Edge.piece24
    · exact H65K.Edge.piece25
    · exact H65K.Edge.piece26
    · exact H65K.Edge.piece27
    · exact H65K.Edge.piece28
    · exact H65K.Edge.piece29
    · exact H65K.Edge.piece30
    · exact H65K.Edge.piece31
    · exact H65K.Edge.piece32
    · exact H65K.Edge.piece33
    · exact H65K.Edge.piece34
    · exact H65K.Edge.piece35
    · exact H65K.Edge.piece36
    · exact H65K.Edge.piece37
    · exact H65K.Edge.piece38
    · exact H65K.Edge.piece39
    · exact H65K.Edge.piece40
  have h := H11K.edge_sound_of_split H65K.Edge.E hrest hpieces
  have hT : H65K.Edge.E.T = (65000 : ℝ) := by
    show ((65000 : ℕ) : ℝ) / 2 ^ (0 : ℕ) = (65000 : ℝ)
    norm_num
  rw [hT] at h
  exact h
