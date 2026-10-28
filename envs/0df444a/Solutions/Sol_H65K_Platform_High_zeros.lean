-- Prove2me | solution 1 for H65K.Platform.High.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:24:17.359315+00:00
-- url     : https://prove2.me/submissions/221a34f0-f252-4491-9f5d-801e3d98dfca

import Theorems.Thm_H65K_Platform_HighGroup000_zeros
import Theorems.Thm_H65K_Platform_HighGroup001_zeros
import Theorems.Thm_H65K_Platform_HighGroup002_zeros
import Theorems.Thm_H65K_Platform_HighGroup003_zeros
import Theorems.Thm_H65K_Platform_HighGroup004_zeros
import Theorems.Thm_H65K_Platform_HighGroup005_zeros
import Theorems.Thm_H65K_Platform_HighGroup006_zeros
import Theorems.Thm_H65K_Platform_HighGroup007_zeros
import Theorems.Thm_H65K_Platform_HighGroup008_zeros
import Theorems.Thm_H65K_Platform_HighGroup009_zeros
import Theorems.Thm_H65K_Platform_HighGroup010_zeros
import Theorems.Thm_H65K_Platform_HighGroup011_zeros
import Theorems.Thm_H65K_Platform_HighGroup012_zeros
import Theorems.Thm_H65K_Platform_HighGroup013_zeros
import Theorems.Thm_H65K_Platform_HighGroup014_zeros
import Theorems.Thm_H65K_Platform_HighGroup015_zeros
import Theorems.Thm_H65K_Platform_HighGroup016_zeros
import Theorems.Thm_H65K_Platform_HighGroup017_zeros
import Theorems.Thm_H65K_Platform_HighGroup018_zeros
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution : RS5.BandZeros ((721160233 : ℝ) / 65536) ((4259840000 : ℝ) / 65536) 73959 := by
  have h0 := H65K.Platform.HighGroup000.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup001.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup002.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup003.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup004.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup005.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup006.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup007.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup008.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup009.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup010.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup011.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup012.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup013.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup014.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup015.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup016.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup017.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K.Platform.HighGroup018.zeros
  exact h18
