-- Prove2me | solution 1 for KramerSaglam.lemma_3_12
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:57:21.669286+00:00
-- url     : https://prove2.me/submissions/402eac97-8ddf-4b9d-9dc4-bcff69ed0c83

import Mathlib
import Definitions.Def_KramerSaglam_TailSeries

open KramerSaglam Finset

noncomputable def KSx_P (w : ℝ) : ℝ :=
  55 / 72 + 9 / 8 * w ^ 8 + 38 * (w ^ 5 / 30 + w ^ 7 / 56 + w ^ 9 / 90 + w ^ 11 / 132 + w ^ 13 / 182 + w ^ 15 / 240 + w ^ 17 / 306 + w ^ 19 / 380 + w ^ 21 / 462 + w ^ 23 / 552 + w ^ 25 / 650 + w ^ 27 / 756 + w ^ 29 / 870 + w ^ 31 / 992)

noncomputable def KSx_N (w : ℝ) : ℝ := 31 / 8 * w ^ 4 + 1 / 8 * w ^ 12

lemma KSx_intv (a b : ℝ) (ha : 0 ≤ a) (hab : KSx_N b < KSx_P a) (w : ℝ) (h1 : a ≤ w)
    (h2 : w ≤ b) : 0 < KSx_P w - KSx_N w := by
  have hP : KSx_P a ≤ KSx_P w := by unfold KSx_P; gcongr
  have hw : 0 ≤ w := le_trans ha h1
  have hN : KSx_N w ≤ KSx_N b := by unfold KSx_N; gcongr
  linarith

lemma KSx_poly (w : ℝ) (h0 : 0 < w) (h1 : w ≤ 1) : 0 < KSx_P w - KSx_N w := by
  rcases le_or_gt w (3330 / 5000 : ℝ) with hhi | hlo1
  · exact KSx_intv 0 (3330 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w h0.le hhi
  rcases le_or_gt w (3586 / 5000 : ℝ) with hhi | hlo2
  · exact KSx_intv (3330 / 5000 : ℝ) (3586 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo1.le hhi
  rcases le_or_gt w (3713 / 5000 : ℝ) with hhi | hlo3
  · exact KSx_intv (3586 / 5000 : ℝ) (3713 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo2.le hhi
  rcases le_or_gt w (3791 / 5000 : ℝ) with hhi | hlo4
  · exact KSx_intv (3713 / 5000 : ℝ) (3791 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo3.le hhi
  rcases le_or_gt w (3845 / 5000 : ℝ) with hhi | hlo5
  · exact KSx_intv (3791 / 5000 : ℝ) (3845 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo4.le hhi
  rcases le_or_gt w (3885 / 5000 : ℝ) with hhi | hlo6
  · exact KSx_intv (3845 / 5000 : ℝ) (3885 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo5.le hhi
  rcases le_or_gt w (3915 / 5000 : ℝ) with hhi | hlo7
  · exact KSx_intv (3885 / 5000 : ℝ) (3915 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo6.le hhi
  rcases le_or_gt w (3939 / 5000 : ℝ) with hhi | hlo8
  · exact KSx_intv (3915 / 5000 : ℝ) (3939 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo7.le hhi
  rcases le_or_gt w (3959 / 5000 : ℝ) with hhi | hlo9
  · exact KSx_intv (3939 / 5000 : ℝ) (3959 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo8.le hhi
  rcases le_or_gt w (3976 / 5000 : ℝ) with hhi | hlo10
  · exact KSx_intv (3959 / 5000 : ℝ) (3976 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo9.le hhi
  rcases le_or_gt w (3990 / 5000 : ℝ) with hhi | hlo11
  · exact KSx_intv (3976 / 5000 : ℝ) (3990 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo10.le hhi
  rcases le_or_gt w (4002 / 5000 : ℝ) with hhi | hlo12
  · exact KSx_intv (3990 / 5000 : ℝ) (4002 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo11.le hhi
  rcases le_or_gt w (4013 / 5000 : ℝ) with hhi | hlo13
  · exact KSx_intv (4002 / 5000 : ℝ) (4013 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo12.le hhi
  rcases le_or_gt w (4022 / 5000 : ℝ) with hhi | hlo14
  · exact KSx_intv (4013 / 5000 : ℝ) (4022 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo13.le hhi
  rcases le_or_gt w (4030 / 5000 : ℝ) with hhi | hlo15
  · exact KSx_intv (4022 / 5000 : ℝ) (4030 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo14.le hhi
  rcases le_or_gt w (4038 / 5000 : ℝ) with hhi | hlo16
  · exact KSx_intv (4030 / 5000 : ℝ) (4038 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo15.le hhi
  rcases le_or_gt w (4045 / 5000 : ℝ) with hhi | hlo17
  · exact KSx_intv (4038 / 5000 : ℝ) (4045 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo16.le hhi
  rcases le_or_gt w (4051 / 5000 : ℝ) with hhi | hlo18
  · exact KSx_intv (4045 / 5000 : ℝ) (4051 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo17.le hhi
  rcases le_or_gt w (4057 / 5000 : ℝ) with hhi | hlo19
  · exact KSx_intv (4051 / 5000 : ℝ) (4057 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo18.le hhi
  rcases le_or_gt w (4062 / 5000 : ℝ) with hhi | hlo20
  · exact KSx_intv (4057 / 5000 : ℝ) (4062 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo19.le hhi
  rcases le_or_gt w (4067 / 5000 : ℝ) with hhi | hlo21
  · exact KSx_intv (4062 / 5000 : ℝ) (4067 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo20.le hhi
  rcases le_or_gt w (4072 / 5000 : ℝ) with hhi | hlo22
  · exact KSx_intv (4067 / 5000 : ℝ) (4072 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo21.le hhi
  rcases le_or_gt w (4076 / 5000 : ℝ) with hhi | hlo23
  · exact KSx_intv (4072 / 5000 : ℝ) (4076 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo22.le hhi
  rcases le_or_gt w (4080 / 5000 : ℝ) with hhi | hlo24
  · exact KSx_intv (4076 / 5000 : ℝ) (4080 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo23.le hhi
  rcases le_or_gt w (4084 / 5000 : ℝ) with hhi | hlo25
  · exact KSx_intv (4080 / 5000 : ℝ) (4084 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo24.le hhi
  rcases le_or_gt w (4087 / 5000 : ℝ) with hhi | hlo26
  · exact KSx_intv (4084 / 5000 : ℝ) (4087 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo25.le hhi
  rcases le_or_gt w (4090 / 5000 : ℝ) with hhi | hlo27
  · exact KSx_intv (4087 / 5000 : ℝ) (4090 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo26.le hhi
  rcases le_or_gt w (4093 / 5000 : ℝ) with hhi | hlo28
  · exact KSx_intv (4090 / 5000 : ℝ) (4093 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo27.le hhi
  rcases le_or_gt w (4096 / 5000 : ℝ) with hhi | hlo29
  · exact KSx_intv (4093 / 5000 : ℝ) (4096 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo28.le hhi
  rcases le_or_gt w (4099 / 5000 : ℝ) with hhi | hlo30
  · exact KSx_intv (4096 / 5000 : ℝ) (4099 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo29.le hhi
  rcases le_or_gt w (4102 / 5000 : ℝ) with hhi | hlo31
  · exact KSx_intv (4099 / 5000 : ℝ) (4102 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo30.le hhi
  rcases le_or_gt w (4105 / 5000 : ℝ) with hhi | hlo32
  · exact KSx_intv (4102 / 5000 : ℝ) (4105 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo31.le hhi
  rcases le_or_gt w (4108 / 5000 : ℝ) with hhi | hlo33
  · exact KSx_intv (4105 / 5000 : ℝ) (4108 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo32.le hhi
  rcases le_or_gt w (4110 / 5000 : ℝ) with hhi | hlo34
  · exact KSx_intv (4108 / 5000 : ℝ) (4110 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo33.le hhi
  rcases le_or_gt w (4112 / 5000 : ℝ) with hhi | hlo35
  · exact KSx_intv (4110 / 5000 : ℝ) (4112 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo34.le hhi
  rcases le_or_gt w (4114 / 5000 : ℝ) with hhi | hlo36
  · exact KSx_intv (4112 / 5000 : ℝ) (4114 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo35.le hhi
  rcases le_or_gt w (4116 / 5000 : ℝ) with hhi | hlo37
  · exact KSx_intv (4114 / 5000 : ℝ) (4116 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo36.le hhi
  rcases le_or_gt w (4118 / 5000 : ℝ) with hhi | hlo38
  · exact KSx_intv (4116 / 5000 : ℝ) (4118 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo37.le hhi
  rcases le_or_gt w (4120 / 5000 : ℝ) with hhi | hlo39
  · exact KSx_intv (4118 / 5000 : ℝ) (4120 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo38.le hhi
  rcases le_or_gt w (4122 / 5000 : ℝ) with hhi | hlo40
  · exact KSx_intv (4120 / 5000 : ℝ) (4122 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo39.le hhi
  rcases le_or_gt w (4124 / 5000 : ℝ) with hhi | hlo41
  · exact KSx_intv (4122 / 5000 : ℝ) (4124 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo40.le hhi
  rcases le_or_gt w (4126 / 5000 : ℝ) with hhi | hlo42
  · exact KSx_intv (4124 / 5000 : ℝ) (4126 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo41.le hhi
  rcases le_or_gt w (4128 / 5000 : ℝ) with hhi | hlo43
  · exact KSx_intv (4126 / 5000 : ℝ) (4128 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo42.le hhi
  rcases le_or_gt w (4130 / 5000 : ℝ) with hhi | hlo44
  · exact KSx_intv (4128 / 5000 : ℝ) (4130 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo43.le hhi
  rcases le_or_gt w (4132 / 5000 : ℝ) with hhi | hlo45
  · exact KSx_intv (4130 / 5000 : ℝ) (4132 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo44.le hhi
  rcases le_or_gt w (4134 / 5000 : ℝ) with hhi | hlo46
  · exact KSx_intv (4132 / 5000 : ℝ) (4134 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo45.le hhi
  rcases le_or_gt w (4136 / 5000 : ℝ) with hhi | hlo47
  · exact KSx_intv (4134 / 5000 : ℝ) (4136 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo46.le hhi
  rcases le_or_gt w (4138 / 5000 : ℝ) with hhi | hlo48
  · exact KSx_intv (4136 / 5000 : ℝ) (4138 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo47.le hhi
  rcases le_or_gt w (4140 / 5000 : ℝ) with hhi | hlo49
  · exact KSx_intv (4138 / 5000 : ℝ) (4140 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo48.le hhi
  rcases le_or_gt w (4142 / 5000 : ℝ) with hhi | hlo50
  · exact KSx_intv (4140 / 5000 : ℝ) (4142 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo49.le hhi
  rcases le_or_gt w (4144 / 5000 : ℝ) with hhi | hlo51
  · exact KSx_intv (4142 / 5000 : ℝ) (4144 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo50.le hhi
  rcases le_or_gt w (4146 / 5000 : ℝ) with hhi | hlo52
  · exact KSx_intv (4144 / 5000 : ℝ) (4146 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo51.le hhi
  rcases le_or_gt w (4148 / 5000 : ℝ) with hhi | hlo53
  · exact KSx_intv (4146 / 5000 : ℝ) (4148 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo52.le hhi
  rcases le_or_gt w (4150 / 5000 : ℝ) with hhi | hlo54
  · exact KSx_intv (4148 / 5000 : ℝ) (4150 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo53.le hhi
  rcases le_or_gt w (4152 / 5000 : ℝ) with hhi | hlo55
  · exact KSx_intv (4150 / 5000 : ℝ) (4152 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo54.le hhi
  rcases le_or_gt w (4154 / 5000 : ℝ) with hhi | hlo56
  · exact KSx_intv (4152 / 5000 : ℝ) (4154 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo55.le hhi
  rcases le_or_gt w (4156 / 5000 : ℝ) with hhi | hlo57
  · exact KSx_intv (4154 / 5000 : ℝ) (4156 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo56.le hhi
  rcases le_or_gt w (4158 / 5000 : ℝ) with hhi | hlo58
  · exact KSx_intv (4156 / 5000 : ℝ) (4158 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo57.le hhi
  rcases le_or_gt w (4160 / 5000 : ℝ) with hhi | hlo59
  · exact KSx_intv (4158 / 5000 : ℝ) (4160 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo58.le hhi
  rcases le_or_gt w (4162 / 5000 : ℝ) with hhi | hlo60
  · exact KSx_intv (4160 / 5000 : ℝ) (4162 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo59.le hhi
  rcases le_or_gt w (4164 / 5000 : ℝ) with hhi | hlo61
  · exact KSx_intv (4162 / 5000 : ℝ) (4164 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo60.le hhi
  rcases le_or_gt w (4166 / 5000 : ℝ) with hhi | hlo62
  · exact KSx_intv (4164 / 5000 : ℝ) (4166 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo61.le hhi
  rcases le_or_gt w (4168 / 5000 : ℝ) with hhi | hlo63
  · exact KSx_intv (4166 / 5000 : ℝ) (4168 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo62.le hhi
  rcases le_or_gt w (4170 / 5000 : ℝ) with hhi | hlo64
  · exact KSx_intv (4168 / 5000 : ℝ) (4170 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo63.le hhi
  rcases le_or_gt w (4172 / 5000 : ℝ) with hhi | hlo65
  · exact KSx_intv (4170 / 5000 : ℝ) (4172 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo64.le hhi
  rcases le_or_gt w (4174 / 5000 : ℝ) with hhi | hlo66
  · exact KSx_intv (4172 / 5000 : ℝ) (4174 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo65.le hhi
  rcases le_or_gt w (4176 / 5000 : ℝ) with hhi | hlo67
  · exact KSx_intv (4174 / 5000 : ℝ) (4176 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo66.le hhi
  rcases le_or_gt w (4178 / 5000 : ℝ) with hhi | hlo68
  · exact KSx_intv (4176 / 5000 : ℝ) (4178 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo67.le hhi
  rcases le_or_gt w (4180 / 5000 : ℝ) with hhi | hlo69
  · exact KSx_intv (4178 / 5000 : ℝ) (4180 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo68.le hhi
  rcases le_or_gt w (4182 / 5000 : ℝ) with hhi | hlo70
  · exact KSx_intv (4180 / 5000 : ℝ) (4182 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo69.le hhi
  rcases le_or_gt w (4184 / 5000 : ℝ) with hhi | hlo71
  · exact KSx_intv (4182 / 5000 : ℝ) (4184 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo70.le hhi
  rcases le_or_gt w (4186 / 5000 : ℝ) with hhi | hlo72
  · exact KSx_intv (4184 / 5000 : ℝ) (4186 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo71.le hhi
  rcases le_or_gt w (4188 / 5000 : ℝ) with hhi | hlo73
  · exact KSx_intv (4186 / 5000 : ℝ) (4188 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo72.le hhi
  rcases le_or_gt w (4190 / 5000 : ℝ) with hhi | hlo74
  · exact KSx_intv (4188 / 5000 : ℝ) (4190 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo73.le hhi
  rcases le_or_gt w (4193 / 5000 : ℝ) with hhi | hlo75
  · exact KSx_intv (4190 / 5000 : ℝ) (4193 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo74.le hhi
  rcases le_or_gt w (4196 / 5000 : ℝ) with hhi | hlo76
  · exact KSx_intv (4193 / 5000 : ℝ) (4196 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo75.le hhi
  rcases le_or_gt w (4199 / 5000 : ℝ) with hhi | hlo77
  · exact KSx_intv (4196 / 5000 : ℝ) (4199 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo76.le hhi
  rcases le_or_gt w (4202 / 5000 : ℝ) with hhi | hlo78
  · exact KSx_intv (4199 / 5000 : ℝ) (4202 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo77.le hhi
  rcases le_or_gt w (4205 / 5000 : ℝ) with hhi | hlo79
  · exact KSx_intv (4202 / 5000 : ℝ) (4205 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo78.le hhi
  rcases le_or_gt w (4208 / 5000 : ℝ) with hhi | hlo80
  · exact KSx_intv (4205 / 5000 : ℝ) (4208 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo79.le hhi
  rcases le_or_gt w (4211 / 5000 : ℝ) with hhi | hlo81
  · exact KSx_intv (4208 / 5000 : ℝ) (4211 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo80.le hhi
  rcases le_or_gt w (4215 / 5000 : ℝ) with hhi | hlo82
  · exact KSx_intv (4211 / 5000 : ℝ) (4215 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo81.le hhi
  rcases le_or_gt w (4219 / 5000 : ℝ) with hhi | hlo83
  · exact KSx_intv (4215 / 5000 : ℝ) (4219 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo82.le hhi
  rcases le_or_gt w (4223 / 5000 : ℝ) with hhi | hlo84
  · exact KSx_intv (4219 / 5000 : ℝ) (4223 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo83.le hhi
  rcases le_or_gt w (4227 / 5000 : ℝ) with hhi | hlo85
  · exact KSx_intv (4223 / 5000 : ℝ) (4227 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo84.le hhi
  rcases le_or_gt w (4232 / 5000 : ℝ) with hhi | hlo86
  · exact KSx_intv (4227 / 5000 : ℝ) (4232 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo85.le hhi
  rcases le_or_gt w (4237 / 5000 : ℝ) with hhi | hlo87
  · exact KSx_intv (4232 / 5000 : ℝ) (4237 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo86.le hhi
  rcases le_or_gt w (4242 / 5000 : ℝ) with hhi | hlo88
  · exact KSx_intv (4237 / 5000 : ℝ) (4242 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo87.le hhi
  rcases le_or_gt w (4248 / 5000 : ℝ) with hhi | hlo89
  · exact KSx_intv (4242 / 5000 : ℝ) (4248 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo88.le hhi
  rcases le_or_gt w (4254 / 5000 : ℝ) with hhi | hlo90
  · exact KSx_intv (4248 / 5000 : ℝ) (4254 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo89.le hhi
  rcases le_or_gt w (4261 / 5000 : ℝ) with hhi | hlo91
  · exact KSx_intv (4254 / 5000 : ℝ) (4261 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo90.le hhi
  rcases le_or_gt w (4268 / 5000 : ℝ) with hhi | hlo92
  · exact KSx_intv (4261 / 5000 : ℝ) (4268 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo91.le hhi
  rcases le_or_gt w (4276 / 5000 : ℝ) with hhi | hlo93
  · exact KSx_intv (4268 / 5000 : ℝ) (4276 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo92.le hhi
  rcases le_or_gt w (4285 / 5000 : ℝ) with hhi | hlo94
  · exact KSx_intv (4276 / 5000 : ℝ) (4285 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo93.le hhi
  rcases le_or_gt w (4295 / 5000 : ℝ) with hhi | hlo95
  · exact KSx_intv (4285 / 5000 : ℝ) (4295 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo94.le hhi
  rcases le_or_gt w (4306 / 5000 : ℝ) with hhi | hlo96
  · exact KSx_intv (4295 / 5000 : ℝ) (4306 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo95.le hhi
  rcases le_or_gt w (4319 / 5000 : ℝ) with hhi | hlo97
  · exact KSx_intv (4306 / 5000 : ℝ) (4319 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo96.le hhi
  rcases le_or_gt w (4334 / 5000 : ℝ) with hhi | hlo98
  · exact KSx_intv (4319 / 5000 : ℝ) (4334 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo97.le hhi
  rcases le_or_gt w (4351 / 5000 : ℝ) with hhi | hlo99
  · exact KSx_intv (4334 / 5000 : ℝ) (4351 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo98.le hhi
  rcases le_or_gt w (4371 / 5000 : ℝ) with hhi | hlo100
  · exact KSx_intv (4351 / 5000 : ℝ) (4371 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo99.le hhi
  rcases le_or_gt w (4395 / 5000 : ℝ) with hhi | hlo101
  · exact KSx_intv (4371 / 5000 : ℝ) (4395 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo100.le hhi
  rcases le_or_gt w (4424 / 5000 : ℝ) with hhi | hlo102
  · exact KSx_intv (4395 / 5000 : ℝ) (4424 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo101.le hhi
  rcases le_or_gt w (4460 / 5000 : ℝ) with hhi | hlo103
  · exact KSx_intv (4424 / 5000 : ℝ) (4460 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo102.le hhi
  rcases le_or_gt w (4506 / 5000 : ℝ) with hhi | hlo104
  · exact KSx_intv (4460 / 5000 : ℝ) (4506 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo103.le hhi
  rcases le_or_gt w (4567 / 5000 : ℝ) with hhi | hlo105
  · exact KSx_intv (4506 / 5000 : ℝ) (4567 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo104.le hhi
  rcases le_or_gt w (4650 / 5000 : ℝ) with hhi | hlo106
  · exact KSx_intv (4567 / 5000 : ℝ) (4650 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo105.le hhi
  rcases le_or_gt w (4771 / 5000 : ℝ) with hhi | hlo107
  · exact KSx_intv (4650 / 5000 : ℝ) (4771 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo106.le hhi
  rcases le_or_gt w (4961 / 5000 : ℝ) with hhi | hlo108
  · exact KSx_intv (4771 / 5000 : ℝ) (4961 / 5000 : ℝ) (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo107.le hhi
  exact KSx_intv (4961 / 5000 : ℝ) 1 (by norm_num) (by norm_num [KSx_P, KSx_N]) w hlo108.le h1

lemma KSx_tt (n : ℕ) (hn : 1 ≤ n) : 0 ≤ tailTerm n ∧ tailTerm n ≤ 1 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  unfold tailTerm
  have hpos : (1:ℝ) ≤ 2 * (n:ℝ) * (2 * (n:ℝ) - 1) := by nlinarith
  constructor
  · apply div_nonneg zero_le_one; linarith
  · rw [div_le_one (by linarith)]; exact hpos

lemma KSx_s_lower (w : ℝ) (h0 : 0 < w) (h1 : w < 1) :
    ∑ k ∈ range 14, w ^ (2 * (2 + 1 + k)) * tailTerm (2 + 1 + k) ≤ s 2 w := by
  unfold s
  have hnn : ∀ k : ℕ, 0 ≤ w ^ (2 * (2 + 1 + k)) * tailTerm (2 + 1 + k) := fun k =>
    mul_nonneg (pow_nonneg h0.le _) (KSx_tt _ (by omega)).1
  have hsum : Summable (fun k : ℕ => w ^ (2 * (2 + 1 + k)) * tailTerm (2 + 1 + k)) := by
    refine Summable.of_nonneg_of_le hnn (fun k => ?_)
      (summable_geometric_of_lt_one (sq_nonneg w) (by nlinarith))
    calc w ^ (2 * (2 + 1 + k)) * tailTerm (2 + 1 + k) ≤ w ^ (2 * (2 + 1 + k)) * 1 :=
          mul_le_mul_of_nonneg_left (KSx_tt _ (by omega)).2 (pow_nonneg h0.le _)
      _ ≤ w ^ (2 * k) := by
          rw [mul_one]; exact pow_le_pow_of_le_one h0.le h1.le (by omega)
      _ = (w ^ 2) ^ k := by rw [pow_mul]
  exact hsum.sum_le_tsum _ (fun i _ => hnn i)

theorem solution (w : ℝ) (h0 : 0 < w) (h1 : w < 1) : JJ w > 0 := by
  have hs := KSx_s_lower w h0 h1
  have hP := KSx_poly w h0 h1.le
  have e : KSx_P w - KSx_N w = 55 / 72 - 31 * w ^ 4 / 8 + 9 * w ^ 8 / 8 - w ^ 12 / 8 +
      38 * (∑ k ∈ range 14, w ^ (2 * (2 + 1 + k)) * tailTerm (2 + 1 + k)) / w := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, tailTerm, KSx_P, KSx_N]
    push_cast
    field_simp
    ring
  have hd : 38 * (∑ k ∈ range 14, w ^ (2 * (2 + 1 + k)) * tailTerm (2 + 1 + k)) / w ≤
      38 * s 2 w / w := by gcongr
  unfold JJ
  linarith
