-- Prove2me | solution 1 for MasulloRH.quarter_shift_rational_energy_score
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:34.088814+00:00
-- url     : https://prove2.me/submissions/a62b4978-42b4-4c0e-8423-fa0128ef993b

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates
import Mathlib.Tactic.IntervalCases

open MasulloRH.ThetaDerivativeCertificate
set_option maxRecDepth 160000
set_option maxHeartbeats 10000000

private def ticks : Array ℕ := #[
  1,1,1,1,1,1,1,1,1,1,1,1,1,1,
  1,1,1,1,1,1,1,1,1,1,1,1,1,1,
  1,1,1,1,1,1,1,1,1,1,1,1,1,1,
  1,1,1,1,2,5,11,25,49,86,129,163,174,178,
  142,82,31,5,8,10,11,10,10,12,14,13,7,32,
  73,91,110,80,121,244,390,537,633,868,1260,1770,2274,3309,
  4620,7278,9868,13041,16933,23139,30362,39764,52078,67808,85745,107576,127678,159584,
  191342,232305,256592,308736,364067,428796,443798,513105,582443,646508,625946,696818,760364,817722,
  798831,904952,998293,1106437,1026461,1109960,1185809,1263111,1098594,1124674,1137205,1163493,1005153,997034,
  971243,940381,801618,728768,682962,640442,538644,466527,421459,373045,301758,256687,221623,190188,
  153876,126804,95405,74716,63213,50197,35736,29032,22513,15523,11493,7970,6740,5317,
  4047,2127,1700,1234,646,511,606,653,587,436,227,102,126,229,
  300,324,296,139,116,203,227,167,207,653,1168,1429,1605,1564,
  1176,749,528,312,140,101,59,66,74,83,94,106,120,136,
  154,174,198,224,254,287,326,369,418,473,536,608,689,780,
  884,1002,1135,1286,1457,1651,1871,2120,2402,2722,3084,3495,3960,4487]
private def upper (n : ℕ) : ℚ := (ticks[n]!:ℚ)/1000000000000000000
private def within (n : ℕ) : Bool := decide (cellCost ((n:ℤ)-112) ≤ upper n)
private theorem band0 : (List.range 4).all (fun m => within (m+0)) = true := by decide +kernel
private theorem band4 : (List.range 4).all (fun m => within (m+4)) = true := by decide +kernel
private theorem band8 : (List.range 4).all (fun m => within (m+8)) = true := by decide +kernel
private theorem band12 : (List.range 4).all (fun m => within (m+12)) = true := by decide +kernel
private theorem band16 : (List.range 4).all (fun m => within (m+16)) = true := by decide +kernel
private theorem band20 : (List.range 4).all (fun m => within (m+20)) = true := by decide +kernel
private theorem band24 : (List.range 4).all (fun m => within (m+24)) = true := by decide +kernel
private theorem band28 : (List.range 4).all (fun m => within (m+28)) = true := by decide +kernel
private theorem band32 : (List.range 4).all (fun m => within (m+32)) = true := by decide +kernel
private theorem band36 : (List.range 4).all (fun m => within (m+36)) = true := by decide +kernel
private theorem band40 : (List.range 4).all (fun m => within (m+40)) = true := by decide +kernel
private theorem band44 : (List.range 4).all (fun m => within (m+44)) = true := by decide +kernel
private theorem band48 : (List.range 4).all (fun m => within (m+48)) = true := by decide +kernel
private theorem band52 : (List.range 4).all (fun m => within (m+52)) = true := by decide +kernel
private theorem band56 : (List.range 4).all (fun m => within (m+56)) = true := by decide +kernel
private theorem band60 : (List.range 4).all (fun m => within (m+60)) = true := by decide +kernel
private theorem band64 : (List.range 4).all (fun m => within (m+64)) = true := by decide +kernel
private theorem band68 : (List.range 4).all (fun m => within (m+68)) = true := by decide +kernel
private theorem band72 : (List.range 4).all (fun m => within (m+72)) = true := by decide +kernel
private theorem band76 : (List.range 4).all (fun m => within (m+76)) = true := by decide +kernel
private theorem band80 : (List.range 4).all (fun m => within (m+80)) = true := by decide +kernel
private theorem band84 : (List.range 4).all (fun m => within (m+84)) = true := by decide +kernel
private theorem band88 : (List.range 4).all (fun m => within (m+88)) = true := by decide +kernel
private theorem band92 : (List.range 4).all (fun m => within (m+92)) = true := by decide +kernel
private theorem band96 : (List.range 4).all (fun m => within (m+96)) = true := by decide +kernel
private theorem band100 : (List.range 4).all (fun m => within (m+100)) = true := by decide +kernel
private theorem band104 : (List.range 4).all (fun m => within (m+104)) = true := by decide +kernel
private theorem band108 : (List.range 4).all (fun m => within (m+108)) = true := by decide +kernel
private theorem band112 : (List.range 4).all (fun m => within (m+112)) = true := by decide +kernel
private theorem band116 : (List.range 4).all (fun m => within (m+116)) = true := by decide +kernel
private theorem band120 : (List.range 4).all (fun m => within (m+120)) = true := by decide +kernel
private theorem band124 : (List.range 4).all (fun m => within (m+124)) = true := by decide +kernel
private theorem band128 : (List.range 4).all (fun m => within (m+128)) = true := by decide +kernel
private theorem band132 : (List.range 4).all (fun m => within (m+132)) = true := by decide +kernel
private theorem band136 : (List.range 4).all (fun m => within (m+136)) = true := by decide +kernel
private theorem band140 : (List.range 4).all (fun m => within (m+140)) = true := by decide +kernel
private theorem band144 : (List.range 4).all (fun m => within (m+144)) = true := by decide +kernel
private theorem band148 : (List.range 4).all (fun m => within (m+148)) = true := by decide +kernel
private theorem band152 : (List.range 4).all (fun m => within (m+152)) = true := by decide +kernel
private theorem band156 : (List.range 4).all (fun m => within (m+156)) = true := by decide +kernel
private theorem band160 : (List.range 4).all (fun m => within (m+160)) = true := by decide +kernel
private theorem band164 : (List.range 4).all (fun m => within (m+164)) = true := by decide +kernel
private theorem band168 : (List.range 4).all (fun m => within (m+168)) = true := by decide +kernel
private theorem band172 : (List.range 4).all (fun m => within (m+172)) = true := by decide +kernel
private theorem band176 : (List.range 4).all (fun m => within (m+176)) = true := by decide +kernel
private theorem band180 : (List.range 4).all (fun m => within (m+180)) = true := by decide +kernel
private theorem band184 : (List.range 4).all (fun m => within (m+184)) = true := by decide +kernel
private theorem band188 : (List.range 4).all (fun m => within (m+188)) = true := by decide +kernel
private theorem band192 : (List.range 4).all (fun m => within (m+192)) = true := by decide +kernel
private theorem band196 : (List.range 4).all (fun m => within (m+196)) = true := by decide +kernel
private theorem band200 : (List.range 4).all (fun m => within (m+200)) = true := by decide +kernel
private theorem band204 : (List.range 4).all (fun m => within (m+204)) = true := by decide +kernel
private theorem band208 : (List.range 4).all (fun m => within (m+208)) = true := by decide +kernel
private theorem band212 : (List.range 4).all (fun m => within (m+212)) = true := by decide +kernel
private theorem band216 : (List.range 4).all (fun m => within (m+216)) = true := by decide +kernel
private theorem band220 : (List.range 4).all (fun m => within (m+220)) = true := by decide +kernel

private theorem covers (n : ℕ) (hn : n < 224) : within n = true := by
  by_cases h0 : n < 4
  · have h := List.all_eq_true.mp band0 (n-0) (List.mem_range.mpr (by omega))
    simpa only [show n-0+0=n by omega] using h
  by_cases h4 : n < 8
  · have h := List.all_eq_true.mp band4 (n-4) (List.mem_range.mpr (by omega))
    simpa only [show n-4+4=n by omega] using h
  by_cases h8 : n < 12
  · have h := List.all_eq_true.mp band8 (n-8) (List.mem_range.mpr (by omega))
    simpa only [show n-8+8=n by omega] using h
  by_cases h12 : n < 16
  · have h := List.all_eq_true.mp band12 (n-12) (List.mem_range.mpr (by omega))
    simpa only [show n-12+12=n by omega] using h
  by_cases h16 : n < 20
  · have h := List.all_eq_true.mp band16 (n-16) (List.mem_range.mpr (by omega))
    simpa only [show n-16+16=n by omega] using h
  by_cases h20 : n < 24
  · have h := List.all_eq_true.mp band20 (n-20) (List.mem_range.mpr (by omega))
    simpa only [show n-20+20=n by omega] using h
  by_cases h24 : n < 28
  · have h := List.all_eq_true.mp band24 (n-24) (List.mem_range.mpr (by omega))
    simpa only [show n-24+24=n by omega] using h
  by_cases h28 : n < 32
  · have h := List.all_eq_true.mp band28 (n-28) (List.mem_range.mpr (by omega))
    simpa only [show n-28+28=n by omega] using h
  by_cases h32 : n < 36
  · have h := List.all_eq_true.mp band32 (n-32) (List.mem_range.mpr (by omega))
    simpa only [show n-32+32=n by omega] using h
  by_cases h36 : n < 40
  · have h := List.all_eq_true.mp band36 (n-36) (List.mem_range.mpr (by omega))
    simpa only [show n-36+36=n by omega] using h
  by_cases h40 : n < 44
  · have h := List.all_eq_true.mp band40 (n-40) (List.mem_range.mpr (by omega))
    simpa only [show n-40+40=n by omega] using h
  by_cases h44 : n < 48
  · have h := List.all_eq_true.mp band44 (n-44) (List.mem_range.mpr (by omega))
    simpa only [show n-44+44=n by omega] using h
  by_cases h48 : n < 52
  · have h := List.all_eq_true.mp band48 (n-48) (List.mem_range.mpr (by omega))
    simpa only [show n-48+48=n by omega] using h
  by_cases h52 : n < 56
  · have h := List.all_eq_true.mp band52 (n-52) (List.mem_range.mpr (by omega))
    simpa only [show n-52+52=n by omega] using h
  by_cases h56 : n < 60
  · have h := List.all_eq_true.mp band56 (n-56) (List.mem_range.mpr (by omega))
    simpa only [show n-56+56=n by omega] using h
  by_cases h60 : n < 64
  · have h := List.all_eq_true.mp band60 (n-60) (List.mem_range.mpr (by omega))
    simpa only [show n-60+60=n by omega] using h
  by_cases h64 : n < 68
  · have h := List.all_eq_true.mp band64 (n-64) (List.mem_range.mpr (by omega))
    simpa only [show n-64+64=n by omega] using h
  by_cases h68 : n < 72
  · have h := List.all_eq_true.mp band68 (n-68) (List.mem_range.mpr (by omega))
    simpa only [show n-68+68=n by omega] using h
  by_cases h72 : n < 76
  · have h := List.all_eq_true.mp band72 (n-72) (List.mem_range.mpr (by omega))
    simpa only [show n-72+72=n by omega] using h
  by_cases h76 : n < 80
  · have h := List.all_eq_true.mp band76 (n-76) (List.mem_range.mpr (by omega))
    simpa only [show n-76+76=n by omega] using h
  by_cases h80 : n < 84
  · have h := List.all_eq_true.mp band80 (n-80) (List.mem_range.mpr (by omega))
    simpa only [show n-80+80=n by omega] using h
  by_cases h84 : n < 88
  · have h := List.all_eq_true.mp band84 (n-84) (List.mem_range.mpr (by omega))
    simpa only [show n-84+84=n by omega] using h
  by_cases h88 : n < 92
  · have h := List.all_eq_true.mp band88 (n-88) (List.mem_range.mpr (by omega))
    simpa only [show n-88+88=n by omega] using h
  by_cases h92 : n < 96
  · have h := List.all_eq_true.mp band92 (n-92) (List.mem_range.mpr (by omega))
    simpa only [show n-92+92=n by omega] using h
  by_cases h96 : n < 100
  · have h := List.all_eq_true.mp band96 (n-96) (List.mem_range.mpr (by omega))
    simpa only [show n-96+96=n by omega] using h
  by_cases h100 : n < 104
  · have h := List.all_eq_true.mp band100 (n-100) (List.mem_range.mpr (by omega))
    simpa only [show n-100+100=n by omega] using h
  by_cases h104 : n < 108
  · have h := List.all_eq_true.mp band104 (n-104) (List.mem_range.mpr (by omega))
    simpa only [show n-104+104=n by omega] using h
  by_cases h108 : n < 112
  · have h := List.all_eq_true.mp band108 (n-108) (List.mem_range.mpr (by omega))
    simpa only [show n-108+108=n by omega] using h
  by_cases h112 : n < 116
  · have h := List.all_eq_true.mp band112 (n-112) (List.mem_range.mpr (by omega))
    simpa only [show n-112+112=n by omega] using h
  by_cases h116 : n < 120
  · have h := List.all_eq_true.mp band116 (n-116) (List.mem_range.mpr (by omega))
    simpa only [show n-116+116=n by omega] using h
  by_cases h120 : n < 124
  · have h := List.all_eq_true.mp band120 (n-120) (List.mem_range.mpr (by omega))
    simpa only [show n-120+120=n by omega] using h
  by_cases h124 : n < 128
  · have h := List.all_eq_true.mp band124 (n-124) (List.mem_range.mpr (by omega))
    simpa only [show n-124+124=n by omega] using h
  by_cases h128 : n < 132
  · have h := List.all_eq_true.mp band128 (n-128) (List.mem_range.mpr (by omega))
    simpa only [show n-128+128=n by omega] using h
  by_cases h132 : n < 136
  · have h := List.all_eq_true.mp band132 (n-132) (List.mem_range.mpr (by omega))
    simpa only [show n-132+132=n by omega] using h
  by_cases h136 : n < 140
  · have h := List.all_eq_true.mp band136 (n-136) (List.mem_range.mpr (by omega))
    simpa only [show n-136+136=n by omega] using h
  by_cases h140 : n < 144
  · have h := List.all_eq_true.mp band140 (n-140) (List.mem_range.mpr (by omega))
    simpa only [show n-140+140=n by omega] using h
  by_cases h144 : n < 148
  · have h := List.all_eq_true.mp band144 (n-144) (List.mem_range.mpr (by omega))
    simpa only [show n-144+144=n by omega] using h
  by_cases h148 : n < 152
  · have h := List.all_eq_true.mp band148 (n-148) (List.mem_range.mpr (by omega))
    simpa only [show n-148+148=n by omega] using h
  by_cases h152 : n < 156
  · have h := List.all_eq_true.mp band152 (n-152) (List.mem_range.mpr (by omega))
    simpa only [show n-152+152=n by omega] using h
  by_cases h156 : n < 160
  · have h := List.all_eq_true.mp band156 (n-156) (List.mem_range.mpr (by omega))
    simpa only [show n-156+156=n by omega] using h
  by_cases h160 : n < 164
  · have h := List.all_eq_true.mp band160 (n-160) (List.mem_range.mpr (by omega))
    simpa only [show n-160+160=n by omega] using h
  by_cases h164 : n < 168
  · have h := List.all_eq_true.mp band164 (n-164) (List.mem_range.mpr (by omega))
    simpa only [show n-164+164=n by omega] using h
  by_cases h168 : n < 172
  · have h := List.all_eq_true.mp band168 (n-168) (List.mem_range.mpr (by omega))
    simpa only [show n-168+168=n by omega] using h
  by_cases h172 : n < 176
  · have h := List.all_eq_true.mp band172 (n-172) (List.mem_range.mpr (by omega))
    simpa only [show n-172+172=n by omega] using h
  by_cases h176 : n < 180
  · have h := List.all_eq_true.mp band176 (n-176) (List.mem_range.mpr (by omega))
    simpa only [show n-176+176=n by omega] using h
  by_cases h180 : n < 184
  · have h := List.all_eq_true.mp band180 (n-180) (List.mem_range.mpr (by omega))
    simpa only [show n-180+180=n by omega] using h
  by_cases h184 : n < 188
  · have h := List.all_eq_true.mp band184 (n-184) (List.mem_range.mpr (by omega))
    simpa only [show n-184+184=n by omega] using h
  by_cases h188 : n < 192
  · have h := List.all_eq_true.mp band188 (n-188) (List.mem_range.mpr (by omega))
    simpa only [show n-188+188=n by omega] using h
  by_cases h192 : n < 196
  · have h := List.all_eq_true.mp band192 (n-192) (List.mem_range.mpr (by omega))
    simpa only [show n-192+192=n by omega] using h
  by_cases h196 : n < 200
  · have h := List.all_eq_true.mp band196 (n-196) (List.mem_range.mpr (by omega))
    simpa only [show n-196+196=n by omega] using h
  by_cases h200 : n < 204
  · have h := List.all_eq_true.mp band200 (n-200) (List.mem_range.mpr (by omega))
    simpa only [show n-200+200=n by omega] using h
  by_cases h204 : n < 208
  · have h := List.all_eq_true.mp band204 (n-204) (List.mem_range.mpr (by omega))
    simpa only [show n-204+204=n by omega] using h
  by_cases h208 : n < 212
  · have h := List.all_eq_true.mp band208 (n-208) (List.mem_range.mpr (by omega))
    simpa only [show n-208+208=n by omega] using h
  by_cases h212 : n < 216
  · have h := List.all_eq_true.mp band212 (n-212) (List.mem_range.mpr (by omega))
    simpa only [show n-212+212=n by omega] using h
  by_cases h216 : n < 220
  · have h := List.all_eq_true.mp band216 (n-216) (List.mem_range.mpr (by omega))
    simpa only [show n-216+216=n by omega] using h
  have h := List.all_eq_true.mp band220 (n-220) (List.mem_range.mpr (by omega))
  simpa only [show n-220+220=n by omega] using h

theorem solution : (∑ n ∈ Finset.range 224, cellCost ((n:ℤ)-112)) ≤ (31/1000000000000:ℚ) := by
  calc _ ≤ ∑ n ∈ Finset.range 224, upper n := by
         apply Finset.sum_le_sum
         intro n hn
         exact of_decide_eq_true (covers n (Finset.mem_range.mp hn))
       _ ≤ _ := by decide +kernel
