-- Prove2me | solution 1 for H65K.Platform.HighGroup004.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:59:39.703855+00:00
-- url     : https://prove2.me/submissions/5aa81f28-61c4-4305-b1ef-ee0230d0ce59

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group016
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group017
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group018
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group019
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0128
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group016).1).1
end RH65K_0128

namespace RH65K_0129
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group016).2).1).1
end RH65K_0129

namespace RH65K_0130
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group016).2).2).1).1
end RH65K_0130

namespace RH65K_0131
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group016).2).2).2).1).1
end RH65K_0131

namespace RH65K_0132
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group016).2).2).2).2).1).1
end RH65K_0132

namespace RH65K_0133
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group016).2).2).2).2).2).1).1
end RH65K_0133

namespace RH65K_0134
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group016).2).2).2).2).2).2).1).1
end RH65K_0134

namespace RH65K_0135
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group016).2).2).2).2).2).2).2).1
end RH65K_0135

namespace RH65K_0136
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group017).1).1
end RH65K_0136

namespace RH65K_0137
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group017).2).1).1
end RH65K_0137

namespace RH65K_0138
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group017).2).2).1).1
end RH65K_0138

namespace RH65K_0139
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group017).2).2).2).1).1
end RH65K_0139

namespace RH65K_0140
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group017).2).2).2).2).1).1
end RH65K_0140

namespace RH65K_0141
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group017).2).2).2).2).2).1).1
end RH65K_0141

namespace RH65K_0142
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group017).2).2).2).2).2).2).1).1
end RH65K_0142

namespace RH65K_0143
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group017).2).2).2).2).2).2).2).1
end RH65K_0143

namespace RH65K_0144
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group018).1).1
end RH65K_0144

namespace RH65K_0145
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group018).2).1).1
end RH65K_0145

namespace RH65K_0146
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group018).2).2).1).1
end RH65K_0146

namespace RH65K_0147
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group018).2).2).2).1).1
end RH65K_0147

namespace RH65K_0148
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group018).2).2).2).2).1).1
end RH65K_0148

namespace RH65K_0149
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group018).2).2).2).2).2).1).1
end RH65K_0149

namespace RH65K_0150
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group018).2).2).2).2).2).2).1).1
end RH65K_0150

namespace RH65K_0151
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group018).2).2).2).2).2).2).2).1
end RH65K_0151

namespace RH65K_0152
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group019).1).1
end RH65K_0152

namespace RH65K_0153
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group019).2).1).1
end RH65K_0153

namespace RH65K_0154
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group019).2).2).1).1
end RH65K_0154

namespace RH65K_0155
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group019).2).2).2).1).1
end RH65K_0155

namespace RH65K_0156
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group019).2).2).2).2).1).1
end RH65K_0156

namespace RH65K_0157
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group019).2).2).2).2).2).1).1
end RH65K_0157

namespace RH65K_0158
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group019).2).2).2).2).2).2).1).1
end RH65K_0158

namespace RH65K_0159
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group019).2).2).2).2).2).2).2).1
end RH65K_0159

namespace H65K_PlatformHighBatch0128
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0128.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0128.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0128.samples = true
  exact RH65K_0128.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1567760127 : ℝ) / 65536) ((1574101531 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1567760127 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0128.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1574101531 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0128.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0128

namespace H65K_PlatformHighBatch0129
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0129.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0129.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0129.samples = true
  exact RH65K_0129.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1574101531 : ℝ) / 65536) ((1580459720 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1574101531 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0129.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1580459720 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0129.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0129

namespace H65K_PlatformHighBatch0130
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0130.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0130.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0130.samples = true
  exact RH65K_0130.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1580459720 : ℝ) / 65536) ((1586796019 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1580459720 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0130.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1586796019 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0130.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0130

namespace H65K_PlatformHighBatch0131
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0131.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0131.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0131.samples = true
  exact RH65K_0131.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1586796019 : ℝ) / 65536) ((1593108646 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1586796019 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0131.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1593108646 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0131.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0131

namespace H65K_PlatformHighBatch0132
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0132.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0132.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0132.samples = true
  exact RH65K_0132.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1593108646 : ℝ) / 65536) ((1599461136 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1593108646 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0132.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1599461136 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0132.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0132

namespace H65K_PlatformHighBatch0133
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0133.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0133.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0133.samples = true
  exact RH65K_0133.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1599461136 : ℝ) / 65536) ((1605798680 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1599461136 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0133.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1605798680 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0133.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0133

namespace H65K_PlatformHighBatch0134
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0134.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0134.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0134.samples = true
  exact RH65K_0134.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1605798680 : ℝ) / 65536) ((1612093594 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1605798680 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0134.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1612093594 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0134.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0134

namespace H65K_PlatformHighBatch0135
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0135.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0135.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0135.samples = true
  exact RH65K_0135.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1612093594 : ℝ) / 65536) ((1618417054 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1612093594 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0135.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1618417054 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0135.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0135

namespace H65K_PlatformHighBatch0136
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0136.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0136.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0136.samples = true
  exact RH65K_0136.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1618417054 : ℝ) / 65536) ((1624724413 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1618417054 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0136.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1624724413 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0136.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0136

namespace H65K_PlatformHighBatch0137
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0137.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0137.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0137.samples = true
  exact RH65K_0137.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1624724413 : ℝ) / 65536) ((1631038309 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1624724413 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0137.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1631038309 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0137.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0137

namespace H65K_PlatformHighBatch0138
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0138.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0138.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0138.samples = true
  exact RH65K_0138.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1631038309 : ℝ) / 65536) ((1637363546 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1631038309 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0138.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1637363546 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0138.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0138

namespace H65K_PlatformHighBatch0139
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0139.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0139.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0139.samples = true
  exact RH65K_0139.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1637363546 : ℝ) / 65536) ((1643676734 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1637363546 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0139.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1643676734 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0139.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0139

namespace H65K_PlatformHighBatch0140
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0140.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0140.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0140.samples = true
  exact RH65K_0140.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1643676734 : ℝ) / 65536) ((1649989737 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1643676734 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0140.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1649989737 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0140.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0140

namespace H65K_PlatformHighBatch0141
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0141.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0141.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0141.samples = true
  exact RH65K_0141.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1649989737 : ℝ) / 65536) ((1656274579 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1649989737 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0141.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1656274579 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0141.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0141

namespace H65K_PlatformHighBatch0142
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0142.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0142.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0142.samples = true
  exact RH65K_0142.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1656274579 : ℝ) / 65536) ((1662567013 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1656274579 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0142.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1662567013 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0142.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0142

namespace H65K_PlatformHighBatch0143
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0143.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0143.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0143.samples = true
  exact RH65K_0143.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1662567013 : ℝ) / 65536) ((1668872952 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1662567013 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0143.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1668872952 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0143.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0143

namespace H65K_PlatformHighBatch0144
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0144.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0144.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0144.samples = true
  exact RH65K_0144.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1668872952 : ℝ) / 65536) ((1675163743 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1668872952 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0144.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1675163743 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0144.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0144

namespace H65K_PlatformHighBatch0145
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0145.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0145.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0145.samples = true
  exact RH65K_0145.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1675163743 : ℝ) / 65536) ((1681469769 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1675163743 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0145.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1681469769 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0145.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0145

namespace H65K_PlatformHighBatch0146
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0146.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0146.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0146.samples = true
  exact RH65K_0146.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1681469769 : ℝ) / 65536) ((1687734815 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1681469769 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0146.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1687734815 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0146.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0146

namespace H65K_PlatformHighBatch0147
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0147.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0147.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0147.samples = true
  exact RH65K_0147.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1687734815 : ℝ) / 65536) ((1694032406 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1687734815 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0147.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1694032406 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0147.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0147

namespace H65K_PlatformHighBatch0148
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0148.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0148.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0148.samples = true
  exact RH65K_0148.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1694032406 : ℝ) / 65536) ((1700330840 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1694032406 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0148.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1700330840 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0148.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0148

namespace H65K_PlatformHighBatch0149
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0149.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0149.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0149.samples = true
  exact RH65K_0149.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1700330840 : ℝ) / 65536) ((1706600946 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1700330840 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0149.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1706600946 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0149.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0149

namespace H65K_PlatformHighBatch0150
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0150.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0150.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0150.samples = true
  exact RH65K_0150.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1706600946 : ℝ) / 65536) ((1712869497 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1706600946 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0150.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1712869497 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0150.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0150

namespace H65K_PlatformHighBatch0151
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0151.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0151.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0151.samples = true
  exact RH65K_0151.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1712869497 : ℝ) / 65536) ((1719134872 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1712869497 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0151.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1719134872 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0151.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0151

namespace H65K_PlatformHighBatch0152
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0152.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0152.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0152.samples = true
  exact RH65K_0152.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1719134872 : ℝ) / 65536) ((1725408282 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1719134872 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0152.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1725408282 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0152.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0152

namespace H65K_PlatformHighBatch0153
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0153.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0153.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0153.samples = true
  exact RH65K_0153.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1725408282 : ℝ) / 65536) ((1731695477 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1725408282 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0153.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1731695477 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0153.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0153

namespace H65K_PlatformHighBatch0154
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0154.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0154.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0154.samples = true
  exact RH65K_0154.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1731695477 : ℝ) / 65536) ((1737932294 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1731695477 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0154.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1737932294 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0154.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0154

namespace H65K_PlatformHighBatch0155
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0155.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0155.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0155.samples = true
  exact RH65K_0155.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1737932294 : ℝ) / 65536) ((1744225766 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1737932294 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0155.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1744225766 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0155.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0155

namespace H65K_PlatformHighBatch0156
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0156.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0156.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0156.samples = true
  exact RH65K_0156.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1744225766 : ℝ) / 65536) ((1750475024 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1744225766 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0156.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1750475024 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0156.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0156

namespace H65K_PlatformHighBatch0157
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0157.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0157.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0157.samples = true
  exact RH65K_0157.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1750475024 : ℝ) / 65536) ((1756742831 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1750475024 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0157.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1756742831 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0157.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0157

namespace H65K_PlatformHighBatch0158
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0158.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0158.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0158.samples = true
  exact RH65K_0158.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1756742831 : ℝ) / 65536) ((1762984641 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1756742831 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0158.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1762984641 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0158.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0158

namespace H65K_PlatformHighBatch0159
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0159.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0159.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0159.samples = true
  exact RH65K_0159.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1762984641 : ℝ) / 65536) ((1769259448 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1762984641 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0159.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1769259448 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0159.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0159

theorem solution : RS5.BandZeros ((1567760127 : ℝ) / 65536) ((1769259448 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0128.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0129.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0130.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0131.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0132.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0133.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0134.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0135.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0136.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0137.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0138.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0139.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0140.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0141.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0142.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0143.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0144.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0145.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0146.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0147.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0148.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0149.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0150.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0151.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0152.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0153.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0154.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0155.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0156.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0157.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0158.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0159.zeros
  exact h31
