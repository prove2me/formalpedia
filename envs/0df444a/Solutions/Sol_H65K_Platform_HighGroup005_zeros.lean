-- Prove2me | solution 1 for H65K.Platform.HighGroup005.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:00:00.484106+00:00
-- url     : https://prove2.me/submissions/ca737fa3-8b32-42d4-9df6-e595a9174d21

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group020
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group021
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group022
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group023
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0160
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group020).1).1
end RH65K_0160

namespace RH65K_0161
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group020).2).1).1
end RH65K_0161

namespace RH65K_0162
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group020).2).2).1).1
end RH65K_0162

namespace RH65K_0163
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group020).2).2).2).1).1
end RH65K_0163

namespace RH65K_0164
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group020).2).2).2).2).1).1
end RH65K_0164

namespace RH65K_0165
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group020).2).2).2).2).2).1).1
end RH65K_0165

namespace RH65K_0166
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group020).2).2).2).2).2).2).1).1
end RH65K_0166

namespace RH65K_0167
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group020).2).2).2).2).2).2).2).1
end RH65K_0167

namespace RH65K_0168
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group021).1).1
end RH65K_0168

namespace RH65K_0169
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group021).2).1).1
end RH65K_0169

namespace RH65K_0170
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group021).2).2).1).1
end RH65K_0170

namespace RH65K_0171
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group021).2).2).2).1).1
end RH65K_0171

namespace RH65K_0172
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group021).2).2).2).2).1).1
end RH65K_0172

namespace RH65K_0173
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group021).2).2).2).2).2).1).1
end RH65K_0173

namespace RH65K_0174
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group021).2).2).2).2).2).2).1).1
end RH65K_0174

namespace RH65K_0175
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group021).2).2).2).2).2).2).2).1
end RH65K_0175

namespace RH65K_0176
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group022).1).1
end RH65K_0176

namespace RH65K_0177
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group022).2).1).1
end RH65K_0177

namespace RH65K_0178
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group022).2).2).1).1
end RH65K_0178

namespace RH65K_0179
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group022).2).2).2).1).1
end RH65K_0179

namespace RH65K_0180
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group022).2).2).2).2).1).1
end RH65K_0180

namespace RH65K_0181
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group022).2).2).2).2).2).1).1
end RH65K_0181

namespace RH65K_0182
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group022).2).2).2).2).2).2).1).1
end RH65K_0182

namespace RH65K_0183
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group022).2).2).2).2).2).2).2).1
end RH65K_0183

namespace RH65K_0184
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group023).1).1
end RH65K_0184

namespace RH65K_0185
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group023).2).1).1
end RH65K_0185

namespace RH65K_0186
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group023).2).2).1).1
end RH65K_0186

namespace RH65K_0187
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group023).2).2).2).1).1
end RH65K_0187

namespace RH65K_0188
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group023).2).2).2).2).1).1
end RH65K_0188

namespace RH65K_0189
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group023).2).2).2).2).2).1).1
end RH65K_0189

namespace RH65K_0190
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group023).2).2).2).2).2).2).1).1
end RH65K_0190

namespace RH65K_0191
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group023).2).2).2).2).2).2).2).1
end RH65K_0191

namespace H65K_PlatformHighBatch0160
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0160.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0160.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0160.samples = true
  exact RH65K_0160.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1769259448 : ℝ) / 65536) ((1775486128 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1769259448 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0160.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1775486128 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0160.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0160

namespace H65K_PlatformHighBatch0161
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0161.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0161.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0161.samples = true
  exact RH65K_0161.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1775486128 : ℝ) / 65536) ((1781740726 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1775486128 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0161.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1781740726 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0161.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0161

namespace H65K_PlatformHighBatch0162
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0162.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0162.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0162.samples = true
  exact RH65K_0162.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1781740726 : ℝ) / 65536) ((1787989533 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1781740726 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0162.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1787989533 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0162.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0162

namespace H65K_PlatformHighBatch0163
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0163.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0163.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0163.samples = true
  exact RH65K_0163.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1787989533 : ℝ) / 65536) ((1794232379 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1787989533 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0163.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1794232379 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0163.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0163

namespace H65K_PlatformHighBatch0164
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0164.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0164.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0164.samples = true
  exact RH65K_0164.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1794232379 : ℝ) / 65536) ((1800458603 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1794232379 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0164.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1800458603 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0164.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0164

namespace H65K_PlatformHighBatch0165
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0165.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0165.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0165.samples = true
  exact RH65K_0165.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1800458603 : ℝ) / 65536) ((1806716870 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1800458603 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0165.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1806716870 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0165.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0165

namespace H65K_PlatformHighBatch0166
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0166.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0166.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0166.samples = true
  exact RH65K_0166.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1806716870 : ℝ) / 65536) ((1812915056 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1806716870 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0166.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1812915056 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0166.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0166

namespace H65K_PlatformHighBatch0167
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0167.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0167.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0167.samples = true
  exact RH65K_0167.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1812915056 : ℝ) / 65536) ((1819172548 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1812915056 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0167.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1819172548 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0167.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0167

namespace H65K_PlatformHighBatch0168
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0168.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0168.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0168.samples = true
  exact RH65K_0168.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1819172548 : ℝ) / 65536) ((1825393715 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1819172548 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0168.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1825393715 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0168.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0168

namespace H65K_PlatformHighBatch0169
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0169.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0169.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0169.samples = true
  exact RH65K_0169.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1825393715 : ℝ) / 65536) ((1831628273 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1825393715 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0169.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1831628273 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0169.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0169

namespace H65K_PlatformHighBatch0170
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0170.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0170.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0170.samples = true
  exact RH65K_0170.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1831628273 : ℝ) / 65536) ((1837854430 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1831628273 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0170.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1837854430 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0170.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0170

namespace H65K_PlatformHighBatch0171
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0171.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0171.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0171.samples = true
  exact RH65K_0171.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1837854430 : ℝ) / 65536) ((1844071087 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1837854430 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0171.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1844071087 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0171.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0171

namespace H65K_PlatformHighBatch0172
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0172.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0172.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0172.samples = true
  exact RH65K_0172.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1844071087 : ℝ) / 65536) ((1850269879 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1844071087 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0172.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1850269879 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0172.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0172

namespace H65K_PlatformHighBatch0173
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0173.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0173.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0173.samples = true
  exact RH65K_0173.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1850269879 : ℝ) / 65536) ((1856534564 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1850269879 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0173.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1856534564 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0173.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0173

namespace H65K_PlatformHighBatch0174
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0174.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0174.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0174.samples = true
  exact RH65K_0174.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1856534564 : ℝ) / 65536) ((1862712985 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1856534564 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0174.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1862712985 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0174.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0174

namespace H65K_PlatformHighBatch0175
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0175.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0175.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0175.samples = true
  exact RH65K_0175.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1862712985 : ℝ) / 65536) ((1868934858 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1862712985 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0175.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1868934858 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0175.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0175

namespace H65K_PlatformHighBatch0176
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0176.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0176.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0176.samples = true
  exact RH65K_0176.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1868934858 : ℝ) / 65536) ((1875141428 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1868934858 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0176.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1875141428 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0176.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0176

namespace H65K_PlatformHighBatch0177
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0177.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0177.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0177.samples = true
  exact RH65K_0177.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1875141428 : ℝ) / 65536) ((1881332754 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1875141428 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0177.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1881332754 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0177.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0177

namespace H65K_PlatformHighBatch0178
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0178.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0178.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0178.samples = true
  exact RH65K_0178.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1881332754 : ℝ) / 65536) ((1887551860 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1881332754 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0178.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1887551860 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0178.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0178

namespace H65K_PlatformHighBatch0179
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0179.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0179.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0179.samples = true
  exact RH65K_0179.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1887551860 : ℝ) / 65536) ((1893740569 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1887551860 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0179.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1893740569 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0179.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0179

namespace H65K_PlatformHighBatch0180
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0180.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0180.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0180.samples = true
  exact RH65K_0180.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1893740569 : ℝ) / 65536) ((1899969134 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1893740569 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0180.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1899969134 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0180.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0180

namespace H65K_PlatformHighBatch0181
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0181.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0181.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0181.samples = true
  exact RH65K_0181.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1899969134 : ℝ) / 65536) ((1906149419 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1899969134 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0181.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1906149419 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0181.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0181

namespace H65K_PlatformHighBatch0182
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0182.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0182.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0182.samples = true
  exact RH65K_0182.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1906149419 : ℝ) / 65536) ((1912368613 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1906149419 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0182.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1912368613 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0182.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0182

namespace H65K_PlatformHighBatch0183
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0183.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0183.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0183.samples = true
  exact RH65K_0183.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1912368613 : ℝ) / 65536) ((1918532676 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1912368613 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0183.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1918532676 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0183.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0183

namespace H65K_PlatformHighBatch0184
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0184.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0184.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0184.samples = true
  exact RH65K_0184.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1918532676 : ℝ) / 65536) ((1924724511 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1918532676 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0184.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1924724511 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0184.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0184

namespace H65K_PlatformHighBatch0185
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0185.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0185.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0185.samples = true
  exact RH65K_0185.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1924724511 : ℝ) / 65536) ((1930915836 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1924724511 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0185.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1930915836 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0185.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0185

namespace H65K_PlatformHighBatch0186
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0186.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0186.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0186.samples = true
  exact RH65K_0186.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1930915836 : ℝ) / 65536) ((1937114216 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1930915836 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0186.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1937114216 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0186.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0186

namespace H65K_PlatformHighBatch0187
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0187.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0187.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0187.samples = true
  exact RH65K_0187.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1937114216 : ℝ) / 65536) ((1943297279 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1937114216 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0187.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1943297279 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0187.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0187

namespace H65K_PlatformHighBatch0188
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0188.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0188.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0188.samples = true
  exact RH65K_0188.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1943297279 : ℝ) / 65536) ((1949474857 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1943297279 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0188.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1949474857 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0188.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0188

namespace H65K_PlatformHighBatch0189
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0189.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0189.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0189.samples = true
  exact RH65K_0189.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1949474857 : ℝ) / 65536) ((1955626273 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1949474857 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0189.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1955626273 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0189.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0189

namespace H65K_PlatformHighBatch0190
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0190.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0190.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0190.samples = true
  exact RH65K_0190.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1955626273 : ℝ) / 65536) ((1961831278 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1955626273 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0190.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1961831278 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0190.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0190

namespace H65K_PlatformHighBatch0191
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0191.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0191.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0191.samples = true
  exact RH65K_0191.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1961831278 : ℝ) / 65536) ((1967982839 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1961831278 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0191.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1967982839 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0191.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0191

theorem solution : RS5.BandZeros ((1769259448 : ℝ) / 65536) ((1967982839 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0160.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0161.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0162.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0163.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0164.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0165.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0166.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0167.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0168.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0169.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0170.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0171.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0172.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0173.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0174.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0175.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0176.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0177.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0178.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0179.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0180.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0181.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0182.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0183.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0184.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0185.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0186.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0187.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0188.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0189.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0190.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0191.zeros
  exact h31
