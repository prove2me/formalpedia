-- Prove2me | solution 1 for H65K.Platform.HighGroup006.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:00:45.432888+00:00
-- url     : https://prove2.me/submissions/059ed864-242e-4a16-b204-5e4711c1c641

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group024
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group025
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group026
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group027
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0192
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group024).1).1
end RH65K_0192

namespace RH65K_0193
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group024).2).1).1
end RH65K_0193

namespace RH65K_0194
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group024).2).2).1).1
end RH65K_0194

namespace RH65K_0195
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group024).2).2).2).1).1
end RH65K_0195

namespace RH65K_0196
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group024).2).2).2).2).1).1
end RH65K_0196

namespace RH65K_0197
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group024).2).2).2).2).2).1).1
end RH65K_0197

namespace RH65K_0198
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group024).2).2).2).2).2).2).1).1
end RH65K_0198

namespace RH65K_0199
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group024).2).2).2).2).2).2).2).1
end RH65K_0199

namespace RH65K_0200
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group025).1).1
end RH65K_0200

namespace RH65K_0201
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group025).2).1).1
end RH65K_0201

namespace RH65K_0202
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group025).2).2).1).1
end RH65K_0202

namespace RH65K_0203
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group025).2).2).2).1).1
end RH65K_0203

namespace RH65K_0204
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group025).2).2).2).2).1).1
end RH65K_0204

namespace RH65K_0205
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group025).2).2).2).2).2).1).1
end RH65K_0205

namespace RH65K_0206
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group025).2).2).2).2).2).2).1).1
end RH65K_0206

namespace RH65K_0207
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group025).2).2).2).2).2).2).2).1
end RH65K_0207

namespace RH65K_0208
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group026).1).1
end RH65K_0208

namespace RH65K_0209
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group026).2).1).1
end RH65K_0209

namespace RH65K_0210
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group026).2).2).1).1
end RH65K_0210

namespace RH65K_0211
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group026).2).2).2).1).1
end RH65K_0211

namespace RH65K_0212
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group026).2).2).2).2).1).1
end RH65K_0212

namespace RH65K_0213
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group026).2).2).2).2).2).1).1
end RH65K_0213

namespace RH65K_0214
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group026).2).2).2).2).2).2).1).1
end RH65K_0214

namespace RH65K_0215
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group026).2).2).2).2).2).2).2).1
end RH65K_0215

namespace RH65K_0216
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group027).1).1
end RH65K_0216

namespace RH65K_0217
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group027).2).1).1
end RH65K_0217

namespace RH65K_0218
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group027).2).2).1).1
end RH65K_0218

namespace RH65K_0219
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group027).2).2).2).1).1
end RH65K_0219

namespace RH65K_0220
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group027).2).2).2).2).1).1
end RH65K_0220

namespace RH65K_0221
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group027).2).2).2).2).2).1).1
end RH65K_0221

namespace RH65K_0222
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group027).2).2).2).2).2).2).1).1
end RH65K_0222

namespace RH65K_0223
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group027).2).2).2).2).2).2).2).1
end RH65K_0223

namespace H65K_PlatformHighBatch0192
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0192.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0192.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0192.samples = true
  exact RH65K_0192.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1967982839 : ℝ) / 65536) ((1974194510 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1967982839 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0192.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1974194510 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0192.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0192

namespace H65K_PlatformHighBatch0193
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0193.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0193.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0193.samples = true
  exact RH65K_0193.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1974194510 : ℝ) / 65536) ((1980340065 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1974194510 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0193.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1980340065 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0193.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0193

namespace H65K_PlatformHighBatch0194
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0194.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0194.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0194.samples = true
  exact RH65K_0194.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1980340065 : ℝ) / 65536) ((1986489470 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1980340065 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0194.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1986489470 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0194.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0194

namespace H65K_PlatformHighBatch0195
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0195.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0195.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0195.samples = true
  exact RH65K_0195.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1986489470 : ℝ) / 65536) ((1992672111 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1986489470 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0195.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1992672111 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0195.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0195

namespace H65K_PlatformHighBatch0196
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0196.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0196.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0196.samples = true
  exact RH65K_0196.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1992672111 : ℝ) / 65536) ((1998808632 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1992672111 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0196.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1998808632 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0196.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0196

namespace H65K_PlatformHighBatch0197
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0197.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0197.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0197.samples = true
  exact RH65K_0197.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1998808632 : ℝ) / 65536) ((2004996490 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1998808632 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0197.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2004996490 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0197.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0197

namespace H65K_PlatformHighBatch0198
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0198.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0198.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0198.samples = true
  exact RH65K_0198.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2004996490 : ℝ) / 65536) ((2011138647 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2004996490 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0198.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2011138647 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0198.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0198

namespace H65K_PlatformHighBatch0199
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0199.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0199.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0199.samples = true
  exact RH65K_0199.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2011138647 : ℝ) / 65536) ((2017297970 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2011138647 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0199.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2017297970 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0199.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0199

namespace H65K_PlatformHighBatch0200
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0200.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0200.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0200.samples = true
  exact RH65K_0200.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2017297970 : ℝ) / 65536) ((2023467054 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2017297970 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0200.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2023467054 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0200.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0200

namespace H65K_PlatformHighBatch0201
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0201.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0201.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0201.samples = true
  exact RH65K_0201.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2023467054 : ℝ) / 65536) ((2029603264 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2023467054 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0201.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2029603264 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0201.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0201

namespace H65K_PlatformHighBatch0202
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0202.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0202.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0202.samples = true
  exact RH65K_0202.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2029603264 : ℝ) / 65536) ((2035744377 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2029603264 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0202.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2035744377 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0202.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0202

namespace H65K_PlatformHighBatch0203
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0203.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0203.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0203.samples = true
  exact RH65K_0203.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2035744377 : ℝ) / 65536) ((2041903455 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2035744377 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0203.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2041903455 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0203.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0203

namespace H65K_PlatformHighBatch0204
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0204.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0204.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0204.samples = true
  exact RH65K_0204.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2041903455 : ℝ) / 65536) ((2048055054 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2041903455 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0204.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2048055054 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0204.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0204

namespace H65K_PlatformHighBatch0205
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0205.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0205.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0205.samples = true
  exact RH65K_0205.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2048055054 : ℝ) / 65536) ((2054175056 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2048055054 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0205.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2054175056 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0205.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0205

namespace H65K_PlatformHighBatch0206
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0206.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0206.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0206.samples = true
  exact RH65K_0206.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2054175056 : ℝ) / 65536) ((2060337067 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2054175056 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0206.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2060337067 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0206.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0206

namespace H65K_PlatformHighBatch0207
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0207.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0207.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0207.samples = true
  exact RH65K_0207.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2060337067 : ℝ) / 65536) ((2066473588 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2060337067 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0207.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2066473588 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0207.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0207

namespace H65K_PlatformHighBatch0208
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0208.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0208.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0208.samples = true
  exact RH65K_0208.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2066473588 : ℝ) / 65536) ((2072592815 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2066473588 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0208.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2072592815 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0208.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0208

namespace H65K_PlatformHighBatch0209
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0209.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0209.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0209.samples = true
  exact RH65K_0209.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2072592815 : ℝ) / 65536) ((2078754523 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2072592815 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0209.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2078754523 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0209.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0209

namespace H65K_PlatformHighBatch0210
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0210.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0210.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0210.samples = true
  exact RH65K_0210.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2078754523 : ℝ) / 65536) ((2084868443 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2078754523 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0210.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2084868443 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0210.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0210

namespace H65K_PlatformHighBatch0211
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0211.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0211.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0211.samples = true
  exact RH65K_0211.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2084868443 : ℝ) / 65536) ((2090980072 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2084868443 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0211.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2090980072 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0211.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0211

namespace H65K_PlatformHighBatch0212
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0212.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0212.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0212.samples = true
  exact RH65K_0212.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2090980072 : ℝ) / 65536) ((2097150713 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2090980072 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0212.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2097150713 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0212.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0212

namespace H65K_PlatformHighBatch0213
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0213.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0213.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0213.samples = true
  exact RH65K_0213.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2097150713 : ℝ) / 65536) ((2103261137 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2097150713 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0213.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2103261137 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0213.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0213

namespace H65K_PlatformHighBatch0214
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0214.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0214.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0214.samples = true
  exact RH65K_0214.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2103261137 : ℝ) / 65536) ((2109373672 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2103261137 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0214.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2109373672 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0214.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0214

namespace H65K_PlatformHighBatch0215
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0215.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0215.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0215.samples = true
  exact RH65K_0215.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2109373672 : ℝ) / 65536) ((2115520788 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2109373672 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0215.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2115520788 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0215.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0215

namespace H65K_PlatformHighBatch0216
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0216.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0216.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0216.samples = true
  exact RH65K_0216.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2115520788 : ℝ) / 65536) ((2121624747 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2115520788 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0216.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2121624747 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0216.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0216

namespace H65K_PlatformHighBatch0217
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0217.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0217.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0217.samples = true
  exact RH65K_0217.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2121624747 : ℝ) / 65536) ((2127724334 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2121624747 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0217.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2127724334 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0217.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0217

namespace H65K_PlatformHighBatch0218
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0218.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0218.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0218.samples = true
  exact RH65K_0218.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2127724334 : ℝ) / 65536) ((2133859445 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2127724334 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0218.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2133859445 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0218.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0218

namespace H65K_PlatformHighBatch0219
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0219.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0219.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0219.samples = true
  exact RH65K_0219.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2133859445 : ℝ) / 65536) ((2139977341 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2133859445 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0219.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2139977341 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0219.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0219

namespace H65K_PlatformHighBatch0220
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0220.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0220.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0220.samples = true
  exact RH65K_0220.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2139977341 : ℝ) / 65536) ((2146071127 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2139977341 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0220.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2146071127 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0220.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0220

namespace H65K_PlatformHighBatch0221
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0221.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0221.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0221.samples = true
  exact RH65K_0221.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2146071127 : ℝ) / 65536) ((2152168389 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2146071127 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0221.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2152168389 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0221.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0221

namespace H65K_PlatformHighBatch0222
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0222.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0222.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0222.samples = true
  exact RH65K_0222.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2152168389 : ℝ) / 65536) ((2158311522 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2152168389 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0222.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2158311522 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0222.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0222

namespace H65K_PlatformHighBatch0223
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0223.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0223.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0223.samples = true
  exact RH65K_0223.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2158311522 : ℝ) / 65536) ((2164401145 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2158311522 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0223.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2164401145 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0223.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0223

theorem solution : RS5.BandZeros ((1967982839 : ℝ) / 65536) ((2164401145 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0192.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0193.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0194.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0195.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0196.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0197.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0198.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0199.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0200.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0201.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0202.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0203.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0204.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0205.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0206.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0207.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0208.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0209.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0210.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0211.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0212.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0213.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0214.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0215.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0216.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0217.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0218.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0219.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0220.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0221.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0222.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0223.zeros
  exact h31
