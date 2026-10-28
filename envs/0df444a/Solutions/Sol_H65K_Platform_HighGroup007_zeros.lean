-- Prove2me | solution 1 for H65K.Platform.HighGroup007.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:01:09.953836+00:00
-- url     : https://prove2.me/submissions/10d46188-2111-4a41-82c2-0a7307e8c6c7

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group028
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group029
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group030
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group031
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0224
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group028).1).1
end RH65K_0224

namespace RH65K_0225
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group028).2).1).1
end RH65K_0225

namespace RH65K_0226
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group028).2).2).1).1
end RH65K_0226

namespace RH65K_0227
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group028).2).2).2).1).1
end RH65K_0227

namespace RH65K_0228
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group028).2).2).2).2).1).1
end RH65K_0228

namespace RH65K_0229
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group028).2).2).2).2).2).1).1
end RH65K_0229

namespace RH65K_0230
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group028).2).2).2).2).2).2).1).1
end RH65K_0230

namespace RH65K_0231
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group028).2).2).2).2).2).2).2).1
end RH65K_0231

namespace RH65K_0232
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group029).1).1
end RH65K_0232

namespace RH65K_0233
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group029).2).1).1
end RH65K_0233

namespace RH65K_0234
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group029).2).2).1).1
end RH65K_0234

namespace RH65K_0235
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group029).2).2).2).1).1
end RH65K_0235

namespace RH65K_0236
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group029).2).2).2).2).1).1
end RH65K_0236

namespace RH65K_0237
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group029).2).2).2).2).2).1).1
end RH65K_0237

namespace RH65K_0238
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group029).2).2).2).2).2).2).1).1
end RH65K_0238

namespace RH65K_0239
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group029).2).2).2).2).2).2).2).1
end RH65K_0239

namespace RH65K_0240
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group030).1).1
end RH65K_0240

namespace RH65K_0241
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group030).2).1).1
end RH65K_0241

namespace RH65K_0242
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group030).2).2).1).1
end RH65K_0242

namespace RH65K_0243
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group030).2).2).2).1).1
end RH65K_0243

namespace RH65K_0244
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group030).2).2).2).2).1).1
end RH65K_0244

namespace RH65K_0245
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group030).2).2).2).2).2).1).1
end RH65K_0245

namespace RH65K_0246
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group030).2).2).2).2).2).2).1).1
end RH65K_0246

namespace RH65K_0247
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group030).2).2).2).2).2).2).2).1
end RH65K_0247

namespace RH65K_0248
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group031).1).1
end RH65K_0248

namespace RH65K_0249
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group031).2).1).1
end RH65K_0249

namespace RH65K_0250
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group031).2).2).1).1
end RH65K_0250

namespace RH65K_0251
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group031).2).2).2).1).1
end RH65K_0251

namespace RH65K_0252
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group031).2).2).2).2).1).1
end RH65K_0252

namespace RH65K_0253
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group031).2).2).2).2).2).1).1
end RH65K_0253

namespace RH65K_0254
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group031).2).2).2).2).2).2).1).1
end RH65K_0254

namespace RH65K_0255
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group031).2).2).2).2).2).2).2).1
end RH65K_0255

namespace H65K_PlatformHighBatch0224
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0224.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0224.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0224.samples = true
  exact RH65K_0224.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2164401145 : ℝ) / 65536) ((2170495303 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2164401145 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0224.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2170495303 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0224.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0224

namespace H65K_PlatformHighBatch0225
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0225.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0225.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0225.samples = true
  exact RH65K_0225.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2170495303 : ℝ) / 65536) ((2176607440 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2170495303 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0225.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2176607440 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0225.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0225

namespace H65K_PlatformHighBatch0226
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0226.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0226.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0226.samples = true
  exact RH65K_0226.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2176607440 : ℝ) / 65536) ((2182715340 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2176607440 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0226.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2182715340 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0226.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0226

namespace H65K_PlatformHighBatch0227
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0227.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0227.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0227.samples = true
  exact RH65K_0227.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2182715340 : ℝ) / 65536) ((2188797963 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2182715340 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0227.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2188797963 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0227.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0227

namespace H65K_PlatformHighBatch0228
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0228.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0228.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0228.samples = true
  exact RH65K_0228.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2188797963 : ℝ) / 65536) ((2194881356 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2188797963 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0228.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2194881356 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0228.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0228

namespace H65K_PlatformHighBatch0229
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0229.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0229.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0229.samples = true
  exact RH65K_0229.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2194881356 : ℝ) / 65536) ((2200990288 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2194881356 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0229.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2200990288 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0229.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0229

namespace H65K_PlatformHighBatch0230
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0230.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0230.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0230.samples = true
  exact RH65K_0230.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2200990288 : ℝ) / 65536) ((2207084416 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2200990288 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0230.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2207084416 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0230.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0230

namespace H65K_PlatformHighBatch0231
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0231.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0231.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0231.samples = true
  exact RH65K_0231.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2207084416 : ℝ) / 65536) ((2213164268 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2207084416 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0231.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2213164268 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0231.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0231

namespace H65K_PlatformHighBatch0232
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0232.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0232.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0232.samples = true
  exact RH65K_0232.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2213164268 : ℝ) / 65536) ((2219245081 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2213164268 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0232.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2219245081 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0232.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0232

namespace H65K_PlatformHighBatch0233
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0233.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0233.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0233.samples = true
  exact RH65K_0233.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2219245081 : ℝ) / 65536) ((2225340870 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2219245081 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0233.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2225340870 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0233.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0233

namespace H65K_PlatformHighBatch0234
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0234.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0234.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0234.samples = true
  exact RH65K_0234.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2225340870 : ℝ) / 65536) ((2231439682 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2225340870 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0234.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2231439682 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0234.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0234

namespace H65K_PlatformHighBatch0235
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0235.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0235.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0235.samples = true
  exact RH65K_0235.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2231439682 : ℝ) / 65536) ((2237500165 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2231439682 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0235.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2237500165 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0235.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0235

namespace H65K_PlatformHighBatch0236
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0236.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0236.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0236.samples = true
  exact RH65K_0236.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2237500165 : ℝ) / 65536) ((2243581784 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2237500165 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0236.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2243581784 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0236.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0236

namespace H65K_PlatformHighBatch0237
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0237.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0237.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0237.samples = true
  exact RH65K_0237.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2243581784 : ℝ) / 65536) ((2249658249 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2243581784 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0237.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2249658249 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0237.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0237

namespace H65K_PlatformHighBatch0238
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0238.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0238.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0238.samples = true
  exact RH65K_0238.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2249658249 : ℝ) / 65536) ((2255748210 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2249658249 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0238.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2255748210 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0238.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0238

namespace H65K_PlatformHighBatch0239
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0239.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0239.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0239.samples = true
  exact RH65K_0239.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2255748210 : ℝ) / 65536) ((2261827366 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2255748210 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0239.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2261827366 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0239.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0239

namespace H65K_PlatformHighBatch0240
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0240.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0240.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0240.samples = true
  exact RH65K_0240.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2261827366 : ℝ) / 65536) ((2267880205 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2261827366 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0240.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2267880205 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0240.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0240

namespace H65K_PlatformHighBatch0241
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0241.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0241.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0241.samples = true
  exact RH65K_0241.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2267880205 : ℝ) / 65536) ((2273930553 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2267880205 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0241.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2273930553 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0241.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0241

namespace H65K_PlatformHighBatch0242
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0242.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0242.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0242.samples = true
  exact RH65K_0242.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2273930553 : ℝ) / 65536) ((2280028919 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2273930553 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0242.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2280028919 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0242.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0242

namespace H65K_PlatformHighBatch0243
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0243.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0243.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0243.samples = true
  exact RH65K_0243.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2280028919 : ℝ) / 65536) ((2286109490 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2280028919 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0243.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2286109490 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0243.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0243

namespace H65K_PlatformHighBatch0244
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0244.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0244.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0244.samples = true
  exact RH65K_0244.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2286109490 : ℝ) / 65536) ((2292158812 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2286109490 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0244.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2292158812 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0244.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0244

namespace H65K_PlatformHighBatch0245
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0245.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0245.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0245.samples = true
  exact RH65K_0245.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2292158812 : ℝ) / 65536) ((2298203685 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2292158812 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0245.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2298203685 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0245.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0245

namespace H65K_PlatformHighBatch0246
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0246.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0246.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0246.samples = true
  exact RH65K_0246.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2298203685 : ℝ) / 65536) ((2304272520 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2298203685 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0246.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2304272520 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0246.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0246

namespace H65K_PlatformHighBatch0247
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0247.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0247.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0247.samples = true
  exact RH65K_0247.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2304272520 : ℝ) / 65536) ((2310342347 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2304272520 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0247.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2310342347 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0247.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0247

namespace H65K_PlatformHighBatch0248
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0248.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0248.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0248.samples = true
  exact RH65K_0248.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2310342347 : ℝ) / 65536) ((2316405291 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2310342347 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0248.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2316405291 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0248.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0248

namespace H65K_PlatformHighBatch0249
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0249.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0249.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0249.samples = true
  exact RH65K_0249.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2316405291 : ℝ) / 65536) ((2322460122 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2316405291 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0249.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2322460122 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0249.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0249

namespace H65K_PlatformHighBatch0250
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0250.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0250.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0250.samples = true
  exact RH65K_0250.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2322460122 : ℝ) / 65536) ((2328502769 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2322460122 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0250.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2328502769 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0250.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0250

namespace H65K_PlatformHighBatch0251
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0251.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0251.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0251.samples = true
  exact RH65K_0251.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2328502769 : ℝ) / 65536) ((2334538663 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2328502769 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0251.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2334538663 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0251.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0251

namespace H65K_PlatformHighBatch0252
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0252.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0252.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0252.samples = true
  exact RH65K_0252.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2334538663 : ℝ) / 65536) ((2340594180 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2334538663 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0252.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2340594180 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0252.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0252

namespace H65K_PlatformHighBatch0253
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0253.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0253.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0253.samples = true
  exact RH65K_0253.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2340594180 : ℝ) / 65536) ((2346661178 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2340594180 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0253.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2346661178 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0253.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0253

namespace H65K_PlatformHighBatch0254
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0254.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0254.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0254.samples = true
  exact RH65K_0254.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2346661178 : ℝ) / 65536) ((2352703615 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2346661178 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0254.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2352703615 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0254.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0254

namespace H65K_PlatformHighBatch0255
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0255.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0255.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0255.samples = true
  exact RH65K_0255.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2352703615 : ℝ) / 65536) ((2358748050 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2352703615 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0255.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2358748050 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0255.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0255

theorem solution : RS5.BandZeros ((2164401145 : ℝ) / 65536) ((2358748050 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0224.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0225.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0226.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0227.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0228.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0229.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0230.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0231.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0232.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0233.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0234.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0235.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0236.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0237.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0238.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0239.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0240.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0241.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0242.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0243.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0244.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0245.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0246.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0247.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0248.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0249.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0250.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0251.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0252.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0253.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0254.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0255.zeros
  exact h31
