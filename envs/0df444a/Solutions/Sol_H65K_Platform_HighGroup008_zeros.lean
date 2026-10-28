-- Prove2me | solution 1 for H65K.Platform.HighGroup008.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:04:28.180362+00:00
-- url     : https://prove2.me/submissions/3d7c7f9a-d57a-45a0-9534-69944dae57ec

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group032
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group033
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group034
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group035
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0256
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group032).1).1
end RH65K_0256

namespace RH65K_0257
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group032).2).1).1
end RH65K_0257

namespace RH65K_0258
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group032).2).2).1).1
end RH65K_0258

namespace RH65K_0259
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group032).2).2).2).1).1
end RH65K_0259

namespace RH65K_0260
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group032).2).2).2).2).1).1
end RH65K_0260

namespace RH65K_0261
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group032).2).2).2).2).2).1).1
end RH65K_0261

namespace RH65K_0262
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group032).2).2).2).2).2).2).1).1
end RH65K_0262

namespace RH65K_0263
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group032).2).2).2).2).2).2).2).1
end RH65K_0263

namespace RH65K_0264
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group033).1).1
end RH65K_0264

namespace RH65K_0265
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group033).2).1).1
end RH65K_0265

namespace RH65K_0266
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group033).2).2).1).1
end RH65K_0266

namespace RH65K_0267
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group033).2).2).2).1).1
end RH65K_0267

namespace RH65K_0268
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group033).2).2).2).2).1).1
end RH65K_0268

namespace RH65K_0269
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group033).2).2).2).2).2).1).1
end RH65K_0269

namespace RH65K_0270
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group033).2).2).2).2).2).2).1).1
end RH65K_0270

namespace RH65K_0271
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group033).2).2).2).2).2).2).2).1
end RH65K_0271

namespace RH65K_0272
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group034).1).1
end RH65K_0272

namespace RH65K_0273
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group034).2).1).1
end RH65K_0273

namespace RH65K_0274
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group034).2).2).1).1
end RH65K_0274

namespace RH65K_0275
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group034).2).2).2).1).1
end RH65K_0275

namespace RH65K_0276
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group034).2).2).2).2).1).1
end RH65K_0276

namespace RH65K_0277
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group034).2).2).2).2).2).1).1
end RH65K_0277

namespace RH65K_0278
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group034).2).2).2).2).2).2).1).1
end RH65K_0278

namespace RH65K_0279
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group034).2).2).2).2).2).2).2).1
end RH65K_0279

namespace RH65K_0280
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group035).1).1
end RH65K_0280

namespace RH65K_0281
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group035).2).1).1
end RH65K_0281

namespace RH65K_0282
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group035).2).2).1).1
end RH65K_0282

namespace RH65K_0283
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group035).2).2).2).1).1
end RH65K_0283

namespace RH65K_0284
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group035).2).2).2).2).1).1
end RH65K_0284

namespace RH65K_0285
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group035).2).2).2).2).2).1).1
end RH65K_0285

namespace RH65K_0286
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group035).2).2).2).2).2).2).1).1
end RH65K_0286

namespace RH65K_0287
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group035).2).2).2).2).2).2).2).1
end RH65K_0287

namespace H65K_PlatformHighBatch0256
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0256.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0256.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0256.samples = true
  exact RH65K_0256.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2358748050 : ℝ) / 65536) ((2364785608 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2358748050 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0256.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2364785608 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0256.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0256

namespace H65K_PlatformHighBatch0257
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0257.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0257.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0257.samples = true
  exact RH65K_0257.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2364785608 : ℝ) / 65536) ((2370817541 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2364785608 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0257.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2370817541 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0257.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0257

namespace H65K_PlatformHighBatch0258
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0258.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0258.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0258.samples = true
  exact RH65K_0258.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2370817541 : ℝ) / 65536) ((2376879987 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2370817541 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0258.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2376879987 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0258.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0258

namespace H65K_PlatformHighBatch0259
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0259.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0259.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0259.samples = true
  exact RH65K_0259.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2376879987 : ℝ) / 65536) ((2382908341 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2376879987 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0259.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2382908341 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0259.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0259

namespace H65K_PlatformHighBatch0260
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0260.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0260.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0260.samples = true
  exact RH65K_0260.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2382908341 : ℝ) / 65536) ((2388942439 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2382908341 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0260.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2388942439 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0260.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0260

namespace H65K_PlatformHighBatch0261
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0261.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0261.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0261.samples = true
  exact RH65K_0261.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2388942439 : ℝ) / 65536) ((2394952173 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2388942439 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0261.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2394952173 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0261.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0261

namespace H65K_PlatformHighBatch0262
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0262.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0262.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0262.samples = true
  exact RH65K_0262.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2394952173 : ℝ) / 65536) ((2400992107 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2394952173 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0262.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2400992107 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0262.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0262

namespace H65K_PlatformHighBatch0263
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0263.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0263.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0263.samples = true
  exact RH65K_0263.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2400992107 : ℝ) / 65536) ((2407012833 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2400992107 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0263.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2407012833 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0263.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0263

namespace H65K_PlatformHighBatch0264
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0264.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0264.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0264.samples = true
  exact RH65K_0264.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2407012833 : ℝ) / 65536) ((2413059191 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2407012833 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0264.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2413059191 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0264.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0264

namespace H65K_PlatformHighBatch0265
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0265.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0265.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0265.samples = true
  exact RH65K_0265.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2413059191 : ℝ) / 65536) ((2419111810 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2413059191 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0265.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2419111810 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0265.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0265

namespace H65K_PlatformHighBatch0266
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0266.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0266.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0266.samples = true
  exact RH65K_0266.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2419111810 : ℝ) / 65536) ((2425137302 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2419111810 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0266.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2425137302 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0266.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0266

namespace H65K_PlatformHighBatch0267
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0267.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0267.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0267.samples = true
  exact RH65K_0267.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2425137302 : ℝ) / 65536) ((2431153687 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2425137302 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0267.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2431153687 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0267.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0267

namespace H65K_PlatformHighBatch0268
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0268.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0268.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0268.samples = true
  exact RH65K_0268.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2431153687 : ℝ) / 65536) ((2437164803 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2431153687 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0268.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2437164803 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0268.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0268

namespace H65K_PlatformHighBatch0269
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0269.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0269.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0269.samples = true
  exact RH65K_0269.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2437164803 : ℝ) / 65536) ((2443185129 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2437164803 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0269.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2443185129 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0269.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0269

namespace H65K_PlatformHighBatch0270
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0270.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0270.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0270.samples = true
  exact RH65K_0270.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2443185129 : ℝ) / 65536) ((2449191126 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2443185129 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0270.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2449191126 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0270.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0270

namespace H65K_PlatformHighBatch0271
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0271.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0271.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0271.samples = true
  exact RH65K_0271.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2449191126 : ℝ) / 65536) ((2455214699 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2449191126 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0271.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2455214699 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0271.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0271

namespace H65K_PlatformHighBatch0272
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0272.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0272.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0272.samples = true
  exact RH65K_0272.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2455214699 : ℝ) / 65536) ((2461226303 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2455214699 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0272.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2461226303 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0272.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0272

namespace H65K_PlatformHighBatch0273
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0273.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0273.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0273.samples = true
  exact RH65K_0273.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2461226303 : ℝ) / 65536) ((2467253898 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2461226303 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0273.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2467253898 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0273.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0273

namespace H65K_PlatformHighBatch0274
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0274.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0274.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0274.samples = true
  exact RH65K_0274.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2467253898 : ℝ) / 65536) ((2473248071 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2467253898 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0274.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2473248071 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0274.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0274

namespace H65K_PlatformHighBatch0275
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0275.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0275.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0275.samples = true
  exact RH65K_0275.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2473248071 : ℝ) / 65536) ((2479273550 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2473248071 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0275.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2479273550 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0275.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0275

namespace H65K_PlatformHighBatch0276
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0276.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0276.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0276.samples = true
  exact RH65K_0276.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2479273550 : ℝ) / 65536) ((2485258673 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2479273550 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0276.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2485258673 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0276.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0276

namespace H65K_PlatformHighBatch0277
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0277.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0277.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0277.samples = true
  exact RH65K_0277.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2485258673 : ℝ) / 65536) ((2491275982 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2485258673 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0277.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2491275982 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0277.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0277

namespace H65K_PlatformHighBatch0278
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0278.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0278.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0278.samples = true
  exact RH65K_0278.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2491275982 : ℝ) / 65536) ((2497269167 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2491275982 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0278.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2497269167 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0278.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0278

namespace H65K_PlatformHighBatch0279
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0279.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0279.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0279.samples = true
  exact RH65K_0279.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2497269167 : ℝ) / 65536) ((2503269043 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2497269167 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0279.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2503269043 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0279.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0279

namespace H65K_PlatformHighBatch0280
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0280.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0280.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0280.samples = true
  exact RH65K_0280.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2503269043 : ℝ) / 65536) ((2509270092 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2503269043 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0280.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2509270092 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0280.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0280

namespace H65K_PlatformHighBatch0281
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0281.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0281.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0281.samples = true
  exact RH65K_0281.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2509270092 : ℝ) / 65536) ((2515287706 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2509270092 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0281.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2515287706 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0281.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0281

namespace H65K_PlatformHighBatch0282
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0282.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0282.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0282.samples = true
  exact RH65K_0282.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2515287706 : ℝ) / 65536) ((2521283812 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2515287706 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0282.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2521283812 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0282.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0282

namespace H65K_PlatformHighBatch0283
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0283.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0283.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0283.samples = true
  exact RH65K_0283.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2521283812 : ℝ) / 65536) ((2527290005 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2521283812 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0283.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2527290005 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0283.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0283

namespace H65K_PlatformHighBatch0284
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0284.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0284.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0284.samples = true
  exact RH65K_0284.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2527290005 : ℝ) / 65536) ((2533280956 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2527290005 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0284.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2533280956 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0284.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0284

namespace H65K_PlatformHighBatch0285
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0285.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0285.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0285.samples = true
  exact RH65K_0285.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2533280956 : ℝ) / 65536) ((2539261898 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2533280956 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0285.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2539261898 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0285.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0285

namespace H65K_PlatformHighBatch0286
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0286.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0286.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0286.samples = true
  exact RH65K_0286.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2539261898 : ℝ) / 65536) ((2545262659 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2539261898 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0286.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2545262659 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0286.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0286

namespace H65K_PlatformHighBatch0287
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0287.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0287.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0287.samples = true
  exact RH65K_0287.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2545262659 : ℝ) / 65536) ((2551237424 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2545262659 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0287.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2551237424 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0287.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0287

theorem solution : RS5.BandZeros ((2358748050 : ℝ) / 65536) ((2551237424 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0256.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0257.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0258.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0259.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0260.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0261.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0262.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0263.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0264.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0265.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0266.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0267.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0268.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0269.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0270.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0271.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0272.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0273.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0274.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0275.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0276.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0277.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0278.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0279.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0280.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0281.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0282.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0283.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0284.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0285.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0286.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0287.zeros
  exact h31
