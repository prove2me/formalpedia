-- Prove2me | solution 1 for H65K.Platform.HighGroup010.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:05:23.995551+00:00
-- url     : https://prove2.me/submissions/70f54ee4-cabf-4c44-b92f-7cdcda1f1631

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group040
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group041
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group042
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group043
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0320
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group040).1).1
end RH65K_0320

namespace RH65K_0321
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group040).2).1).1
end RH65K_0321

namespace RH65K_0322
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group040).2).2).1).1
end RH65K_0322

namespace RH65K_0323
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group040).2).2).2).1).1
end RH65K_0323

namespace RH65K_0324
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group040).2).2).2).2).1).1
end RH65K_0324

namespace RH65K_0325
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group040).2).2).2).2).2).1).1
end RH65K_0325

namespace RH65K_0326
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group040).2).2).2).2).2).2).1).1
end RH65K_0326

namespace RH65K_0327
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group040).2).2).2).2).2).2).2).1
end RH65K_0327

namespace RH65K_0328
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group041).1).1
end RH65K_0328

namespace RH65K_0329
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group041).2).1).1
end RH65K_0329

namespace RH65K_0330
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group041).2).2).1).1
end RH65K_0330

namespace RH65K_0331
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group041).2).2).2).1).1
end RH65K_0331

namespace RH65K_0332
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group041).2).2).2).2).1).1
end RH65K_0332

namespace RH65K_0333
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group041).2).2).2).2).2).1).1
end RH65K_0333

namespace RH65K_0334
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group041).2).2).2).2).2).2).1).1
end RH65K_0334

namespace RH65K_0335
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group041).2).2).2).2).2).2).2).1
end RH65K_0335

namespace RH65K_0336
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group042).1).1
end RH65K_0336

namespace RH65K_0337
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group042).2).1).1
end RH65K_0337

namespace RH65K_0338
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group042).2).2).1).1
end RH65K_0338

namespace RH65K_0339
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group042).2).2).2).1).1
end RH65K_0339

namespace RH65K_0340
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group042).2).2).2).2).1).1
end RH65K_0340

namespace RH65K_0341
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group042).2).2).2).2).2).1).1
end RH65K_0341

namespace RH65K_0342
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group042).2).2).2).2).2).2).1).1
end RH65K_0342

namespace RH65K_0343
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group042).2).2).2).2).2).2).2).1
end RH65K_0343

namespace RH65K_0344
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group043).1).1
end RH65K_0344

namespace RH65K_0345
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group043).2).1).1
end RH65K_0345

namespace RH65K_0346
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group043).2).2).1).1
end RH65K_0346

namespace RH65K_0347
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group043).2).2).2).1).1
end RH65K_0347

namespace RH65K_0348
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group043).2).2).2).2).1).1
end RH65K_0348

namespace RH65K_0349
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group043).2).2).2).2).2).1).1
end RH65K_0349

namespace RH65K_0350
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group043).2).2).2).2).2).2).1).1
end RH65K_0350

namespace RH65K_0351
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group043).2).2).2).2).2).2).2).1
end RH65K_0351

namespace H65K_PlatformHighBatch0320
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0320.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0320.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0320.samples = true
  exact RH65K_0320.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2742087245 : ℝ) / 65536) ((2748026382 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2742087245 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0320.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2748026382 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0320.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0320

namespace H65K_PlatformHighBatch0321
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0321.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0321.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0321.samples = true
  exact RH65K_0321.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2748026382 : ℝ) / 65536) ((2753974656 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2748026382 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0321.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2753974656 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0321.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0321

namespace H65K_PlatformHighBatch0322
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0322.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0322.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0322.samples = true
  exact RH65K_0322.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2753974656 : ℝ) / 65536) ((2759919117 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2753974656 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0322.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2759919117 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0322.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0322

namespace H65K_PlatformHighBatch0323
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0323.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0323.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0323.samples = true
  exact RH65K_0323.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2759919117 : ℝ) / 65536) ((2765851100 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2759919117 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0323.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2765851100 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0323.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0323

namespace H65K_PlatformHighBatch0324
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0324.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0324.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0324.samples = true
  exact RH65K_0324.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2765851100 : ℝ) / 65536) ((2771788214 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2765851100 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0324.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2771788214 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0324.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0324

namespace H65K_PlatformHighBatch0325
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0325.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0325.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0325.samples = true
  exact RH65K_0325.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2771788214 : ℝ) / 65536) ((2777702793 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2771788214 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0325.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2777702793 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0325.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0325

namespace H65K_PlatformHighBatch0326
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0326.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0326.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0326.samples = true
  exact RH65K_0326.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2777702793 : ℝ) / 65536) ((2783637683 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2777702793 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0326.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2783637683 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0326.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0326

namespace H65K_PlatformHighBatch0327
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0327.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0327.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0327.samples = true
  exact RH65K_0327.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2783637683 : ℝ) / 65536) ((2789574850 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2783637683 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0327.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2789574850 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0327.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0327

namespace H65K_PlatformHighBatch0328
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0328.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0328.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0328.samples = true
  exact RH65K_0328.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2789574850 : ℝ) / 65536) ((2795516628 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2789574850 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0328.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2795516628 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0328.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0328

namespace H65K_PlatformHighBatch0329
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0329.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0329.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0329.samples = true
  exact RH65K_0329.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2795516628 : ℝ) / 65536) ((2801431857 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2795516628 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0329.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2801431857 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0329.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0329

namespace H65K_PlatformHighBatch0330
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0330.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0330.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0330.samples = true
  exact RH65K_0330.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2801431857 : ℝ) / 65536) ((2807352887 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2801431857 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0330.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2807352887 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0330.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0330

namespace H65K_PlatformHighBatch0331
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0331.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0331.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0331.samples = true
  exact RH65K_0331.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2807352887 : ℝ) / 65536) ((2813259901 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2807352887 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0331.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2813259901 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0331.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0331

namespace H65K_PlatformHighBatch0332
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0332.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0332.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0332.samples = true
  exact RH65K_0332.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2813259901 : ℝ) / 65536) ((2819194627 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2813259901 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0332.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2819194627 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0332.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0332

namespace H65K_PlatformHighBatch0333
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0333.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0333.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0333.samples = true
  exact RH65K_0333.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2819194627 : ℝ) / 65536) ((2825132596 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2819194627 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0333.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2825132596 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0333.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0333

namespace H65K_PlatformHighBatch0334
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0334.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0334.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0334.samples = true
  exact RH65K_0334.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2825132596 : ℝ) / 65536) ((2831056327 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2825132596 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0334.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2831056327 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0334.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0334

namespace H65K_PlatformHighBatch0335
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0335.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0335.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0335.samples = true
  exact RH65K_0335.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2831056327 : ℝ) / 65536) ((2836964926 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2831056327 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0335.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2836964926 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0335.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0335

namespace H65K_PlatformHighBatch0336
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0336.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0336.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0336.samples = true
  exact RH65K_0336.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2836964926 : ℝ) / 65536) ((2842885046 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2836964926 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0336.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2842885046 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0336.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0336

namespace H65K_PlatformHighBatch0337
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0337.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0337.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0337.samples = true
  exact RH65K_0337.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2842885046 : ℝ) / 65536) ((2848799916 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2842885046 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0337.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2848799916 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0337.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0337

namespace H65K_PlatformHighBatch0338
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0338.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0338.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0338.samples = true
  exact RH65K_0338.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2848799916 : ℝ) / 65536) ((2854714160 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2848799916 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0338.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2854714160 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0338.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0338

namespace H65K_PlatformHighBatch0339
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0339.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0339.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0339.samples = true
  exact RH65K_0339.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2854714160 : ℝ) / 65536) ((2860638706 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2854714160 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0339.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2860638706 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0339.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0339

namespace H65K_PlatformHighBatch0340
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0340.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0340.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0340.samples = true
  exact RH65K_0340.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2860638706 : ℝ) / 65536) ((2866537302 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2860638706 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0340.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2866537302 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0340.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0340

namespace H65K_PlatformHighBatch0341
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0341.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0341.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0341.samples = true
  exact RH65K_0341.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2866537302 : ℝ) / 65536) ((2872453500 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2866537302 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0341.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2872453500 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0341.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0341

namespace H65K_PlatformHighBatch0342
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0342.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0342.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0342.samples = true
  exact RH65K_0342.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2872453500 : ℝ) / 65536) ((2878372043 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2872453500 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0342.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2878372043 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0342.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0342

namespace H65K_PlatformHighBatch0343
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0343.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0343.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0343.samples = true
  exact RH65K_0343.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2878372043 : ℝ) / 65536) ((2884291363 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2878372043 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0343.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2884291363 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0343.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0343

namespace H65K_PlatformHighBatch0344
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0344.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0344.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0344.samples = true
  exact RH65K_0344.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2884291363 : ℝ) / 65536) ((2890173722 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2884291363 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0344.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2890173722 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0344.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0344

namespace H65K_PlatformHighBatch0345
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0345.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0345.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0345.samples = true
  exact RH65K_0345.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2890173722 : ℝ) / 65536) ((2896057797 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2890173722 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0345.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2896057797 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0345.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0345

namespace H65K_PlatformHighBatch0346
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0346.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0346.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0346.samples = true
  exact RH65K_0346.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2896057797 : ℝ) / 65536) ((2901961836 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2896057797 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0346.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2901961836 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0346.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0346

namespace H65K_PlatformHighBatch0347
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0347.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0347.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0347.samples = true
  exact RH65K_0347.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2901961836 : ℝ) / 65536) ((2907871850 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2901961836 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0347.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2907871850 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0347.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0347

namespace H65K_PlatformHighBatch0348
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0348.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0348.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0348.samples = true
  exact RH65K_0348.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2907871850 : ℝ) / 65536) ((2913756552 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2907871850 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0348.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2913756552 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0348.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0348

namespace H65K_PlatformHighBatch0349
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0349.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0349.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0349.samples = true
  exact RH65K_0349.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2913756552 : ℝ) / 65536) ((2919662177 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2913756552 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0349.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2919662177 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0349.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0349

namespace H65K_PlatformHighBatch0350
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0350.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0350.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0350.samples = true
  exact RH65K_0350.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2919662177 : ℝ) / 65536) ((2925567255 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2919662177 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0350.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2925567255 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0350.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0350

namespace H65K_PlatformHighBatch0351
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0351.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0351.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0351.samples = true
  exact RH65K_0351.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2925567255 : ℝ) / 65536) ((2931464713 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2925567255 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0351.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2931464713 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0351.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0351

theorem solution : RS5.BandZeros ((2742087245 : ℝ) / 65536) ((2931464713 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0320.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0321.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0322.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0323.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0324.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0325.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0326.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0327.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0328.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0329.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0330.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0331.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0332.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0333.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0334.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0335.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0336.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0337.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0338.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0339.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0340.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0341.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0342.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0343.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0344.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0345.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0346.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0347.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0348.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0349.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0350.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0351.zeros
  exact h31
