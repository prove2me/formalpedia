-- Prove2me | solution 1 for H65K.Platform.HighGroup011.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:05:38.896199+00:00
-- url     : https://prove2.me/submissions/88ac2180-48e2-4fc2-a260-d37b56ba3ffd

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group044
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group045
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group046
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group047
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0352
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group044).1).1
end RH65K_0352

namespace RH65K_0353
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group044).2).1).1
end RH65K_0353

namespace RH65K_0354
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group044).2).2).1).1
end RH65K_0354

namespace RH65K_0355
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group044).2).2).2).1).1
end RH65K_0355

namespace RH65K_0356
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group044).2).2).2).2).1).1
end RH65K_0356

namespace RH65K_0357
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group044).2).2).2).2).2).1).1
end RH65K_0357

namespace RH65K_0358
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group044).2).2).2).2).2).2).1).1
end RH65K_0358

namespace RH65K_0359
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group044).2).2).2).2).2).2).2).1
end RH65K_0359

namespace RH65K_0360
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group045).1).1
end RH65K_0360

namespace RH65K_0361
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group045).2).1).1
end RH65K_0361

namespace RH65K_0362
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group045).2).2).1).1
end RH65K_0362

namespace RH65K_0363
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group045).2).2).2).1).1
end RH65K_0363

namespace RH65K_0364
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group045).2).2).2).2).1).1
end RH65K_0364

namespace RH65K_0365
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group045).2).2).2).2).2).1).1
end RH65K_0365

namespace RH65K_0366
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group045).2).2).2).2).2).2).1).1
end RH65K_0366

namespace RH65K_0367
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group045).2).2).2).2).2).2).2).1
end RH65K_0367

namespace RH65K_0368
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group046).1).1
end RH65K_0368

namespace RH65K_0369
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group046).2).1).1
end RH65K_0369

namespace RH65K_0370
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group046).2).2).1).1
end RH65K_0370

namespace RH65K_0371
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group046).2).2).2).1).1
end RH65K_0371

namespace RH65K_0372
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group046).2).2).2).2).1).1
end RH65K_0372

namespace RH65K_0373
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group046).2).2).2).2).2).1).1
end RH65K_0373

namespace RH65K_0374
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group046).2).2).2).2).2).2).1).1
end RH65K_0374

namespace RH65K_0375
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group046).2).2).2).2).2).2).2).1
end RH65K_0375

namespace RH65K_0376
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group047).1).1
end RH65K_0376

namespace RH65K_0377
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group047).2).1).1
end RH65K_0377

namespace RH65K_0378
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group047).2).2).1).1
end RH65K_0378

namespace RH65K_0379
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group047).2).2).2).1).1
end RH65K_0379

namespace RH65K_0380
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group047).2).2).2).2).1).1
end RH65K_0380

namespace RH65K_0381
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group047).2).2).2).2).2).1).1
end RH65K_0381

namespace RH65K_0382
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group047).2).2).2).2).2).2).1).1
end RH65K_0382

namespace RH65K_0383
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group047).2).2).2).2).2).2).2).1
end RH65K_0383

namespace H65K_PlatformHighBatch0352
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0352.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0352.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0352.samples = true
  exact RH65K_0352.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2931464713 : ℝ) / 65536) ((2937345686 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2931464713 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0352.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2937345686 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0352.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0352

namespace H65K_PlatformHighBatch0353
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0353.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0353.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0353.samples = true
  exact RH65K_0353.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2937345686 : ℝ) / 65536) ((2943242917 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2937345686 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0353.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2943242917 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0353.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0353

namespace H65K_PlatformHighBatch0354
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0354.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0354.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0354.samples = true
  exact RH65K_0354.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2943242917 : ℝ) / 65536) ((2949147880 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2943242917 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0354.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2949147880 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0354.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0354

namespace H65K_PlatformHighBatch0355
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0355.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0355.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0355.samples = true
  exact RH65K_0355.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2949147880 : ℝ) / 65536) ((2955049631 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2949147880 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0355.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2955049631 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0355.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0355

namespace H65K_PlatformHighBatch0356
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0356.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0356.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0356.samples = true
  exact RH65K_0356.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2955049631 : ℝ) / 65536) ((2960928424 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2955049631 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0356.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2960928424 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0356.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0356

namespace H65K_PlatformHighBatch0357
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0357.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0357.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0357.samples = true
  exact RH65K_0357.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2960928424 : ℝ) / 65536) ((2966827842 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2960928424 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0357.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2966827842 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0357.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0357

namespace H65K_PlatformHighBatch0358
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0358.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0358.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0358.samples = true
  exact RH65K_0358.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2966827842 : ℝ) / 65536) ((2972705002 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2966827842 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0358.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2972705002 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0358.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0358

namespace H65K_PlatformHighBatch0359
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0359.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0359.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0359.samples = true
  exact RH65K_0359.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2972705002 : ℝ) / 65536) ((2978559229 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2972705002 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0359.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2978559229 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0359.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0359

namespace H65K_PlatformHighBatch0360
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0360.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0360.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0360.samples = true
  exact RH65K_0360.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2978559229 : ℝ) / 65536) ((2984456425 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2978559229 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0360.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2984456425 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0360.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0360

namespace H65K_PlatformHighBatch0361
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0361.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0361.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0361.samples = true
  exact RH65K_0361.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2984456425 : ℝ) / 65536) ((2990346976 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2984456425 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0361.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2990346976 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0361.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0361

namespace H65K_PlatformHighBatch0362
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0362.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0362.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0362.samples = true
  exact RH65K_0362.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2990346976 : ℝ) / 65536) ((2996220189 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2990346976 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0362.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2996220189 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0362.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0362

namespace H65K_PlatformHighBatch0363
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0363.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0363.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0363.samples = true
  exact RH65K_0363.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2996220189 : ℝ) / 65536) ((3002107733 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2996220189 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0363.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3002107733 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0363.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0363

namespace H65K_PlatformHighBatch0364
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0364.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0364.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0364.samples = true
  exact RH65K_0364.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3002107733 : ℝ) / 65536) ((3007991815 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3002107733 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0364.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3007991815 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0364.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0364

namespace H65K_PlatformHighBatch0365
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0365.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0365.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0365.samples = true
  exact RH65K_0365.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3007991815 : ℝ) / 65536) ((3013872733 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3007991815 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0365.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3013872733 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0365.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0365

namespace H65K_PlatformHighBatch0366
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0366.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0366.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0366.samples = true
  exact RH65K_0366.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3013872733 : ℝ) / 65536) ((3019758633 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3013872733 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0366.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3019758633 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0366.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0366

namespace H65K_PlatformHighBatch0367
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0367.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0367.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0367.samples = true
  exact RH65K_0367.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3019758633 : ℝ) / 65536) ((3025640060 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3019758633 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0367.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3025640060 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0367.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0367

namespace H65K_PlatformHighBatch0368
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0368.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0368.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0368.samples = true
  exact RH65K_0368.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3025640060 : ℝ) / 65536) ((3031486648 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3025640060 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0368.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3031486648 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0368.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0368

namespace H65K_PlatformHighBatch0369
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0369.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0369.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0369.samples = true
  exact RH65K_0369.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3031486648 : ℝ) / 65536) ((3037347137 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3031486648 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0369.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3037347137 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0369.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0369

namespace H65K_PlatformHighBatch0370
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0370.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0370.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0370.samples = true
  exact RH65K_0370.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3037347137 : ℝ) / 65536) ((3043237713 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3037347137 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0370.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3043237713 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0370.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0370

namespace H65K_PlatformHighBatch0371
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0371.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0371.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0371.samples = true
  exact RH65K_0371.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3043237713 : ℝ) / 65536) ((3049105291 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3043237713 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0371.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3049105291 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0371.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0371

namespace H65K_PlatformHighBatch0372
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0372.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0372.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0372.samples = true
  exact RH65K_0372.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3049105291 : ℝ) / 65536) ((3054972325 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3049105291 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0372.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3054972325 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0372.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0372

namespace H65K_PlatformHighBatch0373
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0373.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0373.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0373.samples = true
  exact RH65K_0373.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3054972325 : ℝ) / 65536) ((3060863749 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3054972325 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0373.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3060863749 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0373.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0373

namespace H65K_PlatformHighBatch0374
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0374.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0374.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0374.samples = true
  exact RH65K_0374.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3060863749 : ℝ) / 65536) ((3066722738 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3060863749 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0374.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3066722738 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0374.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0374

namespace H65K_PlatformHighBatch0375
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0375.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0375.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0375.samples = true
  exact RH65K_0375.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3066722738 : ℝ) / 65536) ((3072587111 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3066722738 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0375.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3072587111 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0375.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0375

namespace H65K_PlatformHighBatch0376
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0376.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0376.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0376.samples = true
  exact RH65K_0376.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3072587111 : ℝ) / 65536) ((3078445735 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3072587111 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0376.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3078445735 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0376.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0376

namespace H65K_PlatformHighBatch0377
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0377.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0377.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0377.samples = true
  exact RH65K_0377.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3078445735 : ℝ) / 65536) ((3084290913 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3078445735 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0377.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3084290913 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0377.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0377

namespace H65K_PlatformHighBatch0378
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0378.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0378.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0378.samples = true
  exact RH65K_0378.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3084290913 : ℝ) / 65536) ((3090155812 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3084290913 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0378.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3090155812 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0378.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0378

namespace H65K_PlatformHighBatch0379
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0379.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0379.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0379.samples = true
  exact RH65K_0379.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3090155812 : ℝ) / 65536) ((3096030943 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3090155812 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0379.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3096030943 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0379.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0379

namespace H65K_PlatformHighBatch0380
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0380.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0380.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0380.samples = true
  exact RH65K_0380.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3096030943 : ℝ) / 65536) ((3101873114 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3096030943 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0380.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3101873114 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0380.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0380

namespace H65K_PlatformHighBatch0381
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0381.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0381.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0381.samples = true
  exact RH65K_0381.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3101873114 : ℝ) / 65536) ((3107753084 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3101873114 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0381.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3107753084 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0381.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0381

namespace H65K_PlatformHighBatch0382
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0382.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0382.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0382.samples = true
  exact RH65K_0382.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3107753084 : ℝ) / 65536) ((3113603703 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3107753084 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0382.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3113603703 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0382.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0382

namespace H65K_PlatformHighBatch0383
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0383.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0383.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0383.samples = true
  exact RH65K_0383.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3113603703 : ℝ) / 65536) ((3119454795 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3113603703 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0383.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3119454795 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0383.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0383

theorem solution : RS5.BandZeros ((2931464713 : ℝ) / 65536) ((3119454795 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0352.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0353.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0354.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0355.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0356.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0357.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0358.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0359.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0360.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0361.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0362.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0363.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0364.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0365.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0366.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0367.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0368.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0369.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0370.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0371.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0372.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0373.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0374.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0375.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0376.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0377.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0378.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0379.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0380.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0381.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0382.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0383.zeros
  exact h31
