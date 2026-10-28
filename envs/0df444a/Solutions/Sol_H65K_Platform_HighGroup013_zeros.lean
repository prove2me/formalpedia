-- Prove2me | solution 1 for H65K.Platform.HighGroup013.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:09:13.609077+00:00
-- url     : https://prove2.me/submissions/5a570f4a-329d-4f2d-9ae3-d1d7346fcfc3

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group052
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group053
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group054
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group055
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0416
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group052).1).1
end RH65K_0416

namespace RH65K_0417
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group052).2).1).1
end RH65K_0417

namespace RH65K_0418
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group052).2).2).1).1
end RH65K_0418

namespace RH65K_0419
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group052).2).2).2).1).1
end RH65K_0419

namespace RH65K_0420
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group052).2).2).2).2).1).1
end RH65K_0420

namespace RH65K_0421
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group052).2).2).2).2).2).1).1
end RH65K_0421

namespace RH65K_0422
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group052).2).2).2).2).2).2).1).1
end RH65K_0422

namespace RH65K_0423
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group052).2).2).2).2).2).2).2).1
end RH65K_0423

namespace RH65K_0424
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group053).1).1
end RH65K_0424

namespace RH65K_0425
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group053).2).1).1
end RH65K_0425

namespace RH65K_0426
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group053).2).2).1).1
end RH65K_0426

namespace RH65K_0427
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group053).2).2).2).1).1
end RH65K_0427

namespace RH65K_0428
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group053).2).2).2).2).1).1
end RH65K_0428

namespace RH65K_0429
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group053).2).2).2).2).2).1).1
end RH65K_0429

namespace RH65K_0430
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group053).2).2).2).2).2).2).1).1
end RH65K_0430

namespace RH65K_0431
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group053).2).2).2).2).2).2).2).1
end RH65K_0431

namespace RH65K_0432
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group054).1).1
end RH65K_0432

namespace RH65K_0433
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group054).2).1).1
end RH65K_0433

namespace RH65K_0434
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group054).2).2).1).1
end RH65K_0434

namespace RH65K_0435
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group054).2).2).2).1).1
end RH65K_0435

namespace RH65K_0436
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group054).2).2).2).2).1).1
end RH65K_0436

namespace RH65K_0437
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group054).2).2).2).2).2).1).1
end RH65K_0437

namespace RH65K_0438
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group054).2).2).2).2).2).2).1).1
end RH65K_0438

namespace RH65K_0439
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group054).2).2).2).2).2).2).2).1
end RH65K_0439

namespace RH65K_0440
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group055).1).1
end RH65K_0440

namespace RH65K_0441
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group055).2).1).1
end RH65K_0441

namespace RH65K_0442
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group055).2).2).1).1
end RH65K_0442

namespace RH65K_0443
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group055).2).2).2).1).1
end RH65K_0443

namespace RH65K_0444
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group055).2).2).2).2).1).1
end RH65K_0444

namespace RH65K_0445
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group055).2).2).2).2).2).1).1
end RH65K_0445

namespace RH65K_0446
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group055).2).2).2).2).2).2).1).1
end RH65K_0446

namespace RH65K_0447
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group055).2).2).2).2).2).2).2).1
end RH65K_0447

namespace H65K_PlatformHighBatch0416
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0416.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0416.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0416.samples = true
  exact RH65K_0416.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3306185316 : ℝ) / 65536) ((3312012422 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3306185316 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0416.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3312012422 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0416.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0416

namespace H65K_PlatformHighBatch0417
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0417.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0417.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0417.samples = true
  exact RH65K_0417.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3312012422 : ℝ) / 65536) ((3317784239 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3312012422 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0417.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3317784239 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0417.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0417

namespace H65K_PlatformHighBatch0418
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0418.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0418.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0418.samples = true
  exact RH65K_0418.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3317784239 : ℝ) / 65536) ((3323623434 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3317784239 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0418.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3323623434 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0418.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0418

namespace H65K_PlatformHighBatch0419
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0419.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0419.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0419.samples = true
  exact RH65K_0419.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3323623434 : ℝ) / 65536) ((3329438765 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3323623434 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0419.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3329438765 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0419.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0419

namespace H65K_PlatformHighBatch0420
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0420.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0420.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0420.samples = true
  exact RH65K_0420.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3329438765 : ℝ) / 65536) ((3335267618 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3329438765 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0420.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3335267618 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0420.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0420

namespace H65K_PlatformHighBatch0421
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0421.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0421.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0421.samples = true
  exact RH65K_0421.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3335267618 : ℝ) / 65536) ((3341052697 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3335267618 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0421.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3341052697 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0421.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0421

namespace H65K_PlatformHighBatch0422
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0422.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0422.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0422.samples = true
  exact RH65K_0422.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3341052697 : ℝ) / 65536) ((3346865378 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3341052697 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0422.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3346865378 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0422.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0422

namespace H65K_PlatformHighBatch0423
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0423.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0423.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0423.samples = true
  exact RH65K_0423.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3346865378 : ℝ) / 65536) ((3352656911 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3346865378 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0423.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3352656911 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0423.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0423

namespace H65K_PlatformHighBatch0424
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0424.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0424.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0424.samples = true
  exact RH65K_0424.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3352656911 : ℝ) / 65536) ((3358493065 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3352656911 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0424.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3358493065 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0424.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0424

namespace H65K_PlatformHighBatch0425
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0425.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0425.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0425.samples = true
  exact RH65K_0425.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3358493065 : ℝ) / 65536) ((3364294613 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3358493065 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0425.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3364294613 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0425.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0425

namespace H65K_PlatformHighBatch0426
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0426.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0426.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0426.samples = true
  exact RH65K_0426.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3364294613 : ℝ) / 65536) ((3370092841 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3364294613 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0426.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3370092841 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0426.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0426

namespace H65K_PlatformHighBatch0427
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0427.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0427.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0427.samples = true
  exact RH65K_0427.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3370092841 : ℝ) / 65536) ((3375878229 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3370092841 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0427.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3375878229 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0427.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0427

namespace H65K_PlatformHighBatch0428
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0428.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0428.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0428.samples = true
  exact RH65K_0428.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3375878229 : ℝ) / 65536) ((3381693722 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3375878229 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0428.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3381693722 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0428.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0428

namespace H65K_PlatformHighBatch0429
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0429.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0429.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0429.samples = true
  exact RH65K_0429.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3381693722 : ℝ) / 65536) ((3387506732 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3381693722 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0429.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3387506732 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0429.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0429

namespace H65K_PlatformHighBatch0430
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0430.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0430.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0430.samples = true
  exact RH65K_0430.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3387506732 : ℝ) / 65536) ((3393301540 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3387506732 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0430.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3393301540 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0430.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0430

namespace H65K_PlatformHighBatch0431
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0431.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0431.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0431.samples = true
  exact RH65K_0431.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3393301540 : ℝ) / 65536) ((3399082472 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3393301540 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0431.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3399082472 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0431.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0431

namespace H65K_PlatformHighBatch0432
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0432.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0432.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0432.samples = true
  exact RH65K_0432.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3399082472 : ℝ) / 65536) ((3404913581 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3399082472 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0432.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3404913581 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0432.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0432

namespace H65K_PlatformHighBatch0433
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0433.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0433.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0433.samples = true
  exact RH65K_0433.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3404913581 : ℝ) / 65536) ((3410690261 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3404913581 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0433.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3410690261 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0433.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0433

namespace H65K_PlatformHighBatch0434
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0434.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0434.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0434.samples = true
  exact RH65K_0434.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3410690261 : ℝ) / 65536) ((3416512613 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3410690261 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0434.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3416512613 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0434.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0434

namespace H65K_PlatformHighBatch0435
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0435.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0435.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0435.samples = true
  exact RH65K_0435.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3416512613 : ℝ) / 65536) ((3422279021 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3416512613 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0435.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3422279021 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0435.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0435

namespace H65K_PlatformHighBatch0436
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0436.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0436.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0436.samples = true
  exact RH65K_0436.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3422279021 : ℝ) / 65536) ((3428074944 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3422279021 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0436.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3428074944 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0436.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0436

namespace H65K_PlatformHighBatch0437
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0437.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0437.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0437.samples = true
  exact RH65K_0437.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3428074944 : ℝ) / 65536) ((3433877478 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3428074944 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0437.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3433877478 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0437.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0437

namespace H65K_PlatformHighBatch0438
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0438.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0438.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0438.samples = true
  exact RH65K_0438.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3433877478 : ℝ) / 65536) ((3439668363 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3433877478 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0438.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3439668363 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0438.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0438

namespace H65K_PlatformHighBatch0439
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0439.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0439.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0439.samples = true
  exact RH65K_0439.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3439668363 : ℝ) / 65536) ((3445442007 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3439668363 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0439.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3445442007 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0439.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0439

namespace H65K_PlatformHighBatch0440
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0440.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0440.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0440.samples = true
  exact RH65K_0440.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3445442007 : ℝ) / 65536) ((3451237534 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3445442007 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0440.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3451237534 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0440.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0440

namespace H65K_PlatformHighBatch0441
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0441.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0441.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0441.samples = true
  exact RH65K_0441.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3451237534 : ℝ) / 65536) ((3457040699 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3451237534 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0441.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3457040699 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0441.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0441

namespace H65K_PlatformHighBatch0442
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0442.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0442.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0442.samples = true
  exact RH65K_0442.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3457040699 : ℝ) / 65536) ((3462819415 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3457040699 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0442.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3462819415 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0442.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0442

namespace H65K_PlatformHighBatch0443
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0443.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0443.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0443.samples = true
  exact RH65K_0443.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3462819415 : ℝ) / 65536) ((3468604257 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3462819415 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0443.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3468604257 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0443.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0443

namespace H65K_PlatformHighBatch0444
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0444.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0444.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0444.samples = true
  exact RH65K_0444.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3468604257 : ℝ) / 65536) ((3474377519 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3468604257 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0444.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3474377519 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0444.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0444

namespace H65K_PlatformHighBatch0445
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0445.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0445.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0445.samples = true
  exact RH65K_0445.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3474377519 : ℝ) / 65536) ((3480202371 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3474377519 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0445.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3480202371 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0445.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0445

namespace H65K_PlatformHighBatch0446
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0446.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0446.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0446.samples = true
  exact RH65K_0446.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3480202371 : ℝ) / 65536) ((3485952646 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3480202371 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0446.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3485952646 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0446.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0446

namespace H65K_PlatformHighBatch0447
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0447.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0447.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0447.samples = true
  exact RH65K_0447.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3485952646 : ℝ) / 65536) ((3491718488 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3485952646 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0447.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3491718488 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0447.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0447

theorem solution : RS5.BandZeros ((3306185316 : ℝ) / 65536) ((3491718488 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0416.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0417.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0418.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0419.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0420.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0421.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0422.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0423.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0424.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0425.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0426.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0427.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0428.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0429.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0430.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0431.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0432.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0433.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0434.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0435.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0436.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0437.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0438.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0439.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0440.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0441.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0442.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0443.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0444.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0445.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0446.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0447.zeros
  exact h31
