-- Prove2me | solution 1 for H65K.Platform.HighGroup009.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:04:59.156664+00:00
-- url     : https://prove2.me/submissions/b9ed94aa-9ecd-40d2-98a8-ac997ef22094

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group036
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group037
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group038
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group039
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0288
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group036).1).1
end RH65K_0288

namespace RH65K_0289
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group036).2).1).1
end RH65K_0289

namespace RH65K_0290
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group036).2).2).1).1
end RH65K_0290

namespace RH65K_0291
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group036).2).2).2).1).1
end RH65K_0291

namespace RH65K_0292
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group036).2).2).2).2).1).1
end RH65K_0292

namespace RH65K_0293
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group036).2).2).2).2).2).1).1
end RH65K_0293

namespace RH65K_0294
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group036).2).2).2).2).2).2).1).1
end RH65K_0294

namespace RH65K_0295
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group036).2).2).2).2).2).2).2).1
end RH65K_0295

namespace RH65K_0296
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group037).1).1
end RH65K_0296

namespace RH65K_0297
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group037).2).1).1
end RH65K_0297

namespace RH65K_0298
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group037).2).2).1).1
end RH65K_0298

namespace RH65K_0299
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group037).2).2).2).1).1
end RH65K_0299

namespace RH65K_0300
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group037).2).2).2).2).1).1
end RH65K_0300

namespace RH65K_0301
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group037).2).2).2).2).2).1).1
end RH65K_0301

namespace RH65K_0302
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group037).2).2).2).2).2).2).1).1
end RH65K_0302

namespace RH65K_0303
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group037).2).2).2).2).2).2).2).1
end RH65K_0303

namespace RH65K_0304
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group038).1).1
end RH65K_0304

namespace RH65K_0305
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group038).2).1).1
end RH65K_0305

namespace RH65K_0306
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group038).2).2).1).1
end RH65K_0306

namespace RH65K_0307
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group038).2).2).2).1).1
end RH65K_0307

namespace RH65K_0308
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group038).2).2).2).2).1).1
end RH65K_0308

namespace RH65K_0309
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group038).2).2).2).2).2).1).1
end RH65K_0309

namespace RH65K_0310
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group038).2).2).2).2).2).2).1).1
end RH65K_0310

namespace RH65K_0311
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group038).2).2).2).2).2).2).2).1
end RH65K_0311

namespace RH65K_0312
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group039).1).1
end RH65K_0312

namespace RH65K_0313
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group039).2).1).1
end RH65K_0313

namespace RH65K_0314
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group039).2).2).1).1
end RH65K_0314

namespace RH65K_0315
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group039).2).2).2).1).1
end RH65K_0315

namespace RH65K_0316
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group039).2).2).2).2).1).1
end RH65K_0316

namespace RH65K_0317
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group039).2).2).2).2).2).1).1
end RH65K_0317

namespace RH65K_0318
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group039).2).2).2).2).2).2).1).1
end RH65K_0318

namespace RH65K_0319
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group039).2).2).2).2).2).2).2).1
end RH65K_0319

namespace H65K_PlatformHighBatch0288
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0288.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0288.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0288.samples = true
  exact RH65K_0288.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2551237424 : ℝ) / 65536) ((2557226630 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2551237424 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0288.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2557226630 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0288.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0288

namespace H65K_PlatformHighBatch0289
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0289.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0289.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0289.samples = true
  exact RH65K_0289.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2557226630 : ℝ) / 65536) ((2563218446 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2557226630 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0289.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2563218446 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0289.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0289

namespace H65K_PlatformHighBatch0290
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0290.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0290.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0290.samples = true
  exact RH65K_0290.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2563218446 : ℝ) / 65536) ((2569201728 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2563218446 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0290.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2569201728 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0290.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0290

namespace H65K_PlatformHighBatch0291
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0291.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0291.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0291.samples = true
  exact RH65K_0291.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2569201728 : ℝ) / 65536) ((2575188972 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2569201728 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0291.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2575188972 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0291.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0291

namespace H65K_PlatformHighBatch0292
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0292.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0292.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0292.samples = true
  exact RH65K_0292.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2575188972 : ℝ) / 65536) ((2581159958 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2575188972 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0292.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2581159958 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0292.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0292

namespace H65K_PlatformHighBatch0293
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0293.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0293.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0293.samples = true
  exact RH65K_0293.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2581159958 : ℝ) / 65536) ((2587157538 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2581159958 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0293.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2587157538 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0293.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0293

namespace H65K_PlatformHighBatch0294
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0294.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0294.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0294.samples = true
  exact RH65K_0294.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2587157538 : ℝ) / 65536) ((2593147885 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2587157538 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0294.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2593147885 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0294.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0294

namespace H65K_PlatformHighBatch0295
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0295.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0295.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0295.samples = true
  exact RH65K_0295.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2593147885 : ℝ) / 65536) ((2599126703 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2593147885 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0295.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2599126703 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0295.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0295

namespace H65K_PlatformHighBatch0296
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0296.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0296.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0296.samples = true
  exact RH65K_0296.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2599126703 : ℝ) / 65536) ((2605113924 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2599126703 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0296.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2605113924 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0296.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0296

namespace H65K_PlatformHighBatch0297
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0297.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0297.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0297.samples = true
  exact RH65K_0297.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2605113924 : ℝ) / 65536) ((2611082755 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2605113924 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0297.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2611082755 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0297.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0297

namespace H65K_PlatformHighBatch0298
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0298.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0298.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0298.samples = true
  exact RH65K_0298.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2611082755 : ℝ) / 65536) ((2617042959 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2611082755 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0298.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2617042959 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0298.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0298

namespace H65K_PlatformHighBatch0299
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0299.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0299.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0299.samples = true
  exact RH65K_0299.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2617042959 : ℝ) / 65536) ((2623019713 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2617042959 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0299.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2623019713 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0299.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0299

namespace H65K_PlatformHighBatch0300
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0300.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0300.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0300.samples = true
  exact RH65K_0300.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2623019713 : ℝ) / 65536) ((2628982342 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2623019713 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0300.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2628982342 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0300.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0300

namespace H65K_PlatformHighBatch0301
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0301.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0301.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0301.samples = true
  exact RH65K_0301.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2628982342 : ℝ) / 65536) ((2634941023 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2628982342 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0301.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2634941023 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0301.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0301

namespace H65K_PlatformHighBatch0302
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0302.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0302.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0302.samples = true
  exact RH65K_0302.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2634941023 : ℝ) / 65536) ((2640911702 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2634941023 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0302.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2640911702 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0302.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0302

namespace H65K_PlatformHighBatch0303
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0303.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0303.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0303.samples = true
  exact RH65K_0303.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2640911702 : ℝ) / 65536) ((2646865086 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2640911702 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0303.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2646865086 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0303.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0303

namespace H65K_PlatformHighBatch0304
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0304.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0304.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0304.samples = true
  exact RH65K_0304.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2646865086 : ℝ) / 65536) ((2652835642 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2646865086 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0304.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2652835642 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0304.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0304

namespace H65K_PlatformHighBatch0305
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0305.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0305.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0305.samples = true
  exact RH65K_0305.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2652835642 : ℝ) / 65536) ((2658787587 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2652835642 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0305.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2658787587 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0305.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0305

namespace H65K_PlatformHighBatch0306
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0306.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0306.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0306.samples = true
  exact RH65K_0306.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2658787587 : ℝ) / 65536) ((2664747036 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2658787587 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0306.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2664747036 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0306.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0306

namespace H65K_PlatformHighBatch0307
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0307.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0307.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0307.samples = true
  exact RH65K_0307.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2664747036 : ℝ) / 65536) ((2670710705 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2664747036 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0307.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2670710705 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0307.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0307

namespace H65K_PlatformHighBatch0308
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0308.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0308.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0308.samples = true
  exact RH65K_0308.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2670710705 : ℝ) / 65536) ((2676671844 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2670710705 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0308.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2676671844 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0308.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0308

namespace H65K_PlatformHighBatch0309
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0309.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0309.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0309.samples = true
  exact RH65K_0309.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2676671844 : ℝ) / 65536) ((2682640281 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2676671844 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0309.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2682640281 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0309.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0309

namespace H65K_PlatformHighBatch0310
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0310.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0310.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0310.samples = true
  exact RH65K_0310.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2682640281 : ℝ) / 65536) ((2688590692 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2682640281 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0310.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2688590692 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0310.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0310

namespace H65K_PlatformHighBatch0311
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0311.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0311.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0311.samples = true
  exact RH65K_0311.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2688590692 : ℝ) / 65536) ((2694528301 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2688590692 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0311.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2694528301 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0311.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0311

namespace H65K_PlatformHighBatch0312
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0312.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0312.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0312.samples = true
  exact RH65K_0312.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2694528301 : ℝ) / 65536) ((2700467614 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2694528301 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0312.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2700467614 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0312.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0312

namespace H65K_PlatformHighBatch0313
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0313.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0313.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0313.samples = true
  exact RH65K_0313.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2700467614 : ℝ) / 65536) ((2706428844 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2700467614 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0313.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2706428844 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0313.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0313

namespace H65K_PlatformHighBatch0314
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0314.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0314.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0314.samples = true
  exact RH65K_0314.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2706428844 : ℝ) / 65536) ((2712376287 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2706428844 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0314.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2712376287 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0314.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0314

namespace H65K_PlatformHighBatch0315
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0315.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0315.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0315.samples = true
  exact RH65K_0315.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2712376287 : ℝ) / 65536) ((2718316572 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2712376287 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0315.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2718316572 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0315.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0315

namespace H65K_PlatformHighBatch0316
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0316.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0316.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0316.samples = true
  exact RH65K_0316.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2718316572 : ℝ) / 65536) ((2724278403 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2718316572 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0316.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2724278403 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0316.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0316

namespace H65K_PlatformHighBatch0317
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0317.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0317.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0317.samples = true
  exact RH65K_0317.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2724278403 : ℝ) / 65536) ((2730227144 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2724278403 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0317.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2730227144 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0317.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0317

namespace H65K_PlatformHighBatch0318
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0318.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0318.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0318.samples = true
  exact RH65K_0318.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2730227144 : ℝ) / 65536) ((2736168834 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2730227144 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0318.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2736168834 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0318.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0318

namespace H65K_PlatformHighBatch0319
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0319.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0319.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0319.samples = true
  exact RH65K_0319.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((2736168834 : ℝ) / 65536) ((2742087245 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((2736168834 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0319.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((2742087245 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0319.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0319

theorem solution : RS5.BandZeros ((2551237424 : ℝ) / 65536) ((2742087245 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0288.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0289.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0290.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0291.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0292.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0293.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0294.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0295.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0296.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0297.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0298.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0299.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0300.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0301.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0302.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0303.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0304.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0305.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0306.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0307.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0308.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0309.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0310.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0311.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0312.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0313.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0314.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0315.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0316.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0317.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0318.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0319.zeros
  exact h31
