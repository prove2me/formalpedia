-- Prove2me | solution 1 for H65K.Platform.HighGroup012.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:08:45.694225+00:00
-- url     : https://prove2.me/submissions/e0cd6f1e-58ba-490f-8dee-73d2fcaf3041

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group048
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group049
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group050
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group051
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0384
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group048).1).1
end RH65K_0384

namespace RH65K_0385
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group048).2).1).1
end RH65K_0385

namespace RH65K_0386
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group048).2).2).1).1
end RH65K_0386

namespace RH65K_0387
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group048).2).2).2).1).1
end RH65K_0387

namespace RH65K_0388
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group048).2).2).2).2).1).1
end RH65K_0388

namespace RH65K_0389
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group048).2).2).2).2).2).1).1
end RH65K_0389

namespace RH65K_0390
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group048).2).2).2).2).2).2).1).1
end RH65K_0390

namespace RH65K_0391
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group048).2).2).2).2).2).2).2).1
end RH65K_0391

namespace RH65K_0392
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group049).1).1
end RH65K_0392

namespace RH65K_0393
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group049).2).1).1
end RH65K_0393

namespace RH65K_0394
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group049).2).2).1).1
end RH65K_0394

namespace RH65K_0395
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group049).2).2).2).1).1
end RH65K_0395

namespace RH65K_0396
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group049).2).2).2).2).1).1
end RH65K_0396

namespace RH65K_0397
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group049).2).2).2).2).2).1).1
end RH65K_0397

namespace RH65K_0398
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group049).2).2).2).2).2).2).1).1
end RH65K_0398

namespace RH65K_0399
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group049).2).2).2).2).2).2).2).1
end RH65K_0399

namespace RH65K_0400
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group050).1).1
end RH65K_0400

namespace RH65K_0401
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group050).2).1).1
end RH65K_0401

namespace RH65K_0402
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group050).2).2).1).1
end RH65K_0402

namespace RH65K_0403
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group050).2).2).2).1).1
end RH65K_0403

namespace RH65K_0404
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group050).2).2).2).2).1).1
end RH65K_0404

namespace RH65K_0405
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group050).2).2).2).2).2).1).1
end RH65K_0405

namespace RH65K_0406
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group050).2).2).2).2).2).2).1).1
end RH65K_0406

namespace RH65K_0407
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group050).2).2).2).2).2).2).2).1
end RH65K_0407

namespace RH65K_0408
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group051).1).1
end RH65K_0408

namespace RH65K_0409
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group051).2).1).1
end RH65K_0409

namespace RH65K_0410
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group051).2).2).1).1
end RH65K_0410

namespace RH65K_0411
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group051).2).2).2).1).1
end RH65K_0411

namespace RH65K_0412
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group051).2).2).2).2).1).1
end RH65K_0412

namespace RH65K_0413
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group051).2).2).2).2).2).1).1
end RH65K_0413

namespace RH65K_0414
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group051).2).2).2).2).2).2).1).1
end RH65K_0414

namespace RH65K_0415
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group051).2).2).2).2).2).2).2).1
end RH65K_0415

namespace H65K_PlatformHighBatch0384
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0384.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0384.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0384.samples = true
  exact RH65K_0384.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3119454795 : ℝ) / 65536) ((3125303023 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3119454795 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0384.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3125303023 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0384.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0384

namespace H65K_PlatformHighBatch0385
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0385.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0385.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0385.samples = true
  exact RH65K_0385.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3125303023 : ℝ) / 65536) ((3131142923 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3125303023 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0385.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3131142923 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0385.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0385

namespace H65K_PlatformHighBatch0386
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0386.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0386.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0386.samples = true
  exact RH65K_0386.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3131142923 : ℝ) / 65536) ((3137008994 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3131142923 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0386.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3137008994 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0386.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0386

namespace H65K_PlatformHighBatch0387
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0387.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0387.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0387.samples = true
  exact RH65K_0387.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3137008994 : ℝ) / 65536) ((3142874621 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3137008994 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0387.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3142874621 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0387.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0387

namespace H65K_PlatformHighBatch0388
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0388.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0388.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0388.samples = true
  exact RH65K_0388.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3142874621 : ℝ) / 65536) ((3148702648 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3142874621 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0388.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3148702648 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0388.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0388

namespace H65K_PlatformHighBatch0389
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0389.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0389.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0389.samples = true
  exact RH65K_0389.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3148702648 : ℝ) / 65536) ((3154566213 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3148702648 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0389.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3154566213 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0389.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0389

namespace H65K_PlatformHighBatch0390
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0390.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0390.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0390.samples = true
  exact RH65K_0390.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3154566213 : ℝ) / 65536) ((3160389613 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3154566213 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0390.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3160389613 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0390.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0390

namespace H65K_PlatformHighBatch0391
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0391.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0391.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0391.samples = true
  exact RH65K_0391.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3160389613 : ℝ) / 65536) ((3166236959 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3160389613 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0391.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3166236959 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0391.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0391

namespace H65K_PlatformHighBatch0392
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0392.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0392.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0392.samples = true
  exact RH65K_0392.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3166236959 : ℝ) / 65536) ((3172107544 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3166236959 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0392.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3172107544 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0392.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0392

namespace H65K_PlatformHighBatch0393
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0393.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0393.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0393.samples = true
  exact RH65K_0393.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3172107544 : ℝ) / 65536) ((3177932870 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3172107544 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0393.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3177932870 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0393.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0393

namespace H65K_PlatformHighBatch0394
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0394.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0394.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0394.samples = true
  exact RH65K_0394.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3177932870 : ℝ) / 65536) ((3183791761 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3177932870 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0394.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3183791761 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0394.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0394

namespace H65K_PlatformHighBatch0395
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0395.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0395.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0395.samples = true
  exact RH65K_0395.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3183791761 : ℝ) / 65536) ((3189623541 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3183791761 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0395.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3189623541 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0395.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0395

namespace H65K_PlatformHighBatch0396
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0396.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0396.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0396.samples = true
  exact RH65K_0396.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3189623541 : ℝ) / 65536) ((3195454062 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3189623541 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0396.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3195454062 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0396.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0396

namespace H65K_PlatformHighBatch0397
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0397.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0397.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0397.samples = true
  exact RH65K_0397.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3195454062 : ℝ) / 65536) ((3201294659 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3195454062 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0397.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3201294659 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0397.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0397

namespace H65K_PlatformHighBatch0398
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0398.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0398.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0398.samples = true
  exact RH65K_0398.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3201294659 : ℝ) / 65536) ((3207128165 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3201294659 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0398.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3207128165 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0398.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0398

namespace H65K_PlatformHighBatch0399
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0399.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0399.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0399.samples = true
  exact RH65K_0399.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3207128165 : ℝ) / 65536) ((3212978945 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3207128165 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0399.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3212978945 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0399.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0399

namespace H65K_PlatformHighBatch0400
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0400.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0400.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0400.samples = true
  exact RH65K_0400.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3212978945 : ℝ) / 65536) ((3218796856 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3212978945 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0400.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3218796856 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0400.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0400

namespace H65K_PlatformHighBatch0401
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0401.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0401.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0401.samples = true
  exact RH65K_0401.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3218796856 : ℝ) / 65536) ((3224652490 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3218796856 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0401.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3224652490 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0401.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0401

namespace H65K_PlatformHighBatch0402
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0402.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0402.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0402.samples = true
  exact RH65K_0402.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3224652490 : ℝ) / 65536) ((3230453938 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3224652490 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0402.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3230453938 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0402.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0402

namespace H65K_PlatformHighBatch0403
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0403.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0403.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0403.samples = true
  exact RH65K_0403.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3230453938 : ℝ) / 65536) ((3236296593 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3230453938 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0403.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3236296593 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0403.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0403

namespace H65K_PlatformHighBatch0404
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0404.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0404.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0404.samples = true
  exact RH65K_0404.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3236296593 : ℝ) / 65536) ((3242132730 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3236296593 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0404.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3242132730 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0404.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0404

namespace H65K_PlatformHighBatch0405
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0405.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0405.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0405.samples = true
  exact RH65K_0405.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3242132730 : ℝ) / 65536) ((3247950001 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3242132730 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0405.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3247950001 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0405.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0405

namespace H65K_PlatformHighBatch0406
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0406.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0406.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0406.samples = true
  exact RH65K_0406.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3247950001 : ℝ) / 65536) ((3253799385 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3247950001 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0406.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3253799385 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0406.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0406

namespace H65K_PlatformHighBatch0407
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0407.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0407.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0407.samples = true
  exact RH65K_0407.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3253799385 : ℝ) / 65536) ((3259599910 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3253799385 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0407.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3259599910 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0407.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0407

namespace H65K_PlatformHighBatch0408
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0408.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0408.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0408.samples = true
  exact RH65K_0408.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3259599910 : ℝ) / 65536) ((3265441627 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3259599910 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0408.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3265441627 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0408.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0408

namespace H65K_PlatformHighBatch0409
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0409.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0409.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0409.samples = true
  exact RH65K_0409.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3265441627 : ℝ) / 65536) ((3271240540 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3265441627 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0409.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3271240540 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0409.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0409

namespace H65K_PlatformHighBatch0410
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0410.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0410.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0410.samples = true
  exact RH65K_0410.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3271240540 : ℝ) / 65536) ((3277099616 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3271240540 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0410.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3277099616 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0410.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0410

namespace H65K_PlatformHighBatch0411
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0411.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0411.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0411.samples = true
  exact RH65K_0411.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3277099616 : ℝ) / 65536) ((3282910549 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3277099616 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0411.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3282910549 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0411.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0411

namespace H65K_PlatformHighBatch0412
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0412.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0412.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0412.samples = true
  exact RH65K_0412.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3282910549 : ℝ) / 65536) ((3288737357 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3282910549 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0412.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3288737357 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0412.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0412

namespace H65K_PlatformHighBatch0413
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0413.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0413.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0413.samples = true
  exact RH65K_0413.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3288737357 : ℝ) / 65536) ((3294518370 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3288737357 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0413.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3294518370 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0413.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0413

namespace H65K_PlatformHighBatch0414
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0414.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0414.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0414.samples = true
  exact RH65K_0414.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3294518370 : ℝ) / 65536) ((3300365500 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3294518370 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0414.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3300365500 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0414.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0414

namespace H65K_PlatformHighBatch0415
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0415.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0415.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0415.samples = true
  exact RH65K_0415.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3300365500 : ℝ) / 65536) ((3306185316 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3300365500 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0415.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3306185316 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0415.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0415

theorem solution : RS5.BandZeros ((3119454795 : ℝ) / 65536) ((3306185316 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0384.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0385.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0386.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0387.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0388.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0389.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0390.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0391.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0392.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0393.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0394.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0395.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0396.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0397.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0398.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0399.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0400.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0401.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0402.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0403.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0404.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0405.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0406.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0407.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0408.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0409.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0410.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0411.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0412.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0413.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0414.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0415.zeros
  exact h31
