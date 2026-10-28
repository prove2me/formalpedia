-- Prove2me | solution 1 for H65K.Platform.HighGroup001.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:55:55.058031+00:00
-- url     : https://prove2.me/submissions/bcbec654-a5b9-4914-ad9e-28d3f8ef564d

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group004
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group005
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group006
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group007
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0032
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group004).1).1
end RH65K_0032

namespace RH65K_0033
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group004).2).1).1
end RH65K_0033

namespace RH65K_0034
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group004).2).2).1).1
end RH65K_0034

namespace RH65K_0035
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group004).2).2).2).1).1
end RH65K_0035

namespace RH65K_0036
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group004).2).2).2).2).1).1
end RH65K_0036

namespace RH65K_0037
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group004).2).2).2).2).2).1).1
end RH65K_0037

namespace RH65K_0038
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group004).2).2).2).2).2).2).1).1
end RH65K_0038

namespace RH65K_0039
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group004).2).2).2).2).2).2).2).1
end RH65K_0039

namespace RH65K_0040
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group005).1).1
end RH65K_0040

namespace RH65K_0041
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group005).2).1).1
end RH65K_0041

namespace RH65K_0042
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group005).2).2).1).1
end RH65K_0042

namespace RH65K_0043
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group005).2).2).2).1).1
end RH65K_0043

namespace RH65K_0044
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group005).2).2).2).2).1).1
end RH65K_0044

namespace RH65K_0045
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group005).2).2).2).2).2).1).1
end RH65K_0045

namespace RH65K_0046
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group005).2).2).2).2).2).2).1).1
end RH65K_0046

namespace RH65K_0047
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group005).2).2).2).2).2).2).2).1
end RH65K_0047

namespace RH65K_0048
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group006).1).1
end RH65K_0048

namespace RH65K_0049
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group006).2).1).1
end RH65K_0049

namespace RH65K_0050
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group006).2).2).1).1
end RH65K_0050

namespace RH65K_0051
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group006).2).2).2).1).1
end RH65K_0051

namespace RH65K_0052
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group006).2).2).2).2).1).1
end RH65K_0052

namespace RH65K_0053
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group006).2).2).2).2).2).1).1
end RH65K_0053

namespace RH65K_0054
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group006).2).2).2).2).2).2).1).1
end RH65K_0054

namespace RH65K_0055
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group006).2).2).2).2).2).2).2).1
end RH65K_0055

namespace RH65K_0056
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group007).1).1
end RH65K_0056

namespace RH65K_0057
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group007).2).1).1
end RH65K_0057

namespace RH65K_0058
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group007).2).2).1).1
end RH65K_0058

namespace RH65K_0059
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group007).2).2).2).1).1
end RH65K_0059

namespace RH65K_0060
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group007).2).2).2).2).1).1
end RH65K_0060

namespace RH65K_0061
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group007).2).2).2).2).2).1).1
end RH65K_0061

namespace RH65K_0062
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group007).2).2).2).2).2).2).1).1
end RH65K_0062

namespace RH65K_0063
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group007).2).2).2).2).2).2).2).1
end RH65K_0063

namespace H65K_PlatformHighBatch0032
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0032.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0032.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0032.samples = true
  exact RH65K_0032.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((941117753 : ℝ) / 65536) ((947844084 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((941117753 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0032.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((947844084 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0032.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0032

namespace H65K_PlatformHighBatch0033
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0033.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0033.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0033.samples = true
  exact RH65K_0033.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((947844084 : ℝ) / 65536) ((954596872 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((947844084 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0033.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((954596872 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0033.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0033

namespace H65K_PlatformHighBatch0034
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0034.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0034.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0034.samples = true
  exact RH65K_0034.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((954596872 : ℝ) / 65536) ((961366002 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((954596872 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0034.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((961366002 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0034.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0034

namespace H65K_PlatformHighBatch0035
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0035.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0035.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0035.samples = true
  exact RH65K_0035.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((961366002 : ℝ) / 65536) ((968078141 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((961366002 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0035.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((968078141 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0035.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0035

namespace H65K_PlatformHighBatch0036
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0036.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0036.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0036.samples = true
  exact RH65K_0036.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((968078141 : ℝ) / 65536) ((974812474 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((968078141 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0036.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((974812474 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0036.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0036

namespace H65K_PlatformHighBatch0037
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0037.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0037.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0037.samples = true
  exact RH65K_0037.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((974812474 : ℝ) / 65536) ((981554194 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((974812474 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0037.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((981554194 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0037.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0037

namespace H65K_PlatformHighBatch0038
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0038.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0038.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0038.samples = true
  exact RH65K_0038.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((981554194 : ℝ) / 65536) ((988266339 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((981554194 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0038.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((988266339 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0038.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0038

namespace H65K_PlatformHighBatch0039
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0039.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0039.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0039.samples = true
  exact RH65K_0039.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((988266339 : ℝ) / 65536) ((994971038 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((988266339 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0039.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((994971038 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0039.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0039

namespace H65K_PlatformHighBatch0040
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0040.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0040.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0040.samples = true
  exact RH65K_0040.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((994971038 : ℝ) / 65536) ((1001716098 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((994971038 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0040.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1001716098 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0040.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0040

namespace H65K_PlatformHighBatch0041
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0041.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0041.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0041.samples = true
  exact RH65K_0041.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1001716098 : ℝ) / 65536) ((1008420616 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1001716098 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0041.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1008420616 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0041.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0041

namespace H65K_PlatformHighBatch0042
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0042.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0042.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0042.samples = true
  exact RH65K_0042.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1008420616 : ℝ) / 65536) ((1015109065 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1008420616 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0042.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1015109065 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0042.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0042

namespace H65K_PlatformHighBatch0043
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0043.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0043.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0043.samples = true
  exact RH65K_0043.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1015109065 : ℝ) / 65536) ((1021805634 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1015109065 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0043.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1021805634 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0043.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0043

namespace H65K_PlatformHighBatch0044
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0044.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0044.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0044.samples = true
  exact RH65K_0044.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1021805634 : ℝ) / 65536) ((1028503115 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1021805634 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0044.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1028503115 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0044.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0044

namespace H65K_PlatformHighBatch0045
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0045.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0045.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0045.samples = true
  exact RH65K_0045.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1028503115 : ℝ) / 65536) ((1035161359 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1028503115 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0045.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1035161359 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0045.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0045

namespace H65K_PlatformHighBatch0046
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0046.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0046.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0046.samples = true
  exact RH65K_0046.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1035161359 : ℝ) / 65536) ((1041839254 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1035161359 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0046.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1041839254 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0046.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0046

namespace H65K_PlatformHighBatch0047
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0047.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0047.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0047.samples = true
  exact RH65K_0047.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1041839254 : ℝ) / 65536) ((1048529560 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1041839254 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0047.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1048529560 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0047.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0047

namespace H65K_PlatformHighBatch0048
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0048.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0048.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0048.samples = true
  exact RH65K_0048.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1048529560 : ℝ) / 65536) ((1055206987 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1048529560 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0048.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1055206987 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0048.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0048

namespace H65K_PlatformHighBatch0049
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0049.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0049.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0049.samples = true
  exact RH65K_0049.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1055206987 : ℝ) / 65536) ((1061857467 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1055206987 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0049.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1061857467 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0049.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0049

namespace H65K_PlatformHighBatch0050
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0050.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0050.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0050.samples = true
  exact RH65K_0050.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1061857467 : ℝ) / 65536) ((1068495978 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1061857467 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0050.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1068495978 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0050.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0050

namespace H65K_PlatformHighBatch0051
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0051.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0051.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0051.samples = true
  exact RH65K_0051.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1068495978 : ℝ) / 65536) ((1075138949 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1068495978 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0051.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1075138949 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0051.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0051

namespace H65K_PlatformHighBatch0052
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0052.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0052.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0052.samples = true
  exact RH65K_0052.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1075138949 : ℝ) / 65536) ((1081811026 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1075138949 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0052.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1081811026 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0052.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0052

namespace H65K_PlatformHighBatch0053
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0053.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0053.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0053.samples = true
  exact RH65K_0053.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1081811026 : ℝ) / 65536) ((1088449762 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1081811026 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0053.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1088449762 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0053.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0053

namespace H65K_PlatformHighBatch0054
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0054.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0054.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0054.samples = true
  exact RH65K_0054.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1088449762 : ℝ) / 65536) ((1095072437 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1088449762 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0054.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1095072437 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0054.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0054

namespace H65K_PlatformHighBatch0055
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0055.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0055.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0055.samples = true
  exact RH65K_0055.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1095072437 : ℝ) / 65536) ((1101707113 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1095072437 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0055.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1101707113 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0055.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0055

namespace H65K_PlatformHighBatch0056
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0056.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0056.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0056.samples = true
  exact RH65K_0056.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1101707113 : ℝ) / 65536) ((1108305026 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1101707113 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0056.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1108305026 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0056.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0056

namespace H65K_PlatformHighBatch0057
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0057.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0057.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0057.samples = true
  exact RH65K_0057.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1108305026 : ℝ) / 65536) ((1114913020 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1108305026 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0057.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1114913020 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0057.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0057

namespace H65K_PlatformHighBatch0058
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0058.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0058.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0058.samples = true
  exact RH65K_0058.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1114913020 : ℝ) / 65536) ((1121552201 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1114913020 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0058.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1121552201 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0058.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0058

namespace H65K_PlatformHighBatch0059
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0059.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0059.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0059.samples = true
  exact RH65K_0059.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1121552201 : ℝ) / 65536) ((1128170858 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1121552201 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0059.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1128170858 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0059.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0059

namespace H65K_PlatformHighBatch0060
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0060.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0060.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0060.samples = true
  exact RH65K_0060.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1128170858 : ℝ) / 65536) ((1134779572 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1128170858 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0060.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1134779572 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0060.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0060

namespace H65K_PlatformHighBatch0061
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0061.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0061.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0061.samples = true
  exact RH65K_0061.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1134779572 : ℝ) / 65536) ((1141380823 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1134779572 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0061.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1141380823 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0061.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0061

namespace H65K_PlatformHighBatch0062
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0062.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0062.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0062.samples = true
  exact RH65K_0062.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1141380823 : ℝ) / 65536) ((1147948410 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1141380823 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0062.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1147948410 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0062.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0062

namespace H65K_PlatformHighBatch0063
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0063.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0063.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0063.samples = true
  exact RH65K_0063.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1147948410 : ℝ) / 65536) ((1154554247 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1147948410 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0063.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1154554247 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0063.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0063

theorem solution : RS5.BandZeros ((941117753 : ℝ) / 65536) ((1154554247 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0032.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0033.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0034.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0035.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0036.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0037.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0038.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0039.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0040.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0041.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0042.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0043.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0044.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0045.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0046.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0047.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0048.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0049.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0050.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0051.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0052.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0053.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0054.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0055.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0056.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0057.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0058.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0059.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0060.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0061.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0062.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0063.zeros
  exact h31
