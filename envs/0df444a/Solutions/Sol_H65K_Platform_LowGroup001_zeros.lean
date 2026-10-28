-- Prove2me | solution 1 for H65K.Platform.LowGroup001.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:15:35.721523+00:00
-- url     : https://prove2.me/submissions/765c32d2-e30e-4717-b572-1beb0d8a812b

import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group004
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group005
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group006
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group007
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_Low_0032
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group004).1).1
end RH65K_Low_0032

namespace RH65K_Low_0033
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group004).2).1).1
end RH65K_Low_0033

namespace RH65K_Low_0034
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group004).2).2).1).1
end RH65K_Low_0034

namespace RH65K_Low_0035
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group004).2).2).2).1).1
end RH65K_Low_0035

namespace RH65K_Low_0036
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group004).2).2).2).2).1).1
end RH65K_Low_0036

namespace RH65K_Low_0037
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group004).2).2).2).2).2).1).1
end RH65K_Low_0037

namespace RH65K_Low_0038
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group004).2).2).2).2).2).2).1).1
end RH65K_Low_0038

namespace RH65K_Low_0039
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group004).2).2).2).2).2).2).2).1
end RH65K_Low_0039

namespace RH65K_Low_0040
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group005).1).1
end RH65K_Low_0040

namespace RH65K_Low_0041
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group005).2).1).1
end RH65K_Low_0041

namespace RH65K_Low_0042
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group005).2).2).1).1
end RH65K_Low_0042

namespace RH65K_Low_0043
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group005).2).2).2).1).1
end RH65K_Low_0043

namespace RH65K_Low_0044
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group005).2).2).2).2).1).1
end RH65K_Low_0044

namespace RH65K_Low_0045
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group005).2).2).2).2).2).1).1
end RH65K_Low_0045

namespace RH65K_Low_0046
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group005).2).2).2).2).2).2).1).1
end RH65K_Low_0046

namespace RH65K_Low_0047
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group005).2).2).2).2).2).2).2).1
end RH65K_Low_0047

namespace RH65K_Low_0048
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group006).1).1
end RH65K_Low_0048

namespace RH65K_Low_0049
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group006).2).1).1
end RH65K_Low_0049

namespace RH65K_Low_0050
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group006).2).2).1).1
end RH65K_Low_0050

namespace RH65K_Low_0051
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group006).2).2).2).1).1
end RH65K_Low_0051

namespace RH65K_Low_0052
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group006).2).2).2).2).1).1
end RH65K_Low_0052

namespace RH65K_Low_0053
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group006).2).2).2).2).2).1).1
end RH65K_Low_0053

namespace RH65K_Low_0054
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group006).2).2).2).2).2).2).1).1
end RH65K_Low_0054

namespace RH65K_Low_0055
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group006).2).2).2).2).2).2).2).1
end RH65K_Low_0055

namespace RH65K_Low_0056
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group007).1).1
end RH65K_Low_0056

namespace RH65K_Low_0057
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group007).2).1).1
end RH65K_Low_0057

namespace RH65K_Low_0058
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group007).2).2).1).1
end RH65K_Low_0058

namespace RH65K_Low_0059
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group007).2).2).2).1).1
end RH65K_Low_0059

namespace RH65K_Low_0060
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group007).2).2).2).2).1).1
end RH65K_Low_0060

namespace RH65K_Low_0061
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group007).2).2).2).2).2).1).1
end RH65K_Low_0061

namespace RH65K_Low_0062
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group007).2).2).2).2).2).2).1).1
end RH65K_Low_0062

namespace RH65K_Low_0063
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group007).2).2).2).2).2).2).2).1
end RH65K_Low_0063

namespace H65K_PlatformLowBatch0032
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0032.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0032.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0032.samples = true
  exact RH65K_Low_0032.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((333962439 : ℝ) / 65536) ((341726730 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((333962439 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0032.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((341726730 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0032.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0032

namespace H65K_PlatformLowBatch0033
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0033.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0033.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0033.samples = true
  exact RH65K_Low_0033.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((341726730 : ℝ) / 65536) ((349514262 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((341726730 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0033.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((349514262 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0033.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0033

namespace H65K_PlatformLowBatch0034
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0034.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0034.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0034.samples = true
  exact RH65K_Low_0034.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((349514262 : ℝ) / 65536) ((357268723 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((349514262 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0034.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((357268723 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0034.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0034

namespace H65K_PlatformLowBatch0035
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0035.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0035.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0035.samples = true
  exact RH65K_Low_0035.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((357268723 : ℝ) / 65536) ((364960530 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((357268723 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0035.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((364960530 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0035.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0035

namespace H65K_PlatformLowBatch0036
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0036.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0036.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0036.samples = true
  exact RH65K_Low_0036.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((364960530 : ℝ) / 65536) ((372674332 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((364960530 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0036.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((372674332 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0036.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0036

namespace H65K_PlatformLowBatch0037
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0037.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0037.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0037.samples = true
  exact RH65K_Low_0037.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((372674332 : ℝ) / 65536) ((380326783 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((372674332 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0037.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((380326783 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0037.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0037

namespace H65K_PlatformLowBatch0038
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0038.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0038.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0038.samples = true
  exact RH65K_Low_0038.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((380326783 : ℝ) / 65536) ((387992585 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((380326783 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0038.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((387992585 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0038.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0038

namespace H65K_PlatformLowBatch0039
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0039.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0039.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0039.samples = true
  exact RH65K_Low_0039.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((387992585 : ℝ) / 65536) ((395592252 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((387992585 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0039.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((395592252 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0039.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0039

namespace H65K_PlatformLowBatch0040
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0040.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0040.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0040.samples = true
  exact RH65K_Low_0040.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((395592252 : ℝ) / 65536) ((403182652 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((395592252 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0040.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((403182652 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0040.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0040

namespace H65K_PlatformLowBatch0041
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0041.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0041.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0041.samples = true
  exact RH65K_Low_0041.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((403182652 : ℝ) / 65536) ((410785734 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((403182652 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0041.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((410785734 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0041.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0041

namespace H65K_PlatformLowBatch0042
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0042.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0042.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0042.samples = true
  exact RH65K_Low_0042.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((410785734 : ℝ) / 65536) ((418377546 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((410785734 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0042.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((418377546 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0042.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0042

namespace H65K_PlatformLowBatch0043
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0043.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0043.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0043.samples = true
  exact RH65K_Low_0043.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((418377546 : ℝ) / 65536) ((425881555 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((418377546 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0043.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((425881555 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0043.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0043

namespace H65K_PlatformLowBatch0044
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0044.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0044.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0044.samples = true
  exact RH65K_Low_0044.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((425881555 : ℝ) / 65536) ((433422722 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((425881555 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0044.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((433422722 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0044.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0044

namespace H65K_PlatformLowBatch0045
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0045.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0045.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0045.samples = true
  exact RH65K_Low_0045.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((433422722 : ℝ) / 65536) ((440927926 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((433422722 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0045.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((440927926 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0045.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0045

namespace H65K_PlatformLowBatch0046
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0046.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0046.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0046.samples = true
  exact RH65K_Low_0046.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((440927926 : ℝ) / 65536) ((448404538 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((440927926 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0046.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((448404538 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0046.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0046

namespace H65K_PlatformLowBatch0047
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0047.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0047.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0047.samples = true
  exact RH65K_Low_0047.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((448404538 : ℝ) / 65536) ((455879376 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((448404538 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0047.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((455879376 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0047.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0047

namespace H65K_PlatformLowBatch0048
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0048.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0048.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0048.samples = true
  exact RH65K_Low_0048.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((455879376 : ℝ) / 65536) ((463324531 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((455879376 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0048.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((463324531 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0048.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0048

namespace H65K_PlatformLowBatch0049
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0049.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0049.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0049.samples = true
  exact RH65K_Low_0049.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((463324531 : ℝ) / 65536) ((470765146 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((463324531 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0049.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((470765146 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0049.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0049

namespace H65K_PlatformLowBatch0050
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0050.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0050.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0050.samples = true
  exact RH65K_Low_0050.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((470765146 : ℝ) / 65536) ((478155127 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((470765146 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0050.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((478155127 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0050.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0050

namespace H65K_PlatformLowBatch0051
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0051.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0051.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0051.samples = true
  exact RH65K_Low_0051.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((478155127 : ℝ) / 65536) ((485577815 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((478155127 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0051.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((485577815 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0051.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0051

namespace H65K_PlatformLowBatch0052
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0052.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0052.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0052.samples = true
  exact RH65K_Low_0052.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((485577815 : ℝ) / 65536) ((492950484 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((485577815 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0052.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((492950484 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0052.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0052

namespace H65K_PlatformLowBatch0053
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0053.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0053.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0053.samples = true
  exact RH65K_Low_0053.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((492950484 : ℝ) / 65536) ((500337347 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((492950484 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0053.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((500337347 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0053.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0053

namespace H65K_PlatformLowBatch0054
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0054.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0054.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0054.samples = true
  exact RH65K_Low_0054.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((500337347 : ℝ) / 65536) ((507703482 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((500337347 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0054.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((507703482 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0054.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0054

namespace H65K_PlatformLowBatch0055
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0055.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0055.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0055.samples = true
  exact RH65K_Low_0055.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((507703482 : ℝ) / 65536) ((515042906 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((507703482 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0055.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((515042906 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0055.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0055

namespace H65K_PlatformLowBatch0056
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0056.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0056.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0056.samples = true
  exact RH65K_Low_0056.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((515042906 : ℝ) / 65536) ((522356931 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((515042906 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0056.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((522356931 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0056.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0056

namespace H65K_PlatformLowBatch0057
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0057.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0057.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0057.samples = true
  exact RH65K_Low_0057.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((522356931 : ℝ) / 65536) ((529688926 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((522356931 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0057.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((529688926 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0057.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0057

namespace H65K_PlatformLowBatch0058
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0058.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0058.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0058.samples = true
  exact RH65K_Low_0058.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((529688926 : ℝ) / 65536) ((536943945 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((529688926 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0058.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((536943945 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0058.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0058

namespace H65K_PlatformLowBatch0059
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0059.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0059.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0059.samples = true
  exact RH65K_Low_0059.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((536943945 : ℝ) / 65536) ((544282319 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((536943945 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0059.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((544282319 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0059.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0059

namespace H65K_PlatformLowBatch0060
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0060.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0060.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0060.samples = true
  exact RH65K_Low_0060.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((544282319 : ℝ) / 65536) ((551522361 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((544282319 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0060.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((551522361 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0060.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0060

namespace H65K_PlatformLowBatch0061
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0061.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0061.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0061.samples = true
  exact RH65K_Low_0061.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((551522361 : ℝ) / 65536) ((558758792 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((551522361 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0061.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((558758792 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0061.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0061

namespace H65K_PlatformLowBatch0062
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0062.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0062.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0062.samples = true
  exact RH65K_Low_0062.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((558758792 : ℝ) / 65536) ((566022223 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((558758792 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0062.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((566022223 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0062.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0062

namespace H65K_PlatformLowBatch0063
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0063.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0063.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0063.samples = true
  exact RH65K_Low_0063.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((566022223 : ℝ) / 65536) ((573251611 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((566022223 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0063.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((573251611 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0063.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0063

theorem solution : RS5.BandZeros ((333962439 : ℝ) / 65536) ((573251611 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformLowBatch0032.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0033.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0034.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0035.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0036.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0037.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0038.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0039.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0040.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0041.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0042.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0043.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0044.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0045.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0046.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0047.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0048.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0049.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0050.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0051.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0052.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0053.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0054.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0055.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0056.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0057.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0058.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0059.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0060.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0061.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0062.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0063.zeros
  exact h31
