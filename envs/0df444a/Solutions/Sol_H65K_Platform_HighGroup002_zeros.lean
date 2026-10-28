-- Prove2me | solution 1 for H65K.Platform.HighGroup002.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:55:49.855609+00:00
-- url     : https://prove2.me/submissions/da09f2fa-3a24-4412-ad79-9e444c0322ac

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group008
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group009
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group010
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group011
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0064
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group008).1).1
end RH65K_0064

namespace RH65K_0065
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group008).2).1).1
end RH65K_0065

namespace RH65K_0066
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group008).2).2).1).1
end RH65K_0066

namespace RH65K_0067
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group008).2).2).2).1).1
end RH65K_0067

namespace RH65K_0068
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group008).2).2).2).2).1).1
end RH65K_0068

namespace RH65K_0069
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group008).2).2).2).2).2).1).1
end RH65K_0069

namespace RH65K_0070
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group008).2).2).2).2).2).2).1).1
end RH65K_0070

namespace RH65K_0071
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group008).2).2).2).2).2).2).2).1
end RH65K_0071

namespace RH65K_0072
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group009).1).1
end RH65K_0072

namespace RH65K_0073
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group009).2).1).1
end RH65K_0073

namespace RH65K_0074
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group009).2).2).1).1
end RH65K_0074

namespace RH65K_0075
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group009).2).2).2).1).1
end RH65K_0075

namespace RH65K_0076
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group009).2).2).2).2).1).1
end RH65K_0076

namespace RH65K_0077
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group009).2).2).2).2).2).1).1
end RH65K_0077

namespace RH65K_0078
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group009).2).2).2).2).2).2).1).1
end RH65K_0078

namespace RH65K_0079
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group009).2).2).2).2).2).2).2).1
end RH65K_0079

namespace RH65K_0080
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group010).1).1
end RH65K_0080

namespace RH65K_0081
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group010).2).1).1
end RH65K_0081

namespace RH65K_0082
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group010).2).2).1).1
end RH65K_0082

namespace RH65K_0083
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group010).2).2).2).1).1
end RH65K_0083

namespace RH65K_0084
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group010).2).2).2).2).1).1
end RH65K_0084

namespace RH65K_0085
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group010).2).2).2).2).2).1).1
end RH65K_0085

namespace RH65K_0086
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group010).2).2).2).2).2).2).1).1
end RH65K_0086

namespace RH65K_0087
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group010).2).2).2).2).2).2).2).1
end RH65K_0087

namespace RH65K_0088
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group011).1).1
end RH65K_0088

namespace RH65K_0089
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group011).2).1).1
end RH65K_0089

namespace RH65K_0090
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group011).2).2).1).1
end RH65K_0090

namespace RH65K_0091
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group011).2).2).2).1).1
end RH65K_0091

namespace RH65K_0092
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group011).2).2).2).2).1).1
end RH65K_0092

namespace RH65K_0093
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group011).2).2).2).2).2).1).1
end RH65K_0093

namespace RH65K_0094
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group011).2).2).2).2).2).2).1).1
end RH65K_0094

namespace RH65K_0095
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group011).2).2).2).2).2).2).2).1
end RH65K_0095

namespace H65K_PlatformHighBatch0064
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0064.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0064.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0064.samples = true
  exact RH65K_0064.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1154554247 : ℝ) / 65536) ((1161130023 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1154554247 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0064.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1161130023 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0064.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0064

namespace H65K_PlatformHighBatch0065
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0065.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0065.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0065.samples = true
  exact RH65K_0065.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1161130023 : ℝ) / 65536) ((1167714759 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1161130023 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0065.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1167714759 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0065.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0065

namespace H65K_PlatformHighBatch0066
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0066.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0066.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0066.samples = true
  exact RH65K_0066.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1167714759 : ℝ) / 65536) ((1174277832 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1167714759 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0066.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1174277832 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0066.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0066

namespace H65K_PlatformHighBatch0067
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0067.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0067.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0067.samples = true
  exact RH65K_0067.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1174277832 : ℝ) / 65536) ((1180849455 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1174277832 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0067.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1180849455 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0067.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0067

namespace H65K_PlatformHighBatch0068
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0068.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0068.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0068.samples = true
  exact RH65K_0068.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1180849455 : ℝ) / 65536) ((1187422662 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1180849455 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0068.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1187422662 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0068.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0068

namespace H65K_PlatformHighBatch0069
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0069.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0069.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0069.samples = true
  exact RH65K_0069.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1187422662 : ℝ) / 65536) ((1193973580 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1187422662 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0069.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1193973580 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0069.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0069

namespace H65K_PlatformHighBatch0070
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0070.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0070.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0070.samples = true
  exact RH65K_0070.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1193973580 : ℝ) / 65536) ((1200550379 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1193973580 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0070.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1200550379 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0070.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0070

namespace H65K_PlatformHighBatch0071
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0071.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0071.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0071.samples = true
  exact RH65K_0071.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1200550379 : ℝ) / 65536) ((1207096731 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1200550379 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0071.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1207096731 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0071.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0071

namespace H65K_PlatformHighBatch0072
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0072.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0072.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0072.samples = true
  exact RH65K_0072.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1207096731 : ℝ) / 65536) ((1213644095 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1207096731 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0072.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1213644095 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0072.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0072

namespace H65K_PlatformHighBatch0073
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0073.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0073.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0073.samples = true
  exact RH65K_0073.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1213644095 : ℝ) / 65536) ((1220199832 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1213644095 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0073.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1220199832 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0073.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0073

namespace H65K_PlatformHighBatch0074
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0074.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0074.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0074.samples = true
  exact RH65K_0074.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1220199832 : ℝ) / 65536) ((1226716736 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1220199832 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0074.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1226716736 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0074.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0074

namespace H65K_PlatformHighBatch0075
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0075.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0075.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0075.samples = true
  exact RH65K_0075.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1226716736 : ℝ) / 65536) ((1233274418 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1226716736 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0075.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1233274418 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0075.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0075

namespace H65K_PlatformHighBatch0076
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0076.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0076.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0076.samples = true
  exact RH65K_0076.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1233274418 : ℝ) / 65536) ((1239774970 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1233274418 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0076.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1239774970 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0076.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0076

namespace H65K_PlatformHighBatch0077
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0077.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0077.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0077.samples = true
  exact RH65K_0077.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1239774970 : ℝ) / 65536) ((1246330916 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1239774970 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0077.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1246330916 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0077.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0077

namespace H65K_PlatformHighBatch0078
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0078.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0078.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0078.samples = true
  exact RH65K_0078.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1246330916 : ℝ) / 65536) ((1252826785 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1246330916 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0078.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1252826785 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0078.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0078

namespace H65K_PlatformHighBatch0079
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0079.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0079.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0079.samples = true
  exact RH65K_0079.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1252826785 : ℝ) / 65536) ((1259360664 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1252826785 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0079.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1259360664 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0079.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0079

namespace H65K_PlatformHighBatch0080
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0080.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0080.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0080.samples = true
  exact RH65K_0080.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1259360664 : ℝ) / 65536) ((1265866765 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1259360664 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0080.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1265866765 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0080.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0080

namespace H65K_PlatformHighBatch0081
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0081.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0081.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0081.samples = true
  exact RH65K_0081.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1265866765 : ℝ) / 65536) ((1272370561 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1265866765 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0081.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1272370561 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0081.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0081

namespace H65K_PlatformHighBatch0082
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0082.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0082.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0082.samples = true
  exact RH65K_0082.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1272370561 : ℝ) / 65536) ((1278890653 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1272370561 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0082.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1278890653 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0082.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0082

namespace H65K_PlatformHighBatch0083
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0083.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0083.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0083.samples = true
  exact RH65K_0083.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1278890653 : ℝ) / 65536) ((1285396461 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1278890653 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0083.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1285396461 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0083.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0083

namespace H65K_PlatformHighBatch0084
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0084.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0084.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0084.samples = true
  exact RH65K_0084.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1285396461 : ℝ) / 65536) ((1291884837 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1285396461 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0084.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1291884837 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0084.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0084

namespace H65K_PlatformHighBatch0085
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0085.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0085.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0085.samples = true
  exact RH65K_0085.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1291884837 : ℝ) / 65536) ((1298375494 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1291884837 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0085.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1298375494 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0085.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0085

namespace H65K_PlatformHighBatch0086
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0086.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0086.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0086.samples = true
  exact RH65K_0086.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1298375494 : ℝ) / 65536) ((1304886746 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1298375494 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0086.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1304886746 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0086.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0086

namespace H65K_PlatformHighBatch0087
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0087.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0087.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0087.samples = true
  exact RH65K_0087.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1304886746 : ℝ) / 65536) ((1311359913 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1304886746 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0087.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1311359913 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0087.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0087

namespace H65K_PlatformHighBatch0088
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0088.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0088.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0088.samples = true
  exact RH65K_0088.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1311359913 : ℝ) / 65536) ((1317843420 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1311359913 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0088.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1317843420 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0088.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0088

namespace H65K_PlatformHighBatch0089
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0089.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0089.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0089.samples = true
  exact RH65K_0089.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1317843420 : ℝ) / 65536) ((1324349796 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1317843420 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0089.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1324349796 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0089.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0089

namespace H65K_PlatformHighBatch0090
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0090.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0090.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0090.samples = true
  exact RH65K_0090.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1324349796 : ℝ) / 65536) ((1330797258 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1324349796 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0090.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1330797258 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0090.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0090

namespace H65K_PlatformHighBatch0091
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0091.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0091.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0091.samples = true
  exact RH65K_0091.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1330797258 : ℝ) / 65536) ((1337256639 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1330797258 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0091.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1337256639 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0091.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0091

namespace H65K_PlatformHighBatch0092
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0092.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0092.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0092.samples = true
  exact RH65K_0092.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1337256639 : ℝ) / 65536) ((1343723458 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1337256639 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0092.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1343723458 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0092.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0092

namespace H65K_PlatformHighBatch0093
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0093.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0093.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0093.samples = true
  exact RH65K_0093.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1343723458 : ℝ) / 65536) ((1350194090 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1343723458 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0093.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1350194090 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0093.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0093

namespace H65K_PlatformHighBatch0094
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0094.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0094.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0094.samples = true
  exact RH65K_0094.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1350194090 : ℝ) / 65536) ((1356643012 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1350194090 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0094.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1356643012 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0094.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0094

namespace H65K_PlatformHighBatch0095
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0095.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0095.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0095.samples = true
  exact RH65K_0095.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1356643012 : ℝ) / 65536) ((1363082502 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1356643012 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0095.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1363082502 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0095.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0095

theorem solution : RS5.BandZeros ((1154554247 : ℝ) / 65536) ((1363082502 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0064.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0065.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0066.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0067.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0068.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0069.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0070.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0071.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0072.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0073.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0074.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0075.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0076.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0077.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0078.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0079.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0080.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0081.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0082.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0083.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0084.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0085.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0086.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0087.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0088.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0089.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0090.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0091.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0092.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0093.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0094.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0095.zeros
  exact h31
