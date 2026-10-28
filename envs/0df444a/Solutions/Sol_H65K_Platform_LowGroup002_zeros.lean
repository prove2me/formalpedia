-- Prove2me | solution 1 for H65K.Platform.LowGroup002.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:16:29.743984+00:00
-- url     : https://prove2.me/submissions/46b801e5-cbc8-4fc6-9a97-41ebae98a45b

import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group008
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group009
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group010
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_Low_0064
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group008).1).1
end RH65K_Low_0064

namespace RH65K_Low_0065
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group008).2).1).1
end RH65K_Low_0065

namespace RH65K_Low_0066
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group008).2).2).1).1
end RH65K_Low_0066

namespace RH65K_Low_0067
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group008).2).2).2).1).1
end RH65K_Low_0067

namespace RH65K_Low_0068
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group008).2).2).2).2).1).1
end RH65K_Low_0068

namespace RH65K_Low_0069
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group008).2).2).2).2).2).1).1
end RH65K_Low_0069

namespace RH65K_Low_0070
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group008).2).2).2).2).2).2).1).1
end RH65K_Low_0070

namespace RH65K_Low_0071
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group008).2).2).2).2).2).2).2).1
end RH65K_Low_0071

namespace RH65K_Low_0072
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group009).1).1
end RH65K_Low_0072

namespace RH65K_Low_0073
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group009).2).1).1
end RH65K_Low_0073

namespace RH65K_Low_0074
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group009).2).2).1).1
end RH65K_Low_0074

namespace RH65K_Low_0075
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group009).2).2).2).1).1
end RH65K_Low_0075

namespace RH65K_Low_0076
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group009).2).2).2).2).1).1
end RH65K_Low_0076

namespace RH65K_Low_0077
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group009).2).2).2).2).2).1).1
end RH65K_Low_0077

namespace RH65K_Low_0078
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group009).2).2).2).2).2).2).1).1
end RH65K_Low_0078

namespace RH65K_Low_0079
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group009).2).2).2).2).2).2).2).1
end RH65K_Low_0079

namespace RH65K_Low_0080
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group010).1).1
end RH65K_Low_0080

namespace RH65K_Low_0081
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group010).2).1).1
end RH65K_Low_0081

namespace RH65K_Low_0082
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group010).2).2).1).1
end RH65K_Low_0082

namespace RH65K_Low_0083
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group010).2).2).2).1).1
end RH65K_Low_0083

namespace RH65K_Low_0084
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group010).2).2).2).2).1
end RH65K_Low_0084

namespace H65K_PlatformLowBatch0064
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0064.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0064.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0064.samples = true
  exact RH65K_Low_0064.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((573251611 : ℝ) / 65536) ((580475210 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((573251611 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0064.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((580475210 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0064.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0064

namespace H65K_PlatformLowBatch0065
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0065.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0065.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0065.samples = true
  exact RH65K_Low_0065.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((580475210 : ℝ) / 65536) ((587691294 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((580475210 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0065.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((587691294 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0065.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0065

namespace H65K_PlatformLowBatch0066
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0066.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0066.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0066.samples = true
  exact RH65K_Low_0066.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((587691294 : ℝ) / 65536) ((594898011 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((587691294 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0066.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((594898011 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0066.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0066

namespace H65K_PlatformLowBatch0067
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0067.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0067.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0067.samples = true
  exact RH65K_Low_0067.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((594898011 : ℝ) / 65536) ((602076716 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((594898011 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0067.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((602076716 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0067.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0067

namespace H65K_PlatformLowBatch0068
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0068.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0068.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0068.samples = true
  exact RH65K_Low_0068.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((602076716 : ℝ) / 65536) ((609228268 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((602076716 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0068.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((609228268 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0068.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0068

namespace H65K_PlatformLowBatch0069
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0069.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0069.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0069.samples = true
  exact RH65K_Low_0069.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((609228268 : ℝ) / 65536) ((616385113 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((609228268 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0069.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((616385113 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0069.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0069

namespace H65K_PlatformLowBatch0070
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0070.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0070.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0070.samples = true
  exact RH65K_Low_0070.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((616385113 : ℝ) / 65536) ((623520914 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((616385113 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0070.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((623520914 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0070.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0070

namespace H65K_PlatformLowBatch0071
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0071.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0071.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0071.samples = true
  exact RH65K_Low_0071.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((623520914 : ℝ) / 65536) ((630664030 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((623520914 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0071.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((630664030 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0071.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0071

namespace H65K_PlatformLowBatch0072
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0072.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0072.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0072.samples = true
  exact RH65K_Low_0072.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((630664030 : ℝ) / 65536) ((637776026 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((630664030 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0072.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((637776026 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0072.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0072

namespace H65K_PlatformLowBatch0073
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0073.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0073.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0073.samples = true
  exact RH65K_Low_0073.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((637776026 : ℝ) / 65536) ((644899396 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((637776026 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0073.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((644899396 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0073.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0073

namespace H65K_PlatformLowBatch0074
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0074.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0074.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0074.samples = true
  exact RH65K_Low_0074.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((644899396 : ℝ) / 65536) ((652012586 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((644899396 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0074.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((652012586 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0074.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0074

namespace H65K_PlatformLowBatch0075
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0075.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0075.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0075.samples = true
  exact RH65K_Low_0075.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((652012586 : ℝ) / 65536) ((659102769 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((652012586 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0075.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((659102769 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0075.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0075

namespace H65K_PlatformLowBatch0076
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0076.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0076.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0076.samples = true
  exact RH65K_Low_0076.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((659102769 : ℝ) / 65536) ((666182397 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((659102769 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0076.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((666182397 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0076.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0076

namespace H65K_PlatformLowBatch0077
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0077.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0077.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0077.samples = true
  exact RH65K_Low_0077.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((666182397 : ℝ) / 65536) ((673263055 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((666182397 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0077.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((673263055 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0077.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0077

namespace H65K_PlatformLowBatch0078
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0078.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0078.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0078.samples = true
  exact RH65K_Low_0078.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((673263055 : ℝ) / 65536) ((680343094 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((673263055 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0078.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((680343094 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0078.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0078

namespace H65K_PlatformLowBatch0079
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0079.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0079.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0079.samples = true
  exact RH65K_Low_0079.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((680343094 : ℝ) / 65536) ((687373276 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((680343094 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0079.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((687373276 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0079.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0079

namespace H65K_PlatformLowBatch0080
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0080.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0080.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0080.samples = true
  exact RH65K_Low_0080.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((687373276 : ℝ) / 65536) ((694399593 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((687373276 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0080.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((694399593 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0080.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0080

namespace H65K_PlatformLowBatch0081
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0081.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0081.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0081.samples = true
  exact RH65K_Low_0081.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((694399593 : ℝ) / 65536) ((701433717 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((694399593 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0081.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((701433717 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0081.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0081

namespace H65K_PlatformLowBatch0082
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0082.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0082.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0082.samples = true
  exact RH65K_Low_0082.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((701433717 : ℝ) / 65536) ((708481088 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((701433717 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0082.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((708481088 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0082.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0082

namespace H65K_PlatformLowBatch0083
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0083.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0083.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0083.samples = true
  exact RH65K_Low_0083.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((708481088 : ℝ) / 65536) ((715486483 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((708481088 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0083.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((715486483 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0083.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0083

namespace H65K_PlatformLowBatch0084
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0084.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0084.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0084.samples = true
  exact RH65K_Low_0084.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 103 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((715486483 : ℝ) / 65536) ((721160233 : ℝ) / 65536) 103 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((715486483 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0084.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((721160233 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0084.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0084

theorem solution : RS5.BandZeros ((573251611 : ℝ) / 65536) ((721160233 : ℝ) / 65536) 2643 := by
  have h0 := H65K_PlatformLowBatch0064.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0065.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0066.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0067.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0068.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0069.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0070.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0071.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0072.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0073.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0074.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0075.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0076.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0077.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0078.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0079.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0080.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0081.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0082.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0083.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0084.zeros
  exact h20
