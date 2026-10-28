-- Prove2me | solution 1 for H65K.Platform.HighGroup003.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:55:49.854981+00:00
-- url     : https://prove2.me/submissions/0c2535cd-e5ee-4fc0-9721-1ee9a4a7deea

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group012
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group013
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group014
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group015
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0096
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group012).1).1
end RH65K_0096

namespace RH65K_0097
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group012).2).1).1
end RH65K_0097

namespace RH65K_0098
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group012).2).2).1).1
end RH65K_0098

namespace RH65K_0099
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group012).2).2).2).1).1
end RH65K_0099

namespace RH65K_0100
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group012).2).2).2).2).1).1
end RH65K_0100

namespace RH65K_0101
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group012).2).2).2).2).2).1).1
end RH65K_0101

namespace RH65K_0102
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group012).2).2).2).2).2).2).1).1
end RH65K_0102

namespace RH65K_0103
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group012).2).2).2).2).2).2).2).1
end RH65K_0103

namespace RH65K_0104
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group013).1).1
end RH65K_0104

namespace RH65K_0105
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group013).2).1).1
end RH65K_0105

namespace RH65K_0106
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group013).2).2).1).1
end RH65K_0106

namespace RH65K_0107
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group013).2).2).2).1).1
end RH65K_0107

namespace RH65K_0108
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group013).2).2).2).2).1).1
end RH65K_0108

namespace RH65K_0109
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group013).2).2).2).2).2).1).1
end RH65K_0109

namespace RH65K_0110
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group013).2).2).2).2).2).2).1).1
end RH65K_0110

namespace RH65K_0111
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group013).2).2).2).2).2).2).2).1
end RH65K_0111

namespace RH65K_0112
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group014).1).1
end RH65K_0112

namespace RH65K_0113
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group014).2).1).1
end RH65K_0113

namespace RH65K_0114
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group014).2).2).1).1
end RH65K_0114

namespace RH65K_0115
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group014).2).2).2).1).1
end RH65K_0115

namespace RH65K_0116
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group014).2).2).2).2).1).1
end RH65K_0116

namespace RH65K_0117
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group014).2).2).2).2).2).1).1
end RH65K_0117

namespace RH65K_0118
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group014).2).2).2).2).2).2).1).1
end RH65K_0118

namespace RH65K_0119
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group014).2).2).2).2).2).2).2).1
end RH65K_0119

namespace RH65K_0120
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group015).1).1
end RH65K_0120

namespace RH65K_0121
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group015).2).1).1
end RH65K_0121

namespace RH65K_0122
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group015).2).2).1).1
end RH65K_0122

namespace RH65K_0123
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group015).2).2).2).1).1
end RH65K_0123

namespace RH65K_0124
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group015).2).2).2).2).1).1
end RH65K_0124

namespace RH65K_0125
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group015).2).2).2).2).2).1).1
end RH65K_0125

namespace RH65K_0126
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group015).2).2).2).2).2).2).1).1
end RH65K_0126

namespace RH65K_0127
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group015).2).2).2).2).2).2).2).1
end RH65K_0127

namespace H65K_PlatformHighBatch0096
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0096.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0096.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0096.samples = true
  exact RH65K_0096.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1363082502 : ℝ) / 65536) ((1369562094 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1363082502 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0096.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1369562094 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0096.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0096

namespace H65K_PlatformHighBatch0097
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0097.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0097.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0097.samples = true
  exact RH65K_0097.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1369562094 : ℝ) / 65536) ((1376023184 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1369562094 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0097.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1376023184 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0097.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0097

namespace H65K_PlatformHighBatch0098
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0098.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0098.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0098.samples = true
  exact RH65K_0098.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1376023184 : ℝ) / 65536) ((1382465360 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1376023184 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0098.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1382465360 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0098.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0098

namespace H65K_PlatformHighBatch0099
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0099.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0099.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0099.samples = true
  exact RH65K_0099.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1382465360 : ℝ) / 65536) ((1388879579 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1382465360 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0099.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1388879579 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0099.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0099

namespace H65K_PlatformHighBatch0100
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0100.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0100.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0100.samples = true
  exact RH65K_0100.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1388879579 : ℝ) / 65536) ((1395304995 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1388879579 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0100.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1395304995 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0100.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0100

namespace H65K_PlatformHighBatch0101
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0101.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0101.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0101.samples = true
  exact RH65K_0101.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1395304995 : ℝ) / 65536) ((1401734875 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1395304995 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0101.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1401734875 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0101.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0101

namespace H65K_PlatformHighBatch0102
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0102.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0102.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0102.samples = true
  exact RH65K_0102.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1401734875 : ℝ) / 65536) ((1408182122 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1401734875 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0102.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1408182122 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0102.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0102

namespace H65K_PlatformHighBatch0103
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0103.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0103.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0103.samples = true
  exact RH65K_0103.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1408182122 : ℝ) / 65536) ((1414626511 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1408182122 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0103.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1414626511 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0103.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0103

namespace H65K_PlatformHighBatch0104
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0104.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0104.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0104.samples = true
  exact RH65K_0104.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1414626511 : ℝ) / 65536) ((1421047177 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1414626511 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0104.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1421047177 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0104.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0104

namespace H65K_PlatformHighBatch0105
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0105.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0105.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0105.samples = true
  exact RH65K_0105.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1421047177 : ℝ) / 65536) ((1427441892 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1421047177 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0105.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1427441892 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0105.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0105

namespace H65K_PlatformHighBatch0106
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0106.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0106.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0106.samples = true
  exact RH65K_0106.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1427441892 : ℝ) / 65536) ((1433851566 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1427441892 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0106.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1433851566 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0106.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0106

namespace H65K_PlatformHighBatch0107
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0107.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0107.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0107.samples = true
  exact RH65K_0107.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1433851566 : ℝ) / 65536) ((1440273332 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1433851566 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0107.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1440273332 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0107.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0107

namespace H65K_PlatformHighBatch0108
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0108.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0108.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0108.samples = true
  exact RH65K_0108.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1440273332 : ℝ) / 65536) ((1446678601 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1440273332 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0108.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1446678601 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0108.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0108

namespace H65K_PlatformHighBatch0109
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0109.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0109.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0109.samples = true
  exact RH65K_0109.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1446678601 : ℝ) / 65536) ((1453067127 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1446678601 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0109.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1453067127 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0109.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0109

namespace H65K_PlatformHighBatch0110
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0110.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0110.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0110.samples = true
  exact RH65K_0110.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1453067127 : ℝ) / 65536) ((1459463123 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1453067127 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0110.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1459463123 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0110.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0110

namespace H65K_PlatformHighBatch0111
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0111.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0111.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0111.samples = true
  exact RH65K_0111.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1459463123 : ℝ) / 65536) ((1465878491 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1459463123 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0111.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1465878491 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0111.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0111

namespace H65K_PlatformHighBatch0112
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0112.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0112.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0112.samples = true
  exact RH65K_0112.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1465878491 : ℝ) / 65536) ((1472272023 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1465878491 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0112.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1472272023 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0112.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0112

namespace H65K_PlatformHighBatch0113
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0113.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0113.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0113.samples = true
  exact RH65K_0113.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1472272023 : ℝ) / 65536) ((1478668739 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1472272023 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0113.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1478668739 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0113.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0113

namespace H65K_PlatformHighBatch0114
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0114.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0114.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0114.samples = true
  exact RH65K_0114.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1478668739 : ℝ) / 65536) ((1485038307 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1478668739 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0114.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1485038307 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0114.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0114

namespace H65K_PlatformHighBatch0115
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0115.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0115.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0115.samples = true
  exact RH65K_0115.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1485038307 : ℝ) / 65536) ((1491440878 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1485038307 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0115.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1491440878 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0115.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0115

namespace H65K_PlatformHighBatch0116
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0116.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0116.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0116.samples = true
  exact RH65K_0116.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1491440878 : ℝ) / 65536) ((1497835867 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1491440878 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0116.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1497835867 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0116.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0116

namespace H65K_PlatformHighBatch0117
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0117.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0117.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0117.samples = true
  exact RH65K_0117.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1497835867 : ℝ) / 65536) ((1504205167 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1497835867 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0117.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1504205167 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0117.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0117

namespace H65K_PlatformHighBatch0118
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0118.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0118.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0118.samples = true
  exact RH65K_0118.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1504205167 : ℝ) / 65536) ((1510571065 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1504205167 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0118.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1510571065 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0118.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0118

namespace H65K_PlatformHighBatch0119
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0119.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0119.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0119.samples = true
  exact RH65K_0119.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1510571065 : ℝ) / 65536) ((1516937473 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1510571065 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0119.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1516937473 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0119.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0119

namespace H65K_PlatformHighBatch0120
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0120.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0120.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0120.samples = true
  exact RH65K_0120.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1516937473 : ℝ) / 65536) ((1523305011 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1516937473 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0120.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1523305011 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0120.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0120

namespace H65K_PlatformHighBatch0121
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0121.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0121.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0121.samples = true
  exact RH65K_0121.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1523305011 : ℝ) / 65536) ((1529641960 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1523305011 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0121.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1529641960 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0121.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0121

namespace H65K_PlatformHighBatch0122
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0122.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0122.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0122.samples = true
  exact RH65K_0122.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1529641960 : ℝ) / 65536) ((1536011406 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1529641960 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0122.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1536011406 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0122.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0122

namespace H65K_PlatformHighBatch0123
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0123.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0123.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0123.samples = true
  exact RH65K_0123.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1536011406 : ℝ) / 65536) ((1542382693 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1536011406 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0123.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1542382693 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0123.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0123

namespace H65K_PlatformHighBatch0124
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0124.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0124.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0124.samples = true
  exact RH65K_0124.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1542382693 : ℝ) / 65536) ((1548732947 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1542382693 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0124.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1548732947 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0124.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0124

namespace H65K_PlatformHighBatch0125
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0125.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0125.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0125.samples = true
  exact RH65K_0125.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1548732947 : ℝ) / 65536) ((1555060218 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1548732947 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0125.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1555060218 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0125.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0125

namespace H65K_PlatformHighBatch0126
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0126.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0126.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0126.samples = true
  exact RH65K_0126.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1555060218 : ℝ) / 65536) ((1561419428 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1555060218 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0126.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1561419428 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0126.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0126

namespace H65K_PlatformHighBatch0127
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0127.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0127.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0127.samples = true
  exact RH65K_0127.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((1561419428 : ℝ) / 65536) ((1567760127 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((1561419428 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0127.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((1567760127 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0127.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0127

theorem solution : RS5.BandZeros ((1363082502 : ℝ) / 65536) ((1567760127 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0096.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0097.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0098.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0099.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0100.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0101.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0102.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0103.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0104.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0105.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0106.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0107.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0108.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0109.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0110.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0111.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0112.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0113.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0114.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0115.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0116.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0117.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0118.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0119.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0120.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0121.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0122.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0123.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0124.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0125.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0126.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0127.zeros
  exact h31
