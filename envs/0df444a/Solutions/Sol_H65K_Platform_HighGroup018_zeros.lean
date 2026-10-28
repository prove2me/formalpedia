-- Prove2me | solution 1 for H65K.Platform.HighGroup018.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:15:07.421851+00:00
-- url     : https://prove2.me/submissions/02af246e-0b34-448b-b1d4-4b0e51e5e2d1

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group072
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0576
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group072).1).1
end RH65K_0576

namespace RH65K_0577
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group072).2).1).1
end RH65K_0577

namespace RH65K_0578
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group072).2).2).1).1
end RH65K_0578

namespace RH65K_0579
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group072).2).2).2).1).1
end RH65K_0579

namespace RH65K_0580
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group072).2).2).2).2).1).1
end RH65K_0580

namespace RH65K_0581
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group072).2).2).2).2).2).1).1
end RH65K_0581

namespace RH65K_0582
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group072).2).2).2).2).2).2).1
end RH65K_0582

namespace H65K_PlatformHighBatch0576
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0576.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0576.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0576.samples = true
  exact RH65K_0576.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4223826555 : ℝ) / 65536) ((4229484973 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4223826555 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0576.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4229484973 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0576.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0576

namespace H65K_PlatformHighBatch0577
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0577.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0577.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0577.samples = true
  exact RH65K_0577.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4229484973 : ℝ) / 65536) ((4235145618 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4229484973 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0577.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4235145618 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0577.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0577

namespace H65K_PlatformHighBatch0578
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0578.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0578.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0578.samples = true
  exact RH65K_0578.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4235145618 : ℝ) / 65536) ((4240800892 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4235145618 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0578.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4240800892 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0578.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0578

namespace H65K_PlatformHighBatch0579
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0579.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0579.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0579.samples = true
  exact RH65K_0579.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4240800892 : ℝ) / 65536) ((4246467194 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4240800892 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0579.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4246467194 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0579.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0579

namespace H65K_PlatformHighBatch0580
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0580.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0580.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0580.samples = true
  exact RH65K_0580.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4246467194 : ℝ) / 65536) ((4252113682 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4246467194 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0580.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4252113682 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0580.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0580

namespace H65K_PlatformHighBatch0581
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0581.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0581.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0581.samples = true
  exact RH65K_0581.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4252113682 : ℝ) / 65536) ((4257765695 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4252113682 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0581.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4257765695 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0581.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0581

namespace H65K_PlatformHighBatch0582
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0582.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0582.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0582.samples = true
  exact RH65K_0582.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 46 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4257765695 : ℝ) / 65536) ((4259840000 : ℝ) / 65536) 46 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4257765695 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0582.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4259840000 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0582.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0582

theorem solution : RS5.BandZeros ((4223826555 : ℝ) / 65536) ((4259840000 : ℝ) / 65536) 808 := by
  have h0 := H65K_PlatformHighBatch0576.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0577.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0578.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0579.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0580.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0581.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0582.zeros
  exact h6
