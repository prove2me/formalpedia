-- Prove2me | solution 1 for H65K.Platform.Bridge520.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:55:45.897245+00:00
-- url     : https://prove2.me/submissions/0973ac25-01a1-48bb-9bfd-ef5ee2fa9d08

import Theorems.Thm_TaoFivePrimes_arda_rh65k_bridge_arithmetic_group000
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_Bridge_0000
theorem checked : RS5.bandOK samples = true := ((TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000).1).1
theorem changes : RS5.chgBy RS5.Sample.pos samples = 127 := ((TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000).1).2
end RH65K_Bridge_0000

namespace RH65K_Bridge_0001
theorem checked : RS5.bandOK samples = true := (((TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000).2).1).1
theorem changes : RS5.chgBy RS5.Sample.pos samples = 127 := (((TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000).2).1).2
end RH65K_Bridge_0001

namespace RH65K_Bridge_0002
theorem checked : RS5.bandOK samples = true := (((TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000).2).2).1
theorem changes : RS5.chgBy RS5.Sample.pos samples = 112 := (((TaoFivePrimes.arda_rh65k_bridge_arithmetic_group000).2).2).2
end RH65K_Bridge_0002

namespace H65K_PlatformBridgeBatch0000
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := RH65K_Bridge_0000.samples.getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Bridge_0000.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Bridge_0000.samples = true
  exact RH65K_Bridge_0000.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  change RS5.chgBy RS5.Sample.pos RH65K_Bridge_0000.samples = 127
  exact RH65K_Bridge_0000.changes
theorem zeros : RS5.BandZeros ((34078720 : ℝ) / 65536) ((45472510 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((34078720 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Bridge_0000.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((45472510 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Bridge_0000.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformBridgeBatch0000

namespace H65K_PlatformBridgeBatch0001
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := RH65K_Bridge_0001.samples.getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Bridge_0001.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Bridge_0001.samples = true
  exact RH65K_Bridge_0001.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  change RS5.chgBy RS5.Sample.pos RH65K_Bridge_0001.samples = 127
  exact RH65K_Bridge_0001.changes
theorem zeros : RS5.BandZeros ((45472510 : ℝ) / 65536) ((56338504 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((45472510 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Bridge_0001.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((56338504 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Bridge_0001.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformBridgeBatch0001

namespace H65K_PlatformBridgeBatch0002
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := RH65K_Bridge_0002.samples.getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Bridge_0002.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Bridge_0002.samples = true
  exact RH65K_Bridge_0002.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 112 := by
  change RS5.chgBy RS5.Sample.pos RH65K_Bridge_0002.samples = 112
  exact RH65K_Bridge_0002.changes
theorem zeros : RS5.BandZeros ((56338504 : ℝ) / 65536) ((65573390 : ℝ) / 65536) 112 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((56338504 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Bridge_0002.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((65573390 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Bridge_0002.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformBridgeBatch0002

theorem solution : RS5.BandZeros 520 ((65573390 : ℝ) / 65536) 366 := by
  have h0 := H65K_PlatformBridgeBatch0000.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformBridgeBatch0001.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformBridgeBatch0002.zeros
  convert h2 using 1 <;> norm_num
