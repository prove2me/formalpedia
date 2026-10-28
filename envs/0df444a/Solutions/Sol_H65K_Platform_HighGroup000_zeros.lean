-- Prove2me | solution 1 for H65K.Platform.HighGroup000.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:56:10.740985+00:00
-- url     : https://prove2.me/submissions/ce492296-908e-43b9-943a-2ed9b6692d95

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group000
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group001
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group002
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group003
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0000
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group000).1).1
end RH65K_0000

namespace RH65K_0001
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group000).2).1).1
end RH65K_0001

namespace RH65K_0002
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group000).2).2).1).1
end RH65K_0002

namespace RH65K_0003
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group000).2).2).2).1).1
end RH65K_0003

namespace RH65K_0004
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group000).2).2).2).2).1).1
end RH65K_0004

namespace RH65K_0005
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group000).2).2).2).2).2).1).1
end RH65K_0005

namespace RH65K_0006
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group000).2).2).2).2).2).2).1).1
end RH65K_0006

namespace RH65K_0007
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group000).2).2).2).2).2).2).2).1
end RH65K_0007

namespace RH65K_0008
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group001).1).1
end RH65K_0008

namespace RH65K_0009
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group001).2).1).1
end RH65K_0009

namespace RH65K_0010
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group001).2).2).1).1
end RH65K_0010

namespace RH65K_0011
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group001).2).2).2).1).1
end RH65K_0011

namespace RH65K_0012
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group001).2).2).2).2).1).1
end RH65K_0012

namespace RH65K_0013
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group001).2).2).2).2).2).1).1
end RH65K_0013

namespace RH65K_0014
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group001).2).2).2).2).2).2).1).1
end RH65K_0014

namespace RH65K_0015
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group001).2).2).2).2).2).2).2).1
end RH65K_0015

namespace RH65K_0016
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group002).1).1
end RH65K_0016

namespace RH65K_0017
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group002).2).1).1
end RH65K_0017

namespace RH65K_0018
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group002).2).2).1).1
end RH65K_0018

namespace RH65K_0019
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group002).2).2).2).1).1
end RH65K_0019

namespace RH65K_0020
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group002).2).2).2).2).1).1
end RH65K_0020

namespace RH65K_0021
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group002).2).2).2).2).2).1).1
end RH65K_0021

namespace RH65K_0022
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group002).2).2).2).2).2).2).1).1
end RH65K_0022

namespace RH65K_0023
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group002).2).2).2).2).2).2).2).1
end RH65K_0023

namespace RH65K_0024
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group003).1).1
end RH65K_0024

namespace RH65K_0025
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group003).2).1).1
end RH65K_0025

namespace RH65K_0026
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group003).2).2).1).1
end RH65K_0026

namespace RH65K_0027
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group003).2).2).2).1).1
end RH65K_0027

namespace RH65K_0028
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group003).2).2).2).2).1).1
end RH65K_0028

namespace RH65K_0029
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group003).2).2).2).2).2).1).1
end RH65K_0029

namespace RH65K_0030
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group003).2).2).2).2).2).2).1).1
end RH65K_0030

namespace RH65K_0031
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group003).2).2).2).2).2).2).2).1
end RH65K_0031

namespace H65K_PlatformHighBatch0000
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0000.samples.drop 1).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0000.samples.drop 2
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  have hc := RH65K_0000.checked
  change (RS5.sampleOK' (RH65K_0000.samples.getD 0 dummy) &&
    RS5.ltH (RH65K_0000.samples.getD 0 dummy) (RH65K_0000.samples.getD 1 dummy) &&
    RS5.bandOK' (RH65K_0000.samples.drop 1)) = true at hc
  simp only [Bool.and_eq_true] at hc
  have ht := hc.2
  change RS5.bandOK' (RH65K_0000.samples.drop 1) = true
  exact ht
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 126 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((721160233 : ℝ) / 65536) ((728095589 : ℝ) / 65536) 126 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((721160233 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0000.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((728095589 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0000.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0000

namespace H65K_PlatformHighBatch0001
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0001.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0001.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0001.samples = true
  exact RH65K_0001.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((728095589 : ℝ) / 65536) ((735113554 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((728095589 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0001.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((735113554 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0001.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0001

namespace H65K_PlatformHighBatch0002
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0002.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0002.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0002.samples = true
  exact RH65K_0002.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((735113554 : ℝ) / 65536) ((742086194 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((735113554 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0002.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((742086194 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0002.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0002

namespace H65K_PlatformHighBatch0003
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0003.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0003.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0003.samples = true
  exact RH65K_0003.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((742086194 : ℝ) / 65536) ((749027509 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((742086194 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0003.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((749027509 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0003.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0003

namespace H65K_PlatformHighBatch0004
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0004.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0004.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0004.samples = true
  exact RH65K_0004.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((749027509 : ℝ) / 65536) ((756005370 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((749027509 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0004.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((756005370 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0004.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0004

namespace H65K_PlatformHighBatch0005
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0005.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0005.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0005.samples = true
  exact RH65K_0005.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((756005370 : ℝ) / 65536) ((762970802 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((756005370 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0005.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((762970802 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0005.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0005

namespace H65K_PlatformHighBatch0006
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0006.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0006.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0006.samples = true
  exact RH65K_0006.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((762970802 : ℝ) / 65536) ((769933440 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((762970802 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0006.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((769933440 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0006.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0006

namespace H65K_PlatformHighBatch0007
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0007.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0007.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0007.samples = true
  exact RH65K_0007.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((769933440 : ℝ) / 65536) ((776846342 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((769933440 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0007.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((776846342 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0007.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0007

namespace H65K_PlatformHighBatch0008
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0008.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0008.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0008.samples = true
  exact RH65K_0008.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((776846342 : ℝ) / 65536) ((783800679 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((776846342 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0008.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((783800679 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0008.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0008

namespace H65K_PlatformHighBatch0009
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0009.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0009.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0009.samples = true
  exact RH65K_0009.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((783800679 : ℝ) / 65536) ((790700526 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((783800679 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0009.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((790700526 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0009.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0009

namespace H65K_PlatformHighBatch0010
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0010.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0010.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0010.samples = true
  exact RH65K_0010.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((790700526 : ℝ) / 65536) ((797616393 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((790700526 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0010.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((797616393 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0010.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0010

namespace H65K_PlatformHighBatch0011
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0011.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0011.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0011.samples = true
  exact RH65K_0011.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((797616393 : ℝ) / 65536) ((804531257 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((797616393 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0011.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((804531257 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0011.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0011

namespace H65K_PlatformHighBatch0012
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0012.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0012.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0012.samples = true
  exact RH65K_0012.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((804531257 : ℝ) / 65536) ((811405096 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((804531257 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0012.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((811405096 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0012.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0012

namespace H65K_PlatformHighBatch0013
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0013.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0013.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0013.samples = true
  exact RH65K_0013.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((811405096 : ℝ) / 65536) ((818329473 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((811405096 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0013.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((818329473 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0013.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0013

namespace H65K_PlatformHighBatch0014
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0014.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0014.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0014.samples = true
  exact RH65K_0014.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((818329473 : ℝ) / 65536) ((825200047 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((818329473 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0014.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((825200047 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0014.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0014

namespace H65K_PlatformHighBatch0015
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0015.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0015.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0015.samples = true
  exact RH65K_0015.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((825200047 : ℝ) / 65536) ((832061502 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((825200047 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0015.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((832061502 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0015.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0015

namespace H65K_PlatformHighBatch0016
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0016.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0016.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0016.samples = true
  exact RH65K_0016.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((832061502 : ℝ) / 65536) ((838953611 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((832061502 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0016.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((838953611 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0016.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0016

namespace H65K_PlatformHighBatch0017
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0017.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0017.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0017.samples = true
  exact RH65K_0017.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((838953611 : ℝ) / 65536) ((845779942 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((838953611 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0017.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((845779942 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0017.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0017

namespace H65K_PlatformHighBatch0018
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0018.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0018.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0018.samples = true
  exact RH65K_0018.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((845779942 : ℝ) / 65536) ((852649635 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((845779942 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0018.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((852649635 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0018.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0018

namespace H65K_PlatformHighBatch0019
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0019.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0019.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0019.samples = true
  exact RH65K_0019.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((852649635 : ℝ) / 65536) ((859484184 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((852649635 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0019.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((859484184 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0019.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0019

namespace H65K_PlatformHighBatch0020
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0020.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0020.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0020.samples = true
  exact RH65K_0020.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((859484184 : ℝ) / 65536) ((866346255 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((859484184 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0020.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((866346255 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0020.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0020

namespace H65K_PlatformHighBatch0021
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0021.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0021.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0021.samples = true
  exact RH65K_0021.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((866346255 : ℝ) / 65536) ((873139498 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((866346255 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0021.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((873139498 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0021.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0021

namespace H65K_PlatformHighBatch0022
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0022.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0022.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0022.samples = true
  exact RH65K_0022.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((873139498 : ℝ) / 65536) ((879982499 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((873139498 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0022.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((879982499 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0022.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0022

namespace H65K_PlatformHighBatch0023
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0023.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0023.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0023.samples = true
  exact RH65K_0023.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((879982499 : ℝ) / 65536) ((886784806 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((879982499 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0023.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((886784806 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0023.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0023

namespace H65K_PlatformHighBatch0024
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0024.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0024.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0024.samples = true
  exact RH65K_0024.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((886784806 : ℝ) / 65536) ((893623716 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((886784806 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0024.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((893623716 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0024.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0024

namespace H65K_PlatformHighBatch0025
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0025.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0025.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0025.samples = true
  exact RH65K_0025.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((893623716 : ℝ) / 65536) ((900424703 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((893623716 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0025.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((900424703 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0025.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0025

namespace H65K_PlatformHighBatch0026
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0026.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0026.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0026.samples = true
  exact RH65K_0026.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((900424703 : ℝ) / 65536) ((907233569 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((900424703 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0026.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((907233569 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0026.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0026

namespace H65K_PlatformHighBatch0027
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0027.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0027.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0027.samples = true
  exact RH65K_0027.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((907233569 : ℝ) / 65536) ((914003556 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((907233569 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0027.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((914003556 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0027.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0027

namespace H65K_PlatformHighBatch0028
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0028.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0028.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0028.samples = true
  exact RH65K_0028.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((914003556 : ℝ) / 65536) ((920777816 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((914003556 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0028.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((920777816 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0028.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0028

namespace H65K_PlatformHighBatch0029
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0029.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0029.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0029.samples = true
  exact RH65K_0029.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((920777816 : ℝ) / 65536) ((927566648 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((920777816 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0029.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((927566648 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0029.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0029

namespace H65K_PlatformHighBatch0030
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0030.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0030.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0030.samples = true
  exact RH65K_0030.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((927566648 : ℝ) / 65536) ((934310950 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((927566648 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0030.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((934310950 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0030.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0030

namespace H65K_PlatformHighBatch0031
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0031.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0031.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0031.samples = true
  exact RH65K_0031.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((934310950 : ℝ) / 65536) ((941117753 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((934310950 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0031.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((941117753 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0031.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0031

theorem solution : RS5.BandZeros ((721160233 : ℝ) / 65536) ((941117753 : ℝ) / 65536) 4063 := by
  have h0 := H65K_PlatformHighBatch0000.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0001.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0002.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0003.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0004.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0005.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0006.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0007.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0008.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0009.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0010.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0011.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0012.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0013.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0014.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0015.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0016.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0017.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0018.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0019.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0020.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0021.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0022.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0023.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0024.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0025.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0026.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0027.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0028.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0029.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0030.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0031.zeros
  exact h31
