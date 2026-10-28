-- Prove2me | solution 1 for H65K.Platform.LowGroup000.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:14:10.865296+00:00
-- url     : https://prove2.me/submissions/609bc0c7-0f5a-444e-a36a-70d01ce01c24

import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group000
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group001
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group002
import Theorems.Thm_TaoFivePrimes_arda_rh65k_low_arithmetic_group003
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_Low_0000
theorem checked : RS5.bandOK samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).1).1
end RH65K_Low_0000

namespace RH65K_Low_0001
theorem checked : RS5.bandOK samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).1).1
end RH65K_Low_0001

namespace RH65K_Low_0002
theorem checked : RS5.bandOK samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).1).1
end RH65K_Low_0002

namespace RH65K_Low_0003
theorem checked : RS5.bandOK samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).1).1
end RH65K_Low_0003

namespace RH65K_Low_0004
theorem checked : RS5.bandOK samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).2).1).1
end RH65K_Low_0004

namespace RH65K_Low_0005
theorem checked : RS5.bandOK samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).2).2).1).1
end RH65K_Low_0005

namespace RH65K_Low_0006
theorem checked : RS5.bandOK samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).2).2).2).1).1
end RH65K_Low_0006

namespace RH65K_Low_0007
theorem checked : RS5.bandOK samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group000).2).2).2).2).2).2).2).1
end RH65K_Low_0007

namespace RH65K_Low_0008
theorem checked : RS5.bandOK samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).1).1
end RH65K_Low_0008

namespace RH65K_Low_0009
theorem checked : RS5.bandOK samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).1).1
end RH65K_Low_0009

namespace RH65K_Low_0010
theorem checked : RS5.bandOK samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).2).1).1
end RH65K_Low_0010

namespace RH65K_Low_0011
theorem checked : RS5.bandOK samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).2).2).1).1
end RH65K_Low_0011

namespace RH65K_Low_0012
theorem checked : RS5.bandOK samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).2).2).2).1).1
end RH65K_Low_0012

namespace RH65K_Low_0013
theorem checked : RS5.bandOK samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).2).2).2).2).1).1
end RH65K_Low_0013

namespace RH65K_Low_0014
theorem checked : RS5.bandOK samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).2).2).2).2).2).1).1
end RH65K_Low_0014

namespace RH65K_Low_0015
theorem checked : RS5.bandOK samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group001).2).2).2).2).2).2).2).1
end RH65K_Low_0015

namespace RH65K_Low_0016
theorem checked : RS5.bandOK samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group002).1).1
end RH65K_Low_0016

namespace RH65K_Low_0017
theorem checked : RS5.bandOK samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group002).2).1).1
end RH65K_Low_0017

namespace RH65K_Low_0018
theorem checked : RS5.bandOK samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group002).2).2).1).1
end RH65K_Low_0018

namespace RH65K_Low_0019
theorem checked : RS5.bandOK samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group002).2).2).2).1).1
end RH65K_Low_0019

namespace RH65K_Low_0020
theorem checked : RS5.bandOK samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group002).2).2).2).2).1).1
end RH65K_Low_0020

namespace RH65K_Low_0021
theorem checked : RS5.bandOK samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group002).2).2).2).2).2).1).1
end RH65K_Low_0021

namespace RH65K_Low_0022
theorem checked : RS5.bandOK samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group002).2).2).2).2).2).2).1).1
end RH65K_Low_0022

namespace RH65K_Low_0023
theorem checked : RS5.bandOK samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group002).2).2).2).2).2).2).2).1
end RH65K_Low_0023

namespace RH65K_Low_0024
theorem checked : RS5.bandOK samples = true := ((TaoFivePrimes.arda_rh65k_low_arithmetic_group003).1).1
end RH65K_Low_0024

namespace RH65K_Low_0025
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_low_arithmetic_group003).2).1).1
end RH65K_Low_0025

namespace RH65K_Low_0026
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_low_arithmetic_group003).2).2).1).1
end RH65K_Low_0026

namespace RH65K_Low_0027
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_low_arithmetic_group003).2).2).2).1).1
end RH65K_Low_0027

namespace RH65K_Low_0028
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group003).2).2).2).2).1).1
end RH65K_Low_0028

namespace RH65K_Low_0029
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group003).2).2).2).2).2).1).1
end RH65K_Low_0029

namespace RH65K_Low_0030
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group003).2).2).2).2).2).2).1).1
end RH65K_Low_0030

namespace RH65K_Low_0031
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_low_arithmetic_group003).2).2).2).2).2).2).2).1
end RH65K_Low_0031

namespace H65K_PlatformLowBatch0000
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0000.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0000.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0000.samples = true
  exact RH65K_Low_0000.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((65573390 : ℝ) / 65536) ((75737303 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((65573390 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0000.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((75737303 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0000.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0000

namespace H65K_PlatformLowBatch0001
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0001.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0001.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0001.samples = true
  exact RH65K_Low_0001.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((75737303 : ℝ) / 65536) ((85648200 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((75737303 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0001.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((85648200 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0001.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0001

namespace H65K_PlatformLowBatch0002
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0002.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0002.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0002.samples = true
  exact RH65K_Low_0002.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((85648200 : ℝ) / 65536) ((95339744 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((85648200 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0002.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((95339744 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0002.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0002

namespace H65K_PlatformLowBatch0003
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0003.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0003.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0003.samples = true
  exact RH65K_Low_0003.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((95339744 : ℝ) / 65536) ((104846701 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((95339744 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0003.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((104846701 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0003.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0003

namespace H65K_PlatformLowBatch0004
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0004.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0004.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0004.samples = true
  exact RH65K_Low_0004.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((104846701 : ℝ) / 65536) ((114225778 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((104846701 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0004.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((114225778 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0004.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0004

namespace H65K_PlatformLowBatch0005
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0005.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0005.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0005.samples = true
  exact RH65K_Low_0005.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((114225778 : ℝ) / 65536) ((123450638 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((114225778 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0005.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((123450638 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0005.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0005

namespace H65K_PlatformLowBatch0006
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0006.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0006.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0006.samples = true
  exact RH65K_Low_0006.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((123450638 : ℝ) / 65536) ((132583211 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((123450638 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0006.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((132583211 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0006.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0006

namespace H65K_PlatformLowBatch0007
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0007.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0007.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0007.samples = true
  exact RH65K_Low_0007.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((132583211 : ℝ) / 65536) ((141582511 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((132583211 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0007.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((141582511 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0007.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0007

namespace H65K_PlatformLowBatch0008
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0008.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0008.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0008.samples = true
  exact RH65K_Low_0008.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((141582511 : ℝ) / 65536) ((150507146 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((141582511 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0008.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((150507146 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0008.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0008

namespace H65K_PlatformLowBatch0009
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0009.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0009.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0009.samples = true
  exact RH65K_Low_0009.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((150507146 : ℝ) / 65536) ((159313983 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((150507146 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0009.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((159313983 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0009.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0009

namespace H65K_PlatformLowBatch0010
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0010.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0010.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0010.samples = true
  exact RH65K_Low_0010.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((159313983 : ℝ) / 65536) ((168028858 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((159313983 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0010.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((168028858 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0010.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0010

namespace H65K_PlatformLowBatch0011
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0011.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0011.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0011.samples = true
  exact RH65K_Low_0011.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((168028858 : ℝ) / 65536) ((176699651 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((168028858 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0011.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((176699651 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0011.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0011

namespace H65K_PlatformLowBatch0012
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0012.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0012.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0012.samples = true
  exact RH65K_Low_0012.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((176699651 : ℝ) / 65536) ((185294590 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((176699651 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0012.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((185294590 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0012.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0012

namespace H65K_PlatformLowBatch0013
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0013.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0013.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0013.samples = true
  exact RH65K_Low_0013.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((185294590 : ℝ) / 65536) ((193839989 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((185294590 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0013.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((193839989 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0013.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0013

namespace H65K_PlatformLowBatch0014
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0014.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0014.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0014.samples = true
  exact RH65K_Low_0014.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((193839989 : ℝ) / 65536) ((202276350 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((193839989 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0014.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((202276350 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0014.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0014

namespace H65K_PlatformLowBatch0015
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0015.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0015.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0015.samples = true
  exact RH65K_Low_0015.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((202276350 : ℝ) / 65536) ((210698006 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((202276350 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0015.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((210698006 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0015.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0015

namespace H65K_PlatformLowBatch0016
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0016.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0016.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0016.samples = true
  exact RH65K_Low_0016.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((210698006 : ℝ) / 65536) ((219062707 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((210698006 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0016.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((219062707 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0016.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0016

namespace H65K_PlatformLowBatch0017
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0017.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0017.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0017.samples = true
  exact RH65K_Low_0017.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((219062707 : ℝ) / 65536) ((227355114 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((219062707 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0017.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((227355114 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0017.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0017

namespace H65K_PlatformLowBatch0018
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0018.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0018.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0018.samples = true
  exact RH65K_Low_0018.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((227355114 : ℝ) / 65536) ((235610057 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((227355114 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0018.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((235610057 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0018.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0018

namespace H65K_PlatformLowBatch0019
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0019.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0019.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0019.samples = true
  exact RH65K_Low_0019.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((235610057 : ℝ) / 65536) ((243842354 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((235610057 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0019.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((243842354 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0019.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0019

namespace H65K_PlatformLowBatch0020
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0020.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0020.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0020.samples = true
  exact RH65K_Low_0020.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((243842354 : ℝ) / 65536) ((252031286 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((243842354 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0020.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((252031286 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0020.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0020

namespace H65K_PlatformLowBatch0021
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0021.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0021.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0021.samples = true
  exact RH65K_Low_0021.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((252031286 : ℝ) / 65536) ((260125466 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((252031286 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0021.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((260125466 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0021.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0021

namespace H65K_PlatformLowBatch0022
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0022.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0022.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0022.samples = true
  exact RH65K_Low_0022.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((260125466 : ℝ) / 65536) ((268223957 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((260125466 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0022.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((268223957 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0022.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0022

namespace H65K_PlatformLowBatch0023
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0023.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0023.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0023.samples = true
  exact RH65K_Low_0023.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((268223957 : ℝ) / 65536) ((276300150 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((268223957 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0023.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((276300150 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0023.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0023

namespace H65K_PlatformLowBatch0024
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0024.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0024.samples.drop 1
theorem inputOK : RS5.bandOK (first :: rest) = true := by
  change RS5.bandOK RH65K_Low_0024.samples = true
  exact RH65K_Low_0024.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 36 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((276300150 : ℝ) / 65536) ((278556407 : ℝ) / 65536) 36 := by
  have hz := RS5.bandZeros_of_ok first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((276300150 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0024.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((278556407 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0024.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0024

namespace H65K_PlatformLowBatch0025
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0025.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0025.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0025.samples = true
  exact RH65K_Low_0025.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((278556407 : ℝ) / 65536) ((286577822 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((278556407 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0025.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((286577822 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0025.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0025

namespace H65K_PlatformLowBatch0026
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0026.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0026.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0026.samples = true
  exact RH65K_Low_0026.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((286577822 : ℝ) / 65536) ((294519681 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((286577822 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0026.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((294519681 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0026.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0026

namespace H65K_PlatformLowBatch0027
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0027.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0027.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0027.samples = true
  exact RH65K_Low_0027.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((294519681 : ℝ) / 65536) ((302506276 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((294519681 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0027.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((302506276 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0027.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0027

namespace H65K_PlatformLowBatch0028
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0028.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0028.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0028.samples = true
  exact RH65K_Low_0028.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((302506276 : ℝ) / 65536) ((310399525 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((302506276 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0028.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((310399525 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0028.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0028

namespace H65K_PlatformLowBatch0029
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0029.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0029.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0029.samples = true
  exact RH65K_Low_0029.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((310399525 : ℝ) / 65536) ((318263797 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((310399525 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0029.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((318263797 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0029.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0029

namespace H65K_PlatformLowBatch0030
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0030.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0030.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0030.samples = true
  exact RH65K_Low_0030.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((318263797 : ℝ) / 65536) ((326116148 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((318263797 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0030.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((326116148 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0030.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0030

namespace H65K_PlatformLowBatch0031
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_Low_0031.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_Low_0031.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_Low_0031.samples = true
  exact RH65K_Low_0031.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((326116148 : ℝ) / 65536) ((333962439 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((326116148 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_Low_0031.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((333962439 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_Low_0031.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformLowBatch0031

theorem solution : RS5.BandZeros ((65573390 : ℝ) / 65536) ((333962439 : ℝ) / 65536) 3973 := by
  have h0 := H65K_PlatformLowBatch0000.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0001.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0002.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0003.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0004.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0005.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0006.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0007.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0008.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0009.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0010.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0011.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0012.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0013.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0014.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0015.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0016.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0017.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0018.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0019.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0020.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0021.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0022.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0023.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0024.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0025.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0026.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0027.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0028.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0029.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0030.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformLowBatch0031.zeros
  exact h31
