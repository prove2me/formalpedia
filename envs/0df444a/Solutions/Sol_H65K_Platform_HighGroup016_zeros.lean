-- Prove2me | solution 1 for H65K.Platform.HighGroup016.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:12:24.543476+00:00
-- url     : https://prove2.me/submissions/2a0f1aa9-91a1-45dd-9ab9-292d1ba12f95

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group064
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group065
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group066
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group067
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0512
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group064).1).1
end RH65K_0512

namespace RH65K_0513
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group064).2).1).1
end RH65K_0513

namespace RH65K_0514
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group064).2).2).1).1
end RH65K_0514

namespace RH65K_0515
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group064).2).2).2).1).1
end RH65K_0515

namespace RH65K_0516
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group064).2).2).2).2).1).1
end RH65K_0516

namespace RH65K_0517
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group064).2).2).2).2).2).1).1
end RH65K_0517

namespace RH65K_0518
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group064).2).2).2).2).2).2).1).1
end RH65K_0518

namespace RH65K_0519
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group064).2).2).2).2).2).2).2).1
end RH65K_0519

namespace RH65K_0520
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group065).1).1
end RH65K_0520

namespace RH65K_0521
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group065).2).1).1
end RH65K_0521

namespace RH65K_0522
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group065).2).2).1).1
end RH65K_0522

namespace RH65K_0523
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group065).2).2).2).1).1
end RH65K_0523

namespace RH65K_0524
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group065).2).2).2).2).1).1
end RH65K_0524

namespace RH65K_0525
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group065).2).2).2).2).2).1).1
end RH65K_0525

namespace RH65K_0526
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group065).2).2).2).2).2).2).1).1
end RH65K_0526

namespace RH65K_0527
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group065).2).2).2).2).2).2).2).1
end RH65K_0527

namespace RH65K_0528
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group066).1).1
end RH65K_0528

namespace RH65K_0529
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group066).2).1).1
end RH65K_0529

namespace RH65K_0530
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group066).2).2).1).1
end RH65K_0530

namespace RH65K_0531
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group066).2).2).2).1).1
end RH65K_0531

namespace RH65K_0532
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group066).2).2).2).2).1).1
end RH65K_0532

namespace RH65K_0533
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group066).2).2).2).2).2).1).1
end RH65K_0533

namespace RH65K_0534
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group066).2).2).2).2).2).2).1).1
end RH65K_0534

namespace RH65K_0535
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group066).2).2).2).2).2).2).2).1
end RH65K_0535

namespace RH65K_0536
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group067).1).1
end RH65K_0536

namespace RH65K_0537
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group067).2).1).1
end RH65K_0537

namespace RH65K_0538
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group067).2).2).1).1
end RH65K_0538

namespace RH65K_0539
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group067).2).2).2).1).1
end RH65K_0539

namespace RH65K_0540
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group067).2).2).2).2).1).1
end RH65K_0540

namespace RH65K_0541
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group067).2).2).2).2).2).1).1
end RH65K_0541

namespace RH65K_0542
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group067).2).2).2).2).2).2).1).1
end RH65K_0542

namespace RH65K_0543
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group067).2).2).2).2).2).2).2).1
end RH65K_0543

namespace H65K_PlatformHighBatch0512
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0512.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0512.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0512.samples = true
  exact RH65K_0512.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3859677541 : ℝ) / 65536) ((3865384120 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3859677541 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0512.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3865384120 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0512.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0512

namespace H65K_PlatformHighBatch0513
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0513.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0513.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0513.samples = true
  exact RH65K_0513.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3865384120 : ℝ) / 65536) ((3871127829 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3865384120 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0513.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3871127829 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0513.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0513

namespace H65K_PlatformHighBatch0514
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0514.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0514.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0514.samples = true
  exact RH65K_0514.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3871127829 : ℝ) / 65536) ((3876812744 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3871127829 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0514.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3876812744 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0514.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0514

namespace H65K_PlatformHighBatch0515
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0515.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0515.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0515.samples = true
  exact RH65K_0515.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3876812744 : ℝ) / 65536) ((3882542484 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3876812744 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0515.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3882542484 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0515.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0515

namespace H65K_PlatformHighBatch0516
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0516.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0516.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0516.samples = true
  exact RH65K_0516.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3882542484 : ℝ) / 65536) ((3888260891 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3882542484 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0516.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3888260891 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0516.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0516

namespace H65K_PlatformHighBatch0517
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0517.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0517.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0517.samples = true
  exact RH65K_0517.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3888260891 : ℝ) / 65536) ((3893954710 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3888260891 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0517.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3893954710 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0517.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0517

namespace H65K_PlatformHighBatch0518
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0518.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0518.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0518.samples = true
  exact RH65K_0518.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3893954710 : ℝ) / 65536) ((3899696135 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3893954710 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0518.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3899696135 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0518.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0518

namespace H65K_PlatformHighBatch0519
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0519.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0519.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0519.samples = true
  exact RH65K_0519.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3899696135 : ℝ) / 65536) ((3905393697 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3899696135 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0519.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3905393697 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0519.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0519

namespace H65K_PlatformHighBatch0520
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0520.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0520.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0520.samples = true
  exact RH65K_0520.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3905393697 : ℝ) / 65536) ((3911094358 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3905393697 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0520.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3911094358 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0520.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0520

namespace H65K_PlatformHighBatch0521
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0521.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0521.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0521.samples = true
  exact RH65K_0521.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3911094358 : ℝ) / 65536) ((3916817666 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3911094358 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0521.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3916817666 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0521.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0521

namespace H65K_PlatformHighBatch0522
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0522.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0522.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0522.samples = true
  exact RH65K_0522.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3916817666 : ℝ) / 65536) ((3922526124 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3916817666 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0522.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3922526124 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0522.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0522

namespace H65K_PlatformHighBatch0523
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0523.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0523.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0523.samples = true
  exact RH65K_0523.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3922526124 : ℝ) / 65536) ((3928233033 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3922526124 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0523.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3928233033 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0523.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0523

namespace H65K_PlatformHighBatch0524
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0524.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0524.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0524.samples = true
  exact RH65K_0524.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3928233033 : ℝ) / 65536) ((3933936334 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3928233033 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0524.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3933936334 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0524.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0524

namespace H65K_PlatformHighBatch0525
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0525.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0525.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0525.samples = true
  exact RH65K_0525.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3933936334 : ℝ) / 65536) ((3939634150 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3933936334 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0525.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3939634150 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0525.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0525

namespace H65K_PlatformHighBatch0526
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0526.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0526.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0526.samples = true
  exact RH65K_0526.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3939634150 : ℝ) / 65536) ((3945364000 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3939634150 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0526.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3945364000 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0526.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0526

namespace H65K_PlatformHighBatch0527
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0527.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0527.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0527.samples = true
  exact RH65K_0527.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3945364000 : ℝ) / 65536) ((3951047427 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3945364000 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0527.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3951047427 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0527.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0527

namespace H65K_PlatformHighBatch0528
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0528.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0528.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0528.samples = true
  exact RH65K_0528.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3951047427 : ℝ) / 65536) ((3956765193 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3951047427 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0528.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3956765193 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0528.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0528

namespace H65K_PlatformHighBatch0529
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0529.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0529.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0529.samples = true
  exact RH65K_0529.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3956765193 : ℝ) / 65536) ((3962460824 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3956765193 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0529.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3962460824 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0529.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0529

namespace H65K_PlatformHighBatch0530
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0530.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0530.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0530.samples = true
  exact RH65K_0530.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3962460824 : ℝ) / 65536) ((3968142965 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3962460824 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0530.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3968142965 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0530.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0530

namespace H65K_PlatformHighBatch0531
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0531.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0531.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0531.samples = true
  exact RH65K_0531.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3968142965 : ℝ) / 65536) ((3973882596 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3968142965 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0531.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3973882596 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0531.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0531

namespace H65K_PlatformHighBatch0532
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0532.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0532.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0532.samples = true
  exact RH65K_0532.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3973882596 : ℝ) / 65536) ((3979559422 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3973882596 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0532.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3979559422 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0532.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0532

namespace H65K_PlatformHighBatch0533
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0533.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0533.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0533.samples = true
  exact RH65K_0533.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3979559422 : ℝ) / 65536) ((3985257780 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3979559422 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0533.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3985257780 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0533.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0533

namespace H65K_PlatformHighBatch0534
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0534.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0534.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0534.samples = true
  exact RH65K_0534.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3985257780 : ℝ) / 65536) ((3990935102 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3985257780 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0534.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3990935102 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0534.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0534

namespace H65K_PlatformHighBatch0535
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0535.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0535.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0535.samples = true
  exact RH65K_0535.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3990935102 : ℝ) / 65536) ((3996641753 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3990935102 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0535.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3996641753 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0535.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0535

namespace H65K_PlatformHighBatch0536
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0536.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0536.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0536.samples = true
  exact RH65K_0536.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3996641753 : ℝ) / 65536) ((4002365593 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3996641753 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0536.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4002365593 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0536.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0536

namespace H65K_PlatformHighBatch0537
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0537.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0537.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0537.samples = true
  exact RH65K_0537.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4002365593 : ℝ) / 65536) ((4008034124 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4002365593 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0537.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4008034124 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0537.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0537

namespace H65K_PlatformHighBatch0538
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0538.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0538.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0538.samples = true
  exact RH65K_0538.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4008034124 : ℝ) / 65536) ((4013730532 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4008034124 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0538.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4013730532 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0538.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0538

namespace H65K_PlatformHighBatch0539
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0539.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0539.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0539.samples = true
  exact RH65K_0539.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4013730532 : ℝ) / 65536) ((4019420880 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4013730532 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0539.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4019420880 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0539.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0539

namespace H65K_PlatformHighBatch0540
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0540.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0540.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0540.samples = true
  exact RH65K_0540.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4019420880 : ℝ) / 65536) ((4025122781 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4019420880 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0540.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4025122781 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0540.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0540

namespace H65K_PlatformHighBatch0541
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0541.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0541.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0541.samples = true
  exact RH65K_0541.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4025122781 : ℝ) / 65536) ((4030829365 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4025122781 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0541.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4030829365 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0541.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0541

namespace H65K_PlatformHighBatch0542
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0542.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0542.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0542.samples = true
  exact RH65K_0542.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4030829365 : ℝ) / 65536) ((4036499504 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4030829365 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0542.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4036499504 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0542.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0542

namespace H65K_PlatformHighBatch0543
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0543.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0543.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0543.samples = true
  exact RH65K_0543.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((4036499504 : ℝ) / 65536) ((4042205117 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((4036499504 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0543.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((4042205117 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0543.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0543

theorem solution : RS5.BandZeros ((3859677541 : ℝ) / 65536) ((4042205117 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0512.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0513.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0514.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0515.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0516.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0517.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0518.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0519.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0520.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0521.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0522.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0523.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0524.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0525.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0526.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0527.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0528.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0529.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0530.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0531.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0532.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0533.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0534.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0535.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0536.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0537.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0538.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0539.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0540.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0541.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0542.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0543.zeros
  exact h31
