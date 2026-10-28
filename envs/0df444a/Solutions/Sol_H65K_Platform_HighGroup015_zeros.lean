-- Prove2me | solution 1 for H65K.Platform.HighGroup015.zeros
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:10:35.847019+00:00
-- url     : https://prove2.me/submissions/4e712fa9-b3cc-4dee-ba67-cac9e554674d

import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group060
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group061
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group062
import Theorems.Thm_TaoFivePrimes_arda_rh65k_arithmetic_group063
import Theorems.Thm_RS5_bandZeros_of_ok
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH65K_0480
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group060).1).1
end RH65K_0480

namespace RH65K_0481
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group060).2).1).1
end RH65K_0481

namespace RH65K_0482
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group060).2).2).1).1
end RH65K_0482

namespace RH65K_0483
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group060).2).2).2).1).1
end RH65K_0483

namespace RH65K_0484
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group060).2).2).2).2).1).1
end RH65K_0484

namespace RH65K_0485
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group060).2).2).2).2).2).1).1
end RH65K_0485

namespace RH65K_0486
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group060).2).2).2).2).2).2).1).1
end RH65K_0486

namespace RH65K_0487
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group060).2).2).2).2).2).2).2).1
end RH65K_0487

namespace RH65K_0488
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group061).1).1
end RH65K_0488

namespace RH65K_0489
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group061).2).1).1
end RH65K_0489

namespace RH65K_0490
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group061).2).2).1).1
end RH65K_0490

namespace RH65K_0491
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group061).2).2).2).1).1
end RH65K_0491

namespace RH65K_0492
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group061).2).2).2).2).1).1
end RH65K_0492

namespace RH65K_0493
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group061).2).2).2).2).2).1).1
end RH65K_0493

namespace RH65K_0494
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group061).2).2).2).2).2).2).1).1
end RH65K_0494

namespace RH65K_0495
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group061).2).2).2).2).2).2).2).1
end RH65K_0495

namespace RH65K_0496
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group062).1).1
end RH65K_0496

namespace RH65K_0497
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group062).2).1).1
end RH65K_0497

namespace RH65K_0498
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group062).2).2).1).1
end RH65K_0498

namespace RH65K_0499
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group062).2).2).2).1).1
end RH65K_0499

namespace RH65K_0500
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group062).2).2).2).2).1).1
end RH65K_0500

namespace RH65K_0501
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group062).2).2).2).2).2).1).1
end RH65K_0501

namespace RH65K_0502
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group062).2).2).2).2).2).2).1).1
end RH65K_0502

namespace RH65K_0503
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group062).2).2).2).2).2).2).2).1
end RH65K_0503

namespace RH65K_0504
theorem checked : RS5.bandOK' samples = true := ((TaoFivePrimes.arda_rh65k_arithmetic_group063).1).1
end RH65K_0504

namespace RH65K_0505
theorem checked : RS5.bandOK' samples = true := (((TaoFivePrimes.arda_rh65k_arithmetic_group063).2).1).1
end RH65K_0505

namespace RH65K_0506
theorem checked : RS5.bandOK' samples = true := ((((TaoFivePrimes.arda_rh65k_arithmetic_group063).2).2).1).1
end RH65K_0506

namespace RH65K_0507
theorem checked : RS5.bandOK' samples = true := (((((TaoFivePrimes.arda_rh65k_arithmetic_group063).2).2).2).1).1
end RH65K_0507

namespace RH65K_0508
theorem checked : RS5.bandOK' samples = true := ((((((TaoFivePrimes.arda_rh65k_arithmetic_group063).2).2).2).2).1).1
end RH65K_0508

namespace RH65K_0509
theorem checked : RS5.bandOK' samples = true := (((((((TaoFivePrimes.arda_rh65k_arithmetic_group063).2).2).2).2).2).1).1
end RH65K_0509

namespace RH65K_0510
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group063).2).2).2).2).2).2).1).1
end RH65K_0510

namespace RH65K_0511
theorem checked : RS5.bandOK' samples = true := ((((((((TaoFivePrimes.arda_rh65k_arithmetic_group063).2).2).2).2).2).2).2).1
end RH65K_0511

namespace H65K_PlatformHighBatch0480
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0480.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0480.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0480.samples = true
  exact RH65K_0480.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3676230740 : ℝ) / 65536) ((3681955794 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3676230740 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0480.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3681955794 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0480.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0480

namespace H65K_PlatformHighBatch0481
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0481.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0481.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0481.samples = true
  exact RH65K_0481.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3681955794 : ℝ) / 65536) ((3687698850 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3681955794 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0481.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3687698850 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0481.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0481

namespace H65K_PlatformHighBatch0482
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0482.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0482.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0482.samples = true
  exact RH65K_0482.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3687698850 : ℝ) / 65536) ((3693478146 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3687698850 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0482.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3693478146 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0482.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0482

namespace H65K_PlatformHighBatch0483
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0483.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0483.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0483.samples = true
  exact RH65K_0483.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3693478146 : ℝ) / 65536) ((3699204452 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3693478146 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0483.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3699204452 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0483.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0483

namespace H65K_PlatformHighBatch0484
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0484.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0484.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0484.samples = true
  exact RH65K_0484.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3699204452 : ℝ) / 65536) ((3704937431 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3699204452 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0484.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3704937431 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0484.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0484

namespace H65K_PlatformHighBatch0485
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0485.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0485.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0485.samples = true
  exact RH65K_0485.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3704937431 : ℝ) / 65536) ((3710705740 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3704937431 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0485.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3710705740 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0485.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0485

namespace H65K_PlatformHighBatch0486
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0486.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0486.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0486.samples = true
  exact RH65K_0486.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3710705740 : ℝ) / 65536) ((3716415511 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3710705740 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0486.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3716415511 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0486.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0486

namespace H65K_PlatformHighBatch0487
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0487.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0487.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0487.samples = true
  exact RH65K_0487.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3716415511 : ℝ) / 65536) ((3722167961 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3716415511 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0487.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3722167961 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0487.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0487

namespace H65K_PlatformHighBatch0488
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0488.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0488.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0488.samples = true
  exact RH65K_0488.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3722167961 : ℝ) / 65536) ((3727918050 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3722167961 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0488.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3727918050 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0488.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0488

namespace H65K_PlatformHighBatch0489
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0489.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0489.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0489.samples = true
  exact RH65K_0489.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3727918050 : ℝ) / 65536) ((3733656123 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3727918050 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0489.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3733656123 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0489.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0489

namespace H65K_PlatformHighBatch0490
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0490.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0490.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0490.samples = true
  exact RH65K_0490.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3733656123 : ℝ) / 65536) ((3739377824 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3733656123 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0490.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3739377824 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0490.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0490

namespace H65K_PlatformHighBatch0491
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0491.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0491.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0491.samples = true
  exact RH65K_0491.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3739377824 : ℝ) / 65536) ((3745144808 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3739377824 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0491.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3745144808 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0491.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0491

namespace H65K_PlatformHighBatch0492
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0492.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0492.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0492.samples = true
  exact RH65K_0492.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3745144808 : ℝ) / 65536) ((3750871348 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3745144808 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0492.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3750871348 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0492.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0492

namespace H65K_PlatformHighBatch0493
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0493.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0493.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0493.samples = true
  exact RH65K_0493.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3750871348 : ℝ) / 65536) ((3756590607 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3750871348 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0493.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3756590607 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0493.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0493

namespace H65K_PlatformHighBatch0494
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0494.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0494.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0494.samples = true
  exact RH65K_0494.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3756590607 : ℝ) / 65536) ((3762340170 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3756590607 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0494.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3762340170 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0494.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0494

namespace H65K_PlatformHighBatch0495
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0495.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0495.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0495.samples = true
  exact RH65K_0495.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3762340170 : ℝ) / 65536) ((3768062556 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3762340170 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0495.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3768062556 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0495.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0495

namespace H65K_PlatformHighBatch0496
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0496.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0496.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0496.samples = true
  exact RH65K_0496.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3768062556 : ℝ) / 65536) ((3773800825 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3768062556 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0496.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3773800825 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0496.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0496

namespace H65K_PlatformHighBatch0497
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0497.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0497.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0497.samples = true
  exact RH65K_0497.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3773800825 : ℝ) / 65536) ((3779534774 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3773800825 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0497.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3779534774 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0497.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0497

namespace H65K_PlatformHighBatch0498
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0498.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0498.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0498.samples = true
  exact RH65K_0498.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3779534774 : ℝ) / 65536) ((3785246893 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3779534774 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0498.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3785246893 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0498.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0498

namespace H65K_PlatformHighBatch0499
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0499.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0499.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0499.samples = true
  exact RH65K_0499.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3785246893 : ℝ) / 65536) ((3791011190 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3785246893 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0499.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3791011190 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0499.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0499

namespace H65K_PlatformHighBatch0500
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0500.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0500.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0500.samples = true
  exact RH65K_0500.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3791011190 : ℝ) / 65536) ((3796721575 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3791011190 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0500.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3796721575 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0500.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0500

namespace H65K_PlatformHighBatch0501
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0501.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0501.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0501.samples = true
  exact RH65K_0501.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3796721575 : ℝ) / 65536) ((3802433572 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3796721575 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0501.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3802433572 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0501.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0501

namespace H65K_PlatformHighBatch0502
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0502.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0502.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0502.samples = true
  exact RH65K_0502.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3802433572 : ℝ) / 65536) ((3808203283 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3802433572 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0502.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3808203283 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0502.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0502

namespace H65K_PlatformHighBatch0503
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0503.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0503.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0503.samples = true
  exact RH65K_0503.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3808203283 : ℝ) / 65536) ((3813902275 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3808203283 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0503.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3813902275 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0503.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0503

namespace H65K_PlatformHighBatch0504
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0504.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0504.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0504.samples = true
  exact RH65K_0504.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3813902275 : ℝ) / 65536) ((3819620359 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3813902275 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0504.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3819620359 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0504.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0504

namespace H65K_PlatformHighBatch0505
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0505.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0505.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0505.samples = true
  exact RH65K_0505.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3819620359 : ℝ) / 65536) ((3825370510 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3819620359 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0505.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3825370510 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0505.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0505

namespace H65K_PlatformHighBatch0506
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0506.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0506.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0506.samples = true
  exact RH65K_0506.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3825370510 : ℝ) / 65536) ((3831069506 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3825370510 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0506.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3831069506 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0506.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0506

namespace H65K_PlatformHighBatch0507
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0507.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0507.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0507.samples = true
  exact RH65K_0507.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3831069506 : ℝ) / 65536) ((3836801211 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3831069506 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0507.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3836801211 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0507.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0507

namespace H65K_PlatformHighBatch0508
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0508.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0508.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0508.samples = true
  exact RH65K_0508.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3836801211 : ℝ) / 65536) ((3842527849 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3836801211 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0508.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3842527849 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0508.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0508

namespace H65K_PlatformHighBatch0509
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0509.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0509.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0509.samples = true
  exact RH65K_0509.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3842527849 : ℝ) / 65536) ((3848232696 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3842527849 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0509.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3848232696 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0509.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0509

namespace H65K_PlatformHighBatch0510
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0510.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0510.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0510.samples = true
  exact RH65K_0510.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3848232696 : ℝ) / 65536) ((3853973413 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3848232696 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0510.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3853973413 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0510.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0510

namespace H65K_PlatformHighBatch0511
noncomputable def dummy : RS5.Sample := ⟨0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩
noncomputable def first : RS5.Sample := (RH65K_0511.samples.drop 0).getD 0 dummy
noncomputable def rest : List RS5.Sample := RH65K_0511.samples.drop 1
theorem inputOK : RS5.bandOK' (first :: rest) = true := by
  change RS5.bandOK' RH65K_0511.samples = true
  exact RH65K_0511.checked
theorem changes : RS5.chgBy RS5.Sample.pos (first :: rest) = 127 := by
  decide +kernel
theorem zeros : RS5.BandZeros ((3853973413 : ℝ) / 65536) ((3859677541 : ℝ) / 65536) 127 := by
  have hz := RS5.bandZeros_of_ok_prime first rest inputOK
  rw [changes] at hz
  have hlo : first.t = ((3853973413 : ℝ) / 65536) := by
    norm_num [first, dummy, RH65K_0511.samples, RS5.Sample.t]
  have hhi : (RS5.lastOf first rest).t = ((3859677541 : ℝ) / 65536) := by
    norm_num [first, rest, dummy, RH65K_0511.samples, RS5.lastOf, RS5.Sample.t]
  rw [hlo, hhi] at hz
  exact hz
end H65K_PlatformHighBatch0511

theorem solution : RS5.BandZeros ((3676230740 : ℝ) / 65536) ((3859677541 : ℝ) / 65536) 4064 := by
  have h0 := H65K_PlatformHighBatch0480.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0481.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0482.zeros
  have h3 := h2.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0483.zeros
  have h4 := h3.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0484.zeros
  have h5 := h4.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0485.zeros
  have h6 := h5.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0486.zeros
  have h7 := h6.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0487.zeros
  have h8 := h7.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0488.zeros
  have h9 := h8.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0489.zeros
  have h10 := h9.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0490.zeros
  have h11 := h10.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0491.zeros
  have h12 := h11.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0492.zeros
  have h13 := h12.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0493.zeros
  have h14 := h13.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0494.zeros
  have h15 := h14.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0495.zeros
  have h16 := h15.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0496.zeros
  have h17 := h16.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0497.zeros
  have h18 := h17.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0498.zeros
  have h19 := h18.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0499.zeros
  have h20 := h19.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0500.zeros
  have h21 := h20.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0501.zeros
  have h22 := h21.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0502.zeros
  have h23 := h22.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0503.zeros
  have h24 := h23.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0504.zeros
  have h25 := h24.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0505.zeros
  have h26 := h25.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0506.zeros
  have h27 := h26.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0507.zeros
  have h28 := h27.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0508.zeros
  have h29 := h28.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0509.zeros
  have h30 := h29.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0510.zeros
  have h31 := h30.glue (by norm_num) (by norm_num) H65K_PlatformHighBatch0511.zeros
  exact h31
