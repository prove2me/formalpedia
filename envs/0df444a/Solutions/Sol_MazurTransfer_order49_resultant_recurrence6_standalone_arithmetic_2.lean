-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:50:05.465945+00:00
-- url     : https://prove2.me/submissions/3f8836d6-067d-4dd8-92ae-546b0e1a5298

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData3
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData5
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneTerm2PartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_row_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_row_2
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_row_4
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_row_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_row_8
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_band_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_band_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_band_12
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_band_18
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_band_24
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_band_30
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows0To1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 rows 0–1

This file checks rows 0 through 1 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

























































theorem recurrence6Term2Row0_eq :
    remainder7Coefficient0NormalizedBlock0 * normalizedResidual6Inner =
      recurrence6Term2Row0 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_0.1


























































theorem recurrence6Term2Row1_eq :
    remainder7Coefficient0NormalizedBlock1 * normalizedResidual6Inner =
      recurrence6Term2Row1 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_0.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows2To3. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 rows 2–3

This file checks rows 2 through 3 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

























































theorem recurrence6Term2Row2_eq :
    remainder7Coefficient0NormalizedBlock2 * normalizedResidual6Inner =
      recurrence6Term2Row2 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_2.1


























































theorem recurrence6Term2Row3_eq :
    remainder7Coefficient0NormalizedBlock3 * normalizedResidual6Inner =
      recurrence6Term2Row3 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows4To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 rows 4–5

This file checks rows 4 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

























































theorem recurrence6Term2Row4_eq :
    remainder7Coefficient0NormalizedBlock4 * normalizedResidual6Inner =
      recurrence6Term2Row4 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_4.1


























































theorem recurrence6Term2Row5_eq :
    remainder7Coefficient0NormalizedBlock5 * normalizedResidual6Inner =
      recurrence6Term2Row5 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_4.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands0To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term2Band0_eq :
    recurrence6Term2Band0 = normalizedResidual6Term2Block0 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_0.1




theorem recurrence6Term2Band1_eq :
    recurrence6Term2Band1 = normalizedResidual6Term2Block1 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_0.2.1




theorem recurrence6Term2Band2_eq :
    recurrence6Term2Band2 = normalizedResidual6Term2Block2 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_0.2.2.1




theorem recurrence6Term2Band3_eq :
    recurrence6Term2Band3 = normalizedResidual6Term2Block3 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_0.2.2.2.1




theorem recurrence6Term2Band4_eq :
    recurrence6Term2Band4 = normalizedResidual6Term2Block4 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_0.2.2.2.2.1




theorem recurrence6Term2Band5_eq :
    recurrence6Term2Band5 = normalizedResidual6Term2Block5 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_0.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows6To7. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 rows 6–7

This file checks rows 6 through 7 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

























































theorem recurrence6Term2Row6_eq :
    remainder7Coefficient0NormalizedBlock6 * normalizedResidual6Inner =
      recurrence6Term2Row6 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_6.1


























































theorem recurrence6Term2Row7_eq :
    remainder7Coefficient0NormalizedBlock7 * normalizedResidual6Inner =
      recurrence6Term2Row7 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_6.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Rows8To9. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 rows 8–9

This file checks rows 8 through 9 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

























































theorem recurrence6Term2Row8_eq :
    remainder7Coefficient0NormalizedBlock8 * normalizedResidual6Inner =
      recurrence6Term2Row8 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_8.1


























































theorem recurrence6Term2Row9_eq :
    remainder7Coefficient0NormalizedBlock9 * normalizedResidual6Inner =
      recurrence6Term2Row9 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_row_8.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands6To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term2Band6_eq :
    recurrence6Term2Band6 = normalizedResidual6Term2Block6 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_6.1




theorem recurrence6Term2Band7_eq :
    recurrence6Term2Band7 = normalizedResidual6Term2Block7 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_6.2.1




theorem recurrence6Term2Band8_eq :
    recurrence6Term2Band8 = normalizedResidual6Term2Block8 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_6.2.2.1




theorem recurrence6Term2Band9_eq :
    recurrence6Term2Band9 = normalizedResidual6Term2Block9 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_6.2.2.2.1




theorem recurrence6Term2Band10_eq :
    recurrence6Term2Band10 = normalizedResidual6Term2Block10 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_6.2.2.2.2.1




theorem recurrence6Term2Band11_eq :
    recurrence6Term2Band11 = normalizedResidual6Term2Block11 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_6.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands12To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 bands 12–17

This file checks bands 12 through 17 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term2Band12_eq :
    recurrence6Term2Band12 = normalizedResidual6Term2Block12 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_12.1




theorem recurrence6Term2Band13_eq :
    recurrence6Term2Band13 = normalizedResidual6Term2Block13 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_12.2.1




theorem recurrence6Term2Band14_eq :
    recurrence6Term2Band14 = normalizedResidual6Term2Block14 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_12.2.2.1




theorem recurrence6Term2Band15_eq :
    recurrence6Term2Band15 = normalizedResidual6Term2Block15 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_12.2.2.2.1




theorem recurrence6Term2Band16_eq :
    recurrence6Term2Band16 = normalizedResidual6Term2Block16 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_12.2.2.2.2.1




theorem recurrence6Term2Band17_eq :
    recurrence6Term2Band17 = normalizedResidual6Term2Block17 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_12.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands18To23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term2Band18_eq :
    recurrence6Term2Band18 = normalizedResidual6Term2Block18 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_18.1




theorem recurrence6Term2Band19_eq :
    recurrence6Term2Band19 = normalizedResidual6Term2Block19 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_18.2.1




theorem recurrence6Term2Band20_eq :
    recurrence6Term2Band20 = normalizedResidual6Term2Block20 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_18.2.2.1




theorem recurrence6Term2Band21_eq :
    recurrence6Term2Band21 = normalizedResidual6Term2Block21 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_18.2.2.2.1




theorem recurrence6Term2Band22_eq :
    recurrence6Term2Band22 = normalizedResidual6Term2Block22 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_18.2.2.2.2.1




theorem recurrence6Term2Band23_eq :
    recurrence6Term2Band23 = normalizedResidual6Term2Block23 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_18.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands24To29. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 bands 24–29

This file checks bands 24 through 29 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term2Band24_eq :
    recurrence6Term2Band24 = normalizedResidual6Term2Block24 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_24.1




theorem recurrence6Term2Band25_eq :
    recurrence6Term2Band25 = normalizedResidual6Term2Block25 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_24.2.1




theorem recurrence6Term2Band26_eq :
    recurrence6Term2Band26 = normalizedResidual6Term2Block26 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_24.2.2.1




theorem recurrence6Term2Band27_eq :
    recurrence6Term2Band27 = normalizedResidual6Term2Block27 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_24.2.2.2.1




theorem recurrence6Term2Band28_eq :
    recurrence6Term2Band28 = normalizedResidual6Term2Block28 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_24.2.2.2.2.1




theorem recurrence6Term2Band29_eq :
    recurrence6Term2Band29 = normalizedResidual6Term2Block29 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_24.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2.Bands30To35. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term2 bands 30–35

This file checks bands 30 through 35 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term2Band30_eq :
    recurrence6Term2Band30 = normalizedResidual6Term2Block30 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_30.1




theorem recurrence6Term2Band31_eq :
    recurrence6Term2Band31 = normalizedResidual6Term2Block31 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_30.2.1




theorem recurrence6Term2Band32_eq :
    recurrence6Term2Band32 = normalizedResidual6Term2Block32 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_30.2.2.1




theorem recurrence6Term2Band33_eq :
    recurrence6Term2Band33 = normalizedResidual6Term2Block33 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_30.2.2.2.1




theorem recurrence6Term2Band34_eq :
    recurrence6Term2Band34 = normalizedResidual6Term2Block34 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_30.2.2.2.2.1




theorem recurrence6Term2Band35_eq :
    recurrence6Term2Band35 = normalizedResidual6Term2Block35 := by
  exact MazurTransfer.order49_resultant_recurrence6_term2_band_30.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: Term2

This compatibility module combines independently checked row and band
shards for the recurrence-6 Term2 arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





theorem normalizedResidual6Term2_eq :
    remainder7Coefficient0Normalized * normalizedResidual6Inner =
      normalizedResidual6Term2 := by
  have rows :
      remainder7Coefficient0Normalized * normalizedResidual6Inner =
        recurrence6Term2Rows := by
    unfold remainder7Coefficient0Normalized recurrence6Term2Rows
    rw [← recurrence6Term2Row0_eq]
    rw [← recurrence6Term2Row1_eq]
    rw [← recurrence6Term2Row2_eq]
    rw [← recurrence6Term2Row3_eq]
    rw [← recurrence6Term2Row4_eq]
    rw [← recurrence6Term2Row5_eq]
    rw [← recurrence6Term2Row6_eq]
    rw [← recurrence6Term2Row7_eq]
    rw [← recurrence6Term2Row8_eq]
    rw [← recurrence6Term2Row9_eq]
    unfold normalizedResidual6Inner
    ring
  rw [rows]
  have rearrange : recurrence6Term2Rows = recurrence6Term2Bands := by
    unfold recurrence6Term2Rows recurrence6Term2Bands recurrence6Term2Row0 recurrence6Term2Row1
    unfold recurrence6Term2Row2 recurrence6Term2Row3 recurrence6Term2Row4 recurrence6Term2Row5
    unfold recurrence6Term2Row6 recurrence6Term2Row7 recurrence6Term2Row8 recurrence6Term2Row9
    unfold recurrence6Term2Band0 recurrence6Term2Band1 recurrence6Term2Band2 recurrence6Term2Band3
    unfold recurrence6Term2Band4 recurrence6Term2Band5 recurrence6Term2Band6 recurrence6Term2Band7
    unfold recurrence6Term2Band8 recurrence6Term2Band9 recurrence6Term2Band10 recurrence6Term2Band11
    unfold recurrence6Term2Band12 recurrence6Term2Band13 recurrence6Term2Band14
    unfold recurrence6Term2Band15 recurrence6Term2Band16 recurrence6Term2Band17
    unfold recurrence6Term2Band18 recurrence6Term2Band19 recurrence6Term2Band20
    unfold recurrence6Term2Band21 recurrence6Term2Band22 recurrence6Term2Band23
    unfold recurrence6Term2Band24 recurrence6Term2Band25 recurrence6Term2Band26
    unfold recurrence6Term2Band27 recurrence6Term2Band28 recurrence6Term2Band29
    unfold recurrence6Term2Band30 recurrence6Term2Band31 recurrence6Term2Band32
    unfold recurrence6Term2Band33 recurrence6Term2Band34 recurrence6Term2Band35
    ring
  rw [rearrange]
  unfold recurrence6Term2Bands normalizedResidual6Term2
  rw [recurrence6Term2Band0_eq]
  rw [recurrence6Term2Band1_eq]
  rw [recurrence6Term2Band2_eq]
  rw [recurrence6Term2Band3_eq]
  rw [recurrence6Term2Band4_eq]
  rw [recurrence6Term2Band5_eq]
  rw [recurrence6Term2Band6_eq]
  rw [recurrence6Term2Band7_eq]
  rw [recurrence6Term2Band8_eq]
  rw [recurrence6Term2Band9_eq]
  rw [recurrence6Term2Band10_eq]
  rw [recurrence6Term2Band11_eq]
  rw [recurrence6Term2Band12_eq]
  rw [recurrence6Term2Band13_eq]
  rw [recurrence6Term2Band14_eq]
  rw [recurrence6Term2Band15_eq]
  rw [recurrence6Term2Band16_eq]
  rw [recurrence6Term2Band17_eq]
  rw [recurrence6Term2Band18_eq]
  rw [recurrence6Term2Band19_eq]
  rw [recurrence6Term2Band20_eq]
  rw [recurrence6Term2Band21_eq]
  rw [recurrence6Term2Band22_eq]
  rw [recurrence6Term2Band23_eq]
  rw [recurrence6Term2Band24_eq]
  rw [recurrence6Term2Band25_eq]
  rw [recurrence6Term2Band26_eq]
  rw [recurrence6Term2Band27_eq]
  rw [recurrence6Term2Band28_eq]
  rw [recurrence6Term2Band29_eq]
  rw [recurrence6Term2Band30_eq]
  rw [recurrence6Term2Band31_eq]
  rw [recurrence6Term2Band32_eq]
  rw [recurrence6Term2Band33_eq]
  rw [recurrence6Term2Band34_eq]
  rw [recurrence6Term2Band35_eq]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

open Polynomial
open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate


end MazurTransfer.Order49Standalone
open Polynomial
open MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
theorem solution :
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0Normalized * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Inner =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term2 := by
  exact MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term2_eq
#print axioms solution
