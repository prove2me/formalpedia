-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:20:12.173002+00:00
-- url     : https://prove2.me/submissions/081f1fcc-4263-40bf-9a15-e14060181c5d

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData0
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneB0A2PartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_row_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_row_2
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_row_4
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_row_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_row_8
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_band_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_band_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_band_12
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_band_18
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b0a2_band_24
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows0To1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 0–1

This file checks rows 0 through 1 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B0A2Row0_eq :
    remainder7Coefficient0NormalizedBlock0 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row0 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_0.1








































theorem recurrence6B0A2Row1_eq :
    remainder7Coefficient0NormalizedBlock1 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row1 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_0.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows2To3. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 2–3

This file checks rows 2 through 3 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B0A2Row2_eq :
    remainder7Coefficient0NormalizedBlock2 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row2 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_2.1








































theorem recurrence6B0A2Row3_eq :
    remainder7Coefficient0NormalizedBlock3 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row3 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows4To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 4–5

This file checks rows 4 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B0A2Row4_eq :
    remainder7Coefficient0NormalizedBlock4 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row4 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_4.1








































theorem recurrence6B0A2Row5_eq :
    remainder7Coefficient0NormalizedBlock5 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row5 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_4.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands0To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B0A2Band0_eq :
    recurrence6B0A2Band0 = remainder7Coefficient0TimesRemainder6Coefficient2Block0 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_0.1




theorem recurrence6B0A2Band1_eq :
    recurrence6B0A2Band1 = remainder7Coefficient0TimesRemainder6Coefficient2Block1 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_0.2.1




theorem recurrence6B0A2Band2_eq :
    recurrence6B0A2Band2 = remainder7Coefficient0TimesRemainder6Coefficient2Block2 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_0.2.2.1




theorem recurrence6B0A2Band3_eq :
    recurrence6B0A2Band3 = remainder7Coefficient0TimesRemainder6Coefficient2Block3 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_0.2.2.2.1




theorem recurrence6B0A2Band4_eq :
    recurrence6B0A2Band4 = remainder7Coefficient0TimesRemainder6Coefficient2Block4 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_0.2.2.2.2.1




theorem recurrence6B0A2Band5_eq :
    recurrence6B0A2Band5 = remainder7Coefficient0TimesRemainder6Coefficient2Block5 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_0.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows6To7. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 6–7

This file checks rows 6 through 7 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B0A2Row6_eq :
    remainder7Coefficient0NormalizedBlock6 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row6 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_6.1








































theorem recurrence6B0A2Row7_eq :
    remainder7Coefficient0NormalizedBlock7 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row7 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_6.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows8To9. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 8–9

This file checks rows 8 through 9 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B0A2Row8_eq :
    remainder7Coefficient0NormalizedBlock8 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row8 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_8.1






































theorem recurrence6B0A2Row9_eq :
    remainder7Coefficient0NormalizedBlock9 * remainder6Coefficient2Normalized =
      recurrence6B0A2Row9 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_row_8.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands6To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B0A2Band6_eq :
    recurrence6B0A2Band6 = remainder7Coefficient0TimesRemainder6Coefficient2Block6 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_6.1




theorem recurrence6B0A2Band7_eq :
    recurrence6B0A2Band7 = remainder7Coefficient0TimesRemainder6Coefficient2Block7 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_6.2.1




theorem recurrence6B0A2Band8_eq :
    recurrence6B0A2Band8 = remainder7Coefficient0TimesRemainder6Coefficient2Block8 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_6.2.2.1




theorem recurrence6B0A2Band9_eq :
    recurrence6B0A2Band9 = remainder7Coefficient0TimesRemainder6Coefficient2Block9 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_6.2.2.2.1




theorem recurrence6B0A2Band10_eq :
    recurrence6B0A2Band10 = remainder7Coefficient0TimesRemainder6Coefficient2Block10 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_6.2.2.2.2.1




theorem recurrence6B0A2Band11_eq :
    recurrence6B0A2Band11 = remainder7Coefficient0TimesRemainder6Coefficient2Block11 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_6.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands12To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 12–17

This file checks bands 12 through 17 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B0A2Band12_eq :
    recurrence6B0A2Band12 = remainder7Coefficient0TimesRemainder6Coefficient2Block12 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_12.1




theorem recurrence6B0A2Band13_eq :
    recurrence6B0A2Band13 = remainder7Coefficient0TimesRemainder6Coefficient2Block13 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_12.2.1




theorem recurrence6B0A2Band14_eq :
    recurrence6B0A2Band14 = remainder7Coefficient0TimesRemainder6Coefficient2Block14 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_12.2.2.1




theorem recurrence6B0A2Band15_eq :
    recurrence6B0A2Band15 = remainder7Coefficient0TimesRemainder6Coefficient2Block15 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_12.2.2.2.1




theorem recurrence6B0A2Band16_eq :
    recurrence6B0A2Band16 = remainder7Coefficient0TimesRemainder6Coefficient2Block16 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_12.2.2.2.2.1




theorem recurrence6B0A2Band17_eq :
    recurrence6B0A2Band17 = remainder7Coefficient0TimesRemainder6Coefficient2Block17 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_12.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands18To23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B0A2Band18_eq :
    recurrence6B0A2Band18 = remainder7Coefficient0TimesRemainder6Coefficient2Block18 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_18.1




theorem recurrence6B0A2Band19_eq :
    recurrence6B0A2Band19 = remainder7Coefficient0TimesRemainder6Coefficient2Block19 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_18.2.1




theorem recurrence6B0A2Band20_eq :
    recurrence6B0A2Band20 = remainder7Coefficient0TimesRemainder6Coefficient2Block20 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_18.2.2.1




theorem recurrence6B0A2Band21_eq :
    recurrence6B0A2Band21 = remainder7Coefficient0TimesRemainder6Coefficient2Block21 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_18.2.2.2.1




theorem recurrence6B0A2Band22_eq :
    recurrence6B0A2Band22 = remainder7Coefficient0TimesRemainder6Coefficient2Block22 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_18.2.2.2.2.1




theorem recurrence6B0A2Band23_eq :
    recurrence6B0A2Band23 = remainder7Coefficient0TimesRemainder6Coefficient2Block23 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_18.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands24To25. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 24–25

This file checks bands 24 through 25 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B0A2Band24_eq :
    recurrence6B0A2Band24 = remainder7Coefficient0TimesRemainder6Coefficient2Block24 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_24.1




theorem recurrence6B0A2Band25_eq :
    recurrence6B0A2Band25 = remainder7Coefficient0TimesRemainder6Coefficient2Block25 := by
  exact MazurTransfer.order49_resultant_recurrence6_b0a2_band_24.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: B0A2

This compatibility module combines independently checked row and band
shards for the recurrence-6 B0A2 arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





theorem remainder7Coefficient0TimesRemainder6Coefficient2_eq :
    remainder7Coefficient0Normalized * remainder6Coefficient2Normalized =
      remainder7Coefficient0TimesRemainder6Coefficient2 := by
  have rows :
      remainder7Coefficient0Normalized * remainder6Coefficient2Normalized =
        recurrence6B0A2Rows := by
    unfold remainder7Coefficient0Normalized recurrence6B0A2Rows
    rw [← recurrence6B0A2Row0_eq]
    rw [← recurrence6B0A2Row1_eq]
    rw [← recurrence6B0A2Row2_eq]
    rw [← recurrence6B0A2Row3_eq]
    rw [← recurrence6B0A2Row4_eq]
    rw [← recurrence6B0A2Row5_eq]
    rw [← recurrence6B0A2Row6_eq]
    rw [← recurrence6B0A2Row7_eq]
    rw [← recurrence6B0A2Row8_eq]
    rw [← recurrence6B0A2Row9_eq]
    unfold remainder6Coefficient2Normalized
    ring
  rw [rows]
  have rearrange : recurrence6B0A2Rows = recurrence6B0A2Bands := by
    unfold recurrence6B0A2Rows recurrence6B0A2Bands recurrence6B0A2Row0 recurrence6B0A2Row1
    unfold recurrence6B0A2Row2 recurrence6B0A2Row3 recurrence6B0A2Row4 recurrence6B0A2Row5
    unfold recurrence6B0A2Row6 recurrence6B0A2Row7 recurrence6B0A2Row8 recurrence6B0A2Row9
    unfold recurrence6B0A2Band0 recurrence6B0A2Band1 recurrence6B0A2Band2 recurrence6B0A2Band3
    unfold recurrence6B0A2Band4 recurrence6B0A2Band5 recurrence6B0A2Band6 recurrence6B0A2Band7
    unfold recurrence6B0A2Band8 recurrence6B0A2Band9 recurrence6B0A2Band10 recurrence6B0A2Band11
    unfold recurrence6B0A2Band12 recurrence6B0A2Band13 recurrence6B0A2Band14 recurrence6B0A2Band15
    unfold recurrence6B0A2Band16 recurrence6B0A2Band17 recurrence6B0A2Band18 recurrence6B0A2Band19
    unfold recurrence6B0A2Band20 recurrence6B0A2Band21 recurrence6B0A2Band22 recurrence6B0A2Band23
    unfold recurrence6B0A2Band24 recurrence6B0A2Band25
    ring
  rw [rearrange]
  unfold recurrence6B0A2Bands remainder7Coefficient0TimesRemainder6Coefficient2
  rw [recurrence6B0A2Band0_eq]
  rw [recurrence6B0A2Band1_eq]
  rw [recurrence6B0A2Band2_eq]
  rw [recurrence6B0A2Band3_eq]
  rw [recurrence6B0A2Band4_eq]
  rw [recurrence6B0A2Band5_eq]
  rw [recurrence6B0A2Band6_eq]
  rw [recurrence6B0A2Band7_eq]
  rw [recurrence6B0A2Band8_eq]
  rw [recurrence6B0A2Band9_eq]
  rw [recurrence6B0A2Band10_eq]
  rw [recurrence6B0A2Band11_eq]
  rw [recurrence6B0A2Band12_eq]
  rw [recurrence6B0A2Band13_eq]
  rw [recurrence6B0A2Band14_eq]
  rw [recurrence6B0A2Band15_eq]
  rw [recurrence6B0A2Band16_eq]
  rw [recurrence6B0A2Band17_eq]
  rw [recurrence6B0A2Band18_eq]
  rw [recurrence6B0A2Band19_eq]
  rw [recurrence6B0A2Band20_eq]
  rw [recurrence6B0A2Band21_eq]
  rw [recurrence6B0A2Band22_eq]
  rw [recurrence6B0A2Band23_eq]
  rw [recurrence6B0A2Band24_eq]
  rw [recurrence6B0A2Band25_eq]

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
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0Normalized * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2 := by
  exact MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2_eq
#print axioms solution
