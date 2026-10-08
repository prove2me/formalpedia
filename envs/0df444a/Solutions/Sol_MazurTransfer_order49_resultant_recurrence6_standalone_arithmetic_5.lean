-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:29:38.876884+00:00
-- url     : https://prove2.me/submissions/1e7dd7ec-6a62-4563-bc16-67ff99f02aca

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData2
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneA2SquarePartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_row_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_row_3
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_row_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_row_9
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_row_12
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_row_15
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_band_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_band_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_band_12
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_band_18
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_band_24
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_a2square_band_30
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows0To2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square rows 0–2

This file checks rows 0 through 2 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6A2SquareRow0_eq :
    remainder6Coefficient2NormalizedBlock0 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow0 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_0.1








































theorem recurrence6A2SquareRow1_eq :
    remainder6Coefficient2NormalizedBlock1 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow1 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_0.2.1








































theorem recurrence6A2SquareRow2_eq :
    remainder6Coefficient2NormalizedBlock2 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow2 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_0.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows3To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square rows 3–5

This file checks rows 3 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6A2SquareRow3_eq :
    remainder6Coefficient2NormalizedBlock3 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow3 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_3.1








































theorem recurrence6A2SquareRow4_eq :
    remainder6Coefficient2NormalizedBlock4 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow4 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_3.2.1








































theorem recurrence6A2SquareRow5_eq :
    remainder6Coefficient2NormalizedBlock5 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow5 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_3.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands0To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6A2SquareBand0_eq :
    recurrence6A2SquareBand0 = remainder6Coefficient2SquareBlock0 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_0.1




theorem recurrence6A2SquareBand1_eq :
    recurrence6A2SquareBand1 = remainder6Coefficient2SquareBlock1 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_0.2.1




theorem recurrence6A2SquareBand2_eq :
    recurrence6A2SquareBand2 = remainder6Coefficient2SquareBlock2 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_0.2.2.1




theorem recurrence6A2SquareBand3_eq :
    recurrence6A2SquareBand3 = remainder6Coefficient2SquareBlock3 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_0.2.2.2.1




theorem recurrence6A2SquareBand4_eq :
    recurrence6A2SquareBand4 = remainder6Coefficient2SquareBlock4 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_0.2.2.2.2.1




theorem recurrence6A2SquareBand5_eq :
    recurrence6A2SquareBand5 = remainder6Coefficient2SquareBlock5 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_0.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows6To8. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square rows 6–8

This file checks rows 6 through 8 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6A2SquareRow6_eq :
    remainder6Coefficient2NormalizedBlock6 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow6 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_6.1








































theorem recurrence6A2SquareRow7_eq :
    remainder6Coefficient2NormalizedBlock7 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow7 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_6.2.1








































theorem recurrence6A2SquareRow8_eq :
    remainder6Coefficient2NormalizedBlock8 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow8 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_6.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows9To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square rows 9–11

This file checks rows 9 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6A2SquareRow9_eq :
    remainder6Coefficient2NormalizedBlock9 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow9 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_9.1








































theorem recurrence6A2SquareRow10_eq :
    remainder6Coefficient2NormalizedBlock10 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow10 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_9.2.1








































theorem recurrence6A2SquareRow11_eq :
    remainder6Coefficient2NormalizedBlock11 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow11 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_9.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands6To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6A2SquareBand6_eq :
    recurrence6A2SquareBand6 = remainder6Coefficient2SquareBlock6 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_6.1




theorem recurrence6A2SquareBand7_eq :
    recurrence6A2SquareBand7 = remainder6Coefficient2SquareBlock7 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_6.2.1




theorem recurrence6A2SquareBand8_eq :
    recurrence6A2SquareBand8 = remainder6Coefficient2SquareBlock8 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_6.2.2.1




theorem recurrence6A2SquareBand9_eq :
    recurrence6A2SquareBand9 = remainder6Coefficient2SquareBlock9 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_6.2.2.2.1




theorem recurrence6A2SquareBand10_eq :
    recurrence6A2SquareBand10 = remainder6Coefficient2SquareBlock10 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_6.2.2.2.2.1




theorem recurrence6A2SquareBand11_eq :
    recurrence6A2SquareBand11 = remainder6Coefficient2SquareBlock11 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_6.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows12To14. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square rows 12–14

This file checks rows 12 through 14 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6A2SquareRow12_eq :
    remainder6Coefficient2NormalizedBlock12 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow12 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_12.1








































theorem recurrence6A2SquareRow13_eq :
    remainder6Coefficient2NormalizedBlock13 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow13 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_12.2.1








































theorem recurrence6A2SquareRow14_eq :
    remainder6Coefficient2NormalizedBlock14 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow14 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_12.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Rows15To16. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square rows 15–16

This file checks rows 15 through 16 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6A2SquareRow15_eq :
    remainder6Coefficient2NormalizedBlock15 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow15 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_15.1






































theorem recurrence6A2SquareRow16_eq :
    remainder6Coefficient2NormalizedBlock16 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow16 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_row_15.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands12To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square bands 12–17

This file checks bands 12 through 17 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6A2SquareBand12_eq :
    recurrence6A2SquareBand12 = remainder6Coefficient2SquareBlock12 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_12.1




theorem recurrence6A2SquareBand13_eq :
    recurrence6A2SquareBand13 = remainder6Coefficient2SquareBlock13 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_12.2.1




theorem recurrence6A2SquareBand14_eq :
    recurrence6A2SquareBand14 = remainder6Coefficient2SquareBlock14 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_12.2.2.1




theorem recurrence6A2SquareBand15_eq :
    recurrence6A2SquareBand15 = remainder6Coefficient2SquareBlock15 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_12.2.2.2.1




theorem recurrence6A2SquareBand16_eq :
    recurrence6A2SquareBand16 = remainder6Coefficient2SquareBlock16 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_12.2.2.2.2.1




theorem recurrence6A2SquareBand17_eq :
    recurrence6A2SquareBand17 = remainder6Coefficient2SquareBlock17 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_12.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands18To23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6A2SquareBand18_eq :
    recurrence6A2SquareBand18 = remainder6Coefficient2SquareBlock18 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_18.1




theorem recurrence6A2SquareBand19_eq :
    recurrence6A2SquareBand19 = remainder6Coefficient2SquareBlock19 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_18.2.1




theorem recurrence6A2SquareBand20_eq :
    recurrence6A2SquareBand20 = remainder6Coefficient2SquareBlock20 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_18.2.2.1




theorem recurrence6A2SquareBand21_eq :
    recurrence6A2SquareBand21 = remainder6Coefficient2SquareBlock21 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_18.2.2.2.1




theorem recurrence6A2SquareBand22_eq :
    recurrence6A2SquareBand22 = remainder6Coefficient2SquareBlock22 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_18.2.2.2.2.1




theorem recurrence6A2SquareBand23_eq :
    recurrence6A2SquareBand23 = remainder6Coefficient2SquareBlock23 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_18.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands24To29. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square bands 24–29

This file checks bands 24 through 29 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6A2SquareBand24_eq :
    recurrence6A2SquareBand24 = remainder6Coefficient2SquareBlock24 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_24.1




theorem recurrence6A2SquareBand25_eq :
    recurrence6A2SquareBand25 = remainder6Coefficient2SquareBlock25 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_24.2.1




theorem recurrence6A2SquareBand26_eq :
    recurrence6A2SquareBand26 = remainder6Coefficient2SquareBlock26 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_24.2.2.1




theorem recurrence6A2SquareBand27_eq :
    recurrence6A2SquareBand27 = remainder6Coefficient2SquareBlock27 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_24.2.2.2.1




theorem recurrence6A2SquareBand28_eq :
    recurrence6A2SquareBand28 = remainder6Coefficient2SquareBlock28 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_24.2.2.2.2.1




theorem recurrence6A2SquareBand29_eq :
    recurrence6A2SquareBand29 = remainder6Coefficient2SquareBlock29 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_24.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square.Bands30To32. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 A2Square bands 30–32

This file checks bands 30 through 32 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6A2SquareBand30_eq :
    recurrence6A2SquareBand30 = remainder6Coefficient2SquareBlock30 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_30.1




theorem recurrence6A2SquareBand31_eq :
    recurrence6A2SquareBand31 = remainder6Coefficient2SquareBlock31 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_30.2.1




theorem recurrence6A2SquareBand32_eq :
    recurrence6A2SquareBand32 = remainder6Coefficient2SquareBlock32 := by
  exact MazurTransfer.order49_resultant_recurrence6_a2square_band_30.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6A2Square. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: A2Square

This compatibility module combines independently checked row and band
shards for the recurrence-6 A2Square arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





theorem remainder6Coefficient2Square_eq :
    remainder6Coefficient2Normalized * remainder6Coefficient2Normalized =
      remainder6Coefficient2Square := by
  have rows :
      remainder6Coefficient2Normalized * remainder6Coefficient2Normalized =
        recurrence6A2SquareRows := by
    unfold remainder6Coefficient2Normalized recurrence6A2SquareRows
    rw [← recurrence6A2SquareRow0_eq]
    rw [← recurrence6A2SquareRow1_eq]
    rw [← recurrence6A2SquareRow2_eq]
    rw [← recurrence6A2SquareRow3_eq]
    rw [← recurrence6A2SquareRow4_eq]
    rw [← recurrence6A2SquareRow5_eq]
    rw [← recurrence6A2SquareRow6_eq]
    rw [← recurrence6A2SquareRow7_eq]
    rw [← recurrence6A2SquareRow8_eq]
    rw [← recurrence6A2SquareRow9_eq]
    rw [← recurrence6A2SquareRow10_eq]
    rw [← recurrence6A2SquareRow11_eq]
    rw [← recurrence6A2SquareRow12_eq]
    rw [← recurrence6A2SquareRow13_eq]
    rw [← recurrence6A2SquareRow14_eq]
    rw [← recurrence6A2SquareRow15_eq]
    rw [← recurrence6A2SquareRow16_eq]
    unfold remainder6Coefficient2Normalized
    ring
  rw [rows]
  have rearrange : recurrence6A2SquareRows = recurrence6A2SquareBands := by
    unfold recurrence6A2SquareRows recurrence6A2SquareBands recurrence6A2SquareRow0
    unfold recurrence6A2SquareRow1 recurrence6A2SquareRow2 recurrence6A2SquareRow3
    unfold recurrence6A2SquareRow4 recurrence6A2SquareRow5 recurrence6A2SquareRow6
    unfold recurrence6A2SquareRow7 recurrence6A2SquareRow8 recurrence6A2SquareRow9
    unfold recurrence6A2SquareRow10 recurrence6A2SquareRow11 recurrence6A2SquareRow12
    unfold recurrence6A2SquareRow13 recurrence6A2SquareRow14 recurrence6A2SquareRow15
    unfold recurrence6A2SquareRow16 recurrence6A2SquareBand0 recurrence6A2SquareBand1
    unfold recurrence6A2SquareBand2 recurrence6A2SquareBand3 recurrence6A2SquareBand4
    unfold recurrence6A2SquareBand5 recurrence6A2SquareBand6 recurrence6A2SquareBand7
    unfold recurrence6A2SquareBand8 recurrence6A2SquareBand9 recurrence6A2SquareBand10
    unfold recurrence6A2SquareBand11 recurrence6A2SquareBand12 recurrence6A2SquareBand13
    unfold recurrence6A2SquareBand14 recurrence6A2SquareBand15 recurrence6A2SquareBand16
    unfold recurrence6A2SquareBand17 recurrence6A2SquareBand18 recurrence6A2SquareBand19
    unfold recurrence6A2SquareBand20 recurrence6A2SquareBand21 recurrence6A2SquareBand22
    unfold recurrence6A2SquareBand23 recurrence6A2SquareBand24 recurrence6A2SquareBand25
    unfold recurrence6A2SquareBand26 recurrence6A2SquareBand27 recurrence6A2SquareBand28
    unfold recurrence6A2SquareBand29 recurrence6A2SquareBand30 recurrence6A2SquareBand31
    unfold recurrence6A2SquareBand32
    ring
  rw [rearrange]
  unfold recurrence6A2SquareBands remainder6Coefficient2Square
  rw [recurrence6A2SquareBand0_eq]
  rw [recurrence6A2SquareBand1_eq]
  rw [recurrence6A2SquareBand2_eq]
  rw [recurrence6A2SquareBand3_eq]
  rw [recurrence6A2SquareBand4_eq]
  rw [recurrence6A2SquareBand5_eq]
  rw [recurrence6A2SquareBand6_eq]
  rw [recurrence6A2SquareBand7_eq]
  rw [recurrence6A2SquareBand8_eq]
  rw [recurrence6A2SquareBand9_eq]
  rw [recurrence6A2SquareBand10_eq]
  rw [recurrence6A2SquareBand11_eq]
  rw [recurrence6A2SquareBand12_eq]
  rw [recurrence6A2SquareBand13_eq]
  rw [recurrence6A2SquareBand14_eq]
  rw [recurrence6A2SquareBand15_eq]
  rw [recurrence6A2SquareBand16_eq]
  rw [recurrence6A2SquareBand17_eq]
  rw [recurrence6A2SquareBand18_eq]
  rw [recurrence6A2SquareBand19_eq]
  rw [recurrence6A2SquareBand20_eq]
  rw [recurrence6A2SquareBand21_eq]
  rw [recurrence6A2SquareBand22_eq]
  rw [recurrence6A2SquareBand23_eq]
  rw [recurrence6A2SquareBand24_eq]
  rw [recurrence6A2SquareBand25_eq]
  rw [recurrence6A2SquareBand26_eq]
  rw [recurrence6A2SquareBand27_eq]
  rw [recurrence6A2SquareBand28_eq]
  rw [recurrence6A2SquareBand29_eq]
  rw [recurrence6A2SquareBand30_eq]
  rw [recurrence6A2SquareBand31_eq]
  rw [recurrence6A2SquareBand32_eq]

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
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Square := by
  exact MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Square_eq
#print axioms solution
