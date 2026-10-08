-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:21:01.472671+00:00
-- url     : https://prove2.me/submissions/fbc1832d-1a0e-4aed-8f9b-d7f15c0f6350
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneTerm1PartitionData
import Mathlib.Tactic.Ring
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_row_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_row_3
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_row_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_row_9
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_row_12
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_row_15
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_band_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_band_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_band_12
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_band_18
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_band_24
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term1_band_30
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows0To2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 rows 0–2

This file checks an independent group of row identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section






















theorem recurrence6Term1Row0_eq :
    remainder6Coefficient0NormalizedBlock0 * remainder7Coefficient1Square =
      recurrence6Term1Row0 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_0.1






















theorem recurrence6Term1Row1_eq :
    remainder6Coefficient0NormalizedBlock1 * remainder7Coefficient1Square =
      recurrence6Term1Row1 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_0.2.1


































theorem recurrence6Term1Row2_eq :
    remainder6Coefficient0NormalizedBlock2 * remainder7Coefficient1Square =
      recurrence6Term1Row2 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_0.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows3To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 rows 3–5

This file checks an independent group of row identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section











































theorem recurrence6Term1Row3_eq :
    remainder6Coefficient0NormalizedBlock3 * remainder7Coefficient1Square =
      recurrence6Term1Row3 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_3.1












































theorem recurrence6Term1Row4_eq :
    remainder6Coefficient0NormalizedBlock4 * remainder7Coefficient1Square =
      recurrence6Term1Row4 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_3.2.1












































theorem recurrence6Term1Row5_eq :
    remainder6Coefficient0NormalizedBlock5 * remainder7Coefficient1Square =
      recurrence6Term1Row5 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_3.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands0To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 bands 0–5

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term1Band0_eq :
    recurrence6Term1Band0 = normalizedResidual6Term1Block0 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_0.1




theorem recurrence6Term1Band1_eq :
    recurrence6Term1Band1 = normalizedResidual6Term1Block1 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_0.2.1




theorem recurrence6Term1Band2_eq :
    recurrence6Term1Band2 = normalizedResidual6Term1Block2 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_0.2.2.1




theorem recurrence6Term1Band3_eq :
    recurrence6Term1Band3 = normalizedResidual6Term1Block3 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_0.2.2.2.1




theorem recurrence6Term1Band4_eq :
    recurrence6Term1Band4 = normalizedResidual6Term1Block4 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_0.2.2.2.2.1




theorem recurrence6Term1Band5_eq :
    recurrence6Term1Band5 = normalizedResidual6Term1Block5 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_0.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows6To8. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 rows 6–8

This file checks an independent group of row identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section











































theorem recurrence6Term1Row6_eq :
    remainder6Coefficient0NormalizedBlock6 * remainder7Coefficient1Square =
      recurrence6Term1Row6 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_6.1












































theorem recurrence6Term1Row7_eq :
    remainder6Coefficient0NormalizedBlock7 * remainder7Coefficient1Square =
      recurrence6Term1Row7 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_6.2.1












































theorem recurrence6Term1Row8_eq :
    remainder6Coefficient0NormalizedBlock8 * remainder7Coefficient1Square =
      recurrence6Term1Row8 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_6.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows9To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 rows 9–11

This file checks an independent group of row identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section











































theorem recurrence6Term1Row9_eq :
    remainder6Coefficient0NormalizedBlock9 * remainder7Coefficient1Square =
      recurrence6Term1Row9 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_9.1












































theorem recurrence6Term1Row10_eq :
    remainder6Coefficient0NormalizedBlock10 * remainder7Coefficient1Square =
      recurrence6Term1Row10 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_9.2.1












































theorem recurrence6Term1Row11_eq :
    remainder6Coefficient0NormalizedBlock11 * remainder7Coefficient1Square =
      recurrence6Term1Row11 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_9.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands6To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 bands 6–11

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term1Band6_eq :
    recurrence6Term1Band6 = normalizedResidual6Term1Block6 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_6.1




theorem recurrence6Term1Band7_eq :
    recurrence6Term1Band7 = normalizedResidual6Term1Block7 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_6.2.1




theorem recurrence6Term1Band8_eq :
    recurrence6Term1Band8 = normalizedResidual6Term1Block8 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_6.2.2.1




theorem recurrence6Term1Band9_eq :
    recurrence6Term1Band9 = normalizedResidual6Term1Block9 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_6.2.2.2.1




theorem recurrence6Term1Band10_eq :
    recurrence6Term1Band10 = normalizedResidual6Term1Block10 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_6.2.2.2.2.1




theorem recurrence6Term1Band11_eq :
    recurrence6Term1Band11 = normalizedResidual6Term1Block11 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_6.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows12To14. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 rows 12–14

This file checks an independent group of row identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section











































theorem recurrence6Term1Row12_eq :
    remainder6Coefficient0NormalizedBlock12 * remainder7Coefficient1Square =
      recurrence6Term1Row12 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_12.1












































theorem recurrence6Term1Row13_eq :
    remainder6Coefficient0NormalizedBlock13 * remainder7Coefficient1Square =
      recurrence6Term1Row13 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_12.2.1












































theorem recurrence6Term1Row14_eq :
    remainder6Coefficient0NormalizedBlock14 * remainder7Coefficient1Square =
      recurrence6Term1Row14 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_12.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Rows15To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 rows 15–17

This file checks an independent group of row identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section











































theorem recurrence6Term1Row15_eq :
    remainder6Coefficient0NormalizedBlock15 * remainder7Coefficient1Square =
      recurrence6Term1Row15 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_15.1












































theorem recurrence6Term1Row16_eq :
    remainder6Coefficient0NormalizedBlock16 * remainder7Coefficient1Square =
      recurrence6Term1Row16 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_15.2.1










































theorem recurrence6Term1Row17_eq :
    remainder6Coefficient0NormalizedBlock17 * remainder7Coefficient1Square =
      recurrence6Term1Row17 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_row_15.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands12To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 bands 12–17

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term1Band12_eq :
    recurrence6Term1Band12 = normalizedResidual6Term1Block12 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_12.1




theorem recurrence6Term1Band13_eq :
    recurrence6Term1Band13 = normalizedResidual6Term1Block13 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_12.2.1




theorem recurrence6Term1Band14_eq :
    recurrence6Term1Band14 = normalizedResidual6Term1Block14 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_12.2.2.1




theorem recurrence6Term1Band15_eq :
    recurrence6Term1Band15 = normalizedResidual6Term1Block15 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_12.2.2.2.1




theorem recurrence6Term1Band16_eq :
    recurrence6Term1Band16 = normalizedResidual6Term1Block16 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_12.2.2.2.2.1




theorem recurrence6Term1Band17_eq :
    recurrence6Term1Band17 = normalizedResidual6Term1Block17 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_12.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands18To23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 bands 18–23

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term1Band18_eq :
    recurrence6Term1Band18 = normalizedResidual6Term1Block18 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_18.1




theorem recurrence6Term1Band19_eq :
    recurrence6Term1Band19 = normalizedResidual6Term1Block19 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_18.2.1




theorem recurrence6Term1Band20_eq :
    recurrence6Term1Band20 = normalizedResidual6Term1Block20 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_18.2.2.1




theorem recurrence6Term1Band21_eq :
    recurrence6Term1Band21 = normalizedResidual6Term1Block21 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_18.2.2.2.1




theorem recurrence6Term1Band22_eq :
    recurrence6Term1Band22 = normalizedResidual6Term1Block22 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_18.2.2.2.2.1




theorem recurrence6Term1Band23_eq :
    recurrence6Term1Band23 = normalizedResidual6Term1Block23 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_18.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands24To29. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 bands 24–29

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term1Band24_eq :
    recurrence6Term1Band24 = normalizedResidual6Term1Block24 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_24.1




theorem recurrence6Term1Band25_eq :
    recurrence6Term1Band25 = normalizedResidual6Term1Block25 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_24.2.1




theorem recurrence6Term1Band26_eq :
    recurrence6Term1Band26 = normalizedResidual6Term1Block26 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_24.2.2.1




theorem recurrence6Term1Band27_eq :
    recurrence6Term1Band27 = normalizedResidual6Term1Block27 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_24.2.2.2.1




theorem recurrence6Term1Band28_eq :
    recurrence6Term1Band28 = normalizedResidual6Term1Block28 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_24.2.2.2.2.1




theorem recurrence6Term1Band29_eq :
    recurrence6Term1Band29 = normalizedResidual6Term1Block29 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_24.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1.Bands30To35. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term1 bands 30–35

This file checks an independent group of band identities for Term1 of the sixth
pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term1Band30_eq :
    recurrence6Term1Band30 = normalizedResidual6Term1Block30 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_30.1




theorem recurrence6Term1Band31_eq :
    recurrence6Term1Band31 = normalizedResidual6Term1Block31 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_30.2.1




theorem recurrence6Term1Band32_eq :
    recurrence6Term1Band32 = normalizedResidual6Term1Block32 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_30.2.2.1




theorem recurrence6Term1Band33_eq :
    recurrence6Term1Band33 = normalizedResidual6Term1Block33 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_30.2.2.2.1




theorem recurrence6Term1Band34_eq :
    recurrence6Term1Band34 = normalizedResidual6Term1Block34 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_30.2.2.2.2.1




theorem recurrence6Term1Band35_eq :
    recurrence6Term1Band35 = normalizedResidual6Term1Block35 := by
  exact MazurTransfer.order49_resultant_recurrence6_term1_band_30.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: Term1

This compatibility module combines the independently checked row and band shards
for Term1 of the sixth pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





theorem normalizedResidual6Term1_eq :
    remainder6Coefficient0Normalized * remainder7Coefficient1Square =
      normalizedResidual6Term1 := by
  have rows :
      remainder6Coefficient0Normalized * remainder7Coefficient1Square =
        recurrence6Term1Rows := by
    unfold remainder6Coefficient0Normalized recurrence6Term1Rows
    rw [← recurrence6Term1Row0_eq]
    rw [← recurrence6Term1Row1_eq]
    rw [← recurrence6Term1Row2_eq]
    rw [← recurrence6Term1Row3_eq]
    rw [← recurrence6Term1Row4_eq]
    rw [← recurrence6Term1Row5_eq]
    rw [← recurrence6Term1Row6_eq]
    rw [← recurrence6Term1Row7_eq]
    rw [← recurrence6Term1Row8_eq]
    rw [← recurrence6Term1Row9_eq]
    rw [← recurrence6Term1Row10_eq]
    rw [← recurrence6Term1Row11_eq]
    rw [← recurrence6Term1Row12_eq]
    rw [← recurrence6Term1Row13_eq]
    rw [← recurrence6Term1Row14_eq]
    rw [← recurrence6Term1Row15_eq]
    rw [← recurrence6Term1Row16_eq]
    rw [← recurrence6Term1Row17_eq]
    unfold remainder7Coefficient1Square
    ring
  rw [rows]
  have rearrange : recurrence6Term1Rows = recurrence6Term1Bands := by
    unfold recurrence6Term1Rows recurrence6Term1Bands recurrence6Term1Row0 recurrence6Term1Row1
    unfold recurrence6Term1Row2 recurrence6Term1Row3 recurrence6Term1Row4 recurrence6Term1Row5
    unfold recurrence6Term1Row6 recurrence6Term1Row7 recurrence6Term1Row8 recurrence6Term1Row9
    unfold recurrence6Term1Row10 recurrence6Term1Row11 recurrence6Term1Row12 recurrence6Term1Row13
    unfold recurrence6Term1Row14 recurrence6Term1Row15 recurrence6Term1Row16 recurrence6Term1Row17
    unfold recurrence6Term1Band0 recurrence6Term1Band1 recurrence6Term1Band2 recurrence6Term1Band3
    unfold recurrence6Term1Band4 recurrence6Term1Band5 recurrence6Term1Band6 recurrence6Term1Band7
    unfold recurrence6Term1Band8 recurrence6Term1Band9 recurrence6Term1Band10 recurrence6Term1Band11
    unfold recurrence6Term1Band12 recurrence6Term1Band13 recurrence6Term1Band14
    unfold recurrence6Term1Band15 recurrence6Term1Band16 recurrence6Term1Band17
    unfold recurrence6Term1Band18 recurrence6Term1Band19 recurrence6Term1Band20
    unfold recurrence6Term1Band21 recurrence6Term1Band22 recurrence6Term1Band23
    unfold recurrence6Term1Band24 recurrence6Term1Band25 recurrence6Term1Band26
    unfold recurrence6Term1Band27 recurrence6Term1Band28 recurrence6Term1Band29
    unfold recurrence6Term1Band30 recurrence6Term1Band31 recurrence6Term1Band32
    unfold recurrence6Term1Band33 recurrence6Term1Band34 recurrence6Term1Band35
    ring
  rw [rearrange]
  unfold recurrence6Term1Bands normalizedResidual6Term1
  rw [recurrence6Term1Band0_eq]
  rw [recurrence6Term1Band1_eq]
  rw [recurrence6Term1Band2_eq]
  rw [recurrence6Term1Band3_eq]
  rw [recurrence6Term1Band4_eq]
  rw [recurrence6Term1Band5_eq]
  rw [recurrence6Term1Band6_eq]
  rw [recurrence6Term1Band7_eq]
  rw [recurrence6Term1Band8_eq]
  rw [recurrence6Term1Band9_eq]
  rw [recurrence6Term1Band10_eq]
  rw [recurrence6Term1Band11_eq]
  rw [recurrence6Term1Band12_eq]
  rw [recurrence6Term1Band13_eq]
  rw [recurrence6Term1Band14_eq]
  rw [recurrence6Term1Band15_eq]
  rw [recurrence6Term1Band16_eq]
  rw [recurrence6Term1Band17_eq]
  rw [recurrence6Term1Band18_eq]
  rw [recurrence6Term1Band19_eq]
  rw [recurrence6Term1Band20_eq]
  rw [recurrence6Term1Band21_eq]
  rw [recurrence6Term1Band22_eq]
  rw [recurrence6Term1Band23_eq]
  rw [recurrence6Term1Band24_eq]
  rw [recurrence6Term1Band25_eq]
  rw [recurrence6Term1Band26_eq]
  rw [recurrence6Term1Band27_eq]
  rw [recurrence6Term1Band28_eq]
  rw [recurrence6Term1Band29_eq]
  rw [recurrence6Term1Band30_eq]
  rw [recurrence6Term1Band31_eq]
  rw [recurrence6Term1Band32_eq]
  rw [recurrence6Term1Band33_eq]
  rw [recurrence6Term1Band34_eq]
  rw [recurrence6Term1Band35_eq]

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
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0Normalized * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term1 := by
  exact MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term1_eq
#print axioms solution
