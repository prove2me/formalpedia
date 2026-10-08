-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:29:51.635596+00:00
-- url     : https://prove2.me/submissions/b97fefa3-c048-4fd3-bb6f-8dcf339f6606

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData1
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneB1A1PartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_row_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_row_2
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_row_4
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_row_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_row_8
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_band_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_band_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_band_12
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_band_18
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_b1a1_band_24
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows0To1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 rows 0–1

This file checks rows 0 through 1 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B1A1Row0_eq :
    remainder7Coefficient1NormalizedBlock0 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row0 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_0.1








































theorem recurrence6B1A1Row1_eq :
    remainder7Coefficient1NormalizedBlock1 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row1 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_0.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows2To3. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 rows 2–3

This file checks rows 2 through 3 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B1A1Row2_eq :
    remainder7Coefficient1NormalizedBlock2 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row2 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_2.1








































theorem recurrence6B1A1Row3_eq :
    remainder7Coefficient1NormalizedBlock3 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row3 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows4To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 rows 4–5

This file checks rows 4 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B1A1Row4_eq :
    remainder7Coefficient1NormalizedBlock4 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row4 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_4.1








































theorem recurrence6B1A1Row5_eq :
    remainder7Coefficient1NormalizedBlock5 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row5 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_4.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands0To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B1A1Band0_eq :
    recurrence6B1A1Band0 = remainder7Coefficient1TimesRemainder6Coefficient1Block0 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_0.1




theorem recurrence6B1A1Band1_eq :
    recurrence6B1A1Band1 = remainder7Coefficient1TimesRemainder6Coefficient1Block1 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_0.2.1




theorem recurrence6B1A1Band2_eq :
    recurrence6B1A1Band2 = remainder7Coefficient1TimesRemainder6Coefficient1Block2 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_0.2.2.1




theorem recurrence6B1A1Band3_eq :
    recurrence6B1A1Band3 = remainder7Coefficient1TimesRemainder6Coefficient1Block3 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_0.2.2.2.1




theorem recurrence6B1A1Band4_eq :
    recurrence6B1A1Band4 = remainder7Coefficient1TimesRemainder6Coefficient1Block4 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_0.2.2.2.2.1




theorem recurrence6B1A1Band5_eq :
    recurrence6B1A1Band5 = remainder7Coefficient1TimesRemainder6Coefficient1Block5 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_0.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows6To7. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 rows 6–7

This file checks rows 6 through 7 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B1A1Row6_eq :
    remainder7Coefficient1NormalizedBlock6 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row6 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_6.1








































theorem recurrence6B1A1Row7_eq :
    remainder7Coefficient1NormalizedBlock7 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row7 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_6.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Rows8To9. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 rows 8–9

This file checks rows 8 through 9 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































theorem recurrence6B1A1Row8_eq :
    remainder7Coefficient1NormalizedBlock8 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row8 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_8.1






































theorem recurrence6B1A1Row9_eq :
    remainder7Coefficient1NormalizedBlock9 * remainder6Coefficient1Normalized =
      recurrence6B1A1Row9 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_row_8.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands6To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B1A1Band6_eq :
    recurrence6B1A1Band6 = remainder7Coefficient1TimesRemainder6Coefficient1Block6 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_6.1




theorem recurrence6B1A1Band7_eq :
    recurrence6B1A1Band7 = remainder7Coefficient1TimesRemainder6Coefficient1Block7 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_6.2.1




theorem recurrence6B1A1Band8_eq :
    recurrence6B1A1Band8 = remainder7Coefficient1TimesRemainder6Coefficient1Block8 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_6.2.2.1




theorem recurrence6B1A1Band9_eq :
    recurrence6B1A1Band9 = remainder7Coefficient1TimesRemainder6Coefficient1Block9 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_6.2.2.2.1




theorem recurrence6B1A1Band10_eq :
    recurrence6B1A1Band10 = remainder7Coefficient1TimesRemainder6Coefficient1Block10 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_6.2.2.2.2.1




theorem recurrence6B1A1Band11_eq :
    recurrence6B1A1Band11 = remainder7Coefficient1TimesRemainder6Coefficient1Block11 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_6.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands12To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 bands 12–17

This file checks bands 12 through 17 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B1A1Band12_eq :
    recurrence6B1A1Band12 = remainder7Coefficient1TimesRemainder6Coefficient1Block12 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_12.1




theorem recurrence6B1A1Band13_eq :
    recurrence6B1A1Band13 = remainder7Coefficient1TimesRemainder6Coefficient1Block13 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_12.2.1




theorem recurrence6B1A1Band14_eq :
    recurrence6B1A1Band14 = remainder7Coefficient1TimesRemainder6Coefficient1Block14 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_12.2.2.1




theorem recurrence6B1A1Band15_eq :
    recurrence6B1A1Band15 = remainder7Coefficient1TimesRemainder6Coefficient1Block15 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_12.2.2.2.1




theorem recurrence6B1A1Band16_eq :
    recurrence6B1A1Band16 = remainder7Coefficient1TimesRemainder6Coefficient1Block16 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_12.2.2.2.2.1




theorem recurrence6B1A1Band17_eq :
    recurrence6B1A1Band17 = remainder7Coefficient1TimesRemainder6Coefficient1Block17 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_12.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands18To23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B1A1Band18_eq :
    recurrence6B1A1Band18 = remainder7Coefficient1TimesRemainder6Coefficient1Block18 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_18.1




theorem recurrence6B1A1Band19_eq :
    recurrence6B1A1Band19 = remainder7Coefficient1TimesRemainder6Coefficient1Block19 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_18.2.1




theorem recurrence6B1A1Band20_eq :
    recurrence6B1A1Band20 = remainder7Coefficient1TimesRemainder6Coefficient1Block20 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_18.2.2.1




theorem recurrence6B1A1Band21_eq :
    recurrence6B1A1Band21 = remainder7Coefficient1TimesRemainder6Coefficient1Block21 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_18.2.2.2.1




theorem recurrence6B1A1Band22_eq :
    recurrence6B1A1Band22 = remainder7Coefficient1TimesRemainder6Coefficient1Block22 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_18.2.2.2.2.1




theorem recurrence6B1A1Band23_eq :
    recurrence6B1A1Band23 = remainder7Coefficient1TimesRemainder6Coefficient1Block23 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_18.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1.Bands24To25. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B1A1 bands 24–25

This file checks bands 24 through 25 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B1A1Band24_eq :
    recurrence6B1A1Band24 = remainder7Coefficient1TimesRemainder6Coefficient1Block24 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_24.1




theorem recurrence6B1A1Band25_eq :
    recurrence6B1A1Band25 = remainder7Coefficient1TimesRemainder6Coefficient1Block25 := by
  exact MazurTransfer.order49_resultant_recurrence6_b1a1_band_24.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B1A1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: B1A1

This compatibility module combines independently checked row and band
shards for the recurrence-6 B1A1 arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





theorem remainder7Coefficient1TimesRemainder6Coefficient1_eq :
    remainder7Coefficient1Normalized * remainder6Coefficient1Normalized =
      remainder7Coefficient1TimesRemainder6Coefficient1 := by
  have rows :
      remainder7Coefficient1Normalized * remainder6Coefficient1Normalized =
        recurrence6B1A1Rows := by
    unfold remainder7Coefficient1Normalized recurrence6B1A1Rows
    rw [← recurrence6B1A1Row0_eq]
    rw [← recurrence6B1A1Row1_eq]
    rw [← recurrence6B1A1Row2_eq]
    rw [← recurrence6B1A1Row3_eq]
    rw [← recurrence6B1A1Row4_eq]
    rw [← recurrence6B1A1Row5_eq]
    rw [← recurrence6B1A1Row6_eq]
    rw [← recurrence6B1A1Row7_eq]
    rw [← recurrence6B1A1Row8_eq]
    rw [← recurrence6B1A1Row9_eq]
    unfold remainder6Coefficient1Normalized
    ring
  rw [rows]
  have rearrange : recurrence6B1A1Rows = recurrence6B1A1Bands := by
    unfold recurrence6B1A1Rows recurrence6B1A1Bands recurrence6B1A1Row0 recurrence6B1A1Row1
    unfold recurrence6B1A1Row2 recurrence6B1A1Row3 recurrence6B1A1Row4 recurrence6B1A1Row5
    unfold recurrence6B1A1Row6 recurrence6B1A1Row7 recurrence6B1A1Row8 recurrence6B1A1Row9
    unfold recurrence6B1A1Band0 recurrence6B1A1Band1 recurrence6B1A1Band2 recurrence6B1A1Band3
    unfold recurrence6B1A1Band4 recurrence6B1A1Band5 recurrence6B1A1Band6 recurrence6B1A1Band7
    unfold recurrence6B1A1Band8 recurrence6B1A1Band9 recurrence6B1A1Band10 recurrence6B1A1Band11
    unfold recurrence6B1A1Band12 recurrence6B1A1Band13 recurrence6B1A1Band14 recurrence6B1A1Band15
    unfold recurrence6B1A1Band16 recurrence6B1A1Band17 recurrence6B1A1Band18 recurrence6B1A1Band19
    unfold recurrence6B1A1Band20 recurrence6B1A1Band21 recurrence6B1A1Band22 recurrence6B1A1Band23
    unfold recurrence6B1A1Band24 recurrence6B1A1Band25
    ring
  rw [rearrange]
  unfold recurrence6B1A1Bands remainder7Coefficient1TimesRemainder6Coefficient1
  rw [recurrence6B1A1Band0_eq]
  rw [recurrence6B1A1Band1_eq]
  rw [recurrence6B1A1Band2_eq]
  rw [recurrence6B1A1Band3_eq]
  rw [recurrence6B1A1Band4_eq]
  rw [recurrence6B1A1Band5_eq]
  rw [recurrence6B1A1Band6_eq]
  rw [recurrence6B1A1Band7_eq]
  rw [recurrence6B1A1Band8_eq]
  rw [recurrence6B1A1Band9_eq]
  rw [recurrence6B1A1Band10_eq]
  rw [recurrence6B1A1Band11_eq]
  rw [recurrence6B1A1Band12_eq]
  rw [recurrence6B1A1Band13_eq]
  rw [recurrence6B1A1Band14_eq]
  rw [recurrence6B1A1Band15_eq]
  rw [recurrence6B1A1Band16_eq]
  rw [recurrence6B1A1Band17_eq]
  rw [recurrence6B1A1Band18_eq]
  rw [recurrence6B1A1Band19_eq]
  rw [recurrence6B1A1Band20_eq]
  rw [recurrence6B1A1Band21_eq]
  rw [recurrence6B1A1Band22_eq]
  rw [recurrence6B1A1Band23_eq]
  rw [recurrence6B1A1Band24_eq]
  rw [recurrence6B1A1Band25_eq]

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
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Normalized * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1Normalized =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1 := by
  exact MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1_eq
#print axioms solution
