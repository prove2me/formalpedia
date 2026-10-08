-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:16:13.037975+00:00
-- url     : https://prove2.me/submissions/a5ffddab-7b8e-4b9c-9272-907362f10b3d

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData2
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData6
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneTerm3PartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_row_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_row_1
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_row_2
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_row_3
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_band_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_band_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_band_12
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_band_18
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_band_24
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term3_band_30
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Rows0To0. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 rows 0–0

This file checks rows 0 through 0 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































































theorem recurrence6Term3Row0_eq :
    normalizedExceptional6Block0 * remainder6Coefficient2Square =
      recurrence6Term3Row0 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_row_0


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Rows1To1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 rows 1–1

This file checks rows 1 through 1 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































































theorem recurrence6Term3Row1_eq :
    normalizedExceptional6Block1 * remainder6Coefficient2Square =
      recurrence6Term3Row1 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_row_1


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Rows2To2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 rows 2–2

This file checks rows 2 through 2 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section







































































theorem recurrence6Term3Row2_eq :
    normalizedExceptional6Block2 * remainder6Coefficient2Square =
      recurrence6Term3Row2 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_row_2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Rows3To3. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 rows 3–3

This file checks rows 3 through 3 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





































































theorem recurrence6Term3Row3_eq :
    normalizedExceptional6Block3 * remainder6Coefficient2Square =
      recurrence6Term3Row3 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_row_3


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands0To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term3Band0_eq :
    recurrence6Term3Band0 = normalizedResidual6Term3Block0 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_0.1




theorem recurrence6Term3Band1_eq :
    recurrence6Term3Band1 = normalizedResidual6Term3Block1 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_0.2.1




theorem recurrence6Term3Band2_eq :
    recurrence6Term3Band2 = normalizedResidual6Term3Block2 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_0.2.2.1




theorem recurrence6Term3Band3_eq :
    recurrence6Term3Band3 = normalizedResidual6Term3Block3 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_0.2.2.2.1




theorem recurrence6Term3Band4_eq :
    recurrence6Term3Band4 = normalizedResidual6Term3Block4 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_0.2.2.2.2.1




theorem recurrence6Term3Band5_eq :
    recurrence6Term3Band5 = normalizedResidual6Term3Block5 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_0.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands6To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 bands 6–11

This file checks bands 6 through 11 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term3Band6_eq :
    recurrence6Term3Band6 = normalizedResidual6Term3Block6 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_6.1




theorem recurrence6Term3Band7_eq :
    recurrence6Term3Band7 = normalizedResidual6Term3Block7 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_6.2.1




theorem recurrence6Term3Band8_eq :
    recurrence6Term3Band8 = normalizedResidual6Term3Block8 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_6.2.2.1




theorem recurrence6Term3Band9_eq :
    recurrence6Term3Band9 = normalizedResidual6Term3Block9 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_6.2.2.2.1




theorem recurrence6Term3Band10_eq :
    recurrence6Term3Band10 = normalizedResidual6Term3Block10 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_6.2.2.2.2.1




theorem recurrence6Term3Band11_eq :
    recurrence6Term3Band11 = normalizedResidual6Term3Block11 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_6.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands12To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 bands 12–17

This file checks bands 12 through 17 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term3Band12_eq :
    recurrence6Term3Band12 = normalizedResidual6Term3Block12 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_12.1




theorem recurrence6Term3Band13_eq :
    recurrence6Term3Band13 = normalizedResidual6Term3Block13 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_12.2.1




theorem recurrence6Term3Band14_eq :
    recurrence6Term3Band14 = normalizedResidual6Term3Block14 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_12.2.2.1




theorem recurrence6Term3Band15_eq :
    recurrence6Term3Band15 = normalizedResidual6Term3Block15 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_12.2.2.2.1




theorem recurrence6Term3Band16_eq :
    recurrence6Term3Band16 = normalizedResidual6Term3Block16 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_12.2.2.2.2.1




theorem recurrence6Term3Band17_eq :
    recurrence6Term3Band17 = normalizedResidual6Term3Block17 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_12.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands18To23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 bands 18–23

This file checks bands 18 through 23 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term3Band18_eq :
    recurrence6Term3Band18 = normalizedResidual6Term3Block18 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_18.1




theorem recurrence6Term3Band19_eq :
    recurrence6Term3Band19 = normalizedResidual6Term3Block19 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_18.2.1




theorem recurrence6Term3Band20_eq :
    recurrence6Term3Band20 = normalizedResidual6Term3Block20 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_18.2.2.1




theorem recurrence6Term3Band21_eq :
    recurrence6Term3Band21 = normalizedResidual6Term3Block21 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_18.2.2.2.1




theorem recurrence6Term3Band22_eq :
    recurrence6Term3Band22 = normalizedResidual6Term3Block22 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_18.2.2.2.2.1




theorem recurrence6Term3Band23_eq :
    recurrence6Term3Band23 = normalizedResidual6Term3Block23 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_18.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands24To29. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 bands 24–29

This file checks bands 24 through 29 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term3Band24_eq :
    recurrence6Term3Band24 = normalizedResidual6Term3Block24 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_24.1




theorem recurrence6Term3Band25_eq :
    recurrence6Term3Band25 = normalizedResidual6Term3Block25 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_24.2.1




theorem recurrence6Term3Band26_eq :
    recurrence6Term3Band26 = normalizedResidual6Term3Block26 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_24.2.2.1




theorem recurrence6Term3Band27_eq :
    recurrence6Term3Band27 = normalizedResidual6Term3Block27 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_24.2.2.2.1




theorem recurrence6Term3Band28_eq :
    recurrence6Term3Band28 = normalizedResidual6Term3Block28 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_24.2.2.2.2.1




theorem recurrence6Term3Band29_eq :
    recurrence6Term3Band29 = normalizedResidual6Term3Block29 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_24.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3.Bands30To35. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 Term3 bands 30–35

This file checks bands 30 through 35 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6Term3Band30_eq :
    recurrence6Term3Band30 = normalizedResidual6Term3Block30 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_30.1




theorem recurrence6Term3Band31_eq :
    recurrence6Term3Band31 = normalizedResidual6Term3Block31 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_30.2.1




theorem recurrence6Term3Band32_eq :
    recurrence6Term3Band32 = normalizedResidual6Term3Block32 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_30.2.2.1




theorem recurrence6Term3Band33_eq :
    recurrence6Term3Band33 = normalizedResidual6Term3Block33 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_30.2.2.2.1




theorem recurrence6Term3Band34_eq :
    recurrence6Term3Band34 = normalizedResidual6Term3Block34 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_30.2.2.2.2.1




theorem recurrence6Term3Band35_eq :
    recurrence6Term3Band35 = normalizedResidual6Term3Block35 := by
  exact MazurTransfer.order49_resultant_recurrence6_term3_band_30.2.2.2.2.2


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Term3. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: Term3

This compatibility module combines independently checked row and band
shards for the recurrence-6 Term3 arithmetic product.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





theorem normalizedResidual6Term3_eq :
    normalizedExceptional6 * remainder6Coefficient2Square =
      normalizedResidual6Term3 := by
  have rows :
      normalizedExceptional6 * remainder6Coefficient2Square =
        recurrence6Term3Rows := by
    unfold normalizedExceptional6 recurrence6Term3Rows
    rw [← recurrence6Term3Row0_eq]
    rw [← recurrence6Term3Row1_eq]
    rw [← recurrence6Term3Row2_eq]
    rw [← recurrence6Term3Row3_eq]
    unfold remainder6Coefficient2Square
    ring
  rw [rows]
  have rearrange : recurrence6Term3Rows = recurrence6Term3Bands := by
    unfold recurrence6Term3Rows recurrence6Term3Bands recurrence6Term3Row0 recurrence6Term3Row1
    unfold recurrence6Term3Row2 recurrence6Term3Row3 recurrence6Term3Band0 recurrence6Term3Band1
    unfold recurrence6Term3Band2 recurrence6Term3Band3 recurrence6Term3Band4 recurrence6Term3Band5
    unfold recurrence6Term3Band6 recurrence6Term3Band7 recurrence6Term3Band8 recurrence6Term3Band9
    unfold recurrence6Term3Band10 recurrence6Term3Band11 recurrence6Term3Band12
    unfold recurrence6Term3Band13 recurrence6Term3Band14 recurrence6Term3Band15
    unfold recurrence6Term3Band16 recurrence6Term3Band17 recurrence6Term3Band18
    unfold recurrence6Term3Band19 recurrence6Term3Band20 recurrence6Term3Band21
    unfold recurrence6Term3Band22 recurrence6Term3Band23 recurrence6Term3Band24
    unfold recurrence6Term3Band25 recurrence6Term3Band26 recurrence6Term3Band27
    unfold recurrence6Term3Band28 recurrence6Term3Band29 recurrence6Term3Band30
    unfold recurrence6Term3Band31 recurrence6Term3Band32 recurrence6Term3Band33
    unfold recurrence6Term3Band34 recurrence6Term3Band35
    ring
  rw [rearrange]
  unfold recurrence6Term3Bands normalizedResidual6Term3
  rw [recurrence6Term3Band0_eq]
  rw [recurrence6Term3Band1_eq]
  rw [recurrence6Term3Band2_eq]
  rw [recurrence6Term3Band3_eq]
  rw [recurrence6Term3Band4_eq]
  rw [recurrence6Term3Band5_eq]
  rw [recurrence6Term3Band6_eq]
  rw [recurrence6Term3Band7_eq]
  rw [recurrence6Term3Band8_eq]
  rw [recurrence6Term3Band9_eq]
  rw [recurrence6Term3Band10_eq]
  rw [recurrence6Term3Band11_eq]
  rw [recurrence6Term3Band12_eq]
  rw [recurrence6Term3Band13_eq]
  rw [recurrence6Term3Band14_eq]
  rw [recurrence6Term3Band15_eq]
  rw [recurrence6Term3Band16_eq]
  rw [recurrence6Term3Band17_eq]
  rw [recurrence6Term3Band18_eq]
  rw [recurrence6Term3Band19_eq]
  rw [recurrence6Term3Band20_eq]
  rw [recurrence6Term3Band21_eq]
  rw [recurrence6Term3Band22_eq]
  rw [recurrence6Term3Band23_eq]
  rw [recurrence6Term3Band24_eq]
  rw [recurrence6Term3Band25_eq]
  rw [recurrence6Term3Band26_eq]
  rw [recurrence6Term3Band27_eq]
  rw [recurrence6Term3Band28_eq]
  rw [recurrence6Term3Band29_eq]
  rw [recurrence6Term3Band30_eq]
  rw [recurrence6Term3Band31_eq]
  rw [recurrence6Term3Band32_eq]
  rw [recurrence6Term3Band33_eq]
  rw [recurrence6Term3Band34_eq]
  rw [recurrence6Term3Band35_eq]

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
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedExceptional6 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term3 := by
  exact MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term3_eq
#print axioms solution
