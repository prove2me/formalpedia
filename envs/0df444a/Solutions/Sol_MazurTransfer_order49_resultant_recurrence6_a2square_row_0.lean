-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_a2square_row_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:54:19.520375+00:00
-- url     : https://prove2.me/submissions/18e1a3a9-107c-4c7c-8192-7ffe712c0a7d

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData2
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneA2SquarePartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
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
  unfold remainder6Coefficient2NormalizedBlock0 remainder6Coefficient2Normalized
  unfold remainder6Coefficient2NormalizedBlock0 remainder6Coefficient2NormalizedBlock1
  unfold remainder6Coefficient2NormalizedBlock2 remainder6Coefficient2NormalizedBlock3
  unfold remainder6Coefficient2NormalizedBlock4 remainder6Coefficient2NormalizedBlock5
  unfold remainder6Coefficient2NormalizedBlock6 remainder6Coefficient2NormalizedBlock7
  unfold remainder6Coefficient2NormalizedBlock8 remainder6Coefficient2NormalizedBlock9
  unfold remainder6Coefficient2NormalizedBlock10 remainder6Coefficient2NormalizedBlock11
  unfold remainder6Coefficient2NormalizedBlock12 remainder6Coefficient2NormalizedBlock13
  unfold remainder6Coefficient2NormalizedBlock14 remainder6Coefficient2NormalizedBlock15
  unfold remainder6Coefficient2NormalizedBlock16 recurrence6A2SquareRow0
  unfold recurrence6A2SquareRow0Band0 recurrence6A2SquareRow0Band1 recurrence6A2SquareRow0Band2
  unfold recurrence6A2SquareRow0Band3 recurrence6A2SquareRow0Band4 recurrence6A2SquareRow0Band5
  unfold recurrence6A2SquareRow0Band6 recurrence6A2SquareRow0Band7 recurrence6A2SquareRow0Band8
  unfold recurrence6A2SquareRow0Band9 recurrence6A2SquareRow0Band10 recurrence6A2SquareRow0Band11
  unfold recurrence6A2SquareRow0Band12 recurrence6A2SquareRow0Band13 recurrence6A2SquareRow0Band14
  unfold recurrence6A2SquareRow0Band15 recurrence6A2SquareRow0Band16 recurrence6A2SquareRow0Band17
  ring







































theorem recurrence6A2SquareRow1_eq :
    remainder6Coefficient2NormalizedBlock1 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow1 := by
  unfold remainder6Coefficient2NormalizedBlock1 remainder6Coefficient2Normalized
  unfold remainder6Coefficient2NormalizedBlock0 remainder6Coefficient2NormalizedBlock1
  unfold remainder6Coefficient2NormalizedBlock2 remainder6Coefficient2NormalizedBlock3
  unfold remainder6Coefficient2NormalizedBlock4 remainder6Coefficient2NormalizedBlock5
  unfold remainder6Coefficient2NormalizedBlock6 remainder6Coefficient2NormalizedBlock7
  unfold remainder6Coefficient2NormalizedBlock8 remainder6Coefficient2NormalizedBlock9
  unfold remainder6Coefficient2NormalizedBlock10 remainder6Coefficient2NormalizedBlock11
  unfold remainder6Coefficient2NormalizedBlock12 remainder6Coefficient2NormalizedBlock13
  unfold remainder6Coefficient2NormalizedBlock14 remainder6Coefficient2NormalizedBlock15
  unfold remainder6Coefficient2NormalizedBlock16 recurrence6A2SquareRow1
  unfold recurrence6A2SquareRow1Band1 recurrence6A2SquareRow1Band2 recurrence6A2SquareRow1Band3
  unfold recurrence6A2SquareRow1Band4 recurrence6A2SquareRow1Band5 recurrence6A2SquareRow1Band6
  unfold recurrence6A2SquareRow1Band7 recurrence6A2SquareRow1Band8 recurrence6A2SquareRow1Band9
  unfold recurrence6A2SquareRow1Band10 recurrence6A2SquareRow1Band11 recurrence6A2SquareRow1Band12
  unfold recurrence6A2SquareRow1Band13 recurrence6A2SquareRow1Band14 recurrence6A2SquareRow1Band15
  unfold recurrence6A2SquareRow1Band16 recurrence6A2SquareRow1Band17 recurrence6A2SquareRow1Band18
  ring







































theorem recurrence6A2SquareRow2_eq :
    remainder6Coefficient2NormalizedBlock2 * remainder6Coefficient2Normalized =
      recurrence6A2SquareRow2 := by
  unfold remainder6Coefficient2NormalizedBlock2 remainder6Coefficient2Normalized
  unfold remainder6Coefficient2NormalizedBlock0 remainder6Coefficient2NormalizedBlock1
  unfold remainder6Coefficient2NormalizedBlock2 remainder6Coefficient2NormalizedBlock3
  unfold remainder6Coefficient2NormalizedBlock4 remainder6Coefficient2NormalizedBlock5
  unfold remainder6Coefficient2NormalizedBlock6 remainder6Coefficient2NormalizedBlock7
  unfold remainder6Coefficient2NormalizedBlock8 remainder6Coefficient2NormalizedBlock9
  unfold remainder6Coefficient2NormalizedBlock10 remainder6Coefficient2NormalizedBlock11
  unfold remainder6Coefficient2NormalizedBlock12 remainder6Coefficient2NormalizedBlock13
  unfold remainder6Coefficient2NormalizedBlock14 remainder6Coefficient2NormalizedBlock15
  unfold remainder6Coefficient2NormalizedBlock16 recurrence6A2SquareRow2
  unfold recurrence6A2SquareRow2Band2 recurrence6A2SquareRow2Band3 recurrence6A2SquareRow2Band4
  unfold recurrence6A2SquareRow2Band5 recurrence6A2SquareRow2Band6 recurrence6A2SquareRow2Band7
  unfold recurrence6A2SquareRow2Band8 recurrence6A2SquareRow2Band9 recurrence6A2SquareRow2Band10
  unfold recurrence6A2SquareRow2Band11 recurrence6A2SquareRow2Band12 recurrence6A2SquareRow2Band13
  unfold recurrence6A2SquareRow2Band14 recurrence6A2SquareRow2Band15 recurrence6A2SquareRow2Band16
  unfold recurrence6A2SquareRow2Band17 recurrence6A2SquareRow2Band18 recurrence6A2SquareRow2Band19
  ring

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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2NormalizedBlock0 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6A2SquareRow0) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2NormalizedBlock1 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6A2SquareRow1) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2NormalizedBlock2 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6A2SquareRow2) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6A2SquareRow0_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6A2SquareRow1_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6A2SquareRow2_eq⟩
#print axioms solution
