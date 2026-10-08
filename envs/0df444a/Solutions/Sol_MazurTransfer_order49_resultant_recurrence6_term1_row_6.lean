-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_term1_row_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:57:36.841856+00:00
-- url     : https://prove2.me/submissions/933528b2-d538-4fb6-a2f1-f792405f1d7c

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData4
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData7
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneTerm1PartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
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
  unfold remainder6Coefficient0NormalizedBlock6 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row6 recurrence6Term1Row6Band6
  unfold recurrence6Term1Row6Band7 recurrence6Term1Row6Band8 recurrence6Term1Row6Band9
  unfold recurrence6Term1Row6Band10 recurrence6Term1Row6Band11 recurrence6Term1Row6Band12
  unfold recurrence6Term1Row6Band13 recurrence6Term1Row6Band14 recurrence6Term1Row6Band15
  unfold recurrence6Term1Row6Band16 recurrence6Term1Row6Band17 recurrence6Term1Row6Band18
  unfold recurrence6Term1Row6Band19 recurrence6Term1Row6Band20 recurrence6Term1Row6Band21
  unfold recurrence6Term1Row6Band22 recurrence6Term1Row6Band23 recurrence6Term1Row6Band24
  unfold recurrence6Term1Row6Band25
  ring











































theorem recurrence6Term1Row7_eq :
    remainder6Coefficient0NormalizedBlock7 * remainder7Coefficient1Square =
      recurrence6Term1Row7 := by
  unfold remainder6Coefficient0NormalizedBlock7 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row7 recurrence6Term1Row7Band7
  unfold recurrence6Term1Row7Band8 recurrence6Term1Row7Band9 recurrence6Term1Row7Band10
  unfold recurrence6Term1Row7Band11 recurrence6Term1Row7Band12 recurrence6Term1Row7Band13
  unfold recurrence6Term1Row7Band14 recurrence6Term1Row7Band15 recurrence6Term1Row7Band16
  unfold recurrence6Term1Row7Band17 recurrence6Term1Row7Band18 recurrence6Term1Row7Band19
  unfold recurrence6Term1Row7Band20 recurrence6Term1Row7Band21 recurrence6Term1Row7Band22
  unfold recurrence6Term1Row7Band23 recurrence6Term1Row7Band24 recurrence6Term1Row7Band25
  unfold recurrence6Term1Row7Band26
  ring











































theorem recurrence6Term1Row8_eq :
    remainder6Coefficient0NormalizedBlock8 * remainder7Coefficient1Square =
      recurrence6Term1Row8 := by
  unfold remainder6Coefficient0NormalizedBlock8 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row8 recurrence6Term1Row8Band8
  unfold recurrence6Term1Row8Band9 recurrence6Term1Row8Band10 recurrence6Term1Row8Band11
  unfold recurrence6Term1Row8Band12 recurrence6Term1Row8Band13 recurrence6Term1Row8Band14
  unfold recurrence6Term1Row8Band15 recurrence6Term1Row8Band16 recurrence6Term1Row8Band17
  unfold recurrence6Term1Row8Band18 recurrence6Term1Row8Band19 recurrence6Term1Row8Band20
  unfold recurrence6Term1Row8Band21 recurrence6Term1Row8Band22 recurrence6Term1Row8Band23
  unfold recurrence6Term1Row8Band24 recurrence6Term1Row8Band25 recurrence6Term1Row8Band26
  unfold recurrence6Term1Row8Band27
  ring

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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock6 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row6) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock7 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row7) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock8 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row8) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row6_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row7_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row8_eq⟩
#print axioms solution
