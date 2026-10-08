-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_term1_row_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:45:42.953984+00:00
-- url     : https://prove2.me/submissions/fbdee8da-493e-4635-b192-43f35a0145f2

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






















theorem recurrence6Term1Row0_eq :
    remainder6Coefficient0NormalizedBlock0 * remainder7Coefficient1Square =
      recurrence6Term1Row0 := by
  unfold remainder6Coefficient0NormalizedBlock0 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row0 recurrence6Term1Row0Band0
  unfold recurrence6Term1Row0Band1 recurrence6Term1Row0Band2 recurrence6Term1Row0Band3
  unfold recurrence6Term1Row0Band4 recurrence6Term1Row0Band5 recurrence6Term1Row0Band6
  unfold recurrence6Term1Row0Band7 recurrence6Term1Row0Band8 recurrence6Term1Row0Band9
  unfold recurrence6Term1Row0Band10 recurrence6Term1Row0Band11 recurrence6Term1Row0Band12
  unfold recurrence6Term1Row0Band13 recurrence6Term1Row0Band14 recurrence6Term1Row0Band15
  unfold recurrence6Term1Row0Band16 recurrence6Term1Row0Band17 recurrence6Term1Row0Band18
  unfold recurrence6Term1Row0Band19
  ring





















theorem recurrence6Term1Row1_eq :
    remainder6Coefficient0NormalizedBlock1 * remainder7Coefficient1Square =
      recurrence6Term1Row1 := by
  unfold remainder6Coefficient0NormalizedBlock1 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row1 recurrence6Term1Row1Band1
  unfold recurrence6Term1Row1Band2 recurrence6Term1Row1Band3 recurrence6Term1Row1Band4
  unfold recurrence6Term1Row1Band5 recurrence6Term1Row1Band6 recurrence6Term1Row1Band7
  unfold recurrence6Term1Row1Band8 recurrence6Term1Row1Band9 recurrence6Term1Row1Band10
  unfold recurrence6Term1Row1Band11 recurrence6Term1Row1Band12 recurrence6Term1Row1Band13
  unfold recurrence6Term1Row1Band14 recurrence6Term1Row1Band15 recurrence6Term1Row1Band16
  unfold recurrence6Term1Row1Band17 recurrence6Term1Row1Band18 recurrence6Term1Row1Band19
  unfold recurrence6Term1Row1Band20
  ring

































theorem recurrence6Term1Row2_eq :
    remainder6Coefficient0NormalizedBlock2 * remainder7Coefficient1Square =
      recurrence6Term1Row2 := by
  unfold remainder6Coefficient0NormalizedBlock2 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row2 recurrence6Term1Row2Band2
  unfold recurrence6Term1Row2Band3 recurrence6Term1Row2Band4 recurrence6Term1Row2Band5
  unfold recurrence6Term1Row2Band6 recurrence6Term1Row2Band7 recurrence6Term1Row2Band8
  unfold recurrence6Term1Row2Band9 recurrence6Term1Row2Band10 recurrence6Term1Row2Band11
  unfold recurrence6Term1Row2Band12 recurrence6Term1Row2Band13 recurrence6Term1Row2Band14
  unfold recurrence6Term1Row2Band15 recurrence6Term1Row2Band16 recurrence6Term1Row2Band17
  unfold recurrence6Term1Row2Band18 recurrence6Term1Row2Band19 recurrence6Term1Row2Band20
  unfold recurrence6Term1Row2Band21
  ring

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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock0 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row0) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock1 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row1) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock2 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row2) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row0_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row1_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row2_eq⟩
#print axioms solution
