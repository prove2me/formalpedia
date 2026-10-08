-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_term1_row_12
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:35:38.253976+00:00
-- url     : https://prove2.me/submissions/5a63882e-b020-41df-b9f4-331a748e2556

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneTerm1Partition6
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











































theorem recurrence6Term1Row12_eq :
    remainder6Coefficient0NormalizedBlock12 * remainder7Coefficient1Square =
      recurrence6Term1Row12 := by
  unfold remainder6Coefficient0NormalizedBlock12 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row12 recurrence6Term1Row12Band12
  unfold recurrence6Term1Row12Band13 recurrence6Term1Row12Band14 recurrence6Term1Row12Band15
  unfold recurrence6Term1Row12Band16 recurrence6Term1Row12Band17 recurrence6Term1Row12Band18
  unfold recurrence6Term1Row12Band19 recurrence6Term1Row12Band20 recurrence6Term1Row12Band21
  unfold recurrence6Term1Row12Band22 recurrence6Term1Row12Band23 recurrence6Term1Row12Band24
  unfold recurrence6Term1Row12Band25 recurrence6Term1Row12Band26 recurrence6Term1Row12Band27
  unfold recurrence6Term1Row12Band28 recurrence6Term1Row12Band29 recurrence6Term1Row12Band30
  unfold recurrence6Term1Row12Band31
  ring











































theorem recurrence6Term1Row13_eq :
    remainder6Coefficient0NormalizedBlock13 * remainder7Coefficient1Square =
      recurrence6Term1Row13 := by
  unfold remainder6Coefficient0NormalizedBlock13 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row13 recurrence6Term1Row13Band13
  unfold recurrence6Term1Row13Band14 recurrence6Term1Row13Band15 recurrence6Term1Row13Band16
  unfold recurrence6Term1Row13Band17 recurrence6Term1Row13Band18 recurrence6Term1Row13Band19
  unfold recurrence6Term1Row13Band20 recurrence6Term1Row13Band21 recurrence6Term1Row13Band22
  unfold recurrence6Term1Row13Band23 recurrence6Term1Row13Band24 recurrence6Term1Row13Band25
  unfold recurrence6Term1Row13Band26 recurrence6Term1Row13Band27 recurrence6Term1Row13Band28
  unfold recurrence6Term1Row13Band29 recurrence6Term1Row13Band30 recurrence6Term1Row13Band31
  unfold recurrence6Term1Row13Band32
  ring











































theorem recurrence6Term1Row14_eq :
    remainder6Coefficient0NormalizedBlock14 * remainder7Coefficient1Square =
      recurrence6Term1Row14 := by
  unfold remainder6Coefficient0NormalizedBlock14 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row14 recurrence6Term1Row14Band14
  unfold recurrence6Term1Row14Band15 recurrence6Term1Row14Band16 recurrence6Term1Row14Band17
  unfold recurrence6Term1Row14Band18 recurrence6Term1Row14Band19 recurrence6Term1Row14Band20
  unfold recurrence6Term1Row14Band21 recurrence6Term1Row14Band22 recurrence6Term1Row14Band23
  unfold recurrence6Term1Row14Band24 recurrence6Term1Row14Band25 recurrence6Term1Row14Band26
  unfold recurrence6Term1Row14Band27 recurrence6Term1Row14Band28 recurrence6Term1Row14Band29
  unfold recurrence6Term1Row14Band30 recurrence6Term1Row14Band31 recurrence6Term1Row14Band32
  unfold recurrence6Term1Row14Band33
  ring

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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock12 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row12) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock13 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row13) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock14 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row14) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row12_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row13_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row14_eq⟩
#print axioms solution
