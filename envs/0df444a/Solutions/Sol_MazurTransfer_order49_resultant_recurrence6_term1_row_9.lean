-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_term1_row_9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:29:50.406546+00:00
-- url     : https://prove2.me/submissions/0300274b-0517-4b78-8f7a-3040303a28d1

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneTerm1Partition4
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











































theorem recurrence6Term1Row9_eq :
    remainder6Coefficient0NormalizedBlock9 * remainder7Coefficient1Square =
      recurrence6Term1Row9 := by
  unfold remainder6Coefficient0NormalizedBlock9 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row9 recurrence6Term1Row9Band9
  unfold recurrence6Term1Row9Band10 recurrence6Term1Row9Band11 recurrence6Term1Row9Band12
  unfold recurrence6Term1Row9Band13 recurrence6Term1Row9Band14 recurrence6Term1Row9Band15
  unfold recurrence6Term1Row9Band16 recurrence6Term1Row9Band17 recurrence6Term1Row9Band18
  unfold recurrence6Term1Row9Band19 recurrence6Term1Row9Band20 recurrence6Term1Row9Band21
  unfold recurrence6Term1Row9Band22 recurrence6Term1Row9Band23 recurrence6Term1Row9Band24
  unfold recurrence6Term1Row9Band25 recurrence6Term1Row9Band26 recurrence6Term1Row9Band27
  unfold recurrence6Term1Row9Band28
  ring











































theorem recurrence6Term1Row10_eq :
    remainder6Coefficient0NormalizedBlock10 * remainder7Coefficient1Square =
      recurrence6Term1Row10 := by
  unfold remainder6Coefficient0NormalizedBlock10 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row10 recurrence6Term1Row10Band10
  unfold recurrence6Term1Row10Band11 recurrence6Term1Row10Band12 recurrence6Term1Row10Band13
  unfold recurrence6Term1Row10Band14 recurrence6Term1Row10Band15 recurrence6Term1Row10Band16
  unfold recurrence6Term1Row10Band17 recurrence6Term1Row10Band18 recurrence6Term1Row10Band19
  unfold recurrence6Term1Row10Band20 recurrence6Term1Row10Band21 recurrence6Term1Row10Band22
  unfold recurrence6Term1Row10Band23 recurrence6Term1Row10Band24 recurrence6Term1Row10Band25
  unfold recurrence6Term1Row10Band26 recurrence6Term1Row10Band27 recurrence6Term1Row10Band28
  unfold recurrence6Term1Row10Band29
  ring











































theorem recurrence6Term1Row11_eq :
    remainder6Coefficient0NormalizedBlock11 * remainder7Coefficient1Square =
      recurrence6Term1Row11 := by
  unfold remainder6Coefficient0NormalizedBlock11 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row11 recurrence6Term1Row11Band11
  unfold recurrence6Term1Row11Band12 recurrence6Term1Row11Band13 recurrence6Term1Row11Band14
  unfold recurrence6Term1Row11Band15 recurrence6Term1Row11Band16 recurrence6Term1Row11Band17
  unfold recurrence6Term1Row11Band18 recurrence6Term1Row11Band19 recurrence6Term1Row11Band20
  unfold recurrence6Term1Row11Band21 recurrence6Term1Row11Band22 recurrence6Term1Row11Band23
  unfold recurrence6Term1Row11Band24 recurrence6Term1Row11Band25 recurrence6Term1Row11Band26
  unfold recurrence6Term1Row11Band27 recurrence6Term1Row11Band28 recurrence6Term1Row11Band29
  unfold recurrence6Term1Row11Band30
  ring

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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock9 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row9) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock10 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row10) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock11 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row11) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row9_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row10_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row11_eq⟩
#print axioms solution
