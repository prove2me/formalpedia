-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_term1_row_15
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:42:28.948744+00:00
-- url     : https://prove2.me/submissions/fa41ed74-f98a-45d1-81ca-7df97f992fd6

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneTerm1Partition7
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
  unfold remainder6Coefficient0NormalizedBlock15 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row15 recurrence6Term1Row15Band15
  unfold recurrence6Term1Row15Band16 recurrence6Term1Row15Band17 recurrence6Term1Row15Band18
  unfold recurrence6Term1Row15Band19 recurrence6Term1Row15Band20 recurrence6Term1Row15Band21
  unfold recurrence6Term1Row15Band22 recurrence6Term1Row15Band23 recurrence6Term1Row15Band24
  unfold recurrence6Term1Row15Band25 recurrence6Term1Row15Band26 recurrence6Term1Row15Band27
  unfold recurrence6Term1Row15Band28 recurrence6Term1Row15Band29 recurrence6Term1Row15Band30
  unfold recurrence6Term1Row15Band31 recurrence6Term1Row15Band32 recurrence6Term1Row15Band33
  unfold recurrence6Term1Row15Band34
  ring











































theorem recurrence6Term1Row16_eq :
    remainder6Coefficient0NormalizedBlock16 * remainder7Coefficient1Square =
      recurrence6Term1Row16 := by
  unfold remainder6Coefficient0NormalizedBlock16 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row16 recurrence6Term1Row16Band16
  unfold recurrence6Term1Row16Band17 recurrence6Term1Row16Band18 recurrence6Term1Row16Band19
  unfold recurrence6Term1Row16Band20 recurrence6Term1Row16Band21 recurrence6Term1Row16Band22
  unfold recurrence6Term1Row16Band23 recurrence6Term1Row16Band24 recurrence6Term1Row16Band25
  unfold recurrence6Term1Row16Band26 recurrence6Term1Row16Band27 recurrence6Term1Row16Band28
  unfold recurrence6Term1Row16Band29 recurrence6Term1Row16Band30 recurrence6Term1Row16Band31
  unfold recurrence6Term1Row16Band32 recurrence6Term1Row16Band33 recurrence6Term1Row16Band34
  unfold recurrence6Term1Row16Band35
  ring









































theorem recurrence6Term1Row17_eq :
    remainder6Coefficient0NormalizedBlock17 * remainder7Coefficient1Square =
      recurrence6Term1Row17 := by
  unfold remainder6Coefficient0NormalizedBlock17 remainder7Coefficient1Square
  unfold remainder7Coefficient1SquareBlock0 remainder7Coefficient1SquareBlock1
  unfold remainder7Coefficient1SquareBlock2 remainder7Coefficient1SquareBlock3
  unfold remainder7Coefficient1SquareBlock4 remainder7Coefficient1SquareBlock5
  unfold remainder7Coefficient1SquareBlock6 remainder7Coefficient1SquareBlock7
  unfold remainder7Coefficient1SquareBlock8 remainder7Coefficient1SquareBlock9
  unfold remainder7Coefficient1SquareBlock10 remainder7Coefficient1SquareBlock11
  unfold remainder7Coefficient1SquareBlock12 remainder7Coefficient1SquareBlock13
  unfold remainder7Coefficient1SquareBlock14 remainder7Coefficient1SquareBlock15
  unfold remainder7Coefficient1SquareBlock16 remainder7Coefficient1SquareBlock17
  unfold remainder7Coefficient1SquareBlock18 recurrence6Term1Row17 recurrence6Term1Row17Band17
  unfold recurrence6Term1Row17Band18 recurrence6Term1Row17Band19 recurrence6Term1Row17Band20
  unfold recurrence6Term1Row17Band21 recurrence6Term1Row17Band22 recurrence6Term1Row17Band23
  unfold recurrence6Term1Row17Band24 recurrence6Term1Row17Band25 recurrence6Term1Row17Band26
  unfold recurrence6Term1Row17Band27 recurrence6Term1Row17Band28 recurrence6Term1Row17Band29
  unfold recurrence6Term1Row17Band30 recurrence6Term1Row17Band31 recurrence6Term1Row17Band32
  unfold recurrence6Term1Row17Band33 recurrence6Term1Row17Band34 recurrence6Term1Row17Band35
  ring

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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock15 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row15) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock16 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row16) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0NormalizedBlock17 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Square =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row17) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row15_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row16_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Row17_eq⟩
#print axioms solution
