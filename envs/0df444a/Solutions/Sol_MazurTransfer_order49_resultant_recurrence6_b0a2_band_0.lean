-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_b0a2_band_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:08:50.15925+00:00
-- url     : https://prove2.me/submissions/904b93c6-49c9-4165-94bb-e3226936281c

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData0
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneB0A2PartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows0To1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 0–1

This file checks rows 0 through 1 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

















































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows2To3. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 2–3

This file checks rows 2 through 3 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

















































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows4To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 4–5

This file checks rows 4 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

















































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands0To5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 0–5

This file checks bands 0 through 5 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section



theorem recurrence6B0A2Band0_eq :
    recurrence6B0A2Band0 = remainder7Coefficient0TimesRemainder6Coefficient2Block0 := by
  unfold recurrence6B0A2Band0 recurrence6B0A2Row0Band0
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block0
  ring



theorem recurrence6B0A2Band1_eq :
    recurrence6B0A2Band1 = remainder7Coefficient0TimesRemainder6Coefficient2Block1 := by
  unfold recurrence6B0A2Band1 recurrence6B0A2Row0Band1 recurrence6B0A2Row1Band1
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block1
  ring



theorem recurrence6B0A2Band2_eq :
    recurrence6B0A2Band2 = remainder7Coefficient0TimesRemainder6Coefficient2Block2 := by
  unfold recurrence6B0A2Band2 recurrence6B0A2Row0Band2 recurrence6B0A2Row1Band2
  unfold recurrence6B0A2Row2Band2 remainder7Coefficient0TimesRemainder6Coefficient2Block2
  ring



theorem recurrence6B0A2Band3_eq :
    recurrence6B0A2Band3 = remainder7Coefficient0TimesRemainder6Coefficient2Block3 := by
  unfold recurrence6B0A2Band3 recurrence6B0A2Row0Band3 recurrence6B0A2Row1Band3
  unfold recurrence6B0A2Row2Band3 recurrence6B0A2Row3Band3
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block3
  ring



theorem recurrence6B0A2Band4_eq :
    recurrence6B0A2Band4 = remainder7Coefficient0TimesRemainder6Coefficient2Block4 := by
  unfold recurrence6B0A2Band4 recurrence6B0A2Row0Band4 recurrence6B0A2Row1Band4
  unfold recurrence6B0A2Row2Band4 recurrence6B0A2Row3Band4 recurrence6B0A2Row4Band4
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block4
  ring



theorem recurrence6B0A2Band5_eq :
    recurrence6B0A2Band5 = remainder7Coefficient0TimesRemainder6Coefficient2Block5 := by
  unfold recurrence6B0A2Band5 recurrence6B0A2Row0Band5 recurrence6B0A2Row1Band5
  unfold recurrence6B0A2Row2Band5 recurrence6B0A2Row3Band5 recurrence6B0A2Row4Band5
  unfold recurrence6B0A2Row5Band5 remainder7Coefficient0TimesRemainder6Coefficient2Block5
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows6To7. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 6–7

This file checks rows 6 through 7 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

















































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Rows8To9. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 rows 8–9

This file checks rows 8 through 9 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section















































































end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands6To11. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 6–11

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


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands12To17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 12–17

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


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands18To23. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 18–23

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


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2.Bands24To25. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 B0A2 bands 24–25

This file checks bands 24 through 25 of an independent arithmetic product for recurrence 6.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section









end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6B0A2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: B0A2

This compatibility module combines independently checked row and band
shards for the recurrence-6 B0A2 arithmetic product.
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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band0 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block0) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band1 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block1) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band2 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block2) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band3 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block3) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band4 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block4) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band5 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block5) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band0_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band1_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band2_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band3_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band4_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band5_eq⟩
#print axioms solution
