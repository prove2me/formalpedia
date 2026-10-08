-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_b0a2_band_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:09:53.845446+00:00
-- url     : https://prove2.me/submissions/e207c58f-ea2c-4a9a-a1be-be20d952eb09

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



theorem recurrence6B0A2Band6_eq :
    recurrence6B0A2Band6 = remainder7Coefficient0TimesRemainder6Coefficient2Block6 := by
  unfold recurrence6B0A2Band6 recurrence6B0A2Row0Band6 recurrence6B0A2Row1Band6
  unfold recurrence6B0A2Row2Band6 recurrence6B0A2Row3Band6 recurrence6B0A2Row4Band6
  unfold recurrence6B0A2Row5Band6 recurrence6B0A2Row6Band6
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block6
  ring



theorem recurrence6B0A2Band7_eq :
    recurrence6B0A2Band7 = remainder7Coefficient0TimesRemainder6Coefficient2Block7 := by
  unfold recurrence6B0A2Band7 recurrence6B0A2Row0Band7 recurrence6B0A2Row1Band7
  unfold recurrence6B0A2Row2Band7 recurrence6B0A2Row3Band7 recurrence6B0A2Row4Band7
  unfold recurrence6B0A2Row5Band7 recurrence6B0A2Row6Band7 recurrence6B0A2Row7Band7
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block7
  ring



theorem recurrence6B0A2Band8_eq :
    recurrence6B0A2Band8 = remainder7Coefficient0TimesRemainder6Coefficient2Block8 := by
  unfold recurrence6B0A2Band8 recurrence6B0A2Row0Band8 recurrence6B0A2Row1Band8
  unfold recurrence6B0A2Row2Band8 recurrence6B0A2Row3Band8 recurrence6B0A2Row4Band8
  unfold recurrence6B0A2Row5Band8 recurrence6B0A2Row6Band8 recurrence6B0A2Row7Band8
  unfold recurrence6B0A2Row8Band8 remainder7Coefficient0TimesRemainder6Coefficient2Block8
  ring



theorem recurrence6B0A2Band9_eq :
    recurrence6B0A2Band9 = remainder7Coefficient0TimesRemainder6Coefficient2Block9 := by
  unfold recurrence6B0A2Band9 recurrence6B0A2Row0Band9 recurrence6B0A2Row1Band9
  unfold recurrence6B0A2Row2Band9 recurrence6B0A2Row3Band9 recurrence6B0A2Row4Band9
  unfold recurrence6B0A2Row5Band9 recurrence6B0A2Row6Band9 recurrence6B0A2Row7Band9
  unfold recurrence6B0A2Row8Band9 recurrence6B0A2Row9Band9
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block9
  ring



theorem recurrence6B0A2Band10_eq :
    recurrence6B0A2Band10 = remainder7Coefficient0TimesRemainder6Coefficient2Block10 := by
  unfold recurrence6B0A2Band10 recurrence6B0A2Row0Band10 recurrence6B0A2Row1Band10
  unfold recurrence6B0A2Row2Band10 recurrence6B0A2Row3Band10 recurrence6B0A2Row4Band10
  unfold recurrence6B0A2Row5Band10 recurrence6B0A2Row6Band10 recurrence6B0A2Row7Band10
  unfold recurrence6B0A2Row8Band10 recurrence6B0A2Row9Band10
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block10
  ring



theorem recurrence6B0A2Band11_eq :
    recurrence6B0A2Band11 = remainder7Coefficient0TimesRemainder6Coefficient2Block11 := by
  unfold recurrence6B0A2Band11 recurrence6B0A2Row0Band11 recurrence6B0A2Row1Band11
  unfold recurrence6B0A2Row2Band11 recurrence6B0A2Row3Band11 recurrence6B0A2Row4Band11
  unfold recurrence6B0A2Row5Band11 recurrence6B0A2Row6Band11 recurrence6B0A2Row7Band11
  unfold recurrence6B0A2Row8Band11 recurrence6B0A2Row9Band11
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block11
  ring

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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band6 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block6) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band7 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block7) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band8 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block8) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band9 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block9) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band10 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block10) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band11 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2Block11) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band6_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band7_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band8_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band9_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band10_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B0A2Band11_eq⟩
#print axioms solution
