-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_b1a1_band_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T22:19:13.726274+00:00
-- url     : https://prove2.me/submissions/315f0500-a4ca-455b-83f3-444c8b3d40d9

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData1
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneB1A1PartitionData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
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
  unfold recurrence6B1A1Band6 recurrence6B1A1Row0Band6 recurrence6B1A1Row1Band6
  unfold recurrence6B1A1Row2Band6 recurrence6B1A1Row3Band6 recurrence6B1A1Row4Band6
  unfold recurrence6B1A1Row5Band6 recurrence6B1A1Row6Band6
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block6
  ring



theorem recurrence6B1A1Band7_eq :
    recurrence6B1A1Band7 = remainder7Coefficient1TimesRemainder6Coefficient1Block7 := by
  unfold recurrence6B1A1Band7 recurrence6B1A1Row0Band7 recurrence6B1A1Row1Band7
  unfold recurrence6B1A1Row2Band7 recurrence6B1A1Row3Band7 recurrence6B1A1Row4Band7
  unfold recurrence6B1A1Row5Band7 recurrence6B1A1Row6Band7 recurrence6B1A1Row7Band7
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block7
  ring



theorem recurrence6B1A1Band8_eq :
    recurrence6B1A1Band8 = remainder7Coefficient1TimesRemainder6Coefficient1Block8 := by
  unfold recurrence6B1A1Band8 recurrence6B1A1Row0Band8 recurrence6B1A1Row1Band8
  unfold recurrence6B1A1Row2Band8 recurrence6B1A1Row3Band8 recurrence6B1A1Row4Band8
  unfold recurrence6B1A1Row5Band8 recurrence6B1A1Row6Band8 recurrence6B1A1Row7Band8
  unfold recurrence6B1A1Row8Band8 remainder7Coefficient1TimesRemainder6Coefficient1Block8
  ring



theorem recurrence6B1A1Band9_eq :
    recurrence6B1A1Band9 = remainder7Coefficient1TimesRemainder6Coefficient1Block9 := by
  unfold recurrence6B1A1Band9 recurrence6B1A1Row0Band9 recurrence6B1A1Row1Band9
  unfold recurrence6B1A1Row2Band9 recurrence6B1A1Row3Band9 recurrence6B1A1Row4Band9
  unfold recurrence6B1A1Row5Band9 recurrence6B1A1Row6Band9 recurrence6B1A1Row7Band9
  unfold recurrence6B1A1Row8Band9 recurrence6B1A1Row9Band9
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block9
  ring



theorem recurrence6B1A1Band10_eq :
    recurrence6B1A1Band10 = remainder7Coefficient1TimesRemainder6Coefficient1Block10 := by
  unfold recurrence6B1A1Band10 recurrence6B1A1Row0Band10 recurrence6B1A1Row1Band10
  unfold recurrence6B1A1Row2Band10 recurrence6B1A1Row3Band10 recurrence6B1A1Row4Band10
  unfold recurrence6B1A1Row5Band10 recurrence6B1A1Row6Band10 recurrence6B1A1Row7Band10
  unfold recurrence6B1A1Row8Band10 recurrence6B1A1Row9Band10
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block10
  ring



theorem recurrence6B1A1Band11_eq :
    recurrence6B1A1Band11 = remainder7Coefficient1TimesRemainder6Coefficient1Block11 := by
  unfold recurrence6B1A1Band11 recurrence6B1A1Row0Band11 recurrence6B1A1Row1Band11
  unfold recurrence6B1A1Row2Band11 recurrence6B1A1Row3Band11 recurrence6B1A1Row4Band11
  unfold recurrence6B1A1Row5Band11 recurrence6B1A1Row6Band11 recurrence6B1A1Row7Band11
  unfold recurrence6B1A1Row8Band11 recurrence6B1A1Row9Band11
  unfold remainder7Coefficient1TimesRemainder6Coefficient1Block11
  ring

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
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band6 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1Block6) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band7 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1Block7) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band8 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1Block8) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band9 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1Block9) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band10 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1Block10) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band11 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1Block11) := by
  exact ⟨MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band6_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band7_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band8_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band9_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band10_eq, MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6B1A1Band11_eq⟩
#print axioms solution
