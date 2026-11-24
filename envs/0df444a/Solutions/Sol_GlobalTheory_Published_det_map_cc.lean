-- Prove2me | solution 1 for GlobalTheory.Published.det_map_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:13.959556+00:00
-- url     : https://prove2.me/submissions/6266ad82-0ffe-40cc-8b45-31745d3de2b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_map_cc_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Published
theorem _root_.solution (P : Matrix (Fin r) (Fin r) E) : (P.map cc).det = cc P.det := by
  rw [map_cc_eq, ← RingHom.map_det]; rfl
end GlobalTheory.Published
