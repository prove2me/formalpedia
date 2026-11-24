-- Prove2me | solution 1 for GlobalTheory.Published.cc_det_of_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:14:59.580305+00:00
-- url     : https://prove2.me/submissions/13737885-4d7c-4ad7-9ff6-023175fd45e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_det_map_cc

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
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) :
    cc G.det = G.det := by
  rw [← det_map_cc, ← Matrix.det_transpose G]
  congr 1
  ext a b
  exact hG a b
end GlobalTheory.Published
