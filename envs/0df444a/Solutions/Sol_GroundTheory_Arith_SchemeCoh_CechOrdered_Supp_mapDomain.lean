-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.Supp.mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:32.849904+00:00
-- url     : https://prove2.me/submissions/7fa448f4-05bc-41e9-bf73-1eccbe60475f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable (ι : Type w)
variable {ι}
variable {q : ℕ} {Q Q' : (Fin (q + 1) → ι) → Prop}
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
namespace Supp
theorem _root_.solution {r : ℕ} {R : (Fin (r + 1) → ι) → Prop}
    (f : (Fin (q + 1) → ι) → (Fin (r + 1) → ι)) {z : Chain ι q} (hz : Supp Q z)
    (h : ∀ t, Q t → R (f t)) : Supp R (Finsupp.mapDomain f z) := by
  classical
  intro s hs
  rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply] at hs
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  by_cases hft : f t = s
  · exact hft ▸ h t (hz t (Finsupp.mem_support_iff.mp ht))
  · simp [hft] at hne
end Supp
end GroundTheory.Arith.SchemeCoh.CechOrdered
