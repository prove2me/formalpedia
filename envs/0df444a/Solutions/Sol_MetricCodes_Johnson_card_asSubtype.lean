-- Prove2me | solution 1 for MetricCodes.Johnson.card_asSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/6e324dec-4136-49a6-81b5-0e53e54aa531

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    (asSubtype C hweight).card = C.card := by
  classical
  unfold asSubtype
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun q : JohnsonSphere n w => q.val) hxy
end MetricCodes.Johnson
