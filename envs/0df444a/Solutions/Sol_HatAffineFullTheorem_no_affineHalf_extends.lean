-- Prove2me | solution 1 for HatAffineFullTheorem.no_affineHalf_extends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:47:10.461521+00:00
-- url     : https://prove2.me/submissions/87eb523d-c7aa-4545-acd8-0f0e834e705c

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
import Theorems.Thm_HatAffineFullTheorem_no_extends_of_affineRealizes

set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
attribute [local instance] HatAffineFullTheorem._p2m_local_instance_f43eda1e4a_11
namespace HatAffineFullTheorem
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 ≤ m) (hq : 4 ≤ Fintype.card K)
    (F :
      (Fin m → K) →
      Fin (Fintype.card K - 1) → K)
    (hF : HatAffineGeneral.AffineHalf F) :
    ¬ HatAffineGeneral.Extends F := by
  obtain ⟨A, b, hrealize⟩ := hF
  exact no_extends_of_affineRealizes hm hq A b F hrealize
end HatAffineFullTheorem
