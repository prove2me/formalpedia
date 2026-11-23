-- Prove2me | solution 1 for GlobalTheory.ArcConst.arcDet_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:21:50.277195+00:00
-- url     : https://prove2.me/submissions/acf3cdde-34fd-477d-8c68-0205bf3e76a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.ArcConst
theorem _root_.solution (Dw : Datum H) (K : Type) [Field K] : arcDet Dw K ≠ 0 := by
  classical
  intro h0
  have h := congrArg (MvPolynomial.eval (fun t : ArcLt Dw => if t.2.1 = t.2.2 then (1 : LaurentSeries K) else 0)) h0
  rw [arcDet, map_prod, map_zero, Finset.prod_eq_one] at h
  · exact one_ne_zero h
  · intro τ _
    rw [RingHom.map_det]
    convert Matrix.det_one (n := Fin (Dw.mult τ)) (R := LaurentSeries K)
    ext1 i k
    simp [Matrix.one_apply]
end GlobalTheory.ArcConst
