-- Prove2me | solution 1 for N25.Endgame.red_pointDiff25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:02.475907+00:00
-- url     : https://prove2.me/submissions/558f1ba9-d57d-4a37-89ce-3128671068b8

import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_redPlace25_degree
import Definitions.Def_N25_Endgame
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace N25.Endgame

theorem _root_.solution
    {ℓ : ℕ} [Fact ℓ.Prime] (D : RedDatum25 ℓ)
    (P Q : GPlace) (hdeg : P.deg = Q.deg) :
    red25 D (pointDiff P Q hdeg) =
      pointDiff (redPlace25 D P) (redPlace25 D Q)
        ((redPlace25_degree D P).trans
          (hdeg.trans (redPlace25_degree D Q).symm)) := by
  let : Algebra (κ D.A) (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25) :=
    (ModularCurve.qExpFunctionFieldC (κ D.A) Γ25).algebra
  change ModularCurve.reductionQExpModL D.A Γ25 (pointDiff P Q hdeg) = _
  unfold pointDiff
  rw [ModularCurve.reductionQExpModL_mk D.hred]
  apply congrArg (AlgebraicCurve.Pic0.mk (K := κ D.A) (F := FSpecial D.A))
  apply Subtype.ext
  change Finsupp.mapDomain (redPlace25 D)
    (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1) = _
  rw [← Finsupp.mapDomain.addMonoidHom_apply, map_sub]
  simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

end N25.Endgame
