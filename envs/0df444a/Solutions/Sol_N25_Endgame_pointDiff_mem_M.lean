-- Prove2me | solution 1 for N25.Endgame.pointDiff_mem_M
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:08.884277+00:00
-- url     : https://prove2.me/submissions/50ad736e-4fd7-4274-b224-de7205ae7f5f

import Definitions.Def_N25_PointDifference

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

/-- A difference of arithmetic-rational geometric places is Galois fixed. -/
theorem _root_.solution
    (P Q : GPlace) (hP : IsRationalGeomPlace P)
    (hQ : IsRationalGeomPlace Q) :
    pointDiff P Q (hP.1.trans hQ.1.symm) ∈ N25.M := by
  change ∀ σ : N25.Gal, σ • pointDiff P Q _ = pointDiff P Q _
  intro σ
  rw [ModularCurve.galois_smul_pic0_def, pointDiff,
    AlgebraicCurve.SemilinearAut.pic0_smul_mk]
  apply congrArg AlgebraicCurve.Pic0.mk
  apply Subtype.ext
  change ModularCurve.arithmeticGalois FQ σ •
    (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1) = _
  rw [smul_sub, AlgebraicCurve.SemilinearAut.smul_single,
    AlgebraicCurve.SemilinearAut.smul_single, hP.2 σ, hQ.2 σ]

end N25.Endgame
