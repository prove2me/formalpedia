-- Prove2me | solution 1 for N25.cuspDiamondEigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:07.301498+00:00
-- url     : https://prove2.me/submissions/46ad92c0-26d9-40ce-9b6c-0d1bbbf2aff0

import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

namespace N25

open AlgebraicCurve Endgame

/-- The coefficient-six principal relation on the selected rational cusp orbit
forces the label-thirteen eigenvalue five and the inverse label-two eigenvalue 57. -/
theorem _root_.solution
    (hcoeff : pointDiff (pG25 0) (pG25 2)
        ((pG25_degree 0).trans (pG25_degree 2).symm) =
      (6 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm))
    (h71 : (71 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) = 0) :
    let t : J := pointDiff (pG25 0) (pG25 1)
      ((pG25_degree 0).trans (pG25_degree 1).symm)
    gamma t = (5 : ℤ) • t ∧
      ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime 2 (by decide)) t =
        (57 : ℤ) • t := by
  let t : J := pointDiff (pG25 0) (pG25 1)
    ((pG25_degree 0).trans (pG25_degree 1).symm)
  have hm0 : SemilinearAut.ofAlgAut gammaF25 • pG25 0 = pG25 1 := by
    simp [pG25]
  have hm1 : SemilinearAut.ofAlgAut gammaF25 • pG25 1 = pG25 2 := by
    simp [pG25, pow_two, mul_smul]
  have hsum : gamma t + t = pointDiff (pG25 0) (pG25 2)
      ((pG25_degree 0).trans (pG25_degree 2).symm) := by
    change SemilinearAut.ofAlgAut gammaF25 •
      Pic0.mk (K := Qbar) (F := FG) _ + Pic0.mk (K := Qbar) (F := FG) _ = _
    rw [SemilinearAut.pic0_smul_mk, ← Pic0.mk_add]
    apply congrArg (Pic0.mk (K := Qbar) (F := FG))
    apply Subtype.ext
    change SemilinearAut.ofAlgAut gammaF25 •
        (Finsupp.single (pG25 0) (1 : ℤ) - Finsupp.single (pG25 1) 1) +
      (Finsupp.single (pG25 0) 1 - Finsupp.single (pG25 1) 1) = _
    rw [smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, hm0, hm1]
    abel
  have hg : gamma t = (5 : ℤ) • t := by
    rw [hcoeff] at hsum
    apply add_right_cancel (b := t)
    calc gamma t + t = (6 : ℤ) • t := hsum
      _ = (5 : ℤ) • t + t := by rw [show (6 : ℤ) = 5 + 1 by norm_num, add_zsmul, one_zsmul]
  refine ⟨hg, ?_⟩
  let d := ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime 2 (by decide))
  have hinv (x : J) : gamma (d x) = x := by
    change ModularCurve.diamondHBar 25 H25 _ (ModularCurve.diamondHBar 25 H25 _ x) = x
    rw [← ModularCurve.diamondHBar_mul]
    have hu : ZMod.unitOfCoprime 13 (by decide) * ZMod.unitOfCoprime 2 (by decide) =
        (1 : (ZMod 25)ˣ) := by decide
    rw [hu]
    exact ModularCurve.diamondHBar_apply_eq_self_of_mem 25 H25 1 H25.one_mem x
  have hginv (x : J) : d (gamma x) = x := by
    change ModularCurve.diamondHBar 25 H25 _ (ModularCurve.diamondHBar 25 H25 _ x) = x
    rw [← ModularCurve.diamondHBar_mul]
    have hu : ZMod.unitOfCoprime 2 (by decide) * ZMod.unitOfCoprime 13 (by decide) =
        (1 : (ZMod 25)ˣ) := by decide
    rw [hu]
    exact ModularCurve.diamondHBar_apply_eq_self_of_mem 25 H25 1 H25.one_mem x
  have hi : Function.Injective gamma := fun x y h => by
    simpa only [hginv] using congrArg d h
  apply hi
  rw [hinv, map_zsmul, hg, smul_smul]
  change t = (57 * 5 : ℤ) • t
  calc t = t + (4 : ℤ) • ((71 : ℤ) • t) := by rw [h71]; simp
    _ = (1 + 4 * 71 : ℤ) • t := by rw [smul_smul, add_zsmul, one_zsmul]
    _ = (57 * 5 : ℤ) • t := by norm_num

end N25
