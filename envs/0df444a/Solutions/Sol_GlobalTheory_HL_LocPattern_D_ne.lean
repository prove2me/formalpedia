-- Prove2me | solution 1 for GlobalTheory.HL.LocPattern.D_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:54.793542+00:00
-- url     : https://prove2.me/submissions/1274d730-674d-45ab-967b-f20c605647e4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalCommonStabiliserBlockUnitriangularOnFrame
import Theorems.Thm_GlobalTheory_HL_LocPattern_zh_loc
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocPattern
open GlobalTheory.HL.Eichler
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.LocPattern
theorem _root_.solution (l : Fin (r + 2)) (h : G.D l ≠ 0) : (G.S p).D l ≠ 0 := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  set e : Fin l → Fin (r + 1) := Fin.castLE (Nat.lt_succ_iff.mp l.2) with he
  let d : Fin l → (A.loc p).Ep := fun i =>
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (e i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp)
  have hsub : (G.S p).Zh.submatrix e e =
      Matrix.diagonal d * (G.Zh.submatrix e e).map (A.loc p).ιE * Matrix.diagonal d := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, zh_loc, d]
    ring
  have hmap : ((G.Zh.submatrix e e).map (A.loc p).ιE).det = (A.loc p).ιE (G.D l) :=
    (RingHom.map_det _ _).symm
  have hD : (G.S p).D l = (∏ i, d i) * (A.loc p).ιE (G.D l) * (∏ i, d i) := by
    show ((G.S p).Zh.submatrix e e).det = _
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hmap]
  have hu : IsUnit (∏ i, d i) := by
    rw [IsUnit.prod_univ_iff]
    intro i
    exact (Units.isUnit _).map _
  rw [hD]
  intro h0
  rw [hu.mul_left_eq_zero, hu.mul_right_eq_zero] at h0
  exact h ((map_eq_zero_iff _ (A.loc p).ιE.injective).1 h0)
end GlobalTheory.HL.LocPattern
