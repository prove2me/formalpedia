-- Prove2me | solution 1 for GlobalTheory.AnArc.im_Hw_Pw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:00:15.859045+00:00
-- url     : https://prove2.me/submissions/893339bd-18a5-4e28-bb11-30622c4229f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_H_im_symm
import Theorems.Thm_GlobalTheory_AnArc_torusProj_Pw_im
import Theorems.Thm_GlobalTheory_AnArc_torusProj_Pw_re
import Theorems.Thm_GlobalTheory_AnArc_dualForm_conj
import Theorems.Thm_GlobalTheory_AnArc_dualForm_BwC
import Theorems.Thm_GlobalTheory_AnArc_dualForm_im_of_real
import Theorems.Thm_GlobalTheory_AnArc_Hw_apply
import Theorems.Thm_GlobalTheory_AnArc_EF_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {w : ℂ} (hw : (A.BwMat w).PosDef) (a b : A.La) :
    (A.Hw w (A.Pw w a) (A.Pw w b)).im = A.EF a b := by
  have hre : ∀ (v : A.La) x, ((A.torusProj (A.Pw w v) - Complex.I • A.BwC w v.y) x).im = 0 := fun v x => by
    simp [torusProj_Pw_im]
  have h1 := A.dualForm_im_of_real w (hre a) (hre b)
  have h2 : A.dualForm w (A.BwC w a.y) (A.torusProj (A.Pw w b)) = starRingEnd ℂ (A.torusProj (A.Pw w b) a.y) := by
    rw [← dualForm_conj, A.dualForm_BwC hw]
  simp only [map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
    A.dualForm_BwC hw, h2, smul_eq_mul] at h1
  simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im, RingHom.id_apply, torusProj_Pw_re, torusProj_Pw_im, BwC_apply, Complex.ofReal_re,
    Complex.ofReal_im] at h1
  rw [Hw_apply, Complex.add_im, EF_apply, Pw_snd, Pw_snd]
  simp only [H_add_left, H_add_right, Complex.add_im]
  push_cast
  rw [Ef_eq_im]
  rw [A.T_symm b.y a.y, A.be_symm b.y a.y, A.H_im_symm (A.ct b.y) (A.ct a.y), A.H_im_symm b.l (A.ct a.y)] at h1
  linarith
end GlobalTheory.AnArc
