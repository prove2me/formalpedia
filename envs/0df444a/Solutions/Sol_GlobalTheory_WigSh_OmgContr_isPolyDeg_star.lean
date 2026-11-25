-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgContr.isPolyDeg_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:52:05.091925+00:00
-- url     : https://prove2.me/submissions/07dd797a-8db7-401f-a07e-92f294e5488d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegPrW
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgMulLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HpkConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsPolyDegStar
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
namespace GlobalTheory.WigSh.OmgContr
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}
private lemma star_eval_eq_eval₂_starRingEnd {σ : Type*} (x : σ → ℂ) (q : MvPolynomial σ ℂ) :
    star (MvPolynomial.eval x q) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun v => star (x v)) q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p v hp => simp [hp]
end GlobalTheory.WigSh.OmgContr
namespace GlobalTheory.WigSh
open OmgContr
end GlobalTheory.WigSh
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmgContr
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}
namespace GlobalTheory.WigSh.OmgContr
theorem _root_.solution {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (le_trans (by
        unfold MvPolynomial.totalDegree
        exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)) hq)
  · intro g
    show star (P g) = _
    rw [hP g, MvPolynomial.eval_rename, MvPolynomial.eval_map, star_eval_eq_eval₂_starRingEnd]
    congr 1
    funext v
    cases v <;> simp
end GlobalTheory.WigSh.OmgContr
