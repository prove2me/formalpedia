-- Prove2me | solution 1 for GlobalTheory.EabClass.eh_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:16:00.326687+00:00
-- url     : https://prove2.me/submissions/2c1f2dad-37d4-4c33-ab91-bb7cb8c2bb7b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OperatorEabPreservesSmoothClassCC
import Theorems.Thm_GlobalTheory_EabClass_rdV_class
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart1_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart2_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
open GlobalTheory GlobalTheory.EabClass
namespace GlobalTheory.EabClass
theorem _root_.solution : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (A : ℝ) (a b : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (B.CkOn ⊤ (B.GV k r) (Q.EH k r a b f) ∧ ∀ m : ℕ, B.InCC (A) m (Q.EH k r a b f)) := by
  intro k r Wp Wq _ _ _ _ _ _ A a b f hf
  have h1 := rdV_class (X := hpart1 (Hpk k r) (Matrix.single a b 1)) (Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _) hf
  have h2 := rdV_class (X := hpart2 (Hpk k r) (Matrix.single a b 1)) (Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _) hf
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h1.1 (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul Complex.I h2.1), fun m => ?_⟩
  obtain ⟨c₁, hc₁⟩ := h1.2 m
  obtain ⟨c₂, hc₂⟩ := h2.2 m
  exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul Complex.I hc₂)⟩
end GlobalTheory.EabClass
