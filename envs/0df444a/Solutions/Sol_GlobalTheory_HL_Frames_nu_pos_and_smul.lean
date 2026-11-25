-- Prove2me | solution 1 for GlobalTheory.HL.Frames.nu_pos_and_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:29.787681+00:00
-- url     : https://prove2.me/submissions/9741d358-692c-4501-b20a-de9fea64edeb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StabilizerCommensurableInvVolumeSmulComplementStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InfStabilizerSmulEqConj
import Theorems.Thm_GlobalTheory_HL_inf_stabilizer_smul_eq_conj
import Theorems.Thm_GlobalTheory_HL_invVol_conj_of_invVol_conj
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
import Theorems.Thm_GlobalTheory_T_hermitian_double_coset_term_basic_facts
import Theorems.Thm_GlobalTheory_T_stabilizer_commensurable_invVolume_smul_complement


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
namespace Frames
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 < S.nu d ∧ ∀ h ∈ S.H0, S.nu (h • d) = S.nu d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨hv, hd⟩ := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement L r k S
  obtain ⟨d1, d2⟩ := hd d Λ hT
  have hSD := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1
  obtain ⟨l1, l2, l3⟩ := hv Λ hSD.1
  refine ⟨(invVol_mul_pos_le_conj _ _ _ d1 d2 d1 d2).2.1, fun h hh => ?_⟩
  have := l3 h hh
  rw [inf_stabilizer_smul_eq_conj _ hh] at this
  unfold Frames.nu
  rw [inf_stabilizer_smul_eq_conj _ hh]
  exact invVol_conj_of_invVol_conj _ _ _ h l1 l2 d1 d2 this
end Frames
end GlobalTheory.HL
