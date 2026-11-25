-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:08.436799+00:00
-- url     : https://prove2.me/submissions/9f99552d-a738-4ea2-b623-85ee910e77ca

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalSupportExists
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSupport_exists_reverse_intertwiner
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_jacquetAll
import Theorems.Thm_PI_SerBridgeGLW_isConstituent_hc_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSupport
namespace GlobalTheory.CompanionTheory.TyFinSupport
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SupportExistsAll := by
  intro K _ _ _ ι _ _ _ τ hτ
  obtain ⟨s, b, lam, Φ, hb, hlam, hΦ, heq⟩ := GlobalTheory.CompanionTheory.TyFinJacquet.jacquetAll K ι τ hτ
  obtain ⟨ψ, hψ, hψeq⟩ := exists_reverse_intertwiner (PI.SerBridgeGLW.inflRep K b lam)
    (τ.ρ.comp (parab K b).subtype) Φ hΦ heq
  exact ⟨s, b, lam, hb, hlam, (PI.SerBridgeGLW.isConstituent_hc_iff K b lam τ).mpr ⟨ψ, hψ, hψeq⟩⟩
end GlobalTheory.CompanionTheory.TyFinSupport
