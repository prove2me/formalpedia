-- Prove2me | solution 1 for GlobalTheory.CuspCharCompare.isSimpleModule_of_finrank_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:37.065875+00:00
-- url     : https://prove2.me/submissions/32ac1804-a565-4df1-9daf-38ca4bb73873

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_IrreducibleCharacters_CuspidalCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsSimpleModuleOfFinrankEnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspCharCompare
open CuspElliptic GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open scoped MonoidAlgebra
variable {G : Type} [Group G]
namespace GlobalTheory.CuspCharCompare
theorem _root_.solution {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module R M]
    [Module ℂ M] [IsScalarTower ℂ R M] [SMulCommClass R ℂ M] [IsSemisimpleModule R M]
    (h : Module.finrank ℂ (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _
end GlobalTheory.CuspCharCompare
