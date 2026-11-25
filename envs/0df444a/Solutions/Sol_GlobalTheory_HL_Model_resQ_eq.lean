-- Prove2me | solution 1 for GlobalTheory.HL.Model.resQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:34.308541+00:00
-- url     : https://prove2.me/submissions/7ece7869-2321-40bd-b23c-f24d0469647d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) ∧ 2 ≤ resQ ϖ := by
  have hm : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp h
  have e : resQ ϖ = Nat.card (IsLocalRing.ResidueField 𝒪[F]) := by
    unfold resQ
    rw [← hm]
    rfl
  refine ⟨e, ?_⟩
  rw [e]
  exact Finite.one_lt_card
end GlobalTheory.HL.Model
