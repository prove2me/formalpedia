-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Iwasawa.map_mem_GLint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:03:27.37015+00:00
-- url     : https://prove2.me/submissions/9715eb04-f3e5-4f8e-b1d4-7ddb6c11f7ee

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Iwasawa
namespace GlobalTheory.CompanionTheory.QL.Iwasawa
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (k : GL (Fin n) (ValuativeRel.valuation F).valuationSubring) :
    GeneralLinearGroup.map (algebraMap (ValuativeRel.valuation F).valuationSubring F) k ∈
      GLint 𝒪[F] n := by
  have key : ∀ (u : GL (Fin n) (ValuativeRel.valuation F).valuationSubring),
      IsInt 𝒪[F] ((GeneralLinearGroup.map
        (algebraMap (ValuativeRel.valuation F).valuationSubring F) u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by
    intro u i j
    have h := (u.1 i j).2
    exact h
  refine ⟨key k, ?_⟩
  rw [← map_inv]
  exact key k⁻¹
end GlobalTheory.CompanionTheory.QL.Iwasawa
