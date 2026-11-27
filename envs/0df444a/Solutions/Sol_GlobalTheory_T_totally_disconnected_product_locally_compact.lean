-- Prove2me | solution 1 for GlobalTheory.T.totally_disconnected_product_locally_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:27.420884+00:00
-- url     : https://prove2.me/submissions/3f0c5ba9-2988-4810-be45-68ab780a9087

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotallyDisconnectedProductLocallyCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotallyDisconnectedProductLocallyCompactStatement
import Theorems.Thm_GlobalTheory_SBProdExt_exists_linear_bijOn_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {P Q P' Q' Z Z' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q] [TotallyDisconnectedSpace Q]
    [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P'] [TotallyDisconnectedSpace P']
    [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q'] [TotallyDisconnectedSpace Q']
    [TopologicalSpace Z] [TopologicalSpace Z'] (eZ : Z ≃ₜ P × Q) (eZ' : Z' ≃ₜ P' × Q')
    (f : (P → ℂ) →ₗ[ℂ] (P' → ℂ)) (g : (Q → ℂ) →ₗ[ℂ] (Q' → ℂ)),
    Set.BijOn f (GlobalTheory.WeilM.SB P : Set (P → ℂ)) (GlobalTheory.WeilM.SB P' : Set (P' → ℂ)) →
    Set.BijOn g (GlobalTheory.WeilM.SB Q : Set (Q → ℂ)) (GlobalTheory.WeilM.SB Q' : Set (Q' → ℂ)) →
    ∃ h : (Z → ℂ) →ₗ[ℂ] (Z' → ℂ), Set.BijOn h (GlobalTheory.WeilM.SB Z : Set (Z → ℂ)) (GlobalTheory.WeilM.SB Z' : Set (Z' → ℂ)) ∧
      ∀ a ∈ GlobalTheory.WeilM.SB P, ∀ b ∈ GlobalTheory.WeilM.SB Q,
        h (fun z => a (eZ z).1 * b (eZ z).2) = fun z' => f a (eZ' z').1 * g b (eZ' z').2 := by
  first | exact @GlobalTheory.SBProdExt.exists_linear_bijOn_prod | exact GlobalTheory.SBProdExt.exists_linear_bijOn_prod | (intros; apply GlobalTheory.SBProdExt.exists_linear_bijOn_prod <;> assumption)
end _root_.GlobalTheory.T
