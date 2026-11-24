-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.isIntegral_prod_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:59:01.597742+00:00
-- url     : https://prove2.me/submissions/26b62417-26c4-4f6f-b40d-3bcfe9db2580

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [Algebra O A₁] [CommRing A₂] [Algebra O A₂]
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution (t : A₁ × A₂) : IsIntegral O t ↔ IsIntegral O t.1 ∧ IsIntegral O t.2 :=
  ⟨fun h => ⟨h.map (AlgHom.fst O A₁ A₂), h.map (AlgHom.snd O A₁ A₂)⟩, fun h => IsIntegral.pair h.1 h.2⟩
end GlobalTheory.UnitLemma.ProdCount
