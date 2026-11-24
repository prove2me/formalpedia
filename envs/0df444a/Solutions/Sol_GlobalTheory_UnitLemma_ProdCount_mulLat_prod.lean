-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.mulLat_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:59:04.261145+00:00
-- url     : https://prove2.me/submissions/2a76fe42-2585-470c-b14a-dd2b7d5ed613

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
theorem _root_.solution (t : A₁ × A₂) (L₁ : Submodule O A₁) (L₂ : Submodule O A₂) :
    mulLat O t (L₁.prod L₂) = (mulLat O t.1 L₁).prod (mulLat O t.2 L₂) := by
  ext y
  simp only [mulLat, Submodule.mem_map, Submodule.mem_prod, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨z.1, h1, rfl⟩, ⟨z.2, h2, rfl⟩⟩
  · rintro ⟨⟨a, ha, e1⟩, ⟨b, hb, e2⟩⟩
    exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext e1 e2⟩
end GlobalTheory.UnitLemma.ProdCount
