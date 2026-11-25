-- Prove2me | solution 1 for GlobalTheory.exists_placeU_mem_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:28.768861+00:00
-- url     : https://prove2.me/submissions/278547e2-9707-4682-ac78-14a70bee6612

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPrimitiveIdempotentMapEqOne
import Theorems.Thm_GlobalTheory_exists_primitive_idempotent_map_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] (σ : OE →+* R) :
    ∃ w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE,
      σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e := by
  haveI : IsNoetherianRing (ℤ_[p] ⊗[ℤ] OE) :=
    IsNoetherianRing.of_finite ℤ_[p] _
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_primitive_idempotent_map_eq_one
    (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (p := p) σ).toRingHom
  exact ⟨⟨e, h1, h2, h3⟩, h4⟩
end GlobalTheory
