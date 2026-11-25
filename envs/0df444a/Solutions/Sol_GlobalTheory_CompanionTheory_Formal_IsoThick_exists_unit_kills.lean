-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:28:46.923841+00:00
-- url     : https://prove2.me/submissions/70f06c47-317b-4cec-ba62-c82f2d48c8fa

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings
import Theorems.Thm_KrullIntersectionUnits_KrullIntersectionLemmas_GlobalTheory_CompanionTheory_Formal_IsoThick_exists_unit_kills


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick
namespace GlobalTheory.CompanionTheory.Formal.IsoThick
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [IsNoetherianRing A] (φ : A →+* B)
    (hφ : φ.Finite) (J : Ideal A) (hsurj : ∀ b, ∃ a, b - φ a ∈ J.map φ)
    (hinj : ∀ a, φ a = 0 → ∀ n : ℕ, a ∈ J ^ n) :
    ∃ s : A, s - 1 ∈ J ∧ (∀ k, φ k = 0 → s * k = 0) ∧ ∀ b, ∃ a, φ s * b = φ a := by
  first | exact @KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills | exact KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills | (intros; apply KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills <;> assumption)
end GlobalTheory.CompanionTheory.Formal.IsoThick
