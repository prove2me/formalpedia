-- Prove2me | solution 1 for GlobalTheory.SymOfZeroDivisor.appLE_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:32.766796+00:00
-- url     : https://prove2.me/submissions/135533e2-c712-4d54-b20f-e82f0311b3a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SymmetricLineBundleOfRegularSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymOfZeroDivisor
namespace GlobalTheory.SymOfZeroDivisor
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (a : Γ(X, W))
    (ha : ∀ (V : X.Opens) (h : V ≤ W), resG X h a ∈ nonZeroDivisors Γ(X, V))
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) : (f.appLE W V h).hom a ∈ nonZeroDivisors Γ(Y, V) := by
  have h' : f ''ᵁ V ≤ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact h hy
  have e : (f.appLE W V h).hom a = (f.appIso V).hom.hom (resG X h' a) := by
    rw [Scheme.Hom.appIso_hom']
    change _ = (X.presheaf.map (homOfLE h').op ≫ f.appLE _ _ _).hom a
    rw [Scheme.Hom.map_appLE]
  rw [e]
  rw [← MulEquivClass.map_nonZeroDivisors (f.appIso V).commRingCatIsoToRingEquiv]
  exact Submonoid.mem_map_of_mem _ (ha _ h')
end GlobalTheory.SymOfZeroDivisor
