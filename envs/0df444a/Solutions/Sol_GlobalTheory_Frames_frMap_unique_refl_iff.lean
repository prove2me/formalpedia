-- Prove2me | solution 1 for GlobalTheory.Frames.frMap_unique_refl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:50:59.981819+00:00
-- url     : https://prove2.me/submissions/a22d3e00-809a-4d94-99a0-add6c0ab6580

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FramedPointBaseChangeUniqueReflIff
import Theorems.Thm_GlobalTheory_Frames_frMapUniq_scal_one
import Theorems.Thm_GlobalTheory_Frames_frMapUniq_chart_le
import Theorems.Thm_GlobalTheory_Frames_frMapUniq_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), (∀ z z' : FrPt Xo c T, FrMap φ y z → FrMap φ y z' → z = z') ∧ FrMap (AlgHom.id c.F S) y y ∧ ∀ z : FrPt Xo c T, FrMap φ y z ↔ (z.x = spMap φ.toRingHom ≫ y.x ∧ (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s) := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y
  refine ⟨?_, frMapUniq_refl y, fun z => ?_⟩
  · rintro ⟨x, xo, u, t, e, b, s, g⟩ ⟨x', xo', u', t', e', b', s', g'⟩ ⟨hx, hu, pm, hs, hf, ha⟩
      ⟨hx', hu', pm', hs', hf', ha'⟩
    dsimp only at hx hu hx' hu' pm pm' hs hf ha hs' hf' ha'
    have h1 : x = x' := hx.trans hx'.symm
    subst h1
    have h2 : u = u' := by
      funext τ i
      exact (hu τ i).trans (hu' τ i).symm
    subst h2
    have h3 : pm = pm' := by
      apply pullback.hom_ext
      · exact hf.trans hf'.symm
      · exact hs.trans hs'.symm
    subst h3
    have h4 : s = s' := by
      have : s.f = s'.f := by
        funext i
        have h := frMapUniq_chart_le pm hs i
        exact (ha i h).symm.trans (ha' i h)
      cases s; cases s'
      congr
    subst h4
    rfl
  · have k : ∀ i : (PPx y.x).ι, scal y.x (1 : S) i * y.s.f i = y.s.f i := fun i => by
      rw [frMapUniq_scal_one, _root_.one_mul]
    constructor
    · rintro ⟨hx, hu, pm, hs, hf, ha⟩
      exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).trans (ha i h)⟩
    · rintro ⟨hx, hu, pm, hs, hf, ha⟩
      exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).symm.trans (ha i h)⟩
end GlobalTheory.Frames
