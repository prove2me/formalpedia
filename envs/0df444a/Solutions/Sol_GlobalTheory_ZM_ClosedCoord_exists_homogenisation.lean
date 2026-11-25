-- Prove2me | solution 1 for GlobalTheory.ZM.ClosedCoord.exists_homogenisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:30.400614+00:00
-- url     : https://prove2.me/submissions/f9e0a3e3-5e33-42b3-91a9-132c98b4c39f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProjectiveCoordinateRepresentationClosedSubsch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ClosedCoord
open MvPolynomial
namespace GlobalTheory.ZM.ClosedCoord
theorem _root_.solution {R σ : Type} [CommRing R] (a : σ) (F : MvPolynomial σ R) :
    ∃ (d : ℕ) (G : MvPolynomial σ R),
      (∀ (R' : Type) [CommRing R'] (β : R →+* R') (u : R') (w : σ → R'),
        eval₂ β (fun j => u * w j) G = u ^ d * eval₂ β w G) ∧
      ∀ (R' : Type) [CommRing R'] (β : R →+* R') (w : σ → R'), w a = 1 → eval₂ β w G = eval₂ β w F := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, fun _ _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
  | add p q hp hq =>
    obtain ⟨d, G, h1, h2⟩ := hp
    obtain ⟨d', G', h1', h2'⟩ := hq
    refine ⟨d + d', X a ^ d' * G + X a ^ d * G', fun R' _ β u w => ?_, fun R' _ β w hw => ?_⟩
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, h1, h1']; ring
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, h2 _ β w hw, h2' _ β w hw, hw]; ring
  | mul_X p n hp =>
    obtain ⟨d, G, h1, h2⟩ := hp
    refine ⟨d + 1, G * X n, fun R' _ β u w => ?_, fun R' _ β w hw => ?_⟩
    · simp only [eval₂_mul, eval₂_X, h1]; ring
    · simp only [eval₂_mul, eval₂_X, h2 _ β w hw]
end GlobalTheory.ZM.ClosedCoord
