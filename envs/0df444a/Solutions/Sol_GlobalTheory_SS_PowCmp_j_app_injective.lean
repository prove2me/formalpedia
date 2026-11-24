-- Prove2me | solution 1 for GlobalTheory.SS.PowCmp.j_app_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:14.83159+00:00
-- url     : https://prove2.me/submissions/297e85e2-325a-453a-94af-ae9e1c4cc3b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PowCmp
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.PowCmp
theorem _root_.solution [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) :
    Function.Injective (M.j.app U).hom := by
  have := M.smooth
  have : IsDominant (spMap (algebraMap R K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsSchemeTheoreticallyDominant (pullback.fst M.Y.hom (spMap (algebraMap R K))) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K))).flip
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : IsSchemeTheoreticallyDominant M.j := by unfold Model.j; infer_instance
  have : QuasiCompact M.j := by unfold Model.j; infer_instance
  exact M.j.app_injective U
end GlobalTheory.SS.PowCmp
