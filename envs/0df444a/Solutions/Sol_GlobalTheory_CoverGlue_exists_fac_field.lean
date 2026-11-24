-- Prove2me | solution 1 for GlobalTheory.CoverGlue.exists_fac_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:29.585501+00:00
-- url     : https://prove2.me/submissions/cb7012d9-22d9-4a83-9909-ce94fe64f51f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionBasisGeometricFibresOfOpenCover
import Theorems.Thm_GlobalTheory_CoverGlue_exists_mem


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
open GlobalTheory GlobalTheory.CoverGlue
namespace GlobalTheory.CoverGlue
theorem _root_.solution {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) (K : Type) [Field K]
    (x : Sp K ⟶ S) : ∃ (i : I) (x' : Sp K ⟶ (U i).toScheme), x' ≫ (U i).ι = x := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  obtain ⟨i, hi⟩ := exists_mem hU (x p)
  have hr : Set.range x.base ⊆ Set.range (U i).ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : q = p := Subsingleton.elim (α := PrimeSpectrum K) q p
    subst hq
    exact hi
  exact ⟨i, IsOpenImmersion.lift (U i).ι x hr, IsOpenImmersion.lift_fac _ _ _⟩
end GlobalTheory.CoverGlue
