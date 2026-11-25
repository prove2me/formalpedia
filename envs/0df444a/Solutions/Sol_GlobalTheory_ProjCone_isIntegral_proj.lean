-- Prove2me | solution 1 for GlobalTheory.ProjCone.isIntegral_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:26:46.054335+00:00
-- url     : https://prove2.me/submissions/75157ca6-ad71-4425-892b-fd7429635ff4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.ProjCone
namespace GlobalTheory.ProjCone
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A] (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜]
    {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) (hf0 : f ≠ 0) : IsIntegral (Proj 𝒜) := by
  have hred : IsReduced (Proj 𝒜) := by
    have (x : Proj 𝒜) : _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) := by
      let x' : ProjectiveSpectrum 𝒜 := x
      have h1 : _root_.IsReduced (HomogeneousLocalization.AtPrime 𝒜 x'.asHomogeneousIdeal.toIdeal) :=
        isReduced_of_injective (algebraMap _ (Localization.AtPrime x'.asHomogeneousIdeal.toIdeal))
          (HomogeneousLocalization.val_injective _)
      exact isReduced_of_injective (Proj.stalkIso' 𝒜 x') (Proj.stalkIso' 𝒜 x').injective
    exact isReduced_of_isReduced_stalk _
  let η : ProjectiveSpectrum 𝒜 := ⟨⊥, Ideal.isPrime_bot, fun h => hf0 (by
    have : f ∈ HomogeneousIdeal.irrelevant 𝒜 := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hf hm.ne']
    exact h this)⟩
  have hcl : closure ({η} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η y).1 (by
      show η.asHomogeneousIdeal ≤ y.asHomogeneousIdeal
      exact bot_le)
  have hirr : IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
    have := (isIrreducible_singleton (x := η)).closure
    rw [hcl] at this
    exact (irreducibleSpace_def _).2 this
  have : IrreducibleSpace (Proj 𝒜) := hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end GlobalTheory.ProjCone
