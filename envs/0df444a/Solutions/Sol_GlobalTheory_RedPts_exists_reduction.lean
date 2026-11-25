-- Prove2me | solution 1 for GlobalTheory.RedPts.exists_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:57.777942+00:00
-- url     : https://prove2.me/submissions/f90e97a4-c003-4651-9884-3cc9e2a0845a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOneOfPowOfClosedPoint
import Theorems.Thm_GlobalTheory_RedPts_toSec_left_fst
import Theorems.Thm_GlobalTheory_RedPts_toSec_injective
import Theorems.Thm_GlobalTheory_RedPts_eq_one_of_pow_of_closedPoint
import Theorems.Thm_GlobalTheory_RedPts_spMap_comp

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
open GlobalTheory GlobalTheory.RedPts
variable {S : Scheme.{0}}
namespace GlobalTheory.RedPts
theorem _root_.solution : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∃ (H : Subgroup (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (r : H →* (𝟙_ (Over (Sp (IsLocalRing.ResidueField R))) ⟶ (Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G)), (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = x.left) ∧ (∀ (x : H) (s : Sp R ⟶ G.left), s ≫ G.hom = spMap (algebraMap W R) → spMap (algebraMap R Ω) ≫ s = x.1.left → (r x).left ≫ pullback.fst G.hom _ = spMap (IsLocalRing.residue R) ≫ s) ∧ ∀ (n : ℕ) (x : H), IsUnit (n : R) → x ^ n = 1 → r x = 1 → x = 1 := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hj G _ hG
  obtain ⟨hc, hsm, hsep, -, -⟩ := hG
  let u : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (algebraMap R Ω))
      ((spMap_comp _ _).trans (congrArg spMap (IsScalarTower.algebraMap_eq W R Ω).symm))
  let v : Over.mk (spMap ((IsLocalRing.residue R).comp (algebraMap W R))) ⟶
      Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (IsLocalRing.residue R)) (spMap_comp _ _)
  have hdom : IsDominant (spMap (algebraMap R Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hj]; exact bot_le)⟩
  have hu : Function.Injective (precomp G u) := fun a b h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp R) G.hom ((Over.w a).trans (Over.w b).symm)
      (spMap (algebraMap R Ω)) (congrArg Over.Hom.left h))
  let e := MonoidHom.ofInjective hu
  refine ⟨(precomp G u).range, ((toSec G _).comp (precomp G v)).comp e.symm.toMonoidHom,
    fun x => ⟨?_, ?_⟩, fun x s hs hx => ?_, fun n x hn hx hr => ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.left, Over.w s, rfl⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨Over.homMk s hs, Over.OverMorphism.ext hx⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    obtain rfl : y = Over.homMk s hs := hu (Over.OverMorphism.ext hx.symm)
    change (toSec G _ (precomp G v (e.symm (e _)))).left ≫ _ = _
    rw [e.symm_apply_apply, toSec_left_fst]
    rfl
  · obtain ⟨y, rfl⟩ := e.surjective x
    change toSec G _ (precomp G v (e.symm (e _))) = _ at hr
    rw [e.symm_apply_apply, map_eq_one_iff _ (toSec_injective G _)] at hr
    rw [← map_pow, map_eq_one_iff _ e.injective] at hx
    rw [eq_one_of_pow_of_closedPoint G _ hn y hx v
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ hr, map_one]
end GlobalTheory.RedPts
