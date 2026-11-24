-- Prove2me | solution 1 for GlobalTheory.HodgeTateCompare.finite_projective_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:15.340806+00:00
-- url     : https://prove2.me/submissions/f1b49281-66fb-438b-a017-9f47a22fbb93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective
import Theorems.Thm_GlobalTheory_HodgeTateCompare_strMap_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateCompare
open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
noncomputable section
variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
namespace GlobalTheory.HodgeTateCompare
theorem _root_.solution [Smooth G.hom] :
    Module.Finite O (Cotangent G) ∧ Module.Projective O (Cotangent G) := by
  let q : PrimeSpectrum O := G.hom (origin G)
  letI : Algebra O ((Spec (CommRingCat.of O)).presheaf.stalk q) := StructureSheaf.stalkAlgebra O q
  have := q.isPrime
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of O)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk O q
  have h₁ : (strMap G).hom.FormallySmooth := by
    have hs : (G.hom.stalkMap (origin G)).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (G.hom.smoothLocus_eq_top.ge (Set.mem_univ _))
    have h₀ : Algebra.FormallySmooth O ((Spec (CommRingCat.of O)).presheaf.stalk q) :=
      Algebra.FormallySmooth.of_isLocalization q.asIdeal.primeCompl
    rw [strMap_eq]
    exact RingHom.FormallySmooth.comp (RingHom.formallySmooth_algebraMap.2 h₀) hs
  have h₂ : (strMap G).hom.EssFiniteType := by
    have hs : (G.hom.stalkMap (origin G)).hom.EssFiniteType :=
      LocallyOfFiniteType.stalkMap G.hom _
    have h₀ : Algebra.EssFiniteType O ((Spec (CommRingCat.of O)).presheaf.stalk q) :=
      Algebra.EssFiniteType.of_isLocalization _ q.asIdeal.primeCompl
    rw [strMap_eq]
    exact RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.2 h₀) hs
  haveI : Algebra.FormallySmooth O (LocRing G) := h₁
  haveI : Algebra.EssFiniteType O (LocRing G) := h₂
  exact ⟨AugCot.finite (aug G), AugCot.projective (aug G)⟩
end GlobalTheory.HodgeTateCompare
