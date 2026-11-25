-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:29:01.768122+00:00
-- url     : https://prove2.me/submissions/f29f43d9-2f34-4df9-8a08-b9e69e82f5dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Sp
  intro x
  have _ : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  have _ : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  have hle : x.asIdeal.primeCompl ≤ nonZeroDivisors R := fun r hr =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hr (h0 ▸ x.asIdeal.zero_mem)
  have _ : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk x) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ _ hle⟩
end GlobalTheory.Published.SemiAbelianHomExtension
