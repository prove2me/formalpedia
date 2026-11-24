-- Prove2me | solution 1 for GlobalTheory.DvrModel.isDiscreteValuationRing_stalk_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:56:06.887799+00:00
-- url     : https://prove2.me/submissions/78d1f7be-c26f-4b8c-955a-a3623f5904d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff_specializes
import Theorems.Thm_GlobalTheory_DvrModel_prime_res_generic
import Theorems.Thm_GlobalTheory_DvrModel_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_PrimeSection_isDiscreteValuationRing_stalk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel
open PrimeSection
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}
local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)
namespace GlobalTheory.DvrModel
theorem _root_.solution (hϖ : Irreducible ϖ) [Flat f]
    [LocallyOfFiniteType f] [IsIntegral H] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) :
    IsDiscreteValuationRing (H.presheaf.stalk (i (genericPoint Hs))) ∧
      Irreducible (H.presheaf.germ ⊤ (i (genericPoint Hs)) trivial cst[f, V, ϖ]) :=
  haveI := isLocallyNoetherian f
  isDiscreteValuationRing_stalk (notMem_basicOpen_iff_specializes hϖ hs) (prime_res_generic hϖ hs)
end GlobalTheory.DvrModel
