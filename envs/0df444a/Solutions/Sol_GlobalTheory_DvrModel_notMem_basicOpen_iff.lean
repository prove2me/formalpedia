-- Prove2me | solution 1 for GlobalTheory.DvrModel.notMem_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:04:56.844332+00:00
-- url     : https://prove2.me/submissions/12d70fa4-6a22-4343-8ea7-4614772e766c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric

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
variable (f)
namespace GlobalTheory.DvrModel
theorem _root_.solution (hϖ : Irreducible ϖ) (x : H) :
    x ∉ H.basicOpen cst[f, V, ϖ] ↔ f x = closedPoint V := by
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  change ¬ ϖ ∉ (f x).asIdeal ↔ _
  rw [not_not]
  constructor
  · intro h
    refine PrimeSpectrum.ext ((maximalIdeal.isMaximal V).eq_of_le (f x).2.ne_top ?_).symm
    rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
  · intro h
    rw [h]
    exact hϖ.not_isUnit
end GlobalTheory.DvrModel
