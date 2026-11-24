-- Prove2me | solution 1 for GlobalTheory.DvrModel.mem_range_special
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:07:19.076854+00:00
-- url     : https://prove2.me/submissions/21658578-2135-47b1-87ae-4addcf40292d

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
namespace GlobalTheory.DvrModel
theorem _root_.solution
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) (x : H) :
    x ∈ Set.range i ↔ f x = closedPoint V := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, hs.w]
    exact PrimeSpectrum.comap_residue V (fs y)
  · intro h
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hs x (closedPoint _)
      (h.trans (PrimeSpectrum.comap_residue V _).symm)
    exact ⟨y, hy⟩
end GlobalTheory.DvrModel
