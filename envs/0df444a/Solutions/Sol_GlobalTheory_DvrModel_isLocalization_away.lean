-- Prove2me | solution 1 for GlobalTheory.DvrModel.isLocalization_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:23.831806+00:00
-- url     : https://prove2.me/submissions/b0d97db3-71db-4236-a2dc-d438ce7abc1b

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
variable (K)
namespace GlobalTheory.DvrModel
theorem _root_.solution (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors V)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun a ha ↦ ?_).2 inferInstance
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hϖ
  exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
end GlobalTheory.DvrModel
