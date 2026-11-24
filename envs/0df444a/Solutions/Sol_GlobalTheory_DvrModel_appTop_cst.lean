-- Prove2me | solution 1 for GlobalTheory.DvrModel.appTop_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:18.296308+00:00
-- url     : https://prove2.me/submissions/c756d391-419d-4e2a-91e8-44a7d8fe91a1

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
omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K]
namespace GlobalTheory.DvrModel
theorem _root_.solution (hw : j ≫ f = fK ≫ Spec.map (CommRingCat.ofHom (algebraMap V K))) (c : V) :
    j.appTop cst[f, V, c] = cst[fK, K, algebraMap V K c] := by
  have h₁ := congrArg (fun φ : HK ⟶ Spec (.of V) ↦ φ.appTop ((Scheme.ΓSpecIso (.of V)).inv c)) hw
  have h₂ := congrArg (fun φ : CommRingCat.of V ⟶ Γ(Spec (.of K), ⊤) ↦ φ c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V K)))
  exact h₁.trans (congrArg fK.appTop h₂.symm)
end GlobalTheory.DvrModel
