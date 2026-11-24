-- Prove2me | solution 1 for GlobalTheory.DvrModel.res_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:19.366465+00:00
-- url     : https://prove2.me/submissions/d1a5cc0c-9bde-4d6e-8192-96a281a49232

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
omit [IsDiscreteValuationRing V]
namespace GlobalTheory.DvrModel
theorem _root_.solution [Flat f] {c : V} (hc : c ≠ 0) {U : H.Opens}
    (hU : IsAffineOpen U) :
    H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op cst[f, V, c] ∈ nonZeroDivisors Γ(H, U) := by
  have hf := f.flat_appLE (isAffineOpen_top _) hU le_top
  let := (f.appLE ⊤ U le_top).hom.toAlgebra
  have hc' : (Scheme.ΓSpecIso (.of V)).inv c ≠ 0 :=
    (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1).2 hc
  have : Module.Flat Γ(Spec (.of V), ⊤) Γ(H, U) := hf
  have := IsSMulRegular.of_flat (S := Γ(H, U)) (IsSMulRegular.of_ne_zero hc')
  exact mem_nonZeroDivisors_iff_left.2 fun z hz ↦ this (hz.trans (smul_zero _).symm)
end GlobalTheory.DvrModel
