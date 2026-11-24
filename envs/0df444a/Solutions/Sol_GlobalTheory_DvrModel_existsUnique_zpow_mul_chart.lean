-- Prove2me | solution 1 for GlobalTheory.DvrModel.existsUnique_zpow_mul_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:19.802955+00:00
-- url     : https://prove2.me/submissions/8e30d367-9db0-4a61-8c84-788984b3af2b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff
import Theorems.Thm_GlobalTheory_DvrModel_isOpenImmersion_generic
import Theorems.Thm_GlobalTheory_DvrModel_opensRange_generic
import Theorems.Thm_GlobalTheory_DvrModel_isIntegral
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff_specializes
import Theorems.Thm_GlobalTheory_DvrModel_prime_res_generic
import Theorems.Thm_GlobalTheory_DvrModel_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_DvrModel_appTop_cst
import Theorems.Thm_GlobalTheory_PrimeSection_existsUnique_zpow_mul_appLE


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
variable [Flat f] [LocallyOfFiniteType f] [IsIntegral HK] [IsIntegral Hs]
  (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
  (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))))
include hK hs
namespace GlobalTheory.DvrModel
theorem _root_.solution (hϖ : Irreducible ϖ) {ι : Type v} {U : ι → H.Opens}
    {g : ∀ a b, Γ(H, U a ⊓ U b)} {W : ι → HK.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
    (hU : ∀ x : H, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b)) {r : ∀ a, Γ(HK, W a)}
    (hr : ∀ a b, HK.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        HK.presheaf.map (homOfLE inf_le_right).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(H, U a),
      (∀ a b, H.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * H.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, j.appLE (U a) (W a) (hW a).le (s a) =
        HK.presheaf.map (homOfLE le_top).op cst[fK, K, algebraMap V K ϖ ^ n] * r a) ∧
      ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s a) := by
  have := isOpenImmersion_generic hK
  have := isIntegral hK
  have := isLocallyNoetherian f
  have h0 : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hϖ.ne_zero
  let φ : K →+* Γ(HK, ⊤) := fK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hτ : ∀ n : ℤ, ((Units.map φ.toMonoidHom (Units.mk0 _ h0) ^ n : Γ(HK, ⊤)ˣ) : Γ(HK, ⊤)) =
      cst[fK, K, algebraMap V K ϖ ^ n] := fun n ↦ by
    rw [← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val]
    rfl
  have := existsUnique_zpow_mul_appLE (notMem_basicOpen_iff_specializes hϖ hs)
    (prime_res_generic hϖ hs) (opensRange_generic hϖ hK) hW hU hg
    (Units.map φ.toMonoidHom (Units.mk0 _ h0)) (appTop_cst hK.w ϖ).symm hr hr0
  simpa only [hτ, notMem_basicOpen_iff f hϖ] using this
end GlobalTheory.DvrModel
