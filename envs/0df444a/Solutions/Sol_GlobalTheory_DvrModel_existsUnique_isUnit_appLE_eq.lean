-- Prove2me | solution 1 for GlobalTheory.DvrModel.existsUnique_isUnit_appLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:35:09.301106+00:00
-- url     : https://prove2.me/submissions/ddf2cf6b-3604-4c20-aea0-209d2f4881d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_isLocalization_away
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff
import Theorems.Thm_GlobalTheory_DvrModel_isOpenImmersion_generic
import Theorems.Thm_GlobalTheory_DvrModel_opensRange_generic
import Theorems.Thm_GlobalTheory_DvrModel_isIntegral
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff_specializes
import Theorems.Thm_GlobalTheory_DvrModel_prime_res_generic
import Theorems.Thm_GlobalTheory_DvrModel_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_injective
import Theorems.Thm_GlobalTheory_PrimeSection_exists_isUnit_appLE_eq


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
theorem _root_.solution {ι : Type v} {U : ι → H.Opens}
    {g : ∀ a b, Γ(H, U a ⊓ U b)} {W : ι → HK.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
    (hU : ∀ x : H, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b)) {r : ∀ a, Γ(HK, W a)}
    (hr : ∀ a b, HK.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        HK.presheaf.map (homOfLE inf_le_right).op (r b))
    (hru : ∀ a, IsUnit (r a)) {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {a₀ : ι} {A : (Spec (.of V)).Opens} (hyA : closedPoint V ∈ A) (hA : A ≤ e ⁻¹ᵁ U a₀)
    {A' : (Spec (.of K)).Opens} (hA' : A' = Spec.map (CommRingCat.ofHom (algebraMap V K)) ⁻¹ᵁ A)
    (hA'' : A' ≤ eK ⁻¹ᵁ W a₀) {u : Γ(Spec (.of V), A)} (hu : IsUnit u)
    (hur : (Spec.map (CommRingCat.ofHom (algebraMap V K))).appLE A A' hA'.le u =
      eK.appLE (W a₀) A' hA'' (r a₀)) :
    ∃! s : ∀ a, Γ(H, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, H.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * H.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, j.appLE (U a) (W a) (hW a).le (s a) = r a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isOpenImmersion_generic hK
  have := isIntegral hK
  have := isLocallyNoetherian f
  have := isLocalization_away K hϖ
  have := IsOpenImmersion.of_isLocalization (S := K) ϖ
  refine existsUnique_of_exists_of_unique
    (exists_isUnit_appLE_eq (notMem_basicOpen_iff_specializes hϖ hs) (prime_res_generic hϖ hs)
      (opensRange_generic hϖ hK) hW hU hg hr hru e _ eK heK ?_ hyA hA hA' hA'' hu hur)
    fun s s' h h' ↦ funext fun a ↦ appLE_injective j (hW a) ((h.2.2 a).trans (h'.2.2 a).symm)
  rw [notMem_basicOpen_iff f hϖ, ← Scheme.Hom.comp_apply, he]
  rfl
end GlobalTheory.DvrModel
