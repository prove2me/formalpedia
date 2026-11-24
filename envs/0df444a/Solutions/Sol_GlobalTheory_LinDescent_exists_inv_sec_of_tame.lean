-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_inv_sec_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:18.012452+00:00
-- url     : https://prove2.me/submissions/e3277dab-0cce-4765-ab9e-21fb05244c83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfInvGenOfInvariants
import Theorems.Thm_GlobalTheory_LinDescent_sum_coeff_eq_zero_of_linearIndependent
import Theorems.Thm_GlobalTheory_FinEt_exists_algClosed_point
import Theorems.Thm_GlobalTheory_LinDescent_exists_average
import Theorems.Thm_GlobalTheory_LinDescent_exists_locSec
import Theorems.Thm_GlobalTheory_LinDescent_gs_eq_gsHom
import Theorems.Thm_GlobalTheory_LinDescent_hom_ext_of_gs
import Theorems.Thm_GlobalTheory_LinDescent_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_LinDescent_val_eq_uv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}
namespace GlobalTheory.LinDescent
theorem _root_.solution [Group C] [Finite C] (hL : L.IsLB)
    (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      (Nat.card {c // r ≫ t c = r} : k) ≠ 0)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X) c, r ≫ t c = r →
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u c) r) (LB.oneGen L))
    {W : X.Opens} (hWa : IsAffineOpen W) (hW : ∀ c, W ≤ t c ⁻¹ᵁ W) (x : X) (hx : x ∈ W) :
    ∃ s : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W s ∧ IsInv u W s ∧
      ∃ i, x ∈ X.basicOpen (s i) := by
  classical
  cases nonempty_fintype C
  obtain ⟨m, hm, hm'⟩ := exists_locSec hL hWa x hx
  obtain ⟨k, _, _, r, hr⟩ := FinEt.exists_algClosed_point X x
  let z : Sp k := IsLocalRing.closedPoint k
  obtain rfl : r z = x := hr.le ⟨z, rfl⟩
  let ek := (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hF : IsField ((Sp k).presheaf.stalk z) := ek.toMulEquiv.isField (Field.toIsField k)
  have hz : ∀ c, (r ≫ t c) z ∈ W := fun c => hW c hx
  let p : C → (Γ(X, W) →* (Sp k).presheaf.stalk z) :=
    fun c => (gsHom (r ≫ t c) z W (hz c)).toMonoidHom
  have hp : ∀ c, p c = (gsHom r z W hx).toMonoidHom ↔ r ≫ t c = r := fun c =>
    ⟨fun e => hom_ext_of_gs hWa
      (fun z' => Subsingleton.elim z z' ▸ hz c) (fun z' => Subsingleton.elim z z' ▸ hx)
      fun z' f => by
        obtain rfl : z = z' := Subsingleton.elim _ _
        rw [gs_eq_gsHom _ _ _ (hz c), gs_eq_gsHom _ _ _ hx]
        exact DFunLike.congr_fun e f,
    fun e => MonoidHom.ext fun f => by
      change gsHom (r ≫ t c) z W (hz c) f = gsHom r z W hx f
      rw [← gs_eq_gsHom, ← gs_eq_gsHom, e]⟩
  choose J hJ using fun χ : Sp k ⟶ X => exists_chart hL (χ z)
  have hJ' : Good L z J := hJ
  have h1 : ∀ c, r ≫ t c = r → uv (u c) r z (J r) (J (r ≫ t c)) = 1 := fun c e => by
    have := val_corr hJ' (hfix k r c e) (𝟙 _)
    rwa [val_pull hJ', val_one, Category.id_comp, val_eq_uv] at this
  have : ∃ f : Γ(X, W), ∑ c, (uv (u c) r z (J r) (J (r ≫ t c))).val *
      gs (r ≫ t c) z _ (m (J (r ≫ t c))) * gs (r ≫ t c) z W f ≠ 0 := by
    by_contra! H
    have h2 := sum_coeff_eq_zero_of_linearIndependent
      (linearIndependent_monoidHom Γ(X, W) ((Sp k).presheaf.stalk z)) p
      (fun c => (uv (u c) r z (J r) (J (r ≫ t c))).val * gs (r ≫ t c) z _ (m (J (r ≫ t c))))
      (funext fun f => by
        rw [Finset.sum_apply]
        refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (H f)
        rw [gs_eq_gsHom _ _ _ (hz c) f]
        rfl) (gsHom r z W hx).toMonoidHom
    have h3 : ∀ c, (if p c = (gsHom r z W hx).toMonoidHom then
        (uv (u c) r z (J r) (J (r ≫ t c))).val * gs (r ≫ t c) z _ (m (J (r ≫ t c))) else 0) =
        if r ≫ t c = r then gs r z _ (m (J r)) else 0 := fun c =>
      if_ctx_congr (hp c) (fun e => by rw [h1 c e, Units.val_one, one_mul, e]) fun _ => rfl
    rw [Finset.sum_congr rfl fun c _ => h3 c, ← Finset.sum_filter, Finset.sum_const,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, nsmul_eq_mul] at h2
    have h4 : IsUnit (gs r z _ (m (J r))) :=
      (isUnit_gs_iff r z (W ⊓ L.U (J r)) ⟨hx, hJ r⟩ _).2 (hm' _ (hJ r))
    have h5 := congrArg ek (h4.mul_left_eq_zero.1 h2)
    rw [map_natCast, map_zero] at h5
    exact htame k r h5
  obtain ⟨f, hf⟩ := this
  obtain ⟨s, h1, h2, h3⟩ := exists_average hL ht hu hc hW hm f
  refine ⟨s, h1, h2, J r, (isUnit_gs_iff r z (W ⊓ L.U (J r)) ⟨hx, hJ r⟩ _).1 ?_⟩
  rw [h3 _ r z (J r) (fun c => J (r ≫ t c)) hx (hJ r) fun c => hJ _]
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel hf
  exact IsUnit.of_mul_eq_one _ hb
end GlobalTheory.LinDescent
