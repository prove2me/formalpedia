-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_inv_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:17.329329+00:00
-- url     : https://prove2.me/submissions/7eed47e7-8e76-466f-b52d-e72272c9f890

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_gs_eq_gsHom
import Theorems.Thm_GlobalTheory_LinDescent_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_LinDescent_exists_locSec
import Theorems.Thm_GlobalTheory_LinDescent_exists_average
import Theorems.Thm_GlobalTheory_LinDescent_hom_ext_of_gs
import Theorems.Thm_GlobalTheory_FinEt_exists_algClosed_point
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
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
variable {L : LB X}
variable {C : Type} {t : C → (X ⟶ X)}
variable [Group C] [Finite C]
namespace GlobalTheory.LinDescent
theorem _root_.solution (hL : L.IsLB) (ht1 : t 1 = 𝟙 X) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ t c)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    {W : X.Opens} (hWa : IsAffineOpen W) (hW : ∀ c, W ≤ t c ⁻¹ᵁ W) (x : X) (hx : x ∈ W) :
    ∃ s : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W s ∧ IsInv u W s ∧
      ∃ i, x ∈ X.basicOpen (s i) := by
  cases nonempty_fintype C
  obtain ⟨m, hm, hm'⟩ := exists_locSec hL hWa x hx
  obtain ⟨k, _, _, r, hr⟩ := FinEt.exists_algClosed_point X x
  let z : Sp k := IsLocalRing.closedPoint k
  obtain rfl : r z = x := hr.le ⟨z, rfl⟩
  have hF : IsField ((Sp k).presheaf.stalk z) :=
    (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  have hz : ∀ c, (r ≫ t c) z ∈ W := fun c => hW c hx
  have hinj : Function.Injective fun c => (gsHom (r ≫ t c) z W (hz c)).toMonoidHom :=
    fun c c' e => hfree k r (hom_ext_of_gs hWa
      (fun z' => Subsingleton.elim z z' ▸ hz c) (fun z' => Subsingleton.elim z z' ▸ hz c')
      fun z' f => by
        obtain rfl : z = z' := Subsingleton.elim _ _
        rw [gs_eq_gsHom _ _ _ (hz c), gs_eq_gsHom _ _ _ (hz c')]
        exact DFunLike.congr_fun e f)
  have hli := (linearIndependent_monoidHom Γ(X, W) ((Sp k).presheaf.stalk z)).comp _ hinj
  obtain ⟨i, hi⟩ := exists_chart hL (r z)
  choose j hj using fun c => exists_chart hL ((r ≫ t c) z)
  have : ∃ f : Γ(X, W), ∑ c, (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c)) *
      gs (r ≫ t c) z W f ≠ 0 := by
    by_contra! H
    have h1 := Fintype.linearIndependent_iff.1 hli
      (fun c => (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c))) (funext fun f => by
        rw [Finset.sum_apply]
        refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (H f)
        rw [gs_eq_gsHom _ _ _ (hz c) f]
        rfl) 1
    have h2 := hj 1
    rw [ht1, Category.comp_id] at h2
    have h3 : IsUnit (gs (r ≫ t 1) z _ (m (j 1))) := by
      rw [ht1, Category.comp_id]
      exact (isUnit_gs_iff r z (W ⊓ L.U (j 1)) ⟨hx, h2⟩ _).2 (hm' _ h2)
    exact ((Units.isUnit _).mul h3).ne_zero h1
  obtain ⟨f, hf⟩ := this
  obtain ⟨s, h1, h2, h3⟩ := exists_average hL ht hu hc hW hm f
  refine ⟨s, h1, h2, i, (isUnit_gs_iff r z (W ⊓ L.U i) ⟨hx, hi⟩ _).1 ?_⟩
  rw [h3 _ r z i j hx hi hj]
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel hf
  exact IsUnit.of_mul_eq_one _ hb
end GlobalTheory.LinDescent
