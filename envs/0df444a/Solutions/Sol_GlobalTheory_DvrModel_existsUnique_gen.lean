-- Prove2me | solution 1 for GlobalTheory.DvrModel.existsUnique_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:04.509683+00:00
-- url     : https://prove2.me/submissions/ad0ccc92-196a-4e62-940c-dd58aa751cee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_wchart_comp
import Theorems.Thm_GlobalTheory_DvrModel_coe_pull_g
import Theorems.Thm_GlobalTheory_DvrModel_coe_res_pullGen
import Theorems.Thm_GlobalTheory_DvrModel_existsUnique_isUnit_appLE_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


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
theorem _root_.solution {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {L : LB H} (hL : L.IsLB) (r : LB.Gen (L.pull j)) (hr : r.IsGen) (ρ : LB.Gen (L.pull e))
    (hρ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r eK)
      (LB.pullGen L _ _ ρ (Spec.map (CommRingCat.ofHom (algebraMap V K))))) :
    ∃! r' : LB.Gen L, r'.IsGen ∧ LB.genPull L r' j = r := by
  obtain ⟨a₀, h₀⟩ := LB.mem_of_cover hL (e (closedPoint V))
  have hc := congrArg Units.val
    (hρ (fun _ ↦ a₀) (fun _ ↦ a₀) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) fun _ _ _ ↦ rfl)
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := L.U) (g := fun a b ↦ L.g a b) (W := fun a ↦ (L.pull j).U fun _ ↦ a)
    (fun a ↦ pull_U L j _) (LB.mem_of_cover hL) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ r.s fun _ ↦ a)
    (fun a b ↦ by
      rw [← coe_pull_g L j (fun _ ↦ a) (fun _ ↦ b)]
      exact congrArg Units.val (hr _ _))
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := (L.pull e).U fun _ ↦ a₀)
    ((pull_U L e _).ge h₀) (pull_U L e _).le
    (A' := LB.wchart L (fun _ : PUnit ↦ eK ≫ j) (fun _ ↦ a₀) ⊓
      LB.wchart L (fun _ : PUnit ↦ Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e) fun _ ↦ a₀)
    (by rw [heK, inf_idem]; exact wchart_comp L _ (fun _ ↦ e) _)
    (inf_le_left.trans (wchart_comp L eK (fun _ ↦ j) _).le) (ρ.s _).isUnit
    ((coe_res_pullGen L (fun _ ↦ e) _ ρ _ (fun _ ↦ a₀) inf_le_right).symm.trans
      (hc.symm.trans (coe_res_pullGen L (fun _ ↦ j) _ r eK (fun _ ↦ a₀) inf_le_left)))
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr (a ⟨⟩)))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ r' a) ⟨fun a ↦ Units.isUnit _, fun a b ↦ congrArg Units.val (h₁ a b),
      fun a ↦ congrArg (fun c : LB.Gen (L.pull j) ↦ (c.s fun _ ↦ a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))
end GlobalTheory.DvrModel
