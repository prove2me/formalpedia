-- Prove2me | solution 1 for GlobalTheory.DvrModel.existsUnique_zpow_mul_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:35:08.044908+00:00
-- url     : https://prove2.me/submissions/bf2c6376-5fbf-460b-ac55-2d07669cddd3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_coe_pull_g
import Theorems.Thm_GlobalTheory_DvrModel_existsUnique_zpow_mul_chart
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
theorem _root_.solution (hϖ : Irreducible ϖ) {L : LB H} (hL : L.IsLB)
    (r : (L.pull j).Sec) (hr0 : ∃ a, r.f a ≠ 0) :
    ∃! n : ℤ, ∃ s : L.Sec,
      (∀ a : PUnit → L.ι, j.appLE (L.U (a ⟨⟩)) ((L.pull j).U a) (pull_U L j a).le (s.f (a ⟨⟩)) =
        HK.presheaf.map (homOfLE le_top).op cst[fK, K, algebraMap V K ϖ ^ n] * r.f a) ∧
      ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s.f a) := by
  obtain ⟨n, ⟨s, hc, hsr, hx⟩, huniq⟩ := existsUnique_zpow_mul_chart hK hs hϖ
    (U := L.U) (g := fun a b ↦ L.g a b) (W := fun a ↦ (L.pull j).U fun _ ↦ a)
    (fun a ↦ pull_U L j _) (LB.mem_of_cover hL) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ r.f fun _ ↦ a)
    (fun a b ↦ by
      rw [← coe_pull_g L j (fun _ ↦ a) (fun _ ↦ b)]
      exact r.compat _ _)
    (hr0.elim fun a ha ↦ ⟨a ⟨⟩, ha⟩)
  refine ⟨n, ⟨⟨s, hc⟩, fun a ↦ hsr (a ⟨⟩), hx⟩, ?_⟩
  rintro m ⟨s', hsr', hx'⟩
  exact huniq m ⟨s'.f, s'.compat, fun a ↦ hsr' fun _ ↦ a, hx'⟩
end GlobalTheory.DvrModel
