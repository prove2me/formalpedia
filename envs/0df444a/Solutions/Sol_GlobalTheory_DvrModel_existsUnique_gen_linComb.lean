-- Prove2me | solution 1 for GlobalTheory.DvrModel.existsUnique_gen_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:45.560326+00:00
-- url     : https://prove2.me/submissions/f7d89476-4f38-4411-8b10-2de2fdbeeab6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_wchart_comp
import Theorems.Thm_GlobalTheory_DvrModel_existsUnique_isUnit_appLE_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_comp
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
    {X : Scheme.{u}} {L : LB X} (hL : L.IsLB) {κ : Type u} [Fintype κ] (φ : κ → (H ⟶ X))
    (ε : κ → ℤ) (r : LB.Gen (LB.LinComb L (fun k ↦ j ≫ φ k) ε)) (hr : r.IsGen) (a₀ : κ → L.ι)
    (h₀ : ⊤ ≤ e ⁻¹ᵁ LB.wchart L φ a₀) (h₀' : ⊤ ≤ eK ⁻¹ᵁ LB.wchart L (fun k ↦ j ≫ φ k) a₀)
    (u : Vˣ) (hu : eK.appLE _ ⊤ h₀' (LB.ts r a₀ : Γ(HK, LB.wchart L (fun k ↦ j ≫ φ k) a₀)) =
      (Scheme.ΓSpecIso (.of K)).inv (algebraMap V K u)) :
    ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L φ ε c j = r := by
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := LB.wchart L φ) (g := fun a b ↦ LB.lcg L φ ε a b) (W := LB.wchart L fun k ↦ j ≫ φ k)
    (wchart_comp L j φ) (LB.mem_of_cover (LB.isLB_linComb hL φ ε)) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ LB.ts r a)
    (fun a b ↦ by
      have := congrArg Units.val ((LB.isGen_iff L r).1 hr a b)
      rw [LB.lcg_comp] at this
      exact this)
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := ⊤) trivial h₀ (A' := ⊤) rfl h₀'
    (u.isUnit.map (Scheme.ΓSpecIso (.of V)).inv.hom) (by
      rw [hu]
      exact (congrArg (fun ψ : CommRingCat.of V ⟶ Γ(Spec (.of K), ⊤) ↦ ψ u)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V K)))).symm)
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr a))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ (r' a).val) ⟨fun a ↦ Units.isUnit _,
      fun a b ↦ congrArg Units.val (h₁ a b), fun a ↦ congrArg (fun c ↦ (LB.ts c a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))
end GlobalTheory.DvrModel
