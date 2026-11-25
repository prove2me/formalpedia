-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.exists_weilIs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:16.069092+00:00
-- url     : https://prove2.me/submissions/192798d4-a443-4e87-93e8-de12eda88e1c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_glue_top
import Theorems.Thm_GlobalTheory_CommutatorPairing_commIsOf_iff
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_pull
import Theorems.Thm_GlobalTheory_CommutatorPairing_commVal_indep
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_commIsOf
import Theorems.Thm_GlobalTheory_CommutatorPairing_gm_unitRes
import Theorems.Thm_P2M_GlobalTheory_CommutatorPairing_overLE___bed2ac08eb35
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} {x y : T ⟶ A}
    (hx : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp A L k (overRes V), θ.pt = overResι V ≫ x)
    (hy : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp A L k (overRes V), θ.pt = overResι V ≫ y) :
    ∃ c : Γ(T.left, ⊤)ˣ, WeilIs A L k x y c := by
  have loc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θx θy : ThetaGrp A L k (overRes V),
      θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y := fun p => by
    obtain ⟨V, hV, θ, e⟩ := hx p
    obtain ⟨V', hV', θ', e'⟩ := hy p
    obtain ⟨θx, ex⟩ := exists_pull hL θ (overLE (inf_le_left : V ⊓ V' ≤ V))
    obtain ⟨θy, ey⟩ := exists_pull hL θ' (overLE (inf_le_right : V ⊓ V' ≤ V'))
    exact ⟨V ⊓ V', ⟨hV, hV'⟩, θx, θy, by rw [ex, e, ← Category.assoc, overLE_ι],
      by rw [ey, e', ← Category.assoc, overLE_ι]⟩
  choose V hV θx θy ex ey using loc
  choose c hc using fun p => exists_commIsOf hG hA hL (θx p) (θy p)
  obtain ⟨a, ha⟩ := glue_top V (fun p => ⟨p, hV p⟩) c (fun s s' Z r r' z hr => by
    let Z' : Over S := Over.mk (r ≫ (V s).ι ≫ T.hom)
    let t : Z' ⟶ overRes (V s) := Over.homMk r rfl
    let t' : Z' ⟶ overRes (V s') := Over.homMk r' (by
      show r' ≫ (V s').ι ≫ T.hom = r ≫ (V s).ι ≫ T.hom
      rw [← Category.assoc, ← hr, Category.assoc])
    have ht : t ≫ overResι (V s) = t' ≫ overResι (V s') := Over.OverMorphism.ext hr
    choose J hJ using fun χ : Z ⟶ A.left => exists_chart hL (χ z)
    have e₁ := (commIsOf_iff hL _ _ _).1 (hc s) _ t 1 z J hJ
    have e₂ := (commIsOf_iff hL _ _ _).1 (hc s') _ t' 1 z J hJ
    have e₃ := commVal_indep hG hA hL (θx s) (θy s) (θx s') (θy s') t t'
      (by rw [ex, ex, ← Category.assoc, ← Category.assoc, ht])
      (by rw [ey, ey, ← Category.assoc, ← Category.assoc, ht]) 1 z J hJ
    exact e₁.symm.trans (e₃.trans e₂))
  refine ⟨a, fun p => ⟨V p, hV p, ⟨θx p, θy p, ex p, ey p⟩, fun θ θ' e e' => ?_⟩⟩
  refine (commIsOf_iff hL _ _ _).2 fun Z t b z J hJ => ?_
  exact (commVal_indep hG hA hL θ θ' (θx p) (θy p) t t (by rw [e, ex]) (by rw [e', ey]) b z J hJ).trans
    (((commIsOf_iff hL _ _ _).1 (hc p) _ t b z J hJ).trans ((ha p _ t.left z).symm.trans
      (gm_unitRes (V p) a t.left z).symm))
end GlobalTheory.CommutatorPairing
