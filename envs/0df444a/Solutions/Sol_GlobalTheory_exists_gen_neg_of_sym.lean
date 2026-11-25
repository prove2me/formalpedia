-- Prove2me | solution 1 for GlobalTheory.exists_gen_neg_of_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:37:18.093095+00:00
-- url     : https://prove2.me/submissions/a0ebf125-8d43-41c5-b8a5-6c770bf97452

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Theorems.Thm_GlobalTheory_exists_gen_of_local_on_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Out.Sym A L) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), u.IsGen := by
  refine exists_gen_of_local_on_base hL _ _ A.hom η[A].left (Over.w η[A]) (fun V => surj_snd hG hA (Over.mk V.ι))
    (fun U _ h => ?_) (fun s => ?_)
  · have e : η[A].left ≫ (GrpObj.inv : A ⟶ A).left = η[A].left :=
      congrArg (fun q => q.left) (show η[A] ≫ (GrpObj.inv : A ⟶ A) = η[A] from GrpObj.one_inv)
    rw [Fin.prod_univ_two]
    show h (η[A].left ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) * h (η[A].left ≫ 𝟙 _) ^ (-1 : ℤ) = 1
    rw [e, Category.comp_id]; simp
  · obtain ⟨U, hU, t, ht⟩ := hs s
    obtain ⟨t', ht', -⟩ := exists_gen hL
      (φ' := fun k => (A.hom ⁻¹ᵁ U).ι ≫ (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) k) (ε' := ![1, -1])
      (fun V _ h => by simp [Fin.prod_univ_two]) t ht
    exact ⟨U, hU, t', ht'⟩
end GlobalTheory
