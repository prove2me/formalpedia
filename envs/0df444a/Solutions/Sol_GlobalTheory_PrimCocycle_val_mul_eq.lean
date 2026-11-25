-- Prove2me | solution 1 for GlobalTheory.PrimCocycle.val_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:04.52158+00:00
-- url     : https://prove2.me/submissions/aa117684-cad8-4d78-98a8-49df406d5395

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Theorems.Thm_GlobalTheory_PrimCocycle_prod_lam
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PrimCocycle
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
namespace GlobalTheory.PrimCocycle
theorem _root_.solution (hG : GlobalFnsSt) (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB)
    (u : LB.Gen (LB.LinComb L (lamφ B) lamε)) (hu : u.IsGen)
    (e : 𝟙_ (Over S) ⟶ G3 B) (a b c d a' b' c' d' : G3 B ⟶ B)
    (hF : ∀ (V : Type) [CommGroup V] (k : (G3 B ⟶ B) → V),
      (k (a' * b') * (k a')⁻¹ * (k b')⁻¹ * k 1) * (k (c' * d') * (k c')⁻¹ * (k d')⁻¹ * k 1) =
      (k (a * b) * (k a)⁻¹ * (k b)⁻¹ * k 1) * (k (c * d) * (k c)⁻¹ * (k d)⁻¹ * k 1))
    (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1) (hd : e ≫ d = 1)
    (ha' : e ≫ a' = 1) (hb' : e ≫ b' = 1) (hc' : e ≫ c' = 1) (hd' : e ≫ d' = 1)
    {T : Over S} (ρ : T ⟶ G3 B) {z : T.left} {J} (hJ : Good L z J) :
    val₂ u z J (ρ ≫ a) (ρ ≫ b) * val₂ u z J (ρ ≫ c) (ρ ≫ d) =
      val₂ u z J (ρ ≫ a') (ρ ≫ b') * val₂ u z J (ρ ≫ c') (ρ ≫ d') := by
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good L z J → ∀ a b : T ⟶ B,
      val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := fun ρ z J hJ a b => by
    rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
  have sj : Function.Surjective ((snd B (B ⊗ B)).left ≫ (snd B B).left ≫ B.hom).appTop.hom :=
    surj_comp (surj_snd hG hB _) (surj_comp (surj_snd hG hB _) (hG _ _ hB).2)
  have he : e.left ≫ (snd B (B ⊗ B)).left ≫ (snd B B).left ≫ B.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 B) {z : T'.left} {J}, Good L z J → ∀ a b c d : G3 B ⟶ B,
      val (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ u (lift a b).left) (LB.pullGen L _ _ u (lift c d).left))
        σ.left z J = val₂ u z J (σ ≫ a) (σ ≫ b) * val₂ u z J (σ ≫ c) (σ ≫ d) := fun σ z J hJ a b c d =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))
  refine (ev ρ hJ a b c d).symm.trans (Eq.trans (gen_unique' hL (fun V _ k => ?_) _ e.left he sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
    (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ a' b' c' d'))
  · exact (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
      (prod_lam a' b' k) (prod_lam c' d' k)).trans ((hF V fun q => k q.left).trans
      (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
        (prod_lam a b k) (prod_lam c d k)).symm)
  · refine (ev e hI a b c d).trans (Eq.trans ?_ (ev e hI a' b' c' d').symm)
    rw [ha, hb, hc, hd, ha', hb', hc', hd']
end GlobalTheory.PrimCocycle
