-- Prove2me | solution 1 for GlobalTheory.adjCompare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:40:53.722254+00:00
-- url     : https://prove2.me/submissions/b2ad9faf-84c5-463f-b03b-1fd3e5f759e9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GrpPullbackSquareProductLift
import Theorems.Thm_GlobalTheory_adjPair3_comp
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
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {σ : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G σ φ)
namespace GlobalTheory
theorem _root_.solution (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G') {P : LB (G ⊗ G).left} (hP : P.IsLB)
    {K L : Type} [Fintype K] [Fintype L] {τ : K → ((G' ⊗ G').left ⟶ (G ⊗ G).left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb P τ ε)) (ht : t.IsGen) {ω : L → ((G3 G).left ⟶ (G ⊗ G).left)} {δ : L → ℤ}
    (w : LB.Gen (LB.LinComb P ω δ)) (hw : w.IsGen) (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ : G3 G' ⟶ G')
    (hF : ∀ (U : Type) [CommGroup U] (h : ((G3 G').left ⟶ (G ⊗ G).left) → U),
      (∏ i, h (adjPair3 gp l₁ l₂ l₃ ≫ ω i) ^ δ i) * ((∏ i, h ((lift a₁ b₁).left ≫ τ i) ^ ε i) *
        (∏ i, h ((lift a₂ b₂).left ≫ τ i) ^ ε i)) =
      (∏ i, h (adjPair3 gp k₁ k₂ k₃ ≫ ω i) ^ δ i) * ((∏ i, h ((lift a b).left ≫ τ i) ^ ε i) *
        (∏ i, h ((lift (1 : G3 G' ⟶ G') (1 : G3 G' ⟶ G')).left ≫ τ i) ^ ε i)))
    (h0 : ∀ q ∈ [a, b, a₁, b₁, a₂, b₂, k₁, k₂, k₃, l₁, l₂, l₃],
      (lift 1 (lift 1 1) : 𝟙_ (Over S') ⟶ G3 G') ≫ q = 1)
    {T : Over S'} (ρ : T ⟶ G3 G') {z : T.left} {J} (hJ : Good P z J) :
    val w (adjPair3 gp (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃)) z J * (val t (lift (ρ ≫ a) (ρ ≫ b)).left z J *
      val t (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J) =
    val w (adjPair3 gp (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃)) z J * (val t (lift (ρ ≫ a₁) (ρ ≫ b₁)).left z J *
      val t (lift (ρ ≫ a₂) (ρ ≫ b₂)).left z J) := by
  let e : 𝟙_ (Over S') ⟶ G3 G' := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have ev : ∀ (a₁ b₁ a₂ b₂ l₁ l₂ l₃ : G3 G' ⟶ G') {T' : Over S'} (r : T' ⟶ G3 G') {z : T'.left} {J}, Good P z J →
      val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ w (adjPair3 gp l₁ l₂ l₃))
        (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ t (lift a₁ b₁).left) (LB.pullGen P _ _ t (lift a₂ b₂).left))) r.left z J =
      val w (adjPair3 gp (r ≫ l₁) (r ≫ l₂) (r ≫ l₃)) z J * (val t (lift (r ≫ a₁) (r ≫ b₁)).left z J *
        val t (lift (r ≫ a₂) (r ≫ b₂)).left z J) := fun a₁ b₁ a₂ b₂ l₁ l₂ l₃ T' r z J hJ => by
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, adjPair3_comp, ← Over.comp_left,
      ← Over.comp_left, comp_lift, comp_lift]
  have gn : ∀ (a₁ b₁ a₂ b₂ l₁ l₂ l₃ : G3 G' ⟶ G'), (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ w (adjPair3 gp l₁ l₂ l₃))
      (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ t (lift a₁ b₁).left) (LB.pullGen P _ _ t (lift a₂ b₂).left))).IsGen :=
    fun _ _ _ _ _ _ _ => DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hw _)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
  have key := gen_unique' hP (fun V _ k => ?_) _ e.left he sj (gn a b 1 1 k₁ k₂ k₃) (gn a₁ b₁ a₂ b₂ l₁ l₂ l₃)
    (fun y I hI => ?_) _ ρ.left z J hJ
  · rwa [ev _ _ _ _ _ _ _ ρ hJ, ev _ _ _ _ _ _ _ ρ hJ, MonObj.comp_one] at key
  · simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact hF V k
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h0
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h0
    refine (ev _ _ _ _ _ _ _ e hI).trans (Eq.trans ?_ (ev _ _ _ _ _ _ _ e hI).symm)
    simp only [e]
    rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, MonObj.comp_one]
end GlobalTheory
