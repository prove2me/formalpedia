-- Prove2me | solution 1 for GlobalTheory.KS.Primitive.cech_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:07.660714+00:00
-- url     : https://prove2.me/submissions/8c02a849-7fd8-4614-a33c-17e1a813b739

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CechPrimitive
import Theorems.Thm_GlobalTheory_KS_Primitive_rsT_eq_rs
import Theorems.Thm_GlobalTheory_KS_Primitive_rs_pbT
import Theorems.Thm_GlobalTheory_KS_Primitive_app_pbT
import Theorems.Thm_GlobalTheory_KS_Primitive_le_pre_inf
import Theorems.Thm_GlobalTheory_KS_Primitive_pbT_coc
import Theorems.Thm_GlobalTheory_KS_Primitive_exists_split
import Theorems.Thm_GlobalTheory_KS_Primitive_iSup_triple
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_kuenneth_injective
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.KS.Primitive
open GlobalTheory.KuennethOne
variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}
private lemma preimage_le_preimage_of_comp_eq {X₁ X₂ X₃ : Scheme.{0}} (s : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (g : X₁ ⟶ X₃)
    (e : s ≫ m = g) {W : X₂.Opens} {O : X₃.Opens} (h : W ≤ m ⁻¹ᵁ O) : s ⁻¹ᵁ W ≤ g ⁻¹ᵁ O := by
  subst e
  intro x hx
  show (s ≫ m) x ∈ O
  rw [Scheme.Hom.comp_apply]
  exact h hx
private lemma presheaf_map_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (h' : O' ≤ O) :
    (T.presheaf.map (homOfLE h').op).hom (pbT f s O) = pbT f s O' :=
  rs_pbT f s h h'
set_option maxHeartbeats 1600000 in
private theorem cech_coboundary_mul_sub_fst_sub_snd : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) := by
  intro hL _ _ K _ P₀ I U c hU hc
  have : IsProper P₀.A.hom := P₀.isAb.proper
  have hsub : Subsingleton (𝟙_ (Over (Sp K))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  let _ : Inhabited (𝟙_ (Over (Sp K))).left := inferInstanceAs (Inhabited (Spec (CommRingCat.of K)))
  have hbij : Function.Bijective P₀.A.hom.appTop.hom := hL.globalFns _ P₀.A P₀.isAb
  let e : 𝟙_ (Over (Sp K)) ⟶ P₀.A := MonObj.one
  let g₀ : P₀.A.left ⟶ P₀.A.left := (toUnit P₀.A ≫ e).left
  let m := (fst P₀.A P₀.A * snd P₀.A P₀.A).left
  let p := (fst P₀.A P₀.A).left
  let q := (snd P₀.A P₀.A).left

  have hpt : ∀ x : P₀.A.left, g₀ x = e.left default := by
    intro x
    show ((toUnit P₀.A).left ≫ e.left) x = _
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have cov : ∀ y : P₀.A.left, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨i₀, hi₀⟩ := cov (e.left default)
  have hg : ⊤ ≤ g₀ ⁻¹ᵁ U i₀ := fun x _ => by
    show g₀ x ∈ U i₀
    rw [hpt x]
    exact hi₀

  have es_m : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (mul_one (𝟙 P₀.A))
  have es_p : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ p = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]
    rfl
  have es_q : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ q = g₀ := by
    rw [← Over.comp_left, lift_snd]
  have et_m : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (one_mul (𝟙 P₀.A))
  have et_p : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ p = g₀ := by
    rw [← Over.comp_left, lift_fst]
  have et_q : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ q = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]
    rfl
  let V : I × I × I → (P₀.A ⊗ P₀.A).left.Opens := fun α =>
    m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2
  have hVm : ∀ α, V α ≤ m ⁻¹ᵁ U α.1 := fun α => inf_le_left.trans inf_le_left
  have hVp : ∀ α, V α ≤ p ⁻¹ᵁ U α.2.1 := fun α => inf_le_left.trans inf_le_right
  have hVq : ∀ α, V α ≤ q ⁻¹ᵁ U α.2.2 := fun α => inf_le_right
  obtain ⟨ψ, hK⟩ := kuenneth_injective K P₀.A P₀.A e e inferInstance inferInstance inferInstance
    inferInstance hbij hbij (I × I × I) V (iSup_triple hU m p q)
    (fun a b => pbT m (c a.1 b.1) (V a ⊓ V b) - pbT p (c a.2.1 b.2.1) (V a ⊓ V b) -
      pbT q (c a.2.2 b.2.2) (V a ⊓ V b))
    (by
      intro a b d
      have w1 : V a ⊓ V b ⊓ V d ≤ V a := inf_le_left.trans inf_le_left
      have w2 : V a ⊓ V b ⊓ V d ≤ V b := inf_le_left.trans inf_le_right
      have w3 : V a ⊓ V b ⊓ V d ≤ V d := inf_le_right
      simp only [map_sub]
      rw [presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm b)) (inf_le_right.trans (hVm d))),
        presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp b)) (inf_le_right.trans (hVp d))), presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq b)) (inf_le_right.trans (hVq d))),
        presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm d))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp d))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq d)))]
      have cm := pbT_coc hc m a.1 b.1 d.1 (w1.trans (hVm a)) (w2.trans (hVm b)) (w3.trans (hVm d))
      have cp := pbT_coc hc p a.2.1 b.2.1 d.2.1 (w1.trans (hVp a)) (w2.trans (hVp b)) (w3.trans (hVp d))
      have cq := pbT_coc hc q a.2.2 b.2.2 d.2.2 (w1.trans (hVq a)) (w2.trans (hVq b)) (w3.trans (hVq d))
      linear_combination cm - cp - cq)
    (by
      let s := (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.1)
        (fun α => α.2.2) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ es_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s p _ es_p (hVp α)) (fun α => preimage_le_preimage_of_comp_eq s q _ es_q (hVq α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) es_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p (𝟙 _) es_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q g₀ es_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b)))]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
    (by
      let s := (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.2)
        (fun α => α.2.1) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ et_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s q _ et_q (hVq α)) (fun α => preimage_le_preimage_of_comp_eq s p _ et_p (hVp α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) et_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p g₀ et_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q (𝟙 _) et_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), sub_right_comm]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
  unfold IsCob
  refine ⟨fun a => -ψ a, fun a b => (hK a b).trans ?_⟩
  rw [rsT_eq_rs _ inf_le_right, rsT_eq_rs _ inf_le_left, map_neg, map_neg]
  exact (neg_sub_neg _ _).symm
end GlobalTheory.KS.Primitive
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Primitive
open GlobalTheory.KuennethOne
variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}
namespace GlobalTheory.KS.Primitive
theorem _root_.solution : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) :=
  cech_coboundary_mul_sub_fst_sub_snd
end GlobalTheory.KS.Primitive
