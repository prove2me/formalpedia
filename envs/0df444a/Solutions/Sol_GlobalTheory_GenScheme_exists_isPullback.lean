-- Prove2me | solution 1 for GlobalTheory.GenScheme.exists_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:02:07.005242+00:00
-- url     : https://prove2.me/submissions/460673b1-2f5d-4653-8877-9f1fb8b34411

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_pb_pb
import Theorems.Thm_GlobalTheory_GenScheme_pb_top_val
import Theorems.Thm_GlobalTheory_GenScheme_exists_hom
import Theorems.Thm_GlobalTheory_GenScheme_hom_ext
import Theorems.Thm_GlobalTheory_GenScheme_torus_hom_ext
import Theorems.Thm_GlobalTheory_GenScheme_exists_torus_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
open GlobalTheory.GenScheme
variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}
open SplitTorus
namespace GlobalTheory.GenScheme
theorem _root_.solution (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u)
    {V : Scheme.{0}} (v : V ⟶ B) (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ v ⁻¹ᵁ (N k).U (j k)) :
    ∃ p : (splitTorus V (κ →₀ ℤ)).left ⟶ G, IsPullback p (splitTorus V (κ →₀ ℤ)).hom q v := by
  let T := splitTorus V (κ →₀ ℤ)
  have lands : ∀ {Z : Scheme.{0}} (c : Z ⟶ V) k, ⊤ ≤ (c ≫ v) ⁻¹ᵁ (N k).U (j k) :=
    fun c k => c.preimage_mono (hj k)
  have lands' : ∀ {Z : Scheme.{0}} (a : Z ⟶ G) (c : Z ⟶ V) (_ : a ≫ q = c ≫ v) k,
      ⊤ ≤ a ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := fun a c h k => by
    rw [← Scheme.Hom.comp_preimage, h]; exact lands c k
  obtain ⟨p, hp, hpu⟩ := exists_hom hN hU (T.hom ≫ v) j (lands T.hom)
    fun k => (isUnit_val (𝟙 T) (Finsupp.single k 1)).unit
  have key : ∀ {Z : Over V} (m : Z ⟶ T) k (h : ⊤ ≤ (m.left ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)),
      (pb (m.left ≫ p) (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k))).val = val m (Finsupp.single k 1) := by
    intro Z m k h
    rw [← pb_pb m.left p _ ⊤ ⊤ (lands' p T.hom hp k) le_rfl, hpu, pb_top_val]
    exact (val_eq m _).symm
  have ex : ∀ s : PullbackCone q v, ∃ l : s.pt ⟶ T.left, l ≫ p = s.fst ∧ l ≫ T.hom = s.snd := by
    intro s
    obtain ⟨l, hl⟩ := exists_torus_hom (T := Over.mk s.snd)
      fun k => pb s.fst (q ⁻¹ᵁ (N k).U (j k)) ⊤ (lands' _ _ s.condition k) (u k (j k))
    have w : l.left ≫ T.hom = s.snd := Over.w l
    have w' : (l.left ≫ p) ≫ q = s.snd ≫ v := by
      rw [Category.assoc, hp, ← Category.assoc, w]
    refine ⟨l.left, hom_ext hu hU j _ _ (w'.trans s.condition.symm) (lands' _ _ s.condition)
      (lands' _ _ w') fun k => Units.ext ?_, w⟩
    exact (key l k _).trans (hl k)
  refine ⟨p, ⟨hp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (ex s).choose)
    (fun s => (ex s).choose_spec.1) (fun s => (ex s).choose_spec.2) fun s m h₁ h₂ => ?_⟩⟩
  obtain ⟨h₃, h₄⟩ := (ex s).choose_spec
  generalize (ex s).choose = l at h₃ h₄
  have : (Over.homMk m h₂ : Over.mk s.snd ⟶ T) = Over.homMk l h₄ := by
    refine torus_hom_ext fun k => ?_
    have hm : ⊤ ≤ (m ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := by rw [h₁]; exact lands' _ _ s.condition k
    have hl : ⊤ ≤ (l ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := by rw [h₃]; exact lands' _ _ s.condition k
    rw [← key (Over.homMk m h₂ : Over.mk s.snd ⟶ T) k hm, ← key (Over.homMk l h₄ : Over.mk s.snd ⟶ T) k hl]
    have aux : ∀ (a a' : s.pt ⟶ G) (_ : a = a') h h',
        pb a (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k)) = pb a' (q ⁻¹ᵁ (N k).U (j k)) ⊤ h' (u k (j k)) := by
      rintro a _ rfl _ _; rfl
    exact congrArg Units.val (aux _ _ (h₁.trans h₃.symm) _ _)
  exact congrArg (·.left) this
end GlobalTheory.GenScheme
