-- Prove2me | solution 1 for GlobalTheory.CubeLawCompare.iso_pull_of_locally_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:43:04.666036+00:00
-- url     : https://prove2.me/submissions/fc2a9d7a-b1cc-4e52-9029-7bace832540c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_RigidityTranslation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull
import Theorems.Thm_GlobalTheory_CubeLawCompare_gen_restrict_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CubeLawCompare
variable {Y T : Scheme.{0}}
namespace GlobalTheory.CubeLawCompare
theorem _root_.solution (p : Y ⟶ T) (hp : ∀ V : T.Opens, Function.Bijective (p.app V).hom)
    {M : LB Y} (hM : M.IsLB)
    (h : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen) :
    ∃ N : LB T, N.IsLB ∧ ∃ u : LB.Iso (N.pull p) M, u.IsGen := by
  choose V hV hc using h
  choose d hd using fun t => (gen_restrict_iff M _).1 (hc t)
  have inj : ∀ (O : T.Opens) (a b : Γ(T, O)ˣ),
      (∀ y : Y, p y ∈ O → gm p y O a = gm p y O b) → a = b := fun O a b hab => by
    have e : pullU p O a = pullU p O b := unit_ext fun y hy => by
      rw [gm_pull (𝟙 Y) p y O hy, gm_pull (𝟙 Y) p y O hy, Category.id_comp]
      exact hab y hy
    exact Units.ext ((hp O).1 (congrArg Units.val e))
  have ratio : ∀ t t' : T, ∃ g : Γ(T, V t ⊓ V t')ˣ, ∀ j (y : Y), p y ∈ V t → p y ∈ V t' → y ∈ M.U j →
      gm p y _ g = gm (𝟙 Y) y (p ⁻¹ᵁ V t' ⊓ M.U j) (d t' j) * (gm (𝟙 Y) y (p ⁻¹ᵁ V t ⊓ M.U j) (d t j))⁻¹ := by
    intro t t'
    have l₁ : ∀ j, p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j ≤ p ⁻¹ᵁ V t ⊓ M.U j := fun j y hy => ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j, p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j ≤ p ⁻¹ᵁ V t' ⊓ M.U j := fun j y hy => ⟨hy.1.2, hy.2⟩
    have v : ∀ j (y : Y) (hy : y ∈ p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j),
        gm (𝟙 Y) y _ (res (l₂ j) (d t' j) * (res (l₁ j) (d t j))⁻¹) =
          gm (𝟙 Y) y (p ⁻¹ᵁ V t' ⊓ M.U j) (d t' j) * (gm (𝟙 Y) y (p ⁻¹ᵁ V t ⊓ M.U j) (d t j))⁻¹ :=
      fun j y hy => by rw [map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy]
    obtain ⟨a, ha⟩ := glue_unit (p ⁻¹ᵁ (V t ⊓ V t')) (fun j => p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j)
      (fun _ => inf_le_left) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hM y
        exact Opens.mem_iSup.2 ⟨j, hy, hj⟩)
      (fun j => res (l₂ j) (d t' j) * (res (l₁ j) (d t j))⁻¹) (fun j j' y hy => by
        rw [v j y hy.1, v j' y hy.2, hd t j j' y hy.1.1.1 hy.1.2 hy.2.2,
          hd t' j j' y hy.1.1.2 hy.1.2 hy.2.2, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
    let E := RingEquiv.ofBijective _ (hp (V t ⊓ V t'))
    let g : Γ(T, V t ⊓ V t')ˣ := Units.map E.symm.toRingHom.toMonoidHom a
    have hg : pullU p _ g = a := Units.ext (E.apply_symm_apply a.val)
    refine ⟨g, fun j y h₁ h₂ hj => ?_⟩
    have hy : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j := ⟨⟨h₁, h₂⟩, hj⟩
    have e := gm_pull (𝟙 Y) p y (V t ⊓ V t') hy.1 g
    rw [Category.id_comp, hg] at e
    rw [← e, ← v j y hy, ← ha j, gm_res _ y _ hy]
  choose g hg using ratio
  let N : LB T := ⟨T, V, g⟩
  have hN : N.IsLB := by
    refine ⟨eq_top_iff.2 fun t _ => Opens.mem_iSup.2 ⟨t, hV t⟩, fun t => inj _ _ _ fun y hy => ?_,
      fun t t' t'' => inj _ _ _ fun y hy => ?_⟩
    · obtain ⟨j, hj⟩ := exists_chart hM y
      exact (gm_res p y _ hy _).trans ((hg t t j y hy hy hj).trans
        ((mul_inv_cancel _).trans (map_one _).symm))
    · obtain ⟨j, hj⟩ := exists_chart hM y
      rw [map_mul, gm_res p y _ hy, gm_res p y _ hy, gm_res p y _ hy]
      refine (congrArg₂ (· * ·) (hg t t' j y hy.1.1 hy.1.2 hj) (hg t' t'' j y hy.1.2 hy.2 hj)).trans
        (Eq.trans ?_ (hg t t'' j y hy.1.1 hy.2 hj).symm)
      rw [mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  have le : ∀ q : M.ι × (PUnit → T), M.U q.1 ⊓ (N.pull p).U q.2 ≤ p ⁻¹ᵁ V (q.2 PUnit.unit) ⊓ M.U q.1 :=
    fun q y hy => ⟨mem_pull (L := N).1 hy.2, hy.1⟩
  refine ⟨N, hN, ⟨fun q => res (le q) (d (q.2 PUnit.unit) q.1)⟩, fun q q' => unit_ext fun y hy => ?_⟩
  have h₁ : p y ∈ V (q.2 PUnit.unit) := mem_pull (L := N).1 hy.1.2
  have h₂ : p y ∈ V (q'.2 PUnit.unit) := mem_pull (L := N).1 hy.2.2
  have eN := gm_pull_g N p (𝟙 Y) y q.2 q'.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at eN
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.1 _)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div (N.pull p) M (𝟙 Y) y q q' hy).trans
    (congrArg (fun w => _ * w⁻¹) (eN.trans (hg _ _ q'.1 y h₁ h₂ hy.2.1))))
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q') hy.2 _)))).trans ?_
  rw [hd _ q.1 q'.1 y h₁ hy.1.1 hy.2.1, mul_inv_rev, inv_inv, _root_.mul_assoc, inv_mul_cancel_right]
end GlobalTheory.CubeLawCompare
