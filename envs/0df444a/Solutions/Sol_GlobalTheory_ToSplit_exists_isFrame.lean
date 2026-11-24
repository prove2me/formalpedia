-- Prove2me | solution 1 for GlobalTheory.ToSplit.exists_isFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:04:46.177645+00:00
-- url     : https://prove2.me/submissions/7f0b77ce-0f7e-4231-9813-a266017b9299

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_GlobalTheory_ToSplit_gm_res_pre
import Theorems.Thm_GlobalTheory_ToSplit_unit_ext_of_cover
import Theorems.Thm_GlobalTheory_ToSplit_exists_unit_descent
import Theorems.Thm_GlobalTheory_ToSplit_exists_act
import Theorems.Thm_GlobalTheory_ToSplit_hasWeight_of_appLE
import Theorems.Thm_GlobalTheory_ToSplit_inv_eq_div_mul_inv
import Theorems.Thm_GlobalTheory_ToSplit_eSec_comp
import Theorems.Thm_GlobalTheory_ToSplit_isAffineHom_left
import Theorems.Thm_GlobalTheory_exists_local_unit_of_weight
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
variable {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
namespace GlobalTheory.ToSplit
theorem _root_.solution (χ : X) : ∃ (O : RigLB B) (u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ),
    IsFrame q i χ O u := by
  let J : Type := Σ V : B.left.Opens, {u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ // HasWeight q i χ V u}
  have l₁ : ∀ a b : J, q.left ⁻¹ᵁ (a.1 ⊓ b.1) ≤ q.left ⁻¹ᵁ a.1 := fun a b x hx => hx.1
  have l₂ : ∀ a b : J, q.left ⁻¹ᵁ (a.1 ⊓ b.1) ≤ q.left ⁻¹ᵁ b.1 := fun a b x hx => hx.2
  have hd : ∀ a b : J, ∃ g : Γ(B.left, a.1 ⊓ b.1)ˣ,
      pullU q.left _ g = res (l₂ a b) b.2.1 / res (l₁ a b) a.2.1 := fun a b =>
    exists_unit_descent q _ _ fun Z g₁ g₂ z e h₁ h₂ => by
      obtain ⟨t, rfl⟩ := exists_act hk e
      rw [map_div, map_div, gm_res_pre _ _ _ _ h₁, gm_res_pre _ _ _ _ h₁, gm_res_pre _ _ _ _ h₂,
        gm_res_pre _ _ _ _ h₂,
        a.2.2 Z t g₂ z h₂.1, b.2.2 Z t g₂ z h₂.2, mul_div_mul_left_eq_div]
  choose g hg using hd
  have hg' : ∀ (a b : J) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ a.1 →
      q.left (r z) ∈ b.1 → gm (r ≫ q.left) z (a.1 ⊓ b.1) (g a b) =
        gm r z _ b.2.1 / gm r z _ a.2.1 := fun a b Z r z h₁ h₂ => by
    have hm : q.left (r z) ∈ a.1 ⊓ b.1 := ⟨h₁, h₂⟩
    rw [← gm_pull r q.left z _ hm, hg, map_div, gm_res_pre _ _ _ _ hm, gm_res_pre _ _ _ _ hm]
  have hg'' : ∀ (a b : J) (y : G.left), q.left y ∈ a.1 → q.left y ∈ b.1 →
      gm q.left y (a.1 ⊓ b.1) (g a b) = gm (𝟙 _) y _ b.2.1 / gm (𝟙 _) y _ a.2.1 :=
    fun a b y h₁ h₂ => by rw [← hg' a b _ (𝟙 _) y h₁ h₂, Category.id_comp]
  let L : LB B.left := ⟨J, fun a => a.1, g⟩
  have hL : L.IsLB := by
    refine ⟨?_, fun a => ?_, fun a b c => ?_⟩
    · refine top_le_iff.1 fun x _ => ?_
      obtain ⟨V, hV, u, hu⟩ := exists_local_unit_of_weight S X G B q i ‹_› ‹_› ‹_› ‹_› ‹_› hk
        (isAffineHom_left hk) χ x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, u, hasWeight_of_appLE hk hu⟩, hV⟩
    · refine unit_ext_of_cover q.left fun y hy => ?_
      rw [gm_res _ _ _ hy, map_one]
      exact (hg'' a a y hy hy).trans (div_self' _)
    · refine unit_ext_of_cover q.left fun y hy => ?_
      rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy, gm_res _ _ _ hy]
      refine (congrArg₂ (· * ·) (hg'' a b y hy.1.1 hy.1.2) (hg'' b c y hy.1.2 hy.2)).trans
        (Eq.trans ?_ (hg'' a c y hy.1.1 hy.2).symm)
      rw [mul_comm, div_mul_div_cancel]
  have hm : ∀ (a : J) (z : (𝟙_ (Over S)).left), eSec B z ∈ a.1 → q.left (eSec G z) ∈ a.1 :=
    fun a z hz => by rwa [← eSec_comp (G := G) (q := q)] at hz
  have le : ∀ j : PUnit → J, (L.pull (eSec B)).U j ≤ eSec G ⁻¹ᵁ (q.left ⁻¹ᵁ (j PUnit.unit).1) :=
    fun j z hz => hm _ z (mem_pull.1 hz)
  let rig : LB.Gen (L.pull (eSec B)) :=
    ⟨fun j => (res (le j) (pullU (eSec G) _ (j PUnit.unit).2.1))⁻¹⟩
  have hrig : ∀ (j : PUnit → J) (z : (𝟙_ (Over S)).left), z ∈ (L.pull (eSec B)).U j →
      gm (𝟙 _) z ((L.pull (eSec B)).U j) (rig.s j) = (gm (eSec G) z _ (j PUnit.unit).2.1)⁻¹ :=
    fun j z hz => (map_inv _ _).trans (congrArg (·⁻¹) (gm_id_res_pull _ z (le j) hz _))
  have hgen : rig.IsGen := fun j j' => unit_ext fun z hz => by
    rw [map_mul, gm_res _ _ _ hz, gm_res _ _ _ hz, hrig j z hz.1, hrig j' z hz.2,
      gm_pull_g L (eSec B) (𝟙 _) z j j' hz.1 hz.2, Category.id_comp]
    have := hg' (j PUnit.unit) (j' PUnit.unit) _ (eSec G) z (le j hz.1) (le j' hz.2)
    rw [eSec_comp] at this
    refine Eq.trans ?_ (congrArg (· * _) this.symm)
    exact inv_eq_div_mul_inv _ _
  exact ⟨⟨L, rig, hL, hgen⟩, fun a => a.2.1, fun a => a.2.2, hg',
    fun a z hz => hrig (fun _ => a) z (mem_pull.2 hz)⟩
end GlobalTheory.ToSplit
