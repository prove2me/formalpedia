-- Prove2me | solution 1 for GlobalTheory.exists_local_unit_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:21.753067+00:00
-- url     : https://prove2.me/submissions/cbc227df-9f63-4817-83d9-620709550b93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_single
import Theorems.Thm_GlobalTheory_TorsorUnit_IsTorsorOn_of_equiv
import Theorems.Thm_GlobalTheory_TorsorUnit_exists_homogeneous
import Theorems.Thm_GlobalTheory_TorsorUnit_pt_appLE
import Theorems.Thm_GlobalTheory_TorsorUnit_exists_eq_pt
import Theorems.Thm_GlobalTheory_TorsorUnit_exists_coaction
import Theorems.Thm_GlobalTheory_TorsorUnit_isTorsorOn
import Theorems.Thm_GlobalTheory_TorsorUnit_faithfullyFlat_appLE
import Theorems.Thm_GlobalTheory_SplitTorusPoints_coord_single


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
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open TorsorUnit SplitTorusPoints
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → IsAffineHom q.left → ∀ (χ : X) (b : B.left), ∃ (V : B.left.Opens) (_ : b ∈ V) (u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ), ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u.val = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u.val := by
  intro S X _ G B _ _ q i _ _ _ _ _ hi _ χ b
  obtain ⟨V, hV, hbV, -⟩ := exists_isAffineOpen_mem_and_subset (x := b) (U := ⊤) trivial
  have hU : IsAffineOpen (q.left ⁻¹ᵁ V) := hV.preimage q.left
  obtain ⟨ρ, hρ⟩ := exists_coaction hi hU
  have htor : ∀ (R : Type) [CommRing R], IsTorsorOn R (q.left.appLE V _ le_rfl).hom ρ :=
    fun R _ => (isTorsorOn hi hV hU hρ (Spec (.of R))).of_equiv
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  obtain ⟨p, rfl⟩ := hV.range_fromSpec.ge hbV
  obtain ⟨a, ha, c, c', hcc, hc⟩ := exists_homogeneous (faithfullyFlat_appLE q.left hV hU) htor χ
    p.asIdeal p.isPrime.ne_top
  have hle : q.left ⁻¹ᵁ B.left.basicOpen a ≤ q.left ⁻¹ᵁ V :=
    fun _ hx => B.left.basicOpen_le a hx
  let r := (G.left.presheaf.map (homOfLE hle).op).hom
  have hunit : IsUnit (r c) := by
    apply isUnit_of_mul_isUnit_left (y := r c')
    rw [← map_mul, hcc]
    have h1 := (B.left.toRingedSpace.isUnit_res_basicOpen a).map
      (q.left.app (B.left.basicOpen a)).hom
    have h2 := q.left.appLE_map (U := V) le_rfl (homOfLE hle).op
    have h3 := q.left.map_appLE (V := q.left ⁻¹ᵁ B.left.basicOpen a) le_rfl
      (homOfLE (B.left.basicOpen_le a)).op
    have h4 := congr($(h2.trans h3.symm).hom a)
    rw [Scheme.Hom.app_eq_appLE] at h1
    exact h4 ▸ h1
  have hr : ∀ {Z : Scheme.{0}} (g : Z ⟶ G.left) (θ) (_ : g = pt hU θ)
      (h : ⊤ ≤ g ⁻¹ᵁ q.left ⁻¹ᵁ B.left.basicOpen a), (g.appLE _ ⊤ h).hom (r c) = θ c := by
    rintro Z g θ rfl h
    have h1 := congr($((pt hU θ).map_appLE h (homOfLE hle).op).hom c)
    rw [pt_appLE] at h1
    exact h1
  refine ⟨B.left.basicOpen a, ?_, hunit.unit, fun Z t g h₁ h₂ => ?_⟩
  · have : p ∈ hV.fromSpec ⁻¹ᵁ B.left.basicOpen a := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact ha
    exact this
  · obtain ⟨θ, hθ⟩ := exists_eq_pt hU g.left (h₂.trans fun _ hx => hle hx)
    rw [IsUnit.unit_spec, hr _ _ (hρ Z t g θ hθ), hr _ _ hθ, RingHom.comp_apply, hc, ev_single,
      toHom_val, coord_single, mul_comm]
end GlobalTheory
