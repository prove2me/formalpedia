-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_descent_of_invGen_of_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:51.97055+00:00
-- url     : https://prove2.me/submissions/fb7dd763-f9a2-4736-b3c6-4c20d4cdb953

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfInvGenOfInvariants
import Theorems.Thm_GlobalTheory_LinDescent_FunctionsAreInvariants_exists_descend
import Theorems.Thm_GlobalTheory_LinDescent_FunctionsAreInvariants_unit_ext
import Theorems.Thm_GlobalTheory_LinDescent_LocTransitive_exists_descend
import Theorems.Thm_GlobalTheory_LinDescent_glue_fn
import Theorems.Thm_GlobalTheory_LinDescent_isUnit_gs_iff
import Theorems.Thm_GlobalTheory_LinDescent_isUnit_of_mem_basicOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}
namespace GlobalTheory.LinDescent
theorem _root_.solution [Surjective π] (hL : L.IsLB)
    (hπ : ∀ c, t c ≫ π = π) (h : FunctionsAreInvariants t π) {u : ∀ c, LB.Gen (twist L (t c))}
    (V : Y → Y.Opens) (hV : ∀ y, y ∈ V y) (e : ∀ y i, Γ(X, π ⁻¹ᵁ V y ⊓ L.U i)ˣ)
    (he : ∀ y, IsInvGen u (π ⁻¹ᵁ V y) (e y)) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  have hmem : ∀ (U : Y.Opens) c {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ U →
      (r ≫ t c) z ∈ π ⁻¹ᵁ U := fun U c Z r z hz => by
    change ((r ≫ t c) ≫ π) z ∈ U
    rw [Category.assoc, hπ]
    exact hz
  have H : ∀ y y', ∃ g : Γ(Y, V y ⊓ V y')ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i,
      r z ∈ π ⁻¹ᵁ V y → r z ∈ π ⁻¹ᵁ V y' → r z ∈ L.U i →
      gm (r ≫ π) z _ g = gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹ := fun y y' => by
    let O : L.ι → X.Opens := fun i => π ⁻¹ᵁ (V y ⊓ V y') ⊓ L.U i
    have l : ∀ i, O i ≤ π ⁻¹ᵁ V y ⊓ L.U i := fun i x hx => ⟨hx.1.1, hx.2⟩
    have l' : ∀ i, O i ≤ π ⁻¹ᵁ V y' ⊓ L.U i := fun i x hx => ⟨hx.1.2, hx.2⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ O i →
        gs r z (O i) (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val =
        (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val := fun Z r z i hz => by
      rw [gs_unit r z _ hz, map_mul, map_inv, gm_res r z _ hz, gm_res r z _ hz]
    obtain ⟨ρ, hρ⟩ := glue_fn (π ⁻¹ᵁ (V y ⊓ V y')) O (fun _ => inf_le_left)
      (fun x hx => (exists_chart hL x).imp fun i hi => ⟨hx, hi⟩)
      (fun i => (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val) (fun i j x hi hj => by
        rw [v _ (𝟙 X) x i hi, v _ (𝟙 X) x j hj, (he y).1 _ (𝟙 X) x i j hi.1.1 hi.2 hj.2,
          (he y').1 _ (𝟙 X) x i j hi.1.2 hi.2 hj.2, ← div_eq_mul_inv, mul_div_mul_left_eq_div,
          div_eq_mul_inv])
    have hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ (V y ⊓ V y') →
        r z ∈ L.U i → gs r z _ ρ = (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val :=
      fun Z r z i h1 h2 => (hρ Z r z i ⟨h1, h2⟩).trans (v Z r z i ⟨h1, h2⟩)
    obtain ⟨a, ha⟩ := h.exists_descend (V y ⊓ V y') ρ fun c Z r z hz => by
      obtain ⟨i, hi⟩ := exists_chart hL (r z)
      obtain ⟨k, hk⟩ := exists_chart hL ((r ≫ t c) z)
      rw [hρ' Z r z i hz hi, hρ' Z (r ≫ t c) z k (hmem _ c r z hz) hk,
        (he y).2 c Z r z i k hz.1 hi hk, (he y').2 c Z r z i k hz.2 hi hk,
        ← div_eq_mul_inv (_ * _), mul_div_mul_left_eq_div, div_eq_mul_inv]
    have hu : IsUnit a := isUnit_of_mem_basicOpen a fun b hb => by
      obtain ⟨x, rfl⟩ := π.surjective b
      obtain ⟨i, hi⟩ := exists_chart hL x
      refine (isUnit_gs_iff (𝟙 X ≫ π) x (V y ⊓ V y') hb a).1 ?_
      rw [ha _ (𝟙 X) x hb, hρ' _ (𝟙 X) x i hb hi]
      exact Units.isUnit _
    refine ⟨hu.unit, fun Z r z i h1 h2 hi => Units.ext ?_⟩
    exact (gs_unit (r ≫ π) z (V y ⊓ V y') ⟨h1, h2⟩ hu.unit).symm.trans
      ((ha Z r z ⟨h1, h2⟩).trans (hρ' Z r z i ⟨h1, h2⟩ hi))
  choose g hg using H
  let M : LB Y := ⟨Y, V, g⟩
  refine ⟨M, ⟨eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hV y⟩, fun y => ?_,
    fun y₁ y₂ y₃ => ?_⟩, ?_⟩
  · refine h.unit_ext fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine (gm_res (𝟙 X ≫ π) x _ hx _).trans ((hg y y _ (𝟙 X) x i hx hx hi).trans ?_)
    rw [mul_inv_cancel, map_one]
  · refine h.unit_ext fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₁ y₂ _ (𝟙 X) x i hx.1.1 hx.1.2 hi))
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₂ y₃ _ (𝟙 X) x i hx.1.2 hx.2 hi)))).trans
      (Eq.trans ?_ ((gm_res (𝟙 X ≫ π) x _ hx _).trans
        (hg y₁ y₃ _ (𝟙 X) x i hx.1.1 hx.2 hi)).symm)
    rw [mul_comm, mul_assoc, inv_mul_cancel_left]
  · have l : ∀ p : (PUnit → Y) × L.ι, (M.pull π).U p.1 ⊓ L.U p.2 ≤
        π ⁻¹ᵁ V (p.1 PUnit.unit) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.1 hx.1, hx.2⟩
    let w : LB.Iso L (M.pull π) := ⟨fun p => (res (l p) (e (p.1 PUnit.unit) p.2))⁻¹⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (y : Y) i, π (r z) ∈ V y → r z ∈ L.U i →
        gw w r z y i = (gm r z _ (e y i))⁻¹ := fun Z r z y i h1 h2 =>
      (map_inv _ _).trans (congrArg _ (gm_res r z (l (fun _ => y, i))
        ⟨(mem_pull (L := M)).2 h1, h2⟩ _))
    refine ⟨w, (isGen_iff w).2 fun Z r z y y' i i' h1 h2 h3 h4 => ?_⟩
    rw [v Z r z y i h1 h3, v Z r z y' i' h2 h4]
    refine Eq.trans ?_ (congrArg (· * _ * _) (hg y y' Z r z i' h1 h2 h4)).symm
    rw [(he y).1 Z r z i i' h1 h3 h4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
end GlobalTheory.LinDescent
