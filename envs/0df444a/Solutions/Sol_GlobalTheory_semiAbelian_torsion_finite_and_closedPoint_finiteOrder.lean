-- Prove2me | solution 1 for GlobalTheory.semiAbelian_torsion_finite_and_closedPoint_finiteOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:47.003927+00:00
-- url     : https://prove2.me/submissions/7dc99710-4b0a-45e3-995d-8da16a5bb8ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Theorems.Thm_GlobalTheory_SemiAbTorsion_finite_pow_eq_one_of_extension
import Theorems.Thm_GlobalTheory_SemiAbTorsion_finite_chars_pow_eq_one
import Theorems.Thm_GlobalTheory_SemiAbTorsion_finite_points_over
import Theorems.Thm_GlobalTheory_SemiAbTorsion_comp_pow_points
import Theorems.Thm_GlobalTheory_jacobson_closedPoints_tools_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open SemiAbTorsion
namespace GlobalTheory
theorem _root_.solution : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → (∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ G // x ^ n = 1}) ∧ (∀ (Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (w : G.left), IsClosed ({w} : Set G.left) → ∃ n : ℕ, 1 ≤ n ∧ ∀ (K : Type) [Field K] (t : Sp K ⟶ Z) (x : Over.mk t ⟶ G), Set.range x.left = {w} → x ^ n = 1) := by
  intro hB
  refine ⟨?_, ?_⟩
  · rintro K _ _ G _ _ ⟨E⟩ n hn
    letI := E.addCommGroup
    letI := E.finite
    letI := E.grpB
    haveI := E.q_hom
    haveI := E.i_hom
    have hk := E.isKernel
    refine finite_pow_eq_one_of_extension (IsMonHom.monoidHom E.i (𝟙_ (Over (Sp K))))
      (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp K)))) ?_ ?_ n ?_ (hB K E.B E.isAbelian n hn)
    · intro a b h
      exact hk.hom_ext h (toUnit_unique _ _)
    · intro x hx
      have hx' : x ≫ E.q = 1 := hx
      exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
    · haveI : IsDomain Γ((𝟙_ (Over (Sp K))).left, ⊤) :=
        inferInstanceAs (IsDomain Γ(Sp K, ⊤))
      haveI := finite_chars_pow_eq_one E.X Γ((𝟙_ (Over (Sp K))).left, ⊤) hn
      let e := splitTorusPointsEquiv (Sp K) E.X (𝟙_ (Over (Sp K)))
      refine Finite.of_injective (fun t => (⟨e t.1, by rw [← map_pow, t.2, map_one]⟩ :
        {t : Multiplicative E.X →* Γ((𝟙_ (Over (Sp K))).left, ⊤)ˣ // t ^ n = 1})) ?_
      intro a b h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro Z π _ G _ _ _ w hw
    haveI : Finite (G.left.residueField w) :=
      (jacobson_closedPoints_tools_int G.left (G.hom ≫ π)).2.1 w hw
    let t₀ : Sp (G.left.residueField w) ⟶ Z := G.left.fromSpecResidueField w ≫ G.hom
    haveI := finite_points_over π G (G.left.residueField w) t₀
    let x₀ : Over.mk t₀ ⟶ G := Over.homMk (G.left.fromSpecResidueField w) rfl
    refine ⟨Nat.card (Over.mk t₀ ⟶ G), Nat.card_pos, fun K _ t x hx => ?_⟩
    obtain ⟨⟨z, φ⟩, hz⟩ := (Scheme.SpecToEquivOfField K G.left).symm.surjective x.left
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hz
    obtain rfl : z = w := by
      have : x.left (default : Sp K) ∈ ({w} : Set G.left) := hx ▸ Set.mem_range_self _
      rw [← hz] at this
      have h2 : (Spec.map φ ≫ G.left.fromSpecResidueField z) (default : Sp K) ∈
          Set.range (G.left.fromSpecResidueField z) := ⟨_, rfl⟩
      rw [Scheme.range_fromSpecResidueField] at h2
      exact h2.symm.trans this
    let u : Over.mk t ⟶ Over.mk t₀ := Over.homMk (Spec.map φ) (by
      change Spec.map φ ≫ G.left.fromSpecResidueField z ≫ G.hom = t
      rw [← Category.assoc, hz]
      exact Over.w x)
    have hu : x = u ≫ x₀ := Over.OverMorphism.ext hz.symm
    rw [hu, ← comp_pow_points, pow_card_eq_one', MonObj.comp_one]
end GlobalTheory
