-- Prove2me | solution 1 for GlobalTheory.SectionTheta.quot_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:52.011809+00:00
-- url     : https://prove2.me/submissions/4a20865e-32ec-4fe9-9067-5c44f301aebb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.SectionTheta
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.SectionTheta
theorem _root_.solution (u : HolUnif A L g) (z : Fin g → ℂ)
    (hhom : ∀ U : A.left.Opens, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U →
      ∃ e : Γ(A.left, U) →+* ℂ, ∀ f, valAt' (u.ex z).left U f = e f)
    (hres : ∀ (U V : A.left.Opens) (h : V ≤ U) (f : Γ(A.left, U)), ⊤ ≤ (u.ex z).left ⁻¹ᵁ V →
      valAt' (u.ex z).left V (resG A.left h f) = valAt' (u.ex z).left U f)
    (n : ℕ) (s : (lbPow L n).Sec) (j j' : (lbPow L n).ι)
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j') :
    valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n =
      valAt' (u.ex z).left ((lbPow L n).U j') (s.f j') / u.fr (j' PUnit.unit) z ^ n := by
  have hW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((lbPow L n).U j ⊓ (lbPow L n).U j') :=
    fun p hp => ⟨hj hp, hj' hp⟩
  have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := Cartier.lbPow_U L n j ▸ hj
  have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j' PUnit.unit) := Cartier.lbPow_U L n j' ▸ hj'
  have hW' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
    fun p hp => ⟨hi hp, hi' hp⟩
  obtain ⟨e, he⟩ := hhom _ hW
  have h1 := hres _ _ (inf_le_left : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j) hW
  have h2 := hres _ _ (inf_le_right : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j') hW
  have h3 := hres _ _ (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
    (L.g (j PUnit.unit) (j' PUnit.unit)).val hW
  have hc : resG A.left (inf_le_left : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j) =
      (resG A.left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
        (L.g (j PUnit.unit) (j' PUnit.unit)).val) ^ n *
      resG A.left (inf_le_right : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j') := by
    refine (s.compat j j').trans ?_
    exact congrArg (· * _) ((congrArg Units.val (Cartier.lbPow_g L n j j')).trans
      (Units.val_pow_eq_pow_val _ _))
  have hfr := u.fr_compat _ _ z hW'
  have hne := u.fr_ne _ z hi
  have hne' := u.fr_ne _ z hi'
  rw [← h1, ← h2, hc, he, map_mul, map_pow, ← he, ← he, h3]
  rw [hfr] at hne ⊢
  have hg := left_ne_zero_of_mul hne
  rw [mul_pow]
  field_simp
end GlobalTheory.SectionTheta
