-- Prove2me | solution 1 for GlobalTheory.exists_smul_eq_of_eq_on_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:38.376418+00:00
-- url     : https://prove2.me/submissions/255a77e6-ae25-4c02-83aa-20ad05f92960

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Theorems.Thm_GlobalTheory_exists_smul_apply_eq_of_eq_on_invariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) : ∃ g : G, ∀ b, y b = x (g • b) := by
  classical
  by_contra hne
  push Not at hne
  choose c hc using hne
  have := Fintype.ofFinite G
  let e := Fintype.equivFin G
  let p : Polynomial B := ∑ g : G, Polynomial.C (c g) * Polynomial.X ^ (e g : ℕ)
  have hcoef : ∀ g, p.coeff (e g) = c g := by
    intro g
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single g (fun g' _ hg' => if_neg (fun hh => hg' (e.injective (Fin.ext hh)).symm))
      (by simp), if_pos rfl]
  have hyp : ∀ q : Polynomial B, (∀ g : G, g • q = q) →
      Polynomial.mapRingHom x q = Polynomial.mapRingHom y q := by
    intro q hq
    ext n
    simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hq]
  obtain ⟨g, hg⟩ := exists_smul_apply_eq_of_eq_on_invariants (G := G)
    (Polynomial.mapRingHom x) (Polynomial.mapRingHom y) hyp p
  have hgc := congrArg (fun q => q.coeff (e g)) hg
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_smul, hcoef] at hgc
  exact hc g hgc
end GlobalTheory
