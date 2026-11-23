-- Prove2me | solution 1 for GlobalTheory.HolChart.exists_etale_coords_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:29.965643+00:00
-- url     : https://prove2.me/submissions/0596845b-ffe3-4919-b657-a957cd663c64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.HolChart
namespace GlobalTheory.HolChart
theorem _root_.solution {g : ℕ} {A : Type} [CommRing A] (c : ℂ →+* A)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (e : A →+* ℂ) (he : ∀ a, e (c a) = a) :
    ∃ φ : MvPolynomial (Fin g) ℂ →+* A, φ.comp MvPolynomial.C = c ∧ φ.Etale ∧
      ∀ i, e (φ (MvPolynomial.X i)) = 0 := by
  obtain ⟨φ, h1, h2⟩ := hc.exists_etale_mvPolynomial
  let a : Fin g → ℂ := fun i => e (φ (MvPolynomial.X i))
  let T : MvPolynomial (Fin g) ℂ ≃ₐ[ℂ] MvPolynomial (Fin g) ℂ :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (a i))
      (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i))
      (by ext i; simp) (by ext i; simp)
  have hC : ∀ x, φ (MvPolynomial.C x) = c x := fun x => by rw [← h1]; rfl
  refine ⟨φ.comp T.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · ext x
    simp [T, hC]
  · exact RingHom.Etale.respectsIso.2 φ T.toRingEquiv h2
  · intro i
    simp [T, hC, he, a]
end GlobalTheory.HolChart
