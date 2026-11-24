-- Prove2me | solution 1 for GlobalTheory.SegreCoord.killed_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:06.062509+00:00
-- url     : https://prove2.me/submissions/ba507df0-f414-4932-a498-a36eb989c265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
variable {R : Type} [CommRing R] (I : Ideal (MvPolynomial σ R))
namespace GlobalTheory.SegreCoord
theorem _root_.solution (β : R →+* T) (w : σ × σ → T) :
    (∀ G ∈ segreIdeal I, MvPolynomial.eval₂ β w G = 0) ↔ RankOne I β w := by
  constructor
  · intro h
    refine ⟨fun a b c d => ?_, fun b F hF => ?_, fun a F hF => ?_⟩
    · have := h _ (Ideal.subset_span (Or.inl (Or.inl ⟨a, b, c, d, rfl⟩)))
      simpa [sub_eq_zero] using this
    · have := h _ (Ideal.subset_span (Or.inl (Or.inr ⟨b, F, hF, rfl⟩)))
      rwa [MvPolynomial.eval₂_rename] at this
    · have := h _ (Ideal.subset_span (Or.inr ⟨a, F, hF, rfl⟩))
      rwa [MvPolynomial.eval₂_rename] at this
  · rintro ⟨h₁, h₂, h₃⟩ G hG
    have : segreIdeal I ≤ RingHom.ker (MvPolynomial.eval₂Hom β w) := by
      rw [segreIdeal, Ideal.span_le]
      rintro _ ((⟨a, b, c, d, rfl⟩ | ⟨b, F, hF, rfl⟩) | ⟨a, F, hF, rfl⟩)
      · simp [h₁ a b c d]
      · exact (MvPolynomial.eval₂_rename _ _ _ _).trans (h₂ b F hF)
      · exact (MvPolynomial.eval₂_rename _ _ _ _).trans (h₃ a F hF)
    exact this hG
end GlobalTheory.SegreCoord
