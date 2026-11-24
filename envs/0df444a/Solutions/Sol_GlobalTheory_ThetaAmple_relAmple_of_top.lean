-- Prove2me | solution 1 for GlobalTheory.ThetaAmple.relAmple_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:29:54.729388+00:00
-- url     : https://prove2.me/submissions/e18e7262-0256-4dfc-9b1c-afd7cde41584

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple
namespace GlobalTheory.ThetaAmple
theorem _root_.solution {X : Over (Sp ℂ)} {L : LB X.left}
    (h : ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (Out.powOver X L ⊤ N),
      (⨆ i, Out.nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
        ∃ r : Fin (M + 1) → Γ((X.hom ⁻¹ᵁ ⊤).toScheme, Out.nonzeroLocus (s i)),
          (∀ j k, ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ (Out.powOver X L ⊤ N).U k)).op).hom
                ((s j).f k) =
            ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ Out.nonzeroLocus (s i))).op).hom (r j) *
            ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ (Out.powOver X L ⊤ N).U k)).op).hom
                ((s i).f k)) ∧
          Function.Surjective (MvPolynomial.eval₂Hom
            ((X.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom r)) : Out.RelAmple X L := by
  intro U hU
  by_cases hne : (default : PrimeSpectrum ℂ) ∈ U
  · have : U = ⊤ := top_le_iff.1 fun p _ => by
      rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) p default]
    subst this
    exact h
  · have he : IsEmpty (X.hom ⁻¹ᵁ U).toScheme := ⟨fun y => hne (by
      have := y.2
      rwa [← Subsingleton.elim (α := PrimeSpectrum ℂ) (X.hom y.1) default])⟩
    have hb : ∀ V : (X.hom ⁻¹ᵁ U).toScheme.Opens, V = ⊥ := fun V => le_bot_iff.1 fun y _ => he.elim y
    have hs : ∀ V : (X.hom ⁻¹ᵁ U).toScheme.Opens, Subsingleton Γ((X.hom ⁻¹ᵁ U).toScheme, V) := fun V => by
      rw [hb V]; infer_instance
    refine ⟨1, le_rfl, 0, fun _ => ⟨fun _ => 0, fun _ _ => Subsingleton.elim _ _⟩, (hb _).trans (hb _).symm,
      fun i => ⟨by rw [hb (Out.nonzeroLocus _)]; exact isAffineOpen_bot _, fun _ => 0,
        fun _ _ => Subsingleton.elim _ _, fun d => ⟨0, Subsingleton.elim _ _⟩⟩⟩
end GlobalTheory.ThetaAmple
