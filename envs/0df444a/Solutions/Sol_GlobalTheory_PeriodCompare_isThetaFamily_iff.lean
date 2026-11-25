-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.isThetaFamily_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:04:31.921846+00:00
-- url     : https://prove2.me/submissions/2a208900-96e4-45fd-ac91-8e4d1b13ee01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_le_pull_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution (L : RigLB G) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ S))
    (ex : ∀ b : Fin m → ℂ, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) :
    IsThetaFamily L B y ex θ ↔
      HolOn (B ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun p => ((ex p.1 p.2).left : Sp ℂ ⟶ G.left)) ∧
      (∀ b ∈ B, (ex b 0).left = y b ≫ eSec G) ∧ Tor.IsThetaFrame L B y (fun b z => (ex b z).left) θ := by
  have hf : ∀ b z, fibrePt (ex b z) ≫ pullback.fst G.hom (y b) = (ex b z).left := fun b z => pullback.lift_fst ..
  have hs : ∀ b z, fibrePt (ex b z) ≫ pullback.snd G.hom (y b) = 𝟙 _ := fun b z => pullback.lift_snd ..
  constructor
  · rintro ⟨fr, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
    refine ⟨h1, h2, fun j p => fr j p.1 p.2, h3, fun j b z hb => h4 j b hb z, fun j j' b z hb => h5 j j' b hb z,
      fun j b hb hj => h6 (fun _ => j) b hb ((le_pull_iff _ _ _ _).2 (by rw [← h2 b hb]; exact hj)), fun b hb => ?_⟩
    obtain ⟨s, hsec⟩ := h7 b hb
    refine ⟨s, fun j z x hx hx' hj => ?_⟩
    obtain rfl : x = fibrePt (ex b z) := pullback.hom_ext (hx.trans (hf b z).symm) (hx'.trans (hs b z).symm)
    exact hsec (fun _ => j) z ((le_pull_iff _ _ _ _).2 (by rw [hf]; exact hj))
  · rintro ⟨h1, h2, fr, h3, h4, h5, h6, h7⟩
    refine ⟨fun j b z => fr j (b, z), ⟨h1, h2, h3, fun j b hb z => h4 j b z hb, fun j j' b hb z => h5 j j' b z hb,
      fun j b hb hj => h6 (j PUnit.unit) b hb ?_⟩, fun b hb => ?_⟩
    · have := (le_pull_iff _ _ _ _).1 hj
      rw [← h2 b hb] at this
      exact this
    · obtain ⟨s, hsec⟩ := h7 b hb
      refine ⟨s, fun j z hj => hsec (j PUnit.unit) z _ (hf b z) (hs b z) ?_⟩
      have := (le_pull_iff _ _ _ _).1 hj
      rw [hf] at this
      exact this
end GlobalTheory.PeriodCompare
