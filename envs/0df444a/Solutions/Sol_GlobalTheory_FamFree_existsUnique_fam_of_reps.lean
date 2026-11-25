-- Prove2me | solution 1 for GlobalTheory.FamFree.existsUnique_fam_of_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:16:46.86201+00:00
-- url     : https://prove2.me/submissions/f95f1d3b-60f2-41b8-b6da-d9c0981ef36a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Theorems.Thm_GlobalTheory_FamFree_eq_of_eq_add_nsmul
import Theorems.Thm_GlobalTheory_FamFree_exists_fam_single

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamFree
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamFree
theorem _root_.solution (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) {C : Type*}
    (rep : C → D.X) (hrep : ∀ α : D.X, ∃! c, ∃ mu, rep c + k • mu = α) (σ : ∀ c, FamSec D F k (rep c)) :
    ∃! s : Fam D F k, ∀ c, s.s (rep c) = σ c := by
  choose cl hcl hcl' using hrep
  choose f hf _ using fun c => exists_fam_single hG hB hk (rep c) (σ c)
  have key : ∀ (α β : D.X) (c : C), cl β = c → (f (cl β)).s β = (f c).s β := by
    rintro α β c rfl; rfl
  refine ⟨⟨fun β => (f (cl β)).s β, fun mu α u hu hc => ?_⟩, fun c => ?_, fun s hs => ?_⟩
  · have e : cl (α + k • mu) = cl α := by
      obtain ⟨nu, hnu⟩ := hcl α
      exact (hcl' (α + k • mu) (cl α) ⟨nu + mu, by rw [smul_add, ← add_assoc, hnu]⟩).symm
    have := (f (cl α)).fe mu α u hu hc
    rw [← key α _ _ e] at this
    exact this
  · have e : cl (rep c) = c := (hcl' (rep c) c ⟨0, by rw [smul_zero, add_zero]⟩).symm
    exact (key (rep c) _ _ e).trans (hf c)
  · refine fam_ext fun α j => ?_
    have := eq_of_eq_add_nsmul hG s (f (cl α)) (hcl α) ((hs (cl α)).trans (hf (cl α)).symm)
    rw [this]
end GlobalTheory.FamFree
