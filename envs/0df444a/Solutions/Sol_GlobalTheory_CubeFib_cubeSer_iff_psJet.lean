-- Prove2me | solution 1 for GlobalTheory.CubeFib.cubeSer_iff_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:42:18.804484+00:00
-- url     : https://prove2.me/submissions/e3cf8cee-c929-4c16-855b-b1c4a82ad872

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Theorems.Thm_GlobalTheory_CubeFib_psJet_eq_toJet_of_pos

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
open GlobalTheory GlobalTheory.CubeFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped BigOperators
attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type} [CommRing k] {d g : ℕ}
namespace GlobalTheory.CubeFib
theorem _root_.solution (hd : 0 < d) {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G) (i : L.L.ι) (Φ : PS k 3 d) :
    CubeSer c x i Φ ↔ ∀ m : ℕ,
      ∃ h : (⊤ : (Sp (JetR k (Fin 3 × Fin d) m)).Opens) ≤ (jet3 x m).left ⁻¹ᵁ (Theta G L.L).U (fun _ => i),
        (Semi.res h (pullU (jet3 x m).left _ (c.t.s fun _ => i))).val =
          (Scheme.ΓSpecIso (CommRingCat.of (JetR k (Fin 3 × Fin d) m))).inv.hom (psJet m Φ) := by
  refine forall_congr' fun m => ?_
  rw [psJet_eq_toJet_of_pos hd m Φ]
end GlobalTheory.CubeFib
