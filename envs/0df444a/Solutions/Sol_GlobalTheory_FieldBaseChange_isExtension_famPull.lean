-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isExtension_famPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:06.083187+00:00
-- url     : https://prove2.me/submissions/f122fb5f-f723-4806-904c-539bbcc5550c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_finset_representatives
import Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_termPull
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsCoord_natural
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_of_proj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (E F : Type) [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) : IsExtension (famPull D E F hG k) := by
  obtain ⟨T, hT⟩ := exists_finset_representatives D.X hk
  choose Θ hΘ using exists_isShift D E hG k
  choose Θ' hΘ' using exists_isShift D F hG k
  refine IsExtension.of_proj _ (termPull D E F k) (isExtension_termPull D E F k) (famProj D _ k) (famProj D F k)
    (fun _ _ => rfl) (fun x hx => fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) (hx α)) T
    (fun v hv => fam_ext fun β j => ?_) fun ℓ Λ hΛ x => ⟨⟨fun α => Λ α (x.s α), ?_⟩, fun _ => rfl⟩
  · obtain ⟨α, hα, mu, rfl⟩ := hT β
    have e : Θ mu α (v.s α) = 0 := (congrArg (Θ mu α) (hv α hα)).trans (map_zero _)
    exact congrArg (fun q => LB.Sec.f q j) (((famFE_iff hG hΘ v.s).1 v.fe mu α).trans e)
  · refine (famFE_iff hG hΘ _).2 fun mu α => ?_
    exact (congrArg (Λ _) ((famFE_iff hG hΘ' x.s).1 x.fe mu α)).trans
      (IsCoord.natural (isExtension_termPull D E F k α).span (hΛ α) (hΛ _) (Θ mu α) (Θ' mu α)
        (shift_termPull (hΘ mu α) (hΘ' mu α)) _)
end GlobalTheory.FieldBaseChange
