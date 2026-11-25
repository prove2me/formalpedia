-- Prove2me | solution 1 for GlobalTheory.TorsionCharacter.isAdicComplete_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:49.104536+00:00
-- url     : https://prove2.me/submissions/6d70b71a-1c72-4d67-8bbf-2bab94f51080

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacter
variable {O : Type} [CommRing O]
namespace GlobalTheory.TorsionCharacter
theorem _root_.solution {I J : Ideal O} [IsAdicComplete I O] {a b : ℕ} (h₁ : I ^ a ≤ J) (h₂ : J ^ b ≤ I) :
    IsAdicComplete J O := by
  letI : TopologicalSpace O := I.adicTopology
  haveI : IsTopologicalRing O := (I.ringFilterBasis).isTopologicalRing
  letI : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  haveI : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  have hI : IsAdic I := rfl
  have hJ : IsAdic J := by
    rw [isAdic_iff] at hI ⊢
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · refine AddSubgroup.isOpen_mono (H₁ := (I ^ (a * n)).toAddSubgroup) (H₂ := (J ^ n).toAddSubgroup) ?_ (hI.1 _)
      intro x hx
      rw [pow_mul] at hx
      exact Ideal.pow_right_mono h₁ n hx
    · obtain ⟨n, hn⟩ := hI.2 s hs
      refine ⟨b * n, fun x hx => hn ?_⟩
      rw [pow_mul] at hx
      exact Ideal.pow_right_mono h₂ n hx
  exact hJ.isAdicComplete_iff.2 (hI.isAdicComplete_iff.1 inferInstance)
end GlobalTheory.TorsionCharacter
