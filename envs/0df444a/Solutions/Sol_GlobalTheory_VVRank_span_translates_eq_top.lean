-- Prove2me | solution 1 for GlobalTheory.VVRank.span_translates_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:06.09897+00:00
-- url     : https://prove2.me/submissions/89eac898-93dd-42ef-b1f7-56aa4796d876

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution {k : ℤ} {T : Over S} {I : Type} [Nonempty I]
    (hirr : ∀ W : Submodule Γ(T.left, ⊤) (SecM A L k T),
      (∀ (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)), IsActOf A L k θ s s' →
        SecM.ofSec A s ∈ W → SecM.ofSec A s' ∈ W) → W = ⊥ ∨ W = ⊤)
    (ρ : ThetaGrp A L k T → (SecM A L k T ≃ₗ[Γ(T.left, ⊤)] SecM A L k T))
    (h₁ : ∀ θ s s', IsActOf A L k θ s s' ↔ ρ θ (SecM.ofSec A s) = SecM.ofSec A s')
    (h₃ : ∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v)
    (h₄ : ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v))
    (U : I → ThetaGrp A L k T) (hU : ∀ θ : ThetaGrp A L k T, ∃ c, (U c).pt = θ.pt)
    (v : SecM A L k T) (hv : v ≠ 0) :
    Submodule.span Γ(T.left, ⊤) (Set.range fun c => ρ (U c) v) = ⊤ := by
  have mem : ∀ θ, ρ θ v ∈ Submodule.span Γ(T.left, ⊤) (Set.range fun c => ρ (U c) v) := fun θ => by
    obtain ⟨c, hc⟩ := hU θ
    obtain ⟨u, hu⟩ := h₃ _ _ hc
    rw [hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  refine (hirr _ fun θ s s' hs hm => ?_).resolve_left fun h => ?_
  · rw [← (h₁ θ s s').1 hs]
    refine (Submodule.span_le (p := Submodule.comap (ρ θ).toLinearMap
      (Submodule.span Γ(T.left, ⊤) (Set.range fun c => ρ (U c) v)))).2 ?_ hm
    rintro _ ⟨c, rfl⟩
    obtain ⟨θ', -, h'⟩ := h₄ θ (U c)
    exact (h' v ▸ mem θ' :)
  · have := mem (U (Classical.arbitrary I))
    rw [h, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at this
    exact hv this
end GlobalTheory.VVRank
