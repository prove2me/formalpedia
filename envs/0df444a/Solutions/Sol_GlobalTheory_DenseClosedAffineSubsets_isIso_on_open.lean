-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.isIso_on_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:26.231842+00:00
-- url     : https://prove2.me/submissions/73e906c9-a8f5-40e4-9217-f86bfe63d22f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_closed_restrict_of_dense

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {S W P X : Scheme.{0}} (f : W ⟶ S) (s : P ⟶ S) [IsSeparated s]
    (U : W.Opens) (ι : X ⟶ pullback f s)
    [IsClosedImmersion ι] (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ ι ≫ pullback.fst f s = U.ι) :
    IsIso ((ι ≫ pullback.fst f s) ∣_ U) := by
  have : IsClosedImmersion ((ι ≫ pullback.fst f s) ∣_ U) :=
    closed_restrict_of_dense (pullback.fst f s) ι j U (𝟙 _) (j ≫ ι) (by simp [h₁])
      fun Z a _ _ ↦ ⟨a, rfl⟩
  have hr : Set.range j ⊆ Set.range ((ι ≫ pullback.fst f s) ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (ι ≫ pullback.fst f s) (j z) ∈ U
    rw [← Scheme.Hom.comp_apply, h₁]
    exact z.2
  have : IsSplitEpi ((ι ≫ pullback.fst f s) ∣_ U) :=
    ⟨⟨IsOpenImmersion.lift _ j hr, by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
        IsOpenImmersion.lift_fac_assoc, h₁, Category.id_comp]⟩⟩
  exact isIso_of_mono_of_isSplitEpi _
end GlobalTheory.DenseClosedAffineSubsets
