-- Prove2me | solution 1 for GlobalTheory.morphisms_spread_out_to_fg_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:24.999942+00:00
-- url     : https://prove2.me/submissions/82d47ba0-6975-472e-8617-ab14ce539336

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_exists_fg_forall_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : IntermediateField ℚ ℂ) (B Z : Scheme.{0})
    (pB : B ⟶ Sp k) (pZ : Z ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB]
    [LocallyOfFinitePresentation pZ] (n : ℕ)
    (φ : Fin n → (pullback pB (spMap (algebraMap k ℂ)) ⟶ Z))
    (hφ : ∀ i, φ i ≫ pZ = pullback.fst _ _ ≫ pB) (R₀ : Subalgebra k ℂ) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k ℂ) (ψ : Fin n → (pullback pB (spMap (algebraMap k R)) ⟶ Z))
      (j : pullback pB (spMap (algebraMap k ℂ)) ⟶ pullback pB (spMap (algebraMap k R))),
      R.FG ∧ R₀ ≤ R ∧ j ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R.val.toRingHom ∧
        ∀ i, ψ i ≫ pZ = pullback.fst _ _ ≫ pB ∧ j ≫ ψ i = φ i := by
  obtain ⟨R, ψ, hR, hle, h⟩ := Spread.exists_fg_forall_comp_eq pB pZ φ hφ R₀ hR₀
  exact ⟨R, ψ, Spread.bcMap pB R.val, hR, hle, Spread.bcMap_fst _ _, Spread.bcMap_snd _ _, h⟩
end GlobalTheory
