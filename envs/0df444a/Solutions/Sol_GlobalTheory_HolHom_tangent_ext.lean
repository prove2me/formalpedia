-- Prove2me | solution 1 for GlobalTheory.HolHom.tangent_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:13.5681+00:00
-- url     : https://prove2.me/submissions/05760d45-ce2c-4202-9229-eecd5f321a37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_point_ext
import Theorems.Thm_GlobalTheory_HolHom_exists_affine
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_dual_iff
import Theorems.Thm_GlobalTheory_HolHom_fst_valR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {v v' : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x)
    (h' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' = x)
    (H : ∀ U : X.Opens, ⊤ ≤ x ⁻¹ᵁ U → ∀ f : Γ(X, U),
      TrivSqZeroExt.snd (valR v U f) = TrivSqZeroExt.snd (valR v' U f)) : v = v' := by
  obtain ⟨U, hU, hx, -⟩ := exists_affine x (U := ⊤) le_top
  refine point_ext hU ((le_preimage_dual_iff h U).2 hx) ((le_preimage_dual_iff h' U).2 hx) fun f => ?_
  exact TrivSqZeroExt.ext ((fst_valR h hx f).trans (fst_valR h' hx f).symm) (H U hx f)
end GlobalTheory.HolHom
