-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.exists_finset_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:06.84152+00:00
-- url     : https://prove2.me/submissions/0a8eff72-27d7-42a2-8868-5a4a7f292848

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives

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
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {k : ℕ} (hk : 1 ≤ k) : ∃ T : Finset X, ∀ β, ∃ α ∈ T, ∃ mu, β = α + k • mu := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨Finset.univ.image fun r : _ → Fin k => ∑ i, ((r i : ℕ) : ℤ) • b i, fun β =>
    ⟨∑ i, (b.repr β i % k) • b i, Finset.mem_image.2 ⟨fun i => ⟨(b.repr β i % k).toNat, ?_⟩,
      Finset.mem_univ _, Finset.sum_congr rfl fun i _ => ?_⟩, ∑ i, (b.repr β i / k) • b i, ?_⟩⟩
  · have := Int.emod_lt_of_pos (b.repr β i) hk'
    have := Int.emod_nonneg (b.repr β i) hk'.ne'
    omega
  · show (((b.repr β i % k).toNat : ℕ) : ℤ) • b i = _
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hk'.ne')]
  · conv_lhs => rw [← b.sum_repr β]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← natCast_zsmul, smul_smul, ← add_smul, Int.emod_add_mul_ediv]
end GlobalTheory.FieldBaseChange
