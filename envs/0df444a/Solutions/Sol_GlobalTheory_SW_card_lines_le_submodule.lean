-- Prove2me | solution 1 for GlobalTheory.SW.card_lines_le_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:00.270664+00:00
-- url     : https://prove2.me/submissions/4a10b7fc-100c-435b-b423-c2d904a48e25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Finite V]
    (K : Submodule F V) :
    Nat.card {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K} * (Nat.card F - 1) + 1
      = Nat.card K := by
  classical
  have e : {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K}
      ≃ {H : Submodule F K // Module.finrank F H = 1} :=
    { toFun := fun l => ⟨l.1.comap K.subtype, by
        rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
          inf_eq_right.mpr l.2.2]
        exact l.2.1⟩
      invFun := fun H => ⟨H.1.map K.subtype,
        by rw [Submodule.finrank_map_subtype_eq]; exact H.2,
        Submodule.map_subtype_le K H.1⟩
      left_inv := fun l => by
        apply Subtype.ext
        simp only [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr l.2.2
      right_inv := fun H => by
        apply Subtype.ext
        exact Submodule.comap_map_eq_of_injective K.injective_subtype H.1 }
  rw [Nat.card_congr e, ← Nat.card_congr (Projectivization.equivSubmodule F K)]
  exact (Projectivization.card' F K).symm
end GlobalTheory.SW
