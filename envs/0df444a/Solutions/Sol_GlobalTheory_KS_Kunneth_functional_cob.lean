-- Prove2me | solution 1 for GlobalTheory.KS.Kunneth.functional_cob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:17.187302+00:00
-- url     : https://prove2.me/submissions/193d1a4e-9796-42b2-a9c1-3f49320a6792

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
import Theorems.Thm_GlobalTheory_KS_Kunneth_functional_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth
namespace GlobalTheory.KS.Kunneth
theorem _root_.solution {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} [Fintype I] [DecidableEq I]
    {U : I → Y.Opens} (α : C1 U →+ K) (h : ∀ c, IsCob U c → α c = 0) (j : I) (b : Γ(Y, U j)) :
    ∑ k, α (Pi.single k (Pi.single j (rsT b (U k ⊓ U j)))) =
      ∑ k, α (Pi.single j (Pi.single k (rsT b (U j ⊓ U k)))) := by
  have hz : ∀ (O₀ O : Y.Opens), rsT (0 : Γ(Y, O₀)) O = 0 := by
    intro O₀ O
    unfold rsT
    split_ifs <;> simp
  have hcob := h (fun i k => rsT ((Pi.single j b : ∀ i, Γ(Y, U i)) k) (U i ⊓ U k) -
      rsT ((Pi.single j b : ∀ i, Γ(Y, U i)) i) (U i ⊓ U k)) ⟨Pi.single j b, fun _ _ => rfl⟩
  rw [functional_eq_sum] at hcob
  simp only [Pi.single_sub, map_sub, Finset.sum_sub_distrib, sub_eq_zero] at hcob
  have e1 : ∀ i, ∑ k, α (Pi.single i (Pi.single k (rsT ((Pi.single j b : ∀ i, Γ(Y, U i)) k) (U i ⊓ U k)))) =
      α (Pi.single i (Pi.single j (rsT b (U i ⊓ U j)))) := by
    intro i
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, hz, Pi.single_zero, Pi.single_zero, map_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have e2 : ∑ i, ∑ k, α (Pi.single i (Pi.single k (rsT ((Pi.single j b : ∀ i, Γ(Y, U i)) i) (U i ⊓ U k)))) =
      ∑ k, α (Pi.single j (Pi.single k (rsT b (U j ⊓ U k)))) := by
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same]
    · intro i _ hi
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.single_eq_of_ne hi, hz, Pi.single_zero, Pi.single_zero, map_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [e2] at hcob
  simp only [e1] at hcob
  exact hcob
end GlobalTheory.KS.Kunneth
