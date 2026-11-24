-- Prove2me | solution 1 for GlobalTheory.ZM.finrank_int_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:19:06.20363+00:00
-- url     : https://prove2.me/submissions/cb673184-7da9-4398-a93a-73146cac32cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivStdSymp

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution (O M : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := M) le_rfl
  let F : Submodule O M := Submodule.span O (Set.range f)
  let bF : Module.Basis (Fin (Module.finrank O M)) O F := Module.Basis.span hf
  have : Module.Free O F := Module.Free.of_basis bF
  have h1 : Module.finrank O F = Module.finrank O M := by
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin]
  have h2 : Module.finrank O (M ⧸ F) = 0 := by
    have := Submodule.finrank_quotient_add_finrank F
    omega
  have h3 : Module.finrank ℤ (M ⧸ F.restrictScalars ℤ) = 0 := by
    rw [Module.finrank_eq_zero_iff] at h2 ⊢
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha, hax⟩ := h2 (Submodule.Quotient.mk x)
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha)
    refine ⟨r, hr, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax ⊢
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul O r x, hc, mul_comm, mul_smul]
    exact F.smul_mem c hax
  have h4 := Submodule.finrank_quotient_add_finrank (F.restrictScalars ℤ)
  have h5 : Module.finrank ℤ (F.restrictScalars ℤ) = Module.finrank ℤ O * Module.finrank O F :=
    (Module.finrank_mul_finrank ℤ O F).symm
  rw [← h4, h3, zero_add, h5, h1]
end GlobalTheory.ZM
