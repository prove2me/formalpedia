-- Prove2me | solution 1 for GlobalTheory.isFractionRing_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:02.262989+00:00
-- url     : https://prove2.me/submissions/cede556c-744d-473c-ba4a-49e917d9fd31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FiniteSeparableOfSumMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ResidueFieldMapFiniteSeparableOfTame
import Theorems.Thm_GlobalTheory_exists_eq_evaluation_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (q : Ideal Γ(X, U)) (hq : ∀ a, a ∈ q ↔ X.evaluation U x hx a = 0) :
    letI := (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
    IsFractionRing (Γ(X, U) ⧸ q) (X.residueField x) := by
  letI : Algebra (Γ(X, U) ⧸ q) (X.residueField x) :=
    (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
  have hmk : ∀ a, algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a) =
      X.evaluation U x hx a := fun a => Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hmk] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hq a).2 hc)
  haveI : NoZeroDivisors (Γ(X, U) ⧸ q) :=
    hinj.noZeroDivisors _ (map_zero _) (map_mul _)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    haveI : Nontrivial (Γ(X, U) ⧸ q) :=
      ⟨⟨0, 1, fun h => by simpa using congrArg (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) h⟩⟩
    exact nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨a, b, hz⟩ := exists_eq_evaluation_div hU x hx z
    by_cases hb : X.evaluation U x hx b = 0
    · refine ⟨(0, 1), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 1 =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 0
      rw [hz, hb, div_zero, zero_mul, map_zero]
    · have hb' : Ideal.Quotient.mk q b ≠ 0 := by
        intro h
        apply hb
        rw [← hmk, h, map_zero]
      refine ⟨(Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q b, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q b) =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a)
      rw [hz, hmk, hmk, div_mul_cancel₀ _ hb]
  · intro c d h
    exact ⟨1, by rw [hinj h]⟩
end GlobalTheory
