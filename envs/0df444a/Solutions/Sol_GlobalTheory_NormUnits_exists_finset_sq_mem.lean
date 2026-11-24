-- Prove2me | solution 1 for GlobalTheory.NormUnits.exists_finset_sq_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:14:48.75631+00:00
-- url     : https://prove2.me/submissions/801f58fe-5fe8-49d6-8373-7e6fbd39af2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetCosetsIntegralNormUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
theorem _root_.solution {G : Type} [CommGroup G] (N : Subgroup G) (hN : Group.FG (G ⧸ N)) :
    ∃ F : Finset G, ∀ u : G, u ^ 2 ∈ N → ∃ f ∈ F, u * f⁻¹ ∈ N := by
  let M := Additive (G ⧸ N)
  haveI : AddGroup.FG M := inferInstance
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let K2 : Submodule ℤ M := LinearMap.ker (LinearMap.lsmul ℤ M 2)
  haveI : Module.Finite ℤ K2 := Module.IsNoetherian.finite ℤ K2
  haveI : Finite K2 := Module.finite_of_fg_torsion K2 (fun x => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero (by norm_num)⟩, by
    apply Subtype.ext; have h := x.2; rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at h
    simpa using h⟩)
  let r : K2 → G := fun k => Quotient.out (Additive.toMul (k : M))
  refine ⟨(Set.finite_range r).toFinset, fun u hu => ?_⟩
  have hk : (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) ∈ K2 := by
    show (2 : ℤ) • (Additive.ofMul (QuotientGroup.mk u : G ⧸ N) : M) = 0
    rw [← ofMul_zpow]
    show Additive.ofMul ((QuotientGroup.mk u : G ⧸ N) ^ (2 : ℤ)) = Additive.ofMul 1
    congr 1
    rw [zpow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]; exact hu
  refine ⟨r ⟨_, hk⟩, by simp, ?_⟩
  have h1 : (QuotientGroup.mk (r ⟨_, hk⟩) : G ⧸ N) = QuotientGroup.mk u := by
    simp only [r]; exact Quotient.out_eq' _
  have := QuotientGroup.eq.mp h1.symm
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]
end GlobalTheory.NormUnits
