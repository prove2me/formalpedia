-- Prove2me | solution 1 for GlobalTheory.UnitCocycle.exists_local_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:45.036827+00:00
-- url     : https://prove2.me/submissions/8855df8f-fea2-411f-a0e5-5ae8473dc819

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
import Theorems.Thm_GlobalTheory_UnitCocycle_datum_apply
import Theorems.Thm_GlobalTheory_UnitCocycle_isDescentDatum
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FlatDescent_IsDescentDatum_bijective_extend
import Theorems.Thm_GlobalTheory_FlatDescent_IsDescentDatum_invertible_invariants
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open GlobalTheory.UnitCocycle
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
namespace GlobalTheory.UnitCocycle
theorem _root_.solution [Module.FaithfullyFlat R B] {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = algebraMap R B s ∧
      (1 : B) ⊗ₜ[R] x = c * (x ⊗ₜ[R] (1 : B)) := by
  have hd := isDescentDatum hu h
  have hI := hd.invertible_invariants
  let I := FlatDescent.invariants (datum c)
  obtain ⟨φ, m, hm⟩ : ∃ (φ : Module.Dual R I) (m : I), φ m ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hP
    rw [Ideal.eq_top_iff_one]
    obtain ⟨z, hz⟩ := hI.bijective.2 1
    rw [← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact P.add_mem hx hy
    | tmul b m => simpa using hcon b m
  let e := LinearEquiv.ofBijective _ hd.bijective_extend
  let Φ : B →ₗ[B] B :=
    (AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ LinearMap.baseChange B φ ∘ₗ e.symm.toLinearMap
  have h1 : e.symm (m : B) = 1 ⊗ₜ m := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e]
  refine ⟨φ m, hm, m, Φ 1, ?_, ?_⟩
  · rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    simp [Φ, h1, Algebra.algebraMap_eq_smul_one]
  · rw [← datum_apply]
    exact (FlatDescent.mem_invariants.1 m.2).symm
end GlobalTheory.UnitCocycle
