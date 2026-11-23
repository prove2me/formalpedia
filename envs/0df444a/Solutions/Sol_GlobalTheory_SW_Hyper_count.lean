-- Prove2me | solution 1 for GlobalTheory.SW.Hyper.count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:41.790044+00:00
-- url     : https://prove2.me/submissions/011c46ee-ce59-43e9-9cb4-175b8ad22588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Theorems.Thm_GlobalTheory_SW_Hyper_surj_of_ne
import Theorems.Thm_GlobalTheory_SW_Hyper_finrank_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Hyper
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
attribute [local instance] Ideal.Quotient.field
namespace GlobalTheory.SW.Hyper
theorem _root_.solution [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.Finite ∧
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.ncard *
      (Nat.card (O ⧸ P) - 1) = Nat.card (O ⧸ P) ^ Module.finrank O M - 1 := by
  classical
  have hcard : Nat.card (M →ₗ[O] O ⧸ P) = Nat.card (O ⧸ P) ^ Module.finrank O M := by
    rw [Nat.card_congr (LinearMap.liftBaseChangeEquiv (M := M) (N := O ⧸ P) (O ⧸ P)).toEquiv,
      Module.natCard_eq_pow_finrank (K := O ⧸ P)]
    congr 1
    rw [← finrank_fibre O M (O ⧸ P)]
    exact Subspace.dual_finrank_eq
  have : Finite (M →ₗ[O] O ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ Nat.card_pos.ne')
  let φ : ℙ (O ⧸ P) (M →ₗ[O] O ⧸ P) → Submodule O M :=
    Projectivization.lift (fun f => LinearMap.ker f.1) (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t (hab : a = t • b)
      have ht : t ≠ 0 := by
        rintro rfl
        apply ha
        rw [hab, zero_smul]
      ext x
      simp only [LinearMap.mem_ker, hab, LinearMap.smul_apply, smul_eq_zero, ht, false_or])
  have key : ∀ (f g : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) (hg : g ≠ 0),
      LinearMap.ker f = LinearMap.ker g →
      Projectivization.mk (O ⧸ P) g hg = Projectivization.mk (O ⧸ P) f hf := by
    intro f g hf hg hfg
    obtain ⟨w, hw⟩ := surj_of_ne P f hf
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨g w, ?_⟩
    ext x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f x)
    have hmem : x - r • w ∈ LinearMap.ker g := by
      rw [← hfg, LinearMap.mem_ker, map_sub, map_smul, hw, ← hr, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, mul_one, sub_self]
    rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at hmem
    rw [LinearMap.smul_apply, hmem, smul_eq_mul, ← hr, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, mul_comm]
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [← Projectivization.mk_rep x, ← Projectivization.mk_rep y] at hxy ⊢
    exact (key _ _ _ _ hxy).symm
  have hS : {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}
      = Set.range φ := by
    ext N
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨Projectivization.mk _ f hf, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨x.rep, x.rep_nonzero, ?_⟩
      have h1 : φ (Projectivization.mk _ x.rep x.rep_nonzero) = LinearMap.ker x.rep := rfl
      rw [Projectivization.mk_rep] at h1
      exact h1.symm
  rw [hS]
  refine ⟨Set.finite_range φ, ?_⟩
  rw [Set.ncard_range_of_injective hφ]
  have h' := Projectivization.card' (O ⧸ P) (M →ₗ[O] O ⧸ P)
  rw [hcard] at h'
  rw [h', Nat.add_sub_cancel]
end GlobalTheory.SW.Hyper
