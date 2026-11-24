-- Prove2me | solution 1 for GlobalTheory.flat_coker_of_complex_exact_mod_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:41.220527+00:00
-- url     : https://prove2.me/submissions/3edfe3c1-260d-4629-bb91-7753d72a9942

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
import Theorems.Thm_GlobalTheory_T_flat_quotient_range_of_injective_mod_maximal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (D : ℕ → Type) [∀ i, AddCommGroup (D i)] [∀ i, Module A (D i)] [∀ i, Module.Finite A (D i)] [∀ i, Module V (D i)] [∀ i, IsScalarTower V A (D i)] [∀ i, Module.Flat V (D i)] (d : ∀ i, D (i + 1) →ₗ[A] D i), (∀ i x, d i (d (i + 1) x) = 0) → (∃ n, ∀ i, n < i → Subsingleton (D i)) → (∀ i (x : D (i + 1)), d i x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D i)) → x ∈ LinearMap.range (d (i + 1)) ⊔ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D (i + 1)))) → Module.Flat V (D 0 ⧸ LinearMap.range (d 0)) := by
  intro V A _ _ _ _ _ _ _ _ D _ _ _ _ _ _ d hdd _ hex
  set J : Ideal A := (IsLocalRing.maximalIdeal V).map (algebraMap V A) with hJ
  have hle : LinearMap.range (d 1) ≤ LinearMap.ker (d 0) := by
    rintro _ ⟨x, rfl⟩
    exact hdd 0 x
  let u : (D 1 ⧸ LinearMap.range (d 1)) →ₗ[A] D 0 := (LinearMap.range (d 1)).liftQ (d 0) hle
  have hr : LinearMap.range u = LinearMap.range (d 0) := Submodule.range_liftQ _ _ _
  have h := GlobalTheory.T.flat_quotient_range_of_injective_mod_maximal V A (D 1 ⧸ LinearMap.range (d 1)) (D 0) u (by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ LinearMap.range (d 1) ⊔ (J • ⊤ : Submodule A (D 1)) := hex 0 y hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have ha0 : (Submodule.Quotient.mk a : D 1 ⧸ LinearMap.range (d 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha
    rw [Submodule.Quotient.mk_add, ha0, zero_add]
    have : (LinearMap.range (d 1)).mkQ b ∈ (J • ⊤ : Submodule A (D 1)).map (LinearMap.range (d 1)).mkQ :=
      Submodule.mem_map_of_mem hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this)
  rwa [hr] at h
end GlobalTheory
