-- Prove2me | solution 1 for GlobalTheory.LocalFlat.flat_of_relationsLift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:48.078727+00:00
-- url     : https://prove2.me/submissions/e6b14fc9-5a57-43fa-bb1c-ba24fc271b1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open GlobalTheory.LocalFlat
variable {A : Type u} [CommRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]
namespace GlobalTheory.LocalFlat
theorem _root_.solution [IsNoetherianRing A] (B : Type v) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (h : ∀ n, RelationsLift (I ^ n) M) :
    Module.Flat A M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  rw [← ker_eq_bot, eq_bot_iff]
  intro x hx
  have : Module.Finite B (M ⊗[A] J) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange A B B M J)
  have key := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⊗[A] J) _ hI
  have hx' : x ∈ (⊥ : Submodule B (M ⊗[A] J)) := by
    rw [← key, Submodule.mem_iInf]
    intro n
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := A) I J
    obtain ⟨y, rfl⟩ := h (n + k) J J.subtype x (by rw [mem_ker.mp hx]; simp)
    clear hx
    induction y with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul m j =>
      obtain ⟨⟨j, hj⟩, hj'⟩ := j
      have h1 : j ∈ I ^ n • (J : Submodule A A) := by
        have := hk (n + k) (by omega)
        rw [Nat.add_sub_cancel] at this
        refine Submodule.smul_mono le_rfl inf_le_right (this.le ⟨?_, hj⟩)
        simpa using hj'
      have h2 : (⟨j, hj⟩ : J) ∈ I ^ n • (⊤ : Submodule A J) := by
        rwa [Submodule.mem_smul_top_iff]
      simp only [lTensor_tmul, Submodule.subtype_apply]
      refine Submodule.smul_induction_on (p := fun d : J => m ⊗ₜ[A] d ∈
        (I.map (algebraMap A B)) ^ n • (⊤ : Submodule B (M ⊗[A] J))) h2 ?_ ?_
      · intro r hr d _
        rw [tmul_smul, ← algebraMap_smul B r]
        refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hr
      · intro d e hd he
        rw [tmul_add]
        exact add_mem hd he
  simpa using hx'
end GlobalTheory.LocalFlat
