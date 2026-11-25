-- Prove2me | solution 1 for GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:30.84096+00:00
-- url     : https://prove2.me/submissions/d18e643e-25be-4a3e-b245-cd9f860f6c81

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
import Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_natCast_mul_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_exists_eq_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_isOpen_integralFiniteAdeles


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Set
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.CuspidalSpectrum
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Automorphic.CuspidalSpectrum
theorem _root_.solution {𝒦 : Set (FiniteAdeleRing (𝓞 K) K)}
    (h𝒦 : IsCompact 𝒦) :
    ∃ m : ℕ, 0 < m ∧ ∀ ξ : K, algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ ∈ 𝒦 →
      ∃ z : 𝓞 K, (z : K) = m * ξ := by
  set U : ℕ → Set (FiniteAdeleRing (𝓞 K) K) := fun c =>
    {a | ((c + 1 : ℕ) : FiniteAdeleRing (𝓞 K) K) * a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K}
  have hU : ∀ c, IsOpen (U c) := fun c =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const_mul _)
  have hcov : 𝒦 ⊆ ⋃ c, U c := fun a _ =>
    mem_iUnion.2 (exists_natCast_mul_mem_integralFiniteAdeles K a)
  obtain ⟨t, ht⟩ := h𝒦.elim_finite_subcover U hU hcov
  refine ⟨∏ c ∈ t, (c + 1), Finset.prod_pos fun c _ => Nat.succ_pos c, fun ξ hξ => ?_⟩
  obtain ⟨c, hct, hc⟩ := mem_iUnion₂.1 (ht hξ)
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun c => c + 1) hct
  have hmem : algebraMap K (FiniteAdeleRing (𝓞 K) K) (((∏ c ∈ t, (c + 1) : ℕ) : K) * ξ) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
    rw [map_mul, map_natCast, hq, Nat.cast_mul, mul_comm (((c + 1 : ℕ)) : FiniteAdeleRing (𝓞 K) K),
      mul_assoc]
    exact Subring.mul_mem _ (natCast_mem _ _) hc
  obtain ⟨z, hz⟩ := GroundTheory.Global.exists_eq_of_forall_mem_adicCompletionIntegers K _ hmem
  exact ⟨z, hz⟩
end GroundTheory.Automorphic.CuspidalSpectrum
