-- Prove2me | solution 1 for GroundTheory.LocalField.exists_limit_of_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:35.944117+00:00
-- url     : https://prove2.me/submissions/47606147-f002-4c16-b438-a898406bebb0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_smodEq_iff_pow_dvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
section
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
section Lattice
variable (π : 𝒪[K]) (θ : L)
end Lattice
section Integral
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]
variable (π : 𝒪[K]) (θ : L)
variable [IsGalois K L]
end Integral
section Product
variable (π : 𝒪[K]) (θ : L)
end Product
section Complete
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [FiniteDimensional K L] in

private theorem isAdicComplete_maximalIdeal : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
variable (π : 𝒪[K]) (θ : L)
variable {π θ}
end Complete
section Existence
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
variable [IsGalois K L]
end Existence
section Open
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]
variable (π : 𝒪[K]) (θ : L)
end Open
end GroundTheory.LocalField
end
end

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {π : 𝒪[K]} (hπ : Irreducible π) (c : ℕ → 𝒪[K])
    (hc : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, π ^ N ∣ c n - c m) :
    ∃ a, ∀ N, ∃ M, ∀ n ≥ M, π ^ N ∣ c n - a := by
  choose M hM using hc
  let M' : ℕ → ℕ := fun N => (range (N + 1)).sup M
  have hM' : ∀ N, M N ≤ M' N := fun N => le_sup (mem_range.mpr (Nat.lt_succ_self N))
  have hmono : Monotone M' := fun i j hij =>
    sup_mono (range_subset_range.mpr (Nat.succ_le_succ hij))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (isAdicComplete_maximalIdeal (K := K)).toIsPrecomplete
    (f := fun N => c (M' N)) (fun {m n} hmn => by
      rw [smodEq_iff_pow_dvd hπ]
      exact hM m (M' n) ((hM' m).trans (hmono hmn)) (M' m) (hM' m))
  refine ⟨a, fun N => ⟨M' N, fun n hn => ?_⟩⟩
  have h1 : π ^ N ∣ c n - c (M' N) := hM N _ (hM' N) n ((hM' N).trans hn)
  have h2 : π ^ N ∣ c (M' N) - a := (smodEq_iff_pow_dvd hπ).mp (ha N)
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this
end GroundTheory.LocalField
