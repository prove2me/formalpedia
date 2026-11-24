-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.isLocalizedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:44.230891+00:00
-- url     : https://prove2.me/submissions/a19634ad-55ef-4c5a-bab7-f7560f4ef428

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open NumberField Matrix
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {r : ℕ}
variable {K : Type} [Field K] [NumberField K]
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup M'] [Module (𝓞 K) M']
open GlobalTheory.IsLatticeEmb
variable {φ : M →ₗ[𝓞 K] (Fin r → K)}
namespace GlobalTheory.IsLatticeEmb
theorem _root_.solution (h : IsLatticeEmb φ) : IsLocalizedModule (𝓞 K)⁰ φ where
  map_units s := by
    have hs : ((s : 𝓞 K) : K) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
    rw [Module.End.isUnit_iff]
    have : ⇑(algebraMap (𝓞 K) (Module.End (𝓞 K) (Fin r → K)) s) = fun v => ((s : 𝓞 K) : K) • v := by
      funext v; rw [Module.algebraMap_end_apply, ← algebraMap_smul K]
    rw [this]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj v := by
    obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul v
    refine ⟨(x, ⟨(n : 𝓞 K), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩), ?_⟩
    rw [hx, Submonoid.smul_def, Int.cast_smul_eq_zsmul]
  exists_of_eq hxy := ⟨1, by rw [h.1 hxy]⟩
end GlobalTheory.IsLatticeEmb
