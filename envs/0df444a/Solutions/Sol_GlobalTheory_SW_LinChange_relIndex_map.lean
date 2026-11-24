-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.relIndex_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:22.220884+00:00
-- url     : https://prove2.me/submissions/fb183050-1e88-46c3-a188-06d380612ce3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_mem_perSub_iff
import Theorems.Thm_GlobalTheory_SW_LinChange_exists_basis
import Theorems.Thm_GlobalTheory_SW_LinChange_map_perSub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.LinChange
theorem _root_.solution (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (R M : ℕ) (hR : 0 < R) (hM : 0 < M)
    (hT : ∀ y, IntM y → IntM ((M : K) • T y)) :
    ((((perSub K κ ι (R * M)).map T.toAddEquiv.toAddMonoidHom).relIndex (perSub K κ ι R) : ℕ) : ℚ)
      = (M : ℚ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
        |LinearMap.det T.toLinearMap| := by
  obtain ⟨J, _, _, b, hb⟩ := exists_basis (K := K) (κ := κ) (ι := ι)
  have hsc : ∀ N : ℕ, 0 < N → ∃ e : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K,
      e.toLinearMap = (N : ℚ) • LinearMap.id := fun N hN =>
    ⟨LinearEquiv.smulOfNeZero ℚ _ (N : ℚ) (by exact_mod_cast hN.ne'), by ext; simp⟩
  have hcl : ∀ e : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K, AddSubgroup.closure (Set.range (b.map e)) =
      (AddSubgroup.closure (Set.range b)).map e.toAddEquiv.toAddMonoidHom := by
    intro e
    rw [AddMonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hper : ∀ (N : ℕ) (e : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K),
      e.toLinearMap = (N : ℚ) • LinearMap.id → perSub K κ ι N =
      (AddSubgroup.closure (Set.range b)).map e.toAddEquiv.toAddMonoidHom := by
    intro N e he
    have he' : ∀ y, e y = (N : K) • y := fun y => by
      have := LinearMap.congr_fun he y
      rw [Nat.cast_smul_eq_nsmul] at this ⊢
      exact this
    ext x
    rw [mem_perSub_iff, AddSubgroup.mem_map]
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, (hb y).2 hy, (he' y).trans h.symm⟩,
      fun ⟨y, hy, h⟩ => ⟨y, (hb y).1 hy, h.symm.trans (he' y)⟩⟩
  obtain ⟨e₁, h₁⟩ := hsc (R * M) (Nat.mul_pos hR hM)
  obtain ⟨e₂, h₂⟩ := hsc R hR
  rw [AddSubgroup.relIndex_eq_abs_det _ _ (map_perSub_le T R M hT) (b.map (e₁.trans T)) (b.map e₂)
    (by rw [hcl, hper _ _ h₁, AddSubgroup.map_map]; rfl) (by rw [hcl, hper _ _ h₂])]
  have hc : ⇑(b.map (e₁.trans T)) = ((M : ℚ) • T.toLinearMap) ∘ (b.map e₂) := by
    funext j
    have a₁ := LinearMap.congr_fun h₁ (b j)
    have a₂ := LinearMap.congr_fun h₂ (b j)
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply] at a₁ a₂
    simp [a₁, a₂, smul_smul, mul_comm]
  rw [hc, Module.Basis.det_comp, Module.Basis.det_self, mul_one, LinearMap.det_smul, abs_mul,
    abs_of_nonneg (by positivity), ← Module.finrank_mul_finrank ℚ K (Matrix κ ι K),
    Module.finrank_matrix, Module.finrank_self, mul_one]
end GlobalTheory.SW.LinChange
