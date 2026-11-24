-- Prove2me | solution 1 for GlobalTheory.TvAdjust.exists_tv_adjust
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:04.257801+00:00
-- url     : https://prove2.me/submissions/b8dba893-283a-4957-b01c-94006f16a10c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTraceZeroAdjustmentOfHermitianLattice
import Theorems.Thm_GlobalTheory_TvAdjust_exists_split
import Theorems.Thm_GlobalTheory_TvAdjust_exists_nsmul_mulVec_mem
import Theorems.Thm_GlobalTheory_TvAdjust_tv_mul_mulVec
import Theorems.Thm_GlobalTheory_IntegralMultipleClearDenominators_exists_nsmul_mulVec_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.TvAdjust
namespace GlobalTheory.TvAdjust
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (t : E) (b : ℕ), 0 < b → t + c t = 0 → ∃ (t' : E) (k e : ℕ), t' + c t' = 0 ∧ k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (tv (c : E →+* E) G x t' *ᵥ v - tv (c : E →+* E) G x t *ᵥ v) = b • w) ∧ b ^ e • (tv (c : E →+* E) G x t' *ᵥ v) ∈ L ∧ b ^ e • (tv (c : E →+* E) G x (-t') *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G _ _ L hfg hL x t b _ ht
  obtain ⟨N, hN0, hN⟩ := exists_nsmul_mulVec_mem L hfg hL (tv (c : E →+* E) G x t - 1)
  obtain ⟨A, B, e, hAB, ⟨r, hr⟩, hB⟩ := exists_split b N hN0
  have hBA : B.Coprime (b * A) := by
    refine Nat.Coprime.mul_right hB ?_
    exact Nat.Coprime.coprime_dvd_right ⟨r, hr⟩ (hB.pow_right e)
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hBA
  push_cast at huw
  refine ⟨((u * B : ℤ) : E) * t, B, e, ?_, hB, fun v hv => ?_⟩
  · rw [map_mul, map_intCast, ← mul_add, ht, mul_zero]
  have hz := hN v hv
  have h1 : tv (c : E →+* E) G x t *ᵥ v = v + (tv (c : E →+* E) G x t - 1) *ᵥ v := by
    rw [sub_mulVec, one_mulVec]; abel
  have key : ∀ s : ℤ, b ^ e • (tv (c : E →+* E) G x (((s * B : ℤ) : E) * t) *ᵥ v) ∈ L := by
    intro s
    rw [tv_mul_mulVec, smul_add]
    refine L.add_mem (nsmul_mem hv _) ?_
    have := zsmul_mem hz (s * r)
    convert this using 1
    rw [hr, hAB, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  refine ⟨⟨(-w) • N • ((tv (c : E →+* E) G x t - 1) *ᵥ v), zsmul_mem hz _, ?_⟩, key u, ?_⟩
  · rw [tv_mul_mulVec]
    generalize tv (c : E →+* E) G x t *ᵥ v = y at h1 ⊢
    generalize (tv (c : E →+* E) G x t - 1) *ᵥ v = z at h1 ⊢
    subst h1
    have : v + (u * B) • z - (v + z) = (u * B - 1) • z := by
      rw [sub_smul, one_smul]; abel
    rw [this, hAB, ← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    linear_combination (B : ℤ) * huw
  · have := key (-u)
    convert this using 4
    push_cast
    ring
end GlobalTheory.TvAdjust
