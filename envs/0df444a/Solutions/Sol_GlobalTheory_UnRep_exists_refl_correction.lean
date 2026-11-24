-- Prove2me | solution 1 for GlobalTheory.UnRep.exists_refl_correction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:39:05.086193+00:00
-- url     : https://prove2.me/submissions/df2b3b23-09db-4e64-8e80-ab83c1979116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosNatMulMemRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormOneReflectionCorrectionAtLevel
import Theorems.Thm_GlobalTheory_UnRep_exists_nat_smul_map_mem
import Theorems.Thm_GlobalTheory_T_normOne_approximation_at_level_primes
import Theorems.Thm_GlobalTheory_UnRep_ReflLaws_refl_laws


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL x u N D hx hu hN hD
  have hap := (GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG x hx).1
  let φ : (Fin n → E) →ₗ[E] (Fin n → E) :=
    { toFun := fun v => (hermE c G v x / hermE c G x x) • x
      map_add' := by
        intro v w
        rw [← add_smul, ← add_div]
        congr 2
        simp [hermE, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        rw [RingHom.id_apply, smul_smul, ← mul_div_assoc]
        congr 2
        simp [hermE, Finset.mul_sum, mul_assoc] }
  obtain ⟨d, hd, hdL⟩ := exists_nat_smul_map_mem L hfg hL φ
  have hap' : ∀ a v, refl c G x a *ᵥ v = v + (a - 1) • φ v := by
    intro a v
    rw [hap]
    show _ = v + (a - 1) • ((hermE c G v x / hermE c G x x) • x)
    rw [smul_smul, mul_div_assoc]
  obtain ⟨u', hu', ⟨t, ht, b, hb⟩, s, hs, ⟨b₁, hb₁⟩, b₂, hb₂⟩ :=
    GlobalTheory.T.normOne_approximation_at_level_primes F E c hG.1 hG.2.1 u N (D * d) hu hN (Nat.mul_pos hD hd)
  have key : ∀ (a : E) (b : 𝓞 E), (s : E) * (a - 1) = ((D * d : ℕ) : E) * (b : E) →
      ∀ v ∈ L, s • (refl c G x a *ᵥ v) ∈ L := by
    intro a b hb v hv
    rw [hap', smul_add]
    refine L.add_mem (L.smul_mem s hv) ?_
    have : s • ((a - 1) • φ v) = ((D : 𝓞 E) * b) • ((d : E) • φ v) := by
      show (s : E) • ((a - 1) • φ v) = (((D : 𝓞 E) * b : 𝓞 E) : E) • ((d : E) • φ v)
      rw [smul_smul, smul_smul, hb]
      congr 1
      push_cast
      ring
    rw [this]
    exact L.smul_mem _ (hdL v hv)
  refine ⟨u', hu', ⟨t, ht, fun v hv => ⟨b • ((d : E) • φ v), L.smul_mem b (hdL v hv), ?_⟩⟩,
    s, hs, fun v hv => ⟨key _ _ hb₁ v hv, key _ _ hb₂ v hv⟩⟩
  rw [hap', add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul E t, ← Nat.cast_smul_eq_nsmul E D]
  show _ = (D : E) • ((b : E) • ((d : E) • φ v))
  rw [smul_smul, smul_smul, smul_smul, hb]
  congr 1
  push_cast
  ring
end GlobalTheory.UnRep
