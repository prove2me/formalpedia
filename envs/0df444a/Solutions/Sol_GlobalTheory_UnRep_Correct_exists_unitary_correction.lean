-- Prove2me | solution 1 for GlobalTheory.UnRep.Correct.exists_unitary_correction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:08.162916+00:00
-- url     : https://prove2.me/submissions/1eff7895-7d49-414b-ab99-0cfb9298c1a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormOneReflectionCorrectionAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevel
import Theorems.Thm_GlobalTheory_UnRep_Correct_exists_nat_mulVec_mem
import Theorems.Thm_GlobalTheory_UnRep_Correct_congAt_mul
import Theorems.Thm_GlobalTheory_UnRep_Correct_congAt_conj
import Theorems.Thm_GlobalTheory_UnRep_Correct_splitOr_mul
import Theorems.Thm_GlobalTheory_UnRep_Correct_smul_mul_mem
import Theorems.Thm_GlobalTheory_T_exists_norm_one_reflection_correction_at_level
import Theorems.Thm_GlobalTheory_T_unitaryMatrix_eq_prod_quasiReflections
import Theorems.Thm_GlobalTheory_T_unitaryQuasiReflection_laws


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
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Correct
variable {E : Type} [Field E] {n : ℕ}
namespace GlobalTheory.UnRep.Correct
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL γ₀ N D hγ₀ hN hD
  obtain ⟨l, hl, hprod⟩ := GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections F E c n G hG _ hγ₀
  clear hγ₀
  induction l generalizing γ₀ D with
  | nil =>
    have h1 : γ₀ = 1 := Units.ext (by simpa using hprod)
    subst h1
    refine ⟨1, fun x y => by simp, ⟨1, by simp, fun v _ => ⟨0, L.zero_mem, by simp⟩⟩, 1,
      ⟨one_ne_zero, fun P hP h => absurd ((Ideal.eq_top_iff_one P).2 h) hP.ne_top⟩, fun v hv => ?_⟩
    simpa using hv
  | cons p l ih =>
    obtain ⟨x, u⟩ := p
    obtain ⟨hx, hu⟩ := hl (x, u) List.mem_cons_self
    simp only at hx hu
    obtain ⟨-, r1, rmul, run⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG x hx
    have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
    let R : (a : E) → a ≠ 0 → GL (Fin n) E := fun a ha =>
      ⟨refl c G x a, refl c G x a⁻¹, by rw [rmul, mul_inv_cancel₀ ha, r1],
        by rw [rmul, inv_mul_cancel₀ ha, r1]⟩
    obtain ⟨d, hd, hRd⟩ := exists_nat_mulVec_mem L hfg hL (R u hu0).1
    obtain ⟨e, he, hRe⟩ := exists_nat_mulVec_mem L hfg hL ((R u hu0)⁻¹).1
    obtain ⟨γ₁, hγ₁, hc₁, s₁, hs₁, hL₁⟩ := ih ((R u hu0)⁻¹ * γ₀) (D * d * e)
      (Nat.mul_pos (Nat.mul_pos hD hd) he) (fun p hp => hl p (List.mem_cons_of_mem _ hp)) (by
        rw [Units.val_mul, hprod, List.map_cons, List.prod_cons, ← mul_assoc]
        change _ = _
        have : ((R u hu0)⁻¹).1 * refl c G x u = 1 := (R u hu0).inv_mul
        rw [this, one_mul])
    obtain ⟨u', hu', hc', s', hs', hL'⟩ := GlobalTheory.T.exists_norm_one_reflection_correction_at_level F E c n G hG L hfg hL x u N D hx hu hN hD
    have hu'0 : u' ≠ 0 := left_ne_zero_of_mul_eq_one hu'
    refine ⟨R u' hu'0 * γ₁, ?_, ?_, s' * s₁, splitOr_mul hs' hs₁, fun v hv => ⟨?_, ?_⟩⟩
    · intro y z
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact (run u' hu' _ _).trans (hγ₁ y z)
    · have hconj := congAt_conj he (R u hu0).mul_inv hRd hRe hc₁
      have h := congAt_mul hc' hconj
      have e1 : refl c G x (u' / u) = (R u' hu'0 * (R u hu0)⁻¹).1 := by
        rw [div_eq_mul_inv, ← rmul]; rfl
      rw [e1, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul] at h
      convert h using 2
      group
    · rw [Units.val_mul]
      exact smul_mul_mem (fun v hv => (hL' v hv).1) (fun v hv => (hL₁ v hv).1) v hv
    · rw [mul_inv_rev, Units.val_mul, mul_comm s']
      exact smul_mul_mem (fun v hv => (hL₁ v hv).2) (fun v hv => (hL' v hv).2) v hv
end GlobalTheory.UnRep.Correct
