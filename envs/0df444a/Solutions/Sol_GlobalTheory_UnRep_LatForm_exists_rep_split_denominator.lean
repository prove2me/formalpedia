-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.exists_rep_split_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:59.197015+00:00
-- url     : https://prove2.me/submissions/bf4d400c-c8ea-4771-b5af-3fc8823dc7b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
import Theorems.Thm_GlobalTheory_UnRep_LatForm_inv_integral
import Theorems.Thm_GlobalTheory_UnRep_LatForm_exists_mem_primes
import Theorems.Thm_GlobalTheory_UnRep_LatForm_fm_mul
import Theorems.Thm_GlobalTheory_UnRep_LatForm_congAtA_of_congAt
import Theorems.Thm_GlobalTheory_UnRep_LatForm_congAtA_mul
import Theorems.Thm_GlobalTheory_UnRep_LatForm_one_tmul_natCast_smul
import Theorems.Thm_GlobalTheory_UnRep_LatForm_one_tmul_natCast_mul_smul
import Theorems.Thm_GlobalTheory_T_exists_unitary_correction_congruent_one_at_level
import Theorems.Thm_GlobalTheory_T_idempotent_adeles_and_small_adelic_matrices
import Theorems.Thm_GlobalTheory_T_unitaryGroup_weak_approximation_at_primes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.LatForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.LatForm
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ c n G hG h2 L hL hL' g N hg hN
  obtain ⟨-, hden, -⟩ := GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices F E n L hL hL'
  obtain ⟨d₁, hd₁, H₁⟩ := hden g.1
  obtain ⟨d₂, hd₂, H₂⟩ := hden (g⁻¹).1
  have hN' : 0 < N * (d₁ * d₂) := by positivity
  obtain ⟨γ₀, hγ₀, hc₀⟩ := GlobalTheory.T.unitaryGroup_weak_approximation_at_primes F E c n G hG h2 L hL hL' g _ _ hg hN' hN'
  obtain ⟨γ, hγ, hc₁, s₁, hs₁, hs⟩ := GlobalTheory.T.exists_unitary_correction_congruent_one_at_level F E c n G hG L hL hL' γ₀ _ _ hγ₀ hN' hN'
  have hc := congAtA_mul L _ _ _ _ (congAtA_of_congAt (F := F) L _ _ _ hc₁) hc₀
  have hγγ : fm F (γ * γ₀⁻¹).1 * (fm F γ₀.1 * g.1) = fm F γ.1 * g.1 := by
    rw [← mul_assoc, ← fm_mul, ← Units.val_mul, inv_mul_cancel_right]
  rw [hγγ] at hc
  obtain ⟨t, ht, hc⟩ := hc
  set k := fm F γ.1 * g.1 with hk
  set k' := (g⁻¹).1 * fm F (γ⁻¹).1 with hk'
  have hkk : k' * k = 1 := by
    rw [hk, hk', mul_assoc, ← mul_assoc (fm F _), ← fm_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, fm_one, one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨m, hm, Hm⟩ := hden k'
  obtain ⟨t', ht', H'⟩ := inv_integral (hat F (L : Set (Fin n → E))) (Matrix.mulVecLin k).toAddMonoidHom
    (Matrix.mulVecLin k').toAddMonoidHom
    (fun z => by
      change k' *ᵥ (k *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]) _ t m ht hm hc Hm
  refine ⟨γ, hγ, ⟨t, Nat.Coprime.coprime_mul_right_right ht, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨w, hw, e⟩ := hc z hz
    exact ⟨(d₁ * d₂) • w, AddSubgroup.nsmul_mem _ hw _, by rw [e, mul_smul]⟩
  have a1 : ((t * t' : ℕ) : 𝓞 E) ∈ denIdeal L k ⊓ denIdeal L k' := by
    constructor
    · intro z hz
      obtain ⟨w, hw, e⟩ := hc z hz
      rw [one_tmul_natCast_smul, mul_comm, mul_smul]
      refine AddSubgroup.nsmul_mem _ ?_ _
      have : t • (k *ᵥ z) = t • z + (N * (d₁ * d₂)) • w := by rw [← e, smul_sub]; abel
      rw [this]
      exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _)
    · intro z hz
      rw [one_tmul_natCast_smul, mul_smul]
      exact AddSubgroup.nsmul_mem _ (H' z hz) _
  have a2 : ((d₁ * d₂ : ℕ) : 𝓞 E) * s₁ ∈ denIdeal L k ⊓ denIdeal L k' := by
    constructor
    · intro z hz
      have := smul_fm_mem (F := F) L s₁ γ.1 (fun v hv => (hs v hv).1) _ (H₁ z hz)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_comm] at this
      rw [one_tmul_natCast_mul_smul, mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ this _
    · intro z hz
      have := H₂ _ (smul_fm_mem (F := F) L s₁ (γ⁻¹).1 (fun v hv => (hs v hv).2) _ hz)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at this
      rw [one_tmul_natCast_mul_smul, mul_smul]
      exact AddSubgroup.nsmul_mem _ this _
  have hne : denIdeal L k ⊓ denIdeal L k' ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at a2
    exact mul_ne_zero (Nat.cast_ne_zero.2 (by positivity)) hs₁.1 a2
  obtain ⟨s, hsI, hs0, hsP⟩ := exists_mem_primes _ hne
  refine ⟨s, ⟨hs0, fun P hP h => ?_⟩, fun z hz => ⟨hsI.1 z hz, hsI.2 z hz⟩⟩
  have b1 := hsP P hP h a1
  have b2 := hsP P hP h a2
  have hcop : IsCoprime ((t * t' : ℕ) : 𝓞 E) ((N * (d₁ * d₂) : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast (Nat.Coprime.mul_left ht ht')
  have hnot : ((N * (d₁ * d₂) : ℕ) : 𝓞 E) ∉ P := by
    intro hh
    obtain ⟨x, y, e⟩ := hcop
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (e ▸ P.add_mem (P.mul_mem_left x b1) (P.mul_mem_left y hh)))
  refine ⟨?_, fun hh => hnot (by rw [Nat.cast_mul]; exact P.mul_mem_right _ hh)⟩
  rcases hP.mem_or_mem b2 with h1 | h1
  · exact (hnot (by rw [Nat.cast_mul]; exact P.mul_mem_left _ h1)).elim
  · exact (hs₁.2 P hP h1).resolve_right hnot
end GlobalTheory.UnRep.LatForm
