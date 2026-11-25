-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.weak_approximation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:46.420716+00:00
-- url     : https://prove2.me/submissions/4532ba67-686a-4c10-8820-af224bb54c3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_preserves_iff
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_core
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_exists_stab
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_skewPart_smul
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_unitary_inv
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_adelic_unitary_scaling_unit
import Theorems.Thm_GlobalTheory_T_exists_inverse_one_add_preserving_adelicCompletion
import Theorems.Thm_GlobalTheory_T_exists_rational_matrix_approx_adele_linear_map
import Theorems.Thm_GlobalTheory_T_idempotent_adeles_and_small_adelic_matrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.WeakApprox
namespace GlobalTheory.UnRep.WeakApprox
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N D : ℕ), IsUnA c G g.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N D (fm F γ.1 * g.1) := by
  intro F E _ _ _ _ _ c n G hG hr L hfg hsp g N D hg hN hD
  classical
  obtain ⟨hcc, hc1, hGc, hdet⟩ := hG
  obtain ⟨i1, i2, -, i4, i5⟩ := GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices F E n L hfg hsp
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have hne : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 hN.ne'
    refine (Ideal.finite_factors hne).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  obtain ⟨e, he1, he0⟩ := i1 hfin.toFinset
  have he1' : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 1 :=
    fun v hv => he1 v (hfin.mem_toFinset.2 hv)
  have he0' : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0 :=
    fun v hv => he0 v fun h => hv (hfin.mem_toFinset.1 h)
  have hee : e * e = e := by
    refine FiniteAdeleRing.ext F fun v => ?_
    change e v * e v = e v
    by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
    · rw [he1' v hv, mul_one]
    · rw [he0' v hv, mul_zero]
  have heI : ∀ v, e v ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
    · rw [he1' v hv]; exact one_mem _
    · rw [he0' v hv]; exact zero_mem _
  have hsupp : {v | e v ≠ 0}.Finite := hfin.subset fun v hv => by
    by_contra h
    exact hv (he0' v h)
  have hsub : ((1 - e) ⊗ₜ[F] (1 : E) : RA F E) = 1 - e ⊗ₜ[F] (1 : E) := by
    rw [TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]

  have key : ∀ k : Matrix (Fin n) (Fin n) (RA F E),
      (∃ X ∈ stab (hat F (L : Set (Fin n → E))), (e ⊗ₜ[F] (1 : E) : RA F E) • (k - 1) = D • X) →
      CongAtA F L N D k := by
    rintro k ⟨X, hX, hk⟩
    obtain ⟨t, ht, H⟩ := i4 N D (1 - e) (k - 1) hD fun v hv => by
      change 1 - e v = 0
      rw [he1' v hv, sub_self]
    refine ⟨t, ht, fun z hz => ?_⟩
    obtain ⟨w, hw, hwz⟩ := H z hz
    refine ⟨w + t • (X *ᵥ z), add_mem hw (nsmul_mem (hX z hz) t), ?_⟩
    have : k *ᵥ z - z = (((1 - e) ⊗ₜ[F] (1 : E) : RA F E) • (k - 1)) *ᵥ z + D • (X *ᵥ z) := by
      rw [← Matrix.smul_mulVec D, ← hk, ← Matrix.add_mulVec, ← add_smul, hsub, sub_add_cancel, one_smul,
        Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [this, smul_add, hwz, smul_add, smul_comm t D]
  by_cases hz : (e ⊗ₜ[F] (1 : E) : RA F E) = 0
  · refine ⟨1, fun x y => by simp, key _ ⟨0, zero_mem _, ?_⟩⟩
    rw [hz, zero_smul, smul_zero]
  let ι : E →+* RA F E := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom
  let σ : RA F E →+* RA F E := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom
  let c' : E →+* E := (c : E →ₐ[F] E).toRingHom
  have hσt : ∀ (a : FiniteAdeleRing (𝓞 F) F) (x : E), σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] c x := fun a x => rfl
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => rw [hσt, hσt, hcc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hσ1 : ∀ a : FiniteAdeleRing (𝓞 F) F, σ (a ⊗ₜ[F] (1 : E)) = a ⊗ₜ[F] (1 : E) := by
    intro a; rw [hσt, map_one]
  have hunit : ∀ d : ℕ, 0 < d → IsUnit (d : RA F E) := by
    intro d hd
    have := (Nat.cast_ne_zero.2 hd.ne' : (d : E) ≠ 0).isUnit.map ι
    rwa [map_natCast] at this
  have hgu : g.1ᵀ * G.map ι * g.1.map σ = G.map ι := (preserves_iff σ (G.map ι) g.1).1 hg
  obtain ⟨lam, hlam, hu⟩ := GlobalTheory.T.adelic_unitary_scaling_unit F E c hr hcc hc1 n (g⁻¹).1 e hee hsupp
  rw [hsub] at hu
  obtain ⟨γ, hγ, hcong⟩ := core ι c' σ (fun x => hσt 1 x) hcc hσσ G
    (by ext a b; exact hGc b a) hdet two_ne_zero (stab (hat F (L : Set (Fin n → E))))
    (fun M => by
      obtain ⟨d, hd, H⟩ := i2 M
      exact ⟨d, hd, fun z hz => by rw [Matrix.smul_mulVec]; exact H z hz⟩)
    (e ⊗ₜ[F] (1 : E)) (by rw [Algebra.TensorProduct.tmul_mul_tmul, hee, mul_one]) (hσ1 e) hz
    (fun X hX z hz => by rw [Matrix.smul_mulVec]; exact i5 e heI _ (hX z hz))
    N hN (fun X hX => by
      obtain ⟨W, hW, hW'⟩ := GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion F E n L hfg hsp N e heI he0' X hX
      exact ⟨W, hW', hW⟩)
    (fun M D' hD' => by
      obtain ⟨M₀, H⟩ := GlobalTheory.T.exists_rational_matrix_approx_adele_linear_map F E n L hfg hsp (skewPart σ (G.map ι))
        (fun a M => skewPart_smul σ _ _ (hσ1 a) M) M D' hD'
      obtain ⟨X, hX, hX'⟩ := exists_stab _ _ D' (hunit D' hD') H
      rw [map_sub] at hX'
      exact ⟨M₀, X, hX, hX'⟩)
    g.1 (g⁻¹).1 g.inv_mul (unitary_inv σ _ g.1 _ g.mul_inv hgu) lam hlam hu D hD
  have hγdet : γ.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hγ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
    exact hdet this.symm
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hγdet, (preserves_iff c' G γ).2 hγ, key _ hcong⟩
end GlobalTheory.UnRep.WeakApprox
