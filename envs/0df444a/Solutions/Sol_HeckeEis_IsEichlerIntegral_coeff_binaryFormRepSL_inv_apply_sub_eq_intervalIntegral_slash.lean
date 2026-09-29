-- Prove2me | solution 1 for HeckeEis.IsEichlerIntegral.coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6b0232cc-5d50-5795-a710-f40753ead657

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_HeckeEis_EichlerIntegral
import Theorems.Thm_HeckeEis_IsEichlerIntegral_slash
import Theorems.Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash

set_option autoImplicit false

open scoped MatrixGroups ModularForm Manifold Topology

namespace A2PER

open UpperHalfPlane MvPolynomial HeckeEis

variable (n : ℕ)

abbrev V : Type := ↥(BinaryForm ℂ n)

noncomputable abbrev R : SL(2, ℤ) →* (V n →ₗ[ℂ] V n) := binaryFormRepSL ℂ n

theorem eval_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 2 → ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval x (binarySubst ℂ M P)
      = MvPolynomial.eval (fun j => ∑ i : Fin 2, x i * ((M i j : ℤ) : ℂ)) P := by
  unfold binarySubst
  rw [MvPolynomial.aeval_eq_bind₁]
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) x (MvPolynomial.bind₁ _ P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun i => MvPolynomial.eval x _) P = _
  congr 2
  funext j
  simp [Fin.sum_univ_two, mul_comm]

noncomputable def top (P : V n) : ℂ := MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) ℂ)

theorem top_eq_eval (P : V n) : top n P = MvPolynomial.eval ![0, 1] (P : MvPolynomial (Fin 2) ℂ) :=
  coeff_single_one_eq_eval_of_mem_binaryForm P.2

theorem top_sub (P Q : V n) : top n (P - Q) = top n P - top n Q := by simp [top]

theorem top_T_zpow (m : ℤ) (P : V n) : top n (R n (ModularGroup.T ^ m) P) = top n P := by
  rw [top_eq_eval, top_eq_eval, binaryFormRepSL_apply_coe, eval_binarySubst, ModularGroup.coe_T_zpow]
  have h : (fun j : Fin 2 => ∑ i : Fin 2, (![0, 1] : Fin 2 → ℂ) i * (((!![1, m; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ))
      = ![0, 1] := by
    funext j
    fin_cases j <;> simp [Fin.sum_univ_two]
  rw [h]

theorem top_linePow (τ : ℂ) : top n (linePow n τ) = 1 := by
  rw [top_eq_eval, coe_linePow]
  simp

theorem main {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {F : ℍ → V n} (hF : IsEichlerIntegral n f F) (σ : SL(2, ℤ))
    (h : ℤ) (τ : ℍ) :
    top n (R n σ⁻¹ (F ((σ * ModularGroup.T ^ h * σ⁻¹) • τ) - R n (σ * ModularGroup.T ^ h * σ⁻¹) (F τ)))
      = ∫ t in (0 : ℝ)..(h : ℝ), (f ∣[((n : ℤ) + 2)] σ) ((t : ℝ) +ᵥ (σ⁻¹ • τ)) := by

  set g : ℍ → ℂ := f ∣[((n : ℤ) + 2)] σ with hgdef
  set G : ℍ → V n := fun τ' => R n σ⁻¹ (F (σ • τ')) with hGdef
  have hG : IsEichlerIntegral n g G := hF.slash σ
  set τ₀ : ℍ := σ⁻¹ • τ with hτ₀
  have hστ₀ : σ • τ₀ = τ := smul_inv_smul σ τ

  have h1 : R n σ⁻¹ (F ((σ * ModularGroup.T ^ h * σ⁻¹) • τ)) = G ((h : ℝ) +ᵥ τ₀) := by
    simp only [hGdef]
    rw [← modular_T_zpow_smul, ← mul_smul, ← mul_smul]
  have h2 : R n σ⁻¹ (R n (σ * ModularGroup.T ^ h * σ⁻¹) (F τ)) = R n (ModularGroup.T ^ h) (G τ₀) := by
    simp only [hGdef]
    rw [hστ₀, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  rw [map_sub, h1, h2, top_sub, top_T_zpow]

  set φ : ℝ → ℂ := fun t => top n (G ((t : ℝ) +ᵥ τ₀)) with hφ
  have hpt : ∀ t : ℝ, ofComplex ((t : ℂ) + (τ₀ : ℂ)) = (t : ℝ) +ᵥ τ₀ := by
    intro t
    have him : 0 < ((t : ℂ) + (τ₀ : ℂ)).im := by simpa using τ₀.im_pos
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos him, coe_vadd]
  have hderiv : ∀ t : ℝ, HasDerivAt φ (g ((t : ℝ) +ᵥ τ₀)) t := by
    intro t
    have hE := hG (Finsupp.single 1 n) ((t : ℝ) +ᵥ τ₀)
    rw [show MvPolynomial.coeff (Finsupp.single 1 n) ((linePow n (((t : ℝ) +ᵥ τ₀ : ℍ) : ℂ) : V n) : MvPolynomial (Fin 2) ℂ)
      = 1 from top_linePow n _, mul_one] at hE

    have hline : HasDerivAt (fun s : ℝ => (s : ℂ) + (τ₀ : ℂ)) 1 t := by
      simpa using ((hasDerivAt_id (t : ℂ)).add_const (τ₀ : ℂ)).comp_ofReal
    have hE' : HasDerivAt (fun z : ℂ => MvPolynomial.coeff (Finsupp.single 1 n) ((G (ofComplex z) : V n) : MvPolynomial (Fin 2) ℂ))
        (g ((t : ℝ) +ᵥ τ₀)) ((t : ℂ) + (τ₀ : ℂ)) := by
      have : ((((t : ℝ) +ᵥ τ₀ : ℍ)) : ℂ) = (t : ℂ) + (τ₀ : ℂ) := coe_vadd _ _
      rw [← this]; exact hE
    have hcomp := hE'.scomp t hline
    have heq : (fun z : ℂ => MvPolynomial.coeff (Finsupp.single 1 n) ((G (ofComplex z) : V n) : MvPolynomial (Fin 2) ℂ))
        ∘ (fun s : ℝ => (s : ℂ) + (τ₀ : ℂ)) = φ := by
      funext s
      simp only [Function.comp_apply, hφ, hpt s, top]
    rw [heq, one_smul] at hcomp
    exact hcomp

  have hgc : Continuous g := by
    have : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
      rw [hgdef, ModularForm.SL_slash]; exact hf.slash _ _
    exact this.continuous
  have hvadd : Continuous fun t : ℝ => (t : ℝ) +ᵥ τ₀ := by
    refine UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr ?_
    have : ((↑) : ℍ → ℂ) ∘ (fun t : ℝ => (t : ℝ) +ᵥ τ₀) = fun t : ℝ => (t : ℂ) + (τ₀ : ℂ) := by
      funext t; simp [coe_vadd]
    rw [this]
    fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => g ((t : ℝ) +ᵥ τ₀)) MeasureTheory.volume 0 (h : ℝ) :=
    (hgc.comp hvadd).intervalIntegrable _ _

  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  rw [hftc]
  simp only [hφ, zero_vadd]

end A2PER

theorem solution {n : ℕ}
    {f : UpperHalfPlane → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (σ : SL(2, ℤ)) (h : ℤ) (τ : UpperHalfPlane) :
    MvPolynomial.coeff (Finsupp.single 1 n)
      ((HeckeEis.binaryFormRepSL ℂ n σ⁻¹
          (F ((σ * ModularGroup.T ^ h * σ⁻¹) • τ)
            - HeckeEis.binaryFormRepSL ℂ n (σ * ModularGroup.T ^ h * σ⁻¹) (F τ)) : ↥(HeckeEis.BinaryForm ℂ n)) :
        MvPolynomial (Fin 2) ℂ)
      = ∫ t in (0 : ℝ)..(h : ℝ), (f ∣[((n : ℤ) + 2)] σ) ((t : ℝ) +ᵥ (σ⁻¹ • τ)) :=
  A2PER.main n hf hF σ h τ

end S_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash
end P2MW
export P2MW.S_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash (solution)
