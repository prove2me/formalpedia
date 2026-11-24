-- Prove2me | solution 1 for GlobalTheory.SW.TracePair.trace_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:29:36.368691+00:00
-- url     : https://prove2.me/submissions/4f4d72be-92cc-4b90-89a3-01bba5e38755

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpace
import Theorems.Thm_GlobalTheory_SW_TracePair_card_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.TracePair
variable {E : Type} [Field E] [NumberField E]
open Matrix NumberField in
open scoped ComplexOrder in
private lemma ratCast_algebra_norm_eq_prod_embeddings {E : Type} [Field E] [NumberField E] (x : E) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ τ : E →+* ℂ, τ x := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
open Matrix NumberField in
open scoped ComplexOrder in
private lemma one_le_prod_re_of_isType_of_isIntegral_pos {E : Type} [Field E] [NumberField E]
    (Ψ : Finset (E →+* ℂ)) (hΨ : _root_.GlobalTheory.SW.IsType Ψ) (d : E)
    (hd : IsIntegral ℤ d) (hpos : ∀ τ ∈ Ψ, 0 < τ d) :
    1 ≤ ∏ τ ∈ Ψ, (τ d).re := by
  classical
  unfold _root_.GlobalTheory.SW.IsType at hΨ
  have hreal : ∀ τ ∈ Ψ, ((τ d).re : ℂ) = τ d := fun τ hτ =>
    Complex.ext (by simp) (by simpa using (Complex.pos_iff.1 (hpos τ hτ)).2)
  have hconj : ∀ τ : E →+* ℂ,
      ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hcompl : ∏ τ ∈ Ψᶜ, τ d = ∏ σ ∈ Ψ, ComplexEmbedding.conjugate σ d := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_
      (fun τ _ => hconj τ) (fun τ _ => hconj τ) ?_
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_compl] at hτ ⊢
      by_contra h
      exact hτ ((hΨ τ).2 h)
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_compl] at hτ ⊢
      exact (hΨ τ).1 hτ
    · intro τ _
      rw [hconj]
  have hconjΨ : ∏ σ ∈ Ψ, ComplexEmbedding.conjugate σ d = ∏ σ ∈ Ψ, σ d :=
    Finset.prod_congr rfl fun σ hσ => by
      rw [ComplexEmbedding.conjugate_coe_eq, ← hreal σ hσ, Complex.conj_ofReal]
  have hprod : ∏ σ ∈ Ψ, σ d = ((∏ σ ∈ Ψ, (σ d).re : ℝ) : ℂ) := by
    push_cast
    exact Finset.prod_congr rfl fun σ hσ => (hreal σ hσ).symm
  have hall := ratCast_algebra_norm_eq_prod_embeddings d
  rw [← Finset.prod_mul_prod_compl Ψ, hcompl, hconjΨ, hprod] at hall
  set r := ∏ σ ∈ Ψ, (σ d).re
  have hr : 0 < r := Finset.prod_pos fun σ hσ => (Complex.pos_iff.1 (hpos σ hσ)).1
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ hd)
  have hmr : (m : ℝ) = r * r := by
    have h1 : ((m : ℚ) : ℂ) = (r : ℂ) * r := by
      rw [← hall, ← hm]
      rfl
    exact_mod_cast h1
  have hm1 : (1 : ℝ) ≤ m := by
    have : 0 < m := by exact_mod_cast (hmr ▸ mul_pos hr hr : (0 : ℝ) < m)
    exact_mod_cast this
  nlinarith
open Matrix NumberField in
open scoped ComplexOrder in
private lemma isIntegral_det_natCast_smul_of_den {E : Type} [Field E] {N : ℕ} (c : ℕ)
    (T : Matrix (Fin N) (Fin N) E) (h : _root_.GlobalTheory.SW.Den c T) :
    IsIntegral ℤ (((c : E) • T).det) := by
  unfold _root_.GlobalTheory.SW.Den _root_.GlobalTheory.SW.IntM at h
  rw [det_apply]
  refine IsIntegral.sum _ fun σ _ => ?_
  rw [Units.smul_def]
  exact IsIntegral.smul _ (IsIntegral.prod _ fun i _ => h _ _)
open Matrix NumberField in
open scoped ComplexOrder in
private lemma map_det_natCast_smul {E : Type} [Field E] {N : ℕ} (c : ℕ)
    (T : Matrix (Fin N) (Fin N) E) (τ : E →+* ℂ) :
    τ (((c : E) • T).det) = ((c : ℂ) • T.map τ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp
open Matrix NumberField in
open scoped ComplexOrder in
private lemma exists_conjTranspose_mul_self_eq_of_posDef {N : ℕ} {Y : Matrix (Fin N) (Fin N) ℂ}
    (hY : Y.PosDef) : ∃ C : Matrix (Fin N) (Fin N) ℂ, Cᴴ * C = Y ∧ C.det ≠ 0 := by
  set U : Matrix (Fin N) (Fin N) ℂ := hY.isHermitian.eigenvectorUnitary.1
  set D : Matrix (Fin N) (Fin N) ℂ :=
    diagonal (fun i => ((Real.sqrt (hY.isHermitian.eigenvalues i) : ℝ) : ℂ))
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hY.isHermitian.eigenvectorUnitary
  refine ⟨D * star U, ?_, ?_⟩
  · have hD : Dᴴ = D := by simp [D, diagonal_conjTranspose]
    have hDD : D * D = diagonal (RCLike.ofReal ∘ hY.isHermitian.eigenvalues) := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Function.comp_apply]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]
      rfl
    conv_rhs => rw [hY.isHermitian.spectral_theorem]
    rw [conjTranspose_mul, hD, star_eq_conjTranspose, conjTranspose_conjTranspose]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [← star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.mul_assoc U D D, hDD]
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · rw [det_diagonal, Finset.prod_ne_zero_iff]
      intro i _
      exact_mod_cast (Real.sqrt_pos.2 (hY.eigenvalues_pos i)).ne'
    · have h1 : (star U).det * U.det = 1 := by rw [← det_mul, hU, det_one]
      exact left_ne_zero_of_mul_eq_one h1
open Matrix NumberField in
open scoped ComplexOrder in
private lemma card_mul_prod_rpow_inv_card_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    (Fintype.card ι : ℝ) * (∏ i, x i) ^ (1 / (Fintype.card ι : ℝ)) ≤ ∑ i, x i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Fintype.card ι : ℝ)) x
    (fun _ _ => by positivity) (by simp [Finset.card_univ]) (fun i _ => hx i)
  rw [Real.finset_prod_rpow _ _ (fun i _ => hx i), ← Finset.mul_sum] at h
  calc (Fintype.card ι : ℝ) * (∏ i, x i) ^ (1 / (Fintype.card ι : ℝ))
      ≤ (Fintype.card ι : ℝ) * (1 / (Fintype.card ι : ℝ) * ∑ i, x i) := by gcongr
    _ = ∑ i, x i := by field_simp
open Matrix NumberField in
open scoped ComplexOrder in
private lemma card_mul_det_rpow_le_trace_of_posDef {N : ℕ} (hN : 0 < N) {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : P.PosDef) : (N : ℝ) * P.det.re ^ (1 / (N : ℝ)) ≤ P.trace.re := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have h := card_mul_prod_rpow_inv_card_le_sum hP.isHermitian.eigenvalues
    (fun i => (hP.eigenvalues_pos i).le)
  rw [Fintype.card_fin] at h
  rw [hP.isHermitian.det_eq_prod_eigenvalues, hP.isHermitian.trace_eq_sum_eigenvalues]
  simpa [← Complex.ofReal_prod, ← Complex.ofReal_sum] using h
open Matrix NumberField in
open scoped ComplexOrder in
private lemma card_mul_det_mul_det_rpow_le_trace_mul_of_posDef {N : ℕ} (hN : 0 < N) {A Y : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.PosDef) (hY : Y.PosDef) :
    (N : ℝ) * (A.det.re * Y.det.re) ^ (1 / (N : ℝ)) ≤ (A * Y).trace.re := by
  obtain ⟨C, rfl, hC⟩ := exists_conjTranspose_mul_self_eq_of_posDef hY
  have hinj : Function.Injective Cᴴ.mulVec := by
    refine Matrix.mulVec_injective_iff_isUnit.2 ?_
    rw [isUnit_iff_isUnit_det, det_conjTranspose]
    exact (star_ne_zero.2 hC).isUnit
  have hP := hA.conjTranspose_mul_mul_same hinj
  rw [conjTranspose_conjTranspose] at hP
  have htr : (A * (Cᴴ * C)).trace = (C * A * Cᴴ).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have hAim : A.det.im = 0 := (Complex.pos_iff.1 hA.det_pos).2.symm
  have hYim : (Cᴴ * C).det.im = 0 := (Complex.pos_iff.1 hY.det_pos).2.symm
  have hdet : (C * A * Cᴴ).det = A.det * (Cᴴ * C).det := by
    simp only [det_mul, det_conjTranspose]
    ring
  have hre : (C * A * Cᴴ).det.re = A.det.re * (Cᴴ * C).det.re := by
    rw [hdet, Complex.mul_re, hAim, hYim]
    ring
  rw [htr, ← hre]
  exact card_mul_det_rpow_le_trace_of_posDef hN hP
end GlobalTheory.SW.TracePair
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TracePair
variable {E : Type} [Field E] [NumberField E]
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SW.TracePair
namespace _root_.GlobalTheory.SW.TracePair
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)),
      _root_.GlobalTheory.SW.IsType Ψ → ∀ N c : ℕ, 0 < N → 0 < c → ∃ k : ℝ, 0 < k ∧
        ∀ T : Matrix (Fin N) (Fin N) E, _root_.GlobalTheory.SW.ccT T = T →
          _root_.GlobalTheory.SW.Den c T → (∀ τ : Ψ, (T.map τ.1).PosDef) →
            ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N,
              k * _root_.GlobalTheory.SW.detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤
                ∑ τ : Ψ, (T.map τ.1 * _root_.GlobalTheory.SW.imH (Z τ)).trace.re := by
  intro E _ _ _ Ψ hΨ N c hN hc
  have hne : Ψ.Nonempty := by
    obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ₀ ∈ Ψ
    · exact ⟨τ₀, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ₀, ?_⟩
      by_contra h'
      exact h ((hΨ τ₀).2 h')
  haveI : Nonempty Ψ := hne.to_subtype
  have hn : 0 < Ψ.card := hne.card_pos
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨(Ψ.card * N : ℝ) / c, by positivity, ?_⟩
  intro T _ hden hpos Z hZ
  have hY : ∀ τ : Ψ, (_root_.GlobalTheory.SW.imH (Z τ)).PosDef := by
    simpa [_root_.GlobalTheory.SW.Hn] using hZ
  have hA : ∀ τ : Ψ, ((c : ℂ) • T.map τ.1).PosDef := fun τ =>
    (hpos τ).smul (by exact_mod_cast hc)
  set a : Ψ → ℝ := fun τ => ((c : ℂ) • T.map τ.1).det.re
  set y : Ψ → ℝ := fun τ => (_root_.GlobalTheory.SW.imH (Z τ)).det.re
  have ha : ∀ τ, 0 < a τ := fun τ => (Complex.pos_iff.1 (hA τ).det_pos).1
  have hy : ∀ τ, 0 < y τ := fun τ => (Complex.pos_iff.1 (hY τ).det_pos).1
  have hD : _root_.GlobalTheory.SW.detIm Z = ∏ τ, y τ := rfl
  have hprod_a : 1 ≤ ∏ τ, a τ := by
    have h := one_le_prod_re_of_isType_of_isIntegral_pos Ψ hΨ (((c : E) • T).det)
      (isIntegral_det_natCast_smul_of_den c T hden) (fun τ hτ => by
        rw [map_det_natCast_smul]
        exact (hA ⟨τ, hτ⟩).det_pos)
    have h' : ∏ τ, a τ = ∏ τ : Ψ, (τ.1 ((c : E) • T).det).re :=
      Finset.prod_congr rfl fun τ _ => by simp only [a]; rw [map_det_natCast_smul]
    rw [h', Finset.prod_coe_sort Ψ (fun τ => (τ ((c : E) • T).det).re)]
    exact h
  have hsum : (c : ℝ) * ∑ τ : Ψ, (T.map τ.1 * _root_.GlobalTheory.SW.imH (Z τ)).trace.re =
      ∑ τ : Ψ, ((c : ℂ) • T.map τ.1 * _root_.GlobalTheory.SW.imH (Z τ)).trace.re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
    simp
  have hlow : ∀ τ : Ψ, (N : ℝ) * (a τ * y τ) ^ (1 / (N : ℝ)) ≤
      ((c : ℂ) • T.map τ.1 * _root_.GlobalTheory.SW.imH (Z τ)).trace.re := fun τ =>
    card_mul_det_mul_det_rpow_le_trace_mul_of_posDef hN (hA τ) (hY τ)
  have hamgm := card_mul_prod_rpow_inv_card_le_sum (fun τ : Ψ => (a τ * y τ) ^ (1 / (N : ℝ)))
    (fun τ => by have := ha τ; have := hy τ; positivity)
  rw [Fintype.card_coe, Real.finset_prod_rpow _ _ (fun τ _ => (mul_pos (ha τ) (hy τ)).le),
    ← Real.rpow_mul (Finset.prod_nonneg fun τ _ => (mul_pos (ha τ) (hy τ)).le),
    Finset.prod_mul_distrib, ← hD] at hamgm
  have he : 1 / (N : ℝ) * (1 / (Ψ.card : ℝ)) = 1 / ((Ψ.card * N : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [he] at hamgm
  have hDnn : 0 ≤ _root_.GlobalTheory.SW.detIm Z := by
    rw [hD]
    exact Finset.prod_nonneg fun τ _ => (hy τ).le
  have hmono : _root_.GlobalTheory.SW.detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤
      ((∏ τ, a τ) * _root_.GlobalTheory.SW.detIm Z) ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) :=
    Real.rpow_le_rpow hDnn (le_mul_of_one_le_left hDnn hprod_a) (by positivity)
  have hchain : (Ψ.card * N : ℝ) * _root_.GlobalTheory.SW.detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤
      (c : ℝ) * ∑ τ : Ψ, (T.map τ.1 * _root_.GlobalTheory.SW.imH (Z τ)).trace.re := by
    rw [hsum]
    calc (Ψ.card * N : ℝ) * _root_.GlobalTheory.SW.detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ))
        ≤ (N : ℝ) * ((Ψ.card : ℝ) *
            ((∏ τ, a τ) * _root_.GlobalTheory.SW.detIm Z) ^ (1 / ((Ψ.card * N : ℕ) : ℝ))) := by
          rw [← mul_assoc, mul_comm (N : ℝ)]
          gcongr
      _ ≤ (N : ℝ) * ∑ τ : Ψ, (a τ * y τ) ^ (1 / (N : ℝ)) := by gcongr
      _ = ∑ τ : Ψ, (N : ℝ) * (a τ * y τ) ^ (1 / (N : ℝ)) := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum fun τ _ => hlow τ
  rw [div_mul_eq_mul_div, div_le_iff₀ hcR]
  linarith
end _root_.GlobalTheory.SW.TracePair
end GlobalTheory.SW.TracePair
