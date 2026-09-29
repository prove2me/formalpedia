-- Prove2me | solution 1 for ModularCurve.not_isEventuallyEisenstein_of_modRepIsIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fb3935a3-ac9c-5537-a05e-0fe9560e9f79

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Theorems.Thm_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel
import Theorems.Thm_WeierstrassCurve_det_galoisRep_frobenius_eq_prime
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_FrobeniusDensity_exists_frobenius_conj_pow_of_statement
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_not_isEventuallyEisenstein_of_modRepIsIrreducible
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

namespace WLightEB

open Module Submodule Polynomial
open scoped Matrix

section MatrixAlgebra

variable {F : Type*} [Field F]

private def fixW (M : Matrix (Fin 2) (Fin 2) F) : Submodule F (Fin 2 → F) :=
  LinearMap.ker (Matrix.toLin' (M - 1))

private def movE (M : Matrix (Fin 2) (Fin 2) F) : Submodule F (Fin 2 → F) :=
  LinearMap.range (Matrix.toLin' (M - 1))

private theorem mem_fixW_iff (M : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    v ∈ fixW M ↔ M *ᵥ v = v := by
  simp only [fixW, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero]

private theorem sub_mulVec_mem_movE (M : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    M *ᵥ v - v ∈ movE M := by
  exact ⟨v, by rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]⟩

private theorem line_eq_of_inf_ne_bot {L L' : Submodule F (Fin 2 → F)} (hL : finrank F L = 1)
    (hL' : finrank F L' = 1) (h : L ⊓ L' ≠ ⊥) : L = L' := by
  have h1 : finrank F ↥(L ⊓ L') ≠ 0 := fun h0 => h (Submodule.finrank_eq_zero.mp h0)
  have h2 : finrank F ↥(L ⊓ L') ≤ 1 := hL ▸ Submodule.finrank_mono inf_le_left
  have h3 : finrank F ↥(L ⊓ L') ≤ finrank F L' := Submodule.finrank_mono inf_le_right
  have hLL : L ⊓ L' = L := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  exact Submodule.eq_of_le_of_finrank_eq (inf_eq_left.mp hLL) (hL.trans hL'.symm)

private theorem finrank_movE_fixW {M : Matrix (Fin 2) (Fin 2) F} (hM : M ≠ 1) (hd : (M - 1).det = 0) :
    finrank F (movE M) = 1 ∧ finrank F (fixW M) = 1 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (M - 1))
  rw [Module.finrank_fin_fun] at hsum
  have hE : finrank F (movE M) ≠ 0 := by
    intro h0
    have hbot : LinearMap.range (Matrix.toLin' (M - 1)) = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hzero : Matrix.toLin' (M - 1) = 0 := LinearMap.range_eq_bot.mp hbot
    have : M - 1 = 0 := (LinearEquiv.map_eq_zero_iff Matrix.toLin').mp hzero
    exact hM (sub_eq_zero.mp this)
  have hW : finrank F (fixW M) ≠ 0 := by
    intro h0
    have hbot : LinearMap.ker (Matrix.toLin' (M - 1)) = ⊥ := Submodule.finrank_eq_zero.mp h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    have : v ∈ LinearMap.ker (Matrix.toLin' (M - 1)) := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, hv]
    rw [hbot, Submodule.mem_bot] at this
    exact hv0 this
  change finrank F (movE M) + finrank F (fixW M) = 2 at hsum
  omega

private theorem movE_eq_or_fixW_eq {M P : Matrix (Fin 2) (Fin 2) F} (hM : M ≠ 1) (hMd : (M - 1).det = 0)
    (hP : P ≠ 1) (hPd : (P - 1).det = 0) (hMP : (M * P - 1).det = 0) :
    movE M = movE P ∨ fixW M = fixW P := by
  by_contra hc
  push Not at hc
  obtain ⟨hE, hW⟩ := hc
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMP
  have hEM := (finrank_movE_fixW hM hMd)
  have hEP := (finrank_movE_fixW hP hPd)

  have hsplit : (M - 1) *ᵥ (P *ᵥ x) + (P *ᵥ x - x) = 0 := by
    have : (M - 1) *ᵥ (P *ᵥ x) + (P *ᵥ x - x) = (M * P - 1) *ᵥ x := by
      rw [Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec,
        Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [this, hx]
  have hz : (M - 1) *ᵥ (P *ᵥ x) ∈ movE M := ⟨P *ᵥ x, Matrix.toLin'_apply _ _⟩
  have hy : P *ᵥ x - x ∈ movE P := sub_mulVec_mem_movE P x
  have hy' : P *ᵥ x - x ∈ movE M := by
    have : P *ᵥ x - x = -((M - 1) *ᵥ (P *ᵥ x)) := eq_neg_of_add_eq_zero_right hsplit
    rw [this]
    exact (movE M).neg_mem hz
  by_cases hyx : P *ᵥ x - x = 0
  ·
    have hxP : x ∈ fixW P := (mem_fixW_iff P x).mpr (sub_eq_zero.mp hyx)
    have hPx : P *ᵥ x = x := sub_eq_zero.mp hyx
    have hxM : x ∈ fixW M := by
      rw [hPx, sub_self, add_zero, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hsplit
      exact (mem_fixW_iff M x).mpr hsplit
    exact hW (line_eq_of_inf_ne_bot hEM.2 hEP.2
      (fun hb => hx0 ((Submodule.mem_bot F).mp (hb ▸ (Submodule.mem_inf.mpr ⟨hxM, hxP⟩)))))
  · exact hE (line_eq_of_inf_ne_bot hEM.1 hEP.1
      (fun hb => hyx ((Submodule.mem_bot F).mp (hb ▸ (Submodule.mem_inf.mpr ⟨hy', hy⟩)))))

private theorem det_sub_one_eq_zero_of_sq {M : Matrix (Fin 2) (Fin 2) F} (hs : (M - 1) * (M - 1) = 0) :
    (M - 1).det = 0 := by
  have h := congrArg Matrix.det hs
  rw [Matrix.det_mul, Matrix.det_zero] at h
  exact mul_self_eq_zero.mp h

private theorem movE_eq_fixW_of_sq {M : Matrix (Fin 2) (Fin 2) F} (hM : M ≠ 1)
    (hs : (M - 1) * (M - 1) = 0) : movE M = fixW M := by
  have hfr := finrank_movE_fixW hM (det_sub_one_eq_zero_of_sq hs)
  apply Submodule.eq_of_le_of_finrank_eq _ (hfr.1.trans hfr.2.symm)
  rintro w ⟨y, rfl⟩
  rw [mem_fixW_iff, Matrix.toLin'_apply]
  have h : (M - 1) *ᵥ ((M - 1) *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec, hs, Matrix.zero_mulVec]
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h

private theorem fixW_eq_of_sq {M P : Matrix (Fin 2) (Fin 2) F} (hM : M ≠ 1) (hMs : (M - 1) * (M - 1) = 0)
    (hP : P ≠ 1) (hPs : (P - 1) * (P - 1) = 0) (hMP : (M * P - 1).det = 0) :
    fixW M = fixW P := by
  rcases movE_eq_or_fixW_eq hM (det_sub_one_eq_zero_of_sq hMs) hP (det_sub_one_eq_zero_of_sq hPs)
      hMP with h | h
  · rw [← movE_eq_fixW_of_sq hM hMs, h, movE_eq_fixW_of_sq hP hPs]
  · exact h

private theorem mul_self_fin_two (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

private theorem sub_mul_sub_eq_zero {M : Matrix (Fin 2) (Fin 2) F} {u v : F} (htr : M.trace = u + v)
    (hdet : M.det = u * v) :
    (M - u • (1 : Matrix (Fin 2) (Fin 2) F)) * (M - v • (1 : Matrix (Fin 2) (Fin 2) F)) = 0 := by
  have h := mul_self_fin_two M
  rw [htr, hdet] at h
  rw [sub_mul, mul_sub, mul_sub, h]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    add_smul, mul_comm v u]
  abel

private theorem pow_sub_mul_pow_sub_eq_zero {M : Matrix (Fin 2) (Fin 2) F} {u v : F}
    (h : (M - u • (1 : Matrix (Fin 2) (Fin 2) F)) * (M - v • (1 : Matrix (Fin 2) (Fin 2) F)) = 0)
    (n : ℕ) :
    (M ^ n - (u ^ n) • (1 : Matrix (Fin 2) (Fin 2) F)) *
      (M ^ n - (v ^ n) • (1 : Matrix (Fin 2) (Fin 2) F)) = 0 := by
  have hdvd : (X - C u) * (X - C v) ∣ (X ^ n - C u ^ n) * (X ^ n - C v ^ n) :=
    mul_dvd_mul (sub_dvd_pow_sub_pow X (C u) n) (sub_dvd_pow_sub_pow X (C v) n)
  obtain ⟨q, hq⟩ := hdvd
  have h0 : Polynomial.aeval M ((X - C u) * (X - C v)) = 0 := by
    simpa [Algebra.algebraMap_eq_smul_one] using h
  have h1 := congrArg (Polynomial.aeval M) hq
  rw [map_mul (Polynomial.aeval M) ((X - C u) * (X - C v)) q, h0, zero_mul] at h1
  simpa [Algebra.algebraMap_eq_smul_one, _root_.smul_pow, one_pow] using h1

private theorem conj_sub_smul_one {C C' N : Matrix (Fin 2) (Fin 2) F} (hCC' : C * C' = 1) (c : F) :
    C * (N - c • (1 : Matrix (Fin 2) (Fin 2) F)) * C' = C * N * C' - c • 1 := by
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hCC']

private theorem conj_sub_one {C C' N : Matrix (Fin 2) (Fin 2) F} (hCC' : C * C' = 1) :
    C * (N - 1) * C' = C * N * C' - 1 := by
  rw [mul_sub, sub_mul, mul_one, hCC']

private theorem conj_mul_conj {C C' A B : Matrix (Fin 2) (Fin 2) F} (hC'C : C' * C = 1) :
    (C * A * C') * (C * B * C') = C * (A * B) * C' := by
  rw [show C * A * C' * (C * B * C') = C * A * (C' * C) * B * C' by
      simp only [mul_assoc], hC'C, mul_one]
  simp only [mul_assoc]

end MatrixAlgebra

section Endgame

variable {F : Type*} [Field F] {G : Type*} [Group G]

private theorem exists_line_of_unipotent_on_commutators (ρ : G →* Matrix (Fin 2) (Fin 2) F) (K : Set G)
    (hKconj : ∀ g : G, ∀ h ∈ K, g * h * g⁻¹ ∈ K) (hKmul : ∀ h ∈ K, ∀ h' ∈ K, h * h' ∈ K)
    (hcomm : ∀ g g' : G, g * g' * g⁻¹ * g'⁻¹ ∈ K)
    (hunip : ∀ h ∈ K, (ρ h - 1) * (ρ h - 1) = 0)
    (heig : ∀ g : G, ∃ u v : F, u ≠ 0 ∧
      (ρ g - u • (1 : Matrix (Fin 2) (Fin 2) F)) * (ρ g - v • (1 : Matrix (Fin 2) (Fin 2) F)) = 0) :
    ∃ L : Submodule F (Fin 2 → F), finrank F L = 1 ∧ ∀ g : G, ∀ w ∈ L, ρ g *ᵥ w ∈ L := by
  by_cases hK : ∃ h ∈ K, ρ h ≠ 1
  ·
    obtain ⟨h₀, hh₀, hne⟩ := hK
    refine ⟨fixW (ρ h₀), (finrank_movE_fixW hne (det_sub_one_eq_zero_of_sq (hunip h₀ hh₀))).2,
      fun g w hw => ?_⟩
    have hh₁ : g * h₀ * g⁻¹ ∈ K := hKconj g h₀ hh₀
    have hne₁ : ρ (g * h₀ * g⁻¹) ≠ 1 := by
      intro h1
      apply hne
      rw [show h₀ = g⁻¹ * (g * h₀ * g⁻¹) * g by group, map_mul, map_mul, h1, mul_one, ← map_mul,
        inv_mul_cancel, map_one]
    have hfix : fixW (ρ h₀) = fixW (ρ (g * h₀ * g⁻¹)) :=
      fixW_eq_of_sq hne (hunip h₀ hh₀) hne₁ (hunip _ hh₁)
        (det_sub_one_eq_zero_of_sq (by rw [← map_mul]; exact hunip _ (hKmul h₀ hh₀ _ hh₁)))
    rw [mem_fixW_iff] at hw
    rw [hfix, mem_fixW_iff, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec w (ρ g⁻¹) (ρ g), ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
      hw]
  ·
    push Not at hK
    have hab : ∀ g g' : G, ρ g * ρ g' = ρ g' * ρ g := fun g g' => by
      rw [← map_mul, show g * g' = (g * g' * g⁻¹ * g'⁻¹) * (g' * g) by group, map_mul,
        hK _ (hcomm g g'), one_mul, map_mul]
    by_cases hsc : ∀ g : G, ∃ c : F, ρ g = c • (1 : Matrix (Fin 2) (Fin 2) F)
    ·
      refine ⟨F ∙ (Pi.single 0 1),
        finrank_span_singleton (Function.ne_iff.mpr ⟨0, by simp⟩), fun g w hw => ?_⟩
      obtain ⟨c, hc⟩ := hsc g
      rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact Submodule.smul_mem _ c hw
    ·
      push Not at hsc
      obtain ⟨g₁, hg₁⟩ := hsc
      obtain ⟨u, v, hu, huv⟩ := heig g₁
      have hdet : (ρ g₁ - u • (1 : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
        by_contra hd
        apply hg₁ v
        have hunit : IsUnit (ρ g₁ - u • (1 : Matrix (Fin 2) (Fin 2) F)).det :=
          isUnit_iff_ne_zero.mpr hd
        have h2 := congrArg ((ρ g₁ - u • (1 : Matrix (Fin 2) (Fin 2) F))⁻¹ * ·) huv
        simp only [← mul_assoc, Matrix.nonsing_inv_mul _ hunit, one_mul, mul_zero] at h2
        exact sub_eq_zero.mp h2
      have hB1 : u⁻¹ • ρ g₁ ≠ 1 := fun h => hg₁ u (by
        rw [← h, smul_smul, mul_inv_cancel₀ hu, one_smul])
      have hBd : (u⁻¹ • ρ g₁ - 1).det = 0 := by
        have : u⁻¹ • ρ g₁ - 1 = u⁻¹ • (ρ g₁ - u • (1 : Matrix (Fin 2) (Fin 2) F)) := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hu, one_smul]
        rw [this, Matrix.det_smul, hdet, mul_zero]
      refine ⟨fixW (u⁻¹ • ρ g₁), (finrank_movE_fixW hB1 hBd).2, fun g w hw => ?_⟩
      rw [mem_fixW_iff] at hw ⊢
      rw [Matrix.mulVec_mulVec, Matrix.smul_mul, hab g₁ g, ← Matrix.mul_smul,
        ← Matrix.mulVec_mulVec, hw]

end Endgame

section Arithmetic

open ModularCurve

private theorem prime_dvd_of_intCast_mem {p : ℕ} (hp : p.Prime) {𝔪 : Ideal HeckeAlg} (h𝔪 : 𝔪 ≠ ⊤)
    (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪) {z : ℤ} (hz : (z : HeckeAlg) ∈ 𝔪) : (p : ℤ) ∣ z := by
  by_contra hdvd
  have hcop : IsCoprime (p : ℤ) z :=
    (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hdvd
  obtain ⟨a, c, hac⟩ := hcop
  apply h𝔪
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : HeckeAlg) =
      (a : HeckeAlg) * ((p : ℕ) : HeckeAlg) + (c : HeckeAlg) * (z : HeckeAlg) := by
    have := congrArg (Int.cast : ℤ → HeckeAlg) hac
    push_cast at this
    exact this.symm
  rw [h1]
  exact 𝔪.add_mem (𝔪.mul_mem_left _ hp𝔪) (𝔪.mul_mem_left _ hz)

private theorem pow_mul_apOfModel_eq {p : ℕ} (hp : p.Prime) (W : WeierstrassCurve ℤ) (S₀ : Set ℕ) (i : ℕ)
    {𝔪 : Ideal HeckeAlg} (h𝔪 : 𝔪 ≠ ⊤) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → W.IsGoodPrimeFor ℓ →
      heckeGen ⟨ℓ, hℓ⟩ - ((ℓ ^ i * W.apOfModel ℓ : ℤ) : HeckeAlg) ∈ 𝔪)
    {S : Finset Nat.Primes}
    (hS : ∀ ℓ : Nat.Primes, ℓ ∉ S → heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1) ∈ 𝔪)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS₀ : ℓ ∉ S₀) (hℓS : (⟨ℓ, hℓ⟩ : Nat.Primes) ∉ S)
    (hgood : W.IsGoodPrimeFor ℓ) :
    (ℓ : ZMod p) ^ i * ((W.apOfModel ℓ : ℤ) : ZMod p) = ℓ + 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hS' : heckeGen ⟨ℓ, hℓ⟩ - (((ℓ : ℕ) : HeckeAlg) + 1) ∈ 𝔪 := hS ⟨ℓ, hℓ⟩ hℓS
  have h1 := 𝔪.sub_mem (hcong ℓ hℓ hℓS₀ hgood) hS'
  have h2 : ((ℓ + 1 - ℓ ^ i * W.apOfModel ℓ : ℤ) : HeckeAlg) =
      (heckeGen ⟨ℓ, hℓ⟩ - ((ℓ ^ i * W.apOfModel ℓ : ℤ) : HeckeAlg)) -
        (heckeGen ⟨ℓ, hℓ⟩ - (((ℓ : ℕ) : HeckeAlg) + 1)) := by
    push_cast
    ring
  rw [← h2] at h1
  have h3 := prime_dvd_of_intCast_mem hp h𝔪 hp𝔪 h1
  have h4 : ((ℓ + 1 - ℓ ^ i * W.apOfModel ℓ : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h3
  push_cast at h4
  linear_combination -h4

end Arithmetic

section Assembly

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ModularCurve
open scoped IntermediateField

private abbrev Tors (W : WeierstrassCurve ℤ) (p : ℕ) : Type :=
  Submodule.torsionBy ℤ
    (WeierstrassCurve.Affine.Point
      (WeierstrassCurve.Affine.baseChange (W.map (Int.castRingHom ℚ)) (AlgebraicClosure ℚ))) p

private noncomputable abbrev rep (W : WeierstrassCurve ℤ) (p : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (ZMod p) (Tors W p) :=
  galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p

private noncomputable def repM (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (b : Module.Basis (Fin 2) (ZMod p) (Tors W p)) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ZMod p) :=
  ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.toMonoidHom).comp (rep W p)

private theorem repM_apply (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (b : Module.Basis (Fin 2) (ZMod p) (Tors W p))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    repM W p b σ = LinearMap.toMatrix b b (rep W p σ) := rfl

private def fixer (p : ℕ) : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  {σ | ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ}

private theorem mem_fixer_iff (p : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ∈ fixer p ↔ ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ := Iff.rfl

private theorem exists_conj_frobenius_pow (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (i : ℕ) (hi : (p - 1) ∣ 2 * i)
    {𝔪 : Ideal HeckeAlg} (h𝔪 : 𝔪 ≠ ⊤) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → W.IsGoodPrimeFor ℓ →
      heckeGen ⟨ℓ, hℓ⟩ - ((ℓ ^ i * W.apOfModel ℓ : ℤ) : HeckeAlg) ∈ 𝔪)
    {S : Finset Nat.Primes}
    (hS : ∀ ℓ : Nat.Primes, ℓ ∉ S → heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1) ∈ 𝔪)
    (b : Module.Basis (Fin 2) (ZMod p) (Tors W p))
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (hL : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → rep W p σ = 1)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ n : ℕ) (C C' M : Matrix (Fin 2) (Fin 2) (ZMod p)),
      repM W p b g = C * M ^ n * C' ∧ C * C' = 1 ∧ C' * C = 1 ∧
      (M - ((ℓ : ZMod p) ^ i) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) *
        (M - ((ℓ : ZMod p) ^ i * ℓ) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) = 0 ∧
      (ℓ : ZMod p) ≠ 0 ∧ ((ℓ : ZMod p) ^ i) ^ 2 = 1 ∧ g ζ = ζ ^ (ℓ ^ n) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζint : IsIntegral ℚ ζ :=
    ⟨X ^ p - C 1, monic_X_pow_sub_C (1 : ℚ) hp.ne_zero, by simp [hζ.pow_eq_one]⟩
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hζint

  obtain ⟨ℓ, hℓ, hℓT, A, τ, γ, n, hA, hτ, hagree⟩ :=
    FrobeniusDensity.exists_frobenius_conj_pow_of_statement
      (fun M _ _ _ => FrobeniusDensity.statement M) (L ⊔ ℚ⟮ζ⟯) g
      (hS₀fin.toFinset ∪ S.image (fun q : Nat.Primes => (q : ℕ)) ∪ {p} ∪ W.Δ.natAbs.primeFactors)
  have hℓS₀ : ℓ ∉ S₀ := fun h => hℓT (by simp [h])
  have hℓS : (⟨ℓ, hℓ⟩ : Nat.Primes) ∉ S := fun h =>
    hℓT (by
      simp only [Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨_, h, rfl⟩)))
  have hℓp : ℓ ≠ p := fun h => hℓT (by simp [h])
  have hgood : W.IsGoodPrimeFor ℓ := by
    intro hdvd
    apply hℓT
    have : ℓ ∈ W.Δ.natAbs.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hℓ, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr hΔ⟩
    simp [this]
  have hℓ0 : (ℓ : ZMod p) ≠ 0 := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp ((ZMod.natCast_eq_zero_iff ℓ p).mp h)).symm

  have hu2 : ((ℓ : ZMod p) ^ i) ^ 2 = 1 := by
    obtain ⟨m, hm⟩ := hi
    rw [← pow_mul, mul_comm i 2, hm, pow_mul, ZMod.pow_card_sub_one_eq_one hℓ0, one_pow]

  have htr : (repM W p b τ).trace = ((W.apOfModel ℓ : ℤ) : ZMod p) := by
    rw [repM_apply, ← LinearMap.trace_eq_matrix_trace (ZMod p) b]
    exact WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel W p ℓ hp hℓ hℓp hgood A hA τ hτ
  have hdet : (repM W p b τ).det = (ℓ : ZMod p) := by
    rw [repM_apply, LinearMap.det_toMatrix]
    exact WeierstrassCurve.det_galoisRep_frobenius_eq_prime W p ℓ hp hℓ hℓp hgood A hA τ hτ
  have hc := pow_mul_apOfModel_eq hp W S₀ i h𝔪 hp𝔪 hcong hS hℓ hℓS₀ hℓS hgood
  have htr' : (repM W p b τ).trace = (ℓ : ZMod p) ^ i + (ℓ : ZMod p) ^ i * ℓ := by
    rw [htr]
    linear_combination ((ℓ : ZMod p) ^ i) * hc - ((W.apOfModel ℓ : ℤ) : ZMod p) * hu2
  have hdet' : (repM W p b τ).det = (ℓ : ZMod p) ^ i * ((ℓ : ZMod p) ^ i * ℓ) := by
    rw [hdet]
    linear_combination (-(ℓ : ZMod p)) * hu2

  have hρg : rep W p g = rep W p (γ * τ ^ n * γ⁻¹) := by
    have hker : rep W p (g⁻¹ * (γ * τ ^ n * γ⁻¹)) = 1 := by
      apply hL
      intro x hx
      have hx' : x ∈ L ⊔ ℚ⟮ζ⟯ := (le_sup_left : L ≤ L ⊔ ℚ⟮ζ⟯) hx
      rw [AlgEquiv.mul_apply, ← hagree x hx', ← AlgEquiv.mul_apply, inv_mul_cancel,
        AlgEquiv.one_apply]
    calc rep W p g = rep W p g * rep W p (g⁻¹ * (γ * τ ^ n * γ⁻¹)) := by rw [hker, mul_one]
      _ = rep W p (γ * τ ^ n * γ⁻¹) := by rw [← map_mul, mul_inv_cancel_left]

  have hτζ : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → ∀ j : ℕ, (τ ^ j) μ = μ ^ (ℓ ^ j) := by
    intro μ hμ j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, AlgEquiv.mul_apply,
        ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow hp hℓ hℓp A hA hτ μ hμ, map_pow, ih,
        ← pow_mul, ← pow_succ]
  have hgζ : g ζ = ζ ^ (ℓ ^ n) := by
    have hζL : ζ ∈ L ⊔ ℚ⟮ζ⟯ :=
      (le_sup_right : ℚ⟮ζ⟯ ≤ L ⊔ ℚ⟮ζ⟯) (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    have h1 : (γ⁻¹ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    rw [hagree ζ hζL, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτζ _ h1 n, map_pow,
      ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  refine ⟨ℓ, n, repM W p b γ, repM W p b γ⁻¹, repM W p b τ, ?_, ?_, ?_,
    sub_mul_sub_eq_zero htr' hdet', hℓ0, hu2, hgζ⟩
  · have e : ∀ x, repM W p b x = (LinearMap.toMatrixAlgEquiv b) (rep W p x) := fun x => rfl
    rw [e g, hρg, ← e, map_mul, map_mul, map_pow]
  · rw [← map_mul, mul_inv_cancel, map_one]
  · rw [← map_mul, inv_mul_cancel, map_one]

private theorem forall_apply_eq_pow_of_apply_primitiveRoot' {p : ℕ} (hp : p.Prime)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {c : ℕ} (hc : σ ζ = ζ ^ c) :
    ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ c := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro μ hμ
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hc, ← pow_mul, ← pow_mul, mul_comm]

end Assembly

end WLightEB

open scoped Matrix in
open Module Submodule WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ModularCurve WLightEB in

theorem solution (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (i : ℕ) (hi : (p - 1) ∣ 2 * i)
    (𝔪 : Ideal HeckeAlg) (h𝔪 : 𝔪 ≠ ⊤) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → W.IsGoodPrimeFor ℓ →
      heckeGen ⟨ℓ, hℓ⟩ - ((ℓ ^ i * W.apOfModel ℓ : ℤ) : HeckeAlg) ∈ 𝔪) :
    ¬ IsEventuallyEisenstein 𝔪 := by
  classical
  rintro ⟨S, hS⟩
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  have hΔQ : (W.map (Int.castRingHom ℚ)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, eq_intCast, Int.cast_ne_zero]
    exact hΔ
  haveI hEll : (W.map (Int.castRingHom ℚ)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔQ⟩
  have hpQ : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcard : Nat.card (Tors W p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := AlgebraicClosure ℚ)
      (W.map (Int.castRingHom ℚ)) hpQ
  haveI : Finite (Tors W p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  have hrank : Module.finrank (ZMod p) (Tors W p) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Tors W p)
    rw [hcard, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) (ZMod p) (Tors W p)) :=
    ⟨Module.finBasisOfFinrankEq _ _ hrank⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  obtain ⟨L, hLfin, hL⟩ :=
    WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel (W.map (Int.castRingHom ℚ)) p
  haveI := hLfin

  have hdens := exists_conj_frobenius_pow p W hΔ S₀ hS₀fin i hi h𝔪 hp𝔪 hcong hS b hζ L hL

  have hKconj : ∀ g, ∀ h ∈ fixer p, g * h * g⁻¹ ∈ fixer p := by
    intro g h hh
    rw [mem_fixer_iff] at hh ⊢
    intro μ hμ
    have h1 : (g⁻¹ μ) ^ p = 1 := by rw [← map_pow, hμ, map_one]
    show (g * h * g⁻¹) μ = μ
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel,
      AlgEquiv.one_apply]
  have hKmul : ∀ h ∈ fixer p, ∀ h' ∈ fixer p, h * h' ∈ fixer p := by
    intro h hh h' hh'
    rw [mem_fixer_iff] at hh hh' ⊢
    intro μ hμ
    show (h * h') μ = μ
    rw [AlgEquiv.mul_apply, hh' μ hμ, hh μ hμ]
  have hpow : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → g μ = μ ^ a := fun g => by
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one
      (show (g ζ) ^ p = 1 by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨a, forall_apply_eq_pow_of_apply_primitiveRoot' hp hζ g ha.symm⟩
  have hcomm : ∀ g g' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      g * g' * g⁻¹ * g'⁻¹ ∈ fixer p := by
    intro g g'
    rw [mem_fixer_iff]
    intro μ hμ
    obtain ⟨a, ha⟩ := hpow g
    obtain ⟨a', ha'⟩ := hpow g'
    have hν : (g⁻¹ (g'⁻¹ μ)) ^ p = 1 := by rw [← map_pow, ← map_pow, hμ, map_one, map_one]
    have key : g (g' (g⁻¹ (g'⁻¹ μ))) = g' (g (g⁻¹ (g'⁻¹ μ))) := by
      rw [ha' _ hν, map_pow, ha _ hν, ← pow_mul, map_pow, ha' _ hν, ← pow_mul, mul_comm]
    show (g * g' * g⁻¹ * g'⁻¹) μ = μ
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, key, ← AlgEquiv.mul_apply g,
      mul_inv_cancel, AlgEquiv.one_apply, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

  have hunip : ∀ h ∈ fixer p, (repM W p b h - 1) * (repM W p b h - 1) = 0 := by
    intro h hh
    rw [mem_fixer_iff] at hh
    obtain ⟨ℓ, n, C, C', M, hM, hCC', hC'C, hfac, hℓ0, hu2, hhζ⟩ := hdens h

    have hℓn : ((ℓ : ZMod p)) ^ n = 1 := by
      have h1 : ζ ^ (ℓ ^ n) = ζ ^ 1 := by rw [pow_one, ← hhζ, hh ζ hζ.pow_eq_one]
      rw [← pow_mod_orderOf ζ (ℓ ^ n), ← pow_mod_orderOf ζ 1, ← hζ.eq_orderOf] at h1
      have hmod : ℓ ^ n ≡ 1 [MOD p] := hζ.pow_inj (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) h1
      have := (ZMod.natCast_eq_natCast_iff (ℓ ^ n) 1 p).mpr hmod
      push_cast at this
      exact this
    have hun : ((ℓ : ZMod p) ^ i) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hℓn, one_pow]
    have hvn : ((ℓ : ZMod p) ^ i * ℓ) ^ n = 1 := by rw [mul_pow, hun, hℓn, one_mul]
    have hN := pow_sub_mul_pow_sub_eq_zero hfac n
    rw [hun, hvn, one_smul] at hN
    rw [hM, ← conj_sub_one hCC', conj_mul_conj hC'C, hN, mul_zero, zero_mul]

  have heig : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ u v : ZMod p, u ≠ 0 ∧
      (repM W p b g - u • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) *
        (repM W p b g - v • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) = 0 := by
    intro g
    obtain ⟨ℓ, n, C, C', M, hM, hCC', hC'C, hfac, hℓ0, hu2, -⟩ := hdens g
    refine ⟨((ℓ : ZMod p) ^ i) ^ n, ((ℓ : ZMod p) ^ i * ℓ) ^ n,
      pow_ne_zero _ (pow_ne_zero _ hℓ0), ?_⟩
    rw [hM, ← conj_sub_smul_one hCC', ← conj_sub_smul_one hCC', conj_mul_conj hC'C,
      pow_sub_mul_pow_sub_eq_zero hfac n, mul_zero, zero_mul]

  obtain ⟨Lm, hLm1, hLm⟩ :=
    exists_line_of_unipotent_on_commutators (repM W p b) (fixer p) hKconj hKmul hcomm hunip heig

  have hfr : Module.finrank (ZMod p)
      (Lm.map (b.equivFun.symm : (Fin 2 → ZMod p) →ₗ[ZMod p] Tors W p)) = 1 := by
    rw [LinearEquiv.finrank_map_eq]
    exact hLm1
  have hstab :
      IsGaloisStable ℚ (Lm.map (b.equivFun.symm : (Fin 2 → ZMod p) →ₗ[ZMod p] Tors W p)) := by
    intro σ x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have key : σ • (b.equivFun.symm w) = b.equivFun.symm (repM W p b σ *ᵥ w) := by
      apply b.equivFun.injective
      have h := LinearMap.toMatrix_mulVec_repr b b (rep W p σ) (b.equivFun.symm w)
      rw [← Basis.equivFun_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at h
      rw [LinearEquiv.apply_symm_apply, repM_apply, h]
      rfl
    show σ • ((b.equivFun.symm : (Fin 2 → ZMod p) →ₗ[ZMod p] Tors W p) w) ∈
      Lm.map (b.equivFun.symm : (Fin 2 → ZMod p) →ₗ[ZMod p] Tors W p)
    rw [LinearEquiv.coe_coe, key]
    exact Submodule.mem_map_of_mem (hLm σ w hw)
  have hirr2 := hirr
  unfold WeierstrassCurve.ModRepIsIrreducible WeierstrassCurve.Affine.Point.GaloisRepIsIrreducible
    at hirr2
  rcases hirr2.2 _ hstab with h | h
  · rw [h, finrank_bot] at hfr
    exact zero_ne_one hfr
  · rw [h, finrank_top, hrank] at hfr
    norm_num at hfr

end S_ModularCurve_not_isEventuallyEisenstein_of_modRepIsIrreducible
end P2MW
export P2MW.S_ModularCurve_not_isEventuallyEisenstein_of_modRepIsIrreducible (solution)
