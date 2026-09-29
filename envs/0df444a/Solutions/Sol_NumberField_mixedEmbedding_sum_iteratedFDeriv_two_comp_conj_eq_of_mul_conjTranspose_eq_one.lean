-- Prove2me | solution 1 for NumberField.mixedEmbedding.sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/59fb8be8-d404-5012-814d-a45e5bdc7312

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open NumberField NumberField.mixedEmbedding
open scoped Classical Matrix

namespace R4LapInv

variable (K : Type) [Field K] [NumberField K]

abbrev S : Type := mixedSpace K
abbrev Mat : Type := Matrix (Fin 2) (Fin 2) (mixedSpace K)
abbrev Ent : Type := Fin 2 → Fin 2 → mixedSpace K
abbrev RIdx : Type := {w : InfinitePlace K // w.IsReal}
abbrev CIdx : Type := {w : InfinitePlace K // w.IsComplex}

theorem stdBasis_inl (r : RIdx K) : stdBasis K (Sum.inl r) = (Pi.single r 1, 0) := by
  rw [Module.Basis.apply_eq_iff]
  ext i
  rcases i with r' | ⟨c, k⟩
  · rw [stdBasis_apply_isReal, Finsupp.single_apply]
    simp only [Pi.single_apply, Sum.inl.injEq]
    simp only [eq_comm]
  · fin_cases k
    · change (stdBasis K).repr _ (Sum.inr (c, 0)) = _
      rw [stdBasis_apply_isComplex_fst, Finsupp.single_apply]
      simp
    · change (stdBasis K).repr _ (Sum.inr (c, 1)) = _
      rw [stdBasis_apply_isComplex_snd, Finsupp.single_apply]
      simp

theorem stdBasis_inr_zero (c : CIdx K) : stdBasis K (Sum.inr (c, 0)) = (0, Pi.single c 1) := by
  rw [Module.Basis.apply_eq_iff]
  ext i
  rcases i with r' | ⟨c', k⟩
  · rw [stdBasis_apply_isReal, Finsupp.single_apply]
    simp
  · fin_cases k
    · change (stdBasis K).repr _ (Sum.inr (c', 0)) = _
      rw [stdBasis_apply_isComplex_fst, Finsupp.single_apply]
      simp only [Pi.single_apply, Sum.inr.injEq, Prod.mk.injEq]
      by_cases h : c' = c
      · subst h; simp
      · simp [h, Ne.symm h]
    · change (stdBasis K).repr _ (Sum.inr (c', 1)) = _
      rw [stdBasis_apply_isComplex_snd, Finsupp.single_apply]
      simp only [Pi.single_apply, Sum.inr.injEq, Prod.mk.injEq]
      by_cases h : c' = c
      · subst h; simp
      · simp [h, Ne.symm h]

theorem stdBasis_inr_one (c : CIdx K) : stdBasis K (Sum.inr (c, 1)) = (0, Pi.single c Complex.I) := by
  rw [Module.Basis.apply_eq_iff]
  ext i
  rcases i with r' | ⟨c', k⟩
  · rw [stdBasis_apply_isReal, Finsupp.single_apply]
    simp
  · fin_cases k
    · change (stdBasis K).repr _ (Sum.inr (c', 0)) = _
      rw [stdBasis_apply_isComplex_fst, Finsupp.single_apply]
      simp only [Pi.single_apply, Sum.inr.injEq, Prod.mk.injEq]
      by_cases h : c' = c
      · subst h; simp
      · simp [h, Ne.symm h]
    · change (stdBasis K).repr _ (Sum.inr (c', 1)) = _
      rw [stdBasis_apply_isComplex_snd, Finsupp.single_apply]
      simp only [Pi.single_apply, Sum.inr.injEq, Prod.mk.injEq]
      by_cases h : c' = c
      · subst h; simp
      · simp [h, Ne.symm h]

theorem mul_stdBasis_inl (s : S K) (r : RIdx K) :
    s * stdBasis K (Sum.inl r) = (s.1 r) • stdBasis K (Sum.inl r) := by
  rw [stdBasis_inl]
  refine Prod.ext ?_ ?_
  · funext r'
    simp only [Prod.fst_mul, Pi.mul_apply, Pi.single_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · subst h; ring
    · ring
  · simp

theorem mul_stdBasis_inr_zero (s : S K) (c : CIdx K) :
    s * stdBasis K (Sum.inr (c, 0)) =
      (s.2 c).re • stdBasis K (Sum.inr (c, 0)) + (s.2 c).im • stdBasis K (Sum.inr (c, 1)) := by
  rw [stdBasis_inr_zero, stdBasis_inr_one]
  refine Prod.ext ?_ ?_
  · simp
  · funext c'
    simp only [Prod.snd_mul, Pi.mul_apply, Pi.single_apply, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, Complex.real_smul]
    split_ifs with h
    · subst h
      apply Complex.ext <;> simp
    · simp

theorem mul_stdBasis_inr_one (s : S K) (c : CIdx K) :
    s * stdBasis K (Sum.inr (c, 1)) =
      (-(s.2 c).im) • stdBasis K (Sum.inr (c, 0)) + (s.2 c).re • stdBasis K (Sum.inr (c, 1)) := by
  rw [stdBasis_inr_zero, stdBasis_inr_one]
  refine Prod.ext ?_ ?_
  · simp
  · funext c'
    simp only [Prod.snd_mul, Pi.mul_apply, Pi.single_apply, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, Complex.real_smul]
    split_ifs with h
    · subst h
      apply Complex.ext <;> simp
    · simp

theorem star_mul_fst (s s' : S K) (r : RIdx K) : (star s * s').1 r = s.1 r * s'.1 r := by
  simp only [Prod.fst_mul, Prod.fst_star, Pi.mul_apply, star_trivial]

theorem star_mul_snd_re (s s' : S K) (c : CIdx K) :
    ((star s * s').2 c).re = (s.2 c).re * (s'.2 c).re + (s.2 c).im * (s'.2 c).im := by
  simp only [Prod.snd_mul, Prod.snd_star, Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem star_mul_snd_im (s s' : S K) (c : CIdx K) :
    ((star s * s').2 c).im = (s.2 c).re * (s'.2 c).im - (s.2 c).im * (s'.2 c).re := by
  simp only [Prod.snd_mul, Prod.snd_star, Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem sum_bilin_mul_stdBasis (L : S K →ₗ[ℝ] S K →ₗ[ℝ] ℂ) (s s' : S K) :
    ∑ j : index K, L (s * stdBasis K j) (s' * stdBasis K j) =
      ∑ j : index K, L (stdBasis K j) (star s * s' * stdBasis K j) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_stdBasis_inl, mul_stdBasis_inl, mul_stdBasis_inl, star_mul_fst]
    simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    set t : S K := star s * s' with ht
    have hre := star_mul_snd_re K s s' c
    have him := star_mul_snd_im K s s' c
    rw [← ht] at hre him
    rw [mul_stdBasis_inr_zero, mul_stdBasis_inr_zero, mul_stdBasis_inr_one, mul_stdBasis_inr_one,
      mul_stdBasis_inr_zero K t, mul_stdBasis_inr_one K t, hre, him]
    set b0 := stdBasis K (Sum.inr (c, 0))
    set b1 := stdBasis K (Sum.inr (c, 1))
    simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      smul_add, smul_neg, neg_smul, Complex.real_smul]
    push_cast
    ring

def Eu (r : Fin 2 × Fin 2) : Mat K := Matrix.single r.1 r.2 1

def tU (U : Mat K) (q r : Fin 2 × Fin 2) : S K := U q.1 r.1 * star (U q.2 r.2)

theorem conj_single_apply (U : Mat K) (a b : Fin 2) (x : S K) (c d : Fin 2) :
    (U * Matrix.single a b x * Uᴴ) c d = U c a * star (U d b) * x := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  simp only [Matrix.single_apply]
  fin_cases a <;> fin_cases b <;> simp <;> ring

theorem conj_Eu (U : Mat K) (r : Fin 2 × Fin 2) :
    U * Eu K r * Uᴴ = ∑ q : Fin 2 × Fin 2, tU K U q r • Eu K q := by
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (U * Eu K r * Uᴴ)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Eu, Eu, tU, conj_single_apply, Matrix.smul_single, smul_eq_mul, mul_one]

theorem sum_star_tU_mul_tU (U : Mat K) (hU : U * Uᴴ = 1) (q₁ q₂ : Fin 2 × Fin 2) :
    ∑ r : Fin 2 × Fin 2, star (tU K U q₁ r) * tU K U q₂ r =
      (1 : Mat K) q₂.1 q₁.1 * (1 : Mat K) q₁.2 q₂.2 := by
  have h1 : (1 : Mat K) q₂.1 q₁.1 = ∑ a, U q₂.1 a * star (U q₁.1 a) := by
    rw [← hU, Matrix.mul_apply]
    rfl
  have h2 : (1 : Mat K) q₁.2 q₂.2 = ∑ b, U q₁.2 b * star (U q₂.2 b) := by
    rw [← hU, Matrix.mul_apply]
    rfl
  rw [h1, h2, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [tU, star_mul, star_star]
  ring

def Lq (Bm : Mat K →ₗ[ℝ] Mat K →ₗ[ℝ] ℂ) (M N : Mat K) : S K →ₗ[ℝ] S K →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun x y => Bm (x • M) (y • N))
    (fun x x' y => by simp only [add_smul, map_add, LinearMap.add_apply])
    (fun c x y => by simp only [smul_assoc, map_smul, LinearMap.smul_apply])
    (fun x y y' => by simp only [add_smul, map_add])
    (fun c x y => by simp only [smul_assoc, map_smul])

theorem Lq_apply (Bm : Mat K →ₗ[ℝ] Mat K →ₗ[ℝ] ℂ) (M N : Mat K) (x y : S K) :
    Lq K Bm M N x y = Bm (x • M) (y • N) := rfl

theorem sum_bilin_conj_eq (Bm : Mat K →ₗ[ℝ] Mat K →ₗ[ℝ] ℂ) (U : Mat K) (hU : U * Uᴴ = 1) :
    ∑ p : Fin 2 × Fin 2 × index K,
        Bm (U * Matrix.single p.1 p.2.1 (stdBasis K p.2.2) * Uᴴ) (U * Matrix.single p.1 p.2.1 (stdBasis K p.2.2) * Uᴴ) =
      ∑ p : Fin 2 × Fin 2 × index K,
        Bm (Matrix.single p.1 p.2.1 (stdBasis K p.2.2)) (Matrix.single p.1 p.2.1 (stdBasis K p.2.2)) := by

  have hre : ∀ f : Fin 2 × Fin 2 × index K → ℂ,
      ∑ p : Fin 2 × Fin 2 × index K, f p = ∑ r : Fin 2 × Fin 2, ∑ j : index K, f (r.1, r.2, j) := by
    intro f
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hre, hre]

  have hsingle : ∀ (r : Fin 2 × Fin 2) (j : index K),
      Matrix.single r.1 r.2 (stdBasis K j) = stdBasis K j • Eu K r := by
    intro r j
    rw [Eu, Matrix.smul_single, smul_eq_mul, mul_one]
  have hconj : ∀ (r : Fin 2 × Fin 2) (x : S K),
      U * (x • Eu K r) * Uᴴ = ∑ q : Fin 2 × Fin 2, (tU K U q r * x) • Eu K q := by
    intro r x
    rw [Matrix.mul_smul, Matrix.smul_mul, conj_Eu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul, mul_comm]
  simp only [hsingle, hconj]

  have hexp : ∀ (r : Fin 2 × Fin 2) (x : S K),
      Bm (∑ q : Fin 2 × Fin 2, (tU K U q r * x) • Eu K q) (∑ q : Fin 2 × Fin 2, (tU K U q r * x) • Eu K q) =
        ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2), Lq K Bm (Eu K q.1) (Eu K q.2) (tU K U q.1 r * x) (tU K U q.2 r * x) := by
    intro r x
    rw [LinearMap.map_sum₂ Bm,
      Fintype.sum_prod_type (f := fun q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
        Lq K Bm (Eu K q.1) (Eu K q.2) (tU K U q.1 r * x) (tU K U q.2 r * x))]
    refine Finset.sum_congr rfl fun q₁ _ => ?_
    rw [map_sum]
    rfl
  simp only [hexp]

  calc ∑ r : Fin 2 × Fin 2, ∑ j : index K, ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
          Lq K Bm (Eu K q.1) (Eu K q.2) (tU K U q.1 r * stdBasis K j) (tU K U q.2 r * stdBasis K j)
      = ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2), ∑ r : Fin 2 × Fin 2, ∑ j : index K,
          Lq K Bm (Eu K q.1) (Eu K q.2) (tU K U q.1 r * stdBasis K j) (tU K U q.2 r * stdBasis K j) := by
        have hsw : ∀ r : Fin 2 × Fin 2,
            ∑ j : index K, ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
                Lq K Bm (Eu K q.1) (Eu K q.2) (tU K U q.1 r * stdBasis K j) (tU K U q.2 r * stdBasis K j) =
              ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2), ∑ j : index K,
                Lq K Bm (Eu K q.1) (Eu K q.2) (tU K U q.1 r * stdBasis K j) (tU K U q.2 r * stdBasis K j) :=
          fun r => Finset.sum_comm
        simp only [hsw]
        exact Finset.sum_comm
    _ = ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2), ∑ r : Fin 2 × Fin 2, ∑ j : index K,
          Lq K Bm (Eu K q.1) (Eu K q.2) (stdBasis K j) (star (tU K U q.1 r) * tU K U q.2 r * stdBasis K j) := by
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
        exact sum_bilin_mul_stdBasis K _ _ _
    _ = ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2), ∑ j : index K,
          Lq K Bm (Eu K q.1) (Eu K q.2) (stdBasis K j)
            ((∑ r : Fin 2 × Fin 2, star (tU K U q.1 r) * tU K U q.2 r) * stdBasis K j) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul, map_sum]
    _ = ∑ q : (Fin 2 × Fin 2) × (Fin 2 × Fin 2), ∑ j : index K,
          Lq K Bm (Eu K q.1) (Eu K q.2) (stdBasis K j)
            (((1 : Mat K) q.2.1 q.1.1 * (1 : Mat K) q.1.2 q.2.2) * stdBasis K j) := by
        simp only [sum_star_tU_mul_tU K U hU]
    _ = ∑ q₁ : Fin 2 × Fin 2, ∑ j : index K, Lq K Bm (Eu K q₁) (Eu K q₁) (stdBasis K j) (stdBasis K j) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun q₁ _ => ?_
        rw [Finset.sum_eq_single q₁]
        · simp only [Matrix.one_apply_eq, mul_one, one_mul]
        · intro q₂ _ hne
          have h0 : (1 : Mat K) q₂.1 q₁.1 * (1 : Mat K) q₁.2 q₂.2 = 0 := by
            by_cases h1 : q₂.1 = q₁.1
            · have h2 : q₁.2 ≠ q₂.2 := fun h2 => hne (Prod.ext h1 h2.symm)
              rw [Matrix.one_apply_ne h2, mul_zero]
            · rw [Matrix.one_apply_ne h1, zero_mul]
          simp only [h0, zero_mul, map_zero, Finset.sum_const_zero]
        · intro h; exact absurd (Finset.mem_univ q₁) h
    _ = ∑ r : Fin 2 × Fin 2, ∑ j : index K, Bm (stdBasis K j • Eu K r) (stdBasis K j • Eu K r) := by
        rfl

def conjCLM (U : Mat K) : Ent K →L[ℝ] Ent K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Matrix.of.symm (U * Matrix.of X * Uᴴ)
      map_add' := fun X X' => by
        change Matrix.of.symm (U * (Matrix.of X + Matrix.of X') * Uᴴ) = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c X => by
        change Matrix.of.symm (U * (c • Matrix.of X) * Uᴴ) = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }

theorem conjCLM_apply (U : Mat K) (X : Ent K) : conjCLM K U X = Matrix.of.symm (U * Matrix.of X * Uᴴ) := rfl

def mulL (Z : Mat K) : Mat K →L[ℝ] Ent K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => Matrix.of.symm (Z * u)
      map_add' := fun u v => by rw [Matrix.mul_add]; rfl
      map_smul' := fun c u => by rw [Matrix.mul_smul]; rfl }

theorem mulL_apply (Z u : Mat K) : mulL K Z u = Matrix.of.symm (Z * u) := rfl

theorem main (U : Mat K) (hU : U * Uᴴ = 1) (F : Ent K → ℂ) (hF : ContDiff ℝ 2 F) (E : Ent K) :
    ∑ p : Fin 2 × Fin 2 × index K,
        iteratedFDeriv ℝ 2 (fun X : Ent K => F (Matrix.of.symm (U * Matrix.of X * Uᴴ))) E
          (fun _ => Matrix.of.symm (Matrix.of E * Matrix.single p.1 p.2.1 (stdBasis K p.2.2))) =
      ∑ p : Fin 2 × Fin 2 × index K,
        iteratedFDeriv ℝ 2 F (Matrix.of.symm (U * Matrix.of E * Uᴴ))
          (fun _ => Matrix.of.symm
            (Matrix.of (Matrix.of.symm (U * Matrix.of E * Uᴴ)) *
              Matrix.single p.1 p.2.1 (stdBasis K p.2.2))) := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  set Z : Mat K := U * Matrix.of E * Uᴴ with hZ

  have hcomp : (fun X : Ent K => F (Matrix.of.symm (U * Matrix.of X * Uᴴ))) = F ∘ ⇑(conjCLM K U) := rfl
  have h2 : ((2 : ℕ) : WithTop ℕ∞) ≤ 2 := le_rfl
  have hchain : ∀ v : Fin 2 → Ent K,
      iteratedFDeriv ℝ 2 (fun X : Ent K => F (Matrix.of.symm (U * Matrix.of X * Uᴴ))) E v =
        iteratedFDeriv ℝ 2 F (Matrix.of.symm Z) (fun i => conjCLM K U (v i)) := by
    intro v
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (conjCLM K U) hF E h2,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rfl

  have hcv : ∀ Y : Mat K, conjCLM K U (Matrix.of.symm (Matrix.of E * Y)) = Matrix.of.symm (Z * (U * Y * Uᴴ)) := by
    intro Y
    rw [conjCLM_apply, Equiv.apply_symm_apply, hZ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U (Y * Uᴴ), hU', Matrix.one_mul]

  set D2 := fderiv ℝ (fderiv ℝ F) (Matrix.of.symm Z) with hD2
  let Bm : Mat K →ₗ[ℝ] Mat K →ₗ[ℝ] ℂ :=
    LinearMap.mk₂ ℝ (fun u v => D2 (mulL K Z u) (mulL K Z v))
      (fun u u' v => by simp only [map_add, ContinuousLinearMap.add_apply])
      (fun c u v => by simp only [map_smul, ContinuousLinearMap.smul_apply])
      (fun u v v' => by simp only [map_add])
      (fun c u v => by simp only [map_smul])
  have hBm : ∀ u v : Mat K, Bm u v = D2 (Matrix.of.symm (Z * u)) (Matrix.of.symm (Z * v)) := fun u v => rfl
  have hL : ∀ p : Fin 2 × Fin 2 × index K,
      iteratedFDeriv ℝ 2 (fun X : Ent K => F (Matrix.of.symm (U * Matrix.of X * Uᴴ))) E
          (fun _ => Matrix.of.symm (Matrix.of E * Matrix.single p.1 p.2.1 (stdBasis K p.2.2))) =
        Bm (U * Matrix.single p.1 p.2.1 (stdBasis K p.2.2) * Uᴴ)
          (U * Matrix.single p.1 p.2.1 (stdBasis K p.2.2) * Uᴴ) := by
    intro p
    rw [hchain, iteratedFDeriv_two_apply, hBm]
    simp only [hcv]
    rfl
  have hR : ∀ p : Fin 2 × Fin 2 × index K,
      iteratedFDeriv ℝ 2 F (Matrix.of.symm Z)
          (fun _ => Matrix.of.symm
            (Matrix.of (Matrix.of.symm Z) * Matrix.single p.1 p.2.1 (stdBasis K p.2.2))) =
        Bm (Matrix.single p.1 p.2.1 (stdBasis K p.2.2)) (Matrix.single p.1 p.2.1 (stdBasis K p.2.2)) := by
    intro p
    rw [iteratedFDeriv_two_apply, hBm, Equiv.apply_symm_apply]
  simp only [hL, hR]
  exact sum_bilin_conj_eq K Bm U hU

end R4LapInv

end

open NumberField

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (U : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (hU : U * U.conjTranspose = 1)
    (F : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (hF : ContDiff ℝ 2 F)
    (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :
    ∑ p : Fin 2 × Fin 2 × mixedEmbedding.index K,
        iteratedFDeriv ℝ 2
          (fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
            F (Matrix.of.symm (U * Matrix.of X * U.conjTranspose))) E
          (fun _ => Matrix.of.symm
            (Matrix.of E * Matrix.single p.1 p.2.1 (mixedEmbedding.stdBasis K p.2.2))) =
      ∑ p : Fin 2 × Fin 2 × mixedEmbedding.index K,
        iteratedFDeriv ℝ 2 F (Matrix.of.symm (U * Matrix.of E * U.conjTranspose))
          (fun _ => Matrix.of.symm
            (Matrix.of (Matrix.of.symm (U * Matrix.of E * U.conjTranspose)) *
              Matrix.single p.1 p.2.1 (mixedEmbedding.stdBasis K p.2.2))) :=
  R4LapInv.main K U hU F hF E

end S_NumberField_mixedEmbedding_sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one
end P2MW
export P2MW.S_NumberField_mixedEmbedding_sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one (solution)
