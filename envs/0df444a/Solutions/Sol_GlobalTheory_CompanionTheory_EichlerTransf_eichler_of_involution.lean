-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EichlerTransf.eichler_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:33.386486+00:00
-- url     : https://prove2.me/submissions/d69edf7e-b5f6-4c89-bd2c-718d2f4dc997

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe
import Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_mulVec_column
import Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_mulVec_mem_of_columns
import Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_exists_gram_inverse
import Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_eichler_isometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.EichlerTransf
theorem _root_.solution (J : Matrix (Fin n) (Fin n) ℂ) (hJJ : J * J = 1) (hJh : Jᴴ = J)
    (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m))
    (hxx : xᴴ * J * x = 0) (hxy : xᴴ * J * y = 1) :
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * J ∈ Formalism.QuantumDeterminants.UH J ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => y j i)),
        J *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => y j i)) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin m) (Fin m) ℂ,
      P = diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) := ⟨_, rfl⟩
  have hPh : Pᴴ = P := by
    rw [hPdef, diagonal_conjTranspose]
    congr 1
    ext i
    by_cases h : i ∈ A <;> simp [h]
  have hPP : P * P = P := by
    rw [hPdef, diagonal_mul_diagonal]
    congr 1
    ext i
    by_cases h : i ∈ A <;> simp [h]
  have colP : ∀ {r : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) (v : Fin r) (i : Fin m),
      (M * P) v i = M v i * (if i ∈ A then (1 : ℂ) else 0) := by
    intro r M v i
    rw [hPdef, Matrix.mul_diagonal]
  have rowP : ∀ {r : ℕ} (M : Matrix (Fin m) (Fin r) ℂ) (i : Fin m) (v : Fin r),
      (P * M) i v = (if i ∈ A then (1 : ℂ) else 0) * M i v := by
    intro r M i v
    rw [hPdef, Matrix.diagonal_mul]
  obtain ⟨a, ha⟩ : ∃ a, a = x * P := ⟨_, rfl⟩
  have hap : a * P = a := by rw [ha, Matrix.mul_assoc, hPP]
  have haH : aᴴ = P * xᴴ := by rw [ha, conjTranspose_mul, hPh]
  have hPaH : P * aᴴ = aᴴ := by rw [haH, ← Matrix.mul_assoc, hPP]
  have haJa : aᴴ * J * a = 0 := by
    calc aᴴ * J * a = P * (xᴴ * J * x) * P := by rw [haH, ha]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hxx]; simp
  have haJy : aᴴ * J * y = P := by
    calc aᴴ * J * y = P * (xᴴ * J * y) := by rw [haH]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hxy, Matrix.mul_one]
  have hyJx : yᴴ * J * x = 1 := by
    have := congrArg conjTranspose hxy
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hb : (yᴴ * J) * a = P := by rw [ha, ← Matrix.mul_assoc, hyJx, Matrix.one_mul]
  obtain ⟨C, H, hCH, haaC, hCP⟩ := exists_gram_inverse a (yᴴ * J) P hPh hPP hb hap
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, y₂ = J * a * C := ⟨_, rfl⟩
  have hJy₂ : J * y₂ = a * C := by
    rw [hy₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJa : J * a = y₂ * H := by
    rw [hy₂, Matrix.mul_assoc, hCH, Matrix.mul_assoc, hap]
  have hy₂P : y₂ * P = y₂ := by rw [hy₂, Matrix.mul_assoc, hCP]
  have hay₂ : aᴴ * J * y₂ = P := by
    rw [Matrix.mul_assoc, hJy₂, ← Matrix.mul_assoc, haaC]
  obtain ⟨d, hd⟩ : ∃ d, d = y₂ - y * P := ⟨_, rfl⟩
  have had : aᴴ * J * d = 0 := by
    rw [hd, Matrix.mul_sub, hay₂, ← Matrix.mul_assoc, haJy, hPP, sub_self]
  have hdP : d * P = d := by
    rw [hd, Matrix.sub_mul, hy₂P, Matrix.mul_assoc, hPP]
  have hPdH : P * dᴴ = dᴴ := by
    have := congrArg conjTranspose hdP
    rwa [conjTranspose_mul, hPh] at this
  obtain ⟨F, hFdef⟩ : ∃ F, F = (1 / 2 : ℂ) • (dᴴ * J * d) := ⟨_, rfl⟩
  have hEh : (dᴴ * J * d)ᴴ = dᴴ * J * d := by
    simp [conjTranspose_mul, hJh, Matrix.mul_assoc]
  have hF : F + Fᴴ = dᴴ * J * d := by
    rw [hFdef, conjTranspose_smul, hEh]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← add_smul]
    norm_num
  have hPF : P * F = F := by
    rw [hFdef, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPdH]
  obtain ⟨u, hu⟩ : ∃ u, u = -(dᴴ * J) - F * (aᴴ * J) := ⟨_, rfl⟩
  have hPu : P * u = u := by
    rw [hu, Matrix.mul_sub, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPdH, hPF]
  have hua : u * a = 0 := by
    have h3 : dᴴ * J * a = 0 := by
      have := congrArg conjTranspose had
      simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
    rw [hu, Matrix.sub_mul, Matrix.neg_mul, h3, Matrix.mul_assoc F, haJa]
    simp
  have hxu : x * u = a * u := by rw [ha, Matrix.mul_assoc, hPu]
  have hdx : d * xᴴ * J = d * (aᴴ * J) := by
    rw [haH, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hdP]
  have hN : 1 + x * u + d * xᴴ * J = 1 + a * u + d * (aᴴ * J) := by rw [hxu, hdx]
  have hiso := eichler_isometry J a d F hJh haJa had hF
  refine ⟨u, d, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v hi
    rw [← hPu, rowP]
    simp [hi]
  · intro v i hi
    rw [← hdP, colP]
    simp [hi]
  · intro i j hj
    have h0 : (u * a) i j = 0 := by rw [hua]; rfl
    rw [ha, ← Matrix.mul_assoc, colP] at h0
    simpa [hj] using h0
  · rw [hN, hu]
    exact hiso
  · rw [hN]
    obtain ⟨N, hNdef⟩ : ∃ N, N = 1 + a * u + d * (aᴴ * J) := ⟨_, rfl⟩
    rw [← hNdef]
    have hNa : N * a = a := by
      rw [hNdef, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc a, hua,
        Matrix.mul_assoc d, haJa]
      simp
    have hNy : N * (y * P) = y₂ + a * (u * (y * P)) := by
      have e : d * (aᴴ * J) * (y * P) = d := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (aᴴ * J), haJy, hPP, hdP]
      rw [hNdef, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc a, e, hd]
      abel
    have colx : ∀ i : A, (fun j => x j i) = fun j => a j i := by
      intro i
      ext j
      rw [ha, colP]
      simp [i.2]
    have coly : ∀ i : A, (fun j => y j i) = fun j => (y * P) j i := by
      intro i
      ext j
      rw [colP]
      simp [i.2]
    have hgx : ∀ i : A, (N *ᵥ fun j => x j i) = fun j => a j i := by
      intro i
      rw [colx, mulVec_column, hNa]
    have hgy : ∀ i : A, (N *ᵥ fun j => y j i) =
        (fun j => y₂ j i) + a *ᵥ (fun j => (u * (y * P)) j i) := by
      intro i
      rw [coly, mulVec_column, hNy, mulVec_column]
      ext j
      simp
    set G := Submodule.span ℂ (Set.range (fun i : A => N *ᵥ fun j => x j i) ∪
      Set.range (fun i : A => N *ᵥ fun j => y j i)) with hG
    have sub1 : ∀ i : A, (N *ᵥ fun j => x j i) ∈ G :=
      fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    have sub2 : ∀ i : A, (N *ᵥ fun j => y j i) ∈ G :=
      fun i => Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    have haG : ∀ z, a *ᵥ z ∈ G := by
      refine mulVec_mem_of_columns G a (fun i => ?_)
      by_cases h : i ∈ A
      · have := sub1 ⟨i, h⟩
        rwa [hgx] at this
      · have e : (fun j => a j i) = 0 := by
          ext j
          rw [← hap, colP]
          simp [h]
        rw [e]
        exact G.zero_mem
    have hyG : ∀ z, y₂ *ᵥ z ∈ G := by
      refine mulVec_mem_of_columns G y₂ (fun i => ?_)
      by_cases h : i ∈ A
      · have h1 := sub2 ⟨i, h⟩
        rw [hgy] at h1
        have h2 := G.sub_mem h1 (haG (fun j => (u * (y * P)) j i))
        rwa [add_sub_cancel_right] at h2
      · have e : (fun j => y₂ j i) = 0 := by
          ext j
          rw [← hy₂P, colP]
          simp [h]
        rw [e]
        exact G.zero_mem
    have J1 : ∀ z, J *ᵥ (a *ᵥ z) ∈ G := by
      intro z
      rw [Matrix.mulVec_mulVec, hJa, ← Matrix.mulVec_mulVec]
      exact hyG _
    have J2 : ∀ z, J *ᵥ (y₂ *ᵥ z) ∈ G := by
      intro z
      rw [Matrix.mulVec_mulVec, hJy₂, ← Matrix.mulVec_mulVec]
      exact haG _
    have hle : G ≤ G.comap (Matrix.mulVecLin J) := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · change J *ᵥ (N *ᵥ fun j => x j i) ∈ G
        have e : (fun j => a j i) = a *ᵥ (fun j => P j i) := by
          rw [mulVec_column, hap]
        rw [hgx, e]
        exact J1 _
      · change J *ᵥ (N *ᵥ fun j => y j i) ∈ G
        have e : (fun j => y₂ j i) = y₂ *ᵥ (fun j => P j i) := by
          rw [mulVec_column, hy₂P]
        rw [hgy, e, Matrix.mulVec_add]
        exact G.add_mem (J2 _) (J1 _)
    intro v hv
    exact hle hv
end GlobalTheory.CompanionTheory.EichlerTransf
