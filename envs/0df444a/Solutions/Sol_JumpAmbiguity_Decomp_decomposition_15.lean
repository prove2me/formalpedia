-- Prove2me | solution 1 for JumpAmbiguity.Decomp.decomposition_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:36:06.328126+00:00
-- url     : https://prove2.me/submissions/14a9b403-9828-49ca-8d32-4f7879f1e1d6

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model

namespace JumpAmbiguity.Decomp
open Matrix

lemma ker_J_trivial {m n : ℕ} (M : Market m n) (hS : M.Standing) (w : Fin n → ℝ)
    (hw : M.J *ᵥ w = 0) : w = 0 := by
  obtain ⟨_, _, hrank, _⟩ := hS
  have h1 := LinearMap.finrank_range_add_finrank_ker M.J.mulVecLin
  have h2 : Module.finrank ℝ (LinearMap.ker M.J.mulVecLin) = 0 := by
    have : M.J.rank = Module.finrank ℝ (LinearMap.range M.J.mulVecLin) := rfl
    simp at h1
    omega
  have h3 := Submodule.finrank_eq_zero.mp h2
  have : w ∈ LinearMap.ker M.J.mulVecLin := by simpa using hw
  rw [h3] at this
  simpa using this

lemma G_isUnit {m n : ℕ} (M : Market m n) (hS : M.Standing) :
    IsUnit (M.Jhat.transpose * M.Jhat).det := by
  have hSig : IsUnit M.Sig.det := hS.2.1
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ w, (M.Jhat.transpose * M.Jhat) *ᵥ w = 0 → w = 0 := by
    intro w hw
    have h1 : (M.Jhat *ᵥ w) ⬝ᵥ (M.Jhat *ᵥ w) = 0 := by
      have := congrArg (dotProduct w) hw
      rwa [← mulVec_mulVec, dotProduct_mulVec, dotProduct_zero, vecMul_transpose] at this
    have h2 : M.Jhat *ᵥ w = 0 := dotProduct_self_eq_zero.mp h1
    have h3 : M.J *ᵥ w = 0 := by
      have : M.Sig *ᵥ (M.Jhat *ᵥ w) = M.J *ᵥ w := by
        simp only [Market.Jhat, mulVec_mulVec, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hSig, Matrix.one_mul]
      rw [← this, h2, mulVec_zero]
    exact ker_J_trivial M hS w h3
  intro x y hxy
  have := key (x - y) (by rw [mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp this

lemma K_eq {m n : ℕ} (M : Market m n) : M.K = LinearMap.range M.Jhat.mulVecLin := by
  rw [Matrix.range_mulVecLin]; rfl

lemma memK_iff {m n : ℕ} (M : Market m n) (x : Fin m → ℝ) :
    x ∈ M.K ↔ ∃ w, x = M.Jhat *ᵥ w := by
  rw [K_eq]; simp [eq_comm]

lemma orth_of {m n : ℕ} (M : Market m n) (u : Fin m → ℝ)
    (hu : M.Jhat.transpose *ᵥ u = 0) : M.IsOrthogonalToK u := by
  intro x hx
  obtain ⟨w, rfl⟩ := (memK_iff M x).mp hx
  rw [dotProduct_mulVec, ← mulVec_transpose, hu, zero_dotProduct]

lemma orth_sub {m n : ℕ} (M : Market m n) {u v : Fin m → ℝ}
    (hu : M.IsOrthogonalToK u) (hv : M.IsOrthogonalToK v) : M.IsOrthogonalToK (u - v) := by
  intro x hx; rw [sub_dotProduct, hu x hx, hv x hx, sub_zero]

lemma proj_mem {m n : ℕ} (M : Market m n) (v : Fin m → ℝ) : M.proj v ∈ M.K :=
  (memK_iff M _).mpr ⟨_, rfl⟩

lemma proj_orth {m n : ℕ} (M : Market m n) (hS : M.Standing) (v : Fin m → ℝ) :
    M.IsOrthogonalToK (v - M.proj v) := by
  apply orth_of
  have hG := G_isUnit M hS
  rw [mulVec_sub, Market.proj, mulVec_mulVec, mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hG, one_mulVec, sub_self]

lemma eq_zero_of_mem_orth {m n : ℕ} (M : Market m n) {x : Fin m → ℝ}
    (hx : x ∈ M.K) (ho : M.IsOrthogonalToK x) : x = 0 :=
  dotProduct_self_eq_zero.mp (ho x hx)

lemma proj_unique {m n : ℕ} (M : Market m n) (hS : M.Standing) (x y : Fin m → ℝ)
    (hx : x ∈ M.K) (hy : M.IsOrthogonalToK y) : M.proj (x + y) = x := by
  have h1 : M.proj (x + y) - x ∈ M.K := M.K.sub_mem (proj_mem M _) hx
  have h2 : M.IsOrthogonalToK (M.proj (x + y) - x) := by
    have := orth_sub M hy (proj_orth M hS (x + y))
    convert this using 1; abel
  exact sub_eq_zero.mp (eq_zero_of_mem_orth M h1 h2)

theorem decomposition_15_aux {m n : ℕ} (M : Market m n) (hS : M.Standing) :
    IsUnit (M.Jhat.transpose * M.Jhat).det ∧
    ∀ v : Fin m → ℝ,
      M.proj v ∈ M.K ∧ M.IsOrthogonalToK (v - M.proj v) ∧
      v = M.proj v + (v - M.proj v) ∧
      ∀ x y : Fin m → ℝ,
        x ∈ M.K → M.IsOrthogonalToK y → v = x + y →
          x = M.proj v ∧ y = v - M.proj v := by
  refine ⟨G_isUnit M hS, fun v => ⟨proj_mem M v, proj_orth M hS v, by abel, ?_⟩⟩
  intro x y hx hy hv
  have := proj_unique M hS x y hx hy
  rw [← hv] at this
  subst hv
  refine ⟨this.symm, ?_⟩
  rw [this]; abel

lemma dot_self_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma Jhatcol_mem {m n : ℕ} (M : Market m n) (k : Fin n) : M.Jhatcol k ∈ M.K :=
  Submodule.subset_span ⟨k, rfl⟩

lemma Jhatcol_eq {m n : ℕ} (M : Market m n) (k : Fin n) :
    M.Jhatcol k = M.Sig⁻¹ *ᵥ M.col k := by
  ext i; simp [Market.Jhatcol, Market.Jhat, Market.col, Matrix.mul_apply, mulVec, dotProduct]

lemma pihat_dot_Jhatcol {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (π : Fin m → ℝ) (k : Fin n) : M.pihat π ⬝ᵥ M.Jhatcol k = π ⬝ᵥ M.col k := by
  have hSig : IsUnit M.Sig.det := hS.2.1
  rw [Jhatcol_eq, dotProduct_mulVec, Market.pihat, mulVec_transpose, vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hSig, vecMul_one]

lemma piperp_orth {m n : ℕ} (M : Market m n) (hS : M.Standing) (π : Fin m → ℝ) :
    M.IsOrthogonalToK (M.piperp π) := proj_orth M hS _

theorem jump_exposure {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (π : Fin m → ℝ) (k : Fin n) :
    π ⬝ᵥ M.col k = M.pibar π ⬝ᵥ M.Jhatcol k := by
  have h := piperp_orth M hS π (M.Jhatcol k) (Jhatcol_mem M k)
  rw [Market.piperp, sub_dotProduct, pihat_dot_Jhatcol M hS] at h
  linarith

lemma muperp_orth {m n : ℕ} (M : Market m n) (hS : M.Standing) :
    M.IsOrthogonalToK M.muperp := proj_orth M hS _

lemma diffusion_gap {m n : ℕ} (M : Market m n) (hγ : 0 < M.γ) (x : Fin m → ℝ) :
    M.diffusionObj ((1 / M.γ) • M.muperp) - M.diffusionObj x =
      (M.γ / 2) * ((x - (1 / M.γ) • M.muperp) ⬝ᵥ (x - (1 / M.γ) • M.muperp)) := by
  simp only [Market.diffusionObj, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm M.muperp x]
  field_simp
  ring

theorem diffusion_A9 {m n : ℕ} (M : Market m n) (hS : M.Standing) :
    M.IsOrthogonalToK ((1 / M.γ) • M.muperp) ∧
    ∀ x : Fin m → ℝ, M.IsOrthogonalToK x →
      M.diffusionObj x ≤ M.diffusionObj ((1 / M.γ) • M.muperp) ∧
      (M.diffusionObj x = M.diffusionObj ((1 / M.γ) • M.muperp) →
        x = (1 / M.γ) • M.muperp) := by
  obtain ⟨-, -, -, -, -, -, -, hγ, -, -⟩ := id hS
  refine ⟨?_, fun x _ => ⟨?_, fun heq => ?_⟩⟩
  · intro y hy
    rw [smul_dotProduct, muperp_orth M hS y hy, smul_zero]
  · have := diffusion_gap M hγ x
    have := dot_self_nonneg (x - (1 / M.γ) • M.muperp)
    nlinarith
  · have h1 := diffusion_gap M hγ x
    rw [heq, sub_self] at h1
    have h2 : (x - (1 / M.γ) • M.muperp) ⬝ᵥ (x - (1 / M.γ) • M.muperp) = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · linarith
      · exact h
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h2)

end JumpAmbiguity.Decomp

open JumpAmbiguity.Decomp

theorem solution {m n : ℕ} (M : Market m n) (hS : M.Standing) :
    IsUnit (M.Jhat.transpose * M.Jhat).det ∧
    ∀ v : Fin m → ℝ,
      M.proj v ∈ M.K ∧ M.IsOrthogonalToK (v - M.proj v) ∧
      v = M.proj v + (v - M.proj v) ∧
      ∀ x y : Fin m → ℝ,
        x ∈ M.K → M.IsOrthogonalToK y → v = x + y →
          x = M.proj v ∧ y = v - M.proj v :=
  JumpAmbiguity.Decomp.decomposition_15_aux M hS
