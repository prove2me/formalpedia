-- Prove2me | solution 1 for GlobalTheory.det_saturated_lattice_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:19.224891+00:00
-- url     : https://prove2.me/submissions/75dd6749-8563-4688-afc3-8d8392864dc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralBasisChangeDeterminant
import Theorems.Thm_GlobalTheory_matrix_exists_rightInverse_of_saturated_rows

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution : ∀ (O k V K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] (f : O →+* V) (em : k →+* K), (∀ a, algebraMap V K (f a) = em (algebraMap O k a)) → ∀ (m n : ℕ) (P : Matrix (Fin m) (Fin n) k) (M : Matrix (Fin m) (Fin m) k) (C : Matrix (Fin m) (Fin m) K), (∀ c, Matrix.vecMul c P = 0 → c = 0) → M.det ≠ 0 → (∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M) → (∀ c : Fin m → K, (∃ a : Fin n → V, Matrix.vecMul c (P.map em) = fun j => algebraMap V K (a j)) ↔ ∃ b : Fin m → V, c = Matrix.vecMul (fun i => algebraMap V K (b i)) C) → ∃ u : Vˣ, C.det = algebraMap V K u * em M.det := by
  intro O k V K _ _ _ _ _ _ _ _ _ _ f em hf m n P M C hP hM hO hV
  have iO : Function.Injective (algebraMap O k) := IsFractionRing.injective O k
  have iV : Function.Injective (algebraMap V K) := IsFractionRing.injective V K

  have hN : ∃ N : Matrix (Fin m) (Fin n) O, M * P = N.map (algebraMap O k) := by
    have : ∀ i, ∃ a : Fin n → O, Matrix.vecMul (M i) P = fun j => algebraMap O k (a j) := by
      intro i
      refine (hO _).mpr ⟨Pi.single i 1, ?_⟩
      have : (fun j => algebraMap O k ((Pi.single i 1 : Fin m → O) j)) = Pi.single i 1 := by
        ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
      rw [this, Matrix.single_one_vecMul]; rfl
    choose a ha using this
    refine ⟨Matrix.of a, ?_⟩
    ext i j
    exact congrFun (ha i) j
  obtain ⟨N, hN⟩ := hN
  have hmap : ∀ b : Fin m → O, Matrix.vecMul (Matrix.vecMul (fun i => algebraMap O k (b i)) M) P
      = fun j => algebraMap O k (Matrix.vecMul b N j) := by
    intro b
    rw [Matrix.vecMul_vecMul, hN]
    ext j
    simp [Matrix.vecMul, dotProduct]
  obtain ⟨Q, hQ⟩ := matrix_exists_rightInverse_of_saturated_rows N (by
      intro b hb
      have h1 := hmap b
      rw [hb] at h1
      have h2 := hP _ (h1.trans (by ext j; simp))
      have h3 := Matrix.eq_zero_of_vecMul_eq_zero hM h2
      ext i
      apply iO
      simpa using congrFun h3 i) (by
      intro r x b hr hx
      have hr' : algebraMap O k r ≠ 0 := fun h => hr (iO (by simpa using h))
      obtain ⟨b', hb'⟩ := (hO ((algebraMap O k r)⁻¹ •
        Matrix.vecMul (fun i => algebraMap O k (b i)) M)).mp ⟨x, by
          rw [Matrix.smul_vecMul, hmap, ← hx]
          ext j
          simp only [Pi.smul_apply, smul_eq_mul, map_mul]
          field_simp⟩
      refine ⟨b', ?_⟩
      have h1 := hmap b'
      rw [← hb', Matrix.smul_vecMul, hmap, ← hx] at h1
      ext j
      apply iO
      rw [← congrFun h1 j]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      field_simp)
  have hcomp : (algebraMap V K).comp f = em.comp (algebraMap O k) := RingHom.ext hf
  set M' := M.map em with hM'
  set P' := P.map em with hP'
  set Q' := (Q.map f).map (algebraMap V K) with hQ'
  have hMP : M' * P' = (N.map f).map (algebraMap V K) := by
    rw [hM', hP', ← Matrix.map_mul, hN]
    ext i j
    simp [hf]
  have h1 : M' * (P' * Q') = 1 := by
    rw [← Matrix.mul_assoc, hMP, hQ', ← Matrix.map_mul, ← Matrix.map_mul, hQ]
    simp
  have h2 : (P' * Q') * M' = 1 := mul_eq_one_comm.mp h1
  have hsingle : ∀ i : Fin m, (fun j => algebraMap V K ((Pi.single i 1 : Fin m → V) j)) = Pi.single i 1 := by
    intro i
    ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
  have hU : ∃ U : Matrix (Fin m) (Fin m) V, C = U.map (algebraMap V K) * M' := by
    have : ∀ i, ∃ a : Fin n → V, Matrix.vecMul (C i) P' = fun j => algebraMap V K (a j) := by
      intro i
      refine (hV _).mpr ⟨Pi.single i 1, ?_⟩
      rw [hsingle, Matrix.single_one_vecMul]; rfl
    choose a ha using this
    have hA : C * P' = (Matrix.of a).map (algebraMap V K) := by
      ext i j
      exact congrFun (ha i) j
    refine ⟨Matrix.of a * Q.map f, ?_⟩
    rw [Matrix.map_mul, ← hA, ← hQ', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc P', h2,
      Matrix.mul_one]
  have hU' : ∃ U' : Matrix (Fin m) (Fin m) V, M' = U'.map (algebraMap V K) * C := by
    have : ∀ i, ∃ b : Fin m → V, M' i = Matrix.vecMul (fun i => algebraMap V K (b i)) C := by
      intro i
      refine (hV _).mp ⟨(N.map f) i, ?_⟩
      ext j
      exact congrFun (congrFun hMP i) j
    choose b hb using this
    refine ⟨Matrix.of b, ?_⟩
    ext i j
    exact congrFun (hb i) j
  obtain ⟨U, hU⟩ := hU
  obtain ⟨U', hU'⟩ := hU'
  have hd : M'.det = em M.det := by rw [hM', RingHom.map_det]; rfl
  have hd0 : em M.det ≠ 0 := by simpa using hM
  have e1 : C.det = algebraMap V K U.det * em M.det := by
    rw [hU, Matrix.det_mul, hd, RingHom.map_det (algebraMap V K)]; rfl
  have e2 : em M.det = algebraMap V K U'.det * C.det := by
    have := congrArg Matrix.det hU'
    rw [Matrix.det_mul, hd] at this
    rw [this, RingHom.map_det (algebraMap V K)]; rfl
  have e3 : U.det * U'.det = 1 := by
    apply iV
    rw [map_mul, map_one]
    apply mul_right_cancel₀ hd0
    rw [one_mul]
    conv_rhs => rw [e2, e1]
    ring
  exact ⟨Units.mkOfMulEqOne _ _ e3, e1⟩
end GlobalTheory
