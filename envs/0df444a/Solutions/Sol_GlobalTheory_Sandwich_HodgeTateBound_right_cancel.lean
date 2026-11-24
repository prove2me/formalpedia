-- Prove2me | solution 1 for GlobalTheory.Sandwich.HodgeTateBound.right_cancel
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T20:28:31.549588+00:00
-- url     : https://prove2.me/submissions/88eb55c0-6f00-4e21-8fce-34279e58b3df

import Mathlib

open Matrix

theorem solution {A : Type} [CommRing A] {h : ℕ} [IsDomain A] {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) {X Y : Matrix (Fin h) (Fin h) A}
    (hX : X * F = Y * F) : X = Y := by
  -- Pass to the fraction field, where μ becomes a unit.
  let K := FractionRing A
  let f : A →+* K := algebraMap A K
  have hf : Function.Injective f := IsFractionRing.injective A K
  have hμ' : f μ ≠ 0 := by
    intro hh
    apply hμ
    exact hf (by simpa using hh)
  -- entrywise image sends μ • 1 to f μ • 1
  have hsmul : (μ • (1 : Matrix (Fin h) (Fin h) A)).map f = f μ • (1 : Matrix (Fin h) (Fin h) K) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs with hij
    · simp
    · simp
  have hGF' : G.map f * F.map f = f μ • (1 : Matrix (Fin h) (Fin h) K) := by
    have := congr_arg (fun M : Matrix (Fin h) (Fin h) A => M.map f) hGF
    simpa [Matrix.map_mul, hsmul] using this
  -- over the field, Dedekind-finiteness turns the left inverse into a right inverse
  have hFG' : F.map f * G.map f = f μ • (1 : Matrix (Fin h) (Fin h) K) := by
    have hinv : (f μ)⁻¹ • G.map f * F.map f = 1 := by
      rw [Matrix.smul_mul, hGF', smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hcomm := mul_eq_one_comm.mp hinv
    calc F.map f * G.map f
        = f μ • (F.map f * ((f μ)⁻¹ • G.map f)) := by
          rw [← Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hμ', one_smul]
      _ = f μ • 1 := by rw [hcomm]
  -- pull F * G = μ • 1 back to A by injectivity
  have hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A) := by
    have hmap : (F * G).map f = (μ • (1 : Matrix (Fin h) (Fin h) A)).map f := by
      rw [Matrix.map_mul, hFG', hsmul]
    ext i j
    apply hf
    have := congr_arg (fun M => M i j) hmap
    simpa [Matrix.map_apply] using this
  -- cancel F on the right
  have h1 : X * (F * G) = Y * (F * G) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hX]
  rw [hFG] at h1
  have h2 : μ • X = μ • Y := by
    simpa [Matrix.mul_smul, Matrix.mul_one] using h1
  exact (smul_right_inj hμ).mp h2