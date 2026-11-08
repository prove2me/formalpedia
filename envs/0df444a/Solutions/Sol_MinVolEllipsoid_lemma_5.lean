-- Prove2me | solution 1 for MinVolEllipsoid.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:47:45.603036+00:00
-- url     : https://prove2.me/submissions/c2006474-58ec-4e9f-8e17-0f294c899bac

import Mathlib
import Definitions.Def_MinVolEllipsoid_GenCopositive
import Definitions.Def_EJASpectral_RootDet_LHSCB

open Matrix

open MinVolEllipsoid in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (A : Matrix κ ι ℝ) (C : Set (ι → ℝ))
    (hC : EJASpectral.RootDet.IsProperCone C) :
    GenCopositive C (M - Aᵀ * A) ↔
      ∃ H : Matrix ι ι ℝ, H.PosSemidef ∧ GenCopositive C (M - H) ∧
        (fromBlocks H Aᵀ A (1 : Matrix κ κ ℝ)).PosSemidef := by
  haveI : Invertible (1 : Matrix κ κ ℝ) := invertibleOne
  have hA : (Aᵀ)ᴴ = A := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
  have key : ∀ H : Matrix ι ι ℝ,
      (fromBlocks H Aᵀ A (1 : Matrix κ κ ℝ)).PosSemidef ↔ (H - Aᵀ * A).PosSemidef := by
    intro H
    have := Matrix.PosDef.fromBlocks₂₂ H Aᵀ (Matrix.PosDef.one (n := κ) (R := ℝ))
    rw [hA, inv_one, Matrix.mul_one] at this
    exact this
  constructor
  · intro h
    refine ⟨Aᵀ * A, ?_, h, ?_⟩
    · have := posSemidef_conjTranspose_mul_self A
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    · rw [key, sub_self]
      exact PosSemidef.zero
  · rintro ⟨H, _, ⟨hsym, hcop⟩, hblk⟩
    have hpsd := (key H).mp hblk
    have hsymA : (Aᵀ * A).IsSymm := by
      unfold Matrix.IsSymm; rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    refine ⟨hM.sub hsymA, fun v hv => ?_⟩
    have e : M - Aᵀ * A = (M - H) + (H - Aᵀ * A) := by abel
    rw [e, add_mulVec, dotProduct_add]
    have h1 := hcop v hv
    have h2 := hpsd.dotProduct_mulVec_nonneg v
    rw [star_trivial] at h2
    linarith
