-- Prove2me | solution 1 for NewMinimalStandardModel.exists_massless_neutrino
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T16:12:25.758019+00:00
-- url     : https://prove2.me/submissions/a7cb8aed-3e83-4666-a06c-91b95be17a16

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

set_option autoImplicit false

open Matrix in
theorem f6832cf0_ker (B : Matrix (Fin 2) (Fin 3) ℂ) : ∃ u : Fin 3 → ℂ, u ≠ 0 ∧ B *ᵥ u = 0 := by
  have h : LinearMap.ker (Matrix.mulVecLin B) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨u, hu, hne⟩ := (Submodule.ne_bot_iff _).mp h
  exact ⟨u, hne, by simpa using hu⟩

open Matrix in
theorem f6832cf0_det (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ) :
    (NewMinimalStandardModel.neutralLeptonMassMatrix v hν M).det = 0 := by
  obtain ⟨u, hu, hBu⟩ := f6832cf0_ker (NewMinimalStandardModel.diracMass v hν)
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨Sum.elim u 0, ?_, ?_⟩
  · intro h
    apply hu
    funext i
    have := congrFun h (Sum.inl i)
    simpa using this
  · unfold NewMinimalStandardModel.neutralLeptonMassMatrix
    rw [Matrix.fromBlocks_mulVec]
    simp [hBu]

open Matrix in
theorem f6832cf0_det2 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (h : A.det = 0) :
    ∃ i, NewMinimalStandardModel.majoranaMasses A i = 0 := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have hd : (Aᴴ * A).det = 0 := by rw [Matrix.det_mul, h, mul_zero]
  rw [hH.det_eq_prod_eigenvalues, Finset.prod_eq_zero_iff] at hd
  obtain ⟨i, -, hi⟩ := hd
  refine ⟨i, ?_⟩
  unfold NewMinimalStandardModel.majoranaMasses
  have : hH.eigenvalues i = 0 := by simpa using hi
  rw [this, Real.sqrt_zero]

open NewMinimalStandardModel in
theorem solution (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ)
    (hM : ∀ α, 0 < M α) :
    ∃ i, majoranaMasses (neutralLeptonMassMatrix v hν M) i = 0 := by
  exact f6832cf0_det2 _ (f6832cf0_det v hν M)
