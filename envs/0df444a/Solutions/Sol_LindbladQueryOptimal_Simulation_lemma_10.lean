-- Prove2me | solution 1 for LindbladQueryOptimal.Simulation.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T07:16:17.466973+00:00
-- url     : https://prove2.me/submissions/ed876eb3-4a74-4bc9-a9bd-dce2fb820038

import Definitions.Def_LindbladQueryOptimal_Simulation_Local
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator
namespace LindbladQueryOptimal.Simulation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rot_abs {a b X : Type} (s t : ℝ) [Fintype a] [Fintype b] [Fintype X]
    [DecidableEq a] [DecidableEq b] [DecidableEq X]
    (A : Matrix X a ℂ) (B : Matrix X b ℂ) (hs : s ^2 + t ^2 = 1)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) (hAB : Aᴴ * B = 0) :
    (Matrix.fromBlocks
    (Matrix.fromBlocks ((s : ℂ) • (1 : Matrix a a ℂ)) 0 0 0)
    (Matrix.fromRows ((-Complex.I * (t : ℂ)) • Aᴴ) (-Complex.I • Bᴴ))
    (Matrix.fromCols ((t : ℂ) • A) B)
    (Complex.I • ((s : ℂ) • (A * Aᴴ) + 1 - (A * Aᴴ) - (B * Bᴴ))) : Matrix (Sum (Sum a b) X) (Sum (Sum a b) X) ℂ)ᴴ *
    (Matrix.fromBlocks
    (Matrix.fromBlocks ((s : ℂ) • (1 : Matrix a a ℂ)) 0 0 0)
    (Matrix.fromRows ((-Complex.I * (t : ℂ)) • Aᴴ) (-Complex.I • Bᴴ))
    (Matrix.fromCols ((t : ℂ) • A) B)
    (Complex.I • ((s : ℂ) • (A * Aᴴ) + 1 - (A * Aᴴ) - (B * Bᴴ))) : Matrix (Sum (Sum a b) X) (Sum (Sum a b) X) ℂ) = 1 := by
  have hBA : Bᴴ * A = 0 := by
    have := congrArg Matrix.conjTranspose hAB
    simpa using this
  have e1 : ∀ (P : Matrix a X ℂ) (Q : Matrix b X ℂ) (c : ℂ), (Matrix.fromBlocks (c • (1 : Matrix a a ℂ)) 0 0 0 : Matrix (Sum a b) (Sum a b) ℂ) * Matrix.fromRows P Q = Matrix.fromRows (c • P) 0 := by
    intro P Q c
    ext i j
    rcases i with i | i
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks]
  have e2 : ∀ (P : Matrix X a ℂ) (Q : Matrix X b ℂ) (c : ℂ), Matrix.fromCols P Q * (Matrix.fromBlocks (c • (1 : Matrix a a ℂ)) 0 0 0 : Matrix (Sum a b) (Sum a b) ℂ) = Matrix.fromCols (c • P) 0 := by
    intro P Q c
    ext i j
    rcases j with j | j
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply, mul_comm]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks]
  have hP00 : (A * Aᴴ) * (A * Aᴴ) = A * Aᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Matrix.one_mul]
  have hP11 : (B * Bᴴ) * (B * Bᴴ) = B * Bᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, hB, Matrix.one_mul]
  have hP01 : (A * Aᴴ) * (B * Bᴴ) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hAB]; simp
  have hP10 : (B * Bᴴ) * (A * Aᴴ) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, hBA]; simp
  have hQ : (1 - A * Aᴴ - B * Bᴴ) * (1 - A * Aᴴ - B * Bᴴ) = 1 - A * Aᴴ - B * Bᴴ := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hP00, hP11, hP01, hP10]; abel
  have hPQ : (A * Aᴴ) * (1 - A * Aᴴ - B * Bᴴ) = 0 := by
    simp only [mul_sub, Matrix.mul_one, hP00, hP01]; abel
  have hQP : (1 - A * Aᴴ - B * Bᴴ) * (A * Aᴴ) = 0 := by
    simp only [sub_mul, Matrix.one_mul, hP00, hP10]; abel
  have hDD : (((s:ℂ) • (A * Aᴴ) + 1 - A * Aᴴ - B * Bᴴ) * ((s:ℂ) • (A * Aᴴ) + 1 - A * Aᴴ - B * Bᴴ)) = ((s:ℂ)^2) • (A * Aᴴ) + (1 - A * Aᴴ - B * Bᴴ) := by
    have h1 : ((s:ℂ) • (A * Aᴴ) + 1 - A * Aᴴ - B * Bᴴ) = (s:ℂ) • (A * Aᴴ) + (1 - A * Aᴴ - B * Bᴴ) := by abel
    rw [h1]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, add_mul, mul_add, hP00, hQ, hPQ, hQP, smul_zero, add_zero, zero_add, pow_two]
  have hAD : Aᴴ * ((s:ℂ) • (A * Aᴴ) + 1 - A * Aᴴ - B * Bᴴ) = (s:ℂ) • Aᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hAB]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul]; abel
  have hBD : Bᴴ * ((s:ℂ) • (A * Aᴴ) + 1 - A * Aᴴ - B * Bᴴ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, hBA, ← Matrix.mul_assoc, hB]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, smul_zero]; abel
  have hDA : ((s:ℂ) • (A * Aᴴ) + 1 - A * Aᴴ - B * Bᴴ) * A = (s:ℂ) • A := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_assoc, hBA]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero]; abel
  have hDB : ((s:ℂ) • (A * Aᴴ) + 1 - A * Aᴴ - B * Bᴴ) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hAB, Matrix.mul_assoc, hB]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero]; abel
  have hst : (s:ℂ)^2 + (t:ℂ)^2 = 1 := by exact_mod_cast hs
  rw [Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose, Matrix.fromRows_mul, Matrix.mul_fromCols, Matrix.fromBlocks_conjTranspose, e1, e2]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I, smul_mul_assoc, mul_smul_comm, hA, hB, hAB, hBA, hAD, hBD, hDA, hDB, hDD, map_mul, map_neg, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, mul_assoc]
  ext i j
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply]
  · split_ifs
    · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]; norm_cast; nlinarith [hs]
    · simp
  · ring
  · ring
  · have h2 : (Complex.I * ((t:ℂ) * (Complex.I * (t:ℂ)))) = -((t:ℂ)^2) := by
      have := Complex.I_mul_I
      linear_combination ((t:ℂ)^2) * this
    rw [h2]
    have h3 : (s:ℂ)^2 = 1 - (t:ℂ)^2 := by linear_combination hst
    rw [h3]; ring

theorem inj0_inj0 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    (inj0 : Matrix (Sum a b) a ℂ)ᴴ * (inj0 : Matrix (Sum a b) a ℂ) = 1 := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, inj0, Matrix.one_apply, Matrix.conjTranspose_apply, eq_comm]

theorem inj1_inj1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    (inj1 : Matrix (Sum a b) b ℂ)ᴴ * (inj1 : Matrix (Sum a b) b ℂ) = 1 := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, inj1, Matrix.one_apply, Matrix.conjTranspose_apply, eq_comm]

theorem inj0_inj1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    (inj0 : Matrix (Sum a b) a ℂ)ᴴ * (inj1 : Matrix (Sum a b) b ℂ) = 0 := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, inj0, inj1, Matrix.conjTranspose_apply]

theorem rotation_unitary {a b e : Type} [Fintype a] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq b] [DecidableEq e]
    (Bin : Matrix e a ℂ) (Bout : Matrix e b ℂ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hin : Binᴴ * Bin = 1) (hout : Boutᴴ * Bout = 1) :
    unitary (rotation Bin Bout δ) := by
  have hs : Real.sqrt (1-δ) ^ 2 + Real.sqrt δ ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt h0]; ring
  have hV0 : V0 Bin = (inj0 : Matrix (Sum e e) e ℂ) * Bin := rfl
  have hV1 : V1 Bout = (inj1 : Matrix (Sum e e) e ℂ) * Bout := rfl
  have h00 : (V0 Bin)ᴴ * V0 Bin = 1 := by
    rw [hV0]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (inj0ᴴ : Matrix e _ ℂ) , inj0_inj0, Matrix.one_mul, hin]
  have h11 : (V1 Bout)ᴴ * V1 Bout = 1 := by
    rw [hV1]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (inj1ᴴ : Matrix e _ ℂ) , inj1_inj1, Matrix.one_mul, hout]
  have h01 : (V0 Bin)ᴴ * V1 Bout = 0 := by
    rw [hV0, hV1]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (inj0ᴴ : Matrix e _ ℂ) , inj0_inj1, Matrix.zero_mul, Matrix.mul_zero]
  have key := rot_abs (Real.sqrt (1-δ)) (Real.sqrt δ) (V0 Bin) (V1 Bout) hs h00 h11 h01
  refine ⟨key, ?_⟩
  exact mul_eq_one_comm.mp key


theorem padding_isometry (n a : ℕ) (ha : n ≤ a) : (padding n a)ᴴ * padding n a = 1 := by
  ext y y'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  set x0 : Bits a := fun j => if h : j.val < a - n then false else y ⟨j.val - (a - n), by omega⟩ with hx0
  have hx0y : ∀ y : Bits n, (padding n a) (fun j : Fin a => if h : j.val < a - n then false else y ⟨j.val - (a - n), by omega⟩) y = 1 := by
    intro y
    simp only [padding]
    rw [if_pos]
    constructor
    · intro i hi; simp [hi]
    · intro i j hj
      have : ¬ j.val < a - n := by omega
      simp only [this, dite_false]
      congr 1; ext; simp; omega
  have hu : ∀ (y : Bits n) (x : Bits a), padding n a x y = 1 → x = (fun j : Fin a => if h : j.val < a - n then false else y ⟨j.val - (a - n), by omega⟩) := by
    intro y x hx
    simp only [padding] at hx
    split_ifs at hx with hc
    · obtain ⟨h1, h2⟩ := hc
      funext j
      by_cases hj : j.val < a - n
      · simp [hj, h1 j hj]
      · simp only [hj, dite_false]
        have := h2 ⟨j.val - (a - n), by omega⟩ j (by simp; omega)
        rw [← this]
    · simp at hx
  have h01 : ∀ x y, padding n a x y = 1 ∨ padding n a x y = 0 := by
    intro x y; simp only [padding]; split_ifs <;> simp
  set cx : Bits n → Bits a := fun y j => if h : j.val < a - n then false else y ⟨j.val - (a - n), by omega⟩ with hcx
  have hinj : ∀ y y', cx y = cx y' → y = y' := by
    intro y y' h
    funext i
    have := congrFun h ⟨a - n + i.val, by omega⟩
    simpa [hcx] using this
  have hz : ∀ y x, x ≠ cx y → padding n a x y = 0 := by
    intro y x hx
    rcases h01 x y with h | h
    · exact absurd (hu y x h) hx
    · exact h
  rw [Finset.sum_eq_single (cx y)]
  · by_cases hyy : y = y'
    · subst hyy; have h1 : padding n a (cx y) y = 1 := hx0y y
      rw [h1]; simp
    · rw [if_neg hyy]
      by_cases h' : padding n a (cx y) y' = 1
      · exact absurd (hinj _ _ (hu y' _ h').symm).symm hyy
      · rcases h01 (cx y) y' with h | h
        · exact absurd h h'
        · simp [h]
  · intro x _ hx
    simp [hz y x hx]
  · intro h; exact absurd (Finset.mem_univ _) h


end LindbladQueryOptimal.Simulation

open LindbladQueryOptimal.Simulation in
theorem solution (n a : ℕ) (ha : n ≤ a) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) :
    unitary (rotation (padding n a) (padding n a) δ) :=
  LindbladQueryOptimal.Simulation.rotation_unitary _ _ δ hδ (by linarith)
    (LindbladQueryOptimal.Simulation.padding_isometry n a ha)
    (LindbladQueryOptimal.Simulation.padding_isometry n a ha)
