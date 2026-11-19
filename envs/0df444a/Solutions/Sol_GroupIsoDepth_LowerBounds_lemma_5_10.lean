-- Prove2me | solution 1 for GroupIsoDepth.LowerBounds.lemma_5_10
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-18T15:39:24.527463+00:00
-- url     : https://prove2.me/submissions/01e697b2-fbb6-46f7-ad2d-9a37cabeb869

import Mathlib

open Matrix

set_option maxHeartbeats 1200000

private lemma rank_block {F : Type*} [Field F] (k r : ℕ)
    (A : GL (Fin r) F) (B : Matrix (Fin r) (Fin (k - r)) F)
    (D : Matrix (Fin (k - r)) (Fin r) F) :
    (fromBlocks (A : Matrix (Fin r) (Fin r) F) B D
      (D * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B)).rank = r := by
  classical
  set E : Matrix (Fin (k - r)) (Fin r) F :=
    D * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) with hE
  have hM : fromBlocks (A : Matrix (Fin r) (Fin r) F) B D
        (D * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B) =
      fromRows (1 : Matrix (Fin r) (Fin r) F) E * fromCols (A : Matrix (Fin r) (Fin r) F) B := by
    rw [fromRows_mul_fromCols]
    simp [hE, Matrix.mul_assoc]
  have hupper : (fromBlocks (A : Matrix (Fin r) (Fin r) F) B D
        (D * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B)).rank ≤ r := by
    rw [hM]
    calc (fromRows (1 : Matrix (Fin r) (Fin r) F) E *
          fromCols (A : Matrix (Fin r) (Fin r) F) B).rank
        ≤ (fromRows (1 : Matrix (Fin r) (Fin r) F) E).rank := rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r) := rank_le_card_width _
      _ = r := Fintype.card_fin r
  have hlower : r ≤ (fromBlocks (A : Matrix (Fin r) (Fin r) F) B D
        (D * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B)).rank := by
    have hsub : (fromBlocks (A : Matrix (Fin r) (Fin r) F) B D
          (D * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B)).submatrix
          (Sum.inl : Fin r → Fin r ⊕ Fin (k - r)) Sum.inl =
        (A : Matrix (Fin r) (Fin r) F) := by
      ext i j
      simp [fromBlocks]
    calc r = (A : Matrix (Fin r) (Fin r) F).rank := by
          rw [Matrix.rank_unit]
          simp
      _ = ((fromBlocks (A : Matrix (Fin r) (Fin r) F) B D
          (D * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B)).submatrix
          (Sum.inl : Fin r → Fin r ⊕ Fin (k - r)) Sum.inl).rank := by rw [hsub]
      _ ≤ _ := rank_submatrix_le _ _ _
  exact le_antisymm hupper hlower

private lemma card_GL_lower {F : Type*} [Field F] [Fintype F] (r : ℕ) :
    Fintype.card F ^ (r * (r - 1)) ≤ Nat.card (GL (Fin r) F) := by
  classical
  set q := Fintype.card F with hq
  have hq1 : 0 < q := Fintype.card_pos
  have hq2 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := F)
    omega
  by_cases hr : r = 0
  · subst r
    simp [Matrix.card_GL_field]
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    rw [Matrix.card_GL_field]
    calc q ^ (r * (r - 1)) = ∏ _i : Fin r, q ^ (r - 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← pow_mul, Nat.mul_comm]
      _ ≤ ∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) := by
          apply Finset.prod_le_prod
          · intro i _
            positivity
          · intro i _
            have hile : (i : ℕ) ≤ r - 1 := by
              have := i.isLt
              omega
            have h1 : q ^ (i : ℕ) ≤ q ^ (r - 1) :=
              Nat.pow_le_pow_right (by omega) hile
            have h2 : q ^ (r - 1) + q ^ (i : ℕ) ≤ q ^ r := by
              have h3 : q ^ (r - 1) + q ^ (r - 1) ≤ q ^ r := by
                have h4 : q ^ r = q * q ^ (r - 1) := by
                  conv_lhs => rw [← Nat.sub_add_cancel hr1]
                  rw [pow_succ]
                  ring
                rw [h4]
                calc q ^ (r - 1) + q ^ (r - 1) = 2 * q ^ (r - 1) := by ring
                  _ ≤ q * q ^ (r - 1) := Nat.mul_le_mul_right _ hq2
              omega
            omega

private lemma matrix_card {F : Type*} [Field F] [Fintype F] (m n : ℕ) :
    Nat.card (Matrix (Fin m) (Fin n) F) = Fintype.card F ^ (m * n) := by
  classical
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Fin m → Fin n → F) = Fintype.card F ^ (m * n)
  rw [Fintype.card_fun, Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

theorem solution {F : Type*} [Field F] [Fintype F] (k r : ℕ) (hr : r ≤ k) :
    (Fintype.card F : ℝ) ^ ((r : ℤ) * (2 * k - r) - 2 * k) ≤
      (Nat.card {M : Matrix (Fin k) (Fin k) F // M.rank = r} : ℝ) := by
  classical
  set q : ℕ := Fintype.card F with hq
  have hq1 : 0 < q := Fintype.card_pos
  have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  by_cases hr0 : r = 0
  · subst r
    haveI hne : Nonempty {M : Matrix (Fin k) (Fin k) F // M.rank = 0} :=
      ⟨⟨0, Matrix.rank_zero⟩⟩
    have hpos : (1 : ℝ) ≤ (Nat.card {M : Matrix (Fin k) (Fin k) F // M.rank = 0} : ℝ) := by
      have h1 : 1 ≤ Nat.card {M : Matrix (Fin k) (Fin k) F // M.rank = 0} :=
        Nat.succ_le_of_lt Nat.card_pos
      exact_mod_cast h1
    have hle : (q : ℝ) ^ (-(2 * (k : ℤ))) ≤ 1 := by
      have := zpow_le_one_of_nonpos₀ hq1' (show -(2 * (k : ℤ)) ≤ 0 by omega)
      simpa using this
    calc (Fintype.card F : ℝ) ^ ((0 : ℤ) * (2 * k - 0) - 2 * k)
        = (q : ℝ) ^ (-(2 * (k : ℤ))) := by
          congr 1
          omega
      _ ≤ 1 := hle
      _ ≤ _ := hpos
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    let β := Fin r ⊕ Fin (k - r)
    let ek : β ≃ Fin k :=
      finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hr))
    let Dom := GL (Fin r) F × Matrix (Fin r) (Fin (k - r)) F × Matrix (Fin (k - r)) (Fin r) F
    let Φ : Dom → {M : Matrix (Fin k) (Fin k) F // M.rank = r} :=
      fun p => ⟨(Matrix.reindex ek ek)
        (fromBlocks (p.1 : Matrix (Fin r) (Fin r) F) p.2.1 p.2.2
          (p.2.2 * ((p.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * p.2.1)),
        by
          rw [Matrix.rank_reindex]
          exact rank_block k r p.1 p.2.1 p.2.2⟩
    have hΦinj : Function.Injective Φ := by
      rintro ⟨A, B, D⟩ ⟨A', B', D'⟩ h
      have hval : (fromBlocks (A : Matrix (Fin r) (Fin r) F) B D
            (D * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B)) =
          fromBlocks (A' : Matrix (Fin r) (Fin r) F) B' D'
            (D' * ((A'⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * B') := by
        apply (Matrix.reindex ek ek).injective
        exact Subtype.ext_iff.mp h
      have hA : A = A' := by
        apply Units.ext
        have hthis := congrArg (fun M => M.submatrix
          (Sum.inl : Fin r → Fin r ⊕ Fin (k - r)) Sum.inl) hval
        ext i j
        simpa [fromBlocks] using congrFun (congrFun hthis i) j
      have hB : B = B' := by
        have hthis := congrArg (fun M => M.submatrix
          (Sum.inl : Fin r → Fin r ⊕ Fin (k - r)) Sum.inr) hval
        ext i j
        simpa [fromBlocks] using congrFun (congrFun hthis i) j
      have hD : D = D' := by
        have hthis := congrArg (fun M => M.submatrix
          (Sum.inr : Fin (k - r) → Fin r ⊕ Fin (k - r)) Sum.inl) hval
        ext i j
        simpa [fromBlocks] using congrFun (congrFun hthis i) j
      simp [hA, hB, hD]
    have hle : Nat.card Dom ≤ Nat.card {M : Matrix (Fin k) (Fin k) F // M.rank = r} :=
      Nat.card_le_card_of_injective Φ hΦinj
    have hGL : q ^ (r * (r - 1)) ≤ Nat.card (GL (Fin r) F) := by
      simpa [hq] using card_GL_lower (F := F) r
    have hcard : Nat.card Dom =
        Nat.card (GL (Fin r) F) * q ^ (r * (k - r)) * q ^ ((k - r) * r) := by
      dsimp only [Dom]
      rw [Nat.card_prod, Nat.card_prod, matrix_card, matrix_card]
      ring
    have hdom : q ^ (r * (r - 1) + r * (k - r) + (k - r) * r) ≤ Nat.card Dom := by
      rw [hcard]
      calc q ^ (r * (r - 1) + r * (k - r) + (k - r) * r)
          = q ^ (r * (r - 1)) * q ^ (r * (k - r)) * q ^ ((k - r) * r) := by
            rw [← pow_add, ← pow_add]
        _ ≤ Nat.card (GL (Fin r) F) * q ^ (r * (k - r)) * q ^ ((k - r) * r) := by
            exact Nat.mul_le_mul (Nat.mul_le_mul hGL le_rfl) le_rfl
    have hexp : (r : ℤ) * (2 * k - r) - 2 * k ≤
        ((r * (r - 1) + r * (k - r) + (k - r) * r : ℕ) : ℤ) := by
      have hcast1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
        rw [Nat.cast_sub hr1]
        norm_num
      have hcast2 : ((k - r : ℕ) : ℤ) = (k : ℤ) - (r : ℤ) := by
        rw [Nat.cast_sub hr]
      have hrk : (r : ℤ) ≤ 2 * (k : ℤ) := by
        have : (r : ℤ) ≤ (k : ℤ) := by exact_mod_cast hr
        linarith
      push_cast
      rw [hcast1, hcast2]
      nlinarith
    have hz : (q : ℝ) ^ ((r : ℤ) * (2 * k - r) - 2 * k) ≤
        (q : ℝ) ^ (((r * (r - 1) + r * (k - r) + (k - r) * r : ℕ)) : ℤ) :=
      zpow_le_zpow_right₀ hq1' hexp
    have hdomR : (q : ℝ) ^ (((r * (r - 1) + r * (k - r) + (k - r) * r : ℕ)) : ℤ) ≤
        (Nat.card Dom : ℝ) := by
      have := hdom
      push_cast [zpow_natCast]
      exact_mod_cast this
    have hleR : (Nat.card Dom : ℝ) ≤
        (Nat.card {M : Matrix (Fin k) (Fin k) F // M.rank = r} : ℝ) := by
      exact_mod_cast hle
    calc (Fintype.card F : ℝ) ^ ((r : ℤ) * (2 * k - r) - 2 * k)
        = (q : ℝ) ^ ((r : ℤ) * (2 * k - r) - 2 * k) := by rw [hq]
      _ ≤ (q : ℝ) ^ (((r * (r - 1) + r * (k - r) + (k - r) * r : ℕ)) : ℤ) := hz
      _ ≤ (Nat.card Dom : ℝ) := hdomR
      _ ≤ _ := hleR
