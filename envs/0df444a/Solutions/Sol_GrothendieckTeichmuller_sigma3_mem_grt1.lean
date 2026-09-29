-- Prove2me | solution 1 for GrothendieckTeichmuller.sigma3_mem_grt1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T18:43:09.617589+00:00
-- url     : https://prove2.me/submissions/c21c81b6-e787-49f1-8f99-929b00671d96

import Definitions.Def_GT_grt1

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open GrothendieckTeichmuller FreeLieAlgebra

namespace Sigma3Aux

/-! ### Relations in the Drinfeld-Kohno Lie algebra `t n` -/

theorem dk_sym {n : ℕ} (i j : Fin n) : dkGen i j = dkGen j i := by
  have h : (of ℚ (i, j) - of ℚ (j, i)) ∈ dkIdeal n :=
    LieSubmodule.subset_lieSpan (Or.inr (Or.inl ⟨i, j, rfl⟩))
  have h0 := (LieSubmodule.Quotient.mk_eq_zero' (N := dkIdeal n)).2 h
  have h1 : (dkGen i j : DrinfeldKohno n) - dkGen j i = 0 := h0
  exact sub_eq_zero.1 h1

theorem dk_loc {n : ℕ} (i j k l : Fin n) (h1 : i ≠ j) (h2 : i ≠ k) (h3 : i ≠ l)
    (h4 : j ≠ k) (h5 : j ≠ l) (h6 : k ≠ l) : ⁅dkGen i j, dkGen k l⁆ = 0 := by
  have h : (⁅of ℚ (i, j), of ℚ (k, l)⁆ : FreeLieAlgebra ℚ (Fin n × Fin n)) ∈ dkIdeal n :=
    LieSubmodule.subset_lieSpan (Or.inr (Or.inr (Or.inl ⟨i, j, k, l, h1, h2, h3, h4, h5, h6, rfl⟩)))
  have h0 := (LieSubmodule.Quotient.mk_eq_zero' (N := dkIdeal n)).2 h
  rw [LieSubmodule.Quotient.mk_bracket] at h0
  exact h0

theorem dk_braid {n : ℕ} (i j k : Fin n) (h1 : i ≠ j) (h2 : i ≠ k) (h3 : j ≠ k) :
    ⁅dkGen i j, dkGen i k + dkGen j k⁆ = 0 := by
  have h : (⁅of ℚ (i, j), of ℚ (i, k) + of ℚ (j, k)⁆ :
      FreeLieAlgebra ℚ (Fin n × Fin n)) ∈ dkIdeal n :=
    LieSubmodule.subset_lieSpan (Or.inr (Or.inr (Or.inr ⟨i, j, k, h1, h2, h3, rfl⟩)))
  have h0 := (LieSubmodule.Quotient.mk_eq_zero' (N := dkIdeal n)).2 h
  have h1 : ⁅dkGen i j, dkGen i k + dkGen j k⁆ = (0 : DrinfeldKohno n) := h0
  exact h1

/-- The braid relation in the form of a rewrite rule. -/
theorem dk_b {n : ℕ} (i j k : Fin n) (h1 : i ≠ j) (h2 : i ≠ k) (h3 : j ≠ k) :
    ⁅dkGen i j, dkGen i k⁆ = -⁅dkGen i j, dkGen j k⁆ := by
  have h := dk_braid i j k h1 h2 h3
  rw [lie_add] at h
  exact add_eq_zero_iff_eq_neg.1 h



/-! ### The six generators of `t₄` -/

/-- `t₁₂`. -/ noncomputable def a12 : DrinfeldKohno 4 := dkGen 0 1
/-- `t₁₃`. -/ noncomputable def a13 : DrinfeldKohno 4 := dkGen 0 2
/-- `t₁₄`. -/ noncomputable def a14 : DrinfeldKohno 4 := dkGen 0 3
/-- `t₂₃`. -/ noncomputable def a23 : DrinfeldKohno 4 := dkGen 1 2
/-- `t₂₄`. -/ noncomputable def a24 : DrinfeldKohno 4 := dkGen 1 3
/-- `t₃₄`. -/ noncomputable def a34 : DrinfeldKohno 4 := dkGen 2 3

theorem L1 : ⁅a12, a34⁆ = 0 := dk_loc 0 1 2 3 (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide)
theorem L2 : ⁅a13, a24⁆ = 0 := dk_loc 0 2 1 3 (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide)
theorem L3 : ⁅a14, a23⁆ = 0 := dk_loc 0 3 1 2 (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide)

theorem Ba : ⁅a12, a13⁆ = -⁅a12, a23⁆ := dk_b 0 1 2 (by decide) (by decide) (by decide)
theorem Bb : ⁅a12, a14⁆ = -⁅a12, a24⁆ := dk_b 0 1 3 (by decide) (by decide) (by decide)
theorem Bc : ⁅a13, a14⁆ = -⁅a13, a34⁆ := dk_b 0 2 3 (by decide) (by decide) (by decide)
theorem Bd : ⁅a23, a24⁆ = -⁅a23, a34⁆ := dk_b 1 2 3 (by decide) (by decide) (by decide)

theorem Be : ⁅a13, a12⁆ = -⁅a13, a23⁆ := by
  have h := dk_b (0 : Fin 4) 2 1 (by decide) (by decide) (by decide)
  rwa [dk_sym 2 1] at h

theorem Bf : ⁅a23, a12⁆ = -⁅a23, a13⁆ := by
  have h := dk_b (1 : Fin 4) 2 0 (by decide) (by decide) (by decide)
  rwa [dk_sym 1 0, dk_sym 2 0] at h

theorem Bg : ⁅a24, a23⁆ = -⁅a24, a34⁆ := by
  have h := dk_b (1 : Fin 4) 3 2 (by decide) (by decide) (by decide)
  rwa [dk_sym 3 2] at h

theorem Bh : ⁅a34, a23⁆ = -⁅a34, a24⁆ := by
  have h := dk_b (2 : Fin 4) 3 1 (by decide) (by decide) (by decide)
  rwa [dk_sym 2 1, dk_sym 3 1] at h

/-! ### The four degree-two elements and the swapped relations -/

/-- `A = ⁅t₁₂, t₂₃⁆`. -/ noncomputable def eA : DrinfeldKohno 4 := ⁅a12, a23⁆
/-- `B = ⁅t₁₂, t₂₄⁆`. -/ noncomputable def eB : DrinfeldKohno 4 := ⁅a12, a24⁆
/-- `C = ⁅t₁₃, t₃₄⁆`. -/ noncomputable def eC : DrinfeldKohno 4 := ⁅a13, a34⁆
/-- `D = ⁅t₂₃, t₃₄⁆`. -/ noncomputable def eD : DrinfeldKohno 4 := ⁅a23, a34⁆

theorem s23_14 : ⁅a23, a14⁆ = 0 := by rw [← lie_skew a23 a14, L3, neg_zero]
theorem s24_13 : ⁅a24, a13⁆ = 0 := by rw [← lie_skew a24 a13, L2, neg_zero]
theorem s34_12 : ⁅a34, a12⁆ = 0 := by rw [← lie_skew a34 a12, L1, neg_zero]

theorem hA1 : ⁅a13, a23⁆ = -eA := by
  have h : ⁅a13, a12⁆ = -⁅a13, a23⁆ := Be
  rw [← lie_skew a13 a12, Ba, neg_neg] at h
  rw [eA, h, neg_neg]

theorem hA1' : eA = -⁅a13, a23⁆ := by rw [hA1, neg_neg]

theorem hA2 : ⁅a13, a12⁆ = eA := by rw [Be, hA1, neg_neg]

theorem h24_23 : ⁅a24, a23⁆ = eD := by rw [← lie_skew a24 a23, Bd, neg_neg]; rfl
theorem h24_34 : ⁅a24, a34⁆ = -eD := by rw [← h24_23, Bg, neg_neg]
theorem h34_23 : ⁅a34, a23⁆ = -eD := by rw [← lie_skew a34 a23, eD]
theorem h34_24 : ⁅a34, a24⁆ = eD := by rw [← neg_inj, ← Bh, h34_23]

/-! ### The four cancellation lemmas -/

theorem lemA : ⁅a23, eC⁆ = -⁅a23, eB⁆ := by
  have hsum : eB + eC = ⁅a14, a12 + a13⁆ := by
    rw [lie_add, ← lie_skew a14 a12, ← lie_skew a14 a13, Bb, Bc, eB, eC]
    abel
  have h23 : ⁅a23, a12 + a13⁆ = 0 := by rw [lie_add, Bf]; abel
  have hz : ⁅a23, eB + eC⁆ = 0 := by
    rw [hsum, leibniz_lie, s23_14, h23, lie_zero, zero_lie, add_zero]
  rw [lie_add, add_comm] at hz
  exact eq_neg_of_add_eq_zero_left hz

theorem lemB : ⁅a13, eD⁆ = -⁅a24, eA⁆ := by
  have h4 : ⁅a24, eA⁆ = -⁅a13, eD⁆ := by
    rw [hA1', lie_neg, leibniz_lie, s24_13, zero_lie, zero_add, h24_23]
  rw [h4, neg_neg]

theorem lemC : ⁅a24, eC⁆ = -⁅a13, eB⁆ := by
  have h1 : ⁅a13, eB⁆ = ⁅a13, eD⁆ := by
    rw [eB, leibniz_lie, L2, lie_zero, add_zero, hA2, ← lie_skew eA a24, lemB]
  have h2 : ⁅a24, eC⁆ = -⁅a13, eD⁆ := by
    rw [eC, leibniz_lie, s24_13, zero_lie, zero_add, h24_34, lie_neg]
  rw [h1, h2]

theorem lemD : ⁅a34, eB⁆ = -⁅a12, eC⁆ := by
  have h1 : ⁅a12, eC⁆ = -⁅a12, eD⁆ := by
    rw [eC, leibniz_lie, L1, lie_zero, add_zero, Ba, ← eA, neg_lie, ← lie_skew eA a34, neg_neg,
      eA, leibniz_lie, s34_12, zero_lie, zero_add, h34_23, lie_neg]
  have h2 : ⁅a34, eB⁆ = ⁅a12, eD⁆ := by
    rw [eB, leibniz_lie, s34_12, zero_lie, zero_add, h34_24]
  rw [h1, h2, neg_neg]

/-! ### The element `σ₃ = ⁅x + y, ⁅x, y⁆⁆` -/

/-- Willwacher's degree-three element of `grt₁`. -/
noncomputable def sig : Lxy := ⁅gx + gy, ⁅gx, gy⁆⁆

theorem subst_sig {A : Type*} [LieRing A] [LieAlgebra ℚ A] (u v : A) :
    substXY u v sig = ⁅u + v, ⁅u, v⁆⁆ := by
  rw [sig, LieHom.map_lie, LieHom.map_lie, map_add, substXY_gx, substXY_gy]

theorem anti : substXY gy gx sig = -sig := by
  rw [subst_sig, sig, add_comm gy gx, ← lie_skew gy gx, lie_neg]

theorem hexa : substXY gx gy sig + substXY gy (-gx - gy) sig
    + substXY (-gx - gy) gx sig = 0 := by
  have hyx : ⁅gy, gx⁆ = -⁅gx, gy⁆ := by rw [← lie_skew gy gx]
  rw [subst_sig, subst_sig, subst_sig]
  simp only [add_lie, lie_add, sub_lie, lie_sub, neg_lie, lie_neg, lie_self, hyx,
    sub_zero, zero_sub, neg_zero, lie_zero, zero_lie, add_zero, zero_add, neg_neg]
  abel

theorem pentagon :
    substXY a12 a23 sig - substXY a12 (a23 + a24) sig
      + substXY (a12 + a13) (a24 + a34) sig
      - substXY (a13 + a23) a34 sig + substXY a23 a34 sig = 0 := by
  have hA' : ⁅a23, ⁅a13, a34⁆⁆ = -⁅a23, ⁅a12, a24⁆⁆ := lemA
  have hB' : ⁅a13, ⁅a23, a34⁆⁆ = -⁅a24, ⁅a12, a23⁆⁆ := lemB
  have hC' : ⁅a24, ⁅a13, a34⁆⁆ = -⁅a13, ⁅a12, a24⁆⁆ := lemC
  have hD' : ⁅a34, ⁅a12, a24⁆⁆ = -⁅a12, ⁅a13, a34⁆⁆ := lemD
  rw [subst_sig, subst_sig, subst_sig, subst_sig, subst_sig]
  simp only [add_lie, lie_add, L1, L2, lie_zero, zero_lie, add_zero, zero_add,
    hA', hB', hC', hD']
  abel

theorem homog : IsHomogeneousOfDegree 3 sig := by
  intro c
  have hin : ⁅c • gx, c • gy⁆ = (c * c) • ⁅gx, gy⁆ := by rw [smul_lie, lie_smul, smul_smul]
  rw [subst_sig, hin, ← smul_add, smul_lie, lie_smul, smul_smul, sig]
  congr 1
  ring

section Nonzero

attribute [local instance 100] LieRing.ofAssociativeRing

/-- `E₁₂`. -/
def MA : Matrix (Fin 4) (Fin 4) ℚ := !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
/-- `E₂₃ + E₃₄`. -/
def MB : Matrix (Fin 4) (Fin 4) ℚ := !![0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0]

theorem sig_ne_zero : sig ≠ 0 := by
  intro h
  have h2 : substXY MA MB sig = 0 := by rw [h, map_zero]
  rw [subst_sig] at h2
  have h3 := congrFun (congrFun h2 0) 3
  simp [Ring.lie_def, MA, MB, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply,
    Matrix.sub_apply] at h3

end Nonzero


theorem sigma3_all : sig ∈ grt1 ∧ sig ≠ 0 ∧ IsHomogeneousOfDegree 3 sig := by
  refine ⟨?_, sig_ne_zero, homog⟩
  rw [mem_grt1_iff]
  exact ⟨anti, hexa, pentagon⟩

end Sigma3Aux

theorem solution :
    ⁅GrothendieckTeichmuller.gx + GrothendieckTeichmuller.gy,
        ⁅GrothendieckTeichmuller.gx, GrothendieckTeichmuller.gy⁆⁆ ∈
        GrothendieckTeichmuller.grt1 ∧
      ⁅GrothendieckTeichmuller.gx + GrothendieckTeichmuller.gy,
        ⁅GrothendieckTeichmuller.gx, GrothendieckTeichmuller.gy⁆⁆ ≠ 0 ∧
      GrothendieckTeichmuller.IsHomogeneousOfDegree 3
        ⁅GrothendieckTeichmuller.gx + GrothendieckTeichmuller.gy,
          ⁅GrothendieckTeichmuller.gx, GrothendieckTeichmuller.gy⁆⁆ :=
  Sigma3Aux.sigma3_all
