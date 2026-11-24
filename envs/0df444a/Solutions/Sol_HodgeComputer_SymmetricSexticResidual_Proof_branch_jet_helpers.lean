-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.branch_jet_helpers
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T10:32:51.270491+00:00
-- url     : https://prove2.me/submissions/c655f2fe-0f2f-4e7b-a070-1cc4fc03d0c2

import Definitions.Def_HodgeComputerSSR_BranchHelpers

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators LaurentSeries PowerSeries

lemma numM_ValLead_of {k1 : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {a0 b0 ξS0 ξQ0 a2_0 a1_0 a0_0 b2_0 b1_0 b0_0 : K5}
    (ha : ValLead 0 a_s a0) (hb : ValLead 0 b_s b0)
    (hξS : ValLead 0 ξS_s ξS0) (hξQ : ValLead 0 ξQ_s ξQ0)
    (ha2 : ValLead k1 (q1_a2 a_s b_s U V) a2_0)
    (ha1 : ValLead k1 (q1_a1 a_s b_s ξS_s ξQ_s U V) a1_0)
    (ha0 : ValLead k1 (q1_a0 ξS_s ξQ_s U V) a0_0)
    (hb2 : ValLead k1 (q2_b2 a_s b_s U V) b2_0)
    (hb1 : ValLead k1 (q2_b1 a_s b_s ξS_s ξQ_s U V) b1_0)
    (hb0 : ValLead k1 (q2_b0 ξS_s ξQ_s U V) b0_0) (mi : Fin 10) :
    ValLead (2 * k1) (numM mi a_s b_s ξS_s ξQ_s U V)
      (let (c2, c1, c0) : K5 × K5 × K5 := match mi with
        | 0 => (a0 ^ 2, 2 * a0 * ξS0, ξS0 ^ 2)
        | 1 => (a0 * b0, a0 * ξQ0 + b0 * ξS0, ξS0 * ξQ0)
        | 2 => (b0 ^ 2, 2 * b0 * ξQ0, ξQ0 ^ 2)
        | 3 => (a0, ξS0, 0)
        | 4 => (0, a0, ξS0)
        | 5 => (b0, ξQ0, 0)
        | 6 => (0, b0, ξQ0)
        | 7 => (1, 0, 0)
        | 8 => (0, 1, 0)
        | 9 => (0, 0, 1)
       (1 / 16 : K5) * (c2 * (a1_0 * b0_0 - a0_0 * b1_0) -
         c1 * (a2_0 * b0_0 - a0_0 * b2_0) + c0 * (a2_0 * b1_0 - a1_0 * b2_0))) := by
  have hd20 := ((ha2.mul hb0).sub (ha0.mul hb2)).eq_k (k' := 2 * k1) (by omega)
  have hd21 := ((ha2.mul hb1).sub (ha1.mul hb2)).eq_k (k' := 2 * k1) (by omega)
  have hd10 := ((ha1.mul hb0).sub (ha0.mul hb1)).eq_k (k' := 2 * k1) (by omega)
  have hc16 : ValLead 0 (1 / 16 : LaurentSeries K5) (1 / 16 : K5) := by
    rw [show (1 / 16 : LaurentSeries K5) = HahnSeries.C (1 / 16 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    exact ValLead.of_C _
  have hcomb {m2 m1 m0 : LaurentSeries K5} {c2 c1 c0 : K5}
      (hm2 : ValLead 0 m2 c2) (hm1 : ValLead 0 m1 c1) (hm0 : ValLead 0 m0 c0) :
      ValLead (2 * k1) ((1 / 16 : LaurentSeries K5) * (m2 * (q1_a1 a_s b_s ξS_s ξQ_s U V * q2_b0 ξS_s ξQ_s U V -
        q1_a0 ξS_s ξQ_s U V * q2_b1 a_s b_s ξS_s ξQ_s U V) -
        m1 * (q1_a2 a_s b_s U V * q2_b0 ξS_s ξQ_s U V - q1_a0 ξS_s ξQ_s U V * q2_b2 a_s b_s U V) +
        m0 * (q1_a2 a_s b_s U V * q2_b1 a_s b_s ξS_s ξQ_s U V - q1_a1 a_s b_s ξS_s ξQ_s U V * q2_b2 a_s b_s U V)))
        ((1 / 16 : K5) * (c2 * (a1_0 * b0_0 - a0_0 * b1_0) -
          c1 * (a2_0 * b0_0 - a0_0 * b2_0) + c0 * (a2_0 * b1_0 - a1_0 * b2_0))) :=
    (hc16.mul ((((hm2.mul hd10).eq_k (k' := 2 * k1) (by omega)).sub
      ((hm1.mul hd20).eq_k (k' := 2 * k1) (by omega))).add
      ((hm0.mul hd21).eq_k (k' := 2 * k1) (by omega)))).eq_k (k' := 2 * k1) (by omega)
  have h0L : ValLead 0 (0 : LaurentSeries K5) (0 : K5) := by simpa only [map_zero] using ValLead.of_C (0 : K5)
  have h1L : ValLead 0 (1 : LaurentSeries K5) (1 : K5) := by simpa only [map_one] using ValLead.of_C (1 : K5)
  have h2L : ValLead 0 (2 : LaurentSeries K5) (2 : K5) := by simpa only [one_add_one_eq_two] using h1L.add h1L
  fin_cases mi
  · dsimp only [numM]; exact hcomb ((ha.pow 2).eq_k (k' := 0) (by omega)) (((h2L.mul ha).mul hξS).eq_k (k' := 0) (by omega)) ((hξS.pow 2).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ((ha.mul hb).eq_k (k' := 0) (by omega)) (((ha.mul hξQ).eq_k (k' := 0) (by omega)).add ((hb.mul hξS).eq_k (k' := 0) (by omega))) ((hξS.mul hξQ).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ((hb.pow 2).eq_k (k' := 0) (by omega)) (((h2L.mul hb).mul hξQ).eq_k (k' := 0) (by omega)) ((hξQ.pow 2).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ha hξS h0L
  · dsimp only [numM]; exact hcomb h0L ha hξS
  · dsimp only [numM]; exact hcomb hb hξQ h0L
  · dsimp only [numM]; exact hcomb h0L hb hξQ
  · dsimp only [numM]; exact hcomb h1L h0L h0L
  · dsimp only [numM]; exact hcomb h0L h1L h0L
  · dsimp only [numM]; exact hcomb h0L h0L h1L

/-- Generic `ValDual` transport for the 10 quadratic line-section numerators `numM mi`
with opaque series arguments (avoids unfolding transparent `set` bindings during `isDefEq`). -/
lemma numM_ValDual_of {k1 : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {aD bD ξSD ξQD a2D a1D a0D b2D b1D b0D : Dual K5}
    (ha : ValDual 0 a_s aD) (hb : ValDual 0 b_s bD)
    (hξS : ValDual 0 ξS_s ξSD) (hξQ : ValDual 0 ξQ_s ξQD)
    (ha2 : ValDual k1 (q1_a2 a_s b_s U V) a2D)
    (ha1 : ValDual k1 (q1_a1 a_s b_s ξS_s ξQ_s U V) a1D)
    (ha0 : ValDual k1 (q1_a0 ξS_s ξQ_s U V) a0D)
    (hb2 : ValDual k1 (q2_b2 a_s b_s U V) b2D)
    (hb1 : ValDual k1 (q2_b1 a_s b_s ξS_s ξQ_s U V) b1D)
    (hb0 : ValDual k1 (q2_b0 ξS_s ξQ_s U V) b0D) (mi : Fin 10) :
    ValDual (2 * k1) (numM mi a_s b_s ξS_s ξQ_s U V)
      (let (c2, c1, c0) : Dual K5 × Dual K5 × Dual K5 := match mi with
        | 0 => (aD ^ 2, 2 * aD * ξSD, ξSD ^ 2)
        | 1 => (aD * bD, aD * ξQD + bD * ξSD, ξSD * ξQD)
        | 2 => (bD ^ 2, 2 * bD * ξQD, ξQD ^ 2)
        | 3 => (aD, ξSD, 0)
        | 4 => (0, aD, ξSD)
        | 5 => (bD, ξQD, 0)
        | 6 => (0, bD, ξQD)
        | 7 => (1, 0, 0)
        | 8 => (0, 1, 0)
        | 9 => (0, 0, 1)
       Dual.C (1 / 16 : K5) * (c2 * (a1D * b0D - a0D * b1D) -
         c1 * (a2D * b0D - a0D * b2D) + c0 * (a2D * b1D - a1D * b2D))) := by
  have hd20 := ((ha2.mul hb0).sub (ha0.mul hb2)).eq_k (k' := 2 * k1) (by omega)
  have hd21 := ((ha2.mul hb1).sub (ha1.mul hb2)).eq_k (k' := 2 * k1) (by omega)
  have hd10 := ((ha1.mul hb0).sub (ha0.mul hb1)).eq_k (k' := 2 * k1) (by omega)
  have hc16 : ValDual 0 (1 / 16 : LaurentSeries K5) (Dual.C (1 / 16 : K5)) := by
    rw [show (1 / 16 : LaurentSeries K5) = HahnSeries.C (1 / 16 : K5) by simp only [map_div₀, map_ofNat, map_one]]
    exact ValDual.of_C _
  have hcomb {m2 m1 m0 : LaurentSeries K5} {c2 c1 c0 : Dual K5}
      (hm2 : ValDual 0 m2 c2) (hm1 : ValDual 0 m1 c1) (hm0 : ValDual 0 m0 c0) :
      ValDual (2 * k1) ((1 / 16 : LaurentSeries K5) * (m2 * (q1_a1 a_s b_s ξS_s ξQ_s U V * q2_b0 ξS_s ξQ_s U V -
        q1_a0 ξS_s ξQ_s U V * q2_b1 a_s b_s ξS_s ξQ_s U V) -
        m1 * (q1_a2 a_s b_s U V * q2_b0 ξS_s ξQ_s U V - q1_a0 ξS_s ξQ_s U V * q2_b2 a_s b_s U V) +
        m0 * (q1_a2 a_s b_s U V * q2_b1 a_s b_s ξS_s ξQ_s U V - q1_a1 a_s b_s ξS_s ξQ_s U V * q2_b2 a_s b_s U V)))
        (Dual.C (1 / 16 : K5) * (c2 * (a1D * b0D - a0D * b1D) -
          c1 * (a2D * b0D - a0D * b2D) + c0 * (a2D * b1D - a1D * b2D))) :=
    (hc16.mul ((((hm2.mul hd10).eq_k (k' := 2 * k1) (by omega)).sub
      ((hm1.mul hd20).eq_k (k' := 2 * k1) (by omega))).add
      ((hm0.mul hd21).eq_k (k' := 2 * k1) (by omega)))).eq_k (k' := 2 * k1) (by omega)
  have h0D : ValDual 0 (0 : LaurentSeries K5) (0 : Dual K5) := by simpa only [map_zero] using ValDual.of_C (0 : K5)
  have h1D : ValDual 0 (1 : LaurentSeries K5) (1 : Dual K5) := by simpa only [map_one] using ValDual.of_C (1 : K5)
  have h2D : ValDual 0 (2 : LaurentSeries K5) (2 : Dual K5) := by simpa only [one_add_one_eq_two] using h1D.add h1D
  fin_cases mi
  · dsimp only [numM]; exact hcomb ((ha.pow 2).eq_k (k' := 0) (by omega)) (((h2D.mul ha).mul hξS).eq_k (k' := 0) (by omega)) ((hξS.pow 2).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ((ha.mul hb).eq_k (k' := 0) (by omega)) (((ha.mul hξQ).eq_k (k' := 0) (by omega)).add ((hb.mul hξS).eq_k (k' := 0) (by omega))) ((hξS.mul hξQ).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ((hb.pow 2).eq_k (k' := 0) (by omega)) (((h2D.mul hb).mul hξQ).eq_k (k' := 0) (by omega)) ((hξQ.pow 2).eq_k (k' := 0) (by omega))
  · dsimp only [numM]; exact hcomb ha hξS h0D
  · dsimp only [numM]; exact hcomb h0D ha hξS
  · dsimp only [numM]; exact hcomb hb hξQ h0D
  · dsimp only [numM]; exact hcomb h0D hb hξQ
  · dsimp only [numM]; exact hcomb h1D h0D h0D
  · dsimp only [numM]; exact hcomb h0D h1D h0D
  · dsimp only [numM]; exact hcomb h0D h0D h1D

lemma A0U_ValLead_of {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {c : Fin 10 → K5} (hm : ∀ i, ValLead k (numM i a_s b_s ξS_s ξQ_s U V) (c i)) :
    ValLead k (A_0U a_s b_s ξS_s ξQ_s U V)
      (-(19708 / 1257375 : K5) * (5 * c 0 - 9 * c 1) +
       (1472 / 1257375 : K5) * (5 * c 1 - 9 * c 2) -
       (16 / 729 : K5) * (5 * c 3 - 9 * c 5) +
       (188 / 2025 : K5) * (5 * c 4 - 9 * c 6)) := by
  unfold A_0U
  have hC (r : K5) {f : LaurentSeries K5} {a : K5} (hf : ValLead k f a) :
      ValLead k (HahnSeries.C r * f) (r * a) := ((ValLead.of_C r).mul hf).eq_k (k' := k) (by omega)
  have hpair (i j : Fin 10) :
      ValLead k (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V)
        (5 * c i - 9 * c j) := by
    have h5 : ValLead k (5 * numM i a_s b_s ξS_s ξQ_s U V) (5 * c i) := by
      simpa only [map_ofNat] using hC 5 (hm i)
    have h9 : ValLead k (9 * numM j a_s b_s ξS_s ξQ_s U V) (9 * c j) := by
      simpa only [map_ofNat] using hC 9 (hm j)
    exact h5.sub h9
  simpa only [map_div₀, map_neg, map_ofNat] using
    (((hC (-(19708 / 1257375 : K5)) (hpair 0 1)).add
      (hC (1472 / 1257375 : K5) (hpair 1 2))).sub
      (hC (16 / 729 : K5) (hpair 3 5))).add
      (hC (188 / 2025 : K5) (hpair 4 6))

lemma A0V_ValLead_of {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {c : Fin 10 → K5} (hm : ∀ i, ValLead k (numM i a_s b_s ξS_s ξQ_s U V) (c i)) :
    ValLead k (A_0V a_s b_s ξS_s ξQ_s U V)
      (-(892 / 3645 : K5) * (5 * c 3 - 9 * c 4) +
       (40 / 81 : K5) * (5 * c 5 - 9 * c 6) -
       (112 / 2395 : K5) * (5 * c 7 - 9 * c 8) +
       (392 / 11975 : K5) * (5 * c 8 - 9 * c 9)) := by
  unfold A_0V
  have hC (r : K5) {f : LaurentSeries K5} {a : K5} (hf : ValLead k f a) :
      ValLead k (HahnSeries.C r * f) (r * a) := ((ValLead.of_C r).mul hf).eq_k (k' := k) (by omega)
  have hpair (i j : Fin 10) :
      ValLead k (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V)
        (5 * c i - 9 * c j) := by
    have h5 : ValLead k (5 * numM i a_s b_s ξS_s ξQ_s U V) (5 * c i) := by
      simpa only [map_ofNat] using hC 5 (hm i)
    have h9 : ValLead k (9 * numM j a_s b_s ξS_s ξQ_s U V) (9 * c j) := by
      simpa only [map_ofNat] using hC 9 (hm j)
    exact h5.sub h9
  simpa only [map_div₀, map_neg, map_ofNat] using
    (((hC (-(892 / 3645 : K5)) (hpair 3 4)).add
      (hC (40 / 81 : K5) (hpair 5 6))).sub
      (hC (112 / 2395 : K5) (hpair 7 8))).add
      (hC (392 / 11975 : K5) (hpair 8 9))

lemma A0U_ValDual_of {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {d : Fin 10 → Dual K5} (hm : ∀ i, ValDual k (numM i a_s b_s ξS_s ξQ_s U V) (d i)) :
    ValDual k (A_0U a_s b_s ξS_s ξQ_s U V)
      (Dual.C (-(19708 / 1257375 : K5)) * (5 * d 0 - 9 * d 1) +
       Dual.C (1472 / 1257375 : K5) * (5 * d 1 - 9 * d 2) -
       Dual.C (16 / 729 : K5) * (5 * d 3 - 9 * d 5) +
       Dual.C (188 / 2025 : K5) * (5 * d 4 - 9 * d 6)) := by
  unfold A_0U
  have hC (r : K5) {f : LaurentSeries K5} {x : Dual K5} (hf : ValDual k f x) :
      ValDual k (HahnSeries.C r * f) (Dual.C r * x) := ((ValDual.of_C r).mul hf).eq_k (k' := k) (by omega)
  have h1v : (1 : Dual K5).val = 1 := rfl
  have h1e : (1 : Dual K5).eps = 0 := rfl
  have hC5 : Dual.C (5 : K5) = (5 : Dual K5) := by
    ext
    · change (5 : K5) = (5 : Dual K5).val
      rw [show (5 : Dual K5) = 1 + 1 + 1 + 1 + 1 by ring]; simp only [Dual.add_val, h1v]; ring
    · change (0 : K5) = (5 : Dual K5).eps
      rw [show (5 : Dual K5) = 1 + 1 + 1 + 1 + 1 by ring]; simp only [Dual.add_eps, h1e]; ring
  have hC9 : Dual.C (9 : K5) = (9 : Dual K5) := by
    ext
    · change (9 : K5) = (9 : Dual K5).val
      rw [show (9 : Dual K5) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]; simp only [Dual.add_val, h1v]; ring
    · change (0 : K5) = (9 : Dual K5).eps
      rw [show (9 : Dual K5) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]; simp only [Dual.add_eps, h1e]; ring
  have hpair (i j : Fin 10) :
      ValDual k (5 * numM i a_s b_s ξS_s ξQ_s U V - 9 * numM j a_s b_s ξS_s ξQ_s U V)
        (5 * d i - 9 * d j) := by
    have h5 : ValDual k (5 * numM i a_s b_s ξS_s ξQ_s U V) (5 * d i) := by
      simpa only [map_ofNat, hC5] using hC 5 (hm i)
    have h9 : ValDual k (9 * numM j a_s b_s ξS_s ξQ_s U V) (9 * d j) := by
      simpa only [map_ofNat, hC9] using hC 9 (hm j)
    exact h5.sub h9
  simpa only [map_div₀, map_neg, map_ofNat] using
    (((hC (-(19708 / 1257375 : K5)) (hpair 0 1)).add
      (hC (1472 / 1257375 : K5) (hpair 1 2))).sub
      (hC (16 / 729 : K5) (hpair 3 5))).add
      (hC (188 / 2025 : K5) (hpair 4 6))

private lemma numM_pair0_eq_zero {S : Type*} [CommRing S] (a b xS xQ w u1 u0 : S) :
    let dHS0 := fun s q => -25 * (5 * s - 9 * q) * (15 * s - 9 * q) * w
    let dHQ0 := fun s q => 50 * s * (5 * s - 9 * q) * w
    let a2 := dHS0 a b
    let a0 := dHS0 xS xQ
    let a1 := dHS0 (a + xS) (b + xQ) - a2 - a0
    let b2 := dHQ0 a b
    let b0 := dHQ0 xS xQ
    let b1 := dHQ0 (a + xS) (b + xQ) - b2 - b0
    let d20 := a2 * b0 - a0 * b2
    let d21 := a2 * b1 - a1 * b2
    let d10 := a1 * b0 - a0 * b1
    (u1 * (5 * a - 9 * b)) * d10 - (u1 * (5 * xS - 9 * xQ) + u0 * (5 * a - 9 * b)) * d20 +
      (u0 * (5 * xS - 9 * xQ)) * d21 = 0 := by
  dsimp only; ring

private lemma dual_det_split {R : Type*} [CommRing R] (A1 A2 B1 B2 : Dual R) (da1 da2 db1 db2 : R) :
    (A1 + ⟨0, da1⟩) * (B2 + ⟨0, db2⟩) - (A2 + ⟨0, da2⟩) * (B1 + ⟨0, db1⟩) =
    (A1 * B2 - A2 * B1) + ⟨0, A1.val * db2 + da1 * B2.val - A2.val * db1 - da2 * B1.val⟩ := by
  ext <;> simp only [Dual.add_val, Dual.sub_val, Dual.mul_val, Dual.add_eps, Dual.sub_eps, Dual.mul_eps] <;> ring

private lemma dual_mul_eps0 {R : Type*} [CommRing R] (m : Dual R) (e : R) :
    m * ⟨0, e⟩ = ⟨0, m.val * e⟩ := by
  ext <;> simp only [Dual.mul_val, Dual.mul_eps] <;> ring

private lemma dual_minor_pair_eq {R : Type*} [Field R]
    (aD bD xSD xQD wD u1 u0 : Dual R) (da2 da1 da0 db2 db1 db0 : R) :
    let dHS0 := fun s q : Dual R => Dual.C (-(25 / 243 : R)) * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
    let dHQ0 := fun s q : Dual R => Dual.C (50 / 27 : R) * s * (5 * s - 9 * q) * wD
    let A2 := dHS0 aD bD
    let A0 := dHS0 xSD xQD
    let A1 := dHS0 (aD + xSD) (bD + xQD) - A2 - A0
    let B2 := dHQ0 aD bD
    let B0 := dHQ0 xSD xQD
    let B1 := dHQ0 (aD + xSD) (bD + xQD) - B2 - B0
    let a2 := A2 + ⟨0, da2⟩
    let a1 := A1 + ⟨0, da1⟩
    let a0 := A0 + ⟨0, da0⟩
    let b2 := B2 + ⟨0, db2⟩
    let b1 := B1 + ⟨0, db1⟩
    let b0 := B0 + ⟨0, db0⟩
    let d20 := a2 * b0 - a0 * b2
    let d21 := a2 * b1 - a1 * b2
    let d10 := a1 * b0 - a0 * b1
    let m2 := u1 * (5 * aD - 9 * bD)
    let m1 := u1 * (5 * xSD - 9 * xQD) + u0 * (5 * aD - 9 * bD)
    let m0 := u0 * (5 * xSD - 9 * xQD)
    m2 * d10 - m1 * d20 + m0 * d21 =
      ⟨0, m2.val * (A1.val * db0 + da1 * B0.val - A0.val * db1 - da0 * B1.val) -
          m1.val * (A2.val * db0 + da2 * B0.val - A0.val * db2 - da0 * B2.val) +
          m0.val * (A2.val * db1 + da2 * B1.val - A1.val * db2 - da1 * B2.val)⟩ := by
  dsimp only
  set dHS0 : Dual R → Dual R → Dual R := fun s q => Dual.C (-(25 / 243 : R)) * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
  set dHQ0 : Dual R → Dual R → Dual R := fun s q => Dual.C (50 / 27 : R) * s * (5 * s - 9 * q) * wD
  set A2 := dHS0 aD bD
  set A0 := dHS0 xSD xQD
  set A1 := dHS0 (aD + xSD) (bD + xQD) - A2 - A0
  set B2 := dHQ0 aD bD
  set B0 := dHQ0 xSD xQD
  set B1 := dHQ0 (aD + xSD) (bD + xQD) - B2 - B0
  set m2 := u1 * (5 * aD - 9 * bD)
  set m1 := u1 * (5 * xSD - 9 * xQD) + u0 * (5 * aD - 9 * bD)
  set m0 := u0 * (5 * xSD - 9 * xQD)
  rw [dual_det_split A1 A0 B1 B0 da1 da0 db1 db0,
      dual_det_split A2 A0 B2 B0 da2 da0 db2 db0,
      dual_det_split A2 A1 B2 B1 da2 da1 db2 db1]
  simp only [mul_add, dual_mul_eps0]
  have h0 : m2 * (A1 * B0 - A0 * B1) - m1 * (A2 * B0 - A0 * B2) + m0 * (A2 * B1 - A1 * B2) = 0 := by
    have hc1 : Dual.C (-(25 / 243 : R)) = Dual.C (1 / 243 : R) * (-25 : Dual R) := by
      rw [← map_ofNat Dual.C 25, ← map_neg Dual.C, ← map_mul Dual.C]; congr 1; ring
    have hc2 : Dual.C (50 / 27 : R) = Dual.C (1 / 27 : R) * (50 : Dual R) := by
      rw [← map_ofNat Dual.C 50, ← map_mul Dual.C]; congr 1; ring
    have hA (s q : Dual R) : dHS0 s q = Dual.C (1 / 243 : R) * (-25 * (5 * s - 9 * q) * (15 * s - 9 * q) * wD) := by
      simp only [dHS0, hc1]; ring
    have hB (s q : Dual R) : dHQ0 s q = Dual.C (1 / 27 : R) * (50 * s * (5 * s - 9 * q) * wD) := by
      simp only [dHQ0, hc2]; ring
    have hmul : m2 * (A1 * B0 - A0 * B1) - m1 * (A2 * B0 - A0 * B2) + m0 * (A2 * B1 - A1 * B2) =
        Dual.C (1 / 243 : R) * Dual.C (1 / 27 : R) *
        (let fS := fun s q : Dual R => -25 * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
         let fQ := fun s q : Dual R => 50 * s * (5 * s - 9 * q) * wD
         let x2 := fS aD bD; let x0 := fS xSD xQD; let x1 := fS (aD + xSD) (bD + xQD) - x2 - x0
         let y2 := fQ aD bD; let y0 := fQ xSD xQD; let y1 := fQ (aD + xSD) (bD + xQD) - y2 - y0
         m2 * (x1 * y0 - x0 * y1) - m1 * (x2 * y0 - x0 * y2) + m0 * (x2 * y1 - x1 * y2)) := by
      dsimp only [A2, A1, A0, B2, B1, B0]
      simp only [hA, hB]; ring
    rw [hmul, show (let fS := fun s q : Dual R => -25 * (5 * s - 9 * q) * (15 * s - 9 * q) * wD
         let fQ := fun s q : Dual R => 50 * s * (5 * s - 9 * q) * wD
         let x2 := fS aD bD; let x0 := fS xSD xQD; let x1 := fS (aD + xSD) (bD + xQD) - x2 - x0
         let y2 := fQ aD bD; let y0 := fQ xSD xQD; let y1 := fQ (aD + xSD) (bD + xQD) - y2 - y0
         m2 * (x1 * y0 - x0 * y1) - m1 * (x2 * y0 - x0 * y2) + m0 * (x2 * y1 - x1 * y2)) = 0 from
      numM_pair0_eq_zero aD bD xSD xQD wD u1 u0, mul_zero]
  calc m2 * (A1 * B0 - A0 * B1) + ⟨0, m2.val * (A1.val * db0 + da1 * B0.val - A0.val * db1 - da0 * B1.val)⟩ -
        (m1 * (A2 * B0 - A0 * B2) + ⟨0, m1.val * (A2.val * db0 + da2 * B0.val - A0.val * db2 - da0 * B2.val)⟩) +
        (m0 * (A2 * B1 - A1 * B2) + ⟨0, m0.val * (A2.val * db1 + da2 * B1.val - A1.val * db2 - da1 * B2.val)⟩)
      = (m2 * (A1 * B0 - A0 * B1) - m1 * (A2 * B0 - A0 * B2) + m0 * (A2 * B1 - A1 * B2)) +
        ⟨0, m2.val * (A1.val * db0 + da1 * B0.val - A0.val * db1 - da0 * B1.val) -
            m1.val * (A2.val * db0 + da2 * B0.val - A0.val * db2 - da0 * B2.val) +
            m0.val * (A2.val * db1 + da2 * B1.val - A1.val * db2 - da1 * B2.val)⟩ := by
        ext <;> simp only [Dual.add_val, Dual.sub_val, Dual.add_eps, Dual.sub_eps] <;> ring
    _ = ⟨0, m2.val * (A1.val * db0 + da1 * B0.val - A0.val * db1 - da0 * B1.val) -
            m1.val * (A2.val * db0 + da2 * B0.val - A0.val * db2 - da0 * B2.val) +
            m0.val * (A2.val * db1 + da2 * B1.val - A1.val * db2 - da1 * B2.val)⟩ := by
        rw [h0, zero_add]

private lemma dual_minor_pair_eq_const {R : Type*} [Field R]
    (aD bD xSD xQD wD u1 u0 : Dual R) (da2 da1 da0 db2 db1 db0 : R) :
    let mk := fun (a b xS xQ w u1' u0' : Dual R) =>
      let dHS0 := fun s q : Dual R => Dual.C (-(25 / 243 : R)) * (5 * s - 9 * q) * (15 * s - 9 * q) * w
      let dHQ0 := fun s q : Dual R => Dual.C (50 / 27 : R) * s * (5 * s - 9 * q) * w
      let A2 := dHS0 a b; let A0 := dHS0 xS xQ; let A1 := dHS0 (a + xS) (b + xQ) - A2 - A0
      let B2 := dHQ0 a b; let B0 := dHQ0 xS xQ; let B1 := dHQ0 (a + xS) (b + xQ) - B2 - B0
      let a2 := A2 + ⟨0, da2⟩; let a1 := A1 + ⟨0, da1⟩; let a0 := A0 + ⟨0, da0⟩
      let b2 := B2 + ⟨0, db2⟩; let b1 := B1 + ⟨0, db1⟩; let b0 := B0 + ⟨0, db0⟩
      let d20 := a2 * b0 - a0 * b2; let d21 := a2 * b1 - a1 * b2; let d10 := a1 * b0 - a0 * b1
      let m2 := u1' * (5 * a - 9 * b)
      let m1 := u1' * (5 * xS - 9 * xQ) + u0' * (5 * a - 9 * b)
      let m0 := u0' * (5 * xS - 9 * xQ)
      m2 * d10 - m1 * d20 + m0 * d21
    mk aD bD xSD xQD wD u1 u0 =
      ⟨0, (mk (Dual.C aD.val) (Dual.C bD.val) (Dual.C xSD.val) (Dual.C xQD.val)
        (Dual.C wD.val) (Dual.C u1.val) (Dual.C u0.val)).eps⟩ := by
  dsimp only
  rw [dual_minor_pair_eq aD bD xSD xQD wD u1 u0 da2 da1 da0 db2 db1 db0,
      dual_minor_pair_eq (Dual.C aD.val) (Dual.C bD.val) (Dual.C xSD.val) (Dual.C xQD.val)
        (Dual.C wD.val) (Dual.C u1.val) (Dual.C u0.val) da2 da1 da0 db2 db1 db0]
  congr 1

lemma EB_bilinear_UV {R : Type*} [Field R] [CharZero R] (S Q T x y U V : R) :
    EB_of S Q T x y U V =
      EB_of S Q T x y 0 0 +
      (EB_of S Q T x y 0 1 - EB_of S Q T x y 0 0) * V +
      (EB_of S Q T x y 1 0 - EB_of S Q T x y 0 0) * U +
      (EB_of S Q T x y 1 1 - EB_of S Q T x y 1 0 - EB_of S Q T x y 0 1 + EB_of S Q T x y 0 0) * U * V := by
  simp only [EB_of, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]
  ring

lemma QY_bilinear_UV {R : Type*} [Field R] [CharZero R] (S Q T x y U V : R) (i : Fin 3) :
    QY_num S Q T x y U V i =
      QY_num S Q T x y 0 0 i +
      (QY_num S Q T x y 0 1 i - QY_num S Q T x y 0 0 i) * V +
      (QY_num S Q T x y 1 0 i - QY_num S Q T x y 0 0 i) * U +
      (QY_num S Q T x y 1 1 i - QY_num S Q T x y 1 0 i - QY_num S Q T x y 0 1 i + QY_num S Q T x y 0 0 i) * U * V := by
  fin_cases i <;>
    (simp only [QY_num, Omega_F, dDX2_F, F_contract, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]; ring)

lemma QX_bilinear_UV {R : Type*} [Field R] [CharZero R] (S Q T x y U V : R) (i : Fin 3) :
    QX_num S Q T x y U V i =
      QX_num S Q T x y 0 0 i +
      (QX_num S Q T x y 0 1 i - QX_num S Q T x y 0 0 i) * V +
      (QX_num S Q T x y 1 0 i - QX_num S Q T x y 0 0 i) * U +
      (QX_num S Q T x y 1 1 i - QX_num S Q T x y 1 0 i - QX_num S Q T x y 0 1 i + QX_num S Q T x y 0 0 i) * U * V := by
  fin_cases i <;>
    (simp only [QX_num, Omega_F, dDY2_F, F_contract, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u_of, v_of]; ring)

private lemma QX_num_01_sub_00_factor {R : Type*} [Field R] [CharZero R] (S Q T x y a b : R) :
    (T - 3) * ((QX_num S Q T x y 0 1 0 - QX_num S Q T x y 0 0 0) * a +
      (QX_num S Q T x y 0 1 1 - QX_num S Q T x y 0 0 1) * b +
      (QX_num S Q T x y 0 1 2 - QX_num S Q T x y 0 0 2)) =
    (80 / 81 : R) * x * T ^ 2 * S ^ 2 * (T - 3) ^ 3 *
      (23 * S ^ 3 - 82 * S ^ 2 * Q + 71 * S * Q ^ 2 + 4 * Q ^ 3 -
        50 * S ^ 2 * x + 90 * S * Q * x + 27 * S * x ^ 2) *
      ((T - 3) * (-(5 * S - 3 * Q) * a + 6 * S * b) + S * (5 * S - 9 * Q)) := by
  simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
    om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of]
  ring


private theorem branch_jet_helpers_proof : BranchJetHelpersSpec where
  numM_ValLead := @numM_ValLead_of
  numM_ValDual := @numM_ValDual_of
  A0U_ValLead := @A0U_ValLead_of
  A0V_ValLead := @A0V_ValLead_of
  A0U_ValDual := @A0U_ValDual_of
  dual_minor_pair_const := @dual_minor_pair_eq_const
  EB_bilinear := @EB_bilinear_UV
  QY_bilinear := @QY_bilinear_UV
  QX_bilinear := @QX_bilinear_UV
  QX_num_01_sub_00 := @QX_num_01_sub_00_factor

end SymmetricSexticResidual.LocalResidueU0

theorem solution : SymmetricSexticResidual.LocalResidueU0.BranchJetHelpersSpec :=
  SymmetricSexticResidual.LocalResidueU0.branch_jet_helpers_proof
