-- Prove2me | solution 1 for LSS.structured_inverse_and_schmidt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T18:09:14.743223+00:00
-- url     : https://prove2.me/submissions/caff3d5b-3147-438f-90cf-1f492faedadc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LSSInterface
import Definitions.Def_LSSNil
import Theorems.Thm_LSS_lss_nil_inverse
import Theorems.Thm_LSS_lss_nil_schmidt




/-!
# Nilsequences satisfy the abstract Leng–Sah–Sawhney interface

We show that the class `NilStr s` of Lipschitz nilsequences satisfies `InvHyp` and
`SchmidtHyp`, assuming the two published results:

* `NilInverseStmt s`: the quasi-polynomial inverse theorem for the `U^{s+1}[N]` norm
  (Leng–Sah–Sawhney, arXiv:2402.17994, Theorem 1.2);
* `NilSchmidtStmt s`: the Schmidt-type decomposition for nilsequences
  (Leng–Sah–Sawhney, arXiv:2402.17995, Lemma 2.1).
-/

open Finset

namespace LSS

noncomputable section

/-- **Leng–Sah–Sawhney, Theorem 1.2** (quasi-polynomial `U^{s+1}[N]` inverse theorem), with the
Gowers norm written as the unnormalised sum `gowersZ`. -/
def NilInverseStmt (s : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ) (f : ℤ → ℝ), 0 < δ → δ ≤ 1 / 2 → (∀ x, |f x| ≤ 1) →
    SupportedOn N f → δ ^ (2 ^ (s + 1)) * (N : ℝ) ^ (s + 2) ≤ gowersZ N (s + 1) f →
    ∃ (G : Nilmanifold s) (g : ℤ → G.Mat) (F : G.Mat → ℂ),
      (G.d : ℝ) ≤ C * (1 + Real.log (1 / δ)) ^ C ∧ G.complexity ≤ qp C (1 / δ) ∧
      G.IsPoly g ∧ G.IsLip (qp C (1 / δ)) F ∧
      (N : ℝ) / qp C (1 / δ) ≤ ‖∑ x ∈ Icc (1 : ℤ) N, (f x : ℂ) * F (g x)‖

/-- **Leng–Sah–Sawhney, Lemma 2.1** (Schmidt-type decomposition for nilsequences): `T`
polynomial sequences on nilmanifolds of degree `s`, dimension `≤ D` and complexity `≤ M` are
simultaneously almost constant (in `G/Γ`) on the pieces of a partition of `{1, …, N}` into
`L ≤ 2 N^{1 - c/((T+1)D)^C}` arithmetic progressions. -/
def NilSchmidtStmt (s : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N T D : ℕ) (M : ℝ) (G : Fin T → Nilmanifold s)
    (g : ∀ i, ℤ → (G i).Mat), 1 ≤ D → 1 ≤ M → (∀ i, (G i).d ≤ D) →
    (∀ i, (G i).complexity ≤ M) → (∀ i, (G i).IsPoly (g i)) →
    ∃ P : APPart N, (P.L : ℝ) * (N : ℝ) ^ (c / (((T : ℝ) + 1) * D) ^ C) ≤ 2 * N ∧
      ∀ i j, ∀ x ∈ P.piece j, ∀ y ∈ P.piece j,
        (G i).distQ (g i x) (g i y) ≤
          C * M ^ (C * (D : ℝ) ^ C) * (N : ℝ) ^ (-(c / (((T : ℝ) + 1) * D) ^ C))

namespace Nilmanifold

variable {s : ℕ} (G : Nilmanifold s)

lemma coordNorm_nonneg (x : G.Mat) : 0 ≤ G.coordNorm x := by
  apply Real.sInf_nonneg
  rintro r ⟨t, -, rfl⟩
  exact norm_nonneg _

lemma dist_nonneg (x y : G.Mat) : 0 ≤ G.dist x y := by
  apply Real.sInf_nonneg
  rintro r ⟨m, z, -, -, -, rfl⟩
  exact Finset.sum_nonneg fun i _ => le_min (G.coordNorm_nonneg _) (G.coordNorm_nonneg _)

lemma mem_mul {x y : G.Mat} (hx : G.Mem x) (hy : G.Mem y) : G.Mem (x * y) := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨u, rfl⟩ := hy
  obtain ⟨v, hv⟩ := G.group_mul t u
  exact ⟨v, hv.symm⟩

lemma mem_of_memΓ {x : G.Mat} (hx : G.MemΓ x) : G.Mem x := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨_, rfl⟩

lemma IsLip.mono {K K' : ℝ} {F : G.Mat → ℂ} (h : G.IsLip K F) (hK : K ≤ K') : G.IsLip K' F :=
  ⟨h.1, fun x hx => (h.2.1 x hx).trans hK, fun x y hx hy =>
    (h.2.2 x y hx hy).trans (mul_le_mul_of_nonneg_right hK (G.dist_nonneg x y))⟩

/-- A Lipschitz function on `G/Γ` is Lipschitz for the quotient metric. -/
lemma IsLip.le_distQ {K : ℝ} (hK : 0 < K) {F : G.Mat → ℂ} (h : G.IsLip K F) {x y : G.Mat}
    (hx : G.Mem x) (hy : G.Mem y) : ‖F x - F y‖ ≤ K * G.distQ x y := by
  rw [← div_le_iff₀' hK]
  apply le_csInf
  · exact ⟨_, G.malcev (fun k => ((0 : Fin G.d → ℤ) k : ℝ)),
      G.malcev (fun k => ((0 : Fin G.d → ℤ) k : ℝ)), ⟨0, rfl⟩, ⟨0, rfl⟩, rfl⟩
  · rintro r ⟨γ, γ', hγ, hγ', rfl⟩
    rw [div_le_iff₀' hK, ← h.1 x γ hx hγ, ← h.1 y γ' hy hγ']
    exact h.2.2 _ _ (G.mem_mul hx (G.mem_of_memΓ hγ)) (G.mem_mul hy (G.mem_of_memΓ hγ'))

end Nilmanifold

lemma qp_eq {C x : ℝ} : qp C x = Real.exp (C * (1 + Real.log x) ^ C) := rfl

/-- The inverse theorem for nilsequences gives `InvHyp (NilStr s) s`. -/
theorem invHyp_of_nilInverse {s : ℕ} (hA : NilInverseStmt s) : InvHyp (NilStr s) s := by
  obtain ⟨C, hC, hA⟩ := hA
  refine ⟨C + 1, by linarith, ?_⟩
  intro N δ f hδ hδ2 hf hfs hgow
  obtain ⟨G, g, F, hd, hcx, hpoly, hlip, hcor⟩ := hA N δ f hδ hδ2 hf hfs hgow
  set y : ℝ := 1 + Real.log (1 / δ) with hy
  have hlog : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]; linarith
  have hy1 : 1 ≤ y := by linarith
  have hpow : y ^ C ≤ y ^ (C + 1) := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
  have hyC : 1 ≤ y ^ C := Real.one_le_rpow hy1 hC.le
  have hexp : C * y ^ C + Real.log 2 ≤ (C + 1) * y ^ (C + 1) := by
    have := Real.log_two_lt_d9
    nlinarith
  set E := qp C (1 / δ) with hE
  set E' := qp (C + 1) (1 / δ) with hE'
  have hEpos : 0 < E := Real.exp_pos _
  have h2E : 2 * E ≤ E' := by
    rw [hE, hE', qp_eq, qp_eq, ← hy]
    calc 2 * Real.exp (C * y ^ C) = Real.exp (C * y ^ C + Real.log 2) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]; ring
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  have hEE : E ≤ E' := by linarith
  have hdim : (G.d : ℝ) ≤ 1 + Real.log E' := by
    rw [hE', qp_eq, Real.log_exp, ← hy]
    nlinarith
  have hbound : ∀ m, ‖F (g m)‖ ≤ E := fun m => hlip.2.1 _ (hpoly.1 m)
  -- split the correlation into real and imaginary parts
  have hre : (∑ x ∈ Icc (1 : ℤ) N, (f x : ℂ) * F (g x)).re =
      ∑ x ∈ Icc (1 : ℤ) N, f x * (F (g x)).re := by
    rw [Complex.re_sum]; simp [Complex.mul_re]
  have him : (∑ x ∈ Icc (1 : ℤ) N, (f x : ℂ) * F (g x)).im =
      ∑ x ∈ Icc (1 : ℤ) N, f x * (F (g x)).im := by
    rw [Complex.im_sum]; simp [Complex.mul_im]
  have hsplit := Complex.norm_le_abs_re_add_abs_im (∑ x ∈ Icc (1 : ℤ) N, (f x : ℂ) * F (g x))
  have hN : (N : ℝ) / E' ≤ (N : ℝ) / E / 2 := by
    rw [div_div, mul_comm E 2]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h2E
  have hQ : ∀ φ : ℤ → ℝ, ((∀ m, φ m = (F (g m)).re) ∨ (∀ m, φ m = (F (g m)).im)) →
      (N : ℝ) / E' ≤ |∑ x ∈ Icc (1 : ℤ) N, f x * φ x| →
      ∃ φ' : ℤ → ℝ, NilStr s N E' φ' ∧ (∀ x, |φ' x| ≤ E') ∧
        (N : ℝ) / E' ≤ |∑ x ∈ Icc (1 : ℤ) N, f x * φ' x| := by
    intro φ hφ hcorφ
    refine ⟨φ, ⟨G, g, F, hdim, hcx.trans hEE, hpoly, Nilmanifold.IsLip.mono G hlip hEE, hφ⟩, ?_, hcorφ⟩
    intro x
    rcases hφ with h | h <;> rw [h x]
    · exact (Complex.abs_re_le_norm _).trans ((hbound x).trans hEE)
    · exact (Complex.abs_im_le_norm _).trans ((hbound x).trans hEE)
  rcases le_total (|∑ x ∈ Icc (1 : ℤ) N, f x * (F (g x)).im|)
      (|∑ x ∈ Icc (1 : ℤ) N, f x * (F (g x)).re|) with h | h
  · exact hQ (fun m => (F (g m)).re) (Or.inl fun _ => rfl) (by
      rw [hre, him] at hsplit; linarith)
  · exact hQ (fun m => (F (g m)).im) (Or.inr fun _ => rfl) (by
      rw [hre, him] at hsplit; linarith)

/-- Numerical core of the Schmidt reduction. -/
lemma schmidt_numeric {c C : ℝ} (hc : 0 < c) (hC : 0 < C) {T : ℕ} {Q D : ℝ} (hQ : 1 ≤ Q)
    (hD1 : 1 ≤ D) (hD : D ≤ 1 + Real.log Q) :
    1 / qp (2 * C + |Real.log c| + |Real.log C| + 2) (((T : ℝ) + 2) * (Q + 2)) ≤
        c / (((T : ℝ) + 1) * D) ^ C ∧
      Q * (C * Q ^ (C * D ^ C)) ≤
        qp (2 * C + |Real.log c| + |Real.log C| + 2) (((T : ℝ) + 2) * (Q + 2)) := by
  set C' := 2 * C + |Real.log c| + |Real.log C| + 2 with hC'
  set X : ℝ := ((T : ℝ) + 2) * (Q + 2) with hX
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hXpos : 0 < X := by linarith
  set y : ℝ := 1 + Real.log X with hy
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hy1 : 1 ≤ y := by linarith
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQX : Real.log Q ≤ Real.log X :=
    Real.log_le_log (by linarith) (by rw [hX]; nlinarith)
  have hDy : D ≤ y := by linarith
  have hyX : y ≤ X := by have := Real.log_le_sub_one_of_pos hXpos; linarith
  have hT1X : (T : ℝ) + 1 ≤ X := by rw [hX]; nlinarith
  have hC'1 : C + 1 ≤ C' := by
    have := abs_nonneg (Real.log c); have := abs_nonneg (Real.log C); linarith
  have hyC'1 : y ^ (C + 1) ≤ y ^ C' := Real.rpow_le_rpow_of_exponent_le hy1 hC'1
  have hy_le : y ≤ y ^ C' := by
    simpa using Real.rpow_le_rpow_of_exponent_le hy1 (show (1 : ℝ) ≤ C' by linarith)
  have hqp : qp C' X = Real.exp (C' * y ^ C') := rfl
  constructor
  · -- `((T+1) D)^C ≤ X^{2C} ≤ exp (2 C y) ≤ c · qp`
    have hTD : ((T : ℝ) + 1) * D ≤ X * X :=
      mul_le_mul hT1X (hDy.trans hyX) (by linarith) hXpos.le
    have h1 : (((T : ℝ) + 1) * D) ^ C ≤ Real.exp (2 * C * y) := by
      calc (((T : ℝ) + 1) * D) ^ C ≤ (X * X) ^ C :=
            Real.rpow_le_rpow (by positivity) hTD hC.le
        _ = Real.exp (2 * C * Real.log X) := by
            rw [Real.rpow_def_of_pos (by positivity), Real.log_mul hXpos.ne' hXpos.ne']
            ring_nf
        _ ≤ Real.exp (2 * C * y) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (2 * C * y) ≤ c * qp C' X := by
      rw [hqp, ← Real.exp_log hc, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hl := neg_abs_le (Real.log c)
      have : (2 * C + |Real.log c|) * y ≤ C' * y ^ C' := by
        have : 2 * C + |Real.log c| ≤ C' := by have := abs_nonneg (Real.log C); linarith
        calc (2 * C + |Real.log c|) * y ≤ C' * y :=
              mul_le_mul_of_nonneg_right this (by linarith)
          _ ≤ C' * y ^ C' := mul_le_mul_of_nonneg_left hy_le (by linarith)
      nlinarith [abs_nonneg (Real.log c)]
    have hqpos : 0 < qp C' X := Real.exp_pos _
    have hTDpos : 0 < (((T : ℝ) + 1) * D) ^ C := by positivity
    rw [div_le_div_iff₀ hqpos hTDpos]
    linarith
  · have hQpos : 0 < Q := by linarith
    have hDC : D ^ C ≤ y ^ C := Real.rpow_le_rpow (by linarith) hDy hC.le
    have hyC1 : 1 ≤ y ^ C := Real.one_le_rpow hy1 hC.le
    have hyCC : y ^ (C + 1) = y ^ C * y := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have hlhs : Q * (C * Q ^ (C * D ^ C)) =
        Real.exp (Real.log Q + Real.log C + C * D ^ C * Real.log Q) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hQpos, Real.exp_log hC,
        Real.rpow_def_of_pos hQpos]
      ring_nf
    rw [hlhs, hqp]
    apply Real.exp_le_exp.mpr
    have e1 : Real.log Q ≤ y := by linarith
    have e2 : Real.log C ≤ |Real.log C| := le_abs_self _
    have e3 : C * D ^ C * Real.log Q ≤ C * y ^ (C + 1) := by
      rw [hyCC, ← mul_assoc]
      apply mul_le_mul (mul_le_mul_of_nonneg_left hDC hC.le) (by linarith) hlogQ0
      positivity
    have e4 : 1 ≤ y ^ (C + 1) := Real.one_le_rpow hy1 (by linarith)
    have e5 : y ≤ y ^ (C + 1) := by rw [hyCC]; nlinarith
    have e6 : (1 + |Real.log C| + C) * y ^ (C + 1) ≤ C' * y ^ C' := by
      apply mul_le_mul _ hyC'1 (by linarith) (by linarith)
      have := abs_nonneg (Real.log c); linarith
    nlinarith [abs_nonneg (Real.log C)]

/-- The Schmidt lemma for nilsequences gives `SchmidtHyp (NilStr s)`. -/
theorem schmidtHyp_of_nilSchmidt {s : ℕ} (hB : NilSchmidtStmt s) : SchmidtHyp (NilStr s) := by
  obtain ⟨c, C, hc, hC, hB⟩ := hB
  refine ⟨2 * C + |Real.log c| + |Real.log C| + 2, by positivity, ?_⟩
  intro N T Q φ hQ hφ
  choose G g F hd hcx hpoly hlip hre using hφ
  set D : ℕ := ⌊1 + Real.log Q⌋₊ with hDdef
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hD1 : 1 ≤ D := Nat.le_floor (by simpa using hlogQ0)
  have hDle : (D : ℝ) ≤ 1 + Real.log Q := Nat.floor_le (by linarith)
  have hdD : ∀ i, (G i).d ≤ D := fun i => Nat.le_floor (hd i)
  obtain ⟨P, hL, hdist⟩ := hB N T D Q G g hD1 hQ hdD hcx hpoly
  obtain ⟨hn1, hn2⟩ := schmidt_numeric (T := T) hc hC hQ (by exact_mod_cast hD1) hDle
  set V := qp (2 * C + |Real.log c| + |Real.log C| + 2) (((T : ℝ) + 2) * (Q + 2)) with hV
  set a := c / (((T : ℝ) + 1) * D) ^ C with ha
  have hVpos : 0 < V := Real.exp_pos _
  refine ⟨P, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [Nat.cast_zero]
      rw [Real.zero_rpow (by positivity)]
      simp
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      calc (P.L : ℝ) * (N : ℝ) ^ (1 / V) ≤ (P.L : ℝ) * (N : ℝ) ^ a :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hn1)
              (Nat.cast_nonneg _)
        _ ≤ 2 * N := hL
  · intro i j x hx y hy
    have hxN : x ∈ Icc (1 : ℤ) N := (P.cover x).mpr ⟨j, hx⟩
    have hN1 : (1 : ℝ) ≤ N := by
      rw [Finset.mem_Icc] at hxN
      exact_mod_cast (show (1 : ℤ) ≤ N by omega)
    have hQpos : 0 < Q := by linarith
    have hF := Nilmanifold.IsLip.le_distQ (G i) hQpos (hlip i) ((hpoly i).1 x) ((hpoly i).1 y)
    have hdiff : |φ i x - φ i y| ≤ ‖F i (g i x) - F i (g i y)‖ := by
      rcases hre i with h | h <;> rw [h x, h y]
      · simpa using Complex.abs_re_le_norm (F i (g i x) - F i (g i y))
      · simpa using Complex.abs_im_le_norm (F i (g i x) - F i (g i y))
    have hNa : (N : ℝ) ^ (-a) ≤ (N : ℝ) ^ (-(1 / V)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hNa0 : 0 ≤ (N : ℝ) ^ (-a) := by positivity
    calc |φ i x - φ i y| ≤ Q * (G i).distQ (g i x) (g i y) := hdiff.trans hF
      _ ≤ Q * (C * Q ^ (C * (D : ℝ) ^ C) * (N : ℝ) ^ (-a)) :=
          mul_le_mul_of_nonneg_left (hdist i j x hx y hy) hQpos.le
      _ = Q * (C * Q ^ (C * (D : ℝ) ^ C)) * (N : ℝ) ^ (-a) := by ring
      _ ≤ V * (N : ℝ) ^ (-(1 / V)) :=
          mul_le_mul hn2 hNa hNa0 hVpos.le

/-- The two published results about nilsequences give the structural input of the
Leng–Sah–Sawhney argument. -/
theorem structured_inverse_and_schmidt_of_nil {s : ℕ} (hA : NilInverseStmt s)
    (hB : NilSchmidtStmt s) :
    ∃ Str : ℕ → ℝ → (ℤ → ℝ) → Prop, InvHyp Str s ∧ SchmidtHyp Str :=
  ⟨NilStr s, invHyp_of_nilInverse hA, schmidtHyp_of_nilSchmidt hB⟩

end

end LSS


theorem solution (s : ℕ) (hs : 3 ≤ s) :
    ∃ Str : ℕ → ℝ → (ℤ → ℝ) → Prop, LSS.InvHyp Str s ∧ LSS.SchmidtHyp Str :=
  LSS.structured_inverse_and_schmidt_of_nil (LSS.lss_nil_inverse s hs) (LSS.lss_nil_schmidt s hs)
