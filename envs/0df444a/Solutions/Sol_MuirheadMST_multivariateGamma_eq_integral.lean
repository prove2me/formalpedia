-- Prove2me | solution 1 for MuirheadMST.multivariateGamma_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T20:18:31.694613+00:00
-- url     : https://prove2.me/submissions/7bc27897-dcf4-4bce-80a3-ef65c0a17005

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory ProbabilityTheory

open scoped Classical

noncomputable section

namespace MvGammaAux
open MuirheadMST

/-- Upper-triangle index set. -/
abbrev U (m : ℕ) := {p : Fin m × Fin m // p.1 ≤ p.2}

/-- Symmetric completion of upper-triangular entries. -/
def symC {m : ℕ} (a : U m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), le_of_not_ge h⟩

lemma measurable_symC (m : ℕ) : Measurable (symC (m := m)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold symC
  split_ifs <;> exact measurable_pi_apply _

/-- The integrand. -/
def F (m : ℕ) (a : ℝ) (A : Fin m → Fin m → ℝ) : ENNReal :=
  ENNReal.ofReal (if (Matrix.of A).PosDef then
        Real.exp (-(Matrix.of A).trace) * (Matrix.of A).det ^ (a - ((m : ℝ) + 1) / 2)
      else 0)

lemma measurableSet_posDef (m : ℕ) :
    MeasurableSet {A : Fin m → Fin m → ℝ | (Matrix.of A).PosDef} := by
  have hdet : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).det :=
    continuous_id.matrix_det
  have key : {A : Fin m → Fin m → ℝ | (Matrix.of A).PosDef} =
      ({A | ∀ i j, A j i = A i j} ∩ ⋂ x : Fin m → ℝ, {A | 0 ≤ dotProduct x (Matrix.mulVec (Matrix.of A) x)}) ∩
        {A | (Matrix.of A).det ≠ 0} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      refine ⟨⟨fun i j => ?_, fun x => ?_⟩, h.det_pos.ne'⟩
      · simpa using (Matrix.IsHermitian.ext_iff.1 h.1) i j
      · simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.1 h.posSemidef).2 x
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hps : (Matrix.of A).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.2
          ⟨Matrix.IsHermitian.ext_iff.2 fun i j => by simpa using h1 i j, fun x => by simpa using h2 x⟩
      exact hps.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h3))
  rw [key]
  refine MeasurableSet.inter (IsClosed.measurableSet ?_) (IsOpen.measurableSet ?_)
  · refine IsClosed.inter ?_ (isClosed_iInter fun x => isClosed_le continuous_const ?_)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq (by fun_prop) (by fun_prop)
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
  · exact isOpen_ne_fun hdet continuous_const

lemma measurable_F (m : ℕ) (a : ℝ) : Measurable (F m a) := by
  have hdet : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).det :=
    continuous_id.matrix_det
  have htr : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]; fun_prop
  refine Measurable.ennreal_ofReal (Measurable.ite (measurableSet_posDef m) ?_ measurable_const)
  exact (htr.measurable.neg.exp).mul (hdet.measurable.pow_const _)

/-- Block assembly `[[t, bᵀ], [b, B]]`. -/
def blk {m : ℕ} (t : ℝ) (b : Fin m → ℝ) (B : Fin m → Fin m → ℝ) :
    Fin (m + 1) → Fin (m + 1) → ℝ :=
  Fin.cons (Fin.cons t b : Fin (m + 1) → ℝ) (fun i => (Fin.cons (b i) (B i) : Fin (m + 1) → ℝ))

def outer {m : ℕ} (t : ℝ) (b : Fin m → ℝ) : Fin m → Fin m → ℝ := fun i j => b i * b j / t

lemma not_posDef_blk {m : ℕ} {t : ℝ} (ht : t ≤ 0) (b : Fin m → ℝ) (B : Fin m → Fin m → ℝ) :
    ¬ (Matrix.of (blk t b B)).PosDef := by
  intro h
  have := h.diag_pos (i := 0)
  simp [blk] at this
  linarith

lemma quad_blk {m : ℕ} {t : ℝ} (ht : 0 < t) (b : Fin m → ℝ) (C : Fin m → Fin m → ℝ)
    (x : Fin (m + 1) → ℝ) :
    dotProduct x (Matrix.mulVec (Matrix.of (blk t b (C + outer t b))) x) =
      t * (x 0 + (∑ j, b j * x j.succ) / t) ^ 2 +
        dotProduct (fun i => x i.succ) (Matrix.mulVec (Matrix.of C) (fun i => x i.succ)) := by
  have e : t * (x 0 + (∑ j, b j * x j.succ) / t) ^ 2 = t * x 0 ^ 2 +
      2 * x 0 * (∑ j, b j * x j.succ) + (∑ j, b j * x j.succ) ^ 2 / t := by
    field_simp; ring
  rw [e, sq (∑ j, b j * x j.succ), Finset.sum_mul_sum, Finset.sum_div]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, blk, Matrix.of_apply, Fin.cons_zero,
    Fin.cons_succ, Pi.add_apply, outer]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul, Finset.sum_div]
  have h1 : ∑ i, x i.succ * (b i * x 0) = ∑ i, x 0 * (b i * x i.succ) :=
    Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, 2 * x 0 * (b i * x i.succ) = 2 * ∑ i, x 0 * (b i * x i.succ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ i, ∑ j, x i.succ * (b i * b j / t * x j.succ) =
      ∑ i, ∑ j, b i * x i.succ * (b j * x j.succ) / t :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, h3]
  ring

lemma posDef_blk_iff {m : ℕ} {t : ℝ} (ht : 0 < t) (b : Fin m → ℝ) (C : Fin m → Fin m → ℝ) :
    (Matrix.of (blk t b (C + outer t b))).PosDef ↔ (Matrix.of C).PosDef := by
  have herm : (Matrix.of (blk t b (C + outer t b))).IsHermitian ↔ (Matrix.of C).IsHermitian := by
    simp only [Matrix.IsHermitian.ext_iff, star_trivial, Matrix.of_apply]
    constructor
    · intro h i j
      have := h i.succ j.succ
      simp only [blk, outer, Fin.cons_succ, Pi.add_apply] at this
      have e : b j * b i / t = b i * b j / t := by ring
      linarith
    · intro h i j
      cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [blk, outer, h] <;> ring
  rw [Matrix.posDef_iff_dotProduct_mulVec, Matrix.posDef_iff_dotProduct_mulVec, herm]
  simp only [star_trivial]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h y hy
    have hne : (Fin.cons (-(∑ j, b j * y j) / t) y : Fin (m + 1) → ℝ) ≠ 0 := by
      intro h0; apply hy; funext i; simpa using congr_fun h0 i.succ
    have := h hne
    rw [quad_blk ht] at this
    simpa [neg_div] using this
  · intro h x hx
    rw [quad_blk ht]
    by_cases hy : (fun i : Fin m => x i.succ) = 0
    · have hy' : ∀ i : Fin m, x i.succ = 0 := fun i => congr_fun hy i
      have hx0 : x 0 ≠ 0 := by
        intro h0; apply hx; funext i
        cases i using Fin.cases with
        | zero => simpa using h0
        | succ i => simpa using hy' i
      simp [hy', Matrix.mulVec, dotProduct]
      positivity
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ht.le (sq_nonneg _)) (h hy)

lemma det_blk {m : ℕ} {t : ℝ} (ht : 0 < t) (b : Fin m → ℝ) (C : Fin m → Fin m → ℝ) :
    (Matrix.of (blk t b (C + outer t b))).det = t * (Matrix.of C).det := by
  -- Cofactor expansions for a matrix whose first column (resp. row) vanishes off the corner.
  have hcol : ∀ N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ, (∀ i : Fin m, N i.succ 0 = 0) →
      N.det = N 0 0 * (N.submatrix Fin.succ Fin.succ).det := by
    intro N hN
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [hN]
  have hrow : ∀ N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ, (∀ j : Fin m, N 0 j.succ = 0) →
      N.det = N 0 0 * (N.submatrix Fin.succ Fin.succ).det := by
    intro N hN
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [hN]
  let P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of
    (Fin.cons (Fin.cons 1 0 : Fin (m + 1) → ℝ)
      (fun i => (Fin.cons (-b i / t) (fun j => if i = j then 1 else 0) : Fin (m + 1) → ℝ)))
  have hP : P.det = 1 := by
    rw [hrow P (fun j => by simp [P])]
    have : P.submatrix Fin.succ Fin.succ = 1 := by
      ext i j; simp [P, Matrix.one_apply]
    rw [this]; simp [P]
  have hPM : P * Matrix.of (blk t b (C + outer t b)) = Matrix.of
      (Fin.cons (Fin.cons t b : Fin (m + 1) → ℝ)
        (fun i => (Fin.cons 0 (C i) : Fin (m + 1) → ℝ))) := by
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_succ, blk, outer] <;> field_simp <;> ring
  have := congrArg Matrix.det hPM
  rw [Matrix.det_mul, hP, one_mul] at this
  rw [this, hcol _ (fun i => by simp)]
  simp only [Matrix.of_apply, Fin.cons_zero]
  congr 2

lemma trace_blk {m : ℕ} {t : ℝ} (ht : 0 < t) (b : Fin m → ℝ) (C : Fin m → Fin m → ℝ) :
    (Matrix.of (blk t b (C + outer t b))).trace = t + (Matrix.of C).trace + (∑ i, b i ^ 2) / t := by
  simp [Matrix.trace, blk, Fin.sum_univ_succ, outer, Finset.sum_add_distrib, Finset.sum_div, sq]
  ring

lemma F_blk {m : ℕ} (a : ℝ) {t : ℝ} (ht : 0 < t) (b : Fin m → ℝ) (C : Fin m → Fin m → ℝ) :
    F (m + 1) a (blk t b (C + outer t b)) =
      ENNReal.ofReal (Real.exp (-t) * t ^ (a - ((m : ℝ) + 2) / 2)) *
        ENNReal.ofReal (Real.exp (-(∑ i, b i ^ 2) / t)) * F m (a - 1 / 2) C := by
  unfold F
  rw [posDef_blk_iff ht, det_blk ht, trace_blk ht]
  split_ifs with h
  · have hd := h.det_pos
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow ht.le hd.le]
    have e1 : a - (((m + 1 : ℕ) : ℝ) + 1) / 2 = a - ((m : ℝ) + 2) / 2 := by push_cast; ring
    have e2 : a - 1 / 2 - ((m : ℝ) + 1) / 2 = a - ((m : ℝ) + 2) / 2 := by ring
    rw [e1, e2]
    have : Real.exp (-(t + (Matrix.of C).trace + (∑ i, b i ^ 2) / t)) =
        Real.exp (-t) * Real.exp (-(∑ i, b i ^ 2) / t) * Real.exp (-(Matrix.of C).trace) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [this]; ring
  · simp

/-- The index map `Unit ⊕ (Fin m ⊕ U m) → U (m+1)`. -/
def idxFun (m : ℕ) : Unit ⊕ (Fin m ⊕ U m) → U (m + 1)
  | .inl _ => ⟨(0, 0), le_rfl⟩
  | .inr (.inl j) => ⟨(0, j.succ), Fin.zero_le _⟩
  | .inr (.inr p) => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.2 p.2⟩

lemma idxFun_bij (m : ℕ) : Function.Bijective (idxFun m) := by
  constructor
  · rintro (_ | j | ⟨⟨i, j⟩, h⟩) (_ | j' | ⟨⟨i', j'⟩, h'⟩) e <;>
      simp [idxFun, Subtype.ext_iff, Prod.ext_iff, Fin.succ_ne_zero] at e ⊢ <;>
      first
        | exact e
        | exact (Fin.succ_ne_zero _ e.symm).elim
        | exact (Fin.succ_ne_zero _ e.1.symm).elim
  · rintro ⟨⟨i, j⟩, h⟩
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact ⟨.inl (), rfl⟩
      | succ j => exact ⟨.inr (.inl j), rfl⟩
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd h (by simp)
      | succ j => exact ⟨.inr (.inr ⟨(i, j), Fin.succ_le_succ_iff.1 h⟩), rfl⟩

def idxEquiv (m : ℕ) : Unit ⊕ (Fin m ⊕ U m) ≃ U (m + 1) := Equiv.ofBijective _ (idxFun_bij m)

lemma symC_decomp (m : ℕ) (t : ℝ) (b : Fin m → ℝ) (y : U m → ℝ) :
    symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
      (Sum.elim (fun _ => t) (Sum.elim b y))) = blk t b (symC y) := by
  have key : ∀ (z : Unit ⊕ (Fin m ⊕ U m) → ℝ) (p : U (m + 1)),
      MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m) z p = z ((idxEquiv m).symm p) := by
    intro z p
    conv_lhs => rw [← (idxEquiv m).apply_symm_apply p]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) _ _ _
  have hs1 : ∀ h, (idxEquiv m).symm ⟨(0, 0), h⟩ = .inl () := fun h =>
    (Equiv.symm_apply_eq _).2 rfl
  have hs2 : ∀ (j : Fin m) h, (idxEquiv m).symm ⟨(0, j.succ), h⟩ = .inr (.inl j) := fun j h =>
    (Equiv.symm_apply_eq _).2 rfl
  have hs3 : ∀ (i j : Fin m) h, (idxEquiv m).symm ⟨(i.succ, j.succ), h⟩ =
      .inr (.inr ⟨(i, j), Fin.succ_le_succ_iff.1 h⟩) := fun i j h =>
    (Equiv.symm_apply_eq _).2 rfl
  funext i j
  simp only [symC, key]
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [hs1, blk]
    | succ j => simp [hs2, blk]
  | succ i =>
    cases j using Fin.cases with
    | zero => simp [hs2, blk]
    | succ j =>
      by_cases h : i ≤ j
      · simp [h, hs3, blk, symC]
      · simp [h, hs3, blk, symC]

lemma lintegral_decomp (m : ℕ) (G : (Fin (m + 1) → Fin (m + 1) → ℝ) → ENNReal)
    (hG : Measurable G) :
    ∫⁻ x : U (m + 1) → ℝ, G (symC x) =
      ∫⁻ t : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ y : U m → ℝ, G (blk t b (symC y)) := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : U (m + 1) => ℝ) (idxEquiv m)
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Unit ⊕ (Fin m ⊕ U m) => ℝ)
  have h3 := (volume_preserving_funUnique Unit ℝ).symm
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ U m => ℝ)
  have hm : Measurable fun p : (Unit → ℝ) × (Fin m ⊕ U m → ℝ) =>
      G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
        ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm p))) :=
    hG.comp ((measurable_symC _).comp ((MeasurableEquiv.measurable _).comp
      (MeasurableEquiv.measurable _)))
  calc ∫⁻ x : U (m + 1) → ℝ, G (symC x)
      = ∫⁻ z : Unit ⊕ (Fin m ⊕ U m) → ℝ,
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m) z)) :=
        (h1.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫⁻ p : (Unit → ℝ) × (Fin m ⊕ U m → ℝ),
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm p))) :=
        (h2.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫⁻ u : Unit → ℝ, ∫⁻ w : Fin m ⊕ U m → ℝ,
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm (u, w)))) :=
        lintegral_prod _ hm.aemeasurable
    _ = ∫⁻ t : ℝ, ∫⁻ w : Fin m ⊕ U m → ℝ,
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm
              ((MeasurableEquiv.funUnique Unit ℝ).symm t, w)))) :=
        (h3.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫⁻ t : ℝ, ∫⁻ q : (Fin m → ℝ) × (U m → ℝ),
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm
              ((MeasurableEquiv.funUnique Unit ℝ).symm t,
                (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm q)))) := by
        refine lintegral_congr fun t => ?_
        exact (h4.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫⁻ t : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ y : U m → ℝ,
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm
              ((MeasurableEquiv.funUnique Unit ℝ).symm t,
                (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm (b, y))))) := by
        refine lintegral_congr fun t => ?_
        refine lintegral_prod _ ?_
        exact (hm.comp (measurable_prodMk_left.comp (MeasurableEquiv.measurable _))).aemeasurable
    _ = ∫⁻ t : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ y : U m → ℝ, G (blk t b (symC y)) := by
        refine lintegral_congr fun t => lintegral_congr fun b => lintegral_congr fun y => ?_
        rw [← symC_decomp m t b y]
        congr 3

lemma lintegral_translate (m : ℕ) (G : (Fin m → Fin m → ℝ) → ENNReal)
    (S : Fin m → Fin m → ℝ) (hS : ∀ i j, S i j = S j i) :
    ∫⁻ y : U m → ℝ, G (symC y + S) = ∫⁻ y : U m → ℝ, G (symC y) := by
  have key : ∀ y : U m → ℝ, symC y + S = symC (y + fun p => S p.1.1 p.1.2) := by
    intro y; funext i j
    simp only [symC, Pi.add_apply]
    split_ifs with h
    · rfl
    · rw [hS]
  simp_rw [key]
  exact lintegral_add_right_eq_self (fun y => G (symC y)) _

lemma gaussian (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ b : Fin m → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, b i ^ 2) / t)) =
      ENNReal.ofReal ((Real.pi * t) ^ ((m : ℝ) / 2)) := by
  have hprod : ∀ b : Fin m → ℝ, Real.exp (-(∑ i, b i ^ 2) / t) =
      ∏ i, Real.exp (-t⁻¹ * b i ^ 2) := by
    intro b
    rw [← Real.exp_sum]; congr 1
    rw [neg_div, div_eq_inv_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    simp [neg_mul]
  simp_rw [hprod]
  have hint : Integrable (fun b : Fin m → ℝ => ∏ i, Real.exp (-t⁻¹ * b i ^ 2)) :=
    Integrable.fintype_prod (f := fun _ (v : ℝ) => Real.exp (-t⁻¹ * v ^ 2))
      (fun _ => integrable_exp_neg_mul_sq (inv_pos.2 ht))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun b => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)]
  congr 1
  rw [integral_fintype_prod_volume_eq_pow (fun v : ℝ => Real.exp (-t⁻¹ * v ^ 2)), integral_gaussian,
    Fintype.card_fin, div_inv_eq_mul, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul
      (by positivity)]
  congr 1; ring

lemma gamma_lintegral {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Real.exp (-t) * t ^ (a - 1)) =
      ENNReal.ofReal (Real.Gamma a) := by
  rw [Real.Gamma_eq_integral ha, ofReal_integral_eq_lintegral_ofReal
    (Real.GammaIntegral_convergent ha)]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)

lemma mvGamma_succ (m : ℕ) (a : ℝ) :
    multivariateGamma (m + 1) a =
      Real.pi ^ ((m : ℝ) / 2) * Real.Gamma a * multivariateGamma m (a - 1 / 2) := by
  unfold multivariateGamma
  rw [Fin.prod_univ_succ]
  have hπ : Real.pi ^ (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1) / 4) =
      Real.pi ^ ((m : ℝ) / 2) * Real.pi ^ ((m : ℝ) * ((m : ℝ) - 1) / 4) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; push_cast; ring
  have hG : ∀ i : Fin m, Real.Gamma (a - ((i.succ : Fin (m + 1)) : ℝ) / 2) =
      Real.Gamma (a - 1 / 2 - (i : ℝ) / 2) := by
    intro i; congr 1; simp only [Fin.val_succ]; push_cast; ring
  simp only [hπ, hG, Fin.val_zero, CharP.cast_eq_zero, zero_div, sub_zero]
  ring

lemma mvGamma_nonneg (m : ℕ) (a : ℝ) (ha : ((m : ℝ) - 1) / 2 < a) :
    0 ≤ multivariateGamma m a := by
  unfold multivariateGamma
  refine mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Finset.prod_nonneg fun i _ => ?_)
  refine (Real.Gamma_pos_of_pos ?_).le
  have : (i : ℝ) ≤ (m : ℝ) - 1 := by
    have := i.isLt
    have : (i : ℕ) + 1 ≤ m := this
    have : ((i : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast this
    linarith
  linarith

lemma main (m : ℕ) : ∀ a : ℝ, ((m : ℝ) - 1) / 2 < a →
    ∫⁻ y : U m → ℝ, F m a (symC y) = ENNReal.ofReal (multivariateGamma m a) := by
  induction m with
  | zero =>
    intro a _
    have h1 : ∀ y : U 0 → ℝ, F 0 a (symC y) = 1 := by
      intro y
      have hpd : (Matrix.of (symC y)).PosDef :=
        Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.IsHermitian.ext_iff.2 fun i => i.elim0)
          fun x hx => absurd (Subsingleton.elim x 0) hx
      simp [F, hpd, Matrix.trace]
    simp_rw [h1]
    simp [multivariateGamma, volume_pi, Measure.pi_of_empty]
  | succ m ih =>
    intro a ha
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    push_cast at ha
    have ha' : ((m : ℝ) - 1) / 2 < a - 1 / 2 := by linarith
    have hapos : 0 < a := by linarith
    have hK := mvGamma_nonneg m (a - 1 / 2) ha'
    have inner : ∀ t (b : Fin m → ℝ), ∫⁻ y : U m → ℝ, F (m + 1) a (blk t b (symC y)) =
        if 0 < t then ENNReal.ofReal (Real.exp (-t) * t ^ (a - ((m : ℝ) + 2) / 2)) *
          ENNReal.ofReal (Real.exp (-(∑ i, b i ^ 2) / t)) *
            ENNReal.ofReal (multivariateGamma m (a - 1 / 2)) else 0 := by
      intro t b
      rcases le_or_gt t 0 with ht | ht
      · rw [if_neg (not_lt.2 ht)]
        have : ∀ y, F (m + 1) a (blk t b (symC y)) = 0 := by
          intro y; simp [F, not_posDef_blk ht]
        simp [this]
      · rw [if_pos ht, ← lintegral_translate m (fun B => F (m + 1) a (blk t b B)) (outer t b)
          (fun i j => by simp only [outer]; ring)]
        simp_rw [F_blk a ht]
        rw [lintegral_const_mul (f := fun y => F m (a - 1 / 2) (symC y)) _
          ((measurable_F m _).comp (measurable_symC m)), ih _ ha']
    have outer2 : ∀ t : ℝ, ∫⁻ b : Fin m → ℝ, (if 0 < t then
        ENNReal.ofReal (Real.exp (-t) * t ^ (a - ((m : ℝ) + 2) / 2)) *
          ENNReal.ofReal (Real.exp (-(∑ i, b i ^ 2) / t)) *
            ENNReal.ofReal (multivariateGamma m (a - 1 / 2)) else 0) =
        Set.indicator (Set.Ioi 0) (fun t => ENNReal.ofReal
          (Real.pi ^ ((m : ℝ) / 2) * multivariateGamma m (a - 1 / 2)) *
            ENNReal.ofReal (Real.exp (-t) * t ^ (a - 1))) t := by
      intro t
      rcases le_or_gt t 0 with ht | ht
      · rw [Set.indicator_of_notMem (by simpa using ht)]
        simp [not_lt.2 ht]
      · rw [Set.indicator_of_mem (by simpa using ht)]
        simp only [if_pos ht]
        rw [lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ (by fun_prop), gaussian m ht,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow Real.pi_pos.le ht.le]
        have : t ^ (a - 1) = t ^ (a - ((m : ℝ) + 2) / 2) * t ^ ((m : ℝ) / 2) := by
          rw [← Real.rpow_add ht]; congr 1; ring
        rw [this]; ring
    rw [lintegral_decomp m (F (m + 1) a) (measurable_F _ _)]
    simp_rw [inner, outer2]
    rw [lintegral_indicator measurableSet_Ioi, lintegral_const_mul _ (by fun_prop),
      gamma_lintegral hapos, ← ENNReal.ofReal_mul (by positivity), mvGamma_succ]
    congr 1
    ring

end MvGammaAux

open MuirheadMST in
theorem solution (m : ℕ) (a : ℝ) (ha : ((m : ℝ) - 1) / 2 < a) :
    ∫⁻ A, ENNReal.ofReal
      (if (Matrix.of A).PosDef then
        Real.exp (-(Matrix.of A).trace) * (Matrix.of A).det ^ (a - ((m : ℝ) + 1) / 2)
      else 0) ∂(symVolume m) = ENNReal.ofReal (multivariateGamma m a) := by
  have := MvGammaAux.main m a ha
  change ∫⁻ A, MvGammaAux.F m a A ∂(Measure.map MvGammaAux.symC volume) = _
  rw [lintegral_map (MvGammaAux.measurable_F m a) (MvGammaAux.measurable_symC m)]
  exact this
