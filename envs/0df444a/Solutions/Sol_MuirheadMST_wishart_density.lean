-- Prove2me | solution 1 for MuirheadMST.wishart_density
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T20:47:09.354792+00:00
-- url     : https://prove2.me/submissions/cf61559d-9cb4-4e0b-bc1b-25981fe775b5

import Mathlib
import Definitions.Def_MuirheadMST_Wishart
import Theorems.Thm_MuirheadMST_bartlett_decomposition
import Theorems.Thm_DbarRegularity_lintegral_fun_norm_eq
import Theorems.Thm_PI_AprimeInfG_lintegral_fintype_prod

open MeasureTheory ProbabilityTheory WithLp

open scoped Classical

noncomputable section

namespace WDAux

open MuirheadMST
open scoped Matrix

/-! ### Bartlett side: the recursion for `BLaw` (from the Bartlett decomposition solution) -/

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The law of `‖g‖` for `g` standard Gaussian in `ℝ^k`. -/
def chi (k : ℕ) : Measure ℝ := (stdGaussian (E k)).map (fun x => ‖x‖)

/-- Bartlett's upper-triangular factor from its diagonal `d` and the array `t`. -/
def T {m : ℕ} (d : Fin m → ℝ) (t : Fin m → Fin m → ℝ) (i j : Fin m) : ℝ :=
  if i = j then d i else if i < j then t i j else 0

/-- `TᵀT`. -/
def B {m : ℕ} (d : Fin m → ℝ) (t : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun j k => ∑ i, T d t i j * T d t i k

/-- Bartlett side, with the diagonal entries already replaced by their χ laws. -/
def BLaw (m n : ℕ) : Measure (Fin m → Fin m → ℝ) :=
  ((Measure.pi fun i : Fin m => chi (n - i)).prod
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin m => gaussianReal 0 1)).map
    (fun p => B p.1 p.2)

/-- The block matrix `[[r², r aᵀ], [r a, a aᵀ + M]]`. -/
def H {m : ℕ} (r : ℝ) (a : Fin m → ℝ) (M : Fin m → Fin m → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun j k => Fin.cases (Fin.cases (r ^ 2) (fun k => r * a k) k)
    (fun j => Fin.cases (r * a j) (fun k => a j * a k + M j k) k) j

instance (k : ℕ) : SigmaFinite (stdGaussian (E k)) := IsFiniteMeasure.toSigmaFinite _

instance (k : ℕ) : IsProbabilityMeasure (chi k) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

lemma measurable_B {m : ℕ} : Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin m → ℝ) => B p.1 p.2) := by
  refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k => ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  unfold T
  refine Measurable.mul ?_ ?_ <;> split_ifs <;> fun_prop

lemma measurable_H {m : ℕ} :
    Measurable (fun p : ℝ × (Fin m → ℝ) × (Fin m → Fin m → ℝ) => H p.1 p.2.1 p.2.2) := by
  refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k => ?_
  cases j using Fin.cases <;> cases k using Fin.cases <;>
    simp only [H, Fin.cases_zero, Fin.cases_succ] <;> fun_prop

instance (m n : ℕ) : IsProbabilityMeasure (BLaw m n) :=
  Measure.isProbabilityMeasure_map measurable_B.aemeasurable

lemma rearr {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (A × B) × (C × D) => (p.1.1, (p.2.1, (p.1.2, p.2.2))))
      ((μa.prod μb).prod (μc.prod μd)) (μa.prod (μc.prod (μb.prod μd))) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  exact (h4.comp (h3.comp (h2.comp h1)))

lemma tail_mp (m : ℕ) :
    MeasurePreserving (fun (r : Fin (m + 1) → ℝ) (k : Fin m) => r k.succ)
      (Measure.pi fun _ => gaussianReal 0 1) (Measure.pi fun _ => gaussianReal 0 1) := by
  have h := (measurePreserving_snd (μ := gaussianReal 0 1)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0)
  convert h using 1
  funext r k
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail]

lemma Φ1_mp (m n : ℕ) :
    MeasurePreserving (fun (d : Fin (m + 1) → ℝ) => (d 0, fun i : Fin m => d i.succ))
      (Measure.pi fun i : Fin (m + 1) => chi (n + 1 - i))
      ((chi (n + 1)).prod (Measure.pi fun i : Fin m => chi (n - i))) := by
  have h := measurePreserving_piFinSuccAbove (fun i : Fin (m + 1) => chi (n + 1 - i)) 0
  have e2 : (fun j : Fin m => chi (n + 1 - ((Fin.succAbove 0 j : Fin (m + 1)) : ℕ))) =
      fun j : Fin m => chi (n - (j : ℕ)) := by
    funext j
    simp
  simp only [Fin.val_zero, Nat.sub_zero, e2] at h
  convert h using 1
  funext d
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  rfl

lemma Φ2_mp (m : ℕ) :
    MeasurePreserving
      (fun (t : Fin (m + 1) → Fin (m + 1) → ℝ) =>
        ((fun k : Fin m => t 0 k.succ), fun (i k : Fin m) => t i.succ k.succ))
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      ((Measure.pi fun _ => gaussianReal 0 1).prod
        (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)) := by
  have h := ((tail_mp m).prod (measurePreserving_pi _ _ fun _ : Fin m => tail_mp m)).comp
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) 0)
  convert h using 1
  funext t
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail]

lemma B_succ {m : ℕ} (d : Fin (m + 1) → ℝ) (t : Fin (m + 1) → Fin (m + 1) → ℝ) :
    B d t = H (d 0) (fun k => t 0 k.succ) (B (fun i => d i.succ) (fun i k => t i.succ k.succ)) := by
  have h00 : T d t 0 0 = d 0 := by simp [T]
  have hs0 : ∀ i : Fin m, T d t i.succ 0 = 0 := fun i => by
    simp [T, Fin.succ_ne_zero, (Fin.succ_pos i).not_gt]
  have h0s : ∀ k : Fin m, T d t 0 k.succ = t 0 k.succ := fun k => by
    simp [T, (Fin.succ_ne_zero k).symm, Fin.succ_pos k]
  have hss : ∀ i k : Fin m, T d t i.succ k.succ =
      T (fun i => d i.succ) (fun i k => t i.succ k.succ) i k := fun i k => by
    simp [T, Fin.succ_inj, Fin.succ_lt_succ_iff]
  funext j k
  cases j using Fin.cases <;> cases k using Fin.cases <;>
    simp only [B, H, Fin.cases_zero, Fin.cases_succ, Fin.sum_univ_succ, h00, hs0, h0s, hss,
      zero_mul, mul_zero, Finset.sum_const_zero, add_zero] <;> ring

lemma prod_map_right {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] {g : Y → Z} (hg : Measurable g) :
    μ.prod (ν.map g) = (μ.prod ν).map (Prod.map id g) := by
  rw [← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id]

lemma BLaw_succ (m n : ℕ) :
    BLaw (m + 1) (n + 1) = ((chi (n + 1)).prod
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (BLaw m n))).map
        (fun p => H p.1 p.2.1 p.2.2) := by
  have hΨ := (rearr _ _ _ _).comp ((Φ1_mp m n).prod (Φ2_mp m))
  rw [BLaw, BLaw, prod_map_right _ _ measurable_B, prod_map_right _ _ (measurable_id.prodMap measurable_B),
    Measure.map_map measurable_H (measurable_id.prodMap (measurable_id.prodMap measurable_B)),
    ← hΨ.map_eq, Measure.map_map
      (measurable_H.comp (measurable_id.prodMap (measurable_id.prodMap measurable_B)))
      hΨ.measurable]
  congr 1
  funext p
  exact B_succ p.1 p.2


lemma bartlett_eq_BLaw (m n : ℕ) :
    (bartlettLaw m n).map (fun ω j k => ∑ i, bartlettFactor ω i j * bartlettFactor ω i k) =
      BLaw m n := by
  have hn : (Measure.pi fun i : Fin m => stdGaussian (E (n - i))).map (fun g i => ‖g i‖) =
      Measure.pi fun i : Fin m => chi (n - i) := by
    have : ∀ i : Fin m, SigmaFinite ((stdGaussian (E (n - i))).map (fun x => ‖x‖)) :=
      fun i => inferInstanceAs (SigmaFinite (chi (n - i)))
    exact Measure.pi_map_pi (fun i => measurable_norm.aemeasurable)
  have hm : Measurable (fun (g : ∀ i : Fin m, E (n - i)) i => ‖g i‖) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).norm
  rw [BLaw, ← hn, ← Measure.map_id (μ := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin m =>
      gaussianReal 0 1), Measure.map_prod_map _ _ hm measurable_id,
    Measure.map_map measurable_B (hm.prodMap measurable_id)]
  rfl


/-! ### Upper-triangle coordinates and Schur blocks (from the `Γ_m` integral solution) -/

/-- Upper-triangle index set. -/
abbrev U (m : ℕ) := {p : Fin m × Fin m // p.1 ≤ p.2}

/-- Symmetric completion of upper-triangular entries. -/
def symC {m : ℕ} (a : U m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), le_of_not_ge h⟩

lemma measurable_symC (m : ℕ) : Measurable (symC (m := m)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold symC
  split_ifs <;> exact measurable_pi_apply _

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


/-! ### Densities of the building blocks -/

open scoped ENNReal

/-- Normalising constant of the `W_m(n, I)` density. -/
def cst (m n : ℕ) : ℝ := (2 ^ ((m : ℝ) * n / 2) * multivariateGamma m ((n : ℝ) / 2))⁻¹

/-- The `W_m(n, I)` density with respect to `symVolume m`. -/
def f1 (m n : ℕ) (A : Fin m → Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (if (Matrix.of A).PosDef then
    cst m n * Real.exp (-(1 / 2) * (Matrix.of A).trace) * (Matrix.of A).det ^ (((n : ℝ) - m - 1) / 2)
  else 0)

lemma measurable_f1 (m n : ℕ) : Measurable (f1 m n) := by
  have hdet : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).det :=
    continuous_id.matrix_det
  have htr : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]; fun_prop
  refine Measurable.ennreal_ofReal (Measurable.ite (measurableSet_posDef m) ?_ measurable_const)
  exact (measurable_const.mul (measurable_const.mul htr.measurable).exp).mul
    (hdet.measurable.pow_const _)

/-- Density of `N(0, I_k)` on `Fin k → ℝ`. -/
def gdens (k : ℕ) (x : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-(∑ i, x i ^ 2) / 2))

lemma measurable_gdens {k : ℕ} : Measurable (gdens k) := by
  unfold gdens; exact Measurable.ennreal_ofReal (by fun_prop)

lemma gauss_pi (k : ℕ) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1) = volume.withDensity (gdens k) := by
  have hg : ∀ x : Fin k → ℝ, gdens k x = ∏ i, gaussianPDF 0 1 (x i) := by
    intro x
    simp only [gdens, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    · rw [NNReal.coe_one, mul_one, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg_one,
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
      congr 1; ring
    · rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      simp [neg_div]
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (gdens k) =
      fun x => ∏ i, (s i).indicator (gaussianPDF 0 1) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx, hg x]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ _)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, volume_pi, PI.AprimeInfG.lintegral_fintype_prod (fun _ => (s _).indicator _)
    (fun i => (measurable_gaussianPDF 0 1).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply 0 one_ne_zero, lintegral_indicator (hs i)]

/-- Normalising constant of the χ law with `k` degrees of freedom. -/
def cchi (k : ℕ) : ℝ := (2 ^ ((k : ℝ) / 2 - 1) * Real.Gamma ((k : ℝ) / 2))⁻¹

lemma cchi_pos (k : ℕ) (hk : 0 < k) : 0 < cchi k := by
  unfold cchi
  have : (0 : ℝ) < (k : ℝ) / 2 := by positivity
  exact inv_pos.2 (mul_pos (by positivity) (Real.Gamma_pos_of_pos this))

lemma chi_J (k : ℕ) (hk : 0 < k) :
    ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r ^ (k - 1) * Real.exp (-r ^ 2 / 2)) =
      ENNReal.ofReal (2 ^ ((k : ℝ) / 2 - 1) * Real.Gamma ((k : ℝ) / 2)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : (-1 : ℝ) < (k : ℝ) - 1 := by linarith
  have hfun : ∀ r ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ (k - 1) * Real.exp (-r ^ 2 / 2)) =
      ENNReal.ofReal (r ^ ((k : ℝ) - 1) * Real.exp (-(1 / 2) * r ^ (2 : ℝ))) := by
    intro r _
    congr 2
    · rw [← Real.rpow_natCast]; congr 1; rw [Nat.cast_sub hk]; simp
    · congr 1; rw [Real.rpow_two]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hfun,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_rpow_mul_exp_neg_mul_rpow hq two_pos (by norm_num))
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt hr) _) (Real.exp_pos _).le)),
    integral_rpow_mul_exp_neg_mul_rpow two_pos hq (by norm_num)]
  congr 1
  have e1 : ((k : ℝ) - 1 + 1) / 2 = (k : ℝ) / 2 := by ring
  have e2 : -((k : ℝ) - 1 + 1) / 2 = -((k : ℝ) / 2) := by ring
  rw [e1, e2, Real.rpow_sub_one two_ne_zero, one_div, Real.inv_rpow (by norm_num), Real.rpow_neg
    (by norm_num), inv_inv]
  ring

lemma lint_norm (k : ℕ) (hk : 0 < k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ‖x‖ ∂stdGaussian (E k) =
      (k * volume (Metric.ball (0 : E k) 1) * ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2))) *
        ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r ^ (k - 1) * Real.exp (-r ^ 2 / 2)) * F r := by
  set G : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-r ^ 2 / 2)) * F r with hGdef
  have hG : Measurable G := by
    refine Measurable.mul ?_ hF
    exact Measurable.ennreal_ofReal (by fun_prop)
  have hgd : Measurable (gdens k) := by
    unfold gdens; exact Measurable.ennreal_ofReal (by fun_prop)
  rw [← map_pi_eq_stdGaussian, lintegral_map (f := fun x : E k => F ‖x‖) (hF.comp measurable_norm) (by fun_prop), gauss_pi,
    lintegral_withDensity_eq_lintegral_mul _ hgd
      (show Measurable (fun a : Fin k → ℝ => F ‖toLp 2 a‖) from
        hF.comp (measurable_norm.comp (by fun_prop)))]
  have h1 : (gdens k * fun a : Fin k → ℝ => F ‖toLp 2 a‖) = fun y => G ‖toLp 2 y‖ := by
    funext y
    have hn : ‖toLp 2 y‖ ^ 2 = ∑ i, y i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Pi.mul_apply, gdens, hGdef, hn]
  rw [h1]
  rw [show (∫⁻ a : Fin k → ℝ, (fun y => G ‖toLp 2 y‖) a) = ∫⁻ a : Fin k → ℝ, (G ∘ norm) (toLp 2 a)
    from rfl, (PiLp.volume_preserving_toLp (Fin k)).lintegral_comp (hG.comp measurable_norm)]
  change ∫⁻ x : EuclideanSpace ℝ (Fin k), G ‖x‖ = _
  rw [DbarRegularity.lintegral_fun_norm_eq hk G hG, mul_assoc (_ * _),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  simp only [hGdef]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  ring

lemma chi_eq (k : ℕ) (hk : 0 < k) :
    chi k = (volume.restrict (Set.Ioi 0)).withDensity
      (fun r => ENNReal.ofReal (cchi k * r ^ (k - 1) * Real.exp (-r ^ 2 / 2))) := by
  set Z := (k * volume (Metric.ball (0 : E k) 1) *
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k : ℝ) / 2))) with hZdef
  have hchi : ∀ s, MeasurableSet s → chi k s =
      Z * ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r ^ (k - 1) * Real.exp (-r ^ 2 / 2)) *
        s.indicator 1 r := by
    intro s hs
    rw [chi, Measure.map_apply measurable_norm hs, ← lintegral_indicator_one (measurable_norm hs)]
    rw [← lint_norm k hk _ (measurable_one.indicator hs)]
    rfl
  have hZ : Z = ENNReal.ofReal (cchi k) := by
    have h := hchi Set.univ MeasurableSet.univ
    simp only [measure_univ, Set.indicator_univ, Pi.one_apply, mul_one, chi_J k hk] at h
    have hpos : 0 < 2 ^ ((k : ℝ) / 2 - 1) * Real.Gamma ((k : ℝ) / 2) :=
      mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))
    rw [ENNReal.eq_inv_of_mul_eq_one_left h.symm, ← ENNReal.ofReal_inv_of_pos hpos, cchi]
  ext s hs
  rw [hchi s hs, hZ, withDensity_apply _ hs, ← lintegral_indicator hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun r => ?_
  by_cases hr : r ∈ s
  · simp only [Set.indicator_of_mem hr, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_mul (cchi_pos k hk).le]; ring_nf
  · simp [Set.indicator_of_notMem hr]

lemma lintegral_smul_eq {m : ℕ} {r : ℝ} (hr : r ≠ 0) (Q : (Fin m → ℝ) → ℝ≥0∞) :
    ∫⁻ a, Q (r • a) = ENNReal.ofReal (|r ^ m|⁻¹) * ∫⁻ b, Q b := by
  let e := (Homeomorph.smulOfNeZero (α := Fin m → ℝ) r hr).toMeasurableEquiv
  have h1 : ∫⁻ a, Q (r • a) = ∫⁻ a, Q (e a) := rfl
  rw [h1, ← lintegral_map_equiv Q e]
  have h2 : Measure.map (⇑e) (volume : Measure (Fin m → ℝ)) = Measure.map (r • ·) volume := rfl
  rw [h2, Measure.map_addHaar_smul volume hr, lintegral_smul_measure, Module.finrank_fin_fun,
    abs_inv, smul_eq_mul]

/-! ### Step 1: the density of `W_m(n, I)` -/

instance (m : ℕ) : SFinite (symVolume m) := by unfold symVolume; infer_instance

lemma H_eq_blk {m : ℕ} {r : ℝ} (hr : r ≠ 0) (a : Fin m → ℝ) (M : Fin m → Fin m → ℝ) :
    H r a M = blk (r ^ 2) (r • a) (M + outer (r ^ 2) (r • a)) := by
  funext j k
  cases j using Fin.cases <;> cases k using Fin.cases <;>
    simp [H, blk, outer, Pi.smul_apply] <;> field_simp <;> ring

/-- The constant relating `cst (m+1) (n+1)` and `cst m n`. -/
def K (m n : ℕ) : ℝ := cchi (n + 1) * (2 * Real.pi) ^ (-(m : ℝ) / 2) / 2

lemma cst_succ (m n : ℕ) : cst (m + 1) (n + 1) = K m n * cst m n := by
  rw [cst, cst, K, cchi, mvGamma_succ]
  have ha : ((n + 1 : ℕ) : ℝ) / 2 - 1 / 2 = (n : ℝ) / 2 := by push_cast; ring
  have h2 : (2 : ℝ) ^ (((m + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) / 2) =
      2 ^ ((m : ℝ) * n / 2) * 2 ^ (((n + 1 : ℕ) : ℝ) / 2 - 1) * 2 ^ ((m : ℝ) / 2) * 2 := by
    rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos, ← Real.rpow_add_one two_ne_zero]
    congr 1; push_cast; ring
  have h3 : (2 * Real.pi) ^ (-(m : ℝ) / 2) = (2 ^ ((m : ℝ) / 2))⁻¹ * (Real.pi ^ ((m : ℝ) / 2))⁻¹ := by
    rw [Real.mul_rpow (by norm_num) Real.pi_pos.le, neg_div, Real.rpow_neg (by norm_num),
      Real.rpow_neg Real.pi_pos.le]
  rw [ha, h2, h3]
  simp only [mul_inv]
  ring

/-- The factor of the `(m+1)`-density in the coordinates `(t, b, C)`. -/
def κ (m n : ℕ) (t : ℝ) (b : Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (K m n * Real.exp (-t / 2) * t ^ (((n : ℝ) - m - 1) / 2) *
    Real.exp (-(∑ i, b i ^ 2) / (2 * t)))

lemma K_pos (m n : ℕ) : 0 < K m n := by
  unfold K
  have := cchi_pos (n + 1) (by omega)
  positivity

lemma f1_blk {m n : ℕ} {t : ℝ} (ht : 0 < t) (b : Fin m → ℝ)
    (C : Fin m → Fin m → ℝ) :
    f1 (m + 1) (n + 1) (blk t b (C + outer t b)) = κ m n t b * f1 m n C := by
  unfold f1 κ
  rw [posDef_blk_iff ht, det_blk ht, trace_blk ht]
  split_ifs with h
  · have hd := h.det_pos
    have hK := K_pos m n
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow ht.le hd.le, cst_succ]
    have e1 : (((n + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ) - 1) / 2 = ((n : ℝ) - m - 1) / 2 := by
      push_cast; ring
    rw [e1]
    have : Real.exp (-(1 / 2) * (t + (Matrix.of C).trace + (∑ i, b i ^ 2) / t)) =
        Real.exp (-t / 2) * Real.exp (-(∑ i, b i ^ 2) / (2 * t)) *
          Real.exp (-(1 / 2) * (Matrix.of C).trace) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
    rw [this]; ring
  · simp

/-- The inner integral over the Schur complement. -/
def Φ (m n : ℕ) (s : Set (Fin (m + 1) → Fin (m + 1) → ℝ)) (t : ℝ) (b : Fin m → ℝ) : ℝ≥0∞ :=
  ∫⁻ y : U m → ℝ, f1 m n (symC y) * s.indicator 1 (blk t b (symC y + outer t b))

lemma step1_rhs {m n : ℕ} {s : Set (Fin (m + 1) → Fin (m + 1) → ℝ)}
    (hs : MeasurableSet s) :
    (symVolume (m + 1)).withDensity (f1 (m + 1) (n + 1)) s =
      ∫⁻ t in Set.Ioi 0, ∫⁻ b, κ m n t b * Φ m n s t b := by
  have hmf := (measurable_f1 (m + 1) (n + 1)).indicator hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs]
  change ∫⁻ A, s.indicator (f1 (m + 1) (n + 1)) A ∂(Measure.map symC volume) = _
  rw [lintegral_map hmf (measurable_symC _), lintegral_decomp m _ hmf]
  have inner : ∀ t (b : Fin m → ℝ), ∫⁻ y : U m → ℝ, s.indicator (f1 (m + 1) (n + 1))
      (blk t b (symC y)) = (Set.Ioi 0).indicator (fun t => κ m n t b * Φ m n s t b) t := by
    intro t b
    rcases le_or_gt t 0 with ht | ht
    · rw [Set.indicator_of_notMem (by simpa using ht)]
      have : ∀ y : U m → ℝ, s.indicator (f1 (m + 1) (n + 1)) (blk t b (symC y)) = 0 := by
        intro y
        have h0 : f1 (m + 1) (n + 1) (blk t b (symC y)) = 0 := by
          simp [f1, not_posDef_blk ht]
        by_cases hy : blk t b (symC y) ∈ s
        · rw [Set.indicator_of_mem hy, h0]
        · rw [Set.indicator_of_notMem hy]
      simp [this]
    · rw [Set.indicator_of_mem (by simpa using ht), ← lintegral_translate m
        (fun B => s.indicator (f1 (m + 1) (n + 1)) (blk t b B)) (outer t b)
        (fun i j => by simp only [outer]; ring), Φ, κ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun y => ?_
      by_cases hy : blk t b (symC y + outer t b) ∈ s
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, f1_blk ht, Pi.one_apply, mul_one, κ]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero, mul_zero]
  have outer2 : ∀ t, ∫⁻ b : Fin m → ℝ, ∫⁻ y : U m → ℝ, s.indicator (f1 (m + 1) (n + 1))
      (blk t b (symC y)) = (Set.Ioi 0).indicator (fun t => ∫⁻ b, κ m n t b * Φ m n s t b) t := by
    intro t
    simp_rw [inner]
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem ht]
    · simp only [Set.indicator_of_notMem ht, lintegral_zero]
  simp_rw [outer2]
  rw [lintegral_indicator measurableSet_Ioi]

lemma lhs_pointwise {m n : ℕ} {r : ℝ} (hr : 0 < r) (b : Fin m → ℝ) :
    ENNReal.ofReal (cchi (n + 1) * r ^ (n + 1 - 1) * Real.exp (-r ^ 2 / 2)) *
      ENNReal.ofReal (|r ^ m|⁻¹) * gdens m (r⁻¹ • b) = ENNReal.ofReal (2 * r) * κ m n (r ^ 2) b := by
  have hc := cchi_pos (n + 1) (by omega)
  have hK := K_pos m n
  unfold gdens κ
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hsum : ∑ i, (r⁻¹ • b) i ^ 2 = (∑ i, b i ^ 2) / r ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hp : (r ^ 2) ^ (((n : ℝ) - m - 1) / 2) = r ^ n / r ^ m / r := by
    rw [show (r ^ 2 : ℝ) = r ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hr.le,
      show 2 * (((n : ℝ) - m - 1) / 2) = (n : ℝ) - m - 1 by ring, Real.rpow_sub hr,
      Real.rpow_sub hr, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_one]
  have he : -((∑ i, b i ^ 2) / r ^ 2) / 2 = -(∑ i, b i ^ 2) / (2 * r ^ 2) := by
    field_simp
  rw [hsum, hp, he, Nat.add_sub_cancel, abs_of_pos (pow_pos hr m), K]
  field_simp

lemma step1_lhs {m n : ℕ} {s : Set (Fin (m + 1) → Fin (m + 1) → ℝ)}
    (hs : MeasurableSet s) :
    ((chi (n + 1)).prod ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
      ((symVolume m).withDensity (f1 m n)))).map (fun p => H p.1 p.2.1 p.2.2) s =
      ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (2 * r) * ∫⁻ b, κ m n (r ^ 2) b * Φ m n s (r ^ 2) b := by
  have hHs := measurable_H hs
  rw [Measure.map_apply measurable_H hs, ← lintegral_indicator_one hHs,
    lintegral_prod _ (measurable_one.indicator hHs).aemeasurable]
  have hin : ∀ r, ∫⁻ q, Set.indicator
      ((fun p : ℝ × (Fin m → ℝ) × (Fin m → Fin m → ℝ) => H p.1 p.2.1 p.2.2) ⁻¹' s)
        (1 : ℝ × (Fin m → ℝ) × (Fin m → Fin m → ℝ) → ℝ≥0∞) (r, q) ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
        ((symVolume m).withDensity (f1 m n))) =
      ∫⁻ a, gdens m a * ∫⁻ y : U m → ℝ, f1 m n (symC y) * s.indicator 1 (H r a (symC y)) := by
    intro r
    have hm : Measurable fun q : (Fin m → ℝ) × (Fin m → Fin m → ℝ) =>
        s.indicator (1 : (Fin (m + 1) → Fin (m + 1) → ℝ) → ℝ≥0∞) (H r q.1 q.2) :=
      (measurable_one.indicator hs).comp (measurable_H.comp (measurable_const.prodMk measurable_id))
    have e : ∀ q : (Fin m → ℝ) × (Fin m → Fin m → ℝ),
        ((fun p : ℝ × (Fin m → ℝ) × (Fin m → Fin m → ℝ) => H p.1 p.2.1 p.2.2) ⁻¹' s).indicator 1
          (r, q) = s.indicator (1 : (Fin (m + 1) → Fin (m + 1) → ℝ) → ℝ≥0∞) (H r q.1 q.2) := by
      intro q
      by_cases hq : H r q.1 q.2 ∈ s
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show (r, q) ∈ _ from hq)]; rfl
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (show (r, q) ∉ _ from hq)]
    simp_rw [e]
    rw [lintegral_prod _ hm.aemeasurable, gauss_pi,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ measurable_gdens
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr fun a => ?_
    rw [Pi.mul_apply]
    congr 1
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_f1 m n)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    change ∫⁻ M, ((f1 m n * fun M => s.indicator 1 (H r a M) :
      (Fin m → Fin m → ℝ) → ℝ≥0∞)) M ∂(Measure.map symC volume) = _
    have hmM : Measurable ((f1 m n * fun M => s.indicator 1 (H r a M) :
        (Fin m → Fin m → ℝ) → ℝ≥0∞)) :=
      (measurable_f1 m n).mul ((measurable_one.indicator hs).comp
        (measurable_H.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))))
    rw [lintegral_map hmM (measurable_symC m)]
    rfl
  simp_rw [hin]
  rw [chi_eq (n + 1) (by omega), lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  simp only [Pi.mul_apply]
  have h1 : ∀ a : Fin m → ℝ, gdens m a * ∫⁻ y : U m → ℝ, f1 m n (symC y) *
      s.indicator 1 (H r a (symC y)) =
      (fun b => gdens m (r⁻¹ • b) * Φ m n s (r ^ 2) b) (r • a) := by
    intro a
    simp only [inv_smul_smul₀ hr'.ne', Φ, H_eq_blk hr'.ne']
  rw [lintegral_congr h1, lintegral_smul_eq hr'.ne' (fun b => gdens m (r⁻¹ • b) * Φ m n s (r ^ 2) b),
    ← mul_assoc, ← lintegral_const_mul' _ _ (by finiteness),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun b => ?_
  rw [← mul_assoc, ← mul_assoc, lhs_pointwise hr' b]

lemma sq_subst (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioi 0, F t = ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (2 * r) * F (r ^ 2) := by
  have himg : (fun r : ℝ => r ^ 2) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨r, hr, rfl⟩; positivity
    · intro ht
      exact ⟨Real.sqrt t, Real.sqrt_pos.2 ht, Real.sq_sqrt ht.le⟩
  have hd : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * x) (Set.Ioi 0) x := by
    intro x _
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : Set.InjOn (fun r : ℝ => r ^ 2) (Set.Ioi 0) := by
    intro x hx y hy hxy
    simp only at hxy
    nlinarith [Set.mem_Ioi.1 hx, Set.mem_Ioi.1 hy]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj F, himg]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [abs_of_pos (by have := Set.mem_Ioi.1 hx; positivity)]

lemma step1_zero (n : ℕ) : BLaw 0 n = (symVolume 0).withDensity (f1 0 n) := by
  have hf : ∀ A : Fin 0 → Fin 0 → ℝ, f1 0 n A = 1 := by
    intro A
    have hpd : (Matrix.of A).PosDef :=
      Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.IsHermitian.ext_iff.2 fun i => i.elim0)
        fun x hx => absurd (Subsingleton.elim x 0) hx
    simp [f1, hpd, Matrix.trace, cst, multivariateGamma]
  have hsv : symVolume 0 Set.univ = 1 := by
    change Measure.map symC volume Set.univ = 1
    rw [Measure.map_apply (measurable_symC 0) MeasurableSet.univ]
    simp [volume_pi, Measure.pi_of_empty]
  ext s hs
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
  · simp
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    subst this
    simp [withDensity_apply, hf, hsv]

theorem step1 : ∀ m n, m ≤ n → BLaw m n = (symVolume m).withDensity (f1 m n) := by
  intro m
  induction m with
  | zero => intro n _; exact step1_zero n
  | succ m ih =>
    intro n' hmn
    obtain ⟨n, rfl⟩ : ∃ n, n' = n + 1 := ⟨n' - 1, by omega⟩
    have hmn' : m ≤ n := by omega
    rw [BLaw_succ, ih n hmn']
    ext s hs
    rw [step1_lhs hs, step1_rhs hs]
    exact (sq_subst (fun t => ∫⁻ b, κ m n t b * Φ m n s t b)).symm

lemma wishart_one {m n : ℕ} (hmn : m ≤ n) :
    wishart m n 1 = (symVolume m).withDensity (f1 m n) := by
  rw [← bartlett_decomposition m n hmn, bartlett_eq_BLaw, step1 m n hmn]

/-! ### Step 2: general `S` by the congruence `A ↦ P A Pᵀ` with `P S Pᵀ = 1`, `P` lower triangular -/

/-- `A ↦ P A Pᵀ` on arrays. -/
def congrA {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (A : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => (P * Matrix.of A * Pᵀ) i j

lemma measurable_congrA {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) : Measurable (congrA P) := by
  unfold congrA
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
  fun_prop

lemma congrA_congrA {m : ℕ} (P V : Matrix (Fin m) (Fin m) ℝ) (A : Fin m → Fin m → ℝ) :
    congrA V (congrA P A) = congrA (V * P) A := by
  have h : Matrix.of (congrA P A) = P * Matrix.of A * Pᵀ := rfl
  funext i j
  simp only [congrA]
  rw [h, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

lemma exists_P {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef) :
    ∃ P : Matrix (Fin m) (Fin m) ℝ, (∀ i j, i < j → P i j = 0) ∧ P * S * Pᵀ = 1 := by
  set W := LDL.lowerInv hS with hW
  have hD : LDL.diag hS = W * S * Wᵀ := by
    rw [LDL.diag_eq_lowerInv_conj, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hDpd : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit (isUnit_of_invertible W))
  have hd : ∀ i, 0 < LDL.diagEntries hS i := by
    intro i
    have := hDpd.diag_pos (i := i)
    simpa [LDL.diag] using this
  refine ⟨Matrix.diagonal (fun i => (Real.sqrt (LDL.diagEntries hS i))⁻¹) * W, ?_, ?_⟩
  · intro i j hij
    rw [Matrix.diagonal_mul, hW, LDL.lowerInv_triangular hS hij, mul_zero]
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc S, ← Matrix.mul_assoc W, ← Matrix.mul_assoc W, ← hD, LDL.diag, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h1 := hd i
    have h2 := Real.sq_sqrt h1.le
    have h3 : 0 < Real.sqrt (LDL.diagEntries hS i) := Real.sqrt_pos.2 h1
    field_simp
    linarith

open scoped MatrixOrder in
lemma gauss_lin {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : P * S * Pᵀ = 1) :
    (multivariateGaussian 0 S).map (Matrix.toEuclideanLin P) = stdGaussian (E m) := by
  set R := CFC.sqrt S with hRdef
  have hS0 : (0 : Matrix (Fin m) (Fin m) ℝ) ≤ S := by
    exact hS.posSemidef.nonneg
  have hRR : R * R = S := by
    exact CFC.sqrt_mul_sqrt_self S hS0
  have hRt : Rᵀ = R := by
    have h := (CFC.sqrt_nonneg S).isSelfAdjoint
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set Q := P * R with hQdef
  have hQ : Q * Qᵀ = 1 := by
    rw [hQdef, Matrix.transpose_mul, hRt, Matrix.mul_assoc, ← Matrix.mul_assoc R, hRR,
      ← Matrix.mul_assoc, hP]
  have hQ' : Qᵀ * Q = 1 := mul_eq_one_comm.1 hQ
  let L : E m ≃ₗ[ℝ] E m := LinearEquiv.ofLinear (Matrix.toEuclideanLin Q)
    (Matrix.toEuclideanLin Qᵀ)
    (LinearMap.ext fun x => by
      change toLp 2 (Q *ᵥ (Qᵀ *ᵥ ofLp x)) = x
      rw [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec])
    (LinearMap.ext fun x => by
      change toLp 2 (Qᵀ *ᵥ (Q *ᵥ ofLp x)) = x
      rw [Matrix.mulVec_mulVec, hQ', Matrix.one_mulVec])
  have hinner : ∀ x y : E m, inner ℝ (L x) (L y) = inner ℝ x y := by
    intro x y
    change inner ℝ (toLp 2 (Q *ᵥ ofLp x)) (toLp 2 (Q *ᵥ ofLp y)) = inner ℝ x y
    rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hQ',
      Matrix.vecMul_one]
  let Q' : E m ≃ₗᵢ[ℝ] E m := L.isometryOfInner hinner
  have hcomp : (fun y => Matrix.toEuclideanLin P y) ∘
      (fun x => (0 : E m) + Matrix.toEuclideanCLM (𝕜 := ℝ) R x) = ⇑Q' := by
    funext x
    simp only [Function.comp_apply, zero_add, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    change toLp 2 (P *ᵥ (R *ᵥ ofLp x)) = toLp 2 (Q *ᵥ ofLp x)
    rw [Matrix.mulVec_mulVec]
  rw [multivariateGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  · rw [hcomp, stdGaussian_map]

lemma wishart_map {m n : ℕ} {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : P * S * Pᵀ = 1) :
    (wishart m n S).map (congrA P) = wishart m n 1 := by
  have hgm : Measurable (gram : (Fin n → E m) → Fin m → Fin m → ℝ) := by
    unfold gram; fun_prop
  have hL : Measurable (Matrix.toEuclideanLin P : E m → E m) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hcomp : congrA P ∘ gram = gram ∘ (fun (Z : Fin n → E m) i => Matrix.toEuclideanLin P (Z i)) := by
    funext Z j k
    simp only [Function.comp_apply, congrA, gram, Matrix.mul_apply, Matrix.of_apply,
      Matrix.transpose_apply]
    change _ = ∑ i, (P *ᵥ ofLp (Z i)) j * (P *ᵥ ofLp (Z i)) k
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun a _ => ?_
    ring
  have : ∀ _ : Fin n, SigmaFinite ((multivariateGaussian (0 : E m) S).map
      (Matrix.toEuclideanLin P)) := fun _ => by
    rw [gauss_lin hS hP]; infer_instance
  rw [wishart, wishart, normalDataMatrix, normalDataMatrix, Measure.map_map (measurable_congrA P) hgm,
    hcomp, ← Measure.map_map hgm (by fun_prop),
    Measure.pi_map_pi (f := fun _ => (Matrix.toEuclideanLin P : E m → E m))
      (fun _ => hL.aemeasurable)]
  simp_rw [gauss_lin hS hP, multivariateGaussian_zero_one]

/-- `A ↦ P A Pᵀ` in upper-triangle coordinates. -/
lemma symC_add {m : ℕ} (x y : U m → ℝ) : symC (x + y) = symC x + symC y := by
  funext i j; simp only [symC, Pi.add_apply]; split_ifs <;> rfl

lemma symC_smul {m : ℕ} (c : ℝ) (x : U m → ℝ) : symC (c • x) = c • symC x := by
  funext i j; simp only [symC, Pi.smul_apply]; split_ifs <;> rfl

lemma symC_symm {m : ℕ} (x : U m → ℝ) (i j : Fin m) : symC x i j = symC x j i := by
  simp only [symC]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [dif_pos h.le, dif_neg (not_le.2 h)]
  · rfl
  · rw [dif_neg (not_le.2 h), dif_pos h.le]

lemma congrA_add {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (A B : Fin m → Fin m → ℝ) :
    congrA P (A + B) = congrA P A + congrA P B := by
  funext i j
  simp only [congrA, Pi.add_apply]
  rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.mul_add, Matrix.add_mul]
  rfl

lemma congrA_smul {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) (A : Fin m → Fin m → ℝ) :
    congrA P (c • A) = c • congrA P A := by
  funext i j
  simp only [congrA, Pi.smul_apply]
  rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.mul_smul, Matrix.smul_mul]
  rfl

def τ {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) : (U m → ℝ) →ₗ[ℝ] (U m → ℝ) where
  toFun x p := congrA P (symC x) p.1.1 p.1.2
  map_add' x y := by funext p; simp [symC_add, congrA_add]
  map_smul' c x := by funext p; simp [symC_smul, congrA_smul]

lemma symC_τ {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (x : U m → ℝ) :
    symC (τ P x) = congrA P (symC x) := by
  have hsym : ∀ i j, congrA P (symC x) i j = congrA P (symC x) j i := by
    intro i j
    simp only [congrA, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [symC_symm x k l]; ring
  funext i j
  simp only [symC, τ, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · rfl
  · exact hsym j i

lemma symC_single_ne {m : ℕ} {q : U m} {a b : Fin m} (h : symC (Pi.single q (1 : ℝ)) a b ≠ 0) :
    (a = q.1.1 ∧ b = q.1.2) ∨ (a = q.1.2 ∧ b = q.1.1) := by
  simp only [symC] at h
  split_ifs at h with hab
  · left
    have hq : (⟨(a, b), hab⟩ : U m) = q := by
      by_contra hne; exact h (Pi.single_eq_of_ne hne _)
    subst hq; exact ⟨rfl, rfl⟩
  · right
    have hq : (⟨(b, a), le_of_not_ge hab⟩ : U m) = q := by
      by_contra hne; exact h (Pi.single_eq_of_ne hne _)
    subst hq; exact ⟨rfl, rfl⟩

lemma τ_apply {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (x : U m → ℝ) (p : U m) :
    τ P x p = ∑ b, ∑ a, P p.1.1 a * symC x a b * P p.1.2 b := by
  simp only [τ, LinearMap.coe_mk, AddHom.coe_mk, congrA, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, Finset.sum_mul]

/-- The order on upper-triangle indices in which `τ P` is lower triangular. -/
def keyU {m : ℕ} (p : U m) : Fin m ×ₗ Fin m := toLex (p.1.2, p.1.1)

lemma keyU_inj {m : ℕ} : Function.Injective (keyU (m := m)) := by
  intro p q h
  simp only [keyU, toLex_inj, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.2 h.1)

lemma τ_single_zero {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (hP : ∀ i j, i < j → P i j = 0)
    {p q : U m} (hpq : keyU p < keyU q) : τ P (Pi.single q 1) p = 0 := by
  rw [τ_apply]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_
  by_contra hne
  have h1 : P p.1.1 a ≠ 0 := fun h => hne (by rw [h]; ring)
  have h2 : symC (Pi.single q (1 : ℝ)) a b ≠ 0 := fun h => hne (by rw [h]; ring)
  have h3 : P p.1.2 b ≠ 0 := fun h => hne (by rw [h]; ring)
  have ha : a ≤ p.1.1 := not_lt.1 fun h => h1 (hP _ _ h)
  have hb : b ≤ p.1.2 := not_lt.1 fun h => h3 (hP _ _ h)
  have hp := p.2
  have hq := q.2
  simp only [keyU, Prod.Lex.toLex_lt_toLex] at hpq
  rcases symC_single_ne h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at *; omega
  · simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff] at *; omega

lemma τ_single_diag {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (hP : ∀ i j, i < j → P i j = 0)
    (p : U m) : τ P (Pi.single p 1) p = P p.1.1 p.1.1 * P p.1.2 p.1.2 := by
  rw [τ_apply, Finset.sum_eq_single p.1.2, Finset.sum_eq_single p.1.1]
  · have : symC (Pi.single p (1 : ℝ)) p.1.1 p.1.2 = 1 := by
      simp only [symC, dif_pos p.2]
      exact Pi.single_eq_same _ _
    rw [this, mul_one]
  · intro a _ ha
    by_contra hne
    have h2 : symC (Pi.single p (1 : ℝ)) a p.1.2 ≠ 0 := fun h => hne (by rw [h]; ring)
    rcases symC_single_ne h2 with ⟨h, _⟩ | ⟨h, h'⟩
    · exact ha h
    · exact ha (h.trans h')
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    by_contra hne
    have h1 : P p.1.1 a ≠ 0 := fun h => hne (by rw [h]; ring)
    have h2 : symC (Pi.single p (1 : ℝ)) a b ≠ 0 := fun h => hne (by rw [h]; ring)
    rcases symC_single_ne h2 with ⟨_, h⟩ | ⟨rfl, rfl⟩
    · exact hb h
    · rcases lt_or_eq_of_le p.2 with h | h
      · exact h1 (hP _ _ h)
      · exact hb h
  · simp

lemma prod_U (m : ℕ) (f : Fin m → ℝ) :
    ∏ p : U m, f p.1.1 * f p.1.2 = (∏ i, f i) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← (idxEquiv m).prod_comp, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [idxEquiv, Equiv.ofBijective_apply, idxFun, Finset.univ_unique,
      Finset.prod_singleton, Fin.succ_zero_eq_one]
    rw [ih (fun i => f i.succ), Fin.prod_univ_succ, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring

/-- `U m` with the linear order from `keyU`. -/
def UL (m : ℕ) : Type := U m

instance (m : ℕ) : Fintype (UL m) := inferInstanceAs (Fintype (U m))
instance (m : ℕ) : DecidableEq (UL m) := inferInstanceAs (DecidableEq (U m))
instance (m : ℕ) : LinearOrder (UL m) :=
  LinearOrder.lift' (fun p : UL m => keyU (m := m) p) keyU_inj

lemma det_τ {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (hP : ∀ i j, i < j → P i j = 0) :
    LinearMap.det (τ P) = P.det ^ (m + 1) := by
  have hPdet : P.det = ∏ i, P i i := Matrix.det_of_isLowerTriangular P fun i j h => hP i j h
  rw [← LinearMap.det_toMatrix', hPdet, ← prod_U m (fun i => P i i)]
  let N : Matrix (UL m) (UL m) ℝ := LinearMap.toMatrix' (τ P)
  have hN : N.IsLowerTriangular := by
    intro p q hpq
    exact τ_single_zero P hP (p := p) (q := q) hpq
  have := Matrix.det_of_isLowerTriangular N hN
  change N.det = _
  rw [this]
  refine Fintype.prod_congr _ _ fun p => ?_
  simp only [N, LinearMap.toMatrix'_apply]
  exact τ_single_diag P hP p

lemma lintegral_τ {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (hd : LinearMap.det (τ P) ≠ 0)
    (G : (U m → ℝ) → ℝ≥0∞) :
    ∫⁻ y, G y = ENNReal.ofReal |LinearMap.det (τ P)| * ∫⁻ x, G (τ P x) := by
  let e := (LinearMap.equivOfDetNeZero (τ P) hd).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ⇑e = ⇑(τ P) := rfl
  have h1 : ∫⁻ x, G (τ P x) = ∫⁻ x, G (e x) := rfl
  rw [h1, ← lintegral_map_equiv G e, he, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← abs_mul, mul_inv_cancel₀ hd, abs_one, ENNReal.ofReal_one, one_mul]

/-- The target density. -/
def fS (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (A : Fin m → Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (if (Matrix.of A).PosDef then
        (2 ^ ((m : ℝ) * n / 2) * multivariateGamma m ((n : ℝ) / 2) * S.det ^ ((n : ℝ) / 2))⁻¹ *
          Real.exp (-(1 / 2) * (S⁻¹ * Matrix.of A).trace) *
          (Matrix.of A).det ^ (((n : ℝ) - m - 1) / 2)
      else 0)

lemma measurable_fS (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) : Measurable (fS m n S) := by
  have hdet : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).det :=
    continuous_id.matrix_det
  have htr : Continuous fun A : Fin m → Fin m → ℝ => (S⁻¹ * Matrix.of A).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]; fun_prop
  refine Measurable.ennreal_ofReal (Measurable.ite (measurableSet_posDef m) ?_ measurable_const)
  exact (measurable_const.mul (measurable_const.mul htr.measurable).exp).mul
    (hdet.measurable.pow_const _)

lemma density_pointwise {m n : ℕ} {S : Matrix (Fin m) (Fin m) ℝ}
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : P * S * Pᵀ = 1) (A : Fin m → Fin m → ℝ) :
    ENNReal.ofReal (|P.det| ^ (m + 1)) * f1 m n (congrA P A) = fS m n S A := by
  have hdet := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hdP : P.det ≠ 0 := by intro h; simp [h] at hdet
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (Ne.isUnit hdP)
  have hdS : S.det = (P.det ^ 2)⁻¹ := by
    field_simp
    linear_combination hdet
  have hSinv : S⁻¹ = Pᵀ * P := by
    have h1 : Pᵀ * (P * S) = 1 := mul_eq_one_comm.1 hP
    rw [← Matrix.mul_assoc] at h1
    exact (Matrix.inv_eq_left_inv h1)
  have hof : Matrix.of (congrA P A) = P * Matrix.of A * Pᵀ := rfl
  have htr : (P * Matrix.of A * Pᵀ).trace = (S⁻¹ * Matrix.of A).trace := by
    rw [Matrix.trace_mul_comm, hSinv, ← Matrix.mul_assoc]
  have hpd : (P * Matrix.of A * Pᵀ).PosDef ↔ (Matrix.of A).PosDef := by
    constructor
    · intro h
      have h2 := h.mul_mul_conjTranspose_same (B := P⁻¹)
        (Matrix.vecMul_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hPu))
      have hdu : IsUnit P.det := Ne.isUnit hdP
      have hdu' : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
      have e : P⁻¹ * (P * Matrix.of A * Pᵀ) * (P⁻¹)ᴴ = Matrix.of A := by
        rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_nonsing_inv,
          Matrix.mul_assoc P, ← Matrix.mul_assoc P⁻¹, Matrix.nonsing_inv_mul _ hdu, Matrix.one_mul,
          Matrix.mul_nonsing_inv_cancel_right _ _ hdu']
      rwa [e] at h2
    · intro h
      have h2 := h.mul_mul_conjTranspose_same (B := P) (Matrix.vecMul_injective_of_isUnit hPu)
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  unfold f1 fS
  rw [hof, hpd, htr]
  split_ifs with h
  · have hA := h.det_pos
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hx : 0 < |P.det| := abs_pos.2 hdP
    have hsq : P.det * (Matrix.of A).det * P.det = |P.det| ^ 2 * (Matrix.of A).det := by
      rw [sq_abs]; ring
    have key : |P.det| ^ (m + 1) * (|P.det| ^ 2) ^ (((n : ℝ) - m - 1) / 2) =
        (|P.det| ^ 2) ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast |P.det| (m + 1), ← Real.rpow_natCast |P.det| 2,
        ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
      congr 1; push_cast; ring
    have hdS' : S.det = (|P.det| ^ 2)⁻¹ := by rw [sq_abs]; exact hdS
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hsq, hdS',
      Real.mul_rpow (by positivity) hA.le, Real.inv_rpow (by positivity), cst]
    simp only [mul_inv, inv_inv]
    rw [← key]
    ring
  · simp

theorem main {m n : ℕ} (hmn : m ≤ n) {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef) :
    wishart m n S = (symVolume m).withDensity (fS m n S) := by
  obtain ⟨P, hPl, hP⟩ := exists_P hS
  have hdetP : P.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hP
    simp [Matrix.det_mul, h] at this
  have hVP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (Ne.isUnit hdetP)
  have hid : congrA P⁻¹ ∘ congrA P = id := by
    funext A
    simp only [Function.comp_apply, congrA_congrA, hVP, id]
    funext i j
    simp [congrA]
  have hdτ : LinearMap.det (τ P) ≠ 0 := by
    rw [det_τ P hPl]; exact pow_ne_zero _ hdetP
  have hw : wishart m n S = (wishart m n 1).map (congrA P⁻¹) := by
    rw [← wishart_map (n := n) hS hP, Measure.map_map (measurable_congrA _) (measurable_congrA _),
      hid, Measure.map_id]
  rw [hw, wishart_one hmn]
  ext s hs
  rw [Measure.map_apply (measurable_congrA _) hs, withDensity_apply _ (measurable_congrA _ hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_congrA _ hs),
    ← lintegral_indicator hs]
  change ∫⁻ A, _ ∂(Measure.map symC volume) = ∫⁻ A, _ ∂(Measure.map symC volume)
  rw [lintegral_map ((measurable_f1 m n).indicator (measurable_congrA _ hs)) (measurable_symC m),
    lintegral_map ((measurable_fS m n S).indicator hs) (measurable_symC m), lintegral_τ P hdτ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  have hb : congrA P⁻¹ (congrA P (symC x)) = symC x := congrFun hid (symC x)
  rw [symC_τ]
  by_cases hx : symC x ∈ s
  · rw [Set.indicator_of_mem (show congrA P (symC x) ∈ congrA P⁻¹ ⁻¹' s by
      rw [Set.mem_preimage, hb]; exact hx), Set.indicator_of_mem hx, det_τ P hPl, abs_pow,
      density_pointwise hP]
  · rw [Set.indicator_of_notMem (show congrA P (symC x) ∉ congrA P⁻¹ ⁻¹' s by
      rw [Set.mem_preimage, hb]; exact hx), Set.indicator_of_notMem hx, mul_zero]

end WDAux

open MuirheadMST in
theorem solution (m n : ℕ) (hmn : m ≤ n) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef) :
    wishart m n S = (symVolume m).withDensity fun A => ENNReal.ofReal
      (if (Matrix.of A).PosDef then
        (2 ^ ((m : ℝ) * n / 2) * multivariateGamma m ((n : ℝ) / 2) * S.det ^ ((n : ℝ) / 2))⁻¹ *
          Real.exp (-(1 / 2) * (S⁻¹ * Matrix.of A).trace) *
          (Matrix.of A).det ^ (((n : ℝ) - m - 1) / 2)
      else 0) :=
  WDAux.main hmn hS
