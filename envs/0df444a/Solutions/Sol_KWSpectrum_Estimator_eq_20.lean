-- Prove2me | solution 1 for KWSpectrum.Estimator.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T14:44:28.921498+00:00
-- url     : https://prove2.me/submissions/afe57858-15ef-41e0-b979-2ab24aea1dc5

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

set_option autoImplicit false

namespace KW20

open QAlgorithms QAlgorithms.Schur

theorem piKron_mul {d n : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    piKron n (A * B) = piKron n A * piKron n B := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

theorem piKron_one {d n : ℕ} : piKron n (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem tp_mul_piKron {d n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin d) (Fin d) ℂ) :
    tensorPermutation d n σ * piKron n A = piKron n A * tensorPermutation d n σ := by
  ext y x
  simp only [Matrix.mul_apply, tensorPermutation, piKron, Matrix.of_apply]
  rw [Fintype.sum_eq_single (y ∘ σ) (fun b hb => by
        have hne : ¬ (y = b ∘ ⇑σ.symm) := by
          rintro rfl; exact hb (by ext i; simp)
        simp [hne]),
      Fintype.sum_eq_single (x ∘ σ.symm) (fun b hb => by simp [hb])]
  have h1 : y = (y ∘ σ) ∘ ⇑σ.symm := by ext i; simp
  rw [if_pos h1, if_pos rfl, one_mul, mul_one]
  refine Eq.trans ?_ (Equiv.prod_comp σ (fun i => A (y i) ((x ∘ σ.symm) i)))
  simp

theorem young_comm {d n : ℕ} (Y : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ) :
    tensorYoungOperator Y * piKron n A = piKron n A * tensorYoungOperator Y := by
  unfold tensorYoungOperator
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, tp_mul_piKron]

theorem piKron_mem {d n : ℕ} (Y : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin n → Fin d)) (hv : v ∈ schurModule Y) :
    Matrix.toEuclideanLin (piKron n A) v ∈ schurModule Y := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨Matrix.toEuclideanLin (piKron n A) w, ?_⟩
  have := congrArg (fun M => Matrix.toEuclideanLin M w) (young_comm Y A)
  simpa using this

theorem rep_apply {d n : ℕ} (Y : Partition d n) (A : Matrix (Fin d) (Fin d) ℂ)
    (v : schurModule Y) :
    ((polynomialRepresentation Y A v : schurModule Y) : EuclideanSpace ℂ (Fin n → Fin d)) =
      Matrix.toEuclideanLin (piKron n A) v := by
  have h := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := schurModule Y)
    ⟨_, piKron_mem Y A v v.2⟩
  exact congrArg Subtype.val h

theorem rep_mul {d n : ℕ} (Y : Partition d n) (A B : Matrix (Fin d) (Fin d) ℂ) :
    polynomialRepresentation Y (A * B) =
      polynomialRepresentation Y A ∘ₗ polynomialRepresentation Y B := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  simp only [rep_apply, LinearMap.comp_apply, piKron_mul, Matrix.toLpLin_mul_same]

theorem rep_one {d n : ℕ} (Y : Partition d n) :
    polynomialRepresentation Y (1 : Matrix (Fin d) (Fin d) ℂ) = LinearMap.id := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  simp only [rep_apply, piKron_one, Matrix.toLpLin_one, LinearMap.id_apply]

/-- Unitary invariance: eq_20 reduces to diagonal matrices. -/
theorem eq20_of_diag {d n : ℕ} (Y : Partition d n)
    (hdiag : ∀ r : Fin d → ℝ,
      LinearMap.trace ℂ (schurModule Y)
          (polynomialRepresentation Y (Matrix.diagonal (fun j => (r j : ℂ)))) =
        ((MvPolynomial.eval r (schurPolynomial Y) : ℝ) : ℂ))
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) :
    LinearMap.trace ℂ (schurModule Y)
        (polynomialRepresentation Y (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U)) =
      ((MvPolynomial.eval r (schurPolynomial Y) : ℝ) : ℂ) := by
  rw [rep_mul, rep_mul, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, ← rep_mul,
    (Matrix.mem_unitaryGroup_iff').mp hU, rep_one, LinearMap.id_comp]
  exact hdiag r

/-- The Kostka basis statement (core child): `schurModule Y` has a basis of weight vectors
indexed by the semistandard fillings, the vector of `T` having weight `content T`. -/
def KostkaBasis {d n : ℕ} (Y : Partition d n) : Prop :=
  ∃ b : Module.Basis {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} ℂ (schurModule Y),
    ∀ T (r : Fin d → ℂ),
      Matrix.toEuclideanLin (piKron n (Matrix.diagonal r)) (b T : EuclideanSpace ℂ (Fin n → Fin d)) =
        (∏ a, r (T.1 a)) • (b T : EuclideanSpace ℂ (Fin n → Fin d))

theorem diag_of_kostka {d n : ℕ} (Y : Partition d n) (hK : KostkaBasis Y) (r : Fin d → ℝ) :
    LinearMap.trace ℂ (schurModule Y)
        (polynomialRepresentation Y (Matrix.diagonal (fun j => (r j : ℂ)))) =
      ((MvPolynomial.eval r (schurPolynomial Y) : ℝ) : ℂ) := by
  classical
  obtain ⟨b, hb⟩ := hK
  have hev : ∀ T, polynomialRepresentation Y (Matrix.diagonal (fun j => (r j : ℂ))) (b T) =
      (∏ a, ((r (T.1 a) : ℝ) : ℂ)) • b T := by
    intro T
    apply Subtype.ext
    rw [rep_apply, hb T]
    rfl
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hev, map_smul, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  unfold schurPolynomial
  simp only [map_sum, map_prod, MvPolynomial.eval_X, Complex.ofReal_sum, Complex.ofReal_prod]
  symm
  refine Finset.sum_subtype _ ?_ _
  intro T
  simp

/-- The tensor word of a filling, read through the cell numbering. -/
noncomputable def wordOf {d n : ℕ} (Y : Partition d n) (T : Y.val.cells → Fin d) : Fin n → Fin d :=
  fun k => T ((cellNumbering Y).symm k)

/-- The Young-symmetrized word vector `C e_{w_T}`. -/
noncomputable def youngVec {d n : ℕ} (Y : Partition d n) (T : Y.val.cells → Fin d) :
    EuclideanSpace ℂ (Fin n → Fin d) :=
  Matrix.toEuclideanLin (tensorYoungOperator Y) (EuclideanSpace.single (wordOf Y T) 1)

theorem piKron_diagonal {d n : ℕ} (r : Fin d → ℂ) :
    piKron n (Matrix.diagonal r) = Matrix.diagonal (fun w : Fin n → Fin d => ∏ k, r (w k)) := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem diag_single {d n : ℕ} (r : Fin d → ℂ) (w : Fin n → Fin d) :
    Matrix.toEuclideanLin (piKron n (Matrix.diagonal r)) (EuclideanSpace.single w (1 : ℂ)) =
      (∏ k, r (w k)) • EuclideanSpace.single w (1 : ℂ) := by
  rw [piKron_diagonal]
  ext x
  by_cases h : x = w
  · subst h; simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  · simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal, h]

theorem youngVec_weight {d n : ℕ} (Y : Partition d n) (T : Y.val.cells → Fin d) (r : Fin d → ℂ) :
    Matrix.toEuclideanLin (piKron n (Matrix.diagonal r)) (youngVec Y T) =
      (∏ a, r (T a)) • youngVec Y T := by
  have hc := congrArg (fun M => Matrix.toEuclideanLin M (EuclideanSpace.single (wordOf Y T) (1 : ℂ)))
    (young_comm Y (Matrix.diagonal r))
  simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] at hc
  unfold youngVec
  rw [← hc, diag_single, map_smul]
  congr 1
  exact Equiv.prod_comp (cellNumbering Y).symm (fun a => r (T a))

/-- Child K1: the Young vectors of the semistandard fillings are linearly independent. -/
def YoungIndep {d n : ℕ} (Y : Partition d n) : Prop :=
  LinearIndependent ℂ (fun T : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} => youngVec Y T.1)

/-- Child K2 (straightening): every `C e_w` lies in the span of the semistandard Young vectors. -/
def YoungSpan {d n : ℕ} (Y : Partition d n) : Prop :=
  ∀ w : Fin n → Fin d,
    Matrix.toEuclideanLin (tensorYoungOperator Y) (EuclideanSpace.single w (1 : ℂ)) ∈
      Submodule.span ℂ (Set.range
        (fun T : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} => youngVec Y T.1))

theorem kostka_of {d n : ℕ} (Y : Partition d n) (h1 : YoungIndep Y) (h2 : YoungSpan Y) :
    KostkaBasis Y := by
  let v : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} → schurModule Y :=
    fun T => ⟨youngVec Y T.1, ⟨_, rfl⟩⟩
  have hli : LinearIndependent ℂ v := LinearIndependent.of_comp (schurModule Y).subtype h1
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rintro ⟨x, u, rfl⟩ -
    have hmem : Matrix.toEuclideanLin (tensorYoungOperator Y) u ∈
        Submodule.span ℂ (Set.range
          (fun T : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} => youngVec Y T.1)) := by
      rw [← (EuclideanSpace.basisFun (Fin n → Fin d) ℂ).sum_repr u, map_sum]
      refine Submodule.sum_mem _ fun w _ => ?_
      rw [map_smul, EuclideanSpace.basisFun_apply]
      exact Submodule.smul_mem _ _ (h2 w)
    have hr : Set.range (fun T : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} =>
        youngVec Y T.1) = (schurModule Y).subtype '' Set.range v := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = ⟨Matrix.toEuclideanLin (tensorYoungOperator Y) u, ⟨u, rfl⟩⟩ := Subtype.ext hyx
    rw [← this]; exact hy
  refine ⟨Module.Basis.mk hli hsp, fun T r => ?_⟩
  rw [Module.Basis.mk_apply]
  exact youngVec_weight Y T.1 r

end KW20

open KW20 in
theorem glue_eq20 {d N : ℕ} (Y : QAlgorithms.Schur.Partition d N) (h1 : YoungIndep Y)
    (h2 : YoungSpan Y)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) :
    LinearMap.trace ℂ (QAlgorithms.Schur.schurModule Y)
        (QAlgorithms.Schur.polynomialRepresentation Y
          (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U)) =
      ((MvPolynomial.eval r (QAlgorithms.Schur.schurPolynomial Y) : ℝ) : ℂ) :=
  eq20_of_diag Y (diag_of_kostka Y (kostka_of Y h1 h2)) U hU r

set_option autoImplicit false

namespace KW20K

open QAlgorithms QAlgorithms.Schur

noncomputable def wordOf {d n : ℕ} (Y : Partition d n) (T : Y.val.cells → Fin d) : Fin n → Fin d :=
  fun k => T ((cellNumbering Y).symm k)

noncomputable def youngVec {d n : ℕ} (Y : Partition d n) (T : Y.val.cells → Fin d) :
    EuclideanSpace ℂ (Fin n → Fin d) :=
  Matrix.toEuclideanLin (tensorYoungOperator Y) (EuclideanSpace.single (wordOf Y T) 1)

theorem youngVec_apply {d n : ℕ} (Y : Partition d n) (T : Y.val.cells → Fin d)
    (x : Fin n → Fin d) :
    youngVec Y T x = ∑ a ∈ rowPermutations Y, ∑ b ∈ columnPermutations Y,
      (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) * (if x = wordOf Y T ∘ (a * b).symm then 1 else 0) := by
  classical
  unfold youngVec tensorYoungOperator
  rw [Matrix.toLpLin_apply]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, tensorPermutation, Matrix.of_apply]
  rw [Finset.sum_eq_single (wordOf Y T)]
  · simp
  · intro y _ hy; simp [hy]
  · simp

/-- Generic segment count: permuting a line whose values are monotone along it can only
lower the number of small values in each initial segment. -/
theorem seg_count {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (s : Finset ι)
    (pos : ι → ℕ) (hinj : Set.InjOn pos s) (F : ι → Fin d)
    (hmono : ∀ x ∈ s, ∀ y ∈ s, pos x < pos y → F x ≤ F y)
    (σ : Equiv.Perm ι) (hσ : ∀ x, σ x ∈ s ↔ x ∈ s) (k : Fin d) (m : ℕ) :
    (s.filter (fun x => pos x < m ∧ F (σ x) ≤ k)).card ≤
      (s.filter (fun x => pos x < m ∧ F x ≤ k)).card := by
  by_cases h : ∀ x ∈ s, pos x < m → F x ≤ k
  · have h1 : s.filter (fun x => pos x < m ∧ F x ≤ k) = s.filter (fun x => pos x < m) := by
      refine Finset.filter_congr fun x hx => ?_
      exact ⟨fun h' => h'.1, fun h' => ⟨h', h x hx h'⟩⟩
    rw [h1]
    exact Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩)
  · push Not at h
    obtain ⟨x0, hx0, hpx0, hkx0⟩ := h
    have h1 : s.filter (fun x => pos x < m ∧ F x ≤ k) = s.filter (fun x => F x ≤ k) := by
      refine Finset.filter_congr fun x hx => ⟨fun h' => h'.2, fun h' => ⟨?_, h'⟩⟩
      rcases lt_trichotomy (pos x) (pos x0) with hlt | heq | hgt
      · omega
      · have := hinj hx hx0 heq
        subst this
        exact absurd h' (not_le.mpr hkx0)
      · exact absurd (le_trans (hmono x0 hx0 x hx hgt) h') (not_le.mpr hkx0)
    rw [h1]
    calc (s.filter (fun x => pos x < m ∧ F (σ x) ≤ k)).card
        ≤ (s.filter (fun x => F (σ x) ≤ k)).card :=
          Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.2⟩)
      _ = (s.filter (fun x => F x ≤ k)).card := by
          refine Finset.card_nbij' σ σ.symm ?_ ?_ ?_ ?_
          · intro x hx
            simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
            exact ⟨(hσ x).mpr hx.1, hx.2⟩
          · intro x hx
            simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
            refine ⟨(hσ _).mp (by simpa using hx.1), by simpa using hx.2⟩
          · intro x _; simp
          · intro x _; simp

theorem seg_point {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (s : Finset ι)
    (pos : ι → ℕ) (hinj : Set.InjOn pos s) (G : ι → Fin d) (x : ι) (hx : x ∈ s) (k : Fin d) :
    (s.filter (fun y => pos y < pos x + 1 ∧ G y ≤ k)).card =
      (s.filter (fun y => pos y < pos x ∧ G y ≤ k)).card + (if G x ≤ k then 1 else 0) := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := s.filter
    (fun y => pos y < pos x + 1 ∧ G y ≤ k)) (fun y => pos y < pos x)
  rw [← hsplit, Finset.filter_filter, Finset.filter_filter]
  congr 1
  · congr 1
    refine Finset.filter_congr fun y _ => ?_
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · split_ifs with hG
    · rw [Finset.card_eq_one]
      refine ⟨x, ?_⟩
      ext y
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, ⟨h1, _⟩, h3⟩
        exact hinj hy hx (by omega)
      · rintro rfl; exact ⟨hx, ⟨by omega, hG⟩, by omega⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro y hy ⟨⟨h1, h2⟩, h3⟩
      have : y = x := hinj hy hx (by omega)
      subst this
      exact hG h2

theorem seg_diff {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (s : Finset ι)
    (pos : ι → ℕ) (hinj : Set.InjOn pos s) (G F : ι → Fin d)
    (h : ∀ x ∈ s, ∀ k : Fin d, ∀ m, m ≤ pos x + 1 →
      (s.filter (fun y => pos y < m ∧ G y ≤ k)).card =
        (s.filter (fun y => pos y < m ∧ F y ≤ k)).card) :
    ∀ x ∈ s, G x = F x := by
  intro x hx
  have key : ∀ k, G x ≤ k ↔ F x ≤ k := by
    intro k
    have e1 := h x hx k (pos x + 1) le_rfl
    have e0 := h x hx k (pos x) (Nat.le_succ _)
    rw [seg_point s pos hinj G x hx, seg_point s pos hinj F x hx, e0] at e1
    have e2 := Nat.add_left_cancel e1
    by_cases hG : G x ≤ k <;> by_cases hF : F x ≤ k
    · exact iff_of_true hG hF
    · simp [hG, hF] at e2
    · simp [hG, hF] at e2
    · exact iff_of_false hG hF
  exact le_antisymm ((key (F x)).mpr le_rfl) ((key (G x)).mp le_rfl)

section words
variable {d n : ℕ} (Y : Partition d n)

noncomputable def rowOf (p : Fin n) : ℕ := ((cellNumbering Y).symm p).val.1
noncomputable def colOf (p : Fin n) : ℕ := ((cellNumbering Y).symm p).val.2

def SSW (w : Fin n → Fin d) : Prop :=
  ∀ p q, (rowOf Y p = rowOf Y q → colOf Y p < colOf Y q → w p ≤ w q) ∧
    (colOf Y p = colOf Y q → rowOf Y p < rowOf Y q → w p < w q)

theorem ssw_of {T : Y.val.cells → Fin d} (hT : IsSemistandardFilling Y T) : SSW Y (wordOf Y T) :=
  fun p q => hT ((cellNumbering Y).symm p) ((cellNumbering Y).symm q)

theorem cell_ext {p q : Fin n} (h1 : rowOf Y p = rowOf Y q) (h2 : colOf Y p = colOf Y q) : p = q :=
  (cellNumbering Y).symm.injective (Subtype.ext (Prod.ext h1 h2))

theorem mem_row {a : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations Y) (i : Fin n) :
    rowOf Y (a i) = rowOf Y i := by
  unfold rowPermutations at ha; rw [Finset.mem_filter] at ha; exact ha.2 i

theorem mem_col {b : Equiv.Perm (Fin n)} (hb : b ∈ columnPermutations Y) (i : Fin n) :
    colOf Y (b i) = colOf Y i := by
  unfold columnPermutations at hb; rw [Finset.mem_filter] at hb; exact hb.2 i

theorem one_mem_row : (1 : Equiv.Perm (Fin n)) ∈ rowPermutations Y := by
  unfold rowPermutations; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, fun i => rfl⟩

theorem one_mem_col : (1 : Equiv.Perm (Fin n)) ∈ columnPermutations Y := by
  unfold columnPermutations; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, fun i => rfl⟩

noncomputable def cnt (w : Fin n → Fin d) (m : ℕ) (k : Fin d) : ℕ :=
  (Finset.univ.filter (fun p => rowOf Y p < m ∧ w p ≤ k)).card

noncomputable def colcnt (w : Fin n → Fin d) (j m : ℕ) (k : Fin d) : ℕ :=
  ((Finset.univ.filter (fun p => colOf Y p = j)).filter (fun p => rowOf Y p < m ∧ w p ≤ k)).card

noncomputable def rowcnt (w : Fin n → Fin d) (i m : ℕ) (k : Fin d) : ℕ :=
  ((Finset.univ.filter (fun p => rowOf Y p = i)).filter (fun p => colOf Y p < m ∧ w p ≤ k)).card

theorem cnt_row_inv {a : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations Y) (w : Fin n → Fin d)
    (m : ℕ) (k : Fin d) : cnt Y (w ∘ a) m k = cnt Y w m k := by
  unfold cnt
  refine Finset.card_nbij' a a.symm ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Function.comp_apply] at hx ⊢
    exact ⟨by rw [mem_row Y ha]; exact hx.1, hx.2⟩
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Function.comp_apply, Equiv.apply_symm_apply] at hx ⊢
    refine ⟨?_, hx.2⟩
    have := mem_row Y ha (a.symm x)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]; exact hx.1
  · intro x _; simp
  · intro x _; simp

theorem cnt_cols (w : Fin n → Fin d) (m : ℕ) (k : Fin d) :
    cnt Y w m k = ∑ j ∈ Finset.univ.image (colOf Y), colcnt Y w j m k := by
  unfold cnt colcnt
  rw [Finset.card_eq_sum_card_fiberwise (f := colOf Y) (t := Finset.univ.image (colOf Y))
    (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.filter_filter, Finset.filter_filter]
  congr 1
  exact Finset.filter_congr fun x _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem inj_col (j : ℕ) :
    Set.InjOn (rowOf Y) ↑(Finset.univ.filter (fun p => colOf Y p = j)) := by
  intro p hp q hq h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
  exact cell_ext Y h (hp.trans hq.symm)

theorem inj_row (i : ℕ) :
    Set.InjOn (colOf Y) ↑(Finset.univ.filter (fun p => rowOf Y p = i)) := by
  intro p hp q hq h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
  exact cell_ext Y (hp.trans hq.symm) h

theorem colcnt_le {w : Fin n → Fin d} (hw : SSW Y w) {b : Equiv.Perm (Fin n)}
    (hb : b ∈ columnPermutations Y) (j m : ℕ) (k : Fin d) :
    colcnt Y (w ∘ b.symm) j m k ≤ colcnt Y w j m k := by
  unfold colcnt
  refine seg_count _ (rowOf Y) (inj_col Y j) w ?_ b.symm ?_ k m
  · intro x hx y hy hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact le_of_lt ((hw x y).2 (hx.trans hy.symm) hlt)
  · intro x
    have := mem_col Y hb (b.symm x)
    rw [Equiv.apply_symm_apply] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← this]

theorem rowcnt_le {w : Fin n → Fin d} (hw : SSW Y w) {a : Equiv.Perm (Fin n)}
    (ha : ∀ i, rowOf Y (a i) = rowOf Y i) (i m : ℕ) (k : Fin d) :
    rowcnt Y (w ∘ a) i m k ≤ rowcnt Y w i m k := by
  unfold rowcnt
  refine seg_count _ (colOf Y) (inj_row Y i) w ?_ a ?_ k m
  · intro x hx y hy hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact (hw x y).1 (hx.trans hy.symm) hlt
  · intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ha x]

noncomputable def bnd : ℕ := Finset.univ.sup (rowOf Y) + 2

noncomputable def pot (w : Fin n → Fin d) : ℕ :=
  ∑ m ∈ Finset.range (bnd Y), ∑ k : Fin d, cnt Y w m k

theorem lt_bnd (p : Fin n) : rowOf Y p + 1 < bnd Y := by
  have := Finset.le_sup (f := rowOf Y) (Finset.mem_univ p)
  unfold bnd; omega

theorem lt_bnd' (p : Fin n) (m : ℕ) (hm : m ≤ rowOf Y p + 1) : m ∈ Finset.range (bnd Y) :=
  Finset.mem_range.mpr (lt_of_le_of_lt hm (lt_bnd Y p))

theorem key {T T' : Y.val.cells → Fin d} (hT : IsSemistandardFilling Y T)
    (hT' : IsSemistandardFilling Y T') {a b : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations Y)
    (hb : b ∈ columnPermutations Y) (hx : wordOf Y T = wordOf Y T' ∘ (a * b).symm) :
    pot Y (wordOf Y T) ≤ pot Y (wordOf Y T') ∧
      (pot Y (wordOf Y T') ≤ pot Y (wordOf Y T) → T = T' ∧ b = 1) := by
  set w := wordOf Y T with hwdef
  set w' := wordOf Y T' with hw'def
  have hs' := ssw_of Y hT'
  have hs := ssw_of Y hT
  have h1 : w ∘ a = w' ∘ b.symm := by
    funext p
    have := congrFun hx (a p)
    simpa [Equiv.Perm.mul_def] using this
  have hc : ∀ m k, cnt Y w m k = cnt Y (w' ∘ b.symm) m k := by
    intro m k; rw [← h1, cnt_row_inv Y ha]
  have hle : ∀ m k, cnt Y (w' ∘ b.symm) m k ≤ cnt Y w' m k := by
    intro m k
    rw [cnt_cols, cnt_cols]
    exact Finset.sum_le_sum fun j _ => colcnt_le Y hs' hb j m k
  have hle2 : ∀ m k, cnt Y w m k ≤ cnt Y w' m k := fun m k => (hc m k).trans_le (hle m k)
  refine ⟨Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun k _ => hle2 m k, fun hge => ?_⟩
  have hEq : pot Y w = pot Y w' := le_antisymm
    (Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun k _ => hle2 m k) hge
  have hEq1 : ∀ m ∈ Finset.range (bnd Y), ∀ k, cnt Y w m k = cnt Y w' m k := by
    intro m hm k
    have h2 := (Finset.sum_eq_sum_iff_of_le (fun m _ =>
      Finset.sum_le_sum fun k _ => hle2 m k)).mp hEq m hm
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => hle2 m k)).mp h2 k (Finset.mem_univ k)
  -- per column equality
  have hcol : ∀ m ∈ Finset.range (bnd Y), ∀ k, ∀ j ∈ Finset.univ.image (colOf Y),
      colcnt Y (w' ∘ b.symm) j m k = colcnt Y w' j m k := by
    intro m hm k
    have h3 : cnt Y (w' ∘ b.symm) m k = cnt Y w' m k := (hc m k).symm.trans (hEq1 m hm k)
    rw [cnt_cols, cnt_cols] at h3
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => colcnt_le Y hs' hb j m k)).mp h3
  have hG : ∀ p, w' (b.symm p) = w' p := by
    intro p
    have := seg_diff (Finset.univ.filter (fun q => colOf Y q = colOf Y p)) (rowOf Y)
      (inj_col Y (colOf Y p)) (w' ∘ b.symm) w' (by
        intro x hx k m hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have := hcol m (lt_bnd' Y x m hm) k (colOf Y p)
          (Finset.mem_image_of_mem _ (Finset.mem_univ p))
        exact this) p (by simp)
    exact this
  have hb1 : b = 1 := by
    have hfix : ∀ p, b.symm p = p := by
      intro p
      by_contra hne
      have hc1 : colOf Y (b.symm p) = colOf Y p := by
        have := mem_col Y hb (b.symm p); rw [Equiv.apply_symm_apply] at this; exact this.symm
      have hr : rowOf Y (b.symm p) ≠ rowOf Y p := fun h => hne (cell_ext Y h hc1)
      rcases lt_or_gt_of_ne hr with hlt | hgt
      · exact absurd (hG p) (ne_of_lt ((hs' _ _).2 hc1 hlt))
      · exact absurd (hG p) (ne_of_gt ((hs' _ _).2 hc1.symm hgt))
    ext p
    have := hfix (b p)
    rw [Equiv.symm_apply_apply] at this
    simp [← this]
  refine ⟨?_, hb1⟩
  -- now w ∘ a = w'
  have hwa : w ∘ a = w' := by rw [h1, hb1]; rfl
  have hwa' : w' ∘ a.symm = w := by rw [← hwa]; funext p; simp
  have hra : ∀ i, rowOf Y (a i) = rowOf Y i := mem_row Y ha
  have hra' : ∀ i, rowOf Y (a.symm i) = rowOf Y i := by
    intro i; have := hra (a.symm i); rw [Equiv.apply_symm_apply] at this; exact this.symm
  have hww : ∀ p, w' p = w p := by
    intro p
    refine seg_diff (Finset.univ.filter (fun q => rowOf Y q = rowOf Y p)) (colOf Y)
      (inj_row Y (rowOf Y p)) w' w ?_ p (by simp)
    intro x _ k m _
    have e1 := rowcnt_le Y hs hra (rowOf Y p) m k
    have e2 := rowcnt_le Y hs' hra' (rowOf Y p) m k
    rw [hwa] at e1; rw [hwa'] at e2
    exact le_antisymm e1 e2
  funext c
  have := hww ((cellNumbering Y) c)
  simp only [hw'def, hwdef, wordOf, Equiv.symm_apply_apply] at this
  exact this.symm

end words

theorem youngIndep {d n : ℕ} (Y : Partition d n) :
    LinearIndependent ℂ
      (fun T : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} => youngVec Y T.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0⟩ := hne
  let S := Finset.univ.filter (fun i => g i ≠ 0)
  have hS : S.Nonempty := ⟨i0, by simp [S, hi0]⟩
  obtain ⟨T, hTS, hTmax⟩ := Finset.exists_max_image S (fun i => pot Y (wordOf Y i.1)) hS
  have hTg : g T ≠ 0 := by simpa [S] using hTS
  have hcoord : ∑ i, g i * youngVec Y i.1 (wordOf Y T.1) = 0 := by
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n → Fin d) => v (wordOf Y T.1)) hg
    simpa [WithLp.ofLp_sum, Finset.sum_apply] using this
  rw [Finset.sum_eq_single T] at hcoord
  · have hdiag : youngVec Y T.1 (wordOf Y T.1) =
        ((∑ a ∈ rowPermutations Y, ∑ b ∈ columnPermutations Y,
          (if wordOf Y T.1 = wordOf Y T.1 ∘ (a * b).symm then 1 else 0 : ℕ) : ℕ) : ℂ) := by
      rw [youngVec_apply]
      push_cast
      refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      split_ifs with h
      · obtain ⟨_, rfl⟩ := (key Y T.2 T.2 ha hb h).2 le_rfl
        simp
      · simp
    have hpos : 1 ≤ ∑ a ∈ rowPermutations Y, ∑ b ∈ columnPermutations Y,
          (if wordOf Y T.1 = wordOf Y T.1 ∘ (a * b).symm then 1 else 0 : ℕ) := by
      calc 1 = (if wordOf Y T.1 = wordOf Y T.1 ∘ ((1 : Equiv.Perm (Fin n)) * 1).symm
              then 1 else 0 : ℕ) := by
            rw [if_pos]; rfl
        _ ≤ ∑ b ∈ columnPermutations Y,
              (if wordOf Y T.1 = wordOf Y T.1 ∘ ((1 : Equiv.Perm (Fin n)) * b).symm
                then 1 else 0 : ℕ) :=
            Finset.single_le_sum (f := fun b => (if wordOf Y T.1 = wordOf Y T.1 ∘
              ((1 : Equiv.Perm (Fin n)) * b).symm then 1 else 0 : ℕ)) (fun _ _ => Nat.zero_le _)
              (one_mem_col Y)
        _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b ∈ columnPermutations Y,
              (if wordOf Y T.1 = wordOf Y T.1 ∘ (a * b).symm then 1 else 0 : ℕ))
              (fun _ _ => Nat.zero_le _) (one_mem_row Y)
    rw [hdiag] at hcoord
    rcases mul_eq_zero.mp hcoord with h | h
    · exact hTg h
    · have := Nat.cast_eq_zero.mp h
      omega
  · intro T' _ hne'
    by_cases hg' : g T' = 0
    · simp [hg']
    · have hT'S : T' ∈ S := by simp [S, hg']
      rw [youngVec_apply]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_)
      rw [if_neg, mul_zero]
      intro h
      have hk := key Y T.2 T'.2 ha hb h
      exact hne' (Subtype.ext ((hk.2 (hTmax T' hT'S)).1.symm))
  · simp

section span
variable {d n : ℕ} (Y : Partition d n)

noncomputable def V (w : Fin n → Fin d) : EuclideanSpace ℂ (Fin n → Fin d) :=
  Matrix.toEuclideanLin (tensorYoungOperator Y) (EuclideanSpace.single w 1)

theorem cond_iff (x w : Fin n → Fin d) (σ : Equiv.Perm (Fin n)) :
    x = w ∘ ⇑σ.symm ↔ x ∘ ⇑σ = w := by
  constructor
  · rintro rfl; funext i; simp
  · rintro rfl; funext i; simp

theorem V_apply (w x : Fin n → Fin d) :
    V Y w x = ∑ a ∈ rowPermutations Y, ∑ b ∈ columnPermutations Y,
      (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) * (if x ∘ ⇑a ∘ ⇑b = w then 1 else 0) := by
  classical
  have h0 : V Y w x = ∑ a ∈ rowPermutations Y, ∑ b ∈ columnPermutations Y,
      (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) * (if x = w ∘ (a * b).symm then 1 else 0) := by
    unfold V tensorYoungOperator
    rw [Matrix.toLpLin_apply]
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    simp only [Matrix.mulVec, dotProduct, tensorPermutation, Matrix.of_apply]
    rw [Finset.sum_eq_single w]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  rw [h0]
  simp only [cond_iff, Equiv.Perm.coe_mul]

theorem mem_col_of {b : Equiv.Perm (Fin n)} (h : ∀ i, colOf Y (b i) = colOf Y i) :
    b ∈ columnPermutations Y := by
  unfold columnPermutations; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩

theorem mem_row_of {a : Equiv.Perm (Fin n)} (h : ∀ i, rowOf Y (a i) = rowOf Y i) :
    a ∈ rowPermutations Y := by
  unfold rowPermutations; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩

theorem comp_iff (x w : Fin n → Fin d) (a b c : Equiv.Perm (Fin n)) :
    x ∘ ⇑a ∘ ⇑b = w ∘ ⇑c ↔ x ∘ ⇑a ∘ ⇑(b * c⁻¹) = w := by
  constructor
  · intro h; funext i
    have := congrFun h (c⁻¹ i)
    simpa [Equiv.Perm.mul_apply] using this
  · intro h; funext i; rw [← h]; simp [Equiv.Perm.mul_apply]

theorem V_comp_col (w : Fin n → Fin d) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ columnPermutations Y) :
    V Y (w ∘ ⇑c) = (((Equiv.Perm.sign c : ℤˣ) : ℤ) : ℂ) • V Y w := by
  refine PiLp.ext fun x => ?_
  rw [PiLp.smul_apply, V_apply, V_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  have hci : ∀ i, colOf Y (c⁻¹ i) = colOf Y i := by
    intro i; have := mem_col Y hc (c⁻¹ i)
    rw [show c (c⁻¹ i) = i from by simp] at this
    exact this.symm
  refine Finset.sum_nbij' (fun b => b * c⁻¹) (fun b => b * c) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact mem_col_of Y fun i => by
      rw [Equiv.Perm.mul_apply, mem_col Y hb, hci]
  · intro b hb
    exact mem_col_of Y fun i => by
      rw [Equiv.Perm.mul_apply, mem_col Y hb, mem_col Y hc]
  · intro b _; simp
  · intro b _; simp
  · intro b _
    simp only [comp_iff]
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h | h <;> simp [h]

theorem swap_mem_col {p q : Fin n} (hc : colOf Y p = colOf Y q) :
    Equiv.swap p q ∈ columnPermutations Y := mem_col_of Y fun i => by
  rcases eq_or_ne i p with rfl | hip
  · simp [Equiv.swap_apply_left, hc]
  · rcases eq_or_ne i q with rfl | hiq
    · simp [Equiv.swap_apply_right, hc]
    · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]

theorem V_repeat (w : Fin n → Fin d) {p q : Fin n} (hpq : p ≠ q) (hc : colOf Y p = colOf Y q)
    (hw : w p = w q) : V Y w = 0 := by
  have ht := swap_mem_col Y hc
  have hwt : w ∘ ⇑(Equiv.swap p q) = w := by
    funext i
    simp only [Function.comp_apply]
    rcases eq_or_ne i p with rfl | hip
    · rw [Equiv.swap_apply_left, hw]
    · rcases eq_or_ne i q with rfl | hiq
      · rw [Equiv.swap_apply_right, hw]
      · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]
  have h := V_comp_col Y w ht
  rw [hwt, Equiv.Perm.sign_swap hpq] at h
  have h2 : (2 : ℂ) • V Y w = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

noncomputable def Qp (w : Fin n → Fin d) : ℕ := ∑ p, colOf Y p * (w p : ℕ)
noncomputable def Rp (w : Fin n → Fin d) : ℕ := ∑ p, rowOf Y p * (w p : ℕ)
noncomputable def Mb : ℕ := (∑ p, rowOf Y p * d) + 1
noncomputable def Phi (w : Fin n → Fin d) : ℕ := Qp Y w * Mb Y + Rp Y w
noncomputable def PhiMax : ℕ := (∑ p, colOf Y p * d) * Mb Y + Mb Y

theorem Rp_lt (w : Fin n → Fin d) : Rp Y w < Mb Y :=
  Nat.lt_succ_of_le (Finset.sum_le_sum fun p _ => Nat.mul_le_mul_left _ (le_of_lt (w p).isLt))

theorem Qp_le (w : Fin n → Fin d) : Qp Y w ≤ ∑ p, colOf Y p * d :=
  Finset.sum_le_sum fun p _ => Nat.mul_le_mul_left _ (le_of_lt (w p).isLt)

theorem Phi_le (w : Fin n → Fin d) : Phi Y w ≤ PhiMax Y :=
  Nat.add_le_add (Nat.mul_le_mul_right _ (Qp_le Y w)) (le_of_lt (Rp_lt Y w))

theorem Phi_lt_of_Q (w w' : Fin n → Fin d) (h : Qp Y w < Qp Y w') : Phi Y w < Phi Y w' := by
  unfold Phi
  have := Rp_lt Y w
  calc Qp Y w * Mb Y + Rp Y w < Qp Y w * Mb Y + Mb Y := by omega
    _ = (Qp Y w + 1) * Mb Y := by ring
    _ ≤ Qp Y w' * Mb Y := Nat.mul_le_mul_right _ h
    _ ≤ _ := Nat.le_add_right _ _

theorem Phi_lt_of_R (w w' : Fin n → Fin d) (hQ : Qp Y w = Qp Y w') (h : Rp Y w < Rp Y w') :
    Phi Y w < Phi Y w' := by
  unfold Phi; rw [hQ]; omega

theorem Qp_swap (w : Fin n → Fin d) {p q : Fin n} (hc : colOf Y p = colOf Y q) :
    Qp Y (w ∘ ⇑(Equiv.swap p q)) = Qp Y w := by
  have ht := swap_mem_col Y hc
  unfold Qp
  calc ∑ i, colOf Y i * ((w ∘ ⇑(Equiv.swap p q)) i : ℕ)
      = ∑ i, colOf Y (Equiv.swap p q i) * (w (Equiv.swap p q i) : ℕ) :=
        Finset.sum_congr rfl fun i _ => by rw [mem_col Y ht]; rfl
    _ = ∑ i, colOf Y i * (w i : ℕ) :=
        Equiv.sum_comp (Equiv.swap p q) (fun i => colOf Y i * (w i : ℕ))

theorem Rp_swap (w : Fin n → Fin d) {p q : Fin n} (hpq : p ≠ q) :
    (Rp Y (w ∘ ⇑(Equiv.swap p q)) : ℤ) =
      Rp Y w + ((rowOf Y q : ℤ) - rowOf Y p) * (((w p : ℕ) : ℤ) - ((w q : ℕ) : ℤ)) := by
  unfold Rp
  push_cast
  have h := Fintype.sum_eq_add p q hpq (f := fun i => (rowOf Y i : ℤ) *
      ((w (Equiv.swap p q i) : ℕ) : ℤ) - (rowOf Y i : ℤ) * ((w i : ℕ) : ℤ))
    (fun x hx => by simp [Equiv.swap_apply_of_ne_of_ne hx.1 hx.2])
  rw [Finset.sum_sub_distrib] at h
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Function.comp_apply] at h ⊢
  linarith

theorem Rp_lt_swap (w : Fin n → Fin d) {p q : Fin n} (hr : rowOf Y p < rowOf Y q)
    (hw : w q < w p) : Rp Y w < Rp Y (w ∘ ⇑(Equiv.swap p q)) := by
  have hpq : p ≠ q := by rintro rfl; omega
  have h := Rp_swap Y w hpq
  have hw' : (w q : ℕ) < (w p : ℕ) := hw
  have hpos : (0 : ℤ) < ((rowOf Y q : ℤ) - rowOf Y p) * (((w p : ℕ) : ℤ) - ((w q : ℕ) : ℤ)) :=
    mul_pos (sub_pos.mpr (by exact_mod_cast hr)) (sub_pos.mpr (by exact_mod_cast hw'))
  have : (Rp Y w : ℤ) < Rp Y (w ∘ ⇑(Equiv.swap p q)) := by linarith
  exact_mod_cast this

theorem ssyt_of_word (w : Fin n → Fin d)
    (hcs : ∀ p q, colOf Y p = colOf Y q → rowOf Y p < rowOf Y q → w p < w q)
    (hrw : ∀ p q, rowOf Y p = rowOf Y q → colOf Y p < colOf Y q → w p ≤ w q) :
    IsSemistandardFilling Y (fun c => w (cellNumbering Y c)) ∧
      wordOf Y (fun c => w (cellNumbering Y c)) = w := by
  refine ⟨fun a b => ⟨fun h1 h2 => hrw _ _ ?_ ?_, fun h1 h2 => hcs _ _ ?_ ?_⟩, ?_⟩
  · simp [rowOf, h1]
  · simp [colOf, h2]
  · simp [colOf, h1]
  · simp [rowOf, h2]
  · funext k; simp [wordOf]

noncomputable def Xset (p q : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => (colOf Y x = colOf Y p ∧ rowOf Y p ≤ rowOf Y x) ∨
    (colOf Y x = colOf Y q ∧ rowOf Y x ≤ rowOf Y q))

noncomputable def SX (p q : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => ∀ x, x ∉ Xset Y p q → σ x = x)

def GarnirP : Prop := ∀ (w : Fin n → Fin d) (p q : Fin n), rowOf Y p = rowOf Y q →
  colOf Y p < colOf Y q →
  ∑ σ ∈ SX Y p q, (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • V Y (w ∘ ⇑σ) = 0

def QincP : Prop := ∀ (w : Fin n → Fin d) (p q : Fin n), rowOf Y p = rowOf Y q →
  colOf Y p < colOf Y q → w q < w p →
  (∀ p' q', colOf Y p' = colOf Y q' → rowOf Y p' < rowOf Y q' → w p' < w q') →
  ∀ σ ∈ SX Y p q, σ ∉ columnPermutations Y → Qp Y w < Qp Y (w ∘ ⇑σ)

theorem V_mem_span (hG : GarnirP Y) (hQ : QincP Y) (w : Fin n → Fin d) :
    V Y w ∈ Submodule.span ℂ (Set.range
      (fun T : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} => youngVec Y T.1)) := by
  classical
  set Sp := Submodule.span ℂ (Set.range
      (fun T : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} => youngVec Y T.1))
  induction hk : PhiMax Y - Phi Y w using Nat.strong_induction_on generalizing w with
  | _ k ih =>
  have IH : ∀ w', Phi Y w < Phi Y w' → V Y w' ∈ Sp := fun w' h =>
    ih (PhiMax Y - Phi Y w') (by have := Phi_le Y w'; omega) w' rfl
  by_cases hrep : ∃ p q, p ≠ q ∧ colOf Y p = colOf Y q ∧ w p = w q
  · obtain ⟨p, q, hpq, hc, hw⟩ := hrep
    rw [V_repeat Y w hpq hc hw]; exact Submodule.zero_mem _
  push Not at hrep
  by_cases hinv : ∃ p q, colOf Y p = colOf Y q ∧ rowOf Y p < rowOf Y q ∧ w q < w p
  · obtain ⟨p, q, hc, hr, hw⟩ := hinv
    have hpq : p ≠ q := by rintro rfl; omega
    have h1 := V_comp_col Y w (swap_mem_col Y hc)
    rw [Equiv.Perm.sign_swap hpq] at h1
    have hmem := IH (w ∘ ⇑(Equiv.swap p q))
      (Phi_lt_of_R Y _ _ (Qp_swap Y w hc).symm (Rp_lt_swap Y w hr hw))
    rw [h1] at hmem
    have := Sp.smul_mem (-1 : ℂ) hmem
    simpa using this
  push Not at hinv
  have hcs : ∀ p q, colOf Y p = colOf Y q → rowOf Y p < rowOf Y q → w p < w q :=
    fun p q hc hr => lt_of_le_of_ne (hinv p q hc hr) (hrep p q (by rintro rfl; omega) hc)
  by_cases hrw : ∀ p q, rowOf Y p = rowOf Y q → colOf Y p < colOf Y q → w p ≤ w q
  · obtain ⟨hT, hwT⟩ := ssyt_of_word Y w hcs hrw
    rw [← hwT]
    exact Submodule.subset_span ⟨⟨_, hT⟩, rfl⟩
  push Not at hrw
  obtain ⟨p, q, hr, hc, hw⟩ := hrw
  have hg := hG w p q hr hc
  rw [← Finset.sum_filter_add_sum_filter_not (SX Y p q) (fun σ => σ ∈ columnPermutations Y)] at hg
  set N : ℂ := ((((SX Y p q).filter (fun σ => σ ∈ columnPermutations Y)).card : ℕ) : ℂ) with hNdef
  have hdiag : ∑ σ ∈ (SX Y p q).filter (fun σ => σ ∈ columnPermutations Y),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • V Y (w ∘ ⇑σ) = N • V Y w := by
    rw [hNdef, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rw [V_comp_col Y w hσ.2, smul_smul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hrest : ∑ σ ∈ (SX Y p q).filter (fun σ => σ ∉ columnPermutations Y),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • V Y (w ∘ ⇑σ) ∈ Sp :=
    Submodule.sum_mem _ fun σ hσ => by
      rw [Finset.mem_filter] at hσ
      exact Sp.smul_mem _ (IH _ (Phi_lt_of_Q Y _ _ (hQ w p q hr hc hw hcs σ hσ.1 hσ.2)))
  rw [hdiag] at hg
  have hN : N ≠ 0 := by
    have h1 : (1 : Equiv.Perm (Fin n)) ∈
        (SX Y p q).filter (fun σ => σ ∈ columnPermutations Y) := by
      rw [Finset.mem_filter]
      refine ⟨?_, one_mem_col Y⟩
      unfold SX; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, fun x _ => rfl⟩
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem h1)
  have hV : V Y w = N⁻¹ • -(∑ σ ∈ (SX Y p q).filter (fun σ => σ ∉ columnPermutations Y),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • V Y (w ∘ ⇑σ)) := by
    rw [← eq_neg_of_add_eq_zero_left hg, inv_smul_smul₀ hN]
  rw [hV]
  exact Sp.smul_mem _ (Sp.neg_mem hrest)

theorem swap_mem_row {u v : Fin n} (hr : rowOf Y u = rowOf Y v) :
    Equiv.swap u v ∈ rowPermutations Y := mem_row_of Y fun i => by
  rcases eq_or_ne i u with rfl | hiu
  · simp [Equiv.swap_apply_left, hr]
  · rcases eq_or_ne i v with rfl | hiv
    · simp [Equiv.swap_apply_right, hr]
    · rw [Equiv.swap_apply_of_ne_of_ne hiu hiv]

theorem hcell (y : Fin n) : rowOf Y y < Y.val.colLen (colOf Y y) := by
  have h := ((cellNumbering Y).symm y).2
  rw [YoungDiagram.mem_cells] at h
  exact YoungDiagram.mem_iff_lt_colLen.mp h

theorem garnir_pigeon {p q : Fin n} (hr : rowOf Y p = rowOf Y q) (hc : colOf Y p < colOf Y q)
    {b : Equiv.Perm (Fin n)} (hb : b ∈ columnPermutations Y) :
    ∃ x1 ∈ Xset Y p q, ∃ x2 ∈ Xset Y p q, x1 ≠ x2 ∧ rowOf Y (b x1) = rowOf Y (b x2) := by
  classical
  have hrowlt : ∀ x ∈ Xset Y p q, rowOf Y (b x) < Y.val.colLen (colOf Y p) := by
    intro x hx
    have h1 := hcell Y (b x)
    rw [mem_col Y hb x] at h1
    unfold Xset at hx; rw [Finset.mem_filter] at hx
    rcases hx.2 with ⟨hx1, _⟩ | ⟨hx1, _⟩
    · rw [hx1] at h1; exact h1
    · rw [hx1] at h1; exact lt_of_lt_of_le h1 (Y.val.colLen_anti _ _ hc.le)
  have hq := hcell Y q
  let f : ℕ → Fin n := fun r =>
    if h : r ≤ rowOf Y q then
      cellNumbering Y ⟨(r, colOf Y q), YoungDiagram.mem_iff_lt_colLen.mpr (by omega)⟩
    else if h2 : r - 1 < Y.val.colLen (colOf Y p) then
      cellNumbering Y ⟨(r - 1, colOf Y p), YoungDiagram.mem_iff_lt_colLen.mpr h2⟩
    else p
  have hfX : ∀ r ∈ Finset.range (Y.val.colLen (colOf Y p) + 1), f r ∈ Xset Y p q := by
    intro r hrr
    rw [Finset.mem_range] at hrr
    simp only [f]
    split_ifs with h h2
    · unfold Xset; rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Or.inr ⟨by simp [colOf], ?_⟩⟩
      simp only [rowOf, Equiv.symm_apply_apply]; exact h
    · unfold Xset; rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Or.inl ⟨by simp [colOf], ?_⟩⟩
      simp only [rowOf, Equiv.symm_apply_apply] at hr h ⊢
      omega
    · omega
  have hfinj : Set.InjOn f ↑(Finset.range (Y.val.colLen (colOf Y p) + 1)) := by
    intro r1 hr1 r2 hr2 heq
    simp only [Finset.coe_range, Set.mem_Iio] at hr1 hr2
    simp only [f] at heq
    split_ifs at heq
    all_goals first
      | (have h3 := congrArg (rowOf Y) heq; simp only [rowOf, Equiv.symm_apply_apply] at h3; omega)
      | (have h3 := congrArg (colOf Y) heq; simp only [colOf, Equiv.symm_apply_apply] at h3 hc; omega)
      | omega
  obtain ⟨r1, hr1, r2, hr2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (Y.val.colLen (colOf Y p) + 1))
    (t := Finset.range (Y.val.colLen (colOf Y p))) (f := fun r => rowOf Y (b (f r))) (by simp)
    (fun r hr => Finset.mem_range.mpr (hrowlt _ (hfX r hr)))
  exact ⟨f r1, hfX r1 hr1, f r2, hfX r2 hr2,
    fun h => hne (hfinj (Finset.mem_coe.mpr hr1) (Finset.mem_coe.mpr hr2) h), heq⟩

theorem garnir : GarnirP Y := by
  classical
  intro w p q hr hc
  refine PiLp.ext fun x => ?_
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_zero, Finset.sum_apply,
    Pi.smul_apply, Pi.zero_apply, smul_eq_mul, V_apply]
  calc _ = ∑ σ ∈ SX Y p q, ∑ a ∈ rowPermutations Y, ∑ b ∈ columnPermutations Y,
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) *
          (if x ∘ ⇑a ∘ ⇑b = w ∘ ⇑σ then 1 else 0)) := by simp only [Finset.mul_sum]
    _ = ∑ z ∈ SX Y p q ×ˢ rowPermutations Y, ∑ b ∈ columnPermutations Y,
        (((Equiv.Perm.sign z.1 : ℤˣ) : ℤ) : ℂ) * ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) *
          (if x ∘ ⇑z.2 ∘ ⇑b = w ∘ ⇑z.1 then 1 else 0)) := by rw [Finset.sum_product]
    _ = ∑ b ∈ columnPermutations Y, ∑ z ∈ SX Y p q ×ˢ rowPermutations Y,
        (((Equiv.Perm.sign z.1 : ℤˣ) : ℤ) : ℂ) * ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) *
          (if x ∘ ⇑z.2 ∘ ⇑b = w ∘ ⇑z.1 then 1 else 0)) := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun b hb => ?_
  obtain ⟨x1, hx1, x2, hx2, hx12, hrow12⟩ := garnir_pigeon Y hr hc hb
  have htb : Equiv.swap (b x1) (b x2) * b = b * Equiv.swap x1 x2 := by
    rw [Equiv.swap_apply_apply]; group
  have ht := swap_mem_row Y hrow12
  have hsX : ∀ σ ∈ SX Y p q, σ * Equiv.swap x1 x2 ∈ SX Y p q := by
    intro σ hσ
    unfold SX at hσ ⊢; rw [Finset.mem_filter] at hσ ⊢
    refine ⟨Finset.mem_univ _, fun y hy => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (fun h => hy (by rw [h]; exact hx1))
      (fun h => hy (by rw [h]; exact hx2)), hσ.2 y hy]
  have haR : ∀ a ∈ rowPermutations Y, a * Equiv.swap (b x1) (b x2) ∈ rowPermutations Y := by
    intro a ha
    exact mem_row_of Y fun i => by rw [Equiv.Perm.mul_apply, mem_row Y ha, mem_row Y ht]
  have hcomp : ∀ (σ a : Equiv.Perm (Fin n)),
      (x ∘ ⇑(a * Equiv.swap (b x1) (b x2)) ∘ ⇑b = w ∘ ⇑(σ * Equiv.swap x1 x2)) ↔
        (x ∘ ⇑a ∘ ⇑b = w ∘ ⇑σ) := by
    intro σ a
    have e1 : x ∘ ⇑(a * Equiv.swap (b x1) (b x2)) ∘ ⇑b = (x ∘ ⇑a ∘ ⇑b) ∘ ⇑(Equiv.swap x1 x2) := by
      funext i
      have h := DFunLike.congr_fun htb i
      simp only [Equiv.Perm.mul_apply] at h
      simp only [Function.comp_apply, Equiv.Perm.mul_apply, h]
    have e2 : w ∘ ⇑(σ * Equiv.swap x1 x2) = (w ∘ ⇑σ) ∘ ⇑(Equiv.swap x1 x2) := by
      rw [Equiv.Perm.coe_mul]; rfl
    rw [e1, e2]
    constructor
    · intro h; funext i
      have := congrFun h (Equiv.swap x1 x2 i)
      simpa [Equiv.swap_apply_self] using this
    · intro h; rw [h]
  refine Finset.sum_involution
    (fun z _ => (z.1 * Equiv.swap x1 x2, z.2 * Equiv.swap (b x1) (b x2))) ?_ ?_ ?_ ?_
  · rintro ⟨σ, a⟩ _
    simp only [hcomp]
    simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hx12, Units.val_mul, Units.val_neg,
      Units.val_one, Int.cast_mul, Int.cast_neg, Int.cast_one]
    ring
  · rintro ⟨σ, a⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    have h1 : Equiv.swap x1 x2 = 1 := mul_left_cancel (h.1.trans (mul_one σ).symm)
    have h2 := DFunLike.congr_fun h1 x1
    rw [Equiv.swap_apply_left] at h2
    exact hx12 h2.symm
  · rintro ⟨σ, a⟩ hz
    rw [Finset.mem_product] at hz ⊢
    exact ⟨hsX σ hz.1, haR a hz.2⟩
  · rintro ⟨σ, a⟩ _
    simp [mul_assoc, Equiv.swap_mul_self]

theorem qinc : QincP Y := by
  classical
  intro w p q hr hc hw hcs σ hσ hσc
  have hσX : ∀ x, x ∉ Xset Y p q → σ x = x := by
    unfold SX at hσ; rw [Finset.mem_filter] at hσ; exact hσ.2
  have hmemX : ∀ x, x ∈ Xset Y p q ↔ ((colOf Y x = colOf Y p ∧ rowOf Y p ≤ rowOf Y x) ∨
      (colOf Y x = colOf Y q ∧ rowOf Y x ≤ rowOf Y q)) := by
    intro x; unfold Xset; simp
  have hinvX : ∀ j, j ∉ Xset Y p q → σ⁻¹ j = j := by
    intro j hj; rw [Equiv.Perm.inv_eq_iff_eq]; exact (hσX j hj).symm
  have hinvX' : ∀ j, j ∈ Xset Y p q → σ⁻¹ j ∈ Xset Y p q := by
    intro j hj
    by_contra h
    have h1 := hσX _ h
    rw [show σ (σ⁻¹ j) = j by simp] at h1
    rw [← h1] at h
    exact h hj
  have hw' : (w q : ℕ) < (w p : ℕ) := hw
  obtain ⟨δ, hδdef⟩ : ∃ δ : Fin n → ℤ, δ = fun j => (colOf Y (σ⁻¹ j) : ℤ) - colOf Y j := ⟨_, rfl⟩
  have hsumδ : ∑ j, δ j = 0 := by
    simp only [hδdef, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact Equiv.sum_comp σ⁻¹ (fun j => (colOf Y j : ℤ))
  have hQσ : (Qp Y (w ∘ ⇑σ) : ℤ) = ∑ j, (colOf Y (σ⁻¹ j) : ℤ) * ((w j : ℕ) : ℤ) := by
    unfold Qp; push_cast
    exact (Equiv.sum_comp σ⁻¹ (fun i => (colOf Y i : ℤ) * ((w (σ i) : ℕ) : ℤ))).symm.trans
      (Finset.sum_congr rfl fun j _ => by simp)
  have hQ : (Qp Y w : ℤ) = ∑ j, (colOf Y j : ℤ) * ((w j : ℕ) : ℤ) := by
    unfold Qp; push_cast; rfl
  have hD : (Qp Y (w ∘ ⇑σ) : ℤ) - Qp Y w = ∑ j, δ j * (((w j : ℕ) : ℤ) - ((w p : ℕ) : ℤ)) := by
    rw [hQσ, hQ, ← Finset.sum_sub_distrib]
    have e : ∀ j, (colOf Y (σ⁻¹ j) : ℤ) * ((w j : ℕ) : ℤ) - (colOf Y j : ℤ) * ((w j : ℕ) : ℤ) =
        δ j * (((w j : ℕ) : ℤ) - ((w p : ℕ) : ℤ)) + δ j * ((w p : ℕ) : ℤ) := by
      intro j; rw [hδdef]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hsumδ, zero_mul, add_zero]
  have hterm : ∀ j, |δ j| - δ j ≤ 2 * (δ j * (((w j : ℕ) : ℤ) - ((w p : ℕ) : ℤ))) := by
    intro j
    by_cases hj : j ∈ Xset Y p q
    · have hj' := hinvX' j hj
      rw [hmemX] at hj hj'
      rcases hj with ⟨hcj, hrj⟩ | ⟨hcj, hrj⟩
      · have hwj : (w p : ℕ) ≤ (w j : ℕ) := by
          rcases eq_or_lt_of_le hrj with h | h
          · have : p = j := cell_ext Y h hcj.symm
            subst this; exact le_rfl
          · exact le_of_lt (hcs p j hcj.symm h)
        have hδ : 0 ≤ δ j := by
          rw [hδdef]
          rcases hj' with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [h1, hcj] <;> omega
        rw [abs_of_nonneg hδ]
        have h0 : (0 : ℤ) ≤ ((w j : ℕ) : ℤ) - ((w p : ℕ) : ℤ) := by omega
        nlinarith [mul_nonneg hδ h0]
      · have hwj : (w j : ℕ) < (w p : ℕ) := by
          have h2 : (w j : ℕ) ≤ (w q : ℕ) := by
            rcases eq_or_lt_of_le hrj with h | h
            · have : j = q := cell_ext Y h hcj
              subst this; exact le_rfl
            · exact le_of_lt (hcs j q hcj h)
          omega
        have hδ : δ j ≤ 0 := by
          rw [hδdef]
          rcases hj' with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only [h1, hcj] <;> omega
        rw [abs_of_nonpos hδ]
        have h0 : ((w j : ℕ) : ℤ) - ((w p : ℕ) : ℤ) + 1 ≤ 0 := by omega
        nlinarith [mul_nonneg_of_nonpos_of_nonpos hδ h0]
    · have : δ j = 0 := by rw [hδdef]; simp only [hinvX j hj, sub_self]
      rw [this]; simp
  have hsum : ∑ j, |δ j| ≤ 2 * ((Qp Y (w ∘ ⇑σ) : ℤ) - Qp Y w) := by
    rw [hD, Finset.mul_sum]
    calc ∑ j, |δ j| = ∑ j, (|δ j| - δ j) := by rw [Finset.sum_sub_distrib, hsumδ, sub_zero]
      _ ≤ _ := Finset.sum_le_sum fun j _ => hterm j
  have hex : ∃ j, δ j ≠ 0 := by
    by_contra h
    push Not at h
    apply hσc
    apply mem_col_of Y
    intro i
    have := h (σ i)
    rw [hδdef] at this
    simp only [show σ⁻¹ (σ i) = i by simp] at this
    omega
  obtain ⟨j0, hj0⟩ := hex
  have h1 : (1 : ℤ) ≤ ∑ j, |δ j| :=
    calc (1 : ℤ) ≤ |δ j0| := Int.one_le_abs hj0
      _ ≤ ∑ j, |δ j| := Finset.single_le_sum (f := fun j => |δ j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ j0)
  have : (Qp Y w : ℤ) < Qp Y (w ∘ ⇑σ) := by omega
  exact_mod_cast this

theorem youngSpan (w : Fin n → Fin d) :
    V Y w ∈ Submodule.span ℂ (Set.range
      (fun T : {T : Y.val.cells → Fin d // IsSemistandardFilling Y T} => youngVec Y T.1)) :=
  V_mem_span Y (garnir Y) (qinc Y) w

end span

end KW20K

open QAlgorithms QAlgorithms.Schur in
theorem solution {d N : ℕ} (Y : Partition d N) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : Fin d → ℝ) :
    LinearMap.trace ℂ (schurModule Y)
        (polynomialRepresentation Y (U * Matrix.diagonal (fun j => (r j : ℂ)) * star U)) =
      ((MvPolynomial.eval r (schurPolynomial Y) : ℝ) : ℂ) := by
  exact glue_eq20 Y (KW20K.youngIndep Y) (fun w => KW20K.youngSpan Y w) U hU r
