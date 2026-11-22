-- Prove2me | solution 1 for MixedCloning.Optimal.proposition_20
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T06:39:53.535632+00:00
-- url     : https://prove2.me/submissions/065d7713-21ad-41f0-be80-474f394194b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MixedCloning_Optimal_lemma_21
import Theorems.Thm_MixedCloning_Optimal_lemma_22
import Theorems.Thm_MixedCloning_Optimal_lemma_23
import Theorems.Thm_MixedCloning_Optimal_lemma_9
import Theorems.Thm_MixedCloning_Optimal_branching

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq


/-! ## Separable matrices: closure under the algebraic operations -/

section SepAlg
variable {a b : Type}

lemma p20_sep_zero [Fintype a] [Fintype b] : Separable (0 : Op (a × b)) :=
  ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, fun j => j.elim0, by simp⟩

lemma p20_sep_add [Fintype a] [Fintype b] {X Y : Op (a × b)} (hX : Separable X) (hY : Separable Y) :
    Separable (X + Y) := by
  obtain ⟨N, w, A, B, h, rfl⟩ := hX
  obtain ⟨N', w', A', B', h', rfl⟩ := hY
  refine ⟨N + N', Fin.append w w', Fin.append A A', Fin.append B B', ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]; exact h i
    · simp only [Fin.append_right]; exact h' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

lemma p20_sep_smul [Fintype a] [Fintype b] {X : Op (a × b)} (hX : Separable X) {t : ℝ} (ht : 0 ≤ t) :
    Separable ((t : ℂ) • X) := by
  obtain ⟨N, w, A, B, h, rfl⟩ := hX
  refine ⟨N, fun j => t * w j, A, B, fun j => ⟨mul_nonneg ht (h j).1, (h j).2⟩, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  push_cast
  rfl

lemma p20_sep_sum [Fintype a] [Fintype b] {ι : Type} (s : Finset ι) (f : ι → Op (a × b))
    (hf : ∀ i ∈ s, Separable (f i)) : Separable (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (p20_sep_zero (a := a) (b := b))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact p20_sep_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma p20_one_eq_kron [DecidableEq a] [DecidableEq b] [DecidableEq (a × b)] :
    (1 : Op (a × b)) = Matrix.kronecker (1 : Op a) (1 : Op b) := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  rw [Matrix.one_apply]
  change _ = (1 : Op a) i i' * (1 : Op b) j j'
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases h1 : i = i' <;> by_cases h2 : j = j'
  · rw [if_pos (by rw [h1, h2]), if_pos h1, if_pos h2, mul_one]
  · rw [if_neg (by intro h; exact h2 (Prod.mk.inj h).2), if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg (by intro h; exact h1 (Prod.mk.inj h).1), if_neg h1, zero_mul]
  · rw [if_neg (by intro h; exact h1 (Prod.mk.inj h).1), if_neg h1, zero_mul]

lemma p20_sep_one [Fintype a] [Fintype b] [DecidableEq (a × b)] {t : ℝ} (ht : 0 ≤ t) :
    Separable ((t : ℂ) • (1 : Op (a × b))) := by
  refine ⟨1, fun _ => t, fun _ => 1, fun _ => 1,
    fun _ => ⟨ht, Matrix.PosSemidef.one, Matrix.PosSemidef.one⟩, ?_⟩
  rw [Fin.sum_univ_one, p20_one_eq_kron]

lemma p20_sep_conj [Fintype a] [Fintype b] {a' b' : Type} [Fintype a'] [Fintype b'] (P : Matrix a a' ℂ)
    (Q : Matrix b b' ℂ) {X : Op (a' × b')} (hX : Separable X) :
    Separable (Matrix.kronecker P Q * X * (Matrix.kronecker P Q)ᴴ) := by
  obtain ⟨N, w, A, B, h, rfl⟩ := hX
  refine ⟨N, w, fun j => P * A j * Pᴴ, fun j => Q * B j * Qᴴ,
    fun j => ⟨(h j).1, (h j).2.1.mul_mul_conjTranspose_same P,
      (h j).2.2.mul_mul_conjTranspose_same Q⟩, ?_⟩
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.kronecker]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

lemma p20_reindex_kron (A : Op a) (B : Op b) :
    reindex (Equiv.prodComm b a) (Equiv.prodComm b a) (Matrix.kronecker B A) =
      Matrix.kronecker A B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  change B j j' * A i i' = A i i' * B j j'
  ring

lemma p20_sep_swap [Fintype a] [Fintype b] {X : Op (b × a)} (hX : Separable X) :
    Separable (reindex (Equiv.prodComm b a) (Equiv.prodComm b a) X) := by
  obtain ⟨N, w, A, B, h, rfl⟩ := hX
  refine ⟨N, w, B, A, fun j => ⟨(h j).1, (h j).2.2, (h j).2.1⟩, ?_⟩
  have e : ∀ Y : Op (b × a), reindex (Equiv.prodComm b a) (Equiv.prodComm b a) Y =
      reindexLinearEquiv ℂ ℂ (Equiv.prodComm b a) (Equiv.prodComm b a) Y := fun Y => rfl
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ← e, p20_reindex_kron]

end SepAlg

/-! ## Reindexing and conjugation commute with the Bochner integral -/

lemma p20_reindex_integral {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {m n : Type}
    [Fintype m] [Fintype n] (e : m ≃ n) (f : Ω → Op m) :
    reindex e e (∫ x, f x ∂μ) = ∫ x, reindex e e (f x) ∂μ := by
  have h := ContinuousLinearEquiv.integral_comp_comm (μ := μ)
    (Matrix.reindexLinearEquiv ℂ ℂ e e).toContinuousLinearEquiv f
  exact h.symm

lemma p20_reindex_one {m n : Type} [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    reindex e e (1 : Matrix m m ℂ) = 1 := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun h' => h (e.symm.injective h')), if_neg h]

/-- Conjugation by a unitary, as a linear equivalence. -/
def p20Conj {m : Type} [Fintype m] [DecidableEq m] (W : Op m) (hW : W * Wᴴ = 1)
    (hW' : Wᴴ * W = 1) : Op m ≃ₗ[ℂ] Op m where
  toFun X := Wᴴ * X * W
  invFun X := W * X * Wᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]
  left_inv X := by
    change W * (Wᴴ * X * W) * Wᴴ = X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW, Matrix.one_mul, Matrix.mul_assoc, hW,
      Matrix.mul_one]
  right_inv X := by
    change Wᴴ * (W * X * Wᴴ) * W = X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW', Matrix.one_mul, Matrix.mul_assoc, hW',
      Matrix.mul_one]

lemma p20_conj_integral {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {m : Type}
    [Fintype m] [DecidableEq m] (W : Op m) (hW : W * Wᴴ = 1) (hW' : Wᴴ * W = 1)
    (f : Ω → Op m) :
    Wᴴ * (∫ x, f x ∂μ) * W = ∫ x, Wᴴ * f x * W ∂μ := by
  have h := ContinuousLinearEquiv.integral_comp_comm (μ := μ)
    (p20Conj W hW hW').toContinuousLinearEquiv f
  exact h.symm

/-! ## Young-diagram combinatorics -/

lemma p20_mem_tail {L : YoungDiagram} {i j : ℕ} : (i, j) ∈ tailDiagram L ↔ (i+1, j) ∈ L := by
  change (i, j) ∈ ((L.cells.filter fun c => 0 < c.1).image fun c => (c.1-1, c.2)) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨x, y⟩, hxy, heq⟩
    rw [Finset.mem_filter] at hxy
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hx : x = i + 1 := by have := hxy.2; simp only at this; omega
    rw [← YoungDiagram.mem_cells]
    rw [← h2, ← hx]
    exact hxy.1
  · intro h
    exact ⟨(i+1, j), Finset.mem_filter.mpr ⟨(YoungDiagram.mem_cells _).mpr h, by simp⟩, by simp⟩

lemma p20_tail_rowLen (L : YoungDiagram) (i : ℕ) :
    (tailDiagram L).rowLen i = L.rowLen (i+1) := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have h' : (i, L.rowLen (i+1)) ∈ tailDiagram L := YoungDiagram.mem_iff_lt_rowLen.mpr h
    rw [p20_mem_tail, YoungDiagram.mem_iff_lt_rowLen] at h'
    exact lt_irrefl _ h'
  · by_contra h
    push Not at h
    have h' : (i+1, (tailDiagram L).rowLen i) ∈ L := YoungDiagram.mem_iff_lt_rowLen.mpr h
    rw [← p20_mem_tail, YoungDiagram.mem_iff_lt_rowLen] at h'
    exact lt_irrefl _ h'

lemma p20_height_le_iff (L : YoungDiagram) (n : ℕ) : height L ≤ n ↔ (n, 0) ∉ L := by
  unfold height
  rw [YoungDiagram.mem_iff_lt_colLen]
  omega

lemma p20_height_sup (L M : YoungDiagram) (n : ℕ) :
    height (L ⊔ M) ≤ n ↔ height L ≤ n ∧ height M ≤ n := by
  simp only [p20_height_le_iff, YoungDiagram.mem_sup, not_or]

lemma p20_height_tail (L : YoungDiagram) (n : ℕ) :
    height (tailDiagram L) ≤ n ↔ height L ≤ n + 1 := by
  rw [p20_height_le_iff, p20_height_le_iff, p20_mem_tail]

lemma p20_tail_mem_branches (d : ℕ) (L : YoungDiagram) (hL : height L ≤ d + 1) :
    tailDiagram L ∈ branches d L := by
  unfold branches
  rw [Finset.mem_filter]
  refine ⟨?_, fun i => ?_⟩
  · unfold diagramsInBox
    rw [Finset.mem_biUnion]
    refine ⟨(tailDiagram L).cells, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro x hx
      obtain ⟨i, j⟩ := x
      have hx' : (i, j) ∈ tailDiagram L := (YoungDiagram.mem_cells _).mp hx
      rw [p20_mem_tail] at hx'
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      constructor
      · have h0 : (i+1, 0) ∈ L := L.up_left_mem le_rfl (Nat.zero_le _) hx'
        rw [YoungDiagram.mem_iff_lt_colLen] at h0
        unfold height at hL
        simp only
        omega
      · rw [YoungDiagram.mem_iff_lt_rowLen] at hx'
        have := L.rowLen_anti 0 (i+1) (Nat.zero_le _)
        simp only
        omega
    · rw [dif_pos (tailDiagram L).isLowerSet, Finset.mem_singleton]
  · rw [p20_tail_rowLen]
    exact ⟨le_rfl, L.rowLen_anti i (i+1) (Nat.le_succ i)⟩

lemma p20_branch_height {d : ℕ} {M M' : YoungDiagram} (h : M' ∈ branches d M) :
    height M' ≤ d := by
  unfold branches at h
  rw [Finset.mem_filter] at h
  obtain ⟨h1, -⟩ := h
  unfold diagramsInBox at h1
  obtain ⟨S, hS, hM'⟩ := Finset.mem_biUnion.mp h1
  split_ifs at hM' with hs
  · rw [Finset.mem_singleton] at hM'
    subst hM'
    rw [p20_height_le_iff]
    intro hmem
    have := Finset.mem_powerset.mp hS hmem
    simp at this
  · simp at hM'

lemma p20_tail_le_branch {d : ℕ} {M M' : YoungDiagram} (h : M' ∈ branches d M) :
    tailDiagram M ≤ M' := by
  rw [← YoungDiagram.cells_subset_iff]
  intro x hx
  obtain ⟨i, j⟩ := x
  have hx' : (i, j) ∈ tailDiagram M := (YoungDiagram.mem_cells _).mp hx
  rw [p20_mem_tail, YoungDiagram.mem_iff_lt_rowLen] at hx'
  apply (YoungDiagram.mem_cells _).mpr
  rw [YoungDiagram.mem_iff_lt_rowLen]
  unfold branches at h
  exact lt_of_lt_of_le hx' ((Finset.mem_filter.mp h).2 i).1

lemma p20_eq_bot_of_height (L : YoungDiagram) (h : height L = 0) : L = ⊥ := by
  apply SetLike.ext
  intro x
  obtain ⟨i, j⟩ := x
  refine ⟨fun hx => ?_, fun hx => absurd hx (YoungDiagram.notMem_bot _)⟩
  have h0 : (0, 0) ∈ L := L.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hx
  rw [YoungDiagram.mem_iff_lt_colLen] at h0
  unfold height at h
  omega

lemma p20_tail_eq_bot (L : YoungDiagram) (h : height L ≤ 1) : tailDiagram L = ⊥ :=
  p20_eq_bot_of_height _ (by have := (p20_height_tail L 0).mpr h; omega)

lemma p20_schurCount_pos (L : YoungDiagram) (t : ℕ) (h : height L ≤ t) : 0 < schurCount L t := by
  unfold schurCount
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨fun c => ⟨c.val.1, ?_⟩, ?_, ?_⟩⟩
  · have hc : (c.val.1, 0) ∈ L :=
      L.up_left_mem le_rfl (Nat.zero_le _) ((YoungDiagram.mem_cells _).mp c.2)
    rw [YoungDiagram.mem_iff_lt_colLen] at hc
    unfold height at h
    omega
  · intro x y hxy _
    exact Fin.mk_le_mk.mpr hxy.le
  · intro x y _ hlt
    exact Fin.mk_lt_mk.mpr hlt

lemma p20_schurCount_eq_zero (L : YoungDiagram) (t : ℕ) (h : t < height L) :
    schurCount L t = 0 := by
  unfold schurCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  rintro ⟨T, -, hcol⟩
  let f : Fin (height L) → Fin t := fun k =>
    T ⟨(k.val, 0), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_colLen.mpr k.2)⟩
  have hf : StrictMono f := fun k1 k2 hk => hcol _ _ rfl hk
  have := Fintype.card_le_of_injective f hf.injective
  simp only [Fintype.card_fin] at this
  omega

lemma p20_ratio_eq_zero (X : YoungDiagram) (r d : ℕ) (h : r < height X) : ratio X r d = 0 := by
  unfold ratio
  rw [p20_schurCount_eq_zero X r h]
  simp

lemma p20_schurCount_bot (t : ℕ) : schurCount ⊥ t = 1 := by
  haveI : IsEmpty (Cell (⊥ : YoungDiagram)) :=
    ⟨fun c => YoungDiagram.notMem_bot _ ((YoungDiagram.mem_cells _).mp c.2)⟩
  unfold schurCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨isEmptyElim, fun x => isEmptyElim x, fun x => isEmptyElim x⟩, ?_⟩
  rintro ⟨T, hT⟩
  apply Subtype.ext
  funext c
  exact isEmptyElim c

lemma p20_schurCount_zero_le (X : YoungDiagram) : schurCount X 0 ≤ 1 := by
  unfold schurCount
  apply Fintype.card_le_one_iff_subsingleton.mpr
  constructor
  rintro ⟨T1, _⟩ ⟨T2, _⟩
  apply Subtype.ext
  funext c
  exact (T1 c).elim0

lemma p20_ratio_zero_le (X : YoungDiagram) (d : ℕ) (hX : height X ≤ d) :
    ratio X 0 d ≤ ratio ⊥ 0 d := by
  unfold ratio
  rw [p20_schurCount_bot, p20_schurCount_bot, Nat.cast_one, div_one]
  have h1 := p20_schurCount_zero_le X
  have h2 := p20_schurCount_pos X d hX
  rw [div_le_one (by exact_mod_cast h2)]
  exact_mod_cast h1.trans h2

/-! ## Continuity of `q` (for the integrability of the lift integrand) -/

/-- The linear part of `q`. -/
def p20Psi (L : YoungDiagram) {d : ℕ} (b : SchurBasis L d) :
    Op (Cell L → Fin d) →ₗ[ℂ] Op (SchurIndex L d) where
  toFun T := LinearMap.toMatrix b.toBasis b.toBasis
    ((schurModule L d).orthogonalProjectionOnto.toLinearMap.comp
      ((Matrix.toEuclideanLin T).comp (schurModule L d).subtype))
  map_add' S T := by simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c T := by simp [LinearMap.smul_comp, LinearMap.comp_smul]

lemma p20_cellTensor_continuous (L : YoungDiagram) (d : ℕ) :
    Continuous (fun A : Op (Fin d) => cellTensor L A) := by
  unfold cellTensor
  fun_prop

lemma p20_q_continuous (L : YoungDiagram) {d : ℕ} (b : SchurBasis L d) :
    Continuous (fun A : Op (Fin d) => q L b A) := by
  have h1 := (p20Psi L b).continuous_of_finiteDimensional
  exact h1.comp (p20_cellTensor_continuous L d)

lemma p20_q_unitary_continuous (L : YoungDiagram) {d : ℕ} (b : SchurBasis L d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => q L b (U : Op (Fin d))) :=
  (p20_q_continuous L b).comp continuous_subtype_val

lemma p20_cont_kron {X : Type} [TopologicalSpace X] {l m n p : Type}
    {A : X → Matrix l m ℂ} {B : X → Matrix n p ℂ} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => Matrix.kronecker (A x) (B x)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun x => A x i.1 j.1 * B x i.2 j.2
  exact (hA.matrix_elem i.1 j.1).mul (hB.matrix_elem i.2 j.2)

lemma p20_integral_sub {d : ℕ} {ι : Type} [Fintype ι]
    (f g : Matrix.unitaryGroup (Fin d) ℂ → Op ι)
    (hf : Continuous f) (hg : Continuous g) :
    ∫ U, (f U - g U) ∂haar d = (∫ U, f U ∂haar d) - ∫ U, g U ∂haar d := by
  refine integral_sub ?_ ?_
  · exact hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact
  · exact hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

/-! ## The lift is linear in the needed form -/

lemma p20_lift_smul_sub {d : ℕ} {L M : YoungDiagram} (E : BranchFamily d L)
    (G : BranchFamily d M) (L' : {L' : YoungDiagram // L' ∈ branches d L})
    (M' : {M' : YoungDiagram // M' ∈ branches d M}) (t : ℂ)
    (X Y : Op (SchurIndex L'.val d × SchurIndex M'.val d)) :
    lift E G L' M' (t • X - Y) = t • lift E G L' M' X - lift E G L' M' Y := by
  unfold lift
  dsimp only
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hV : Continuous fun U : Matrix.unitaryGroup (Fin (d+1)) ℂ =>
      Matrix.kronecker (q L (schurBasis L (d+1)) (U : Op (Fin (d+1))))
        (q M (schurBasis M (d+1)) (U : Op (Fin (d+1)))) :=
    p20_cont_kron (p20_q_unitary_continuous L _) (p20_q_unitary_continuous M _)
  rw [p20_integral_sub _ _ ?_ ?_, integral_smul]
  · exact ((((hV.matrix_mul continuous_const).matrix_mul continuous_const).matrix_mul
      continuous_const).matrix_mul hV.matrix_conjTranspose).const_smul t
  · exact (((hV.matrix_mul continuous_const).matrix_mul continuous_const).matrix_mul
      continuous_const).matrix_mul hV.matrix_conjTranspose

/-! ## `q` on the empty diagram -/

lemma p20_cellTensor_bot {d : ℕ} (A : Op (Fin d)) [DecidableEq (Cell ⊥ → Fin d)] :
    cellTensor ⊥ A = 1 := by
  haveI : IsEmpty (Cell (⊥ : YoungDiagram)) :=
    ⟨fun c => YoungDiagram.notMem_bot _ ((YoungDiagram.mem_cells _).mp c.2)⟩
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  simp [cellTensor]

lemma p20_polyRep_bot {d : ℕ} (A : Op (Fin d)) :
    polynomialRepresentation ⊥ A = LinearMap.id := by
  apply LinearMap.ext
  intro v
  unfold polynomialRepresentation
  rw [LinearMap.comp_apply, LinearMap.comp_apply, p20_cellTensor_bot]
  have h1 : Matrix.toEuclideanLin (1 : Op (Cell ⊥ → Fin d)) ((schurModule ⊥ d).subtype v) =
      (v : EuclideanSpace ℂ (Cell ⊥ → Fin d)) := by
    change WithLp.toLp 2 ((1 : Op (Cell ⊥ → Fin d)) *ᵥ WithLp.ofLp (v : EuclideanSpace ℂ _)) = _
    rw [Matrix.one_mulVec]
  rw [h1]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v

lemma p20_q_bot {d : ℕ} (b : SchurBasis ⊥ d) (A : Op (Fin d)) : q ⊥ b A = 1 := by
  unfold q
  rw [p20_polyRep_bot]
  exact LinearMap.toMatrix_id b.toBasis



/-! ## `q` of a rank-`r` projector vanishes on diagrams of height `> r` -/

lemma p20s_cellTensor_mul (L : YoungDiagram) {d : ℕ} (A B : Op (Fin d)) :
    cellTensor L A * cellTensor L B = cellTensor L (A * B) := by
  ext i j
  simp only [cellTensor, Matrix.mul_apply]
  rw [Fintype.prod_sum (fun c l => A (i c) l * B l (j c))]
  simp only [Finset.prod_mul_distrib]

/-- Tensor powers commute with the cell permutations. -/
lemma p20s_cellTensor_comm_perm (L : YoungDiagram) {d : ℕ} (A : Op (Fin d))
    (p : Equiv.Perm (Cell L)) :
    cellTensor L A * cellPermutation L d p = cellPermutation L d p * cellTensor L A := by
  ext i j
  have lhs : (cellTensor L A * cellPermutation L d p) i j = ∏ c, A (i c) (j (p.symm c)) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (j ∘ p.symm)]
    · simp [cellPermutation, cellTensor]
    · intro k _ hk
      simp [cellPermutation, hk]
    · simp
  have rhs : (cellPermutation L d p * cellTensor L A) i j = ∏ c, A (i (p c)) (j c) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (i ∘ p)]
    · have h : i = (i ∘ p) ∘ p.symm := by funext c; simp
      simp only [cellPermutation, cellTensor, if_pos h, one_mul, Function.comp_apply]
    · intro k _ hk
      have h : ¬ i = k ∘ p.symm := by
        intro h
        apply hk
        rw [h]
        funext c
        simp
      simp only [cellPermutation, if_neg h, zero_mul]
    · simp
  rw [lhs, rhs]
  exact (Equiv.prod_comp p (fun c => A (i c) (j (p.symm c)))).symm.trans (by simp)

lemma p20s_cellTensor_comm_young (L : YoungDiagram) {d : ℕ} (A : Op (Fin d)) :
    cellTensor L A * youngOperator L d = youngOperator L d * cellTensor L A := by
  unfold youngOperator
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, p20s_cellTensor_comm_perm]

/-- The column antisymmetrizer kills tensors with a repeated index in one column. -/
lemma p20s_young_apply_eq_zero (L : YoungDiagram) (d : ℕ) (i j : Cell L → Fin d)
    (c1 c2 : Cell L) (hne : c1 ≠ c2) (hcol : c1.val.2 = c2.val.2) (hj : j c1 = j c2) :
    youngOperator L d i j = 0 := by
  unfold youngOperator
  rw [Matrix.sum_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.sum_apply]
  have hτj : ∀ y, j (Equiv.swap c1 c2 y) = j y := by
    intro y
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hj]
    · rw [h2, hj]
    · rfl
  have hτcol : ∀ y, (Equiv.swap c1 c2 y).val.2 = y.val.2 := by
    intro y
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hcol]
    · rw [h2, hcol]
    · rfl
  have hkey : ∀ b : Equiv.Perm (Cell L),
      j ∘ (a * (b * Equiv.swap c1 c2)).symm = j ∘ (a * b).symm := by
    intro b
    funext x
    exact hτj ((a * b).symm x)
  refine Finset.sum_involution (fun b _ => b * Equiv.swap c1 c2) ?_ ?_ ?_ ?_
  · intro b _
    simp only [Matrix.smul_apply, cellPermutation, smul_eq_mul]
    rw [hkey b, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
    simp only [mul_neg, mul_one, Units.val_neg, Int.cast_neg, neg_mul, add_neg_cancel]
  · intro b _ _ h
    have h' : Equiv.swap c1 c2 = 1 := mul_eq_left.mp h
    exact hne (Equiv.swap_eq_one_iff.mp h')
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, fun c => ?_⟩
    rw [Equiv.Perm.mul_apply, hb.2, hτcol]
  · intro b _
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- `Y · (P₀)^{⊗ cells} = 0` when the column 0 is longer than `r`. -/
lemma p20s_young_mul_base (L : YoungDiagram) (d r : ℕ) (hL : r < height L) :
    youngOperator L d * cellTensor L (baseProjector d r) = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases h0 : ∃ c, baseProjector d r (j c) (k c) = 0
  · obtain ⟨c, hc⟩ := h0
    have : cellTensor L (baseProjector d r) j k = 0 := Finset.prod_eq_zero (Finset.mem_univ c) hc
    rw [this, mul_zero]
  push Not at h0
  have htop : ∀ c, d - r ≤ (j c).val := by
    intro c
    have h := h0 c
    unfold baseProjector at h
    simp only [Matrix.diagonal_apply] at h
    split_ifs at h with h1 h2
    · exact h2
    · exact absurd rfl h
    · exact absurd rfl h
  -- pigeonhole on column 0
  let col : Fin (height L) → Cell L := fun m =>
    ⟨(m.val, 0), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_colLen.mpr m.2)⟩
  let f : Fin (height L) → Fin r := fun m =>
    ⟨(j (col m)).val - (d - r), by have := (j (col m)).2; have := htop (col m); omega⟩
  obtain ⟨m1, m2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hL)
  have hv : j (col m1) = j (col m2) := by
    have h1 := htop (col m1)
    have h2 := htop (col m2)
    have := congrArg Fin.val heq
    simp only [f] at this
    exact Fin.ext (by omega)
  have hcne : col m1 ≠ col m2 := by
    intro h
    apply hne
    have := congrArg (fun c : Cell L => c.val.1) h
    exact Fin.ext this
  rw [p20s_young_apply_eq_zero L d i j (col m1) (col m2) hcne rfl hv, zero_mul]

theorem p20s_q_rotatedProjector_eq_zero (d r : ℕ) (L : YoungDiagram) (hL : r < height L)
    (b : SchurBasis L d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    q L b (rotatedProjector r U) = 0 := by
  have hT : cellTensor L (rotatedProjector r U) * youngOperator L d = 0 := by
    unfold rotatedProjector
    rw [← p20s_cellTensor_mul, ← p20s_cellTensor_mul]
    simp only [Matrix.mul_assoc]
    rw [p20s_cellTensor_comm_young L (U : Op (Fin d))ᴴ,
      ← Matrix.mul_assoc (cellTensor L (baseProjector d r)) (youngOperator L d),
      p20s_cellTensor_comm_young L (baseProjector d r), p20s_young_mul_base L d r hL,
      Matrix.zero_mul, Matrix.mul_zero]
  have hP : polynomialRepresentation L (rotatedProjector r U) = 0 := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := (LinearMap.mem_range).mp v.2
    unfold polynomialRepresentation
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, ← hw,
      LinearMap.zero_apply]
    have h0 : Matrix.toEuclideanLin (cellTensor L (rotatedProjector r U))
        (Matrix.toEuclideanLin (youngOperator L d) w) = 0 := by
      change WithLp.toLp 2 (cellTensor L (rotatedProjector r U) *ᵥ
        (youngOperator L d *ᵥ WithLp.ofLp w)) = 0
      rw [Matrix.mulVec_mulVec, hT, Matrix.zero_mulVec]
      first | rfl | simp
    rw [h0, map_zero]
  unfold q
  rw [hP, map_zero]



/-! ## The separable cone is closed -/

/-- Entries of a positive semidefinite matrix are bounded by its trace
(via the `2 × 2` principal minor). -/
lemma p20c_psd_entry_le {n : Type} [Fintype n] {A : Op n} (hA : A.PosSemidef) (x y : n) :
    ‖A x y‖ ≤ (A.trace).re := by
  have hdiag : ∀ z, 0 ≤ (A z z).re ∧ (A z z).im = 0 := fun z => by
    have h := Complex.nonneg_iff.mp (hA.diag_nonneg (i := z))
    exact ⟨h.1, h.2.symm⟩
  have hT : ∀ z, (A z z).re ≤ (A.trace).re := fun z => by
    rw [Matrix.trace, Complex.re_sum]
    exact Finset.single_le_sum (f := fun z => (A.diag z).re) (fun z _ => (hdiag z).1)
      (Finset.mem_univ z)
  have h2 := (hA.submatrix ![x, y]).det_nonneg
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h2
  rw [← hA.1.apply y x, Complex.star_def, Complex.mul_conj] at h2
  have h3 := (Complex.nonneg_iff.mp h2).1
  rw [Complex.sub_re, Complex.mul_re, (hdiag x).2, (hdiag y).2, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] at h3
  have hx := hT x
  have hy := hT y
  have hx0 := (hdiag x).1
  have hy0 := (hdiag y).1
  have hsq : ‖A x y‖ ^ 2 ≤ (A.trace).re ^ 2 := by
    nlinarith [mul_le_mul hx hy hy0 (hx0.trans hx)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hx0.trans hx) two_ne_zero).mp hsq

lemma p20c_trace_re_nonneg {n : Type} [Fintype n] {A : Op n} (hA : A.PosSemidef) :
    0 ≤ (A.trace).re :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma p20c_psd_norm_le {n : Type} [Fintype n] {A : Op n} (hA : A.PosSemidef) :
    ‖A‖ ≤ (A.trace).re :=
  (Matrix.norm_le_iff (p20c_trace_re_nonneg hA)).mpr fun x y => p20c_psd_entry_le hA x y

lemma p20c_trace_re_le {n : Type} [Fintype n] (F : Op n) :
    (F.trace).re ≤ Fintype.card n * ‖F‖ := by
  rw [Matrix.trace, Complex.re_sum]
  calc ∑ i, (F.diag i).re ≤ ∑ _i : n, ‖F‖ := Finset.sum_le_sum fun i _ =>
        (Complex.re_le_norm _).trans (Matrix.norm_entry_le_entrywise_sup_norm F)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- If every bounded slice of the preimage is bounded, the image of a closed set is closed. -/
lemma p20c_isClosed_image {P V : Type} [MetricSpace P] [ProperSpace P] [MetricSpace V]
    (D : Set P) (hD : IsClosed D) (F : P → V) (hF : Continuous F)
    (hb : ∀ X : V, Bornology.IsBounded (D ∩ F ⁻¹' Metric.closedBall X 1)) :
    IsClosed (F '' D) := by
  refine isClosed_of_closure_subset fun X hX => ?_
  have hKc : IsCompact (D ∩ F ⁻¹' Metric.closedBall X 1) :=
    Metric.isCompact_of_isClosed_isBounded
      (hD.inter (Metric.isClosed_closedBall.preimage hF)) (hb X)
  have hXK : X ∈ closure (F '' (D ∩ F ⁻¹' Metric.closedBall X 1)) := by
    rw [Metric.mem_closure_iff] at hX ⊢
    intro ε hε
    obtain ⟨y, ⟨p, hpD, rfl⟩, hy⟩ := hX (min ε 1) (lt_min hε one_pos)
    refine ⟨F p, ⟨p, ⟨hpD, ?_⟩, rfl⟩, lt_of_lt_of_le hy (min_le_left _ _)⟩
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_comm]
    exact (lt_of_lt_of_le hy (min_le_right _ _)).le
  rw [(hKc.image hF).isClosed.closure_eq] at hXK
  exact Set.image_mono Set.inter_subset_left hXK

lemma p20c_isClosed_psd {ι : Type} [Fintype ι] : IsClosed {A : Op ι | A.PosSemidef} := by
  have h : {A : Op ι | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : ι → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [h]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  fun_prop

lemma p20c_cont_kron {X : Type} [TopologicalSpace X] {l m n p : Type}
    {A : X → Matrix l m ℂ} {B : X → Matrix n p ℂ} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => Matrix.kronecker (A x) (B x)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun x => A x i.1 j.1 * B x i.2 j.2
  exact (hA.matrix_elem i.1 j.1).mul (hB.matrix_elem i.2 j.2)

section Cone
variable {a b : Type} [Fintype a] [Fintype b]

/-- Unweighted sums of `n` Kronecker products. -/
def p20cF (n : ℕ) (p : (Fin n → Op a) × (Fin n → Op b)) : Op (a × b) :=
  ∑ j, Matrix.kronecker (p.1 j) (p.2 j)

/-- Positive semidefinite factors, the second one normalized to trace one. -/
def p20cD (n : ℕ) : Set ((Fin n → Op a) × (Fin n → Op b)) :=
  {p | ∀ j, (p.1 j).PosSemidef ∧ (p.2 j).PosSemidef ∧ (p.2 j).trace = 1}

lemma p20cD_closed (n : ℕ) : IsClosed (p20cD (a := a) (b := b) n) := by
  have h : p20cD (a := a) (b := b) n = ⋂ j : Fin n,
      ((fun p : (Fin n → Op a) × (Fin n → Op b) => p.1 j) ⁻¹' {A | A.PosSemidef} ∩
        (fun p : (Fin n → Op a) × (Fin n → Op b) => p.2 j) ⁻¹' {A | A.PosSemidef}) ∩
        {p | (p.2 j).trace = 1} := by
    ext p
    simp only [p20cD, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨fun h j => ⟨⟨(h j).1, (h j).2.1⟩, (h j).2.2⟩,
      fun h j => ⟨(h j).1.1, (h j).1.2, (h j).2⟩⟩
  rw [h]
  refine isClosed_iInter fun j => ((p20c_isClosed_psd.preimage ?_).inter
    (p20c_isClosed_psd.preimage ?_)).inter (isClosed_eq ?_ continuous_const)
  · exact (continuous_apply j).comp continuous_fst
  · exact (continuous_apply j).comp continuous_snd
  · exact ((continuous_apply j).comp continuous_snd).matrix_trace

lemma p20cF_cont (n : ℕ) : Continuous (p20cF (a := a) (b := b) n) := by
  unfold p20cF
  exact continuous_finset_sum _ fun j _ =>
    p20c_cont_kron ((continuous_apply j).comp continuous_fst)
      ((continuous_apply j).comp continuous_snd)

lemma p20c_bounded (n : ℕ) (X : Op (a × b)) :
    Bornology.IsBounded (p20cD (a := a) (b := b) n ∩ p20cF n ⁻¹' Metric.closedBall X 1) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Fintype.card (a × b) * (‖X‖ + 1) + 1, fun p hp => ?_⟩
  obtain ⟨hpD, hpF⟩ := hp
  rw [Set.mem_preimage] at hpF
  have hFn : ‖p20cF n p‖ ≤ ‖X‖ + 1 := norm_le_of_mem_closedBall hpF
  have hR0 : (0 : ℝ) ≤ Fintype.card (a × b) * (‖X‖ + 1) :=
    mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have htr : (p20cF n p).trace = ∑ j, (p.1 j).trace := by
    unfold p20cF
    rw [Matrix.trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.kronecker]
    rw [Matrix.trace_kronecker, (hpD j).2.2, mul_one]
  have hA : ∀ j, ‖p.1 j‖ ≤ Fintype.card (a × b) * (‖X‖ + 1) := by
    intro j
    refine (p20c_psd_norm_le (hpD j).1).trans ?_
    have h1 : ((p.1 j).trace).re ≤ ((p20cF n p).trace).re := by
      rw [htr, Complex.re_sum]
      exact Finset.single_le_sum (f := fun j => ((p.1 j).trace).re)
        (fun j _ => p20c_trace_re_nonneg (hpD j).1) (Finset.mem_univ j)
    refine h1.trans ((p20c_trace_re_le _).trans ?_)
    exact mul_le_mul_of_nonneg_left hFn (Nat.cast_nonneg _)
  have hB : ∀ j, ‖p.2 j‖ ≤ 1 := by
    intro j
    refine (p20c_psd_norm_le (hpD j).2.1).trans ?_
    rw [(hpD j).2.2, Complex.one_re]
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_)
    ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_)
  · linarith [hA j]
  · linarith [hB j]

lemma p20c_real_smul (u : ℝ) (Z : Op (a × b)) : u • Z = (u : ℂ) • Z := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- Every separable matrix is a sum of at most `finrank + 1` normalized Kronecker products. -/
lemma p20c_sep_subset (β₀ : Op b) (hβ : β₀.PosSemidef) (hβt : β₀.trace = 1) (X : Op (a × b))
    (hX : Separable X) :
    ∃ n ≤ Module.finrank ℝ (Op (a × b)) + 1, X ∈ p20cF n '' p20cD n := by
  obtain ⟨M, w, A, B, hpos, rfl⟩ := hX
  -- Step a: normalize each term.
  have hnorm : ∀ j, ∃ A' : Op a, ∃ B' : Op b, A'.PosSemidef ∧ B'.PosSemidef ∧ B'.trace = 1 ∧
      (w j : ℂ) • Matrix.kronecker (A j) (B j) = Matrix.kronecker A' B' := by
    intro j
    obtain ⟨hw, hAj, hBj⟩ := hpos j
    by_cases h0 : (B j).trace = 0
    · refine ⟨0, β₀, Matrix.PosSemidef.zero, hβ, hβt, ?_⟩
      rw [(hBj.trace_eq_zero_iff).mp h0]
      simp only [Matrix.kronecker, Matrix.kronecker_zero, Matrix.zero_kronecker, smul_zero]
    · have hre : (B j).trace = (((B j).trace).re : ℂ) := by
        apply Complex.ext
        · simp
        · simp only [Complex.ofReal_im]
          exact ((Complex.nonneg_iff.mp hBj.trace_nonneg).2).symm
      obtain ⟨t, ht⟩ : ∃ t : ℝ, (B j).trace = (t : ℂ) := ⟨_, hre⟩
      have hpos' : 0 < t := by
        have h1 : 0 ≤ t := by
          have := p20c_trace_re_nonneg hBj
          rw [ht, Complex.ofReal_re] at this
          exact this
        rcases h1.lt_or_eq with h | h
        · exact h
        · exact absurd (by rw [ht, ← h, Complex.ofReal_zero]) h0
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast hpos'.ne'
      refine ⟨((w j * t : ℝ) : ℂ) • A j, ((t⁻¹ : ℝ) : ℂ) • B j, ?_, ?_, ?_, ?_⟩
      · exact hAj.smul (Complex.zero_le_real.mpr (mul_nonneg hw hpos'.le))
      · exact hBj.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hpos'.le))
      · rw [Matrix.trace_smul, smul_eq_mul, ht, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos'.ne',
          Complex.ofReal_one]
      · simp only [Matrix.kronecker]
        rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
        congr 1
        push_cast
        rw [mul_assoc, mul_inv_cancel₀ htc, mul_one]
  choose A' B' hA' hB' hBt' hAB using hnorm
  have hX : ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j) =
      ∑ j, Matrix.kronecker (A' j) (B' j) := Finset.sum_congr rfl fun j _ => hAB j
  rw [hX]
  -- Step b: Carathéodory.
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    refine ⟨0, Nat.zero_le _, (fun k => k.elim0, fun k => k.elim0), fun k => k.elim0, ?_⟩
    simp [p20cF]
  set Z : Fin M → Op (a × b) := fun j => Matrix.kronecker (A' j) (B' j) with hZ
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hmem : ∑ j, Z j ∈ convexHull ℝ (Set.range fun j => (M : ℝ) • Z j) := by
    have h : ∑ j, Z j = ∑ j, (1 / (M : ℝ)) • ((M : ℝ) • Z j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, one_div, inv_mul_cancel₀ hMpos.ne', one_smul]
    rw [h]
    refine (convex_convexHull ℝ _).sum_mem (fun j _ => by positivity) ?_
      (fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hMpos.ne']
  obtain ⟨ι, _, z, v, hzs, hai, hvpos, -, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hmem
  have hcard : Fintype.card ι ≤ Module.finrank ℝ (Op (a × b)) + 1 :=
    hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hσ : ∀ i, ∃ j, (M : ℝ) • Z j = z i := fun i => hzs ⟨i, rfl⟩
  choose σ hσ using hσ
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, hcard,
    (fun k => (((v (e.symm k) * M : ℝ)) : ℂ) • A' (σ (e.symm k)),
      fun k => B' (σ (e.symm k))), fun k => ⟨?_, hB' _, hBt' _⟩, ?_⟩
  · exact (hA' _).smul (Complex.zero_le_real.mpr (mul_nonneg (hvpos _).le hMpos.le))
  · rw [← hsum]
    unfold p20cF
    dsimp only
    rw [← e.symm.sum_comp (fun i => v i • z i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hσ (e.symm k), smul_smul, p20c_real_smul, hZ]
    simp only [Matrix.kronecker]
    rw [Matrix.smul_kronecker]

end Cone

theorem p20c_separable_isClosed {a b : Type} [Fintype a] [Fintype b] :
    IsClosed {X : Op (a × b) | Separable X} := by
  by_cases hb : IsEmpty b
  · haveI : Subsingleton (Op (a × b)) :=
      ⟨fun X Y => by ext ⟨i, j⟩ ⟨i', j'⟩; exact isEmptyElim j⟩
    exact Set.Subsingleton.isClosed Set.subsingleton_of_subsingleton
  rw [not_isEmpty_iff] at hb
  obtain ⟨b0⟩ := hb
  let β₀ : Op b := Matrix.diagonal (Pi.single b0 1)
  have hβ : β₀.PosSemidef := by
    refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
    by_cases h : i = b0
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hβt : β₀.trace = 1 := by
    simp [β₀, Matrix.trace_diagonal]
  have hEq : {X : Op (a × b) | Separable X} =
      ⋃ n ∈ Finset.range (Module.finrank ℝ (Op (a × b)) + 2), p20cF n '' p20cD n := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · intro hX
      obtain ⟨n, hn, hmem⟩ := p20c_sep_subset β₀ hβ hβt X hX
      exact ⟨n, by omega, hmem⟩
    · rintro ⟨n, -, p, hp, rfl⟩
      exact ⟨n, fun _ => 1, p.1, p.2, fun j => ⟨zero_le_one, (hp j).1, (hp j).2.1⟩,
        by simp [p20cF]⟩
  rw [hEq]
  exact isClosed_biUnion_finset fun n _ =>
    p20c_isClosed_image _ (p20cD_closed n) _ (p20cF_cont n) (p20c_bounded n)



/-! ## Integrals of separable-valued functions -/

lemma p20_sep_convex {a b : Type} [Fintype a] [Fintype b] :
    Convex ℝ {X : Op (a × b) | Separable X} := by
  intro X hX Y hY s t hs ht _
  have e : ∀ (u : ℝ) (Z : Op (a × b)), u • Z = (u : ℂ) • Z := by
    intro u Z
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  change Separable (s • X + t • Y)
  rw [e s X, e t Y]
  exact p20_sep_add (p20_sep_smul hX hs) (p20_sep_smul hY ht)

lemma p20_sep_integral {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {a b : Type} [Fintype a] [Fintype b] (f : Ω → Op (a × b)) (hf : ∀ x, Separable (f x)) :
    Separable (∫ x, f x ∂μ) := by
  by_cases hi : ∫ x, f x ∂μ = 0
  · rw [hi]
    exact p20_sep_zero
  · refine Convex.integral_mem (s := {X | Separable X}) ?_ ?_
      (Filter.Eventually.of_forall hf) (Integrable.of_integral_ne_zero hi)
    · exact p20_sep_convex
    · exact p20c_separable_isClosed

/-! ## The lift preserves separability -/

lemma p20_lift_sep {d : ℕ} {L M : YoungDiagram} (E : BranchFamily d L) (G : BranchFamily d M)
    (L' : {L' : YoungDiagram // L' ∈ branches d L})
    (M' : {M' : YoungDiagram // M' ∈ branches d M})
    (X : Op (SchurIndex L'.val d × SchurIndex M'.val d)) (hX : Separable X) :
    Separable (lift E G L' M' X) := by
  unfold lift
  refine p20_sep_integral _ _ fun U => ?_
  dsimp only
  simp only [Matrix.kronecker]
  rw [Matrix.mul_assoc _ (kroneckerMap (fun x1 x2 => x1 * x2) (E L') (G M'))ᴴ,
    ← Matrix.conjTranspose_mul, ← Matrix.mul_kronecker_mul]
  exact p20_sep_conj _ _ hX

/-! ## Height reduction -/

lemma p20_delta_eq_zero_of_height {d : ℕ} (r : ℕ) (L M : YoungDiagram) (b : SchurBasis L d)
    (c : SchurBasis M d) (h : r < height L ∨ r < height M) : delta r L M b c = 0 := by
  have hsup : r < height (L ⊔ M) := by
    by_contra h'
    push Not at h'
    have := (p20_height_sup L M r).mp h'
    omega
  have hint : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      Matrix.kronecker (q L b (rotatedProjector r U)) (q M c (rotatedProjector r U)) = 0 := by
    intro U
    simp only [Matrix.kronecker]
    rcases h with h | h
    · rw [p20s_q_rotatedProjector_eq_zero d r L h b U, Matrix.zero_kronecker]
    · rw [p20s_q_rotatedProjector_eq_zero d r M h c U, Matrix.kronecker_zero]
  unfold delta schurIntegral
  simp only [hint, integral_zero, p20_ratio_eq_zero _ r d hsup, Complex.ofReal_zero, zero_smul,
    sub_zero]

/-! ## The case `r = 0` -/

lemma p20_delta_zero {d : ℕ} (L M : YoungDiagram) (b : SchurBasis L d) (c : SchurBasis M d) :
    delta 0 L M b c = 0 := by
  by_cases h : 0 < height L ∨ 0 < height M
  · exact p20_delta_eq_zero_of_height 0 L M b c h
  push Not at h
  have hL := p20_eq_bot_of_height L (by omega)
  have hM := p20_eq_bot_of_height M (by omega)
  subst hL hM
  have hr : ratio ((⊥ : YoungDiagram) ⊔ ⊥) 0 d = 1 := by
    unfold ratio
    rw [sup_idem, p20_schurCount_bot, p20_schurCount_bot]
    norm_num
  unfold delta schurIntegral
  simp only [p20_q_bot, integral_const, probReal_univ, one_smul, hr, Complex.ofReal_one]
  rw [p20_one_eq_kron, sub_self]

/-! ## Swapping the two factors -/

lemma p20_delta_swap {d : ℕ} (r : ℕ) (L M : YoungDiagram) (b : SchurBasis L d)
    (c : SchurBasis M d) :
    delta r L M b c = reindex (Equiv.prodComm (SchurIndex M d) (SchurIndex L d))
      (Equiv.prodComm (SchurIndex M d) (SchurIndex L d)) (delta r M L c b) := by
  have e : ∀ Y : Op (SchurIndex M d × SchurIndex L d),
      reindex (Equiv.prodComm (SchurIndex M d) (SchurIndex L d))
        (Equiv.prodComm (SchurIndex M d) (SchurIndex L d)) Y =
      reindexLinearEquiv ℂ ℂ (Equiv.prodComm (SchurIndex M d) (SchurIndex L d))
        (Equiv.prodComm (SchurIndex M d) (SchurIndex L d)) Y := fun Y => rfl
  unfold delta schurIntegral
  rw [e, map_sub, map_smul, ← e, ← e, p20_reindex_one, p20_reindex_integral, sup_comm M L]
  simp only [p20_reindex_kron]

/-! ## Change of orthonormal bases -/

lemma p20_q_change (L : YoungDiagram) {d : ℕ} (b b0 : SchurBasis L d) (A : Op (Fin d)) :
    q L b A = (b0.toBasis.toMatrix b.toBasis)ᴴ * q L b0 A * b0.toBasis.toMatrix b.toBasis := by
  have h1 : b.toBasis.toMatrix b0.toBasis * b0.toBasis.toMatrix b.toBasis = 1 :=
    Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : b0.toBasis.toMatrix b.toBasis * (b0.toBasis.toMatrix b.toBasis)ᴴ = 1 :=
    OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose b0 b
  have hP : b.toBasis.toMatrix b0.toBasis = (b0.toBasis.toMatrix b.toBasis)ᴴ := by
    calc b.toBasis.toMatrix b0.toBasis
        = b.toBasis.toMatrix b0.toBasis *
            (b0.toBasis.toMatrix b.toBasis * (b0.toBasis.toMatrix b.toBasis)ᴴ) := by
          rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold q
  rw [← hP]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (c := b.toBasis)
    (c' := b0.toBasis) (b := b.toBasis) (b' := b0.toBasis)
    (f := polynomialRepresentation L A)).symm

lemma p20_kron_conj {a' b' : Type} [Fintype a'] [Fintype b'] (Q : Op a') (Q' : Op b')
    (X : Op a') (Y : Op b') :
    Matrix.kronecker (Qᴴ * X * Q) (Q'ᴴ * Y * Q') =
      (Matrix.kronecker Q Q')ᴴ * Matrix.kronecker X Y * Matrix.kronecker Q Q' := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

lemma p20_delta_basis {d : ℕ} (r : ℕ) (L M : YoungDiagram) (b b0 : SchurBasis L d)
    (c c0 : SchurBasis M d) :
    delta r L M b c =
      (Matrix.kronecker (b0.toBasis.toMatrix b.toBasis) (c0.toBasis.toMatrix c.toBasis))ᴴ *
        delta r L M b0 c0 *
        Matrix.kronecker (b0.toBasis.toMatrix b.toBasis) (c0.toBasis.toMatrix c.toBasis) := by
  have hQ1 : b0.toBasis.toMatrix b.toBasis * (b0.toBasis.toMatrix b.toBasis)ᴴ = 1 :=
    OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose b0 b
  have hQ2 : (b0.toBasis.toMatrix b.toBasis)ᴴ * b0.toBasis.toMatrix b.toBasis = 1 :=
    OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self b0 b
  have hR1 : c0.toBasis.toMatrix c.toBasis * (c0.toBasis.toMatrix c.toBasis)ᴴ = 1 :=
    OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose c0 c
  have hR2 : (c0.toBasis.toMatrix c.toBasis)ᴴ * c0.toBasis.toMatrix c.toBasis = 1 :=
    OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self c0 c
  have hW1 : Matrix.kronecker (b0.toBasis.toMatrix b.toBasis) (c0.toBasis.toMatrix c.toBasis) *
      (Matrix.kronecker (b0.toBasis.toMatrix b.toBasis) (c0.toBasis.toMatrix c.toBasis))ᴴ = 1 := by
    rw [p20_one_eq_kron]
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hQ1, hR1]
  have hW2 : (Matrix.kronecker (b0.toBasis.toMatrix b.toBasis) (c0.toBasis.toMatrix c.toBasis))ᴴ *
      Matrix.kronecker (b0.toBasis.toMatrix b.toBasis) (c0.toBasis.toMatrix c.toBasis) = 1 := by
    rw [p20_one_eq_kron]
    simp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hQ2, hR2]
  unfold delta schurIntegral
  simp only [p20_q_change L b b0, p20_q_change M c c0, p20_kron_conj]
  rw [← p20_conj_integral _ _ hW1 hW2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hW2]

/-! ## The inductive step (the paper's computation on p. 26) -/

lemma p20_step (r d' : ℕ)
    (ih : ∀ d, r ≤ d → ∀ L M : YoungDiagram, height L ≤ d → height M ≤ d →
      Separable (delta r L M (schurBasis L d) (schurBasis M d)))
    (hrd : r + 1 ≤ d' + 1) (L M : YoungDiagram) (hL : height L ≤ d' + 1)
    (hM : height M ≤ d' + 1) (hLr : height L ≤ r + 1) (hMr : height M ≤ r + 1)
    (hfirst : M.rowLen 0 ≤ L.rowLen 0) :
    Separable (delta (r+1) L M (schurBasis L (d'+1)) (schurBasis M (d'+1))) := by
  obtain ⟨E, hE, -, -⟩ := branching d' L hL
  obtain ⟨G, hG, -, -⟩ := branching d' M hM
  obtain ⟨L', hL'eq⟩ : ∃ L' : {L' : YoungDiagram // L' ∈ branches d' L},
      L'.val = tailDiagram L := ⟨⟨tailDiagram L, p20_tail_mem_branches d' L hL⟩, rfl⟩
  have hLt : height L'.val ≤ r := by rw [hL'eq]; exact (p20_height_tail L r).mpr hLr
  have h21 := lemma_21 d' L M hL hM E G hE hG L'
  have h22 := lemma_22 d' (r+1) (by omega) hrd L M hL hM E G hE hG L' (by simpa using hLt)
  have h23 := (lemma_23 (d'+1) (r+1) (by omega) (by omega) hrd L M hLr hMr hfirst).2
  simp only [Nat.add_sub_cancel] at h22 h23
  rw [← hL'eq] at h23
  have ha : (schurCount L'.val d' : ℂ) ≠ 0 := by
    exact_mod_cast (p20_schurCount_pos _ _ (by omega)).ne'
  have hb : (schurCount L (d'+1) : ℂ) ≠ 0 := by
    exact_mod_cast (p20_schurCount_pos _ _ hL).ne'
  have h23c : (ratio (L ⊔ M) (r+1) (d'+1) : ℂ) *
      ((schurCount L (d'+1) : ℂ) / schurCount L'.val d') =
      (ratio (L'.val ⊔ tailDiagram M) r d' : ℂ) *
        ((schurCount L (r+1) : ℂ) / schurCount L'.val r) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) h23
    push_cast at this
    exact this
  have hR : (ratio (L ⊔ M) (r+1) (d'+1) : ℂ) =
      ((schurCount L (r+1) : ℂ) / schurCount L'.val r) *
        (ratio (L'.val ⊔ tailDiagram M) r d' : ℂ) *
        ((schurCount L'.val d' : ℂ) / schurCount L (d'+1)) := by
    calc (ratio (L ⊔ M) (r+1) (d'+1) : ℂ)
        = (ratio (L ⊔ M) (r+1) (d'+1) : ℂ) *
            ((schurCount L (d'+1) : ℂ) / schurCount L'.val d') *
            ((schurCount L'.val d' : ℂ) / schurCount L (d'+1)) := by
          field_simp
      _ = _ := by rw [h23c]; ring
  have key : delta (r+1) L M (schurBasis L (d'+1)) (schurBasis M (d'+1)) =
      (((schurCount L (r+1) : ℝ) / schurCount L'.val r : ℝ) : ℂ) •
        ∑ M' : {M' : YoungDiagram // M' ∈ branches d' M}, lift E G L' M'
          ((ratio (L'.val ⊔ tailDiagram M) r d' : ℂ) • 1 -
            schurIntegral r L'.val M'.val (schurBasis L'.val d') (schurBasis M'.val d')) := by
    simp only [p20_lift_smul_sub, Finset.sum_sub_distrib, ← Finset.smul_sum]
    rw [h21]
    unfold delta
    rw [h22, hR]
    push_cast
    module
  rw [key]
  refine p20_sep_smul (p20_sep_sum _ _ fun M' _ => p20_lift_sep _ _ _ _ _ ?_) (by positivity)
  have hM'h : height M'.val ≤ d' := p20_branch_height M'.2
  have hdecomp : (ratio (L'.val ⊔ tailDiagram M) r d' : ℂ) •
        (1 : Op (SchurIndex L'.val d' × SchurIndex M'.val d')) -
      schurIntegral r L'.val M'.val (schurBasis L'.val d') (schurBasis M'.val d') =
      ((ratio (L'.val ⊔ tailDiagram M) r d' - ratio (L'.val ⊔ M'.val) r d' : ℝ) : ℂ) • 1 +
        delta r L'.val M'.val (schurBasis L'.val d') (schurBasis M'.val d') := by
    unfold delta
    push_cast
    rw [sub_smul]
    abel
  rw [hdecomp]
  refine p20_sep_add (p20_sep_one (sub_nonneg.mpr ?_)) (ih d' (by omega) _ _ (by omega) hM'h)
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    rw [hL'eq, p20_tail_eq_bot L hLr, p20_tail_eq_bot M hMr, sup_idem, bot_sup_eq]
    exact p20_ratio_zero_le _ d' hM'h
  · have hS : height (L'.val ⊔ tailDiagram M) ≤ d' :=
      (p20_height_sup _ _ _).mpr ⟨by omega, by have := (p20_height_tail M r).mpr hMr; omega⟩
    have hT : height (L'.val ⊔ M'.val) ≤ d' := (p20_height_sup _ _ _).mpr ⟨by omega, hM'h⟩
    exact lemma_9 d' r hr0 (by omega) _ _ hS hT (sup_le_sup_left (p20_tail_le_branch M'.2) _)

/-! ## Induction on the rank -/

theorem p20_main : ∀ r d, r ≤ d → ∀ L M : YoungDiagram, height L ≤ d → height M ≤ d →
    Separable (delta r L M (schurBasis L d) (schurBasis M d)) := by
  intro r
  induction r with
  | zero =>
    intro d _ L M _ _
    rw [p20_delta_zero]
    exact p20_sep_zero
  | succ r ih =>
    intro d hrd L M hL hM
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    by_cases hh : r + 1 < height L ∨ r + 1 < height M
    · rw [p20_delta_eq_zero_of_height _ _ _ _ _ hh]
      exact p20_sep_zero
    push Not at hh
    obtain ⟨hLr, hMr⟩ := hh
    rcases le_total (M.rowLen 0) (L.rowLen 0) with hfirst | hfirst
    · exact p20_step r d' ih hrd L M hL hM hLr hMr hfirst
    · rw [p20_delta_swap]
      exact p20_sep_swap (p20_step r d' ih hrd M L hM hL hMr hLr hfirst)

/-! ## Proposition 20 -/

theorem solution (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (L M : YoungDiagram) (hL : height L ≤ d) (hM : height M ≤ d)
    (b : SchurBasis L d) (c : SchurBasis M d) :
    Separable (delta r L M b c) := by
  rw [p20_delta_basis r L M b (schurBasis L d) c (schurBasis M d)]
  have h := p20_sep_conj ((schurBasis L d).toBasis.toMatrix b.toBasis)ᴴ
    ((schurBasis M d).toBasis.toMatrix c.toBasis)ᴴ (p20_main r d hrd L M hL hM)
  simp only [Matrix.kronecker] at h ⊢
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h
  rw [Matrix.conjTranspose_kronecker]
  exact h
