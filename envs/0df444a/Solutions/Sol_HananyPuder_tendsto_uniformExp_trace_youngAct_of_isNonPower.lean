-- Prove2me | solution 1 for HananyPuder.tendsto_uniformExp_trace_youngAct_of_isNonPower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:12:12.217327+00:00
-- url     : https://prove2.me/submissions/4c202e43-0139-456e-ab5d-a3f5f10b6402

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4
import Theorems.Thm_HananyPuder_tendsto_uniformExp_prod_xi_pow_sub_uniformExp
import Theorems.Thm_HananyPuder_exists_trace_youngAct_eq_aeval_and_weightedTotalDegree_le

section
open Filter Topology StrongConv

namespace StrongConvHP17

variable {N : ℕ}


/-- The signed column sum `b` of the Young symmetrizer. -/
noncomputable def colSum (N : ℕ) (rows : List ℕ) : MonoidAlgebra ℂ (Equiv.Perm (Fin N)) :=
  ∑ q ∈ Finset.univ.filter (fun q : Equiv.Perm (Fin N) =>
      ∀ x : Fin N, tabCol rows (q x : ℕ) = tabCol rows (x : ℕ)),
    ((Equiv.Perm.sign q : ℤ) : ℂ) • MonoidAlgebra.of ℂ (Equiv.Perm (Fin N)) q

lemma colSum_mul_of (rows : List ℕ) (t : Equiv.Perm (Fin N))
    (ht : ∀ x : Fin N, tabCol rows (t x : ℕ) = tabCol rows (x : ℕ)) :
    colSum N rows * MonoidAlgebra.of ℂ _ t =
      ((Equiv.Perm.sign t : ℤ) : ℂ) • colSum N rows := by
  classical
  unfold colSum
  rw [Finset.sum_mul, Finset.smul_sum]
  simp_rw [Finset.sum_filter]
  refine Fintype.sum_equiv (Equiv.mulRight t) _ _ ?_
  intro q
  simp only [Equiv.coe_mulRight, Equiv.Perm.coe_mul, Function.comp_apply]
  have key : (∀ x : Fin N, tabCol rows (q (t x) : ℕ) = tabCol rows (x : ℕ)) ↔
      (∀ x : Fin N, tabCol rows (q x : ℕ) = tabCol rows (x : ℕ)) := by
    constructor
    · intro h x
      have h1 := h (t⁻¹ x)
      have h2 := ht (t⁻¹ x)
      simp at h1 h2
      rw [h1, ← h2]
    · intro h x; rw [h, ht]
  have hs : ((Equiv.Perm.sign q : ℤ) : ℂ) = ((Equiv.Perm.sign t : ℤ) : ℂ) *
      ((Equiv.Perm.sign (q * t) : ℤˣ) : ℤ) := by
    rw [Equiv.Perm.sign_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h | h <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h' | h' <;> simp [h, h']
  split_ifs with h1 h2 h2
  · rw [smul_mul_assoc, ← map_mul, smul_smul, ← hs]
    exact (if_pos h2).symm
  · exact absurd (key.mpr h1) h2
  · exact absurd (key.mp h2) h1
  · simp
    exact fun h => absurd h h2

lemma youngSymmetrizer_eq (rows : List ℕ) :
    ∃ a, youngSymmetrizer N rows = a * colSum N rows := ⟨_, rfl⟩

/-- Every element of `youngSpace` is negated by right multiplication by an odd column-preserving
permutation. -/
lemma mul_of_eq_neg {rows : List ℕ} (t : Equiv.Perm (Fin N))
    (ht : ∀ x : Fin N, tabCol rows (t x : ℕ) = tabCol rows (x : ℕ))
    (hsign : Equiv.Perm.sign t = -1) {x : MonoidAlgebra ℂ (Equiv.Perm (Fin N))}
    (hx : x ∈ youngSpace N rows) : x * MonoidAlgebra.of ℂ _ t = -x := by
  rw [youngSpace, Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hx
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨a, ha⟩ := youngSymmetrizer_eq (N := N) rows
  rw [ha, smul_eq_mul, mul_assoc, mul_assoc, colSum_mul_of rows t ht, hsign]
  simp

/-- The sum of all group elements. -/
noncomputable def total (N : ℕ) : MonoidAlgebra ℂ (Equiv.Perm (Fin N)) :=
  ∑ σ : Equiv.Perm (Fin N), MonoidAlgebra.of ℂ _ σ

lemma total_mul_of (g : Equiv.Perm (Fin N)) :
    total N * MonoidAlgebra.of ℂ _ g = total N := by
  unfold total
  rw [Finset.sum_mul]
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

lemma total_mul (x : MonoidAlgebra ℂ (Equiv.Perm (Fin N))) :
    ∃ e : ℂ, total N * x = e • total N := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨e, he⟩ := hf; obtain ⟨e', he'⟩ := hg
    exact ⟨e + e', by rw [mul_add, he, he', add_smul]⟩
  | single g r =>
    refine ⟨r, ?_⟩
    have : MonoidAlgebra.single g r = r • MonoidAlgebra.of ℂ _ g := by simp
    rw [this, mul_smul_comm, total_mul_of]

lemma total_mul_eq_zero {rows : List ℕ} (t : Equiv.Perm (Fin N))
    (ht : ∀ x : Fin N, tabCol rows (t x : ℕ) = tabCol rows (x : ℕ))
    (hsign : Equiv.Perm.sign t = -1) {x : MonoidAlgebra ℂ (Equiv.Perm (Fin N))}
    (hx : x ∈ youngSpace N rows) : total N * x = 0 := by
  obtain ⟨e, he⟩ := total_mul x
  have h1 : total N * x * MonoidAlgebra.of ℂ _ t = total N * x := by
    rw [he, smul_mul_assoc, total_mul_of]
  have h2 : total N * x * MonoidAlgebra.of ℂ _ t = -(total N * x) := by
    rw [mul_assoc, mul_of_eq_neg t ht hsign hx, mul_neg]
  have h3 : (2 : ℂ) • (total N * x) = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h1]; rw [h2, neg_add_cancel]
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

lemma sum_trace_youngAct_eq_zero {rows : List ℕ} (t : Equiv.Perm (Fin N))
    (ht : ∀ x : Fin N, tabCol rows (t x : ℕ) = tabCol rows (x : ℕ))
    (hsign : Equiv.Perm.sign t = -1) :
    ∑ σ : Equiv.Perm (Fin N), LinearMap.trace ℂ _ (youngAct N rows σ) = 0 := by
  rw [← map_sum]
  have : ∑ σ : Equiv.Perm (Fin N), youngAct N rows σ = 0 := by
    apply LinearMap.ext; intro x
    apply Subtype.ext
    have hx := x.2
    have hz := total_mul_eq_zero t ht hsign hx
    have : ((∑ σ : Equiv.Perm (Fin N), youngAct N rows σ) x : MonoidAlgebra ℂ _) =
        total N * (x : MonoidAlgebra ℂ (Equiv.Perm (Fin N))) := by
      rw [LinearMap.sum_apply, Submodule.coe_sum, total, Finset.sum_mul]
      rfl
    rw [this, hz]; rfl
  rw [this, map_zero]

/-- The column transposition `(0 n₀)` of `λ[N]`. -/
lemma exists_col_transposition (μ : YoungDiagram) (hμ₀ : μ.rowLens ≠ []) (N : ℕ)
    (hN : μ.cells.card < N) :
    ∃ t : Equiv.Perm (Fin N),
      (∀ x : Fin N, tabCol (stableRows μ N) (t x : ℕ) = tabCol (stableRows μ N) (x : ℕ)) ∧
      Equiv.Perm.sign t = -1 := by
  have hcard : 0 < μ.cells.card := by
    rcases Nat.eq_zero_or_pos μ.cells.card with h | h
    · exfalso; apply hμ₀
      have h00 : (0, 0) ∉ μ := by
        intro hm; have := Finset.card_pos.mpr ⟨_, hm⟩; omega
      rw [YoungDiagram.mem_iff_lt_colLen, not_lt, Nat.le_zero] at h00
      rw [← List.length_eq_zero_iff, YoungDiagram.length_rowLens, h00]
    · exact h
  set n0 := N - μ.cells.card with hn0
  have hn0pos : 0 < n0 := by omega
  have hn0lt : n0 < N := by omega
  refine ⟨Equiv.swap ⟨0, by omega⟩ ⟨n0, hn0lt⟩, ?_, ?_⟩
  · have hcol0 : tabCol (stableRows μ N) 0 = 0 := by simp [tabCol]
    have hcoln : tabCol (stableRows μ N) n0 = 0 := by
      have hrow : 1 ≤ tabRow (stableRows μ N) n0 := by
        unfold tabRow
        apply List.length_pos_of_mem (a := 0)
        simp [stableRows, hn0]
      unfold tabCol
      apply Nat.sub_eq_zero_of_le
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hrow
      rw [hk, add_comm]
      simp [stableRows, List.take_succ_cons, hn0]
    intro x
    rcases eq_or_ne x ⟨0, by omega⟩ with rfl | h0
    · rw [Equiv.swap_apply_left]; simp only [Fin.val_mk]; rw [hcol0, hcoln]
    rcases eq_or_ne x ⟨n0, hn0lt⟩ with rfl | h1
    · rw [Equiv.swap_apply_right]; simp only [Fin.val_mk]; rw [hcol0, hcoln]
    rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
  · rw [Equiv.Perm.sign_swap]
    intro h; rw [Fin.ext_iff] at h; simp at h; omega

lemma uniformExp_trace_youngAct_eq_zero (μ : YoungDiagram) (hμ₀ : μ.rowLens ≠ []) (N : ℕ)
    (hN : μ.cells.card < N) :
    uniformExp (fun σ : Equiv.Perm (Fin N) =>
      (LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ)).re) = 0 := by
  obtain ⟨t, ht, hs⟩ := exists_col_transposition μ hμ₀ N hN
  unfold uniformExp
  rw [← Complex.re_sum, sum_trace_youngAct_eq_zero t ht hs]
  simp

end StrongConvHP17
end

section
open Filter Topology StrongConv

namespace StrongConvHP17

/-- The monomial `∏ᵢ ξ_{i+1}^{d i}`, indexed over `Fin (R d)` as in HP Theorem 1.3. -/
def bnd (d : ℕ →₀ ℕ) : ℕ := d.support.sup id + 1

noncomputable def monoVal {N : ℕ} (d : ℕ →₀ ℕ) (τ : Equiv.Perm (Fin N)) : ℝ :=
  ∏ i : Fin (bnd d), ((xi ((i : ℕ) + 1) τ : ℕ) : ℝ) ^ (d i)

lemma support_subset_range (d : ℕ →₀ ℕ) : d.support ⊆ Finset.range (bnd d) := by
  intro i hi
  rw [Finset.mem_range, bnd, Nat.lt_succ_iff]
  exact Finset.le_sup (f := id) hi

lemma aeval_eq_sum {N : ℕ} (p : MvPolynomial ℕ ℚ) (τ : Equiv.Perm (Fin N)) :
    MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) τ : ℕ) : ℂ)) p =
      ((∑ d ∈ p.support, ((MvPolynomial.coeff d p : ℚ) : ℝ) * monoVal d τ : ℝ) : ℂ) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Complex.ofReal_mul, monoVal, Complex.ofReal_prod, Fin.prod_univ_eq_prod_range
    (fun i => (((((xi (i + 1) τ : ℕ) : ℝ) ^ (d i) : ℝ)) : ℂ)),
    ← Finset.prod_subset (support_subset_range d)]
  · congr 1
    all_goals first
      | simp
      | (refine Finset.prod_congr rfl (fun i _ => ?_); push_cast; rfl)
  · intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi]; simp

lemma uniformExp_sum {X : Type*} [Fintype X] {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (g : ι → X → ℝ) :
    uniformExp (fun x => ∑ d ∈ s, c d * g d x) = ∑ d ∈ s, c d * uniformExp (g d) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← Finset.mul_sum, mul_div_assoc]

theorem tendsto_dev (μ : YoungDiagram) (hμ₀ : μ.rowLens ≠ [])
    (_hμ₁ : μ.rowLens ≠ [1]) {d : ℕ} (w : FreeGroup (Fin d)) (hw : IsNonPower w) :
    Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        (LinearMap.trace ℂ (youngSpace N (stableRows μ N))
          (youngAct N (stableRows μ N) (FreeGroup.lift σ w))).re))
      atTop (𝓝 0) := by
  obtain ⟨q, hq, -⟩ :=
    HananyPuder.exists_trace_youngAct_eq_aeval_and_weightedTotalDegree_le
  set p := q μ
  have hre : ∀ N, μ.cells.card + μ.rowLen 0 ≤ N → ∀ τ : Equiv.Perm (Fin N),
      (LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) τ)).re =
        ∑ e ∈ p.support, ((MvPolynomial.coeff e p : ℚ) : ℝ) * monoVal e τ := by
    intro N hN τ
    rw [hq μ N hN τ, aeval_eq_sum, Complex.ofReal_re]
  have hlim : ∀ e : ℕ →₀ ℕ, Tendsto (fun N : ℕ =>
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => monoVal e (FreeGroup.lift σ w)) -
        uniformExp (fun τ : Equiv.Perm (Fin N) => monoVal e τ)) atTop (𝓝 0) := by
    intro e
    have := HananyPuder.tendsto_uniformExp_prod_xi_pow_sub_uniformExp w hw 1 le_rfl
      (fun i : Fin (bnd e) => e i)
    simpa only [pow_one, mul_one, monoVal] using this
  have hsum : Tendsto (fun N : ℕ => ∑ e ∈ p.support, ((MvPolynomial.coeff e p : ℚ) : ℝ) *
      (uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => monoVal e (FreeGroup.lift σ w)) -
        uniformExp (fun τ : Equiv.Perm (Fin N) => monoVal e τ))) atTop (𝓝 0) := by
    have := tendsto_finsetSum p.support (fun e _ => (hlim e).const_mul
      ((MvPolynomial.coeff e p : ℚ) : ℝ))
    simpa using this
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (μ.cells.card + μ.rowLen 0 + 1)] with N hN
  have hN' : μ.cells.card + μ.rowLen 0 ≤ N := by omega
  have h0 := uniformExp_trace_youngAct_eq_zero μ hμ₀ N (by omega)
  have hw' : uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      (LinearMap.trace ℂ (youngSpace N (stableRows μ N))
        (youngAct N (stableRows μ N) (FreeGroup.lift σ w))).re) =
      ∑ e ∈ p.support, ((MvPolynomial.coeff e p : ℚ) : ℝ) *
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => monoVal e (FreeGroup.lift σ w)) := by
    simp_rw [hre N hN']
    exact uniformExp_sum _ _ _
  have hu : uniformExp (fun τ : Equiv.Perm (Fin N) =>
      (LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) τ)).re) =
      ∑ e ∈ p.support, ((MvPolynomial.coeff e p : ℚ) : ℝ) *
        uniformExp (fun τ : Equiv.Perm (Fin N) => monoVal e τ) := by
    simp_rw [hre N hN']
    exact uniformExp_sum _ _ _
  rw [hw']
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← hu, h0, sub_zero]

end StrongConvHP17
end

open Filter Topology StrongConv in
theorem solution (μ : YoungDiagram) (hμ₀ : μ.rowLens ≠ [])
    (hμ₁ : μ.rowLens ≠ [1]) {d : ℕ} (w : FreeGroup (Fin d)) (hw : IsNonPower w) :
    Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        (LinearMap.trace ℂ (youngSpace N (stableRows μ N))
          (youngAct N (stableRows μ N) (FreeGroup.lift σ w))).re))
      atTop (𝓝 0) :=
  StrongConvHP17.tendsto_dev μ hμ₀ hμ₁ w hw
