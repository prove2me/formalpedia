-- Prove2me | solution 1 for OAI.Problem315.PairResampling.tripleGenerator_square
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:14:11.872229+00:00
-- url     : https://prove2.me/submissions/cd2b3307-62dc-45ef-8f72-4a546cfd21d6

import Mathlib
import Definitions.Def_SwitchChain
import Definitions.Def_OAIQWSWC002

section
-- module Solutions.OAIQW_Problem315.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem315.OrthogonalPairResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315
namespace PairResampling

attribute [local instance] Classical.propDecidable

theorem graphDegree_partition {n : ℕ} (a : Finset (Fin n))
    (G : SimpleGraph (Fin n)) (w : Fin n) :
    (a.filter (G.Adj w)).card + ((Finset.univ \ a).filter (G.Adj w)).card =
      graphDegree G w := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (G.Adj w)) (p := fun v => v ∈ a)
  have heq : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∈ a) = a.filter (G.Adj w) := by
    ext v
    simp [and_comm]
  have hneq : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a) =
      (Finset.univ \ a).filter (G.Adj w) := by
    ext v
    simp [and_comm]
  rw [heq, hneq] at h
  exact h

theorem sameFiber_of_fixed_edges {n : ℕ} (a : Finset (Fin n))
    {G H : SimpleGraph (Fin n)}
    (hdeg : ∀ w, graphDegree G w = graphDegree H w)
    (hout : ∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v)
    (hin : ∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) :
    SameFiber a G H := by
  refine ⟨hout, hin, ?_⟩
  intro w hw
  have hext : (Finset.univ \ a).filter (G.Adj w) =
      (Finset.univ \ a).filter (H.Adj w) := by
    apply Finset.filter_congr
    intro v hv
    exact hout w hw v (Finset.mem_sdiff.mp hv).2
  have hG := graphDegree_partition a G w
  have hH := graphDegree_partition a H w
  rw [hext, hdeg w] at hG
  omega

theorem sameFiber_state_iff {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))
    (G H : GraphState n d) :
    SameFiber a G.val H.val ↔
      (∀ u ∉ a, ∀ v ∉ a, G.val.Adj u v ↔ H.val.Adj u v) ∧
      (∀ u ∈ a, ∀ v ∈ a, G.val.Adj u v ↔ H.val.Adj u v) := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ?_⟩
  apply sameFiber_of_fixed_edges a _ h.1 h.2
  intro w
  exact (G.property w).trans (H.property w).symm

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

theorem expectation_isSymmetric :
    (expectation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a).starProjection_isSymmetric

theorem fluctuation_eq_sub (f : StateSpace n d) :
    fluctuation n d a f = f - expectation n d a f := by
  exact (fiberSpace n d a).starProjection_orthogonal_val f

@[simp] theorem fluctuation_eq_zero_iff (f : StateSpace n d) :
    fluctuation n d a f = 0 ↔ f ∈ fiberSpace n d a := by
  rw [fluctuation_eq_sub, sub_eq_zero, eq_comm, expectation_eq_self_iff]

end PairResampling
end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairGeneratorSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem tripleGenerator_apply {n : Nat} {d : Fin n → Nat}
    (T : Finset (Fin n)) (f : StateSpace n d) :
    tripleGenerator n d T f = ∑ a ∈ T.powersetCard 2, fluctuation n d a f := by
  simp [tripleGenerator]

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.PairFibers

section Partition

variable {α : Type*} [Fintype α]

theorem expectation_mem (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R f ∈ constantSubspace R :=
  (constantSubspace R).starProjection_apply_mem f

theorem expectation_constant (R : Setoid α) (f : EuclideanSpace ℝ α)
    {x y : α} (hxy : R.r x y) : expectation R f x = expectation R f y :=
  expectation_mem R f x y hxy

theorem expectation_eq_self_iff (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R f = f ↔ ∀ x y, R.r x y → f x = f y :=
  Submodule.starProjection_eq_self_iff

theorem expectation_symmetric (R : Setoid α) :
    (expectation R).toLinearMap.IsSymmetric :=
  (constantSubspace R).starProjection_isSymmetric

theorem cell_nonempty (R : Setoid α) (x : α) : (cell R x).Nonempty :=
  ⟨x, (mem_cell R x x).2 (R.refl x)⟩

omit [Fintype α] in
theorem cellIndicator_mem (R : Setoid α) (x : α) :
    cellIndicator R x ∈ constantSubspace R := by
  intro y z hyz
  change (if R.r x y then (1 : ℝ) else 0) = if R.r x z then 1 else 0
  have hiff : R.r x y ↔ R.r x z :=
    ⟨fun h => R.trans h hyz, fun h => R.trans h (R.symm hyz)⟩
  simp only [hiff]

theorem inner_cellIndicator (R : Setoid α) (x : α) (f : EuclideanSpace ℝ α) :
    inner ℝ f (cellIndicator R x) = ∑ y ∈ cell R x, f y := by
  simp [cellIndicator, PiLp.inner_apply, cell, Finset.sum_filter]

theorem expectation_apply (R : Setoid α) (f : EuclideanSpace ℝ α) (x : α) :
    expectation R f x = (∑ y ∈ cell R x, f y) / ((cell R x).card : ℝ) := by
  have hcNat : 0 < (cell R x).card := Finset.card_pos.mpr (cell_nonempty R x)
  have hc : (0 : ℝ) < (cell R x).card := by exact_mod_cast hcNat
  have horth := Submodule.starProjection_inner_eq_zero
    (K := constantSubspace R) f (cellIndicator R x) (cellIndicator_mem R x)
  change inner ℝ (f - expectation R f) (cellIndicator R x) = 0 at horth
  rw [inner_sub_left, inner_cellIndicator, inner_cellIndicator] at horth
  have hsum : (∑ y ∈ cell R x, expectation R f y) =
      (cell R x).card * expectation R f x := by
    calc
      (∑ y ∈ cell R x, expectation R f y) = ∑ _y ∈ cell R x, expectation R f x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (expectation_constant R f ((mem_cell R x y).1 hy)).symm
      _ = _ := by simp
  rw [hsum] at horth
  apply (eq_div_iff (ne_of_gt hc)).2
  nlinarith

end Partition

end Problem315.PairFibers

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CellProjectionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CellProjectionTransport

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

theorem expectation_restrict (R : Setoid α) (C : α → Prop)
    (hC : ∀ x y, R.r x y → (C x ↔ C y)) (f : EuclideanSpace ℝ α) :
    restrict C (PairFibers.expectation R f) =
      PairFibers.expectation (restrictedSetoid R C) (restrict C f) := by
  ext x
  simp only [restrict_apply, PairFibers.expectation_apply]
  have hc : (PairFibers.cell R x.val).card =
      (PairFibers.cell (restrictedSetoid R C) x).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (classEquiv R C hC x)
  rw [hc]
  congr 1
  calc
    (∑ y ∈ PairFibers.cell R x.val, f y) =
        ∑ y : PairFibers.cell R x.val, f y.val :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ y : PairFibers.cell (restrictedSetoid R C) x, f y.val.val :=
      (classEquiv R C hC x).sum_comp (fun y => f y.val.val)
    _ = ∑ y ∈ PairFibers.cell (restrictedSetoid R C) x, f y.val :=
      Finset.sum_coe_sort (PairFibers.cell (restrictedSetoid R C) x) (fun y => f y.val)

@[simp] theorem expectation_constant (R : Setoid α) (c : ℝ) :
    PairFibers.expectation R (WithLp.toLp 2 (fun _ : α => c)) =
      WithLp.toLp 2 (fun _ : α => c) := by
  apply (PairFibers.expectation_eq_self_iff R _).mpr
  intro x y hxy
  rfl

theorem sum_expectation (R : Setoid α) (f : EuclideanSpace ℝ α) :
    (∑ x, PairFibers.expectation R f x) = ∑ x, f x := by
  let one : EuclideanSpace ℝ α := WithLp.toLp 2 (fun _ => 1)
  have h := PairFibers.expectation_symmetric R f one
  change ⟪PairFibers.expectation R f, one⟫ =
    ⟪f, PairFibers.expectation R one⟫ at h
  rw [show PairFibers.expectation R one = one from expectation_constant R 1] at h
  simpa [PiLp.inner_apply, one] using h

variable {n : ℕ} {d : Fin n → ℕ}

theorem graph_expectation (a : Finset (Fin n)) :
    PairFibers.expectation (graphSetoid (d := d) a) = PairResampling.expectation n d a := by
  have h : PairFibers.constantSubspace (graphSetoid (d := d) a) =
      PairResampling.fiberSpace n d a := by
    ext f
    rfl
  unfold PairFibers.expectation PairResampling.expectation
  simp only [h]

theorem graph_expectation_restrict (a : Finset (Fin n)) (C : GraphState n d → Prop)
    (hC : ∀ G H, PairResampling.SameFiber a G.val H.val → (C G ↔ C H))
    (f : PairResampling.StateSpace n d) :
    restrict C (PairResampling.expectation n d a f) =
      PairFibers.expectation (restrictedSetoid (graphSetoid a) C) (restrict C f) := by
  rw [← graph_expectation]
  exact expectation_restrict (graphSetoid a) C hC f

end Problem315.CellProjectionTransport

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FixedBlockPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FixedBlock

variable {α : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α]

lemma relabel_mul {sizes : Fin 3 → ℕ} (σ τ : Equiv.Perm α)
    (c : Partition (α := α) sizes) :
    relabel (σ * τ) c = relabel σ (relabel τ c) := by
  apply Subtype.ext
  rfl

lemma row_swap_unchanged (c : α → Fin 3) (a b : α) (i : Fin 3)
    (hai : c a ≠ i) (hbi : c b ≠ i) :
    row (fun x => c ((Equiv.swap a b).symm x)) i = row c i := by
  ext x
  simp only [mem_row, Equiv.symm_swap]
  by_cases hxa : x = a
  · subst x
    simp [hai, hbi]
  · by_cases hxb : x = b
    · subst x
      simp [hai, hbi]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

lemma exists_unused_color (a b : Fin 3) : ∃ i : Fin 3, i ≠ a ∧ i ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma three_sum_sq_le_twice (f : Fin 3 → ℝ) (i : Fin 3) (hi : f i = 0) :
    (∑ j, f j) ^ 2 ≤ 2 * ∑ j, (f j) ^ 2 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i
  · change f 0 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 1 - f 2)]
  · change f 1 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 0 - f 2)]
  · change f 2 = 0 at hi
    rw [hi]
    nlinarith [sq_nonneg (f 0 - f 1)]

lemma exists_relabel {sizes : Fin 3 → ℕ}
    (c d : Partition (α := α) sizes) :
    ∃ σ : Equiv.Perm α, relabel σ c = d := by
  classical
  have hcard (i : Fin 3) :
      Fintype.card {a : α // c.val a = i} = Fintype.card {a : α // d.val a = i} := by
    simpa [Fintype.card_subtype, row] using (c.property i).trans (d.property i).symm
  let e (i : Fin 3) : {a : α // c.val a = i} ≃ {a : α // d.val a = i} :=
    Fintype.equivOfCardEq (hcard i)
  let σ : Equiv.Perm α := Equiv.ofFiberEquiv e
  refine ⟨σ, Subtype.ext ?_⟩
  funext a
  have h := Equiv.ofFiberEquiv_map e (σ.symm a)
  change d.val (σ (σ.symm a)) = c.val (σ.symm a) at h
  change c.val (σ.symm a) = d.val a
  simpa only [Equiv.apply_symm_apply] using h.symm

lemma eq_of_swap_invariant {sizes : Fin 3 → ℕ}
    (f : Partition (α := α) sizes → ℝ)
    (hf : ∀ a b c, f (relabel (Equiv.swap a b) c) = f c)
    (c d : Partition (α := α) sizes) : f c = f d := by
  obtain ⟨σ, hσ⟩ := exists_relabel c d
  have hperm (σ : Equiv.Perm α) : ∀ c, f (relabel σ c) = f c := by
    induction σ using Equiv.Perm.swap_induction_on with
    | one => intro c; simp
    | swap_mul σ a b hab ih =>
      intro c
      rw [relabel_mul, hf, ih]
  rw [← hσ, hperm]

end Problem315.FixedBlock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.EnergyTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.EnergyTransfer

theorem norm_sq_le_of_intertwining_energy_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (J : E →ₗ[ℝ] E) (K : F →ₗ[ℝ] F)
    (hJ : ∀ x : E, x ≠ 0 → 0 < ⟪x, J x⟫)
    (hinter : ∀ x : E, K (A x) = A (J x))
    (c : ℝ) (henergy : ∀ x : E, ⟪A x, K (A x)⟫ ≤ c * ⟪x, J x⟫)
    (x : E) : ‖A x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := by
  classical
  let B : E →ₗ[ℝ] E := A.adjoint.comp A
  have hB : B.IsSymmetric := A.isPositive_adjoint_comp_self.isSymmetric
  let b := hB.eigenvectorBasis rfl
  let ev := hB.eigenvalues rfl
  have hbe (i : Fin (Module.finrank ℝ E)) : B (b i) = ev i • b i :=
    hB.apply_eigenvectorBasis rfl i
  have hev (i : Fin (Module.finrank ℝ E)) : ev i ≤ c := by
    have he := henergy (b i)
    rw [hinter] at he
    have hid : ⟪A (b i), A (J (b i))⟫ = ⟪B (b i), J (b i)⟫ :=
      (A.adjoint_inner_left (J (b i)) (A (b i))).symm
    rw [hid, hbe, inner_smul_left] at he
    simp only [RCLike.conj_to_real] at he
    have hp : 0 < ⟪b i, J (b i)⟫ := hJ (b i) (b.toBasis.ne_zero i)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [mul_comm] using he)
  have hnorm : ‖A x‖ ^ 2 = ⟪x, B x⟫ := by
    change ‖A x‖ ^ 2 = ⟪x, A.adjoint (A x)⟫
    rw [A.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hnorm, ← b.sum_sq_inner_right x, Finset.mul_sum,
    ← b.sum_inner_mul_inner x (B x)]
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : ⟪b i, B x⟫ = ev i * ⟪b i, x⟫ := by
    rw [← hB (b i) x, hbe, inner_smul_left]
    simp
  rw [hcoord, real_inner_comm x (b i)]
  nlinarith [mul_le_mul_of_nonneg_right (hev i) (sq_nonneg ⟪x, b i⟫)]

theorem norm_sum_sq_le_of_invariant_energy_bound
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (V : ι → Submodule ℝ E) (J : E →ₗ[ℝ] E)
    (hinv : ∀ i x, x ∈ V i → J x ∈ V i)
    (hpos : ∀ i x, x ∈ V i → x ≠ 0 → 0 < ⟪x, J x⟫)
    (c : ℝ)
    (henergy : ∀ f : ι → E, (∀ i, f i ∈ V i) →
      ⟪∑ i, f i, J (∑ i, f i)⟫ ≤ c * ∑ i, ⟪f i, J (f i)⟫)
    (f : ι → E) (hf : ∀ i, f i ∈ V i) :
    ‖∑ i, f i‖ ^ 2 ≤ c * ∑ i, ‖f i‖ ^ 2 := by
  classical
  let D := PiLp 2 (fun i => V i)
  let A : D →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, (x i : E)
      map_add' := by intro x y; simp [D, Finset.sum_add_distrib]
      map_smul' := by intro r x; simp [D, Finset.smul_sum] }
  let L : D →ₗ[ℝ] D :=
    { toFun := fun x => WithLp.toLp 2 (fun i => ⟨J (x i), hinv i _ (x i).property⟩)
      map_add' := by intro x y; ext i; simp [D]
      map_smul' := by intro r x; ext i; simp [D] }
  have hL (x : D) (hx : x ≠ 0) : 0 < ⟪x, L x⟫ := by
    have hnonneg (i : ι) : 0 ≤ ⟪(x i : E), J (x i)⟫ := by
      by_cases hz : (x i : E) = 0
      · simp [hz]
      · exact (hpos i _ (x i).property hz).le
    have hex : ∃ i, (x i : E) ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      ext i
      exact hn i
    obtain ⟨i, hi⟩ := hex
    change 0 < ∑ j, ⟪(x j : E), J (x j)⟫
    exact Finset.sum_pos' (fun j _ => hnonneg j)
      ⟨i, Finset.mem_univ i, hpos i _ (x i).property hi⟩
  have hinter (x : D) : J (A x) = A (L x) := by
    change J (∑ i, (x i : E)) = ∑ i, J (x i)
    exact map_sum J _ _
  have hEn (x : D) : ⟪A x, J (A x)⟫ ≤ c * ⟪x, L x⟫ := by
    exact henergy (fun i => (x i : E)) (fun i => (x i).property)
  have h := norm_sq_le_of_intertwining_energy_bound A L J hL hinter c hEn
    (WithLp.toLp 2 (fun i => (⟨f i, hf i⟩ : V i)))
  simpa [D, A, PiLp.norm_sq_eq_of_L2] using h

end Problem315.EnergyTransfer

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PermutationGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PermutationGenerator

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

theorem sum_apply (τ : S → Equiv.Perm Ω) (f : Ω → ℝ) :
    ∑ x, apply τ f x = 0 := by
  unfold apply
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (τ s)]
  exact sub_self _

theorem inner_operator (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    ⟪f, operator τ f⟫ = (1 / 2 : ℝ) * ∑ s, ∑ x, (f x - f (τ s x)) ^ 2 := by
  have hsingle (s : S) :
      (∑ x, f x * (f x - f (τ s x))) =
        (1 / 2 : ℝ) * ∑ x, (f x - f (τ s x)) ^ 2 := by
    have heq : (∑ x, (f (τ s x)) ^ 2) = ∑ x, (f x) ^ 2 :=
      Equiv.sum_comp (τ s) (fun x => (f x) ^ 2)
    have hexpand : (∑ x, (f x - f (τ s x)) ^ 2) =
        (∑ x, (f x) ^ 2) + (∑ x, (f (τ s x)) ^ 2) -
          2 * ∑ x, f x * f (τ s x) := by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hexpand, heq]
    simp only [mul_sub, ← pow_two, Finset.sum_sub_distrib]
    ring
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, operator_apply, apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simpa only [Finset.mul_sum, mul_comm] using hsingle s

theorem inner_operator_nonneg (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    0 ≤ ⟪f, operator τ f⟫ := by
  rw [inner_operator]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem inner_operator_eq_zero_iff (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    ⟪f, operator τ f⟫ = 0 ↔ ∀ s x, f (τ s x) = f x := by
  rw [inner_operator]
  constructor
  · intro hz s x
    have hall : (∑ s, ∑ x, (f x - f (τ s x)) ^ 2) = 0 := by linarith
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
      Finset.sum_nonneg (fun x _ => sq_nonneg (f x - f (τ s x))))).mp hall s (Finset.mem_univ s)
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      sq_nonneg (f x - f (τ s x)))).mp hs x (Finset.mem_univ x)
    nlinarith
  · intro h
    simp [h]

theorem inner_operator_pos_of_centered [Nonempty Ω]
    (τ : S → Equiv.Perm Ω)
    (hconn : ∀ f : Ω → ℝ, (∀ s x, f (τ s x) = f x) → ∀ x y, f x = f y)
    (f : EuclideanSpace ℝ Ω) (hcenter : ∑ x, f x = 0) (hf : f ≠ 0) :
    0 < ⟪f, operator τ f⟫ := by
  have hnonneg := inner_operator_nonneg τ f
  apply lt_of_le_of_ne hnonneg
  intro he
  have hinv := (inner_operator_eq_zero_iff τ f).mp he.symm
  obtain ⟨a⟩ := ‹Nonempty Ω›
  have hc := hconn f hinv
  have hfa : f a = 0 := by
    have heq : (∑ x, f x) = (Fintype.card Ω : ℝ) * f a := by
      simp [fun x => hc x a]
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [heq] at hcenter
    exact (mul_eq_zero.mp hcenter).resolve_left hcard
  apply hf
  ext x
  change f x = 0
  rw [hc x a, hfa]

theorem energy_sum_le_of_local_bound
    {ι : Type*} [Fintype ι] (τ : S → Equiv.Perm Ω)
    (f : ι → EuclideanSpace ℝ Ω) (c : ℝ)
    (hlocal : ∀ s x,
      (∑ i, (f i x - f i (τ s x))) ^ 2 ≤
        c * ∑ i, (f i x - f i (τ s x)) ^ 2) :
    ⟪∑ i, f i, operator τ (∑ i, f i)⟫ ≤ c * ∑ i, ⟪f i, operator τ (f i)⟫ := by
  simp_rw [inner_operator]
  have heval (x : Ω) : (∑ i, f i) x = ∑ i, f i x := by simp
  simp_rw [heval, ← Finset.sum_sub_distrib]
  calc
    (1 / 2 : ℝ) * ∑ s, ∑ x, (∑ i, (f i x - f i (τ s x))) ^ 2
        ≤ (1 / 2 : ℝ) * ∑ s, ∑ x, c * ∑ i, (f i x - f i (τ s x)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun x _ => hlocal s x
    _ = c * ∑ i, (1 / 2 : ℝ) * ∑ s, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      have heq : (∑ s, ∑ x, ∑ i, (f i x - f i (τ s x)) ^ 2) =
          ∑ i, ∑ s, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
        calc
          _ = ∑ s, ∑ i, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_comm]
          _ = _ := Finset.sum_comm
      rw [heq]
      ring

theorem norm_sum_sq_le_of_invariant_moves [Nonempty Ω]
    {ι : Type*} [Fintype ι] (τ : S → Equiv.Perm Ω)
    (hconn : ∀ f : Ω → ℝ, (∀ s x, f (τ s x) = f x) → ∀ x y, f x = f y)
    (V : ι → Submodule ℝ (EuclideanSpace ℝ Ω))
    (hcenter : ∀ i f, f ∈ V i → ∑ x, f x = 0)
    (hinv : ∀ i f, f ∈ V i → operator τ f ∈ V i)
    (c : ℝ)
    (hlocal : ∀ f : ι → EuclideanSpace ℝ Ω, (∀ i, f i ∈ V i) → ∀ s x,
      (∑ i, (f i x - f i (τ s x))) ^ 2 ≤ c * ∑ i, (f i x - f i (τ s x)) ^ 2)
    (f : ι → EuclideanSpace ℝ Ω) (hf : ∀ i, f i ∈ V i) :
    ‖∑ i, f i‖ ^ 2 ≤ c * ∑ i, ‖f i‖ ^ 2 := by
  apply EnergyTransfer.norm_sum_sq_le_of_invariant_energy_bound V (operator τ) hinv
    (fun i g hg hne => inner_operator_pos_of_centered τ hconn g (hcenter i g hg) hne)
    c _ f hf
  intro g hg
  exact energy_sum_le_of_local_bound τ g c (hlocal g hg)

end Problem315.PermutationGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FixedBlockVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.FixedBlockVariance
open FixedBlock

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (p q : Fin 3 → ℕ)

theorem key_move_eq (i : Fin 3) (s : (α × α) ⊕ (β × β))
    (x y : State (α := α) (β := β) p q) (h : key p q i x = key p q i y) :
    key p q i (move p q s x) = key p q i (move p q s y) := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change row x.1.val i = row y.1.val i at h1
  change row x.2.val i = row y.2.val i at h2
  cases s with
  | inl ab =>
      change (row (fun a => x.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row x.2.val i) =
        (row (fun a => y.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row y.2.val i)
      rw [row_relabel, row_relabel, h1, h2]
  | inr ab =>
      change (row x.1.val i, row (fun b => x.2.val ((Equiv.swap ab.1 ab.2).symm b)) i) =
        (row y.1.val i, row (fun b => y.2.val ((Equiv.swap ab.1 ab.2).symm b)) i)
      rw [row_relabel, row_relabel, h1, h2]

theorem constant_of_move_invariant
    (f : State (α := α) (β := β) p q → ℝ)
    (hf : ∀ s x, f (move p q s x) = f x)
    (x y : State (α := α) (β := β) p q) : f x = f y := by
  have hleft (d : Partition (α := β) q) (c e : Partition (α := α) p) :
      f (c, d) = f (e, d) := by
    apply eq_of_swap_invariant (fun c => f (c, d)) _ c e
    intro a b c
    exact hf (Sum.inl (a, b)) (c, d)
  have hright (c : Partition (α := α) p) (d e : Partition (α := β) q) :
      f (c, d) = f (c, e) := by
    apply eq_of_swap_invariant (fun d => f (c, d)) _ d e
    intro a b d
    exact hf (Sum.inr (a, b)) (c, d)
  exact (hleft x.2 x.1 y.1).trans (hright y.1 x.2 y.2)

theorem rowSpace_invariant (i : Fin 3)
    (f : EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : f ∈ rowSpace p q i) :
    PermutationGenerator.operator (move p q) f ∈ rowSpace p q i := by
  constructor
  · exact PermutationGenerator.sum_apply (move p q) f
  · intro x y h
    change (∑ s, (f x - f (move p q s x))) = ∑ s, (f y - f (move p q s y))
    apply Finset.sum_congr rfl
    intro s hs
    rw [hf.2 x y h, hf.2 _ _ (key_move_eq p q i s x y h)]

theorem local_energy_bound
    (f : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : ∀ i, f i ∈ rowSpace p q i)
    (s : (α × α) ⊕ (β × β)) (x : State (α := α) (β := β) p q) :
    (∑ i, (f i x - f i (move p q s x))) ^ 2 ≤
      2 * ∑ i, (f i x - f i (move p q s x)) ^ 2 := by
  cases s with
  | inl ab =>
      obtain ⟨i, hia, hib⟩ := exists_unused_color (x.1.val ab.1) (x.1.val ab.2)
      apply three_sum_sq_le_twice _ i
      have hk : key p q i (move p q (Sum.inl ab) x) = key p q i x := by
        change (row (fun a => x.1.val ((Equiv.swap ab.1 ab.2).symm a)) i, row x.2.val i) =
          (row x.1.val i, row x.2.val i)
        rw [row_swap_unchanged _ _ _ _ (Ne.symm hia) (Ne.symm hib)]
      rw [(hf i).2 _ _ hk, sub_self]
  | inr ab =>
      obtain ⟨i, hia, hib⟩ := exists_unused_color (x.2.val ab.1) (x.2.val ab.2)
      apply three_sum_sq_le_twice _ i
      have hk : key p q i (move p q (Sum.inr ab) x) = key p q i x := by
        change (row x.1.val i, row (fun b => x.2.val ((Equiv.swap ab.1 ab.2).symm b)) i) =
          (row x.1.val i, row x.2.val i)
        rw [row_swap_unchanged _ _ _ _ (Ne.symm hia) (Ne.symm hib)]
      rw [(hf i).2 _ _ hk, sub_self]

theorem centered_row_norm_bound [Nonempty (State (α := α) (β := β) p q)]
    (f : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q))
    (hf : ∀ i, f i ∈ rowSpace p q i) :
    ‖∑ i, f i‖ ^ 2 ≤ 2 * ∑ i, ‖f i‖ ^ 2 := by
  exact PermutationGenerator.norm_sum_sq_le_of_invariant_moves (move p q)
    (constant_of_move_invariant p q) (rowSpace p q)
    (fun i f hf => hf.1) (rowSpace_invariant p q) 2
    (local_energy_bound p q) f hf

theorem sum_sub_average [Nonempty (State (α := α) (β := β) p q)]
    (f : State (α := α) (β := β) p q → ℝ) :
    ∑ x, (f x - average p q f) = 0 := by
  have hc : (Fintype.card (State (α := α) (β := β) p q) : ℝ) ≠ 0 :=
    by exact_mod_cast Fintype.card_ne_zero
  simp only [average, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem average_sum (f : Fin 3 → State (α := α) (β := β) p q → ℝ) :
    average p q (fun x => ∑ i, f i x) = ∑ i, average p q (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem row_variance_bound [Nonempty (State (α := α) (β := β) p q)]
    (f : Fin 3 → State (α := α) (β := β) p q → ℝ)
    (hf : ∀ i x y, key p q i x = key p q i y → f i x = f i y) :
    variance p q (fun x => ∑ i, f i x) ≤ 2 * ∑ i, variance p q (f i) := by
  let g : Fin 3 → EuclideanSpace ℝ (State (α := α) (β := β) p q) :=
    fun i => WithLp.toLp 2 (fun x => f i x - average p q (f i))
  have hg (i : Fin 3) : g i ∈ rowSpace p q i := by
    constructor
    · exact sum_sub_average p q (f i)
    · intro x y h
      change f i x - average p q (f i) = f i y - average p q (f i)
      rw [hf i x y h]
  have h := centered_row_norm_bound p q g hg
  have htotal : ‖∑ i, g i‖ ^ 2 =
      ∑ x, ((∑ i, f i x) - average p q (fun y => ∑ i, f i y)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro x hx
    have he : (∑ i, g i) x = ∑ i, (f i x - average p q (f i)) := by simp [g]
    rw [he, Finset.sum_sub_distrib, average_sum]
  have heach (i : Fin 3) : ‖g i‖ ^ 2 = ∑ x, (f i x - average p q (f i)) ^ 2 := by
    exact EuclideanSpace.real_norm_sq_eq (g i)
  rw [htotal] at h
  simp_rw [heach] at h
  unfold variance
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

theorem variance_sum_row_functions [Nonempty (State (α := α) (β := β) p q)]
    (g : Fin 3 → Finset α → Finset β → ℝ) :
    variance p q (fun x => ∑ i, g i (row x.1.val i) (row x.2.val i)) ≤
      2 * ∑ i, variance p q (fun x => g i (row x.1.val i) (row x.2.val i)) := by
  apply row_variance_bound p q
  intro i x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change row x.1.val i = row y.1.val i at h1
  change row x.2.val i = row y.2.val i at h2
  rw [h1, h2]

end Problem315.FixedBlockVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FixedBlockMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FixedBlockMarginal
open FixedBlock

theorem average_congr {X : Type*} [Fintype X] {f g : X → ℝ}
    (h : ∀ x, f x = g x) : average f = average g := by
  simp only [average]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => h x)

theorem average_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    average (fun _ : X => c) = c := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, hc]

theorem average_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, e.sum_comp, Fintype.card_congr e]

theorem average_comm {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    average (fun x => average (fun y => f x y)) =
      average (fun y => average (fun x => f x y)) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem average_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    average f = average (fun x => average (fun y => f (x, y))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

variable {α : Type*} [sectionFintypeα : Fintype α] [sectionDecidableEqα : DecidableEq α]

theorem permutation_average_eq {p : Fin 3 → ℕ}
    (f : Partition (α := α) p → ℝ) (c d : Partition (α := α) p) :
    average (fun σ : Equiv.Perm α => f (relabel σ c)) =
      average (fun σ : Equiv.Perm α => f (relabel σ d)) := by
  obtain ⟨τ, rfl⟩ := exists_relabel c d
  symm
  calc
    average (fun σ : Equiv.Perm α => f (relabel σ (relabel τ c))) =
        average (fun σ : Equiv.Perm α => f (relabel (σ * τ) c)) := by
      apply average_congr
      intro σ
      rw [relabel_mul]
    _ = _ := by
      simpa using average_equiv (Equiv.mulRight τ) (fun σ : Equiv.Perm α => f (relabel σ c))

theorem average_eq_permutation_average {p : Fin 3 → ℕ}
    (f : Partition (α := α) p → ℝ) (c : Partition (α := α) p) :
    average f = average (fun σ : Equiv.Perm α => f (relabel σ c)) := by
  let : Nonempty (Partition (α := α) p) := ⟨c⟩
  calc
    average f = average (fun _ : Equiv.Perm α => average f) := (average_const _).symm
    _ = average (fun σ : Equiv.Perm α =>
        average (fun d : Partition (α := α) p => f (relabel σ d))) := by
      apply average_congr
      intro σ
      exact (average_equiv (FixedBlockVariance.relabelPerm p σ) f).symm
    _ = average (fun d : Partition (α := α) p =>
        average (fun σ : Equiv.Perm α => f (relabel σ d))) := average_comm _
    _ = average (fun _ : Partition (α := α) p =>
        average (fun σ : Equiv.Perm α => f (relabel σ c))) := by
      apply average_congr
      intro d
      exact permutation_average_eq f d c
    _ = _ := average_const _

theorem exists_perm_map (s t : Finset α) (h : s.card = t.card) :
    ∃ σ : Equiv.Perm α, s.map σ.toEmbedding = t := by
  let e : {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
    Fintype.equivOfCardEq (by simpa using h)
  refine ⟨e.extendSubtype, ?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact e.extendSubtype_mem b hb
  · intro ha
    let b := e.extendSubtype.symm a
    have hb : b ∈ s := by
      by_contra hn
      have hh := e.extendSubtype_not_mem b hn
      exact hh (by simpa [b] using ha)
    exact Finset.mem_map.mpr ⟨b, hb, e.extendSubtype.apply_symm_apply a⟩

variable {β : Type*} [Fintype β] [DecidableEq β]

include sectionFintypeα sectionDecidableEqα in
theorem subsetPerm_mul (k : ℕ) (σ τ : Equiv.Perm α) (s : Subsets (α := α) k) :
    subsetPerm k (σ * τ) s = subsetPerm k σ (subsetPerm k τ s) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  ext a
  simp [subsetPerm]
  rfl

theorem subset_permutation_average_eq (k : ℕ) (g : Subsets (α := α) k → ℝ)
    (s t : Subsets (α := α) k) :
    average (fun σ : Equiv.Perm α => g (subsetPerm k σ s)) =
      average (fun σ : Equiv.Perm α => g (subsetPerm k σ t)) := by
  obtain ⟨τ, hτ⟩ := exists_perm_map s.val t.val (s.property.trans t.property.symm)
  have ht : subsetPerm k τ s = t := Subtype.ext hτ
  rw [← ht]
  symm
  calc
    _ = average (fun σ : Equiv.Perm α => g (subsetPerm k (σ * τ) s)) := by
      apply average_congr
      intro σ
      rw [subsetPerm_mul]
    _ = _ := by
      simpa using average_equiv (Equiv.mulRight τ)
        (fun σ : Equiv.Perm α => g (subsetPerm k σ s))

theorem subset_average_eq_permutation_average (k : ℕ)
    (g : Subsets (α := α) k → ℝ) (s : Subsets (α := α) k) :
    average g = average (fun σ : Equiv.Perm α => g (subsetPerm k σ s)) := by
  let : Nonempty (Subsets (α := α) k) := ⟨s⟩
  calc
    average g = average (fun _ : Equiv.Perm α => average g) := (average_const _).symm
    _ = average (fun σ : Equiv.Perm α =>
        average (fun t : Subsets (α := α) k => g (subsetPerm k σ t))) := by
      apply average_congr
      intro σ
      exact (average_equiv (subsetPerm k σ) g).symm
    _ = average (fun t : Subsets (α := α) k =>
        average (fun σ : Equiv.Perm α => g (subsetPerm k σ t))) := average_comm _
    _ = average (fun _ : Subsets (α := α) k =>
        average (fun σ : Equiv.Perm α => g (subsetPerm k σ s))) := by
      apply average_congr
      intro t
      exact subset_permutation_average_eq k g t s
    _ = _ := average_const _

theorem average_row_eq_subset_average {p : Fin 3 → ℕ} (i : Fin 3)
    (c : Partition (α := α) p) (g : Finset α → ℝ) :
    average (fun x : Partition (α := α) p => g (row x.val i)) =
      average (fun s : Subsets (α := α) (p i) => g s.val) := by
  rw [average_eq_permutation_average _ c,
    subset_average_eq_permutation_average _ _ ⟨row c.val i, c.property i⟩]
  apply average_congr
  intro σ
  change g (row (fun a => c.val (σ.symm a)) i) = g ((row c.val i).map σ.toEmbedding)
  rw [row_relabel]

theorem row_function_average_eq_subset_average {p q : Fin 3 → ℕ} (i : Fin 3)
    (c : Partition (α := α) p) (d : Partition (α := β) q)
    (g : Finset α → Finset β → ℝ) :
    FixedBlockVariance.average p q (fun x => g (row x.1.val i) (row x.2.val i)) =
      average (fun x : Subsets (α := α) (p i) × Subsets (α := β) (q i) =>
        g x.1.val x.2.val) := by
  change average (fun x : Partition (α := α) p × Partition (α := β) q =>
      g (row x.1.val i) (row x.2.val i)) = _
  rw [average_prod, average_prod]
  calc
    _ = average (fun x : Partition (α := α) p =>
        average (fun y : Subsets (α := β) (q i) => g (row x.val i) y.val)) := by
      apply average_congr
      intro x
      exact average_row_eq_subset_average i d (g (row x.val i))
    _ = _ := average_row_eq_subset_average i c
      (fun s => average (fun y : Subsets (α := β) (q i) => g s y.val))

end Problem315.FixedBlockMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiniteVarianceDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteVariance

open FixedBlockMarginal (average)

variable {X I : Type*} [Fintype X] [Fintype I]

theorem average_add (f g : X → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp only [average, Finset.sum_add_distrib, add_div]

theorem average_sub (f g : X → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp only [average, Finset.sum_sub_distrib, sub_div]

theorem average_mul (c : ℝ) (f : X → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : I → X → ℝ) :
    average (fun x => ∑ i, f i x) = ∑ i, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem variance_eq [Nonempty X] (f : X → ℝ) :
    variance f = average (fun x => (f x) ^ 2) - (average f) ^ 2 := by
  have heq : (fun x => (f x - average f) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * average f) * f x + (average f) ^ 2) := by
    funext x
    ring
  rw [variance, heq, average_add, average_sub, average_mul,
    FixedBlockMarginal.average_const]
  ring

theorem average_center [Nonempty X] (f : X → ℝ) :
    average (fun x => f x - average f) = 0 := by
  rw [average_sub, FixedBlockMarginal.average_const, sub_self]

theorem variance_equiv {Y : Type*} [Fintype Y] (e : X ≃ Y) (f : Y → ℝ) :
    variance (fun x => f (e x)) = variance f := by
  unfold variance
  rw [FixedBlockMarginal.average_equiv]
  exact FixedBlockMarginal.average_equiv e (fun y => (f y - average f) ^ 2)

theorem mixture_centered_row_bound {K : Type*} [Fintype K]
    (Y : K → Type*) [∀ k, Fintype (Y k)] [∀ k, Nonempty (Y k)]
    (p : K → ℝ) (hp : ∀ k, 0 ≤ p k)
    (f : I → ∀ k, Y k → ℝ)
    (hfixed : ∀ k, variance (fun y => ∑ i, f i k y) ≤
      2 * ∑ i, variance (f i k))
    (hmean : (∑ k, p k * (∑ i, average (f i k)) ^ 2) ≤
      2 * ∑ i, ∑ k, p k * (average (f i k)) ^ 2) :
    (∑ k, p k * average (fun y => (∑ i, f i k y) ^ 2)) ≤
      2 * ∑ i, ∑ k, p k * average (fun y => (f i k y) ^ 2) := by
  have hfixed' (k : K) := hfixed k
  simp_rw [variance_eq, average_sum] at hfixed'
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hfixed' k) (hp k))
  simp only [mul_sub, Finset.sum_sub_distrib] at hs
  have hrew (q : I → K → ℝ) :
      (∑ k, p k * (2 * ∑ i, q i k)) = 2 * ∑ i, ∑ k, p k * q i k := by
    calc
      _ = ∑ k, 2 * (∑ i, p k * q i k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.mul_sum]
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hrew, hrew] at hs
  linarith

end Problem315.FiniteVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiniteVarianceEuclidean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteVariance

open FixedBlockMarginal (average)

variable {X I : Type*} [Fintype X] [Fintype I]

theorem average_square_eq_norm_sq_div_card (f : X → ℝ) :
    average (fun x => (f x) ^ 2) =
      ‖WithLp.toLp 2 f‖ ^ 2 / (Fintype.card X : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem variance_eq_centered_norm_sq_div_card (f : X → ℝ) :
    variance f =
      ‖WithLp.toLp 2 (fun x => f x - average f)‖ ^ 2 /
        (Fintype.card X : ℝ) :=
  average_square_eq_norm_sq_div_card _

theorem variance_eq_norm_sq_div_card_of_average_zero
    (f : EuclideanSpace ℝ X) (hf : average (fun x => f x) = 0) :
    variance (fun x => f x) = ‖f‖ ^ 2 / (Fintype.card X : ℝ) := by
  rw [variance_eq_centered_norm_sq_div_card, hf]
  simp only [sub_zero, WithLp.toLp_ofLp]

theorem norm_sum_sq_le_of_variance_bound [Nonempty X]
    (y : I → EuclideanSpace ℝ X) (c : ℝ)
    (hcenter : ∀ i, average (fun x => y i x) = 0)
    (hvar : variance (fun x => ∑ i, y i x) ≤
      c * ∑ i, variance (fun x => y i x)) :
    ‖∑ i, y i‖ ^ 2 ≤ c * ∑ i, ‖y i‖ ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos
  have hsum : average (fun x => (∑ i, y i) x) = 0 := by
    simp only [WithLp.ofLp_sum, Finset.sum_apply, average_sum, hcenter, Finset.sum_const_zero]
  have hleft := variance_eq_norm_sq_div_card_of_average_zero (∑ i, y i) hsum
  have hright (i : I) := variance_eq_norm_sq_div_card_of_average_zero (y i) (hcenter i)
  simp only [WithLp.ofLp_sum, Finset.sum_apply] at hleft
  rw [hleft] at hvar
  simp_rw [hright] at hvar
  rw [← Finset.sum_div, ← mul_div_assoc] at hvar
  exact (div_le_div_iff_of_pos_right hcard).mp hvar

end Problem315.FiniteVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiberLabelCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.FiberLabelCounting

variable {V C : Type*} [sectionFintypeV : Fintype V] [sectionFintypeC : Fintype C]

theorem equalFiberColorings_card_mul_factorials (f₀ : V → C) :
    Fintype.card (EqualFiberColorings f₀) *
      (∏ c, (Fintype.card {v // f₀ v = c}).factorial) = (Fintype.card V).factorial := by
  have he (g : EqualFiberColorings f₀) :
      Fintype.card (∀ c, {v // f₀ v = c} ≃ {v // g.val v = c}) =
        ∏ c, (Fintype.card {v // f₀ v = c}).factorial := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro c _
    exact Fintype.card_equiv (Fintype.equivOfCardEq (g.property c).symm)
  have hd : Fintype.card (LabeledFibers f₀) =
      Fintype.card (EqualFiberColorings f₀) *
        (∏ c, (Fintype.card {v // f₀ v = c}).factorial) := by
    rw [Fintype.card_sigma]
    simp_rw [he]
    simp
  rw [← hd, Fintype.card_congr (labeledFibersEquivPerm f₀), Fintype.card_perm]

theorem prescribedFiberColorings_nonempty (k : C → ℕ)
    (hk : ∑ c, k c = Fintype.card V) :
    Nonempty (PrescribedFiberColorings (V := V) k) := by
  have hc : Fintype.card V = Fintype.card (Σ c, Fin (k c)) := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using hk.symm
  let e : V ≃ (Σ c, Fin (k c)) := Fintype.equivOfCardEq hc
  let g : V → C := fun v => (e v).1
  refine ⟨⟨g, fun c => ?_⟩⟩
  let ef : {v // g v = c} ≃ Fin (k c) :=
    (e.subtypeEquiv (fun v => Iff.rfl)).trans (Equiv.sigmaSubtype c)
  exact (Fintype.card_congr ef).trans (Fintype.card_fin (k c))

theorem prescribedFiberColorings_card_mul_factorials (k : C → ℕ)
    (hne : Nonempty (PrescribedFiberColorings (V := V) k)) :
    Fintype.card (PrescribedFiberColorings (V := V) k) *
      (∏ c, (k c).factorial) = (Fintype.card V).factorial := by
  obtain ⟨⟨f₀, hf₀⟩⟩ := hne
  let e : {g : V → C // ∀ c, Fintype.card {v // g v = c} = k c} ≃
      EqualFiberColorings f₀ :=
    Equiv.subtypeEquivRight (fun g => by simp only [hf₀])
  have h := equalFiberColorings_card_mul_factorials f₀
  rw [Fintype.card_congr e]
  simpa only [hf₀] using h

end Problem315.FiberLabelCounting

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FixedBlockCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Problem315.FixedBlock

variable {α β : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α] [Fintype β] [DecidableEq β]

include sectionDecidableEqα in
theorem partition_nonempty (sizes : Fin 3 → ℕ)
    (hsum : ∑ i, sizes i = Fintype.card α) :
    Nonempty (Partition (α := α) sizes) := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have h := FiberLabelCounting.prescribedFiberColorings_nonempty (V := α) sizes hsum
  exact h.map (fun c => (partitionEquivColorings (α := α) sizes).symm c)

theorem partition_card_mul_factorials (sizes : Fin 3 → ℕ)
    (hne : Nonempty (Partition (α := α) sizes)) :
    Fintype.card (Partition (α := α) sizes) * (∏ i, (sizes i).factorial) =
      (Fintype.card α).factorial := by
  rw [Fintype.card_congr (partitionEquivColorings sizes)]
  have h := FiberLabelCounting.prescribedFiberColorings_card_mul_factorials (V := α) sizes
    (hne.map (fun c => partitionEquivColorings (α := α) sizes c))
  simpa only [← Nat.card_eq_fintype_card] using h

theorem partition_card_real (sizes : Fin 3 → ℕ)
    (hne : Nonempty (Partition (α := α) sizes)) :
    (Fintype.card (Partition (α := α) sizes) : ℝ) =
      (Fintype.card α).factorial / ∏ i, ((sizes i).factorial : ℝ) := by
  have hp : (∏ i, ((sizes i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero (sizes i))
  apply (eq_div_iff hp).mpr
  exact_mod_cast partition_card_mul_factorials sizes hne

theorem partition_pair_card_real (sizesU sizesW : Fin 3 → ℕ)
    (hU : Nonempty (Partition (α := α) sizesU))
    (hW : Nonempty (Partition (α := β) sizesW)) :
    (Fintype.card (Partition (α := α) sizesU × Partition (α := β) sizesW) : ℝ) =
      ((Fintype.card α).factorial * (Fintype.card β).factorial : ℝ) /
        ∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)) := by
  rw [Fintype.card_prod, Nat.cast_mul, partition_card_real sizesU hU,
    partition_card_real sizesW hW, div_mul_div_comm, Finset.prod_mul_distrib]

theorem partition_pair_card_real_of_sum (sizesU sizesW : Fin 3 → ℕ)
    (hU : ∑ i, sizesU i = Fintype.card α)
    (hW : ∑ i, sizesW i = Fintype.card β) :
    (Fintype.card (Partition (α := α) sizesU × Partition (α := β) sizesW) : ℝ) =
      ((Fintype.card α).factorial * (Fintype.card β).factorial : ℝ) /
        ∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)) :=
  partition_pair_card_real sizesU sizesW
    (partition_nonempty sizesU hU) (partition_nonempty sizesW hW)

theorem uniform_size_expectation {K : Type*} [Fintype K]
    (sizesU sizesW : K → Fin 3 → ℕ)
    (hU : ∀ k, ∑ i, sizesU k i = Fintype.card α)
    (hW : ∀ k, ∑ i, sizesW k i = Fintype.card β) (f : K → ℝ) :
    (∑ p : (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)),
      f p.1) /
      Fintype.card (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)) =
    (∑ k, pairSizeWeight (sizesU k) (sizesW k) * f k) /
      ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
  let C : ℝ := (Fintype.card α).factorial * (Fintype.card β).factorial
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (Fintype.card α))
      (by exact_mod_cast Nat.factorial_ne_zero (Fintype.card β))
  have hc (k : K) :
      (Fintype.card (Partition (α := α) (sizesU k) ×
        Partition (α := β) (sizesW k)) : ℝ) =
      C * pairSizeWeight (sizesU k) (sizesW k) := by
    simpa only [C, pairSizeWeight, div_eq_mul_inv] using
      partition_pair_card_real_of_sum (sizesU k) (sizesW k) (hU k) (hW k)
  have hn : (∑ p : (Σ k, Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)), f p.1) =
      C * ∑ k, pairSizeWeight (sizesU k) (sizesW k) * f k := by
    rw [Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc, mul_assoc]
  have hd : (Fintype.card (Σ k, Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) : ℝ) =
      C * ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
    rw [Fintype.card_sigma, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => hc k)
  rw [hn, hd, mul_div_mul_left _ _ hC]

theorem uniform_family_expectation {K : Type*} [Fintype K]
    (sizesU sizesW : K → Fin 3 → ℕ)
    (hU : ∀ k, ∑ i, sizesU k i = Fintype.card α)
    (hW : ∀ k, ∑ i, sizesW k i = Fintype.card β)
    (f : ∀ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k) → ℝ) :
    (∑ p : (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)),
      f p.1 p.2) /
      Fintype.card (Σ k, Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)) =
    (∑ k, pairSizeWeight (sizesU k) (sizesW k) *
      ((∑ p, f k p) /
        Fintype.card (Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k)))) /
      ∑ k, pairSizeWeight (sizesU k) (sizesW k) := by
  rw [← uniform_size_expectation sizesU sizesW hU hW]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨u⟩ := partition_nonempty (sizesU k) (hU k)
  obtain ⟨w⟩ := partition_nonempty (sizesW k) (hW k)
  have : Nonempty (Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) := ⟨(u, w)⟩
  have hc : (Fintype.card (Partition (α := α) (sizesU k) ×
      Partition (α := β) (sizesW k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (∑ p, f k p) =
    ∑ _p : Partition (α := α) (sizesU k) × Partition (α := β) (sizesW k),
      (∑ p, f k p) / Fintype.card (Partition (α := α) (sizesU k) ×
        Partition (α := β) (sizesW k))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Problem315.FixedBlock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CountCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

theorem weighted_covariance_identity {ι : Type*} (s : Finset ι)
    (w a b : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i - a j) * (b i - b j)) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) -
        (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i)) := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (w i * a i * b i * w j - w i * a i * (w j * b j) -
          w i * b i * (w j * a j) + w i * (w j * a j * b j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem weighted_chebyshev {ι : Type*} (s : Finset ι)
    (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hab : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ (a i - a j) * (b i - b j)) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) := by
  have hnonneg : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      w i * w j * (a i - a j) * (b i - b j) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    simpa only [mul_assoc] using
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hab i hi j hj)
  rw [weighted_covariance_identity] at hnonneg
  linarith

theorem weighted_chebyshev_of_monotone {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : MonotoneOn a s) (hb : MonotoneOn b s) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) := by
  apply weighted_chebyshev s w a b hw
  intro i hi j hj
  rcases le_total i j with hij | hji
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (ha hi hj hij))
      (sub_nonpos.mpr (hb hi hj hij))
  · exact mul_nonneg (sub_nonneg.mpr (ha hj hi hji))
      (sub_nonneg.mpr (hb hj hi hji))

theorem monotone_reweighting {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i)
    (hA : 0 < ∑ i ∈ s, w i * a i)
    (ha : MonotoneOn a s) (hb : MonotoneOn b s) :
    (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i) ≤
      (∑ i ∈ s, w i * a i * b i) / (∑ i ∈ s, w i * a i) := by
  apply (div_le_div_iff₀ hW hA).mpr
  simpa only [mul_comm] using weighted_chebyshev_of_monotone s w a b hw ha hb

theorem countWeight_pos (α t : ℕ) : 0 < countWeight α t := by
  unfold countWeight
  positivity

theorem countWeight_succ (α t : ℕ) :
    countWeight α (t + 1) =
      countWeight α t / (((t : ℝ) + 1) * ((t : ℝ) + 1 + α)) := by
  unfold countWeight
  rw [show t + 1 + α = (t + α) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [div_div]
  congr 1
  ring

theorem adjacent_likelihood_monotone (α s : ℕ) :
    MonotoneOn
      (fun y : ℕ => 1 / (((s - y : ℕ) : ℝ) * ((s - y + α : ℕ) : ℝ)))
      (Finset.range s) := by
  intro y hy z hz hyz
  have hys : y < s := Finset.mem_range.mp hy
  have hzs : z < s := Finset.mem_range.mp hz
  have hsub : s - z ≤ s - y := Nat.sub_le_sub_left hyz s
  have hzpos : (0 : ℝ) < (s - z : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hzs
  have hsubR : ((s - z : ℕ) : ℝ) ≤ (s - y : ℕ) := by exact_mod_cast hsub
  apply one_div_le_one_div_of_le
  · have hzpos' : (0 : ℝ) < ((s - z + α : ℕ) : ℝ) := by
      have : 0 < s - z + α := by omega
      exact_mod_cast this
    exact mul_pos hzpos hzpos'
  · push_cast
    exact mul_le_mul hsubR (add_le_add hsubR le_rfl) (by positivity)
      (by positivity)

theorem mean_le_add_top_mass {ι : Type*} (s : Finset ι)
    (w b : ι → ℝ) (a B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < ∑ i ∈ s, w i)
    (ha : 0 ≤ a) (hB : ∀ i ∈ s, b i ≤ B) :
    (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i) ≤
      ((∑ i ∈ s, w i * b i) + a * B) / ((∑ i ∈ s, w i) + a) := by
  have hsum : (∑ i ∈ s, w i * b i) ≤ (∑ i ∈ s, w i) * B := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (hw i hi))
  apply (div_le_div_iff₀ hW (by linarith)).mpr
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hsum)]

theorem pairWeight_pos (α β s y : ℕ) : 0 < pairWeight α β s y := by
  exact mul_pos (countWeight_pos α y) (countWeight_pos β (s - y))

theorem pairWeight_succ (α β s y : ℕ) (hy : y ≤ s) :
    pairWeight α β (s + 1) y = pairWeight α β s y *
      (1 / (((s + 1 - y : ℕ) : ℝ) * ((s + 1 - y + β : ℕ) : ℝ))) := by
  unfold pairWeight
  have hsub : s + 1 - y = (s - y) + 1 := by omega
  rw [hsub, countWeight_succ]
  push_cast
  ring

theorem pairExpectation_le_succ (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Monotone b) : pairExpectation α β s b ≤ pairExpectation α β (s + 1) b := by
  let S := Finset.range (s + 1)
  let w := pairWeight α β s
  let a : ℕ → ℝ := fun y =>
    1 / (((s + 1 - y : ℕ) : ℝ) * ((s + 1 - y + β : ℕ) : ℝ))
  have hw : ∀ y ∈ S, 0 ≤ w y := fun y _ => le_of_lt (pairWeight_pos α β s y)
  have hW : 0 < ∑ y ∈ S, w y := by
    apply Finset.sum_pos
    · intro y hy
      exact pairWeight_pos α β s y
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hnew : ∀ y ∈ S, w y * a y = pairWeight α β (s + 1) y := by
    intro y hy
    symm
    exact pairWeight_succ α β s y (by have := Finset.mem_range.mp hy; omega)
  have hA : 0 < ∑ y ∈ S, w y * a y := by
    apply Finset.sum_pos
    · intro y hy
      rw [hnew y hy]
      exact pairWeight_pos α β (s + 1) y
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hfirst := monotone_reweighting S w a b hw hW hA
    (adjacent_likelihood_monotone β (s + 1)) (hb.monotoneOn _)
  have hnext := mean_le_add_top_mass S (fun y => w y * a y) b
    (pairWeight α β (s + 1) (s + 1)) (b (s + 1))
    (fun y hy => by rw [hnew y hy]; exact le_of_lt (pairWeight_pos α β (s + 1) y))
    hA (le_of_lt (pairWeight_pos α β (s + 1) (s + 1)))
    (fun y hy => hb (by have := Finset.mem_range.mp hy; omega))
  have hnum : (∑ y ∈ S, w y * a y * b y) =
      ∑ y ∈ S, pairWeight α β (s + 1) y * b y := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [hnew y hy]
  have hden : (∑ y ∈ S, w y * a y) =
      ∑ y ∈ S, pairWeight α β (s + 1) y := by
    exact Finset.sum_congr rfl hnew
  rw [hnum, hden] at hfirst hnext
  simpa only [pairExpectation, S, w, Finset.sum_range_succ] using hfirst.trans hnext

theorem pairExpectation_congr (α β s : ℕ) (b c : ℕ → ℝ)
    (h : ∀ y ≤ s, b y = c y) :
    pairExpectation α β s b = pairExpectation α β s c := by
  unfold pairExpectation
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  rw [h y (by have := Finset.mem_range.mp hy; omega)]

theorem sum_pairWeight_reflect (α β s : ℕ) (b : ℕ → ℝ) :
    (∑ y ∈ Finset.range (s + 1), pairWeight α β s y * b y) =
      ∑ y ∈ Finset.range (s + 1), pairWeight β α s y * b (s - y) := by
  calc
    _ = ∑ y ∈ Finset.range (s + 1), pairWeight α β s (s - y) * b (s - y) := by
      simpa using (Finset.sum_range_reflect
        (fun y => pairWeight α β s y * b y) (s + 1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
      have hsub : s - (s - y) = y := by omega
      simp only [pairWeight, hsub]
      ring

theorem pairExpectation_reflect (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s b = pairExpectation β α s (fun y => b (s - y)) := by
  unfold pairExpectation
  rw [sum_pairWeight_reflect]
  have hden := sum_pairWeight_reflect α β s (fun _ => (1 : ℝ))
  simp only [mul_one] at hden
  rw [hden]

theorem pairExpectation_neg (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s (fun y => -b y) = -pairExpectation α β s b := by
  simp only [pairExpectation, mul_neg, Finset.sum_neg_distrib, neg_div]

theorem pairExpectation_succ_le_of_antitone (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Antitone b) : pairExpectation α β (s + 1) b ≤ pairExpectation α β s b := by
  have h := pairExpectation_le_succ α β s (fun y => -b y)
    (fun _ _ hij => neg_le_neg (hb hij))
  rw [pairExpectation_neg, pairExpectation_neg] at h
  linarith

theorem pairExpectation_succ_le_shift (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Monotone b) :
    pairExpectation α β (s + 1) b ≤ pairExpectation α β s (fun y => b (y + 1)) := by
  let c : ℕ → ℝ := fun y => b (s + 1 - y)
  have hc : Antitone c := by
    intro y z hyz
    exact hb (Nat.sub_le_sub_left hyz (s + 1))
  rw [pairExpectation_reflect α β (s + 1) b]
  calc
    pairExpectation β α (s + 1) c ≤ pairExpectation β α s c :=
      pairExpectation_succ_le_of_antitone β α s c hc
    _ = pairExpectation α β s (fun y => c (s - y)) :=
      pairExpectation_reflect β α s c
    _ = pairExpectation α β s (fun y => b (y + 1)) := by
      apply pairExpectation_congr
      intro y hy
      dsimp [c]
      congr 1
      omega

end Problem315.CountCoupling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CountCovering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

theorem adjacent_transport_identity (p q f : ℕ → ℝ) (s : ℕ)
    (hpEnd : p (s + 1) = 0)
    (hmass : prefixMass p (s + 1) = prefixMass q (s + 2)) :
    (∑ i ∈ Finset.range (s + 2), q i * f i) -
        (∑ i ∈ Finset.range (s + 1), p i * f i) =
      ∑ i ∈ Finset.range (s + 1),
        (prefixMass p (i + 1) - prefixMass q (i + 1)) * (f (i + 1) - f i) := by
  have htotal : (∑ i ∈ Finset.range (s + 2), (q i - p i)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_succ (f := p)]
    change prefixMass q (s + 2) - (prefixMass p (s + 1) + p (s + 1)) = 0
    rw [hpEnd, add_zero, hmass, sub_self]
  have hab := Finset.sum_range_by_parts f (fun i => q i - p i) (s + 2)
  simp only [smul_eq_mul, htotal, mul_zero, zero_sub,
    show s + 2 - 1 = s + 1 by omega] at hab
  calc
    _ = ∑ i ∈ Finset.range (s + 2), f i * (q i - p i) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [Finset.sum_range_succ (f := fun i => f i * p i)]
      simp only [hpEnd, mul_zero, add_zero]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ = -(∑ i ∈ Finset.range (s + 1),
        (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), (q j - p j)) := hab
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [prefixMass, Finset.sum_sub_distrib]
      ring

theorem adjacent_two_coordinate_expectation_bound
    (p q b c : ℕ → ℝ) (s : ℕ) (M : ℝ)
    (hpEnd : p (s + 1) = 0)
    (hpMass : prefixMass p (s + 1) = 1)
    (hqMass : prefixMass q (s + 2) = 1)
    (hinterlace : ∀ i ≤ s,
      0 ≤ prefixMass p (i + 1) - prefixMass q (i + 1) ∧
      prefixMass p (i + 1) - prefixMass q (i + 1) ≤ p i)
    (hb : ∀ i ≤ s, |b (i + 1) - b i| ≤ M)
    (hc : ∀ i ≤ s, |c (i + 1) - c i| ≤ M) :
    |(∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
      (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i)))| ≤ M := by
  let δ : ℕ → ℝ := fun i => prefixMass p (i + 1) - prefixMass q (i + 1)
  have hid := adjacent_transport_identity p q (fun i => b i + c (s + 1 - i)) s
    hpEnd (hpMass.trans hqMass.symm)
  have hexpand :
      (∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
        (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i))) =
      ∑ i ∈ Finset.range (s + 1),
        ((p i - δ i) * (c (s - i + 1) - c (s - i)) +
          δ i * (b (i + 1) - b i)) := by
    calc
      _ = ((∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
          (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s + 1 - i)))) +
          ((∑ i ∈ Finset.range (s + 1), p i * (b i + c (s + 1 - i))) -
          (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i)))) := by ring
      _ = _ := by
        rw [hid, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
        have hsub : s + 1 - i = s - i + 1 := by omega
        have hsub' : s + 1 - (i + 1) = s - i := by omega
        simp only [hsub, hsub', δ]
        ring
  rw [hexpand]
  calc
    _ ≤ ∑ i ∈ Finset.range (s + 1),
        |(p i - δ i) * (c (s - i + 1) - c (s - i)) +
          δ i * (b (i + 1) - b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (s + 1), p i * M := by
      apply Finset.sum_le_sum
      intro i hi
      have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
      have hd0 : 0 ≤ δ i := (hinterlace i his).1
      have hdp : δ i ≤ p i := (hinterlace i his).2
      calc
        _ ≤ |(p i - δ i) * (c (s - i + 1) - c (s - i))| +
            |δ i * (b (i + 1) - b i)| := abs_add_le _ _
        _ = (p i - δ i) * |c (s - i + 1) - c (s - i)| +
            δ i * |b (i + 1) - b i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hdp), abs_of_nonneg hd0]
        _ ≤ (p i - δ i) * M + δ i * M := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hc (s - i) (Nat.sub_le _ _)) (sub_nonneg.mpr hdp))
            (mul_le_mul_of_nonneg_left (hb i his) hd0)
        _ = p i * M := by ring
    _ = M := by rw [← Finset.sum_mul]; change prefixMass p (s + 1) * M = M; rw [hpMass, one_mul]

theorem pairWeight_mass_pos (α β s : ℕ) :
    0 < ∑ y ∈ Finset.range (s + 1), pairWeight α β s y := by
  apply Finset.sum_pos
  · intro y hy
    exact pairWeight_pos α β s y
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

theorem coveredPairProbability_mass (α β s : ℕ) :
    prefixMass (coveredPairProbability α β s) (s + 1) = 1 := by
  unfold prefixMass
  calc
    _ = ∑ y ∈ Finset.range (s + 1), pairWeight α β s y /
        (∑ z ∈ Finset.range (s + 1), pairWeight α β s z) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
      simp only [coveredPairProbability, ite_eq_left hys]
    _ = 1 := by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (pairWeight_mass_pos α β s))

theorem pairExpectation_eq_probability_sum (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s b =
      ∑ y ∈ Finset.range (s + 1), coveredPairProbability α β s y * b y := by
  unfold pairExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
  simp only [coveredPairProbability, ite_eq_left hys]
  ring

theorem probability_prefix_eq_expectation (α β s k : ℕ) (hk : k ≤ s + 1) :
    prefixMass (coveredPairProbability α β s) k =
      pairExpectation α β s (fun y => if y < k then 1 else 0) := by
  rw [pairExpectation_eq_probability_sum]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hset : (Finset.range (s + 1)).filter (fun y => y < k) = Finset.range k := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset]
  rfl

theorem covered_pairExpectation_shift_le_succ_of_antitone (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Antitone b) :
    pairExpectation α β s (fun y => b (y + 1)) ≤ pairExpectation α β (s + 1) b := by
  have h := pairExpectation_succ_le_shift α β s (fun y => -b y)
    (fun _ _ hij => neg_le_neg (hb hij))
  rw [pairExpectation_neg, pairExpectation_neg] at h
  linarith

theorem coveredPairProbability_interlace (α β s i : ℕ) (hi : i ≤ s) :
    0 ≤ prefixMass (coveredPairProbability α β s) (i + 1) -
      prefixMass (coveredPairProbability α β (s + 1)) (i + 1) ∧
    prefixMass (coveredPairProbability α β s) (i + 1) -
      prefixMass (coveredPairProbability α β (s + 1)) (i + 1) ≤
        coveredPairProbability α β s i := by
  have hantitone (k : ℕ) : Antitone (fun y : ℕ => if y < k then (1 : ℝ) else 0) := by
    intro y z hyz
    dsimp only
    split_ifs <;> norm_num ; omega
  have hfirst := pairExpectation_succ_le_of_antitone α β s
    (fun y => if y < i + 1 then (1 : ℝ) else 0) (hantitone (i + 1))
  rw [← probability_prefix_eq_expectation α β (s + 1) (i + 1) (by omega),
    ← probability_prefix_eq_expectation α β s (i + 1) (by omega)] at hfirst
  refine ⟨sub_nonneg.mpr hfirst, ?_⟩
  have hsecond := covered_pairExpectation_shift_le_succ_of_antitone α β s
    (fun y => if y < i + 1 then (1 : ℝ) else 0) (hantitone (i + 1))
  simp only [Nat.add_lt_add_iff_right] at hsecond
  rw [← probability_prefix_eq_expectation α β s i (by omega),
    ← probability_prefix_eq_expectation α β (s + 1) (i + 1) (by omega)] at hsecond
  have hprefix : prefixMass (coveredPairProbability α β s) (i + 1) =
      prefixMass (coveredPairProbability α β s) i + coveredPairProbability α β s i := by
    exact Finset.sum_range_succ _ _
  linarith

theorem pairExpectation_adjacent_sum_bound (α β s : ℕ) (b c : ℕ → ℝ) (M : ℝ)
    (hb : ∀ i ≤ s, |b (i + 1) - b i| ≤ M)
    (hc : ∀ i ≤ s, |c (i + 1) - c i| ≤ M) :
    |pairExpectation α β (s + 1) (fun i => b i + c (s + 1 - i)) -
      pairExpectation α β s (fun i => b i + c (s - i))| ≤ M := by
  rw [pairExpectation_eq_probability_sum, pairExpectation_eq_probability_sum]
  exact adjacent_two_coordinate_expectation_bound
    (coveredPairProbability α β s) (coveredPairProbability α β (s + 1)) b c s M
    (by simp [coveredPairProbability]) (coveredPairProbability_mass α β s)
    (coveredPairProbability_mass α β (s + 1)) (coveredPairProbability_interlace α β s) hb hc

end Problem315.CountCoupling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CountEigenvalue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.CountEigenvalue

theorem abs_eigenvalue_sub_one_le_one
    {lam M δ : ℝ} (hM : 0 < M) (hδ : |δ| = M)
    (hbound : |(lam - 1) * δ| ≤ M) : |lam - 1| ≤ 1 := by
  rw [abs_mul, hδ] at hbound
  nlinarith

theorem eigenvalue_le_two
    {lam M δ : ℝ} (hM : 0 < M) (hδ : |δ| = M)
    (hbound : |(lam - 1) * δ| ≤ M) : lam ≤ 2 := by
  have h := abs_eigenvalue_sub_one_le_one hM hδ hbound
  have := (abs_le.mp h).2
  linarith

theorem fin_eq_zero_value_of_adjacent_eq {m : ℕ} (b : Fin (m + 1) → ℝ)
    (h : ∀ t : Fin m, b t.succ = b t.castSucc) :
    ∀ t, b t = b 0 := by
  intro t
  induction t using Fin.induction with
  | zero => rfl
  | succ t ih => exact (h t).trans ih

theorem exists_nonzero_adjacent_difference {ι : Type*} {m : ℕ}
    (b : ι → Fin (m + 1) → ℝ)
    (hne : ∃ i s t, b i s ≠ b i t) :
    ∃ i, ∃ t : Fin m, b i t.succ - b i t.castSucc ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨i, s, t, hst⟩ := hne
  have hi : ∀ t : Fin m, b i t.succ = b i t.castSucc := by
    intro t
    exact sub_eq_zero.mp (h i t)
  exact hst ((fin_eq_zero_value_of_adjacent_eq (b i) hi s).trans
    (fin_eq_zero_value_of_adjacent_eq (b i) hi t).symm)

theorem exists_positive_max_abs {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hne : ∃ i, x i ≠ 0) :
    ∃ i, 0 < |x i| ∧ ∀ j, |x j| ≤ |x i| := by
  classical
  obtain ⟨j, hj⟩ := hne
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun k => |x k|) ⟨j, Finset.mem_univ j⟩
  refine ⟨i, lt_of_lt_of_le (abs_pos.mpr hj) (hi j (Finset.mem_univ j)), ?_⟩
  intro k
  exact hi k (Finset.mem_univ k)

theorem eigenvalue_le_two_of_adjacent_coupling
    {ι : Type*} [Fintype ι] {m : ℕ}
    (b : ι → Fin (m + 1) → ℝ) (lam : ℝ)
    (hne : ∃ i s t, b i s ≠ b i t)
    (hcoupling : ∀ i (t : Fin m),
      (∀ j (s : Fin m),
        |b j s.succ - b j s.castSucc| ≤ |b i t.succ - b i t.castSucc|) →
      |(lam - 1) * (b i t.succ - b i t.castSucc)| ≤
        |b i t.succ - b i t.castSucc|) : lam ≤ 2 := by
  obtain ⟨i, t, hit⟩ := exists_nonzero_adjacent_difference b hne
  let x : ι × Fin m → ℝ := fun p => b p.1 p.2.succ - b p.1 p.2.castSucc
  obtain ⟨⟨j, s⟩, hpos, hmax⟩ := exists_positive_max_abs x ⟨(i, t), hit⟩
  exact eigenvalue_le_two hpos rfl (hcoupling j s (fun k u => hmax (k, u)))

theorem exists_nonconstant_of_centered
    {ι : Type*} {m : ℕ} (b p : ι → Fin (m + 1) → ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ i, ∑ t, p i t * b i t = 0)
    (hne : ∃ i t, b i t ≠ 0) :
    ∃ i s t, b i s ≠ b i t := by
  classical
  by_contra h
  push Not at h
  obtain ⟨i, t, hit⟩ := hne
  have hi : (∑ u, p i u * b i u) = b i t := by
    calc
      _ = ∑ u, p i u * b i t := Finset.sum_congr rfl (fun u _ => by rw [h i u t])
      _ = (∑ u, p i u) * b i t := (Finset.sum_mul _ _ _).symm
      _ = b i t := by rw [hmass, one_mul]
  exact hit (hi.symm.trans (hcenter i))

end Problem315.CountEigenvalue

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CountEigenEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CountEigenvalue

theorem count_eigenvalue_le_two
    {ι : Type*} [Fintype ι] (m : ℕ)
    (α : ι → ℕ) (left right : ι → ι) (b : ι → ℕ → ℝ) (lam : ℝ)
    (hne : ∃ i, ∃ s t : Fin (m + 1), b i s.val ≠ b i t.val)
    (heig : ∀ i t, t ≤ m →
      (lam - 1) * b i t =
        CountCoupling.pairExpectation (α (left i)) (α (right i)) (m - t)
          (fun y => b (left i) y + b (right i) (m - t - y))) : lam ≤ 2 := by
  apply eigenvalue_le_two_of_adjacent_coupling
    (fun i (t : Fin (m + 1)) => b i t.val) lam hne
  intro i t hmax
  let s := m - (t.val + 1)
  have htotal : s + 1 = m - t.val := by dsimp [s]; omega
  have hleft : ∀ u ≤ s,
      |b (left i) (u + 1) - b (left i) u| ≤
        |b i (t.val + 1) - b i t.val| := by
    intro u hu
    have hum : u < m := by dsimp [s] at hu; have := t.isLt; omega
    exact hmax (left i) ⟨u, hum⟩
  have hright : ∀ u ≤ s,
      |b (right i) (u + 1) - b (right i) u| ≤
        |b i (t.val + 1) - b i t.val| := by
    intro u hu
    have hum : u < m := by dsimp [s] at hu; have := t.isLt; omega
    exact hmax (right i) ⟨u, hum⟩
  have hcover := CountCoupling.pairExpectation_adjacent_sum_bound
    (α (left i)) (α (right i)) s (b (left i)) (b (right i))
    |b i (t.val + 1) - b i t.val| hleft hright
  rw [htotal] at hcover
  change |(lam - 1) * (b i (t.val + 1) - b i t.val)| ≤
    |b i (t.val + 1) - b i t.val|
  rw [mul_sub, heig i (t.val + 1) (by have := t.isLt; omega),
    heig i t.val (by have := t.isLt; omega)]
  simpa only [s, abs_sub_comm] using hcover

theorem count_eigenvalue_le_two_of_centered
    {ι : Type*} [Fintype ι] (m : ℕ)
    (α : ι → ℕ) (left right : ι → ι) (b : ι → ℕ → ℝ)
    (p : ι → Fin (m + 1) → ℝ) (lam : ℝ)
    (hmass : ∀ i, ∑ t, p i t = 1)
    (hcenter : ∀ i, ∑ t, p i t * b i t.val = 0)
    (hne : ∃ i, ∃ t : Fin (m + 1), b i t.val ≠ 0)
    (heig : ∀ i t, t ≤ m →
      (lam - 1) * b i t =
        CountCoupling.pairExpectation (α (left i)) (α (right i)) (m - t)
          (fun y => b (left i) y + b (right i) (m - t - y))) : lam ≤ 2 := by
  exact count_eigenvalue_le_two m α left right b lam
    (exists_nonconstant_of_centered (fun i (t : Fin (m + 1)) => b i t.val)
      p hmass hcenter hne) heig

end Problem315.CountEigenvalue

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

theorem weight_pos (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : 0 < weight a x := by
  exact Finset.prod_pos (fun i _ => CountCoupling.countWeight_pos _ _)

theorem weight_fiberEquiv (a : Fin 3 → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    weight a (fiberEquiv m σ t ht y).val =
      CountCoupling.countWeight (a (σ 0)) t *
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val := by
  unfold weight
  rw [← Equiv.prod_comp σ]
  simp [Fin.prod_univ_three, CountCoupling.pairWeight, mul_assoc]

theorem conditionalAverage_reindex (a : Fin 3 → ℕ) {m : ℕ}
    (f : Triple m → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    conditionalAverage a f σ t =
      (∑ y : Fin (m - t + 1),
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val *
          f (fiberEquiv m σ t ht y).val) /
      (∑ y : Fin (m - t + 1),
        CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y.val) := by
  unfold conditionalAverage
  rw [← Equiv.sum_comp (fiberEquiv m σ t ht) (fun x => weight a x.val * f x.val),
    ← Equiv.sum_comp (fiberEquiv m σ t ht) (fun x => weight a x.val)]
  simp_rw [weight_fiberEquiv, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt (CountCoupling.countWeight_pos _ _))

theorem rowSum_fiberEquiv (b : Fin 3 → ℕ → ℝ) (m : ℕ)
    (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    rowSum b (fiberEquiv m σ t ht y).val =
      b (σ 0) t + (b (σ 1) y.val + b (σ 2) (m - t - y.val)) := by
  unfold rowSum
  rw [← Equiv.sum_comp σ]
  simp [Fin.sum_univ_three, add_assoc]

theorem conditionalAverage_rowSum (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → ℕ → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    conditionalAverage a (rowSum b : Triple m → ℝ) σ t =
      b (σ 0) t + CountCoupling.pairExpectation (a (σ 1)) (a (σ 2)) (m - t)
        (fun y => b (σ 1) y + b (σ 2) (m - t - y)) := by
  rw [conditionalAverage_reindex a (rowSum b) σ t ht]
  simp_rw [rowSum_fiberEquiv]
  rw [Fin.sum_univ_eq_sum_range
    (fun y => CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y *
      (b (σ 0) t + (b (σ 1) y + b (σ 2) (m - t - y)))) (m - t + 1),
    Fin.sum_univ_eq_sum_range]
  unfold CountCoupling.pairExpectation
  have hpos : 0 < ∑ y ∈ Finset.range (m - t + 1),
      CountCoupling.pairWeight (a (σ 1)) (a (σ 2)) (m - t) y := by
    apply Finset.sum_pos
    · intro y hy
      exact CountCoupling.pairWeight_pos _ _ _ _
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  field_simp [ne_of_gt hpos]

theorem fiber_nonempty (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    Nonempty (Fiber m σ t) :=
  ⟨fiberEquiv m σ t ht ⟨0, by omega⟩⟩

theorem totalWeight_pos (a : Fin 3 → ℕ) (m : ℕ) : 0 < totalWeight a m := by
  obtain ⟨x⟩ := fiber_nonempty m (Equiv.refl _) 0 (Nat.zero_le _)
  have : Nonempty (Triple m) := ⟨x.val⟩
  exact Finset.sum_pos (fun x _ => weight_pos a x) Finset.univ_nonempty

theorem probability_pos (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) :
    0 < probability a x := div_pos (weight_pos a x) (totalWeight_pos a m)

theorem probability_sum (a : Fin 3 → ℕ) (m : ℕ) :
    ∑ x : Triple m, probability a x = 1 := by
  simp only [probability, ← Finset.sum_div]
  exact div_self (ne_of_gt (totalWeight_pos a m))

theorem sum_fiber_eq_indicator (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ)
    (f : Triple m → ℝ) :
    (∑ x : Fiber m σ t, f x.val) =
      ∑ x : Triple m, if (x.val (σ 0)).val = t then f x else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun x => by simp) f).symm

theorem normalized_conditionalAverage (a : Fin 3 → ℕ) {m : ℕ}
    (f : Triple m → ℝ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) :
    ((∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x * f x else 0) /
      (∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x else 0)) =
      conditionalAverage a f σ t := by
  rw [← sum_fiber_eq_indicator, ← sum_fiber_eq_indicator]
  unfold probability conditionalAverage
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div]
  exact div_div_div_cancel_right₀ (ne_of_gt (totalWeight_pos a m)) _ _

theorem marginal_pos (a : Fin 3 → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) :
    0 < ∑ x : Triple m, if (x.val (σ 0)).val = t then probability a x else 0 := by
  rw [← sum_fiber_eq_indicator]
  have := fiber_nonempty m σ t ht
  exact Finset.sum_pos (fun x _ => probability_pos a x.val) Finset.univ_nonempty

end Problem315.TripleCountLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCountEigenvalue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

theorem marginal_sum (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) :
    ∑ t : Fin (m + 1), marginal a m i t = 1 := by
  classical
  unfold marginal
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact probability_sum a m

theorem marginal_positive (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3)
    (t : Fin (m + 1)) : 0 < marginal a m i t := by
  have h := marginal_pos a m (Equiv.swap 0 i) t.val (by have := t.isLt; omega)
  simpa only [marginal, Equiv.swap_apply_left, Fin.val_eq_val] using h

theorem conditional_eigenvalue_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → ℕ → ℝ) (lam : ℝ)
    (hcenter : ∀ i, ∑ t : Fin (m + 1), marginal a m i t * b i t.val = 0)
    (hne : ∃ i, ∃ t : Fin (m + 1), b i t.val ≠ 0)
    (heig : ∀ i t, t ≤ m → lam * b i t =
      conditionalAverage a (rowSum b : Triple m → ℝ) (Equiv.swap 0 i) t) :
    lam ≤ 2 := by
  apply CountEigenvalue.count_eigenvalue_le_two_of_centered m a
    (fun i => Equiv.swap 0 i 1) (fun i => Equiv.swap 0 i 2) b
    (marginal a m) lam (marginal_sum a m) hcenter hne
  intro i t ht
  have h := heig i t ht
  rw [conditionalAverage_rowSum a m b (Equiv.swap 0 i) t ht,
    Equiv.swap_apply_left] at h
  nlinarith

end Problem315.TripleCountLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.WeightedConditionalVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.WeightedConditional

variable {Ω ι β : Type*} [Fintype Ω] [sectionFintypeι : Fintype ι] [sectionFintypeβ : Fintype β]
  [sectionDecidableEqβ : DecidableEq β]

include sectionFintypeι in
theorem sum_mul_conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (g : β → ℝ) (f : Ω → ℝ) :
    (∑ t, g t * conditionalSum w key i t f) =
      ∑ x, w x * g (key i x) * f x := by
  have retainedsectionFintypeι := sectionFintypeι
  classical
  unfold conditionalSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem sum_conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (f : Ω → ℝ) :
    (∑ t, conditionalSum w key i t f) = ∑ x, w x * f x := by
  simpa using sum_mul_conditionalSum w key i (fun _ => 1) f

theorem inner_gram (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) (z z' : Space ι β) :
    inner ℝ z (gram w p key z') =
      ∑ x, w x * rowSum p key z x * rowSum p key z' x := by
  classical
  rw [real_inner_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type,
    gram_apply]
  have hrew (i : ι) :
      (∑ t, z (i,t) * (conditionalSum w key i t (rowSum p key z') /
        Real.sqrt (p i t))) =
      ∑ x, w x * decode p z i (key i x) * rowSum p key z' x := by
    rw [← sum_mul_conditionalSum w key i (decode p z i) (rowSum p key z')]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [decode]
    ring
  simp_rw [hrew]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  unfold rowSum
  rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem gram_symmetric (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) : (gram w p key).IsSymmetric := by
  intro z z'
  rw [real_inner_comm, inner_gram, inner_gram]
  apply Finset.sum_congr rfl
  intro x hx
  ring

include sectionDecidableEqβ in
theorem marginal_mul_decode (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (z : Space ι β) (i : ι) (t : β) :
    p i t * decode p z i t = Real.sqrt (p i t) * z (i,t) := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
  unfold decode
  calc
    p i t * (z (i,t) / Real.sqrt (p i t)) =
        (Real.sqrt (p i t) * Real.sqrt (p i t)) *
          (z (i,t) / Real.sqrt (p i t)) := by
      rw [Real.mul_self_sqrt (hp i t).le]
    _ = Real.sqrt (p i t) * z (i,t) := by field_simp

theorem weighted_rowSum (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (z : Space ι β) :
    (∑ x, w x * rowSum p key z x) =
      ∑ i, ∑ t, Real.sqrt (p i t) * z (i,t) := by
  classical
  unfold rowSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have h := sum_mul_conditionalSum w key i (decode p z i) (fun _ => 1)
  simp only [hmarginal, mul_one] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mul_comm, marginal_mul_decode p hp]

theorem gram_preserves_centered (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (z : Space ι β) (hz : z ∈ centered p) : gram w p key z ∈ centered p := by
  classical
  intro i
  calc
    (∑ t, Real.sqrt (p i t) * gram w p key z (i,t)) =
        ∑ t, conditionalSum w key i t (rowSum p key z) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [gram_apply]
      have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
      field_simp
    _ = ∑ x, w x * rowSum p key z x := sum_conditionalSum w key i _
    _ = ∑ j, ∑ t, Real.sqrt (p j t) * z (j,t) :=
      weighted_rowSum w p hp key hmarginal z
    _ = 0 := by
      have hz' := (mem_centered p z).mp hz
      simp only [hz', Finset.sum_const_zero]

theorem conditional_eigen_equation (w : Ω → ℝ) (p : ι → β → ℝ)
    (hp : ∀ i t, 0 < p i t) (key : ι → Ω → β)
    (z : Space ι β) (lam : ℝ) (heig : gram w p key z = lam • z)
    (i : ι) (t : β) :
    lam * decode p z i t =
      conditionalSum w key i t (rowSum p key z) / p i t := by
  have hs : Real.sqrt (p i t) ≠ 0 := (Real.sqrt_pos.2 (hp i t)).ne'
  have he := congrArg (fun q : Space ι β => q (i,t)) heig
  change conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t) =
    lam * z (i,t) at he
  calc
    lam * decode p z i t = (lam * z (i,t)) / Real.sqrt (p i t) := by
      unfold decode
      ring
    _ = (conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t)) /
        Real.sqrt (p i t) := by rw [he]
    _ = conditionalSum w key i t (rowSum p key z) / p i t := by
      rw [div_div, Real.mul_self_sqrt (hp i t).le]

include sectionDecidableEqβ in
theorem encode_mem_centered (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) (hb : ∀ i, ∑ t, p i t * b i t = 0) :
    encode p b ∈ centered p := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  intro i
  convert hb i using 1
  apply Finset.sum_congr rfl
  intro t ht
  change Real.sqrt (p i t) * (Real.sqrt (p i t) * b i t) = p i t * b i t
  rw [← mul_assoc, Real.mul_self_sqrt (hp i t).le]

include sectionDecidableEqβ in
theorem norm_encode_sq (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) :
    ‖encode p b‖ ^ 2 = ∑ i, ∑ t, p i t * (b i t) ^ 2 := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro t ht
  change (Real.sqrt (p i t) * b i t) ^ 2 = p i t * (b i t) ^ 2
  rw [mul_pow, Real.sq_sqrt (hp i t).le]

theorem centered_variance_le_of_eigenvalue_bound
    (w : Ω → ℝ) (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (key : ι → Ω → β)
    (hmarginal : ∀ i t, conditionalSum w key i t (fun _ => 1) = p i t)
    (C : ℝ)
    (heigen : ∀ (lam : ℝ) (b : ι → β → ℝ),
      (∀ i, ∑ t, p i t * b i t = 0) →
      (∃ i t, b i t ≠ 0) →
      (∀ i t, lam * b i t =
        conditionalSum w key i t (fun x => ∑ j, b j (key j x)) / p i t) →
      lam ≤ C)
    (b : ι → β → ℝ) (hb : ∀ i, ∑ t, p i t * b i t = 0) :
    (∑ x, w x * (∑ i, b i (key i x)) ^ 2) ≤
      C * ∑ i, ∑ t, p i t * (b i t) ^ 2 := by
  classical
  let U := centered p
  let T := (gram w p key).restrict (gram_preserves_centered w p hp key hmarginal)
  have hT : T.IsSymmetric :=
    (gram_symmetric w p key).restrict_invariant
      (gram_preserves_centered w p hp key hmarginal)
  let basis := hT.eigenvectorBasis (rfl : Module.finrank ℝ U = Module.finrank ℝ U)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ U = Module.finrank ℝ U)
  have hbe (k : Fin (Module.finrank ℝ U)) : T (basis k) = ev k • basis k :=
    hT.apply_eigenvectorBasis rfl k
  have hev (k : Fin (Module.finrank ℝ U)) : ev k ≤ C := by
    apply heigen (ev k) (decode p (basis k : Space ι β))
    · intro i
      simp_rw [marginal_mul_decode p hp]
      exact (basis k).property i
    · by_contra hz
      push Not at hz
      have hz0 : (basis k : Space ι β) = 0 := by
        ext it
        have h := hz it.1 it.2
        unfold decode at h
        exact (div_eq_zero_iff).mp h |>.resolve_right (Real.sqrt_pos.2 (hp it.1 it.2)).ne'
      have hzero : basis k = 0 := Subtype.ext hz0
      have hn := basis.orthonormal.1 k
      rw [hzero, norm_zero] at hn
      norm_num at hn
    · intro i t
      exact conditional_eigen_equation w p hp key _ (ev k)
        (congrArg Subtype.val (hbe k)) i t
  have hquad (z : U) : inner ℝ z (T z) ≤ C * ‖z‖ ^ 2 := by
    rw [← basis.sum_inner_mul_inner z (T z), ← basis.sum_sq_inner_right z,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hcoord : inner ℝ (basis k) (T z) = ev k * inner ℝ (basis k) z := by
      rw [← hT (basis k) z, hbe]
      exact real_inner_smul_left (basis k : U) z (ev k)
    rw [hcoord, real_inner_comm z (basis k)]
    have hk := hev k
    nlinarith [sq_nonneg (inner ℝ (basis k) z)]
  let z : U := ⟨encode p b, encode_mem_centered p hp b hb⟩
  have h := hquad z
  change inner ℝ (encode p b) (gram w p key (encode p b)) ≤ C * ‖encode p b‖ ^ 2 at h
  rw [inner_gram, norm_encode_sq p hp] at h
  simpa only [rowSum, decode_encode p hp, mul_assoc, ← pow_two] using h

end Problem315.WeightedConditional

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCountGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

theorem count_marginal_eq (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) (t : Fin (m + 1)) :
    WeightedConditional.conditionalSum (probability a : Triple m → ℝ) (countKey m)
      i t (fun _ => 1) = marginal a m i t := by
  simp [WeightedConditional.conditionalSum, countKey, marginal]

theorem conditionalSum_ratio (a : Fin 3 → ℕ) (m : ℕ) (f : Triple m → ℝ)
    (i : Fin 3) (t : Fin (m + 1)) :
    WeightedConditional.conditionalSum (probability a) (countKey m) i t f /
      marginal a m i t = conditionalAverage a f (Equiv.swap 0 i) t.val := by
  rw [← normalized_conditionalAverage]
  simp only [WeightedConditional.conditionalSum, countKey, marginal,
    Equiv.swap_apply_left, Fin.val_eq_val]
  rfl

theorem count_row_variance_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → Fin (m + 1) → ℝ)
    (hb : ∀ i, ∑ t : Fin (m + 1), marginal a m i t * b i t = 0) :
    (∑ x : Triple m, probability a x * (∑ i : Fin 3, b i (x.val i)) ^ 2) ≤
      2 * ∑ i : Fin 3, ∑ t : Fin (m + 1), marginal a m i t * (b i t) ^ 2 := by
  apply WeightedConditional.centered_variance_le_of_eigenvalue_bound
    (probability a : Triple m → ℝ) (marginal a m) (marginal_positive a m)
    (countKey m) (count_marginal_eq a m) 2 _ b hb
  intro lam c hc hne heig
  let cNat : Fin 3 → ℕ → ℝ := fun i t =>
    if h : t < m + 1 then c i ⟨t, h⟩ else 0
  have hcNat (i : Fin 3) (t : Fin (m + 1)) : cNat i t.val = c i t := by
    dsimp only [cNat]
    rw [dite_eq_left t.isLt]
  apply conditional_eigenvalue_le_two a m cNat lam
  · intro i
    simpa only [hcNat] using hc i
  · obtain ⟨i, t, ht⟩ := hne
    exact ⟨i, t, by simpa only [hcNat] using ht⟩
  · intro i t ht
    let t' : Fin (m + 1) := ⟨t, by omega⟩
    have h := heig i t'
    rw [conditionalSum_ratio] at h
    have hr : (fun x : Triple m => ∑ j : Fin 3, c j (countKey m j x)) =
        rowSum cNat := by
      funext x
      simp only [rowSum, countKey, hcNat]
    rw [hr] at h
    simpa only [← hcNat] using h

end Problem315.TripleCountLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.VariableBlockVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.VariableBlockVariance
open FixedBlockMarginal (average)
open TripleCountLaw (Triple)

variable (U W : Type*) [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

variable {U W}

theorem sum_sizes (o : Fin 3 → ℕ) {m : ℕ} (x : Triple m) :
    ∑ i, sizes o x i = m + ∑ i, o i := by
  simp only [sizes, Finset.sum_add_distrib, x.property]

theorem fiber_nonempty (m : ℕ) (u w : Fin 3 → ℕ)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W) (x : Triple m) :
    Nonempty (Fiber U W m u w x) := by
  obtain ⟨c⟩ := FixedBlock.partition_nonempty (α := U) (sizes u x)
    ((sum_sizes u x).trans hU)
  obtain ⟨d⟩ := FixedBlock.partition_nonempty (α := W) (sizes w x)
    ((sum_sizes w x).trans hW)
  exact ⟨(c, d)⟩

theorem pairSizeWeight_eq (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0) (x : Triple m) :
    FixedBlock.pairSizeWeight (sizes u x) (sizes w x) =
      TripleCountLaw.weight (fun i => u i + w i) x := by
  unfold FixedBlock.pairSizeWeight TripleCountLaw.weight
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rcases hsep i with hu | hw
  · simp [sizes, hu, CountCoupling.countWeight, one_div]
  · simp [sizes, hw, CountCoupling.countWeight, one_div, mul_comm]

theorem family_average (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (f : Family U W m u w → ℝ) :
    average f = ∑ x : Triple m, TripleCountLaw.probability (fun i => u i + w i) x *
      average (fun z : Fiber U W m u w x => f ⟨x, z⟩) := by
  have h := FixedBlock.uniform_family_expectation (α := U) (β := W)
    (sizes u : Triple m → Fin 3 → ℕ) (sizes w)
    (fun x => (sum_sizes u x).trans hU) (fun x => (sum_sizes w x).trans hW)
    (fun x z => f ⟨x, z⟩)
  change average f = _ at h
  simp_rw [pairSizeWeight_eq m u w hsep] at h
  rw [h]
  simp only [TripleCountLaw.probability, TripleCountLaw.totalWeight,
    div_mul_eq_mul_div, ← Finset.sum_div, average]

theorem average_rowFunction (m : ℕ) (u w : Fin 3 → ℕ)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3) (x : Triple m) :
    average (rowFunction m u w g i x) = rowMean m u w g i (x.val i) := by
  obtain ⟨z⟩ := fiber_nonempty m u w hU hW x
  exact FixedBlockMarginal.row_function_average_eq_subset_average i z.1 z.2 (g i)

theorem marginal_expectation (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3)
    (b : Fin (m + 1) → ℝ) :
    (∑ t, TripleCountLaw.marginal a m i t * b t) =
      ∑ x : Triple m, TripleCountLaw.probability a x * b (x.val i) := by
  classical
  unfold TripleCountLaw.marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem centered_row_average_sq (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ)
    (hcenter : ∀ i, average (fun z : Family U W m u w =>
      rowFunction m u w g i z.1 z.2) = 0) :
    average (fun z : Family U W m u w =>
      (∑ i, rowFunction m u w g i z.1 z.2) ^ 2) ≤
      2 * ∑ i, average (fun z : Family U W m u w =>
        (rowFunction m u w g i z.1 z.2) ^ 2) := by
  let (x : Triple m) : Nonempty (Fiber U W m u w x) :=
    fiber_nonempty m u w hU hW x
  have hb (i : Fin 3) : ∑ t, TripleCountLaw.marginal (fun j => u j + w j) m i t *
      rowMean m u w g i t = 0 := by
    rw [marginal_expectation]
    have hc := hcenter i
    rw [family_average m u w hsep hU hW] at hc
    simpa only [average_rowFunction m u w hU hW g i] using hc
  have hmean := TripleCountLaw.count_row_variance_le_two
    (fun i => u i + w i) m (rowMean m u w g) hb
  simp_rw [marginal_expectation] at hmean
  simp_rw [family_average m u w hsep hU hW]
  apply FiniteVariance.mixture_centered_row_bound (Fiber U W m u w)
    (TripleCountLaw.probability (fun i => u i + w i))
    (fun x => (TripleCountLaw.probability_pos _ x).le)
    (rowFunction m u w g)
  · intro x
    exact FixedBlockVariance.variance_sum_row_functions (sizes u x) (sizes w x) g
  · simpa only [average_rowFunction m u w hU hW] using hmean

theorem row_variance_bound (m : ℕ) (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (hU : m + ∑ i, u i = Fintype.card U)
    (hW : m + ∑ i, w i = Fintype.card W)
    (g : Fin 3 → Finset U → Finset W → ℝ) :
    FiniteVariance.variance (fun z : Family U W m u w =>
      ∑ i, rowFunction m u w g i z.1 z.2) ≤
      2 * ∑ i, FiniteVariance.variance (fun z : Family U W m u w =>
        rowFunction m u w g i z.1 z.2) := by
  obtain ⟨x⟩ := TripleCountLaw.fiber_nonempty m (Equiv.refl _) 0 (Nat.zero_le _)
  obtain ⟨z⟩ := fiber_nonempty m u w hU hW x.val
  let : Nonempty (Family U W m u w) := ⟨⟨x.val, z⟩⟩
  let c (i : Fin 3) := average (fun z : Family U W m u w =>
    rowFunction m u w g i z.1 z.2)
  let g' (i : Fin 3) (s : Finset U) (t : Finset W) := g i s t - c i
  have he (i : Fin 3) (z : Family U W m u w) :
      rowFunction m u w g' i z.1 z.2 = rowFunction m u w g i z.1 z.2 - c i := rfl
  have hc (i : Fin 3) : average (fun z : Family U W m u w =>
      rowFunction m u w g' i z.1 z.2) = 0 := by
    simp_rw [he]
    exact FiniteVariance.average_center _
  have h := centered_row_average_sq m u w hsep hU hW g' hc
  simp_rw [he, Finset.sum_sub_distrib] at h
  unfold FiniteVariance.variance
  rw [FiniteVariance.average_sum]
  exact h

end Problem315.VariableBlockVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.BalancedBlockVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.BalancedBlockVariance
open FixedBlockMarginal (average)
open VariableBlockVariance (Family sizes rowFunction)

variable (U W : Type*) [Fintype U] [sectionDecidableEqU : DecidableEq U] [Fintype W] [sectionDecidableEqW : DecidableEq W]

variable {U W}

theorem lower_sum_le {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) : (∑ i, w i) ≤ Fintype.card W := by
  rw [← sum_row_card c.val.2]
  exact Finset.sum_le_sum (fun i _ => lower_le hsep c i)

theorem totals {u w : Fin 3 → ℕ} (c : Balanced U W u w) :
    Fintype.card U + ∑ i, w i = Fintype.card W + ∑ i, u i := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => c.property i)
  simpa only [Finset.sum_add_distrib, sum_row_card] using h

theorem row_variance_bound (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    [Nonempty (Balanced U W u w)]
    (g : Fin 3 → Finset U → Finset W → ℝ) :
    FiniteVariance.variance (fun c : Balanced U W u w =>
      ∑ i, g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i)) ≤
      2 * ∑ i, FiniteVariance.variance (fun c : Balanced U W u w =>
        g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i)) := by
  obtain ⟨c⟩ := ‹Nonempty (Balanced U W u w)›
  have hw := lower_sum_le hsep c
  have ht := totals c
  let m := Fintype.card W - ∑ i, w i
  have hW : m + ∑ i, w i = Fintype.card W := Nat.sub_add_cancel hw
  have hU : m + ∑ i, u i = Fintype.card U := by omega
  let e := familyEquiv (U := U) (W := W) u w hsep
  have h := VariableBlockVariance.row_variance_bound m u w hsep hU hW g
  have he (f : Balanced U W u w → ℝ) :
      FiniteVariance.variance (fun z => f (e.symm z)) = FiniteVariance.variance f :=
    FiniteVariance.variance_equiv e.symm f
  rw [← he (fun c => ∑ i, g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i))]
  simp_rw [← he (fun c => g _ (FixedBlock.row c.val.1 _) (FixedBlock.row c.val.2 _))]
  exact h

end Problem315.BalancedBlockVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.BinaryColumnPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.BinaryColumnPartitions

variable (U W : Type*)

variable [Fintype U] [Fintype W]

theorem row_eq_iff (c d : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) :
    (matrixEquiv U W c).val i = (matrixEquiv U W d).val i ↔
      FixedBlock.row c.1 i = FixedBlock.row d.1 i ∧
      FixedBlock.row c.2 i = FixedBlock.row d.2 i := by
  classical
  have h1 : ∀ a b i : Fin 3,
      (if i = a then (1 : Fin 2) else 0) = (if i = b then 1 else 0) ↔
        (a = i ↔ b = i) := by decide
  have h2 : ∀ a b i : Fin 3,
      (if i = a then (0 : Fin 2) else 1) = (if i = b then 0 else 1) ↔
        (a = i ↔ b = i) := by decide
  constructor
  · intro h
    constructor
    · ext u
      have he := congrFun h (Sum.inl u)
      simpa only [FixedBlock.mem_row, matrixEquiv_inl, h1] using he
    · ext w
      have he := congrFun h (Sum.inr w)
      simpa only [FixedBlock.mem_row, matrixEquiv_inr, h2] using he
  · rintro ⟨hu, hw⟩
    funext j
    cases j with
    | inl u =>
      rw [matrixEquiv_inl, matrixEquiv_inl, h1]
      simpa only [FixedBlock.mem_row] using (Finset.ext_iff.mp hu u)
    | inr w =>
      rw [matrixEquiv_inr, matrixEquiv_inr, h2]
      simpa only [FixedBlock.mem_row] using (Finset.ext_iff.mp hw w)

end Problem315.BinaryColumnPartitions

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ForcedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.ForcedColumns

variable {C : Type*}

theorem row_eq_iff (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M N : MatrixSpace k) (i : Fin 3) :
    (restrict k M).val i = (restrict k N).val i ↔ M.val i = N.val i := by
  constructor
  · intro h
    funext c
    by_cases h1 : k c = 1
    · exact congrFun h (Sum.inl ⟨c, h1⟩)
    · by_cases h2 : k c = 2
      · exact congrFun h (Sum.inr ⟨c, h2⟩)
      · by_cases h3 : k c = 3
        · exact (column_three _ ((M.property c).trans h3) i).trans
            (column_three _ ((N.property c).trans h3) i).symm
        · have h0 : k c = 0 := by have := hk c; omega
          exact (column_zero _ ((M.property c).trans h0) i).trans
            (column_zero _ ((N.property c).trans h0) i).symm
  · intro h
    funext c
    cases c with
    | inl c => exact congrFun h c.val
    | inr c => exact congrFun h c.val

attribute [local instance] Classical.propDecidable
variable [Fintype C]

theorem coloring_row_eq_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) (M N : FullMargins k r) (i : Fin 3) :
    M.val i = N.val i ↔
      FixedBlock.row (coloringEquiv k r h M).val.1 i =
        FixedBlock.row (coloringEquiv k r h N).val.1 i ∧
      FixedBlock.row (coloringEquiv k r h M).val.2 i =
        FixedBlock.row (coloringEquiv k r h N).val.2 i := by
  let m : MatrixSpace k := ⟨M.val, M.property.2⟩
  let n : MatrixSpace k := ⟨N.val, N.property.2⟩
  have hm : BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      (coloringEquiv k r h M).val = restrict k m := by
    change BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      ((BinaryColumnPartitions.matrixEquiv (One k) (Two k)).symm (restrict k m)) = _
    exact Equiv.apply_symm_apply _ _
  have hn : BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      (coloringEquiv k r h N).val = restrict k n := by
    change BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      ((BinaryColumnPartitions.matrixEquiv (One k) (Two k)).symm (restrict k n)) = _
    exact Equiv.apply_symm_apply _ _
  have hb := BinaryColumnPartitions.row_eq_iff (One k) (Two k)
    (coloringEquiv k r h M).val (coloringEquiv k r h N).val i
  rw [hm, hn] at hb
  exact (row_eq_iff k (bounds_of_nonempty k r h).1 m n i).symm.trans hb

end Problem315.ForcedColumns

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MatrixRowVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.MatrixRowVariance

variable {C : Type*} [Fintype C]

theorem offset_separated (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) :
    positive k r i = 0 ∨ negative k r i = 0 := by
  unfold positive negative
  omega

theorem fullBalance_row_eq_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r))
    (M N : ForcedColumns.FullMargins k r) (i : Fin 3) :
    M.val i = N.val i ↔
      FixedBlock.row (fullBalanceEquiv k r h M).val.1 i =
        FixedBlock.row (fullBalanceEquiv k r h N).val.1 i ∧
      FixedBlock.row (fullBalanceEquiv k r h M).val.2 i =
        FixedBlock.row (fullBalanceEquiv k r h N).val.2 i := by
  exact ForcedColumns.coloring_row_eq_iff k r h M N i

theorem row_variance_bound (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r))
    (f : Fin 3 → ForcedColumns.FullMargins k r → ℝ)
    (hf : ∀ i M N, M.val i = N.val i → f i M = f i N) :
    FiniteVariance.variance (fun M => ∑ i, f i M) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let B := BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
    (positive k r) (negative k r)
  let e : ForcedColumns.FullMargins k r ≃ B := fullBalanceEquiv k r h
  let : Nonempty B := h.map e
  let key (i : Fin 3) (c : B) :=
    (FixedBlock.row c.val.1 i, FixedBlock.row c.val.2 i)
  have hfac (i : Fin 3) :
      Function.FactorsThrough (fun c : B => f i (e.symm c)) (key i) := by
    intro c d hcd
    apply hf i
    apply (fullBalance_row_eq_iff k r h (e.symm c) (e.symm d) i).mpr
    change FixedBlock.row (e (e.symm c)).val.1 i =
      FixedBlock.row (e (e.symm d)).val.1 i ∧
      FixedBlock.row (e (e.symm c)).val.2 i =
      FixedBlock.row (e (e.symm d)).val.2 i
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact ⟨congrArg Prod.fst hcd, congrArg Prod.snd hcd⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin 3 →
      (Finset (ForcedColumns.One k) × Finset (ForcedColumns.Two k)) → ℝ,
      ∀ i c, f i (e.symm c) = g i (key i c) := by
    have he (i : Fin 3) := (Function.factorsThrough_iff (fun c : B => f i (e.symm c))).mp
      (hfac i)
    choose g hg using he
    exact ⟨g, fun i c => congrFun (hg i) c⟩
  have hv := BalancedBlockVariance.row_variance_bound
    (positive k r) (negative k r) (offset_separated k r)
    (fun i s t => g i (s, t))
  have heq (F : ForcedColumns.FullMargins k r → ℝ) :
      FiniteVariance.variance (fun c : B => F (e.symm c)) = FiniteVariance.variance F :=
    FiniteVariance.variance_equiv e.symm F
  rw [← heq (fun M => ∑ i, f i M)]
  simp_rw [← heq (f _)]
  simp_rw [hg]
  exact hv

end Problem315.MatrixRowVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleMatrixEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding

variable (W : Type*) [Fintype W]

variable {W}

theorem extraColumn_eq_margin_sub_row {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A : TripleCell W e d c) (v : Fin 3) :
    extraColumn A.inside v = d v - rowOffset e - ∑ w, A.outside v w := by
  have hrow := A.rows v
  rw [degree_eq_extra_add_offset, A.edge_count] at hrow
  omega

theorem encode_row_eq_iff {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A B : TripleCell W e d c) (v : Fin 3) :
    (encodeCell A).matrix v = (encodeCell B).matrix v ↔ A.outside v = B.outside v := by
  constructor
  · intro h
    funext w
    exact congrFun h (some w)
  · intro h
    funext w
    cases w with
    | none =>
        change extraColumn A.inside v = extraColumn B.inside v
        rw [extraColumn_eq_margin_sub_row, extraColumn_eq_margin_sub_row, h]
    | some w => exact congrFun h w

end Problem315.TripleInternalEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TriplePairFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

theorem complement_edges_eq (G H : SimpleGraph (Fin 3)) (i : Fin 3)
    (he : internalEdgeCount G = internalEdgeCount H)
    (hd : graphDegree G i = graphDegree H i) :
    ∀ u v, u ≠ i → v ≠ i → (G.Adj u v ↔ H.Adj u v) := by
  unfold internalEdgeCount at he
  fin_cases i
  · change graphDegree G 0 = graphDegree H 0 at hd
    rw [degree_zero, degree_zero] at hd
    have h12 : G.Adj 1 2 ↔ H.Adj 1 2 := (edgeBit_eq_iff G H 1 2).mp (by omega)
    have h21 : G.Adj 2 1 ↔ H.Adj 2 1 :=
      (G.adj_comm 2 1).trans (h12.trans (H.adj_comm 1 2))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all
  · change graphDegree G 1 = graphDegree H 1 at hd
    rw [degree_one, degree_one] at hd
    have h02 : G.Adj 0 2 ↔ H.Adj 0 2 := (edgeBit_eq_iff G H 0 2).mp (by omega)
    have h20 : G.Adj 2 0 ↔ H.Adj 2 0 :=
      (G.adj_comm 2 0).trans (h02.trans (H.adj_comm 0 2))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all
  · change graphDegree G 2 = graphDegree H 2 at hd
    rw [degree_two, degree_two] at hd
    have h01 : G.Adj 0 1 ↔ H.Adj 0 1 := (edgeBit_eq_iff G H 0 1).mp (by omega)
    have h10 : G.Adj 1 0 ↔ H.Adj 1 0 :=
      (G.adj_comm 1 0).trans (h01.trans (H.adj_comm 0 1))
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp_all

variable {W : Type*} [Fintype W]

variable {O : SimpleGraph W} {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}

theorem adjacencyBit_eq_one {V : Type*} (G : SimpleGraph V) (u v : V) :
    adjacencyBit G u v = 1 ↔ G.Adj u v := by simp [adjacencyBit]

theorem samePairRestrictions_iff_row (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairRestrictions (complementaryPair i) G.val H.val ↔
      (graphToCell G).outside i = (graphToCell H).outside i := by
  classical
  constructor
  · intro h
    funext w
    have ha := h.1 (Sum.inl i) (by simp) (Sum.inr w) (by simp)
    simp only [graphToCell, adjacencyBit, ha]
  · intro hrow
    have hcross (w : W) : G.val.Adj (Sum.inl i) (Sum.inr w) ↔
        H.val.Adj (Sum.inl i) (Sum.inr w) := by
      have hb := congrFun hrow w
      exact (adjacencyBit_eq_one G.val _ _).symm.trans
        ((iff_of_eq (congrArg (fun x : ℕ => x = 1) hb)).trans
          (adjacencyBit_eq_one H.val _ _))
    have houtside (w z : W) : G.val.Adj (Sum.inr w) (Sum.inr z) ↔
        H.val.Adj (Sum.inr w) (Sum.inr z) := by
      have heq : outsideGraph G.val = outsideGraph H.val :=
        G.property.1.trans H.property.1.symm
      exact Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) heq)
    have hdegree : graphDegree (internalGraph G.val) i =
        graphDegree (internalGraph H.val) i := by
      have hG := (graphToCell G).rows i
      have hH := (graphToCell H).rows i
      rw [hrow] at hG
      exact Nat.add_left_cancel (hG.trans hH.symm)
    have hcomp := complement_edges_eq (internalGraph G.val) (internalGraph H.val) i
      (G.property.2.1.trans H.property.2.1.symm) hdegree
    constructor
    · intro u hu v hv
      cases u with
      | inl j =>
          have hji : j = i := by simpa using hu
          subst j
          cases v with
          | inl k =>
              have hki : k = i := by simpa using hv
              subst k
              simp
          | inr w => exact hcross w
      | inr w =>
          cases v with
          | inl j =>
              have hji : j = i := by simpa using hv
              subst j
              exact (G.val.adj_comm _ _).trans ((hcross w).trans (H.val.adj_comm _ _))
          | inr z => exact houtside w z
    · intro u hu v hv
      cases u with
      | inl j =>
          have hji : j ≠ i := by simpa using hu
          cases v with
          | inl k => exact hcomp j k hji (by simpa using hv)
          | inr w => simp at hv
      | inr w => simp at hu

theorem samePairData_iff_restrictions {V : Type*} [Fintype V]
    (a : Finset V) (G H : SimpleGraph V)
    (hdeg : ∀ w, G.degree w = H.degree w) :
    SamePairData a G H ↔ SamePairRestrictions a G H := by
  classical
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hout, hin⟩
    refine ⟨hout, hin, ?_⟩
    intro w hw
    have hsplit (K : SimpleGraph V) :
        K.degree w = (a.filter (K.Adj w)).card +
          ((Finset.univ.filter (K.Adj w)).filter (fun v => v ∉ a)).card := by
      have h := (Finset.univ.filter (K.Adj w)).card_filter_add_card_filter_not
        (fun v => v ∈ a)
      have hinset : (Finset.univ.filter (K.Adj w)).filter (fun v => v ∈ a) =
          a.filter (K.Adj w) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      rw [hinset] at h
      have hcard : (Finset.univ.filter (K.Adj w)).card = K.degree w := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact (K.degree_eq_sum_if_adj (R := ℕ) w).symm
      rw [hcard] at h
      exact h.symm
    have hs : ((Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a)) =
        ((Finset.univ.filter (H.Adj w)).filter (fun v => v ∉ a)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hG, hv⟩
        exact ⟨(hout w hw v hv).mp hG, hv⟩
      · rintro ⟨hH, hv⟩
        exact ⟨(hout w hw v hv).mpr hH, hv⟩
    have h := hdeg w
    rw [hsplit G, hsplit H, hs] at h
    exact Nat.add_right_cancel h

theorem samePairData_iff_row (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairData (complementaryPair i) G.val H.val ↔
      (graphToCell G).outside i = (graphToCell H).outside i := by
  rw [samePairData_iff_restrictions _ _ _ (graphCell_degrees_eq G H),
    samePairRestrictions_iff_row]

theorem samePairData_iff_augmentedRow (G H : GraphTripleCell O e d c) (i : Fin 3) :
    SamePairData (complementaryPair i) G.val H.val ↔
      (encodeCell (graphToCell G)).matrix i = (encodeCell (graphToCell H)).matrix i := by
  exact (samePairData_iff_row G H i).trans
    (encode_row_eq_iff (graphToCell G) (graphToCell H) i).symm

end Problem315.TripleInternalEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCellTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCellTransport

open TripleStateReindex TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}
variable (T : Finset (Fin n)) (hT : T.card = 3)

theorem restrictions_map_iff {V W : Type*} (e : V ≃ W) (a : Finset V)
    (G H : SimpleGraph W) :
    SamePairRestrictions (a.map e.toEmbedding) G H ↔
      SamePairRestrictions a (G.comap e) (H.comap e) := by
  classical
  constructor
  · rintro ⟨hout, hin⟩
    constructor
    · intro u hu v hv
      exact hout (e u) (by simpa using hu) (e v) (by simpa using hv)
    · intro u hu v hv
      exact hin (e u) (by simpa using hu) (e v) (by simpa using hv)
  · rintro ⟨hout, hin⟩
    constructor
    · intro u hu v hv
      obtain ⟨x, rfl⟩ := e.surjective u
      obtain ⟨y, rfl⟩ := e.surjective v
      exact hout x (by simpa using hu) y (by simpa using hv)
    · intro u hu v hv
      obtain ⟨x, rfl⟩ := e.surjective u
      obtain ⟨y, rfl⟩ := e.surjective v
      exact hin x (by simpa using hu) y (by simpa using hv)

theorem sameFiber_iff_splitPairData (G H : GraphState n d) (i : Fin 3) :
    PairResampling.SameFiber (pair T hT i) G.val H.val ↔
      SamePairData (complementaryPair i) (splitGraph T hT G) (splitGraph T hT H) := by
  rw [PairResampling.sameFiber_state_iff]
  rw [samePairData_iff_restrictions _ _ _ (by
    intro v
    rw [splitGraph_degree, splitGraph_degree])]
  exact restrictions_map_iff (splitEquiv T hT) _ G.val H.val

theorem sameFiber_iff_matrixRow (G : GraphState n d)
    (H K : Cell T hT G) (i : Fin 3) :
    PairResampling.SameFiber (pair T hT i) H.val.val K.val.val ↔
      (matrixEquiv T hT G H).matrix i = (matrixEquiv T hT G K).matrix i := by
  rw [sameFiber_iff_splitPairData]
  exact samePairData_iff_augmentedRow (toModel T hT G H) (toModel T hT G K) i

end Problem315.TripleCellTransport

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleProjectionBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.TripleProjectionBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_sum_bound {ι : Type*} [Fintype ι]
    (x : E) (y : ι → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    (∑ i, ‖y i‖ ^ 2) ≤ 2 * ‖x‖ ^ 2 := by
  have hi : ⟪x, ∑ i, y i⟫ = ∑ i, ‖y i‖ ^ 2 := by
    simp [inner_sum, horth]
  have hnorm := sq_nonneg ‖(2 : ℝ) • x - ∑ i, y i‖
  rw [norm_sub_sq_real] at hnorm
  norm_num [norm_smul, inner_smul_left, hi] at hnorm
  nlinarith

theorem triple_gap_of_row_variance (x : E) (y : Fin 3 → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    ‖x‖ ^ 2 ≤ ⟪x, ∑ i, (x - y i)⟫ := by
  have hb := projection_sum_bound x y horth hvar
  have hi : ⟪x, ∑ i, (x - y i)⟫ =
      3 * ‖x‖ ^ 2 - ∑ i, ‖y i‖ ^ 2 := by
    rw [inner_sum]
    simp only [inner_sub_right, horth, real_inner_self_eq_norm_sq]
    rw [Finset.sum_sub_distrib]
    simp
  rw [hi]
  linarith

theorem square_bound_of_unit_gap (x z : E) (hgap : ‖x‖ ^ 2 ≤ ⟪x, z⟫) :
    ⟪x, z⟫ ≤ ‖z‖ ^ 2 := by
  have hnorm := sq_nonneg ‖x - z‖
  rw [norm_sub_sq_real] at hnorm
  linarith

theorem triple_square_of_row_variance (x : E) (y : Fin 3 → E)
    (horth : ∀ i, ⟪x, y i⟫ = ‖y i‖ ^ 2)
    (hvar : ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2) :
    ⟪x, ∑ i, (x - y i)⟫ ≤ ‖∑ i, (x - y i)‖ ^ 2 :=
  square_bound_of_unit_gap x _ (triple_gap_of_row_variance x y horth hvar)

theorem triple_square_of_centered_row_variance
    (P : Fin 3 → E →ₗ[ℝ] E) (C : E → E)
    (hsymm : ∀ i, (P i).IsSymmetric)
    (hidem : ∀ i x, P i (P i x) = P i x)
    (hfix : ∀ i x, P i (C x) = C x)
    (hvar : ∀ x, ‖∑ i, P i (x - C x)‖ ^ 2 ≤
      2 * ∑ i, ‖P i (x - C x)‖ ^ 2) :
    ∀ x, ⟪x, ∑ i, (x - P i x)⟫ ≤ ‖∑ i, (x - P i x)‖ ^ 2 := by
  intro x
  have horth : ∀ i, ⟪x - C x, P i (x - C x)⟫ =
      ‖P i (x - C x)‖ ^ 2 := by
    intro i
    have hi := hsymm i (x - C x) (P i (x - C x))
    rw [hidem] at hi
    rw [← hi, real_inner_self_eq_norm_sq]
  have heq : (∑ i, ((x - C x) - P i (x - C x))) =
      ∑ i, (x - P i x) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sub, hfix]
    abel
  have hzero : ⟪C x, ∑ i, (x - P i x)⟫ = 0 := by
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [inner_sub_right, ← hsymm i (C x) x, hfix, sub_self]
  have h := triple_square_of_row_variance (x - C x)
    (fun i => P i (x - C x)) horth (hvar x)
  rw [heq, inner_sub_left, hzero, sub_zero] at h
  exact h

end Problem315.TripleProjectionBridge

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairTripleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.TripleProjectionBridge

theorem square_of_card_three_centered_row_variance
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hcard : Fintype.card ι = 3) (P : ι → E →ₗ[ℝ] E) (C : E → E)
    (hsymm : ∀ i, (P i).IsSymmetric)
    (hidem : ∀ i x, P i (P i x) = P i x)
    (hfix : ∀ i x, P i (C x) = C x)
    (hvar : ∀ x, ‖∑ i, P i (x - C x)‖ ^ 2 ≤
      2 * ∑ i, ‖P i (x - C x)‖ ^ 2) :
    ∀ x, ⟪x, ∑ i, (x - P i x)⟫ ≤ ‖∑ i, (x - P i x)‖ ^ 2 := by
  let e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  have hv : ∀ x, ‖∑ j : Fin 3, P (e.symm j) (x - C x)‖ ^ 2 ≤
      2 * ∑ j : Fin 3, ‖P (e.symm j) (x - C x)‖ ^ 2 := by
    intro x
    rw [e.symm.sum_comp (fun i => P i (x - C x)),
      e.symm.sum_comp (fun i => ‖P i (x - C x)‖ ^ 2)]
    exact hvar x
  have h := triple_square_of_centered_row_variance
    (fun j => P (e.symm j)) C (fun j => hsymm (e.symm j))
    (fun j => hidem (e.symm j)) (fun j => hfix (e.symm j)) hv
  intro x
  simpa only [e.symm.sum_comp (fun i => x - P i x)] using h x

end Problem315.TripleProjectionBridge

namespace Problem315.PairResampling

theorem triple_fluctuation_square_of_row_variance
    {n : ℕ} {d : Fin n → ℕ} {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 3) (a : ι → Finset (Fin n))
    (C : StateSpace n d → StateSpace n d)
    (hfix : ∀ i f, expectation n d (a i) (C f) = C f)
    (hvar : ∀ f, ‖∑ i, expectation n d (a i) (f - C f)‖ ^ 2 ≤
      2 * ∑ i, ‖expectation n d (a i) (f - C f)‖ ^ 2) :
    ∀ f, ⟪f, ∑ i, fluctuation n d (a i) f⟫ ≤
      ‖∑ i, fluctuation n d (a i) f‖ ^ 2 := by
  have h := TripleProjectionBridge.square_of_card_three_centered_row_variance
    hcard (fun i => (expectation n d (a i)).toLinearMap) C
    (fun i => expectation_isSymmetric (a i))
    (fun i => expectation_idempotent (a i)) hfix hvar
  intro f
  simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using h f

theorem vertex_triple_square_of_row_variance
    {n : ℕ} {d : Fin n → ℕ} (T : Finset (Fin n)) (hT : T.card = 3)
    (C : StateSpace n d → StateSpace n d)
    (hfix : ∀ a ∈ T.powersetCard 2, ∀ f, expectation n d a (C f) = C f)
    (hvar : ∀ f, ‖∑ a ∈ T.powersetCard 2, expectation n d a (f - C f)‖ ^ 2 ≤
      2 * ∑ a ∈ T.powersetCard 2, ‖expectation n d a (f - C f)‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  classical
  have hc : Fintype.card (T.powersetCard 2) = 3 := by
    rw [Fintype.card_coe, Finset.card_powersetCard, hT]
    norm_num
  have hv : ∀ f, ‖∑ a : T.powersetCard 2, expectation n d a.val (f - C f)‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2, ‖expectation n d a.val (f - C f)‖ ^ 2 := by
    intro f
    rw [Finset.sum_coe_sort (T.powersetCard 2) (fun a => expectation n d a (f - C f)),
      Finset.sum_coe_sort (T.powersetCard 2) (fun a => ‖expectation n d a (f - C f)‖ ^ 2)]
    exact hvar f
  have h := triple_fluctuation_square_of_row_variance hc
    (fun a : T.powersetCard 2 => a.val) C (fun a => hfix a.val a.property) hv
  intro f
  simpa only [Finset.sum_coe_sort (T.powersetCard 2)
    (fun a => fluctuation n d a f)] using h f

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCellVarianceGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.CellVarianceGluing

variable {α κ : Type*} [sectionFintypeα : Fintype α] [sectionFintypeκ : Fintype κ]

theorem norm_sq_eq_sum_restrict (key : α → κ) (f : EuclideanSpace ℝ α) :
    ‖f‖ ^ 2 = ∑ k, ‖restrict key k f‖ ^ 2 := by
  classical
  simp only [EuclideanSpace.norm_sq_eq]
  exact (Fintype.sum_fiberwise key (fun x => ‖f x‖ ^ 2)).symm

theorem norm_sum_sq_le_of_cells {ι : Type*} [Fintype ι]
    (key : α → κ) (y : ι → EuclideanSpace ℝ α) (c : ℝ)
    (hlocal : ∀ k, ‖∑ i, restrict key k (y i)‖ ^ 2 ≤
      c * ∑ i, ‖restrict key k (y i)‖ ^ 2) :
    ‖∑ i, y i‖ ^ 2 ≤ c * ∑ i, ‖y i‖ ^ 2 := by
  calc
    _ = ∑ k, ‖∑ i, restrict key k (y i)‖ ^ 2 := by
      rw [norm_sq_eq_sum_restrict key]
      simp only [map_sum]
    _ ≤ ∑ k, c * ∑ i, ‖restrict key k (y i)‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => hlocal k)
    _ = c * ∑ i, ‖y i‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (norm_sq_eq_sum_restrict key (y i)).symm)

include sectionFintypeκ in
theorem center_mem (key : α → κ) (f : EuclideanSpace ℝ α) :
    center key f ∈ cellSpace key := by
  have retainedsectionFintypeκ := sectionFintypeκ
  exact (cellSpace key).starProjection_apply_mem f

include sectionFintypeκ in
theorem sum_restrict_sub_center_eq_zero (key : α → κ) (k : κ)
    (f : EuclideanSpace ℝ α) :
    ∑ x : {x // key x = k}, restrict key k (f - center key f) x = 0 := by
  have retainedsectionFintypeκ := sectionFintypeκ
  classical
  let indicator : EuclideanSpace ℝ α :=
    WithLp.toLp 2 (fun x => if key x = k then 1 else 0)
  have hmem : indicator ∈ cellSpace key := by
    intro x y h
    change (if key x = k then (1 : ℝ) else 0) =
      (if key y = k then (1 : ℝ) else 0)
    rw [h]
  have horth := Submodule.starProjection_inner_eq_zero
    (K := cellSpace key) f indicator hmem
  change ⟪f - center key f, indicator⟫ = 0 at horth
  have horth' : (∑ x, if key x = k then (f - center key f) x else 0) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, indicator,
      mul_ite] using horth
  have hsum : (∑ x ∈ Finset.univ.filter (fun x => key x = k),
      (f - center key f) x) = 0 := by
    simpa only [Finset.sum_filter] using horth'
  rw [Finset.sum_subtype (p := fun x => key x = k) _ (fun x => by simp)] at hsum
  exact hsum

end Problem315.CellVarianceGluing

namespace Problem315.PairResampling
open CellVarianceGluing

theorem expectation_center_of_key_invariant
    {n : ℕ} {d : Fin n → ℕ} {κ : Type*} [Fintype κ]
    (key : GraphState n d → κ) (a : Finset (Fin n))
    (hkey : ∀ G H : GraphState n d, SameFiber a G.val H.val → key G = key H)
    (f : StateSpace n d) : expectation n d a (center key f) = center key f := by
  apply (expectation_eq_self_iff a _).mpr
  intro G H h
  exact center_mem key f G H (hkey G H h)

theorem vertex_triple_square_of_cellwise_row_variance
    {n : ℕ} {d : Fin n → ℕ} {κ : Type*} [Fintype κ]
    (T : Finset (Fin n)) (hT : T.card = 3)
    (key : GraphState n d → κ)
    (hkey : ∀ a ∈ T.powersetCard 2, ∀ G H : GraphState n d,
      SameFiber a G.val H.val → key G = key H)
    (hlocal : ∀ k (f : StateSpace n d),
      ‖∑ a : T.powersetCard 2,
        restrict key k (expectation n d a.val (f - center key f))‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2,
        ‖restrict key k (expectation n d a.val (f - center key f))‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  apply vertex_triple_square_of_row_variance T hT (center key)
  · intro a ha f
    exact expectation_center_of_key_invariant key a (hkey a ha) f
  · intro f
    have h := norm_sum_sq_le_of_cells key
      (fun a : T.powersetCard 2 => expectation n d a.val (f - center key f)) 2
      (fun k => hlocal k f)
    simpa only [Finset.sum_coe_sort (T.powersetCard 2)
      (fun a => expectation n d a (f - center key f)),
      Finset.sum_coe_sort (T.powersetCard 2)
      (fun a => ‖expectation n d a (f - center key f)‖ ^ 2)] using h

end Problem315.PairResampling

namespace Problem315.PairResampling
open CellVarianceGluing

theorem tripleExteriorKey_eq_of_sameFiber {n : ℕ} {d : Fin n → ℕ}
    {T a : Finset (Fin n)} (ha : a ⊆ T) (G H : GraphState n d)
    (h : SameFiber a G.val H.val) : tripleExteriorKey T G = tripleExteriorKey T H := by
  ext u v
  exact h.1 u.val (fun hu => u.property (ha hu))
    v.val (fun hv => v.property (ha hv))

theorem vertex_triple_square_of_exterior_cellwise_row_variance
    {n : ℕ} {d : Fin n → ℕ}
    (T : Finset (Fin n)) (hT : T.card = 3)
    (hlocal : ∀ (k : SimpleGraph {v : Fin n // v ∉ T}) (f : StateSpace n d),
      ‖∑ a : T.powersetCard 2,
        restrict (tripleExteriorKey T) k
          (expectation n d a.val (f - center (tripleExteriorKey T) f))‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2,
        ‖restrict (tripleExteriorKey T) k
          (expectation n d a.val (f - center (tripleExteriorKey T) f))‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  apply vertex_triple_square_of_cellwise_row_variance T hT (tripleExteriorKey T) _ hlocal
  intro a ha G H h
  exact tripleExteriorKey_eq_of_sameFiber (Finset.mem_powersetCard.mp ha).1 G H h

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleMatrixFinEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleMatrixFinEquiv
open TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W]

theorem augmented_row_eq_iff (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ)
    (M N : AugmentedMatrix W e d c) (i : Fin 3) :
    (augmentedEquiv e d c M).val i = (augmentedEquiv e d c N).val i ↔
      M.matrix i = N.matrix i := by
  constructor
  · intro h
    funext w
    exact congrArg Fin.val (congrFun h w)
  · intro h
    funext w
    apply Fin.ext
    exact congrFun h w

end Problem315.TripleMatrixFinEquiv

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleActualRowBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.TripleActualRowBound

open TripleCellTransport TripleInternalEncoding
attribute [local instance] Classical.propDecidable

theorem row_variance_transport {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
    (e : X ≃ Y) (f : I → X → ℝ)
    (h : FiniteVariance.variance (fun y => ∑ i, f i (e.symm y)) ≤
      2 * ∑ i, FiniteVariance.variance (fun y => f i (e.symm y))) :
    FiniteVariance.variance (fun x => ∑ i, f i x) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  have hl := FiniteVariance.variance_equiv e.symm (fun x => ∑ i, f i x)
  have hr (i : I) := FiniteVariance.variance_equiv e.symm (f i)
  rw [hl] at h
  simp_rw [hr] at h
  exact h

theorem full_matrix_row_variance_transport {X C : Type*} [Fintype X] [Fintype C]
    [Nonempty X] (k : C → ℕ) (r : Fin 3 → ℕ)
    (e : X ≃ ForcedColumns.FullMargins k r) (f : Fin 3 → X → ℝ)
    (hf : ∀ i x y, (e x).val i = (e y).val i → f i x = f i y) :
    FiniteVariance.variance (fun x => ∑ i, f i x) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  apply row_variance_transport e f
  apply MatrixRowVariance.row_variance_bound k r ⟨e (Classical.choice inferInstance)⟩
  intro i M N hMN
  apply hf i
  simpa only [e.apply_symm_apply] using hMN

variable {n : ℕ} {d : Fin n → ℕ}
variable (T : Finset (Fin n)) (hT : T.card = 3)

theorem finiteCell_row_iff (G : GraphState n d) (H K : Cell T hT G) (i : Fin 3) :
    (finiteCellEquiv T hT G H).val i = (finiteCellEquiv T hT G K).val i ↔
      PairResampling.SameFiber (pair T hT i) H.val.val K.val.val := by
  change (TripleMatrixFinEquiv.augmentedEquiv _ _ _ (matrixEquiv T hT G H)).val i =
    (TripleMatrixFinEquiv.augmentedEquiv _ _ _ (matrixEquiv T hT G K)).val i ↔ _
  rw [TripleMatrixFinEquiv.augmented_row_eq_iff]
  exact (sameFiber_iff_matrixRow T hT G H K i).symm

theorem cell_row_variance (G : GraphState n d)
    (f : Fin 3 → Cell T hT G → ℝ)
    (hf : ∀ i H K, PairResampling.SameFiber (pair T hT i) H.val.val K.val.val →
      f i H = f i K) :
    FiniteVariance.variance (fun H => ∑ i, f i H) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let : Nonempty (Cell T hT G) := ⟨referenceCell T hT G⟩
  apply full_matrix_row_variance_transport _ _ (finiteCellEquiv T hT G) f
  intro i H K hHK
  exact hf i H K ((finiteCell_row_iff T hT G H K i).mp hHK)

theorem exterior_row_variance (G : GraphState n d)
    (f : Fin 3 → {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} → ℝ)
    (hf : ∀ i H K, PairResampling.SameFiber (pair T hT i) H.val.val K.val.val →
      f i H = f i K) :
    FiniteVariance.variance (fun H => ∑ i, f i H) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let e := exteriorCellEquiv T hT G
  apply row_variance_transport e f
  apply cell_row_variance T hT G
  intro i H K hHK
  exact hf i (e.symm H) (e.symm K) hHK

theorem sum_expectation_exterior (a : Finset (Fin n)) (ha : a ⊆ T)
    (k : SimpleGraph {v : Fin n // v ∉ T}) (f : PairResampling.StateSpace n d) :
    (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H = k},
      PairResampling.expectation n d a f H.val) =
    ∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H = k}, f H.val := by
  let C := fun H : GraphState n d => PairResampling.tripleExteriorKey T H = k
  have hc : ∀ G H : GraphState n d, PairResampling.SameFiber a G.val H.val →
      (C G ↔ C H) := by
    intro G H h
    dsimp [C]
    rw [PairResampling.tripleExteriorKey_eq_of_sameFiber ha G H h]
  have he := CellProjectionTransport.graph_expectation_restrict a C hc f
  have hs := CellProjectionTransport.sum_expectation
    (CellProjectionTransport.restrictedSetoid (CellProjectionTransport.graphSetoid a) C)
    (CellProjectionTransport.restrict C f)
  rw [← he] at hs
  exact hs

theorem exterior_projection_norm_centered (G : GraphState n d)
    (f : PairResampling.StateSpace n d)
    (hf : (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G}, f H.val) = 0) :
    ‖∑ i : Fin 3, CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
      (PairResampling.tripleExteriorKey T G)
      (PairResampling.expectation n d (pair T hT i) f)‖ ^ 2 ≤
    2 * ∑ i : Fin 3, ‖CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
      (PairResampling.tripleExteriorKey T G)
      (PairResampling.expectation n d (pair T hT i) f)‖ ^ 2 := by
  let : Nonempty {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} := ⟨⟨G, rfl⟩⟩
  apply FiniteVariance.norm_sum_sq_le_of_variance_bound
  · intro i
    unfold FixedBlockMarginal.average
    change (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G},
      PairResampling.expectation n d (pair T hT i) f H.val) / _ = 0
    rw [sum_expectation_exterior T (pair T hT i)
      (Finset.mem_powersetCard.mp (pair_mem_powersetCard T hT i)).1, hf, zero_div]
  · apply exterior_row_variance T hT G
    intro i H K hHK
    exact PairResampling.expectation_mem (pair T hT i) f H.val K.val hHK

include hT in

theorem triple_square (f : PairResampling.StateSpace n d) :
    ⟪f, ∑ a ∈ T.powersetCard 2, PairResampling.fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, PairResampling.fluctuation n d a f‖ ^ 2 := by
  apply PairResampling.vertex_triple_square_of_exterior_cellwise_row_variance T hT
  intro k g
  by_cases hk : Nonempty {H : GraphState n d // PairResampling.tripleExteriorKey T H = k}
  · obtain ⟨⟨G, hG⟩⟩ := hk
    subst k
    have hz := CellVarianceGluing.sum_restrict_sub_center_eq_zero
      (PairResampling.tripleExteriorKey T) (PairResampling.tripleExteriorKey T G) g
    have h := exterior_projection_norm_centered T hT G
      (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g) hz
    let y : T.powersetCard 2 → _ := fun a =>
      CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
        (PairResampling.tripleExteriorKey T G)
        (PairResampling.expectation n d a.val
          (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g))
    change ‖∑ i : Fin 3, y (pairEquiv T hT i)‖ ^ 2 ≤
      2 * ∑ i : Fin 3, ‖y (pairEquiv T hT i)‖ ^ 2 at h
    rw [(pairEquiv T hT).sum_comp y,
      (pairEquiv T hT).sum_comp (fun a => ‖y a‖ ^ 2)] at h
    exact h
  · have hz (a : T.powersetCard 2) :
        CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T) k
          (PairResampling.expectation n d a.val
            (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g)) = 0 := by
      ext H
      exact False.elim (hk ⟨H⟩)
    simp only [hz, Finset.sum_const_zero, norm_zero, zero_pow (by omega : 2 ≠ 0),
      mul_zero, le_refl]

end Problem315.TripleActualRowBound

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ActualTripleSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem tripleGenerator_square_oai {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d) (T : Finset (Fin n)) (hT : T.card = 3) :
    ⟪f, tripleGenerator n d T f⟫ ≤
      ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫ := by
  rw [real_inner_self_eq_norm_sq, tripleGenerator_apply]
  exact TripleActualRowBound.triple_square T hT f

end Problem315.PairResampling

end

end OAI
end

theorem solution : type_of% @OAI.Problem315.PairResampling.tripleGenerator_square_oai := @OAI.Problem315.PairResampling.tripleGenerator_square_oai
