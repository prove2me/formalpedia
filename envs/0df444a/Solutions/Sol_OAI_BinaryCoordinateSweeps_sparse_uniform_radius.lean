-- Prove2me | solution 1 for OAI.BinaryCoordinateSweeps.sparse_uniform_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T16:04:49.115951+00:00
-- url     : https://prove2.me/submissions/3bc88f61-51c5-4a22-ae5b-a53c3e8f1827

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000
import Theorems.Thm_OAI_BinaryCoordinateSweeps_sparse_finite_radius

section
-- module Solutions.OAIB3_Bsw.Compat
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_PositiveTraceRestriction
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

lemma positive_pow {B : W →ₗ[ℂ] W} (hB : B.IsPositive) (q : ℕ) : (B^q).IsPositive :=
  match q with
  | 0 => LinearMap.isPositive_one
  | 1 => by simpa using hB
  | n+2 => by
    rw [pow_succ,pow_succ']
    simpa only [Module.End.mul_eq_comp,LinearMap.comp_assoc,hB.adjoint_eq] using (positive_pow hB n).conj_adjoint B

theorem positive_trace_restrict_le (S : Submodule ℂ W) (B : W →ₗ[ℂ] W)
    (hB : B.IsPositive) (hS : ∀ x ∈ S, B x ∈ S) :
    (LinearMap.trace ℂ S (B.restrict hS)).re ≤ (LinearMap.trace ℂ W B).re := by
  let P := S.starProjection.toLinearMap
  let Q : W →ₗ[ℂ] W := 1-P
  have hPsy : P.IsSymmetric := (Submodule.isSymmetricProjection_starProjection S).isSymmetric
  have hQsy : Q.IsSymmetric := LinearMap.IsSymmetric.id.sub hPsy
  have hPP : P*P = P := by
    ext x
    exact congrArg (fun t : W →L[ℂ] W => t x) S.isIdempotentElem_starProjection
  have hQQ : Q*Q = Q := by
    dsimp [Q]
    noncomm_ring [hPP]
  have hQBQ : (Q*B*Q).IsPositive := by
    simpa only [Module.End.mul_eq_comp,LinearMap.comp_assoc,hQsy.adjoint_eq] using hB.conj_adjoint Q
  have hpRange : ∀ x, ((P*B)*P) x ∈ S := by
    intro x
    exact S.starProjection_apply_mem _
  have hpRestr : ((P*B)*P).restrict (fun x _ => hpRange x) = B.restrict hS := by
    ext x
    change P (B (P x.val)) = B x.val
    rw [show P x.val = x.val from Submodule.starProjection_eq_self_iff.mpr x.property]
    exact Submodule.starProjection_eq_self_iff.mpr (hS x.val x.property)
  have hTrP : LinearMap.trace ℂ W (P*B*P) = LinearMap.trace ℂ W (B*P) := by
    change LinearMap.trace ℂ W (P.comp (B*P)) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ W (B*P*P) = _
    rw [mul_assoc,hPP]
  have hTrQ : LinearMap.trace ℂ W (Q*B*Q) = LinearMap.trace ℂ W B -
      LinearMap.trace ℂ W (B*P) := by
    change LinearMap.trace ℂ W (Q.comp (B*Q)) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ W (B*Q*Q) = _
    rw [mul_assoc,hQQ]
    dsimp [Q]
    rw [mul_sub,mul_one,map_sub]
  have hTrace := LinearMap.trace_restrict_eq_of_forall_mem S (P*B*P) hpRange
  rw [hpRestr,hTrP] at hTrace
  have hn := (Complex.nonneg_iff.mp hQBQ.trace_nonneg).1
  rw [hTrQ,Complex.sub_re,← hTrace] at hn
  linarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFactor
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instDecidableEqElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.instMulActionGElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma nat_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i < n := by omega
    have hl := hf (show (⟨i, hi'⟩ : Fin n) < ⟨i+1, hi⟩ from by simp)
    have hp := ih hi'
    change i ≤ f ⟨i, hi'⟩ at hp
    change i + 1 ≤ f ⟨i+1, hi⟩
    omega

lemma sum_orderEmb (s : Finset ℕ) :
    ∑ i : Fin s.card, s.orderEmbOfFin rfl i = ∑ i ∈ s, i := by
  have h := Finset.sum_map (s := (Finset.univ : Finset (Fin s.card)))
    (s.orderEmbOfFin rfl).toEmbedding (fun i : ℕ => i)
  rw [s.map_orderEmbOfFin_univ rfl] at h
  exact h.symm

lemma range_sum_le (s : Finset ℕ) :
    ∑ i ∈ Finset.range s.card, i ≤ ∑ i ∈ s, i := by
  let e := s.orderEmbOfFin rfl
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => nat_le_strictMono e e.strictMono i)
  simpa only [← Fin.sum_univ_eq_sum_range, e, sum_orderEmb] using h

lemma eq_range_of_sum_eq (s : Finset ℕ)
    (h : ∑ i ∈ s, i = ∑ i ∈ Finset.range s.card, i) : s = Finset.range s.card := by
  let e := s.orderEmbOfFin rfl
  have he : ∀ i : Fin s.card, e i = i.val := by
    have hsum : ∑ i : Fin s.card, i.val = ∑ i : Fin s.card, e i := by
      dsimp only [e]
      rw [sum_orderEmb, Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
      exact h.symm
    have hh := (Finset.sum_eq_sum_iff_of_le
        (fun (i : Fin s.card) _ => nat_le_strictMono e e.strictMono i)).mp hsum
    exact fun i => (hh i (Finset.mem_univ i)).symm
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj⟩ := (s.range_orderEmbOfFin rfl ▸ hi : i ∈ Set.range e)
    rw [← hj, he]
    exact Finset.mem_range.mpr j.isLt
  · intro hi
    let j : Fin s.card := ⟨i, Finset.mem_range.mp hi⟩
    rw [← show e j = i from he j]
    exact s.orderEmbOfFin_mem rfl j

lemma mem_columnCells {μ : YoungDiagram} {j : ℕ} {x : Cell μ} :
    x ∈ columnCells μ j ↔ col x = j := by simp [columnCells]

lemma row_injectiveOn_column (μ : YoungDiagram) (j : ℕ) :
    Set.InjOn (row (μ := μ)) (↑(columnCells μ j) : Set (Cell μ)) := by
  intro x hx y hy hxy
  apply Subtype.ext
  apply Prod.ext hxy
  exact (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm

lemma image_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).image row = Finset.range (μ.colLen j) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hc := x.property
    have hj := mem_columnCells.mp hx
    change x.val.2 = j at hj
    rw [← hj]
    exact YoungDiagram.mem_iff_lt_colLen.mp hc
  · intro hi
    refine ⟨⟨(i,j), YoungDiagram.mem_iff_lt_colLen.mpr hi⟩, ?_, rfl⟩
    exact mem_columnCells.mpr rfl

lemma card_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).card = μ.colLen j := by
  rw [← Finset.card_image_of_injOn (row_injectiveOn_column μ j), image_row_columnCells]
  exact Finset.card_range _

lemma sum_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    ∑ x ∈ columnCells μ j, row x = ∑ i ∈ Finset.range (μ.colLen j), i := by
  rw [← image_row_columnCells μ j]
  exact (Finset.sum_image (f := fun i : ℕ => i) (row_injectiveOn_column μ j)).symm

lemma sum_columnCells_le (μ : YoungDiagram) (f : Cell μ → ℕ) (j : ℕ)
    (hf : Set.InjOn f (columnCells μ j)) :
    ∑ x ∈ columnCells μ j, row x ≤ ∑ x ∈ columnCells μ j, f x := by
  have h := range_sum_le ((columnCells μ j).image f)
  rw [Finset.card_image_of_injOn hf, card_columnCells, Finset.sum_image hf] at h
  rwa [sum_row_columnCells]

lemma column_image_of_total_sum (μ : YoungDiagram) (f : Cell μ → ℕ)
    (hf : ∀ j, Set.InjOn f (columnCells μ j))
    (hsum : ∑ x, f x = ∑ x : Cell μ, row x) (j : ℕ) :
    (columnCells μ j).image f = Finset.range (μ.colLen j) := by
  classical
  let J := (Finset.univ : Finset (Cell μ)).image col
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Cell μ)), col x ∈ J := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hfib (g : Cell μ → ℕ) :
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, g x = ∑ x, g x :=
    Finset.sum_fiberwise_of_maps_to hmaps g
  have heq : ∑ j ∈ J, ∑ x ∈ columnCells μ j, row x =
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, f x := by rw [hfib, hfib, hsum]
  have hone := (Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ J) => sum_columnCells_le μ f j (hf j))).mp heq
  by_cases hj : j ∈ J
  · have hc : ((columnCells μ j).image f).card = μ.colLen j := by
      rw [Finset.card_image_of_injOn (hf j), card_columnCells]
    have h : ∑ i ∈ (columnCells μ j).image f, i =
        ∑ i ∈ Finset.range ((columnCells μ j).image f).card, i := by
      rw [hc, Finset.sum_image (hf j), ← sum_row_columnCells]
      exact (hone j hj).symm
    simpa only [hc] using eq_range_of_sum_eq _ h
  · have hc : columnCells μ j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hj
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, mem_columnCells.mp hx⟩
    have hz : μ.colLen j = 0 := by rw [← card_columnCells, hc]; rfl
    simp [hc, hz]

lemma rearranged_row_mem (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) (x : Cell μ) :
    (row (π x), col x) ∈ μ := by
  have he := column_image_of_total_sum μ (fun x => row (π x)) hc
    (Equiv.sum_comp π row) (col x)
  have hm : row (π x) ∈ (columnCells μ (col x)).image (fun x => row (π x)) :=
    Finset.mem_image.mpr ⟨x, mem_columnCells.mpr rfl, rfl⟩
  rw [he, Finset.mem_range] at hm
  exact YoungDiagram.mem_iff_lt_colLen.mpr hm

lemma row_col_intersection (μ : YoungDiagram) :
    rowStabilizer μ ⊓ colStabilizer μ = ⊥ := by
  apply le_antisymm
  · intro π hπ
    change π = 1
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (hπ.1 x) (hπ.2 x)
  · exact bot_le

theorem row_col_factorization (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) :
    ∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c := by
  let t : Cell μ → Cell μ := fun x =>
    ⟨(row (π x), col x), rearranged_row_mem μ π hc x⟩
  have ht : Function.Injective t := by
    intro x y hxy
    have hcol := congrArg (fun z : Cell μ => col z) hxy
    change col x = col y at hcol
    have hrow := congrArg (fun z : Cell μ => row z) hxy
    change row (π x) = row (π y) at hrow
    exact hc (col x) (mem_columnCells.mpr rfl) (mem_columnCells.mpr hcol.symm) hrow
  let c : Equiv.Perm (Cell μ) := Equiv.ofBijective t
    ⟨ht, (Finite.injective_iff_surjective).mp ht⟩
  have cc : c ∈ colStabilizer μ := by intro x; rfl
  have cr : ∀ x, row (c x) = row (π x) := by intro x; rfl
  refine ⟨π * c⁻¹, ?_, c, cc, ?_⟩
  · intro x
    change row (π (c⁻¹ x)) = row x
    rw [← cr]
    simp
  · simp

theorem row_col_alternative (μ : YoungDiagram) (π : Equiv.Perm (Cell μ)) :
    (∃ x y : Cell μ, x ≠ y ∧ col x = col y ∧ row (π x) = row (π y)) ∨
    (∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c) := by
  by_cases hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)
  · exact Or.inr (row_col_factorization μ π hc)
  · left
    simp only [Set.InjOn] at hc
    push Not at hc
    obtain ⟨j, x, hx, y, hy, hrow, hne⟩ := hc
    exact ⟨x, y, hne, (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm, hrow⟩

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungTabloid
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma tabloidOfPerm_row_mul (π : G μ) (r : rowStabilizer μ) :
    tabloidOfPerm μ (π * r.val) = tabloidOfPerm μ π := by
  apply (tabloidOfPerm_eq_iff μ _ _).mpr
  simp

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungAnti
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma signC_swap {x y : Cell μ} (h : x ≠ y) : signC μ (Equiv.swap x y) = -1 := by
  simp [signC_eq, Equiv.Perm.sign_swap h]

lemma columnAnti_apply (v : Tabloid μ → ℂ) :
    columnAnti μ v = ∑ c : C μ, signC μ c.val • tabloidRepresentation μ c.val v := by
  simp [columnAnti, LinearMap.sum_apply]

lemma columnAnti_rep (c : C μ) (v : Tabloid μ → ℂ) :
    columnAnti μ (tabloidRepresentation μ c.val v) = signC μ c.val • columnAnti μ v := by
  rw [columnAnti_apply, columnAnti_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val • (signC μ d.val • tabloidRepresentation μ d.val v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • tabloidRepresentation μ d.val (tabloidRepresentation μ c.val v) =
    signC μ c.val • (signC μ (d * c).val • tabloidRepresentation μ (d * c).val v)
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

lemma columnAnti_basis_column (c : C μ) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ c.val)) = signC μ c.val • polytabloid μ := by
  rw [← mul_one c.val, ← smul_tabloidOfPerm, ← rep_basis, columnAnti_rep]
  rfl

lemma col_fixes_base_iff (c : C μ) :
    c.val • tabloidOfPerm μ 1 = tabloidOfPerm μ 1 ↔ c = 1 := by
  rw [smul_tabloidOfPerm, mul_one, tabloidOfPerm_eq_iff]
  constructor
  · intro hc
    have hr : c.val ∈ rowStabilizer μ := by
      have h := (rowStabilizer μ).inv_mem hc
      simpa using h
    have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hr, c.property⟩
    rw [row_col_intersection] at hi
    exact Subtype.ext hi
  · intro hc
    subst c
    simp

lemma polytabloid_base : polytabloid μ (tabloidOfPerm μ 1) = 1 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ 1 = tabloidOfPerm μ c.val ↔ c = 1 := by
    simpa [smul_tabloidOfPerm, eq_comm] using (col_fixes_base_iff μ c)
  simp only [he]
  simp

lemma polytabloid_ne_zero : polytabloid μ ≠ 0 := by
  intro h
  have hh := congrFun h (tabloidOfPerm μ 1)
  rw [polytabloid_base] at hh
  exact one_ne_zero hh

lemma swap_mem_fiber {X Y : Type*} [DecidableEq X] (f : X → Y) {x y : X}
    (h : f x = f y) : Equiv.swap x y ∈ fiberStabilizer f := by
  intro z
  exact Equiv.apply_swap_eq_self h z

lemma swap_fixes_tabloid (t : Tabloid μ) {x y : Cell μ} (h : t.val x = t.val y) :
    (Equiv.swap x y : G μ) • t = t := by
  apply Subtype.ext
  funext z
  change t.val ((Equiv.swap x y)⁻¹ z) = t.val z
  simpa only [Equiv.swap_inv] using Equiv.apply_swap_eq_self h z

lemma columnAnti_basis_collision (π : G μ) {x y : Cell μ}
    (hne : x ≠ y) (hc : col x = col y) (hr : row (π⁻¹ x) = row (π⁻¹ y)) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) = 0 := by
  let c : C μ := ⟨Equiv.swap x y, swap_mem_fiber _ hc⟩
  have hf : c.val • tabloidOfPerm μ π = tabloidOfPerm μ π :=
    swap_fixes_tabloid μ _ hr
  have h := columnAnti_rep μ c (tabloidBasis μ (tabloidOfPerm μ π))
  rw [rep_basis, hf] at h
  have hs : signC μ c.val = -1 := signC_swap μ hne
  rw [hs, neg_one_smul] at h
  ext t
  have ht := congrFun h t
  simp only [Pi.neg_apply] at ht
  change columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) t = 0
  linear_combination (1 / 2 : ℂ) * ht

lemma columnAnti_basis_span (t : Tabloid μ) :
    ∃ a : ℂ, columnAnti μ (tabloidBasis μ t) = a • polytabloid μ := by
  obtain ⟨π, rfl⟩ := tabloidOfPerm_surjective μ t
  rcases row_col_alternative μ π⁻¹ with ⟨x, y, hne, hc, hr⟩ | ⟨r, hr, c, hc, he⟩
  · exact ⟨0, by rw [columnAnti_basis_collision μ π hne hc hr, zero_smul]⟩
  · have hp : π = c⁻¹ * r⁻¹ := by simpa using congrArg Inv.inv he
    rw [hp, tabloidOfPerm_row_mul μ c⁻¹ ⟨r⁻¹, (rowStabilizer μ).inv_mem hr⟩]
    exact ⟨signC μ c⁻¹, columnAnti_basis_column μ ⟨c⁻¹, (colStabilizer μ).inv_mem hc⟩⟩

theorem columnAnti_rank_one (v : Tabloid μ → ℂ) :
    columnAnti μ v = (columnAnti μ v (tabloidOfPerm μ 1)) • polytabloid μ := by
  have hv : ∃ a : ℂ, columnAnti μ v = a • polytabloid μ := by
    choose a ha using columnAnti_basis_span μ
    refine ⟨∑ t, v t * a t, ?_⟩
    conv_lhs => rw [← sum_tabloidBasis μ v]
    rw [map_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_smul, ha, smul_smul]
  obtain ⟨a, ha⟩ := hv
  have he := congrFun ha (tabloidOfPerm μ 1)
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at he
  rw [he, ha]

lemma columnAnti_square (v : Tabloid μ → ℂ) :
    columnAnti μ (columnAnti μ v) = (Fintype.card (C μ) : ℂ) • columnAnti μ v := by
  rw [columnAnti_apply μ v]
  rw [map_sum]
  simp_rw [map_smul, columnAnti_rep, smul_smul, signC_sq, one_smul]
  rw [← columnAnti_apply]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

lemma columnAnti_polytabloid :
    columnAnti μ (polytabloid μ) = (Fintype.card (C μ) : ℂ) • polytabloid μ :=
  columnAnti_square μ _

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungSpecht
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma antiModule_apply (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v = (tabloidRepresentation μ).asModuleEquiv.symm
      (columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v)) := rfl

lemma antiModule_rank_one (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v =
      columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) • polyModule μ := by
  rw [antiModule_apply, columnAnti_rank_one, map_smul]
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one]
  rfl

lemma polyModule_ne_zero : polyModule μ ≠ 0 := by
  intro h
  apply polytabloid_ne_zero μ
  have he := congrArg (tabloidRepresentation μ).asModuleEquiv h
  simpa only [polyModule, LinearEquiv.apply_symm_apply, map_zero] using he

lemma Specht_ne_bot : Specht μ ≠ ⊥ := by
  intro h
  have hm := polyModule_mem_Specht μ
  rw [h] at hm
  exact polyModule_ne_zero μ hm

lemma antiModule_mem (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    (v : (tabloidRepresentation μ).asModule) (hv : v ∈ U) : antiModule μ v ∈ U := by
  rw [antiModule_apply, columnAnti_apply, map_sum]
  apply U.sum_mem
  intro c hc
  have h := U.smul_mem (MonoidAlgebra.single c.val (signC μ c.val)) hv
  have he : (tabloidRepresentation μ).asModuleEquiv.symm
      (signC μ c.val • tabloidRepresentation μ c.val ((tabloidRepresentation μ).asModuleEquiv v)) =
      MonoidAlgebra.single c.val (signC μ c.val) • v := by
    apply (tabloidRepresentation μ).asModuleEquiv.injective
    rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, LinearMap.smul_apply]
  rw [he]
  exact h

lemma scalar_polyModule_mem_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    {a : ℂ} (ha : a ≠ 0) : a • polyModule μ ∈ U ↔ polyModule μ ∈ U := by
  exact (U.restrictScalars ℂ).smul_mem_iff ha

lemma Specht_le_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule) :
    Specht μ ≤ U ↔ polyModule μ ∈ U := by
  rw [Specht, Submodule.span_le, Set.singleton_subset_iff]
  rfl

theorem Specht_isAtom : IsAtom (Specht μ) := by
  refine ⟨Specht_ne_bot μ, ?_⟩
  intro U hU
  obtain ⟨V, hUV⟩ := exists_isCompl U
  have ht : polyModule μ ∈ U ⊔ V := by
    rw [hUV.sup_eq_top]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ht
  have hau := antiModule_mem μ U u hu
  have hav := antiModule_mem μ V v hv
  rw [antiModule_rank_one] at hau hav
  by_cases hc : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv u) (tabloidOfPerm μ 1) = 0
  · have he : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) =
          (Fintype.card (C μ) : ℂ) := by
      have hh := congrArg (fun w : (tabloidRepresentation μ).asModule =>
        columnAnti μ ((tabloidRepresentation μ).asModuleEquiv w) (tabloidOfPerm μ 1)) huv
      simp only [map_add, Pi.add_apply, hc, zero_add, polyModule,
        LinearEquiv.apply_symm_apply, columnAnti_polytabloid,
        Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at hh
      exact hh
    have hne : (Fintype.card (C μ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hSV : Specht μ ≤ V := (Specht_le_iff μ V).mpr
      ((scalar_polyModule_mem_iff μ V (he.trans_ne hne)).mp hav)
    apply le_antisymm _ bot_le
    calc U ≤ U ⊓ V := le_inf le_rfl (hU.le.trans hSV)
         _ = ⊥ := hUV.inf_eq_bot
  · have hSU : Specht μ ≤ U := (Specht_le_iff μ U).mpr
      ((scalar_polyModule_mem_iff μ U hc).mp hau)
    exact (hU.not_ge hSU).elim

instance Specht_isSimpleModule : IsSimpleModule ℂ[G μ] (Specht μ) :=
  isSimpleModule_iff_isAtom.mpr (Specht_isAtom μ)

end BinaryCoordinateSweeps.Young

end

open scoped MonoidAlgebra BigOperators

namespace BinaryCoordinateSweeps.Young

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V] [IsScalarTower ℂ A V]

variable (μ : YoungDiagram)

instance instIsIrreducibleGComplexSpechtSpaceSpechtRep : Representation.IsIrreducible (k := ℂ) (G := G μ) (V := SpechtSpace μ) (spechtRep μ) :=
  (Representation.isSimpleModule_iff_irreducible_ofModule (Specht μ)).mp inferInstance

lemma spechtInclude_poly : spechtInclude μ (spechtPoly μ) = polytabloid μ := by
  change (tabloidRepresentation μ).asModuleEquiv
    ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)
      ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm
        (⟨polyModule μ, polyModule_mem_Specht μ⟩ : Specht μ))).val) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (tabloidRepresentation μ).asModuleEquiv.apply_symm_apply _

lemma spechtPoly_ne_zero : spechtPoly μ ≠ 0 := by
  intro h
  have he := congrArg (spechtInclude μ) h
  rw [map_zero, spechtInclude_poly] at he
  exact polytabloid_ne_zero μ he

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungHilbert
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

variable (μ : YoungDiagram)

lemma spechtHilbertEquiv_coeff (v : SpechtSpace μ) (t : Tabloid μ) :
    (spechtHilbertEquiv μ v).val t = spechtInclude μ v t := rfl

lemma hilbertSpecht_coeff (g : G μ) (v : SpechtHilbert μ) (t : Tabloid μ) :
    (hilbertSpecht μ g v).val t = v.val (g⁻¹ • t) := by
  obtain ⟨w,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  change (spechtHilbertEquiv μ (spechtRep μ g ((spechtHilbertEquiv μ).symm
      (spechtHilbertEquiv μ w)))).val t = _
  rw [LinearEquiv.symm_apply_apply,spechtHilbertEquiv_coeff,spechtInclude_rep]
  rfl

lemma hilbertSpecht_inner (g : G μ) (v w : SpechtHilbert μ) :
    inner ℂ (hilbertSpecht μ g v) (hilbertSpecht μ g w) = inner ℂ v w := by
  change inner ℂ (hilbertSpecht μ g v).val (hilbertSpecht μ g w).val = inner ℂ v.val w.val
  simp only [PiLp.inner_apply,RCLike.inner_apply,hilbertSpecht_coeff]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun t => w.val t * star (v.val t))

lemma hilbertSpecht_unitary (g : G μ) (v : SpechtHilbert μ) :
    ‖hilbertSpecht μ g v‖ = ‖v‖ :=
  ((hilbertSpecht μ g).isometryOfInner (hilbertSpecht_inner μ g)).norm_map v

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_SumDite
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
lemma sum_dite_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : ∀ x, P x → M) :
    (∑ x, if h : P x then f x h else 0) = ∑ x : {x // P x}, f x.val x.property := by
  classical
  have he := (Equiv.Set.sumCompl {x | P x}).sum_comp
    (fun x => if h : P x then f x h else 0)
  rw [Fintype.sum_sum_type] at he
  rw [← he]
  simp only [Equiv.Set.sumCompl_apply_inl, Equiv.Set.sumCompl_apply_inr]
  have hp : (∑ x : {x // P x}, if h : P x.val then f x.val h else 0) =
      ∑ x : {x // P x}, f x.val x.property := by
    apply Finset.sum_congr rfl
    intro x _
    exact dite_eq_left x.property
  have hn : (∑ x : {x // ¬P x}, if h : P x.val then f x.val h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact dite_eq_right x.property
  exact (congrArg₂ (· + ·) hp hn).trans (add_zero _)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_Basic
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section FiniteProbability
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

lemma finiteLaw_nonneg (f : Ω → G) (g : G) : 0 ≤ finiteLaw f g := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma finiteLaw_sum [Nonempty Ω] (f : Ω → G) : ∑ g, finiteLaw f g = 1 := by
  classical
  simp only [finiteLaw]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

lemma uniformLaw_sum [Nonempty G] : ∑ g, uniformLaw G g = 1 := by
  simp [uniformLaw, Fintype.card_ne_zero]

end FiniteProbability

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_SupportTimeBoundBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma sign_boolSwitch (c : Bool) :
    Equiv.Perm.sign (boolSwitch c) = if c then (-1 : ℤˣ) else 1 := by
  cases c
  · have : boolSwitch false = 1 := by ext x; cases x <;> rfl
    rw [this]; rfl
  · have : boolSwitch true = Equiv.swap false true := by
      ext x; cases x <;> simp [boolSwitch]
    rw [this, Equiv.Perm.sign_swap (by decide)]; rfl

lemma realSign_coordinateLayer (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i ≠ j} → Bool) → Bool) :
    realSign (coordinateLayer d j c) = ∏ y, (if c y then (-1 : ℝ) else 1) := by
  classical
  have he : coordinateLayer d j c =
      (Equiv.piSplitAt j (fun _ : Fin d => Bool)).trans
        ((Equiv.prodCongrLeft (fun y => boolSwitch (c y))).trans
          (Equiv.piSplitAt j (fun _ : Fin d => Bool)).symm) := rfl
  rw [he]
  simp [realSign, Equiv.Perm.sign_prodCongrLeft, sign_boolSwitch, apply_ite]

lemma sum_realSign_coordinateLayer (d : ℕ) (j : Fin d) :
    ∑ c : ({i : Fin d // i ≠ j} → Bool) → Bool,
      realSign (coordinateLayer d j c) = 0 := by
  classical
  simp_rw [realSign_coordinateLayer]
  rw [← Fintype.prod_sum (fun (_ : {i : Fin d // i ≠ j} → Bool) (b : Bool) =>
    if b then (-1 : ℝ) else 1)]
  simp

lemma realSign_binarySweep (d : ℕ) (c : SweepCoins d) :
    realSign (binarySweep d c) = ∏ j, realSign (coordinateLayer d j (c j)) := by
  classical
  simp [binarySweep, map_list_prod, List.map_reverse, List.prod_reverse,
    List.map_ofFn, List.prod_ofFn]

lemma sum_realSign_binarySweep (d : ℕ) (hd : 0 < d) :
    ∑ c : SweepCoins d, realSign (binarySweep d c) = 0 := by
  classical
  simp_rw [realSign_binarySweep]
  rw [← Fintype.prod_sum (fun (j : Fin d) (c : ({i : Fin d // i ≠ j} → Bool) → Bool) =>
    realSign (coordinateLayer d j c))]
  apply Finset.prod_eq_zero (i := ⟨0, hd⟩) (Finset.mem_univ _)
  exact sum_realSign_coordinateLayer d ⟨0, hd⟩

lemma finiteLaw_expectation {Ω G : Type*} [Fintype Ω] [Fintype G]
    (f : Ω → G) (a : G → ℝ) :
    ∑ g, finiteLaw f g * a g = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, a (f ω) := by
  classical
  simp only [finiteLaw, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul, Finset.mul_sum]

theorem binary_sign_annihilated (d : ℕ) (hd : 0 < d) :
    ∑ g : Equiv.Perm (Slot d), binaryLaw d g * realSign g = 0 := by
  rw [binaryLaw, finiteLaw_expectation, sum_realSign_binarySweep d hd, mul_zero]

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_GridSweepPath
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

theorem pathEvent_nonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    ∃ g : GridChoices bits, pathEvent H g := by
  classical
  let A (j : Fin b) (y : GridOutside bits j) :=
    {k : Fin h // (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i) = y}
  have hp (j : Fin b) (y : GridOutside bits j) :
      ∃ σ : Equiv.Perm (Slot (bits j)), ∀ k : A j y,
        σ (H.position j.castSucc k.val j) = H.position j.succ k.val j := by
    apply Equiv.Perm.exists_extending_pair
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.castSucc
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.succ
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · rw [H.changes_only_stage j k.val i hi, H.changes_only_stage j l.val i hi]
        exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
  choose g hg using hp
  refine ⟨g, ?_⟩
  intro j k
  apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
  simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
  apply Prod.ext
  · exact hg j _ ⟨k, rfl⟩
  · funext i
    exact (H.changes_only_stage j k i.val i.property).symm

lemma lineLaw_pos (d : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : Equiv.Perm (Slot d)) : 0 < lineLaw d z g := by
  have hu : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    exact inv_pos.mpr hc
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hz1) hu)
    (mul_nonneg hz (finiteLaw_nonneg (binarySweep d) g))

lemma lineLaw_sum (d : ℕ) (z : ℝ) : ∑ g, lineLaw d z g = 1 := by
  simp only [lineLaw, Finset.sum_add_distrib, ← Finset.mul_sum,
    uniformLaw_sum, binaryLaw, finiteLaw_sum]
  ring

lemma gridWeight_pos {b : ℕ} (bits : Fin b → ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : GridChoices bits) : 0 < gridWeight bits z g := by
  apply Finset.prod_pos
  intro j _
  exact Finset.prod_pos (fun y _ => lineLaw_pos (bits j) hz hz1 (g j y))

theorem conditionalNormalizer_pos {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) : 0 < conditionalNormalizer H z := by
  classical
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  apply Finset.sum_pos'
  · intro g' _
    split_ifs
    · exact (gridWeight_pos bits hz hz1 g').le
    · exact le_rfl
  · exact ⟨g, Finset.mem_univ _, by simpa [hg] using gridWeight_pos bits hz hz1 g⟩

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_IndependentHistory
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section Assignments
attribute [local instance] Classical.propDecidable
variable {X I : Type*} [Fintype X] [Fintype I]

lemma card_assignment_completions (A B : I ↪ X) :
    Fintype.card {σ : Equiv.Perm X // Assigns A B σ} =
      (Fintype.card X - Fintype.card I).factorial := by
  classical
  let eA := Equiv.ofInjective A A.injective
  let eB := Equiv.ofInjective B B.injective
  let e₀ : Set.range A ≃ Set.range B := eA.symm.trans eB
  have ha : Fintype.card (Set.range A) = Fintype.card I := Fintype.card_congr eA.symm
  have hb : Fintype.card (Set.range B) = Fintype.card I := Fintype.card_congr eB.symm
  let e : {σ : Equiv.Perm X // Assigns A B σ} ≃
      {σ : X ≃ X // ∀ x : Set.range A, σ x = e₀ x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro σ
      constructor
      · intro h x
        obtain ⟨i, hi⟩ := x.property
        have hx : x = eA i := Subtype.ext hi.symm
        rw [hx]
        simpa [e₀, eA, eB] using h i
      · intro h i
        simpa [e₀, eA, eB] using h (eA i))
  let c : ↥((Set.range A)ᶜ) ≃ ↥((Set.range B)ᶜ) := Fintype.equivOfCardEq (by
    change Fintype.card {x : X // x ∉ Set.range A} = Fintype.card {x : X // x ∉ Set.range B}
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, ha, hb])
  rw [Fintype.card_congr (e.trans (Equiv.Set.compl e₀)), Fintype.card_equiv c]
  change (Fintype.card {x : X // x ∉ Set.range A}).factorial = _
  rw [Fintype.card_subtype_compl, ha]

lemma uniform_assignment_probability (A B : I ↪ X) :
    (∑ σ : Equiv.Perm X, if Assigns A B σ then
      (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ else 0) =
      (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ := by
  classical
  have hn : Fintype.card I ≤ Fintype.card X := Fintype.card_le_of_injective A A.injective
  have hcard : (Fintype.card {σ : Equiv.Perm X // Assigns A B σ} : ℝ) =
      ((Fintype.card X - Fintype.card I).factorial : ℝ) := by
    exact_mod_cast card_assignment_completions A B
  have hsum : (∑ σ : Equiv.Perm X, if Assigns A B σ then
      (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ else 0) =
      (Fintype.card {σ : Equiv.Perm X // Assigns A B σ} : ℝ) *
        (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ := by
    simp [Fintype.card_subtype, Finset.sum_ite]
  rw [hsum, hcard, Fintype.card_perm,
    ← Nat.factorial_mul_descFactorial hn, Nat.cast_mul, mul_inv_rev]
  have hf : (((Fintype.card X - Fintype.card I).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (Fintype.card X - Fintype.card I))
  field_simp

end Assignments

lemma fallingCost_sum {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) :
    fallingCost m u = ∑ j ∈ Finset.range u, Real.log ((m : ℝ) / (m - j : ℕ)) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hdf : (0 : ℝ) < m.descFactorial u := by exact_mod_cast (Nat.descFactorial_pos.mpr hu)
  have hdiff (j : ℕ) (hj : j ∈ Finset.range u) : (m - j : ℕ) ≠ 0 := by
    simp only [Finset.mem_range] at hj
    omega
  have hlog (j : ℕ) (hj : j ∈ Finset.range u) :
      Real.log ((m : ℝ) / (m - j : ℕ)) = Real.log m - Real.log (m - j : ℕ) :=
    Real.log_div hmp.ne' (by exact_mod_cast hdiff j hj)
  rw [fallingCost, Real.log_div (pow_ne_zero _ hmp.ne') hdf.ne', Real.log_pow,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod, Real.log_prod (fun j hj => by exact_mod_cast hdiff j hj)]
  rw [Finset.sum_congr rfl hlog, Finset.sum_sub_distrib]
  simp

lemma fallingCost_nonneg {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) : 0 ≤ fallingCost m u := by
  rw [fallingCost_sum hm hu]
  apply Finset.sum_nonneg
  intro j hj
  have hdiff : (0 : ℝ) < (m - j : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt ((Finset.mem_range.mp hj).trans_le hu))
  apply Real.log_nonneg
  exact (le_div_iff₀ hdiff).mpr (by simp)

lemma prefix_sum_le_of_full_sum_le {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) (f : ℕ → ℝ)
    (hf : ∀ i < u, ∀ j, u ≤ j → j < m → f i ≤ f j)
    (hfull : ∑ j ∈ Finset.range m, f j ≤ m) :
    ∑ j ∈ Finset.range u, f j ≤ u := by
  have hc : ((m : ℝ) - u) * (∑ i ∈ Finset.range u, f i) ≤
      (u : ℝ) * ∑ j ∈ Finset.Ico u m, f j := by
    calc
      _ = ∑ i ∈ Finset.range u, ∑ _j ∈ Finset.Ico u m, f i := by
        simp [Nat.cast_sub hu, Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range u, ∑ j ∈ Finset.Ico u m, f j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hf i (Finset.mem_range.mp hi) j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
      _ = _ := by simp
  have hsplit := Finset.sum_range_add_sum_Ico f hu
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hu0 : (0 : ℝ) ≤ u := by positivity
  nlinarith

lemma fallingCost_le {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) : fallingCost m u ≤ u := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hfull : fallingCost m m ≤ m := by
    have hst := Stirling.le_log_factorial_stirling hm.ne'
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [fallingCost, Nat.descFactorial_self, Real.log_div (pow_ne_zero _ hmp.ne') (by positivity), Real.log_pow]
    linarith
  rw [fallingCost_sum hm hu]
  apply prefix_sum_le_of_full_sum_le hm hu
  · intro i hi j huj hjm
    apply Real.log_le_log
    · exact div_pos hmp (by exact_mod_cast Nat.sub_pos_of_lt (hi.trans_le hu))
    · apply div_le_div_of_nonneg_left hmp.le
      · exact_mod_cast Nat.sub_pos_of_lt hjm
      · exact_mod_cast Nat.sub_le_sub_left (hi.le.trans huj) m
  · rwa [← fallingCost_sum hm le_rfl]

attribute [local instance] Classical.propDecidable

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_AssignmentWeight
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section AssignmentWeights
attribute [local instance] Classical.propDecidable
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

omit [Fintype I] in
lemma assignmentWeight_mono (p q : Equiv.Perm X → ℝ)
    (hpq : ∀ σ, p σ ≤ q σ) (A B : I ↪ X) :
    assignmentWeight p A B ≤ assignmentWeight q A B := by
  apply Finset.sum_le_sum
  intro σ _
  split_ifs
  · exact hpq σ
  · exact le_rfl

omit [Fintype I] in
lemma assignmentWeight_smul (p : Equiv.Perm X → ℝ) (c : ℝ) (A B : I ↪ X) :
    assignmentWeight (fun σ => c * p σ) A B = c * assignmentWeight p A B := by
  simp only [assignmentWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

lemma assignmentWeight_uniform (A B : I ↪ X) :
    assignmentWeight (fun _ => (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) A B =
      (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ :=
  uniform_assignment_probability A B

lemma assignmentWeight_comparison {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) :
    (1 / 2 : ℝ) * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ ≤
      assignmentWeight p A B ∧
    assignmentWeight p A B ≤
      2 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ := by
  constructor
  · simpa [assignmentWeight_smul, assignmentWeight_uniform] using
      assignmentWeight_mono (fun _ => (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) p hl A B
  · simpa [assignmentWeight_smul, assignmentWeight_uniform] using
      assignmentWeight_mono p (fun _ => 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) hu A B

lemma assignmentWeight_ratio_le {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) (A' B' : J ↪ X) :
    assignmentWeight p A' B' / assignmentWeight p A B ≤
      4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
        (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ) := by
  have hi : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A A.injective)
  have hj : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card J) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A' A'.injective)
  have hden := (assignmentWeight_comparison hl hu A B).1
  have hnum := (assignmentWeight_comparison hl hu A' B').2
  have hdp : 0 < assignmentWeight p A B :=
    lt_of_lt_of_le (mul_pos (by norm_num) (inv_pos.mpr hi)) hden
  apply (div_le_iff₀ hdp).mpr
  calc
    _ ≤ 2 * (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)⁻¹ := hnum
    _ = (4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
        (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)) *
          ((1 / 2 : ℝ) * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

end AssignmentWeights

attribute [local instance] Classical.propDecidable

lemma lineHoles_le {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : lineHoles H j y ≤ 2 ^ bits j := by
  simpa [lineHoles, Slot, Fintype.card_pi] using
    Fintype.card_le_of_injective (lineInput H j y) (lineInput H j y).injective

lemma sum_lineHoles {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) : ∑ y, lineHoles H j y = h := by
  classical
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun k : Fin h => (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i)))
  simpa only [Fintype.card_sigma, Fintype.card_fin, lineHoles] using hh

lemma pathCost_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    0 ≤ pathCost H := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro y _
  exact fallingCost_nonneg (by positivity) (lineHoles_le H j y)

lemma pathCost_le {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    pathCost H ≤ (b : ℝ) * h := by
  calc
    pathCost H ≤ ∑ j : Fin b, ∑ y, (lineHoles H j y : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro y _
      exact fallingCost_le (by positivity) (lineHoles_le H j y)
    _ = _ := by simp only [← Nat.cast_sum, sum_lineHoles]; simp

lemma pathEvent_iff_assigns {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) : pathEvent H g ↔
      ∀ (j : Fin b) (y : GridOutside bits j), Assigns (lineInput H j y) (lineOutput H j y) (g j y) := by
  constructor
  · intro hg j y k
    change g j y (H.position j.castSucc k.val j) = H.position j.succ k.val j
    have he := congrArg (fun x : GridSlot bits => x j) (hg j k.val)
    simpa only [gridLayer, Equiv.trans_apply, Equiv.piSplitAt_apply,
      Equiv.prodCongrLeft_apply, Equiv.piSplitAt_symm_apply, dite_true, eq_self,
      lineInput, lineOutput, Function.Embedding.coeFn_mk, k.property] using he
  · intro hg j k
    apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
    simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
    apply Prod.ext
    · exact hg j _ ⟨k, rfl⟩
    · funext i
      exact (H.changes_only_stage j k i.val i.property).symm

lemma finiteLaw_le_one {Ω G : Type*} [Fintype Ω] [Fintype G] [Nonempty Ω]
    (f : Ω → G) (g : G) : finiteLaw f g ≤ 1 := by
  calc
    _ ≤ ∑ x, finiteLaw f x := Finset.single_le_sum (fun x _ => finiteLaw_nonneg f x) (Finset.mem_univ _)
    _ = 1 := finiteLaw_sum f

lemma linePerturbationRadius_pos (r : ℕ) : 0 < linePerturbationRadius r := by
  unfold linePerturbationRadius
  positivity

lemma lineLaw_comparison (r d : ℕ) (hd : d ≤ 2 * r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) (g : Equiv.Perm (Slot d)) :
    (1 / 2 : ℝ) * uniformLaw (Equiv.Perm (Slot d)) g ≤ lineLaw d z g ∧
      lineLaw d z g ≤ 2 * uniformLaw (Equiv.Perm (Slot d)) g := by
  have hf1 : (1 : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 ^ (2 * r))
  have hzp : z ≤ 1 / 2 := hzr.trans (by
    unfold linePerturbationRadius
    apply one_div_le_one_div_of_le (by norm_num)
    linarith)
  have hfd : (Fintype.card (Equiv.Perm (Slot d)) : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast (show Fintype.card (Equiv.Perm (Slot d)) ≤ (2 ^ (2 * r)).factorial from by
      simp only [Fintype.card_perm, Slot, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Nat.factorial_le (Nat.pow_le_pow_right (by norm_num) hd))
  have hup : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    positivity
  have hzU : z ≤ uniformLaw (Equiv.Perm (Slot d)) g := hzr.trans (by
    unfold linePerturbationRadius uniformLaw
    rw [one_div]
    apply inv_anti₀ (by exact_mod_cast Fintype.card_pos)
    linarith)
  have hB0 : 0 ≤ binaryLaw d g := finiteLaw_nonneg _ _
  have hB1 : binaryLaw d g ≤ 1 := finiteLaw_le_one _ _
  constructor
  · unfold lineLaw
    nlinarith
  · unfold lineLaw
    nlinarith [mul_le_mul_of_nonneg_left hB1 hz]

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_LocalPathWeight
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma fallingCost_formula {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) :
    fallingCost m u = (u : ℝ) * Real.log m - Real.log (m.descFactorial u : ℕ) := by
  have hmp : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdf : (m.descFactorial u : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hu).ne'
  rw [fallingCost, Real.log_div (pow_ne_zero _ hmp) hdf, Real.log_pow]

lemma assignmentWeight_eq_of_card_eq {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (p : Equiv.Perm X → ℝ) (A B : I ↪ X) (A' B' : J ↪ X) (f : I ↪ J)
    (hA : ∀ i, A' (f i) = A i) (hB : ∀ i, B' (f i) = B i)
    (hcard : Fintype.card I = Fintype.card J) : assignmentWeight p A' B' = assignmentWeight p A B := by
  have hsur : Function.Surjective f := by
    by_contra hn
    have hc := Fintype.card_lt_of_injective_not_surjective f f.injective hn
    omega
  have he (σ : Equiv.Perm X) : Assigns A' B' σ ↔ Assigns A B σ := by
    constructor
    · intro hσ i
      simpa only [hA, hB] using hσ (f i)
    · intro hσ j
      obtain ⟨i, rfl⟩ := hsur j
      simpa only [hA, hB] using hσ i
  simp only [assignmentWeight, he]

lemma assignmentWeight_log_ratio_le {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (hm : 0 < Fintype.card X) {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) (A' B' : J ↪ X) (f : I ↪ J)
    (hA : ∀ i, A' (f i) = A i) (hB : ∀ i, B' (f i) = B i) :
    Real.log (assignmentWeight p A' B' / assignmentWeight p A B) ≤
      fallingCost (Fintype.card X) (Fintype.card J) - fallingCost (Fintype.card X) (Fintype.card I) -
        ((Fintype.card J : ℝ) - Fintype.card I) * Real.log (Fintype.card X) +
          Real.log 4 * ((Fintype.card J : ℝ) - Fintype.card I) := by
  have hI := Fintype.card_le_of_injective A A.injective
  have hJ := Fintype.card_le_of_injective A' A'.injective
  have hi : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hI
  have hj : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card J) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hJ
  have wi : 0 < assignmentWeight p A B := lt_of_lt_of_le (by positivity) (assignmentWeight_comparison hl hu A B).1
  have wj : 0 < assignmentWeight p A' B' := lt_of_lt_of_le (by positivity) (assignmentWeight_comparison hl hu A' B').1
  by_cases hc : Fintype.card I = Fintype.card J
  · rw [assignmentWeight_eq_of_card_eq p A B A' B' f hA hB hc, div_self wi.ne', Real.log_one, hc]
    simp
  · have hIJ := Fintype.card_le_of_injective f f.injective
    have hgap : (1 : ℝ) ≤ (Fintype.card J : ℝ) - Fintype.card I := by
      have hh : Fintype.card I + 1 ≤ Fintype.card J := by omega
      exact_mod_cast (show (1 : ℤ) ≤ (Fintype.card J : ℤ) - Fintype.card I from by omega)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤ Real.log (4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
          (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)) :=
        Real.log_le_log (div_pos wj wi) (assignmentWeight_ratio_le hl hu A B A' B')
      _ = Real.log 4 + Real.log (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) -
          Real.log (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ) := by
        rw [Real.log_div (by positivity) hj.ne', Real.log_mul (by norm_num) hi.ne']
      _ ≤ _ := by
        rw [fallingCost_formula hm hI, fallingCost_formula hm hJ]
        nlinarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_Placement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma independent_event_weight {J : Type*} [Fintype J] {X : J → Type*}
    [∀ j, Fintype (X j)] (w : ∀ j, X j → ℝ) (P : ∀ j, X j → Prop) :
    (∑ x : ∀ j, X j, if ∀ j, P j (x j) then ∏ j, w j (x j) else 0) =
      ∏ j, ∑ a : X j, if P j a then w j a else 0 := by
  classical
  calc
    _ = ∑ x : ∀ j, X j, ∏ j, if P j (x j) then w j (x j) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact Fintype.prod_ite_zero.symm
    _ = _ := (Fintype.prod_sum (fun j a => if P j a then w j a else 0)).symm

lemma conditionalWeight_factor {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g else 0) =
      ∏ j, ∏ y, if Assigns (lineInput H j y) (lineOutput H j y) (g j y) then
        lineLaw (bits j) z (g j y) else 0 := by
  classical
  rw [pathEvent_iff_assigns]
  simp only [Fintype.prod_ite_zero]
  split_ifs <;> rfl

lemma sum_prod_grid {b : ℕ} (bits : Fin b → ℕ)
    (f : ∀ j : Fin b, GridOutside bits j → Equiv.Perm (Slot (bits j)) → ℝ) :
    (∑ g : GridChoices bits, ∏ j, ∏ y, f j y (g j y)) =
      ∏ j, ∏ y, ∑ σ, f j y σ := by
  rw [← Fintype.prod_sum (fun (j : Fin b)
    (g : GridOutside bits j → Equiv.Perm (Slot (bits j))) => ∏ y, f j y (g y))]
  apply Finset.prod_congr rfl
  intro j _
  exact (Fintype.prod_sum (f j)).symm

lemma conditionalNormalizer_eq_prod {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) : conditionalNormalizer H z = ∏ j, ∏ y, localPathWeight H z j y := by
  let f (j : Fin b) (y : GridOutside bits j) (σ : Equiv.Perm (Slot (bits j))) : ℝ :=
    if Assigns (lineInput H j y) (lineOutput H j y) σ then lineLaw (bits j) z σ else 0
  have hL : conditionalNormalizer H z =
      ∑ g : GridChoices bits, ∏ j, ∏ y, f j y (g j y) := by
    unfold conditionalNormalizer
    apply Finset.sum_congr rfl
    intro g _
    rw [conditionalWeight_factor]
  have hR : (∏ j, ∏ y, localPathWeight H z j y) =
      ∏ j, ∏ y, ∑ σ, f j y σ := by
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro y _
    unfold localPathWeight assignmentWeight
    refine Finset.sum_congr ?_ ?_
    · ext σ
      simp only [Finset.mem_univ]
    intro σ _
    unfold f
    split_ifs <;> rfl
  rw [hL, hR]
  exact sum_prod_grid bits f

instance conditionalChoicesNonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    Nonempty (ConditionalChoices H) := by
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  exact ⟨⟨g, hg⟩⟩

lemma conditionalChoiceWeight_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (g : ConditionalChoices H) :
    0 ≤ conditionalChoiceWeight H z g :=
  le_of_lt (div_pos (gridWeight_pos bits hz hz1 g.val) (conditionalNormalizer_pos H hz hz1))

section FiniteBijectionKernel
variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma bijectionKernel_nonneg (w : Ω → ℝ) (e : Ω → A ≃ B)
    (hw : ∀ ω, 0 ≤ w ω) (x : A) (y : B) : 0 ≤ bijectionKernel w e x y := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_rfl

end FiniteBijectionKernel

lemma placementProbability_eq_kernel {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    placementProbability H z x y =
      bijectionKernel (conditionalChoiceWeight H z) (placementBijection H k) x y := by
  unfold placementProbability bijectionKernel
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> rfl

lemma placementProbability_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    0 ≤ placementProbability H z x y := by
  rw [placementProbability_eq_kernel]
  exact bijectionKernel_nonneg _ _ (conditionalChoiceWeight_nonneg H hz hz1) x y

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathExtension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

namespace PathExtension
variable {b h h' : ℕ} {bits : Fin b → ℕ}
  {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma lineInput_eq (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j)
    (i : LinePaths H j y) :
    lineInput H' j y (E.lineEmbedding j y i) = lineInput H j y i := by
  change H'.position j.castSucc (E.labels i.val) j = H.position j.castSucc i.val j
  rw [E.position_eq]

lemma lineOutput_eq (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j)
    (i : LinePaths H j y) :
    lineOutput H' j y (E.lineEmbedding j y i) = lineOutput H j y i := by
  change H'.position j.succ (E.labels i.val) j = H.position j.succ i.val j
  rw [E.position_eq]

end PathExtension

lemma localPathWeight_pos_comparison {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (j : Fin b) (y : GridOutside bits j) : 0 < localPathWeight H z j y := by
  unfold localPathWeight
  have hw := @assignmentWeight_comparison (Slot (bits j)) (LinePaths H j y) _ _
    (lineLaw (bits j) z) ?_ ?_ (lineInput H j y) (lineOutput H j y)
  · have hm : 0 < (Nat.descFactorial (Fintype.card (Slot (bits j)))
        (Fintype.card (LinePaths H j y)) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.mpr
        (Fintype.card_le_of_injective (lineInput H j y) (lineInput H j y).injective)
    exact lt_of_lt_of_le (by positivity) hw.1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).2

lemma lineExtension_log_bound {b h h' r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (j : Fin b) (y : GridOutside bits j) :
    Real.log (localPathWeight H' z j y / localPathWeight H z j y) ≤
      fallingCost (2^bits j) (lineHoles H' j y) - fallingCost (2^bits j) (lineHoles H j y) -
      ((lineHoles H' j y : ℝ) - lineHoles H j y) * Real.log (2^bits j : ℕ) +
      Real.log 4 * ((lineHoles H' j y : ℝ) - lineHoles H j y) := by
  have he := @assignmentWeight_log_ratio_le (Slot (bits j)) (LinePaths H j y)
    (LinePaths H' j y) _ _ _ Fintype.card_pos (lineLaw (bits j) z)
    ?_ ?_ (lineInput H j y) (lineOutput H j y) (lineInput H' j y) (lineOutput H' j y)
      (E.lineEmbedding j y) (E.lineInput_eq j y) (E.lineOutput_eq j y)
  · simpa only [localPathWeight, lineHoles, Slot, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool] using he
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).2

lemma log_gridSize {b : ℕ} (bits : Fin b → ℕ) :
    Real.log (gridSize bits : ℝ) = ∑ j, Real.log (2^bits j : ℕ) := by
  unfold gridSize
  rw [Nat.cast_prod, Real.log_prod]
  intro j _
  positivity

lemma sum_lineHoles_sub {b h h' : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (H' : PathFamily bits h') (j : Fin b) :
    ∑ y : GridOutside bits j, ((lineHoles H' j y : ℝ) - lineHoles H j y) = (h' : ℝ) - h := by
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, sum_lineHoles, sum_lineHoles]

lemma pathCost_eq_sum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    pathCost H = ∑ j, ∑ y, fallingCost (2^bits j) (lineHoles H j y) := rfl

theorem pathExtension_log_ratio {b h h' r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) :
    Real.log (conditionalNormalizer H' z / conditionalNormalizer H z) ≤
      pathCost H' - pathCost H - ((h' : ℝ) - h) * Real.log (gridSize bits) +
        Real.log 4 * ((h' : ℝ) - h) * b := by
  have hposH := localPathWeight_pos_comparison H hd hz hzr
  have hposH' := localPathWeight_pos_comparison H' hd hz hzr
  rw [conditionalNormalizer_eq_prod, conditionalNormalizer_eq_prod]
  rw [← Finset.prod_div_distrib]
  simp_rw [← Finset.prod_div_distrib]
  rw [Real.log_prod (fun j _ => Finset.prod_ne_zero_iff.mpr (fun y _ =>
    (div_pos (hposH' j y) (hposH j y)).ne'))]
  simp_rw [Real.log_prod (fun y _ => (div_pos (hposH' _ y) (hposH _ y)).ne')]
  calc
    _ ≤ ∑ j, ∑ y,
        (fallingCost (2^bits j) (lineHoles H' j y) - fallingCost (2^bits j) (lineHoles H j y) -
        ((lineHoles H' j y : ℝ) - lineHoles H j y) * Real.log (2^bits j : ℕ) +
        Real.log 4 * ((lineHoles H' j y : ℝ) - lineHoles H j y)) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun y _ => lineExtension_log_bound E hd hz hzr j y)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
      simp_rw [sum_lineHoles_sub]
      rw [pathCost_eq_sum, pathCost_eq_sum, log_gridSize]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring

lemma pathExtension_event_ratio {b h h' : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H') (z : ℝ) :
    conditionalEventWeight H z (pathEvent H') =
      conditionalNormalizer H' z / conditionalNormalizer H z := by
  unfold conditionalEventWeight conditionalChoiceWeight
  have hdiv (g : ConditionalChoices H) :
      (if pathEvent H' g.val then gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (if pathEvent H' g.val then gridWeight bits z g.val else 0) / conditionalNormalizer H z := by
    split_ifs <;> simp only [zero_div]
  simp_rw [hdiv]
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter (pathEvent H)) (by simp)
    (fun g => if pathEvent H' g then gridWeight bits z g else 0)]
  rw [Finset.sum_filter]
  unfold conditionalNormalizer
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : pathEvent H' g
  · simp only [hg, E.pathEvent_mono hg, ite_true]
  · simp only [hg, ite_false, ite_self]

lemma gridSize_pos {b : ℕ} (bits : Fin b → ℕ) : 0 < gridSize bits := by
  unfold gridSize
  exact Finset.prod_pos (fun j _ => Nat.pow_pos (by norm_num))

theorem pathExtension_probability_bound {b h k r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits (h+k)} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) :
    conditionalEventWeight H z (pathEvent H') ≤
      (gridSize bits : ℝ) ^ (-(k : ℝ)) *
        Real.exp (pathCost H' - pathCost H + Real.log 4 * k * b) := by
  rw [pathExtension_event_ratio E]
  have hp : 0 < conditionalNormalizer H' z / conditionalNormalizer H z := by
    rw [conditionalNormalizer_eq_prod, conditionalNormalizer_eq_prod]
    apply div_pos <;> apply Finset.prod_pos <;> intro j _ <;>
      apply Finset.prod_pos <;> intro y _
    · exact localPathWeight_pos_comparison H' hd hz hzr j y
    · exact localPathWeight_pos_comparison H hd hz hzr j y
  have hs : (0 : ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  have he := pathExtension_log_ratio E hd hz hzr
  simp only [Nat.cast_add, add_sub_cancel_left] at he
  calc
    _ ≤ Real.exp (pathCost H' - pathCost H - (k : ℝ) * Real.log (gridSize bits) +
        Real.log 4 * k * b) := (Real.log_le_iff_le_exp hp).mp he
    _ = _ := by
      rw [Real.rpow_def_of_pos hs, ← Real.exp_add]
      congr 1
      ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ComplementBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h h' : ℕ} {bits : Fin b → ℕ}
variable {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma PathExtension.sum_restrict {V : Type*} [AddCommMonoid V]
    (E : PathExtension H H') (f : ConditionalChoices H' → V) :
    (∑g : ConditionalChoices H,
      if hg : pathEvent H' g.val then f ⟨g.val,hg⟩ else 0) =
      ∑g : ConditionalChoices H',f g := by
  have hL := sum_dite_zero (pathEvent H)
    (fun (g : GridChoices bits) (_ : pathEvent H g) =>
      if hg' : pathEvent H' g then f ⟨g,hg'⟩ else 0)
  have hR := sum_dite_zero (pathEvent H') (fun g hg => f ⟨g,hg⟩)
  refine Eq.trans ?_ (Eq.trans hL.symm (Eq.trans ?_ (Eq.trans hR ?_)))
  · apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro g _
    by_cases hg : pathEvent H' g
    · simp only [hg,E.pathEvent_mono hg,dite_eq_left]
    · simp [hg]
  · apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _
    rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_Trajectory
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma placementProbability_augmentation {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H z x (placementBijection H k g x) =
      conditionalEventWeight H z (pathEvent (augmentByChoice H x g)) := by
  unfold placementProbability conditionalEventWeight
  apply Finset.sum_congr rfl
  intro g' _
  simp only [placementEvent_iff_augmentation]

theorem placement_probability_cost {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H z x (placementBijection H k g x) ≤
      (gridSize bits : ℝ) ^ (-(k : ℝ)) *
        Real.exp (pathCost (augmentByChoice H x g) - pathCost H + Real.log 4 * k * b) := by
  rw [placementProbability_augmentation]
  exact pathExtension_probability_bound (augmentByChoice_extension H x g) hd hz hzr

lemma realizePlacement_spec {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    placementBijection H k (realizePlacement H z x y hp) x = y :=
  Classical.choose_spec (placementProbability_pos_has_choice H z x y hp)

theorem placement_probability_cost_of_pos {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    {k : ℕ} (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    placementProbability H z x y ≤ (gridSize bits : ℝ) ^ (-(k : ℝ)) *
      Real.exp (placementTransitionCost H z x y - pathCost H + Real.log 4 * k * b) := by
  have he := placement_probability_cost H hd hz hzr x (realizePlacement H z x y hp)
  unfold placementTransitionCost
  rw [dite_eq_left hp]
  rwa [realizePlacement_spec] at he

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungDominance
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  have he : (Finset.univ.filter (fun x : Cell μ => row x < k+1)) =
      (Finset.univ.filter (fun x : Cell μ => row x < k)) ∪
      (Finset.univ.filter (fun x : Cell μ => row x = k)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.univ.filter (fun x : Cell μ => row x < k))
      (Finset.univ.filter (fun x : Cell μ => row x = k)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    omega
  rw [rowPrefix, he, Finset.card_union_of_disjoint hd]
  congr 1
  rw [YoungDiagram.rowLen_eq_card]
  apply Finset.card_bij (fun (x : Cell μ) _ => x.val)
  · intro x hx
    rw [YoungDiagram.mem_row_iff]
    exact ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    have h := YoungDiagram.mem_row_iff.mp hx
    exact ⟨⟨x, h.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h.2, rfl⟩

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable {μ ν : YoungDiagram}

lemma spechtInclude_column_sum :
    (∑ c : C μ, signC μ c.val • spechtRep μ c.val (spechtPoly μ)) =
      (Fintype.card (C μ) : ℂ) • spechtPoly μ := by
  apply spechtInclude_injective μ
  simp only [map_sum, map_smul, spechtInclude_rep, spechtInclude_poly]
  simpa only [columnAnti_apply] using columnAnti_polytabloid μ

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

variable {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]

omit [Fintype X] [DecidableEq X] [Fintype J] in
lemma movePlacement_mul (g h : Equiv.Perm X) (x : J ↪ X) :
    movePlacement (g*h) x = movePlacement g (movePlacement h x) := rfl

lemma placementRep_basis (g : Equiv.Perm X) (x : J ↪ X) :
    placementRep (X := X) (J := J) g (Pi.single x (1 : ℂ)) =
      (Pi.single (movePlacement g x) (1 : ℂ) : (J ↪ X) → ℂ) := by
  ext y
  change (Pi.single x (1 : ℂ) : (J ↪ X) → ℂ) (movePlacement g⁻¹ y) = _
  simp only [Pi.single_apply]
  have he : movePlacement g⁻¹ y = x ↔ y = movePlacement g x := by
    constructor <;> intro h
    · have hh := congrArg (movePlacement g) h
      simpa only [← movePlacement_mul, mul_inv_cancel, movePlacement_one] using hh
    · subst y
      simp only [← movePlacement_mul, inv_mul_cancel, movePlacement_one]
  simp only [he]

variable (μ : YoungDiagram)

lemma perm_same_tail_tabloid (g h : G μ)
    (he : ∀ x : Tail μ, g x.val = h x.val) : tabloidOfPerm μ g = tabloidOfPerm μ h := by
  apply (tabloidOfPerm_eq_iff μ _ _).mpr
  intro x
  by_cases hx : row x ≠ 0
  · have hh := he ⟨x,hx⟩
    change row (g⁻¹ (h x)) = row x
    rw [← hh]
    exact congrArg row (g.symm_apply_apply x)
  · have hx0 : row x = 0 := not_ne_iff.mp hx
    change row (g⁻¹ (h x)) = row x
    rw [hx0]
    by_contra hr
    have hh := he ⟨g⁻¹ (h x),hr⟩
    change g (g.symm (h x)) = _ at hh
    rw [g.apply_symm_apply] at hh
    have hh' : x = g⁻¹ (h x) := h.injective hh
    exact hr (hh' ▸ hx0)

lemma placementTabloid_eq (x : Tail μ ↪ Cell μ) (g : G μ)
    (hg : ∀ a : Tail μ, g a.val = x a) : placementTabloid μ x = tabloidOfPerm μ g := by
  apply perm_same_tail_tabloid
  intro a
  rw [(placement_extends μ x).choose_spec, hg]

lemma placementTabloid_surjective : Function.Surjective (placementTabloid μ) := by
  intro t
  obtain ⟨g,rfl⟩ := tabloidOfPerm_surjective μ t
  exact ⟨⟨fun a => g a.val, g.injective.comp Subtype.val_injective⟩,
    placementTabloid_eq μ _ g (fun _ => rfl)⟩

lemma placementTabloid_move (g : G μ) (x : Tail μ ↪ Cell μ) :
    placementTabloid μ (movePlacement g x) = g • placementTabloid μ x := by
  obtain ⟨h,hh⟩ := placement_extends μ x
  rw [placementTabloid_eq μ x h hh, smul_tabloidOfPerm]
  apply placementTabloid_eq
  intro a
  change g (h a.val) = g (x a)
  rw [hh]

lemma spechtPlacement_injective : Function.Injective (spechtPlacement μ) := by
  intro v w h
  apply spechtInclude_injective μ
  ext t
  obtain ⟨x,rfl⟩ := placementTabloid_surjective μ t
  exact congrFun h x

lemma spechtPlacement_intertwines (g : G μ) (v : SpechtSpace μ) :
    spechtPlacement μ (spechtRep μ g v) = placementRep g (spechtPlacement μ v) := by
  ext x
  change spechtInclude μ (spechtRep μ g v) (placementTabloid μ x) =
    spechtInclude μ v (placementTabloid μ (movePlacement g⁻¹ x))
  rw [spechtInclude_rep, placementTabloid_move]
  rfl

lemma card_tail : Fintype.card (Tail μ) = Fintype.card (Cell μ) - μ.rowLen 0 := by
  rw [Fintype.card_subtype_compl]
  congr 1
  rw [Fintype.card_subtype]
  have h := rowPrefix_succ μ 0
  simpa [rowPrefix] using h

lemma col_lt_firstRow (x : Cell μ) : col x < μ.rowLen 0 := by
  exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp x.property)
    (μ.rowLen_anti 0 (row x) (Nat.zero_le _))

lemma placement_column_collision (x : J ↪ Cell μ)
    (hj : Fintype.card J < Fintype.card (Cell μ) - μ.rowLen 0) :
    ∃ a b : Cell μ, a ≠ b ∧ a ∉ Set.range x ∧ b ∉ Set.range x ∧ col a = col b := by
  classical
  by_contra hn
  have hinj : Function.Injective (fun a : {a : Cell μ // a ∉ Set.range x} =>
      (⟨col a.val, col_lt_firstRow μ a.val⟩ : Fin (μ.rowLen 0))) := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    exact hn ⟨a.val,b.val,hne,a.property,b.property,congrArg Fin.val hab⟩
  have hh := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin] at hh
  have hjn : Fintype.card J ≤ Fintype.card (Cell μ) := Fintype.card_le_of_injective x x.injective
  omega

section ColumnSum
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma columnSum_apply (ρ : Representation ℂ (G μ) V) (v : V) :
    columnSum μ ρ v = ∑ c : C μ, signC μ c.val • ρ c.val v := by
  simp [columnSum, LinearMap.sum_apply]

lemma columnSum_rep (ρ : Representation ℂ (G μ) V) (c : C μ) (v : V) :
    columnSum μ ρ (ρ c.val v) = signC μ c.val • columnSum μ ρ v := by
  rw [columnSum_apply, columnSum_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val • (signC μ d.val • ρ d.val v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • ρ d.val (ρ c.val v) =
    signC μ c.val • (signC μ (d * c).val • ρ (d * c).val v)
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

end ColumnSum

lemma columnSum_placement_zero
    (hj : Fintype.card J < Fintype.card (Cell μ) - μ.rowLen 0) :
    columnSum μ (placementRep (X := Cell μ) (J := J)) = 0 := by
  have hb (x : J ↪ Cell μ) : columnSum μ placementRep (Pi.single x (1 : ℂ)) = 0 := by
    obtain ⟨a,b,hne,ha,hb,hcol⟩ := placement_column_collision μ x hj
    let c : C μ := ⟨Equiv.swap a b, swap_mem_fiber _ hcol⟩
    have hf : movePlacement c.val x = x := by
      apply Function.Embedding.ext
      intro j
      change Equiv.swap a b (x j) = x j
      apply Equiv.swap_apply_of_ne_of_ne
      · exact fun h => ha ⟨j,h⟩
      · exact fun h => hb ⟨j,h⟩
    have he := columnSum_rep μ placementRep c (Pi.single x (1 : ℂ))
    rw [placementRep_basis, hf, show signC μ c.val = -1 from signC_swap μ hne,
      neg_one_smul] at he
    ext y
    have hy := congrFun he y
    simp only [Pi.neg_apply] at hy
    change columnSum μ placementRep (Pi.single x (1 : ℂ)) y = 0
    linear_combination (1/2 : ℂ) * hy
  apply LinearMap.ext
  intro v
  have hv : v = ∑ x : J ↪ Cell μ, v x • Pi.single x (1 : ℂ) := by
    ext y
    simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, hb, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

theorem no_short_placement_intertwiner
    (hj : Fintype.card J < Fintype.card (Cell μ) - μ.rowLen 0)
    (f : SpechtSpace μ →ₗ[ℂ] ((J ↪ Cell μ) → ℂ))
    (hf : ∀ g v, f (spechtRep μ g v) = placementRep g (f v)) : f = 0 := by
  have he : columnSum μ placementRep (f (spechtPoly μ)) =
      (Fintype.card (C μ) : ℂ) • f (spechtPoly μ) := by
    rw [columnSum_apply]
    simp_rw [← hf]
    have hh := congrArg f (spechtInclude_column_sum (μ := μ))
    simpa only [map_sum, map_smul] using hh
  rw [columnSum_placement_zero μ hj, LinearMap.zero_apply] at he
  have hp : f (spechtPoly μ) = 0 := (smul_eq_zero.mp he.symm).resolve_left
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let f' := f.intertwiningMap_of_isIntertwiningMap (spechtRep μ) placementRep hf
  rcases Representation.IsIrreducible.injective_or_eq_zero (k := ℂ) (G := G μ)
      (V := SpechtSpace μ) (W := (J ↪ Cell μ) → ℂ) f' with hinj | hz
  · exact False.elim (spechtPoly_ne_zero μ (hinj (hp.trans f.map_zero.symm)))
  · exact congrArg (fun g => g.toLinearMap) hz

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_AugmentedComplement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

omit [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] in
lemma subPlacement_move (A : Finset I) (g : Equiv.Perm X) (x : I ↪ X) :
    subPlacement A (movePlacement g x)=movePlacement g (subPlacement A x) := rfl

omit [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] in
lemma move_sub_eq_iff (A : Finset I) (g : Equiv.Perm X)
    (x : I ↪ X) (u : A ↪ X) :
    subPlacement A (movePlacement g x)=u ↔ subPlacement A x=movePlacement g⁻¹ u := by
  rw [subPlacement_move]
  constructor
  · intro h
    have he := congrArg (movePlacement g⁻¹) h
    simpa only [← movePlacement_mul,inv_mul_cancel,movePlacement_one] using he
  · intro h
    rw [h,← movePlacement_mul,mul_inv_cancel,movePlacement_one]

omit [DecidableEq I] in
lemma placementMarginal_intertwines (A : Finset I) (g : Equiv.Perm X)
    (v : (I ↪ X) → ℂ) :
    placementMarginal A (placementRep g v)=placementRep g (placementMarginal A v) := by
  funext u
  change (∑x : I ↪ X, if subPlacement A x=u then v (movePlacement g⁻¹ x) else 0) =
    ∑x : I ↪ X, if subPlacement A x=movePlacement g⁻¹ u then v x else 0
  rw [← (placementMoveEquiv (I:=I) g).sum_comp
    (fun x => if subPlacement A x=u then v (movePlacement g⁻¹ x) else 0)]
  apply Finset.sum_congr rfl
  intro x _
  change (if subPlacement A (movePlacement g x)=u then
    v (movePlacement g⁻¹ (movePlacement g x)) else 0)=_
  simp only [move_sub_eq_iff,← movePlacement_mul,inv_mul_cancel,movePlacement_one]

variable (μ : YoungDiagram)

theorem spechtPlacement_marginal_zero (A : Finset (Tail μ))
    (hA : A≠Finset.univ) (v : SpechtSpace μ) :
    placementMarginal A (spechtPlacement μ v)=0 := by
  let f := (placementMarginal A).comp (spechtPlacement μ)
  have hcard : Fintype.card A < Fintype.card (Cell μ) - μ.rowLen 0 := by
    rw [← card_tail]
    simp only [Fintype.card_coe]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA)
  have hf : ∀g w, f (spechtRep μ g w)=placementRep g (f w) := by
    intro g w
    simp only [f,LinearMap.comp_apply,spechtPlacement_intertwines,placementMarginal_intertwines]
  have he := no_short_placement_intertwiner μ hcard f hf
  exact congrArg (fun f => f v) he

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_MatrixProjection
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma trace_toEuclideanLinear (M : Matrix I I ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ I) M.toEuclideanLin = M.trace := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun I ℂ)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  simp [EuclideanSpace.basisFun_apply, PiLp.inner_apply, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, PiLp.ofLp_single, Matrix.mulVec, dotProduct, Pi.single_apply]

end BinaryCoordinateSweeps.Density

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_CenteredPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

omit [DecidableEq I] [Fintype X] [DecidableEq X] in
lemma subPlacement_univ_injective :
    Function.Injective (subPlacement (X:=X) (Finset.univ : Finset I)) := by
  intro x y he
  ext i
  exact congrArg (fun t => t ⟨i,Finset.mem_univ _⟩) he

omit [DecidableEq I] in
lemma partialPlacement_apply (A : Finset I) (g : Equiv.Perm X)
    (v : (I ↪ X) → ℂ) (y : I ↪ X) :
    partialPlacement A g v y = ∑x : I ↪ X,
      if subPlacement A (movePlacement g x)=subPlacement A y then v x else 0 := by
  simp only [partialPlacement,placementMarginal,LinearMap.coe_mk,AddHom.coe_mk,
    move_sub_eq_iff]

omit [DecidableEq I] in
lemma partialPlacement_univ (g : Equiv.Perm X) :
    partialPlacement (Finset.univ : Finset I) g = placementRep g := by
  apply LinearMap.ext
  intro v
  funext y
  change (∑x : I ↪ X,
    if subPlacement Finset.univ x=movePlacement g⁻¹ (subPlacement Finset.univ y)
    then v x else 0)=v (movePlacement g⁻¹ y)
  simp only [← subPlacement_move,subPlacement_univ_injective.eq_iff]
  simp

lemma partialPlacement_specht_zero (μ : YoungDiagram) (A : Finset (Tail μ))
    (hA : A≠Finset.univ) (g : G μ) (v : SpechtSpace μ) :
    partialPlacement A g (spechtPlacement μ v)=0 := by
  ext y
  change placementMarginal A (spechtPlacement μ v) _=0
  rw [spechtPlacement_marginal_zero μ A hA]
  rfl

lemma partialPlacementAverage_specht_zero (μ : YoungDiagram) (A : Finset (Tail μ))
    (hA : A≠Finset.univ) (p : G μ → ℂ) (v : SpechtSpace μ) :
    partialPlacementAverage A p (spechtPlacement μ v)=0 := by
  simp only [partialPlacementAverage,LinearMap.sum_apply,LinearMap.smul_apply,
    partialPlacement_specht_zero μ A hA,smul_zero,Finset.sum_const_zero]

theorem centeredPlacement_specht (μ : YoungDiagram) (s : ℂ) (hs : s≠0)
    (p : G μ → ℂ) (v : SpechtSpace μ) :
    centeredPlacement s p (spechtPlacement μ v) =
      placementAverage p (spechtPlacement μ v) := by
  unfold centeredPlacement
  simp only [LinearMap.sum_apply,LinearMap.smul_apply]
  rw [Finset.sum_eq_single Finset.univ]
  · simp only [Finset.card_univ,Nat.sub_self,pow_zero,one_mul,
      div_self (pow_ne_zero _ hs),one_smul,partialPlacementAverage,
      partialPlacement_univ,placementAverage,LinearMap.sum_apply,LinearMap.smul_apply]
  · intro A _ hA
    rw [partialPlacementAverage_specht_zero μ A hA,smul_zero]
  · intro hn
    exact (hn (Finset.mem_powerset.mpr (Finset.Subset.refl _))).elim

lemma placementAverage_specht (μ : YoungDiagram) (p : G μ → ℂ) (v : SpechtSpace μ) :
    placementAverage p (spechtPlacement μ v)=
      spechtPlacement μ (∑g, p g • spechtRep μ g v) := by
  simp only [placementAverage,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    spechtPlacement_intertwines]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

omit [DecidableEq I] in
lemma partialKernel_toLin (A : Finset I) (g : Equiv.Perm X) :
    (partialKernel A g).toEuclideanLin=partialHilbert A g := by
  apply LinearMap.ext
  intro v
  apply (placementCoeffs (I:=I) (X:=X)).injective
  funext y
  change (∑x, partialKernel A g y x*v x)=partialPlacement A g (placementCoeffs v) y
  rw [partialPlacement_apply]
  apply Finset.sum_congr rfl
  intro x _
  dsimp [partialKernel]
  split_ifs <;> simp [placementCoeffs]

omit [Fintype I] [DecidableEq I] [Fintype X] in
lemma partialKernel_adjoint (A : Finset I) (g : Equiv.Perm X) :
    (partialKernel A g).conjTranspose=partialKernel A g⁻¹ := by
  ext y x
  have he : subPlacement A (movePlacement g y)=subPlacement A x ↔
      subPlacement A (movePlacement g⁻¹ x)=subPlacement A y := by
    rw [move_sub_eq_iff,← subPlacement_move]
    exact eq_comm
  simp only [Matrix.conjTranspose_apply,partialKernel,he]
  split_ifs <;> simp

omit [DecidableEq I] in
lemma partialHilbert_adjoint (A : Finset I) (g : Equiv.Perm X) :
    (partialHilbert A g).adjoint=partialHilbert A g⁻¹ := by
  rw [← partialKernel_toLin,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    partialKernel_adjoint,partialKernel_toLin]

omit [DecidableEq I] in
lemma centeredHilbert_sum (s : ℝ) (p : Equiv.Perm X → ℂ) :
    centeredHilbert (I:=I) s p = ∑A ∈ (Finset.univ : Finset I).powerset,
      ((-1:ℂ)^(Fintype.card I-A.card)*(s:ℂ)^A.card/(s:ℂ)^Fintype.card I) •
        ∑g, p g • partialHilbert A g := by
  simp only [centeredHilbert,centeredPlacement,partialPlacementAverage,map_sum,map_smul,
    partialHilbert]

omit [DecidableEq I] in
lemma centeredHilbert_adjoint (s : ℝ) (p : Equiv.Perm X → ℂ) :
    (centeredHilbert (I:=I) s p).adjoint=centeredHilbert s (fun g => star (p g⁻¹)) := by
  simp only [centeredHilbert_sum,map_sum,map_smulₛₗ,partialHilbert_adjoint,
    map_div₀,map_mul,map_pow,map_neg,map_one,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  have he := Equiv.sum_comp (Equiv.inv (Equiv.Perm X)) (fun g => star (p g⁻¹) • partialHilbert A g)
  simp only [starRingEnd_apply]
  simpa only [Equiv.inv_apply,inv_inv] using he

lemma spechtPlacementHilbert_injective (μ : YoungDiagram) :
    Function.Injective (spechtPlacementHilbert μ) :=
  placementCoeffs.symm.injective.comp ((spechtPlacement_injective μ).comp (spechtHilbertEquiv μ).symm.injective)

lemma centeredHilbert_specht (μ : YoungDiagram) (s : ℝ) (hs : s≠0)
    (p : G μ → ℂ) (v : SpechtHilbert μ) :
    centeredHilbert s p (spechtPlacementHilbert μ v)=
      spechtPlacementHilbert μ (Irrep.groupAverage (hilbertSpecht μ) p v) := by
  obtain ⟨u,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  apply placementCoeffs.injective
  simp only [centeredHilbert,spechtPlacementHilbert,LinearMap.comp_apply,
    LinearEquiv.conj_apply,LinearEquiv.coe_coe,LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
  change centeredPlacement (s:ℂ) p (spechtPlacement μ u)=
    spechtPlacement μ ((spechtHilbertEquiv μ).symm (Irrep.groupAverage (hilbertSpecht μ) p
      (spechtHilbertEquiv μ u)))
  rw [centeredPlacement_specht μ _ (by exact_mod_cast hs),placementAverage_specht]
  congr 1
  simp only [Irrep.groupAverage,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change spechtRep μ g u=(spechtHilbertEquiv μ).symm
    ((spechtHilbertEquiv μ) (spechtRep μ g ((spechtHilbertEquiv μ).symm ((spechtHilbertEquiv μ) u))))
  simp only [LinearEquiv.symm_apply_apply]

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_CenteredMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

lemma groupAverage_adjoint (ρ : Representation ℂ G V)
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (p : G → ℂ) :
    (groupAverage ρ p).adjoint=groupAverage ρ (fun g => star (p g⁻¹)) := by
  simp only [groupAverage,map_sum,map_smulₛₗ,unitary_rep_adjoint ρ hρ,starRingEnd_apply]
  have he := Equiv.sum_comp (Equiv.inv G) (fun g => star (p g⁻¹) • ρ g)
  simpa only [Equiv.inv_apply,inv_inv] using he

lemma even_compatible_maps (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (f : V →ₗ[ℂ] W) (hf : ∀v, B (f v)=f (A v))
    (hs : ∀v, B.adjoint (f v)=f (A.adjoint v)) (q : ℕ) (v : V) :
    ((B.adjoint*B)^q) (f v)=f (((A.adjoint*A)^q) v) := by
  induction q generalizing v with
  | zero => simp
  | succ q ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,ih]
    rw [Module.End.mul_apply,hf,hs]
    rfl

theorem evenMoment_le_of_injective (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (f : V →ₗ[ℂ] W) (hi : Function.Injective f)
    (hf : ∀v, B (f v)=f (A v)) (hs : ∀v, B.adjoint (f v)=f (A.adjoint v)) (q : ℕ) :
    evenMoment q A ≤ evenMoment q B := by
  let S := LinearMap.range f
  let a := (A.adjoint*A)^q
  let b := (B.adjoint*B)^q
  have hb : ∀w∈S, b w∈S := by
    intro w hw
    obtain ⟨v,rfl⟩ := hw
    exact ⟨a v,(even_compatible_maps A B f hf hs q v).symm⟩
  let e : V ≃ₗ[ℂ] S := LinearEquiv.ofInjective f hi
  have he : e.symm.conj (b.restrict hb)=a := by
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (e.symm ((b.restrict hb) (e v)))=e (a v)
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact even_compatible_maps A B f hf hs q v
  have ht := LinearMap.trace_conj' (b.restrict hb) e.symm
  rw [he] at ht
  have hle := positive_trace_restrict_le S b
    (positive_pow (LinearMap.isPositive_adjoint_comp_self B) q) hb
  rw [← ht] at hle
  exact hle

end BinaryCoordinateSweeps.Irrep
namespace BinaryCoordinateSweeps.Young

theorem centeredHilbert_moment (μ : YoungDiagram) (s : ℝ) (hs : s≠0)
    (p : G μ → ℂ) (q : ℕ) :
    Irrep.evenMoment q (Irrep.groupAverage (hilbertSpecht μ) p) ≤
      Irrep.evenMoment q (centeredHilbert (I:=Tail μ) s p) := by
  apply Irrep.evenMoment_le_of_injective _ _ (spechtPlacementHilbert μ)
    (spechtPlacementHilbert_injective μ)
  · exact centeredHilbert_specht μ s hs p
  · intro v
    rw [centeredHilbert_adjoint,Irrep.groupAverage_adjoint _ (hilbertSpecht_unitary μ)]
    exact centeredHilbert_specht μ s hs _ v

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_CenteredMatrix
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

omit [DecidableEq I] in
lemma centeredMatrix_toLin (s : ℝ) (p : Equiv.Perm X → ℂ) :
    (centeredMatrix (I:=I) s p).toEuclideanLin=centeredHilbert s p := by
  simp only [centeredMatrix,map_sum,map_smul,partialKernel_toLin,centeredHilbert_sum]

lemma evenMoment_one_matrix {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J ℂ) : Irrep.evenMoment 1 M.toEuclideanLin = ∑x,∑y, ‖M y x‖^2 := by
  have hc (z : ℂ) : (star z*z).re=‖z‖^2 := by
    rw [Complex.star_def,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]
  unfold Irrep.evenMoment
  rw [pow_one,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,Module.End.mul_eq_comp,← Matrix.toLpLin_mul_same,
    Density.trace_toEuclideanLinear]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact hc (M y x)

theorem specht_moment_one_le_centered_matrix (μ : YoungDiagram) (s : ℝ) (hs : s≠0)
    (p : G μ → ℂ) :
    Irrep.evenMoment 1 (Irrep.groupAverage (hilbertSpecht μ) p) ≤
      ∑x : Tail μ ↪ Cell μ, ∑y, ‖centeredMatrix s p y x‖^2 := by
  have he := centeredHilbert_moment μ s hs p 1
  rw [← centeredMatrix_toLin,evenMoment_one_matrix] at he
  exact he

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_CenteredReindex
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I J X Y : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] in
lemma partialKernel_iff (A : Finset I) (g : Equiv.Perm X) (x y : I ↪ X) :
    subPlacement A (movePlacement g x)=subPlacement A y ↔ ∀i∈A, g (x i)=y i := by
  constructor
  · intro h i hi
    exact congrArg (fun u => u ⟨i,hi⟩) h
  · intro h
    apply Function.Embedding.ext
    intro i
    exact h i.val i.property

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X] [Fintype Y] in
lemma partialKernel_reindex (a : I ≃ J) (e : X ≃ Y) (A : Finset I)
    (g : Equiv.Perm X) (x y : I ↪ X) :
    partialKernel (a.finsetCongr A) (e.permCongr g)
      (Equiv.embeddingCongr a e y) (Equiv.embeddingCongr a e x)=partialKernel A g y x := by
  unfold partialKernel
  congr 1
  rw [partialKernel_iff,partialKernel_iff]
  apply propext
  constructor
  · intro he i hi
    have ht := he (a i) (by simpa using hi)
    simpa using ht
  · intro he j hj
    obtain ⟨i,rfl⟩ := a.surjective j
    have ht := he i (by simpa using hj)
    simpa using congrArg e ht

omit [DecidableEq I] [DecidableEq J] in
theorem centeredMatrix_reindex (a : I ≃ J) (e : X ≃ Y) (s : ℝ)
    (p : Equiv.Perm X → ℂ) (x y : I ↪ X) :
    centeredMatrix s (fun g => p (e.permCongr.symm g))
      (Equiv.embeddingCongr a e y) (Equiv.embeddingCongr a e x)=centeredMatrix s p y x := by
  simp only [centeredMatrix,Finset.powerset_univ,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  have ht := Equiv.sum_comp a.finsetCongr (fun A : Finset J =>
    ((-1:ℂ)^(Fintype.card J-A.card)*(s:ℂ)^A.card/(s:ℂ)^Fintype.card J) *
      ∑g, p (e.permCongr.symm g) * partialKernel A g
        (Equiv.embeddingCongr a e y) (Equiv.embeddingCongr a e x))
  rw [← ht]
  apply Finset.sum_congr rfl
  intro A _
  have hc : (a.finsetCongr A).card=A.card := by simp
  rw [hc,← Fintype.card_congr a]
  congr 1
  have hu := Equiv.sum_comp e.permCongr (fun g =>
    p (e.permCongr.symm g) * partialKernel (a.finsetCongr A) g
      (Equiv.embeddingCongr a e y) (Equiv.embeddingCongr a e x))
  rw [← hu]
  apply Finset.sum_congr rfl
  intro g _
  rw [Equiv.symm_apply_apply,partialKernel_reindex]

omit [DecidableEq I] [DecidableEq J] in
lemma centeredMatrix_hs_reindex (a : I ≃ J) (e : X ≃ Y) (s : ℝ)
    (p : Equiv.Perm X → ℂ) :
    (∑x : J ↪ Y, ∑y, ‖centeredMatrix s (fun g => p (e.permCongr.symm g)) y x‖^2)=
      ∑x : I ↪ X, ∑y, ‖centeredMatrix s p y x‖^2 := by
  rw [← Equiv.sum_comp (Equiv.embeddingCongr a e)]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Equiv.sum_comp (Equiv.embeddingCongr a e)]
  simp_rw [centeredMatrix_reindex]

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_PlacementAlternation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {I : Type*} [DecidableEq I]

lemma alternatingSubsetSum_of_isolated (U : Finset I) {s : ℝ} (hs : s≠0)
    (p : Finset I → ℝ) (i : I) (hi : i∈U)
    (hp : ∀A ⊆ U.erase i, p (insert i A)=s⁻¹*p A) :
    alternatingSubsetSum U s p=0 := by
  have hUi : U=insert i (U.erase i) := (Finset.insert_erase hi).symm
  have hn : i∉U.erase i := Finset.notMem_erase i U
  unfold alternatingSubsetSum
  rw [hUi,Finset.sum_powerset_insert hn,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro A hA
  have hAU : A⊆U.erase i := Finset.mem_powerset.mp hA
  have hiA : i∉A := fun h => hn (hAU h)
  have hcard := Finset.card_le_card hAU
  rw [Finset.card_insert_of_notMem hiA,hp A hAU]
  have he : (insert i (U.erase i)).card-A.card =
      ((insert i (U.erase i)).card-(A.card+1))+1 := by
    rw [Finset.card_insert_of_notMem hn]
    omega
  rw [he,pow_succ,pow_succ]
  simp only [mul_assoc]
  field_simp
  ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_FiniteProductProbability
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

omit [DecidableEq I] [Fintype Ω] in
lemma productWeight_nonneg {p : Ω → ℝ} (hp : ∀ u, 0 ≤ p u) (x : I → Ω) :
    0 ≤ productWeight p x := Finset.prod_nonneg (fun i _ => hp (x i))

lemma productWeight_sum (p : Ω → ℝ) (hp : ∑ u, p u = 1) :
    ∑ x : I → Ω, productWeight p x = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  simp [hp]

omit [DecidableEq I] in
lemma indicator_prod (P : I → Prop) :
    (∏ i, (if P i then (1:ℝ) else 0)) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq I] [Fintype Ω] in
lemma productWeight_split (p : Ω → ℝ) (T : I → Prop) [DecidablePred T]
    (u : {i // T i} → Ω) (v : {i // ¬ T i} → Ω) :
    productWeight p ((Equiv.piEquivPiSubtypeProd T (fun _ => Ω)).symm (u,v)) =
      productWeight p u * productWeight p v := by
  unfold productWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype T]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [Equiv.piEquivPiSubtypeProd_symm_apply,i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp [Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

lemma productProbability_mono {p : Ω → ℝ} (hp : ∀ u, 0 ≤ p u)
    {E F : (I → Ω) → Prop} (h : ∀ x, E x → F x) :
    productProbability p E ≤ productProbability p F := by
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (productWeight_nonneg hp x)
  by_cases hx : E x
  · simp [hx,h x hx]
  · simp [hx]; split_ifs <;> norm_num

lemma productProbability_union_le {J : Type*} [Fintype J] {p : Ω → ℝ}
    (hp : ∀ u, 0 ≤ p u) (E : J → (I → Ω) → Prop) :
    productProbability p (fun x => ∃ j, E j x) ≤ ∑ j, productProbability p (E j) := by
  unfold productProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (productWeight_nonneg hp x)
  by_cases h : ∃ j, E j x
  · obtain ⟨j,hj⟩ := h
    rw [ite_eq_left ⟨j,hj⟩]
    exact (show (1:ℝ) ≤ if E j x then 1 else 0 by simp [hj]).trans
      (Finset.single_le_sum (f:=fun i:J => if E i x then (1:ℝ) else 0) (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem depthOne_probability_le {H : Type*} [Fintype H]
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1)
    (R : Ω → Ω → Prop) (ω : ℝ) (_hω : 0 ≤ ω)
    (hR : ∀ v, (∑ u, p u * (if R u v then 1 else 0)) ≤ ω)
    (T : Finset I) (f : T → {i // i ∉ T} ⊕ H) (roots : H → Ω) :
    productProbability p (fun x : I → Ω => ∀ i : T, R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots)) ≤
      ω^T.card := by
  classical
  let : Fintype T := Subtype.fintype (fun i => i ∈ T)
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ T) (fun _ => Ω)
  unfold productProbability
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  have he (u : T → Ω) (v : {i // i ∉ T} → Ω) (i : T) :
      R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots) ↔
        R (u i) ((f i).elim v roots) := by
    cases hf : f i with
    | inl j => simp [e,Equiv.piEquivPiSubtypeProd_symm_apply,i.property,j.property]
    | inr h => simp [e,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]
  change (∑ v : {i // i ∉ T} → Ω, ∑ u : T → Ω,
    productWeight p (e.symm (u,v)) * _) ≤ _
  have hsplit (u : T → Ω) (v : {i // i ∉ T} → Ω) :
      productWeight p (e.symm (u,v)) = productWeight p u * productWeight p v := by
    exact productWeight_split p (fun i => i ∈ T) u v
  simp_rw [hsplit]
  have ht (v : {i // i ∉ T} → Ω) :
      (∑ u : T → Ω, productWeight p u *
        (if ∀ i : T, R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots)
          then 1 else 0)) ≤ ω^T.card := by
    simp_rw [he,← indicator_prod,productWeight,← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (i : T) (u : Ω) => p u * (if R u ((f i).elim v roots) then 1 else 0))]
    simpa using Finset.prod_le_prod (s:=Finset.univ) (fun i _ => Finset.sum_nonneg (fun u _ =>
      mul_nonneg (hp u) (by split_ifs <;> norm_num))) (fun i _ => hR ((f i).elim v roots))
  calc
    _ = ∑ v : {i // i ∉ T} → Ω, productWeight p v *
        (∑ u : T → Ω, productWeight p u *
          (if ∀ i : T, R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots)
            then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_assoc, mul_left_comm]
      congr 2
      simp only [he]
    _ ≤ ∑ v : {i // i ∉ T} → Ω, productWeight p v * ω^T.card :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (ht v) (productWeight_nonneg hp v))
    _ = ω^T.card := by rw [← Finset.sum_mul,productWeight_sum p hp1,one_mul]

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_SharingWitness
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I H : Type*} [Fintype I] [Fintype H] [DecidableEq I]

theorem sharing_witness (G : SimpleGraph I) (R : I → H → Prop) :
    let S := Finset.univ.filter (fun i => (∃ j, G.Adj i j) ∨ ∃ h, R i h)
    ∃ T : Finset I, T ⊆ S ∧ S.card ≤ 2*T.card ∧
      ∀ i ∈ T, (∃ j, j ∉ T ∧ G.Adj i j) ∨ ∃ h, R i h := by
  classical
  intro S
  obtain ⟨A,hA⟩ := G.maximumIndepSet_exists
  have hm := hA.isMaximalIndepSet A
  have hi := (G.isIndepSet_iff).mp hm.1
  have hn (i : I) (hiA : i ∉ A) : ∃ j ∈ A, G.Adj i j := by
    by_contra! h
    have hins : G.IsIndepSet (insert i (A : Set I)) := by
      apply G.isIndepSet_iff.mpr
      intro x hx y hy hxy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact h y hy
      · exact fun hadj => h x hx hadj.symm
      · exact hi hx hy hxy
    have hj := hm.2 hins (Set.subset_insert i (A : Set I)) (Set.mem_insert i (A : Set I))
    exact hiA hj
  have hcard := Finset.card_sdiff_add_card_inter S A
  by_cases hc : (S \ A).card ≤ (S ∩ A).card
  · refine ⟨S ∩ A,Finset.inter_subset_left,by omega,?_⟩
    intro i hiT
    obtain ⟨hiS, hiA⟩ := Finset.mem_inter.mp hiT
    obtain hiS | hiS := (Finset.mem_filter.mp hiS).2
    · obtain ⟨j,hij⟩ := hiS
      refine Or.inl ⟨j,?_,hij⟩
      intro hj
      exact hi hiA (Finset.mem_inter.mp hj).2 (G.ne_of_adj hij) hij
    · exact Or.inr hiS
  · refine ⟨S \ A,Finset.sdiff_subset,by omega,?_⟩
    intro i hiT
    obtain ⟨j,hj,hij⟩ := hn i (Finset.mem_sdiff.mp hiT).2
    exact Or.inl ⟨j,fun hjT => (Finset.mem_sdiff.mp hjT).2 hj,hij⟩

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_SharingProbability
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I H Ω : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype Ω]

omit [Fintype Ω] in
lemma sharing_depthOne (R : Ω → Ω → Prop)
    (hs : ∀ ⦃first second⦄, R first second → R second first)
    (roots : H → Ω) (x : I → Ω) (w : ℕ) (hw : w ≤ (incidentSet R roots x).card) :
    ∃ T : Finset I, w ≤ 2*T.card ∧
      ∃ f : T → {i // i ∉ T} ⊕ H, ∀ i : T,
        R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots) := by
  classical
  obtain ⟨T,_,hc,hT⟩ := sharing_witness (sharingGraph R hs x) (fun i h => R (x i) (roots h))
  have hc' : (incidentSet R roots x).card ≤ 2*T.card := by
    convert hc using 1
    congr 1
    ext i
    simp only [incidentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

  refine ⟨T,hw.trans hc',?_⟩
  have hp (i : T) : ∃ a : {i // i ∉ T} ⊕ H,
      R (x i) (a.elim (fun j : {i // i ∉ T} => x j.val) roots) := by
    obtain ⟨j,hj,hij⟩ | ⟨h,hi⟩ := hT i i.property
    · exact ⟨Sum.inl ⟨j,hj⟩,hij.2⟩
    · exact ⟨Sum.inr h,hi⟩
  choose f hf using hp
  exact ⟨f,hf⟩

theorem sharing_probability_le
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1)
    (R : Ω → Ω → Prop)
    (hs : ∀ ⦃first second⦄, R first second → R second first) (roots : H → Ω)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hR : ∀ v, (∑ u, p u * (if R u v then 1 else 0)) ≤ ω)
    (w : ℕ) (hsmall : ((Fintype.card I + Fintype.card H : ℕ) : ℝ)*ω ≤ 1) :
    productProbability p (fun x : I → Ω => w ≤ (incidentSet R roots x).card) ≤
      (2:ℝ)^Fintype.card I *
        (((Fintype.card I + Fintype.card H : ℕ):ℝ)*ω)^((w+1)/2) := by
  classical
  let E (T : Finset I) (f : T → {i // i ∉ T} ⊕ H) (x : I → Ω) :=
    ∀ i : T, R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots)
  let r : ℝ := ((Fintype.card I + Fintype.card H : ℕ):ℝ)*ω
  have hr : 0 ≤ r := mul_nonneg (Nat.cast_nonneg _) hω
  have hT (T : Finset I) : productProbability p (fun x => w ≤ 2*T.card ∧ ∃ f, E T f x) ≤
      r^((w+1)/2) := by
    by_cases hc : w ≤ 2*T.card
    · have h1 := productProbability_union_le hp (E T)
      have h2 : (∑ f, productProbability p (E T f)) ≤
          (Fintype.card (T → {i // i ∉ T} ⊕ H) : ℝ)*ω^T.card := by
        simpa [E] using Finset.sum_le_sum (s:=Finset.univ) (fun f _ => depthOne_probability_le p hp hp1 R ω hω hR T f roots)
      have hd : Fintype.card ({i // i ∉ T} ⊕ H) ≤ Fintype.card I + Fintype.card H := by
        rw [Fintype.card_sum]
        exact Nat.add_le_add_right (Fintype.card_subtype_le _) _
      have h3 : (Fintype.card (T → {i // i ∉ T} ⊕ H) : ℝ)*ω^T.card ≤ r^T.card := by
        rw [Fintype.card_fun,Fintype.card_coe,Nat.cast_pow]
        dsimp [r]
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hω _)
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hd) _
      have he : (w+1)/2 ≤ T.card := by omega
      simpa only [hc,true_and] using h1.trans (h2.trans (h3.trans
        (pow_le_pow_of_le_one hr hsmall he)))
    · simp only [hc,false_and,productProbability,ite_false,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hr _
  calc
    _ ≤ productProbability p (fun x => ∃ T : Finset I, w ≤ 2*T.card ∧ ∃ f, E T f x) :=
      productProbability_mono hp (fun x hx => sharing_depthOne R hs roots x w hx)
    _ ≤ ∑ T : Finset I, productProbability p (fun x => w ≤ 2*T.card ∧ ∃ f, E T f x) :=
      productProbability_union_le hp _
    _ ≤ ∑ T : Finset I, r^((w+1)/2) := Finset.sum_le_sum (fun T _ => hT T)
    _ = _ := by simp [r,Fintype.card_finset]

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_UniformFiniteProbability
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {Ω V W : Type*} [Fintype Ω] [Fintype V] [Fintype W]

lemma uniformWeight_nonneg (u : Ω) : 0 ≤ uniformWeight u := by
  unfold uniformWeight; positivity

lemma uniformWeight_sum [Nonempty Ω] : ∑ u : Ω, uniformWeight u = 1 := by
  simp [uniformWeight,ne_of_gt (Fintype.card_pos : 0 < Fintype.card Ω)]

lemma finiteProbability_union {T : Type*} [Fintype T]
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (E : T → Ω → Prop) :
    finiteProbability p (fun u => ∃ t, E t u) ≤ ∑ t, finiteProbability p (E t) := by
  unfold finiteProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hp u)
  by_cases h : ∃ t, E t u
  · obtain ⟨t,ht⟩ := h
    rw [ite_eq_left ⟨t,ht⟩]
    exact (show (1:ℝ) ≤ if E t u then 1 else 0 by simp [ht]).trans
      (Finset.single_le_sum (f:=fun t:T => if E t u then (1:ℝ) else 0)
        (fun t _ => by split_ifs <;> norm_num) (Finset.mem_univ t))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num)

lemma uniform_projection_probability [Nonempty W] (e : Ω ≃ V × W) (v : V) :
    finiteProbability uniformWeight (fun u => (e u).1 = v) = 1 / Fintype.card V := by
  classical
  unfold finiteProbability uniformWeight
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type,Fintype.card_congr e,Fintype.card_prod]
  have hW : (Fintype.card W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  simp [Nat.cast_mul]

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
namespace Sparse
variable {b : ℕ} {bits : Fin b → ℕ}

lemma independentPosition_changes (z : GridSlot bits × GridSlot bits) (j i : Fin b) (h : i≠j) :
    independentPosition z j.succ i=independentPosition z j.castSucc i := by
  have hn : i.val≠j.val := fun he => h (Fin.ext he)
  simp only [independentPosition,Fin.val_succ,Fin.val_castSucc]
  have he : i.val<j.val+1 ↔ i.val<j.val := by omega
  simp only [he]

lemma independentPosition_of_path (x : Fin (b+1) → GridSlot bits)
    (h : ∀(j i : Fin b), i≠j → x j.succ i=x j.castSucc i) (t : Fin (b+1)) :
    independentPosition (x 0,x (Fin.last b)) t=x t := by
  funext i
  exact (trajectory_coordinates x h t i).symm

lemma independent_line_uniform (j : Fin b) (y : GridOutside bits j) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      (fun i : {i : Fin b // i≠j} => independentPosition z j.castSucc i)=y)=
      1/Fintype.card (GridOutside bits j) := by
  exact uniform_projection_probability (endpointLineEquiv j) y

end Sparse
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_OneCard
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma coordinateLayer_apply_at (d : ℕ) (j : Fin d)
    (c : ({i : Fin d // i≠j} → Bool) → Bool) (x : Slot d) :
    coordinateLayer d j c x j = (x j ^^ c (fun i => x i)) := by
  simp [coordinateLayer,Equiv.piSplitAt_symm_apply]

lemma coordinateLayer_apply_other (d : ℕ) (j i : Fin d) (hi : i≠j)
    (c : ({i : Fin d // i≠j} → Bool) → Bool) (x : Slot d) :
    coordinateLayer d j c x i = x i := by
  simp [coordinateLayer,Equiv.piSplitAt_symm_apply,hi]

lemma binaryPartialSweep_succ (d : ℕ) (c : SweepCoins d) (j : Fin d) :
    binaryPartialSweep d c j.succ=coordinateLayer d j (c j)*binaryPartialSweep d c j.castSucc := by
  unfold binaryPartialSweep
  simp only [Fin.val_succ,Fin.val_castSucc]
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp only [List.reverse_append,List.reverse_singleton,List.prod_append,
    List.prod_singleton,List.getElem_ofFn,Fin.eta]

lemma singleCoordinate_trajectory {d : ℕ} {β : Fin d → Type*}
    (x : Fin (d+1) → ∀i, β i)
    (hmov : ∀j i : Fin d, i≠j → x j.succ i=x j.castSucc i)
    (t : Fin (d+1)) (i : Fin d) :
    x t i = if i.val<t.val then x (Fin.last d) i else x 0 i := by
  have hbefore : ∀t : Fin (d+1), t.val ≤ i.val → x t i=x 0 i := by
    intro t
    induction t using Fin.induction with
    | zero => intro _; rfl
    | succ j ih =>
      intro ht
      have hij : i≠j := by intro h; subst j; simp at ht
      rw [hmov j i hij,ih]
      exact Nat.le_trans (Nat.le_succ j.val) ht
  have hafter : ∀t : Fin (d+1), i.val<t.val → x t i=x (Fin.last d) i := by
    intro t
    induction t using Fin.reverseInduction with
    | last => intro _; rfl
    | cast j ih =>
      intro ht
      have hij : i≠j := by intro h; subst j; simp at ht
      rw [← hmov j i hij,ih]
      exact Nat.lt_succ_of_lt ht
  split_ifs with h
  · exact hafter t h
  · exact hbefore t (Nat.le_of_not_lt h)

lemma binarySweep_endpoint_iff (d : ℕ) (c : SweepCoins d) (x y : Slot d) :
    binarySweep d c x=y ↔ ∀j, c j (fun i => binaryPosition x y j.castSucc i)= (x j ^^ y j) := by
  constructor
  · intro he j
    have hp (t : Fin (d+1)) : binaryPartialSweep d c t x=binaryPosition x y t := by
      funext i
      rw [singleCoordinate_trajectory (fun t => binaryPartialSweep d c t x)
        (by intro j i hi; rw [binaryPartialSweep_succ,Equiv.Perm.mul_apply,
          coordinateLayer_apply_other d j i hi])]
      simp only [binaryPartialSweep_last,binaryPartialSweep_zero,Equiv.Perm.one_apply,he,binaryPosition]
    have hj := congrFun (hp j.succ) j
    rw [binaryPartialSweep_succ,Equiv.Perm.mul_apply,hp j.castSucc,coordinateLayer_apply_at] at hj
    simp only [binaryPosition,Fin.val_succ,Fin.val_castSucc,lt_self_iff_false,ite_false,
      Nat.lt_succ_self,ite_true] at hj
    cases hx : x j <;> cases hy : y j <;> cases hc : c j (fun i => binaryPosition x y j.castSucc i) <;>
      simp_all [binaryPosition]
  · intro he
    have hp (t : Fin (d+1)) : binaryPartialSweep d c t x=binaryPosition x y t := by
      induction t using Fin.induction with
      | zero => ext i; simp [binaryPosition]
      | succ j ih =>
        rw [binaryPartialSweep_succ,Equiv.Perm.mul_apply,ih]
        funext i
        by_cases hi : i=j
        · subst i
          rw [coordinateLayer_apply_at,he j]
          simp [binaryPosition]
        · rw [coordinateLayer_apply_other d j i hi]
          dsimp [binaryPosition]
          congr 1
          exact propext (by have hij : i.val≠j.val := fun h => hi (Fin.ext h); omega)
    have hy : binaryPosition x y (Fin.last d)=y := by ext i; simp [binaryPosition]
    simpa only [binaryPartialSweep_last,hy] using hp (Fin.last d)

lemma uniform_coin_evaluation {I : Type*} [Fintype I] [DecidableEq I] (i : I) (b : Bool) :
    (∑c : I → Bool, if c i=b then (Fintype.card (I → Bool):ℝ)⁻¹ else 0) = (1/2:ℝ) := by
  have h := Sparse.uniform_projection_probability (Equiv.piSplitAt i (fun _ : I => Bool)) b
  simpa only [Sparse.finiteProbability,Sparse.uniformWeight,Equiv.piSplitAt_apply,
    Fintype.card_bool,Nat.cast_ofNat,one_div,mul_ite,mul_one,mul_zero] using h

lemma uniform_independent_event {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    [∀j, Fintype (X j)] (P : ∀j, X j → Prop) :
    (∑x : ∀j, X j, if ∀j, P j (x j) then (Fintype.card (∀j, X j):ℝ)⁻¹ else 0) =
      ∏j, ∑a : X j, if P j a then (Fintype.card (X j):ℝ)⁻¹ else 0 := by
  have h := independent_event_weight (fun j (_ : X j) => (Fintype.card (X j):ℝ)⁻¹) P
  have hc : (∏j, (Fintype.card (X j):ℝ)⁻¹) = (Fintype.card (∀j, X j):ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib,← Nat.cast_prod,Fintype.card_pi]
  refine Eq.trans ?_ h
  apply Finset.sum_congr
  · ext x; simp only [Finset.mem_univ]
  intro x _
  split_ifs <;> simp only [hc]

lemma uniform_pi_coin_evaluation {J : Type*} [Fintype J] [DecidableEq J] {I : J → Type*}
    [∀j,Fintype (I j)] [∀j,DecidableEq (I j)] (i : ∀j,I j) (b : J → Bool) :
    (∑c : ∀j,I j → Bool, if ∀j,c j (i j)=b j then
      (Fintype.card (∀j,I j → Bool):ℝ)⁻¹ else 0) = (1/2:ℝ)^Fintype.card J := by
  have h := uniform_independent_event (X:=fun j => I j → Bool) (fun j a => a (i j)=b j)
  refine Eq.trans ?_ (Eq.trans h ?_)
  · apply Finset.sum_congr rfl
    intro c _
    by_cases hc : ∀j,c j (i j)=b j <;> simp [hc]
  · calc
      _ = ∏j, (1/2:ℝ) := by
        apply Finset.prod_congr rfl
        intro j _
        refine Eq.trans ?_ (uniform_coin_evaluation (i j) (b j))
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : c (i j)=b j <;> simp [hc]
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ]

lemma binary_one_card (d : ℕ) (x y : Slot d) :
    ∑σ, binaryLaw d σ * (if σ x=y then (1:ℝ) else 0) = (Fintype.card (Slot d):ℝ)⁻¹ := by
  rw [binaryLaw,finiteLaw_expectation]
  simp_rw [binarySweep_endpoint_iff]
  rw [Finset.mul_sum]
  simp only [mul_ite,mul_one,mul_zero]
  have h := uniform_pi_coin_evaluation (J:=Fin d)
    (I:=fun j => {i : Fin d // i≠j} → Bool)
    (fun j i => binaryPosition x y j.castSucc i) (fun j => (x j ^^ y j))
  have hc : (1/2:ℝ)^Fintype.card (Fin d) = (Fintype.card (Slot d):ℝ)⁻¹ := by
    simp [Slot,inv_pow,one_div]
  refine Eq.trans ?_ (h.trans hc)
  apply Finset.sum_congr
  · ext c; simp only [Finset.mem_univ]
  intro c _
  by_cases hh : ∀j, c j (fun i => binaryPosition x y j.castSucc i)= (x j ^^ y j)
  · simp only [hh]
  · simp only [hh,ite_false]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma uniform_one_card {X : Type*} [Fintype X] [DecidableEq X] (x y : X) :
    (∑σ : Equiv.Perm X, uniformLaw (Equiv.Perm X) σ * (if σ x=y then (1:ℝ) else 0)) =
      (Fintype.card X:ℝ)⁻¹ := by
  let A : Unit ↪ X := ⟨fun _ => x,fun _ _ _ => Subsingleton.elim _ _⟩
  let B : Unit ↪ X := ⟨fun _ => y,fun _ _ _ => Subsingleton.elim _ _⟩
  have h := assignmentWeight_uniform A B
  have he (σ : Equiv.Perm X) : Assigns A B σ ↔ σ x=y := by
    change (∀u : Unit, σ x=y) ↔ σ x=y
    simp only [forall_const]
  simp only [assignmentWeight,he,uniformLaw,mul_ite,mul_one,mul_zero,
    Fintype.card_unique,Nat.descFactorial_one] at h ⊢
  refine Eq.trans ?_ h
  apply Finset.sum_congr
  · ext σ; simp only [Finset.mem_univ]
  intro σ _
  split_ifs <;> simp only [Fintype.card_perm]

lemma line_one_card (d : ℕ) (z : ℝ) (x y : Slot d) :
    (∑σ, lineLaw d z σ * (if σ x=y then (1:ℝ) else 0)) = (Fintype.card (Slot d):ℝ)⁻¹ := by
  simp only [lineLaw,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [uniform_one_card (X:=Slot d) x y,binary_one_card d x y]
  ring

lemma line_one_card_ite (d : ℕ) (z : ℝ) (x y : Slot d) :
    (∑σ, if σ x=y then lineLaw d z σ else 0) = (Fintype.card (Slot d):ℝ)⁻¹ := by
  simpa only [mul_ite,mul_one,mul_zero] using line_one_card d z x y

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointEvents
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open Sparse

variable {b h : ℕ} {bits : Fin b → ℕ}

lemma endpoint_gridLayer_iff (g : GridChoices bits) (e : GridSlot bits × GridSlot bits) (j : Fin b) :
    gridLayer bits g j (independentPosition e j.castSucc)=independentPosition e j.succ ↔
      g j (endpointLine e j) (e.1 j)=e.2 j := by
  unfold endpointLine
  constructor
  · intro he
    have hh := congrFun he j
    simpa only [gridLayer_at,endpointLine,independentPosition,Fin.val_castSucc,
      Fin.val_succ,lt_self_iff_false,ite_false,Nat.lt_succ_self,ite_true] using hh
  · intro he
    funext i
    by_cases hi : i=j
    · subst i
      simpa only [gridLayer_at,endpointLine,independentPosition,Fin.val_castSucc,
        Fin.val_succ,lt_self_iff_false,ite_false,Nat.lt_succ_self,ite_true] using he
    · rw [gridLayer_other bits g j i hi]
      exact (independentPosition_changes e j i hi).symm

lemma gridSweep_endpoint_iff (g : GridChoices bits) (e : GridSlot bits × GridSlot bits) :
    gridSweep bits g e.1=e.2 ↔ ∀j, g j (endpointLine e j) (e.1 j)=e.2 j := by
  constructor
  · intro he j
    have hp (t : Fin (b+1)) : gridPartialSweep bits g t e.1=independentPosition e t := by
      have hh := independentPosition_of_path (fun t => gridPartialSweep bits g t e.1)
        (gridPartialSweep_changes bits g e.1) t
      simpa only [gridPartialSweep_zero,Equiv.Perm.one_apply,gridPartialSweep_last,he] using hh.symm
    apply (endpoint_gridLayer_iff g e j).mp
    rw [← hp j.castSucc,← hp j.succ,gridPartialSweep_succ,Equiv.Perm.mul_apply]
  · intro he
    have hh := chronological_trajectory b (gridLayer bits g) (independentPosition e)
      (fun j => (endpoint_gridLayer_iff g e j).mpr (he j))
    simpa only [independentPosition_zero,independentPosition_last,gridSweep] using hh

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma endpointMass_factor (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) :
    endpointMass H z A e = ∏j, ∏y, localEndpointMass H z A e j y := by
  have he (g : GridChoices bits) :
      (pathEvent H g ∧ ∀i ∈ A, gridSweep bits g (e i).1=(e i).2) ↔
      ∀j y, Assigns (lineInput H j y) (lineOutput H j y) (g j y) ∧
        localEndpointEvent A e j y (g j y) := by
    rw [pathEvent_iff_assigns]
    simp_rw [gridSweep_endpoint_iff]
    constructor
    · rintro ⟨hg,hp⟩ j y
      refine ⟨hg j y,?_⟩
      intro i hi hiy
      rw [← hiy]
      exact hp i hi j
    · intro hh
      refine ⟨fun j y => (hh j y).1,?_⟩
      intro i hi j
      exact (hh j (endpointLine (e i) j)).2 i hi rfl
  unfold endpointMass localEndpointMass
  rw [← sum_prod_grid]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Fintype.prod_ite_zero]
  simp only [he,gridWeight]
  split_ifs <;> rfl

omit [Fintype I] in
lemma localEndpointEvent_insert (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (i : I) (j : Fin b) (y : GridOutside bits j) (σ : Equiv.Perm (Slot (bits j))) :
    localEndpointEvent (insert i A) e j y σ ↔
      (endpointLine (e i) j=y → σ ((e i).1 j)=(e i).2 j) ∧ localEndpointEvent A e j y σ := by
  simp only [localEndpointEvent,Finset.mem_insert,forall_eq_or_imp]

omit [Fintype I] [DecidableEq I] in
lemma localEndpointEvent_empty_line (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (j : Fin b) (y : GridOutside bits j) (ha : ∀i ∈ A, endpointLine (e i) j≠y)
    (σ : Equiv.Perm (Slot (bits j))) : localEndpointEvent A e j y σ := by
  intro i hi hiy
  exact (ha i hi hiy).elim

lemma assigns_empty_line (H : PathFamily bits h) (j : Fin b) (y : GridOutside bits j)
    (hn : ∀k, (fun i : {i : Fin b // i≠j} => H.position j.castSucc k i) ≠ y)
    (σ : Equiv.Perm (Slot (bits j))) : Assigns (lineInput H j y) (lineOutput H j y) σ := by
  intro k
  exact (hn k.val k.property).elim

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_IsolatedCancellation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ}
variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
lemma localEndpointMass_empty_line (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (j : Fin b) (y : GridOutside bits j)
    (hh : ∀k, (fun i : {i : Fin b // i≠j} => H.position j.castSucc k i) ≠ y)
    (ha : ∀i ∈ A, endpointLine (e i) j≠y) :
    localEndpointMass H z A e j y=1 := by
  unfold localEndpointMass
  simp only [assigns_empty_line H j y hh,localEndpointEvent_empty_line A e j y ha,
    and_self,ite_true,lineLaw_sum]

lemma localEndpointMass_insert_at (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (i : I) (j : Fin b)
    (hh : ∀k, (fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) ≠ endpointLine (e i) j)
    (ha : ∀a ∈ A, endpointLine (e a) j≠endpointLine (e i) j) :
    localEndpointMass H z (insert i A) e j (endpointLine (e i) j)=
      (Fintype.card (Slot (bits j)):ℝ)⁻¹ := by
  unfold localEndpointMass
  simp only [assigns_empty_line H j _ hh,localEndpointEvent_insert,
    localEndpointEvent_empty_line A e j _ ha,true_and,and_true,
    forall_true_left]
  exact line_one_card_ite (bits j) z ((e i).1 j) ((e i).2 j)

lemma localEndpointMass_insert_other (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (i : I) (j : Fin b) (y : GridOutside bits j)
    (hy : y≠endpointLine (e i) j) :
    localEndpointMass H z (insert i A) e j y=localEndpointMass H z A e j y := by
  unfold localEndpointMass
  apply Finset.sum_congr rfl
  intro σ _
  simp only [localEndpointEvent_insert,Ne.symm hy,IsEmpty.forall_iff,true_and]

lemma prod_one_coordinate {J : Type*} [Fintype J] [DecidableEq J]
    (f g : J → ℝ) (j : J) (a : ℝ) (hf : f j=1) (hg : g j=a)
    (he : ∀k, k≠j → g k=f k) : ∏k, g k=a*∏k, f k := by
  calc
    _ = ∏k, (if k=j then a else 1)*f k := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k=j
      · subst k; simp [hf,hg]
      · simp [hk,he k hk]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

variable [Fintype I]

lemma endpointMass_insert_isolated (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (i : I)
    (hh : ∀j k, (fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) ≠ endpointLine (e i) j)
    (ha : ∀j, ∀a ∈ A, endpointLine (e a) j≠endpointLine (e i) j) :
    endpointMass H z (insert i A) e=(gridSize bits:ℝ)⁻¹ * endpointMass H z A e := by
  rw [endpointMass_factor,endpointMass_factor]
  have hj (j : Fin b) : (∏y, localEndpointMass H z (insert i A) e j y) =
      (Fintype.card (Slot (bits j)):ℝ)⁻¹ * ∏y, localEndpointMass H z A e j y := by
    exact prod_one_coordinate _ _ (endpointLine (e i) j) _
      (localEndpointMass_empty_line H z A e j _ (hh j) (ha j))
      (localEndpointMass_insert_at H z A e i j (hh j) (ha j))
      (fun y hy => localEndpointMass_insert_other H z A e i j y hy)
  simp only [hj,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  congr 2
  simp only [Slot,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,
    gridSize,Nat.cast_prod]

lemma endpointProbability_insert_isolated (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (i : I)
    (hh : ∀j k, (fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) ≠ endpointLine (e i) j)
    (ha : ∀j, ∀a ∈ A, endpointLine (e a) j≠endpointLine (e i) j) :
    endpointProbability H z (insert i A) e=(gridSize bits:ℝ)⁻¹ * endpointProbability H z A e := by
  unfold endpointProbability
  rw [endpointMass_insert_isolated H z A e i hh ha,mul_div_assoc]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseKernel
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open Sparse

variable {b h : ℕ} {bits : Fin b → ℕ} {I : Type*} [Fintype I] [DecidableEq I]

lemma centeredEndpointKernel_isolated (H : PathFamily bits h) (z : ℝ)
    (e : I → GridSlot bits × GridSlot bits) (i : I)
    (hh : ∀j k, (fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) ≠ endpointLine (e i) j)
    (ha : ∀j a, a≠i → endpointLine (e a) j≠endpointLine (e i) j) :
    centeredEndpointKernel H z e=0 := by
  unfold centeredEndpointKernel
  rw [alternatingSubsetSum_of_isolated Finset.univ
    (by exact_mod_cast (gridSize_pos bits).ne') _ i (Finset.mem_univ _) ?_,mul_zero]
  intro A hA
  exact endpointProbability_insert_isolated H z A e i hh
    (fun j a haA => ha j a (Finset.mem_erase.mp (hA haA)).1)

lemma endpointLine_path (H : PathFamily bits h) (k : Fin h) (j : Fin b) :
    endpointLine (pathEndpoints H k) j=(fun a : {a : Fin b // a≠j} => H.position j.castSucc k a) := by
  unfold endpointLine pathEndpoints
  rw [independentPosition_of_path (fun t => H.position t k) (fun j i hi => H.changes_only_stage j k i hi)]

lemma shareLine_symmetric :
    ∀ ⦃first second : GridSlot bits × GridSlot bits⦄,
      shareLine first second → shareLine second first := by
  rintro e f ⟨j,hj⟩
  exact ⟨j,hj.symm⟩

lemma shareLine_probability (f : GridSlot bits × GridSlot bits) :
    finiteProbability uniformWeight (fun e => shareLine (bits:=bits) e f) ≤
      ∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j) := by
  have he := finiteProbability_union uniformWeight uniformWeight_nonneg
    (fun (j : Fin b) (e : GridSlot bits × GridSlot bits) => endpointLine e j=endpointLine f j)
  have hj (j : Fin b) : finiteProbability uniformWeight
      (fun e : GridSlot bits × GridSlot bits => endpointLine e j=endpointLine f j)=
      (1:ℝ)/Fintype.card (GridOutside bits j) :=
    independent_line_uniform j (endpointLine f j)
  simpa only [hj,shareLine] using he

lemma centeredEndpointKernel_support (H : PathFamily bits h) (z : ℝ)
    (e : I → GridSlot bits × GridSlot bits) (he : centeredEndpointKernel H z e≠0) :
    incidentSet shareLine (pathEndpoints H) e=Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  have hn : ¬((∃a, i≠a ∧ shareLine (e i) (e a)) ∨ ∃k, shareLine (e i) (pathEndpoints H k)) := by
    simpa only [incidentSet,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  apply he
  apply centeredEndpointKernel_isolated H z e i
  · intro j k hk
    apply hn
    exact Or.inr ⟨k,j,hk.symm.trans (endpointLine_path H k j).symm⟩
  · intro j a hai hj
    exact hn (Or.inl ⟨a,Ne.symm hai,j,hj.symm⟩)

theorem centeredEndpointKernel_exceptional_probability (H : PathFamily bits h) (z : ℝ)
    (hsmall : ((Fintype.card I+h:ℕ):ℝ) *
      (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)) ≤ 1) :
    productProbability (uniformWeight (Ω:=GridSlot bits × GridSlot bits))
      (fun e : I → GridSlot bits × GridSlot bits => centeredEndpointKernel H z e≠0) ≤
      (2:ℝ)^Fintype.card I *
        (((Fintype.card I+h:ℕ):ℝ) * (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j))) ^
          ((Fintype.card I+1)/2) := by
  have hh := sharing_probability_le (I:=I) uniformWeight uniformWeight_nonneg uniformWeight_sum
      shareLine shareLine_symmetric (pathEndpoints H) _ (by positivity)
      shareLine_probability (Fintype.card I) (by simpa only [Fintype.card_fin] using hsmall)
  simp only [Fintype.card_fin] at hh
  apply (productProbability_mono uniformWeight_nonneg ?_).trans hh
  intro e he
  rw [centeredEndpointKernel_support H z e he,Finset.card_univ]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma restrictPlacement_event (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (A : Finset (Fin k)) (g : ConditionalChoices H) :
    placementBijection H (Fintype.card A) g (restrictPlacement H x A)=restrictPlacement H y A ↔
      ∀i ∈ A, gridSweep bits g.val (x i).val=(y i).val := by
  constructor
  · intro he i hi
    have hh := congrArg (fun q => (q (Fintype.equivFin A ⟨i,hi⟩)).val) he
    change gridSweep bits g.val (x ((Fintype.equivFin A).symm
      (Fintype.equivFin A ⟨i,hi⟩)).val).val =
      (y ((Fintype.equivFin A).symm (Fintype.equivFin A ⟨i,hi⟩)).val).val at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · intro he
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact he _ ((Fintype.equivFin A).symm i).property

lemma endpointProbability_conditional {I : Type*} [Fintype I] [DecidableEq I]
    (z : ℝ) (A : Finset I) (e : I → GridSlot bits × GridSlot bits) :
    endpointProbability H z A e =
      conditionalEventWeight H z (fun g => ∀i ∈ A, gridSweep bits g (e i).1=(e i).2) := by
  unfold endpointProbability endpointMass conditionalEventWeight conditionalChoiceWeight
  have hh (g : ConditionalChoices H) :
      (if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then gridWeight bits z g.val else 0) /
        conditionalNormalizer H z := by split_ifs <;> simp
  have hR : (∑g : ConditionalChoices H,
      if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (∑g : ConditionalChoices H, if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val else 0) / conditionalNormalizer H z := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    exact hh g
  refine Eq.trans ?_ (Eq.trans hR.symm ?_)
  · congr 1
    have hs := sum_dite_zero (pathEvent H) (fun g _ =>
      if ∀i ∈ A, gridSweep bits g (e i).1=(e i).2 then gridWeight bits z g else 0)
    refine Eq.trans ?_ (hs.trans ?_)
    · apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp_all
    · apply Finset.sum_congr (by ext sample; simp)
      intro g _
      rfl
  · apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> rfl

theorem endpointProbability_placement (z : ℝ)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    endpointProbability H z A (fun i => ((x i).val,(y i).val)) =
      placementProbability H z (restrictPlacement H x A) (restrictPlacement H y A) := by
  rw [endpointProbability_conditional]
  unfold conditionalEventWeight placementProbability
  apply Finset.sum_congr rfl
  intro g _
  simp only [restrictPlacement_event]
  split_ifs <;> rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_ConditionalCentered
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Sparse

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma conditionalGroupLaw_expectation {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (z : ℝ) (f : Equiv.Perm (FreeSlot H 0) → W) :
    (∑a, conditionalGroupLaw H z a • f a) =
      ∑g : ConditionalChoices H, conditionalChoiceWeight H z g • f (remainingPerm H g.val g.property) := by
  unfold conditionalGroupLaw
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [ite_smul,zero_smul]
  simp

lemma partialKernel_event (g : ConditionalChoices H) (A : Finset (Fin k))
    (x y : Placement H k 0) :
    subPlacement A (movePlacement (remainingPerm H g.val g.property) x)=subPlacement A y ↔
      ∀i∈A, gridSweep bits g.val (x i).val=((placementIdentification H k y i).val) := by
  constructor
  · intro he i hi
    have hh := congrArg (fun u => u ⟨i,hi⟩) he
    have he' : remainingPerm H g.val g.property (x i)=y i := hh
    have ht := congrArg (freeIdentification H) he'
    change (freeIdentification H) ((freeIdentification H).symm
      (remainingBijection H g.val g.property (x i)))=(freeIdentification H) (y i) at ht
    rw [Equiv.apply_symm_apply] at ht
    exact congrArg Subtype.val ht
  · intro he
    apply Function.Embedding.ext
    intro i
    change (freeIdentification H).symm (remainingBijection H g.val g.property (x i.val))=y i.val
    apply (freeIdentification H).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact he i.val i.property

lemma partialKernel_conditional (z : ℝ) (A : Finset (Fin k)) (x y : Placement H k 0) :
    (∑a : Equiv.Perm (FreeSlot H 0), (conditionalGroupLaw H z a:ℂ) * partialKernel A a y x)=
      (endpointProbability H z A (fun i => ((x i).val,(placementIdentification H k y i).val)):ℂ) := by
  have he := conditionalGroupLaw_expectation H z (fun a => partialKernel A a y x)
  simp only [Complex.real_smul] at he
  rw [he,endpointProbability_conditional]
  unfold conditionalEventWeight
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr
  · ext g; simp only [Finset.mem_univ]
  intro g _
  simp only [partialKernel,partialKernel_event H g A x y]
  split_ifs <;> simp

theorem centeredMatrix_conditional (z : ℝ) (x y : Placement H k 0) :
    centeredMatrix (gridSize bits) (fun a => (conditionalGroupLaw H z a:ℂ)) y x =
      (centeredEndpointKernel H z (fun i => ((x i).val,(placementIdentification H k y i).val)):ℂ) := by
  simp only [centeredMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  simp_rw [partialKernel_conditional H z]
  unfold centeredEndpointKernel alternatingSubsetSum
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_natCast,
    Complex.ofReal_sum,Complex.ofReal_neg,Complex.ofReal_one,Finset.card_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [div_eq_mul_inv,inv_pow]
  ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseAmplitude
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma placementProbability_uniform_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    (gridSize bits : ℝ)^k * placementProbability H z x y ≤
      Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hp := placementProbability_nonneg H hz hz1 x y
  by_cases hp0 : placementProbability H z x y=0
  · rw [hp0,mul_zero]; exact (Real.exp_pos _).le
  have hp' : 0<placementProbability H z x y := lt_of_le_of_ne hp (Ne.symm hp0)
  have hb := placement_probability_cost_of_pos H hd hz hzr x y hp'
  have hc : placementTransitionCost H z x y ≤ (b:ℝ)*(h+k) := by
    unfold placementTransitionCost
    rw [dite_eq_left hp']
    simpa only [Nat.cast_add] using pathCost_le
      (augmentByChoice H x (realizePlacement H z x y hp'))
  have hpow : (gridSize bits:ℝ)^k * (gridSize bits:ℝ)^(-(k:ℝ))=1 := by
    rw [Real.rpow_neg hs.le,Real.rpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ hs.ne')
  calc
    _ ≤ (gridSize bits:ℝ)^k * ((gridSize bits:ℝ)^(-(k:ℝ)) *
        Real.exp (placementTransitionCost H z x y-pathCost H+Real.log 4*k*b)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs.le _)
    _ = Real.exp (placementTransitionCost H z x y-pathCost H+Real.log 4*k*b) := by
      rw [← mul_assoc,hpow,one_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [pathCost_nonneg H])

lemma endpointProbability_scaled_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H z A (fun i => ((x i).val,(y i).val)) ≤
      Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  rw [endpointProbability_placement]
  have hb := placementProbability_uniform_bound H hd hz hzr hz1
    (restrictPlacement H x A) (restrictPlacement H y A)
  simp only [Fintype.card_coe] at hb
  refine hb.trans (Real.exp_le_exp.mpr ?_)
  have hk : (A.card:ℝ) ≤ k := by exact_mod_cast (show A.card ≤ k from (by simpa only [Fintype.card_fin] using A.card_le_univ))
  have hl : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hbk := mul_le_mul_of_nonneg_left hk (show (0:ℝ)≤b by positivity)
  have hbkl := mul_le_mul_of_nonneg_left hbk hl
  nlinarith

lemma alternatingSubsetSum_abs_le {I : Type*} [DecidableEq I] (U : Finset I)
    (s : ℝ) (p : Finset I → ℝ) (C : ℝ)
    (hp : ∀ A ⊆ U, 0 ≤ s^A.card*p A ∧ s^A.card*p A ≤ C) :
    |alternatingSubsetSum U s p|≤(2:ℝ)^U.card*C := by
  unfold alternatingSubsetSum
  calc
    _ ≤ ∑A ∈ U.powerset, |(-1:ℝ)^(U.card-A.card)*s^A.card*p A| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_A ∈ U.powerset, C := by
      apply Finset.sum_le_sum
      intro A hA
      rw [mul_assoc,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
        abs_of_nonneg (hp A (Finset.mem_powerset.mp hA)).1]
      exact (hp A (Finset.mem_powerset.mp hA)).2
    _ = _ := by simp

theorem centeredEndpointKernel_amplitude (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    |(gridSize bits:ℝ)^k * centeredEndpointKernel H z (fun i => ((x i).val,(y i).val))| ≤
      (2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  unfold centeredEndpointKernel
  simp only [Fintype.card_fin]
  rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ (by exact_mod_cast (gridSize_pos bits).ne'),
    one_pow,one_mul]
  have hb := alternatingSubsetSum_abs_le Finset.univ (gridSize bits)
    (fun A => endpointProbability H z A (fun i => ((x i).val,(y i).val)))
    (Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b)) (by
      intro A _
      constructor
      · rw [endpointProbability_placement]
        exact mul_nonneg (by positivity) (placementProbability_nonneg H hz hz1 _ _)
      · exact endpointProbability_scaled_bound H hd hz hzr hz1 x y A)
  simpa only [Finset.card_univ,Fintype.card_fin] using hb

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {P Ω I : Type*} [Fintype P] [Fintype Ω] [Fintype I] [DecidableEq I]

lemma productProbability_uniform (E : (I → Ω) → Prop) :
    productProbability uniformWeight E=finiteProbability uniformWeight E := by
  unfold productProbability finiteProbability productWeight uniformWeight
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,one_div,inv_pow]

lemma sum_injective_le (f : P → Ω) (hi : Function.Injective f) (w : Ω → ℝ)
    (hw : ∀u, 0≤w u) : ∑i, w (f i) ≤ ∑u, w u := by
  classical
  rw [← Finset.sum_image (fun x _ y _ hxy => hi hxy)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun u _ _ => hw u)

theorem sum_square_le_uniform_event (f : P → Ω) (hi : Function.Injective f)
    (Q : Ω → ℝ) (a C : ℝ) (ha : 0<a) (hC : 0≤C)
    (hN : (Fintype.card Ω:ℝ)=a^2) (hb : ∀i, |a*Q (f i)|≤C) :
    ∑i, (Q (f i))^2 ≤ C^2 * finiteProbability uniformWeight (fun u => Q u≠0) := by
  have hcard : (Fintype.card Ω:ℝ)≠0 := by rw [hN]; positivity
  have hp : (Fintype.card Ω:ℝ)*finiteProbability uniformWeight (fun u => Q u≠0) =
      ∑u : Ω, if Q u≠0 then (1:ℝ) else 0 := by
    unfold finiteProbability uniformWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [← mul_assoc,mul_one_div_cancel hcard,one_mul]
    split_ifs <;> rfl
  have hle : a^2*(∑i, (Q (f i))^2) ≤
      ∑u : Ω, if Q u≠0 then C^2 else 0 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans
      (sum_injective_le f hi (fun u => if Q u≠0 then C^2 else 0)
        (fun u => by
          split_ifs
          · exact pow_nonneg hC 2
          · exact le_rfl))
    by_cases hz : Q (f i)=0
    · simp only [hz,ne_eq,not_true_eq_false,ite_false,zero_pow (by decide : 2≠0),mul_zero]
      exact le_rfl
    · rw [ite_eq_left hz,← mul_pow]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
  have he : (∑u : Ω, if Q u≠0 then C^2 else 0)=
      C^2 * ((Fintype.card Ω:ℝ)*finiteProbability uniformWeight (fun u => Q u≠0)) := by
    rw [hp,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  rw [he,hN] at hle
  nlinarith [sq_pos_of_pos ha]

end BinaryCoordinateSweeps.Sparse
namespace BinaryCoordinateSweeps
open Sparse

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma placementEndpointArray_injective : Function.Injective (placementEndpointArray (k:=k) H) := by
  intro x y he
  apply Prod.ext
  · apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun z => (z i).1) he
  · apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun z => (z i).2) he

theorem centeredEndpointKernel_hs_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (hsmall : ((k+h:ℕ):ℝ) * (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)) ≤ 1) :
    (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2) ≤
      ((2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
        ((2:ℝ)^k * (((k+h:ℕ):ℝ) *
          (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)))^((k+1)/2)) := by
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hN : (Fintype.card (Fin k → GridSlot bits × GridSlot bits):ℝ)=((gridSize bits:ℝ)^k)^2 := by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,card_gridSlot,Nat.cast_pow,Nat.cast_mul,mul_pow,pow_two]
  have he := sum_square_le_uniform_event (placementEndpointArray (k:=k) H)
    (placementEndpointArray_injective H) (centeredEndpointKernel H z)
    ((gridSize bits:ℝ)^k) ((2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))
    (pow_pos hs _) (by positivity) hN (fun xy => centeredEndpointKernel_amplitude H hd hz hzr hz1 xy.1 xy.2)
  rw [← productProbability_uniform] at he
  have hp := centeredEndpointKernel_exceptional_probability (I:=Fin k) H z
    (by simpa only [Fintype.card_fin] using hsmall)
  simp only [Fintype.card_fin] at hp
  have heq : (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2) =
      ∑xy : Placement H k 0 × Placement H k (Fin.last b),
        (centeredEndpointKernel H z (placementEndpointArray H xy))^2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr
    · ext x; simp only [Finset.mem_univ]
    intro x _
    apply Finset.sum_congr
    · ext y; simp only [Finset.mem_univ]
    intro y _
    rfl
  rw [heq]
  exact he.trans (mul_le_mul_of_nonneg_left hp (sq_nonneg _))

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ConditionalSpecht
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Irrep

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma groupAverage_comp_slots {X Y V : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (e : X ≃ Y) (ρ : Representation ℂ (Equiv.Perm X) V) (p : Equiv.Perm Y → ℂ) :
    groupAverage (ρ.comp e.symm.permCongrHom.toMonoidHom) p =
      groupAverage ρ (fun g => p (e.permCongr g)) := by
  unfold groupAverage
  rw [← Equiv.sum_comp e.permCongr]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change ρ (e.permCongr.symm (e.permCongr g))=ρ g
  rw [Equiv.symm_apply_apply]

theorem conditional_specht_hs (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0)
    (a : Tail μ ≃ Fin k) (z : ℝ) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
      ∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
        (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2 := by
  rw [groupAverage_comp_slots]
  have hs : (gridSize bits:ℝ)≠0 := by exact_mod_cast (gridSize_pos bits).ne'
  have he := specht_moment_one_le_centered_matrix μ (gridSize bits) hs
    (fun g => (conditionalGroupLaw H z (e.permCongr g):ℂ))
  have hr := centeredMatrix_hs_reindex a e (gridSize bits)
    (fun g => (conditionalGroupLaw H z (e.permCongr g):ℂ))
  simp only [Equiv.apply_symm_apply] at hr
  rw [← hr] at he
  refine he.trans_eq ?_
  change (∑x : Placement H k 0, ∑y : Placement H k 0,
    ‖centeredMatrix (gridSize bits) (fun g => (conditionalGroupLaw H z g:ℂ)) y x‖^2)=_
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [centeredMatrix_conditional H z,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact Equiv.sum_comp (placementIdentification H k) (fun y : Placement H k (Fin.last b) =>
    (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2)

theorem conditional_specht_many_bound (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0)
    (a : Tail μ ≃ Fin k) (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (hsmall : ((k+h:ℕ):ℝ) * (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)) ≤ 1) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
      ((2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
        ((2:ℝ)^k * (((k+h:ℕ):ℝ) *
          (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)))^((k+1)/2)) :=
  (conditional_specht_hs H μ e a z).trans
    (centeredEndpointKernel_hs_bound H hd hz hzr hz1 hsmall)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_MainEasyCases
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

lemma grid_log_lower {b r : ℕ} {bits : Fin b → ℕ} (hd : ∀ j, r ≤ bits j) :
    (b : ℝ) * ((r : ℝ) * Real.log 2) ≤ Real.log (gridSize bits) := by
  calc
    _ = ∑ _j : Fin b, (r : ℝ) * Real.log 2 := by simp
    _ ≤ ∑ j : Fin b, (bits j : ℝ) * Real.log 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hd j)
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    _ = _ := by
      rw [log_gridSize]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_WeightedCycle
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma linePerturbationRadius_lt_one (r : ℕ) : linePerturbationRadius r < 1 := by
  have hf : (1 : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 ^ (2 * r))
  unfold linePerturbationRadius
  apply (div_lt_one (by positivity)).mpr
  linarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_AssignmentSign
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]

lemma realSign_swap {u v : X} (huv : u≠v) : realSign (Equiv.swap u v) = -1 := by
  simp [realSign,Equiv.Perm.sign_swap huv]

omit [Fintype I] [Fintype X] in
lemma assigns_swap_left (A B : I ↪ X) {u v : X}
    (hu : u∉Set.range B) (hv : v∉Set.range B) (σ : Equiv.Perm X) :
    Assigns A B (Equiv.swap u v*σ) ↔ Assigns A B σ := by
  have hf (i : I) : Equiv.swap u v (B i)=B i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; exact hu ⟨i,he⟩
    · intro he; exact hv ⟨i,he⟩
  constructor
  · intro hh i
    apply (Equiv.swap u v).injective
    exact (hh i).trans (hf i).symm
  · intro hh i
    change Equiv.swap u v (σ (A i))=B i
    rw [hh i,hf]

omit [Fintype I] in
theorem sum_sign_assigns_zero (A B : I ↪ X) {u v : X}
    (huv : u≠v) (hu : u∉Set.range B) (hv : v∉Set.range B) :
    (∑σ : Equiv.Perm X, if Assigns A B σ then realSign σ else 0) = 0 := by
  classical
  let f (σ : Equiv.Perm X) := if Assigns A B σ then realSign σ else 0
  have ht (σ : Equiv.Perm X) : f (Equiv.swap u v*σ) = -f σ := by
    dsimp [f]
    rw [assigns_swap_left A B hu hv,map_mul,realSign_swap huv]
    split_ifs <;> ring
  have he := Equiv.sum_comp (Equiv.mulLeft (Equiv.swap u v)) f
  change (∑σ, f (Equiv.swap u v*σ))=∑σ,f σ at he
  simp_rw [ht] at he
  rw [Finset.sum_neg_distrib] at he
  dsimp [f] at he
  linarith

omit [Fintype I] in
lemma uniform_sign_assigns_zero (A B : I ↪ X) {u v : X}
    (huv : u≠v) (hu : u∉Set.range B) (hv : v∉Set.range B) :
    (∑σ : Equiv.Perm X, if Assigns A B σ then
      uniformLaw (Equiv.Perm X) σ * realSign σ else 0) = 0 := by
  have ht (σ : Equiv.Perm X) :
      (if Assigns A B σ then uniformLaw (Equiv.Perm X) σ*realSign σ else 0) =
      (Fintype.card (Equiv.Perm X):ℝ)⁻¹*(if Assigns A B σ then realSign σ else 0) := by
    split_ifs <;> simp [uniformLaw]
  simp_rw [ht]
  rw [←Finset.mul_sum,sum_sign_assigns_zero A B huv hu hv,mul_zero]

lemma uniform_sign_zero [Nontrivial X] :
    (∑σ : Equiv.Perm X, uniformLaw (Equiv.Perm X) σ*realSign σ)=0 := by
  obtain ⟨u,v,huv⟩ := exists_pair_ne X
  let E : Fin 0 ↪ X := ⟨Fin.elim0,by intro i; exact Fin.elim0 i⟩
  have hs := uniform_sign_assigns_zero E E huv
    (by rintro ⟨i,_⟩; exact Fin.elim0 i) (by rintro ⟨i,_⟩; exact Fin.elim0 i)
  simpa [Assigns] using hs

lemma lineLaw_sign_zero {d : ℕ} (hd : 0<d) (z : ℝ) :
    (∑σ : Equiv.Perm (Slot d), lineLaw d z σ*realSign σ)=0 := by
  have : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have : Nontrivial (Slot d) := inferInstance
  simp_rw [lineLaw,add_mul,mul_assoc]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
    uniform_sign_zero,binary_sign_annihilated d hd,mul_zero,mul_zero,add_zero]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceInterpolation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma star_diagReal (s : ι → ℝ) : star (diagReal s) = diagReal s := by
  simp [diagReal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]

lemma diagReal_mul (s t : ι → ℝ) : diagReal s * diagReal t = diagReal (fun i => s i*t i) := by
  simp [diagReal, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

omit [DecidableEq ι] in
lemma gram_product (X Y : M ι) :
    star (X*Y) * (X*Y) = star Y * (star X * X) * Y := by
  simp only [star_mul, mul_assoc]

lemma gram_diagonal_factor (X : M ι) (s : ι → ℝ)
    (hX : star X * X = diagReal (fun i => s i ^ 2)) :
    ∃ U : M ι, ‖U‖ ≤ 1 ∧ X = U * diagReal s := by
  let t : ι → ℝ := fun i => (s i)⁻¹
  let U := X * diagReal t
  have hU : star U * U = diagReal (fun i => if s i = 0 then 0 else 1) := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    congr 1
    funext i
    dsimp [t]
    split_ifs with hi
    · simp [hi]
    · field_simp
  have hUnorm : ‖U‖ ≤ 1 := by
    have h : ‖star U * U‖ ≤ 1 := by
      rw [hU, diagReal, Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      split_ifs <;> norm_num
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg U]
  let w : ι → ℝ := fun i => 1 - t i * s i
  have hz : star (X * diagReal w) * (X * diagReal w) = 0 := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    have hw : (fun i => (w i * s i ^ 2) * w i) = 0 := by
      funext i
      dsimp [w, t]
      by_cases hi : s i = 0 <;> simp [hi]
    rw [hw]
    simp [diagReal]
  have hzero : X * diagReal w = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  have hw : diagReal w = 1 - diagReal t * diagReal s := by
    rw [diagReal_mul]
    dsimp [diagReal, w]
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp
  rw [hw, mul_sub, mul_one] at hzero
  refine ⟨U, hUnorm, ?_⟩
  exact (sub_eq_zero.mp hzero).trans (mul_assoc _ _ _).symm

theorem exists_partial_svd (A : M ι) :
    ∃ (U : M ι) (V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ ‖U‖ ≤ 1 ∧
      A = U * diagReal s * star (V : M ι) ∧
      star A * A = (V : M ι) * diagReal (fun i => s i ^ 2) * star (V : M ι) := by
  let h := Matrix.isHermitian_conjTranspose_mul_self A
  let V := h.eigenvectorUnitary
  let s : ι → ℝ := fun i => Real.sqrt (h.eigenvalues i)
  have hs0 : ∀ i, 0 ≤ s i := fun i => Real.sqrt_nonneg _
  have hs : ∀ i, s i ^ 2 = h.eigenvalues i := fun i =>
    Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
  have hdiag : star (V : M ι) * (star A * A) * (V : M ι) =
      diagReal (fun i => s i ^ 2) := by
    simpa only [V, s, hs, diagReal, Matrix.star_eq_conjTranspose, Function.comp_def,
      Unitary.conjStarAlgAut_star_apply] using! h.conjStarAlgAut_star_eigenvectorUnitary
  have hgram : star (A * (V : M ι)) * (A * (V : M ι)) =
      diagReal (fun i => s i ^ 2) := by rw [gram_product, hdiag]
  obtain ⟨U, hU, heq⟩ := gram_diagonal_factor (A * (V : M ι)) s hgram
  have hVV : (V : M ι) * star (V : M ι) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self V
  refine ⟨U, V, s, hs0, hU, ?_, ?_⟩
  · have heq' := congrArg (fun X => X * star (V : M ι)) heq
    simpa only [mul_assoc, hVV, mul_one] using heq'
  · calc
      star A * A = ((V : M ι) * star (V : M ι)) * (star A * A) *
          ((V : M ι) * star (V : M ι)) := by rw [hVV, one_mul, mul_one]
      _ = (V : M ι) * (star (V : M ι) * (star A * A) * (V : M ι)) *
          star (V : M ι) := by simp only [mul_assoc]
      _ = _ := by rw [hdiag]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SpectralMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagReal_pow (s : ι → ℝ) (q : ℕ) :
    (diagReal s)^q = diagReal (fun i => s i ^ q) := by
  simp [diagReal, Matrix.diagonal_pow]

lemma trace_unitary_conj (V : Matrix.unitaryGroup ι ℂ) (B : M ι) :
    Matrix.trace ((V : M ι) * B * star (V : M ι)) = Matrix.trace B := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

lemma unitary_conj_pow (V : Matrix.unitaryGroup ι ℂ) (B : M ι) (q : ℕ) :
    ((V : M ι) * B * star (V : M ι))^q = (V : M ι) * B^q * star (V : M ι) := by
  have h := ((Unitary.conjStarAlgAut ℂ (M ι) V).toAlgEquiv.map_pow B q).symm
  change (Unitary.conjStarAlgAut ℂ (M ι) V B)^q =
    Unitary.conjStarAlgAut ℂ (M ι) V (B^q) at h
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star] using h

lemma matrixMoment_of_svd (A : M ι) (q : ℕ) (V : Matrix.unitaryGroup ι ℂ)
    (s : ι → ℝ) (hgram : star A * A = (V : M ι) * diagReal (fun i => s i^2) * star (V : M ι)) :
    matrixMoment q A = ∑ i, s i ^ (2*q) := by
  rw [matrixMoment, hgram, unitary_conj_pow, trace_unitary_conj, diagReal_pow]
  simp only [diagReal, Matrix.trace_diagonal,
    Complex.re_sum, Complex.ofReal_re, ← pow_mul]

lemma matrixMoment_nonneg (q : ℕ) (A : M ι) : 0 ≤ matrixMoment q A := by
  obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  rw [matrixMoment_of_svd A q V s hg]
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (hs i) _)

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_LinearEvenMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [Fintype ι] [DecidableEq ι]

lemma trace_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (A : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V A = Matrix.trace (LinearMap.toMatrixOrthonormal v A) :=
  LinearMap.trace_eq_matrix_trace ℂ v.toBasis A

lemma evenMoment_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (q : ℕ) (A : V →ₗ[ℂ] V) :
    evenMoment q A=matrixMoment q (LinearMap.toMatrixOrthonormal v A) := by
  unfold evenMoment matrixMoment
  rw [trace_orthonormalMatrix v]
  simp only [map_pow,map_mul,← LinearMap.star_eq_adjoint,map_star]

lemma evenMoment_nonneg (q : ℕ) (A : V →ₗ[ℂ] V) : 0≤evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  exact matrixMoment_nonneg _ _

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_RemainingSign
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma realSign_ne_zero {X : Type*} [Fintype X] [DecidableEq X] (g : Equiv.Perm X) :
    realSign g≠0 := by
  simp [realSign]

lemma realSign_inv {X : Type*} [Fintype X] [DecidableEq X] (f : Equiv.Perm X) :
    realSign f⁻¹=(realSign f)⁻¹ := by
  have hm : realSign f⁻¹*realSign f=1 := by rw [←map_mul,inv_mul_cancel,map_one]
  calc
    realSign f⁻¹ = (realSign f⁻¹*realSign f)*(realSign f)⁻¹ := by
      rw [mul_assoc,mul_inv_cancel₀ (realSign_ne_zero f),mul_one]
    _ = _ := by rw [hm,one_mul]

lemma remaining_relative_realSign (g g₀ : ConditionalChoices H) :
    realSign ((remainingPerm H g₀.val g₀.property)⁻¹*remainingPerm H g.val g.property)=
      realSign ((gridSweep bits g₀.val)⁻¹*gridSweep bits g.val) := by
  let f := (gridSweep bits g₀.val)⁻¹*gridSweep bits g.val
  have hfix (i : Fin h) : f (H.position 0 i)=H.position 0 i := by
    change (gridSweep bits g₀.val).symm (gridSweep bits g.val (H.position 0 i))=_
    rw [gridSweep_path H g.val g.property,←gridSweep_path H g₀.val g₀.property,
      Equiv.symm_apply_apply]
  have hp (x : GridSlot bits) : f x∉Set.range (H.position 0) ↔ x∉Set.range (H.position 0) := by
    constructor
    · intro hx hi; obtain ⟨i,rfl⟩ := hi; exact hx ⟨i,hfix i |>.symm⟩
    · intro hx hi; obtain ⟨i,hi⟩ := hi
      exact hx ⟨i,f.injective ((hfix i).trans hi)⟩
  have hs := Equiv.Perm.sign_subtypePerm f (p := fun x => x∉Set.range (H.position 0)) hp (by
    intro x hx hi; obtain ⟨i,rfl⟩ := hi; exact hx (hfix i))
  have he : Equiv.Perm.subtypePerm f hp =
      (remainingPerm H g₀.val g₀.property)⁻¹*remainingPerm H g.val g.property := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change f x.val =
      (gridSweep bits g₀.val).symm
        ((freeIdentification H) ((freeIdentification H).symm
          ((remainingBijection H g.val g.property) x))).val
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he] at hs
  convert congrArg (fun u : ℤˣ => ((u:ℤ):ℝ)) hs using 1
  · unfold realSign; dsimp; congr 3
    congr 1; exact Subsingleton.elim _ _
  · rfl

theorem remaining_realSign_factor (g g₀ : ConditionalChoices H) :
    realSign (remainingPerm H g.val g.property) =
      (realSign (remainingPerm H g₀.val g₀.property)/realSign (gridSweep bits g₀.val))*
        realSign (gridSweep bits g.val) := by
  have he := remaining_relative_realSign H g g₀
  simp only [map_mul,realSign_inv] at he
  have h₀ := realSign_ne_zero (remainingPerm H g₀.val g₀.property)
  have h₁ := realSign_ne_zero (gridSweep bits g₀.val)
  field_simp [h₀,h₁] at he ⊢
  nlinarith [he]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseNumerics
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Asymptotics

namespace BinaryCoordinateSweeps.Sparse

lemma nat_pow_le_exp_of_le {x A : ℝ} (hx : 0≤x) (h : x≤Real.exp A) (n : ℕ) :
    x^n≤Real.exp ((n:ℝ)*A) := by
  simpa only [←Real.exp_nat_mul] using pow_le_pow_left₀ hx h n

lemma log_le_small_rpow_eventually {ε : ℝ} (hε : 0<ε) : ∀ᶠ s : ℕ in atTop,
    Real.log (s:ℝ)≤(s:ℝ)^ε := by
  have hh := (isLittleO_log_rpow_rpow_atTop (1:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  have hc : Tendsto (fun s : ℕ => (s:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hc.eventually hh,eventually_ge_atTop (1:ℕ)] with s hs hs1
  have hl : 0≤Real.log (s:ℝ) := Real.log_nonneg (by exact_mod_cast hs1)
  simpa only [Real.rpow_one,Real.norm_of_nonneg hl,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg s) ε),one_mul] using hs

lemma many_hs_scalar (b h k : ℕ) {L x : ℝ} (hb : 1≤b)
    (hh : (h:ℝ)≤100000*k) (hL : 4000000000*(b:ℝ)≤L)
    (hx0 : 0≤x) (hx : x≤Real.exp (-L/4000)) :
    ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*x^((k+1)/2)) ≤ Real.exp (-(k:ℝ)*L/16000) := by
  have hL0 : 0≤L := (by positivity : (0:ℝ)≤4000000000*b).trans hL
  have hbk : (1:ℝ)≤b := by exact_mod_cast hb
  have hkt : (k:ℝ)≤2*(((k+1)/2:ℕ):ℝ) := by exact_mod_cast (show k≤2*((k+1)/2) from by omega)
  have hal : x^((k+1)/2)≤Real.exp (-(k:ℝ)*L/8000) := by
    apply (nat_pow_le_exp_of_le hx0 hx _).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hkt hL0]
  have hlog2 : Real.log 2≤2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans (by norm_num)
  have hlog4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hp (n : ℕ) : (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  calc
    _ ≤ ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
        ((2:ℝ)^k*Real.exp (-(k:ℝ)*L/8000)) := by gcongr
    _ = Real.exp (3*(k:ℝ)*Real.log 2+2*((b:ℝ)*(h+k)+Real.log 4*k*b)-(k:ℝ)*L/8000) := by
      simp only [hp,←Real.exp_add,←Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤b by positivity)
      have h2 := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ)≤k by positivity)
      have h4 := mul_le_mul_of_nonneg_right hlog4 (show (0:ℝ)≤k*b by positivity)
      have hkb := mul_le_mul_of_nonneg_left hbk (show (0:ℝ)≤k by positivity)
      have hLc := mul_le_mul_of_nonneg_right hL (show (0:ℝ)≤k by positivity)
      nlinarith

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseReduction
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse

lemma outside_card_mul_axis {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :
    Fintype.card (GridOutside bits j)*2^bits j=gridSize bits := by
  have he := Fintype.card_congr (Equiv.piSplitAt j (fun i => Slot (bits i)))
  change Fintype.card (GridSlot bits)=Fintype.card (Slot (bits j) × GridOutside bits j) at he
  have hs : Fintype.card (Slot (bits j))=2^bits j := by simp [Slot]
  have hg : Fintype.card (GridSlot bits)=gridSize bits := by simp [GridSlot,gridSize,Slot]
  simpa only [Fintype.card_prod,hs,hg,mul_comm] using he.symm

lemma outside_inv_axis_ratio {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :
    (1:ℝ)/Fintype.card (GridOutside bits j)=(2^bits j:ℕ)/(gridSize bits:ℝ) := by
  have hp : (0:ℝ)<(2^bits j:ℕ) := by positivity
  have he : (Fintype.card (GridOutside bits j):ℝ)*(2^bits j:ℕ)=gridSize bits := by
    exact_mod_cast outside_card_mul_axis bits j
  rw [←he]
  field_simp

lemma many_axis_size_bound {b r : ℕ} {bits : Fin b → ℕ}
    (hb : 16000≤b) (hd : ∀j, r≤bits j ∧ bits j≤2*r) (j : Fin b) :
    ((2^bits j:ℕ):ℝ)≤Real.exp (Real.log (gridSize bits)/8000) := by
  have hbR : (16000:ℝ)≤b := by exact_mod_cast hb
  have hr : 0≤(r:ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hl := grid_log_lower (fun j => (hd j).1)
  have ha := mul_le_mul_of_nonneg_right hbR hr
  have hj := mul_le_mul_of_nonneg_right (show (bits j:ℝ)≤2*r by exact_mod_cast (hd j).2)
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  have hp : (0:ℝ)<((2^bits j:ℕ):ℝ) := by positivity
  rw [←Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  linarith

lemma many_collision_base_eventually : ∀ᶠ s : ℕ in atTop,
    ∀ b r h k : ℕ, ∀ bits : Fin b → ℕ, gridSize bits=s → 16000≤b →
    (∀j, r≤bits j ∧ bits j≤2*r) → 1≤(r:ℝ)*Real.log 2 →
    ((k+h:ℕ):ℝ)≤(s:ℝ)^(1599/1600:ℝ) →
    ((k+h:ℕ):ℝ)*(∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j))≤
      Real.exp (-Real.log s/4000) := by
  filter_upwards [log_le_small_rpow_eventually (by norm_num : (0:ℝ)<1/4000)] with s hs
  intro b r h k bits he hb hd hr hk
  have sp : (0:ℝ)<s := by rw [←he]; exact_mod_cast gridSize_pos bits
  have hl := grid_log_lower (fun j => (hd j).1)
  rw [he] at hl
  have hbL : (b:ℝ)≤Real.log s := by nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg b)]
  have hbE : (b:ℝ)≤Real.exp (Real.log s/4000) := by
    refine (hbL.trans hs).trans_eq ?_
    rw [Real.rpow_def_of_pos sp]
    congr 1
    ring
  have hsum : (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j))≤
      (b:ℝ)*Real.exp (Real.log s/8000)/(s:ℝ) := by
    calc
      _ ≤ ∑_j : Fin b, Real.exp (Real.log s/8000)/(s:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [outside_inv_axis_ratio,he]
        exact div_le_div_of_nonneg_right (by simpa only [he] using many_axis_size_bound hb hd j) sp.le
      _ = _ := by simp; ring
  have hkE : ((k+h:ℕ):ℝ)≤Real.exp ((1599/1600:ℝ)*Real.log s) := by
    simpa only [Real.rpow_def_of_pos sp,mul_comm] using hk
  calc
    _ ≤ Real.exp ((1599/1600:ℝ)*Real.log s)*
        (Real.exp (Real.log s/4000)*Real.exp (Real.log s/8000)/(s:ℝ)) := by
      apply mul_le_mul hkE
      · exact hsum.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbE (Real.exp_pos _).le) sp.le)
      · positivity
      · positivity
    _ = _ := by
      rw [←Real.exp_log sp,←Real.exp_add,←Real.exp_sub,←Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathSign
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma realSign_gridLayer {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) (j : Fin b) :
    realSign (gridLayer bits g j)=∏y, realSign (g j y) := by
  simp [gridLayer,realSign,Equiv.Perm.sign_prodCongrLeft,map_prod]

lemma realSign_gridSweep {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    realSign (gridSweep bits g)=∏j, ∏y, realSign (g j y) := by
  simp [gridSweep,map_list_prod,List.map_reverse,List.prod_reverse,
    List.map_ofFn,List.prod_ofFn,realSign_gridLayer]

lemma signed_path_integrand_factor {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g*realSign (gridSweep bits g) else 0) =
      ∏j, ∏y, if Assigns (lineInput H j y) (lineOutput H j y) (g j y) then
        lineLaw (bits j) z (g j y)*realSign (g j y) else 0 := by
  rw [pathEvent_iff_assigns,realSign_gridSweep]
  simp only [Fintype.prod_ite_zero,Finset.prod_mul_distrib,gridWeight]
  split_ifs <;> rfl

lemma signed_path_weight_factor {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0) =
      ∏j, ∏y, ∑σ : Equiv.Perm (Slot (bits j)),
        if Assigns (lineInput H j y) (lineOutput H j y) σ then
          lineLaw (bits j) z σ*realSign σ else 0 := by
  simp_rw [signed_path_integrand_factor H z]
  exact sum_prod_grid bits (fun j y σ =>
    if Assigns (lineInput H j y) (lineOutput H j y) σ then
      lineLaw (bits j) z σ*realSign σ else 0)

theorem signed_path_weight_zero_empty {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) (j : Fin b) (hj : 0<bits j)
    (y : GridOutside bits j) (hy : lineHoles H j y=0) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0)=0 := by
  rw [signed_path_weight_factor]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ y)
  have hz : IsEmpty (LinePaths H j y) := Fintype.card_eq_zero_iff.mp hy
  have ha (σ : Equiv.Perm (Slot (bits j))) :
      Assigns (lineInput H j y) (lineOutput H j y) σ := by
    intro a; exact isEmptyElim a
  simp only [ha,ite_true]
  exact lineLaw_sign_zero hj z

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseSignGeometry
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma exists_untouched_line (j : Fin b) (hh : h<Fintype.card (GridOutside bits j)) :
    ∃y : GridOutside bits j, lineHoles H j y=0 := by
  by_contra hn
  push Not at hn
  have he := Finset.sum_le_sum (s:=Finset.univ)
    (fun y _ => Nat.one_le_iff_ne_zero.mpr (hn y))
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,sum_lineHoles] at he
  omega

lemma signed_path_weight_zero_sparse (z : ℝ) (j : Fin b) (hj : 0<bits j)
    (hh : h<Fintype.card (GridOutside bits j)) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0)=0 := by
  obtain ⟨y,hy⟩ := exists_untouched_line H j hh
  exact signed_path_weight_zero_empty H z j hj y hy

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

section
attribute [local instance] Classical.propDecidable
variable {b h h' k : ℕ} {bits : Fin b → ℕ} {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma PathExtension.signed_restrict_zero (E : PathExtension H H') (z : ℝ)
    (hs : (∑g : GridChoices bits, if pathEvent H' g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0)=0) :
    (∑g : ConditionalChoices H, if pathEvent H' g.val then
      conditionalChoiceWeight H z g*realSign (remainingPerm H g.val g.property) else 0)=0 := by
  obtain ⟨g₀,hg₀⟩ := pathEvent_nonempty H
  let a := realSign (remainingPerm H g₀ hg₀)/realSign (gridSweep bits g₀)
  have hs' : (∑g : ConditionalChoices H', gridWeight bits z g.val*realSign (gridSweep bits g.val))=0 := by
    have he := sum_dite_zero (pathEvent H')
      (fun g _ => gridWeight bits z g*realSign (gridSweep bits g))
    rw [←hs]
    refine Eq.trans ?_ he.symm
    apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _; rfl
  calc
    _ = (a/conditionalNormalizer H z)*
        (∑g : ConditionalChoices H, if pathEvent H' g.val then
          gridWeight bits z g.val*realSign (gridSweep bits g.val) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : pathEvent H' g.val
      · rw [ite_eq_left hg,ite_eq_left hg,remaining_realSign_factor H g ⟨g₀,hg₀⟩]
        dsimp [a,conditionalChoiceWeight]
        ring
      · simp only [ite_eq_right hg,mul_zero]
    _ = (a/conditionalNormalizer H z)*
        (∑g : ConditionalChoices H', gridWeight bits z g.val*realSign (gridSweep bits g.val)) := by
      congr 1
      exact E.sum_restrict (fun g => gridWeight bits z g.val*realSign (gridSweep bits g.val))
    _ = 0 := by rw [hs',mul_zero]

variable (H)

lemma signedPlacementEntry_zero (z : ℝ) (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hs : ∀g₀ : ConditionalChoices H,
      (∑g : GridChoices bits, if pathEvent (augmentByChoice H x g₀) g then
        gridWeight bits z g*realSign (gridSweep bits g) else 0)=0) :
    signedPlacementEntry H z x y=0 := by
  by_cases he : ∃g₀ : ConditionalChoices H, placementBijection H k g₀ x=y
  · obtain ⟨g₀,rfl⟩ := he
    have hz := (augmentByChoice_extension H x g₀).signed_restrict_zero z (hs g₀)
    refine Eq.trans ?_ hz
    unfold signedPlacementEntry
    apply Finset.sum_congr rfl
    intro g _
    simp only [placementEvent_iff_augmentation]
  · unfold signedPlacementEntry
    apply Finset.sum_eq_zero
    intro g _
    exact ite_eq_right (fun hg => he ⟨g,hg⟩)

theorem signedPlacementEntry_zero_many (z : ℝ) (j : Fin b) (hj : 0<bits j)
    (hh : h+k<Fintype.card (GridOutside bits j))
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    signedPlacementEntry H z x y=0 :=
  signedPlacementEntry_zero H z x y (fun g₀ =>
    signed_path_weight_zero_sparse (augmentByChoice H x g₀) z j hj hh)

end

open Young Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma signed_partialKernel_conditional (z : ℝ) (A : Finset (Fin k))
    (x y : Placement H k 0) :
    (∑a : Equiv.Perm (FreeSlot H 0), (conditionalGroupLaw H z a*realSign a:ℂ)*partialKernel A a y x)=
      (signedPlacementEntry H z (restrictPlacement H x A)
        (restrictPlacement H (placementIdentification H k y) A):ℂ) := by
  have he := conditionalGroupLaw_expectation H z (fun a => (realSign a:ℂ)*partialKernel A a y x)
  simp only [Complex.real_smul] at he
  simp only [mul_assoc]
  rw [he]
  unfold signedPlacementEntry
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr
  · ext g; simp only [Finset.mem_univ]
  intro g _
  simp only [partialKernel, partialKernel_event H g A x y, restrictPlacement_event]
  split_ifs <;> simp

lemma signed_centeredMatrix_zero (z : ℝ)
    (hh : ∀ l ≤ k, ∀x : Placement H l 0, ∀y : Placement H l (Fin.last b),
      signedPlacementEntry H z x y=0) :
    centeredMatrix (I:=Fin k) (gridSize bits)
      (fun a => (conditionalGroupLaw H z a*realSign a:ℂ))=0 := by
  ext y x
  simp only [centeredMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro A _
  rw [signed_partialKernel_conditional H z A x y]
  have hA : Fintype.card A ≤ k := by simpa using Finset.card_le_univ A
  rw [hh _ hA,Complex.ofReal_zero,mul_zero]

theorem conditional_signed_specht_one_le_zero (μ : YoungDiagram)
    (e : Cell μ ≃ FreeSlot H 0) (a : Tail μ ≃ Fin k) (z : ℝ)
    (hh : ∀ l ≤ k, ∀x : Placement H l 0, ∀y : Placement H l (Fin.last b),
      signedPlacementEntry H z x y=0) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ 0 := by
  rw [groupAverage_comp_slots]
  have hs : (gridSize bits:ℝ)≠0 := by exact_mod_cast (gridSize_pos bits).ne'
  have he := specht_moment_one_le_centered_matrix μ (gridSize bits) hs
    (fun g => (conditionalGroupLaw H z (e.permCongr g)*realSign (e.permCongr g):ℂ))
  have hr := centeredMatrix_hs_reindex a e (gridSize bits)
    (fun g => (conditionalGroupLaw H z (e.permCongr g)*realSign (e.permCongr g):ℂ))
  simp only [Equiv.apply_symm_apply] at hr
  rw [←hr,signed_centeredMatrix_zero H z hh] at he
  simpa using he

theorem conditional_signed_specht_many (μ : YoungDiagram)
    (e : Cell μ ≃ FreeSlot H 0) (a : Tail μ ≃ Fin k) (z : ℝ)
    (j : Fin b) (hj : 0 < bits j) (hh : h+k < Fintype.card (GridOutside bits j)) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ 0 :=
  conditional_signed_specht_one_le_zero H μ e a z (fun l hl x y =>
    signedPlacementEntry_zero_many H z j hj (by omega) x y)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps
open Young Irrep

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma conditional_signed_specht_hs {k : ℕ} (μ : YoungDiagram)
    (e : Cell μ ≃ FreeSlot H 0) (a : Tail μ ≃ Fin k) (z : ℝ) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ signedCenteredHS H k z := by
  rw [groupAverage_comp_slots]
  have hs : (gridSize bits:ℝ)≠0 := by exact_mod_cast (gridSize_pos bits).ne'
  have he := specht_moment_one_le_centered_matrix μ (gridSize bits) hs
    (fun g => (conditionalGroupLaw H z (e.permCongr g)*realSign (e.permCongr g):ℂ))
  have hr := centeredMatrix_hs_reindex a e (gridSize bits)
    (fun g => (conditionalGroupLaw H z (e.permCongr g)*realSign (e.permCongr g):ℂ))
  simp only [Equiv.apply_symm_apply] at hr
  rwa [←hr] at he

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_FewSparse
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma many_sparse_sign_geometry {b h k : ℕ} {bits : Fin b → ℕ}
    (hbase : ((k+h:ℕ):ℝ)*(∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)) < 1)
    (j : Fin b) : h+k < Fintype.card (GridOutside bits j) := by
  have hp : (0:ℝ) < Fintype.card (GridOutside bits j) := by exact_mod_cast Fintype.card_pos
  have he : (1:ℝ)/Fintype.card (GridOutside bits j) ≤
      ∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j) :=
    Finset.single_le_sum (f := fun j : Fin b => (1:ℝ)/Fintype.card (GridOutside bits j)) (fun _ _ => by positivity) (Finset.mem_univ j)
  have hh := (mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ (k+h:ℕ) by positivity)).trans_lt hbase
  rw [mul_one_div] at hh
  have hl := (div_lt_one hp).mp hh
  simpa only [Nat.add_comm] using (show k+h < Fintype.card (GridOutside bits j) by exact_mod_cast hl)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_ManySparse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse Young Irrep

theorem conditional_specht_many_sparse_eventually : ∀ᶠ s : ℕ in atTop,
    ∀ b r h k : ℕ, ∀ bits : Fin b → ℕ, gridSize bits=s → 16000≤b →
    (∀j, r≤bits j ∧ bits j≤2*r) → 4000000000≤(r:ℝ)*Real.log 2 →
    ((k+h:ℕ):ℝ)≤(s:ℝ)^(1599/1600:ℝ) → h≤100000*k →
    ∀ H : PathFamily bits h, ∀ μ : YoungDiagram, ∀ e : Cell μ ≃ FreeSlot H 0,
    ∀ _a : Tail μ ≃ Fin k, ∀z : ℝ, 0≤z → z≤linePerturbationRadius r →
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ)))≤Real.exp (-(k:ℝ)*Real.log s/16000) := by
  filter_upwards [many_collision_base_eventually] with s hs
  intro b r h k bits he hb hd hr hk hh H μ e a z hz hzr
  have hL : 4000000000*(b:ℝ)≤Real.log s := by
    have hl := grid_log_lower (fun j => (hd j).1)
    rw [he] at hl
    nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg b)]
  have hbase := hs b r h k bits he hb hd (by linarith) hk
  have hl0 : 0≤Real.log (s:ℝ) := (by positivity : (0:ℝ)≤4000000000*b).trans hL
  have hsmall := hbase.trans (show Real.exp (-Real.log s/4000)≤1 by
    rw [Real.exp_le_one_iff]; linarith)
  have hbound := conditional_specht_many_bound H μ e a (fun j => (hd j).2) hz hzr
    (hzr.trans_lt (linePerturbationRadius_lt_one r)) hsmall
  exact hbound.trans (many_hs_scalar b h k (by omega) (by exact_mod_cast hh) hL
    (by positivity) hbase)

end BinaryCoordinateSweeps

end

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

lemma sum_pow_le_sum_pow {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀i,0≤a i)
    {q : ℕ} (hq : 0<q) : (∑i,a i^q) ≤ (∑i,a i)^q := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ q hq ih =>
    have hs : 0≤∑i,a i := Finset.sum_nonneg (fun i _ => ha i)
    calc
      _ = ∑i,a i^q*a i := by simp only [pow_succ]
      _ ≤ ∑i,a i^q*(∑j,a j) := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i))
          (pow_nonneg (ha i) q))
      _ = (∑i,a i^q)*(∑j,a j) := by rw [Finset.sum_mul]
      _ ≤ (∑i,a i)^q*(∑j,a j) := mul_le_mul_of_nonneg_right ih hs
      _ = _ := (pow_succ _ _).symm

lemma evenMoment_le_one_pow {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {q : ℕ} (hq : 0<q) (A : V →ₗ[ℂ] V) :
    evenMoment q A ≤ (evenMoment 1 A)^q := by
  let v := stdOrthonormalBasis ℂ V
  rw [evenMoment_orthonormalMatrix v,evenMoment_orthonormalMatrix v]
  let M := LinearMap.toMatrixOrthonormal v A
  obtain ⟨U,W,s,hs,hU,hM,hg⟩ := exists_partial_svd M
  rw [matrixMoment_of_svd M q W s hg,matrixMoment_of_svd M 1 W s hg]
  simp only [mul_one]
  simp_rw [pow_mul]
  exact sum_pow_le_sum_pow (fun i => s i^2) (fun i => sq_nonneg _) hq

lemma evenMoment_le_exp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {q : ℕ} (hq : 0<q) (A : V →ₗ[ℂ] V) (x : ℝ)
    (h : evenMoment 1 A≤Real.exp x) : evenMoment q A≤Real.exp ((q:ℝ)*x) := by
  calc
    _ ≤ (evenMoment 1 A)^q := evenMoment_le_one_pow hq A
    _ ≤ (Real.exp x)^q := pow_le_pow_left₀ (evenMoment_nonneg 1 A) h q
    _ = _ := (Real.exp_nat_mul x q).symm

end BinaryCoordinateSweeps.Irrep

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse Young Irrep

theorem sparse_uniform_radius_oai : ∃ S : ℕ, ∀ r : ℕ, 2 ≤ r →
    4000000000 ≤ (r:ℝ)*Real.log 2 →
    ∃ δ : ℝ, 0<δ ∧ δ≤linePerturbationRadius r ∧ ∀ s : ℕ, S ≤ s →
    ∀ b h k : ℕ, ∀bits : Fin b → ℕ, gridSize bits=s → 1≤b →
    (∀j,r≤bits j ∧ bits j≤2*r) → (10:ℝ)^26≤Real.log s → 1≤k →
    ((k+h:ℕ):ℝ)≤(s:ℝ)^(1599/1600:ℝ) → h≤100000*k →
    ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀e : Cell μ ≃ FreeSlot H 0,
    ∀_a : Tail μ ≃ Fin k, ∀z : ℝ, 0≤z → z≤δ →
    (evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s)) ∧
    (evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s)) := by
  obtain ⟨S,hS⟩ := eventually_atTop.mp
    (conditional_specht_many_sparse_eventually.and many_collision_base_eventually)
  refine ⟨S,?_⟩
  intro r hr hrL
  obtain ⟨δ,hδ,hbound⟩ := sparse_finite_radius r hr
  refine ⟨min δ (linePerturbationRadius r),lt_min hδ (linePerturbationRadius_pos r),min_le_right _ _,?_⟩
  intro s hSs
  obtain ⟨hs,hc⟩ := hS s hSs
  intro b h k bits he hb hd hL hk htail hh H μ e a z hz hzr
  have hzδ := hzr.trans (min_le_left _ _)
  have hzline := hzr.trans (min_le_right _ _)
  have hone :
      (evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
        (fun g => (conditionalGroupLaw H z g:ℂ)))≤Real.exp (-(k:ℝ)*Real.log s/2000000000000)) ∧
      (evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
        (fun g => (conditionalGroupLaw H z g*realSign g:ℂ)))≤Real.exp (-(k:ℝ)*Real.log s/2000000000000)) := by
    by_cases hbB : b≤16000
    · have hhS : h≤gridSize bits := by
        have hec := Fintype.card_le_of_injective (H.position 0) (H.disjoint 0)
        simpa only [Fintype.card_fin,card_gridSlot] using hec
      have hkS : k≤gridSize bits := by
        have ht : ((k+h:ℕ):ℝ)≤gridSize bits := htail.trans
          (by rw [he]; exact Real.rpow_le_self_of_one_le (by exact_mod_cast (he ▸ gridSize_pos bits)) (by norm_num))
        have : k+h≤gridSize bits := by exact_mod_cast ht
        omega
      have hf := hbound b hb hbB bits hd h k hhS hkS (by simpa only [he] using hL) hk (by simpa only [he] using htail) hh H z hz hzδ
      constructor
      · exact (conditional_specht_hs H μ e a z).trans (by simpa only [he] using hf.1)
      · exact (conditional_signed_specht_hs H μ e a z).trans (by simpa only [he] using hf.2)
    · constructor
      · refine (hs b r h k bits he (by omega) hd hrL htail hh H μ e a z hz hzline).trans ?_
        apply Real.exp_le_exp.mpr
        have : 0≤(k:ℝ)*Real.log s := mul_nonneg (Nat.cast_nonneg _) (by linarith)
        linarith
      · let j : Fin b := ⟨0,by omega⟩
        have hbase := hc b r h k bits he (by omega) hd (by linarith) htail
        have hsmall : Real.exp (-Real.log s/4000)<1 := by rw [Real.exp_lt_one_iff]; linarith
        have hgeom := many_sparse_sign_geometry (hbase.trans_lt hsmall) j
        exact (conditional_signed_specht_many H μ e a z j (by have := (hd j).1; omega) hgeom).trans
          (Real.exp_pos _).le
  have hq : 0 < mainMomentPower := by norm_num [mainMomentPower]
  constructor
  · have h := evenMoment_le_exp hq _ _ hone.1
    convert h using 1
    congr 1
    norm_num [mainMomentPower]
    ring
  · have h := evenMoment_le_exp hq _ _ hone.2
    convert h using 1
    congr 1
    norm_num [mainMomentPower]
    ring

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

end

end OAI
end

theorem solution : type_of% @OAI.BinaryCoordinateSweeps.sparse_uniform_radius_oai := @OAI.BinaryCoordinateSweeps.sparse_uniform_radius_oai
