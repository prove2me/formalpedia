-- Prove2me | solution 1 for OAI.Falconer.Regularization.scalar_weak_block_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:58:31.304247+00:00
-- url     : https://prove2.me/submissions/5225fdc2-a252-49df-8825-551f085fb51e

import Mathlib
import Definitions.Def_OAIQ088F002

section
-- module Solutions.OAIQ088_FD.Compat
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixCounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional prefix counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem prefixFiber_zero (C : Finset (CellPath d)) : prefixFiber C 0 [] = C := by
  classical
  simp [prefixFiber]

theorem prefixFiber_leaf {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {p : CellPath d} (hp : p ∈ C) : prefixFiber C N p = {p} := by
  classical
  ext q
  have hlen {path : CellPath d} (hpath : path ∈ C) : path.length = N :=
    (mem_cubePaths d N path).mp (hC hpath)
  simp only [prefixFiber, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq,he⟩
    simpa only [← hlen hq, List.take_length] using he
  · intro he; subst q
    exact ⟨hp,by rw [← hlen hp,List.take_length]⟩

theorem prefixFiber_nonempty {C : Finset (CellPath d)} {a : ℕ} {P : CellPath d}
    (hP : P ∈ C.image (List.take a)) : (prefixFiber C a P).Nonempty := by
  classical
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  exact ⟨q,by simp [prefixFiber,hq]⟩

theorem prefixFiber_card_sum {C : Finset (CellPath d)} {a b : ℕ} (hab : a ≤ b)
    (P : CellPath d) :
    (prefixFiber C a P).card =
      ∑ c ∈ prefixChildren C a b P, (prefixFiber C b c).card := by
  classical
  rw [Finset.card_eq_sum_card_image (List.take b) (prefixFiber C a P)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [prefixFiber_parent_filter hab hc]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSumCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer-cell comparison for scalar sumsets. These constant-factor
bridges allow the finite additive-combinatorial estimates to be applied
at the same scale as the parameter projections. -/
namespace Falconer
open scoped Pointwise

theorem floor_add_carry (u v : ℝ) :
    ⌊u+v⌋ = ⌊u⌋+⌊v⌋ ∨ ⌊u+v⌋ = ⌊u⌋+⌊v⌋+1 := by
  have h1 := Int.le_floor_add u v
  have h2 := Int.le_floor_add_floor u v
  omega

theorem add_scalarCells_subset (δ : ℝ) (A B : Finset ℝ) :
    scalarCells δ A+scalarCells δ B ⊆ scalarCells δ (A+B) ∪
      ((scalarCells δ (A+B)).image fun z => z-1) := by
  intro z hz
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  have hmem : ⌊a/δ+b/δ⌋ ∈ scalarCells δ (A+B) := by
    rw [← add_div]
    exact Finset.mem_image.mpr ⟨a+b,Finset.add_mem_add ha hb,rfl⟩
  rcases floor_add_carry (a/δ) (b/δ) with h | h
  · exact Finset.mem_union_left _ (h ▸ hmem)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,hmem,by omega⟩)

theorem add_scalarCells_card (δ : ℝ) (A B : Finset ℝ) :
    (scalarCells δ A+scalarCells δ B).card ≤ 2*(scalarCells δ (A+B)).card := by
  have hb := Finset.card_le_card (add_scalarCells_subset δ A B)
  have hc := Finset.card_union_le (scalarCells δ (A+B))
    ((scalarCells δ (A+B)).image fun z => z-1)
  have hi := Finset.card_image_le (s := scalarCells δ (A+B)) (f := fun z => z-1)
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRuzsa
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar discretized Ruzsa triangle inequality, with the rounding
constant stated explicitly. -/
namespace Falconer
open scoped Pointwise

theorem floor_sub_carry (u v : ℝ) :
    ⌊u-v⌋ = ⌊u⌋-⌊v⌋ ∨ ⌊u-v⌋ = ⌊u⌋-⌊v⌋-1 := by
  have h1 := Int.le_floor_add (u-v) v
  have h2 := Int.le_floor_add_floor (u-v) v
  rw [sub_add_cancel] at h1 h2
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarEnergyRefinement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the integer additive-energy refinement to separated real
sets, preserving the original points and the quantized difference bound. -/
namespace Falconer
open scoped Pointwise

theorem same_scalar_cell_dist_lt {δ x y : ℝ} (hδ : 0 < δ) (hcell : ⌊x/δ⌋ = ⌊y/δ⌋) :
    |x-y| < δ := by
  have hx0 := Int.floor_le (x/δ)
  have hx1 := Int.lt_floor_add_one (x/δ)
  have hy0 := Int.floor_le (y/δ)
  have hy1 := Int.lt_floor_add_one (y/δ)
  rw [hcell] at hx0 hx1
  have hh : |x/δ-y/δ| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_div,abs_div,abs_of_pos hδ] at hh
  exact (div_lt_one hδ).1 hh

theorem scalarCells_injective {δ : ℝ} (hδ : 0 < δ) {A : Finset ℝ}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|) :
    Set.InjOn (fun x => ⌊x/δ⌋) (A : Set ℝ) := by
  intro x hx y hy he
  by_contra hne
  exact (not_lt_of_ge (hsep x hx y hy hne)) (same_scalar_cell_dist_lt hδ he)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarGridFibers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar dyadic cell fibers for the porous grouping step. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalarGridFiber_mono (η z : ℝ) {E F : Finset ℝ} (hEF : E ⊆ F) (k : ℤ) :
    scalarGridFiber η z E k ⊆ scalarGridFiber η z F k :=
  Finset.filter_subset_filter _ hEF

 theorem scalarGridFiber_small {η μ z : ℝ} (hη : 0 < η) (hημ : η ≤ μ)
    (E : Finset ℝ) (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → μ ≤ |x-y|) (k : ℤ) :
    (scalarGridFiber η z E k).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hx,hxk⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy,hyk⟩ := Finset.mem_filter.mp hy
  by_contra hne
  have he := same_scalar_cell_dist_lt hη (hxk.trans hyk.symm)
  have hid : (x-z)-(y-z) = x-y := by ring
  rw [hid] at he
  exact (not_lt_of_ge ((hημ.trans (hsep x hx y hy hne)))) he

 theorem scalarGridFiber_double_subset (η z : ℝ) (E : Finset ℝ) (k : ℤ) :
    scalarGridFiber (2*η) z E k ⊆
      scalarGridFiber η z E (2*k) ∪ scalarGridFiber η z E (2*k+1) := by
  intro x hx
  obtain ⟨hx,hxk⟩ := Finset.mem_filter.mp hx
  have hid : (x-z)/(2*η) = ((x-z)/η)/2 := by ring
  rw [hid] at hxk
  have hf := Int.floor_div_natCast ((x-z)/η) 2
  norm_num only [Nat.cast_ofNat] at hf
  rw [hf] at hxk
  have he : ⌊(x-z)/η⌋ = 2*k ∨ ⌊(x-z)/η⌋ = 2*k+1 := by omega
  rcases he with h | h
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,h⟩)

 theorem scalarGridFiber_double_card (η z : ℝ) (E : Finset ℝ) (k : ℤ) :
    (scalarGridFiber (2*η) z E k).card ≤
      (scalarGridFiber η z E (2*k)).card+(scalarGridFiber η z E (2*k+1)).card :=
  (Finset.card_le_card (scalarGridFiber_double_subset η z E k)).trans (Finset.card_union_le _ _)

 theorem scalarGridFiber_wide {η z : ℝ} (hη : 2 < η) (E : Finset ℝ)
    (hE : ∀ x ∈ E, 0 ≤ x-z ∧ x-z ≤ 2) : scalarGridFiber η z E 0 = E := by
  apply Finset.filter_eq_self.mpr
  intro x hx
  have hη0 : 0 < η := by linarith
  apply Int.floor_eq_zero_iff.mpr
  exact ⟨div_nonneg (hE x hx).1 hη0.le,(div_lt_one hη0).2 ((hE x hx).2.trans_lt hη)⟩

 theorem scalar_grid_sum (η z : ℝ) (X : Finset ℝ) (f : ℤ → ℝ → ℝ) :
    (∑ k ∈ X.image (fun x => ⌊(x-z)/η⌋), ∑ x ∈ scalarGridFiber η z X k, f k x) =
      ∑ x ∈ X, f ⌊(x-z)/η⌋ x := by
  classical
  calc
    _ = ∑ k ∈ X.image (fun x => ⌊(x-z)/η⌋),
        ∑ x ∈ scalarGridFiber η z X k, f ⌊(x-z)/η⌋ x := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun x hx => Finset.mem_image_of_mem (fun x => ⌊(x-z)/η⌋) hx) _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarGridGrouping
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dyadic grid scale with controlled maximal occupancy. This selects
 the local groups used to treat arbitrary branching at a porous level. -/
namespace Falconer

 theorem scalar_grid_grouping_of_small_cells {h z : ℝ} (hh : 0 < h)
    (E : Finset ℝ) (hE : ∀ x ∈ E, 0 ≤ x-z ∧ x-z ≤ 2)
    (M : ℕ) (hcard : 2*M ≤ E.card)
    (hsmall : ∀ k : ℤ, (scalarGridFiber h z E k).card < 2*M) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ,
      2*M ≤ (scalarGridFiber ((2:ℝ)^n*h) z E k).card ∧
      ∀ j : ℤ, (scalarGridFiber ((2:ℝ)^n*h) z E j).card ≤ 4*M := by
  classical
  let P := fun n : ℕ => ∃ k : ℤ, 2*M ≤ (scalarGridFiber ((2:ℝ)^n*h) z E k).card
  have hex : ∃ n, P n := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 2 by norm_num)).eventually
      (Filter.eventually_gt_atTop (2/h))
    obtain ⟨n,hn⟩ := ht.exists
    have hw : 2 < (2:ℝ)^n*h := (div_lt_iff₀ hh).1 hn
    refine ⟨n,0,?_⟩
    rw [scalarGridFiber_wide hw E hE]
    exact hcard
  let n := Nat.find hex
  have hn : P n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra hn0
    have hnz : n = 0 := by omega
    obtain ⟨k,hk⟩ := hn
    rw [hnz,pow_zero,one_mul] at hk
    exact (not_lt_of_ge hk) (hsmall k)
  obtain ⟨k,hk⟩ := hn
  refine ⟨n,hn0,k,hk,?_⟩
  intro j
  have hprev : ¬ P (n-1) := Nat.find_min hex (by dsimp [n]; omega)
  have hsmall (q : ℤ) : (scalarGridFiber ((2:ℝ)^(n-1)*h) z E q).card < 2*M := by
    by_contra hq
    exact hprev ⟨q,le_of_not_gt hq⟩
  have he : (2:ℝ)^n*h = 2*((2:ℝ)^(n-1)*h) := by
    have hn_eq : n = (n-1)+1 := by omega
    conv_lhs => rw [hn_eq,pow_succ]
    ring
  rw [he]
  have hd := scalarGridFiber_double_card ((2:ℝ)^(n-1)*h) z E j
  have h1 := hsmall (2*j)
  have h2 := hsmall (2*j+1)
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPairGrouping
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous grouping for two separated child sets. Separation of
 their union is not required; the dense group may come from either side. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_pair_grid_grouping {h μ z : ℝ} (hh : 0 < h) (hhμ : h ≤ μ)
    (X Y : Finset ℝ)
    (hXbound : ∀ x ∈ X, 0 ≤ x-z ∧ x-z ≤ 2)
    (hYbound : ∀ y ∈ Y, 0 ≤ y-z ∧ y-z ≤ 2)
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → μ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → μ ≤ |x-y|)
    (M : ℕ) (hM : 2 ≤ M) (hcard : 2*M ≤ X.card) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ,
      (M ≤ (scalarGridFiber ((2:ℝ)^n*h) z X k).card ∨
       M ≤ (scalarGridFiber ((2:ℝ)^n*h) z Y k).card) ∧
      ∀ j : ℤ, (scalarGridFiber ((2:ℝ)^n*h) z X j).card ≤ 4*M ∧
        (scalarGridFiber ((2:ℝ)^n*h) z Y j).card ≤ 4*M := by
  have hEbound : ∀ x ∈ X ∪ Y, 0 ≤ x-z ∧ x-z ≤ 2 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hXbound x hx
    · exact hYbound x hx
  have hEcard : 2*M ≤ (X ∪ Y).card := hcard.trans (Finset.card_le_card (Finset.subset_union_left))
  have hunion (η : ℝ) (k : ℤ) : scalarGridFiber η z (X ∪ Y) k =
      scalarGridFiber η z X k ∪ scalarGridFiber η z Y k := by
    exact Finset.filter_union _ _ _
  have hsmall (k : ℤ) : (scalarGridFiber h z (X ∪ Y) k).card < 2*M := by
    rw [hunion]
    have hu := Finset.card_union_le (scalarGridFiber h z X k) (scalarGridFiber h z Y k)
    have hx := scalarGridFiber_small (z := z) hh hhμ X hXsep k
    have hy := scalarGridFiber_small (z := z) hh hhμ Y hYsep k
    omega
  obtain ⟨n,hn,k,hk,hall⟩ := scalar_grid_grouping_of_small_cells hh (X ∪ Y) hEbound M hEcard hsmall
  refine ⟨n,hn,k,?_,?_⟩
  · rw [hunion] at hk
    have hu := Finset.card_union_le (scalarGridFiber ((2:ℝ)^n*h) z X k)
      (scalarGridFiber ((2:ℝ)^n*h) z Y k)
    omega
  · intro j
    constructor
    · exact (Finset.card_le_card (scalarGridFiber_mono _ _ Finset.subset_union_left _)).trans (hall j)
    · exact (Finset.card_le_card (scalarGridFiber_mono _ _ Finset.subset_union_right _)).trans (hall j)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarDenseGroup
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting an exact-size dense group at a scale large enough to
 control projected overlap. The dense group can lie in either child set. -/
namespace Falconer

 theorem scalar_pair_dense_group {μ r z : ℝ} (hμ : 0 < μ) (hr : 10*r ≤ μ)
    (X Y : Finset ℝ)
    (hXbound : ∀ x ∈ X, 0 ≤ x-z ∧ x-z ≤ 2)
    (hYbound : ∀ y ∈ Y, 0 ≤ y-z ∧ y-z ≤ 2)
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → μ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → μ ≤ |x-y|)
    (M : ℕ) (hM : 2 ≤ M) (hcard : 2*M ≤ X.card) :
    ∃ η : ℝ, 0 < η ∧ 10*r ≤ η ∧ ∃ k : ℤ,
      (∀ j : ℤ, (scalarGridFiber η z X j).card ≤ 4*M ∧
        (scalarGridFiber η z Y j).card ≤ 4*M) ∧
      ((∃ F ⊆ scalarGridFiber η z X k, F.card = M) ∨
       (∃ F ⊆ scalarGridFiber η z Y k, F.card = M)) := by
  obtain ⟨n,hn,k,hk,hall⟩ := scalar_pair_grid_grouping (half_pos hμ) (by linarith : μ/2 ≤ μ)
    X Y hXbound hYbound hXsep hYsep M hM hcard
  have hp : (2:ℝ) ≤ (2:ℝ)^n := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show 1 ≤ n by omega)
    simpa only [pow_one] using h
  have hη : μ ≤ (2:ℝ)^n*(μ/2) := by nlinarith
  refine ⟨(2:ℝ)^n*(μ/2),by positivity,hr.trans hη,k,hall,?_⟩
  rcases hk with hk | hk
  · exact Or.inl (Finset.exists_subset_card_eq hk)
  · exact Or.inr (Finset.exists_subset_card_eq hk)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ScalarAffineExceptions
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional coefficient counts for separated scalar clusters. This is
 the finite real-variable separation estimate in the porous amplification
 argument; the coefficient distribution is the original finite set. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_affine_small_subset {μ R u v : ℝ} (hμ : 0 < μ)
    (hv : μ ≤ |v|) (hR : 0 ≤ R) (B : Finset ℝ) :
    B.filter (fun b => |u+b*v| ≤ R) ⊆
      B.filter (fun b => |b-(-u/v)| ≤ R/μ) := by
  intro b hb
  obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
  refine Finset.mem_filter.mpr ⟨hb,?_⟩
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv; linarith
  have hid : b-(-u/v) = (u+b*v)/v := by field_simp; ring
  rw [hid,abs_div]
  exact (div_le_div_of_nonneg_right he (abs_nonneg v)).trans
    (div_le_div_of_nonneg_left hR hμ hv)

 theorem scalar_affine_small_card {δ μ R K κ : ℝ} (hμ : 0 < μ)
    (hR : 0 ≤ R) (hscale : δ ≤ R/μ) (hscale1 : R/μ ≤ 1)
    (B : Finset ℝ)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass B u r ≤ K*r^κ*(B.card : ℝ))
    {u v : ℝ} (hv : μ ≤ |v|) :
    ((B.filter fun b => |u+b*v| ≤ R).card : ℝ) ≤
      K*(R/μ)^κ*(B.card : ℝ) := by
  calc
    _ ≤ scalarBallMass B (-u/v) (R/μ) := by
      change ((B.filter fun b => |u+b*v| ≤ R).card : ℝ) ≤
        ((B.filter fun b => |b-(-u/v)| ≤ R/μ).card : ℝ)
      exact_mod_cast Finset.card_le_card (scalar_affine_small_subset (u := u) hμ hv hR B)
    _ ≤ _ := hball _ _ hscale hscale1

 theorem scalar_bad_cluster_card {δ μ R K κ : ℝ} (hμ : 0 < μ)
    (hR : 0 ≤ R) (hRμ : R < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ R/μ) (hscale1 : R/μ ≤ 1)
    (B X Y : Finset ℝ)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → μ ≤ |x-y|)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → μ ≤ |x-y|)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass B u r ≤ K*r^κ*(B.card : ℝ)) :
    ((scalarBadClusterCoefficients B X Y R).card : ℝ) ≤
      ((X.card : ℝ)*(Y.card : ℝ))^2 * (K*(R/μ)^κ*(B.card : ℝ)) := by
  let D := X ×ˢ Y
  let E := fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
    if pq.1 = pq.2 then (∅ : Finset ℝ) else
      B.filter fun b => |(pq.1.1+b*pq.1.2)-(pq.2.1+b*pq.2.2)| ≤ R
  have hn : 0 ≤ K*(R/μ)^κ*(B.card : ℝ) := by positivity
  have hE : ∀ pq ∈ D ×ˢ D,
      ((E pq).card : ℝ) ≤ K*(R/μ)^κ*(B.card : ℝ) := by
    rintro ⟨p,q⟩ hpq
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    obtain ⟨hpx,hpy⟩ := Finset.mem_product.mp hp
    obtain ⟨hqx,hqy⟩ := Finset.mem_product.mp hq
    by_cases heq : p = q
    · simpa [E,heq] using hn
    dsimp only [E]
    simp only [ite_eq_right heq]
    by_cases hy : p.2 = q.2
    · have hx : p.1 ≠ q.1 := by intro hx; exact heq (Prod.ext hx hy)
      have hsep := hX p.1 hpx q.1 hqx hx
      have hemp : (B.filter fun b => |(p.1+b*p.2)-(q.1+b*q.2)| ≤ R) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        have hh := (Finset.mem_filter.mp hb).2
        have hid : (p.1+b*p.2)-(q.1+b*q.2) = p.1-q.1 := by rw [hy]; ring
        rw [hid] at hh
        linarith
      simpa only [hemp,Finset.card_empty,Nat.cast_zero] using hn
    · have hs := scalar_affine_small_card hμ hR hscale hscale1 B hball
        (u := p.1-q.1) (hY p.2 hpy q.2 hqy hy)
      have hid : (fun b : ℝ => |(p.1+b*p.2)-(q.1+b*q.2)| ≤ R) =
          (fun b : ℝ => |p.1-q.1+b*(p.2-q.2)| ≤ R) := by
        funext b; congr 2; ring
      have he : (B.filter fun b => |(p.1+b*p.2)-(q.1+b*q.2)| ≤ R) =
          (B.filter fun b => |p.1-q.1+b*(p.2-q.2)| ≤ R) := by
        ext b; simp only [Finset.mem_filter]; rw [congrFun hid b]
      simpa only [he] using hs
  have hsub : scalarBadClusterCoefficients B X Y R ⊆ (D ×ˢ D).biUnion E := by
    intro b hb
    obtain ⟨hb,p,hp,q,hq,hne,hsmall⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_biUnion.mpr ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,
      by simp only [E,ite_eq_right hne,Finset.mem_filter]; exact ⟨hb,hsmall⟩⟩
  calc
    _ ≤ (((D ×ˢ D).biUnion E).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ pq ∈ D ×ˢ D, ((E pq).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := D ×ˢ D) (t := E))
    _ ≤ ∑ _pq ∈ D ×ˢ D, K*(R/μ)^κ*(B.card : ℝ) := Finset.sum_le_sum hE
    _ = _ := by simp only [Finset.sum_const,Finset.card_product,D,nsmul_eq_mul,Nat.cast_mul]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClusterSums
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint scalar projection cells outside the explicitly bounded
 exceptional coefficient set. The children are the actual original
 finite clusters, so their covering numbers can be iterated. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_cells_disjoint_of_centers {δ R c d : ℝ} (hδ : 0 < δ)
    (hR : δ ≤ R) (hcd : 5*R < |c-d|)
    (A B : Finset ℝ) (hA : ∀ x ∈ A, |x-c| ≤ 2*R)
    (hB : ∀ y ∈ B, |y-d| ≤ 2*R) :
    Disjoint (scalarCells δ A) (scalarCells δ B) := by
  apply Finset.disjoint_left.mpr
  intro k hkA hkB
  obtain ⟨x,hx,hxk⟩ := Finset.mem_image.mp hkA
  obtain ⟨y,hy,hyk⟩ := Finset.mem_image.mp hkB
  have hxy := same_scalar_cell_dist_lt hδ (hxk.trans hyk.symm)
  have ht : |c-d| ≤ |x-c|+|x-y|+|y-d| := by
    calc
      |c-d| = |(c-x)+(x-y)+(y-d)| := by congr 1; ring
      _ ≤ |c-x|+|x-y|+|y-d| := (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by rw [abs_sub_comm c x]
  have ha := hA x hx
  have hb := hB y hy
  linarith

 theorem scalar_cluster_sum_near {r b x y : ℝ} (hb : |b| ≤ 1)
    (A C : Finset ℝ) (hA : ∀ a ∈ A, |a-x| ≤ r)
    (hC : ∀ c ∈ C, |c-y| ≤ r) :
    ∀ z ∈ A+C.image (fun c => b*c), |z-(x+b*y)| ≤ 2*r := by
  intro z hz
  obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
  calc
    |(a+b*c)-(x+b*y)| = |(a-x)+b*(c-y)| := by congr 1; ring
    _ ≤ |a-x|+|b*(c-y)| := abs_add_le _ _
    _ = |a-x|+|b| * |c-y| := by rw [abs_mul]
    _ ≤ r+1*r := add_le_add (hA a ha) (mul_le_mul hb (hC c hc) (abs_nonneg _) (by norm_num))
    _ = 2*r := by ring

 theorem scalar_cluster_sums_cells {δ r b : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hb : |b| ≤ 1)
    (hgood : b ∉ scalarBadClusterCoefficients B X Y (5*r))
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y, (scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card) ≤
      (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  let W := fun p : ℝ × ℝ => scalarCells δ (U p.1+(V p.2).image (fun c => b*c))
  have hdis : ((X ×ˢ Y : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).PairwiseDisjoint W := by
    intro p hp q hq hpq
    have hc : 5*r < |(p.1+b*p.2)-(q.1+b*q.2)| := by
      by_contra hn
      apply hgood
      exact Finset.mem_filter.mpr ⟨hbB,p,hp,q,hq,hpq,le_of_not_gt hn⟩
    exact scalar_cells_disjoint_of_centers hδ hr hc _ _
      (scalar_cluster_sum_near hb _ _
        (hU p.1 (Finset.mem_product.mp hp).1) (hV p.2 (Finset.mem_product.mp hp).2))
      (scalar_cluster_sum_near hb _ _
        (hU q.1 (Finset.mem_product.mp hq).1) (hV q.2 (Finset.mem_product.mp hq).2))
  have hsub : (X ×ˢ Y).biUnion W ⊆
      scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c)) := by
    intro k hk
    obtain ⟨p,hp,hkp⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hkp
    obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨a+b*c,Finset.add_mem_add ?_ ?_,rfl⟩
    · exact Finset.mem_biUnion.mpr ⟨p.1,(Finset.mem_product.mp hp).1,ha⟩
    · exact Finset.mem_image.mpr ⟨c,Finset.mem_biUnion.mpr
        ⟨p.2,(Finset.mem_product.mp hp).2,hc⟩,rfl⟩
  exact (Finset.card_biUnion hdis).symm.trans_le (Finset.card_le_card hsub)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCorrelatedWeights
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same coefficient is used at every porous scale. The following
 finite Jensen estimate averages products without any independence
 assumption on the exceptional sets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem finite_correlated_product_mean {ι β : Type*} (I : Finset ι) (B : Finset β)
    (hB : B.Nonempty) (w : ι → β → ℝ) (ell : ι → ℝ)
    (hw : ∀ i ∈ I, ∀ b ∈ B, 0 < w i b)
    (hlog : ∀ i ∈ I, (B.card : ℝ)*ell i ≤ ∑ b ∈ B, Real.log (w i b)) :
    Real.exp (∑ i ∈ I, ell i) ≤
      (∑ b ∈ B, ∏ i ∈ I, w i b)/(B.card : ℝ) := by
  classical
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hp : ∀ b ∈ B, 0 < ∏ i ∈ I, w i b := fun b hb => Finset.prod_pos (fun i hi => hw i hi b hb)
  have hs : (B.card : ℝ)*(∑ i ∈ I, ell i) ≤
      ∑ b ∈ B, Real.log (∏ i ∈ I, w i b) := by
    calc
      _ = ∑ i ∈ I, (B.card : ℝ)*ell i := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ I, ∑ b ∈ B, Real.log (w i b) := Finset.sum_le_sum hlog
      _ = ∑ b ∈ B, ∑ i ∈ I, Real.log (w i b) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun b hb => (Real.log_prod (fun i hi => (hw i hi b hb).ne')).symm)
  have he : (∑ i ∈ I, ell i) ≤
      (∑ b ∈ B, Real.log (∏ i ∈ I, w i b))/(B.card : ℝ) := by
    apply (le_div_iff₀ hn).2
    simpa only [mul_comm] using hs
  have hweight : ∑ _b ∈ B, 1/(B.card : ℝ) = 1 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_one_div_cancel hn.ne'
  have hj := convexOn_exp.map_sum_le
    (fun _b (_hb : _b ∈ B) => (div_nonneg (by norm_num : (0:ℝ) ≤ 1) hn.le))
    hweight (fun b (_hb : b ∈ B) => Set.mem_univ (Real.log (∏ i ∈ I, w i b)))
  have hsumlog : (∑ b ∈ B, (1/(B.card : ℝ))*Real.log (∏ i ∈ I, w i b)) =
      (∑ b ∈ B, Real.log (∏ i ∈ I, w i b))/(B.card : ℝ) := by
    rw [← Finset.mul_sum]
    ring
  simp only [smul_eq_mul] at hj
  rw [hsumlog] at hj
  have hexp : (∑ b ∈ B, (1/(B.card : ℝ))*Real.exp (Real.log (∏ i ∈ I, w i b))) =
      (∑ b ∈ B, ∏ i ∈ I, w i b)/(B.card : ℝ) := by
    calc
      _ = ∑ b ∈ B, (1/(B.card : ℝ))*(∏ i ∈ I, w i b) :=
        Finset.sum_congr rfl (fun b hb => by rw [Real.exp_log (hp b hb)])
      _ = _ := by rw [← Finset.mul_sum]; ring
  rw [hexp] at hj
  exact (Real.exp_le_exp.mpr he).trans hj

 theorem scalarCollisionWeight_pos {β : Type*} {L : ℝ} (hL : 0 < L) (G : Finset β) (b : β) :
    0 < scalarCollisionWeight L G b := by
  unfold scalarCollisionWeight
  split_ifs <;> positivity

 theorem scalarCollisionWeight_log_sum {β : Type*} (B G : Finset β) (hGB : G ⊆ B) (L : ℝ) :
    (∑ b ∈ B, Real.log (scalarCollisionWeight L G b)) = -(G.card : ℝ)*Real.log L := by
  classical
  have hf : B.filter (fun b => b ∈ G) = G := by ext b; simp only [Finset.mem_filter]; exact ⟨And.right,fun hb => ⟨hGB hb,hb⟩⟩
  calc
    _ = ∑ b ∈ B, if b ∈ G then -Real.log L else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbg : b ∈ G <;> simp [scalarCollisionWeight,hbg,Real.log_inv]
    _ = ∑ _b ∈ B.filter (fun b => b ∈ G), -Real.log L := (Finset.sum_filter _ _).symm
    _ = _ := by rw [hf]; simp

 theorem scalarCollisionWeight_log_bound {β : Type*} (B G : Finset β)
    (hGB : G ⊆ B) {L p : ℝ} (hL : 1 ≤ L) (hcard : (G.card : ℝ) ≤ p*(B.card : ℝ)) :
    (B.card : ℝ)*(-p*Real.log L) ≤
      ∑ b ∈ B, Real.log (scalarCollisionWeight L G b) := by
  rw [scalarCollisionWeight_log_sum B G hGB]
  have h := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hL)
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClusterWeights
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-level porous inequality, including a positive fallback weight
 for every coefficient. This permits later multiplication of the level
 weights even when their exceptional sets are correlated. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_cluster_one_column {δ r μ b : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ r) (hgap : 5*r < μ) (hb : |b| ≤ 1)
    (X Y : Finset ℝ) (y : ℝ) (hy : y ∈ Y)
    (hX : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → μ ≤ |x-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ x ∈ X, (scalarCells δ (U x+(V y).image (fun c => b*c))).card) ≤
      (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  have hg : b ∉ scalarBadClusterCoefficients {b} X {y} (5*r) := by
    intro hbad
    obtain ⟨_,p,hp,q,hq,hpq,he⟩ := Finset.mem_filter.mp hbad
    obtain ⟨hpx,hpy⟩ := Finset.mem_product.mp hp
    obtain ⟨hqx,hqy⟩ := Finset.mem_product.mp hq
    have hpy' : p.2 = y := Finset.mem_singleton.mp hpy
    have hqy' : q.2 = y := Finset.mem_singleton.mp hqy
    have hx : p.1 ≠ q.1 := by intro heq; exact hpq (Prod.ext heq (hpy'.trans hqy'.symm))
    have hh := hX p.1 hpx q.1 hqx hx
    have hid : (p.1+b*p.2)-(q.1+b*q.2) = p.1-q.1 := by rw [hpy',hqy']; ring
    rw [hid] at he
    linarith
  have hs := scalar_cluster_sums_cells hδ hr {b} X {y} (Finset.mem_singleton_self b)
    hb hg U V hU (fun z hz => by simpa only [Finset.mem_singleton.mp hz] using hV)
  simp only [Finset.sum_product,Finset.sum_singleton,Finset.singleton_biUnion] at hs
  apply hs.trans
  apply Finset.card_le_card
  apply Finset.image_subset_image
  apply Finset.add_subset_add (Finset.Subset.refl _)
  apply Finset.image_subset_image
  intro c hc
  exact Finset.mem_biUnion.mpr ⟨y,hy,hc⟩

 theorem scalar_cluster_fallback {δ r μ b : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ r) (hgap : 5*r < μ) (hb : |b| ≤ 1)
    (X Y : Finset ℝ)
    (hX : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → μ ≤ |x-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y, (scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card) ≤
      Y.card*(scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  rw [Finset.sum_product,Finset.sum_comm]
  calc
    _ ≤ ∑ _y ∈ Y, (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card :=
      Finset.sum_le_sum (fun y hy => scalar_cluster_one_column hδ hr hgap hb X Y y hy hX U V hU (hV y hy))
    _ = _ := by simp

 theorem scalar_cluster_weighted_cells {δ r μ b : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ r) (hgap : 5*r < μ) (hb : |b| ≤ 1)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hY : Y.Nonempty)
    (hX : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → μ ≤ |x-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    scalarCollisionWeight (Y.card : ℝ) (scalarBadClusterCoefficients B X Y (5*r)) b *
      (∑ p ∈ X ×ˢ Y, ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
      ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
  by_cases hg : b ∈ scalarBadClusterCoefficients B X Y (5*r)
  · simp only [scalarCollisionWeight,ite_eq_left hg]
    have hs : (∑ p ∈ X ×ˢ Y, ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
        (Y.card : ℝ)*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
      exact_mod_cast scalar_cluster_fallback hδ hr hgap hb X Y hX U V hU hV
    have hn : 0 < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
    calc
      _ ≤ (Y.card : ℝ)⁻¹*((Y.card : ℝ)*
          ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul]
  · simp only [scalarCollisionWeight,ite_eq_right hg,one_mul]
    exact_mod_cast scalar_cluster_sums_cells hδ hr B X Y hbB hb hg U V hU hV

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarGroupGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded overlap of projections of consecutive groups in a
 scalar grid. This keeps the cost independent of the total branching. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_group_index_near {η δ r b x y u v z w : ℝ} {j k q : ℤ}
    (hη : 0 < η) (hδ : 0 < δ) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : ⌊(x-z)/η⌋ = k) (hy : ⌊(y-w)/η⌋ = j)
    (hu : |u-x| ≤ r) (hv : |v-y| ≤ r)
    (hq : ⌊(u+b*v)/δ⌋ = q) :
    k ∈ Finset.Icc (⌊((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η⌋-4)
      (⌊((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η⌋+4) := by
  have hx0 := Int.floor_le ((x-z)/η)
  have hx1 := Int.lt_floor_add_one ((x-z)/η)
  have hy0 := Int.floor_le ((y-w)/η)
  have hy1 := Int.lt_floor_add_one ((y-w)/η)
  rw [hx] at hx0 hx1
  rw [hy] at hy0 hy1
  have hxlo : (k:ℝ)*η ≤ x-z := (le_div_iff₀ hη).1 hx0
  have hxhi : x-z < ((k:ℝ)+1)*η := (div_lt_iff₀ hη).1 hx1
  have hylo : (j:ℝ)*η ≤ y-w := (le_div_iff₀ hη).1 hy0
  have hyhi : y-w < ((j:ℝ)+1)*η := (div_lt_iff₀ hη).1 hy1
  have hyres0 : 0 ≤ y-(w+(j:ℝ)*η) := by linarith
  have hyres1 : y-(w+(j:ℝ)*η) ≤ η := by linarith
  have hbys := mul_le_mul hb1 hyres1 hyres0 (by norm_num : (0:ℝ) ≤ 1)
  have hby0 := mul_nonneg hb0 hyres0
  rw [abs_le] at hu hv
  have hbvr := mul_le_mul_of_nonneg_left hv.2 hb0
  have hbvl := mul_le_mul_of_nonneg_left hv.1 hb0
  have hbr := mul_le_mul_of_nonneg_right hb1 (hδ.le.trans hδr)
  have hq0 := Int.floor_le ((u+b*v)/δ)
  have hq1 := Int.lt_floor_add_one ((u+b*v)/δ)
  rw [hq] at hq0 hq1
  have hqlo : (q:ℝ)*δ ≤ u+b*v := (le_div_iff₀ hδ).1 hq0
  have hqhi : u+b*v < ((q:ℝ)+1)*δ := (div_lt_iff₀ hδ).1 hq1
  let t : ℝ := ((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η
  have ht : t*η = (q:ℝ)*δ-z-b*(w+(j:ℝ)*η) := by
    dsimp [t]; field_simp
  have hl := Int.floor_le t
  have hh := Int.lt_floor_add_one t
  have hfl := mul_le_mul_of_nonneg_right hl hη.le
  have hfh := mul_lt_mul_of_pos_right hh hη
  have hkl : (⌊t⌋:ℝ)-4 ≤ (k:ℝ) := by
    apply (mul_le_mul_iff_right₀ hη).1
    nlinarith
  have hku : (k:ℝ) ≤ (⌊t⌋:ℝ)+4 := by
    apply (mul_le_mul_iff_right₀ hη).1
    nlinarith
  apply Finset.mem_Icc.mpr
  dsimp only [t] at hkl hku
  constructor
  · exact_mod_cast hkl
  · exact_mod_cast hku

 theorem finite_family_sum_card_le {α β : Type*} (I : Finset α) (Z : Finset β)
    (G : α → Finset β) (C : ℕ)
    (hsub : ∀ i ∈ I, G i ⊆ Z)
    (hmul : ∀ z ∈ Z, (I.filter fun i => z ∈ G i).card ≤ C) :
    (∑ i ∈ I, (G i).card) ≤ C*Z.card := by
  classical
  have he : (∑ i ∈ I, (G i).card) =
      ∑ z ∈ Z, (I.filter fun i => z ∈ G i).card := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := I) (t := Z) (fun i z => z ∈ G i)
    have hf (i : α) (hi : i ∈ I) : Z.bipartiteAbove (fun i z => z ∈ G i) i = G i := by
      ext z; simp only [Finset.mem_bipartiteAbove]; exact ⟨And.right,fun hz => ⟨hsub i hi hz,hz⟩⟩
    calc
      _ = ∑ i ∈ I, (Z.bipartiteAbove (fun i z => z ∈ G i) i).card :=
        Finset.sum_congr rfl (fun i hi => by rw [hf i hi])
      _ = _ := h
  rw [he]
  exact (Finset.sum_le_sum hmul).trans_eq (by simp [Nat.mul_comm])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarGroupOverlap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed nine-fold overlap bound for all projected horizontal groups.
 The number of children and occupied grid cells is unrestricted. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_group_projection_overlap {δ r η b z w : ℝ} (hδ : 0 < δ)
    (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (X Y : Finset ℝ) (j : ℤ) (hYgrid : ∀ y ∈ Y, ⌊(y-w)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r) (I : Finset ℤ) :
    (∑ k ∈ I, (scalarCells δ
      (((scalarGridFiber η z X k).biUnion U)+(Y.biUnion V).image (fun c => b*c))).card) ≤
      9*(scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  let G := fun k : ℤ => scalarCells δ
    (((scalarGridFiber η z X k).biUnion U)+(Y.biUnion V).image (fun c => b*c))
  let Z := scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))
  have hsub : ∀ k ∈ I, G k ⊆ Z := by
    intro k _ q hq
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨a,ha,c,hc,rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
    refine Finset.mem_image.mpr ⟨a+c,Finset.add_mem_add ?_ hc,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨x,(Finset.mem_filter.mp hx).1,hax⟩
  apply finite_family_sum_card_le I Z G 9 hsub
  intro q _hq
  let l : ℤ := ⌊((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η⌋
  have hcontain : I.filter (fun k => q ∈ G k) ⊆ Finset.Icc (l-4) (l+4) := by
    intro k hk
    obtain ⟨_,hqk⟩ := Finset.mem_filter.mp hk
    obtain ⟨s,hs,hsq⟩ := Finset.mem_image.mp hqk
    obtain ⟨a,ha,bc,hbc,hs⟩ := Finset.mem_add.mp hs
    obtain ⟨c,hc,hbc⟩ := Finset.mem_image.mp hbc
    obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨y,hy,hcy⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨hx,hxk⟩ := Finset.mem_filter.mp hx
    have hsum : s = a+b*c := by rw [← hbc] at hs; exact hs.symm
    have hqeq : ⌊(a+b*c)/δ⌋ = q := by rw [← hsum]; exact hsq
    exact scalar_group_index_near hη hδ hδr hrη hb0 hb1 hxk
      (hYgrid y hy) (hU x hx a hax) (hV y hy c hcy) hqeq
  have hi : (Finset.Icc (l-4) (l+4)).card = 9 := by
    rw [Int.card_Icc]
    have he : l+4+1-(l-4) = (9:ℤ) := by omega
    rw [he]; rfl
  simpa only [G] using (Finset.card_le_card hcontain).trans_eq hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarGroupedWeights
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive projection weights for arbitrary total branching, after
 fixing one column group and summing all horizontal groups. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_grouped_weighted_cells {δ r μ η b z w : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hgap : 5*r < μ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hYne : Y.Nonempty)
    (j : ℤ) (hYgrid : ∀ y ∈ Y, ⌊(y-w)/η⌋ = j)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y,
      scalarCollisionWeight (Y.card : ℝ)
        (scalarBadClusterCoefficients B (scalarGridFiber η z X ⌊(p.1-z)/η⌋) Y (5*r)) b *
        ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
      9*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
  let I := X.image (fun x => ⌊(x-z)/η⌋)
  let G := fun k => scalarGridFiber η z X k
  let W := fun k => scalarCollisionWeight (Y.card : ℝ) (scalarBadClusterCoefficients B (G k) Y (5*r)) b
  let Q := fun x y => ((scalarCells δ (U x+(V y).image (fun c => b*c))).card : ℝ)
  have hb : |b| ≤ 1 := by rwa [abs_of_nonneg hb0]
  have hk (k : ℤ) : W k*(∑ p ∈ G k ×ˢ Y, Q p.1 p.2) ≤
      ((scalarCells δ (((G k).biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
    exact scalar_cluster_weighted_cells hδ hδr hgap hb B (G k) Y hbB hYne
      (fun x hx x' hx' hne => hXsep x (Finset.mem_filter.mp hx).1 x' (Finset.mem_filter.mp hx').1 hne)
      U V (fun x hx => hU x (Finset.mem_filter.mp hx).1) hV
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ I) => hk k)
  have he : (∑ k ∈ I, W k*(∑ p ∈ G k ×ˢ Y, Q p.1 p.2)) =
      ∑ p ∈ X ×ˢ Y, W ⌊(p.1-z)/η⌋*Q p.1 p.2 := by
    simp only [Finset.sum_product,Finset.mul_sum]
    exact scalar_grid_sum η z X (fun k x => ∑ y ∈ Y, W k*Q x y)
  rw [he] at hs
  have ho : (∑ k ∈ I, ((scalarCells δ (((G k).biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) ≤
      9*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
    exact_mod_cast scalar_group_projection_overlap hδ hη hδr hrη hb0 hb1 X Y j hYgrid U V hU hV I
  exact hs.trans ho

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarLogAverages
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient averages for the multiscale porous argument. -/
namespace Falconer

 theorem scalarAverage_mono {β : Type*} (B : Finset β) {f g : β → ℝ}
    (h : ∀ b ∈ B, f b ≤ g b) : scalarAverage B f ≤ scalarAverage B g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

 theorem scalarAverage_const {β : Type*} (B : Finset β) (hB : B.Nonempty) (c : ℝ) :
    scalarAverage B (fun _ => c) = c := by
  have hn : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  simp only [scalarAverage,Finset.sum_const,nsmul_eq_mul]
  field_simp

 theorem scalarAverage_add {β : Type*} (B : Finset β) (f g : β → ℝ) :
    scalarAverage B (fun b => f b+g b) = scalarAverage B f+scalarAverage B g := by
  simp only [scalarAverage,Finset.sum_add_distrib,add_div]

 theorem scalar_log_sum_ge {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    (f : ι → ℝ) (hf : ∀ i ∈ I, 0 < f i) :
    Real.log (I.card : ℝ)+scalarAverage I (fun i => Real.log (f i)) ≤
      Real.log (∑ i ∈ I, f i) := by
  have hn : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  have hw : ∑ _i ∈ I, 1/(I.card : ℝ) = 1 := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_one_div_cancel hn.ne'
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (fun _i (_hi : _i ∈ I) => (div_nonneg (by norm_num : (0:ℝ) ≤ 1) hn.le))
    hw hf
  have hsum (g : ι → ℝ) : (∑ i ∈ I, (1/(I.card : ℝ))*g i) = scalarAverage I g := by
    rw [← Finset.mul_sum]
    unfold scalarAverage
    ring
  simp only [smul_eq_mul] at hj
  rw [hsum,hsum] at hj
  have hs : 0 < ∑ i ∈ I, f i := Finset.sum_pos hf hI
  have he : Real.log (scalarAverage I f) = Real.log (∑ i ∈ I, f i)-Real.log (I.card : ℝ) := by
    exact Real.log_div hs.ne' hn.ne'
  rw [he] at hj
  linarith

 theorem scalar_average_log_sum_ge {ι β : Type*} (I : Finset ι) (B : Finset β)
    (hI : I.Nonempty) (hB : B.Nonempty) (f : ι → β → ℝ)
    (hf : ∀ i ∈ I, ∀ b ∈ B, 0 < f i b) {a : ℝ}
    (ha : ∀ i ∈ I, a ≤ scalarAverage B (fun b => Real.log (f i b))) :
    Real.log (I.card : ℝ)+a ≤ scalarAverage B (fun b => Real.log (∑ i ∈ I, f i b)) := by
  have hj := scalarAverage_mono B (fun b hb =>
    scalar_log_sum_ge I hI (fun i => f i b) (fun i hi => hf i hi b hb))
  rw [scalarAverage_add,scalarAverage_const B hB] at hj
  have he : scalarAverage B (fun b => scalarAverage I (fun i => Real.log (f i b))) =
      scalarAverage I (fun i => scalarAverage B (fun b => Real.log (f i b))) := by
    unfold scalarAverage
    rw [← Finset.sum_div,← Finset.sum_div,Finset.sum_comm]
    ring
  rw [he] at hj
  have hl := scalarAverage_mono I (fun i hi => ha i hi)
  rw [scalarAverage_const I hI] at hl
  linarith

 theorem scalar_average_weighted_children {ι β : Type*} (I : Finset ι) (B : Finset β)
    (hI : I.Nonempty) (hB : B.Nonempty) (f w : ι → β → ℝ) (q : β → ℝ)
    (hf : ∀ i ∈ I, ∀ b ∈ B, 0 < f i b)
    (hw : ∀ i ∈ I, ∀ b ∈ B, 0 < w i b)
    (hstep : ∀ b ∈ B, (∑ i ∈ I, w i b*f i b) ≤ q b)
    {a ell : ℝ} (ha : ∀ i ∈ I, a ≤ scalarAverage B (fun b => Real.log (f i b)))
    (hell : ∀ i ∈ I, ell ≤ scalarAverage B (fun b => Real.log (w i b))) :
    Real.log (I.card : ℝ)+ell+a ≤ scalarAverage B (fun b => Real.log (q b)) := by
  have ht : ∀ i ∈ I, ell+a ≤ scalarAverage B (fun b => Real.log (w i b*f i b)) := by
    intro i hi
    have he : scalarAverage B (fun b => Real.log (w i b*f i b)) =
        scalarAverage B (fun b => Real.log (w i b))+scalarAverage B (fun b => Real.log (f i b)) := by
      calc
        _ = scalarAverage B (fun b => Real.log (w i b)+Real.log (f i b)) := by
          unfold scalarAverage
          congr 1
          exact Finset.sum_congr rfl (fun b hb => Real.log_mul (hw i hi b hb).ne' (hf i hi b hb).ne')
        _ = _ := scalarAverage_add B _ _
    rw [he]
    exact add_le_add (hell i hi) (ha i hi)
  have hs := scalar_average_log_sum_ge I B hI hB (fun i b => w i b*f i b)
    (fun i hi b hb => mul_pos (hw i hi b hb) (hf i hi b hb)) ht
  have hq := scalarAverage_mono B (fun b hb => Real.log_le_log
    (Finset.sum_pos (fun i hi => mul_pos (hw i hi b hb) (hf i hi b hb)) hI) (hstep b hb))
  linarith

 theorem scalar_exp_average_log_le {β : Type*} (B : Finset β) (hB : B.Nonempty)
    (q : β → ℝ) (hq : ∀ b ∈ B, 0 < q b) :
    Real.exp (scalarAverage B (fun b => Real.log (q b))) ≤ scalarAverage B q := by
  have hn : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  have he : (B.card : ℝ)*scalarAverage B (fun b => Real.log (q b)) =
      ∑ b ∈ B, Real.log (q b) := by
    unfold scalarAverage
    field_simp
  have hh := finite_correlated_product_mean ({0} : Finset ℕ) B hB
    (fun _ b => q b) (fun _ => scalarAverage B (fun b => Real.log (q b)))
    (fun _ _ b hb => hq b hb) (fun _ _ => le_of_eq he)
  simpa only [Finset.sum_singleton,Finset.prod_singleton,scalarAverage] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPorousLevel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar porous one-level gain for actual finite sets. This combines
 separated children, the original coefficient ball bound, and logarithmic
 averaging with its explicit exceptional-set loss. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_sum_cells_pos {δ b : ℝ} (A C : Finset ℝ)
    (hA : A.Nonempty) (hC : C.Nonempty) :
    0 < ((scalarCells δ (A+C.image (fun c => b*c))).card : ℝ) := by
  classical
  obtain ⟨a,ha⟩ := hA
  obtain ⟨c,hc⟩ := hC
  have hh : (scalarCells δ (A+C.image (fun c => b*c))).Nonempty :=
    ⟨⌊(a+b*c)/δ⌋,Finset.mem_image.mpr
      ⟨a+b*c,Finset.add_mem_add ha (Finset.mem_image.mpr ⟨c,hc,rfl⟩),rfl⟩⟩
  exact_mod_cast hh.card_pos

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarGroupedGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A porous gain with unrestricted horizontal branching. Only the
 occupancy of individual horizontal groups enters the exceptional loss. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_grouped_log_gain {δ r μ η z w K κ a : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hμ : 0 < μ) (hgap : 5*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 0 ≤ b ∧ b ≤ 1)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 →
      scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (L : ℕ) (hoccupancy : ∀ k : ℤ, (scalarGridFiber η z X k).card ≤ L)
    (j : ℤ) (hYgrid : ∀ y ∈ Y, ⌊(y-w)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log ((X.card : ℝ)*(Y.card : ℝ))+a-Real.log 9-
      (((L:ℝ)*(Y.card : ℝ))^2*K*(5*r/μ)^κ)*Real.log (Y.card : ℝ) ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  classical
  let G := fun p : ℝ × ℝ => scalarBadClusterCoefficients B
    (scalarGridFiber η z X ⌊(p.1-z)/η⌋) Y (5*r)
  let p : ℝ := (((L:ℝ)*(Y.card : ℝ))^2*K*(5*r/μ)^κ)
  let W := fun x b => scalarCollisionWeight (Y.card : ℝ) (G x) b/9
  let Q := fun (x : ℝ × ℝ) (b : ℝ) => ((scalarCells δ (U x.1+(V x.2).image (fun c => b*c))).card : ℝ)
  let R := fun b => ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)
  have hr0 : 0 ≤ r := hδ.le.trans hδr
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hYn : 1 ≤ (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hwpos : ∀ x ∈ X ×ˢ Y, ∀ b ∈ B, 0 < W x b := by
    intro x _ b _
    exact div_pos (scalarCollisionWeight_pos (by linarith) (G x) b) (by norm_num)
  have hwlog : ∀ x ∈ X ×ˢ Y,
      -Real.log 9-p*Real.log (Y.card : ℝ) ≤ scalarAverage B (fun b => Real.log (W x b)) := by
    intro x _hx
    have hgb : G x ⊆ B := Finset.filter_subset _ _
    have hgc : ((G x).card : ℝ) ≤ p*(B.card : ℝ) := by
      have hh := scalar_bad_cluster_card hμ (by positivity : 0 ≤ 5*r) hgap hK hscale hscale1
        B (scalarGridFiber η z X ⌊(x.1-z)/η⌋) Y
        (fun u hu v hv huv => hXsep u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 huv)
        hYsep hball
      change ((G x).card : ℝ) ≤ _ at hh
      calc
        _ ≤ _ := hh
        _ ≤ p*(B.card : ℝ) := by
          dsimp [p]
          have hc : ((scalarGridFiber η z X ⌊(x.1-z)/η⌋).card : ℝ) ≤ (L:ℝ) := by
            exact_mod_cast hoccupancy ⌊(x.1-z)/η⌋
          have hmul := mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ (Y.card : ℝ) by positivity)
          have hsq := pow_le_pow_left₀
            (show (0:ℝ) ≤ ((scalarGridFiber η z X ⌊(x.1-z)/η⌋).card : ℝ)*(Y.card : ℝ) by positivity) hmul 2
          have hb := mul_le_mul_of_nonneg_right hsq
            (show (0:ℝ) ≤ K*(5*r/μ)^κ*(B.card : ℝ) by positivity)
          convert hb using 1
          all_goals try with_reducible_and_instances rfl
          ring
    have hmean : -p*Real.log (Y.card : ℝ) ≤
        scalarAverage B (fun b => Real.log (scalarCollisionWeight (Y.card : ℝ) (G x) b)) := by
      have hh := scalarCollisionWeight_log_bound B (G x) hgb hYn hgc
      apply (le_div_iff₀ hn).2
      change (-p*Real.log (Y.card : ℝ))*(B.card : ℝ) ≤ _
      simpa only [G,Q,R,mul_comm] using hh
    have he : scalarAverage B (fun b => Real.log (W x b)) =
        scalarAverage B (fun b => Real.log (scalarCollisionWeight (Y.card : ℝ) (G x) b))-Real.log 9 := by
      calc
        _ = scalarAverage B (fun b => Real.log (scalarCollisionWeight (Y.card : ℝ) (G x) b)+(-Real.log 9)) := by
          unfold scalarAverage
          congr 1
          apply Finset.sum_congr rfl
          intro b hb
          exact Real.log_div (scalarCollisionWeight_pos (by linarith) (G x) b).ne' (by norm_num)
        _ = _ := by rw [scalarAverage_add,scalarAverage_const B hB]; ring
    rw [he]
    linarith
  have hstep : ∀ b ∈ B, (∑ x ∈ X ×ˢ Y, W x b*Q x b) ≤ R b := by
    intro b hb
    have hh := scalar_grouped_weighted_cells (z := z) hδ hη hδr hrη hgap (hBb b hb).1 (hBb b hb).2
      B X Y hb hY j hYgrid hXsep U V hU hV
    have he : (∑ x ∈ X ×ˢ Y, W x b*Q x b) =
        (∑ x ∈ X ×ˢ Y, scalarCollisionWeight (Y.card : ℝ) (G x) b*Q x b)/9 := by
      dsimp only [W]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [he]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 9)).2
    simpa only [G,Q,R,mul_comm] using hh
  have h := scalar_average_weighted_children (X ×ˢ Y) B (hX.product hY) hB Q W R
    (fun x hx b _ => scalar_sum_cells_pos _ _ (hUne x.1 (Finset.mem_product.mp hx).1)
      (hVne x.2 (Finset.mem_product.mp hx).2)) hwpos hstep hchild hwlog
  rw [Finset.card_product,Nat.cast_mul] at h
  dsimp [p] at h
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarGroupedHalfGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit positive gain from a dense column group. The horizontal
 family may have arbitrarily many children. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_grouped_half_gain {δ r μ η z w K κ a : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hμ : 0 < μ) (hgap : 5*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 0 ≤ b ∧ b ≤ 1)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ) (hM : 6561 ≤ M) (hYcard : Y.card = M)
    (hoccupancy : ∀ k : ℤ, (scalarGridFiber η z X k).card ≤ 4*M)
    (hsmall : 16*(M:ℝ)^4*K*(5*r/μ)^κ ≤ 1/4)
    (j : ℤ) (hYgrid : ∀ y ∈ Y, ⌊(y-w)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log (X.card : ℝ)+(1/2 : ℝ)*Real.log (M:ℝ)+a ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  have hh := scalar_grouped_log_gain hδ hη hδr hrη hμ hgap hK hscale hscale1
    B X Y hB hX hY hBb hXsep hYsep hball (4*M) hoccupancy j hYgrid U V hUne hVne hU hV hchild
  rw [hYcard,Nat.cast_mul,Nat.cast_ofNat] at hh
  have hm : 0 < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hx : 0 < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  rw [Real.log_mul hx.ne' hm.ne'] at hh
  have hbase : (9:ℝ)^4 ≤ (M:ℝ) := by exact_mod_cast hM
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 9^4) hbase
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hm1 : 1 ≤ (M:ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
  have hp := mul_le_mul_of_nonneg_right hsmall (Real.log_nonneg hm1)
  have he : ((4*(M:ℝ))*(M:ℝ))^2*K*(5*r/μ)^κ = 16*(M:ℝ)^4*K*(5*r/μ)^κ := by ring
  rw [he] at hh
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarGroupReverseGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient bounds needed when reversing the two child families. -/
namespace Falconer
 theorem scalar_group_index_near_three {η δ r b x y u v z w : ℝ} {j k q : ℤ}
    (hη : 0 < η) (hδ : 0 < δ) (hδr : δ ≤ 3*r) (hrη : 10*r ≤ η)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 3)
    (hx : ⌊(x-z)/η⌋ = k) (hy : ⌊(y-w)/η⌋ = j)
    (hu : |u-x| ≤ r) (hv : |v-y| ≤ r)
    (hq : ⌊(u+b*v)/δ⌋ = q) :
    k ∈ Finset.Icc (⌊((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η⌋-8)
      (⌊((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η⌋+8) := by
  have hx0 := Int.floor_le ((x-z)/η)
  have hx1 := Int.lt_floor_add_one ((x-z)/η)
  have hy0 := Int.floor_le ((y-w)/η)
  have hy1 := Int.lt_floor_add_one ((y-w)/η)
  rw [hx] at hx0 hx1
  rw [hy] at hy0 hy1
  have hxlo : (k:ℝ)*η ≤ x-z := (le_div_iff₀ hη).1 hx0
  have hxhi : x-z < ((k:ℝ)+1)*η := (div_lt_iff₀ hη).1 hx1
  have hylo : (j:ℝ)*η ≤ y-w := (le_div_iff₀ hη).1 hy0
  have hyhi : y-w < ((j:ℝ)+1)*η := (div_lt_iff₀ hη).1 hy1
  have hyres0 : 0 ≤ y-(w+(j:ℝ)*η) := by linarith
  have hyres1 : y-(w+(j:ℝ)*η) ≤ η := by linarith
  have hbys := mul_le_mul hb1 hyres1 hyres0 (by norm_num : (0:ℝ) ≤ 3)
  have hby0 := mul_nonneg hb0 hyres0
  rw [abs_le] at hu hv
  have hbvr := mul_le_mul_of_nonneg_left hv.2 hb0
  have hbvl := mul_le_mul_of_nonneg_left hv.1 hb0
  have hbr := mul_le_mul_of_nonneg_right hb1 (by linarith : 0 ≤ r)
  have hq0 := Int.floor_le ((u+b*v)/δ)
  have hq1 := Int.lt_floor_add_one ((u+b*v)/δ)
  rw [hq] at hq0 hq1
  have hqlo : (q:ℝ)*δ ≤ u+b*v := (le_div_iff₀ hδ).1 hq0
  have hqhi : u+b*v < ((q:ℝ)+1)*δ := (div_lt_iff₀ hδ).1 hq1
  let t : ℝ := ((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η
  have ht : t*η = (q:ℝ)*δ-z-b*(w+(j:ℝ)*η) := by
    dsimp [t]; field_simp
  have hl := Int.floor_le t
  have hh := Int.lt_floor_add_one t
  have hfl := mul_le_mul_of_nonneg_right hl hη.le
  have hfh := mul_lt_mul_of_pos_right hh hη
  have hkl : (⌊t⌋:ℝ)-8 ≤ (k:ℝ) := by
    apply (mul_le_mul_iff_right₀ hη).1
    nlinarith
  have hku : (k:ℝ) ≤ (⌊t⌋:ℝ)+8 := by
    apply (mul_le_mul_iff_right₀ hη).1
    nlinarith
  apply Finset.mem_Icc.mpr
  dsimp only [t] at hkl hku
  constructor
  · exact_mod_cast hkl
  · exact_mod_cast hku

 theorem scalar_group_reverse_index_near {η δ r b x y u v z w : ℝ} {j k q : ℤ}
    (hη : 0 < η) (hδ : 0 < δ) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hb0 : 1/3 ≤ b)
    (hx : ⌊(x-z)/η⌋ = j) (hy : ⌊(y-w)/η⌋ = k)
    (hu : |u-x| ≤ r) (hv : |v-y| ≤ r)
    (hq : ⌊(u+b*v)/δ⌋ = q) :
    k ∈ Finset.Icc (⌊((q:ℝ)*(δ/b)-w-(1/b)*(z+(j:ℝ)*η))/η⌋-8)
      (⌊((q:ℝ)*(δ/b)-w-(1/b)*(z+(j:ℝ)*η))/η⌋+8) := by
  have hb : 0 < b := by linarith
  have hr : 0 ≤ r := hδ.le.trans hδr
  have hi : 1/b ≤ (3:ℝ) := (div_le_iff₀ hb).2 (by linarith)
  have hd : δ/b ≤ 3*r := (div_le_iff₀ hb).2 (by nlinarith)
  have hid : (v+(1/b)*u)/(δ/b) = (u+b*v)/δ := by
    field_simp
    ring
  have hq' : ⌊(v+(1/b)*u)/(δ/b)⌋ = q := by rw [hid]; exact hq
  exact scalar_group_index_near_three hη (div_pos hδ hb) hd hrη
    (one_div_nonneg.mpr hb.le) hi hy hx hv hu hq'

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarGroupReverseOverlap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded overlap when the fixed dense group is in the first
 coordinate. Coefficients in [1/3,1] preserve the vertical group spacing. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_group_reverse_projection_overlap {δ r η b z w : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hb0 : 1/3 ≤ b)
    (X Y : Finset ℝ) (j : ℤ) (hXgrid : ∀ x ∈ X, ⌊(x-z)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r) (I : Finset ℤ) :
    (∑ k ∈ I, (scalarCells δ
      ((X.biUnion U)+((scalarGridFiber η w Y k).biUnion V).image (fun c => b*c))).card) ≤
      17*(scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  let G := fun k : ℤ => scalarCells δ
    ((X.biUnion U)+((scalarGridFiber η w Y k).biUnion V).image (fun c => b*c))
  let Z := scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))
  have hsub : ∀ k ∈ I, G k ⊆ Z := by
    intro k _ q hq
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨a,ha,bc,hbc,rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hbc
    obtain ⟨y,hy,hcy⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_image.mpr ⟨a+b*c,Finset.add_mem_add ha
      (Finset.mem_image.mpr ⟨c,Finset.mem_biUnion.mpr ⟨y,(Finset.mem_filter.mp hy).1,hcy⟩,rfl⟩),rfl⟩
  apply finite_family_sum_card_le I Z G 17 hsub
  intro q _hq
  let l : ℤ := ⌊((q:ℝ)*(δ/b)-w-(1/b)*(z+(j:ℝ)*η))/η⌋
  have hcontain : I.filter (fun k => q ∈ G k) ⊆ Finset.Icc (l-8) (l+8) := by
    intro k hk
    obtain ⟨_,hqk⟩ := Finset.mem_filter.mp hk
    obtain ⟨s,hs,hsq⟩ := Finset.mem_image.mp hqk
    obtain ⟨a,ha,bc,hbc,hs⟩ := Finset.mem_add.mp hs
    obtain ⟨c,hc,hbc⟩ := Finset.mem_image.mp hbc
    obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨y,hy,hcy⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨hy,hyk⟩ := Finset.mem_filter.mp hy
    have hsum : s = a+b*c := by rw [← hbc] at hs; exact hs.symm
    have hqeq : ⌊(a+b*c)/δ⌋ = q := by rw [← hsum]; exact hsq
    exact scalar_group_reverse_index_near hη hδ hδr hrη hb0
      (hXgrid x hx) hyk (hU x hx a hax) (hV y hy c hcy) hqeq
  have hi : (Finset.Icc (l-8) (l+8)).card = 17 := by
    rw [Int.card_Icc]
    have he : l+8+1-(l-8) = (17:ℤ) := by omega
    rw [he]; rfl
  simpa only [G] using (Finset.card_le_card hcontain).trans_eq hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarReverseWeights
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fallback weight when the dense group is in the first coordinate.
 A positive lower coefficient bound preserves the second-coordinate gaps. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_cluster_one_row {δ r μ b : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hgap : 5*r < b*μ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (X Y : Finset ℝ) (x : ℝ) (hx : x ∈ X)
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → μ ≤ |y-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ y ∈ Y, (scalarCells δ (U x+(V y).image (fun c => b*c))).card) ≤
      (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  let G := fun y => scalarCells δ (U x+(V y).image (fun c => b*c))
  have hb : |b| ≤ 1 := by rwa [abs_of_nonneg hb0]
  have hd : (Y : Set ℝ).PairwiseDisjoint G := by
    intro y hy z hz hyz
    have hc : 5*r < |(x+b*y)-(x+b*z)| := by
      calc
        _ < b*μ := hgap
        _ ≤ b*|y-z| := mul_le_mul_of_nonneg_left (hY y hy z hz hyz) hb0
        _ = _ := by rw [show (x+b*y)-(x+b*z) = b*(y-z) by ring,abs_mul,abs_of_nonneg hb0]
    exact scalar_cells_disjoint_of_centers hδ hr hc _ _
      (scalar_cluster_sum_near hb _ _ hU (hV y hy))
      (scalar_cluster_sum_near hb _ _ hU (hV z hz))
  have hs : Y.biUnion G ⊆ scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c)) := by
    intro k hk
    obtain ⟨y,hy,hk⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨a+b*c,Finset.add_mem_add
      (Finset.mem_biUnion.mpr ⟨x,hx,ha⟩)
      (Finset.mem_image.mpr ⟨c,Finset.mem_biUnion.mpr ⟨y,hy,hc⟩,rfl⟩),rfl⟩
  exact (Finset.card_biUnion hd).symm.trans_le (Finset.card_le_card hs)

 theorem scalar_cluster_reverse_fallback {δ r μ b : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hgap : 5*r < b*μ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (X Y : Finset ℝ)
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → μ ≤ |y-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y, (scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card) ≤
      X.card*(scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  rw [Finset.sum_product]
  calc
    _ ≤ ∑ _x ∈ X, (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card :=
      Finset.sum_le_sum (fun x hx => scalar_cluster_one_row hδ hr hgap hb0 hb1 X Y x hx hY U V (hU x hx) hV)
    _ = _ := by simp

 theorem scalar_cluster_reverse_weighted_cells {δ r μ b : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hgap : 5*r < b*μ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hX : X.Nonempty)
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → μ ≤ |y-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    scalarCollisionWeight (X.card : ℝ) (scalarBadClusterCoefficients B X Y (5*r)) b *
      (∑ p ∈ X ×ˢ Y, ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
      ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
  by_cases hg : b ∈ scalarBadClusterCoefficients B X Y (5*r)
  · simp only [scalarCollisionWeight,ite_eq_left hg]
    have hs : (∑ p ∈ X ×ˢ Y, ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
        (X.card : ℝ)*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
      exact_mod_cast scalar_cluster_reverse_fallback hδ hr hgap hb0 hb1 X Y hY U V hU hV
    have hn : 0 < (X.card : ℝ) := by exact_mod_cast hX.card_pos
    calc
      _ ≤ (X.card : ℝ)⁻¹*((X.card : ℝ)*
          ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul]
  · simp only [scalarCollisionWeight,ite_eq_right hg,one_mul]
    have hb : |b| ≤ 1 := by rwa [abs_of_nonneg hb0]
    exact_mod_cast scalar_cluster_sums_cells hδ hr B X Y hbB hb hg U V hU hV

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarReverseGroupedWeights
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Grouped weights with a dense first-coordinate group. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_reverse_grouped_weighted_cells {δ r μ η b z w : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hgap : 15*r < μ) (hb0 : 1/3 ≤ b) (hb1 : b ≤ 1)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hXne : X.Nonempty)
    (j : ℤ) (hXgrid : ∀ x ∈ X, ⌊(x-z)/η⌋ = j)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y,
      scalarCollisionWeight (X.card : ℝ)
        (scalarBadClusterCoefficients B X (scalarGridFiber η w Y ⌊(p.2-w)/η⌋) (5*r)) b *
        ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
      17*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
  let I := Y.image (fun y => ⌊(y-w)/η⌋)
  let G := fun k => scalarGridFiber η w Y k
  let W := fun k => scalarCollisionWeight (X.card : ℝ) (scalarBadClusterCoefficients B X (G k) (5*r)) b
  let Q := fun x y => ((scalarCells δ (U x+(V y).image (fun c => b*c))).card : ℝ)
  have hμ : 0 < μ := by have := hδ.trans_le hδr; linarith
  have hb : 0 ≤ b := by linarith
  have hbgap : 5*r < b*μ := by nlinarith
  have hk (k : ℤ) : W k*(∑ p ∈ X ×ˢ G k, Q p.1 p.2) ≤
      ((scalarCells δ ((X.biUnion U)+((G k).biUnion V).image (fun c => b*c))).card : ℝ) := by
    exact scalar_cluster_reverse_weighted_cells hδ hδr hbgap hb hb1 B X (G k) hbB hXne
      (fun y hy y' hy' hne => hYsep y (Finset.mem_filter.mp hy).1 y' (Finset.mem_filter.mp hy').1 hne)
      U V hU (fun y hy => hV y (Finset.mem_filter.mp hy).1)
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ I) => hk k)
  have he : (∑ k ∈ I, W k*(∑ p ∈ X ×ˢ G k, Q p.1 p.2)) =
      ∑ p ∈ X ×ˢ Y, W ⌊(p.2-w)/η⌋*Q p.1 p.2 := by
    simp only [Finset.sum_product,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _hx
    exact scalar_grid_sum η w Y (fun k y => W k*Q x y)
  rw [he] at hs
  have ho : (∑ k ∈ I, ((scalarCells δ ((X.biUnion U)+((G k).biUnion V).image (fun c => b*c))).card : ℝ)) ≤
      17*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
    exact_mod_cast scalar_group_reverse_projection_overlap hδ hη hδr hrη hb0 X Y j hXgrid U V hU hV I
  exact hs.trans ho

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarReverseGroupedGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The grouped logarithmic gain when the dense group lies in the first
 coordinate. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_reverse_grouped_log_gain {δ r μ η z w K κ a : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hμ : 0 < μ) (hgap : 15*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (L : ℕ) (hoccupancy : ∀ k : ℤ, (scalarGridFiber η w Y k).card ≤ L)
    (j : ℤ) (hXgrid : ∀ x ∈ X, ⌊(x-z)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log ((X.card : ℝ)*(Y.card : ℝ))+a-Real.log 17-
      (((X.card : ℝ)*(L:ℝ))^2*K*(5*r/μ)^κ)*Real.log (X.card : ℝ) ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  classical
  let G := fun p : ℝ × ℝ => scalarBadClusterCoefficients B X
    (scalarGridFiber η w Y ⌊(p.2-w)/η⌋) (5*r)
  let p : ℝ := (((X.card : ℝ)*(L:ℝ))^2*K*(5*r/μ)^κ)
  let W := fun x b => scalarCollisionWeight (X.card : ℝ) (G x) b/17
  let Q := fun (x : ℝ × ℝ) (b : ℝ) => ((scalarCells δ (U x.1+(V x.2).image (fun c => b*c))).card : ℝ)
  let R := fun b => ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)
  have hr0 : 0 ≤ r := hδ.le.trans hδr
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hXn : 1 ≤ (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hwpos : ∀ x ∈ X ×ˢ Y, ∀ b ∈ B, 0 < W x b := by
    intro x _ b _
    exact div_pos (scalarCollisionWeight_pos (by linarith) (G x) b) (by norm_num)
  have hwlog : ∀ x ∈ X ×ˢ Y,
      -Real.log 17-p*Real.log (X.card : ℝ) ≤ scalarAverage B (fun b => Real.log (W x b)) := by
    intro x _hx
    have hgb : G x ⊆ B := Finset.filter_subset _ _
    have hgc : ((G x).card : ℝ) ≤ p*(B.card : ℝ) := by
      have hh := scalar_bad_cluster_card hμ (by positivity : 0 ≤ 5*r) (by linarith : 5*r < μ)
        hK hscale hscale1 B X (scalarGridFiber η w Y ⌊(x.2-w)/η⌋) hXsep
        (fun u hu v hv huv => hYsep u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 huv) hball
      change ((G x).card : ℝ) ≤ _ at hh
      calc
        _ ≤ _ := hh
        _ ≤ p*(B.card : ℝ) := by
          dsimp [p]
          have hc : ((scalarGridFiber η w Y ⌊(x.2-w)/η⌋).card : ℝ) ≤ (L:ℝ) := by
            exact_mod_cast hoccupancy ⌊(x.2-w)/η⌋
          have hmul := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ (X.card : ℝ) by positivity)
          have hsq := pow_le_pow_left₀
            (show (0:ℝ) ≤ (X.card : ℝ)*((scalarGridFiber η w Y ⌊(x.2-w)/η⌋).card : ℝ) by positivity) hmul 2
          have hb := mul_le_mul_of_nonneg_right hsq
            (show (0:ℝ) ≤ K*(5*r/μ)^κ*(B.card : ℝ) by positivity)
          convert hb using 1
          all_goals try with_reducible_and_instances rfl
          ring
    have hmean : -p*Real.log (X.card : ℝ) ≤
        scalarAverage B (fun b => Real.log (scalarCollisionWeight (X.card : ℝ) (G x) b)) := by
      have hh := scalarCollisionWeight_log_bound B (G x) hgb hXn hgc
      apply (le_div_iff₀ hn).2
      change (-p*Real.log (X.card : ℝ))*(B.card : ℝ) ≤ _
      simpa only [mul_comm] using hh
    have he : scalarAverage B (fun b => Real.log (W x b)) =
        scalarAverage B (fun b => Real.log (scalarCollisionWeight (X.card : ℝ) (G x) b))-Real.log 17 := by
      calc
        _ = scalarAverage B (fun b => Real.log (scalarCollisionWeight (X.card : ℝ) (G x) b)+(-Real.log 17)) := by
          unfold scalarAverage
          congr 1
          apply Finset.sum_congr rfl
          intro b hb
          exact Real.log_div (scalarCollisionWeight_pos (by linarith) (G x) b).ne' (by norm_num)
        _ = _ := by rw [scalarAverage_add,scalarAverage_const B hB]; ring
    rw [he]
    linarith
  have hstep : ∀ b ∈ B, (∑ x ∈ X ×ˢ Y, W x b*Q x b) ≤ R b := by
    intro b hb
    have hh := scalar_reverse_grouped_weighted_cells (w := w) hδ hη hδr hrη hgap
      (hBb b hb).1 (hBb b hb).2 B X Y hb hX j hXgrid hYsep U V hU hV
    have he : (∑ x ∈ X ×ˢ Y, W x b*Q x b) =
        (∑ x ∈ X ×ˢ Y, scalarCollisionWeight (X.card : ℝ) (G x) b*Q x b)/17 := by
      dsimp only [W]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [he]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 17)).2
    simpa only [G,Q,R,mul_comm] using hh
  have h := scalar_average_weighted_children (X ×ˢ Y) B (hX.product hY) hB Q W R
    (fun x hx b _ => scalar_sum_cells_pos _ _ (hUne x.1 (Finset.mem_product.mp hx).1)
      (hVne x.2 (Finset.mem_product.mp hx).2)) hwpos hstep hchild hwlog
  rw [Finset.card_product,Nat.cast_mul] at h
  dsimp [p] at h
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarReverseGroupedHalfGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit positive gain from a dense first-coordinate group. The second-coordinate
 family may have arbitrarily many children. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_reverse_grouped_half_gain {δ r μ η z w K κ a : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hμ : 0 < μ) (hgap : 15*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ) (hM : 83521 ≤ M) (hXcard : X.card = M)
    (hoccupancy : ∀ k : ℤ, (scalarGridFiber η w Y k).card ≤ 4*M)
    (hsmall : 16*(M:ℝ)^4*K*(5*r/μ)^κ ≤ 1/4)
    (j : ℤ) (hXgrid : ∀ x ∈ X, ⌊(x-z)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log (Y.card : ℝ)+(1/2 : ℝ)*Real.log (M:ℝ)+a ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  have hh := scalar_reverse_grouped_log_gain hδ hη hδr hrη hμ hgap hK hscale hscale1
    B X Y hB hX hY hBb hXsep hYsep hball (4*M) hoccupancy j hXgrid U V hUne hVne hU hV hchild
  rw [hXcard,Nat.cast_mul,Nat.cast_ofNat] at hh
  have hm : 0 < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hy : 0 < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  rw [Real.log_mul hm.ne' hy.ne'] at hh
  have hbase : (17:ℝ)^4 ≤ (M:ℝ) := by exact_mod_cast hM
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 17^4) hbase
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hm1 : 1 ≤ (M:ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
  have hp := mul_le_mul_of_nonneg_right hsmall (Real.log_nonneg hm1)
  have he : ((M:ℝ)*(4*(M:ℝ)))^2*K*(5*r/μ)^κ = 16*(M:ℝ)^4*K*(5*r/μ)^κ := by ring
  rw [he] at hh
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPorousGroupingGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two orientations of the porous grouping argument assembled on
 original finite sets. Total branching is unrestricted above 2M. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_projection_log_mono (δ : ℝ) (B A C D E : Finset ℝ)
    (hA : A.Nonempty) (hC : C.Nonempty) (hAD : A ⊆ D) (hCE : C ⊆ E) :
    scalarAverage B (fun b => Real.log ((scalarCells δ (A+C.image (fun c => b*c))).card : ℝ)) ≤
      scalarAverage B (fun b => Real.log ((scalarCells δ (D+E.image (fun c => b*c))).card : ℝ)) := by
  apply scalarAverage_mono
  intro b _
  apply Real.log_le_log (scalar_sum_cells_pos A C hA hC)
  exact_mod_cast Finset.card_le_card (Finset.image_subset_image
    (Finset.add_subset_add hAD (Finset.image_subset_image hCE)))

 theorem scalar_porous_grouping_gain {δ r μ z K κ a : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hμ : 0 < μ) (hgap : 15*r < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ 5*r/μ) (hscale1 : 5*r/μ ≤ 1)
    (B X Y : Finset ℝ) (hB : B.Nonempty) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hXbound : ∀ x ∈ X, 0 ≤ x-z ∧ x-z ≤ 2)
    (hYbound : ∀ y ∈ Y, 0 ≤ y-z ∧ y-z ≤ 2)
    (hXsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → μ ≤ |x-x'|)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → μ ≤ |y-y'|)
    (hcard : X.card = Y.card)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ) (hM : 83521 ≤ M) (hMX : 2*M ≤ X.card)
    (hsmall : 16*(M:ℝ)^4*K*(5*r/μ)^κ ≤ 1/4)
    (U V : ℝ → Finset ℝ)
    (hUne : ∀ x ∈ X, (U x).Nonempty) (hVne : ∀ y ∈ Y, (V y).Nonempty)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r)
    (hchild : ∀ p ∈ X ×ˢ Y, a ≤ scalarAverage B (fun b => Real.log
      ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ))) :
    Real.log (X.card : ℝ)+(1/2 : ℝ)*Real.log (M:ℝ)+a ≤
      scalarAverage B (fun b => Real.log
        ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  obtain ⟨η,hη,hrη,j,hall,hF⟩ := scalar_pair_dense_group hμ (by linarith : 10*r ≤ μ)
    X Y hXbound hYbound hXsep hYsep M (by omega) hMX
  rcases hF with ⟨F,hF,hFc⟩ | ⟨F,hF,hFc⟩
  · have hFX : F ⊆ X := hF.trans (Finset.filter_subset _ _)
    have hFn : F.Nonempty := Finset.card_pos.mp (by rw [hFc]; omega)
    have hfgrid : ∀ x ∈ F, ⌊(x-z)/η⌋ = j := fun x hx => (Finset.mem_filter.mp (hF hx)).2
    have hg := scalar_reverse_grouped_half_gain hδ hη hδr hrη hμ hgap hK hscale hscale1
      B F Y hB hFn hY hBb
      (fun x hx x' hx' hne => hXsep x (hFX hx) x' (hFX hx') hne) hYsep hball M hM hFc
      (fun k => (hall k).2) hsmall j hfgrid U V (fun x hx => hUne x (hFX hx)) hVne
      (fun x hx => hU x (hFX hx)) hV
      (fun p hp => hchild p (Finset.mem_product.mpr ⟨hFX (Finset.mem_product.mp hp).1,(Finset.mem_product.mp hp).2⟩))
    have hu : F.biUnion U ⊆ X.biUnion U := by
      intro u hu
      obtain ⟨x,hx,hux⟩ := Finset.mem_biUnion.mp hu
      exact Finset.mem_biUnion.mpr ⟨x,hFX hx,hux⟩
    rw [← hcard] at hg
    exact hg.trans (scalar_projection_log_mono δ B _ _ _ _
      (hFn.biUnion fun x hx => hUne x (hFX hx)) (hY.biUnion hVne) hu (Finset.Subset.refl _))
  · have hFY : F ⊆ Y := hF.trans (Finset.filter_subset _ _)
    have hFn : F.Nonempty := Finset.card_pos.mp (by rw [hFc]; omega)
    have hfgrid : ∀ y ∈ F, ⌊(y-z)/η⌋ = j := fun y hy => (Finset.mem_filter.mp (hF hy)).2
    have hg := scalar_grouped_half_gain hδ hη hδr hrη hμ (by linarith : 5*r < μ) hK hscale hscale1
      B X F hB hX hFn (fun b hb => ⟨by linarith [(hBb b hb).1],(hBb b hb).2⟩)
      hXsep (fun y hy y' hy' hne => hYsep y (hFY hy) y' (hFY hy') hne) hball M (by omega) hFc
      (fun k => (hall k).1) hsmall j hfgrid U V hUne (fun y hy => hVne y (hFY hy)) hU
      (fun y hy => hV y (hFY hy))
      (fun p hp => hchild p (Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).1,hFY (Finset.mem_product.mp hp).2⟩))
    have hv : F.biUnion V ⊆ Y.biUnion V := by
      intro v hv
      obtain ⟨y,hy,hvy⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_biUnion.mpr ⟨y,hFY hy,hvy⟩
    exact hg.trans (scalar_projection_log_mono δ B _ _ _ _
      (hX.biUnion hUne) (hFn.biUnion fun y hy => hVne y (hFY hy)) (Finset.Subset.refl _) hv)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchingSuffix
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Minimal heavy suffixes for the porous level-bunching construction.
 Trimming a short terminal segment has a controlled entropy cost. -/
namespace Falconer

 theorem scalar_heavy_suffix_trim (w : ℕ → ℝ) (theta : ℝ) (N r t : ℕ)
    (hr : r ≤ N) (ht : t < r)
    (hheavy : theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i)
    (hminimal : ∀ s < r, (∑ i ∈ Finset.Ico (N-s) N, w i) ≤ theta*(s:ℝ)) :
    (∑ i ∈ Finset.Ico (N-t) N, w i) ≤ theta*(t:ℝ) ∧
      theta*((r-t:ℕ):ℝ) < ∑ i ∈ Finset.Ico (N-r) (N-t), w i := by
  have htail := hminimal t ht
  have hsum := Finset.sum_Ico_consecutive w (show N-r ≤ N-t by omega) (show N-t ≤ N by omega)
  have hcast : ((r-t:ℕ):ℝ) = (r:ℝ)-(t:ℝ) := Nat.cast_sub ht.le
  refine ⟨htail,?_⟩
  rw [hcast]
  nlinarith

 theorem scalarBunchTrim_lt {r : ℕ} (hr : 0 < r) : scalarBunchTrim r < r := by
  unfold scalarBunchTrim
  split_ifs with h
  · exact hr
  · exact Nat.div_lt_self hr (by decide)

 theorem scalarBunchTrim_budget (r : ℕ) : 100*scalarBunchTrim r ≤ r := by
  unfold scalarBunchTrim
  split_ifs
  · omega
  · have hh := Nat.div_mul_le_self r 100
    omega

 theorem scalarBunchTrim_lower {r : ℕ} (hr : 1000 < r) : r ≤ 200*scalarBunchTrim r := by
  unfold scalarBunchTrim
  rw [ite_eq_right (by omega)]
  have hmod := Nat.mod_lt r (by decide : 0 < 100)
  have hdiv := Nat.mod_add_div r 100
  omega

 theorem scalar_bunch_retained_weight (w : ℕ → ℝ) {theta : ℝ} (htheta : 0 ≤ theta)
    (N r : ℕ) (hr0 : 0 < r) (hr : r ≤ N)
    (hheavy : theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i)
    (hminimal : ∀ s < r, (∑ i ∈ Finset.Ico (N-s) N, w i) ≤ theta*(s:ℝ)) :
    (∑ i ∈ Finset.Ico (N-scalarBunchTrim r) N, w i) ≤ theta*(r:ℝ)/100 ∧
      (99/100:ℝ)*theta*(r:ℝ) <
        ∑ i ∈ Finset.Ico (N-r) (N-scalarBunchTrim r), w i := by
  have hh := scalar_heavy_suffix_trim w theta N r (scalarBunchTrim r) hr (scalarBunchTrim_lt hr0) hheavy hminimal
  have hb : 100*(scalarBunchTrim r:ℝ) ≤ (r:ℝ) := by exact_mod_cast scalarBunchTrim_budget r
  have hcost := mul_le_mul_of_nonneg_left hb htheta
  have hcast : ((r-scalarBunchTrim r:ℕ):ℝ) = (r:ℝ)-(scalarBunchTrim r:ℝ) :=
    Nat.cast_sub (scalarBunchTrim_lt hr0).le
  rw [hcast] at hh
  constructor <;> nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarBunchingLedger
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite greedy ledger for porous bunches. Its intervals partition
 a terminal range, and every omitted tail has a controlled weight loss. -/
namespace Falconer

 theorem scalar_minimal_heavy_suffix_of_exists (w : ℕ → ℝ) (theta : ℝ) (N : ℕ)
    (hex : ∃ r ≤ N, theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i) :
    ∃ r, 0 < r ∧ r ≤ N ∧ theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i ∧
      ∀ s < r, (∑ i ∈ Finset.Ico (N-s) N, w i) ≤ theta*(s:ℝ) := by
  let P := fun r : ℕ => r ≤ N ∧ theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i
  have hex' : ∃ r, P r := hex
  let r := Nat.find hex'
  have hr := Nat.find_spec hex'
  have hr0 : 0 < r := by
    by_contra hh
    have hz : r = 0 := by omega
    have hx := hr.2
    change theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i at hx
    simp only [hz,Nat.sub_zero,Finset.Ico_self,Finset.sum_empty,Nat.cast_zero,mul_zero,lt_self_iff_false] at hx
  refine ⟨r,hr0,hr.1,hr.2,?_⟩
  intro s hs
  have hh := Nat.find_min hex' hs
  exact le_of_not_gt (fun he => hh ⟨by omega,he⟩)

 theorem scalar_bunching_ledger (w : ℕ → ℝ) {theta : ℝ} (htheta : 0 ≤ theta) (N : ℕ) :
    ∃ lo : ℕ, ∃ bs : List ScalarBunch, ScalarBunchChain N lo bs ∧
      (∀ b ∈ bs, ScalarBunchGood w theta b) ∧
      ∀ r ≤ lo, (∑ i ∈ Finset.Ico (lo-r) lo, w i) ≤ theta*(r:ℝ) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hex : ∃ r ≤ N, theta*(r:ℝ) < ∑ i ∈ Finset.Ico (N-r) N, w i
    · obtain ⟨r,hr0,hrN,hr,hmin⟩ := scalar_minimal_heavy_suffix_of_exists w theta N hex
      let t := scalarBunchTrim r
      have ht : t < r := scalarBunchTrim_lt hr0
      let b : ScalarBunch := ⟨N-r,N-t,N,by omega,by omega⟩
      have hlen : b.stop-b.start = r := by dsimp [b]; omega
      have htail : b.stop-b.cut = t := by dsimp [b]; omega
      have hgood : ScalarBunchGood w theta b := by
        have hw := scalar_bunch_retained_weight w htheta N r hr0 hrN hr hmin
        refine ⟨?_,?_,?_,?_⟩
        · simpa only [b,hlen] using hw.1
        · exact (show (99/100:ℝ)*theta*((b.stop-b.start:ℕ):ℝ) <
            ∑ i ∈ Finset.Ico b.start b.cut, w i from by simpa only [b,hlen] using hw.2).le
        · rw [hlen,htail]
          exact scalarBunchTrim_budget r
        · by_cases hrs : r ≤ 1000
          · left
            constructor
            · have ht0 : t = 0 := by simp [t,scalarBunchTrim,hrs]
              dsimp [b]
              omega
            · rwa [hlen]
          · right
            rw [hlen,htail]
            exact scalarBunchTrim_lower (by omega)
      obtain ⟨lo,bs,hchain,hgoods,hstop⟩ := ih (N-r) (by omega)
      refine ⟨lo,b :: bs,ScalarBunchChain.cons b hchain,?_,hstop⟩
      intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · subst c
        exact hgood
      · exact hgoods c hc
    · refine ⟨N,[],ScalarBunchChain.nil N,by simp,?_⟩
      intro r hr
      exact le_of_not_gt (fun h => hex ⟨r,hr,h⟩)


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchingTotals
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total length, discarded weight and retained weight of the actual greedy
 bunching ledger. The loss and gain use the same covered terminal interval. -/
namespace Falconer

 theorem ScalarBunchChain.total_loss {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) {w : ℕ → ℝ} {theta : ℝ}
    (hg : ∀ b ∈ bs, ScalarBunchGood w theta b) :
    (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum ≤
      theta*((N-lo:ℕ):ℝ)/100 := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have hb := (hg b (by simp)).loss
    have hi := ih (fun c hc => hg c (by simp [hc]))
    have he : ((b.stop-lo:ℕ):ℝ) = ((b.stop-b.start:ℕ):ℝ)+((b.start-lo:ℕ):ℝ) := by
      have ho := h.start_le
      have hc := b.cut_le_stop
      have ha := b.start_lt_cut
      exact_mod_cast (show b.stop-lo = (b.stop-b.start)+(b.start-lo) by omega)
    simp only [List.map_cons,List.sum_cons]
    rw [he]
    linarith

 theorem ScalarBunchChain.total_retained {N lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain N lo bs) {w : ℕ → ℝ} {theta : ℝ}
    (hg : ∀ b ∈ bs, ScalarBunchGood w theta b) :
    (99/100:ℝ)*theta*((N-lo:ℕ):ℝ) ≤
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have hb := (hg b (by simp)).retained
    have hi := ih (fun c hc => hg c (by simp [hc]))
    have he : ((b.stop-lo:ℕ):ℝ) = ((b.stop-b.start:ℕ):ℝ)+((b.start-lo:ℕ):ℝ) := by
      have ho := h.start_le
      have hc := b.cut_le_stop
      have ha := b.start_lt_cut
      exact_mod_cast (show b.stop-lo = (b.stop-b.start)+(b.start-lo) by omega)
    simp only [List.map_cons,List.sum_cons]
    rw [he]
    linarith

 theorem scalar_bunching_total_weights (w : ℕ → ℝ) {theta : ℝ} (htheta : 0 ≤ theta) (N : ℕ) :
    ∃ lo : ℕ, ∃ bs : List ScalarBunch, ScalarBunchChain N lo bs ∧
      (∀ b ∈ bs, ScalarBunchGood w theta b) ∧
      (∑ i ∈ Finset.range lo, w i) ≤ theta*(lo:ℝ) ∧
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum ≤ theta*((N-lo:ℕ):ℝ)/100 ∧
      (99/100:ℝ)*theta*((N-lo:ℕ):ℝ) ≤
        (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum := by
  obtain ⟨lo,bs,h,hg,hs⟩ := scalar_bunching_ledger w htheta N
  refine ⟨lo,bs,h,hg,?_,h.total_loss hg,h.total_retained hg⟩
  simpa only [Nat.sub_self,Nat.Ico_zero_eq_range] using hs lo le_rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarIncrementSelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting nearly equal scalar increments among finitely many copies.
 This is the scalar pigeonhole step in the nonporous sumset construction. -/
namespace Falconer

 theorem scalar_increment_selection {ι : Type*} {ε R : ℝ} (hε : 0 < ε)
    (I : Finset ι) (d : ι → ℝ) (hd : ∀ i ∈ I, |d i| ≤ R)
    (L J : ℕ) (hJ : 0 < J) (hR : R ≤ (L:ℝ)*ε)
    (hsize : (2*L+1)*J ≤ I.card) :
    ∃ F ⊆ I, F.card = J ∧ ∃ a ∈ F, ∀ i ∈ F, |d i-d a| < ε := by
  classical
  let C := Finset.Icc (-(L:ℤ)) (L:ℤ)
  let c := fun i => ⌊d i/ε⌋
  have hC : C.card = 2*L+1 := by
    dsimp [C]
    rw [Int.card_Icc]
    omega
  have hCn : C.Nonempty := ⟨0,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  have hc : ∀ i ∈ I, c i ∈ C := by
    intro i hi
    have hiR := abs_le.mp (hd i hi)
    have hlu : -(L:ℝ) ≤ d i/ε := (le_div_iff₀ hε).2 (by nlinarith)
    have huu : d i/ε ≤ (L:ℝ) := (div_le_iff₀ hε).2 (by linarith)
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa only [Int.cast_neg,Int.cast_natCast] using hlu
    · have hh := (Int.floor_le (d i/ε)).trans huu
      exact_mod_cast hh
  have hsum : C.card • J ≤ ∑ _i ∈ I, (1:ℕ) := by
    simpa only [hC,nsmul_eq_mul,Finset.sum_const,smul_eq_mul,mul_one] using hsize
  obtain ⟨k,hk,hkJ⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hc hCn hsum
  have hj : J ≤ (I.filter fun i => c i = k).card := by simpa using hkJ
  obtain ⟨F,hF,hFc⟩ := Finset.exists_subset_card_eq hj
  have hFn : F.Nonempty := Finset.card_pos.mp (by rwa [hFc])
  obtain ⟨a,ha⟩ := hFn
  refine ⟨F,hF.trans (Finset.filter_subset _ _),hFc,a,ha,?_⟩
  intro i hi
  exact same_scalar_cell_dist_lt hε ((Finset.mem_filter.mp (hF hi)).2.trans
    (Finset.mem_filter.mp (hF ha)).2.symm)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPartialSums
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Approximate arithmetic progressions from nearly equal increments. -/
namespace Falconer

 theorem scalar_partial_sum_error {ε a : ℝ} (d : ℕ → ℝ) (J j : ℕ) (hj : j ≤ J)
    (hd : ∀ i < J, |d i-a| ≤ ε) :
    |scalarPartialSum d j-(j:ℝ)*a| ≤ (j:ℝ)*ε := by
  have he : scalarPartialSum d j-(j:ℝ)*a = ∑ i ∈ Finset.range j, (d i-a) := by
    simp only [scalarPartialSum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range j, |d i-a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j, ε := Finset.sum_le_sum (fun i hi => hd i ((Finset.mem_range.mp hi).trans_le hj))
    _ = _ := by simp

 theorem scalar_partial_sum_pair {ε a : ℝ} (d : ℕ → ℝ) (J i j : ℕ)
    (hi : i ≤ J) (hj : j ≤ J) (hd : ∀ k < J, |d k-a| ≤ ε) :
    |(i:ℝ)-(j:ℝ)| * |a| ≤ |scalarPartialSum d i-scalarPartialSum d j|+((i:ℝ)+(j:ℝ))*ε := by
  have h1 := scalar_partial_sum_error d J i hi hd
  have h2 := scalar_partial_sum_error d J j hj hd
  have ht : |(i:ℝ)*a-(j:ℝ)*a| ≤
      |scalarPartialSum d i-(i:ℝ)*a|+|scalarPartialSum d i-scalarPartialSum d j|+
      |scalarPartialSum d j-(j:ℝ)*a| := by
    calc
      _ = |((i:ℝ)*a-scalarPartialSum d i)+
          (scalarPartialSum d i-scalarPartialSum d j)+(scalarPartialSum d j-(j:ℝ)*a)| := by congr 1; ring
      _ ≤ |(i:ℝ)*a-scalarPartialSum d i|+|scalarPartialSum d i-scalarPartialSum d j|+
          |scalarPartialSum d j-(j:ℝ)*a| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by rw [abs_sub_comm ((i:ℝ)*a) (scalarPartialSum d i)]
  rw [← sub_mul,abs_mul] at ht
  nlinarith

 theorem scalar_partial_sums_separated {ε a ρ : ℝ} (hε : 0 ≤ ε)
    (d : ℕ → ℝ) (J : ℕ) (hd : ∀ k < J, |d k-a| ≤ ε)
    (hmargin : ρ+2*(J:ℝ)*ε ≤ |a|) :
    ∀ i ≤ J, ∀ j ≤ J, i ≠ j → ρ ≤ |scalarPartialSum d i-scalarPartialSum d j| := by
  intro i hi j hj hij
  have he : (1:ℝ) ≤ |(i:ℝ)-(j:ℝ)| := by
    have hne : (i:ℤ)-(j:ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
    have hh : (1:ℤ) ≤ |(i:ℤ)-(j:ℤ)| := Int.one_le_abs hne
    exact_mod_cast hh
  have ht := scalar_partial_sum_pair d J i j hi hj hd
  have hia : (i:ℝ) ≤ (J:ℝ) := by exact_mod_cast hi
  have hja : (j:ℝ) ≤ (J:ℝ) := by exact_mod_cast hj
  have hbound := mul_le_mul_of_nonneg_right (show (i:ℝ)+(j:ℝ) ≤ 2*(J:ℝ) by linarith) hε
  have ha := mul_le_mul_of_nonneg_right he (abs_nonneg a)
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSwitchSums
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite sum identities for changing selected coordinates. All
 switched sums remain in the same fixed-fold sumset of original points. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_switch_sum_eq {ι : Type*} (I F : Finset ι) (hFI : F ⊆ I) (p q : ι → ℝ) :
    scalarSwitchSum I F p q = (∑ i ∈ I, p i)+(∑ i ∈ F, (q i-p i)) := by
  have hf : I.filter (fun i => i ∈ F) = F := by
    ext i; simp only [Finset.mem_filter]; exact ⟨And.right,fun hi => ⟨hFI hi,hi⟩⟩
  calc
    _ = ∑ i ∈ I, (p i+(if i ∈ F then q i-p i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hif : i ∈ F <;> simp [hif]
    _ = (∑ i ∈ I, p i)+(∑ i ∈ I, if i ∈ F then q i-p i else 0) := Finset.sum_add_distrib
    _ = _ := by rw [← Finset.sum_filter,hf]

 theorem scalar_sum_mem_nsmul {ι : Type*} (I : Finset ι) (f : ι → ℝ) (A : Finset ℝ)
    (hf : ∀ i ∈ I, f i ∈ A) : (∑ i ∈ I, f i) ∈ I.card • A := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,succ_nsmul,add_comm (f i)]
    exact Finset.add_mem_add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      (hf i (Finset.mem_insert_self i I))

 theorem scalar_switch_prefix_eq {ι : Type*} [DecidableEq ι] (I : Finset ι) (p q : ι → ℝ)
    (e : ℕ → ι) (J j : ℕ) (hj : j ≤ J)
    (he : ∀ i < J, e i ∈ I) (hinj : Set.InjOn e (Finset.range J : Set ℕ)) :
    scalarSwitchSum I ((Finset.range j).image e) p q =
      (∑ i ∈ I, p i)+scalarPartialSum (fun i => q (e i)-p (e i)) j := by
  have hs : (Finset.range j).image e ⊆ I := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact he i ((Finset.mem_range.mp hi).trans_le hj)
  rw [scalar_switch_sum_eq I _ hs p q]
  congr 1
  unfold scalarPartialSum
  exact Finset.sum_image (hinj.mono (by
    intro i hi
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hj)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSwitchProgression
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonporous branching step: a fixed number of original summands
 produces an approximate arithmetic progression by switching selected
 coordinates. The coordinate ordering is retained for recursive use. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_increment_ordering {ι : Type*} [DecidableEq ι] {ε R ell : ℝ} (hε : 0 < ε)
    (I : Finset ι) (d : ι → ℝ)
    (hlo : ∀ i ∈ I, ell ≤ |d i|) (hhi : ∀ i ∈ I, |d i| ≤ R)
    (L J : ℕ) (hJ : 0 < J) (hR : R ≤ (L:ℝ)*ε)
    (hsize : (2*L+1)*J ≤ I.card) :
    ∃ e : ℕ → ι, (∀ i < J, e i ∈ I) ∧
      Set.InjOn e (Finset.range J : Set ℕ) ∧
      ∃ a : ℝ, ell ≤ |a| ∧ ∀ i < J, |d (e i)-a| < ε := by
  obtain ⟨F,hFI,hFJ,a,ha,hd⟩ := scalar_increment_selection hε I d hhi L J hJ hR hsize
  let E := (Finset.equivFinOfCardEq hFJ).symm
  let e : ℕ → ι := fun i => if hi : i < J then (E ⟨i,hi⟩).val else a
  have he : ∀ i < J, e i ∈ F := by
    intro i hi
    simpa only [e,dite_eq_left hi] using (E ⟨i,hi⟩).property
  refine ⟨e,fun i hi => hFI (he i hi),?_,d a,hlo a (hFI ha),?_⟩
  · intro i hi j hj heq
    have hiJ := Finset.mem_range.mp hi
    have hjJ := Finset.mem_range.mp hj
    have hE : E ⟨i,hiJ⟩ = E ⟨j,hjJ⟩ := by
      apply Subtype.ext
      simpa only [e,dite_eq_left hiJ,dite_eq_left hjJ] using heq
    exact congrArg Fin.val (E.injective hE)
  · intro i hi
    exact hd (e i) (he i hi)

 theorem scalar_switch_progression_separated {ι : Type*} [DecidableEq ι] (I : Finset ι) (p q : ι → ℝ)
    (e : ℕ → ι) {ε a ρ : ℝ} (hε : 0 ≤ ε) (J : ℕ)
    (he : ∀ i < J, e i ∈ I) (hinj : Set.InjOn e (Finset.range J : Set ℕ))
    (hd : ∀ i < J, |q (e i)-p (e i)-a| ≤ ε)
    (hmargin : ρ+2*(J:ℝ)*ε ≤ |a|) :
    ∀ i ≤ J, ∀ j ≤ J, i ≠ j →
      ρ ≤ |scalarSwitchSum I ((Finset.range i).image e) p q-
        scalarSwitchSum I ((Finset.range j).image e) p q| := by
  intro i hi j hj hij
  rw [scalar_switch_prefix_eq I p q e J i hi he hinj,
    scalar_switch_prefix_eq I p q e J j hj he hinj,add_sub_add_left_eq_sub]
  exact scalar_partial_sums_separated hε _ J hd hmargin i hi j hj hij

 theorem scalar_switch_prefix_displacement {ι : Type*} [DecidableEq ι] (I : Finset ι) (p q : ι → ℝ)
    (e : ℕ → ι) {R : ℝ} (J j : ℕ) (hj : j ≤ J)
    (he : ∀ i < J, e i ∈ I) (hinj : Set.InjOn e (Finset.range J : Set ℕ))
    (hd : ∀ i ∈ I, |q i-p i| ≤ R) :
    |scalarSwitchSum I ((Finset.range j).image e) p q-(∑ i ∈ I, p i)| ≤ (j:ℝ)*R := by
  rw [scalar_switch_prefix_eq I p q e J j hj he hinj,add_sub_cancel_left]
  unfold scalarPartialSum
  calc
    _ ≤ ∑ i ∈ Finset.range j, |q (e i)-p (e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j, R := Finset.sum_le_sum (fun i hi =>
      hd (e i) (he i ((Finset.mem_range.mp hi).trans_le hj)))
    _ = _ := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarBinaryBranch
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonporous binary state produces many separated children in a
 fixed-fold sumset. Only actual bit updates of original words are used. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_binary_step_tail {N k : ℕ} (c : Fin k → Fin N → Bool)
    (n : Fin N) (F : Finset (Fin k)) (hc : ∀ i, ScalarBinaryTail n (c i)) :
    ∀ i, ScalarBinaryTail ((n:ℕ)+1) (scalarBinaryStep c n F i) := by
  intro i j hj
  have hjn : j ≠ n := by intro h; subst j; omega
  unfold scalarBinaryStep
  split_ifs
  · rw [Function.update_of_ne hjn]
    exact hc i j (by omega)
  · exact hc i j (by omega)

 theorem scalar_binary_step_sum {N k : ℕ} (f : (Fin N → Bool) → ℝ)
    (c : Fin k → Fin N → Bool) (n : Fin N) (F : Finset (Fin k)) :
    scalarBinarySum f (scalarBinaryStep c n F) =
      scalarSwitchSum Finset.univ F (fun i => f (c i))
        (fun i => f (Function.update (c i) n true)) := by
  apply Finset.sum_congr rfl
  intro i hi
  unfold scalarBinaryStep
  split_ifs <;> rfl

 theorem scalar_binary_sum_mem {N k : ℕ} (f : (Fin N → Bool) → ℝ)
    (A : Finset ℝ) (hf : ∀ w, f w ∈ A) (c : Fin k → Fin N → Bool) :
    scalarBinarySum f c ∈ k • A := by
  simpa [scalarBinarySum] using scalar_sum_mem_nsmul Finset.univ (fun i => f (c i)) A
    (fun i _ => hf (c i))

 theorem scalar_binary_branch {N k : ℕ} (f : (Fin N → Bool) → ℝ)
    (c : Fin k → Fin N → Bool) (n : Fin N) (hc : ∀ i, ScalarBinaryTail n (c i))
    {ε R ell ρ : ℝ} (hε : 0 < ε)
    (hlo : ∀ w, ScalarBinaryTail n w → ell ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ w, ScalarBinaryTail n w → |f (Function.update w n true)-f w| ≤ R)
    (L J : ℕ) (hJ : 0 < J) (hR : R ≤ (L:ℝ)*ε)
    (hsize : (2*L+1)*J ≤ k) (hmargin : ρ+2*(J:ℝ)*ε ≤ ell) :
    ∃ e : ℕ → Fin k, Set.InjOn e (Finset.range J : Set ℕ) ∧
      (∀ j ≤ J, ∀ i, ScalarBinaryTail ((n:ℕ)+1)
        (scalarBinaryStep c n ((Finset.range j).image e) i)) ∧
      (∀ j ≤ J, |scalarBinarySum f (scalarBinaryStep c n ((Finset.range j).image e))-
        scalarBinarySum f c| ≤ (j:ℝ)*R) ∧
      (∀ i ≤ J, ∀ j ≤ J, i ≠ j →
        ρ ≤ |scalarBinarySum f (scalarBinaryStep c n ((Finset.range i).image e))-
          scalarBinarySum f (scalarBinaryStep c n ((Finset.range j).image e))|) := by
  let p : Fin k → ℝ := fun i => f (c i)
  let q : Fin k → ℝ := fun i => f (Function.update (c i) n true)
  have hl : ∀ i ∈ (Finset.univ : Finset (Fin k)), ell ≤ |q i-p i| :=
    fun i _ => hlo (c i) (hc i)
  have hu : ∀ i ∈ (Finset.univ : Finset (Fin k)), |q i-p i| ≤ R :=
    fun i _ => hhi (c i) (hc i)
  obtain ⟨e,he,hinj,a,ha,hd⟩ := scalar_increment_ordering hε (Finset.univ : Finset (Fin k))
    (fun i => q i-p i) hl hu L J hJ hR (by simpa using hsize)
  refine ⟨e,hinj,fun j _ => scalar_binary_step_tail c n _ hc,?_,?_⟩
  · intro j hj
    rw [scalar_binary_step_sum]
    have hh := scalar_switch_prefix_displacement Finset.univ p q e J j hj he hinj hu
    simpa only [p,q,scalarBinarySum] using hh
  · intro i hi j hj hij
    rw [scalar_binary_step_sum,scalar_binary_step_sum]
    have hh := scalar_switch_progression_separated Finset.univ p q e hε.le J he hinj
      (fun m hm => (hd m hm).le) (hmargin.trans ha) i hi j hj hij
    simpa only [p,q] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBinaryEmbedding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructing the binary point map from nested finite forks. The
 resulting map has exactly the bit-update bounds used in the sumset step. -/
namespace Falconer

 theorem scalar_binary_embedding (N : ℕ) (P : ℕ → Finset ℝ → Prop)
    (lo hi : ℕ → ℝ) (S : Finset ℝ) (hS : P 0 S)
    (hne : ∀ n ≤ N, ∀ E, P n E → E.Nonempty)
    (hstep : ∀ n < N, ∀ E, P n E → ∃ E0 E1 : Finset ℝ,
      E0 ⊆ E ∧ E1 ⊆ E ∧ P (n+1) E0 ∧ P (n+1) E1 ∧
      ∀ x ∈ E0, ∀ y ∈ E1, lo n ≤ |x-y| ∧ |x-y| ≤ hi n) :
    ∃ f : (Fin N → Bool) → ℝ, (∀ w, f w ∈ S) ∧
      ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
        lo n ≤ |f (Function.update w n true)-f w| ∧
        |f (Function.update w n true)-f w| ≤ hi n := by
  classical
  induction N generalizing P lo hi S with
  | zero =>
    obtain ⟨x,hx⟩ := hne 0 le_rfl S hS
    exact ⟨fun _ => x,fun _ => hx,fun n => Fin.elim0 n⟩
  | succ N ih =>
    obtain ⟨S0,S1,h0S,h1S,hP0,hP1,hcross⟩ := hstep 0 (by omega) S hS
    let P' := fun n E => P (n+1) E
    have hn' : ∀ n ≤ N, ∀ E, P' n E → E.Nonempty := by
      intro n hn E hE
      exact hne (n+1) (by omega) E hE
    have hs' : ∀ n < N, ∀ E, P' n E → ∃ E0 E1 : Finset ℝ,
        E0 ⊆ E ∧ E1 ⊆ E ∧ P' (n+1) E0 ∧ P' (n+1) E1 ∧
        ∀ x ∈ E0, ∀ y ∈ E1, lo (n+1) ≤ |x-y| ∧ |x-y| ≤ hi (n+1) := by
      intro n hn E hE
      exact hstep (n+1) (by omega) E hE
    obtain ⟨f0,hf0,hb0⟩ := ih P' (fun n => lo (n+1)) (fun n => hi (n+1)) S0 hP0 hn' hs'
    obtain ⟨f1,hf1,hb1⟩ := ih P' (fun n => lo (n+1)) (fun n => hi (n+1)) S1 hP1 hn' hs'
    let f : (Fin (N+1) → Bool) → ℝ := fun w => if w 0 = true then f1 (Fin.tail w) else f0 (Fin.tail w)
    refine ⟨f,?_,?_⟩
    · intro w
      dsimp only [f]
      split_ifs
      · exact h1S (hf1 _)
      · exact h0S (hf0 _)
    · intro n
      refine Fin.cases ?_ (fun j => ?_) n
      · intro w hw
        have hw0 : w 0 = false := hw 0 (by simp)
        dsimp only [f]
        simp only [Function.update_self,ite_true, if_true,hw0,Bool.false_eq_true,ite_false, if_false,Fin.tail_update_zero]
        have hh := hcross (f0 (Fin.tail w)) (hf0 _) (f1 (Fin.tail w)) (hf1 _)
        simpa only [Fin.val_zero,abs_sub_comm] using hh
      · intro w hw
        have hwt : ScalarBinaryTail j (Fin.tail w) := by
          intro q hq
          exact hw q.succ (by simpa only [Fin.val_succ] using Nat.succ_le_succ hq)
        have hzero : (0 : Fin (N+1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
        dsimp only [f]
        rw [Function.update_of_ne hzero,Fin.tail_update_succ]
        by_cases hw0 : w 0 = true
        · simp only [hw0,ite_true, if_true]
          exact hb1 j (Fin.tail w) hwt
        · simp only [ite_eq_right hw0]
          exact hb0 j (Fin.tail w) hwt

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarGridThinning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant-loss separation before selecting the intermediate branching
scale. The selected points are original points, grouped by grid residue. -/
namespace Falconer

 theorem scalar_floor_distance_lt {δ x y : ℝ} :
    |(⌊x/δ⌋:ℝ)-(⌊y/δ⌋:ℝ)| < |x/δ-y/δ|+1 := by
  have hx0 := Int.floor_le (x/δ)
  have hx1 := Int.lt_floor_add_one (x/δ)
  have hy0 := Int.floor_le (y/δ)
  have hy1 := Int.lt_floor_add_one (y/δ)
  have h1 := le_abs_self (x/δ-y/δ)
  have h2 := neg_le_abs (x/δ-y/δ)
  rw [abs_lt]
  constructor <;> linarith

 theorem scalar_residue_separation {δ x y : ℝ} (hδ : 0 < δ) (M : ℕ)
    (hcell : ⌊x/δ⌋ ≠ ⌊y/δ⌋)
    (hres : ⌊x/δ⌋ % (M:ℤ) = ⌊y/δ⌋ % (M:ℤ)) :
    ((M:ℝ)-1)*δ < |x-y| := by
  have hdvd : (M:ℤ) ∣ ⌊x/δ⌋-⌊y/δ⌋ :=
    Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hres)
  have hm : (M:ℤ) ≤ |⌊x/δ⌋-⌊y/δ⌋| := Int.le_abs_of_dvd (sub_ne_zero.mpr hcell) hdvd
  have hmR : (M:ℝ) ≤ |(⌊x/δ⌋:ℝ)-(⌊y/δ⌋:ℝ)| := by exact_mod_cast hm
  have hh := scalar_floor_distance_lt (δ := δ) (x := x) (y := y)
  rw [← sub_div,abs_div,abs_of_pos hδ] at hh
  have hlt : (M:ℝ)-1 < |x-y|/δ := by linarith
  exact (lt_div_iff₀ hδ).mp hlt

 theorem scalar_grid_thinning {δ : ℝ} (hδ : 0 < δ) (E : Finset ℝ)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ |x-y|)
    (M : ℕ) (hM : 0 < M) :
    ∃ F ⊆ E, E.card ≤ M*F.card ∧
      ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ((M:ℝ)-1)*δ < |x-y| := by
  classical
  by_cases hE : E.Nonempty
  · let code := fun x : ℝ => ⌊x/δ⌋ % (M:ℤ)
    let C := E.image code
    have hC : C.Nonempty := hE.image code
    obtain ⟨c,hc,hmax⟩ := C.exists_max_image (fun k => (E.filter fun x => code x = k).card) hC
    let F := E.filter fun x => code x = c
    have hCsub : C ⊆ Finset.Ico 0 (M:ℤ) := by
      intro k hk
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (by exact_mod_cast hM.ne'),
        Int.emod_lt_of_pos _ (by exact_mod_cast hM)⟩
    have hCc : C.card ≤ M := by
      have hh := Finset.card_le_card hCsub
      simpa only [Int.card_Ico,sub_zero,Int.toNat_natCast] using hh
    refine ⟨F,Finset.filter_subset _ _,?_,?_⟩
    · calc
        E.card = ∑ k ∈ C, (E.filter fun x => code x = k).card := Finset.card_eq_sum_card_image code E
        _ ≤ ∑ _k ∈ C, F.card := Finset.sum_le_sum hmax
        _ = C.card*F.card := by simp
        _ ≤ M*F.card := Nat.mul_le_mul_right _ hCc
    · intro x hx y hy hxy
      have hxE := (Finset.mem_filter.mp hx).1
      have hyE := (Finset.mem_filter.mp hy).1
      have hcell : ⌊x/δ⌋ ≠ ⌊y/δ⌋ := fun hh => hxy (scalarCells_injective hδ hsep hxE hyE hh)
      exact scalar_residue_separation hδ M hcell
        ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  · have hEe : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    subst E
    exact ⟨∅,Finset.Subset.refl _,by simp,by simp⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClosestScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing the intermediate dyadic scale from the closest pair of a
 finite separated set. The entire set is separated at that scale, and
 two original points witness that the scale is not unnecessarily coarse. -/
namespace Falconer

 theorem scalar_closest_pair (E : Finset ℝ) (hE : 2 ≤ E.card) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧
      ∀ u ∈ E, ∀ v ∈ E, u ≠ v → |x-y| ≤ |u-v| := by
  classical
  let P := (E.product E).filter (fun p => p.1 ≠ p.2)
  have hP : P.Nonempty := by
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < E.card by omega)
    exact ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩⟩
  obtain ⟨p,hp,hmin⟩ := P.exists_min_image (fun p => |p.1-p.2|) hP
  have hp' := Finset.mem_filter.mp hp
  have hpp := Finset.mem_product.mp hp'.1
  refine ⟨p.1,hpp.1,p.2,hpp.2,hp'.2,?_⟩
  intro u hu v hv huv
  exact hmin (u,v) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hv⟩,huv⟩)

 theorem scalar_closest_dyadic_scale (E : Finset ℝ) (hE : 2 ≤ E.card)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, |x-y| ≤ 16) :
    ∃ n : ℕ, (∀ x ∈ E, ∀ y ∈ E, x ≠ y → 8*(1/2:ℝ)^n < |x-y|) ∧
      ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧ |x-y| ≤ 16*(1/2:ℝ)^n := by
  obtain ⟨x,hx,y,hy,hxy,hmin⟩ := scalar_closest_pair E hE
  have hg : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨n,hn0,hn1⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < |x-y|/16 by positivity)
    (show |x-y|/16 ≤ 1 by linarith [hdiam x hx y hy])
    (show 0 < (1/2:ℝ) by norm_num) (show (1/2:ℝ) < 1 by norm_num)
  rw [pow_succ] at hn0
  refine ⟨n,?_,x,hx,y,hy,hxy,by linarith⟩
  intro u hu v hv huv
  have hh := hmin u hu v hv huv
  linarith

 theorem scalar_dyadic_scale_indices (n lo hi : ℕ) (g : ℝ)
    (hn0 : 8*(1/2:ℝ)^n < g) (hn1 : g ≤ 16*(1/2:ℝ)^n)
    (hlo : g ≤ (1/2:ℝ)^lo) (hhi : 1024*(1/2:ℝ)^hi ≤ g) :
    lo+3 < n ∧ n+6 ≤ hi := by
  constructor
  · by_contra hn
    have hh : (1/2:ℝ)^(lo+3) ≤ (1/2:ℝ)^n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have he : (1/2:ℝ)^(lo+3) = (1/2:ℝ)^lo/8 := by rw [pow_add]; norm_num; ring
    rw [he] at hh
    linarith
  · by_contra hn
    have hh : (1/2:ℝ)^(n+5) ≤ (1/2:ℝ)^hi :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have he : (1/2:ℝ)^(n+5) = (1/2:ℝ)^n/32 := by rw [pow_add]; norm_num; ring
    rw [he] at hh
    have hp : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) _
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarInitialChildren
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local geometric extraction at a block of the original dyadic
 tree. Large child families retain a fixed proportion and have a
 witnessed intermediate separation scale; small families can collapse. -/
namespace Falconer

 theorem scalar_initial_children (E : Finset ℝ) (lo hi : ℕ)
    (hsize : 2050 ≤ E.card)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → (1/2:ℝ)^hi ≤ |x-y|)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, |x-y| ≤ (1/2:ℝ)^lo) :
    ∃ F ⊆ E, E.card ≤ 1025*F.card ∧ 2 ≤ F.card ∧
      ∃ n : ℕ, lo+3 < n ∧ n+6 ≤ hi ∧
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → 8*(1/2:ℝ)^n < |x-y|) ∧
        ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ |x-y| ≤ 16*(1/2:ℝ)^n := by
  obtain ⟨F,hFE,hcard,hFsep⟩ := scalar_grid_thinning (pow_pos (by norm_num) hi) E hsep
    1025 (by norm_num)
  have hFc : 2 ≤ F.card := by omega
  have hFd : ∀ x ∈ F, ∀ y ∈ F, |x-y| ≤ 16 := by
    intro x hx y hy
    have hp : (1/2:ℝ)^lo ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (hdiam x (hFE hx) y (hFE hy)).trans (by linarith)
  obtain ⟨n,hn,x,hx,y,hy,hxy,hbound⟩ := scalar_closest_dyadic_scale F hFc hFd
  have hindex := scalar_dyadic_scale_indices n lo hi |x-y| (hn x hx y hy hxy) hbound
    (hdiam x (hFE hx) y (hFE hy)) (by have hh := hFsep x hx y hy hxy; norm_num at hh; exact hh.le)
  exact ⟨F,hFE,hcard,hFc,n,hindex.1,hindex.2,hn,x,hx,y,hy,hxy,hbound⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarInitialDyadic
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic branching counts with a retained close pair. This provides
 finite tags for the bottom-up scalar tree regularization. -/
namespace Falconer

 theorem scalar_initial_dyadic_children (E : Finset ℝ) (lo hi : ℕ)
    (hsize : 2050 ≤ E.card)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → (1/2:ℝ)^hi ≤ |x-y|)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, |x-y| ≤ (1/2:ℝ)^lo) :
    ∃ F ⊆ E, ∃ k n : ℕ, 1 ≤ k ∧ F.card = 2^k ∧ E.card ≤ 2050*F.card ∧
      lo+3 < n ∧ n+6 ≤ hi ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → 8*(1/2:ℝ)^n < |x-y|) ∧
      ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ |x-y| ≤ 16*(1/2:ℝ)^n := by
  classical
  obtain ⟨G,hGE,hGcard,hG2,n,hn0,hn1,hGs,x,hx,y,hy,hxy,hpair⟩ :=
    scalar_initial_children E lo hi hsize hsep hdiam
  let k := Nat.log 2 G.card
  have hk : 1 ≤ k := Nat.log_pos (by decide) hG2
  have hR2 : 2 ≤ 2^k := by
    calc
      2 = 2^1 := rfl
      _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
  have hR : 2^k ≤ G.card := Nat.pow_log_le_self 2 (by omega)
  have hpG : ({x,y} : Finset ℝ) ⊆ G := by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hx,hy⟩
  have hpc : ({x,y} : Finset ℝ).card = 2 := by simp [hxy]
  obtain ⟨F,hpF,hFG,hFc⟩ := Finset.exists_subsuperset_card_eq hpG (by rwa [hpc]) hR
  have hGc : G.card ≤ 2*(2^k) := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) G.card
    simpa only [k,pow_succ,Nat.mul_comm] using hh.le
  refine ⟨F,hFG.trans hGE,k,n,hk,hFc,?_,hn0,hn1,?_,x,?_,y,?_,hxy,hpair⟩
  · calc
      E.card ≤ 1025*G.card := hGcard
      _ ≤ 1025*(2*(2^k)) := Nat.mul_le_mul_left _ hGc
      _ = 2050*F.card := by rw [hFc]; ring
  · exact fun x hx y hy hxy => hGs x (hFG hx) y (hFG hy) hxy
  · exact hpF (by simp)
  · exact hpF (by simp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPathCenters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real coordinates of the scalar dyadic tree used in the initial
 regularization. These are the existing geometric descendants. -/
namespace Falconer

namespace Regularization

 theorem scalar_prefix_children_parent {a b : ℕ} (hab : a ≤ b)
    (L : Finset (CellPath 1)) (p : CellPath 1) :
    ∀ q ∈ prefixChildren L a b p, q.take a = p := by
  classical
  intro q hq
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  rw [List.take_take,min_eq_left hab]
  exact (Finset.mem_filter.mp hr).2

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarInitialPathChildren
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local scalar extraction on actual dyadic path children. Taking
 inverse images of selected centers retains the original child cells. -/
namespace Falconer.Regularization

 theorem scalar_initial_path_children {N a b : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hab : a ≤ b) (hb : b ≤ N) (p : CellPath 1)
    (hsize : 2050 ≤ (prefixChildren L a b p).card) :
    ∃ K ⊆ prefixChildren L a b p, ∃ k n : ℕ, 1 ≤ k ∧ K.card = 2^k ∧
      (prefixChildren L a b p).card ≤ 2050*K.card ∧ a+3 < n ∧ n+6 ≤ b ∧
      (∀ q ∈ K, ∀ r ∈ K, q ≠ r → 8*(1/2:ℝ)^n < |scalarPathCenter q-scalarPathCenter r|) ∧
      ∃ q ∈ K, ∃ r ∈ K, q ≠ r ∧ |scalarPathCenter q-scalarPathCenter r| ≤ 16*(1/2:ℝ)^n := by
  classical
  let C := prefixChildren L a b p
  let E := C.image scalarPathCenter
  have hlen := scalar_prefix_children_length (a := a) hL hb p
  have hinj := scalarPathCenter_injOn C hlen
  have hEc : E.card = C.card := Finset.card_image_of_injOn hinj
  have hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → (1/2:ℝ)^b ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    exact scalarPathCenter_separated (hlen q hq) (hlen r hr)
      (fun heq => hxy (congrArg scalarPathCenter heq))
  have hdiam : ∀ x ∈ E, ∀ y ∈ E, |x-y| ≤ (1/2:ℝ)^a := by
    intro x hx y hy
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    exact scalarPathCenter_same_parent (hlen q hq) hab
      ((scalar_prefix_children_parent hab L p q hq).trans
        (scalar_prefix_children_parent hab L p r hr).symm)
  obtain ⟨F,hFE,k,n,hk,hFc,hcard,hn0,hn1,hsepF,q,hq,r,hr,hqr,hpair⟩ :=
    scalar_initial_dyadic_children E a b (by simpa only [hEc] using hsize) hsep hdiam
  obtain ⟨K,hKC,hKF⟩ := Finset.subset_image_iff.mp hFE
  have hKc : K.card = F.card := by
    rw [← hKF]
    exact (Finset.card_image_of_injOn (hinj.mono hKC)).symm
  have hKmem : ∀ q ∈ K, scalarPathCenter q ∈ F := by
    intro q hq
    rw [← hKF]
    exact Finset.mem_image_of_mem scalarPathCenter hq
  refine ⟨K,hKC,k,n,hk,hKc.trans hFc,?_,hn0,hn1,?_,?_⟩
  · simpa only [hEc,← hKc] using hcard
  · intro q hq r hr hqr
    exact hsepF _ (hKmem q hq) _ (hKmem r hr)
      (fun heq => hqr (hinj (hKC hq) (hKC hr) heq))
  · rw [← hKF] at hq hr
    obtain ⟨q',hq',rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r',hr',rfl⟩ := Finset.mem_image.mp hr
    exact ⟨q',hq',r',hr',fun heq => hqr (congrArg scalarPathCenter heq),hpair⟩

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarPrefixPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-child pruning in the scalar dyadic tree. Lower completed levels
 retain their exact fibers, which makes bottom-up regularization stable. -/
namespace Falconer.Regularization

 theorem scalarPruneLeaves_subset (L : Finset (CellPath 1)) (a b : ℕ)
    (K : CellPath 1 → Finset (CellPath 1)) : scalarPruneLeaves L a b K ⊆ L := by
  classical
  exact Finset.filter_subset _ _

 theorem scalarPruneLeaves_children (L : Finset (CellPath 1)) (a b : ℕ)
    (K : CellPath 1 → Finset (CellPath 1)) (p : CellPath 1)
    (hK : K p ⊆ prefixChildren L a b p) :
    prefixChildren (scalarPruneLeaves L a b K) a b p = K p := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hqa := (Finset.mem_filter.mp hq).2
    have hqK := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
    rwa [hqa] at hqK
  · intro hc
    obtain ⟨q,hq,hqc⟩ := Finset.mem_image.mp (hK hc)
    have hqa := (Finset.mem_filter.mp hq).2
    apply Finset.mem_image.mpr
    refine ⟨q,?_,hqc⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,hqa⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,by rw [hqa,hqc]; exact hc⟩

 theorem scalarPruneLeaves_fiber (L : Finset (CellPath 1)) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (K : CellPath 1 → Finset (CellPath 1))
    {q : CellPath 1} (hq : q ∈ scalarPruneLeaves L a b K) :
    prefixFiber (scalarPruneLeaves L a b K) c (q.take c) = prefixFiber L c (q.take c) := by
  classical
  ext r
  simp only [prefixFiber,Finset.mem_filter]
  constructor
  · rintro ⟨hr,he⟩
    exact ⟨scalarPruneLeaves_subset L a b K hr,he⟩
  · rintro ⟨hr,he⟩
    have ha : r.take a = q.take a := take_eq_of_take_eq (hab.trans hbc) he
    have hb : r.take b = q.take b := take_eq_of_take_eq hbc he
    have hqK := (Finset.mem_filter.mp hq).2
    exact ⟨Finset.mem_filter.mpr ⟨hr,by rw [ha,hb]; exact hqK⟩,he⟩

 theorem scalarPruneLeaves_lower_children (L : Finset (CellPath 1)) {a b c d : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (K : CellPath 1 → Finset (CellPath 1))
    {q : CellPath 1} (hq : q ∈ scalarPruneLeaves L a b K) :
    prefixChildren (scalarPruneLeaves L a b K) c d (q.take c) = prefixChildren L c d (q.take c) := by
  unfold prefixChildren
  rw [scalarPruneLeaves_fiber L hab hbc K hq]

 theorem scalarPruneLeaves_fiber_card (L : Finset (CellPath 1)) {a b : ℕ}
    (hab : a ≤ b) (K : CellPath 1 → Finset (CellPath 1)) (p : CellPath 1)
    (hK : K p ⊆ prefixChildren L a b p) :
    (prefixFiber (scalarPruneLeaves L a b K) a p).card =
      ∑ c ∈ K p, (prefixFiber L b c).card := by
  classical
  rw [prefixFiber_card_sum hab,scalarPruneLeaves_children L a b K p hK]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨q,hq,hqc⟩ := Finset.mem_image.mp (hK hc)
  have hqa := (Finset.mem_filter.mp hq).2
  have hq' : q ∈ scalarPruneLeaves L a b K :=
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,by rw [hqa,hqc]; exact hc⟩
  rw [← hqc,scalarPruneLeaves_fiber L hab le_rfl K hq']

 theorem scalar_prefix_children_card_le {N a b : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hab : a ≤ b) (hb : b ≤ N) (p : CellPath 1) :
    (prefixChildren L a b p).card ≤ 2^(b-a) := by
  classical
  have hsub : prefixChildren L a b p ⊆
      (cubePaths 1 (b-a)).image (fun q => p ++ q) := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hqa := (Finset.mem_filter.mp hq).2
    have hlen := (mem_cubePaths 1 N q).mp (hL (Finset.mem_filter.mp hq).1)
    refine Finset.mem_image.mpr ⟨(q.take b).drop a,?_,?_⟩
    · simp only [mem_cubePaths,List.length_drop,List.length_take,hlen,min_eq_left hb]
    · have hh := List.take_append_drop a (q.take b)
      simpa only [List.take_take,min_eq_left hab,hqa] using hh
  calc
    _ ≤ ((cubePaths 1 (b-a)).image (fun q => p ++ q)).card := Finset.card_le_card hsub
    _ ≤ (cubePaths 1 (b-a)).card := Finset.card_image_le
    _ = _ := by simp only [card_cubePaths,one_mul]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarChildChoice
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single local choice for every occupied parent. Both the collapsed
 and branching alternatives have a dyadic child count and finite tags. -/
namespace Falconer.Regularization

 theorem exists_scalar_child_choice {N a b : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hab : a ≤ b) (hb : b ≤ N)
    (p : CellPath 1) (hp : p ∈ L.image (List.take a)) :
    ∃ K k n, ScalarChildChoice L a b p K k n := by
  classical
  let C := prefixChildren L a b p
  by_cases hlarge : 2050 ≤ C.card
  · obtain ⟨K,hK,k,n,hk,hcard,hkeep,hn0,hn1,hsep,hpair⟩ :=
      scalar_initial_path_children L hL hab hb p hlarge
    have hkB : k ≤ b-a := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      rw [← hcard]
      exact (Finset.card_le_card hK).trans (scalar_prefix_children_card_le hL hab hb p)
    exact ⟨K,k,n,hK,hcard,hkB,by omega,by omega,hkeep,Or.inr ⟨hn0,hn1,hsep,hpair⟩⟩
  · have hCn : C.Nonempty := (prefixFiber_nonempty hp).image (List.take b)
    obtain ⟨q,hq⟩ := hCn
    refine ⟨{q},0,a,Finset.singleton_subset_iff.mpr hq,by simp,by omega,le_rfl,hab,?_,Or.inl rfl⟩
    simp only [Finset.card_singleton,mul_one]
    change C.card ≤ 2050
    omega

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarTaggedPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting a common geometric tag while retaining whole child fibers.
 The loss is the number of tags times the local pruning loss. -/
namespace Falconer

 theorem scalar_tagged_child_pruning {ι α τ : Type*} [DecidableEq ι] [DecidableEq α] [DecidableEq τ]
    (P : Finset ι) (hP : P.Nonempty) (C F : ι → Finset α) (tag : ι → τ)
    (D H : ℕ) (hF : ∀ p ∈ P, F p ⊆ C p)
    (hd : (P : Set ι).PairwiseDisjoint C)
    (hkeep : ∀ p ∈ P, (C p).card ≤ D*(F p).card)
    (htags : (P.image tag).card ≤ H) :
    ∃ t ∈ P.image tag, (P.biUnion C).card ≤
      D*H*((P.filter fun p => tag p = t).biUnion F).card := by
  classical
  let T := P.image tag
  let w := fun t => ∑ p ∈ P.filter (fun p => tag p = t), (F p).card
  obtain ⟨t,ht,hmax⟩ := T.exists_max_image w (hP.image tag)
  have hFd : (P : Set ι).PairwiseDisjoint F := by
    intro p hp q hq hpq
    exact (hd hp hq hpq).mono (hF p hp) (hF q hq)
  have hsubset : (P.filter fun p => tag p = t : Finset ι) ⊆ P := Finset.filter_subset _ _
  have hv : ((P.filter fun p => tag p = t).biUnion F).card = w t := by
    apply Finset.card_biUnion
    intro p hp q hq hpq
    exact hFd (hsubset hp) (hsubset hq) hpq
  have hsum : (∑ p ∈ P, (F p).card) = ∑ t ∈ T, w t := by
    exact (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem tag hp) _).symm
  refine ⟨t,ht,?_⟩
  rw [hv]
  calc
    (P.biUnion C).card = ∑ p ∈ P, (C p).card := Finset.card_biUnion hd
    _ ≤ ∑ p ∈ P, D*(F p).card := Finset.sum_le_sum hkeep
    _ = D*(∑ p ∈ P, (F p).card) := (Finset.mul_sum _ _ _).symm
    _ = D*(∑ t ∈ T, w t) := by rw [hsum]
    _ ≤ D*(∑ _t ∈ T, w t) := Nat.mul_le_mul_left _ (Finset.sum_le_sum hmax)
    _ = D*(T.card*w t) := by simp
    _ ≤ D*(H*w t) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ htags)
    _ = D*H*w t := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarTaggedPrefix
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-tag selection for a scalar dyadic block. The operation
 removes whole child cells and therefore keeps lower completed fibers. -/
namespace Falconer.Regularization

 theorem prefixFiber_pairwise_disjoint (L : Finset (CellPath 1)) (a : ℕ)
    (P : Finset (CellPath 1)) : (P : Set (CellPath 1)).PairwiseDisjoint (prefixFiber L a) := by
  classical
  intro p _ q _ hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hpq ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)

 theorem prefixFiber_biUnion (L : Finset (CellPath 1)) (a : ℕ) :
    (L.image (List.take a)).biUnion (prefixFiber L a) = L := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨p,_,hq⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_filter.mp hq).1
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨q.take a,Finset.mem_image_of_mem _ hq,
      Finset.mem_filter.mpr ⟨hq,rfl⟩⟩

 theorem scalarPruneLeaves_fiber_uniform (L : Finset (CellPath 1)) {a b : ℕ}
    (hab : a ≤ b) (K : CellPath 1 → Finset (CellPath 1)) (p : CellPath 1)
    (hK : K p ⊆ prefixChildren L a b p) (m : ℕ)
    (hm : ∀ c ∈ prefixChildren L a b p, (prefixFiber L b c).card = m) :
    (prefixFiber (scalarPruneLeaves L a b K) a p).card = (K p).card*m := by
  rw [scalarPruneLeaves_fiber_card L hab K p hK]
  calc
    _ = ∑ _c ∈ K p, m := Finset.sum_congr rfl (fun c hc => hm c (hK hc))
    _ = _ := by simp

 theorem scalar_tagged_prefix_prune (L : Finset (CellPath 1)) (hL : L.Nonempty)
    {a b : ℕ} (hab : a ≤ b) (K : CellPath 1 → Finset (CellPath 1))
    {τ : Type*} [DecidableEq τ] (tag : CellPath 1 → τ) (D H m : ℕ)
    (hK : ∀ p ∈ L.image (List.take a), K p ⊆ prefixChildren L a b p)
    (hkeep : ∀ p ∈ L.image (List.take a), (prefixChildren L a b p).card ≤ D*(K p).card)
    (hm : ∀ c ∈ L.image (List.take b), (prefixFiber L b c).card = m)
    (htags : ((L.image (List.take a)).image tag).card ≤ H) :
    ∃ t ∈ (L.image (List.take a)).image tag,
      let Kt := fun p => if tag p = t then K p else ∅
      L.card ≤ D*H*(scalarPruneLeaves L a b Kt).card ∧
      ∀ q ∈ scalarPruneLeaves L a b Kt, tag (q.take a) = t := by
  classical
  let P := L.image (List.take a)
  let R := scalarPruneLeaves L a b K
  let C := prefixFiber L a
  let F := prefixFiber R a
  have hFC : ∀ p ∈ P, F p ⊆ C p := by
    intro p _ q hq
    exact Finset.mem_filter.mpr ⟨scalarPruneLeaves_subset L a b K (Finset.mem_filter.mp hq).1,
      (Finset.mem_filter.mp hq).2⟩
  have hcards : ∀ p ∈ P, (C p).card ≤ D*(F p).card := by
    intro p hp
    have hm' : ∀ c ∈ prefixChildren L a b p, (prefixFiber L b c).card = m :=
      fun c hc => hm c (prefixChildren_mem_image hc)
    have hc : (C p).card = (prefixChildren L a b p).card*m := by
      rw [prefixFiber_card_sum hab]
      calc
        _ = ∑ _c ∈ prefixChildren L a b p, m := Finset.sum_congr rfl hm'
        _ = _ := by simp
    have hf : (F p).card = (K p).card*m := scalarPruneLeaves_fiber_uniform L hab K p (hK p hp) m hm'
    rw [hc,hf]
    calc
      _ ≤ (D*(K p).card)*m := Nat.mul_le_mul_right m (hkeep p hp)
      _ = _ := by ring
  obtain ⟨t,ht,hbound⟩ := scalar_tagged_child_pruning P (hL.image (List.take a)) C F tag D H hFC
    (prefixFiber_pairwise_disjoint L a P) hcards htags
  let Kt := fun p => if tag p = t then K p else ∅
  have heq : (P.filter fun p => tag p = t).biUnion F = scalarPruneLeaves L a b Kt := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp,hq⟩ := Finset.mem_biUnion.mp hq
      have hpt := (Finset.mem_filter.mp hp).2
      have hqa := (Finset.mem_filter.mp hq).2
      have hqR := (Finset.mem_filter.mp hq).1
      have hqL := scalarPruneLeaves_subset L a b K hqR
      have hqK := (Finset.mem_filter.mp hqR).2
      apply Finset.mem_filter.mpr
      refine ⟨hqL,?_⟩
      change q.take b ∈ if tag (q.take a) = t then K (q.take a) else ∅
      rw [hqa,ite_eq_left hpt]
      rwa [hqa] at hqK
    · intro hq
      have hqL := (Finset.mem_filter.mp hq).1
      have hqKt := (Finset.mem_filter.mp hq).2
      have hqt : tag (q.take a) = t := by
        by_contra hh
        simp only [Kt,ite_eq_right hh,Finset.notMem_empty] at hqKt
      have hqK : q.take b ∈ K (q.take a) := by
        simpa only [Kt,ite_eq_left hqt] using hqKt
      exact Finset.mem_biUnion.mpr ⟨q.take a,
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hqL,hqt⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hqL,hqK⟩,rfl⟩⟩
  refine ⟨t,ht,?_,?_⟩
  · rw [← heq,← prefixFiber_biUnion L a]
    exact hbound
  · intro q hq
    have hh := (Finset.mem_filter.mp hq).2
    by_contra hqt
    simp only [ite_eq_right hqt,Finset.notMem_empty] at hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_ScalarBlockPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One bottom-up scalar regularization step. Every surviving parent
 has the same branching and intermediate scale, with an explicit
 quadratic-in-block-width loss and unchanged deeper fibers. -/
namespace Falconer.Regularization

 theorem scalar_block_pruning {N a b : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (hab : a ≤ b) (hb : b ≤ N)
    (m : ℕ) (hm : ∀ c ∈ L.image (List.take b), (prefixFiber L b c).card = m) :
    ∃ K : CellPath 1 → Finset (CellPath 1), ∃ k n : ℕ,
      let Q := scalarPruneLeaves L a b K
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ 2050*(b-a+1)^2*Q.card ∧
      ∀ p ∈ Q.image (List.take a),
        ScalarChildChoice L a b p (K p) k n ∧
        prefixChildren Q a b p = K p ∧ (prefixFiber Q a p).card = 2^k*m := by
  classical
  let P := L.image (List.take a)
  have hex : ∀ p : CellPath 1, ∃ F k n, p ∈ P → ScalarChildChoice L a b p F k n := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨F,k,n,hdata⟩ := exists_scalar_child_choice L hL hab hb p hp
      exact ⟨F,k,n,fun _ => hdata⟩
    · exact ⟨∅,0,a,fun h => False.elim (hp h)⟩
  choose K k n hdata using hex
  let tag := fun p => (k p,n p)
  have htags : (P.image tag).card ≤ (b-a+1)^2 := by
    have hsub : P.image tag ⊆ (Finset.range (b-a+1)).product (Finset.Icc a b) := by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      have hd := hdata p hp
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hd.2.2.1),
        Finset.mem_Icc.mpr ⟨hd.2.2.2.1,hd.2.2.2.2.1⟩⟩
    have hc : (Finset.Icc a b).card = b-a+1 := by rw [Nat.card_Icc]; omega
    calc
      _ ≤ ((Finset.range (b-a+1)).product (Finset.Icc a b)).card := Finset.card_le_card hsub
      _ = (Finset.range (b-a+1)).card*(Finset.Icc a b).card := Finset.card_product _ _
      _ = _ := by rw [Finset.card_range,hc,pow_two]
  obtain ⟨t,ht,hbound,_⟩ := scalar_tagged_prefix_prune L hne hab K tag 2050 ((b-a+1)^2) m
    (fun p hp => (hdata p hp).1) (fun p hp => (hdata p hp).2.2.2.2.2.1) hm htags
  let Kt := fun p => if tag p = t then K p else ∅
  let Q := scalarPruneLeaves L a b Kt
  have hQne : Q.Nonempty := by
    apply Finset.card_pos.mp
    have hc := hne.card_pos
    by_contra hh
    have hz : Q.card = 0 := by omega
    change L.card ≤ 2050*(b-a+1)^2*Q.card at hbound
    rw [hz,mul_zero] at hbound
    omega
  have hQsub : Q ⊆ L := scalarPruneLeaves_subset L a b Kt
  have hcommon : ∀ p ∈ Q.image (List.take a), p ∈ P ∧ tag p = t := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨Finset.mem_image_of_mem _ (hQsub hq),?_⟩
    have hh := (Finset.mem_filter.mp hq).2
    by_contra hqt
    simp only [Kt,ite_eq_right hqt,Finset.notMem_empty] at hh
  refine ⟨Kt,t.1,t.2,hQne,hQsub,hbound,?_⟩
  intro p hp
  have hcp := hcommon p hp
  have htag : (k p,n p) = t := hcp.2
  have hk : k p = t.1 := congrArg Prod.fst htag
  have hn : n p = t.2 := congrArg Prod.snd htag
  have hKt : Kt p = K p := by dsimp only [Kt]; rw [ite_eq_left hcp.2]
  have hd : ScalarChildChoice L a b p (Kt p) t.1 t.2 := by
    rw [hKt,← hk,← hn]
    exact hdata p hcp.1
  refine ⟨hd,scalarPruneLeaves_children L a b Kt p hd.1,?_⟩
  have hmass := scalarPruneLeaves_fiber_uniform L hab Kt p hd.1 m
    (fun c hc => hm c (prefixChildren_mem_image hc))
  rw [hd.2.1] at hmass
  exact hmass

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarBranchingLevel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric data retained by scalar regularization at each block.
 Subsequent coarser pruning preserves this data exactly. -/
namespace Falconer.Regularization

 theorem ScalarBranchingLevel.prune {L : Finset (CellPath 1)} {a b k n c d : ℕ}
    (h : ScalarBranchingLevel L a b k n) (hcd : c ≤ d) (hda : d ≤ a)
    (K : CellPath 1 → Finset (CellPath 1)) :
    ScalarBranchingLevel (scalarPruneLeaves L c d K) a b k n := by
  classical
  refine ⟨h.exponent_le,h.level_lo,h.level_hi,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [scalarPruneLeaves_lower_children L hcd hda K hq]
    exact h.children_card _ (Finset.mem_image_of_mem _ (scalarPruneLeaves_subset L c d K hq))
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [scalarPruneLeaves_lower_children L hcd hda K hq]
    exact h.fork_geometry _ (Finset.mem_image_of_mem _ (scalarPruneLeaves_subset L c d K hq))

 theorem scalar_block_pruning_level {N a b : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (hab : a ≤ b) (hb : b ≤ N)
    (m : ℕ) (hm : ∀ c ∈ L.image (List.take b), (prefixFiber L b c).card = m) :
    ∃ K : CellPath 1 → Finset (CellPath 1), ∃ k n : ℕ,
      let Q := scalarPruneLeaves L a b K
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ 2050*(b-a+1)^2*Q.card ∧
      ScalarBranchingLevel Q a b k n ∧
      ∀ p ∈ Q.image (List.take a), (prefixFiber Q a p).card = 2^k*m := by
  classical
  obtain ⟨K,k,n,hne',hsub,hcard,hdata⟩ := scalar_block_pruning L hL hne hab hb m hm
  let Q := scalarPruneLeaves L a b K
  obtain ⟨q,hq⟩ := hne'
  have hp := Finset.mem_image_of_mem (List.take a) hq
  have hd := (hdata _ hp).1
  refine ⟨K,k,n,⟨q,hq⟩,hsub,hcard,?_,fun p hp => (hdata p hp).2.2⟩
  refine ⟨hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,?_,?_⟩
  · intro p hp
    rw [(hdata p hp).2.1]
    exact (hdata p hp).1.2.1
  · intro p hp
    rw [(hdata p hp).2.1]
    exact (hdata p hp).1.2.2.2.2.2.2

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarForkGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A witnessed pair of regularized child centers separates their entire
 descendant fibers. This supplies the nonporous binary fork geometry. -/
namespace Falconer.Regularization

 theorem scalar_fork_leaf_bounds {N a b k n : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hb : b ≤ N) (hlevel : ScalarBranchingLevel L a b k n)
    (hk : k ≠ 0) {p : CellPath 1} (hp : p ∈ L.image (List.take a)) :
    ∃ c ∈ prefixChildren L a b p, ∃ d ∈ prefixChildren L a b p, c ≠ d ∧
      ∀ u ∈ prefixFiber L b c, ∀ v ∈ prefixFiber L b d,
        6*(1/2:ℝ)^n ≤ |scalarPathCenter u-scalarPathCenter v| ∧
        |scalarPathCenter u-scalarPathCenter v| ≤ 18*(1/2:ℝ)^n := by
  rcases hlevel.fork_geometry p hp with hz | ⟨_,_,hsep,c,hc,d,hd,hcd,hpair⟩
  · exact False.elim (hk hz)
  refine ⟨c,hc,d,hd,hcd,?_⟩
  intro u hu v hv
  have hu0 := scalar_prefix_leaf_center_dist hL hb hu
  have hv0 := scalar_prefix_leaf_center_dist hL hb hv
  have hsc := hsep c hc d hd hcd
  have hscale : (1/2:ℝ)^b ≤ (1/2:ℝ)^n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hlevel.level_hi
  have hlow : |scalarPathCenter c-scalarPathCenter d| ≤
      |scalarPathCenter u-scalarPathCenter c|+|scalarPathCenter u-scalarPathCenter v|+
        |scalarPathCenter v-scalarPathCenter d| := by
    calc
      _ ≤ |scalarPathCenter c-scalarPathCenter u|+|scalarPathCenter u-scalarPathCenter d| := abs_sub_le _ _ _
      _ ≤ |scalarPathCenter c-scalarPathCenter u|+
          (|scalarPathCenter u-scalarPathCenter v|+|scalarPathCenter v-scalarPathCenter d|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (scalarPathCenter c) (scalarPathCenter u)]; ring
  have hupp : |scalarPathCenter u-scalarPathCenter v| ≤
      |scalarPathCenter u-scalarPathCenter c|+|scalarPathCenter c-scalarPathCenter d|+
        |scalarPathCenter v-scalarPathCenter d| := by
    calc
      _ ≤ |scalarPathCenter u-scalarPathCenter c|+|scalarPathCenter c-scalarPathCenter v| := abs_sub_le _ _ _
      _ ≤ |scalarPathCenter u-scalarPathCenter c|+
          (|scalarPathCenter c-scalarPathCenter d|+|scalarPathCenter d-scalarPathCenter v|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (scalarPathCenter d) (scalarPathCenter v)]; ring
  constructor <;> linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSelectedForks
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embedding selected regularized forks into the scalar binary cube.
 Gaps between selected levels are filled by actual descendant fibers. -/
namespace Falconer.Regularization

 theorem prefixFiber_nested {L : Finset (CellPath 1)} {a b : ℕ}
    (hab : a ≤ b) {p q : CellPath 1} (hq : q ∈ prefixFiber L a p) :
    prefixFiber L b (q.take b) ⊆ prefixFiber L a p := by
  classical
  intro u hu
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
    (take_eq_of_take_eq hab (Finset.mem_filter.mp hu).2).trans (Finset.mem_filter.mp hq).2⟩

 theorem scalar_selected_binary_forks {N : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (hne : Q.Nonempty) (t : ℕ)
    (a b k n : ℕ → ℕ)
    (hab : ∀ i < t, a i ≤ b i) (hnext : ∀ i < t, b i ≤ a (i+1))
    (hb : ∀ i < t, b i ≤ N)
    (hlevel : ∀ i < t, ScalarBranchingLevel Q (a i) (b i) (k i) (n i))
    (hk : ∀ i < t, k i ≠ 0) :
    ∃ f : (Fin t → Bool) → ℝ, (∀ w, f w ∈ Q.image scalarPathCenter) ∧
      ∀ i : Fin t, ∀ w, ScalarBinaryTail i w →
        6*(1/2:ℝ)^(n i) ≤ |f (Function.update w i true)-f w| ∧
        |f (Function.update w i true)-f w| ≤ 18*(1/2:ℝ)^(n i) := by
  classical
  let P : ℕ → Finset ℝ → Prop := fun i E =>
    ∃ p ∈ Q.image (List.take (a i)), E = (prefixFiber Q (a i) p).image scalarPathCenter
  have hPn : ∀ i ≤ t, ∀ E, P i E → E.Nonempty := by
    intro i _ E hE
    obtain ⟨p,hp,rfl⟩ := hE
    exact (prefixFiber_nonempty hp).image scalarPathCenter
  have hstep : ∀ i < t, ∀ E, P i E → ∃ E0 E1 : Finset ℝ,
      E0 ⊆ E ∧ E1 ⊆ E ∧ P (i+1) E0 ∧ P (i+1) E1 ∧
      ∀ x ∈ E0, ∀ y ∈ E1,
        6*(1/2:ℝ)^(n i) ≤ |x-y| ∧ |x-y| ≤ 18*(1/2:ℝ)^(n i) := by
    intro i hi E hE
    obtain ⟨p,hp,rfl⟩ := hE
    obtain ⟨c,hc,d,hd,_,hfork⟩ := scalar_fork_leaf_bounds hQ (hb i hi) (hlevel i hi) (hk i hi) hp
    obtain ⟨u,hu⟩ := prefixFiber_nonempty (prefixChildren_mem_image hc)
    obtain ⟨v,hv⟩ := prefixFiber_nonempty (prefixChildren_mem_image hd)
    let E0 := (prefixFiber Q (a (i+1)) (u.take (a (i+1)))).image scalarPathCenter
    let E1 := (prefixFiber Q (a (i+1)) (v.take (a (i+1)))).image scalarPathCenter
    have h0 := prefixFiber_nested (hnext i hi) hu
    have h1 := prefixFiber_nested (hnext i hi) hv
    have h0P := prefixFiber_child_subset (hab i hi) hc
    have h1P := prefixFiber_child_subset (hab i hi) hd
    refine ⟨E0,E1,Finset.image_subset_image (h0.trans h0P),
      Finset.image_subset_image (h1.trans h1P),?_,?_,?_⟩
    · exact ⟨u.take (a (i+1)),Finset.mem_image_of_mem _ (Finset.mem_filter.mp hu).1,rfl⟩
    · exact ⟨v.take (a (i+1)),Finset.mem_image_of_mem _ (Finset.mem_filter.mp hv).1,rfl⟩
    · intro x hx y hy
      obtain ⟨u',hu',rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v',hv',rfl⟩ := Finset.mem_image.mp hy
      exact hfork u' (h0 hu') v' (h1 hv')
  obtain ⟨q,hq⟩ := hne
  let S := (prefixFiber Q (a 0) (q.take (a 0))).image scalarPathCenter
  have hS : P 0 S := ⟨q.take (a 0),Finset.mem_image_of_mem _ hq,rfl⟩
  obtain ⟨f,hf,hbits⟩ := scalar_binary_embedding t P (fun i => 6*(1/2:ℝ)^(n i))
    (fun i => 18*(1/2:ℝ)^(n i)) S hS hPn hstep
  refine ⟨f,?_,hbits⟩
  intro w
  exact Finset.image_subset_image (Finset.filter_subset _ _) (hf w)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPathNodes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translating actual scalar prefix nodes into their distinct centers.
 This is the coordinate bridge to the separated-tree projection estimate. -/
namespace Falconer.Regularization

 theorem ScalarBranchingLevel.separated {Q : Finset (CellPath 1)} {a b k n : ℕ}
    (h : ScalarBranchingLevel Q a b k n) {p : CellPath 1}
    (hp : p ∈ Q.image (List.take a)) :
    ∀ q ∈ prefixChildren Q a b p, ∀ r ∈ prefixChildren Q a b p, q ≠ r →
      8*(1/2:ℝ)^n ≤ |scalarPathCenter q-scalarPathCenter r| := by
  intro q hq r hr hqr
  rcases h.fork_geometry p hp with hk | ⟨_,_,hs,_⟩
  · have hc : (prefixChildren Q a b p).card ≤ 1 := by rw [h.children_card p hp,hk]; simp
    exact False.elim (hqr (Finset.card_le_one.mp hc q hq r hr))
  · exact (hs q hq r hr hqr).le

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPrefixTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Truncation retains all prefix fibers above the truncation depth. -/
namespace Falconer.Regularization

 theorem prefixFiber_image_take (L : Finset (CellPath 1)) {a t : ℕ}
    (hat : a ≤ t) (p : CellPath 1) :
    prefixFiber (L.image (List.take t)) a p = (prefixFiber L a p).image (List.take t) := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    have hparent := (Finset.mem_filter.mp hc).2
    simp only [List.take_take,min_eq_left hat] at hparent
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hparent⟩,rfl⟩
  · intro hc
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hu).1,
      by simpa only [List.take_take,min_eq_left hat] using (Finset.mem_filter.mp hu).2⟩

 theorem prefixChildren_image_take (L : Finset (CellPath 1)) {a b t : ℕ}
    (hat : a ≤ t) (hbt : b ≤ t) (p : CellPath 1) :
    prefixChildren (L.image (List.take t)) a b p = prefixChildren L a b p := by
  classical
  simp only [prefixChildren,prefixFiber_image_take L hat,Finset.image_image,
    Function.comp_def,List.take_take,min_eq_left hbt]

 theorem prefixChildren_same (L : Finset (CellPath 1)) {a : ℕ} {p : CellPath 1}
    (hp : p ∈ L.image (List.take a)) : prefixChildren L a a p = {p} := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    simpa only [Finset.mem_singleton] using (Finset.mem_filter.mp hq).2
  · intro hc
    have heq := Finset.mem_singleton.mp hc
    subst c
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq,rfl⟩)

 theorem prefixChildren_card_compose (L : Finset (CellPath 1)) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (p : CellPath 1) :
    (prefixChildren L a c p).card =
      ∑ q ∈ prefixChildren L a b p, (prefixChildren L b c q).card := by
  classical
  have hh := prefixFiber_card_sum (C := L.image (List.take c)) hab p
  rw [prefixFiber_image_take L (hab.trans hbc),
    prefixChildren_image_take L (hab.trans hbc) hbc] at hh
  change (prefixChildren L a c p).card = _ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro q _
  rw [prefixFiber_image_take L hbc]
  rfl

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarGroupedPaths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact branching counts and first splits across groups of regularized
 dyadic levels. No abstract replacement for the original path set is used. -/
namespace Falconer.Regularization

 theorem scalar_grouped_children_card (Q : Finset (CellPath 1))
    (d k : ℕ → ℕ) (hd : Monotone d) (M : ℕ)
    (hcard : ∀ i < M, ∀ p ∈ Q.image (List.take (d i)),
      (prefixChildren Q (d i) (d (i+1)) p).card = 2^(k i))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ M) (p : CellPath 1)
    (hp : p ∈ Q.image (List.take (d a))) :
    (prefixChildren Q (d a) (d b) p).card = 2^(∑ i ∈ Finset.Ico a b, k i) := by
  induction b,hab using Nat.le_induction with
  | base => simp [prefixChildren_same Q hp]
  | succ b hab ih =>
    rw [prefixChildren_card_compose Q (hd hab) (hd (Nat.le_succ b))]
    have hc : ∀ c ∈ prefixChildren Q (d a) (d b) p,
        (prefixChildren Q (d b) (d (b+1)) c).card = 2^(k b) := by
      intro c hc
      exact hcard b (by omega) c (prefixChildren_mem_image hc)
    rw [Finset.sum_congr rfl hc]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul]
    rw [ih (by omega),Finset.sum_Ico_succ_top hab,pow_add]

 theorem scalar_first_prefix_split (u v : CellPath 1) (d : ℕ → ℕ)
    {a b : ℕ} (hab : a ≤ b) (hstart : u.take (d a) = v.take (d a))
    (hend : u.take (d b) ≠ v.take (d b)) :
    ∃ i, a ≤ i ∧ i < b ∧ u.take (d i) = v.take (d i) ∧
      u.take (d (i+1)) ≠ v.take (d (i+1)) := by
  induction b,hab using Nat.le_induction with
  | base => exact False.elim (hend hstart)
  | succ b hab ih =>
    by_cases heq : u.take (d b) = v.take (d b)
    · exact ⟨b,hab,Nat.lt_succ_self b,heq,hend⟩
    · obtain ⟨i,hai,hib,hi,hi'⟩ := ih heq
      exact ⟨i,hai,by omega,hi,hi'⟩

 theorem scalar_grouped_children_separated {N M : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (d k n : ℕ → ℕ) (hd : Monotone d)
    (hdN : ∀ i ≤ M, d i ≤ N)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ M) {g : ℝ}
    (hg : ∀ i, a ≤ i → i < b → k i ≠ 0 → g ≤ 6*(1/2:ℝ)^(n i))
    (p : CellPath 1) :
    ∀ u ∈ prefixChildren Q (d a) (d b) p, ∀ v ∈ prefixChildren Q (d a) (d b) p,
      u ≠ v → g ≤ |scalarPathCenter u-scalarPathCenter v| := by
  classical
  intro u hu v hv huv
  have huLen := scalar_prefix_children_length (a := d a) hQ (hdN b hb) p u hu
  have hvLen := scalar_prefix_children_length (a := d a) hQ (hdN b hb) p v hv
  have huParent := scalar_prefix_children_parent (hd hab) Q p u hu
  have hvParent := scalar_prefix_children_parent (hd hab) Q p v hv
  have hsplit := scalar_first_prefix_split u v d hab (huParent.trans hvParent.symm)
    (by
      have huTake : u.take (d b) = u := by rw [← huLen,List.take_length]
      have hvTake : v.take (d b) = v := by rw [← hvLen,List.take_length]
      simpa only [huTake,hvTake] using huv)
  obtain ⟨i,hai,hib,heq,hne⟩ := hsplit
  have hiM : i < M := lt_of_lt_of_le hib hb
  have hui : u.take (d i) ∈ Q.image (List.take (d i)) := by
    obtain ⟨q,hq,hqu⟩ := Finset.mem_image.mp hu
    refine Finset.mem_image.mpr ⟨q,(Finset.mem_filter.mp hq).1,?_⟩
    rw [← hqu,List.take_take,min_eq_left (hd (by omega : i ≤ b))]
  have huc : u.take (d (i+1)) ∈ prefixChildren Q (d i) (d (i+1)) (u.take (d i)) := by
    obtain ⟨q,hq,hqu⟩ := Finset.mem_image.mp hu
    refine Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,?_⟩,?_⟩
    · rw [← hqu,List.take_take,min_eq_left (hd (by omega : i ≤ b))]
    · rw [← hqu,List.take_take,min_eq_left (hd (by omega : i+1 ≤ b))]
  have hvc : v.take (d (i+1)) ∈ prefixChildren Q (d i) (d (i+1)) (u.take (d i)) := by
    obtain ⟨q,hq,hqv⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,?_⟩,?_⟩
    · rw [heq,← hqv,List.take_take,min_eq_left (hd (by omega : i ≤ b))]
    · rw [← hqv,List.take_take,min_eq_left (hd (by omega : i+1 ≤ b))]
  have hki : k i ≠ 0 := by
    intro hz
    have hc : (prefixChildren Q (d i) (d (i+1)) (u.take (d i))).card ≤ 1 := by
      rw [(hlevel i hiM).children_card _ hui,hz]
      simp
    exact hne (Finset.card_le_one.mp hc _ huc _ hvc)
  have hsep := (hlevel i hiM).separated hui _ huc _ hvc hne
  have hiDepth : d (i+1) ≤ d b := hd (by omega)
  have hdu : |scalarPathCenter u-scalarPathCenter (u.take (d (i+1)))| ≤
      (1/2:ℝ)^(d (i+1)) :=
    scalarPathCenter_same_parent huLen hiDepth (by simp only [List.take_take,min_self])
  have hdv : |scalarPathCenter v-scalarPathCenter (v.take (d (i+1)))| ≤
      (1/2:ℝ)^(d (i+1)) :=
    scalarPathCenter_same_parent hvLen hiDepth (by simp only [List.take_take,min_self])
  have hscale : (1/2:ℝ)^(d (i+1)) ≤ (1/2:ℝ)^(n i) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (hlevel i hiM).level_hi
  have htri : |scalarPathCenter (u.take (d (i+1)))-scalarPathCenter (v.take (d (i+1)))| ≤
      |scalarPathCenter u-scalarPathCenter (u.take (d (i+1)))| +
        |scalarPathCenter u-scalarPathCenter v| +
        |scalarPathCenter v-scalarPathCenter (v.take (d (i+1)))| := by
    calc
      _ ≤ |scalarPathCenter (u.take (d (i+1)))-scalarPathCenter u| +
        |scalarPathCenter u-scalarPathCenter (v.take (d (i+1)))| := abs_sub_le _ _ _
      _ ≤ |scalarPathCenter (u.take (d (i+1)))-scalarPathCenter u| +
        (|scalarPathCenter u-scalarPathCenter v| +
          |scalarPathCenter v-scalarPathCenter (v.take (d (i+1)))|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (scalarPathCenter (u.take (d (i+1))))]; ring
  have hgg := hg i hai hib hki
  linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarPruningPreservation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning nonempty collections of whole children preserves every coarser
 prefix and every finer branch above an occupied retained node. -/
namespace Falconer.Regularization

 theorem prefixChildren_eq_filter (L : Finset (CellPath 1)) {a b : ℕ}
    (hab : a ≤ b) (p : CellPath 1) :
    prefixChildren L a b p = (L.image (List.take b)).filter (fun q => q.take a = p) := by
  classical
  ext c
  constructor
  · intro hc
    exact Finset.mem_filter.mpr ⟨prefixChildren_mem_image hc,
      scalar_prefix_children_parent hab L p c hc⟩
  · intro hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    have hp := (Finset.mem_filter.mp hc).2
    simp only [List.take_take,min_eq_left hab] at hp
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq,hp⟩)

 theorem scalarPruneLeaves_lift (L : Finset (CellPath 1)) {a b : ℕ}
    (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p)
    {q : CellPath 1} (hq : q ∈ L) :
    ∃ u ∈ scalarPruneLeaves L a b K, u.take a = q.take a := by
  classical
  obtain ⟨c,hc⟩ := (hK (q.take a) (Finset.mem_image_of_mem _ hq)).1
  obtain ⟨u,hu,huc⟩ := Finset.mem_image.mp
    ((hK (q.take a) (Finset.mem_image_of_mem _ hq)).2 hc)
  have hua := (Finset.mem_filter.mp hu).2
  refine ⟨u,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,?_⟩,hua⟩
  rw [hua,huc]
  exact hc

 theorem scalarPruneLeaves_upper_prefixes (L : Finset (CellPath 1)) {a b c : ℕ}
    (hca : c ≤ a) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p) :
    (scalarPruneLeaves L a b K).image (List.take c) = L.image (List.take c) := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (scalarPruneLeaves_subset L a b K)
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨u,hu,hua⟩ := scalarPruneLeaves_lift L K hK hq
    exact Finset.mem_image.mpr ⟨u,hu,take_eq_of_take_eq hca hua⟩

 theorem scalarPruneLeaves_upper_children (L : Finset (CellPath 1)) {a b c d : ℕ}
    (hcd : c ≤ d) (hda : d ≤ a) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p)
    (p : CellPath 1) :
    prefixChildren (scalarPruneLeaves L a b K) c d p = prefixChildren L c d p := by
  rw [prefixChildren_eq_filter _ hcd,prefixChildren_eq_filter _ hcd,
    scalarPruneLeaves_upper_prefixes L hda K hK]

 theorem scalarPruneLeaves_nonempty (L : Finset (CellPath 1)) (hne : L.Nonempty) {a b : ℕ}
    (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p) :
    (scalarPruneLeaves L a b K).Nonempty := by
  obtain ⟨q,hq⟩ := hne
  obtain ⟨u,hu,_⟩ := scalarPruneLeaves_lift L K hK hq
  exact ⟨u,hu⟩

 theorem scalar_single_child_choice (L : Finset (CellPath 1)) (a b : ℕ) :
    ∃ K : CellPath 1 → Finset (CellPath 1),
      ∀ p ∈ L.image (List.take a), K p ⊆ prefixChildren L a b p ∧ (K p).card = 1 := by
  classical
  have hne : ∀ p ∈ L.image (List.take a), (prefixChildren L a b p).Nonempty := by
    intro p hp
    exact (prefixFiber_nonempty hp).image _
  let K : CellPath 1 → Finset (CellPath 1) := fun p => if hp : p ∈ L.image (List.take a) then {(hne p hp).choose} else ∅
  refine ⟨K,?_⟩
  intro p hp
  simp only [K,dite_eq_left hp,Finset.singleton_subset_iff,Finset.card_singleton]
  exact ⟨(hne p hp).choose_spec,trivial⟩

 theorem prefixFiber_total_card (L : Finset (CellPath 1)) (a : ℕ) :
    L.card = ∑ p ∈ L.image (List.take a), (prefixFiber L a p).card := by
  have hh := prefixFiber_card_sum (C := L) (Nat.zero_le a) ([] : CellPath 1)
  simpa only [prefixFiber_zero,prefixChildren] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarSingleChildPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact loss and new branching after keeping one child per terminal
 prefix. These are the operations used to trim a porous bunch. -/
namespace Falconer.Regularization

 theorem scalar_single_child_pruning_cost (L : Finset (CellPath 1)) {a b D m : ℕ}
    (hab : a ≤ b) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), K p ⊆ prefixChildren L a b p ∧ (K p).card = 1)
    (hD : ∀ p ∈ L.image (List.take a), (prefixChildren L a b p).card = D)
    (hm : ∀ c ∈ L.image (List.take b), (prefixFiber L b c).card = m) :
    L.card = D*(scalarPruneLeaves L a b K).card := by
  classical
  have hKn : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p := by
    intro p hp
    exact ⟨Finset.card_pos.mp (by rw [(hK p hp).2]; omega),(hK p hp).1⟩
  have hLcard : ∀ p ∈ L.image (List.take a), (prefixFiber L a p).card = D*m := by
    intro p hp
    rw [prefixFiber_card_sum hab]
    have he : ∀ c ∈ prefixChildren L a b p, (prefixFiber L b c).card = m :=
      fun c hc => hm c (prefixChildren_mem_image hc)
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul,hD p hp]
  have hQcard : ∀ p ∈ L.image (List.take a),
      (prefixFiber (scalarPruneLeaves L a b K) a p).card = m := by
    intro p hp
    rw [scalarPruneLeaves_fiber_card L hab K p (hK p hp).1]
    have he : ∀ c ∈ K p, (prefixFiber L b c).card = m :=
      fun c hc => hm c (prefixChildren_mem_image ((hK p hp).1 hc))
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul,(hK p hp).2,one_mul]
  rw [prefixFiber_total_card L a,prefixFiber_total_card (scalarPruneLeaves L a b K) a,
    scalarPruneLeaves_upper_prefixes L le_rfl K hKn,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hLcard p hp,hQcard p hp]

 theorem scalar_single_child_group_card (L : Finset (CellPath 1)) {a c b : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take c), K p ⊆ prefixChildren L c b p ∧ (K p).card = 1)
    (p : CellPath 1) :
    (prefixChildren (scalarPruneLeaves L c b K) a b p).card = (prefixChildren L a c p).card := by
  classical
  have hKn : ∀ p ∈ L.image (List.take c), (K p).Nonempty ∧ K p ⊆ prefixChildren L c b p := by
    intro p hp
    exact ⟨Finset.card_pos.mp (by rw [(hK p hp).2]; omega),(hK p hp).1⟩
  rw [prefixChildren_card_compose _ hac hcb,
    scalarPruneLeaves_upper_children L hac le_rfl K hKn]
  have he : ∀ q ∈ prefixChildren L a c p,
      (prefixChildren (scalarPruneLeaves L c b K) c b q).card = 1 := by
    intro q hq
    have hq' := prefixChildren_mem_image hq
    rw [scalarPruneLeaves_children L c b K q (hK q hq').1,(hK q hq').2]
  rw [Finset.sum_congr rfl he]
  simp

 theorem scalar_single_child_group_separated {N : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) {a c b : ℕ} (_hac : a ≤ c) (hcb : c ≤ b)
    (hb : b ≤ N) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take c), K p ⊆ prefixChildren L c b p ∧ (K p).card = 1)
    (g : ℝ) (p : CellPath 1)
    (hsep : ∀ u ∈ prefixChildren L a c p, ∀ v ∈ prefixChildren L a c p,
      u ≠ v → g ≤ |scalarPathCenter u-scalarPathCenter v|) :
    ∀ u ∈ prefixChildren (scalarPruneLeaves L c b K) a b p,
      ∀ v ∈ prefixChildren (scalarPruneLeaves L c b K) a b p,
      u ≠ v → g-2*(1/2:ℝ)^c ≤ |scalarPathCenter u-scalarPathCenter v| := by
  classical
  intro u hu v hv huv
  have hQu := (Finset.mem_image.mp hu)
  obtain ⟨x,hx,hxu⟩ := hQu
  obtain ⟨y,hy,hyv⟩ := Finset.mem_image.mp hv
  have hxL := scalarPruneLeaves_subset L c b K (Finset.mem_filter.mp hx).1
  have hyL := scalarPruneLeaves_subset L c b K (Finset.mem_filter.mp hy).1
  have hux : u.take c = x.take c := by rw [← hxu,List.take_take,min_eq_left hcb]
  have hvy : v.take c = y.take c := by rw [← hyv,List.take_take,min_eq_left hcb]
  have hxK : u ∈ K (x.take c) := by
    rw [← hxu]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hyK : v ∈ K (y.take c) := by
    rw [← hyv]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
  have huvC : u.take c ≠ v.take c := by
    intro heq
    have hxy : x.take c = y.take c := hux.symm.trans (heq.trans hvy)
    rw [← hxy] at hyK
    have hc : (K (x.take c)).card ≤ 1 := by
      rw [(hK _ (Finset.mem_image_of_mem _ hxL)).2]
    exact huv (Finset.card_le_one.mp hc u hxK v hyK)
  have huc : u.take c ∈ prefixChildren L a c p := by
    rw [hux]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hxL,(Finset.mem_filter.mp hx).2⟩)
  have hvc : v.take c ∈ prefixChildren L a c p := by
    rw [hvy]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hyL,(Finset.mem_filter.mp hy).2⟩)
  have hse := hsep _ huc _ hvc huvC
  have huLen := scalar_prefix_children_length (a := a)
    ((scalarPruneLeaves_subset L c b K).trans hL) hb p u hu
  have hvLen := scalar_prefix_children_length (a := a)
    ((scalarPruneLeaves_subset L c b K).trans hL) hb p v hv
  have hdu : |scalarPathCenter u-scalarPathCenter (u.take c)| ≤ (1/2:ℝ)^c :=
    scalarPathCenter_same_parent huLen hcb (by simp only [List.take_take,min_self])
  have hdv : |scalarPathCenter v-scalarPathCenter (v.take c)| ≤ (1/2:ℝ)^c :=
    scalarPathCenter_same_parent hvLen hcb (by simp only [List.take_take,min_self])
  have ht : |scalarPathCenter (u.take c)-scalarPathCenter (v.take c)| ≤
      |scalarPathCenter u-scalarPathCenter (u.take c)|+|scalarPathCenter u-scalarPathCenter v|+
        |scalarPathCenter v-scalarPathCenter (v.take c)| := by
    calc
      _ ≤ |scalarPathCenter (u.take c)-scalarPathCenter u|+
        |scalarPathCenter u-scalarPathCenter (v.take c)| := abs_sub_le _ _ _
      _ ≤ |scalarPathCenter (u.take c)-scalarPathCenter u|+
        (|scalarPathCenter u-scalarPathCenter v|+|scalarPathCenter v-scalarPathCenter (v.take c)|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (scalarPathCenter (u.take c))]; ring
  linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPathLevel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated levels retain only the information used by the projection
 argument. They allow bunching without requiring a new closest-pair witness. -/
namespace Falconer.Regularization

 theorem ScalarPathLevel.trim {N : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) {a c b K : ℕ} {g : ℝ}
    (h : ScalarPathLevel L a c K g) (hcb : c ≤ b) (hb : b ≤ N)
    (F : CellPath 1 → Finset (CellPath 1))
    (hF : ∀ p ∈ L.image (List.take c), F p ⊆ prefixChildren L c b p ∧ (F p).card = 1) :
    ScalarPathLevel (scalarPruneLeaves L c b F) a b K (g-2*(1/2:ℝ)^c) := by
  classical
  refine ⟨h.order.trans hcb,?_,?_⟩
  · intro p hp
    rw [scalar_single_child_group_card L h.order hcb F hF]
    exact h.card p (Finset.image_subset_image (scalarPruneLeaves_subset L c b F) hp)
  · intro p hp
    exact scalar_single_child_group_separated hL h.order hcb hb F hF g p
      (h.separated p (Finset.image_subset_image (scalarPruneLeaves_subset L c b F) hp))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarUniformTrim
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A complete bunch-trimming step on the original regularized paths:
 exact cardinal loss, retained branch count, separation, and common mass. -/
namespace Falconer.Regularization

 theorem scalar_trimmed_uniform_block {N : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k : ℕ → ℕ) (hd : Monotone d)
    {a c b m : ℕ} (hac : a ≤ c) (hcb : c ≤ b) (hb : d b ≤ N)
    (hcard : ∀ i < b, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i))
    (hm : ∀ p ∈ L.image (List.take (d b)), (prefixFiber L (d b) p).card = m)
    (g : ℝ) (hsep : ∀ p ∈ L.image (List.take (d a)),
      ∀ u ∈ prefixChildren L (d a) (d c) p, ∀ v ∈ prefixChildren L (d a) (d c) p,
      u ≠ v → g ≤ |scalarPathCenter u-scalarPathCenter v|) :
    ∃ F : CellPath 1 → Finset (CellPath 1),
      (∀ p ∈ L.image (List.take (d c)), F p ⊆ prefixChildren L (d c) (d b) p ∧ (F p).card = 1) ∧
      let Q := scalarPruneLeaves L (d c) (d b) F
      Q.Nonempty ∧ L.card = 2^(∑ i ∈ Finset.Ico c b, k i)*Q.card ∧
      ScalarPathLevel Q (d a) (d b) (2^(∑ i ∈ Finset.Ico a c, k i))
        (g-2*(1/2:ℝ)^(d c)) ∧
      (∀ p ∈ Q.image (List.take (d a)),
        (prefixFiber Q (d a) p).card = 2^(∑ i ∈ Finset.Ico a c, k i)*m) := by
  classical
  obtain ⟨F,hF⟩ := scalar_single_child_choice L (d c) (d b)
  have hFn : ∀ p ∈ L.image (List.take (d c)),
      (F p).Nonempty ∧ F p ⊆ prefixChildren L (d c) (d b) p := by
    intro p hp
    exact ⟨Finset.card_pos.mp (by rw [(hF p hp).2]; omega),(hF p hp).1⟩
  let Q := scalarPruneLeaves L (d c) (d b) F
  have hcCount : ∀ p ∈ L.image (List.take (d c)),
      (prefixChildren L (d c) (d b) p).card = 2^(∑ i ∈ Finset.Ico c b, k i) :=
    fun p hp => scalar_grouped_children_card L d k hd b hcard hcb le_rfl p hp
  have haCount : ∀ p ∈ L.image (List.take (d a)),
      (prefixChildren L (d a) (d c) p).card = 2^(∑ i ∈ Finset.Ico a c, k i) :=
    fun p hp => scalar_grouped_children_card L d k hd b hcard hac hcb p hp
  have hl : ScalarPathLevel L (d a) (d c) (2^(∑ i ∈ Finset.Ico a c, k i)) g :=
    ⟨hd hac,haCount,hsep⟩
  have hl' := hl.trim hL (hd hcb) hb F hF
  refine ⟨F,hF,scalarPruneLeaves_nonempty L hne F hFn,
    scalar_single_child_pruning_cost L (hd hcb) F hF hcCount hm,hl',?_⟩
  have hm' : ∀ p ∈ Q.image (List.take (d b)), (prefixFiber Q (d b) p).card = m := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [scalarPruneLeaves_fiber L (hd hcb) le_rfl F hq]
    exact hm _ (Finset.mem_image_of_mem _ (scalarPruneLeaves_subset L (d c) (d b) F hq))
  intro p hp
  rw [prefixFiber_card_sum (hd (hac.trans hcb))]
  have he : ∀ q ∈ prefixChildren Q (d a) (d b) p, (prefixFiber Q (d b) q).card = m :=
    fun q hq => hm' q (prefixChildren_mem_image hq)
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,Nat.nsmul_eq_mul]
  exact congrArg (fun t : ℕ => t*m) (hl'.card p hp)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchTransfer
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality facts for iterating bunch trims from fine to coarse scales. -/
namespace Falconer

namespace Regularization

 theorem prefixChildren_mono {L Q : Finset (CellPath 1)} (hsub : Q ⊆ L)
    (a b : ℕ) (p : CellPath 1) : prefixChildren Q a b p ⊆ prefixChildren L a b p := by
  classical
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2⟩

 theorem ScalarPathLevel.of_same_fibers {L Q : Finset (CellPath 1)} {a b K : ℕ} {g : ℝ}
    (h : ScalarPathLevel L a b K g) (hsub : Q ⊆ L)
    (hf : ∀ q ∈ Q, prefixFiber Q a (q.take a) = prefixFiber L a (q.take a)) :
    ScalarPathLevel Q a b K g := by
  classical
  have hc : ∀ p ∈ Q.image (List.take a), prefixChildren Q a b p = prefixChildren L a b p := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    unfold prefixChildren
    rw [hf q hq]
  refine ⟨h.order,?_,?_⟩
  · intro p hp
    rw [hc p hp]
    exact h.card p (Finset.image_subset_image hsub hp)
  · intro p hp
    rw [hc p hp]
    exact h.separated p (Finset.image_subset_image hsub hp)

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarBunchPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entire greedy ledger is realized by successive prunings of the
 original finite paths. All losses multiply exactly, and each retained
 bunch keeps its proved separation and branching count. -/
namespace Falconer.Regularization

 theorem scalar_trim_bunch_chain {N top lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (d k : ℕ → ℕ) (hd : Monotone d)
    (gap : ScalarBunch → ℝ) :
    ∀ (L : Finset (CellPath 1)) (m : ℕ), L ⊆ cubePaths 1 N → L.Nonempty → d top ≤ N →
    (∀ i < top, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i)) →
    (∀ p ∈ L.image (List.take (d top)), (prefixFiber L (d top) p).card = m) →
    (∀ b ∈ bs, ∀ p ∈ L.image (List.take (d b.start)),
      ∀ u ∈ prefixChildren L (d b.start) (d b.cut) p,
      ∀ v ∈ prefixChildren L (d b.start) (d b.cut) p,
      u ≠ v → gap b ≤ |scalarPathCenter u-scalarPathCenter v|) →
    ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
      L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, k i)).sum)*Q.card ∧
      (∀ c ≤ d lo, Q.image (List.take c) = L.image (List.take c)) ∧
      (∀ c, d top ≤ c → ∀ q ∈ Q, prefixFiber Q c (q.take c) = prefixFiber L c (q.take c)) ∧
      (∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
        (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (gap b-2*(1/2:ℝ)^(d b.cut))) := by
  induction hchain with
  | nil n =>
    intro L m hL hne hN hcard hm hg
    refine ⟨L,Finset.Subset.refl _,hne,by simp,?_,?_,by simp⟩
    · intro c hc
      rfl
    · intro c hc q hq
      rfl
  | @cons b lo bs hchain ih =>
    intro L m hL hne hN hcard hm hg
    have hsc : b.start ≤ b.cut := b.start_lt_cut.le
    have hsb : b.start ≤ b.stop := hsc.trans b.cut_le_stop
    obtain ⟨F,hF,hRne,hcost,hlevel,hmR⟩ := scalar_trimmed_uniform_block L hL hne d k hd
      hsc b.cut_le_stop hN hcard hm (gap b) (hg b (by simp))
    let R := scalarPruneLeaves L (d b.cut) (d b.stop) F
    have hRL : R ⊆ L := scalarPruneLeaves_subset L _ _ F
    have hFn : ∀ p ∈ L.image (List.take (d b.cut)),
        (F p).Nonempty ∧ F p ⊆ prefixChildren L (d b.cut) (d b.stop) p := by
      intro p hp
      exact ⟨Finset.card_pos.mp (by rw [(hF p hp).2]; omega),(hF p hp).1⟩
    have hcardR : ∀ i < b.start, ∀ p ∈ R.image (List.take (d i)),
        (prefixChildren R (d i) (d (i+1)) p).card = 2^(k i) := by
      intro i hi p hp
      rw [scalarPruneLeaves_upper_children L (hd (Nat.le_succ i))
        (hd (show i+1 ≤ b.cut by omega)) F hFn]
      exact hcard i (lt_of_lt_of_le hi hsb) p (Finset.image_subset_image hRL hp)
    have hgR : ∀ c ∈ bs, ∀ p ∈ R.image (List.take (d c.start)),
        ∀ u ∈ prefixChildren R (d c.start) (d c.cut) p,
        ∀ v ∈ prefixChildren R (d c.start) (d c.cut) p,
        u ≠ v → gap c ≤ |scalarPathCenter u-scalarPathCenter v| := by
      intro c hc p hp u hu v hv huv
      exact hg c (by simp [hc]) p (Finset.image_subset_image hRL hp)
        u (prefixChildren_mono hRL _ _ _ hu) v (prefixChildren_mono hRL _ _ _ hv) huv
    obtain ⟨Q,hQR,hQne,hcostQ,hupperQ,hfiberQ,hlevelsQ⟩ :=
      ih R ((2^(∑ i ∈ Finset.Ico b.start b.cut, k i))*m) (hRL.trans hL) hRne
        ((hd hsb).trans hN) hcardR hmR hgR
    refine ⟨Q,hQR.trans hRL,hQne,?_,?_,?_,?_⟩
    · rw [hcost,hcostQ]
      simp only [List.map_cons,List.sum_cons,pow_add]
      exact (Nat.mul_assoc _ _ _).symm
    · intro c hc
      rw [hupperQ c hc]
      exact scalarPruneLeaves_upper_prefixes L
        (hc.trans ((hd hchain.start_le).trans (hd hsc))) F hFn
    · intro c hc q hq
      rw [hfiberQ c ((hd hsb).trans hc) q hq]
      exact scalarPruneLeaves_fiber L (hd b.cut_le_stop) hc F (hQR hq)
    · intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · subst c
        exact hlevel.of_same_fibers hQR (fun q hq => hfiberQ _ le_rfl q hq)
      · exact hlevelsQ c hc

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCompressedLevels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Consecutive original blocks collapse to a separated level. Its gap is
 controlled by the final original block, so prescribed porous endpoints
 supply the separation needed after bunching. -/
namespace Falconer.Regularization

 theorem scalar_branch_scale_mono {M : ℕ} {Q : Finset (CellPath 1)}
    (d k n : ℕ → ℕ) (hd : Monotone d)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    {i j : ℕ} (hij : i ≤ j) (hj : j < M) : n i ≤ n j := by
  rcases hij.eq_or_lt with heq | hij
  · subst i
    exact le_rfl
  · exact (hlevel i (hij.trans hj)).level_hi.trans
      ((hd (show i+1 ≤ j by omega)).trans (hlevel j hj).level_lo)

 theorem scalar_grouped_path_level {N M : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (d k n : ℕ → ℕ) (hd : Monotone d)
    (hdN : ∀ i ≤ M, d i ≤ N)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    {a b : ℕ} (hab : a < b) (hb : b ≤ M) :
    ScalarPathLevel Q (d a) (d b) (2^(∑ i ∈ Finset.Ico a b, k i))
      (6*(1/2:ℝ)^(n (b-1))) := by
  refine ⟨hd hab.le,?_,?_⟩
  · exact fun p hp => scalar_grouped_children_card Q d k hd M
      (fun i hi => (hlevel i hi).children_card) hab.le hb p hp
  · intro p hp
    apply scalar_grouped_children_separated hQ d k n hd hdN hlevel hab.le hb
    intro i hai hib hki
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (scalar_branch_scale_mono d k n hd hlevel (by omega : i ≤ b-1) (by omega)))
      (by norm_num)

 theorem scalar_compressed_path_level {N M T : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (d k n : ℕ → ℕ) (hd : Monotone d)
    (hdN : ∀ i ≤ M, d i ≤ N)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T ≤ M) {j : ℕ} (hj : j < T) :
    ScalarPathLevel Q (d (e j)) (d (e (j+1))) (2^(scalarCompressedBranch e k j))
      (6*(1/2:ℝ)^(n (e (j+1)-1))) := by
  exact scalar_grouped_path_level hQ d k n hd hdN hlevel (he (Nat.lt_succ_self j))
    ((he.monotone (show j+1 ≤ T by omega)).trans heT)

 theorem scalar_compressed_group_separated {N M T : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (d k n : ℕ → ℕ) (hd : Monotone d)
    (hdN : ∀ i ≤ M, d i ≤ N)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T ≤ M)
    {a b : ℕ} (hab : a < b) (hb : b ≤ T) :
    ∀ p ∈ Q.image (List.take (d (e a))),
      ∀ u ∈ prefixChildren Q (d (e a)) (d (e b)) p,
      ∀ v ∈ prefixChildren Q (d (e a)) (d (e b)) p,
      u ≠ v → 6*(1/2:ℝ)^(n (e b-1)) ≤ |scalarPathCenter u-scalarPathCenter v| :=
  (scalar_grouped_path_level hQ d k n hd hdN hlevel (he hab)
    ((he.monotone hb).trans heT)).separated

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarCompressedBunching
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realizing a bunching ledger after grouping the original regularized
 dyadic levels. The final gap is stated in the original geometric scale. -/
namespace Falconer.Regularization

 theorem ScalarPathLevel.mono_gap {Q : Finset (CellPath 1)} {a b K : ℕ} {g h : ℝ}
    (hp : ScalarPathLevel Q a b K g) (hh : h ≤ g) : ScalarPathLevel Q a b K h :=
  ⟨hp.order,hp.card,fun p hq u hu v hv hne => hh.trans (hp.separated p hq u hu v hv hne)⟩

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarBunchGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative radius-to-gap estimates for a trimmed porous bunch. -/
namespace Falconer

 theorem scalar_dyadic_gap_ratio {n s H : ℕ} (hs : n+H ≤ s) :
    5*(1/2:ℝ)^s/(4*(1/2:ℝ)^n) ≤ (5/4:ℝ)*(1/2:ℝ)^H := by
  have hpow : (1/2:ℝ)^s ≤ (1/2:ℝ)^n*(1/2:ℝ)^H := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  apply (div_le_iff₀ (by positivity : 0 < 4*(1/2:ℝ)^n)).2
  nlinarith

 theorem scalar_dyadic_gap_geometry {n s N : ℕ} (hn : n+2 ≤ s) (hs : s ≤ N) :
    15*(1/2:ℝ)^s < 4*(1/2:ℝ)^n ∧
      (1/2:ℝ)^N ≤ 5*(1/2:ℝ)^s/(4*(1/2:ℝ)^n) := by
  have hpow : (1/2:ℝ)^s ≤ (1/2:ℝ)^n/4 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) hn
    rw [pow_add] at hh
    norm_num at hh
    linarith
  have hpos : 0 < (1/2:ℝ)^n := by positivity
  have hle : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hNs : (1/2:ℝ)^N ≤ (1/2:ℝ)^s :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  constructor
  · linarith
  · apply hNs.trans
    apply (le_div_iff₀ (by positivity : 0 < 4*(1/2:ℝ)^n)).2
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) s]

 theorem scalar_dyadic_bunch_small {n s H M : ℕ} {K κ : ℝ}
    (hs : n+H ≤ s) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hsmall : 16*(M:ℝ)^4*K*((5/4:ℝ)*(1/2:ℝ)^H)^κ ≤ 1/4) :
    16*(M:ℝ)^4*K*(5*(1/2:ℝ)^s/(4*(1/2:ℝ)^n))^κ ≤ 1/4 := by
  apply le_trans _ hsmall
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (by positivity) (scalar_dyadic_gap_ratio hs) hκ

 theorem scalarPathCenter_unit (p : List (Fin 1 → Bool)) :
    0 ≤ scalarPathCenter p ∧ scalarPathCenter p ≤ 1 := by
  have hh := (⟨0,1⟩ : DyadicCube 1).descendant_subset p
    (((⟨0,1⟩ : DyadicCube 1).descendant p).center_mem
      ((⟨0,1⟩ : DyadicCube 1).descendant_side_pos (by norm_num) p))
  have hcoord := hh 0
  change 0 ≤ scalarPathCenter p ∧ scalarPathCenter p < 0+1 at hcoord
  exact ⟨hcoord.1,by linarith [hcoord.2]⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarBunchProducts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite ledger products in the exact form used by the path tree. -/
namespace Falconer

 theorem scalar_list_product_powers {α : Type*} (L : List α) (f : α → ℕ) :
    (∏ i ∈ Finset.range L.length, (L.map (fun x => 2^(f x))).getD i 1) =
      2^((L.map f).sum) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    rw [Finset.prod_range_succ']
    simp only [List.getD_cons_succ,List.getD_cons_zero]
    rw [ih,pow_add,Nat.mul_comm]

 theorem scalar_list_sum_logs {α : Type*} (L : List α) (f : α → ℕ) :
    (∑ i ∈ Finset.range L.length, Real.log ((L.map f).getD i 1 : ℝ)) =
      (L.map (fun x => Real.log (f x : ℝ))).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ,List.getD_cons_zero]
    rw [ih,add_comm]

 theorem scalarBunchBoundary_length (lo : ℕ) (bs : List ScalarBunch) :
    scalarBunchBoundary lo bs bs.length = lo := by
  apply List.getD_eq_default
  simp

namespace Regularization

 theorem scalar_prefix_points_subset (Q : Finset (CellPath 1)) (a : ℕ) (x : ℝ) :
    scalarPrefixPoints Q a x ⊆ Q.image scalarPathCenter :=
  Finset.image_subset_image (Finset.filter_subset _ _)

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchSizes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing group sizes from the greedy bunch lengths. A threshold 2P
 gives groups of size 2^(P length), with a closed formula for total gain. -/
namespace Falconer

 theorem ScalarBunch.length_pos (b : ScalarBunch) : 0 < b.stop-b.start := by
  have h1 := b.start_lt_cut
  have h2 := b.cut_le_stop
  omega

 theorem scalar_bunch_group_large {P : ℕ} (hP : 18 ≤ P) (b : ScalarBunch) :
    83521 ≤ scalarBunchGroup P b := by
  have hx : 18 ≤ P*(b.stop-b.start) := by
    have hh := Nat.mul_le_mul_left P (show 1 ≤ b.stop-b.start from b.length_pos)
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hx
  exact (by norm_num : 83521 ≤ 2^18).trans hpow

 theorem scalar_bunch_group_room (w : ℕ → ℕ) {P : ℕ} (hP : 2 ≤ P) (b : ScalarBunch)
    (hgood : ScalarBunchGood (fun i => (w i:ℝ)) (2*(P:ℝ)) b) :
    2*scalarBunchGroup P b ≤ 2^(∑ i ∈ Finset.Ico b.start b.cut, w i) := by
  have hx : 2 ≤ P*(b.stop-b.start) := by
    have hh := Nat.mul_le_mul_left P (show 1 ≤ b.stop-b.start from b.length_pos)
    omega
  have hxR : (2:ℝ) ≤ (P:ℝ)*((b.stop-b.start:ℕ):ℝ) := by exact_mod_cast hx
  have hr := hgood.retained
  have hs : ((P*(b.stop-b.start)+1:ℕ):ℝ) ≤
      ((∑ i ∈ Finset.Ico b.start b.cut, w i):ℝ) := by
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    nlinarith
  have hsN : P*(b.stop-b.start)+1 ≤ ∑ i ∈ Finset.Ico b.start b.cut, w i := by exact_mod_cast hs
  calc
    2*scalarBunchGroup P b = 2^(P*(b.stop-b.start)+1) := by
      simp only [scalarBunchGroup,pow_succ]
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hsN

 theorem ScalarBunchChain.group_log_sum {top lo P : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) :
    (bs.map (fun b => Real.log (scalarBunchGroup P b:ℝ))).sum =
      (P:ℝ)*((top-lo:ℕ):ℝ)*Real.log 2 := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have he : ((b.stop-lo:ℕ):ℝ) = ((b.stop-b.start:ℕ):ℝ)+((b.start-lo:ℕ):ℝ) := by
      have hlo := h.start_le
      have h1 := b.start_lt_cut
      have h2 := b.cut_le_stop
      exact_mod_cast (show b.stop-lo = (b.stop-b.start)+(b.start-lo) by omega)
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    simp only [scalarBunchGroup,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul]
    rw [he]
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchMargins
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each discarded porous level contributes a full block of geometric
 separation. These bounds use the actual increasing endpoint indices. -/
namespace Falconer

 theorem scalar_increasing_endpoint_gap (e : ℕ → ℕ) (he : StrictMono e)
    {a b : ℕ} (hab : a ≤ b) : e a+(b-a) ≤ e b := by
  have hh := he.add_le_nat (b-a) a
  simpa only [Nat.sub_add_cancel hab,Nat.add_comm] using hh

 theorem scalar_bunch_margin (e n : ℕ → ℕ) (he : StrictMono e) (B C : ℕ)
    (b : ScalarBunch) (hporous : n (e b.cut-1)+C ≤ B*e b.cut) :
    n (e b.cut-1)+(C+B*(b.stop-b.cut)) ≤ B*e b.stop := by
  have hg := Nat.mul_le_mul_left B (scalar_increasing_endpoint_gap e he b.cut_le_stop)
  rw [Nat.mul_add] at hg
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single explicit parameter choice controls the exceptional-pair
 budget in both the short and long porous bunches. -/
namespace Falconer

 theorem scalar_bunch_log_weight (P H : ℕ) (b : ScalarBunch) {K κ : ℝ} (hK : 0 < K) :
    Real.log (16*(scalarBunchGroup P b:ℝ)^4*K*((5/4:ℝ)*(1/2:ℝ)^H)^κ) =
      4*Real.log 2 + 4*(P:ℝ)*((b.stop-b.start:ℕ):ℝ)*Real.log 2 + Real.log K +
        κ*(Real.log (5/4:ℝ)-(H:ℝ)*Real.log 2) := by
  have hgroup : 0 < (scalarBunchGroup P b:ℝ) := by
    unfold scalarBunchGroup
    positivity
  have h16 : Real.log (16:ℝ) = 4*Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num,Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (ne_of_gt hK),Real.log_mul (by norm_num) (by positivity),
    Real.log_pow,Real.log_rpow (by positivity),Real.log_mul (by norm_num) (by positivity),
    Real.log_pow,h16,hhalf]
  simp only [scalarBunchGroup,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul]
  ring

 theorem scalar_bunch_uniform_budget {P B C : ℕ} {K κ : ℝ} (hK : 0 < K)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (b : ScalarBunch) {w : ℕ → ℝ} {theta : ℝ} (hgood : ScalarBunchGood w theta b) :
    16*(scalarBunchGroup P b:ℝ)^4*K*
      ((5/4:ℝ)*(1/2:ℝ)^(C+B*(b.stop-b.cut)))^κ ≤ 1/4 := by
  have hgroup : 0 < (scalarBunchGroup P b:ℝ) := by
    unfold scalarBunchGroup
    positivity
  have ht : (0:ℝ) ≤ ((b.stop-b.cut:ℕ):ℝ) := Nat.cast_nonneg _
  have hp : (0:ℝ) ≤ (P:ℝ) := Nat.cast_nonneg _
  have hlen : 4*(P:ℝ)*((b.stop-b.start:ℕ):ℝ) ≤
      4000*(P:ℝ)+κ*(B:ℝ)*((b.stop-b.cut:ℕ):ℝ) := by
    rcases hgood.gap with ⟨hzero,hsmall⟩ | hlarge
    · have hs : ((b.stop-b.start:ℕ):ℝ) ≤ 1000 := by exact_mod_cast hsmall
      have hz : b.stop-b.cut = 0 := by omega
      simp only [hz,Nat.cast_zero,mul_zero,add_zero]
      nlinarith
    · have hl : ((b.stop-b.start:ℕ):ℝ) ≤ 200*((b.stop-b.cut:ℕ):ℝ) := by exact_mod_cast hlarge
      have hm := mul_le_mul_of_nonneg_right hB ht
      nlinarith
  have hlog64 : Real.log (64*K) = 6*Real.log 2+Real.log K := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hK),show (64:ℝ) = 2^6 by norm_num,Real.log_pow]
    norm_num
  have hquarter : Real.log (1/4:ℝ) = -2*Real.log 2 := by
    rw [show (1/4:ℝ) = ((2:ℝ)^2)⁻¹ by norm_num,Real.log_inv,Real.log_pow]
    norm_num
  apply (Real.log_le_log_iff (by positivity) (by norm_num : (0:ℝ) < 1/4)).1
  rw [scalar_bunch_log_weight P _ b hK,hquarter]
  simp only [Nat.cast_add,Nat.cast_mul]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hlen hlog2.le
  rw [hlog64] at hC
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarBranchGrowth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite scalar branching with a reserved separation margin. This
 records exactly the tail-motion bookkeeping of the nonporous argument. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_branch_union_separated {α : Type*} (v : α → ℝ) (S : Finset α)
    (F : α → Finset α) {D ρ r : ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → D ≤ |v x-v y|)
    (hF : ∀ x ∈ S, ∀ y ∈ F x, ∀ z ∈ F x, y ≠ z → ρ ≤ |v y-v z|)
    (hm : ∀ x ∈ S, ∀ y ∈ F x, |v y-v x| ≤ r)
    (hgap : ρ+2*r ≤ D) :
    ∀ y ∈ S.biUnion F, ∀ z ∈ S.biUnion F, y ≠ z → ρ ≤ |v y-v z| := by
  intro y hy z hz hyz
  obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨w,hw,hz⟩ := Finset.mem_biUnion.mp hz
  by_cases hxw : x = w
  · subst w
    exact hF x hx y hy z hz hyz
  · have h0 := hS x hx w hw hxw
    have h1 := hm x hx y hy
    have h2 := hm w hw z hz
    have ht : |v x-v w| ≤ |v y-v x|+|v y-v z|+|v z-v w| := by
      calc
        _ ≤ |v x-v y|+|v y-v w| := abs_sub_le _ _ _
        _ ≤ |v x-v y|+(|v y-v z|+|v z-v w|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ = _ := by rw [abs_sub_comm (v x) (v y)]; ring
    linarith

 theorem scalar_branch_union_card {α : Type*} (v : α → ℝ) (S : Finset α)
    (F : α → Finset α) (J : ℕ) {D r : ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → D ≤ |v x-v y|)
    (hcard : ∀ x ∈ S, (F x).card = J)
    (hm : ∀ x ∈ S, ∀ y ∈ F x, |v y-v x| ≤ r)
    (hgap : 2*r < D) : (S.biUnion F).card = S.card*J := by
  have hd : (S : Set α).PairwiseDisjoint F := by
    intro x hx w hw hxw
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have h0 := hS x hx w hw hxw
    have h1 := hm x hx y hy
    have h2 := hm w hw y hz
    have ht : |v x-v w| ≤ |v y-v x|+|v y-v w| := by
      simpa only [abs_sub_comm (v x) (v y)] using abs_sub_le (v x) (v y) (v w)
    linarith
  rw [Finset.card_biUnion hd]
  calc
    _ = ∑ _x ∈ S, J := Finset.sum_congr rfl (fun x hx => hcard x hx)
    _ = _ := by simp

 theorem scalar_finite_branch_growth {α : Type*} (v : α → ℝ) (P : ℕ → α → Prop)
    (N J : ℕ) (r b : ℕ → ℝ) (root : α) (hroot : P 0 root)
    (hb : ∀ n ≤ N, 0 < b n)
    (hgap : ∀ n < N, b (n+1)+2*r n ≤ b n)
    (hstep : ∀ n < N, ∀ x, P n x → ∃ F : Finset α,
      F.card = J ∧ (∀ y ∈ F, P (n+1) y) ∧
      (∀ y ∈ F, |v y-v x| ≤ r n) ∧
      (∀ y ∈ F, ∀ z ∈ F, y ≠ z → b (n+1) ≤ |v y-v z|)) :
    ∃ S : Finset α, S.card = J^N ∧ (∀ x ∈ S, P N x) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → b N ≤ |v x-v y| := by
  suffices hh : ∀ n ≤ N, ∃ S : Finset α, S.card = J^n ∧ (∀ x ∈ S, P n x) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → b n ≤ |v x-v y| from hh N le_rfl
  intro n hn
  induction n with
  | zero =>
    refine ⟨{root},by simp,?_,?_⟩
    · intro x hx
      simpa only [Finset.mem_singleton.mp hx] using hroot
    · intro x hx y hy hne
      exact False.elim (hne ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm))
  | succ n ih =>
    obtain ⟨S,hcard,hP,hsep⟩ := ih (by omega)
    have hnN : n < N := by omega
    have hex : ∀ x, ∃ F : Finset α, x ∈ S →
        F.card = J ∧ (∀ y ∈ F, P (n+1) y) ∧
        (∀ y ∈ F, |v y-v x| ≤ r n) ∧
        (∀ y ∈ F, ∀ z ∈ F, y ≠ z → b (n+1) ≤ |v y-v z|) := by
      intro x
      by_cases hx : x ∈ S
      · obtain ⟨F,hF⟩ := hstep n hnN x (hP x hx)
        exact ⟨F,fun _ => hF⟩
      · exact ⟨∅,fun h => False.elim (hx h)⟩
    choose F hF using hex
    have hmotion := fun x hx => (hF x hx).2.2.1
    have hchildren := fun x hx => (hF x hx).2.2.2
    refine ⟨S.biUnion F,?_,?_,?_⟩
    · rw [scalar_branch_union_card v S F J hsep (fun x hx => (hF x hx).1)
        hmotion (by have := hb (n+1) hn; have := hgap n hnN; linarith),hcard,pow_succ]
    · intro y hy
      obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
      exact (hF x hx).2.1 y hy
    · exact scalar_branch_union_separated v S F hsep hchildren hmotion (hgap n hnN)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBinaryGrowth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating the actual binary switching construction. The final points
 remain in one fixed-fold sumset, while their number grows at every level. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_binary_growth {N k J : ℕ} (f : (Fin N → Bool) → ℝ)
    (A : Finset ℝ) (hf : ∀ w, f w ∈ A)
    (ε R ell b : ℕ → ℝ) (L : ℕ → ℕ) (hJ : 0 < J)
    (hε : ∀ n < N, 0 < ε n) (hb : ∀ n ≤ N, 0 < b n)
    (hlo : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      ell n ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      |f (Function.update w n true)-f w| ≤ R n)
    (hR : ∀ n < N, R n ≤ (L n:ℝ)*ε n)
    (hsize : ∀ n < N, (2*L n+1)*J ≤ k)
    (hmargin : ∀ n < N, b (n+1)+2*(J:ℝ)*ε n ≤ ell n)
    (hgap : ∀ n < N, b (n+1)+2*(J:ℝ)*R n ≤ b n) :
    ∃ E : Finset ℝ, E ⊆ k • A ∧ E.card = (J+1)^N ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → b N ≤ |x-y| := by
  let P : ℕ → (Fin k → Fin N → Bool) → Prop :=
    fun n c => ∀ i, ScalarBinaryTail n (c i)
  let root : Fin k → Fin N → Bool := fun _ _ => false
  have hroot : P 0 root := fun _ _ _ => rfl
  have hstep : ∀ n < N, ∀ c, P n c →
      ∃ F : Finset (Fin k → Fin N → Bool), F.card = J+1 ∧
        (∀ d ∈ F, P (n+1) d) ∧
        (∀ d ∈ F, |scalarBinarySum f d-scalarBinarySum f c| ≤ (J:ℝ)*R n) ∧
        (∀ d ∈ F, ∀ d' ∈ F, d ≠ d' → b (n+1) ≤ |scalarBinarySum f d-scalarBinarySum f d'|) := by
    intro n hn c hc
    let n' : Fin N := ⟨n,hn⟩
    obtain ⟨e,_,htail,hmotion,hsep⟩ := scalar_binary_branch f c n' hc (hε n hn)
      (hlo n') (hhi n') (L n) J hJ (hR n hn) (hsize n hn) (hmargin n hn)
    let child := fun j => scalarBinaryStep c n' ((Finset.range j).image e)
    have hinj : Set.InjOn child (Finset.range (J+1) : Set ℕ) := by
      intro i hi j hj hij
      by_contra hne
      have hs := hsep i (by have := Finset.mem_range.mp hi; omega)
        j (by have := Finset.mem_range.mp hj; omega) hne
      change b (n+1) ≤ |scalarBinarySum f (child i)-scalarBinarySum f (child j)| at hs
      rw [hij,sub_self,abs_zero] at hs
      exact (not_le_of_gt (hb (n+1) (by omega))) hs
    refine ⟨(Finset.range (J+1)).image child,?_,?_,?_,?_⟩
    · rw [Finset.card_image_of_injOn hinj,Finset.card_range]
    · intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      exact htail j (by have := Finset.mem_range.mp hj; omega)
    · intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      have hjJ : j ≤ J := by have := Finset.mem_range.mp hj; omega
      have hk : 0 < k := (Nat.mul_pos (by omega) hJ).trans_le (hsize n hn)
      let i0 : Fin k := ⟨0,hk⟩
      have hRn : 0 ≤ R n := (abs_nonneg _).trans (hhi n' (c i0) (hc i0))
      exact (hmotion j hjJ).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hjJ) hRn)
    · intro d hd d' hd' hne
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd'
      exact hsep i (by have := Finset.mem_range.mp hi; omega)
        j (by have := Finset.mem_range.mp hj; omega) (fun hij => hne (congrArg child hij))
  obtain ⟨S,hcard,_,hsep⟩ := scalar_finite_branch_growth (scalarBinarySum f) P N (J+1)
    (fun n => (J:ℝ)*R n) b root hroot hb (by simpa only [mul_assoc] using hgap) hstep
  have hinj : Set.InjOn (scalarBinarySum f) (S : Set (Fin k → Fin N → Bool)) := by
    intro c hc d hd heq
    by_contra hne
    have hs := hsep c hc d hd hne
    rw [heq,sub_self,abs_zero] at hs
    exact (not_le_of_gt (hb N le_rfl)) hs
  refine ⟨S.image (scalarBinarySum f),?_,?_,?_⟩
  · intro x hx
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hx
    exact scalar_binary_sum_mem f A hf c
  · rw [Finset.card_image_of_injOn hinj,hcard]
  · intro x hx y hy hxy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hy
    exact hsep c hc d hd (fun hcd => hxy (congrArg (scalarBinarySum f) hcd))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRepeatedSums
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding errors for repeated scalar sumsets. Only one interval of
integer carries is required, so the loss is linear in the number of terms. -/
namespace Falconer
open scoped Pointwise

theorem scalar_nsum_floor (δ : ℝ) (X : Finset ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ n • X) :
    ∃ z ∈ n • scalarCells δ X, ∃ k : ℤ,
      0 ≤ k ∧ k ≤ (n : ℤ) ∧ ⌊x/δ⌋ = z+k := by
  classical
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact ⟨0,by simp,0,by norm_num,by norm_num,by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨z,hz,k,hk0,hkn,hk⟩ := ih ha
    have hbq : ⌊b/δ⌋ ∈ scalarCells δ X := Finset.mem_image.mpr ⟨b,hb,rfl⟩
    have hmem : z+⌊b/δ⌋ ∈ (n+1) • scalarCells δ X := by
      rw [succ_nsmul]
      exact Finset.add_mem_add hz hbq
    rw [add_div]
    rcases floor_add_carry (a/δ) (b/δ) with he | he
    · refine ⟨z+⌊b/δ⌋,hmem,k,hk0,by omega,?_⟩
      omega
    · refine ⟨z+⌊b/δ⌋,hmem,k+1,by omega,by omega,?_⟩
      omega

theorem scalar_signed_sum_cells_subset (δ : ℝ) (X : Finset ℝ) (m n : ℕ) :
    scalarCells δ (m • X-n • X) ⊆
      (m • scalarCells δ X-n • scalarCells δ X)+Finset.Icc (-(n : ℤ)-1) (m : ℤ) := by
  classical
  intro w hw
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  obtain ⟨z,hz,k,hk0,hkm,hk⟩ := scalar_nsum_floor δ X m ha
  obtain ⟨v,hv,l,hl0,hln,hl⟩ := scalar_nsum_floor δ X n hb
  rw [sub_div]
  rcases floor_sub_carry (a/δ) (b/δ) with he | he
  · apply Finset.mem_add.mpr
    exact ⟨z-v,Finset.sub_mem_sub hz hv,k-l,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · apply Finset.mem_add.mpr
    exact ⟨z-v,Finset.sub_mem_sub hz hv,k-l-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩

theorem scalar_signed_sum_card (δ : ℝ) (X : Finset ℝ) (m n : ℕ) :
    (scalarCells δ (m • X-n • X)).card ≤
      (m+n+2)*(m • scalarCells δ X-n • scalarCells δ X).card := by
  classical
  have hc : (Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card = m+n+2 := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((m • scalarCells δ X-n • scalarCells δ X)+Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card :=
      Finset.card_le_card (scalar_signed_sum_cells_subset δ X m n)
    _ ≤ (m • scalarCells δ X-n • scalarCells δ X).card*
        (Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card := Finset.card_add_le
    _ = _ := by rw [hc,Nat.mul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPluennecke
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The application form of Pluennecke's inequality for scalar covering
numbers. Its only rounding loss is linear in the number of summands. -/
namespace Falconer
open scoped Pointwise

theorem scalar_pluennecke (δ : ℝ) (A B : Finset ℝ) (hA : A.Nonempty)
    {K : ℝ}
    (hsmall : ((scalarCells δ (A+B)).card : ℝ) ≤ K*(scalarCells δ A).card)
    (m n : ℕ) :
    ((scalarCells δ (m • B-n • B)).card : ℝ) ≤
      (m+n+2)*(2*K)^(m+n)*(scalarCells δ A).card := by
  have hAQ : (scalarCells δ A).Nonempty := Finset.image_nonempty.mpr hA
  have hAc : 0 < ((scalarCells δ A).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hAQ)
  have hR := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hAQ
    (scalarCells δ B) m n
  have hRR : ((m • scalarCells δ B-n • scalarCells δ B).card : ℝ) ≤
      (((scalarCells δ A+scalarCells δ B).card : ℝ)/(scalarCells δ A).card)^(m+n)*
        (scalarCells δ A).card := by
    have hReal := NNRat.cast_mono (K := ℝ) hR
    push_cast at hReal
    exact hReal
  have hsum : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
      (2*K)*(scalarCells δ A).card := by
    have hc : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
        2*((scalarCells δ (A+B)).card : ℝ) := by exact_mod_cast add_scalarCells_card δ A B
    nlinarith
  have hratio : ((scalarCells δ A+scalarCells δ B).card : ℝ)/(scalarCells δ A).card ≤
      2*K := (div_le_iff₀ hAc).2 hsum
  have hpow := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hAc.le) hratio (m+n)
  have hbound := hRR.trans (mul_le_mul_of_nonneg_right hpow hAc.le)
  have hcarry : ((scalarCells δ (m • B-n • B)).card : ℝ) ≤
      (m+n+2)*((m • scalarCells δ B-n • scalarCells δ B).card : ℝ) := by
    exact_mod_cast scalar_signed_sum_card δ B m n
  have hmn : (0 : ℝ) ≤ m+n+2 := by positivity
  exact hcarry.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hmn)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBinaryGeometric
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometrically spaced nonporous binary increments force growth of a
 fixed-fold sumset, and hence contradict an appropriately small sumset. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_scaled_binary_growth {N k J L : ℕ} {U : ℝ}
    (f : (Fin N → Bool) → ℝ) (A : Finset ℝ) (hf : ∀ w, f w ∈ A)
    (scale : ℕ → ℝ) (hs : ∀ n ≤ N, 0 < scale n) (hJ : 0 < J)
    (hcontract : ∀ n < N, scale (n+1)*(1+2*(J:ℝ)*U) ≤ scale n)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hk : (2*L+1)*J ≤ k)
    (hlo : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      2*scale ((n:ℕ)+1) ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      |f (Function.update w n true)-f w| ≤ U*scale ((n:ℕ)+1)) :
    ∃ E : Finset ℝ, E ⊆ k • A ∧ E.card = (J+1)^N ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → scale N ≤ |x-y| := by
  have hJr : 0 < (J:ℝ) := by exact_mod_cast hJ
  apply scalar_binary_growth f A hf (fun n => scale (n+1)/(4*(J:ℝ)))
    (fun n => U*scale (n+1)) (fun n => 2*scale (n+1)) (fun n => scale n) (fun _ => L) hJ
  · intro n hn
    exact div_pos (hs (n+1) (by omega)) (by positivity)
  · exact hs
  · exact hlo
  · exact hhi
  · intro n hn
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < 4*(J:ℝ) by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hL (hs (n+1) (by omega)).le
    calc
      U*scale (n+1)*(4*(J:ℝ)) = (4*(J:ℝ)*U)*scale (n+1) := by ring
      _ ≤ (L:ℝ)*scale (n+1) := hh
  · exact fun _ _ => hk
  · intro n hn
    have he : 2*(J:ℝ)*(scale (n+1)/(4*(J:ℝ))) = scale (n+1)/2 := by
      field_simp
      ring
    rw [he]
    have hp := (hs (n+1) (by omega)).le
    linarith
  · intro n hn
    calc
      scale (n+1)+2*(J:ℝ)*(U*scale (n+1)) = scale (n+1)*(1+2*(J:ℝ)*U) := by ring
      _ ≤ scale n := hcontract n hn

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarForkSumset
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the fixed-fold sumset construction to actual selected
 dyadic forks, with explicit scale margins. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_selected_fork_sumset {N copies J L : ℕ} {U : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 N) (hne : Q.Nonempty)
    (t : ℕ) (a b branch n : ℕ → ℕ)
    (hab : ∀ i < t, a i ≤ b i) (hnext : ∀ i < t, b i ≤ a (i+1))
    (hb : ∀ i < t, b i ≤ N)
    (hlevel : ∀ i < t, ScalarBranchingLevel Q (a i) (b i) (branch i) (n i))
    (hbranch : ∀ i < t, branch i ≠ 0)
    (scale : ℕ → ℝ) (hs : ∀ i ≤ t, 0 < scale i) (hJ : 0 < J)
    (hcontract : ∀ i < t, scale (i+1)*(1+2*(J:ℝ)*U) ≤ scale i)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hcopies : (2*L+1)*J ≤ copies)
    (hlow : ∀ i < t, 2*scale (i+1) ≤ 6*(1/2:ℝ)^(n i))
    (hhigh : ∀ i < t, 18*(1/2:ℝ)^(n i) ≤ U*scale (i+1)) :
    ∃ E : Finset ℝ, E ⊆ copies • Q.image scalarPathCenter ∧ E.card = (J+1)^t ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → scale t ≤ |x-y| := by
  obtain ⟨f,hf,hbits⟩ := scalar_selected_binary_forks Q hQ hne t a b branch n hab hnext hb hlevel hbranch
  apply scalar_scaled_binary_growth f (Q.image scalarPathCenter) hf scale hs hJ hcontract hL hcopies
  · intro i w hw
    exact (hlow i i.isLt).trans (hbits i w hw).1
  · intro i w hw
    exact (hbits i w hw).2.trans (hhigh i i.isLt)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarNonporousPowers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale arithmetic for a subsequence of nonporous dyadic blocks. -/
namespace Falconer.Regularization

 theorem scalar_dyadic_shift (b n C : ℕ) (h : b ≤ n+C) :
    (1/2:ℝ)^n ≤ (2:ℝ)^C*(1/2:ℝ)^b := by
  have hh : (1/2:ℝ)^(n+C) ≤ (1/2:ℝ)^b :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have he : (1/2:ℝ)^(n+C)*(2:ℝ)^C = (1/2:ℝ)^n := by
    rw [pow_add,mul_assoc,← mul_pow]
    norm_num
  have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) C)
  rw [he] at hm
  simpa only [mul_comm] using hm

 theorem scalar_dyadic_contract {W : ℝ} (hW : 0 ≤ W) (B x y : ℕ)
    (hgap : x+B ≤ y) (hc : (1/2:ℝ)^B*W ≤ 1) :
    (1/2:ℝ)^y*W ≤ (1/2:ℝ)^x := by
  have hp : (1/2:ℝ)^y ≤ (1/2:ℝ)^(x+B) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hgap
  calc
    _ ≤ (1/2:ℝ)^(x+B)*W := mul_le_mul_of_nonneg_right hp hW
    _ = (1/2:ℝ)^x*((1/2:ℝ)^B*W) := by rw [pow_add,mul_assoc]
    _ ≤ (1/2:ℝ)^x*1 := mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num) x)
    _ = _ := mul_one _

 theorem scalarSelectedScale_succ (B : ℕ) (g : ℕ → ℕ) (i : ℕ) :
    scalarSelectedScale B g (i+1) = (1/2:ℝ)^(B*(g i+1)) := by
  simp [scalarSelectedScale]

 theorem scalarSelectedScale_pos (B : ℕ) (g : ℕ → ℕ) (i : ℕ) :
    0 < scalarSelectedScale B g i := by
  unfold scalarSelectedScale
  split_ifs <;> positivity

 theorem scalarSelectedScale_contract {W : ℝ} (hW : 0 ≤ W) (B t : ℕ) (g : ℕ → ℕ)
    (hg : ∀ i < t, g i < g (i+1)) (hc : (1/2:ℝ)^B*W ≤ 1) :
    ∀ i < t, scalarSelectedScale B g (i+1)*W ≤ scalarSelectedScale B g i := by
  intro i hi
  rw [scalarSelectedScale_succ]
  by_cases hi0 : i = 0
  · subst i
    rw [scalarSelectedScale,ite_eq_left rfl]
    apply scalar_dyadic_contract hW B _ _ _ hc
    simp only [Nat.mul_add,Nat.mul_one]
    exact le_rfl
  · rw [scalarSelectedScale,ite_eq_right hi0]
    apply scalar_dyadic_contract hW B _ _ _ hc
    have hprev := hg (i-1) (by omega)
    have hie : i-1+1 = i := by omega
    rw [hie] at hprev
    have hm := Nat.mul_le_mul_left B (show g (i-1)+1+1 ≤ g i+1 by omega)
    simpa only [Nat.mul_add,Nat.mul_one] using hm

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarNonporousGrowth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual nonporous blocks, including skipped levels, produce a large
 separated subset of a fixed-fold sumset of the original leaf centers. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_nonporous_growth {B M copies J L C : ℕ} {U : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (branch n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (branch i) (n i))
    (t : ℕ) (g : ℕ → ℕ) (hg : ∀ i < t, g i < g (i+1)) (hgM : ∀ i < t, g i < M)
    (hbranch : ∀ i < t, branch (g i) ≠ 0)
    (hpor : ∀ i < t, B*(g i+1) ≤ n (g i)+C)
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hcopies : (2*L+1)*J ≤ copies) :
    ∃ E : Finset ℝ, E ⊆ copies • Q.image scalarPathCenter ∧ E.card = (J+1)^t ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → (1/2:ℝ)^(B*M) ≤ |x-y| := by
  by_cases ht0 : t = 0
  · have hA : (Q.image scalarPathCenter).Nonempty := hne.image scalarPathCenter
    have hsum : (copies • Q.image scalarPathCenter).Nonempty := hA.nsmul
    obtain ⟨x,hx⟩ := hsum
    refine ⟨{x},Finset.singleton_subset_iff.mpr hx,by simp [ht0],?_⟩
    intro y hy z hz hyz
    exact False.elim (hyz ((Finset.mem_singleton.mp hy).trans (Finset.mem_singleton.mp hz).symm))
  have hU0 : 0 ≤ U := (by positivity : (0:ℝ) ≤ 18*(2:ℝ)^C).trans hU
  have hW : 0 ≤ 1+2*(J:ℝ)*U := by positivity
  have hscale := scalarSelectedScale_contract hW B t g hg hcontract
  have hlower : ∀ i < t,
      2*scalarSelectedScale B g (i+1) ≤ 6*(1/2:ℝ)^(n (g i)) := by
    intro i hi
    rw [scalarSelectedScale_succ]
    have hn := (hlevel (g i) (hgM i hi)).level_hi
    have hp : (1/2:ℝ)^(B*(g i+1)) ≤ (1/2:ℝ)^(n (g i)) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have hp0 : 0 ≤ (1/2:ℝ)^(n (g i)) := by positivity
    linarith
  have hupper : ∀ i < t,
      18*(1/2:ℝ)^(n (g i)) ≤ U*scalarSelectedScale B g (i+1) := by
    intro i hi
    rw [scalarSelectedScale_succ]
    have hh := scalar_dyadic_shift (B*(g i+1)) (n (g i)) C (hpor i hi)
    calc
      _ ≤ 18*((2:ℝ)^C*(1/2:ℝ)^(B*(g i+1))) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = (18*(2:ℝ)^C)*(1/2:ℝ)^(B*(g i+1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hU (by positivity)
  obtain ⟨E,hE,hcard,hsep⟩ := scalar_selected_fork_sumset Q hQ hne t
    (fun i => B*g i) (fun i => B*(g i+1)) (fun i => branch (g i)) (fun i => n (g i))
    (fun i _ => Nat.mul_le_mul_left B (Nat.le_succ _))
    (fun i hi => Nat.mul_le_mul_left B (by have := hg i hi; omega))
    (fun i hi => Nat.mul_le_mul_left B (by have := hgM i hi; omega))
    (fun i hi => hlevel (g i) (hgM i hi)) hbranch
    (scalarSelectedScale B g) (fun i _ => scalarSelectedScale_pos B g i) hJ hscale hL hcopies hlower hupper
  refine ⟨E,hE,hcard,?_⟩
  have hfinal : (1/2:ℝ)^(B*M) ≤ scalarSelectedScale B g t := by
    rw [scalarSelectedScale,ite_eq_right ht0]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.mul_le_mul_left B (by have := hgM (t-1) (by omega); omega))
  exact fun x hx y hy hxy => hfinal.trans (hsep x hx y hy hxy)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarLevelEnumeration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerating selected scalar blocks in geometric order, with a final
 sentinel for the gap after the last selected block. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_level_enumeration (M : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range M) :
    ∃ g : ℕ → ℕ, (∀ i < S.card, g i ∈ S) ∧
      (∀ i < S.card, g i < g (i+1)) ∧ (∀ i < S.card, g i < M) := by
  classical
  let E := S.orderIsoOfFin rfl
  let g := fun i : ℕ => if hi : i < S.card then (E ⟨i,hi⟩).val else M
  have hm : ∀ i < S.card, g i ∈ S := by
    intro i hi
    simpa only [g,dite_eq_left hi] using (E ⟨i,hi⟩).property
  have hb : ∀ i < S.card, g i < M := fun i hi => Finset.mem_range.mp (hS (hm i hi))
  refine ⟨g,hm,?_,hb⟩
  intro i hi
  by_cases hj : i+1 < S.card
  · have he : (E ⟨i,hi⟩).val < (E ⟨i+1,hj⟩).val := E.strictMono (by simp)
    simpa only [g,dite_eq_left hi,dite_eq_left hj] using he
  · simpa only [g,dite_eq_left hi,dite_eq_right hj] using hb i hi

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSubsetTransfer
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transferring a small projection from an overlapping subset to its
reference set. Every denominator remains an actual covering number. -/
namespace Falconer
open scoped Pointwise

 theorem scalarCells_mono (δ : ℝ) {A B : Finset ℝ} (hAB : A ⊆ B) :
    scalarCells δ A ⊆ scalarCells δ B := Finset.image_subset_image hAB

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPorousLevels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual porous/nonporous partition. Collapsed levels have no
 geometric constraint and can be normalized to their coarser endpoint. -/
namespace Falconer.Regularization

 theorem scalar_effective_branching_level {B i : ℕ} {L : Finset (CellPath 1)}
    (k n : ℕ → ℕ) (h : ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i)) :
    ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (scalarEffectiveLevel B k n i) := by
  by_cases hz : k i = 0
  · simp only [scalarEffectiveLevel,ite_eq_left hz]
    refine ⟨h.exponent_le,le_rfl,Nat.mul_le_mul_left B (Nat.le_succ i),h.children_card,?_⟩
    intro p hp
    exact Or.inl hz
  · simpa only [scalarEffectiveLevel,ite_eq_right hz] using h

 theorem scalar_porous_margin {M B C : ℕ} (hCB : C ≤ B) (k n : ℕ → ℕ)
    {i : ℕ} (hi : i ∈ scalarPorousLevels M B C k n) :
    scalarEffectiveLevel B k n i+C ≤ B*(i+1) := by
  classical
  rcases (Finset.mem_filter.mp hi).2 with hz | hgap
  · simp only [scalarEffectiveLevel,ite_eq_left hz]
    nlinarith
  · by_cases hz : k i = 0
    · simp only [scalarEffectiveLevel,ite_eq_left hz]
      nlinarith
    · simpa only [scalarEffectiveLevel,ite_eq_right hz] using hgap.le

 theorem scalar_porous_nonporous_partition (M B C : ℕ) (k n : ℕ → ℕ) :
    scalarPorousLevels M B C k n = Finset.range M \ scalarNonporousLevels M B C k n := by
  classical
  ext i
  simp only [scalarPorousLevels,scalarNonporousLevels,Finset.mem_filter,Finset.mem_sdiff,
    Finset.mem_range]
  omega

 theorem scalar_porous_count (M B C : ℕ) (k n : ℕ → ℕ) :
    (scalarPorousLevels M B C k n).card+(scalarNonporousLevels M B C k n).card = M := by
  classical
  rw [scalar_porous_nonporous_partition]
  have hs : scalarNonporousLevels M B C k n ⊆ Finset.range M := Finset.filter_subset _ _
  simpa only [Finset.card_range] using Finset.card_sdiff_add_card_eq_card hs

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPorousEndpoints
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered endpoints selected from the actual porous levels, extended
 monotonically beyond the final endpoint without altering selected data. -/
namespace Falconer.Regularization

 theorem scalar_porous_endpoint_enumeration (M : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range M) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ e 0 = 0 ∧ e S.card ≤ M ∧
      (∀ j, 0 < j → j ≤ S.card → e j-1 ∈ S) ∧ (∀ i ∈ S, i < e S.card) := by
  classical
  let E := S.orderIsoOfFin rfl
  let g : ℕ → ℕ := fun i => if hi : i < S.card then (E ⟨i,hi⟩).val else M+(i-S.card)
  have hgmem : ∀ i < S.card, g i ∈ S := by
    intro i hi
    simpa only [g,dite_eq_left hi] using (E ⟨i,hi⟩).property
  have hgbound : ∀ i < S.card, g i < M := fun i hi => Finset.mem_range.mp (hS (hgmem i hi))
  have hg : StrictMono g := by
    intro i j hij
    by_cases hi : i < S.card
    · by_cases hj : j < S.card
      · have hh : (E ⟨i,hi⟩).val < (E ⟨j,hj⟩).val :=
          E.strictMono (show (⟨i,hi⟩ : Fin S.card) < ⟨j,hj⟩ from hij)
        simpa only [g,dite_eq_left hi,dite_eq_left hj] using hh
      · have hh := hgbound i hi
        simp only [g,dite_eq_left hi,dite_eq_right hj]
        change (E ⟨i,hi⟩).val < M+(j-S.card)
        have hh' : (E ⟨i,hi⟩).val < M := by simpa only [g,dite_eq_left hi] using hh
        omega
    · have hj : ¬j < S.card := by omega
      simp only [g,dite_eq_right hi,dite_eq_right hj]
      omega
  let e : ℕ → ℕ := fun j => if j = 0 then 0 else g (j-1)+1
  have he : StrictMono e := by
    intro i j hij
    by_cases hi : i = 0
    · simp only [e,ite_eq_left hi,ite_eq_right (show j ≠ 0 by omega)]
      omega
    · have hj : j ≠ 0 := by omega
      simp only [e,ite_eq_right hi,ite_eq_right hj]
      exact Nat.add_lt_add_right (hg (by omega : i-1 < j-1)) 1
  have hemem : ∀ j, 0 < j → j ≤ S.card → e j-1 ∈ S := by
    intro j hj hjS
    simp only [e,ite_eq_right (show j ≠ 0 by omega),Nat.add_sub_cancel]
    exact hgmem (j-1) (by omega)
  refine ⟨e,he,by simp [e],?_,hemem,?_⟩
  · by_cases hz : S.card = 0
    · simp [hz,e]
    · have hp := hgbound (S.card-1) (by omega)
      simp only [e,ite_eq_right hz]
      omega
  · intro i hi
    let j := (E.symm ⟨i,hi⟩).val
    have hj : j < S.card := (E.symm ⟨i,hi⟩).isLt
    have hgj : g j = i := by
      simp only [g,dite_eq_left hj,j]
      exact congrArg Subtype.val (E.apply_symm_apply ⟨i,hi⟩)
    have hle : g j ≤ g (S.card-1) := hg.monotone (by omega)
    have hz : S.card ≠ 0 := by omega
    simp only [e,ite_eq_right hz]
    omega

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarNonporousTail
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal run past the last selected porous endpoint consists
 entirely of the already-counted nonporous blocks. -/
namespace Falconer.Regularization

 theorem scalar_nonporous_tail_subset {M B C t : ℕ} (k n : ℕ → ℕ)
    (hend : ∀ i ∈ scalarPorousLevels M B C k n, i < t) :
    Finset.Ico t M ⊆ scalarNonporousLevels M B C k n := by
  classical
  intro i hi
  have hit := Finset.mem_Ico.mp hi
  by_contra hnot
  have hp : i ∈ scalarPorousLevels M B C k n := by
    rw [scalar_porous_nonporous_partition]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hit.2,hnot⟩
  have hh := hend i hp
  omega

 theorem scalar_nonporous_tail_length {M B C t : ℕ} (k n : ℕ → ℕ)
    (hend : ∀ i ∈ scalarPorousLevels M B C k n, i < t) :
    M-t ≤ (scalarNonporousLevels M B C k n).card := by
  have hh := Finset.card_le_card (scalar_nonporous_tail_subset k n hend)
  simpa only [Nat.card_Ico] using hh

 theorem scalar_nonporous_tail_weight {M B C t : ℕ} {L : Finset (CellPath 1)}
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i))
    (hend : ∀ i ∈ scalarPorousLevels M B C k n, i < t) :
    (∑ i ∈ Finset.Ico t M, k i) ≤ B*(scalarNonporousLevels M B C k n).card := by
  have hk : ∀ i ∈ Finset.Ico t M, k i ≤ B := by
    intro i hi
    have hh := (hlevel i (Finset.mem_Ico.mp hi).2).exponent_le
    rw [Nat.mul_add,Nat.mul_one] at hh
    omega
  calc
    _ ≤ ∑ _i ∈ Finset.Ico t M, B := Finset.sum_le_sum hk
    _ = B*(M-t) := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left B (scalar_nonporous_tail_length k n hend)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarNonporousEntropy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic form of the fixed-fold sumset bound, and the resulting
 quantitative supply of porous blocks for a set below full dimension. -/
namespace Falconer

 theorem scalar_porous_fraction {M bad B : ℕ} {κ cost size Jlog : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB : 0 < B)
    (hJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Jlog)
    (hcost : cost ≤ (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hsize : size ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hcount : (bad:ℝ)*Jlog ≤ cost+size) :
    (bad:ℝ) ≤ (1-κ/2)*(M:ℝ) := by
  let x : ℝ := (B:ℝ)*Real.log 2
  have hx : 0 < x := mul_pos (by exact_mod_cast hB) (Real.log_pos (by norm_num))
  have hc : 0 < (1-κ/4)*x := mul_pos (by linarith) hx
  have hlow := mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg bad)
  have hpre : (bad:ℝ)*((1-κ/4)*x) ≤ (1-3*κ/4)*(M:ℝ)*x := by
    dsimp [x] at *
    nlinarith
  have hcoef : (1-3*κ/4)*(M:ℝ) ≤ ((1-κ/2)*(M:ℝ))*(1-κ/4) := by
    have hs : 0 ≤ κ^2*(M:ℝ) := mul_nonneg (pow_nonneg hκ.le 2) (Nat.cast_nonneg M)
    nlinarith
  have hmain : (bad:ℝ)*((1-κ/4)*x) ≤ ((1-κ/2)*(M:ℝ))*((1-κ/4)*x) := by
    calc
      _ ≤ (1-3*κ/4)*(M:ℝ)*x := hpre
      _ ≤ (((1-κ/2)*(M:ℝ))*(1-κ/4))*x := mul_le_mul_of_nonneg_right hcoef hx.le
      _ = _ := by ring
  exact le_of_mul_le_mul_right hmain hc

namespace Regularization

 theorem scalar_porous_count_from_entropy {B M C : ℕ} (k n : ℕ → ℕ)
    {κ cost size Jlog : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB : 0 < B)
    (hJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Jlog)
    (hcost : cost ≤ (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hsize : size ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hcount : ((scalarNonporousLevels M B C k n).card:ℝ)*Jlog ≤ cost+size) :
    (κ/2)*(M:ℝ) ≤ ((scalarPorousLevels M B C k n).card:ℝ) := by
  have hh := scalar_porous_fraction hκ hκ1 hB hJ hcost hsize hcount
  have hc : ((scalarPorousLevels M B C k n).card:ℝ)+
      ((scalarNonporousLevels M B C k n).card:ℝ) = (M:ℝ) := by
    exact_mod_cast scalar_porous_count M B C k n
  nlinarith

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarTerminalProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A terminal fiber contributes its full cardinality to every sum
 projection. This is the base case for keeping whole terminal clusters. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_sum_cells_card_left {δ t : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hB : B.Nonempty)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|) :
    A.card ≤ (scalarCells δ (A+B.image (fun y => t*y))).card := by
  classical
  obtain ⟨y,hy⟩ := hB
  let D := A.image (fun x => x+t*y)
  have hDcard : D.card = A.card := Finset.card_image_of_injective _ (add_left_injective (t*y))
  have hDsep : ∀ x ∈ D, ∀ z ∈ D, x ≠ z → δ ≤ |x-z| := by
    intro x hx z hz hxz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have huv : u ≠ v := fun hh => hxz (by rw [hh])
    simpa only [add_sub_add_right_eq_sub] using hsep u hu v hv huv
  have hsub : D ⊆ A+B.image (fun z => t*z) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_add.mpr ⟨x,hx,t*y,Finset.mem_image_of_mem _ hy,rfl⟩
  have hc : (scalarCells δ D).card = D.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hDsep)
  rw [← hDcard,← hc]
  exact Finset.card_le_card (scalarCells_mono δ hsub)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClusterTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated cluster trees retain all leaves in each terminal fiber.
 Their common terminal cardinality multiplies every level of the gain. -/
namespace Falconer

 theorem ScalarClusterTree.child_nonempty {δ : ℝ} {N : ℕ} (T : ScalarClusterTree δ N)
    {n : ℕ} (hn : n < N) {x : ℝ} (hx : x ∈ T.nodes (n+1)) :
    (T.children n x).Nonempty := by
  rw [← Finset.card_pos,T.child_card n hn x hx]
  exact T.branch_pos n hn

 theorem ScalarClusterTree.points_card {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (T : ScalarClusterTree δ N) :
    ∀ n ≤ N, ∀ x ∈ T.nodes n,
      (T.points n x).card = T.leaf_size*(∏ j ∈ Finset.range n, T.branching j) := by
  classical
  intro n hn
  induction n with
  | zero => intro x hx; simpa using T.leaf_card x hx
  | succ n ih =>
    intro x hx
    have hnN : n < N := by omega
    have hr0 : 0 < T.radius n := hδ.trans_le (T.radius_ge n hnN)
    have hd : (T.children n x : Set ℝ).PairwiseDisjoint (T.points n) := by
      intro y hy z hz hyz
      apply Finset.disjoint_left.mpr
      intro a hay haz
      have h1 := T.child_bound n hnN x hx y hy a hay
      have h2 := T.child_bound n hnN x hx z hz a haz
      have hs := T.child_sep n hnN x hx y hy z hz hyz
      have ht : |y-z| ≤ |a-y|+|a-z| := by
        calc
          |y-z| ≤ |y-a|+|a-z| := abs_sub_le _ _ _
          _ = _ := by rw [abs_sub_comm y a]
      have hg := T.gap_gt n hnN
      linarith
    rw [T.parent_eq n hnN x hx,Finset.card_biUnion hd]
    calc
      _ = ∑ _y ∈ T.children n x, T.leaf_size*(∏ j ∈ Finset.range n, T.branching j) :=
        Finset.sum_congr rfl (fun y hy => ih (by omega) y (T.child_subset n hnN x hx hy))
      _ = _ := by simp [T.child_card n hnN x hx,Finset.prod_range_succ,Nat.mul_comm,Nat.mul_assoc]

 theorem ScalarClusterTree.points_nonempty {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (T : ScalarClusterTree δ N) {n : ℕ} (hn : n ≤ N) {x : ℝ} (hx : x ∈ T.nodes n) :
    (T.points n x).Nonempty := by
  apply Finset.card_pos.mp
  rw [T.points_card hδ n hn x hx]
  exact Nat.mul_pos T.leaf_pos (Finset.prod_pos (fun j hj =>
    T.branch_pos j (lt_of_lt_of_le (Finset.mem_range.mp hj) hn)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClusterGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Grouped porous gain with the full mass of terminal clusters. -/
namespace Falconer
open scoped Pointwise

 theorem ScalarClusterTree.grouped_projection_log_gain {δ K κ : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K) {N : ℕ} (T : ScalarClusterTree δ N)
    (hbound : ∀ n ≤ N, ∀ x ∈ T.nodes n, |x| ≤ 1)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ → ℕ) (hM : ∀ n < N, 83521 ≤ M n)
    (hbranch : ∀ n < N, 2*M n ≤ T.branching n)
    (hgap : ∀ n < N, 15*T.radius n < T.gap n)
    (hscale : ∀ n < N, δ ≤ 5*T.radius n/T.gap n)
    (hsmall : ∀ n < N, 16*(M n:ℝ)^4*K*(5*T.radius n/T.gap n)^κ ≤ 1/4) :
    ∀ n ≤ N, ∀ x ∈ T.nodes n, ∀ y ∈ T.nodes n,
      (∑ j ∈ Finset.range n, (Real.log (T.branching j : ℝ)+(1/2 : ℝ)*Real.log (M j : ℝ))) +
        Real.log (T.leaf_size:ℝ) ≤
        scalarAverage B (fun b => Real.log ((scalarCells δ
          (T.points n x+(T.points n y).image (fun z => b*z))).card : ℝ)) := by
  have hbnd (n : ℕ) (hn : n ≤ N) (x : ℝ) (hx : x ∈ T.nodes n) :
      0 ≤ x-(-1) ∧ x-(-1) ≤ 2 := by
    have hh := abs_le.mp (hbound n hn x hx)
    constructor <;> linarith
  intro n hn
  induction n with
  | zero =>
    intro x hx y hy
    simp only [Finset.range_zero,Finset.sum_empty,zero_add]
    have hleaf : 0 < (T.leaf_size:ℝ) := by exact_mod_cast T.leaf_pos
    have hbound (b : ℝ) : (T.leaf_size:ℝ) ≤ ((scalarCells δ
        (T.points 0 x+(T.points 0 y).image (fun z => b*z))).card:ℝ) := by
      rw [← T.leaf_card x hx]
      exact_mod_cast scalar_sum_cells_card_left hδ (T.points 0 x) (T.points 0 y)
        (T.points_nonempty hδ (by omega) hy) (T.leaf_sep x hx)
    have hh := scalarAverage_mono B (fun b _ => Real.log_le_log hleaf (hbound b))
    simpa only [scalarAverage_const B hB (Real.log (T.leaf_size:ℝ))] using hh
  | succ n ih =>
    intro x hx y hy
    have hnN : n < N := by omega
    have hxy : (T.children n x).card = (T.children n y).card := by
      rw [T.child_card n hnN x hx,T.child_card n hnN y hy]
    have hmx : 2*M n ≤ (T.children n x).card := by
      rw [T.child_card n hnN x hx]
      exact hbranch n hnN
    have hs1 : 5*T.radius n/T.gap n ≤ 1 :=
      (div_le_one (T.gap_pos n hnN)).2 (T.gap_gt n hnN).le
    have hs := scalar_porous_grouping_gain hδ (T.radius_ge n hnN) (T.gap_pos n hnN)
      (hgap n hnN) hK (hscale n hnN) hs1 B (T.children n x) (T.children n y)
      hB (T.child_nonempty hnN hx) (T.child_nonempty hnN hy) hBb
      (fun z hz => hbnd n (by omega) z (T.child_subset n hnN x hx hz))
      (fun z hz => hbnd n (by omega) z (T.child_subset n hnN y hy hz))
      (T.child_sep n hnN x hx) (T.child_sep n hnN y hy) hxy hball
      (M n) (hM n hnN) hmx (hsmall n hnN) (T.points n) (T.points n)
      (fun z hz => T.points_nonempty hδ (by omega) (T.child_subset n hnN x hx hz))
      (fun z hz => T.points_nonempty hδ (by omega) (T.child_subset n hnN y hy hz))
      (T.child_bound n hnN x hx) (T.child_bound n hnN y hy)
      (fun p hp => ih (by omega) p.1 (T.child_subset n hnN x hx (Finset.mem_product.mp hp).1)
        p.2 (T.child_subset n hnN y hy (Finset.mem_product.mp hp).2))
    rw [T.child_card n hnN x hx,← T.parent_eq n hnN x hx,← T.parent_eq n hnN y hy] at hs
    rw [Finset.sum_range_succ]
    linarith

 theorem ScalarClusterTree.grouped_projection_gain {δ K κ : ℝ} (hδ : 0 < δ)
    (hK : 0 ≤ K) {N : ℕ} (T : ScalarClusterTree δ N)
    (hbound : ∀ n ≤ N, ∀ x ∈ T.nodes n, |x| ≤ 1)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ b ∈ B, 1/3 ≤ b ∧ b ≤ 1)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 → scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (M : ℕ → ℕ) (hM : ∀ n < N, 83521 ≤ M n)
    (hbranch : ∀ n < N, 2*M n ≤ T.branching n)
    (hgap : ∀ n < N, 15*T.radius n < T.gap n)
    (hscale : ∀ n < N, δ ≤ 5*T.radius n/T.gap n)
    (hsmall : ∀ n < N, 16*(M n:ℝ)^4*K*(5*T.radius n/T.gap n)^κ ≤ 1/4)
    (x : ℝ) (hx : x ∈ T.nodes N) (y : ℝ) (hy : y ∈ T.nodes N) :
    ∃ b ∈ B, ((T.points N x).card : ℝ)*Real.exp ((1/2 : ℝ)*(∑ j ∈ Finset.range N, Real.log (M j : ℝ))) ≤
      ((scalarCells δ (T.points N x+(T.points N y).image (fun z => b*z))).card : ℝ) := by
  have hg := T.grouped_projection_log_gain hδ hK hbound B hB hBb hball M hM hbranch hgap hscale hsmall
    N le_rfl x hx y hy
  let q := fun b : ℝ => ((scalarCells δ
    (T.points N x+(T.points N y).image (fun z => b*z))).card : ℝ)
  have hq : ∀ b ∈ B, 0 < q b := fun b _ => scalar_sum_cells_pos _ _
    (T.points_nonempty hδ le_rfl hx) (T.points_nonempty hδ le_rfl hy)
  have hc : 0 < ((T.points N x).card : ℝ) := by exact_mod_cast (T.points_nonempty hδ le_rfl hx).card_pos
  have hleaf : 0 < (T.leaf_size:ℝ) := by exact_mod_cast T.leaf_pos
  have hprod : 0 < (∏ j ∈ Finset.range N, T.branching j:ℝ) := by
    exact Finset.prod_pos (fun j hj => by exact_mod_cast T.branch_pos j (Finset.mem_range.mp hj))
  have hlog : Real.log ((T.points N x).card : ℝ) =
      Real.log (T.leaf_size:ℝ)+∑ j ∈ Finset.range N, Real.log (T.branching j : ℝ) := by
    rw [T.points_card hδ N le_rfl x hx,Nat.cast_mul,Nat.cast_prod,Real.log_mul hleaf.ne' hprod.ne']
    congr 1
    exact Real.log_prod (fun j hj => by exact_mod_cast (T.branch_pos j (Finset.mem_range.mp hj)).ne')
  have he : Real.exp ((∑ j ∈ Finset.range N,
      (Real.log (T.branching j : ℝ)+(1/2 : ℝ)*Real.log (M j : ℝ)))+Real.log (T.leaf_size:ℝ)) =
      ((T.points N x).card : ℝ)*Real.exp ((1/2 : ℝ)*(∑ j ∈ Finset.range N, Real.log (M j : ℝ))) := by
    have hexp : (∑ j ∈ Finset.range N,
        (Real.log (T.branching j : ℝ)+(1/2 : ℝ)*Real.log (M j : ℝ)))+Real.log (T.leaf_size:ℝ) =
        Real.log ((T.points N x).card:ℝ)+(1/2:ℝ)*(∑ j ∈ Finset.range N, Real.log (M j:ℝ)) := by
      rw [hlog,Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    rw [hexp,Real.exp_add,Real.exp_log hc]
  have hmean : ((T.points N x).card : ℝ)*Real.exp ((1/2 : ℝ)*(∑ j ∈ Finset.range N, Real.log (M j : ℝ))) ≤
      scalarAverage B q := by
    rw [← he]
    exact (Real.exp_le_exp.mpr hg).trans (scalar_exp_average_log_le B hB q hq)
  apply Finset.exists_le_of_sum_le hB
  have hn : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hh := (le_div_iff₀ hn).1 hmean
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm,scalarAverage] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClusterBunching
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bunching preserves the whole terminal fiber, including its mass. -/
namespace Falconer.Regularization

 theorem scalar_cluster_bunch_pruning {N M T lo m : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain T lo bs) (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k n : ℕ → ℕ)
    (hd : Monotone d) (hdN : ∀ i ≤ M, d i ≤ N)
    (hleaf : ∀ p ∈ L.image (List.take (d M)), (prefixFiber L (d M) p).card = m)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (d i) (d (i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T = M) :
    ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
      L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        scalarCompressedBranch e k i)).sum)*Q.card ∧
      (∀ c ≤ d (e lo), Q.image (List.take c) = L.image (List.take c)) ∧
      (∀ p ∈ Q.image (List.take (d (e T))), (prefixFiber Q (d (e T)) p).card = m) ∧
      (∀ b ∈ bs, ScalarPathLevel Q (d (e b.start)) (d (e b.stop))
        (2^(∑ i ∈ Finset.Ico b.start b.cut, scalarCompressedBranch e k i))
        (4*(1/2:ℝ)^(n (e b.cut-1)))) := by
  classical
  have heT' : e T ≤ M := heT.le
  have hcard : ∀ i < T, ∀ p ∈ L.image (List.take (d (e i))),
      (prefixChildren L (d (e i)) (d (e (i+1))) p).card = 2^(scalarCompressedBranch e k i) :=
    fun i hi => (scalar_compressed_path_level hL d k n hd hdN hlevel e he heT' hi).card
  have hm : ∀ p ∈ L.image (List.take (d (e T))), (prefixFiber L (d (e T)) p).card = m := by
    simpa only [heT] using hleaf
  have hg : ∀ b ∈ bs, ∀ p ∈ L.image (List.take (d (e b.start))),
      ∀ u ∈ prefixChildren L (d (e b.start)) (d (e b.cut)) p,
      ∀ v ∈ prefixChildren L (d (e b.start)) (d (e b.cut)) p,
      u ≠ v → 6*(1/2:ℝ)^(n (e b.cut-1)) ≤ |scalarPathCenter u-scalarPathCenter v| := by
    intro b hb
    have hbound := hchain.mem_bounds b hb
    exact scalar_compressed_group_separated hL d k n hd hdN hlevel e he heT'
      b.start_lt_cut (b.cut_le_stop.trans hbound.2)
  obtain ⟨Q,hQL,hQne,hsize,hprefix,hfiber,hlevels⟩ := scalar_trim_bunch_chain hchain
    (fun j => d (e j)) (scalarCompressedBranch e k) (hd.comp he.monotone)
    (fun b => 6*(1/2:ℝ)^(n (e b.cut-1))) L m hL hne
    (by rw [heT]; exact hdN M le_rfl) hcard hm hg
  refine ⟨Q,hQL,hQne,hsize,hprefix,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [hfiber _ le_rfl q hq]
    exact hm _ (Finset.mem_image_of_mem _ (hQL hq))
  intro b hb
  apply (hlevels b hb).mono_gap
  have hpos : 0 < e b.cut := (Nat.zero_le (e b.start)).trans_lt (he b.start_lt_cut)
  have hbound := hchain.mem_bounds b hb
  have hecut : e b.cut ≤ M := (he.monotone (b.cut_le_stop.trans hbound.2)).trans heT'
  have hx := (hlevel (e b.cut-1) (by omega)).level_hi
  rw [Nat.sub_add_cancel hpos] at hx
  have hs : (1/2:ℝ)^(d (e b.cut)) ≤ (1/2:ℝ)^(n (e b.cut-1)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hx
  change 4*(1/2:ℝ)^(n (e b.cut-1)) ≤
    6*(1/2:ℝ)^(n (e b.cut-1))-2*(1/2:ℝ)^(d (e b.cut))
  linarith


end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarClusterProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Porous amplification retains every point of the terminal fibers. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_bunch_cluster_projection_gain {N top lo mass : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain top lo bs) (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (hne : Q.Nonempty) (d k : ℕ → ℕ)
    (hd : Monotone d) (hdtop : d top ≤ N) (hmass : 0 < mass)
    (hleaf : ∀ p ∈ Q.image (List.take (d top)), (prefixFiber Q (d top) p).card = mass)
    (n H M : ScalarBunch → ℕ)
    (hlevels : ∀ b ∈ bs, ScalarPathLevel Q (d b.start) (d b.stop)
      (2^(∑ i ∈ Finset.Ico b.start b.cut, k i)) (4*(1/2:ℝ)^(n b)))
    (hH : ∀ b ∈ bs, 2 ≤ H b)
    (hmargin : ∀ b ∈ bs, n b+H b ≤ d b.stop)
    {K κ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (B : Finset ℝ) (hB : B.Nonempty) (hBb : ∀ t ∈ B, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass B u t ≤ K*t^κ*(B.card : ℝ))
    (hM : ∀ b ∈ bs, 83521 ≤ M b)
    (hbranch : ∀ b ∈ bs, 2*M b ≤ 2^(∑ i ∈ Finset.Ico b.start b.cut, k i))
    (hsmall : ∀ b ∈ bs, 16*(M b:ℝ)^4*K*((5/4:ℝ)*(1/2:ℝ)^(H b))^κ ≤ 1/4) :
    ∃ t ∈ B,
      (mass:ℝ)*(2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, k i)).sum) : ℝ)*
        Real.exp ((1/2:ℝ)*(bs.map (fun b => Real.log (M b:ℝ))).sum) ≤
      ((scalarCells ((1/2:ℝ)^N) ((Q.image scalarPathCenter)+
        (Q.image scalarPathCenter).image (fun x => t*x))).card : ℝ) := by
  classical
  have hgeo (b : ScalarBunch) (hb : b ∈ bs) :
      15*(1/2:ℝ)^(d b.stop) < 4*(1/2:ℝ)^(n b) ∧
      (1/2:ℝ)^N ≤ 5*(1/2:ℝ)^(d b.stop)/(4*(1/2:ℝ)^(n b)) := by
    exact scalar_dyadic_gap_geometry
      (by have h1 := hH b hb; have h2 := hmargin b hb; omega)
      ((hd (hchain.mem_bounds b hb).2).trans hdtop)
  let T := scalarBunchClusterTree hchain Q hQ d k hd hdtop hmass
    (fun b => 4*(1/2:ℝ)^(n b)) hlevels (fun b hb => by
      have hr : 0 < (1/2:ℝ)^(d b.stop) := by positivity
      linarith [(hgeo b hb).1]) hleaf
  let m : ℕ → ℕ := fun i => (bs.map M).getD i 1
  have hbound : ∀ i ≤ bs.length, ∀ x ∈ T.nodes i, |x| ≤ 1 := by
    intro i _hi x hx
    change x ∈ (Q.image (List.take (d (scalarBunchBoundary lo bs i)))).image scalarPathCenter at hx
    obtain ⟨p,_hp,rfl⟩ := Finset.mem_image.mp hx
    have hh := scalarPathCenter_unit p
    exact abs_le.mpr ⟨by linarith,hh.2⟩
  have hm : ∀ i < bs.length, 83521 ≤ m i := by
    intro i hi
    dsimp [m]
    rw [scalarBunchValue_at M 1 hi]
    exact hM bs[i] (List.getElem_mem hi)
  have hbr : ∀ i < bs.length, 2*m i ≤ T.branching i := by
    intro i hi
    change 2*(bs.map M).getD i 1 ≤
      (bs.map (fun b => 2^(∑ j ∈ Finset.Ico b.start b.cut, k j))).getD i 1
    rw [scalarBunchValue_at _ _ hi,scalarBunchValue_at _ _ hi]
    exact hbranch bs[i] (List.getElem_mem hi)
  have hgap : ∀ i < bs.length, 15*T.radius i < T.gap i := by
    intro i hi
    change 15*(1/2:ℝ)^(d (scalarBunchBoundary lo bs i)) <
      (bs.map (fun b => 4*(1/2:ℝ)^(n b))).getD i 1
    rw [(hchain.boundary_edges i hi).1,scalarBunchValue_at _ _ hi]
    exact (hgeo bs[i] (List.getElem_mem hi)).1
  have hscale : ∀ i < bs.length, (1/2:ℝ)^N ≤ 5*T.radius i/T.gap i := by
    intro i hi
    change (1/2:ℝ)^N ≤ 5*(1/2:ℝ)^(d (scalarBunchBoundary lo bs i))/
      (bs.map (fun b => 4*(1/2:ℝ)^(n b))).getD i 1
    rw [(hchain.boundary_edges i hi).1,scalarBunchValue_at _ _ hi]
    exact (hgeo bs[i] (List.getElem_mem hi)).2
  have hsm : ∀ i < bs.length, 16*(m i:ℝ)^4*K*(5*T.radius i/T.gap i)^κ ≤ 1/4 := by
    intro i hi
    change 16*((bs.map M).getD i 1:ℝ)^4*K*
      (5*(1/2:ℝ)^(d (scalarBunchBoundary lo bs i))/
        (bs.map (fun b => 4*(1/2:ℝ)^(n b))).getD i 1)^κ ≤ 1/4
    rw [(hchain.boundary_edges i hi).1,scalarBunchValue_at _ _ hi,scalarBunchValue_at _ _ hi]
    exact scalar_dyadic_bunch_small (hmargin bs[i] (List.getElem_mem hi)) hK hκ
      (hsmall bs[i] (List.getElem_mem hi))
  obtain ⟨q,hq⟩ := hne
  let x := scalarPathCenter (q.take (d lo))
  have hx : x ∈ T.nodes bs.length := by
    change x ∈ (Q.image (List.take (d (scalarBunchBoundary lo bs bs.length)))).image scalarPathCenter
    rw [scalarBunchBoundary_length]
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hq)
  obtain ⟨t,ht,hgain⟩ := T.grouped_projection_gain (by positivity) hK hbound B hB hBb hball
    m hm hbr hgap hscale hsm x hx x hx
  have hcard : (T.points bs.length x).card =
      mass*2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, k i)).sum) := by
    rw [T.points_card (by positivity) bs.length le_rfl x hx]
    exact congrArg (fun j : ℕ => mass*j) (scalar_list_product_powers bs _)
  have hlog : (∑ i ∈ Finset.range bs.length, Real.log (m i:ℝ)) =
      (bs.map (fun b => Real.log (M b:ℝ))).sum := scalar_list_sum_logs bs M
  rw [hcard,hlog] at hgain
  have hsub : T.points bs.length x ⊆ Q.image scalarPathCenter :=
    scalar_prefix_points_subset Q _ x
  have hsub' := scalarCells_mono ((1/2:ℝ)^N)
    (Finset.add_subset_add hsub (Finset.image_subset_image (f := fun x => t*x) hsub))
  refine ⟨t,ht,?_⟩
  have hnat := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub')
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hgain.trans hnat


end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarClusterPorousGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy porous gain retaining all original points in the terminal fibers. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_cluster_porous_gain {N B0 C P M T mass : ℕ}
    (hC2 : 2 ≤ C) (hP : 18 ≤ P) (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (hN : B0*M ≤ N) (hmass : 0 < mass)
    (hleaf : ∀ p ∈ L.image (List.take (B0*M)), (prefixFiber L (B0*M) p).card = mass)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B0*i) (B0*(i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (heT : e T = M)
    (hporous : ∀ j, 0 < j → j ≤ T → n (e j-1)+C ≤ B0*e j)
    {K κ : ℝ} (hK : 0 < K) (hκ : 0 ≤ κ)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB0 : 800*(P:ℝ) ≤ κ*(B0:ℝ))
    (S : Finset ℝ) (hS : S.Nonempty) (hSb : ∀ t ∈ S, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass S u t ≤ K*t^κ*(S.card : ℝ)) :
    ∃ lo : ℕ, ∃ bs : List ScalarBunch, ScalarBunchChain T lo bs ∧
      (∀ b ∈ bs, ScalarBunchGood (fun i => (scalarCompressedBranch e k i:ℝ)) (2*(P:ℝ)) b) ∧
      (∑ i ∈ Finset.range lo, (scalarCompressedBranch e k i:ℝ)) ≤ 2*(P:ℝ)*(lo:ℝ) ∧
      ((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        (scalarCompressedBranch e k i:ℝ))).sum ≤ 2*(P:ℝ)*((T-lo:ℕ):ℝ)/100) ∧
      ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
        L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
          scalarCompressedBranch e k i)).sum)*Q.card ∧
        ∃ t ∈ S,
          (mass:ℝ)*(2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut,
            scalarCompressedBranch e k i)).sum):ℝ)*
            Real.exp ((1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) ≤
          ((scalarCells ((1/2:ℝ)^N) ((L.image scalarPathCenter)+
            (L.image scalarPathCenter).image (fun x => t*x))).card : ℝ) := by
  classical
  obtain ⟨lo,bs,hchain,hgoods,hprefix,hloss,_⟩ :=
    scalar_bunching_total_weights (fun i => (scalarCompressedBranch e k i:ℝ))
      (by positivity : 0 ≤ 2*(P:ℝ)) T
  have hd : Monotone (fun i : ℕ => B0*i) := fun _ _ hij => Nat.mul_le_mul_left B0 hij
  have hdN : ∀ i ≤ M, B0*i ≤ N := fun i hi => (Nat.mul_le_mul_left B0 hi).trans hN
  obtain ⟨Q,hQL,hQne,hsize,_,hleafQ,hQlevels⟩ := scalar_cluster_bunch_pruning hchain L hL hne
    (fun i => B0*i) k n hd hdN hleaf hlevel e he heT
  let w := scalarCompressedBranch e k
  let H := fun b : ScalarBunch => C+B0*(b.stop-b.cut)
  have hmargin : ∀ b ∈ bs, n (e b.cut-1)+H b ≤ B0*e b.stop := by
    intro b hb
    have hbc : b.cut ≤ T := b.cut_le_stop.trans (hchain.mem_bounds b hb).2
    exact scalar_bunch_margin e n he B0 C b
      (hporous b.cut (by have hh := b.start_lt_cut; omega) hbc)
  have hgroups : ∀ b ∈ bs, 2*scalarBunchGroup P b ≤
      2^(∑ i ∈ Finset.Ico b.start b.cut, w i) :=
    fun b hb => scalar_bunch_group_room w (by omega) b (hgoods b hb)
  have hsmall : ∀ b ∈ bs, 16*(scalarBunchGroup P b:ℝ)^4*K*
      ((5/4:ℝ)*(1/2:ℝ)^(H b))^κ ≤ 1/4 :=
    fun b hb => scalar_bunch_uniform_budget hK hC hB0 b (hgoods b hb)
  obtain ⟨t,ht,hgain⟩ := scalar_bunch_cluster_projection_gain hchain Q (hQL.trans hL) hQne
    (fun j => B0*e j) w (fun i j hij => Nat.mul_le_mul_left B0 (he.monotone hij))
    (by rw [heT]; exact hN) hmass hleafQ (fun b => n (e b.cut-1)) H (scalarBunchGroup P) hQlevels
    (fun b _ => by dsimp [H]; omega) hmargin hK.le hκ S hS hSb hball
    (fun b _ => scalar_bunch_group_large hP b) hgroups hsmall
  rw [hchain.group_log_sum] at hgain
  have hsub := Finset.image_subset_image (f := scalarPathCenter) hQL
  have hcover := scalarCells_mono ((1/2:ℝ)^N)
    (Finset.add_subset_add hsub (Finset.image_subset_image (f := fun x => t*x) hsub))
  refine ⟨lo,bs,hchain,hgoods,hprefix,hloss,Q,hQL,hQne,hsize,t,ht,?_⟩
  dsimp [w] at hgain
  have he : (1/2:ℝ)*((P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) =
      (1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2 := by ring
  rw [he] at hgain
  exact hgain.trans (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hcover))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarTerminalFiberMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact masses of terminal fibers before bunching. -/
namespace Falconer.Regularization

 theorem scalar_uniform_terminal_mass {N M t : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (d k : ℕ → ℕ) (hd : Monotone d) (hdM : d M = N)
    (hcard : ∀ i < M, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i))
    (ht : t ≤ M) : ∀ p ∈ L.image (List.take (d t)),
      (prefixFiber L (d t) p).card = 2^(∑ i ∈ Finset.Ico t M, k i) := by
  classical
  intro p hp
  have hc := scalar_grouped_children_card L d k hd M hcard ht le_rfl p hp
  rw [hdM] at hc
  have hi : (prefixFiber L (d t) p).image (List.take N) = prefixFiber L (d t) p := by
    calc
      _ = (prefixFiber L (d t) p).image id := Finset.image_congr (by
        intro q hq
        have hn := (mem_cubePaths 1 N q).mp (hL (Finset.mem_filter.mp hq).1)
        change q.take N = q
        rw [← hn,List.take_length])
      _ = _ := Finset.image_id
  change ((prefixFiber L (d t) p).image (List.take N)).card = _ at hc
  rwa [hi] at hc

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarActualClusterGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting the actual porous endpoints while retaining every point of
 every terminal fiber. Only the scalar parameter inequalities remain. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_actual_cluster_gain {B C P M : ℕ}
    (hC2 : 2 ≤ C) (hCB : C ≤ B) (hP : 18 ≤ P)
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i))
    {K κ : ℝ} (hK : 0 < K) (hκ : 0 ≤ κ)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (A : Finset ℝ) (hA : A.Nonempty) (hAb : ∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass A u t ≤ K*t^κ*(A.card : ℝ)) :
    let T := (scalarPorousLevels M B C k n).card
    ∃ e : ℕ → ℕ, StrictMono e ∧ e 0 = 0 ∧ e T ≤ M ∧
    ∃ lo : ℕ, ∃ bs : List ScalarBunch, ScalarBunchChain T lo bs ∧
      (∀ b ∈ bs, ScalarBunchGood (fun i => (scalarCompressedBranch e k i:ℝ)) (2*(P:ℝ)) b) ∧
      (∑ i ∈ Finset.range lo, (scalarCompressedBranch e k i:ℝ)) ≤ 2*(P:ℝ)*(lo:ℝ) ∧
      ((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        (scalarCompressedBranch e k i:ℝ))).sum ≤ 2*(P:ℝ)*((T-lo:ℕ):ℝ)/100) ∧
      (∑ i ∈ Finset.Ico (e T) M, k i) ≤ B*(scalarNonporousLevels M B C k n).card ∧
      ∃ Q : Finset (CellPath 1), Q ⊆ L ∧ Q.Nonempty ∧
        L.card = 2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
          scalarCompressedBranch e k i)).sum)*Q.card ∧
        ∃ t ∈ A,
          (2^(∑ i ∈ Finset.Ico (e T) M, k i):ℝ)*(2^((bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut,
            scalarCompressedBranch e k i)).sum):ℝ)*
            Real.exp ((1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) ≤
          ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
            (L.image scalarPathCenter).image (fun x => t*x))).card : ℝ) := by
  classical
  let S := scalarPorousLevels M B C k n
  let T := S.card
  obtain ⟨e,he,he0,heT,heMem,heMax⟩ :=
    scalar_porous_endpoint_enumeration M S (Finset.filter_subset _ _)
  let n' := scalarEffectiveLevel B k n
  have hn' : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n' i) :=
    fun i hi => scalar_effective_branching_level k n (hlevel i hi)
  have hd : Monotone (fun i : ℕ => B*i) := fun _ _ hij => Nat.mul_le_mul_left B hij
  have hmass : 0 < 2^(∑ i ∈ Finset.Ico (e T) M, k i) := by positivity
  have hleaf : ∀ p ∈ L.image (List.take (B*e T)),
      (prefixFiber L (B*e T) p).card = 2^(∑ i ∈ Finset.Ico (e T) M, k i) :=
    scalar_uniform_terminal_mass L hL (fun i => B*i) k hd rfl
      (fun i hi => (hlevel i hi).children_card) heT
  have hends : ∀ j, 0 < j → j ≤ T → n' (e j-1)+C ≤ B*e j := by
    intro j hj hjT
    have hmem := heMem j hj hjT
    have hh := scalar_porous_margin hCB k n hmem
    have hepos : 0 < e j := by rw [← he0]; exact he hj
    rwa [Nat.sub_add_cancel hepos] at hh
  obtain ⟨lo,bs,hchain,hgoods,hprefix,hloss,Q,hQL,hQne,hcostQ,t,ht,hgain⟩ :=
    scalar_cluster_porous_gain hC2 hP L hL hne
      (Nat.mul_le_mul_left B heT) hmass hleaf k n'
      (fun i hi => hn' i (hi.trans_le heT)) e he rfl hends
      hK hκ hC hB A hA hAb hball
  have hweight := scalar_nonporous_tail_weight k n hlevel heMax
  refine ⟨e,he,he0,heT,lo,bs,hchain,hgoods,hprefix,hloss,hweight,
    Q,hQL,hQne,hcostQ,t,ht,?_⟩
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hgain

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPrefixNonconcentration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonconcentration bounds the number of occupied scalar prefixes from
 below. This controls the ungrouped prefix left by the greedy ledger. -/
namespace Falconer.Regularization

 theorem scalar_prefix_ball_bound {N a : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (ha : a ≤ N) (p : CellPath 1) :
    ((prefixFiber L a p).card:ℝ) ≤
      scalarBallMass (L.image scalarPathCenter) (scalarPathCenter p) ((1/2:ℝ)^a) := by
  classical
  have hinj := scalarPathCenter_injOn (prefixFiber L a p) (fun q hq =>
    (mem_cubePaths 1 N q).mp (hL (Finset.mem_filter.mp hq).1))
  have hc := Finset.card_image_of_injOn hinj
  have hsub : (prefixFiber L a p).image scalarPathCenter ⊆
      (L.image scalarPathCenter).filter (fun x => |x-scalarPathCenter p| ≤ (1/2:ℝ)^a) := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hq).1,
      scalar_prefix_leaf_center_dist hL ha hq⟩
  have hb := Finset.card_le_card hsub
  rw [hc] at hb
  unfold scalarBallMass
  exact_mod_cast hb

 theorem scalar_prefix_nonconcentration {N a : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (ha : a ≤ N) {K κ : ℝ}
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K*t^κ*((L.image scalarPathCenter).card:ℝ)) :
    1 ≤ ((L.image (List.take a)).card:ℝ)*K*((1/2:ℝ)^a)^κ := by
  classical
  have hcard : (L.image scalarPathCenter).card = L.card :=
    Finset.card_image_of_injOn (scalarPathCenter_injOn L (fun q hq =>
      (mem_cubePaths 1 N q).mp (hL hq)))
  have hbound : ∀ p ∈ L.image (List.take a), ((prefixFiber L a p).card:ℝ) ≤
      K*((1/2:ℝ)^a)^κ*(L.card:ℝ) := by
    intro p hp
    have hb := hball (scalarPathCenter p) ((1/2:ℝ)^a)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) ha)
      (pow_le_one₀ (by norm_num) (by norm_num))
    rw [hcard] at hb
    exact (scalar_prefix_ball_bound L hL ha p).trans hb
  have hs : (L.card:ℝ) ≤ ((L.image (List.take a)).card:ℝ)*
      (K*((1/2:ℝ)^a)^κ*(L.card:ℝ)) := by
    calc
      _ = ∑ p ∈ L.image (List.take a), ((prefixFiber L a p).card:ℝ) := by
        exact_mod_cast prefixFiber_total_card L a
      _ ≤ ∑ _p ∈ L.image (List.take a), K*((1/2:ℝ)^a)^κ*(L.card:ℝ) :=
        Finset.sum_le_sum hbound
      _ = _ := by simp
  have hpos : 0 < (L.card:ℝ) := by exact_mod_cast hne.card_pos
  nlinarith

 theorem scalar_uniform_prefix_card {M : ℕ} (L : Finset (CellPath 1)) (hne : L.Nonempty)
    (d k : ℕ → ℕ) (hd : Monotone d) (hd0 : d 0 = 0)
    (hcard : ∀ i < M, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i))
    {j : ℕ} (hj : j ≤ M) :
    (L.image (List.take (d j))).card = 2^(∑ i ∈ Finset.range j, k i) := by
  classical
  obtain ⟨q,hq⟩ := hne
  have hp : ([] : CellPath 1) ∈ L.image (List.take (d 0)) := by
    rw [hd0]
    exact Finset.mem_image.mpr ⟨q,hq,rfl⟩
  have hh := scalar_grouped_children_card L d k hd M hcard (Nat.zero_le j) hj [] hp
  simpa only [hd0,prefixChildren,prefixFiber_zero,Nat.Ico_zero_eq_range] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPrefixEntropy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy accounting for the ungrouped prefix. The lower estimate comes
 directly from the original finite set's ball bound. -/
namespace Falconer

 theorem scalar_dyadic_prefix_entropy {a W : ℕ} {K κ : ℝ} (hK : 0 < K)
    (h : 1 ≤ (2:ℝ)^W*K*((1/2:ℝ)^a)^κ) :
    κ*(a:ℝ)*Real.log 2 ≤ Real.log K+(W:ℝ)*Real.log 2 := by
  have hh := Real.log_le_log (by norm_num : (0:ℝ) < 1) h
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [Real.log_one,Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hK.ne',Real.log_pow,
    Real.log_rpow (by positivity),Real.log_pow,hhalf] at hh
  nlinarith

 theorem scalar_stopped_prefix_length {a W lo B P : ℕ} {K κ : ℝ}
    (hK : 0 < K) (hκ : 0 ≤ κ)
    (hcount : 1 ≤ (2:ℝ)^W*K*((1/2:ℝ)^a)^κ)
    (ha : B*lo ≤ a) (hW : (W:ℝ) ≤ 2*(P:ℝ)*(lo:ℝ)) :
    (κ*(B:ℝ)-2*(P:ℝ))*(lo:ℝ)*Real.log 2 ≤ Real.log K := by
  have hh := scalar_dyadic_prefix_entropy hK hcount
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have haR : (B:ℝ)*(lo:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hlow := mul_le_mul_of_nonneg_left haR (mul_nonneg hκ hlog)
  have hupp := mul_le_mul_of_nonneg_right hW hlog
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarBranchAccounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact exponent accounting from original blocks through compressed
 blocks and the bunch ledger. -/
namespace Falconer

 theorem ScalarBunchChain.nat_weight_partition {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) (w : ℕ → ℕ) :
    (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum =
        ∑ i ∈ Finset.Ico lo top, w i := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have hp := Finset.sum_Ico_consecutive w h.start_le (b.start_lt_cut.le.trans b.cut_le_stop)
    have hb := Finset.sum_Ico_consecutive w b.start_lt_cut.le b.cut_le_stop
    simp only [List.map_cons,List.sum_cons]
    omega

 theorem ScalarBunchChain.total_weight {top lo : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) (w : ℕ → ℕ) :
    (∑ i ∈ Finset.range top, w i) = (∑ i ∈ Finset.range lo, w i)+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, w i)).sum+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, w i)).sum := by
  have hp := Finset.sum_Ico_consecutive w (Nat.zero_le lo) h.start_le
  have hh := h.nat_weight_partition w
  simp only [Nat.Ico_zero_eq_range] at hp
  omega

namespace Regularization

 theorem scalar_compressed_branch_sum (e k : ℕ → ℕ) (he : Monotone e)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ Finset.Ico a b, scalarCompressedBranch e k j) = ∑ i ∈ Finset.Ico (e a) (e b), k i := by
  induction b,hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab,ih]
    exact Finset.sum_Ico_consecutive k (he hab) (he (Nat.le_succ b))

 theorem scalar_uniform_total_card {N M : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k : ℕ → ℕ)
    (hd : Monotone d) (hd0 : d 0 = 0) (hdM : d M = N)
    (hcard : ∀ i < M, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i)) :
    L.card = 2^(∑ i ∈ Finset.range M, k i) := by
  have hh := scalar_uniform_prefix_card L hne d k hd hd0 hcard (le_refl M)
  rw [hdM] at hh
  have hi : L.image (List.take N) = L := by
    calc
      _ = L.image id := Finset.image_congr (by
        intro q hq
        have hn := (mem_cubePaths 1 N q).mp (hL hq)
        change q.take N = q
        rw [← hn,List.take_length])
      _ = _ := Finset.image_id
  rwa [hi] at hh

 theorem scalar_total_branch_decomposition {M T lo : ℕ} {bs : List ScalarBunch}
    (hchain : ScalarBunchChain T lo bs) (e k : ℕ → ℕ) (he : Monotone e)
    (he0 : e 0 = 0) (heT : e T ≤ M) :
    (∑ i ∈ Finset.range M, k i) = (∑ i ∈ Finset.Ico (e T) M, k i)+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, scalarCompressedBranch e k i)).sum+
      (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, scalarCompressedBranch e k i)).sum+
      (∑ i ∈ Finset.range lo, scalarCompressedBranch e k i) := by
  have hc := scalar_compressed_branch_sum e k he (Nat.zero_le T)
  simp only [he0,Nat.Ico_zero_eq_range] at hc
  have ht := hchain.total_weight (scalarCompressedBranch e k)
  have hp := Finset.sum_Ico_consecutive k (Nat.zero_le (e T)) heT
  simp only [Nat.Ico_zero_eq_range] at hp
  omega

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBunchedPrefix
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prefix left by the greedy ledger is short because every occupied
 prefix obeys the original scalar nonconcentration bound. -/
namespace Falconer.Regularization

 theorem scalar_bunched_prefix_length {B M T lo P : ℕ}
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (he0 : e 0 = 0) (heT : e T ≤ M) (hlo : lo ≤ T)
    (hprefix : (∑ i ∈ Finset.range lo, (scalarCompressedBranch e k i:ℝ)) ≤
      2*(P:ℝ)*(lo:ℝ))
    {K κ : ℝ} (hK : 0 < K) (hκ : 0 ≤ κ)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K*t^κ*((L.image scalarPathCenter).card:ℝ)) :
    (κ*(B:ℝ)-2*(P:ℝ))*(lo:ℝ)*Real.log 2 ≤ Real.log K := by
  have hd : Monotone (fun j : ℕ => B*e j) := fun _ _ hij => Nat.mul_le_mul_left B (he.monotone hij)
  have helo : e lo ≤ M := (he.monotone hlo).trans heT
  have hcard : ∀ i < T, ∀ p ∈ L.image (List.take (B*e i)),
      (prefixChildren L (B*e i) (B*e (i+1)) p).card = 2^(scalarCompressedBranch e k i) := by
    intro i hi p hp
    exact scalar_grouped_children_card L (fun j => B*j) k
      (fun _ _ hij => Nat.mul_le_mul_left B hij) M (fun j hj => (hlevel j hj).children_card)
      (he.monotone (Nat.le_succ i)) ((he.monotone (show i+1 ≤ T by omega)).trans heT) p hp
  have hc := scalar_prefix_nonconcentration L hL hne (Nat.mul_le_mul_left B helo) hball
  rw [scalar_uniform_prefix_card L hne (fun j => B*e j) (scalarCompressedBranch e k) hd
    (by rw [he0,Nat.mul_zero]) hcard hlo,Nat.cast_pow,Nat.cast_ofNat] at hc
  have hidx : lo ≤ e lo := by
    have hh := he.add_le_nat lo 0
    simpa only [he0,Nat.add_zero] using hh
  apply scalar_stopped_prefix_length hK hκ hc (Nat.mul_le_mul_left B hidx)
  simpa only [Nat.cast_sum] using hprefix

 theorem scalar_bunched_prefix_short {B P T lo : ℕ} {K κ : ℝ}
    (hP : 0 < P) (hbudget : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hprefix : (κ*(B:ℝ)-2*(P:ℝ))*(lo:ℝ)*Real.log 2 ≤ Real.log K)
    (hscale : 10*Real.log K ≤ (κ*(B:ℝ)-2*(P:ℝ))*(T:ℝ)*Real.log 2) :
    10*lo ≤ T := by
  have hPR : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP
  have hc : 0 < (κ*(B:ℝ)-2*(P:ℝ))*Real.log 2 :=
    mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hh : (10*(lo:ℝ))*((κ*(B:ℝ)-2*(P:ℝ))*Real.log 2) ≤
      (T:ℝ)*((κ*(B:ℝ)-2*(P:ℝ))*Real.log 2) := by nlinarith
  have hh' := le_of_mul_le_mul_right hh hc
  exact_mod_cast hh'

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarBunchNetGain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparing the porous projection gain with the exact discarded
 branching. This is the numerical endgame of the scalar dichotomy. -/
namespace Falconer

 theorem scalar_bunch_gain_log {R S W : ℕ} {E D : ℝ} (hD : 0 < D)
    (h : (2:ℝ)^R*Real.exp E ≤ D*(2:ℝ)^(R+S+W)) :
    E ≤ Real.log D+((S:ℝ)+(W:ℝ))*Real.log 2 := by
  have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^R*Real.exp E) h
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero E),Real.log_pow,Real.log_exp,
    Real.log_mul hD.ne' (by positivity),Real.log_pow] at hh
  simp only [Nat.cast_add] at hh
  nlinarith

 theorem scalar_bunch_net_gain {R S W P T lo : ℕ} {D : ℝ} (hD : 0 < D)
    (hlo : lo ≤ T) (hshort : 10*lo ≤ T)
    (hS : (S:ℝ) ≤ (P:ℝ)*((T-lo:ℕ):ℝ)/50)
    (hW : (W:ℝ) ≤ 2*(P:ℝ)*(lo:ℝ))
    (h : (2:ℝ)^R*Real.exp ((1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) ≤
      D*(2:ℝ)^(R+S+W)) :
    (1/5:ℝ)*(P:ℝ)*(T:ℝ)*Real.log 2 ≤ Real.log D := by
  have hlog := scalar_bunch_gain_log hD h
  have hbase : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hcovered : ((T-lo:ℕ):ℝ) = (T:ℝ)-(lo:ℝ) := Nat.cast_sub hlo
  have hloR : 10*(lo:ℝ) ≤ (T:ℝ) := by exact_mod_cast hshort
  have hbudget : (S:ℝ)+(W:ℝ) ≤
      (P:ℝ)*((T-lo:ℕ):ℝ)/50+2*(P:ℝ)*(lo:ℝ) := add_le_add hS hW
  have hb := mul_le_mul_of_nonneg_right hbudget hbase
  have hm := mul_le_mul_of_nonneg_left hloR (mul_nonneg (Nat.cast_nonneg P) hbase)
  rw [hcovered] at hlog hb
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarPorousGrowth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative porous scalar growth after all original-path losses have
 been accounted for. The terminal fibers retain their entire mass. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_porous_log_growth {B C P M : ℕ}
    (hC2 : 2 ≤ C) (hCB : C ≤ B) (hP : 18 ≤ P)
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i))
    {K K0 κ D : ℝ} (hK : 0 < K) (hK0 : 0 < K0) (hκ : 0 < κ) (hD : 0 < D)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hporous : (κ/2)*(M:ℝ) ≤ ((scalarPorousLevels M B C k n).card:ℝ))
    (hscale : 20*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2)
    (hpoint : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K0*t^κ*((L.image scalarPathCenter).card:ℝ))
    (A : Finset ℝ) (hA : A.Nonempty) (hAb : ∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass A u t ≤ K*t^κ*(A.card : ℝ))
    (hproj : ∀ t ∈ A, ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
      (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ) ≤ D*(L.card:ℝ)) :
    (κ/10)*(P:ℝ)*(M:ℝ)*Real.log 2 ≤ Real.log D := by
  classical
  let T := (scalarPorousLevels M B C k n).card
  obtain ⟨e,he,he0,heT,lo,bs,hchain,_,hprefix,hloss,_,Q,_,_,_,t,ht,hgain⟩ :=
    scalar_actual_cluster_gain hC2 hCB hP L hL hne k n hlevel hK hκ.le hC hB A hA hAb hball
  have hpre := scalar_bunched_prefix_length L hL hne k n hlevel e he he0 heT
    hchain.start_le hprefix hK0 hκ.le hpoint
  have hPR : (0:ℝ) < (P:ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hco : 0 < κ*(B:ℝ)-2*(P:ℝ) := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTscale : 10*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*(T:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hporous (mul_nonneg hco.le hlog2.le)
    change (κ/2)*(M:ℝ) ≤ (T:ℝ) at hporous
    nlinarith
  have hshort : 10*lo ≤ T := scalar_bunched_prefix_short (by omega) hB hpre hTscale
  let r := (∑ i ∈ Finset.Ico (e T) M, k i)+
    (bs.map (fun b => ∑ i ∈ Finset.Ico b.start b.cut, scalarCompressedBranch e k i)).sum
  let s := (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop, scalarCompressedBranch e k i)).sum
  let w := ∑ i ∈ Finset.range lo, scalarCompressedBranch e k i
  have hs : (s:ℝ) ≤ (P:ℝ)*((T-lo:ℕ):ℝ)/50 := by
    have hc : (s:ℝ) = (bs.map (fun b => ∑ i ∈ Finset.Ico b.cut b.stop,
        (scalarCompressedBranch e k i:ℝ))).sum := by
      simp only [s,Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_sum]
    rw [hc]
    linarith
  have hw : (w:ℝ) ≤ 2*(P:ℝ)*(lo:ℝ) := by
    simpa only [w,Nat.cast_sum] using hprefix
  have htotal := scalar_uniform_total_card L hL hne (fun i => B*i) k
    (fun _ _ hij => Nat.mul_le_mul_left B hij) (by simp) rfl
    (fun i hi => (hlevel i hi).children_card)
  have hsplit := scalar_total_branch_decomposition hchain e k he.monotone he0 heT
  have hsize : L.card = 2^(r+s+w) := by
    rw [htotal,hsplit]
  rw [← pow_add] at hgain
  change (2:ℝ)^r*Real.exp ((1/2:ℝ)*(P:ℝ)*((T-lo:ℕ):ℝ)*Real.log 2) ≤ _ at hgain
  have hu := hproj t ht
  rw [hsize,Nat.cast_pow,Nat.cast_ofNat] at hu
  have hnet := scalar_bunch_net_gain hD hchain.start_le hshort hs hw (hgain.trans hu)
  have hh := mul_le_mul_of_nonneg_left hporous (show 0 ≤ (P:ℝ)*Real.log 2/5 by positivity)
  nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarBinaryParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit fixed-fold parameters for the nonporous binary construction.
 Their logarithmic branching approaches the original block width. -/
namespace Falconer

theorem scalar_binary_parameter_contract {B C : ℕ} (hC : 7 ≤ C) (hBC : 2*C ≤ B) :
    (1/2:ℝ)^B*(1+2*(scalarBinaryBranchCount B C:ℝ)*(18*(2:ℝ)^C)) ≤ 1 := by
  have hcancel (n : ℕ) : (1/2:ℝ)^n*(2:ℝ)^n = 1 := by rw [← mul_pow]; norm_num
  have hsplit : (1/2:ℝ)^B = (1/2:ℝ)^(B-2*C)*(1/2:ℝ)^C*(1/2:ℝ)^C := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  have hprod : (1/2:ℝ)^B*(2:ℝ)^(B-2*C)*(2:ℝ)^C = (1/2:ℝ)^C := by
    calc
      _ = ((1/2:ℝ)^(B-2*C)*(2:ℝ)^(B-2*C))*
          ((1/2:ℝ)^C*(2:ℝ)^C)*(1/2:ℝ)^C := by rw [hsplit]; ring
      _ = _ := by rw [hcancel,hcancel]; ring
  have hbnd : (1/2:ℝ)^B ≤ 1/2 := by
    have hh : (1/2:ℝ)^B ≤ (1/2:ℝ)^1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (show 1 ≤ B by omega)
    simpa only [pow_one] using hh
  have hcbnd : (1/2:ℝ)^C ≤ 1/128 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) hC
    norm_num at hh
    exact hh
  simp only [scalarBinaryBranchCount,Nat.cast_pow,Nat.cast_ofNat]
  have he : (1/2:ℝ)^B*(1+2*(2:ℝ)^(B-2*C)*(18*(2:ℝ)^C)) =
      (1/2:ℝ)^B+36*(1/2:ℝ)^C := by nlinarith [hprod]
  rw [he]
  linarith

theorem scalar_binary_parameter_copy_bound (B C : ℕ) :
    4*(scalarBinaryBranchCount B C:ℝ)*(18*(2:ℝ)^C) =
      (scalarBinaryCopyBound B C:ℝ) := by
  simp only [scalarBinaryCopyBound,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  ring

theorem scalar_binary_parameter_log {B C : ℕ} {κ : ℝ} (hBC : 2*C ≤ B)
    (hmargin : 8*(C:ℝ) ≤ κ*(B:ℝ)) :
    (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Real.log (scalarBinaryBranchCount B C+1:ℝ) := by
  have hp : 0 < (2:ℝ)^(B-2*C) := by positivity
  have hh := Real.log_le_log hp (show (2:ℝ)^(B-2*C) ≤ (2:ℝ)^(B-2*C)+1 by linarith)
  rw [Real.log_pow] at hh
  have hcast : ((B-2*C:ℕ):ℝ) = (B:ℝ)-2*(C:ℝ) := by
    rw [Nat.cast_sub hBC,Nat.cast_mul,Nat.cast_ofNat]
  rw [hcast] at hh
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hmargin hlog.le
  simp only [scalarBinaryBranchCount,Nat.cast_pow,Nat.cast_ofNat]
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockRegularization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All-dimensional block regularization

The upward labels preserve complete child groups at every selected depth.
Count bins cost d*N+1 possibilities and leaf mass bins cost (d+2)*N+1.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem blockDepth_antitone (N B : ℕ) : Antitone (blockDepth N B) := by
  intro i j hij
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right B hij) N

theorem blockDepth_gap (N B i : ℕ) : blockDepth N B i - blockDepth N B (i+1) ≤ B := by
  dsimp only [blockDepth]
  rw [Nat.add_mul, one_mul]
  omega

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarInitialRegularization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial scalar tree regularization with actual separated child cells,
 exact dyadic branching, and a quadratic loss per block. -/
namespace Falconer.Regularization

 theorem scalar_initial_regularization {N : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (B : ℕ) :
    ∃ Q : Finset (CellPath 1), ∃ k n : ℕ → ℕ,
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ (2050*(B+1)^2)^(N/B+1)*Q.card ∧
      ∀ i < N/B+1, ScalarBranchingLevel Q (blockDepth N B (i+1)) (blockDepth N B i) (k i) (n i) := by
  classical
  let D := 2050*(B+1)^2
  have hbuild : ∀ i ≤ N/B+1, ∃ Q : Finset (CellPath 1), ∃ m : ℕ, ∃ k n : ℕ → ℕ,
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ D^i*Q.card ∧
      (∀ p ∈ Q.image (List.take (blockDepth N B i)),
        (prefixFiber Q (blockDepth N B i) p).card = m) ∧
      ∀ j < i, ScalarBranchingLevel Q (blockDepth N B (j+1)) (blockDepth N B j) (k j) (n j) := by
    intro i hi
    induction i with
    | zero =>
      refine ⟨L,1,fun _ => 0,fun _ => 0,hne,Finset.Subset.refl _,by simp,?_,by simp⟩
      intro p hp
      simp only [blockDepth,Nat.zero_mul,Nat.sub_zero] at hp ⊢
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      have hlen := (mem_cubePaths 1 N q).mp (hL hq)
      have he : q.take N = q := by rw [← hlen,List.take_length]
      change (prefixFiber L N (q.take N)).card = 1
      rw [he,prefixFiber_leaf hL hq]
      simp
    | succ i ih =>
      obtain ⟨Q,m,k,n,hQne,hQL,hsize,hm,hlevels⟩ := ih (by omega)
      have hab := blockDepth_antitone N B (Nat.le_succ i)
      have hb : blockDepth N B i ≤ N := Nat.sub_le _ _
      obtain ⟨K,k0,n0,hRne,hRQ,hQR,hlevel,hm'⟩ :=
        scalar_block_pruning_level Q (hQL.trans hL) hQne hab hb m hm
      let R := scalarPruneLeaves Q (blockDepth N B (i+1)) (blockDepth N B i) K
      have hloc : 2050*(blockDepth N B i-blockDepth N B (i+1)+1)^2 ≤ D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (blockDepth_gap N B i) 1) 2)
      refine ⟨R,2^k0*m,Function.update k i k0,Function.update n i n0,hRne,hRQ.trans hQL,?_,hm',?_⟩
      · calc
          L.card ≤ D^i*Q.card := hsize
          _ ≤ D^i*((2050*(blockDepth N B i-blockDepth N B (i+1)+1)^2)*R.card) :=
            Nat.mul_le_mul_left _ hQR
          _ ≤ D^i*(D*R.card) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hloc)
          _ = D^(i+1)*R.card := by rw [pow_succ]; ring
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self] using hlevel
        · have hji' : j < i := by omega
          have hdepth : blockDepth N B i ≤ blockDepth N B (j+1) :=
            blockDepth_antitone N B (by omega)
          have hh := (hlevels j hji').prune hab hdepth K
          simpa only [Function.update_of_ne hji] using hh
  obtain ⟨Q,_,k,n,hQne,hQL,hcard,_,hlevels⟩ := hbuild (N/B+1) le_rfl
  exact ⟨Q,k,n,hQne,hQL,hcard,hlevels⟩

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarForwardRegularization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial scalar regularization in increasing geometric depth.
 Exact full blocks are the form used in the porous/nonporous dichotomy. -/
namespace Falconer.Regularization

 theorem blockDepth_product (B M i : ℕ) (hi : i ≤ M) :
    blockDepth (B*M) B (M-i) = B*i := by
  unfold blockDepth
  rw [Nat.mul_comm (M-i) B,← Nat.mul_sub_left_distrib,Nat.sub_sub_self hi]

 theorem scalar_forward_regularization {B M : ℕ} (hB : 0 < B)
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty) :
    ∃ Q : Finset (CellPath 1), ∃ k n : ℕ → ℕ,
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ (2050*(B+1)^2)^(M+1)*Q.card ∧
      ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (k i) (n i) := by
  obtain ⟨Q,k,n,hQne,hQL,hsize,hlevels⟩ := scalar_initial_regularization L hL hne B
  have hdiv : B*M/B = M := by rw [Nat.mul_comm B M,Nat.mul_div_cancel _ hB]
  rw [hdiv] at hsize hlevels
  refine ⟨Q,fun i => k (M-i-1),fun i => n (M-i-1),hQne,hQL,hsize,?_⟩
  intro i hi
  have hj : M-i-1 < M+1 := by omega
  have hh := hlevels (M-i-1) hj
  have hleft : blockDepth (B*M) B (M-i-1+1) = B*i := by
    rw [show M-i-1+1 = M-i by omega]
    exact blockDepth_product B M i (by omega)
  have hright : blockDepth (B*M) B (M-i-1) = B*(i+1) := by
    rw [show M-i-1 = M-(i+1) by omega]
    exact blockDepth_product B M (i+1) (by omega)
  rwa [hleft,hright] at hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRegularizationBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A square parameter absorbs the logarithmic loss of the initial
 scalar regularization. -/
namespace Falconer

 theorem scalar_square_dominates_linear {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∃ n : ℕ, 5 ≤ n ∧ β+4*(n:ℝ) ≤ α*(n:ℝ)^2 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 5 ((β+4)/α))
  have hn5 : (5:ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn1 : (1:ℝ) ≤ n := by linarith
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hmul : β+4 ≤ α*(n:ℝ) := by
    simpa only [mul_comm] using
      (le_of_lt ((div_lt_iff₀ hα).1 ((le_max_right _ _).trans_lt hn)))
  have hm := mul_le_mul_of_nonneg_right hmul hn0
  have hb := mul_le_mul_of_nonneg_left hn1 hβ
  refine ⟨n,by exact_mod_cast (show (5:ℝ) ≤ n by linarith),?_⟩
  nlinarith

 theorem scalar_regularization_log_bound (D n : ℕ) (hn : 1 ≤ n) :
    Real.log (2050*((D^2*n^2)+1)^2:ℝ) ≤
      Real.log 2050+2*Real.log ((D:ℝ)^2+1)+4*(n:ℝ) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have hp : (D:ℝ)^2*(n:ℝ)^2+1 ≤ ((D:ℝ)^2+1)*(n:ℝ)^2 := by nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ) < (D:ℝ)^2*(n:ℝ)^2+1) hp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hl
  have hnlog := Real.log_le_sub_one_of_pos hn0
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  norm_num only [Nat.cast_ofNat] at hl ⊢
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarParameterChoice
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing the fixed scalar block parameters. The resulting projection
 gain dominates the loss of the initial dyadic regularization. -/
namespace Falconer

 theorem scalar_block_parameters {κ : ℝ} (hκ : 0 < κ) (K : ℝ) :
    ∃ P B C : ℕ, 18 ≤ P ∧ 7 ≤ C ∧ 2*C ≤ B ∧
      800*(P:ℝ) ≤ κ*(B:ℝ) ∧ 8*(C:ℝ) ≤ κ*(B:ℝ) ∧
      Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
        κ*(C:ℝ)*Real.log 2 ∧
      Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200 := by
  let l := Real.log 2
  have hl : 0 < l := Real.log_pos (by norm_num)
  let A := Real.log (64*K)+κ*Real.log (5/4:ℝ)
  obtain ⟨D,hD⟩ := exists_nat_gt (max 7 ((|A|+4001*l)/(κ*l)))
  have hD7 : 7 ≤ D := by
    exact_mod_cast (show (7:ℝ) ≤ D from le_of_lt ((le_max_left _ _).trans_lt hD))
  have hDscalar : |A|+4001*l ≤ κ*(D:ℝ)*l := by
    have hh := (div_lt_iff₀ (mul_pos hκ hl)).1 ((le_max_right _ _).trans_lt hD)
    nlinarith
  have hkD : 4001 ≤ κ*(D:ℝ) := by nlinarith [abs_nonneg A]
  let β := Real.log 2050+2*Real.log ((D:ℝ)^2+1)
  have hβ : 0 ≤ β := add_nonneg (Real.log_nonneg (by norm_num))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg (D:ℝ)])))
  obtain ⟨n,hn5,hn⟩ := scalar_square_dominates_linear
    (show 0 < κ*l/200 by positivity) hβ
  let P := n^2
  let C := D*P
  let B := D^2*P
  have hP18 : 18 ≤ P := by dsimp [P]; nlinarith
  have hP1 : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast (show 1 ≤ P by omega)
  have hP0 : (0:ℝ) ≤ (P:ℝ) := Nat.cast_nonneg _
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
  have hC7 : 7 ≤ C := by
    have hh := Nat.mul_le_mul_left D (show 1 ≤ P by omega)
    dsimp [C]
    omega
  have h2CB : 2*C ≤ B := by
    have hh : 2*D ≤ D^2 := by nlinarith
    have hm := Nat.mul_le_mul_right P hh
    dsimp [C,B]
    nlinarith
  refine ⟨P,B,C,hP18,hC7,h2CB,?_,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hkD (Nat.cast_nonneg D)
    have hd2 : 800 ≤ κ*(D:ℝ)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hd2 hP0
    dsimp [B]
    push_cast
    nlinarith
  · have hh : 8 ≤ κ*(D:ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_right hh (mul_nonneg (Nat.cast_nonneg D) hP0)
    dsimp [C,B]
    push_cast
    nlinarith
  · have hm := mul_le_mul_of_nonneg_right hDscalar hP0
    have ha := mul_le_mul_of_nonneg_left hP1 (abs_nonneg A)
    dsimp [C]
    push_cast
    change A+4000*(P:ℝ)*l ≤ κ*((D:ℝ)*(P:ℝ))*l
    nlinarith [le_abs_self A]
  · have hr := scalar_regularization_log_bound D n (by omega)
    dsimp [B,P]
    push_cast
    change Real.log (2050*((D:ℝ)^2*(n:ℝ)^2+1)^2) ≤ κ*(n:ℝ)^2*l/200
    calc
      _ ≤ Real.log 2050+2*Real.log ((D:ℝ)^2+1)+4*(n:ℝ) := hr
      _ ≤ (κ*l/200)*(n:ℝ)^2 := hn
      _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed block parameters absorb the initial regularization loss
 both in the final projection cardinality and in prefix nonconcentration. -/
namespace Falconer

 theorem scalar_regularization_loss {B P M : ℕ} {κ : ℝ} (hM : 0 < M) (hκ : 0 ≤ κ)
    (hR : Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200) :
    Real.log (((2050*(B+1)^2:ℝ)^(M+1))) ≤ κ*(P:ℝ)*(M:ℝ)*Real.log 2/100 := by
  rw [Real.log_pow]
  have hm : (M:ℝ)+1 ≤ 2*(M:ℝ) := by exact_mod_cast (show M+1 ≤ 2*M by omega)
  have ha : 0 ≤ κ*(P:ℝ)*Real.log 2/200 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (M+1))
  have h2 := mul_le_mul_of_nonneg_right hm ha
  push_cast at h1 ⊢
  nlinarith

 theorem scalar_regularization_scale_budget {B P M : ℕ} {κ K : ℝ}
    (hM : 0 < M) (hκ : 0 < κ) (hK : 0 < K)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hR : Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200)
    (hscale : 40*Real.log K ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2) :
    20*Real.log (K*(2050*(B+1)^2:ℝ)^(M+1)) ≤
      (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2 := by
  have hloss := scalar_regularization_loss hM hκ.le hR
  have hc : (P:ℝ)/5 ≤ (κ*(B:ℝ)-2*(P:ℝ))/2 := by
    have hp : 0 ≤ (P:ℝ) := Nat.cast_nonneg _
    linarith
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ κ*(M:ℝ)*Real.log 2 by positivity)
  rw [Real.log_mul hK.ne' (by positivity)]
  nlinarith

 theorem scalar_regularization_gain {B P M : ℕ} {κ : ℝ} (hM : 0 < M) (hκ : 0 ≤ κ)
    (hR : Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200) :
    Real.exp ((κ/25)*(P:ℝ)*(M:ℝ)*Real.log 2)*(2050*(B+1)^2:ℝ)^(M+1) ≤
      Real.exp ((κ/20)*(P:ℝ)*(M:ℝ)*Real.log 2) := by
  have hloss := scalar_regularization_loss hM hκ hR
  have hp : 0 < (2050*(B+1)^2:ℝ)^(M+1) := by positivity
  rw [← Real.exp_log hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarNonporousCover
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The binary alternative compared directly with a covering bound for the
 original repeated sumset. This avoids multiplying a regularization loss
 by the number of summands in a Pluennecke estimate. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_nsmul_subset (n : ℕ) {A B : Finset ℝ} (h : A ⊆ B) : n • A ⊆ n • B := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [succ_nsmul] using Finset.add_subset_add ih h

namespace Regularization

 theorem scalar_nonporous_cover_bound {B M copies J F C : ℕ} {U : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (k i) (n i))
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hF : 4*(J:ℝ)*U ≤ (F:ℝ)) (hcopies : (2*F+1)*J ≤ copies)
    (A : Finset ℝ) (hQA : Q.image scalarPathCenter ⊆ A) :
    (J+1)^(scalarNonporousLevels M B C k n).card ≤
      (scalarCells ((1/2:ℝ)^(B*M)) (copies • A)).card := by
  let S := scalarNonporousLevels M B C k n
  obtain ⟨g,hm,hg,hb⟩ := scalar_level_enumeration M S (Finset.filter_subset _ _)
  obtain ⟨E,hE,hcard,hsep⟩ := scalar_nonporous_growth Q hQ hne k n hlevel S.card g hg hb
    (fun i hi => (Finset.mem_filter.mp (hm i hi)).2.1)
    (fun i hi => (Finset.mem_filter.mp (hm i hi)).2.2) hU hJ hcontract hF hcopies
  rw [← hcard,← Finset.card_image_of_injOn (scalarCells_injective (by positivity) hsep)]
  exact Finset.card_le_card (Finset.image_subset_image (hE.trans (scalar_nsmul_subset copies hQA)))

 theorem scalar_porous_count_of_sumset {B M copies J F C : ℕ} {U κ : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (k i) (n i))
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hF : 4*(J:ℝ)*U ≤ (F:ℝ)) (hcopies : (2*F+1)*J ≤ copies)
    (A : Finset ℝ) (hQA : Q.image scalarPathCenter ⊆ A)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB : 0 < B)
    (hlogJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Real.log (J+1:ℝ))
    (hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M)) (copies • A)).card:ℝ) ≤
      (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2) :
    (κ/2)*(M:ℝ) ≤ ((scalarPorousLevels M B C k n).card:ℝ) := by
  have hraw := scalar_nonporous_cover_bound Q hQ hne k n hlevel hU hJ hcontract hF hcopies A hQA
  have hrawR : (J+1:ℝ)^(scalarNonporousLevels M B C k n).card ≤
      ((scalarCells ((1/2:ℝ)^(B*M)) (copies • A)).card:ℝ) := by exact_mod_cast hraw
  have hl := Real.log_le_log (by positivity : (0:ℝ) < (J+1:ℝ)^
    (scalarNonporousLevels M B C k n).card) hrawR
  rw [Real.log_pow] at hl
  apply scalar_porous_count_from_entropy k n hκ hκ1 hB hlogJ
    (le_refl ((κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2))
    (le_refl ((1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2))
  calc
    _ ≤ (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := hl.trans hsmall
    _ = _ := by ring

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarGrowthOfCover
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection growth from a bound on the original repeated sumset.
 The regularized subset incurs no repeated Pluennecke loss. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_projection_growth_of_sumset {B C P M copies J F : ℕ} {U K K0 κ : ℝ}
    (hC2 : 2 ≤ C) (hCB : C ≤ B) (hP : 18 ≤ P) (hM : 0 < M) (hBpos : 0 < B)
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (k i) (n i))
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hF : 4*(J:ℝ)*U ≤ (F:ℝ)) (hcopies : (2*F+1)*J ≤ copies)
    (X : Finset ℝ) (hQX : Q.image scalarPathCenter ⊆ X)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hlogJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Real.log (J+1:ℝ))
    (hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M)) (copies • X)).card:ℝ) ≤
      (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hK : 0 < K) (hK0 : 0 < K0)
    (hC : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hscale : 20*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2)
    (hpoint : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass (Q.image scalarPathCenter) u t ≤
        K0*t^κ*((Q.image scalarPathCenter).card:ℝ))
    (A : Finset ℝ) (hA : A.Nonempty) (hAb : ∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass A u t ≤ K*t^κ*(A.card : ℝ)) :
    ∃ t ∈ A, Real.exp ((κ/20)*(P:ℝ)*(M:ℝ)*Real.log 2)*(Q.card:ℝ) <
      ((scalarCells ((1/2:ℝ)^(B*M)) ((Q.image scalarPathCenter)+
        (Q.image scalarPathCenter).image (fun x => t*x))).card:ℝ) := by
  have hporous := scalar_porous_count_of_sumset Q hQ hne k n hlevel hU hJ
    hcontract hF hcopies X hQX hκ hκ1 hBpos hlogJ hsmall
  by_contra hn
  push Not at hn
  have hg := scalar_porous_log_growth hC2 hCB hP Q hQ hne k n hlevel hK hK0 hκ
    (Real.exp_pos _) hC hB hporous hscale hpoint A hA hAb hball hn
  rw [Real.log_exp] at hg
  have hp : (0:ℝ) < (P:ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hm : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hpos : 0 < κ*(P:ℝ)*(M:ℝ)*Real.log 2 :=
    mul_pos (mul_pos (mul_pos hκ hp) hm) (Real.log_pos (by norm_num))
  nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarSubsetMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative ball bounds and projection covers under the actual scalar
 pruning. The sole cost is the ratio of the numbers of retained leaves. -/
namespace Falconer
open scoped Pointwise

 theorem scalarBallMass_mono {A B : Finset ℝ} (h : A ⊆ B) (u r : ℝ) :
    scalarBallMass A u r ≤ scalarBallMass B u r := by
  unfold scalarBallMass
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ h)

 theorem scalar_projection_cover_mono {A B : Finset ℝ} (h : A ⊆ B) (δ t : ℝ) :
    (scalarCells δ (A+A.image (fun x => t*x))).card ≤
      (scalarCells δ (B+B.image (fun x => t*x))).card := by
  exact Finset.card_le_card (Finset.image_subset_image
    (Finset.add_subset_add h (Finset.image_subset_image h)))

namespace Regularization

 theorem scalar_leaf_center_card {N : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) : (Q.image scalarPathCenter).card = Q.card := by
  exact Finset.card_image_of_injOn (scalarPathCenter_injOn Q
    (fun q hq => (mem_cubePaths 1 N q).mp (hQ hq)))

 theorem scalar_pruned_ball_bound {N : ℕ} {L Q : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) (hQL : Q ⊆ L) {R K κ : ℝ} (hK : 0 ≤ K)
    (hsize : (L.card:ℝ) ≤ R*(Q.card:ℝ))
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K*t^κ*((L.image scalarPathCenter).card:ℝ)) :
    ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass (Q.image scalarPathCenter) u t ≤
        (K*R)*t^κ*((Q.image scalarPathCenter).card:ℝ) := by
  intro u t ht ht1
  have hm := scalarBallMass_mono (Finset.image_subset_image (f := scalarPathCenter) hQL) u t
  have hh := hball u t ht ht1
  rw [scalar_leaf_center_card L hL] at hh
  rw [scalar_leaf_center_card Q (hQL.trans hL)]
  have hp := mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg (by
    exact (pow_pos (by norm_num : (0:ℝ) < 1/2) N).le.trans ht) κ))
  nlinarith

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarInitialGrowth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative projection growth before the initial regularization.
 Both nonporous and porous alternatives are compared to the original set. -/
namespace Falconer
open scoped Pointwise

namespace Regularization

 theorem scalar_initial_projection_growth {B C P M : ℕ} {K K0 κ : ℝ}
    (hC : 7 ≤ C) (hCB : 2*C ≤ B) (hP : 18 ≤ P) (hM : 0 < M)
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hK : 0 < K) (hK0 : 0 < K0)
    (hCbudget : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hBbudget : 800*(P:ℝ) ≤ κ*(B:ℝ)) (hCmargin : 8*(C:ℝ) ≤ κ*(B:ℝ))
    (hloss : Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200)
    (hscale : 40*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2)
    (hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M))
      (scalarBinaryCopies B C • L.image scalarPathCenter)).card:ℝ) ≤
        (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hpoint : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K0*t^κ*((L.image scalarPathCenter).card:ℝ))
    (A : Finset ℝ) (hA : A.Nonempty) (hAb : ∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass A u t ≤ K*t^κ*(A.card:ℝ)) :
    ∃ t ∈ A, Real.exp ((κ/25)*(P:ℝ)*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
      ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
        (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ) := by
  have hBpos : 0 < B := by omega
  obtain ⟨Q,k,n,hQne,hQL,hsize,hlevels⟩ := scalar_forward_regularization hBpos L hL hne
  have hsizeR : (L.card:ℝ) ≤ (2050*(B+1)^2:ℝ)^(M+1)*(Q.card:ℝ) := by
    exact_mod_cast hsize
  have hpointQ := scalar_pruned_ball_bound hL hQL hK0.le hsizeR hpoint
  have hscaleQ := scalar_regularization_scale_budget hM hκ hK0 hBbudget hloss hscale
  have hJ : 0 < scalarBinaryBranchCount B C := by
    unfold scalarBinaryBranchCount
    positivity
  obtain ⟨t,ht,hgain⟩ := scalar_projection_growth_of_sumset (by omega) (by omega) hP hM
    hBpos Q (hQL.trans hL) hQne k n hlevels (le_refl (18*(2:ℝ)^C)) hJ
    (scalar_binary_parameter_contract hC hCB)
    (scalar_binary_parameter_copy_bound B C).le (le_refl (scalarBinaryCopies B C))
    (L.image scalarPathCenter) (Finset.image_subset_image (f := scalarPathCenter) hQL) hκ hκ1
    (scalar_binary_parameter_log hCB hCmargin) hsmall hK (by positivity)
    hCbudget hBbudget hscaleQ hpointQ A hA hAb hball
  refine ⟨t,ht,?_⟩
  calc
    _ ≤ Real.exp ((κ/25)*(P:ℝ)*(M:ℝ)*Real.log 2)*
        ((2050*(B+1)^2:ℝ)^(M+1)*(Q.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hsizeR (Real.exp_pos _).le
    _ = (Real.exp ((κ/25)*(P:ℝ)*(M:ℝ)*Real.log 2)*
        (2050*(B+1)^2:ℝ)^(M+1))*(Q.card:ℝ) := by ring
    _ ≤ Real.exp ((κ/20)*(P:ℝ)*(M:ℝ)*Real.log 2)*(Q.card:ℝ) :=
      mul_le_mul_of_nonneg_right (scalar_regularization_gain hM hκ.le hloss) (Nat.cast_nonneg _)
    _ < _ := hgain
    _ ≤ _ := by
      exact_mod_cast scalar_projection_cover_mono
        (Finset.image_subset_image (f := scalarPathCenter) hQL) ((1/2:ℝ)^(B*M)) t

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarSumsetLogBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparing the original fixed-fold sumset with small doubling. The
 logarithmic loss does not contain the regularization factor. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_sumset_log_bound {δ K : ℝ} (_hδ : 0 < δ) (hK : 0 < K)
    (A : Finset ℝ) (hA : A.Nonempty)
    (hsmall : ((scalarCells δ (A+A)).card:ℝ) ≤ K*(scalarCells δ A).card)
    (copies : ℕ) :
    Real.log ((scalarCells δ (copies • A)).card:ℝ) ≤
      Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*K)+Real.log (A.card:ℝ) := by
  have hp := scalar_pluennecke δ A A hA hsmall copies 0
  simp only [zero_nsmul,sub_zero,add_zero,Nat.cast_zero] at hp
  have hcard : ((scalarCells δ A).card:ℝ) ≤ (A.card:ℝ) := by
    exact_mod_cast Finset.card_image_le (s := A)
  have hu := hp.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
  have hs : (scalarCells δ (copies • A)).Nonempty := (hA.nsmul).image _
  have hpos : (0:ℝ) < ((scalarCells δ (copies • A)).card:ℝ) := by exact_mod_cast hs.card_pos
  have hAc : (0:ℝ) < (A.card:ℝ) := by exact_mod_cast hA.card_pos
  have hl := Real.log_le_log hpos hu
  rw [Real.log_mul (by positivity) hAc.ne',Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at hl
  exact hl

 theorem scalar_weak_prefix_budget {B P M : ℕ} {κ K0 : ℝ} (hκ : 0 ≤ κ)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hweak : Real.log K0 ≤ κ^2*(B:ℝ)*(M:ℝ)*Real.log 2/160) :
    40*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2 := by
  have hp : (0:ℝ) ≤ (P:ℝ) := Nat.cast_nonneg _
  have hc : κ*(B:ℝ)/4 ≤ κ*(B:ℝ)-2*(P:ℝ) := by linarith
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ κ*(M:ℝ)*Real.log 2 by positivity)
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_ScalarWeakBlockProjection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar projection gain in the weak Frostman regime required by
 the planar application. Only the coefficient Frostman constant is fixed. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_weak_block_projection_oai {κ K : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hK : 0 < K) :
    ∃ B copies : ℕ, ∃ η : ℝ, 0 < B ∧ 0 < copies ∧ 0 < η ∧
      ∀ M : ℕ, 0 < M → ∀ K0 Kadd : ℝ, 0 < K0 → 0 < Kadd →
      Real.log K0 ≤ κ^2*(B:ℝ)*(M:ℝ)*Real.log 2/160 →
      Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*Kadd) ≤
        (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ∀ L : Finset (CellPath 1), L ⊆ cubePaths 1 (B*M) → L.Nonempty →
      Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ((scalarCells ((1/2:ℝ)^(B*M))
        (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
        Kadd*(scalarCells ((1/2:ℝ)^(B*M)) (L.image scalarPathCenter)).card →
      (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
        scalarBallMass (L.image scalarPathCenter) u t ≤
          K0*t^κ*((L.image scalarPathCenter).card:ℝ)) →
      ∀ A : Finset ℝ, A.Nonempty → (∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1) →
      (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
        scalarBallMass A u t ≤ K*t^κ*(A.card:ℝ)) →
      ∃ t ∈ A, Real.exp (η*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
        ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
          (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ) := by
  obtain ⟨P,B,C,hP,hC,hCB,hB,hmargin,hbudget,hloss⟩ := scalar_block_parameters hκ K
  refine ⟨B,scalarBinaryCopies B C,κ*(P:ℝ)/25,by omega,?_,by positivity,?_⟩
  · unfold scalarBinaryCopies scalarBinaryBranchCount
    positivity
  intro M hM K0 Kadd hK0 hKadd hweak hcost L hL hne hsize hadd hpoint A hA hAb hball
  have hscale := scalar_weak_prefix_budget hκ.le hB hweak
  have hsum := scalar_sumset_log_bound (by positivity) hKadd
    (L.image scalarPathCenter) (hne.image _) hadd (scalarBinaryCopies B C)
  rw [scalar_leaf_center_card L hL] at hsum
  have hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M))
      (scalarBinaryCopies B C • L.image scalarPathCenter)).card:ℝ) ≤
      (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 := by nlinarith
  simpa only [div_mul_eq_mul_div,mul_assoc] using
    scalar_initial_projection_growth hC hCB hP hM L hL hne hκ hκ1 hK hK0
      hbudget hB hmargin hloss hscale hsmall hpoint A hA hAb hball

end Falconer.Regularization

end OAI
end

theorem solution : type_of% @OAI.Falconer.Regularization.scalar_weak_block_projection_oai := @OAI.Falconer.Regularization.scalar_weak_block_projection_oai
