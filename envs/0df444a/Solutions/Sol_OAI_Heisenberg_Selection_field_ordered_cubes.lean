-- Prove2me | solution 1 for OAI.Heisenberg.Selection.field_ordered_cubes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:43:11.401823+00:00
-- url     : https://prove2.me/submissions/57adc6cb-bfac-4c09-b0c2-e821c9462e2c

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002
import Theorems.Thm_OAI_Heisenberg_Selection_physical_field_mean
import Theorems.Thm_OAI_Heisenberg_Surface_mesh_matrix_surface

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExponentialEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

lemma nearestNeighbor_symm {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    NearestNeighbor y x := by
  unfold NearestNeighbor at *
  simpa only [abs_sub_comm] using h

lemma nearestNeighbor_coordinate {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    ∃ i, (y i = x i + 1 ∨ y i = x i - 1) ∧ ∀ j, j ≠ i → y j = x j := by
  have hi : ∃ i, x i ≠ y i := by
    by_contra! hh
    have : ∑ i : Fin d, |x i - y i| = (0 : ℤ) := by simp [hh]
    change ∑ i : Fin d, |x i - y i| = (1 : ℤ) at h
    omega
  obtain ⟨i, hi⟩ := hi
  have hain : 1 ≤ |x i-y i| := by
    have hn : x i-y i ≠ 0 := sub_ne_zero.mpr hi
    have := abs_pos.mpr hn
    omega
  have hai : |x i-y i| ≤ 1 := by
    change ∑ i : Fin d, |x i-y i| = (1 : ℤ) at h
    rw [← h]
    exact Finset.single_le_sum (f := fun j : Fin d => |x j - y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨i, ?_, ?_⟩
  · have hab : x i-y i = 1 ∨ x i-y i = -1 := by
      have : |x i-y i| = 1 := le_antisymm hai hain
      exact (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp this
    omega
  · intro j hji
    have hsum : |x i-y i| + |x j-y j| ≤ (1 : ℤ) := by
      change ∑ i : Fin d, |x i-y i| = (1 : ℤ) at h
      rw [← h]
      rw [← Finset.sum_pair (f := fun j : Fin d => |x j-y j|) (Ne.symm hji)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    have : |x j-y j| = 0 := le_antisymm (by omega) (abs_nonneg _)
    exact (sub_eq_zero.mp (abs_eq_zero.mp this)).symm

lemma mem_neighbors_of_nearestNeighbor {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) :
    y ∈ neighbors x := by
  obtain ⟨i, hi, he⟩ := nearestNeighbor_coordinate h
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rcases hi with hi | hi
  · have hy : y = Function.update x i (x i+1) := by
      ext j
      by_cases hj : j = i
      · subst j; simpa using hi
      · simp [Function.update_of_ne hj, he j hj]
    simp [hy]
  · have hy : y = Function.update x i (x i-1) := by
      ext j
      by_cases hj : j = i
      · subst j; simpa using hi
      · simp [Function.update_of_ne hj, he j hj]
    simp [hy]

lemma card_neighbors_le {d : ℕ} (x : Site d) : (neighbors x).card ≤ 2*d := by
  calc
    (neighbors x).card ≤ ∑ i : Fin d,
        ({Function.update x i (x i+1), Function.update x i (x i-1)} : Finset (Site d)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin d, 2 := Finset.sum_le_sum (fun _ _ => Finset.card_le_two)
    _ = 2*d := by simp [mul_comm]

lemma mem_incidentEdges {d : ℕ} {F : Finset (Site d)} {x y : Site d}
    (h : NearestNeighbor x y) (hm : x ∈ F ∨ y ∈ F) : (x,y) ∈ incidentEdges F := by
  rcases hm with hx | hy
  · exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨y, mem_neighbors_of_nearestNeighbor h, rfl⟩)⟩
  · exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x, mem_neighbors_of_nearestNeighbor (nearestNeighbor_symm h), rfl⟩)⟩

lemma card_incidentEdges_le {d : ℕ} (F : Finset (Site d)) :
    (incidentEdges F).card ≤ (4*d)*F.card := by
  calc
    _ ≤ ∑ x ∈ F, (((neighbors x).image (fun y => (x,y))) ∪
        ((neighbors x).image (fun y => (y,x)))).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ F, 4*d := by
      apply Finset.sum_le_sum
      intro x _
      exact (Finset.card_union_le _ _).trans ((add_le_add
        ((Finset.card_image_le).trans (card_neighbors_le x))
        ((Finset.card_image_le).trans (card_neighbors_le x))).trans (by omega))
    _ = (4*d)*F.card := by simp [mul_comm]

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_KilledContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MatrixContraction

variable {V : Type*} [Fintype V]

lemma DoublySubstochastic.mul {U W : Matrix V V ℝ}
    (hU : DoublySubstochastic U) (hW : DoublySubstochastic W) :
    DoublySubstochastic (U * W) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hU.nonneg i k) (hW.nonneg k j))
  · intro i
    change (∑ j, ∑ k, U i k * W k j) ≤ 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    exact (Finset.sum_le_sum (fun k _ =>
      mul_le_of_le_one_right (hU.nonneg i k) (hW.row k))).trans (hU.row i)
  · intro j
    change (∑ i, ∑ k, U i k * W k j) ≤ 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    exact (Finset.sum_le_sum (fun k _ =>
      mul_le_of_le_one_left (hW.nonneg k j) (hU.col k))).trans (hW.col j)

theorem of_partial_permutation (p : V → Option V)
    (hp : ∀ i j a, p i = some a → p j = some a → i = j) :
    DoublySubstochastic (fun i j => if p j = some i then 1 else 0) := by
  constructor
  · intro i j; split_ifs <;> norm_num
  · intro i
    have hc : (Finset.univ.filter fun j => p j = some i).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      exact hp j k i (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.cast_le_one] using (show ((Finset.univ.filter fun j => p j = some i).card : ℝ) ≤ 1 by
        exact_mod_cast hc)
  · intro j
    cases hj : p j with
    | none => simp
    | some i => simp

theorem weighted_average {I : Type*} [Fintype I] (w : I → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (U : I → Matrix V V ℝ)
    (hU : ∀ a, DoublySubstochastic (U a)) :
    DoublySubstochastic (fun i j => ∑ a, w a * U a i j) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) ((hU a).nonneg i j))
  · intro i
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ a, w a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right (hw a) ((hU a).row i))
      _ = 1 := hs
  · intro j
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ a, w a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right (hw a) ((hU a).col j))
      _ = 1 := hs

end Heisenberg.MatrixContraction

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma card_boxFinset (d r : ℕ) : (boxFinset d r).card = (2 * r + 1) ^ d := by
  simp only [boxFinset, Fintype.card_piFinset, Int.card_Icc]
  have hc : ((r : ℤ) + 1 + (r : ℤ)).toNat = 2 * r + 1 := by omega
  simp [hc]

end Heisenberg.Geometry
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ScheduledResiduals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Fin.NatCast

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.Serial
open Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks
variable {V T X E : Type} [Fintype V] [DecidableEq V] [Fintype T]
  [PseudoMetricSpace X] [Fintype E]

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma product_snoc (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ) :
    product (n+1) K=K (Fin.last n)*product n (fun i=>K i.castSucc) := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [product,ih,product,Matrix.mul_assoc]
    rfl

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma prefix_product (K : ℕ → Matrix V V ℝ) (n : ℕ) :
    prefixMatrix K n=product n (fun i=>K i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixMatrix,product_snoc]
    simpa only [Fin.val_last,Fin.val_castSucc] using congrArg (K n * ·) ih

end Heisenberg.Serial

end
end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SlotColorTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Matrix.Norms.Operator
namespace Heisenberg.SlotColor
variable {V : Type*}

lemma permute_mul (π ρ : Equiv.Perm V) : permute (π*ρ) = permute π * permute ρ := by
  ext c i
  rfl

variable [Fintype V]

lemma matrix_one : matrix (1 : Equiv.Perm V) = 1 := by
  ext c b
  have he : permute (1 : Equiv.Perm V) b = b := by ext i; rfl
  simp [matrix,he,Matrix.one_apply,eq_comm]

lemma matrix_mul (π ρ : Equiv.Perm V) : matrix (π*ρ) = matrix π * matrix ρ := by
  ext c b
  simp only [matrix,Matrix.mul_apply,permute_mul,Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (permute ρ b)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

end Heisenberg.SlotColor
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SerialBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Serial
open MeshPair
variable {V : Type} [Fintype V] [DecidableEq V]

lemma prefix_add (K : ℕ → Matrix V V ℝ) (m n : ℕ) :
    prefixMatrix K (m+n)=prefixMatrix (fun j=>K (m+j)) n*prefixMatrix K m := by
  induction n with
  | zero=>simp [prefixMatrix]
  | succ n ih=>rw [Nat.add_succ,prefixMatrix,ih,prefixMatrix,Matrix.mul_assoc]

lemma prefix_congr (K L : ℕ → Matrix V V ℝ) (n : ℕ)
    (h : ∀ j,j<n → K j=L j) : prefixMatrix K n=prefixMatrix L n := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [prefixMatrix,prefixMatrix,h n (by omega),ih (fun j hj=>h j (by omega))]

lemma prefix_periodic (K : ℕ → Matrix V V ℝ) (Q k : ℕ) :
    prefixMatrix (fun j=>K (j%Q)) (k*Q)=(prefixMatrix (fun j=>K (j%Q)) Q)^k := by
  induction k with
  | zero=>simp [prefixMatrix]
  | succ k ih=>
    rw [Nat.succ_mul,prefix_add,ih,pow_succ']
    congr 1
    apply prefix_congr
    intro j _
    rw [Nat.add_mod]
    simp

lemma prefix_period (K : ℕ → Matrix V V ℝ) (Q : ℕ) :
    prefixMatrix (fun j=>K (j%Q)) Q=prefixMatrix K Q := by
  apply prefix_congr
  intro j hj
  rw [Nat.mod_eq_of_lt hj]

lemma completed_sweeps (A P : ℕ → Matrix V V ℝ) (q c k : ℕ) :
    let Q:=q+c
    let base : ℕ → Matrix V V ℝ:=fun j=>if j<q then A j else 1
    let final : ℕ → Matrix V V ℝ:=fun j=>if j<q then A j else P (j-q)
    let all : ℕ → Matrix V V ℝ:=fun j=>if j<k*Q then base (j%Q) else final (j-k*Q)
    prefixMatrix all ((k+1)*Q)=prefixMatrix P c*(prefixMatrix A q)^(k+1) := by
  intro Q base final all
  rw [Nat.succ_mul,prefix_add]
  have hfirst : prefixMatrix all (k*Q)=(prefixMatrix A q)^k := by
    trans prefixMatrix (fun j=>base (j%Q)) (k*Q)
    · apply prefix_congr; intro j hj; simp [all,hj]
    rw [prefix_periodic,prefix_period]
    congr 1
    change prefixMatrix base (q+c)=_
    rw [prefix_add]
    have he : prefixMatrix (fun j=>base (q+j)) c=1 := by
      suffices ∀ n,prefixMatrix (fun j=>base (q+j)) n=1 from this c
      intro n
      induction n with
      | zero=>rfl
      | succ n ih=>rw [prefixMatrix,ih]; simp [base]
    rw [he,Matrix.one_mul]
    apply prefix_congr; intro j hj; simp [base,hj]
  have hlast : prefixMatrix (fun j=>all (k*Q+j)) Q=prefixMatrix P c*prefixMatrix A q := by
    trans prefixMatrix final Q
    · apply prefix_congr; intro j _; simp [all]
    change prefixMatrix final (q+c)=_
    rw [prefix_add]
    congr 1
    · apply prefix_congr; intro j _; simp [final]
    · apply prefix_congr; intro j hj; simp [final,hj]
  rw [hfirst,hlast,Matrix.mul_assoc,pow_succ']

end Heisenberg.Serial
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open LayeredExchange MeshPair
variable {V : Type} [Fintype V]

attribute [local instance] OAI.completionDecEq
lemma completed_product (a b u v : ℕ → V) (q c k : ℕ) (δ : ℝ) :
    Serial.product ((k+1)*(q+c)) (fun j=>colorCoin
      (completedEndpoint a u q c j) (completedEndpoint b v q c j) (completedRate δ q c k j))=
    prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c*
      (prefixMatrix (fun j=>colorCoin (a j) (b j) (δ/2)) q)^(k+1) := by
  let Q:=q+c
  let A:=fun j=>colorCoin (a j) (b j) (δ/2)
  let P:=fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))
  rw [←Serial.prefix_product (fun j=>colorCoin
    (completedEndpoint a u q c j) (completedEndpoint b v q c j) (completedRate δ q c k j))]
  rw [←Serial.completed_sweeps A P q c k]
  apply Serial.prefix_congr
  intro j hj
  change j<(k+1)*Q at hj
  rw [Nat.add_mul,Nat.one_mul] at hj
  change colorCoin _ _ _=(if j<k*Q then _ else _)
  by_cases hearly : j<k*Q
  · rw [ite_eq_left hearly]
    by_cases hsp : j%Q<q
    · simp only [completedEndpoint,completedRate,Q] at hsp ⊢
      rw [ite_eq_left hsp,ite_eq_left hsp,ite_eq_left hsp,ite_eq_left hsp]
    · simp only [completedEndpoint,completedRate,Q] at hsp ⊢
      rw [ite_eq_right hsp,ite_eq_right hsp,ite_eq_right hsp,ite_eq_right hsp,ite_eq_right (show ¬k*(q+c)≤j from by change ¬k*Q≤j; omega)]
      exact colorCoin_zero _ _
  · rw [ite_eq_right hearly]
    have hrem : j%Q=j-k*Q := by
      have hlt : j-k*Q<Q := by omega
      have hdecomp : j=k*Q+(j-k*Q):=by omega
      conv_lhs=>rw [hdecomp]
      rw [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt hlt]
    by_cases hsp : j-k*Q<q
    · simp only [completedEndpoint,completedRate,show q+c=Q from rfl,hrem,ite_eq_left hsp,A]
    · simp only [completedEndpoint,completedRate,show q+c=Q from rfl,hrem,ite_eq_right hsp,
        ite_eq_left (by omega : k*Q≤j),colorCoin_one,P]

lemma completed_rate_bounds (q c k j : ℕ) {δ : ℝ} (hδ : 0≤δ) (hδ2 : δ≤2) :
    0≤completedRate δ q c k j ∧ completedRate δ q c k j≤1 := by
  unfold completedRate
  split_ifs <;> constructor <;> linarith

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SlotOnMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
namespace Heisenberg.SpinSlots

lemma config_card_le (ℓ : ℕ) (A : Config ℓ) : A.card ≤ ℓ := by
  simpa using Finset.card_le_univ A

lemma multiplicity_pos (ℓ : ℕ) (k : Level ℓ) : 0 < (ℓ.choose k.val : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : k.val ≤ ℓ)

lemma sqrt_multiplicity_pos (ℓ : ℕ) (k : Level ℓ) : 0 < Real.sqrt (ℓ.choose k.val) :=
  Real.sqrt_pos.mpr (multiplicity_pos ℓ k)

lemma card_layer (ℓ k : ℕ) :
    (Finset.univ.filter (fun A : Config ℓ => A.card = k)).card = ℓ.choose k := by
  have he : Finset.univ.filter (fun A : Config ℓ => A.card = k) =
      (Finset.univ : Finset (Fin ℓ)).powersetCard k := by
    ext A
    simp
  rw [he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

theorem basis_orthonormal (ℓ : ℕ) : (basis ℓ).transpose * basis ℓ = 1 := by
  ext k m
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  by_cases hkm : k = m
  · subst m
    have he : ∑ A : Config ℓ, basis ℓ A k * basis ℓ A k =
      ((ℓ.choose k.val : ℝ)) / (Real.sqrt (ℓ.choose k.val))^2 := by
      calc
        _ = ∑ A ∈ (Finset.univ.filter (fun A : Config ℓ => A.card = k.val)),
            (Real.sqrt (ℓ.choose k.val))⁻¹ * (Real.sqrt (ℓ.choose k.val))⁻¹ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro A _
          by_cases hk : A.card = k.val <;> simp [basis,hk]
        _ = _ := by
          simp only [Finset.sum_const,nsmul_eq_mul,card_layer]
          ring
    rw [he,Real.sq_sqrt (multiplicity_pos ℓ k).le]
    simp [ne_of_gt (multiplicity_pos ℓ k)]
  · rw [Matrix.one_apply_ne hkm]
    apply Finset.sum_eq_zero
    intro A _
    by_cases hk : A.card = k.val
    · have hm : A.card ≠ m.val := fun hm => hkm (Fin.ext (hk.symm.trans hm))
      simp [basis,hm]
    · simp [basis,hk]

lemma raising_mul_basis (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) :
    (raising ℓ * basis ℓ) A k = ∑ j ∈ A, basis ℓ (A.erase j) k := by
  simp only [Matrix.mul_apply,raising,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp

lemma binomial_raising_coefficient (ℓ : ℕ) (k : Fin ℓ) :
    ((k.val+1 : ℕ) : ℝ) * (Real.sqrt (ℓ.choose k.val))⁻¹ =
      Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) * (Real.sqrt (ℓ.choose (k.val+1)))⁻¹ := by
  have hA := multiplicity_pos ℓ k.castSucc
  have hB := multiplicity_pos ℓ k.succ
  have ha := sqrt_multiplicity_pos ℓ k.castSucc
  have hb := sqrt_multiplicity_pos ℓ k.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hA hB ha hb
  have he : ((ℓ.choose (k.val+1) : ℝ)) * (k.val+1) =
      (ℓ.choose k.val : ℝ) * (ℓ-k.val : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq ℓ k.val
  have hc : 0 ≤ (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) := by positivity
  have hsqA := Real.sq_sqrt hA.le
  have hsqB := Real.sq_sqrt hB.le
  have hsqC := Real.sq_sqrt hc
  have he' : ((k.val+1 : ℕ) : ℝ) * Real.sqrt (ℓ.choose (k.val+1)) =
      Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) * Real.sqrt (ℓ.choose k.val) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,hsqB,hsqC,hsqA]
    push_cast
    nlinarith [he]
  simpa only [div_eq_mul_inv] using (div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)).mpr he'

lemma raising_basis_entry (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) :
    (raising ℓ * basis ℓ) A k =
      if A.card = k.val+1 then (A.card : ℝ) * (Real.sqrt (ℓ.choose k.val))⁻¹ else 0 := by
  rw [raising_mul_basis]
  have he : ∀ j ∈ A, basis ℓ (A.erase j) k =
      if A.card = k.val+1 then (Real.sqrt (ℓ.choose k.val))⁻¹ else 0 := by
    intro j hj
    have hcard := Finset.card_pos.mpr ⟨j,hj⟩
    simp only [basis,Finset.card_erase_of_mem hj]
    have hi : (A.card-1=k.val) ↔ (A.card=k.val+1) := by omega
    simp only [hi]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,nsmul_eq_mul]
  split_ifs <;> simp

theorem diagonal_intertwines (ℓ : ℕ) : diagonalZ ℓ * basis ℓ = basis ℓ * physicalZ ℓ := by
  ext A k
  simp only [diagonalZ,physicalZ,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases h : A.card = k.val <;> simp [basis,h,mul_comm]

theorem raising_intertwines (ℓ : ℕ) : raising ℓ * basis ℓ = basis ℓ * physicalPlus ℓ := by
  ext A k
  rw [raising_basis_entry]
  by_cases hk : k.val < ℓ
  · let j : Fin ℓ := ⟨k.val,hk⟩
    have he : (basis ℓ * physicalPlus ℓ) A k =
        basis ℓ A j.succ * Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single j.succ]
      · simp [physicalPlus,j]
      · intro m hm hmj
        have hne : m.val ≠ k.val+1 := fun h => hmj (Fin.ext h)
        simp [physicalPlus,hne]
      · simp
    rw [he]
    by_cases hA : A.card = k.val+1
    · simpa [basis,hA,j,mul_comm] using binomial_raising_coefficient ℓ j
    · simp [basis,hA,j]
  · have htop : k.val = ℓ := by omega
    have hA : A.card ≠ k.val+1 := by have := config_card_le ℓ A; omega
    rw [ite_eq_right hA,Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro m _
    have hm : m.val ≠ k.val+1 := by omega
    simp [physicalPlus,hm]

lemma map_mul (ℓ : ℕ) (A : Config ℓ) (σ τ : Equiv.Perm (Fin ℓ)) :
    A.map (σ*τ).toEmbedding = (A.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

lemma average_map_left (ℓ : ℕ) (A B : Config ℓ) (τ : Equiv.Perm (Fin ℓ)) :
    average ℓ (A.map τ.toEmbedding) B = average ℓ A B := by
  unfold average
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulLeft τ)]
  apply Finset.sum_congr rfl
  intro σ _
  change (if A.map τ.toEmbedding = B.map (τ*σ).toEmbedding then (1 : ℝ) else 0) = _
  rw [map_mul]
  simp only [(Finset.map_injective τ.toEmbedding).eq_iff]

lemma average_column_sum (ℓ : ℕ) (B : Config ℓ) : ∑ A, average ℓ A B = 1 := by
  have hp : (Fintype.card (Equiv.Perm (Fin ℓ)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold average
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp [hp]

lemma average_eq_zero (ℓ : ℕ) (A B : Config ℓ) (h : A.card ≠ B.card) :
    average ℓ A B = 0 := by
  unfold average
  have hn : ∀ σ : Equiv.Perm (Fin ℓ), A ≠ B.map σ.toEmbedding := by
    intro σ he
    exact h (by rw [he,Finset.card_map])
  simp [hn]

lemma average_eq_diagonal (ℓ : ℕ) (A B : Config ℓ) (h : A.card = B.card) :
    average ℓ A B = average ℓ B B := by
  obtain ⟨τ,hτ⟩ := Equiv.Perm.exists_map_finset_eq B A h.symm
  rw [← hτ,average_map_left]

lemma average_diagonal (ℓ : ℕ) (B : Config ℓ) :
    average ℓ B B = (ℓ.choose B.card : ℝ)⁻¹ := by
  have hp : (ℓ.choose B.card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.choose_pos (config_card_le ℓ B))
  have he := average_column_sum ℓ B
  have hf : ∑ A, average ℓ A B =
      (ℓ.choose B.card : ℝ) * average ℓ B B := by
    calc
      _ = ∑ A : Config ℓ, if A.card = B.card then average ℓ B B else 0 := by
        apply Finset.sum_congr rfl
        intro A _
        by_cases h : A.card = B.card
        · rw [ite_eq_left h,average_eq_diagonal ℓ A B h]
        · rw [ite_eq_right h,average_eq_zero ℓ A B h]
      _ = _ := by rw [← Finset.sum_filter]; simp
  rw [hf] at he
  simpa only [one_div] using (eq_div_iff hp).mpr (show average ℓ B B * (ℓ.choose B.card : ℝ) = 1 by simpa [mul_comm] using he)

theorem average_entry (ℓ : ℕ) (A B : Config ℓ) :
    average ℓ A B = if A.card = B.card then (ℓ.choose B.card : ℝ)⁻¹ else 0 := by
  split_ifs with h
  · rw [average_eq_diagonal ℓ A B h,average_diagonal]
  · exact average_eq_zero ℓ A B h

lemma basis_projection_entry (ℓ : ℕ) (A B : Config ℓ) :
    (basis ℓ * (basis ℓ).transpose) A B =
      if A.card = B.card then (ℓ.choose B.card : ℝ)⁻¹ else 0 := by
  let k : Level ℓ := ⟨B.card,by have := config_card_le ℓ B; omega⟩
  have he : (basis ℓ * (basis ℓ).transpose) A B = basis ℓ A k * basis ℓ B k := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    apply Finset.sum_eq_single k
    · intro m hm hmk
      have hne : B.card ≠ m.val := fun h => hmk (Fin.ext h.symm)
      simp [basis,hne]
    · simp
  rw [he]
  have hp : 0 ≤ (ℓ.choose B.card : ℝ) := by positivity
  by_cases h : A.card = B.card
  · simp only [basis,k,h,ite_true]
    rw [← mul_inv_rev,← sq,Real.sq_sqrt hp]
  · simp [basis,k,h]

theorem symmetrizer (ℓ : ℕ) : average ℓ = basis ℓ * (basis ℓ).transpose := by
  ext A B
  rw [average_entry,basis_projection_entry]

lemma erase_relation (ℓ : ℕ) (A B : Config ℓ) (j : Fin ℓ) :
    (j ∈ B ∧ A = B.erase j) ↔ (j ∉ A ∧ B = insert j A) := by
  constructor
  · rintro ⟨hj,rfl⟩
    exact ⟨by simp,(Finset.insert_erase hj).symm⟩
  · rintro ⟨hj,rfl⟩
    exact ⟨Finset.mem_insert_self _ _,(Finset.erase_insert hj).symm⟩

lemma lowering_entry (ℓ : ℕ) (A B : Config ℓ) :
    (raising ℓ).transpose A B = ∑ j ∈ (Finset.univ \ A), if B = insert j A then 1 else 0 := by
  simp only [Matrix.transpose_apply,raising]
  rw [← Finset.sum_filter,← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact erase_relation ℓ A B j
  · intro j hj
    rfl

lemma lowering_mul_basis (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) :
    ((raising ℓ).transpose * basis ℓ) A k =
      ∑ j ∈ (Finset.univ \ A), basis ℓ (insert j A) k := by
  simp only [Matrix.mul_apply,lowering_entry,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma lowering_basis_entry (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) :
    ((raising ℓ).transpose * basis ℓ) A k =
      if A.card+1 = k.val then ((ℓ-A.card : ℕ) : ℝ) *
        (Real.sqrt (ℓ.choose k.val))⁻¹ else 0 := by
  rw [lowering_mul_basis]
  have he : ∀ j ∈ (Finset.univ \ A), basis ℓ (insert j A) k =
      if A.card+1 = k.val then (Real.sqrt (ℓ.choose k.val))⁻¹ else 0 := by
    intro j hj
    simp only [basis,Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hj).2]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_sdiff,Finset.inter_univ,
    Finset.card_univ,Fintype.card_fin]
  split_ifs <;> simp

lemma binomial_lowering_coefficient (ℓ : ℕ) (k : Fin ℓ) :
    ((ℓ-k.val : ℕ) : ℝ) * (Real.sqrt (ℓ.choose (k.val+1)))⁻¹ =
      Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) * (Real.sqrt (ℓ.choose k.val))⁻¹ := by
  have hA := multiplicity_pos ℓ k.castSucc
  have hB := multiplicity_pos ℓ k.succ
  have ha := sqrt_multiplicity_pos ℓ k.castSucc
  have hb := sqrt_multiplicity_pos ℓ k.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hA hB ha hb
  have he : ((ℓ.choose (k.val+1) : ℝ)) * (k.val+1) =
      (ℓ.choose k.val : ℝ) * (ℓ-k.val : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq ℓ k.val
  have hc : 0 ≤ (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) := by positivity
  have hsqA := Real.sq_sqrt hA.le
  have hsqB := Real.sq_sqrt hB.le
  have hsqC := Real.sq_sqrt hc
  have he' : ((ℓ-k.val : ℕ) : ℝ) * Real.sqrt (ℓ.choose k.val) =
      Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) * Real.sqrt (ℓ.choose (k.val+1)) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,hsqA,hsqC,hsqB]
    nlinarith [he]
  simpa only [div_eq_mul_inv] using (div_eq_div_iff (ne_of_gt hb) (ne_of_gt ha)).mpr he'

theorem lowering_intertwines (ℓ : ℕ) :
    (raising ℓ).transpose * basis ℓ = basis ℓ * (physicalPlus ℓ).transpose := by
  ext A k
  rw [lowering_basis_entry]
  by_cases hk : 0 < k.val
  · let j : Fin ℓ := ⟨k.val-1,by omega⟩
    have hjs : j.val+1 = k.val := by dsimp [j]; omega
    have he : (basis ℓ * (physicalPlus ℓ).transpose) A k =
        basis ℓ A j.castSucc * Real.sqrt (((ℓ-j.val : ℕ) : ℝ)*(j.val+1)) := by
      rw [Matrix.mul_apply,Finset.sum_eq_single j.castSucc]
      · simp [physicalPlus,hjs]
      · intro m hm hmj
        have hne : k.val ≠ m.val+1 := by
          intro h
          apply hmj
          apply Fin.ext
          dsimp [j]
          omega
        simp [physicalPlus,hne]
      · simp
    rw [he]
    by_cases hA : A.card+1 = k.val
    · have hAj : A.card = j.val := by omega
      simpa [basis,hAj,← hjs,mul_comm] using binomial_lowering_coefficient ℓ j
    · have hAj : A.card ≠ j.val := by omega
      simp [basis,hA,hAj]
  · have hzero : k.val = 0 := by omega
    have hA : A.card+1 ≠ k.val := by omega
    rw [ite_eq_right hA,Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro m _
    have hm : k.val ≠ m.val+1 := by omega
    simp [physicalPlus,hm]

end Heisenberg.SpinSlots

open scoped Classical BigOperators
namespace Heisenberg.TensorMatrix
variable {X α β γ R : Type*} [Fintype X] [DecidableEq X] [CommSemiring R]

lemma tensor_mul [Fintype β] (M : X → Matrix α β R) (N : X → Matrix β γ R) :
    tensor M * tensor N = tensor (fun x => M x * N x) := by
  ext a b
  simp only [Matrix.mul_apply,tensor,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun x y => M x (a x) y * N x y (b x)).symm

omit [DecidableEq X] in
lemma tensor_one [DecidableEq α] : tensor (fun _ : X => (1 : Matrix α α R)) = 1 := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [tensor]
  · obtain ⟨x,hx⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ x)
    exact Matrix.one_apply_ne hx

omit [DecidableEq X] in
lemma tensor_transpose (M : X → Matrix α β R) :
    (tensor M).transpose = tensor (fun x => (M x).transpose) := rfl

lemma local_entry [DecidableEq α] (x : X) (M : Matrix α α R)
    (a b : X → α) : onsite x M a b =
      M (a x) (b x) * ∏ y ∈ (Finset.univ.erase x), (1 : Matrix α α R) (a y) (b y) := by
  unfold onsite tensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  simp only [Function.update_of_ne (Finset.mem_erase.mp hy).1]

lemma local_intertwines [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] (x : X) (V : Matrix α β R)
    (A : Matrix α α R) (B : Matrix β β R) (h : A * V = V * B) :
    onsite x A * tensor (fun _ : X => V) = tensor (fun _ : X => V) * onsite x B := by
  simp only [onsite]
  rw [tensor_mul (X := X) (α := α) (β := α) (γ := β),tensor_mul (X := X) (α := α) (β := β) (γ := β)]
  congr 1
  funext y
  by_cases hy : y = x
  · simp [hy,h]
  · simp [hy]

lemma tensor_orthonormal [Fintype α] [DecidableEq β] (V : Matrix α β R)
    (h : V.transpose * V = 1) :
    (tensor (fun _ : X => V)).transpose * tensor (fun _ : X => V) = 1 := by
  rw [tensor_transpose,tensor_mul]
  simpa only [h] using (tensor_one (X := X) (α := β) (R := R))

end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open SpinSlots TensorMatrix
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
lemma configEquiv_fiberPerm {ℓ : ℕ} (κ : X → Equiv.Perm (Fin ℓ))
    (c : SlotColor.Color (V:=X × Fin ℓ)) :
    configEquiv ℓ (SlotColor.permute (fiberPerm κ) c) =
      fun x => (configEquiv ℓ c x).map (κ x).toEmbedding := by
  ext x a
  simp [Finset.mem_map_equiv,SlotColor.permute,fiberPerm]

omit [DecidableEq X] in
lemma matrix_fiberPerm {ℓ : ℕ} (κ : X → Equiv.Perm (Fin ℓ)) :
    matrix (fiberPerm κ) = tensor (fun x => fun A B : Config ℓ =>
      if A = B.map (κ x).toEmbedding then (1:ℝ) else 0) := by
  ext A B
  have he : SlotColor.permute (fiberPerm κ) ((configEquiv ℓ).symm B) =
      (configEquiv ℓ).symm A ↔ A = fun x => (B x).map (κ x).toEmbedding := by
    rw [← (configEquiv ℓ).injective.eq_iff,configEquiv_fiberPerm]
    simp [eq_comm]
  change (if SlotColor.permute (fiberPerm κ) ((configEquiv ℓ).symm B) =
      (configEquiv ℓ).symm A then (1:ℝ) else 0) = _
  simp only [he]
  by_cases h : A = fun x => (B x).map (κ x).toEmbedding
  · subst A
    simp [tensor]
  · rw [ite_eq_right h]
    symm
    obtain ⟨x,hx⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ x) (ite_eq_right hx)

theorem symmetrizer (ℓ : ℕ) :
    (Fintype.card (X → Equiv.Perm (Fin ℓ)) : ℝ)⁻¹ •
      (∑ κ : X → Equiv.Perm (Fin ℓ), matrix (fiberPerm κ)) =
    tensor (fun _ : X => basis ℓ) * (tensor (fun _ : X => basis ℓ)).transpose := by
  rw [tensor_transpose,tensor_mul]
  simp_rw [← SpinSlots.symmetrizer,matrix_fiberPerm]
  ext A B
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,tensor,average,
    Fintype.card_fun,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Nat.cast_pow,inv_pow]
  rw [Fintype.prod_sum]

lemma basis_orthonormal (ℓ : ℕ) :
    (tensor (fun _ : X => basis ℓ)).transpose * tensor (fun _ : X => basis ℓ) = 1 :=
  tensor_orthonormal _ (SpinSlots.basis_orthonormal ℓ)

lemma raising_intertwines (ℓ : ℕ) (x : X) :
    onsite x (SpinSlots.raising ℓ) * tensor (fun _ : X => basis ℓ) =
      tensor (fun _ : X => basis ℓ) * onsite x (physicalPlus ℓ) :=
  local_intertwines x _ _ _ (SpinSlots.raising_intertwines ℓ)

lemma lowering_intertwines (ℓ : ℕ) (x : X) :
    onsite x (SpinSlots.raising ℓ).transpose * tensor (fun _ : X => basis ℓ) =
      tensor (fun _ : X => basis ℓ) * onsite x (physicalPlus ℓ).transpose :=
  local_intertwines x _ _ _ (SpinSlots.lowering_intertwines ℓ)

lemma diagonal_intertwines (ℓ : ℕ) (x : X) :
    onsite x (SpinSlots.diagonalZ ℓ) * tensor (fun _ : X => basis ℓ) =
      tensor (fun _ : X => basis ℓ) * onsite x (physicalZ ℓ) :=
  local_intertwines x _ _ _ (SpinSlots.diagonal_intertwines ℓ)

end Heisenberg.SlotTensor
namespace Heisenberg.SlotHalf
open SlotColor
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma change_mul {i j : V} (hij : i ≠ j) (s t : Bool) (a b : Color (V:=V)) :
    (change i s * change j t) a b = if b j ≠ t ∧ b i ≠ s ∧
      a = Function.update (Function.update b j t) i s then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : b j = t
  · simp [change,hj]
  · rw [Finset.sum_eq_single (Function.update b j t)]
    · simp [change,hj,Function.update_of_ne hij]
    · intro c _ hc
      have he : c ≠ Function.update b j t := hc
      simp [change,he]
    · simp

omit [Fintype V] in
lemma swapped_same {i j : V} (b : Color (V:=V)) (h : b i = b j) :
    SlotColor.permute (Equiv.swap i j) b = b := by
  ext k
  by_cases hi : k = i
  · subst k; simp [permute,h]
  · by_cases hj : k = j
    · subst k; simp [permute,h]
    · simp [permute,Equiv.swap_apply_of_ne_of_ne hi hj]

omit [Fintype V] in
lemma swapped_different {i j : V} (hij : i ≠ j) (b : Color (V:=V)) :
    SlotColor.permute (Equiv.swap i j) b =
      Function.update (Function.update b j (b i)) i (b j) := by
  ext k
  by_cases hi : k = i
  · subst k; simp [permute]
  · by_cases hj : k = j
    · subst k; simp [permute,hij.symm]
    · simp [permute,hi,hj,Equiv.swap_apply_of_ne_of_ne hi hj]

theorem swap_spin {i j : V} (hij : i ≠ j) :
    SlotColor.matrix (Equiv.swap i j) =
      change i true * change j false + change i false * change j true +
      (2:ℝ) • (z i * z j) + (1/2:ℝ) • (1:Matrix (Color (V:=V)) (Color (V:=V)) ℝ) := by
  ext a b
  rw [Matrix.add_apply,Matrix.add_apply,Matrix.add_apply,change_mul hij,change_mul hij]
  simp only [z,Matrix.diagonal_mul_diagonal,Matrix.smul_apply,smul_eq_mul,
    Matrix.diagonal_apply,Matrix.one_apply]
  cases hi : b i <;> cases hj : b j
  · have he := swapped_same b (hi.trans hj.symm)
    by_cases hab : a = b
    · subst a; norm_num [SlotColor.matrix,he,hi,hj]
    · simp [SlotColor.matrix,he,hab,Ne.symm hab]
  · have he := swapped_different hij b
    rw [hi,hj] at he
    by_cases hab : a = b
    · subst a
      have hn : b ≠ Function.update (Function.update b j false) i true := by
        intro hh
        have hh' := congrFun hh i
        simp [hi] at hh'
      norm_num [SlotColor.matrix,he,hi,hj,hn,Ne.symm hn]
    · simp [SlotColor.matrix,he,hab,eq_comm]
  · have he := swapped_different hij b
    rw [hi,hj] at he
    by_cases hab : a = b
    · subst a
      have hn : b ≠ Function.update (Function.update b j true) i false := by
        intro hh
        have hh' := congrFun hh i
        simp [hi] at hh'
      norm_num [SlotColor.matrix,he,hi,hj,hn,Ne.symm hn]
    · simp [SlotColor.matrix,he,hab,eq_comm]
  · have he := swapped_same b (hi.trans hj.symm)
    by_cases hab : a = b
    · subst a; norm_num [SlotColor.matrix,he,hi,hj]
    · simp [SlotColor.matrix,he,hab,Ne.symm hab]

end Heisenberg.SlotHalf
namespace Heisenberg.TensorMatrix
variable {X α R : Type*} [Fintype X] [DecidableEq X] [DecidableEq α] [CommSemiring R]
lemma local_entry_ite (x : X) (M : Matrix α α R) (A B : X → α) :
    onsite x M A B = if ∀ y, y ≠ x → A y = B y then M (A x) (B x) else 0 := by
  rw [local_entry]
  by_cases h : ∀ y, y ≠ x → A y = B y
  · rw [ite_eq_left h]
    have he : ∏ y ∈ Finset.univ.erase x, (1:Matrix α α R) (A y) (B y) = 1 := by
      apply Finset.prod_eq_one
      intro y hy
      rw [h y (Finset.mem_erase.mp hy).1]
      exact Matrix.one_apply_eq _
    rw [he,mul_one]
  · rw [ite_eq_right h]
    obtain ⟨y,hy,hab⟩ := not_forall.mp h |>.imp (fun _ => Classical.not_imp.mp)
    have he : ∏ y ∈ Finset.univ.erase x, (1:Matrix α α R) (A y) (B y) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hy,Finset.mem_univ _⟩) (Matrix.one_apply_ne hab)
    rw [he,mul_zero]
end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] in
lemma config_update_true (ℓ : ℕ) (b : SlotColor.Color (V:=X × Fin ℓ)) (x : X) (a : Fin ℓ) :
    configEquiv ℓ (Function.update b (x,a) true) =
      Function.update (configEquiv ℓ b) x (insert a (configEquiv ℓ b x)) := by
  ext y k
  by_cases hy : y = x
  · subst y
    by_cases hk : k = a
    · subst k; simp
    · simp [hk]
  · simp [Function.update_of_ne hy,Function.update_of_ne (show (y,k) ≠ (x,a) by simp [hy])]

lemma reindex_change_true_entry (ℓ : ℕ) (x : X) (a : Fin ℓ) (A B : X → Config ℓ) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (SlotHalf.change (x,a) true) A B =
      if a ∉ B x ∧ A = Function.update B x (insert a (B x)) then (1:ℝ) else 0 := by
  have he : (configEquiv ℓ).symm A = Function.update ((configEquiv ℓ).symm B) (x,a) true ↔
      A = Function.update B x (insert a (B x)) := by
    rw [← (configEquiv ℓ).injective.eq_iff,config_update_true]
    simp
  change (if ((configEquiv ℓ).symm B) (x,a) ≠ true ∧
      (configEquiv ℓ).symm A = Function.update ((configEquiv ℓ).symm B) (x,a) true then (1:ℝ) else 0) = _
  simp only [he]
  simp [configEquiv]

lemma erase_insert_condition {ℓ : ℕ} (a : Fin ℓ) (A B : Config ℓ) :
    (a ∉ B ∧ A = insert a B) ↔ (a ∈ A ∧ B = A.erase a) := by
  constructor
  · rintro ⟨ha,rfl⟩
    simp [ha]
  · rintro ⟨ha,rfl⟩
    simp [Finset.insert_erase ha]

theorem slot_raising (ℓ : ℕ) (x : X) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (∑ a : Fin ℓ, SlotHalf.change (x,a) true) = onsite x (SpinSlots.raising ℓ) := by
  ext A B
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.sum_apply]
  change (∑ a : Fin ℓ, Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
    (SlotHalf.change (x,a) true) A B) = _
  simp_rw [reindex_change_true_entry,Function.eq_update_iff]
  rw [local_entry_ite]
  by_cases h : ∀ y, y ≠ x → A y = B y
  · simp only [iff_true_intro h,and_true,ite_true]
    simp_rw [erase_insert_condition]
    unfold SpinSlots.raising
    have he : Finset.univ.filter (fun a : Fin ℓ => a ∈ A x) = A x := by ext a; simp
    simp only [ite_and]
    rw [← Finset.sum_filter,he]
  · simp only [iff_false_intro h,and_false,ite_false,Finset.sum_const_zero]

end Heisenberg.SlotTensor

namespace Heisenberg.SlotHalf
variable {V : Type*} [Fintype V] [DecidableEq V]
lemma change_transpose (i : V) : (change i true).transpose = change i false := by
  ext a b
  have he : (b i ≠ false ∧ a = Function.update b i false) ↔
      (a i ≠ true ∧ b = Function.update a i true) := by
    constructor
    · rintro ⟨hb,rfl⟩
      have hb' : b i = true := by cases h : b i <;> simp_all
      simp [Function.update_idem,hb']
    · rintro ⟨ha,rfl⟩
      have ha' : a i = false := by cases h : a i <;> simp_all
      simp [Function.update_idem,ha']
  simp only [Matrix.transpose_apply,change,he]
end Heisenberg.SlotHalf

namespace Heisenberg.TensorMatrix
variable {X α R : Type*} [Fintype X] [DecidableEq X] [DecidableEq α] [CommSemiring R]
lemma local_transpose (x : X) (M : Matrix α α R) :
    (onsite x M).transpose = onsite x M.transpose := by
  rw [onsite,tensor_transpose]
  congr 1
  funext y
  by_cases h : y=x <;> simp [h]
lemma local_diagonal (x : X) (f : α → R) :
    onsite x (Matrix.diagonal f) = Matrix.diagonal (fun A => f (A x)) := by
  ext A B
  rw [local_entry_ite]
  by_cases h : A = B
  · subst B
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    split_ifs with ho
    · apply Matrix.diagonal_apply_ne
      intro hx
      apply h
      funext y
      by_cases hy : y=x
      · simpa [hy] using hx
      · exact ho y hy
    · rfl
end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type*} [Fintype X] [DecidableEq X]
theorem slot_lowering (ℓ : ℕ) (x : X) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (∑ a : Fin ℓ, SlotHalf.change (x,a) false) = onsite x (SpinSlots.raising ℓ).transpose := by
  rw [← local_transpose,← slot_raising]
  ext A B
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.sum_apply,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact congrFun (congrFun (SlotHalf.change_transpose (x,a)).symm ((configEquiv ℓ).symm A))
    ((configEquiv ℓ).symm B)

theorem slot_z (ℓ : ℕ) (x : X) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (∑ a : Fin ℓ, SlotHalf.z (x,a)) = onsite x (SpinSlots.diagonalZ ℓ) := by
  rw [diagonalZ,local_diagonal]
  ext A B
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.sum_apply,SlotHalf.z]
  by_cases h : A = B
  · subst B
    simp only [Matrix.diagonal_apply_eq]
    have he : ∀ a : Fin ℓ, (if ((configEquiv ℓ).symm A) (x,a) then (1:ℝ)/2 else -1/2) =
        (if a ∈ A x then (1:ℝ) else 0) - 1/2 := by
      intro a
      change (if decide (a ∈ A x) then (1:ℝ)/2 else -1/2) = _
      by_cases ha : a ∈ A x <;> simp [ha] <;> norm_num
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    simp [div_eq_mul_inv]
  · have hn : (configEquiv ℓ).symm A ≠ (configEquiv ℓ).symm B :=
      (configEquiv ℓ).symm.injective.ne h
    simp [Matrix.diagonal_apply_ne _ h,Matrix.diagonal_apply_ne _ hn]

end Heisenberg.SlotTensor

namespace Heisenberg.SlotHalf
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem cross_site_swaps (ℓ : ℕ) {x y : X} (hxy : x ≠ y) :
    (∑ a : Fin ℓ, ∑ b : Fin ℓ, SlotColor.matrix (Equiv.swap (x,a) (y,b))) =
      totalPlus ℓ x * totalMinus ℓ y + totalMinus ℓ x * totalPlus ℓ y +
      (2:ℝ) • (totalZ ℓ x * totalZ ℓ y) +
      ((ℓ:ℝ)^2/2) • (1:Matrix (SlotColor.Color (V:=X × Fin ℓ)) (SlotColor.Color (V:=X × Fin ℓ)) ℝ) := by
  have hh : ∀ a b : Fin ℓ, (x,a) ≠ (y,b) := fun _ _ => fun h => hxy (congrArg Prod.fst h)
  simp_rw [swap_spin (hh _ _),Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul,← Finset.smul_sum]
  simp only [totalPlus,totalMinus,totalZ]
  have hz : (∑ a : Fin ℓ, ∑ b : Fin ℓ, z (x,a)*z (y,b)) =
      (∑ a : Fin ℓ, z (x,a))*(∑ b : Fin ℓ, z (y,b)) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hz]
  congr 1
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,smul_smul]
  congr 1
  ring
end Heisenberg.SlotHalf

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bond_intertwines (ℓ : ℕ) {x y : X} (hxy : x ≠ y) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (slotBond ℓ x y) *
      tensor (fun _ : X => basis ℓ) =
        tensor (fun _ : X => basis ℓ) * spinBond ℓ x y := by
  let R := Matrix.reindexAlgEquiv ℝ ℝ (configEquiv (X:=X) ℓ)
  have hR (M : Matrix (SlotColor.Color (V:=X × Fin ℓ)) (SlotColor.Color (V:=X × Fin ℓ)) ℝ) :
      R M = Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) M := rfl
  have hmul (M N : Matrix (SlotColor.Color (V:=X × Fin ℓ)) (SlotColor.Color (V:=X × Fin ℓ)) ℝ) : R (M*N)=R M*R N := by
    exact map_mul R M N
  rw [← hR]
  rw [slotBond,SlotHalf.cross_site_swaps ℓ hxy]
  simp only [map_sub,map_smul,map_add,map_one,hmul]
  simp only [hR,SlotHalf.totalPlus,SlotHalf.totalMinus,SlotHalf.totalZ,slot_raising,slot_lowering,slot_z]
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.add_mul,Matrix.one_mul,
    Matrix.mul_assoc,raising_intertwines,lowering_intertwines,diagonal_intertwines]
  simp only [← Matrix.mul_assoc,raising_intertwines,lowering_intertwines,diagonal_intertwines]
  simp only [spinBond,Matrix.mul_add,Matrix.mul_smul]
  simp only [Matrix.mul_assoc]
  module

end Heisenberg.SlotTensor

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RectangularExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.TensorMatrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma pow_intertwines (A : Matrix m m ℝ) (B : Matrix n n ℝ) (V : Matrix m n ℝ)
    (h : A*V=V*B) (k : ℕ) : A^k*V=V*B^k := by
  induction k with
  | zero=> simp
  | succ k ih=>
    rw [pow_succ',Matrix.mul_assoc,ih,←Matrix.mul_assoc,h,Matrix.mul_assoc,←pow_succ']

theorem exp_intertwines (A : Matrix m m ℝ) (B : Matrix n n ℝ) (V : Matrix m n ℝ)
    (h : A*V=V*B) : NormedSpace.exp A*V=V*NormedSpace.exp B := by
  let L:=mulRightLinearMap m ℝ V
  let R:=mulLeftLinearMap n ℝ V
  have hL : Continuous L:=L.continuous_of_finiteDimensional
  have hR : Continuous R:=R.continuous_of_finiteDimensional
  have ha:=(NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) A).map L.toAddMonoidHom hL
  have hb:=(NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) B).map R.toAddMonoidHom hR
  have he : (fun k : ℕ=>L ((k.factorial:ℝ)⁻¹ • A^k))=
      (fun k : ℕ=>R ((k.factorial:ℝ)⁻¹ • B^k)) := by
    funext k
    change ((k.factorial:ℝ)⁻¹ • A^k)*V=V*((k.factorial:ℝ)⁻¹ • B^k)
    rw [Matrix.smul_mul,Matrix.mul_smul,pow_intertwines A B V h]
  change HasSum (fun k : ℕ=>L ((k.factorial:ℝ)⁻¹ • A^k)) (NormedSpace.exp A*V) at ha
  change HasSum (fun k : ℕ=>R ((k.factorial:ℝ)⁻¹ • B^k)) (V*NormedSpace.exp B) at hb
  rw [he] at ha
  exact ha.unique hb

end Heisenberg.TensorMatrix
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpectralTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.TensorMatrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma diagonal_function_intertwines (a : m → ℝ) (b : n → ℝ) (V : Matrix m n ℝ)
    (h : Matrix.diagonal a*V=V*Matrix.diagonal b) (f : ℝ → ℝ) :
    Matrix.diagonal (f ∘ a)*V=V*Matrix.diagonal (f ∘ b) := by
  ext i j
  have he:=congrFun (congrFun h i) j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at he ⊢
  by_cases hv : V i j=0
  · simp [hv]
  · have hab : a i=b j:=mul_right_cancel₀ hv (he.trans (mul_comm _ _))
    simp only [Function.comp_apply,hab,mul_comm]

omit [Fintype m] in
lemma diagonal_fintype_sum {I : Type*} [Fintype I] (f : I → m → ℝ) :
    (∑ i,Matrix.diagonal (f i))=Matrix.diagonal (fun j=>∑ i,f i j) := by
  ext a b
  by_cases h : a=b
  · subst b; simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply,Matrix.diagonal_apply_ne _ h]

theorem trace_exp_compression (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (V : Matrix m n ℝ) (hV : V.transpose*V=1) (hAB : A*V=V*B)
    (D : Matrix m m ℝ) (E : Matrix n n ℝ) (hDE : D*V=V*E) :
    Matrix.trace (V*V.transpose*NormedSpace.exp A*D)=Matrix.trace (NormedSpace.exp B*E) := by
  rw [Matrix.mul_assoc,Matrix.mul_assoc,Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [hDE,←Matrix.mul_assoc (NormedSpace.exp A) V E,exp_intertwines A B V hAB]
  simp only [←Matrix.mul_assoc,hV,Matrix.one_mul]

end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]

lemma total_diagonal_intertwines (ℓ : ℕ) :
    Matrix.diagonal (configMagnetization (X:=X) ℓ)*tensor (fun _ : X=>basis ℓ)=
      tensor (fun _ : X=>basis ℓ)*Matrix.diagonal (physicalMagnetization (X:=X) ℓ) := by
  have hh:=congrArg (fun f : X → Matrix (X → Config ℓ) (X → Level ℓ) ℝ=>∑ x,f x)
    (funext (diagonal_intertwines (X:=X) ℓ))
  simp only [SpinSlots.diagonalZ,physicalZ,local_diagonal,←Matrix.sum_mul,←Matrix.mul_sum,
    diagonal_fintype_sum] at hh
  exact hh

omit [DecidableEq X] in
lemma color_config_mag (ℓ : ℕ) (A : X → Config ℓ) :
    SlotColor.magnetization ((configEquiv ℓ).symm A)=configMagnetization ℓ A := by
  unfold SlotColor.magnetization configMagnetization
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have he (a : Fin ℓ) : (if ((configEquiv ℓ).symm A) (x,a) then (1:ℝ)/2 else -1/2)=
      (if a∈A x then (1:ℝ) else 0)-1/2 := by
    change (if decide (a∈A x) then (1:ℝ)/2 else -1/2)=_
    by_cases ha : a∈A x <;> simp [ha] <;> norm_num
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp [div_eq_mul_inv]

end Heisenberg.SlotTensor
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PhysicalClock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]

lemma sum_clock_pair (ℓ : ℕ) (x y : X) :
    (∑ a : Fin ℓ,∑ b : Fin ℓ,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (x,a) (y,b))-1))=
      slotBond ℓ x y-((ℓ:ℝ)^2/4) • 1 := by
  simp only [smul_sub,Finset.sum_sub_distrib,←Finset.smul_sum,slotBond]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [←Nat.cast_smul_eq_nsmul ℝ,←Nat.cast_smul_eq_nsmul ℝ,smul_smul,smul_smul]
  module

lemma generator_intertwines (R : X → X → Prop) (hR : ∀ x y,R x y → x≠y) (ℓ : ℕ) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (clockGenerator R ℓ)*tensor (fun _ : X=>basis ℓ)=
      tensor (fun _ : X=>basis ℓ)*spinGenerator R ℓ := by
  let r:=Matrix.reindexAlgEquiv ℝ ℝ (configEquiv (X:=X) ℓ)
  have hr (A : Matrix ((X×Fin ℓ) → Bool) ((X×Fin ℓ) → Bool) ℝ) :
      r A=Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) A:=rfl
  rw [←hr]
  have he : clockGenerator R ℓ=∑ e : SiteEdges R,∑ a : Fin ℓ,∑ b : Fin ℓ,
      (1/2:ℝ) • (SlotColor.matrix (Equiv.swap (e.val.1,a) (e.val.2,b))-1) := by
    rw [clockGenerator,←(clockEdgeEquiv R ℓ).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rfl
  rw [he]
  simp only [sum_clock_pair,map_sum,map_sub,map_smul,map_one,Matrix.sum_mul,Matrix.sub_mul,
    Matrix.smul_mul,Matrix.one_mul,spinGenerator,Matrix.mul_sum,Matrix.mul_sub,
    Matrix.mul_smul,Matrix.mul_one]
  apply Finset.sum_congr rfl
  intro e _
  rw [hr,bond_intertwines ℓ (hR _ _ e.property)]

end Heisenberg.SlotTensor
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeOnMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

open scoped Matrix Matrix.Norms.Operator
namespace Heisenberg.Heat
open MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma _root_.OAI.Heisenberg.MatrixContraction.DoublySubstochastic.one : DoublySubstochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num
  · intro i; simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]; norm_num
  · intro j; simp only [Matrix.one_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]; norm_num

lemma _root_.OAI.Heisenberg.MatrixContraction.DoublySubstochastic.pow {P : Matrix V V ℝ} (hP : DoublySubstochastic P) (n : ℕ) :
    DoublySubstochastic (P ^ n) := by
  induction n with
  | zero => simpa using DoublySubstochastic.one (V := V)
  | succ n ih => simpa only [pow_succ] using ih.mul hP

lemma exp_scalar (a : ℝ) :
    NormedSpace.exp (a • (1 : Matrix V V ℝ)) = Real.exp a • 1 := by
  have result := (NormedSpace.algebraMap_exp_comm (𝔸 := Matrix V V ℝ) a).symm
  simp only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] at result
  convert! result

lemma uniformization (P : Matrix V V ℝ) (a : ℝ) :
    NormedSpace.exp (a • (P - 1)) = Real.exp (-a) • NormedSpace.exp (a • P) := by
  have he : a • (P - 1) = (-a) • (1 : Matrix V V ℝ) + a • P := by
    simp only [smul_sub, neg_smul]; abel
  rw [he, Matrix.exp_add_of_commute, exp_scalar, smul_mul_assoc, one_mul]
  exact ((Commute.one_left P).smul_left (-a)).smul_right a

lemma exp_series (P : Matrix V V ℝ) (a : ℝ) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * a ^ n) • P ^ n)
      (NormedSpace.exp (a • P)) := by
  have result := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • P)
  simp only [smul_pow, smul_smul] at result
  convert! result

lemma exp_sub_identity_substochastic {P : Matrix V V ℝ}
    (hP : DoublySubstochastic P) {a : ℝ} (ha : 0 ≤ a) :
    DoublySubstochastic (NormedSpace.exp (a • (P - 1))) := by
  rw [uniformization]
  have hs := exp_series P a
  have hw : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * a ^ n) (Real.exp a) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a)
  have hn (n : ℕ) : 0 ≤ (n.factorial : ℝ)⁻¹ * a ^ n := by positivity
  have hnorm : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  constructor
  · intro i j
    change 0 ≤ Real.exp (-a) * NormedSpace.exp (a • P) i j
    apply mul_nonneg (Real.exp_pos _).le
    exact HasSum.nonneg (fun n => by
      change 0 ≤ ((n.factorial : ℝ)⁻¹ * a ^ n) * (P ^ n) i j
      exact mul_nonneg (hn n) ((hP.pow n).nonneg i j)) ((entry i j).hasSum hs)
  · intro i
    have hb : (∑ j, NormedSpace.exp (a • P) i j) ≤ Real.exp a := by
      let row : Matrix V V ℝ →L[ℝ] ℝ := ∑ j : V, entry i j
      have hr := row.hasSum hs
      simp only [row, sum_apply, entry_apply, Matrix.smul_apply, smul_eq_mul] at hr
      apply hasSum_le (fun n => ?_) hr hw
      change (∑ j, ((n.factorial : ℝ)⁻¹ * a ^ n) * (P ^ n) i j) ≤ _
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right (hn n) ((hP.pow n).row i)
    change (∑ j, Real.exp (-a) * NormedSpace.exp (a • P) i j) ≤ 1
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq hnorm
  · intro j
    have hb : (∑ i, NormedSpace.exp (a • P) i j) ≤ Real.exp a := by
      let col : Matrix V V ℝ →L[ℝ] ℝ := ∑ i : V, entry i j
      have hr := col.hasSum hs
      simp only [col, sum_apply, entry_apply, Matrix.smul_apply, smul_eq_mul] at hr
      apply hasSum_le (fun n => ?_) hr hw
      change (∑ i, ((n.factorial : ℝ)⁻¹ * a ^ n) * (P ^ n) i j) ≤ _
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right (hn n) ((hP.pow n).col j)
    change (∑ i, Real.exp (-a) * NormedSpace.exp (a • P) i j) ≤ 1
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq hnorm

lemma uniformized_substochastic {G : Matrix V V ℝ} (hG : SubMarkovGenerator G)
    {c : ℝ} (hc : 0 < c) (hdiag : ∀ i, -G i i ≤ c) :
    DoublySubstochastic (1 + c⁻¹ • G) := by
  constructor
  · intro i j
    change 0 ≤ (1 : Matrix V V ℝ) i j + c⁻¹ * G i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.one_apply_eq]
      have : -G i i / c ≤ 1 := (div_le_iff₀ hc).mpr (by simpa using hdiag i)
      rw [neg_div] at this
      rw [mul_comm, ← div_eq_mul_inv]
      linarith
    · simp only [Matrix.one_apply_ne h, zero_add]
      exact mul_nonneg (inv_nonneg.mpr hc.le) (hG.offdiag i j h)
  · intro i
    change (∑ j, ((1 : Matrix V V ℝ) i j + c⁻¹ * G i j)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Matrix.one_apply, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, add_le_iff_nonpos_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le) (hG.row i)
  · intro j
    change (∑ i, ((1 : Matrix V V ℝ) i j + c⁻¹ * G i j)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Matrix.one_apply, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, add_le_iff_nonpos_right]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le) (hG.col j)

theorem kernel_substochastic {G : Matrix V V ℝ} (hG : SubMarkovGenerator G)
    {t : ℝ} (ht : 0 ≤ t) : DoublySubstochastic (kernel G t) := by
  let c : ℝ := 1 + ∑ i, |G i i|
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hd (i : V) : -G i i ≤ c := by
    have h := Finset.single_le_sum (fun j _ => abs_nonneg (G j j)) (Finset.mem_univ i)
    have := neg_le_abs (G i i)
    dsimp [c]; linarith
  have hp := uniformized_substochastic hG hc hd
  have he : (t * c) • ((1 + c⁻¹ • G) - 1) = t • G := by
    rw [add_sub_cancel_left, smul_smul]
    congr 1
    field_simp
  simpa only [he, kernel] using exp_sub_identity_substochastic hp (mul_nonneg ht hc.le)

end Heisenberg.Heat

noncomputable section
open Filter Topology
namespace ExchangeLimit

variable {E : Type*} [NormedRing E] [NormOneClass E]

lemma contraction_power_difference (a b : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a^n-b^n‖ ≤ n * ‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : ‖b^n‖ ≤ 1 := (norm_pow_le b n).trans (pow_le_one₀ (norm_nonneg _) hb)
    have he : a^(n+1)-b^(n+1) = a*(a^n-b^n)+(a-b)*b^n := by
      rw [pow_succ',pow_succ']; noncomm_ring
    rw [he]
    calc
      _ ≤ ‖a‖*‖a^n-b^n‖+‖a-b‖*‖b^n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖a^n-b^n‖ + ‖a-b‖ := add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) ha)
        (mul_le_of_le_one_right (norm_nonneg _) hbn)
      _ ≤ (n:ℝ)*‖a-b‖+‖a-b‖ := by linarith
      _ = _ := by push_cast; ring

end ExchangeLimit

namespace Heisenberg.ExchangeMatrix
open MatrixContraction Heat
open scoped Matrix Matrix.Norms.Operator NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma substochastic_norm_le {P : Matrix V V ℝ} (hP : DoublySubstochastic P) : ‖P‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup fun i : V => ∑ j : V, ‖P i j‖₊ : ℝ≥0) : ℝ) ≤ (1:ℝ≥0)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum,coe_nnnorm,Real.norm_eq_abs,abs_of_nonneg (hP.nonneg i _),
    NNReal.coe_one] using hP.row i

lemma permutationMatrix_substochastic (σ : Equiv.Perm V) :
    DoublySubstochastic (permutationMatrix σ) := by
  unfold permutationMatrix
  simpa only [Option.some.injEq] using of_partial_permutation (fun i => some (σ i)) (fun i j a hi hj =>
    σ.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm))

lemma clockGenerator_subMarkov (L : List (Clock V)) : SubMarkovGenerator (clockGenerator L) := by
  induction L with
  | nil => exact ⟨by simp [clockGenerator],by simp [clockGenerator],by simp [clockGenerator]⟩
  | cons e L ih =>
    have hp := permutationMatrix_substochastic e.2
    constructor
    · intro i j hij
      change 0 ≤ (e.1:ℝ) * (permutationMatrix e.2 i j - (1:Matrix V V ℝ) i j) + clockGenerator L i j
      rw [Matrix.one_apply_ne hij,sub_zero]
      exact add_nonneg (mul_nonneg e.1.property (hp.nonneg i j)) (ih.offdiag i j hij)
    · intro i
      change (∑ j, ((e.1:ℝ) * (permutationMatrix e.2 i j - (1:Matrix V V ℝ) i j) + clockGenerator L i j)) ≤ 0
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,permutationMatrix_row]
      simpa [Matrix.one_apply] using ih.row i
    · intro j
      change (∑ i, ((e.1:ℝ) * (permutationMatrix e.2 i j - (1:Matrix V V ℝ) i j) + clockGenerator L i j)) ≤ 0
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,permutationMatrix_col]
      simpa [Matrix.one_apply] using ih.col j

end Heisenberg.ExchangeMatrix
end

noncomputable section
open Filter Topology
namespace ExchangeLimit
variable {E : Type*} [NormedRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E]
theorem local_contraction_product_limit (f : ℝ → E) (D : E)
    (h0 : f 0 = 1) (hd : HasDerivAt f D 0)
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), 0 ≤ t → ‖f t‖ ≤ 1)
    (hD : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • D)‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (f (t/(n+1)))^(n+1)) atTop (nhds (NormedSpace.exp (t • D))) := by
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let g : ℝ → E := fun s => f s - NormedSpace.exp (s • D)
  have hg0 : g 0 = 0 := by simp [g,h0]
  have hgd : HasDerivAt g 0 0 := by
    have h := hd.sub (hasDerivAt_exp_smul_const D (0:ℝ))
    change HasDerivAt g _ _ at h
    simpa only [zero_smul,NormedSpace.exp_zero,one_mul,sub_self] using h
  have hs : Tendsto (fun n : ℕ => t/(n+1:ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have herr : Tendsto (fun n : ℕ => ((n+1:ℝ)) * ‖g (t/(n+1:ℝ))‖) atTop (nhds 0) := by
    by_cases ht0 : t = 0
    · simp [ht0,hg0]
    · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hsl := hgd.tendsto_slope_zero
      have hsn : Tendsto (fun n : ℕ => t/(n+1:ℝ)) atTop (𝓝[≠] (0:ℝ)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨hs, Filter.Eventually.of_forall ?_⟩
        intro n
        simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
        exact div_ne_zero ht0 (by positivity)
      have hh := (hsl.comp hsn).norm.const_mul t
      convert hh using 1
      · funext n
        simp only [Function.comp_apply,hg0,sub_zero,zero_add,norm_smul,Real.norm_eq_abs]
        rw [abs_of_pos (inv_pos.mpr (div_pos hpos (by positivity)))]
        field_simp
      · simp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ herr
  filter_upwards [hs.eventually hf] with n hn
  have hpn : 0 < (n+1:ℝ) := by positivity
  have hexp : (NormedSpace.exp ((t/(n+1:ℝ)) • D))^(n+1) = NormedSpace.exp (t • D) := by
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    congr 1
    push_cast
    field_simp
  rw [← hexp]
  simpa only [g,Nat.cast_add,Nat.cast_one] using contraction_power_difference
    (f (t/(n+1:ℝ))) (NormedSpace.exp ((t/(n+1:ℝ)) • D))
    (hn (div_nonneg ht hpn.le)) (hD _ (div_nonneg ht hpn.le)) (n+1)

end ExchangeLimit

namespace Heisenberg.ExchangeMatrix
open MatrixContraction Heat
open scoped Matrix Matrix.Norms.Operator NNReal
variable {V : Type*} [fV : Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma linearStep_zero (r : ℝ) (σ : Equiv.Perm V) : linearStep r σ 0=1 := by
  simp [linearStep]

lemma linearStep_substochastic (r : ℝ) (σ : Equiv.Perm V) (t : ℝ)
    (h0 : 0≤r*t) (h1 : r*t≤1) : DoublySubstochastic (linearStep r σ t) := by
  have hh:=weighted_average (V:=V) (fun b : Bool=>if b then 1-r*t else r*t)
    (fun b=>by cases b; exact h0; exact sub_nonneg.mpr h1)
    (by simp) (fun b : Bool=>if b then 1 else permutationMatrix σ)
    (fun b=>by cases b; exact permutationMatrix_substochastic σ; exact DoublySubstochastic.one)
  change DoublySubstochastic (fun i j=>(1-r*t)*(1:Matrix V V ℝ) i j+(r*t)*permutationMatrix σ i j)
  simpa only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false] using hh

include fV in
lemma linearStep_derivative (r : ℝ) (σ : Equiv.Perm V) :
    HasDerivAt (linearStep r σ) (r • (permutationMatrix σ-1)) 0 := by
  have hd:=(hasDerivAt_id (0:ℝ)).const_mul r
  have hh:=((hasDerivAt_const (0:ℝ) 1).sub hd |>.smul_const (1:Matrix V V ℝ)).add
    (hd.smul_const (permutationMatrix σ))
  convert hh using 1 <;> try dsimp [linearStep]
  all_goals try simp only [mul_one,zero_sub,smul_sub,neg_smul]
  all_goals first | rfl | abel

lemma linearMesh_zero (L : List (Clock V)) : linearMesh L 0=1 := by
  induction L with
  | nil=>rfl
  | cons e L ih=>simp [linearMesh,linearStep_zero,ih]

lemma linearMesh_derivative (L : List (Clock V)) : HasDerivAt (linearMesh L) (clockGenerator L) 0 := by
  induction L with
  | nil=>exact hasDerivAt_const _ _
  | cons e L ih=>
    have hh:=(linearStep_derivative (e.1:ℝ) e.2).fun_mul ih
    change HasDerivAt (linearMesh (e::L)) _ _ at hh
    simpa only [clockGenerator,linearMesh_zero,linearStep_zero,mul_one,one_mul] using hh

lemma linearMesh_locally_substochastic (L : List (Clock V)) :
    ∀ᶠ t in 𝓝 (0:ℝ),0≤t → DoublySubstochastic (linearMesh L t) := by
  induction L with
  | nil=>exact Filter.Eventually.of_forall (fun _ _=>DoublySubstochastic.one)
  | cons e L ih=>
    have hh : ∀ᶠ t in 𝓝 (0:ℝ),(e.1:ℝ)*t≤1 := by
      have hc : ContinuousAt (fun t : ℝ=>(e.1:ℝ)*t) 0:=continuousAt_const.mul continuousAt_id
      exact (hc.eventually (eventually_le_nhds (by simp : (e.1:ℝ)*0<1)))
    filter_upwards [ih,hh] with t ht hrate
    intro h0
    exact (linearStep_substochastic _ _ _ (mul_nonneg e.1.property h0) hrate).mul (ht h0)

theorem linear_mesh_converges [Nonempty V] (L : List (Clock V)) (t : ℝ) (ht : 0≤t) :
    Tendsto (fun n : ℕ=>(linearMesh L (t/(n+1:ℝ)))^(n+1)) atTop
      (𝓝 (NormedSpace.exp (t • clockGenerator L))) := by
  apply ExchangeLimit.local_contraction_product_limit _ _ (linearMesh_zero L) (linearMesh_derivative L)
    ?_ (fun u hu=>substochastic_norm_le (kernel_substochastic (clockGenerator_subMarkov L) hu)) t ht
  filter_upwards [linearMesh_locally_substochastic L] with u hu
  intro h0
  exact substochastic_norm_le (hu h0)

end Heisenberg.ExchangeMatrix
end
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ColorClockLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator NNReal
open Filter Topology
namespace Heisenberg.Surface
open ExchangeMatrix MeshPair
variable {V : Type} [Fintype V]

lemma color_matrix_permutation (π : Equiv.Perm V) :
    SlotColor.matrix π=permutationMatrix (SlotColor.permute π) := rfl

lemma color_prefix_linear (a b : ℕ → V) (q : ℕ) (δ : ℝ) :
    prefixMatrix (fun j=>colorCoin (a j) (b j) (δ/2)) q=linearMesh (colorClocks a b q) δ := by
  induction q with
  | zero=>rfl
  | succ q ih=>
    rw [prefixMatrix,ih,colorClocks,linearMesh]
    congr 1
    change (1-δ/2) • (1:Matrix (V → Bool) (V → Bool) ℝ)+(δ/2) •
      permutationMatrix (SlotColor.permute (Equiv.swap (a q) (b q)))=
      (1-(1/2:ℝ)*δ) • 1+((1/2:ℝ)*δ) • permutationMatrix (SlotColor.permute (Equiv.swap (a q) (b q)))
    rw [show δ/2=(1/2:ℝ)*δ by ring]

lemma color_generator (a b : ℕ → V) (q : ℕ) :
    clockGenerator (colorClocks a b q)=∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a j) (b j))-1) := by
  induction q with
  | zero=>simp [colorClocks,clockGenerator]
  | succ q ih=>
    rw [colorClocks,clockGenerator,ih,Finset.sum_range_succ]
    rw [color_matrix_permutation]
    exact add_comm _ _

theorem color_clock_limit (a b : ℕ → V) (q : ℕ) {t : ℝ} (ht : 0≤t) :
    Tendsto (fun n : ℕ=>(prefixMatrix (fun j=>colorCoin (a j) (b j) ((t/(n+1:ℝ))/2)) q)^(n+1)) atTop
      (𝓝 (NormedSpace.exp (t • ∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a j) (b j))-1)))) := by
  simp_rw [color_prefix_linear]
  rw [←color_generator]
  exact linear_mesh_converges _ _ ht

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PeriodicCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface

lemma periodic_count (k Q : ℕ) (P : ℕ → Prop) :
    (Finset.univ.filter (fun j : Fin (k*Q)=>P (j.val%Q))).card=
      k*(Finset.univ.filter (fun j : Fin Q=>P j.val)).card := by
  simp only [Finset.card_filter]
  have hh:=Fintype.sum_equiv (finProdFinEquiv (m:=k) (n:=Q))
    (fun j : Fin k × Fin Q=>if P j.2.val then (1:ℕ) else 0)
    (fun j : Fin (k*Q)=>if P (j.val%Q) then (1:ℕ) else 0)
    (fun j=>by simp [finProdFinEquiv,Nat.mod_eq_of_lt j.2.isLt])
  rw [←hh]
  rw [Fintype.sum_prod_type]
  trans ∑ _ : Fin k,∑ j : Fin Q,if P j.val then (1:ℕ) else 0
  · congr! 20
  · simp

lemma truncated_count (q Q : ℕ) (hq : q≤Q) (P : ℕ → Prop) :
    (Finset.univ.filter (fun j : Fin Q=>j.val<q ∧ P j.val)).card=
      ((Finset.range q).filter P).card := by
  apply Finset.card_nbij (fun j : Fin Q=>j.val)
  · intro j hj
    simpa only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_range] using hj
  · intro i _ j _ h; exact Fin.ext h
  · intro j hj
    have h:=Finset.mem_filter.mp hj
    exact ⟨⟨j,lt_of_lt_of_le (Finset.mem_range.mp h.1) hq⟩,by simpa using h,rfl⟩

lemma periodic_truncated_count (k q Q : ℕ) (hq : q≤Q) (P : ℕ → Prop) :
    (Finset.univ.filter (fun j : Fin (k*Q)=>j.val%Q<q ∧ P (j.val%Q))).card=
      k*((Finset.range q).filter P).card := by
  trans k*(Finset.univ.filter (fun j : Fin Q=>j.val<q ∧ P j.val)).card
  · convert periodic_count k Q (fun j=>j<q ∧ P j) using 1 <;> congr! 10
  · rw [truncated_count q Q hq]

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeshRoom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical
open Filter Topology
namespace Heisenberg.Surface
lemma mesh_room {s t δ : ℝ} (hs : 0 ≤ s) (hδ : 0<δ) (htδ : 2*(s+δ) ≤ t)
    (k Q : ℕ) (hk : δ*(k+1:ℝ)=t) :
    2*(⌊s/δ⌋₊+1)*Q≤(k+1)*Q := by
  apply Nat.mul_le_mul_right
  have hf:=Nat.floor_le (div_nonneg hs hδ.le)
  have hh:=mul_le_mul_of_nonneg_right hf hδ.le
  rw [div_mul_cancel₀ _ hδ.ne'] at hh
  have ht : (2:ℝ)*((⌊s/δ⌋₊:ℝ)+1)≤(k+1:ℝ) := by nlinarith
  exact_mod_cast ht

lemma mesh_step_tendsto (t : ℝ) : Tendsto (fun k : ℕ=>t/(k+1:ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

lemma eventually_mesh_room {s t : ℝ} (hs : 0 ≤ s) (ht : 2*s < t) (Q : ℕ) :
    ∀ᶠ k : ℕ in atTop,2*(⌊s/(t/(k+1:ℝ))⌋₊+1)*Q≤(k+1)*Q := by
  have ht0 : 0<t:=by linarith
  have hh : ∀ᶠ k : ℕ in atTop,t/(k+1:ℝ)≤(t-2*s)/2 :=
    (mesh_step_tendsto t).eventually (eventually_le_nhds (by linarith))
  filter_upwards [hh] with k hk
  apply mesh_room (t := t) (δ := t/(k+1:ℝ)) hs (div_pos ht0 (by positivity)) (by linarith) k Q
  field_simp

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CompletedSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open Heisenberg.Geometry LatticeRegular SpatialFrame MeshPair

lemma trace_tendsto {V I : Type*} [Fintype V] {l : Filter I} {f : I → Matrix V V ℝ}
    {M : Matrix V V ℝ} (hf : Tendsto f l (𝓝 M)) :
    Tendsto (fun i=>Matrix.trace (f i)) l (𝓝 (Matrix.trace M)) := by
  exact tendsto_finsetSum _ (fun i _=>(Heat.entry i i).continuous.tendsto M |>.comp hf)

attribute [local instance] OAI.completedSurfaceDecEq
theorem completed_surface_bound (d : ℕ) (hd : 2≤d) (B : Type) [Fintype B] [Nonempty B] :
    ∃ s : ℝ,0<s ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : ℕ → Slots (B:=B) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
        (c : ℕ) (u v : ℕ → Slots (B:=B) Λ)
        (_huv : ∀ j,(u j).1.val=(v j).1.val)
        (_hF : F⊆Λ) (_hf : ∀ z∈F,∀ w,Step z w → w∈Λ) (t : ℝ) (_ht : 2*s<t),
        let Z:=((Finset.univ.filter (fun v : Slots (B:=B) Λ=>v.1.val∉F)).card:ℝ)
        let J:=(((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card:ℝ)
        let E:=NormedSpace.exp (t • ∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1))
        let U:=prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c
        Real.exp (-(Real.log 2)*(Z+2*t*J))/2*Matrix.trace (U*E)≤
          Matrix.trace (U*E*tailProjection (Slots (B:=B) Λ)) := by
  obtain ⟨s,hs,hbound⟩:=mesh_matrix_surface d hd B
  refine ⟨s,hs,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀ c u v huv hF hf t ht Z J E U
  let Q:=q+c
  have hq : 0<q:=NeZero.pos q
  have hQ : 0<Q:=by dsimp [Q]; omega
  have ht0 : 0<t:=by linarith
  let A : ℝ → Matrix (Slots (B:=B) Λ → Bool) (Slots (B:=B) Λ → Bool) ℝ:=
    fun δ=>prefixMatrix (fun j=>colorCoin (a₀ j) (b₀ j) (δ/2)) q
  have hA : Tendsto (fun k : ℕ=>U*(A (t/(k+1:ℝ)))^(k+1)) atTop (𝓝 (U*E)) :=
    tendsto_const_nhds.mul (color_clock_limit a₀ b₀ q ht0.le)
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (trace_tendsto hA))
    (trace_tendsto (hA.mul_const (tailProjection (Slots (B:=B) Λ))))
  have hδevent:=hbound Λ F hΛ q edge a₀ b₀ ha₀ hb₀
  have hδsmall : ∀ᶠ k : ℕ in atTop,t/(k+1:ℝ)≤2 :=
    (mesh_step_tendsto t).eventually (eventually_le_nhds (by norm_num))
  filter_upwards [(mesh_step_tendsto t).eventually hδevent,hδsmall,eventually_mesh_room hs.le ht Q] with k hk hk2 hroom
  let δ:=t/(k+1:ℝ)
  have hδ : 0<δ:=div_pos ht0 (by positivity)
  let a : Fin ((k+1)*Q) → Slots (B:=B) Λ:=fun j=>completedEndpoint a₀ u q c j.val
  let b : Fin ((k+1)*Q) → Slots (B:=B) Λ:=fun j=>completedEndpoint b₀ v q c j.val
  let rates : Fin ((k+1)*Q) → ℝ:=fun j=>completedRate δ q c k j.val
  have hab : ∀ j : Fin ((k+1)*Q),j.val%Q<q → a j=a₀ (j.val%Q) ∧ b j=b₀ (j.val%Q) := by
    intro j hj
    simp only [a,b,completedEndpoint,show q+c=Q from rfl,ite_eq_left hj,and_self]
  have hsite : ∀ j : Fin ((k+1)*Q),q≤j.val%Q → (a j).1.val=(b j).1.val := by
    intro j hj
    simp only [a,b,completedEndpoint,show q+c=Q from rfl,ite_eq_right (by omega : ¬j.val%Q<q)]
    exact huv _
  have hrate : ∀ j : Fin ((k+1)*Q),j.val%Q<q → rates j=δ/2 := by
    intro j hj
    simp only [rates,completedRate,show q+c=Q from rfl,ite_eq_left hj]
  have hh:=hk hδ ((k+1)*Q) Q (Nat.mul_pos (by omega) hQ) hQ (by dsimp [Q]; omega)
    (dvd_mul_left Q (k+1)) a b hab hsite rates
    (fun j=>completed_rate_bounds q c k j.val hδ.le hk2) hrate hF hf hroom
  let K:=Finset.univ.filter (fun j : Fin ((k+1)*Q)=>j.val%Q<q ∧ ((a j).1.val∉F ∨ (b j).1.val∉F))
  have hK : K.card=(k+1)*((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card := by
    have hset : K=Finset.univ.filter (fun j : Fin ((k+1)*Q)=>j.val%Q<q ∧
        ((a₀ (j.val%Q)).1.val∉F ∨ (b₀ (j.val%Q)).1.val∉F)) := by
      ext j
      simp only [K,Finset.mem_filter,Finset.mem_univ,true_and]
      by_cases hj : j.val%Q<q
      · rw [(hab j hj).1,(hab j hj).2]
      · simp only [hj,false_and]
    rw [hset]
    convert periodic_truncated_count (k+1) q Q (by dsimp [Q]; omega)
      (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F) using 1 <;> congr! 10
  have he : 2*δ*(K.card:ℝ)=2*t*J := by
    rw [hK,Nat.cast_mul]
    dsimp only [δ,J]
    push_cast
    field_simp
  have hprod : Serial.product ((k+1)*Q) (fun j=>colorCoin (a j) (b j) (rates j))=U*(A δ)^(k+1) := by
    exact completed_product a₀ b₀ u v q c k δ
  change Real.exp (-(Real.log 2)*(Z+2*δ*(K.card:ℝ)))/2*
    Matrix.trace (Serial.product ((k+1)*Q) (fun j=>colorCoin (a j) (b j) (rates j)))≤_ at hh
  rw [he,hprod] at hh
  exact hh

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_OnsiteSwaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Onsite

theorem swap_factorization {V X : Type*} [Fintype V] (loc : V → X)
    (π : Equiv.Perm V) (hπ : ∀ v,loc (π v)=loc v) :
    ∃ L : List (V×V),(∀ e∈L,loc e.1=loc e.2) ∧
      (L.map (fun e=>Equiv.swap e.1 e.2)).prod=π := by
  classical
  generalize hn : π.support.card=n
  induction n using Nat.strong_induction_on generalizing π with
  | h n ih=>
    by_cases hp : π=1
    · subst π; exact ⟨[],by simp,by simp⟩
    obtain ⟨a,ha⟩ : ∃ a,π a≠a := by
      by_contra hf
      push Not at hf
      apply hp
      ext a
      exact hf a
    let τ:=Equiv.swap a (π a)*π
    have hτ : ∀ v,loc (τ v)=loc v := by
      intro v
      change loc (Equiv.swap a (π a) (π v))=loc v
      by_cases h1 : π v=a
      · rw [h1,Equiv.swap_apply_left]
        exact (hπ a).trans ((congrArg loc h1).symm.trans (hπ v))
      by_cases h2 : π v=π a
      · have hv : v=a:=π.injective h2
        subst v
        simp only [Equiv.swap_apply_right]
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hπ v
    obtain ⟨L,hL,hprod⟩:=ih τ.support.card (by simpa [hn] using Equiv.Perm.card_support_swap_mul ha) τ hτ rfl
    refine ⟨(a,π a)::L,?_,?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl|he
      · exact (hπ a).symm
      · exact hL e he
    · simp only [List.map_cons,List.prod_cons,hprod,τ]
      rw [←mul_assoc,Equiv.swap_mul_self,one_mul]

end Heisenberg.Onsite
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CompletionFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open MeshPair
variable {V X : Type} [Fintype V] [Nonempty V]

lemma list_completion (loc : V → X) (L : List (V×V))
    (hL : ∀ e∈L,loc e.1=loc e.2) :
    ∃ (c : ℕ) (u v : ℕ → V),(∀ j,loc (u j)=loc (v j)) ∧
      prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c=
        SlotColor.matrix ((L.map (fun e=>Equiv.swap e.1 e.2)).prod) := by
  classical
  induction L with
  | nil=>
    refine ⟨0,fun _=>Classical.arbitrary V,fun _=>Classical.arbitrary V,fun _=>rfl,?_⟩
    simp only [prefixMatrix,List.map_nil,List.prod_nil,SlotColor.matrix_one]
  | cons e L ih=>
    obtain ⟨c,u,v,huv,hprod⟩:=ih (fun f hf=>hL f (List.mem_cons_of_mem e hf))
    let u' : ℕ → V:=fun j=>if j=c then e.1 else u j
    let v' : ℕ → V:=fun j=>if j=c then e.2 else v j
    refine ⟨c+1,u',v',?_,?_⟩
    · intro j
      by_cases hj : j=c
      · simpa only [u',v',ite_eq_left hj] using hL e (List.mem_cons_self ..)
      · simpa only [u',v',ite_eq_right hj] using huv j
    · rw [prefixMatrix]
      have hp : prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u' j) (v' j))) c=
          prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c := by
        apply Serial.prefix_congr
        intro j hj
        simp only [u',v',ite_eq_right (show j≠c by omega)]
      rw [hp,hprod]
      simp only [u',v',ite_eq_left rfl,List.map_cons,List.prod_cons,SlotColor.matrix_mul]

theorem completion_factorization (loc : V → X) (π : Equiv.Perm V)
    (hπ : ∀ v,loc (π v)=loc v) :
    ∃ (c : ℕ) (u v : ℕ → V),(∀ j,loc (u j)=loc (v j)) ∧
      prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c=SlotColor.matrix π := by
  obtain ⟨L,hL,he⟩:=Onsite.swap_factorization loc π hπ
  obtain ⟨c,u,v,h,hp⟩:=list_completion loc L hL
  exact ⟨c,u,v,h,by simpa only [he] using hp⟩

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SymmetrizedSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
attribute [-instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open Heisenberg.Geometry LatticeRegular SpatialFrame MeshPair

attribute [local instance] OAI.symSurfaceDecEq
lemma colorSymmetrizer_reindex (X : Type) [Fintype X] (ℓ : ℕ) :
    Matrix.reindex (SlotTensor.configEquiv ℓ) (SlotTensor.configEquiv ℓ) (colorSymmetrizer X ℓ)=
      TensorMatrix.tensor (fun _ : X=>SpinSlots.basis ℓ) *
        (TensorMatrix.tensor (fun _ : X=>SpinSlots.basis ℓ)).transpose := by
  rw [← SlotTensor.symmetrizer]
  ext A B
  simp only [colorSymmetrizer,SlotTensor.matrix,Matrix.reindex_apply,Matrix.submatrix_apply,
    Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  congr! 20

theorem symmetrized_surface_bound (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ] :
    ∃ s : ℝ,0<s ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=Fin ℓ) Step Λ) (a₀ b₀ : ℕ → Slots (B:=Fin ℓ) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
        (_hF : F⊆Λ) (_hf : ∀ z∈F,∀ w,Step z w → w∈Λ) (t : ℝ) (_ht : 2*s<t),
        let Z:=((Finset.univ.filter (fun v : Slots (B:=Fin ℓ) Λ=>v.1.val∉F)).card:ℝ)
        let J:=(((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card:ℝ)
        let E:=NormedSpace.exp (t • ∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1))
        let P:=colorSymmetrizer Λ ℓ
        Real.exp (-(Real.log 2)*(Z+2*t*J))/2*Matrix.trace (P*E)≤
          Matrix.trace (P*E*tailProjection (Slots (B:=Fin ℓ) Λ)) := by
  obtain ⟨s,hs,hbound⟩:=completed_surface_bound d hd (Fin ℓ)
  refine ⟨s,hs,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀ hF hf t ht Z J E P
  let : Nonempty Λ:=Finset.Nonempty.coe_sort hΛ
  have hh (κ : Λ → Equiv.Perm (Fin ℓ)) :
      Real.exp (-(Real.log 2)*(Z+2*t*J))/2*Matrix.trace (SlotColor.matrix (SlotTensor.fiberPerm κ)*E)≤
      Matrix.trace (SlotColor.matrix (SlotTensor.fiberPerm κ)*E*tailProjection (Slots (B:=Fin ℓ) Λ)) := by
    obtain ⟨c,u,v,huv,hp⟩:=completion_factorization (fun p : Slots (B:=Fin ℓ) Λ=>p.1.val)
      (SlotTensor.fiberPerm κ) (fun _=>rfl)
    have hh:=hbound Λ F hΛ q edge a₀ b₀ ha₀ hb₀ c u v huv hF hf t ht
    dsimp only at hh
    rw [hp] at hh
    exact hh
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun κ _=>hh κ)
  rw [←Finset.mul_sum] at hsum
  have hm:=mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Λ → Equiv.Perm (Fin ℓ))) : 0≤(Fintype.card (Λ → Equiv.Perm (Fin ℓ)):ℝ)))
  dsimp only [P,colorSymmetrizer]
  simp only [Matrix.smul_mul,Matrix.sum_mul,Matrix.trace_smul,Matrix.trace_sum,smul_eq_mul]
  with_reducible convert hm using 1 <;> (try ring_nf) <;> congr! 20

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PhysicalSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

attribute [instance] instDecidableEqFin instDecidableEqProd
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.TensorMatrix
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
lemma trace_reindex_eq (e : m ≃ n) (A : Matrix m m ℝ) :
    Matrix.trace (Matrix.reindex e e A)=Matrix.trace A := by
  exact e.symm.sum_comp (fun i=>A i i)

lemma reindex_exp (e : m ≃ n) (A : Matrix m m ℝ) :
    Matrix.reindex e e (NormedSpace.exp A)=NormedSpace.exp (Matrix.reindex e e A) :=
  NormedSpace.map_exp (Matrix.reindexAlgEquiv ℝ ℝ e)
    (Matrix.reindexAlgEquiv ℝ ℝ e).toLinearMap.continuous_of_finiteDimensional A
lemma trace_reindex_exp_compression {p : Type} [Fintype p] [DecidableEq p]
    (e : m ≃ p) (P A D : Matrix m m ℝ) (B E : Matrix n n ℝ) (V : Matrix p n ℝ)
    (hV : V.transpose*V=1) (hP : Matrix.reindex e e P=V*V.transpose)
    (hAB : Matrix.reindex e e A*V=V*B) (hDE : Matrix.reindex e e D*V=V*E) :
    Matrix.trace (P*NormedSpace.exp A*D)=Matrix.trace (NormedSpace.exp B*E) := by
  let r:=Matrix.reindexAlgEquiv ℝ ℝ e
  rw [←trace_reindex_eq e]
  change Matrix.trace (r (P*NormedSpace.exp A*D))=_
  rw [_root_.map_mul,_root_.map_mul]
  change Matrix.trace (Matrix.reindex e e P * Matrix.reindex e e (NormedSpace.exp A) * Matrix.reindex e e D)=_
  rw [hP,reindex_exp]
  exact trace_exp_compression _ _ _ hV hAB _ _ hDE

end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
lemma reindex_spectral (ℓ : ℕ) (f : ℝ → ℝ) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (Matrix.diagonal (fun c : (X×Fin ℓ) → Bool=>f (SlotColor.magnetization c)))=
      Matrix.diagonal (fun a : X → Config ℓ=>f (configMagnetization ℓ a)) := by
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.diagonal_apply_eq,color_config_mag]
  · have he : (configEquiv ℓ).symm a ≠ (configEquiv ℓ).symm b := fun hh=>hab ((configEquiv ℓ).symm.injective hh)
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.diagonal_apply_ne _ he,
      Matrix.diagonal_apply_ne _ hab]

theorem trace_clock_spectral (R : X → X → Prop) (hR : ∀ x y,R x y → x≠y)
    (ℓ : ℕ) (t : ℝ) (f : ℝ → ℝ) :
    Matrix.trace (Surface.colorSymmetrizer X ℓ * NormedSpace.exp (t • clockGenerator R ℓ) *
      Matrix.diagonal (fun c : (X×Fin ℓ) → Bool=>f (SlotColor.magnetization c)))=
    Matrix.trace (NormedSpace.exp (t • spinGenerator R ℓ) *
      Matrix.diagonal (fun k : X → Level ℓ=>f (physicalMagnetization ℓ k))) := by
  have hAB : Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (t • clockGenerator R ℓ)*tensor (fun _ : X=>basis ℓ)=
      tensor (fun _ : X=>basis ℓ)*(t • spinGenerator R ℓ) := by
    have he := congrArg (fun M : Matrix (X → Config ℓ) (X → Level ℓ) ℝ=>t • M)
      (generator_intertwines R hR ℓ)
    have hs : Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (t • clockGenerator R ℓ) =
        t • Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (clockGenerator R ℓ) := rfl
    rw [hs,Matrix.smul_mul,Matrix.mul_smul]
    exact he
  have hDE : Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (Matrix.diagonal (fun c : (X×Fin ℓ) → Bool=>f (SlotColor.magnetization c)))*tensor (fun _ : X=>basis ℓ)=
      tensor (fun _ : X=>basis ℓ)*Matrix.diagonal (fun k : X → Level ℓ=>f (physicalMagnetization ℓ k)) := by
    rw [reindex_spectral]
    exact diagonal_function_intertwines _ _ _ (total_diagonal_intertwines (X:=X) ℓ) f
  have hP : Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (Surface.colorSymmetrizer X ℓ)=
      tensor (fun _ : X=>basis ℓ)*(tensor (fun _ : X=>basis ℓ)).transpose := by
    convert Surface.colorSymmetrizer_reindex X ℓ using 1; congr! 20
  exact trace_reindex_exp_compression (configEquiv ℓ) _ _ _ _ _
    (tensor (fun _ : X=>basis ℓ)) (basis_orthonormal ℓ) hP hAB hDE

end Heisenberg.SlotTensor
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor TensorMatrix
variable {d ℓ : ℕ}

lemma nearestNeighbor_iff_step {x y : Site d} : NearestNeighbor x y ↔ Geometry.Step x y := by
  constructor
  · intro h
    obtain ⟨i,hi,hj⟩:=nearestNeighbor_coordinate h
    exact ⟨i,by omega,hj⟩
  · rintro ⟨i,hi,hj⟩
    change ∑ j : Fin d,|x j-y j|=(1:ℤ)
    rw [Finset.sum_eq_single i]
    · rcases hi with hi | hi <;> rw [hi] <;> simp
    · intro j _ hji
      rw [hj j hji,sub_self,abs_zero]
    · exact fun h=>False.elim (h (Finset.mem_univ i))

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PhysicalSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
attribute [instance] instDecidableEqFin instDecidableEqProd
namespace Heisenberg.Surface
open Heisenberg.Geometry SpatialFrame SlotTensor TensorMatrix

lemma cycleGenerator_eq {d ℓ q : ℕ} (Λ : Finset (Site d))
    (edge : Fin q ≃ Edges (B:=Fin ℓ) Step Λ) (a₀ b₀ : ℕ → Slots (B:=Fin ℓ) Λ)
    (ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1) (hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2) :
    (∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1))=
      clockGenerator (fun x y : Λ=>Step x.val y.val) ℓ := by
  rw [←Fin.sum_univ_eq_sum_range]
  simp_rw [ha₀,hb₀]
  exact edge.sum_comp (fun e : Edges (B:=Fin ℓ) Step Λ =>
    (1/2:ℝ) • (SlotColor.matrix (Equiv.swap e.val.1 e.val.2)-1))

lemma step_ne {d : ℕ} {x y : Site d} (h : Step x y) : x≠y := by
  obtain ⟨j,hj,_⟩:=h
  intro he
  subst y
  omega

lemma spectral_tail_eq {X : Type} [Fintype X] (ℓ : ℕ) :
    tailProjection (X×Fin ℓ)=Matrix.diagonal
      (fun c : (X×Fin ℓ) → Bool=>if (Fintype.card X:ℝ)*ℓ/4≤SlotColor.magnetization c then (1:ℝ) else 0) := by
  simp only [tailProjection,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]

theorem physical_surface_bound (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ] :
    ∃ s : ℝ,0<s ∧
      ∀ (Λ F : Finset (Site (d+1))) (_hΛ : Λ.Nonempty) (q : ℕ) [NeZero q]
        (edge : Fin q ≃ Edges (B:=Fin ℓ) Step Λ) (a₀ b₀ : ℕ → Slots (B:=Fin ℓ) Λ)
        (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
        (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
        (_hF : F⊆Λ) (_hf : ∀ z∈F,∀ w,Step z w → w∈Λ) (t : ℝ) (_ht : 2*s<t),
        let Z:=((Finset.univ.filter (fun v : Slots (B:=Fin ℓ) Λ=>v.1.val∉F)).card:ℝ)
        let J:=(((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card:ℝ)
        let E:=NormedSpace.exp (t • spinGenerator (fun x y : Λ=>Step x.val y.val) ℓ)
        Real.exp (-(Real.log 2)*(Z+2*t*J))/2*Matrix.trace E≤
          Matrix.trace (E*Matrix.diagonal (fun k : Λ → SpinSlots.Level ℓ=>
            if (Λ.card:ℝ)*ℓ/4≤physicalMagnetization ℓ k then (1:ℝ) else 0)) := by
  obtain ⟨s,hs,hbound⟩:=symmetrized_surface_bound d ℓ hd
  refine ⟨s,hs,?_⟩
  intro Λ F hΛ q _ edge a₀ b₀ ha₀ hb₀ hF hf t ht Z J E
  have hh : Real.exp (-(Real.log 2)*(Z+2*t*J))/2*
      Matrix.trace (colorSymmetrizer Λ ℓ*NormedSpace.exp (t • ∑ j∈Finset.range q,
        (1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1)))≤
      Matrix.trace (colorSymmetrizer Λ ℓ*NormedSpace.exp (t • ∑ j∈Finset.range q,
        (1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a₀ j) (b₀ j))-1))*tailProjection (Slots (B:=Fin ℓ) Λ)) := by
    convert hbound Λ F hΛ q edge a₀ b₀ ha₀ hb₀ hF hf t ht using 1 <;> congr! 30
  rw [cycleGenerator_eq Λ edge a₀ b₀ ha₀ hb₀,spectral_tail_eq] at hh
  have hn : ∀ x y : Λ,Step x.val y.val → x≠y := fun x y h he=>step_ne h (congrArg Subtype.val he)
  have hb:=trace_clock_spectral (fun x y : Λ=>Step x.val y.val) hn ℓ t (fun _=>1)
  simp only [Matrix.diagonal_one,Matrix.mul_one] at hb
  rw [hb] at hh
  have htail:=trace_clock_spectral (fun x y : Λ=>Step x.val y.val) hn ℓ t
    (fun m=>if (Fintype.card Λ:ℝ)*ℓ/4≤ m then (1:ℝ) else 0)
  rw [htail] at hh
  simpa only [Fintype.card_coe] using hh

end Heisenberg.Surface
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CubeSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
open Filter Topology
namespace Heisenberg
open SpatialFrame
variable {d ℓ : ℕ}

lemma bad_slots_le (Λ F : Finset (Site d)) :
    (Finset.univ.filter (fun v : Slots (B:=Fin ℓ) Λ=>v.1.val∉F)).card≤(Λ\F).card*ℓ := by
  let f : {v : Slots (B:=Fin ℓ) Λ // v.1.val∉F} → ↥(Λ\F) × Fin ℓ:=
    fun v=>(⟨v.val.1,Finset.mem_sdiff.mpr ⟨v.val.1.property,v.property⟩⟩,v.val.2)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; exact congrArg (fun v : ↥(Λ\F) × Fin ℓ=>v.1.val) h
    · exact congrArg (fun v : ↥(Λ\F) × Fin ℓ=>v.2) h
  have hc:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] using hc

lemma bad_edges_le (Λ F : Finset (Site d)) :
    (Finset.univ.filter (fun e : Edges (B:=Fin ℓ) Geometry.Step Λ=>
      e.val.1.1.val∉F ∨ e.val.2.1.val∉F)).card≤(4*d)*(Λ\F).card*ℓ^2 := by
  let E:={e : Edges (B:=Fin ℓ) Geometry.Step Λ // e.val.1.1.val∉F ∨ e.val.2.1.val∉F}
  let f : E → (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ):=fun e=>
    (⟨(e.val.val.1.1.val,e.val.val.2.1.val),mem_incidentEdges (nearestNeighbor_iff_step.mpr e.val.property)
      (e.property.imp (fun h=>Finset.mem_sdiff.mpr ⟨e.val.val.1.1.property,h⟩)
        (fun h=>Finset.mem_sdiff.mpr ⟨e.val.val.2.1.property,h⟩))⟩,(e.val.val.1.2,e.val.val.2.2))
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext; exact congrArg (fun v : (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ)=>v.1.val.1) h
      · exact congrArg (fun v : (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ)=>v.2.1) h
    · apply Prod.ext
      · apply Subtype.ext; exact congrArg (fun v : (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ)=>v.1.val.2) h
      · exact congrArg (fun v : (incidentEdges (Λ\F)) × (Fin ℓ × Fin ℓ)=>v.2.2) h
  have hc:=Fintype.card_le_of_injective f hf
  simp only [E,Fintype.card_subtype,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] at hc
  exact hc.trans (by simpa only [pow_two] using Nat.mul_le_mul_right (ℓ*ℓ) (card_incidentEdges_le (Λ\F)))

lemma schedule_bad_eq {q : ℕ} (Λ F : Finset (Site d))
    (edge : Fin q ≃ Edges (B:=Fin ℓ) Geometry.Step Λ) (a₀ b₀ : ℕ → Slots (B:=Fin ℓ) Λ)
    (ha : ∀ j : Fin q,a₀ j=(edge j).val.1) (hb : ∀ j : Fin q,b₀ j=(edge j).val.2) :
    ((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card=
      (Finset.univ.filter (fun e : Edges (B:=Fin ℓ) Geometry.Step Λ=>e.val.1.1.val∉F ∨ e.val.2.1.val∉F)).card := by
  have hsum := edge.sum_comp (fun e : Edges (B:=Fin ℓ) Geometry.Step Λ=>if e.val.1.1.val∉F ∨ e.val.2.1.val∉F then (1:ℕ) else 0)
  rw [Finset.card_filter,Finset.card_filter,←Fin.sum_univ_eq_sum_range]
  simpa only [ha,hb] using hsum

lemma box_card (d n : ℕ) : (box d n).card=(2*n+1)^d := Geometry.card_boxFinset d n
lemma box_mono {n m : ℕ} (hnm : n≤ m) : box d n⊆box d m := by
  intro x hx
  apply (box_mem d m x).mpr
  intro j
  exact (box_mem d n x |>.mp hx j).trans (by exact_mod_cast hnm)

lemma box_neighbor {n : ℕ} {x y : Site d} (hx : x∈box d n) (h : Geometry.Step x y) : y∈box d (n+1) := by
  obtain ⟨i,hi,hj⟩:=h
  apply (box_mem _ _ _).mpr
  intro j
  have hxj:=(box_mem d n x).mp hx j
  by_cases hji : j=i
  · subst j
    rcases hi with hi | hi
    · rw [hi]
      exact (abs_add_le _ _).trans (by simpa only [abs_one,Nat.cast_add,Nat.cast_one,add_le_add_iff_right] using hxj)
    · rw [show y i=x i-1 by omega]
      exact (abs_sub _ _).trans (by simpa only [abs_one,Nat.cast_add,Nat.cast_one,add_le_add_iff_right] using hxj)
  · rw [hj j hji]
    exact hxj.trans (by exact_mod_cast Nat.le_succ n)

lemma box_ratio_tendsto (d r : ℕ) :
    Tendsto (fun n : ℕ=>((box d n).card:ℝ)/((box d (n+r)).card:ℝ)) atTop (𝓝 1) := by
  have hx : Tendsto (fun n : ℕ=>(2*(n:ℝ)+1)/(2*((n:ℝ)+r)+1)) atTop (𝓝 1) := by
    have hi : Tendsto (fun n : ℕ=>(2*((n:ℝ)+r)+1)⁻¹) atTop (𝓝 0) := by
      apply tendsto_inv_atTop_zero.comp
      exact tendsto_atTop_add_const_right _ 1
        ((tendsto_atTop_add_const_right _ (r:ℝ) tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0:ℝ)<2))
    have hh:=(tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub (hi.const_mul (2*r:ℝ))
    convert hh using 1
    · ext n
      field_simp
      ring
    · simp
  have hh:=hx.pow d
  simpa only [box_card,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,div_pow,one_pow] using hh

lemma box_boundary_ratio_tendsto (d r : ℕ) :
    Tendsto (fun n : ℕ=>((box d (n+r)\box d n).card:ℝ)/((box d (n+r)).card:ℝ)) atTop (𝓝 0) := by
  have hh:=(tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub (box_ratio_tendsto d r)
  convert hh using 1
  · ext n
    rw [Finset.card_sdiff_of_subset (box_mono (Nat.le_add_right n r)),Nat.cast_sub (Finset.card_le_card (box_mono (Nat.le_add_right n r))),sub_div,div_self]
    exact_mod_cast (Finset.card_ne_zero.mpr (box_nonempty d (n+r)))
  · norm_num

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CubeSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
namespace Heisenberg.Selection
open Heisenberg.Geometry SpatialFrame SlotTensor

lemma box_volume_tendsto {d : ℕ} (hd : 0<d) (r : ℕ) :
    Tendsto (fun n : ℕ=>((box d (n+r)).card:ℝ)) atTop atTop := by
  simp only [box_card,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  exact (tendsto_pow_atTop hd.ne').comp (tendsto_atTop_add_const_right _ 1
    ((tendsto_atTop_add_const_right _ (r:ℝ) tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0:ℝ)<2)))

lemma surface_exp_tendsto {d : ℕ} (hd : 0<d) (C a : ℝ) (ha : 0<a) :
    Tendsto (fun n : ℕ=>2*Real.exp (C*((box d (n+1)\box d n).card:ℝ)-a*((box d (n+1)).card:ℝ))) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ=>C*(((box d (n+1)\box d n).card:ℝ)/((box d (n+1)).card:ℝ))-a) atTop (𝓝 (-a)) := by
    simpa only [mul_zero,zero_sub] using ((box_boundary_ratio_tendsto d 1).const_mul C).sub_const a
  have hmul:=(hc.neg_mul_atTop (neg_lt_zero.mpr ha) (box_volume_tendsto hd 1))
  have hexp:=(Real.tendsto_exp_atBot.comp hmul).const_mul 2
  convert hexp using 1
  · ext n
    congr 2
    have hv : ((box d (n+1)).card:ℝ)≠0:=by exact_mod_cast Finset.card_ne_zero.mpr (box_nonempty d (n+1))
    field_simp
  · norm_num

lemma cube_edges_nonempty (d ℓ n : ℕ) (hd : 0<d) [NeZero ℓ] :
    Nonempty (Edges (B:=Fin ℓ) Step (box d (n+1))) := by
  let i : Fin d:=⟨0,hd⟩
  let y : Site d:=Function.update 0 i 1
  have h0 : (0:Site d)∈box d (n+1):=(box_mem d (n+1) 0).mpr (by intro j; simp; omega)
  have hy : y∈box d (n+1) := by
    apply (box_mem d (n+1) y).mpr
    intro j
    by_cases hj : j=i
    · subst j; simp [y]
    · simp [y,Function.update_of_ne hj]; omega
  have hs : Step (0:Site d) y:=⟨i,Or.inl (by simp [y]),fun j hj=>by simp [y,Function.update_of_ne hj]⟩
  exact ⟨⟨((⟨0,h0⟩,(0:Fin ℓ)),(⟨y,hy⟩,(0:Fin ℓ))),hs⟩⟩

theorem field_ordered_cubes_oai (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ]
    (τ : State (d+1) ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A)) :
    ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β → ∀ h : ℝ,0<h →
      ∀ᶠ n : ℕ in atTop,
        ((box (d+1) (n+1)).card:ℝ)*ℓ/8≤
          ((gibbsState τ (shiftedField (box (d+1) (n+1)) h) β).functional
            (totalZ (box (d+1) (n+1)))).re := by
  obtain ⟨s,hs,hbound⟩:=Surface.physical_surface_bound d ℓ hd
  refine ⟨4*s+1,by linarith,?_⟩
  intro β hβ h hh
  have hb : 0<β:=by linarith
  let C : ℝ:=Real.log 2*((ℓ:ℝ)+β*((4*(d+1):ℕ):ℝ)*ℓ^2)
  let a : ℝ:=β*h*ℓ/16
  have ha : 0<a:=by dsimp [a]; exact div_pos (mul_pos (mul_pos hb hh) (by exact_mod_cast NeZero.pos ℓ)) (by norm_num)
  have he :=(surface_exp_tendsto (by omega : 0<d+1) C a ha).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/11))
  filter_upwards [he] with n hn
  let Λ:=box (d+1) (n+1)
  let F:=box (d+1) n
  let E:=Edges (B:=Fin ℓ) Step Λ
  let : Nonempty E:=cube_edges_nonempty (d+1) ℓ n (by omega)
  let q:=Fintype.card E
  let : NeZero q:=⟨Fintype.card_ne_zero⟩
  let edge : Fin q ≃ E:=(Fintype.equivFin E).symm
  let a₀ : ℕ → Slots (B:=Fin ℓ) Λ:=fun j=>(edge (j:Fin q)).val.1
  let b₀ : ℕ → Slots (B:=Fin ℓ) Λ:=fun j=>(edge (j:Fin q)).val.2
  have ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1:=by intro j; simp only [a₀,Fin.cast_val_eq_self]
  have hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2:=by intro j; simp only [b₀,Fin.cast_val_eq_self]
  let Z : ℝ:=((Finset.univ.filter (fun v : Slots (B:=Fin ℓ) Λ=>v.1.val∉F)).card:ℝ)
  let J : ℝ:=(((Finset.range q).filter (fun j=>(a₀ j).1.val∉F ∨ (b₀ j).1.val∉F)).card:ℝ)
  let L : ℝ:=Real.exp (-(Real.log 2)*(Z+β*J))/2
  have htail :=hbound Λ F (box_nonempty _ _) q edge a₀ b₀ ha₀ hb₀
    (box_mono (Nat.le_succ n)) (fun z hz w hzw=>box_neighbor hz hzw) (β/2) (by linarith)
  have htail' : L*Matrix.trace (NormedSpace.exp ((β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ))≤
      Matrix.trace (NormedSpace.exp ((β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ)*
        Matrix.diagonal (fun k : Λ → SpinSlots.Level ℓ=>if (Λ.card:ℝ)*ℓ/4≤physicalMagnetization ℓ k then (1:ℝ) else 0)) := by
    convert htail using 1 <;> simp only [L,Z,J,nearestNeighbor_iff_step]; congr 5; ring
  apply physical_field_mean Λ τ hτ β h L (mul_pos hb hh).le (by dsimp [L]; positivity) htail'
  have hZ : Z≤((Λ\F).card:ℝ)*ℓ := by dsimp [Z]; exact_mod_cast bad_slots_le (ℓ:=ℓ) Λ F
  have hJ : J≤((4*(d+1):ℕ):ℝ)*((Λ\F).card:ℝ)*ℓ^2 := by
    dsimp [J]
    rw [schedule_bad_eq Λ F edge a₀ b₀ ha₀ hb₀]
    exact_mod_cast bad_edges_le (ℓ:=ℓ) Λ F
  have hcost : (Real.log 2)*(Z+β*J)≤C*((Λ\F).card:ℝ) := by
    have hbJ:=mul_le_mul_of_nonneg_left hJ hb.le
    have hhcost:=mul_le_mul_of_nonneg_left (add_le_add hZ hbJ) (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
    calc _ ≤ (Real.log 2)*(((Λ\F).card:ℝ)*ℓ+β*(((4*(d+1):ℕ):ℝ)*((Λ\F).card:ℝ)*ℓ^2)) := hhcost
         _ = C*((Λ\F).card:ℝ) := by dsimp [C]; ring
  calc L⁻¹*Real.exp (-((β*h)*((Λ.card:ℝ)*ℓ)/16))=
        2*Real.exp ((Real.log 2)*(Z+β*J)-a*(Λ.card:ℝ)) := by
          dsimp [L,a]
          rw [inv_div,div_eq_mul_inv,←Real.exp_neg]
          simp only [neg_mul,neg_neg]
          rw [mul_assoc,←Real.exp_add]
          congr 2
          ring
       _ ≤ 2*Real.exp (C*((Λ\F).card:ℝ)-a*(Λ.card:ℝ)) :=
         mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_right hcost _)) (by norm_num)
       _ ≤ 1/11 := hn

end Heisenberg.Selection
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.Selection.field_ordered_cubes_oai := @OAI.Heisenberg.Selection.field_ordered_cubes_oai
