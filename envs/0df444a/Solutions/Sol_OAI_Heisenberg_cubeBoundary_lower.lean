-- Prove2me | solution 1 for OAI.Heisenberg.cubeBoundary_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:35:57.147817+00:00
-- url     : https://prove2.me/submissions/05c8e0fb-50d3-4515-b2cf-75387b649aa2

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalAlgebra
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical

open scoped ComplexConjugate BigOperators
namespace Heisenberg

lemma localUnit_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d}
    (hx : x ∈ F) (a b : Level ℓ) : localUnit d ℓ x a b ∈ localAlgebra d ℓ F :=
  StarAlgebra.subset_adjoin ℂ _ ⟨x, hx, a, b, rfl⟩

lemma spinZ_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinZ d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k k) _

lemma spinPlus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinPlus d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k.succ k.castSucc) _

lemma spinMinus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinMinus d ℓ x ∈ localAlgebra d ℓ F :=
  star_mem (spinPlus_mem_localAlgebra d ℓ F hx)

lemma spinX_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinX d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).add_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

lemma spinY_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinY d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).sub_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

theorem localAlgebras_commute {d ℓ : ℕ} {F G : Set (Site d)} (hFG : Disjoint F G)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ F) (hB : B ∈ localAlgebra d ℓ G) :
    Commute A B := by
  have hg (x : Site d) (hx : x ∈ F) (a b : Level ℓ) :
      localAlgebra d ℓ G ≤ StarSubalgebra.centralizer ℂ {localUnit d ℓ x a b} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨y, hy, c, e, rfl⟩
    have hxy : x ≠ y := fun h => (Set.disjoint_left.mp hFG hx) (h ▸ hy)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨(localUnits_commute hxy a b c e).eq, by
      rw [star_localUnit]
      exact (localUnits_commute hxy b a c e).eq⟩
  have hle : localAlgebra d ℓ F ≤ StarSubalgebra.centralizer ℂ {B} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨x, hx, a, b, rfl⟩
    have h₁ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hg x hx a b hB)) _ (Set.mem_singleton _)
    have h₂ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp
      (hg x hx a b (star_mem hB))) _ (Set.mem_singleton _)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨h₁.1.symm, h₂.1.symm⟩
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA)) B (Set.mem_singleton B)).1.symm

lemma singleton_local_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ {x})
    (hB : B ∈ localAlgebra d ℓ {y}) : Commute A B :=
  localAlgebras_commute (Set.disjoint_singleton.mpr hxy) hA hB

lemma nearestNeighbor_ne {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) : x ≠ y := by
  intro he
  subst y
  simp [NearestNeighbor] at h

end Heisenberg
end

end OAI
end

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

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundedStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

open scoped ComplexConjugate Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]

attribute [local instance] OAI.GibbsStrip.instNormedAlgebraRat_solutions
lemma exp_scalar_add (K : E) (z w : ℂ) :
    NormedSpace.exp ((z+w) • K) = NormedSpace.exp (z • K) * NormedSpace.exp (w • K) := by
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl K).smul_left z |>.smul_right w)

lemma exp_cancel_left (K : E) (z : ℂ) :
    NormedSpace.exp (z • K) * NormedSpace.exp ((-z) • K) = 1 := by
  rw [← exp_scalar_add]
  simp

end GibbsStrip

open Set Filter Complex
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_TensorLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators Matrix
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
  [Fintype K] [DecidableEq K]

lemma list_prod_smul {I : Type*} (L : List I) (c : I → R) (f : I → E) :
    (L.map (fun i=>c i • f i)).prod=(L.map c).prod • (L.map f).prod := by
  induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.map_cons,List.prod_cons,ih,smul_mul_smul_comm]

lemma ofFn_prod_smul {n : ℕ} (c : Fin n → R) (f : Fin n → E) :
    (List.ofFn (fun i=>c i • f i)).prod=(∏ i,c i) • (List.ofFn f).prod := by
  have hh:=list_prod_smul (List.ofFn (id:Fin n → Fin n)) c f
  simpa only [List.map_ofFn,Function.comp_id,List.prod_ofFn] using hh

omit [DecidableEq K] in
lemma lift_tensorFin {n : ℕ} (u : Fin n → K → K → E) (M : Fin n → Matrix K K R) :
    liftLinear (system u) (fun a b=>∏ i,M i (a i) (b i))=
      (List.ofFn (fun i=>liftLinear (u i) (M i))).prod := by
  have hh:=(MultilinearMap.mkPiAlgebraFin R n E).map_sum
    (fun i (v : K×K)=>M i v.1 v.2 • u i v.1 v.2)
  simp only [Fintype.sum_prod_type,MultilinearMap.mkPiAlgebraFin_apply] at hh
  rw [←(pairConfigEquiv n K).symm.sum_comp,Fintype.sum_prod_type] at hh
  simp only [ofFn_prod_smul] at hh
  exact hh.symm

end Heisenberg.TensorUnits
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
-- module Solutions.OAIW2_Heis.Heisenberg_TensorLiftIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix
namespace Heisenberg.TensorUnits
variable {R E K : Type*} [CommSemiring R] [Semiring E] [Algebra R E]
  [Fintype K] [DecidableEq K]

lemma ofFn_prod_eq_single {n : ℕ} (f : Fin n → E) (i : Fin n)
    (h : ∀ j,j≠i → f j=1) : (List.ofFn f).prod=f i := by
  induction n with
  | zero=>exact Fin.elim0 i
  | succ n ih=>
    induction i using Fin.cases with
    | zero=>
      rw [List.ofFn_succ,List.prod_cons]
      have he : (fun j : Fin n=>f j.succ)=fun _=>1 := by
        funext j
        exact h _ (Fin.succ_ne_zero j)
      rw [he,List.ofFn_const,List.prod_replicate,one_pow,mul_one]
    | succ i=>
      rw [List.ofFn_succ,List.prod_cons,h 0 (Ne.symm (Fin.succ_ne_zero i)),one_mul]
      exact ih (fun j=>f j.succ) i (fun j hj=>h _ (fun he=>hj (Fin.succ_injective _ he)))

lemma lift_onsiteFin {n : ℕ} (u : Fin n → K → K → E)
    (hs : ∀ i,∑ a,u i a a=1) (i : Fin n) (M : Matrix K K R) :
    liftLinear (system u) (TensorMatrix.onsite i M)=liftLinear (u i) M := by
  unfold TensorMatrix.onsite TensorMatrix.tensor
  rw [lift_tensorFin]
  have he:=ofFn_prod_eq_single (fun j=>liftLinear (u j) (Function.update (fun _ : Fin n=>(1:Matrix K K R)) i M j)) i
    (fun j hj=>by rw [Function.update_of_ne hj,lift_one (u j) (hs j)])
  simpa only [Function.update_self] using he

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype K] [DecidableEq K] [DecidableEq X] in
lemma reindex_tensor {n : ℕ} (e : X ≃ Fin n) (M : X → Matrix K K R) :
    Matrix.reindex (functionReindex e) (functionReindex e) (TensorMatrix.tensor M)=
      TensorMatrix.tensor (fun i=>M (e.symm i)) := by
  ext a b
  change (∏ x,M x (a (e x)) (b (e x)))=∏ i,M (e.symm i) (a i) (b i)
  simpa only [Equiv.apply_symm_apply] using (e.symm.prod_comp (fun x=>M x (a (e x)) (b (e x)))).symm

omit [Fintype K] in
lemma reindex_onsite {n : ℕ} (e : X ≃ Fin n) (x : X) (M : Matrix K K R) :
    Matrix.reindex (functionReindex e) (functionReindex e) (TensorMatrix.onsite x M)=
      TensorMatrix.onsite (e x) M := by
  unfold TensorMatrix.onsite
  rw [reindex_tensor]
  congr 1
  ext i a b
  by_cases hi : i=e x
  · subst i; simp
  · have hx : e.symm i≠x:=fun hh=>hi (by rw [←hh,Equiv.apply_symm_apply])
    simp [Function.update_of_ne hi,Function.update_of_ne hx]

end Heisenberg.TensorUnits
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinTensorRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open TensorUnits
variable {d ℓ : ℕ} {X : Type} [Fintype X] [DecidableEq X]

lemma finiteRepresentation_onsite (site : X → Site d) (hinj : Function.Injective site)
    (x : X) (M : Matrix (Level ℓ) (Level ℓ) ℝ) :
    finiteRepresentation site hinj (TensorMatrix.onsite x M)=
      liftLinear (localUnit d ℓ (site x)) M := by
  change liftLinear (system (fun i=>localUnit d ℓ (site ((Fintype.equivFin X).symm i))))
    (Matrix.reindex (functionReindex (Fintype.equivFin X)) (functionReindex (Fintype.equivFin X))
      (TensorMatrix.onsite x M))=_
  rw [reindex_onsite,lift_onsiteFin _ (fun i=>localUnit_diagonal_sum d ℓ _)]
  simp only [Equiv.symm_apply_apply]

lemma finiteRepresentation_z (site : X → Site d) (hinj : Function.Injective site) (x : X) :
    finiteRepresentation site hinj (TensorMatrix.onsite x (SpinSlots.physicalZ ℓ))=spinZ d ℓ (site x) := by
  rw [finiteRepresentation_onsite]
  change (∑ a,∑ b,Matrix.diagonal (fun k : Level ℓ=>(k:ℝ)-(ℓ:ℝ)/2) a b • localUnit d ℓ (site x) a b)=_
  simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  exact (IsScalarTower.algebraMap_smul ℂ ((a:ℝ)-(ℓ:ℝ)/2) (localUnit d ℓ (site x) a a)).symm

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinPhysicalOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open TensorUnits
variable {d ℓ : ℕ}

lemma plus_coefficient (k : Fin ℓ) :
    Real.sqrt (((ℓ-k.val:ℕ):ℝ)*(k.val+1))=
      Real.sqrt ((ℓ/2:ℝ)*(ℓ/2+1)-magneticLevel ℓ k.castSucc*(magneticLevel ℓ k.castSucc+1)) := by
  congr 1
  rw [Nat.cast_sub k.isLt.le]
  simp only [magneticLevel,Fin.val_castSucc]
  ring

lemma oneSite_plus (x : Site d) :
    liftLinear (localUnit d ℓ x) (SpinSlots.physicalPlus ℓ)=spinPlus d ℓ x := by
  change (∑ a : Level ℓ,∑ b : Level ℓ,
    (if a.val=b.val+1 then Real.sqrt (((ℓ-b.val:ℕ):ℝ)*(b.val+1)) else 0) • localUnit d ℓ x a b)=_
  rw [Finset.sum_comm,Fin.sum_univ_castSucc]
  have hsum (k : Fin ℓ) :
      (∑ a : Level ℓ,(if a.val=k.val+1 then Real.sqrt (((ℓ-k.val:ℕ):ℝ)*(k.val+1)) else 0) • localUnit d ℓ x a k.castSucc)=
        Real.sqrt (((ℓ-k.val:ℕ):ℝ)*(k.val+1)) • localUnit d ℓ x k.succ k.castSucc := by
    rw [Finset.sum_eq_single k.succ]
    · simp only [Fin.val_succ,ite_true]
    · intro a _ ha
      have hne : a.val≠k.val+1:=fun he=>ha (Fin.ext he)
      rw [ite_eq_right hne,zero_smul]
    · exact fun h=>False.elim (h (Finset.mem_univ _))
  have hlast : (∑ a : Level ℓ,(if a.val=(Fin.last ℓ).val+1 then Real.sqrt (((ℓ-(Fin.last ℓ).val:ℕ):ℝ)*((Fin.last ℓ).val+1)) else 0) • localUnit d ℓ x a (Fin.last ℓ))=0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [ite_eq_right (by have := a.isLt; simp only [Fin.val_last]; omega),zero_smul]
  simp only [Fin.val_castSucc,hsum,hlast,add_zero,spinPlus]
  apply Finset.sum_congr rfl
  intro k _
  rw [plus_coefficient]
  exact (IsScalarTower.algebraMap_smul ℂ _ _).symm

lemma oneSite_transpose (x : Site d) (M : Matrix (Level ℓ) (Level ℓ) ℝ) :
    liftLinear (localUnit d ℓ x) M.transpose=star (liftLinear (localUnit d ℓ x) M) := by
  simp only [liftLinear,LinearMap.coe_mk,AddHom.coe_mk,Matrix.transpose_apply,star_sum,star_smul,
    star_trivial,star_localUnit]
  rw [Finset.sum_comm]

variable {X : Type} [Fintype X] [DecidableEq X]
lemma finiteRepresentation_plus (site : X → Site d) (hinj : Function.Injective site) (x : X) :
    finiteRepresentation site hinj (TensorMatrix.onsite x (SpinSlots.physicalPlus ℓ))=spinPlus d ℓ (site x) := by
  rw [finiteRepresentation_onsite,oneSite_plus]

lemma finiteRepresentation_minus (site : X → Site d) (hinj : Function.Injective site) (x : X) :
    finiteRepresentation site hinj (TensorMatrix.onsite x (SpinSlots.physicalPlus ℓ).transpose)=spinMinus d ℓ (site x) := by
  rw [finiteRepresentation_onsite,oneSite_transpose,oneSite_plus]
  rfl

lemma xy_bond (d ℓ : ℕ) (x y : Site d) :
    spinX d ℓ x*spinX d ℓ y+spinY d ℓ x*spinY d ℓ y=
      (1/2:ℝ) • (spinPlus d ℓ x*spinMinus d ℓ y+spinMinus d ℓ x*spinPlus d ℓ y) := by
  have hc : (1/(2*Complex.I):ℂ)*(1/(2*Complex.I))= -(1/4:ℂ) := by
    simp only [one_div,mul_inv_rev,Complex.inv_I]
    ring_nf
    norm_num [Complex.I_sq]
  rw [spinX,spinX,spinY,spinY,smul_mul_smul_comm,smul_mul_smul_comm,hc]
  rw [←IsScalarTower.algebraMap_smul ℂ (1/2:ℝ)]
  norm_num only [map_div₀,map_one,map_ofNat]
  simp only [mul_add,add_mul,mul_sub,sub_mul]
  module

lemma finiteRepresentation_bond (site : X → Site d) (hinj : Function.Injective site) (x y : X) :
    finiteRepresentation site hinj (SlotTensor.spinBond ℓ x y)=bond d ℓ (site x) (site y) := by
  simp only [SlotTensor.spinBond,map_add,map_smul,map_mul,
    finiteRepresentation_plus,finiteRepresentation_minus,finiteRepresentation_z]
  rw [←xy_bond]
  rfl

end Heisenberg
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

omit [Fintype m] in
lemma diagonal_fintype_sum {I : Type*} [Fintype I] (f : I → m → ℝ) :
    (∑ i,Matrix.diagonal (f i))=Matrix.diagonal (fun j=>∑ i,f i j) := by
  ext a b
  by_cases h : a=b
  · subst b; simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply,Matrix.diagonal_apply_ne _ h]

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
-- module Solutions.OAIW2_Heis.Heisenberg_SpinDirected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
attribute [instance] instDecidableEqFin instDecidableEqProd
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor

lemma directed_sum {X E : Type*} [Fintype X] [AddCommMonoid E]
    (R r : X → X → Prop) (hR : ∀ x y,R x y → R y x) (hne : ∀ x y,R x y → x≠y)
    (hr : ∀ x y,x≠y → r x y ∨ r y x) (ha : ∀ x y,r x y → ¬r y x)
    (f : X → X → E) (hf : ∀ x y,R x y → f x y=f y x) :
    (∑ e : X×X,if R e.1 e.2 then f e.1 e.2 else 0)=
      2 • (∑ e : X×X,if R e.1 e.2 ∧ r e.1 e.2 then f e.1 e.2 else 0) := by
  let g : X×X → E:=fun e=>if R e.1 e.2 ∧ r e.1 e.2 then f e.1 e.2 else 0
  have h (e : X×X) : (if R e.1 e.2 then f e.1 e.2 else 0)=g e+g e.swap := by
    dsimp only [g]
    by_cases hh : R e.1 e.2
    · rw [ite_eq_left hh]
      by_cases he : r e.1 e.2
      · rw [ite_eq_left ⟨hh,he⟩,ite_eq_right (fun h=>ha _ _ he h.2),add_zero]
      · have he' : r e.2 e.1:=(hr _ _ (hne _ _ hh)).resolve_left he
        rw [ite_eq_right (fun h=>he h.2),ite_eq_left ⟨hR _ _ hh,he'⟩,zero_add,hf _ _ hh]
        rfl
    · have hh' : ¬R e.2 e.1:=fun h=>hh (hR _ _ h)
      rw [ite_eq_right hh,ite_eq_right (fun h=>hh h.1),ite_eq_right (fun h=>hh' h.1),add_zero]
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  change (∑ e,g e)+(∑ e,g ((Equiv.prodComm X X) e))=2 • ∑ e,g e
  rw [(Equiv.prodComm X X).sum_comp,two_smul]

lemma bond_symm {d ℓ : ℕ} {x y : Site d} (hxy : x≠y) : bond d ℓ x y=bond d ℓ y x := by
  have hX:=singleton_local_commute hxy (spinX_mem_localAlgebra d ℓ {x} (Set.mem_singleton x))
    (spinX_mem_localAlgebra d ℓ {y} (Set.mem_singleton y))
  have hY:=singleton_local_commute hxy (spinY_mem_localAlgebra d ℓ {x} (Set.mem_singleton x))
    (spinY_mem_localAlgebra d ℓ {y} (Set.mem_singleton y))
  have hZ:=singleton_local_commute hxy (spinZ_mem_localAlgebra d ℓ {x} (Set.mem_singleton x))
    (spinZ_mem_localAlgebra d ℓ {y} (Set.mem_singleton y))
  simp only [bond,hX.eq,hY.eq,hZ.eq]

lemma sum_siteEdges {X : Type} {E : Type*} [Fintype X] [AddCommMonoid E]
    (R : X → X → Prop) (f : X → X → E) :
    (∑ e : SiteEdges R,f e.val.1 e.val.2)=∑ e : X×X,if R e.1 e.2 then f e.1 e.2 else 0 := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun e : X×X=>R e.1 e.2)) (by simp) (fun e=>f e.1 e.2)]
  simp only [Finset.sum_filter]

lemma sum_volumeEdges {d ℓ : ℕ} (Λ : Finset (Site d)) :
    (∑ e : Λ×Λ,if NearestNeighbor e.1.val e.2.val ∧ WellOrderingRel e.1.val e.2.val
      then bond d ℓ e.1.val e.2.val else 0)= -hamiltonian d ℓ Λ := by
  rw [hamiltonian,neg_neg,volumeEdges,Finset.sum_filter,Finset.sum_product,Fintype.sum_prod_type]
  rw [←Finset.sum_coe_sort Λ]
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.sum_coe_sort Λ (fun y=>if NearestNeighbor x.val y ∧ WellOrderingRel x.val y then bond d ℓ x.val y else 0)

lemma directed_bond_sum {d ℓ : ℕ} (Λ : Finset (Site d)) :
    (∑ e : SiteEdges (fun x y : Λ=>NearestNeighbor x.val y.val),bond d ℓ e.val.1.val e.val.2.val)=
      2 • (-hamiltonian d ℓ Λ) := by
  rw [sum_siteEdges (fun x y : Λ=>NearestNeighbor x.val y.val) (fun x y : Λ=>bond d ℓ x.val y.val)]
  have hh:=directed_sum (fun x y : Λ=>NearestNeighbor x.val y.val) (fun x y : Λ=>WellOrderingRel x.val y.val)
    (fun _ _ h=>nearestNeighbor_symm h)
    (fun x y h he=>nearestNeighbor_ne h (congrArg Subtype.val he))
    (fun x y h=>by
      rcases trichotomous_of WellOrderingRel x.val y.val with hxy | hxy | hxy
      · exact Or.inl hxy
      · exact False.elim (h (Subtype.ext hxy))
      · exact Or.inr hxy)
    (fun x y h=>asymm h)
    (fun x y : Λ=>bond d ℓ x.val y.val) (fun x y h=>bond_symm (nearestNeighbor_ne h))
  rw [sum_volumeEdges] at hh
  exact hh

lemma finiteRepresentation_generator {d ℓ : ℕ} (Λ : Finset (Site d)) :
    finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective
      (spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ)=
      (-2:ℝ) • hamiltonian d ℓ Λ-
        ((Fintype.card (SiteEdges (fun x y : Λ=>NearestNeighbor x.val y.val)):ℝ)*(ℓ:ℝ)^2/4) • 1 := by
  simp only [spinGenerator,map_sum,map_sub,finiteRepresentation_bond,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,directed_bond_sum]
  rw [←Nat.cast_smul_eq_nsmul ℝ,←Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  rw [map_smul, map_one]
  norm_num
  module

end Heisenberg
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

end Heisenberg.SlotTensor
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinMatrixConservation
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
omit [DecidableEq m] in
lemma compress_commute (A D : Matrix m m ℝ) (B E : Matrix n n ℝ) (V : Matrix m n ℝ)
    (hV : V.transpose*V=1) (hAB : A*V=V*B) (hDE : D*V=V*E) (hAD : Commute A D) : Commute B E := by
  have he:=congrArg (fun M : Matrix m m ℝ=>V.transpose*M*V) hAD.eq
  simp only [Matrix.mul_assoc] at he
  rw [hDE,hAB,←Matrix.mul_assoc A V E,hAB,←Matrix.mul_assoc D V B,hDE] at he
  simp only [←Matrix.mul_assoc,hV,Matrix.one_mul] at he
  exact he
end Heisenberg.TensorMatrix
namespace Heisenberg.SlotColor
variable {V : Type} [Fintype V]
lemma magnetization_permute (π : Equiv.Perm V) (c : V → Bool) :
    magnetization (permute π c)=magnetization c := by
  exact π.symm.sum_comp (fun v=>if c v then (1:ℝ)/2 else -1/2)
end Heisenberg.SlotColor
namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]
lemma clockGenerator_mag (R : X → X → Prop) (ℓ : ℕ) :
    Commute (clockGenerator R ℓ) (Matrix.diagonal (SlotColor.magnetization (V:=X×Fin ℓ))) := by
  change clockGenerator R ℓ * _ = _ * clockGenerator R ℓ
  ext a b
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,clockGenerator,Matrix.sum_apply,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [SlotColor.matrix,Matrix.one_apply]
  split_ifs with h h'
  · subst a
    ring
  · subst a
    rw [SlotColor.magnetization_permute]
    ring
  · subst a
    ring
  · ring

lemma spinGenerator_mag (R : X → X → Prop) (hR : ∀ x y,R x y → x≠y) (ℓ : ℕ) :
    Commute (spinGenerator R ℓ) (Matrix.diagonal (physicalMagnetization (X:=X) ℓ)) := by
  apply compress_commute _ (Matrix.diagonal (configMagnetization (X:=X) ℓ)) _ _
    (tensor (fun _ : X=>basis ℓ)) (basis_orthonormal ℓ) (generator_intertwines R hR ℓ) (total_diagonal_intertwines ℓ)
  have hh:=(clockGenerator_mag R ℓ).map (Matrix.reindexAlgEquiv ℝ ℝ (configEquiv (X:=X) ℓ))
  change Commute (Matrix.reindex _ _ _) (Matrix.reindex _ _ _) at hh
  rw [show Matrix.diagonal (SlotColor.magnetization (V:=X×Fin ℓ))=
      Matrix.diagonal (fun c=>id (SlotColor.magnetization c)) from rfl,
    reindex_spectral ℓ id] at hh
  exact hh
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

lemma finiteRepresentation_totalZ (Λ : Finset (Site d)) :
    finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective
      (Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ))=totalZ Λ := by
  have he : Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ)=
      ∑ x : Λ,onsite x (SpinSlots.physicalZ ℓ) := by
    simp only [SpinSlots.physicalZ,local_diagonal,diagonal_fintype_sum]
    rfl
  rw [he,map_sum]
  simp only [finiteRepresentation_z,totalZ]
  exact Finset.sum_coe_sort Λ _

lemma field_commute (Λ : Finset (Site d)) : Commute (hamiltonian d ℓ Λ) (totalZ Λ) := by
  have hh:=(spinGenerator_mag (fun x y : Λ=>NearestNeighbor x.val y.val)
    (fun x y h he=>nearestNeighbor_ne h (congrArg Subtype.val he)) ℓ).map
      (finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective)
  rw [finiteRepresentation_generator,finiteRepresentation_totalZ] at hh
  change ((-2:ℝ) • hamiltonian d ℓ Λ-_) * totalZ Λ=totalZ Λ*((-2:ℝ) • hamiltonian d ℓ Λ-_) at hh
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one] at hh
  have he : (-2:ℝ) • (hamiltonian d ℓ Λ*totalZ Λ)=(-2:ℝ) • (totalZ Λ*hamiltonian d ℓ Λ):=sub_left_injective hh
  have he':=congrArg (fun A : QuasiLocal d ℓ=>(-1/2:ℝ) • A) he
  norm_num only [smul_smul,neg_div,neg_mul_neg,div_mul_cancel₀ _ (by norm_num : (2:ℝ)≠0),one_smul] at he'
  exact he'

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinFieldDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]

attribute [local instance] OAI.GibbsStrip.instNormedAlgebraRat_solutions_1
lemma evolve_hamiltonian_add (H K : E) (hHK : Commute H K) (z : ℂ) (A : E) :
    evolve (H+K) z A=evolve H z (evolve K z A) := by
  unfold evolve
  rw [smul_add,NormedSpace.exp_add_of_commute ((hHK.smul_left _).smul_right _)]
  have he : (-(Complex.I*z)) • (H+K)=(-(Complex.I*z)) • K+(-(Complex.I*z)) • H:=by module
  rw [he,NormedSpace.exp_add_of_commute ((hHK.symm.smul_left _).smul_right _)]
  simp only [mul_assoc]

lemma evolve_of_commute (K A : E) (hKA : Commute K A) (z : ℂ) : evolve K z A=A := by
  rw [evolve,((hKA.smul_left (Complex.I*z)).exp_left).eq,mul_assoc,exp_cancel_left,mul_one]

lemma evolve_smul_real (K A : E) (h : ℝ) (z : ℂ) :
    evolve (h • K) z A=evolve K ((h:ℂ)*z) A := by
  rw [←IsScalarTower.algebraMap_smul ℂ h K]
  simp only [evolve,smul_smul,Complex.coe_algebraMap]
  congr 2 <;> congr 1 <;> ring_nf

end GibbsStrip
namespace Heisenberg
variable {d ℓ : ℕ}

lemma shiftedField_evolve (Γ : Finset (Site d)) (h t : ℝ) (A : QuasiLocal d ℓ) :
    GibbsStrip.evolve (shiftedField Γ h) t A=
      finiteDynamics d ℓ Γ t (GibbsStrip.evolve (totalZ Γ) ((-h*t:ℝ):ℂ) A) := by
  let c : ℝ:=(Fintype.card (SlotTensor.SiteEdges (fun x y : Γ=>NearestNeighbor x.val y.val)):ℝ)*(ℓ:ℝ)^2/8
  have hc : Commute (hamiltonian d ℓ Γ+c • (1:QuasiLocal d ℓ)) (h • totalZ (ℓ:=ℓ) Γ) :=
    ((field_commute (ℓ:=ℓ) Γ).smul_right h).add_left ((Commute.one_left (h • totalZ (ℓ:=ℓ) Γ)).smul_left c)
  change GibbsStrip.evolve (hamiltonian d ℓ Γ+c • (1:QuasiLocal d ℓ)-h • totalZ (ℓ:=ℓ) Γ) t A=_
  rw [sub_eq_add_neg,GibbsStrip.evolve_hamiltonian_add _ _ hc.neg_right]
  rw [GibbsStrip.evolve_hamiltonian_add _ _ ((Commute.one_right _).smul_right c)]
  rw [GibbsStrip.evolve_of_commute (c • (1:QuasiLocal d ℓ)) _ ((Commute.one_left _).smul_left c)]
  rw [←neg_smul,GibbsStrip.evolve_smul_real]
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  rfl

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinTranslations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace Heisenberg
variable {d ℓ : ℕ}

lemma nearestNeighbor_add (x y z : Site d) : NearestNeighbor (x+y) (x+z) ↔ NearestNeighbor y z := by
  simp only [NearestNeighbor,Pi.add_apply,add_sub_add_left_eq_sub]

lemma translation_bond (x y z : Site d) : translation d ℓ x (bond d ℓ y z)=bond d ℓ (x+y) (x+z) := by
  have hadd (A B : QuasiLocal d ℓ) :
      translation d ℓ x (A + B) = translation d ℓ x A + translation d ℓ x B :=
    (translation d ℓ x).map_add' A B
  have hmul (A B : QuasiLocal d ℓ) :
      translation d ℓ x (A * B) = translation d ℓ x A * translation d ℓ x B :=
    (translation d ℓ x).map_mul' A B
  simp only [bond, hadd, hmul, translation_spinX, translation_spinY, translation_spinZ]

lemma directed_bond_double_sum (Λ : Finset (Site d)) :
    (∑ x∈Λ,∑ y∈Λ,if NearestNeighbor x y then bond d ℓ x y else 0)=2 • (-hamiltonian d ℓ Λ) := by
  rw [←directed_bond_sum Λ,sum_siteEdges (fun x y : Λ=>NearestNeighbor x.val y.val) (fun x y : Λ=>bond d ℓ x.val y.val),Fintype.sum_prod_type]
  rw [←Finset.sum_coe_sort Λ]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.sum_coe_sort Λ _).symm

lemma translation_hamiltonian (x : Site d) (Λ : Finset (Site d)) :
    translation d ℓ x (hamiltonian d ℓ Λ)=hamiltonian d ℓ (Λ.image (fun y=>x+y)) := by
  have he :=congrArg (translation d ℓ x) (directed_bond_double_sum (ℓ:=ℓ) Λ)
  have hsum : translation d ℓ x (∑ y∈Λ,∑ z∈Λ,if NearestNeighbor y z then bond d ℓ y z else 0)=
      ∑ y∈Λ.image (fun y=>x+y),∑ z∈Λ.image (fun y=>x+y),if NearestNeighbor y z then bond d ℓ y z else 0 := by
    rw [Finset.sum_image (fun _ _ _ _ he=>add_left_cancel he)]
    simp_rw [Finset.sum_image (fun _ _ _ _ he=>add_left_cancel he)]
    simp only [map_sum,apply_ite,map_zero,translation_bond,nearestNeighbor_add]
  rw [hsum,directed_bond_double_sum,map_nsmul,map_neg] at he
  have he2 : (2:ℂ) • (-hamiltonian d ℓ (Λ.image (fun y=>x+y)))=(2:ℂ) • (-translation d ℓ x (hamiltonian d ℓ Λ)) := by
    simpa only [two_smul] using he
  have he' := congrArg (fun A : QuasiLocal d ℓ=>(1/2:ℂ) • A) he2
  norm_num only [smul_smul,one_div,inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul] at he'
  exact neg_injective he'.symm

lemma translation_exp (x : Site d) (A : QuasiLocal d ℓ) :
    translation d ℓ x (NormedSpace.exp A)=NormedSpace.exp (translation d ℓ x A) := by
  let : NormedAlgebra ℚ (QuasiLocal d ℓ):=NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp (translation d ℓ x) (translationLinear d ℓ x).continuous A

lemma translation_finiteDynamics (x : Site d) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    translation d ℓ x (finiteDynamics d ℓ Λ t A)=
      finiteDynamics d ℓ (Λ.image (fun y=>x+y)) t (translation d ℓ x A) := by
  have hmul (B C : QuasiLocal d ℓ) :
      translation d ℓ x (B * C) = translation d ℓ x B * translation d ℓ x C :=
    (translation d ℓ x).map_mul' B C
  have hsmul (scalar : ℂ) (B : QuasiLocal d ℓ) :
      translation d ℓ x (scalar • B) = scalar • translation d ℓ x B :=
    (translation d ℓ x).toAlgHom.toLinearMap.map_smul scalar B
  simp only [finiteDynamics, hmul, translation_exp, hsmul, translation_hamiltonian]

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinBulk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma translation_totalZ (x : Site d) (Γ : Finset (Site d)) :
    translation d ℓ x (totalZ Γ)=totalZ (Γ.image (fun y=>x+y)) := by
  simp only [totalZ,map_sum,translation_spinZ,Finset.sum_image (fun _ _ _ _ he=>add_left_cancel he)]

lemma translation_evolve (x : Site d) (H : QuasiLocal d ℓ) (z : ℂ) (A : QuasiLocal d ℓ) :
    translation d ℓ x (GibbsStrip.evolve H z A)=GibbsStrip.evolve (translation d ℓ x H) z (translation d ℓ x A) := by
  have hmul (B C : QuasiLocal d ℓ) :
      translation d ℓ x (B * C) = translation d ℓ x B * translation d ℓ x C :=
    (translation d ℓ x).map_mul' B C
  have hsmul (scalar : ℂ) (B : QuasiLocal d ℓ) :
      translation d ℓ x (scalar • B) = scalar • translation d ℓ x B :=
    (translation d ℓ x).toAlgHom.toLinearMap.map_smul scalar B
  simp only [GibbsStrip.evolve, hmul, translation_exp, hsmul]

lemma translation_fieldDynamics (x : Site d) (Γ : Finset (Site d)) (h t : ℝ) (A : QuasiLocal d ℓ) :
    translation d ℓ x (GibbsStrip.evolve (shiftedField Γ h) t A)=
      GibbsStrip.evolve (shiftedField (Γ.image (fun y=>x+y)) h) t (translation d ℓ x A) := by
  simp only [shiftedField_evolve,translation_finiteDynamics,translation_evolve,translation_totalZ]

lemma translated_volume_cancel (x : Site d) (Λ : Finset (Site d)) :
    (Λ.image (fun y=>-x+y)).image (fun y=>x+y)=Λ := by
  rw [Finset.image_image]
  simp only [Function.comp_def,←add_assoc,add_neg_cancel,zero_add]
  exact Finset.image_id'

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAveragedKMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma cubeBoundary_lower_oai (Λ : Finset (Site d)) (ω : State d ℓ) (h : ℝ)
    (A B : QuasiLocal d ℓ) (t : ℝ) :
    cubeBoundary Λ ω h (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B t=
      (Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (translation d ℓ x A*
        GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B)) := by
  simp only [cubeBoundary,ContinuousLinearMap.mul_apply',map_mul,translation_fieldDynamics,translated_volume_cancel]

end Heisenberg
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.cubeBoundary_lower_oai := @OAI.Heisenberg.cubeBoundary_lower_oai
