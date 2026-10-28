-- Prove2me | solution 1 for OAI.Heisenberg.finiteRepresentation_field
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:42:05.507975+00:00
-- url     : https://prove2.me/submissions/3eafef35-4d8f-4381-87af-23c60c90cf65

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM000

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

open scoped Classical BigOperators
namespace Heisenberg.TensorMatrix
variable {X α β γ R : Type*} [Fintype X] [DecidableEq X] [CommSemiring R]

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

end Heisenberg.TensorMatrix

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

namespace Heisenberg.TensorMatrix
variable {X α R : Type*} [Fintype X] [DecidableEq X] [DecidableEq α] [CommSemiring R]
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

lemma finiteRepresentation_field_oai (Λ : Finset (Site d)) (h : ℝ) :
    finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective
      ((-1/2:ℝ) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ-
        h • Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ))=shiftedField Λ h := by
  rw [map_sub,map_smul,map_smul,finiteRepresentation_generator,finiteRepresentation_totalZ,shiftedField]
  module

end Heisenberg
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.finiteRepresentation_field_oai := @OAI.Heisenberg.finiteRepresentation_field_oai
