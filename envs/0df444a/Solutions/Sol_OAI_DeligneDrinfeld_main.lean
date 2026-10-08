-- Prove2me | solution 1 for OAI.DeligneDrinfeld.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:20.446665+00:00
-- url     : https://prove2.me/submissions/2a13e71f-ac2c-4b6d-928e-c891bbcfd6fc

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid
import Theorems.Thm_OAI_DeligneDrinfeld_Differentiation_special_identity
import Theorems.Thm_OAI_DeligneDrinfeld_IntegralFamily_main_of_oddValues
import Theorems.Thm_OAI_DeligneDrinfeld_odd_solution

set_option linter.all false


section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

theorem eval_self : eval x y = LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i <;> simp [eval, x, y]

theorem eval_commutes {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b z : M) (ha : ⁅z,a⁆ = 0) (hb : ⁅z,b⁆ = 0) (p : L) :
    ⁅z,eval a b p⁆ = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval, ha, hb]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [LieHom.map_lie, leibniz_lie, hp, hq]

theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

theorem commute_symm {M : Type*} [LieRing M] {a b : M} (h : ⁅a,b⁆ = 0) : ⁅b,a⁆ = 0 := by
  rw [← lie_skew, h, neg_zero]

theorem evals_commute {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p q : L) :
    ⁅eval a b p,eval c d q⁆ = 0 := by
  apply eval_commutes
  · exact commute_symm (eval_commutes a b c (commute_symm hac) (commute_symm hbc) p)
  · exact commute_symm (eval_commutes a b d (commute_symm had) (commute_symm hbd) p)

theorem eval_add_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p : L) :
    eval (a+c) (b+d) p = eval a b p + eval c d p := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq =>
    simp only [LieHom.map_lie, hp, hq, add_lie, lie_add]
    rw [evals_commute a b c d hac had hbc hbd p q,
      commute_symm (evals_commute a b c d hac had hbc hbd q p)]
    simp

theorem eval_vanish_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b : M) (hab : ⁅a,b⁆ = 0) {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a b p = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    cases hp with
    | generator i => omega
    | @bracket n m p q hp hq =>
      rw [LieHom.map_lie]
      exact evals_commute a b a b (lie_self a) hab (commute_symm hab) (lie_self b) p q
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

theorem eval_central_shift {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (a b c : M) (hac : ⁅a,c⁆ = 0) (hbc : ⁅b,c⁆ = 0)
    {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a (b+c) p = eval a b p := by
  have h := eval_add_of_commuting a b 0 c (lie_zero a) hac (lie_zero b) hbc p
  simpa [eval_vanish_of_commuting 0 c (zero_lie c) hp hn] using h

namespace T4Universal
variable {M : Type*} [LieRing M] [LieAlgebra ℚ M]

def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun e => f e.val.1 e.val.2)

theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]

def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℚ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }

@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j

end T4Universal

def t4Rename (e : Equiv.Perm (Fin 4)) : T4 →ₗ⁅ℚ⁆ T4 :=
  T4Universal.lift (fun i j => t (e i) (e j))
    (fun _ _ => t_comm _ _) (fun _ => t_self _)
    (fun _ _ _ _ hij hik hil hjk hjl hkl => t_disjoint _ _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hil)
      (e.injective.ne hjk) (e.injective.ne hjl) (e.injective.ne hkl))
    (fun _ _ _ hij hik hjk => t_three _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))

@[simp] theorem t4Rename_t (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    t4Rename e (t i j) = t (e i) (e j) := T4Universal.lift_t _ _ _ _ _ _ _

theorem solution_swap {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b p = - eval b a p := by
  have h := congrArg (eval a b) hp.1
  simp only [map_add, map_zero, map_eval, eval_x, eval_y] at h
  exact eq_neg_of_add_eq_zero_left h

theorem solution_three {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b p + eval b (-a-b) p + eval (-a-b) a p = 0 := by
  have h := congrArg (eval a b) hp.2.1
  simpa only [map_add, map_zero, map_eval, map_sub, map_neg, eval_x, eval_y] using h

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

end DeligneDrinfeld

end

end OAI

end

















section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace RationalScalar

section
open scoped TensorProduct
open AssociativeElimination UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing
variable {M N : Type*} [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]
abbrev T (M : Type*) [AddCommGroup M] [Module ℚ M] := ℝ ⊗[ℚ] M
variable {α : Type*}
 def free : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ T (FreeLieAlgebra ℚ α) :=
  FreeLieAlgebra.lift ℝ (fun a => 1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ a)
 @[simp] theorem free_of (a : α) : free (FreeLieAlgebra.of ℝ a)=1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ a := FreeLieAlgebra.lift_of_apply _ _
end

open scoped TensorProduct
 def pentagonMap : L →ₗ[ℚ] T4 :=
  (eval (t 0 1) (t 1 2+t 1 3)).toLinearMap+(eval (t 0 2+t 1 2) (t 2 3)).toLinearMap-
  ((eval (t 1 2) (t 2 3)).toLinearMap+(eval (t 0 1+t 0 2) (t 1 3+t 2 3)).toLinearMap+(eval (t 0 1) (t 1 2)).toLinearMap)

end RationalScalar

namespace BraidSix
variable {M : Type*} [LieRing M]

def total (a b c d e f : M) : M := a+b+c+d+e+f

def matrix (a b c d e f : M) : Fin 4 → Fin 4 → M :=
  ![![0,a,d,f],![a,0,b,e],![d,b,0,c],![f,e,c,0]]

structure Relations (a b c d e f : M) : Prop where
  central : ∀ u∈({a,b,c,d,e,f}:Set M),⁅u,total a b c d e f⁆=0
  ac : ⁅a,c⁆=0
  de : ⁅d,e⁆=0
  aK : ⁅a,a+b+d⁆=0
  bK : ⁅b,a+b+d⁆=0
  bL : ⁅b,b+c+e⁆=0
  cL : ⁅c,b+c+e⁆=0

variable {a b c d e f : M}

theorem bf (h : Relations a b c d e f) : ⁅b,f⁆=0 := by
  calc
    _=⁅b,total a b c d e f⁆-⁅b,a+b+d⁆-⁅b,b+c+e⁆ := by
      simp only [total,lie_add,lie_self]
      abel
    _=0 := by rw [h.central b (by simp),h.bK,h.bL]; abel

theorem dK (h : Relations a b c d e f) : ⁅d,a+b+d⁆=0 := by
  have hh := lie_self (a+b+d)
  rw [add_lie,add_lie,h.aK,h.bK] at hh
  simpa only [zero_add] using hh

theorem eL (h : Relations a b c d e f) : ⁅e,b+c+e⁆=0 := by
  have hh := lie_self (b+c+e)
  rw [add_lie,add_lie,h.bL,h.cL] at hh
  simpa only [zero_add] using hh

theorem aM (h : Relations a b c d e f) : ⁅a,a+e+f⁆=0 := by
  calc
    _=⁅a,total a b c d e f⁆-⁅a,a+b+d⁆-⁅a,c⁆ := by
      simp only [total,lie_add,lie_self]; abel
    _=0 := by rw [h.central a (by simp),h.aK,h.ac]; abel

theorem eM (h : Relations a b c d e f) : ⁅e,a+e+f⁆=0 := by
  calc
    _=⁅e,total a b c d e f⁆-⁅e,b+c+e⁆+⁅d,e⁆ := by
      simp only [total,lie_add,lie_self]
      rw [←lie_skew d e]
      abel
    _=0 := by rw [h.central e (by simp),eL h,h.de]; abel

theorem fM (h : Relations a b c d e f) : ⁅f,a+e+f⁆=0 := by
  have hh := lie_self (a+e+f)
  rw [add_lie,add_lie,aM h,eM h] at hh
  simpa only [zero_add] using hh

theorem dP (h : Relations a b c d e f) : ⁅d,d+c+f⁆=0 := by
  calc
    _=⁅d,total a b c d e f⁆-⁅d,a+b+d⁆-⁅d,e⁆ := by
      simp only [total,lie_add,lie_self]; abel
    _=0 := by rw [h.central d (by simp),dK h,h.de]; abel

theorem cP (h : Relations a b c d e f) : ⁅c,d+c+f⁆=0 := by
  calc
    _=⁅c,total a b c d e f⁆-⁅c,b+c+e⁆+⁅a,c⁆ := by
      simp only [total,lie_add,lie_self]
      rw [←lie_skew a c]
      abel
    _=0 := by rw [h.central c (by simp),h.cL,h.ac]; abel

theorem fP (h : Relations a b c d e f) : ⁅f,d+c+f⁆=0 := by
  have hh := lie_self (d+c+f)
  rw [add_lie,add_lie,dP h,cP h] at hh
  simpa only [zero_add] using hh

theorem matrix_self (i : Fin 4) : matrix a b c d e f i i=0 := by
  fin_cases i <;> rfl

theorem matrix_symm (i j : Fin 4) : matrix a b c d e f i j=matrix a b c d e f j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem matrix_disjoint_0 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (0:Fin 4)≠k) (hil : (0:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 0 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_1 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (1:Fin 4)≠k) (hil : (1:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 1 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_2 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (2:Fin 4)≠k) (hil : (2:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 2 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_3 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (3:Fin 4)≠k) (hil : (3:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 3 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint (h : Relations a b c d e f) (i j k l : Fin 4)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f i j,matrix a b c d e f k l⁆=0 := by
  fin_cases i
  · exact matrix_disjoint_0 h j k l hik hil hjk hjl
  · exact matrix_disjoint_1 h j k l hik hil hjk hjl
  · exact matrix_disjoint_2 h j k l hik hil hjk hjl
  · exact matrix_disjoint_3 h j k l hik hil hjk hjl

theorem matrix_three_0 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (0:Fin 4)≠j) (hik : (0:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 0 j,matrix a b c d e f 0 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_1 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (1:Fin 4)≠j) (hik : (1:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 1 j,matrix a b c d e f 1 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_2 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (2:Fin 4)≠j) (hik : (2:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 2 j,matrix a b c d e f 2 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_3 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (3:Fin 4)≠j) (hik : (3:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 3 j,matrix a b c d e f 3 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three (h : Relations a b c d e f) (i j k : Fin 4)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f i j,matrix a b c d e f i k+matrix a b c d e f j k⁆=0 := by
  fin_cases i
  · exact matrix_three_0 h j k hij hik hjk
  · exact matrix_three_1 h j k hij hik hjk
  · exact matrix_three_2 h j k hij hik hjk
  · exact matrix_three_3 h j k hij hik hjk

end BraidSix

namespace T4Basic
open BraidSix

def a : T4 := t 0 1
def b : T4 := t 1 2
def c : T4 := t 2 3
def d : T4 := t 0 2
def e : T4 := t 1 3
def f : T4 := t 0 3

 theorem induction {P : T4 → Prop} (hz : P 0) (ht : ∀ i j,P (t i j))
    (ha : ∀ p q,P p → P q → P (p+q)) (hs : ∀ (r : ℚ) p,P p → P (r • p))
    (hl : ∀ p q,P p → P q → P ⁅p,q⁆) (p : T4) : P p := by
  induction p using Submodule.Quotient.induction_on with | _ p =>
    induction p using freeLie_induction with
    | h0 => exact hz
    | hg ij =>
      have hh : (FreeLieAlgebra.of ℚ ij : BraidFree)=chord ij.val.1 ij.val.2 := by
        simp only [chord,dif_pos ij.property]
      rw [hh]
      exact ht _ _
    | ha p q hp hq => exact ha _ _ hp hq
    | hs r p hp => exact hs r _ hp
    | hl p q hp hq => exact hl _ _ hp hq

 theorem hom_ext {M : Type*} [LieRing M] [LieAlgebra ℚ M] {F G : T4 →ₗ⁅ℚ⁆ M}
    (h : ∀ i j,F (t i j)=G (t i j)) : F=G := by
  apply LieHom.ext
  intro p
  induction p using induction with
  | hz => simp
  | ht i j => exact h i j
  | ha p q hp hq => simp only [map_add,hp,hq]
  | hs r p hp => simp only [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]

 theorem matrix_t (i j : Fin 4) : matrix a b c d e f i j=t i j := by
  fin_cases i <;> fin_cases j <;> rfl

 theorem central_a : ⁅a,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 1 2 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 1 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 1,t 0 2+t 1 2⁆+⁅t 0 1,t 0 3+t 1 3⁆+⁅t 0 1,t 2 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_b : ⁅b,total a b c d e f⁆=0 := by
  have h₁ := t_three 1 2 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 1 2 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 1 2,t 1 0+t 2 0⁆+⁅t 1 2,t 1 3+t 2 3⁆+⁅t 1 2,t 0 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 1 0,t_comm 2 0]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_c : ⁅c,total a b c d e f⁆=0 := by
  have h₁ := t_three 2 3 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 2 3 1 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 2 3,t 2 0+t 3 0⁆+⁅t 2 3,t 2 1+t 3 1⁆+⁅t 2 3,t 0 1⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 2 0,t_comm 2 1,t_comm 3 0,t_comm 3 1]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_d : ⁅d,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 2 1 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 2 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 2,t 0 1+t 2 1⁆+⁅t 0 2,t 0 3+t 2 3⁆+⁅t 0 2,t 1 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 2 1]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_e : ⁅e,total a b c d e f⁆=0 := by
  have h₁ := t_three 1 3 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 1 3 2 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 1 3,t 1 0+t 3 0⁆+⁅t 1 3,t 1 2+t 3 2⁆+⁅t 1 3,t 0 2⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 1 0,t_comm 3 0,t_comm 3 2]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_f : ⁅f,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 3 1 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 3 2 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 3,t 0 1+t 3 1⁆+⁅t 0 3,t 0 2+t 3 2⁆+⁅t 0 3,t 1 2⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 3 1,t_comm 3 2]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central (p : T4) : ⁅total a b c d e f,p⁆=0 := by
  induction p using induction with
  | hz => exact lie_zero _
  | ht i j =>
    rw [←matrix_t i j]
    have ha := commute_symm central_a
    have hb := commute_symm central_b
    have hc := commute_symm central_c
    have hd := commute_symm central_d
    have he := commute_symm central_e
    have hf := commute_symm central_f
    fin_cases i <;> fin_cases j <;> simp_all [matrix]
  | ha p q hp hq => rw [lie_add,hp,hq,add_zero]
  | hs r p hp => rw [lie_smul,hp,smul_zero]
  | hl p q hp hq => rw [leibniz_lie,hp,hq,zero_lie,lie_zero,add_zero]

 theorem relations : Relations a b c d e f := by
  constructor
  · intro u _; exact commute_symm (central u)
  · exact t_disjoint 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact t_disjoint 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have h := t_three 0 1 2 (by decide) (by decide) (by decide)
    change ⁅t 0 1,t 0 1+t 1 2+t 0 2⁆=0
    simp only [lie_add,lie_self] at h ⊢
    rw [add_comm] at h
    simpa only [zero_add] using h
  · have h := t_three 1 2 0 (by decide) (by decide) (by decide)
    simpa only [a,b,d,lie_add,lie_self,add_zero,t_comm 1 0,t_comm 2 0] using h
  · have h := t_three 1 2 3 (by decide) (by decide) (by decide)
    change ⁅t 1 2,t 1 2+t 2 3+t 1 3⁆=0
    simp only [lie_add,lie_self] at h ⊢
    rw [add_comm] at h
    simpa only [zero_add] using h
  · have h := t_three 2 3 1 (by decide) (by decide) (by decide)
    simpa only [b,c,e,lie_add,lie_self,add_zero,t_comm 2 1,t_comm 3 1] using h

end T4Basic

namespace TangentBraid
open FreeDerivations BraidSix
variable {R M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]

structure Data (a b c d e f A B C D E H I J P Q : M) : Prop where
  base : BraidSix.Relations a b c d e f
  central : ∀ u : M,⁅total a b c d e f,u⁆=0
  aD : ⁅a,D⁆=0
  bB : ⁅b,B⁆=0
  cE : ⁅c,E⁆=0
  KA : ⁅a+b+d,A⁆=0
  LC : ⁅b+c+e,C⁆=0
  special_d : ⁅b,A⁆+⁅d,A+H⁆=0
  special_e : ⁅c,C⁆+⁅e,C+I⁆=0
  cyclic : C+I=J
  pentagon : D+E=A+B+C
  permuted : P+Q= -H+B+J
  dP : ⁅d,P⁆=0
  eQ : ⁅e,Q⁆=0

variable {a b c d e f A B C D E H I J P Q : M}

 theorem crossing {a b h k p q : M} (hab : ⁅a,b⁆=0)
    (hk : k-h=p+q) (hap : ⁅a,p⁆=0) (hbq : ⁅b,q⁆=0) :
    ⁅⁅a,h⁆,b⁆+⁅a,⁅b,k⁆⁆=0 := by
  calc
    _=⁅a,⁅b,k-h⁆⁆ := by
      rw [lie_sub,lie_sub,leibniz_lie a b h,hab,zero_lie,zero_add,←lie_skew b ⁅a,h⁆]
      abel
    _=0 := by
      rw [hk,lie_add,lie_add,hbq,lie_zero,add_zero,leibniz_lie,hab,hap,zero_lie,lie_zero,add_zero]

 theorem inner_pair {a b h : M} (hab : ⁅a,b⁆=0) :
    ⁅⁅a,h⁆,b⁆+⁅a,⁅b,h⁆⁆=0 := by
  rw [leibniz_lie a b h,hab,zero_lie,zero_add,←lie_skew b ⁅a,h⁆]
  abel

 theorem commute_lie {a b h : M} (ha : ⁅a,h⁆=0) (hb : ⁅b,h⁆=0) : ⁅⁅a,b⁆,h⁆=0 := by
  rw [lie_lie,ha,hb,lie_zero,lie_zero,sub_self]

 def vb (b A : M) : M := ⁅b,A⁆
 def vc (c D : M) : M := ⁅c,D⁆
 def vd (b A : M) : M := -⁅b,A⁆
 def ve (b e A D E : M) : M := ⁅b+e,D+E⁆-⁅b,A⁆
 def vf (b c e A D E : M) : M := -vc c D-ve b e A D E

 theorem vd_tangent (h : Data a b c d e f A B C D E H I J P Q) : vd b A=⁅d,A+H⁆ := by
  exact neg_eq_of_add_eq_zero_right h.special_d

 theorem bC (h : Data a b c d e f A B C D E H I J P Q) : ⁅b,C⁆=⁅e,I⁆ := by
  apply sub_eq_zero.mp
  calc
    _=⁅b+c+e,C⁆-(⁅c,C⁆+⁅e,C+I⁆) := by simp only [add_lie,lie_add]; abel
    _=0 := by rw [h.LC,h.special_e,sub_self]

 theorem ve_tangent (h : Data a b c d e f A B C D E H I J P Q) :
    ve b e A D E=⁅e,A+B+C+I⁆ := by
  rw [ve,h.pentagon]
  simp only [add_lie,lie_add]
  rw [h.bB,bC h]
  abel

 theorem gauge_difference (h : Data a b c d e f A B C D E H I J P Q) :
    (A+B+C+I)-(A+H)=P+Q := by
  rw [h.permuted,←h.cyclic]
  abel

 theorem crossing_de (h : Data a b c d e f A B C D E H I J P Q) :
    ⁅vd b A,e⁆+⁅d,ve b e A D E⁆=0 := by
  rw [vd_tangent h,ve_tangent h]
  exact crossing h.base.de (gauge_difference h) h.dP h.eQ

 theorem velocity_K : (0:M)+vb b A+vd b A=0 := by simp only [vb,vd,zero_add,add_neg_cancel]
 theorem velocity_L (h : Data a b c d e f A B C D E H I J P Q) :
    vb b A+vc c D+ve b e A D E=⁅b+c+e,A+B⁆ := by
  calc
    _=⁅b+c+e,D+E⁆ := by simp only [vb,vc,ve,add_lie,lie_add,h.cE]; abel
    _=⁅b+c+e,A+B⁆ := by rw [h.pentagon,lie_add,h.LC,add_zero]

 theorem velocity_b (h : Data a b c d e f A B C D E H I J P Q) :
    vb b A=⁅b,A+B⁆ := by simp only [vb,lie_add,h.bB,add_zero]
 theorem velocity_c (h : Data a b c d e f A B C D E H I J P Q) :
    vc c D=⁅c,A+B⁆+⁅c,C⁆ := by
  have hh := congrArg (fun u => ⁅c,u⁆) h.pentagon
  simpa only [vc,lie_add,h.cE,add_zero] using hh

 theorem velocity_total :
    total (0:M) (vb b A) (vc c D) (vd b A) (ve b e A D E) (vf b c e A D E)=0 := by
  simp only [total,vb,vc,vd,vf]
  abel

 def ja (a : M) : Jet R M := ⟨a,0⟩
 def jb (b A : M) : Jet R M := ⟨b,vb b A⟩
 def jc (c D : M) : Jet R M := ⟨c,vc c D⟩
 def jd (d b A : M) : Jet R M := ⟨d,vd b A⟩
 def je (e b A D E : M) : Jet R M := ⟨e,ve b e A D E⟩
 def jf (f b c e A D E : M) : Jet R M := ⟨f,vf b c e A D E⟩

 theorem relations (h : Data a b c d e f A B C D E H I J P Q) :
    BraidSix.Relations (ja (R:=R) a) (jb b A) (jc c D) (jd d b A)
      (je e b A D E) (jf f b c e A D E) := by
  constructor
  · intro u _
    apply Jet.ext
    · change ⁅u.base,total a b c d e f⁆=0
      exact commute_symm (h.central u.base)
    · change ⁅u.velocity,total a b c d e f⁆+⁅u.base,
        total 0 (vb b A) (vc c D) (vd b A) (ve b e A D E) (vf b c e A D E)⁆=0
      rw [velocity_total,lie_zero,add_zero]
      exact commute_symm (h.central u.velocity)
  · apply Jet.ext
    · exact h.base.ac
    · change ⁅(0:M),c⁆+⁅a,⁅c,D⁆⁆=0
      rw [zero_lie,zero_add,leibniz_lie,h.base.ac,h.aD,zero_lie,lie_zero,add_zero]
  · apply Jet.ext
    · exact h.base.de
    · exact crossing_de h
  · apply Jet.ext
    · exact h.base.aK
    · change ⁅(0:M),a+b+d⁆+⁅a,(0:M)+vb b A+vd b A⁆=0
      rw [velocity_K,zero_lie,lie_zero,add_zero]
  · apply Jet.ext
    · exact h.base.bK
    · change ⁅⁅b,A⁆,a+b+d⁆+⁅b,(0:M)+vb b A+vd b A⁆=0
      rw [velocity_K,lie_zero,add_zero]
      exact commute_lie h.base.bK (commute_symm h.KA)
  · apply Jet.ext
    · exact h.base.bL
    · change ⁅vb b A,b+c+e⁆+⁅b,vb b A+vc c D+ve b e A D E⁆=0
      rw [velocity_L h,velocity_b h]
      exact inner_pair h.base.bL
  · apply Jet.ext
    · exact h.base.cL
    · change ⁅vc c D,b+c+e⁆+⁅c,vb b A+vc c D+ve b e A D E⁆=0
      rw [velocity_L h,velocity_c h,add_lie]
      have hz := commute_lie h.base.cL (commute_symm h.LC)
      rw [hz,add_zero]
      exact inner_pair h.base.cL

end TangentBraid

namespace TriangleSolutions
variable {M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)
variable (u v w : M) (hu : ⁅u,u+v+w⁆=0) (hv : ⁅v,u+v+w⁆=0)

omit [LieAlgebra ℚ M] in
include hu hv in
theorem third : ⁅w,u+v+w⁆=0 := by
  have h := lie_self (u+v+w)
  rw [add_lie,add_lie,hu,hv,zero_add,zero_add] at h
  exact h

include hqn hn hu hv in
theorem shift_u : eval u w q=eval u (-u-v) q := by
  have hsum : w=(-u-v)+(u+v+w) := by abel
  have hneg : ⁅-u-v,u+v+w⁆=0 := by rw [sub_lie,neg_lie,hu,hv,neg_zero,sub_zero]
  conv_lhs => rw [hsum]
  exact eval_central_shift u (-u-v) (u+v+w) hu hneg hqn (by omega)

include hqn hn hu hv in
theorem shift_v : eval v w q=eval v (-u-v) q := by
  have hsum : w=(-u-v)+(u+v+w) := by abel
  have hneg : ⁅-u-v,u+v+w⁆=0 := by rw [sub_lie,neg_lie,hu,hv,neg_zero,sub_zero]
  conv_lhs => rw [hsum]
  exact eval_central_shift v (-u-v) (u+v+w) hv hneg hqn (by omega)

include hq hqn hn hu hv in
theorem cyclic : eval u v q+eval v w q=eval u w q := by
  have h := solution_three hq u v
  rw [solution_swap hq (-u-v) u,←shift_u hqn hn u v w hu hv,
    ←shift_v hqn hn u v w hu hv] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

include hq hqn hn hu hv in
theorem special : ⁅v,eval u v q⁆+⁅w,eval u v q+eval v w q⁆=0 := by
  have h := Differentiation.special_identity hq hqn hn v u
  have hc : -v-u= -u-v := by abel
  rw [hc,←shift_u hqn hn u v w hu hv] at h
  have hk : ⁅u+v+w,eval u w q⁆=0 :=
    eval_commutes u w (u+v+w) (commute_symm hu) (commute_symm (third u v w hu hv)) q
  have he : ⁅-u-v,eval u w q⁆=⁅w,eval u w q⁆ := by
    have hh : -u-v=w-(u+v+w) := by abel
    rw [hh,sub_lie,hk,sub_zero]
  rw [he] at h
  rw [cyclic hq hqn hn u v w hu hv]
  exact h

end TriangleSolutions

namespace T4SolutionData
open T4Basic

def A (q : L) : T4 := eval a b q
def B (q : L) : T4 := eval (a+d) (e+c) q
def C (q : L) : T4 := eval b c q
def D (q : L) : T4 := eval (d+b) c q
def E (q : L) : T4 := eval a (b+e) q
def H (q : L) : T4 := eval b d q
def I (q : L) : T4 := eval c e q
def J (q : L) : T4 := eval b e q
def P (q : L) : T4 := eval (a+b) e q
def Q (q : L) : T4 := eval d (b+c) q

 theorem pentagon {q : L} (hq : q∈W) : D q+E q=A q+B q+C q := by
  calc
    _=E q+D q := add_comm _ _
    _=C q+B q+A q := hq.2.2
    _=_ := by abel

 theorem permuted {q : L} (hq : q∈W) : P q+Q q= -H q+B q+J q := by
  have hh := congrArg (t4Rename (Equiv.swap (1:Fin 4) 2)) hq.2.2
  simp only [map_add,map_eval,t4Rename_t] at hh
  change eval d (b+c) q+eval (a+b) e q=eval b e q+eval (d+a) (c+e) q+eval d b q at hh
  rw [add_comm d a,add_comm c e,solution_swap hq d b] at hh
  calc
    _=Q q+P q := add_comm _ _
    _=J q+B q+(-H q) := hh
    _=_ := by abel

 theorem data {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    TangentBraid.Data a b c d e f (A q) (B q) (C q) (D q) (E q)
      (H q) (I q) (J q) (P q) (Q q) := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using relations.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using relations.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using BraidSix.dK relations
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using relations.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using relations.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using BraidSix.eL relations
  constructor
  · exact relations
  · exact central
  · exact eval_commutes (d+b) c a (by rwa [add_comm]) relations.ac q
  · exact eval_commutes (a+d) (e+c) b hb (by rwa [add_comm]) q
  · exact eval_commutes a (b+e) c (commute_symm relations.ac) hc q
  · exact eval_commutes a b (a+b+d) (commute_symm relations.aK) (commute_symm relations.bK) q
  · exact eval_commutes b c (b+c+e) (commute_symm relations.bL) (commute_symm relations.cL) q
  · exact TriangleSolutions.special hq hqn hn a b d relations.aK relations.bK
  · exact TriangleSolutions.special hq hqn hn b c e relations.bL relations.cL
  · exact TriangleSolutions.cyclic hq hqn hn b c e relations.bL relations.cL
  · exact pentagon hq
  · exact permuted hq
  · exact eval_commutes (a+b) e d hd relations.de q
  · exact eval_commutes d (b+c) e (commute_symm relations.de) he q

end T4SolutionData

namespace T4Derivation
open T4Basic T4SolutionData FreeDerivations TangentBraid
variable {n : ℕ} {q : L}

def jets (q : L) : Fin 4 → Fin 4 → Jet ℚ T4 :=
  BraidSix.matrix (ja a) (jb b (A q)) (jc c (T4SolutionData.D q)) (jd d b (A q))
    (je e b (A q) (T4SolutionData.D q) (E q)) (jf f b c e (A q) (T4SolutionData.D q) (E q))

@[simp] theorem jets_base (q : L) (i j : Fin 4) : (jets q i j).base=t i j := by
  rw [←matrix_t i j]
  fin_cases i <;> fin_cases j <;> rfl

def lift (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : T4 →ₗ⁅ℚ⁆ Jet ℚ T4 :=
  T4Universal.lift (jets q) BraidSix.matrix_symm BraidSix.matrix_self
    (fun i j k l _ hik hil hjk hjl _ =>
      BraidSix.matrix_disjoint (TangentBraid.relations (data hq hqn hn)) i j k l hik hil hjk hjl)
    (BraidSix.matrix_three (TangentBraid.relations (data hq hqn hn)))

@[simp] theorem lift_t (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (i j : Fin 4) :
    lift hq hqn hn (t i j)=jets q i j := T4Universal.lift_t _ _ _ _ _ _ _

@[simp] theorem lift_base (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : T4) :
    (lift hq hqn hn p).base=p := by
  have he : Jet.baseHom.comp (lift hq hqn hn)=LieHom.id := by
    apply T4Basic.hom_ext
    intro i j
    change (lift hq hqn hn (t i j)).base=t i j
    rw [lift_t,jets_base]
  exact LieHom.congr_fun he p

def derivation (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : LieDerivation ℚ T4 T4 where
  toFun p := (lift hq hqn hn p).velocity
  map_add' p r := by change (lift hq hqn hn (p+r)).velocity=_; rw [map_add]; rfl
  map_smul' s p := by change (lift hq hqn hn (s • p)).velocity=_; rw [map_smul]; rfl
  leibniz' p r := by
    change (lift hq hqn hn ⁅p,r⁆).velocity=⁅p,(lift hq hqn hn r).velocity⁆-⁅r,(lift hq hqn hn p).velocity⁆
    rw [LieHom.map_lie,Jet.velocity_lie,lift_base,lift_base,sub_eq_add_neg,lie_skew,add_comm]

@[simp] theorem derivation_t (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (i j : Fin 4) :
    derivation hq hqn hn (t i j)=(jets q i j).velocity := by
  change (lift hq hqn hn (t i j)).velocity=_
  rw [lift_t]

@[simp] theorem derivation_a (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn a=0 := by
  exact derivation_t hq hqn hn 0 1
@[simp] theorem derivation_b (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn b=⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 1 2
@[simp] theorem derivation_c (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn c=⁅c,T4SolutionData.D q⁆ := by
  exact derivation_t hq hqn hn 2 3
@[simp] theorem derivation_d (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn d= -⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 0 2
@[simp] theorem derivation_e (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    derivation hq hqn hn e=⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 1 3
@[simp] theorem derivation_f (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    derivation hq hqn hn f= -⁅c,T4SolutionData.D q⁆-(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆) := by
  exact derivation_t hq hqn hn 0 3

end T4Derivation

end DeligneDrinfeld

end

end OAI

end


section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace GaugeCompatibility
open CategoryGauge

 theorem intertwine {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (D : LieDerivation ℚ M M) (q : L) (a b : M)
    (hx : D a=0) (hy : D b=⁅b,eval a b q⁆) (p : L) :
    D (eval a b p)=eval a b (derivation q p) := by
  induction p using freeLie_induction with
  | h0 => simp only [map_zero]
  | hg i =>
    cases i
    · change D (eval a b x)=eval a b (derivation q x)
      simp only [eval_x,derivation_apply,D_x,map_zero,hx]
    · change D (eval a b y)=eval a b (derivation q y)
      simp only [eval_y,derivation_apply,D_y,LieHom.map_lie,hy]
  | ha p r hp hr => simp only [map_add,hp,hr]
  | hs s p hp => simp only [map_smul,hp]
  | hl p r hp hr => simp only [LieHom.map_lie,LieDerivation.apply_lie_eq_add,map_add,hp,hr]

 theorem compatible {M N O P : Type*} [LieRing M] [LieAlgebra ℚ M]
    [LieRing N] [LieAlgebra ℚ N] (g : Data ℚ M O) (k : Data ℚ N P)
    (F : M →ₗ⁅ℚ⁆ N) (f : O → P) (K : N)
    (hh : ∀ p,k.h (f p)=F (g.h p)+K)
    (hd : ∀ z,k.d (F z)+⁅K,F z⁆=F (g.d z)) : Compatible F f g k := by
  constructor
  · intro p q
    simp only [unit,hh,map_sub]
    abel
  · intro p z
    simp only [loop_apply,hh,add_lie,map_add,LieHom.map_lie]
    rw [←hd z]
    abel

end GaugeCompatibility

namespace ThreeSolutionCategory
open CategoricalValues CategoryGauge

def data (q : L) : Data ℚ L (Fin 3) :=
  ⟨derivation q,![0,q,q+rotateLie q]⟩

@[simp] theorem loop_zero (q : L) : loop (data q) 0=derivation q := by
  ext p
  simp [loop_apply,data]
@[simp] theorem value (q : L) : unit (data q) 0 1=q := by simp [unit,data]

 theorem anti {q : L} (hq : q∈W) : swapLie q= -q := by
  exact eq_neg_of_add_eq_zero_right hq.1

 theorem rotating_anti {q : L} (hq : q∈W) : swapLie (rotateLie q)=q+rotateLie q := by
  change eval y x (eval y (-x-y) q)=q+eval y (-x-y) q
  rw [map_eval,eval_y,map_sub,map_neg,eval_x,eval_y]
  have h := solution_three hq x y
  rw [eval_self,LieHom.id_apply,solution_swap hq (-x-y) x] at h
  have hs : -y-x= -x-y := by abel
  rw [hs]
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)).symm

 theorem rotating_twice {q : L} (hq : q∈W) : rotateLie (q+rotateLie q)= -q := by
  rw [map_add]
  have hsq := LieHom.congr_fun rotate_squared q
  change rotateLie (rotateLie q)=eval (-x-y) x q at hsq
  rw [hsq]
  exact eq_neg_of_add_eq_zero_right (by simpa only [rotateLie,add_assoc] using hq.2.1)

 theorem swap {q : L} (hq : q∈W) : Compatible swapLie swapObjects (data q) (data q) := by
  apply GaugeCompatibility.compatible (data q) (data q) swapLie swapObjects q
  · intro i
    fin_cases i
    · simp [data,swapObjects]
    · change 0=swapLie q+q
      rw [anti hq,neg_add_cancel]
    · change q+rotateLie q=swapLie (q+rotateLie q)+q
      rw [map_add,anti hq,rotating_anti hq]
      abel
  · intro p
    have hh := GaugeCompatibility.intertwine (loop (data q) 1) q y x
      (by simp only [loop_apply,data,D_y,derivation_apply,Matrix.cons_val_one,Matrix.cons_val_zero]; rw [←lie_skew y q]; abel)
      (by
        simp only [loop_apply,data,derivation_apply,D_x,zero_add,Matrix.cons_val_one,Matrix.cons_val_zero]
        change ⁅q,x⁆=⁅x,swapLie q⁆
        rw [anti hq,lie_neg,←lie_skew x q,neg_neg]) p
    simpa only [loop_apply,data,Matrix.cons_val_one,Matrix.cons_val_zero,swapLie,rotateLie] using hh

 theorem rotate {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    Compatible rotateLie rotateObjects (data q) (data q) := by
  have hs : ⁅x,q⁆=⁅-x-y,rotateLie q⁆ := by
    have hh := Differentiation.special_identity hq hqn hn x y
    have hanti : eval y x q= -q := anti hq
    rw [hanti,lie_neg] at hh
    exact neg_add_eq_zero.mp hh
  apply GaugeCompatibility.compatible (data q) (data q) rotateLie rotateObjects q
  · intro i
    fin_cases i
    · simp [data,rotateObjects]
    · change q+rotateLie q=rotateLie q+q
      exact add_comm _ _
    · change 0=rotateLie (q+rotateLie q)+q
      rw [rotating_twice hq,neg_add_cancel]
  · intro p
    have hh := GaugeCompatibility.intertwine (loop (data q) 1) q y (-x-y)
      (by simp only [loop_apply,data,D_y,derivation_apply,Matrix.cons_val_one,Matrix.cons_val_zero]; rw [←lie_skew y q]; abel)
      (by
        simp only [loop_apply,data,Matrix.cons_val_one,Matrix.cons_val_zero,map_sub,map_neg,
          derivation_apply,D_x,D_y,zero_add]
        change -⁅q,x⁆-(⁅y,q⁆+⁅q,y⁆)=⁅-x-y,rotateLie q⁆
        rw [←hs,←lie_skew x q,←lie_skew y q]
        abel) p
    simpa only [loop_apply,data,Matrix.cons_val_one,Matrix.cons_val_zero,swapLie,rotateLie] using hh

end ThreeSolutionCategory

namespace FourSolutionCategory
open T4Basic T4SolutionData CategoryGauge
variable {n : ℕ} {q : L}

def data (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : Data ℚ T4 (Fin 5) :=
  ⟨T4Derivation.derivation hq hqn hn,![0,A q,A q+B q,T4SolutionData.D q,T4SolutionData.D q+E q]⟩

 theorem edge (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (X Y : T4) (s t : Fin 5)
    (hu : unit (data hq hqn hn) s t=eval X Y q)
    (hx : loop (data hq hqn hn) s X=0)
    (hy : loop (data hq hqn hn) s Y=⁅Y,eval X Y q⁆) :
    EdgeCompatible (eval X Y) 0 1 s t (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  constructor
  · rw [ThreeSolutionCategory.value]; exact hu
  · intro p
    rw [ThreeSolutionCategory.loop_zero]
    exact GaugeCompatibility.intertwine _ q X Y hx hy p

 theorem AB (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval a b) 0 1 0 1 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  apply edge hq hqn hn
  · simp [data,unit,A]
  · simp [data,loop_apply]
  · simp [data,loop_apply,A]

 theorem AD (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval (d+b) c) 0 1 0 3 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  apply edge hq hqn hn
  · simp [data,unit,T4SolutionData.D]
  · simp only [data,loop_apply,Matrix.cons_val_zero,zero_lie,add_zero,map_add,
      T4Derivation.derivation_d,T4Derivation.derivation_b,neg_add_cancel]
  · simp [data,loop_apply,T4SolutionData.D]

 theorem DE (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval a (b+e)) 0 1 3 4 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · simp [data,unit,E]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn a+⁅T4SolutionData.D q,a⁆=0
    rw [T4Derivation.derivation_a,zero_add]
    exact commute_symm hd.aD
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (b+e)+⁅T4SolutionData.D q,b+e⁆=⁅b+e,E q⁆
    rw [map_add,T4Derivation.derivation_b,T4Derivation.derivation_e,lie_add,←lie_skew (b+e) (T4SolutionData.D q)]
    abel

 theorem BC (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval (a+d) (e+c)) 0 1 1 2 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · simp [data,unit,B]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (a+d)+⁅A q,a+d⁆=0
    rw [map_add,T4Derivation.derivation_a,T4Derivation.derivation_d,zero_add]
    calc
      _= -⁅a+b+d,A q⁆ := by simp only [add_lie,lie_add]; rw [←lie_skew a (A q),←lie_skew d (A q)]; abel
      _=0 := by rw [hd.KA,neg_zero]
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn (e+c)+⁅A q,e+c⁆=⁅e+c,B q⁆
    rw [map_add,T4Derivation.derivation_e,T4Derivation.derivation_c]
    have hl := TangentBraid.velocity_L hd
    change ⁅b,A q⁆+⁅c,T4SolutionData.D q⁆+(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆)=⁅b+c+e,A q+B q⁆ at hl
    calc
      _=(⁅b,A q⁆+⁅c,T4SolutionData.D q⁆+(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆))-⁅b,A q⁆+⁅A q,e+c⁆ := by abel
      _=⁅b+c+e,A q+B q⁆-⁅b,A q⁆+⁅A q,e+c⁆ := by rw [hl]
      _=⁅e+c,B q⁆ := by
        simp only [add_lie,lie_add]
        rw [hd.bB,←lie_skew e (A q),←lie_skew c (A q)]
        abel

 theorem CE (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    EdgeCompatible (eval b c) 0 1 2 4 (ThreeSolutionCategory.data q) (data hq hqn hn) := by
  have hd := T4SolutionData.data hq hqn hn
  apply edge hq hqn hn
  · change (T4SolutionData.D q+E q)-(A q+B q)=C q
    rw [pentagon hq]
    abel
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn b+⁅A q+B q,b⁆=0
    rw [T4Derivation.derivation_b,add_lie,←lie_skew b (A q),commute_symm hd.bB]
    abel
  · rw [loop_apply]
    change T4Derivation.derivation hq hqn hn c+⁅A q+B q,c⁆=⁅c,C q⁆
    rw [T4Derivation.derivation_c]
    have hc := TangentBraid.velocity_c hd
    change ⁅c,T4SolutionData.D q⁆=⁅c,A q+B q⁆+⁅c,C q⁆ at hc
    rw [hc,←lie_skew c (A q+B q)]
    abel

end FourSolutionCategory

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
end

section
namespace SolutionGrading
open LieGrading AssociativeElimination UniversalEmbedding

def dilation (c : ℚ) : L →ₗ⁅ℚ⁆ L := eval (c • x) (c • y)
@[simp] theorem dilation_x (c : ℚ) : dilation c x=c • x := eval_x _ _
@[simp] theorem dilation_y (c : ℚ) : dilation c y=c • y := eval_y _ _

end SolutionGrading

end

namespace CategoricalValues

def OddWitnesses : Prop := ∀ k,∃ w : Witness,
  value w∈Ln (oddWeight k) ∧
  (AssociativeElimination.embed (value w)).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0

theorem main_of_oddWitnesses (h : OddWitnesses) : MainStatement := by
  apply IntegralFamily.main_of_oddValues values
  intro k
  obtain ⟨w,hw,hc⟩ := h k
  exact ⟨⟨value w,value_mem w,hw⟩,⟨w,rfl⟩,hc⟩

open CategoryGauge

def ofSolution {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : Witness where
  three := ThreeSolutionCategory.data q
  four := FourSolutionCategory.data hq hqn hn
  swap := ThreeSolutionCategory.swap hq
  rotate := ThreeSolutionCategory.rotate hq hqn hn
  kill_x := by simp [ThreeSolutionCategory.loop_zero,derivation_apply]
  kill_y := by
    simp only [loop_apply,ThreeSolutionCategory.data,Matrix.cons_val_one,Matrix.cons_val_zero,
      derivation_apply,D_y,←lie_skew y q]
    abel
  AD := FourSolutionCategory.AD hq hqn hn
  DE := FourSolutionCategory.DE hq hqn hn
  AB := FourSolutionCategory.AB hq hqn hn
  BC := FourSolutionCategory.BC hq hqn hn
  CE := FourSolutionCategory.CE hq hqn hn

@[simp] theorem value_ofSolution {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    value (ofSolution hq hqn hn)=q := ThreeSolutionCategory.value q

theorem main_of_oddSolutions
    (h : ∀ k,∃ q : L,q∈Wn (oddWeight k) ∧
      (AssociativeElimination.embed q).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0) :
    MainStatement := by
  apply main_of_oddWitnesses
  intro k
  obtain ⟨q,hq,hc⟩ := h k
  exact ⟨ofSolution hq.1 hq.2 (by unfold oddWeight; omega),by simpa using hq.2,by simpa using hc⟩

end CategoricalValues

open AssociativeElimination WordGrading

end DeligneDrinfeld

end

end OAI

end

section
open OAI.DeligneDrinfeld

theorem solution : MainStatement :=
  OAI.DeligneDrinfeld.CategoricalValues.main_of_oddSolutions (fun k => by
    obtain ⟨q, hq, hc⟩ := OAI.DeligneDrinfeld.odd_solution k
    have e : oddWeight k - 1 = 2 * k + 2 := by simp [oddWeight]
    rw [e]
    exact ⟨q, hq, hc⟩)

end
