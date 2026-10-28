-- Prove2me | solution 1 for OAI.SharpLogRamsey.ActualPivot.Book.live_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:29:50.025485+00:00
-- url     : https://prove2.me/submissions/73424187-3123-4659-ac00-c65b22037d46

import Mathlib
import Definitions.Def_OAIQ045S002

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_LevelLosses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in

lemma incidenceCount_eq_card (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount S T=((S.product T).filter (fun z => Incident z.1 z.2)).card := by
  classical
  simp only [Finset.product_eq_sprod,incidenceCount,Finset.card_filter]
  rw [Finset.sum_product S T,Finset.sum_comm]

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SupportMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.SupportMixtures
noncomputable section
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

omit [Fintype A] in
lemma kernel_nonneg (S : Finset A) (a : A) : 0≤kernel S a := by
  unfold kernel
  split_ifs <;> positivity

lemma pairing_mono (f f' : A→ℝ) (g g' : B→ℝ) (R : A→B→ℝ)
    (hf : ∀ a, 0≤f a) (hg : ∀ b, 0≤g b) (hR : ∀ a b, 0≤R a b)
    (hff : ∀ a,f a≤f' a) (hgg : ∀ b,g b≤g' b) :
    pairing f g R≤pairing f' g' R := by
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_right _ (hR a b)
  exact mul_le_mul (hff a) (hgg b) (hg b) ((hf a).trans (hff a))

lemma pairing_scale (f : A→ℝ) (g : B→ℝ) (R : A→B→ℝ) (c d : ℝ) :
    pairing (fun a => c*f a) (fun b => d*g b) R=c*d*pairing f g R := by
  simp only [pairing,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

lemma independent_pairing (w : I→ℝ) (v : J→ℝ)
    (S : I→Finset A) (T : J→Finset B) (R : A→B→ℝ) :
    (∑ i, ∑ j, w i*v j*pairing (kernel (S i)) (kernel (T j)) R)=
      pairing (mixture w S) (mixture v T) R := by
  simp only [pairing,mixture,mul_sum,sum_mul]
  calc
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
        w i*v j*(kernel (S i) a*kernel (T j) b*R a b) := by
      calc
        _ = ∑ ij : I×J, ∑ ab : A×B,
            w ij.1*v ij.2*(kernel (S ij.1) ab.1*kernel (T ij.2) ab.2*R ab.1 ab.2) := by
          simp only [Fintype.sum_prod_type]
        _ = ∑ ab : A×B, ∑ ij : I×J,
            w ij.1*v ij.2*(kernel (S ij.1) ab.1*kernel (T ij.2) ab.2*R ab.1 ab.2) := sum_comm
        _ = _ := by simp only [Fintype.sum_prod_type]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro i _
      ring

theorem independent_pairing_le (w : I→ℝ) (v : J→ℝ)
    (S : I→Finset A) (T : J→Finset B) (R : A→B→ℝ)
    (p : A→ℝ) (q : B→ℝ) (c d : ℝ)
    (hw : ∀ i, 0≤w i) (hv : ∀ j, 0≤v j)
    (hR : ∀ a b, 0≤R a b)
    (hS : ∀ a, mixture w S a ≤ c*p a) (hT : ∀ b, mixture v T b≤d*q b) :
    (∑ i, ∑ j, w i*v j*pairing (kernel (S i)) (kernel (T j)) R)≤
      c*d*pairing p q R := by
  rw [independent_pairing]
  rw [←pairing_scale]
  apply pairing_mono _ _ _ _ R _ _ hR hS hT
  · intro a
    exact sum_nonneg (fun i _ => mul_nonneg (hw i) (kernel_nonneg _ a))
  · intro b
    exact sum_nonneg (fun j _ => mul_nonneg (hv j) (kernel_nonneg _ b))

lemma one_sided_pairing (w : I→ℝ) (S : I→Finset A) (q : B→ℝ) (R : A→B→ℝ) :
    (∑ i, w i*pairing (kernel (S i)) q R)=pairing (mixture w S) q R := by
  simp only [pairing,mixture,mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro i _
  ring

theorem one_sided_pairing_le (w : I→ℝ) (S : I→Finset A)
    (p : A→ℝ) (q : B→ℝ) (R : A→B→ℝ) (c : ℝ)
    (hw : ∀ i,0≤w i) (hq : ∀ b,0≤q b) (hR : ∀ a b,0≤R a b)
    (hS : ∀ a,mixture w S a ≤ c*p a) :
    (∑ i,w i*pairing (kernel (S i)) q R) ≤ c*pairing p q R := by
  rw [one_sided_pairing]
  have H := pairing_mono (mixture w S) (fun a => c*p a) q q R
    (fun a => sum_nonneg (fun i _ => mul_nonneg (hw i) (kernel_nonneg _ a)))
      hq hR hS (fun _ => le_rfl)
  have he := pairing_scale p q R c 1
  simp only [one_mul,mul_one] at he
  rwa [he] at H

lemma kernel_incidence (S : Finset A) (T : Finset B) (R : A→B→Prop) :
    pairing (kernel S) (kernel T) (fun a b => if R a b then 1 else 0)=
      (((S×ˢT).filter (fun z => R z.1 z.2)).card:ℝ)/((S.card:ℝ)*(T.card:ℝ)) := by
  classical
  let U := (S×ˢT).filter (fun z => R z.1 z.2)
  have he : pairing (kernel S) (kernel T) (fun a b => if R a b then 1 else 0)=
      ∑ z : A×B, if z∈U then 1/((S.card:ℝ)*(T.card:ℝ)) else 0 := by
    simp only [pairing,Fintype.sum_prod_type]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    by_cases ha : a∈S <;> by_cases hb : b∈T <;> by_cases hr : R a b <;>
      simp [kernel,U,ha,hb,hr,mul_comm]
  rw [he,←sum_filter]
  have hf : univ.filter (fun z => z∈U)=U := by ext; simp
  rw [hf,sum_const,nsmul_eq_mul]
  change (U.card:ℝ)*(1/((S.card:ℝ)*(T.card:ℝ)))=(U.card:ℝ)/_
  ring

end
end SharpLogRamsey.SupportMixtures

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_SupportIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

lemma good_pairing_eq_event (p : Law A) (q : Law B) (S : Finset A) (T : Finset B)
    (R : A → B → Prop) :
    SupportMixtures.pairing (fun a => if a ∈ S then p.mass a else 0)
      (fun b => if b ∈ T then q.mass b else 0) (fun a b => if R a b then 1 else 0) =
    (p.prod q).event (univ.filter (fun z => z.1 ∈ S ∧ z.2 ∈ T ∧ R z.1 z.2)) := by
  simp only [SupportMixtures.pairing, Law.event, sum_filter, Fintype.sum_prod_type, Law.prod]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ T <;> by_cases hR : R a b <;>
    simp [ha, hb, hR]

lemma pairing_reverse (f : A → ℝ) (g : B → ℝ) (R : A → B → ℝ) :
    SupportMixtures.pairing f g R =
      SupportMixtures.pairing g f (fun b a => R a b) := by
  unfold SupportMixtures.pairing
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  rw [mul_comm (f a)]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FreshFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι→Type*} [∀ i,Fintype (α i)]

lemma family_mass_split (p : ∀ i,Law (α i)) (i : ι) (z : ∀ j,α j) :
    (piLaw p).mass z=(p i).mass (z i)*(outsideLaw p i).mass (outside i z) := by
  change (∏ j,(p j).mass (z j))=(p i).mass (z i)*
    (∏ j : {j : ι // j≠i},(p j).mass (z j))
  have he : (∏ j ∈ (univ : Finset ι).erase i,(p j).mass (z j))=
      ∏ j : {j : ι // j≠i},(p j).mass (z j) :=
    Finset.prod_subtype _ (by simp) _
  rw [←he]
  exact (mul_prod_erase univ (fun j=>(p j).mass (z j)) (mem_univ i)).symm

theorem family_integral (p : ∀ i,Law (α i)) (i : ι)
    (f : Outside (α:=α) i→α i→ℝ) :
    (∑ z,(piLaw p).mass z*f (outside i z) (z i)) =
      ∑ s,(outsideLaw p i).mass s*(∑ x,(p i).mass x*f s x) := by
  calc
    _ = ∑ z,(p i).mass (z i)*(outsideLaw p i).mass (outside i z)*f (outside i z) (z i) := by
      apply sum_congr rfl
      intro z _
      rw [family_mass_split]
    _ = ∑ y : α i×Outside (α:=α) i,(p i).mass y.1*(outsideLaw p i).mass y.2*f y.2 y.1 :=
        Fintype.sum_equiv (Equiv.piSplitAt i α) _ _ (fun _=>rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type,sum_comm]
      apply sum_congr rfl
      intro s _
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_FreshExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I]
variable {α : I→Type*}

theorem arrive_congr (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z z' : ∀ i,α i) (target : I)
    (hz : ∀ j,j≠target→z j=z' j) (t : BinaryTree I) (U : Domains A B) :
    arrive choose read z target t U=arrive choose read z' target t U := by
  induction t generalizing U with
  | nil=>rfl
  | node i l r hl hr=>
    simp only [arrive]
    split_ifs with hi
    · rfl
    · rw [hz i hi]
      cases choose i (z' i) U with
      | none=>rfl
      | some c=>
        simp only
        rw [hl,hr]

theorem arrive_outside (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I) (dummy : α target)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) :
    arrive choose read z target t U=
      outsideState choose read target dummy t U (outside target z) := by
  apply arrive_congr
  intro j hj
  simp only [Equiv.piSplitAt_symm_apply,dite_eq_right hj,outside]

variable [Fintype I] [∀ i,Fintype (α i)]

theorem produced_bound (p : ∀ i,Law (α i))
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I) (dummy : α target)
    (f : Domains A B→α target→ℝ) (t : BinaryTree I) (U : Domains A B)
    (B₀ : ℝ) (hB : 0≤B₀)
    (hlocal : ∀ V,(∑ x,(p target).mass x*f V x)≤B₀) :
    (∑ z,(piLaw p).mass z*produced choose read target f t U z)≤B₀ := by
  let g := fun s : Outside (α:=α) target=>fun x : α target=>
    match outsideState choose read target dummy t U s with
    | none=>0
    | some V=>f V x
  have he (z : ∀ i,α i) : produced choose read target f t U z=
      g (outside target z) (z target) := by
    unfold produced g
    rw [arrive_outside choose read target dummy] <;> rfl
  simp_rw [he]
  rw [family_integral]
  calc
    _ ≤ ∑ s,(outsideLaw p target).mass s*B₀ := by
      apply sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ ((outsideLaw p target).nonneg s)
      dsimp only [g]
      cases outsideState choose read target dummy t U s with
      | none=>simpa only [mul_zero,sum_const_zero] using hB
      | some V=>exact hlocal V
    _ = B₀ := by rw [←sum_mul,(outsideLaw p target).total,one_mul]

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FreshAccrual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

lemma separated_of_nodup (t : BinaryTree I) (h : (inorder t).Nodup) : Separated t := by
  induction t with
  | nil=>trivial
  | node i l r hl hr=>
    simp only [inorder,List.nodup_append,List.nodup_cons] at h
    refine ⟨hl h.1,hr h.2.1.2,?_,?_,?_⟩
    · intro hi
      exact h.2.2 i (by simpa only [labels,List.mem_toFinset] using hi) i (List.mem_cons_self ..) rfl
    · simpa only [labels,List.mem_toFinset] using h.2.1.1
    · apply disjoint_left.mpr
      intro j hj hj'
      exact h.2.2 j (by simpa only [labels,List.mem_toFinset] using hj) j
        (List.mem_cons_of_mem _ (by simpa only [labels,List.mem_toFinset] using hj')) rfl

lemma arrive_absent (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (target : I)
    (t : BinaryTree I) (U : Domains A B) (h : target∉labels t) :
    arrive choose read z target t U=none := by
  induction t generalizing U with
  | nil=>rfl
  | node i l r hl hr=>
    have hi : i≠target := by
      intro he
      apply h
      rw [labels_node,he]
      exact mem_insert_self target _
    have hL : target∉labels l := by intro hj; apply h; simp only [labels_node,mem_insert,mem_union]; tauto
    have hR : target∉labels r := by intro hj; apply h; simp only [labels_node,mem_insert,mem_union]; tauto
    rw [arrive,ite_eq_right hi]
    cases hc : choose i (z i) U with
    | none=>rfl
    | some c=>simp only [hl _ hL,hr _ hR,Option.orElse_none]

lemma produced_root (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i : I)
    (f : Domains A B→α i→ℝ) (l r : BinaryTree I) (U : Domains A B) :
    produced choose read i f (.node i l r) U z=f U (z i) := by
  simp only [produced,arrive,ite_true]

lemma produced_left (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i j : I)
    (f : Domains A B→α j→ℝ) (l r : BinaryTree I) (U : Domains A B)
    (hj : j∈labels l) (hi : i∉labels l) (hd : Disjoint (labels l) (labels r))
    (c : C) (hc : choose i (z i) U=some c) :
    produced choose read j f (.node i l r) U z=
      produced choose read j f l ((read i (z i) U c).1,U.2) z := by
  have hij : i≠j := fun he=>hi (he ▸ hj)
  have hnj : j∉labels r := disjoint_left.mp hd hj
  unfold produced
  rw [arrive,ite_eq_right hij,hc]
  dsimp only
  rw [arrive_absent choose read z j r _ hnj]
  cases arrive choose read z j l ((read i (z i) U c).1,U.2) <;> rfl

lemma produced_right (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i j : I)
    (f : Domains A B→α j→ℝ) (l r : BinaryTree I) (U : Domains A B)
    (hj : j∈labels r) (hi : i∉labels r) (hd : Disjoint (labels l) (labels r))
    (c : C) (hc : choose i (z i) U=some c) :
    produced choose read j f (.node i l r) U z=
      produced choose read j f r (U.1,(read i (z i) U c).2) z := by
  have hij : i≠j := fun he=>hi (he ▸ hj)
  have hnj : j∉labels l := disjoint_right.mp hd hj
  unfold produced
  rw [arrive,ite_eq_right hij,hc]
  dsimp only
  rw [arrive_absent choose read z j l _ hnj]
  rfl

lemma produced_deleted (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i j : I)
    (f : Domains A B→α j→ℝ) (l r : BinaryTree I) (U : Domains A B)
    (hi : i≠j) (hc : choose i (z i) U=none) :
    produced choose read j f (.node i l r) U z=0 := by
  simp only [produced,arrive,ite_eq_right hi,hc]

theorem accrued_eq_sum (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (f : ∀ i,Domains A B→α i→ℝ)
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) (ht : Separated t) :
    accrued choose read f z t U=∑ i∈labels t,produced choose read i (f i) t U z := by
  induction t generalizing U with
  | nil=>simp only [accrued,labels_nil,sum_empty]
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    rw [labels_node,sum_insert (by simp only [mem_union,not_or]; exact ⟨hli,hri⟩),
      sum_union hd,produced_root,accrued]
    cases hc : choose i (z i) U with
    | none=>
      simp only [add_zero]
      have hzl : (∑ j∈labels l,produced choose read j (f j) (.node i l r) U z)=0 := by
        apply sum_eq_zero
        intro j hj
        exact produced_deleted choose read z i j (f j) l r U (fun he=>hli (he ▸ hj)) hc
      have hzr : (∑ j∈labels r,produced choose read j (f j) (.node i l r) U z)=0 := by
        apply sum_eq_zero
        intro j hj
        exact produced_deleted choose read z i j (f j) l r U (fun he=>hri (he ▸ hj)) hc
      rw [hzl,hzr,add_zero,add_zero]
    | some c=>
      dsimp only
      rw [hl _ htl,hr _ htr]
      congr 1
      exact congrArg₂ (·+·)
        (sum_congr rfl (fun j hj=>(produced_left choose read z i j (f j) l r U hj hli hd c hc).symm))
        (sum_congr rfl (fun j hj=>(produced_right choose read z i j (f j) l r U hj hri hd c hc).symm))

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

lemma leftPath_subset (target : I) (t : BinaryTree I) : leftPath target t⊆labels t := by
  induction t with
  | nil=>exact empty_subset _
  | node i l r hl hr=>
    rw [leftPath,labels_node]
    split_ifs with hi hj
    · exact empty_subset _
    · exact insert_subset_insert i (hl.trans subset_union_left)
    · exact hr.trans (subset_union_right.trans (subset_insert _ _))

lemma leftPath_card (target : I) (t : BinaryTree I) :
    (leftPath target t).card≤t.height := by
  induction t with
  | nil=>rfl
  | node i l r hl hr=>
    rw [leftPath]
    split_ifs
    · exact Nat.zero_le _
    · exact (card_insert_le _ _).trans (by simp only [height]; omega)
    · simp only [height]; omega

omit [DecidableEq I] in
lemma firstLoss_nonneg (choose : ∀ i,α i→Domains A B→Option C)
    (mask : ∀ i,α i→CapReader A B C) (Y : Finset A)
    (i : I) (U : Domains A B) (x : α i) : 0≤firstLoss choose mask Y i U x := by
  unfold firstLoss
  cases choose i x U <;> positivity

lemma sdiff_inter_card (Y U M : Finset A) :
    ((Y\(U∩M)).card:ℝ)≤((Y\U).card:ℝ)+(Y\M).card := by
  have he : Y\(U∩M)=(Y\U)∪(Y\M) := by ext x; simp; tauto
  rw [he]
  exact_mod_cast card_union_le (Y\U) (Y\M)

theorem reached_first_loss (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hread : ∀ i x U c,(read i x U c).1=U.1∩(mask i x U c).1)
    (z : ∀ i,α i) (target : I) (Y : Finset A)
    (t : BinaryTree I) (U V : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hv : arrive choose read z target t U=some V) :
    ((Y\V.1).card:ℝ)≤((Y\U.1).card:ℝ)+
      ∑ j∈leftPath target t,produced choose read j (firstLoss choose mask Y j) t U z := by
  induction t generalizing U V with
  | nil=>simp [labels_nil] at hmem
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    by_cases hi : i=target
    · rw [arrive,ite_eq_left hi] at hv
      have hUV : U=V := Option.some.inj hv
      rw [leftPath,ite_eq_left hi,hUV,sum_empty,add_zero]
    · by_cases hL : target∈labels l
      · have hR : target∉labels r := disjoint_left.mp hd hL
        rw [arrive,ite_eq_right hi] at hv
        cases hc : choose i (z i) U with
        | none=>simp only [hc] at hv; contradiction
        | some c=>
          rw [hc] at hv
          dsimp only at hv
          rw [arrive_absent choose read z target r _ hR] at hv
          have hv' : arrive choose read z target l ((read i (z i) U c).1,U.2)=some V := by
            cases hh : arrive choose read z target l ((read i (z i) U c).1,U.2) with
            | none=>simp [hh] at hv
            | some W=>rw [hh] at hv; exact hv
          have hchild:=hl _ _ htl hL hv'
          rw [leftPath,ite_eq_right hi,ite_eq_left hL]
          have hnot : i∉leftPath target l := fun hj=>hli (leftPath_subset target l hj)
          rw [sum_insert hnot,produced_root]
          have he : (∑ j∈leftPath target l,produced choose read j (firstLoss choose mask Y j)
              (.node i l r) U z)=
              ∑ j∈leftPath target l,produced choose read j (firstLoss choose mask Y j)
                l ((read i (z i) U c).1,U.2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_left choose read z i j _ l r U (leftPath_subset target l hj) hli hd c hc
          rw [he]
          have hs:=sdiff_inter_card Y U.1 (mask i (z i) U c).1
          have hs' : ((Y\(read i (z i) U c).1).card:ℝ)≤
              ((Y\U.1).card:ℝ)+(Y\(mask i (z i) U c).1).card := by
            rw [hread]
            exact hs
          simp only [firstLoss,hc]
          linarith
      · have hR : target∈labels r := by
          rw [labels_node,mem_insert,mem_union] at hmem
          rcases hmem with he|he|he
          · exact False.elim (hi he.symm)
          · exact False.elim (hL he)
          · exact he
        rw [arrive,ite_eq_right hi] at hv
        cases hc : choose i (z i) U with
        | none=>simp only [hc] at hv; contradiction
        | some c=>
          rw [hc] at hv
          dsimp only at hv
          rw [arrive_absent choose read z target l _ hL] at hv
          have hv' : arrive choose read z target r (U.1,(read i (z i) U c).2)=some V := hv
          have hchild:=hr _ _ htr hR hv'
          rw [leftPath,ite_eq_right hi,ite_eq_right hL]
          have he : (∑ j∈leftPath target r,produced choose read j (firstLoss choose mask Y j)
              (.node i l r) U z)=
              ∑ j∈leftPath target r,produced choose read j (firstLoss choose mask Y j)
                r (U.1,(read i (z i) U c).2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_right choose read z i j _ l r U (leftPath_subset target r hj) hri hd c hc
          rw [he]
          exact hchild

variable [Fintype I] [∀ i,Fintype (α i)]

omit [Fintype I] [∀ i,Fintype (α i)] in

lemma produced_nonneg (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I)
    (f : Domains A B→α target→ℝ) (hf : ∀ V x,0≤f V x)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) :
    0≤produced choose read target f t U z := by
  unfold produced
  cases arrive choose read z target t U with
  | none=>exact le_rfl
  | some V=>exact hf V (z target)

omit [Fintype I] [∀ i,Fintype (α i)] in

theorem reached_first_trim_charge (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hread : ∀ i x U c,(read i x U c).1=U.1∩(mask i x U c).1)
    (z : ∀ i,α i) (target : I) (Y : Finset A) (hY : Y.Nonempty)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hYU : Y⊆U.1) :
    (if firstTrim choose read Y target t U z then (1:ℝ) else 0)≤
      (10/(Y.card:ℝ))*∑ j∈leftPath target t,
        produced choose read j (firstLoss choose mask Y j) t U z := by
  have hy : 0<(Y.card:ℝ) := by exact_mod_cast card_pos.mpr hY
  split_ifs with htrim
  · obtain ⟨V,hv,hsmall⟩:=htrim
    have hl:=reached_first_loss choose read mask hread z target Y t U V ht hmem hv
    rw [sdiff_eq_empty_iff_subset.mpr hYU,card_empty,Nat.cast_zero,zero_add] at hl
    have hc : ((Y\V.1).card:ℝ)+((Y∩V.1).card:ℝ)=Y.card := by
      exact_mod_cast card_sdiff_add_card_inter Y V.1
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hy).mpr
    nlinarith
  · apply mul_nonneg (div_nonneg (by norm_num) hy.le)
    apply sum_nonneg
    intro j _
    exact produced_nonneg choose read j _ (firstLoss_nonneg choose mask Y j) t U z

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

lemma plannedPath_subset (target : I) (t : BinaryTree I) : plannedPath target t⊆labels t := by
  induction t with
  | nil=>exact empty_subset _
  | node i l r hl hr=>
    rw [plannedPath,labels_node]
    split_ifs with hi hj
    · exact singleton_subset_iff.mpr (mem_insert_self _ _)
    · exact insert_subset_insert i (hl.trans subset_union_left)
    · exact insert_subset_insert i (hr.trans subset_union_right)

lemma plannedPath_card (target : I) (t : BinaryTree I) :
    (plannedPath target t).card≤t.height := by
  induction t with
  | nil=>rfl
  | node i l r hl hr=>
    rw [plannedPath]
    split_ifs
    · simp only [card_singleton,height]; omega
    · exact (card_insert_le _ _).trans (by simp only [height]; omega)
    · exact (card_insert_le _ _).trans (by simp only [height]; omega)

theorem deletion_eq_path (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (target : I)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) :
    1-pivotSuccess choose read target t U z=
      ∑ j∈plannedPath target t,produced choose read j (trialFailure choose j) t U z := by
  induction t generalizing U with
  | nil=>simp [labels_nil] at hmem
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    by_cases hi : i=target
    · subst target
      rw [plannedPath,ite_eq_left rfl,sum_singleton,produced_root,pivotSuccess,produced_root]
      ring
    · rw [plannedPath,ite_eq_right hi]
      by_cases hL : target∈labels l
      · rw [ite_eq_left hL,sum_insert (fun hj=>hli (plannedPath_subset target l hj)),produced_root]
        cases hc : choose i (z i) U with
        | none=>
          rw [pivotSuccess,produced_deleted choose read z i target _ l r U hi hc]
          have hzero : (∑ j∈plannedPath target l,
              produced choose read j (trialFailure choose j) (.node i l r) U z)=0 := by
            apply sum_eq_zero
            intro j hj
            exact produced_deleted choose read z i j _ l r U
              (fun he=>hli (he ▸ plannedPath_subset target l hj)) hc
          rw [hzero]
          simp only [trialFailure,hc,ite_true,sub_zero,add_zero]
        | some c=>
          rw [pivotSuccess,produced_left choose read z i target _ l r U hL hli hd c hc]
          have he : (∑ j∈plannedPath target l,
              produced choose read j (trialFailure choose j) (.node i l r) U z)=
              ∑ j∈plannedPath target l,produced choose read j (trialFailure choose j)
                l ((read i (z i) U c).1,U.2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_left choose read z i j _ l r U
              (plannedPath_subset target l hj) hli hd c hc
          rw [he]
          simp only [trialFailure,hc,Option.some_ne_none,ite_false,zero_add]
          exact hl _ htl hL
      · have hR : target∈labels r := by
          rw [labels_node,mem_insert,mem_union] at hmem
          rcases hmem with he|he|he
          · exact False.elim (hi he.symm)
          · exact False.elim (hL he)
          · exact he
        rw [ite_eq_right hL,sum_insert (fun hj=>hri (plannedPath_subset target r hj)),produced_root]
        cases hc : choose i (z i) U with
        | none=>
          rw [pivotSuccess,produced_deleted choose read z i target _ l r U hi hc]
          have hzero : (∑ j∈plannedPath target r,
              produced choose read j (trialFailure choose j) (.node i l r) U z)=0 := by
            apply sum_eq_zero
            intro j hj
            exact produced_deleted choose read z i j _ l r U
              (fun he=>hri (he ▸ plannedPath_subset target r hj)) hc
          rw [hzero]
          simp only [trialFailure,hc,ite_true,sub_zero,add_zero]
        | some c=>
          rw [pivotSuccess,produced_right choose read z i target _ l r U hR hri hd c hc]
          have he : (∑ j∈plannedPath target r,
              produced choose read j (trialFailure choose j) (.node i l r) U z)=
              ∑ j∈plannedPath target r,produced choose read j (trialFailure choose j)
                r (U.1,(read i (z i) U c).2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_right choose read z i j _ l r U
              (plannedPath_subset target r hj) hri hd c hc
          rw [he]
          simp only [trialFailure,hc,Option.some_ne_none,ite_false,zero_add]
          exact hr _ htr hR

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedSecondTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

lemma rightPath_subset (target : I) (t : BinaryTree I) : rightPath target t⊆labels t := by
  induction t with
  | nil=>exact empty_subset _
  | node i l r hl hr=>
    rw [rightPath,labels_node]
    split_ifs with hi hj
    · exact empty_subset _
    · exact insert_subset_insert i (hr.trans subset_union_right)
    · exact hl.trans (subset_union_left.trans (subset_insert _ _))

lemma rightPath_card (target : I) (t : BinaryTree I) :
    (rightPath target t).card≤t.height := by
  induction t with
  | nil=>rfl
  | node i l r hl hr=>
    rw [rightPath]
    split_ifs
    · exact Nat.zero_le _
    · exact (card_insert_le _ _).trans (by simp only [height]; omega)
    · simp only [height]; omega

omit [DecidableEq I] in
lemma secondLoss_nonneg (choose : ∀ i,α i→Domains A B→Option C)
    (mask : ∀ i,α i→CapReader A B C) (Y : Finset B)
    (i : I) (U : Domains A B) (x : α i) : 0 ≤ secondLoss choose mask Y i U x := by
  unfold secondLoss
  cases choose i x U <;> positivity

theorem reached_second_loss (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hread : ∀ i x U c,(read i x U c).2=U.2∩(mask i x U c).2)
    (z : ∀ i,α i) (target : I) (Y : Finset B)
    (t : BinaryTree I) (U V : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hv : arrive choose read z target t U=some V) :
    ((Y\V.2).card:ℝ)≤((Y\U.2).card:ℝ)+
      ∑ j∈rightPath target t,produced choose read j (secondLoss choose mask Y j) t U z := by
  induction t generalizing U V with
  | nil=>simp [labels_nil] at hmem
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    by_cases hi : i=target
    · rw [arrive,ite_eq_left hi] at hv
      have hUV : U=V := Option.some.inj hv
      rw [rightPath,ite_eq_left hi,hUV,sum_empty,add_zero]
    · by_cases hR : target∈labels r
      · have hL : target∉labels l := disjoint_right.mp hd hR
        rw [arrive,ite_eq_right hi] at hv
        cases hc : choose i (z i) U with
        | none=>simp only [hc] at hv; contradiction
        | some c=>
          rw [hc] at hv
          dsimp only at hv
          rw [arrive_absent choose read z target l _ hL] at hv
          have hv' : arrive choose read z target r (U.1,(read i (z i) U c).2)=some V := hv
          have hchild:=hr _ _ htr hR hv'
          rw [rightPath,ite_eq_right hi,ite_eq_left hR]
          have hnot : i∉rightPath target r := fun hj=>hri (rightPath_subset target r hj)
          rw [sum_insert hnot,produced_root]
          have he : (∑ j∈rightPath target r,produced choose read j (secondLoss choose mask Y j)
              (.node i l r) U z)=
              ∑ j∈rightPath target r,produced choose read j (secondLoss choose mask Y j)
                r (U.1,(read i (z i) U c).2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_right choose read z i j _ l r U (rightPath_subset target r hj) hri hd c hc
          rw [he]
          have hs:=sdiff_inter_card Y U.2 (mask i (z i) U c).2
          have hs' : ((Y\(read i (z i) U c).2).card:ℝ)≤
              ((Y\U.2).card:ℝ)+(Y\(mask i (z i) U c).2).card := by
            rw [hread]
            exact hs
          simp only [secondLoss,hc]
          linarith
      · have hL : target∈labels l := by
          rw [labels_node,mem_insert,mem_union] at hmem
          rcases hmem with he|he|he
          · exact False.elim (hi he.symm)
          · exact he
          · exact False.elim (hR he)
        rw [arrive,ite_eq_right hi] at hv
        cases hc : choose i (z i) U with
        | none=>simp only [hc] at hv; contradiction
        | some c=>
          rw [hc] at hv
          dsimp only at hv
          rw [arrive_absent choose read z target r _ hR] at hv
          have hv' : arrive choose read z target l ((read i (z i) U c).1,U.2)=some V := by
            cases hh : arrive choose read z target l ((read i (z i) U c).1,U.2) with
            | none=>simp [hh] at hv
            | some W=>rw [hh] at hv; exact hv
          have hchild:=hl _ _ htl hL hv'
          rw [rightPath,ite_eq_right hi,ite_eq_right hR]
          have he : (∑ j∈rightPath target l,produced choose read j (secondLoss choose mask Y j)
              (.node i l r) U z)=
              ∑ j∈rightPath target l,produced choose read j (secondLoss choose mask Y j)
                l ((read i (z i) U c).1,U.2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_left choose read z i j _ l r U (rightPath_subset target l hj) hli hd c hc
          rw [he]
          exact hchild

variable [Fintype I] [∀ i,Fintype (α i)]

omit [Fintype I] [∀ i,Fintype (α i)] in
theorem reached_second_trim_charge (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hread : ∀ i x U c,(read i x U c).2=U.2∩(mask i x U c).2)
    (z : ∀ i,α i) (target : I) (Y : Finset B) (hY : Y.Nonempty)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hYU : Y⊆U.2) :
    (if secondTrim choose read Y target t U z then (1:ℝ) else 0)≤
      (10/(Y.card:ℝ))*∑ j∈rightPath target t,
        produced choose read j (secondLoss choose mask Y j) t U z := by
  have hy : 0<(Y.card:ℝ) := by exact_mod_cast card_pos.mpr hY
  split_ifs with htrim
  · obtain ⟨V,hv,hsmall⟩:=htrim
    have hl:=reached_second_loss choose read mask hread z target Y t U V ht hmem hv
    rw [sdiff_eq_empty_iff_subset.mpr hYU,card_empty,Nat.cast_zero,zero_add] at hl
    have hc : ((Y\V.2).card:ℝ)+((Y∩V.2).card:ℝ)=Y.card := by
      exact_mod_cast card_sdiff_add_card_inter Y V.2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hy).mpr
    nlinarith
  · apply mul_nonneg (div_nonneg (by norm_num) hy.le)
    apply sum_nonneg
    intro j _
    exact produced_nonneg choose read j _ (secondLoss_nonneg choose mask Y j) t U z

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

theorem target_failure_charge (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hreadA : ∀ i x V c,(read i x V c).1=V.1∩(mask i x V c).1)
    (hreadB : ∀ i x V c,(read i x V c).2=V.2∩(mask i x V c).2)
    (z : ∀ i,α i) (target : I) (a : A) (b : B)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (haU : a∈U.1) (hbU : b∈U.2) :
    targetFailure choose read a b target t U z≤
      1-pivotSuccess choose read target t U z+
      (∑ j∈leftPath target t,produced choose read j (firstLoss choose mask {a} j) t U z)+
      (∑ j∈rightPath target t,produced choose read j (secondLoss choose mask {b} j) t U z)+
      produced choose read target (firstLoss choose mask {a} target) t U z+
      produced choose read target (secondLoss choose mask {b} target) t U z := by
  have hpA : 0≤∑ j∈leftPath target t,produced choose read j (firstLoss choose mask {a} j) t U z := by
    apply sum_nonneg
    intro j _
    exact produced_nonneg choose read j _ (firstLoss_nonneg choose mask {a} j) t U z
  have hpB : 0≤∑ j∈rightPath target t,produced choose read j (secondLoss choose mask {b} j) t U z := by
    apply sum_nonneg
    intro j _
    exact produced_nonneg choose read j _ (secondLoss_nonneg choose mask {b} j) t U z
  have hoA := produced_nonneg choose read target _ (firstLoss_nonneg choose mask {a} target) t U z
  have hoB := produced_nonneg choose read target _ (secondLoss_nonneg choose mask {b} target) t U z
  cases hv : arrive choose read z target t U with
  | none=>
    have hs : pivotSuccess choose read target t U z=0 := by simp only [pivotSuccess,produced,hv]
    rw [targetFailure,hv,hs]
    linarith
  | some V=>
    cases hc : choose target (z target) V with
    | none=>
      have hs : pivotSuccess choose read target t U z=0 := by
        simp only [pivotSuccess,produced,hv,trialFailure,hc,ite_true,sub_self]
      simp only [targetFailure,hv,hc,hs]
      linarith
    | some c=>
      have hs : pivotSuccess choose read target t U z=1 := by
        simp only [pivotSuccess,produced,hv,trialFailure,hc,Option.some_ne_none,ite_false,sub_zero]
      have hoA' : produced choose read target (firstLoss choose mask {a} target) t U z=
          (({a}\(mask target (z target) V c).1).card:ℝ) := by
        simp only [produced,hv,firstLoss,hc]
      have hoB' : produced choose read target (secondLoss choose mask {b} target) t U z=
          (({b}\(mask target (z target) V c).2).card:ℝ) := by
        simp only [produced,hv,secondLoss,hc]
      have hf:=reached_first_loss choose read mask hreadA z target {a} t U V ht hmem hv
      have hg:=reached_second_loss choose read mask hreadB z target {b} t U V ht hmem hv
      rw [sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr haU),card_empty,Nat.cast_zero,zero_add] at hf
      rw [sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr hbU),card_empty,Nat.cast_zero,zero_add] at hg
      have hcapA : (({a}\(read target (z target) V c).1).card:ℝ)≤
          (({a}\V.1).card:ℝ)+({a}\(mask target (z target) V c).1).card := by
        rw [hreadA]
        exact sdiff_inter_card {a} V.1 _
      have hcapB : (({b}\(read target (z target) V c).2).card:ℝ)≤
          (({b}\V.2).card:ℝ)+({b}\(mask target (z target) V c).2).card := by
        rw [hreadB]
        exact sdiff_inter_card {b} V.2 _
      have hpoint : (if a∈(read target (z target) V c).1 ∧ b∈(read target (z target) V c).2
          then (0:ℝ) else 1)≤
          (({a}\(read target (z target) V c).1).card:ℝ)+({b}\(read target (z target) V c).2).card := by
        have haa : (({a}\(read target (z target) V c).1).card:ℝ) =
            if a∈(read target (z target) V c).1 then 0 else 1 := by
          by_cases ha : a∈(read target (z target) V c).1
          · rw [sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr ha)]
            simp [ha]
          · have he : {a}\(read target (z target) V c).1={a} := by
              ext x
              simp only [mem_sdiff,mem_singleton]
              constructor
              · exact And.left
              · rintro rfl
                exact ⟨rfl,ha⟩
            simp [he,ha]
        have hbb : (({b}\(read target (z target) V c).2).card:ℝ) =
            if b∈(read target (z target) V c).2 then 0 else 1 := by
          by_cases hb : b∈(read target (z target) V c).2
          · rw [sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr hb)]
            simp [hb]
          · have he : {b}\(read target (z target) V c).2={b} := by
              ext x
              simp only [mem_sdiff,mem_singleton]
              constructor
              · exact And.left
              · rintro rfl
                exact ⟨rfl,hb⟩
            simp [he,hb]
        rw [haa,hbb]
        split_ifs <;> norm_num
        tauto
      simp only [targetFailure,hv,hc,hs,hoA',hoB']
      linarith

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedSupportTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] [Fintype I] [Fintype Ω]
  {α : I→Type*} [∀ i,Fintype (α i)]

theorem averaged_path_bound (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C)
    (loss : Ω→∀ i,Domains A B→α i→ℝ)
    (t : BinaryTree I) (U : Domains A B) (J : Finset I)
    (M : Ω→ℝ) (hM : ∀ ω,0≤M ω) (budget : Ω→I→ℝ)
    (hb : ∀ ω,∀ i∈J,0≤budget ω i)
    (hlocal : ∀ ω,∀ i∈J,∀ V,(∑ x,(p i).mass x*loss ω i V x)≤budget ω i)
    (ε : ℝ) (hmean : ∀ i∈J,(∑ ω,μ.mass ω*(budget ω i/M ω))≤ε) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      ((∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z)/M ω)))≤J.card*ε := by
  have hω (ω : Ω) : (∑ z,(piLaw p).mass z*
      ((∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z)/M ω))≤
      ∑ j∈J,budget ω j/M ω := by
    simp_rw [←mul_div_assoc,←sum_div,mul_sum]
    rw [sum_comm]
    apply div_le_div_of_nonneg_right _ (hM ω)
    apply sum_le_sum
    intro j hj
    exact produced_bound p (choose ω) (read ω) j (dummy j) (loss ω j) t U
      (budget ω j) (hb ω j hj) (hlocal ω j hj)
  calc
    _ ≤ ∑ ω,μ.mass ω*(∑ j∈J,budget ω j/M ω) := by
      apply sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hω ω) (μ.nonneg ω)
    _ = ∑ j∈J,∑ ω,μ.mass ω*(budget ω j/M ω) := by
      simp_rw [mul_sum]
      rw [sum_comm]
    _ ≤ ∑ _j∈J,ε := sum_le_sum (fun j hj=>hmean j hj)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]

theorem averaged_charge_bound (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C)
    (loss : Ω→∀ i,Domains A B→α i→ℝ)
    (t : BinaryTree I) (U : Domains A B) (J : Finset I)
    (M : Ω→ℝ) (hM : ∀ ω,0≤M ω) (budget : Ω→I→ℝ)
    (hb : ∀ ω,∀ i∈J,0≤budget ω i)
    (hlocal : ∀ ω,∀ i∈J,∀ V,(∑ x,(p i).mass x*loss ω i V x)≤budget ω i)
    (ε : ℝ) (hmean : ∀ i∈J,(∑ ω,μ.mass ω*(budget ω i/M ω))≤ε)
    (E : Ω→(∀ i,α i)→Prop)
    (hcharge : ∀ ω z,(if E ω z then (1:ℝ) else 0)≤
      (10/M ω)*∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*(if E ω z then (1:ℝ) else 0)))≤10*J.card*ε := by
  have hpath:=averaged_path_bound μ p dummy choose read loss t U J M hM budget hb hlocal ε hmean
  calc
    _ ≤ ∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*((10/M ω)*
        ∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z)) := by
      apply sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg ω)
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (hcharge ω z) ((piLaw p).nonneg z)
    _ = 10*(∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
        ((∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z)/M ω))) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro ω _
      have hh : (∑ z,(piLaw p).mass z*((10/M ω)*
          ∑ j∈J,produced (choose ω) (read ω) j (loss ω j) t U z))=
          10*(∑ z,(piLaw p).mass z*((∑ j∈J,
            produced (choose ω) (read ω) j (loss ω j) t U z)/M ω)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro z _
        ring
      rw [hh]
      ring
    _ ≤ 10*(J.card*ε) := mul_le_mul_of_nonneg_left hpath (by norm_num)
    _ = _ := by ring

theorem original_first_trim (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read mask : Ω→∀ i,α i→CapReader A B C)
    (hread : ∀ ω i x U c,(read ω i x U c).1=U.1∩(mask ω i x U c).1)
    (target : I) (Y : Ω→Finset A) (hY : ∀ ω,(Y ω).Nonempty)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hYU : ∀ ω,Y ω⊆U.1)
    (budget : Ω→I→ℝ) (hb : ∀ ω,∀ i∈leftPath target t,0≤budget ω i)
    (hlocal : ∀ ω,∀ i∈leftPath target t,∀ V,
      (∑ x,(p i).mass x*firstLoss (choose ω) (mask ω) (Y ω) i V x)≤budget ω i)
    (ε : ℝ) (hε : 0≤ε)
    (hmean : ∀ i∈leftPath target t,(∑ ω,μ.mass ω*(budget ω i/(Y ω).card))≤ε) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if firstTrim (choose ω) (read ω) (Y ω) target t U z then (1:ℝ) else 0)))≤
      10*t.height*ε := by
  apply (averaged_charge_bound μ p dummy choose read
    (fun ω=>firstLoss (choose ω) (mask ω) (Y ω)) t U (leftPath target t)
    (fun ω=>((Y ω).card:ℝ)) (fun ω=>Nat.cast_nonneg _) budget hb hlocal ε hmean
    (fun ω=>firstTrim (choose ω) (read ω) (Y ω) target t U)
    (fun ω z=>reached_first_trim_charge (choose ω) (read ω) (mask ω) (hread ω)
      z target (Y ω) (hY ω) t U ht hmem (hYU ω))).trans
  have hh : ((leftPath target t).card:ℝ)≤t.height := by exact_mod_cast leftPath_card target t
  gcongr

theorem original_second_trim (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read mask : Ω→∀ i,α i→CapReader A B C)
    (hread : ∀ ω i x U c,(read ω i x U c).2=U.2∩(mask ω i x U c).2)
    (target : I) (Y : Ω→Finset B) (hY : ∀ ω,(Y ω).Nonempty)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (hYU : ∀ ω,Y ω⊆U.2)
    (budget : Ω→I→ℝ) (hb : ∀ ω,∀ i∈rightPath target t,0≤budget ω i)
    (hlocal : ∀ ω,∀ i∈rightPath target t,∀ V,
      (∑ x,(p i).mass x*secondLoss (choose ω) (mask ω) (Y ω) i V x)≤budget ω i)
    (ε : ℝ) (hε : 0≤ε)
    (hmean : ∀ i∈rightPath target t,(∑ ω,μ.mass ω*(budget ω i/(Y ω).card))≤ε) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if secondTrim (choose ω) (read ω) (Y ω) target t U z then (1:ℝ) else 0)))≤
      10*t.height*ε := by
  apply (averaged_charge_bound μ p dummy choose read
    (fun ω=>secondLoss (choose ω) (mask ω) (Y ω)) t U (rightPath target t)
    (fun ω=>((Y ω).card:ℝ)) (fun ω=>Nat.cast_nonneg _) budget hb hlocal ε hmean
    (fun ω=>secondTrim (choose ω) (read ω) (Y ω) target t U)
    (fun ω z=>reached_second_trim_charge (choose ω) (read ω) (mask ω) (hread ω)
      z target (Y ω) (hY ω) t U ht hmem (hYU ω))).trans
  have hh : ((rightPath target t).card:ℝ)≤t.height := by exact_mod_cast rightPath_card target t
  gcongr

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedFailureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}

theorem failure_partition (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i : I)
    (S : Finset A) (T : Finset B) (bad : Prop) (t : BinaryTree I) (U : Domains A B) :
    produced choose read i (trialFailure choose i) t U z≤
      (if firstTrim choose read S i t U z then (1:ℝ) else 0)+
      (if secondTrim choose read T i t U z then (1:ℝ) else 0)+
      (if bad then (1:ℝ) else 0)+
      produced choose read i (readyFailure choose S T bad i) t U z := by
  unfold produced
  cases ha : arrive choose read z i t U with
  | none=>
    by_cases hb : bad <;> simp [firstTrim,secondTrim,ha,hb]
  | some V=>
    have hS : firstTrim choose read S i t U z ↔
        ((S∩V.1).card:ℝ)<(9/10:ℝ)*S.card := by simp [firstTrim,ha]
    have hT : secondTrim choose read T i t U z ↔
        ((T∩V.2).card:ℝ)<(9/10:ℝ)*T.card := by simp [secondTrim,ha]
    rw [hS,hT]
    by_cases hs : ((S∩V.1).card:ℝ)<(9/10:ℝ)*S.card <;>
      by_cases ht : ((T∩V.2).card:ℝ)<(9/10:ℝ)*T.card <;>
      by_cases hb : bad <;> by_cases hc : choose i (z i) V=none <;>
      norm_num [readyFailure,trialFailure,hs,ht,hb,hc]

variable [Fintype I] [Fintype Ω] [∀ i,Fintype (α i)]

theorem averaged_failure_budget (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C) (i : I)
    (S : Ω→Finset A) (T : Ω→Finset B) (bad : Ω→Prop)
    (t : BinaryTree I) (U : Domains A B) (F G D ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if firstTrim (choose ω) (read ω) (S ω) i t U z then (1:ℝ) else 0)))≤F)
    (hsecond : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if secondTrim (choose ω) (read ω) (T ω) i t U z then (1:ℝ) else 0)))≤G)
    (hdensity : (∑ ω,μ.mass ω*(if bad ω then (1:ℝ) else 0))≤D)
    (hready : ∀ ω V,(∑ x,(p i).mass x*readyFailure (choose ω) (S ω) (T ω) (bad ω) i V x)≤ρ) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      produced (choose ω) (read ω) i (trialFailure (choose ω) i) t U z))≤F+G+D+ρ := by
  have hprodω (ω : Ω) : (∑ z,(piLaw p).mass z*
      produced (choose ω) (read ω) i (readyFailure (choose ω) (S ω) (T ω) (bad ω) i) t U z)≤ρ :=
    produced_bound p (choose ω) (read ω) i (dummy i) _ t U ρ hρ (hready ω)
  have hprod : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      produced (choose ω) (read ω) i (readyFailure (choose ω) (S ω) (T ω) (bad ω) i) t U z))≤ρ := by
    calc
      _ ≤ ∑ ω,μ.mass ω*ρ := sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (hprodω ω) (μ.nonneg ω))
      _ = ρ := by rw [←sum_mul,μ.total,one_mul]
  have hpart : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      produced (choose ω) (read ω) i (trialFailure (choose ω) i) t U z))≤
      ∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*((if firstTrim (choose ω) (read ω) (S ω) i t U z then (1:ℝ) else 0)+
        (if secondTrim (choose ω) (read ω) (T ω) i t U z then (1:ℝ) else 0)+
        (if bad ω then (1:ℝ) else 0)+produced (choose ω) (read ω) i
          (readyFailure (choose ω) (S ω) (T ω) (bad ω) i) t U z)) := by
    apply sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg ω)
    apply sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left
      (failure_partition (choose ω) (read ω) z i (S ω) (T ω) (bad ω) t U) ((piLaw p).nonneg z)
  simp_rw [mul_add,sum_add_distrib] at hpart
  simp only [←sum_mul,(piLaw p).total,one_mul] at hpart
  simp_rw [mul_add,sum_add_distrib] at hpart
  linarith

theorem original_deletion_quadratic (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C)
    (S : Ω→I→Finset A) (T : Ω→I→Finset B) (bad : Ω→I→Prop)
    (target : I) (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (ε D ρ : ℝ) (hε : 0≤ε) (hD : 0≤D) (hρ : 0≤ρ)
    (hfirst : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if firstTrim (choose ω) (read ω) (S ω i) i t U z then (1:ℝ) else 0)))≤10*t.height*ε)
    (hsecond : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (if secondTrim (choose ω) (read ω) (T ω i) i t U z then (1:ℝ) else 0)))≤10*t.height*ε)
    (hdensity : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*(if bad ω i then (1:ℝ) else 0))≤D)
    (hready : ∀ i∈plannedPath target t,∀ ω V,
      (∑ x,(p i).mass x*readyFailure (choose ω) (S ω i) (T ω i) (bad ω i) i V x)≤ρ) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*(1-pivotSuccess (choose ω) (read ω) target t U z)))≤
      20*ε*t.height^2+(D+ρ)*t.height := by
  have hloc (i : I) (hi : i∈plannedPath target t) :
      (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
        produced (choose ω) (read ω) i (trialFailure (choose ω) i) t U z))≤
        20*t.height*ε+D+ρ := by
    have h:=averaged_failure_budget μ p dummy choose read i (fun ω=>S ω i) (fun ω=>T ω i)
      (fun ω=>bad ω i) t U (10*t.height*ε) (10*t.height*ε) D ρ hρ
      (hfirst i hi) (hsecond i hi) (hdensity i hi) (hready i hi)
    linarith
  have he (ω : Ω) :
      (∑ z,(piLaw p).mass z*(1-pivotSuccess (choose ω) (read ω) target t U z))=
      ∑ i∈plannedPath target t,(∑ z,(piLaw p).mass z*
        produced (choose ω) (read ω) i (trialFailure (choose ω) i) t U z) := by
    simp_rw [deletion_eq_path (choose ω) (read ω) _ target t U ht hmem,mul_sum]
    rw [sum_comm]
  simp_rw [he,mul_sum]
  rw [sum_comm]
  simp_rw [mul_sum] at hloc
  calc
    _ ≤ ∑ _i∈plannedPath target t,(20*t.height*ε+D+ρ) := sum_le_sum (fun i hi=>hloc i hi)
    _ = ((plannedPath target t).card:ℝ)*(20*t.height*ε+D+ρ) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (t.height:ℝ)*(20*t.height*ε+D+ρ) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast plannedPath_card target t)
      positivity
    _ = _ := by ring

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedGoodTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}

lemma targetFailure_le_one (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (a : A) (b : B) (i : I)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) :
    targetFailure choose read a b i t U z≤1 := by
  unfold targetFailure
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · split_ifs <;> norm_num

lemma deletion_nonneg (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (i : I)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) :
    0≤1-pivotSuccess choose read i t U z := by
  unfold pivotSuccess produced
  split
  · norm_num
  · dsimp [trialFailure]
    split_ifs <;> norm_num

lemma target_failure_good_charge (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hreadA : ∀ i x V c,(read i x V c).1=V.1∩(mask i x V c).1)
    (hreadB : ∀ i x V c,(read i x V c).2=V.2∩(mask i x V c).2)
    (goodA goodB : Prop) (z : ∀ i,α i) (target : I) (a : A) (b : B)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (haU : a∈U.1) (hbU : b∈U.2) :
    targetFailure choose read a b target t U z≤
      1-pivotSuccess choose read target t U z+
      (if goodA then (0:ℝ) else 1)+(if goodB then (0:ℝ) else 1)+
      (∑ j∈leftPath target t,produced choose read j (firstLoss choose mask (goodSingleton goodA a) j) t U z)+
      (∑ j∈rightPath target t,produced choose read j (secondLoss choose mask (goodSingleton goodB b) j) t U z)+
      produced choose read target (firstLoss choose mask (goodSingleton goodA a) target) t U z+
      produced choose read target (secondLoss choose mask (goodSingleton goodB b) target) t U z := by
  by_cases hA : goodA ∧ goodB
  · simpa only [goodSingleton,ite_eq_left hA.1,ite_eq_left hA.2,add_zero] using
      target_failure_charge choose read mask hreadA hreadB z target a b t U ht hmem haU hbU
  · have hbad : (1:ℝ)≤(if goodA then (0:ℝ) else 1)+(if goodB then (0:ℝ) else 1) := by
      split_ifs <;> try norm_num
      tauto
    have hlo := targetFailure_le_one choose read a b target t U z
    have hd := deletion_nonneg choose read target t U z
    have hoA := produced_nonneg choose read target _
      (firstLoss_nonneg choose mask (goodSingleton goodA a) target) t U z
    have hoB := produced_nonneg choose read target _
      (secondLoss_nonneg choose mask (goodSingleton goodB b) target) t U z
    have hpA : 0≤∑ j∈leftPath target t,produced choose read j
        (firstLoss choose mask (goodSingleton goodA a) j) t U z := by
      exact sum_nonneg (fun j _=>produced_nonneg choose read j _
        (firstLoss_nonneg choose mask _ j) t U z)
    have hpB : 0≤∑ j∈rightPath target t,produced choose read j
        (secondLoss choose mask (goodSingleton goodB b) j) t U z := by
      exact sum_nonneg (fun j _=>produced_nonneg choose read j _
        (secondLoss_nonneg choose mask _ j) t U z)
    linarith

variable [Fintype I] [Fintype Ω] [∀ i,Fintype (α i)]

theorem original_good_target_loss (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read mask : Ω→∀ i,α i→CapReader A B C)
    (hreadA : ∀ ω i x V c,(read ω i x V c).1=V.1∩(mask ω i x V c).1)
    (hreadB : ∀ ω i x V c,(read ω i x V c).2=V.2∩(mask ω i x V c).2)
    (goodA goodB : Ω→Prop) (a : Ω→A) (b : Ω→B) (target : I) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t) (hmem : target∈labels t)
    (haU : ∀ ω,a ω∈U.1) (hbU : ∀ ω,b ω∈U.2)
    (BA BB : Ω→I→ℝ) (εA εB L δA δB : ℝ) (hεA : 0≤εA) (hεB : 0≤εB)
    (hBA : ∀ ω,∀ i∈insert target (leftPath target t),0≤BA ω i)
    (hBB : ∀ ω,∀ i∈insert target (rightPath target t),0≤BB ω i)
    (hlocalA : ∀ ω,∀ i∈insert target (leftPath target t),∀ V,
      (∑ x,(p i).mass x*firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) i V x)≤BA ω i)
    (hlocalB : ∀ ω,∀ i∈insert target (rightPath target t),∀ V,
      (∑ x,(p i).mass x*secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) i V x)≤BB ω i)
    (hmeanA : ∀ i∈insert target (leftPath target t),(∑ ω,μ.mass ω*BA ω i)≤εA)
    (hmeanB : ∀ i∈insert target (rightPath target t),(∑ ω,μ.mass ω*BB ω i)≤εB)
    (hbadA : (∑ ω,μ.mass ω*(if goodA ω then (0:ℝ) else 1))≤δA)
    (hbadB : (∑ ω,μ.mass ω*(if goodB ω then (0:ℝ) else 1))≤δB)
    (hdelete : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (1-pivotSuccess (choose ω) (read ω) target t U z)))≤L) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      targetFailure (choose ω) (read ω) (a ω) (b ω) target t U z))≤
        L+δA+δB+((t.height:ℝ)+1)*(εA+εB) := by
  have hpathA := averaged_path_bound μ p dummy choose read
    (fun ω i=>firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) i) t U (leftPath target t)
    (fun _=>1) (fun _=>by norm_num) BA
    (fun ω i hi=>hBA ω i (mem_insert_of_mem hi))
    (fun ω i hi=>hlocalA ω i (mem_insert_of_mem hi)) εA
    (fun i hi=>by simpa only [div_one] using hmeanA i (mem_insert_of_mem hi))
  have hpathB := averaged_path_bound μ p dummy choose read
    (fun ω i=>secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) i) t U (rightPath target t)
    (fun _=>1) (fun _=>by norm_num) BB
    (fun ω i hi=>hBB ω i (mem_insert_of_mem hi))
    (fun ω i hi=>hlocalB ω i (mem_insert_of_mem hi)) εB
    (fun i hi=>by simpa only [div_one] using hmeanB i (mem_insert_of_mem hi))
  have hownA := averaged_path_bound μ p dummy choose read
    (fun ω i=>firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) i) t U {target}
    (fun _=>1) (fun _=>by norm_num) BA
    (fun ω i hi=>hBA ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _))
    (fun ω i hi=>hlocalA ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _)) εA
    (fun i hi=>by
      have hi' : i=target := mem_singleton.mp hi
      subst i
      simpa only [div_one] using hmeanA target (mem_insert_self _ _))
  have hownB := averaged_path_bound μ p dummy choose read
    (fun ω i=>secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) i) t U {target}
    (fun _=>1) (fun _=>by norm_num) BB
    (fun ω i hi=>hBB ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _))
    (fun ω i hi=>hlocalB ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _)) εB
    (fun i hi=>by
      have hi' : i=target := mem_singleton.mp hi
      subst i
      simpa only [div_one] using hmeanB target (mem_insert_self _ _))
  simp only [div_one] at hpathA hpathB
  simp only [div_one,sum_singleton,card_singleton,Nat.cast_one,one_mul] at hownA hownB
  have hcA : ((leftPath target t).card:ℝ)*εA≤(t.height:ℝ)*εA :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast leftPath_card target t) hεA
  have hcB : ((rightPath target t).card:ℝ)*εB≤(t.height:ℝ)*εB :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast rightPath_card target t) hεB
  have hpart : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      targetFailure (choose ω) (read ω) (a ω) (b ω) target t U z))≤
      ∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*(
        1-pivotSuccess (choose ω) (read ω) target t U z+
        (if goodA ω then (0:ℝ) else 1)+(if goodB ω then (0:ℝ) else 1)+
        (∑ j∈leftPath target t,produced (choose ω) (read ω) j
          (firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) j) t U z)+
        (∑ j∈rightPath target t,produced (choose ω) (read ω) j
          (secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) j) t U z)+
        produced (choose ω) (read ω) target (firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) target) t U z+
        produced (choose ω) (read ω) target (secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) target) t U z)) := by
    apply sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg ω)
    apply sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left (target_failure_good_charge (choose ω) (read ω) (mask ω)
      (hreadA ω) (hreadB ω) (goodA ω) (goodB ω) z target (a ω) (b ω) t U ht hmem (haU ω) (hbU ω))
      ((piLaw p).nonneg z)
  simp_rw [mul_add,sum_add_distrib] at hpart
  simp_rw [mul_add,sum_add_distrib] at hpart
  simp only [←sum_mul,(piLaw p).total,one_mul] at hpart
  linarith

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

lemma retained_all (R : A→B→Prop) (U : Domains A B) (xs : List (A×B)) :
    retained R U xs xs.length=xs.filter (fun z=>z∈flagDomain R U) := by
  exact List.take_of_length_le (List.length_filter_le _ _)

omit [DecidableEq I] in
lemma fullOutput_nil (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (U : Domains A B) :
    fullOutput R choose read targets z .nil U=[] := rfl

omit [DecidableEq I] in
lemma fullOutput_fail (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (i : I) (l r : BinaryTree I) (U : Domains A B)
    (hc : choose i (z i) U=none) :
    fullOutput R choose read targets z (.node i l r) U=[] := by
  simp only [fullOutput,execute,fixedChoose,hc,Option.map_none,output]

omit [DecidableEq I] in
lemma fullOutput_success (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (i : I) (l r : BinaryTree I) (U : Domains A B)
    (c : C) (hc : choose i (z i) U=some c) :
    let V:=read i (z i) U c
    fullOutput R choose read targets z (.node i l r) U=
      fullOutput R choose read targets z l (V.1,U.2)++
      (targets i).filter (fun x=>x∈flagDomain R V)++
      fullOutput R choose read targets z r (U.1,V.2) := by
  simp only [fullOutput,execute,fixedChoose,hc,Option.map_some,output,fixedRead,retained_all]

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedOutputCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

omit [DecidableEq I] in
lemma fullOutput_length_accrued (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) :
    ((fullOutput R choose read targets z t U).length:ℝ)=
      accrued choose read (keptCount R choose read targets) z t U := by
  induction t generalizing U with
  | nil=>simp only [fullOutput_nil,List.length_nil,Nat.cast_zero,accrued]
  | node i l r hl hr=>
    cases hc : choose i (z i) U with
    | none=>simp only [fullOutput_fail R choose read targets z i l r U hc,
        accrued,keptCount,hc,add_zero,List.length_nil,Nat.cast_zero]
    | some c=>
      rw [fullOutput_success R choose read targets z i l r U c hc]
      simp only [List.length_append,Nat.cast_add,hl,hr,accrued,keptCount,hc]
      dsimp only [compatible]
      ring

lemma population_length_sum (targets : I→List (A×B)) (t : BinaryTree I)
    (ht : Separated t) :
    ((population targets t).length:ℝ)=∑ i∈labels t,((targets i).length:ℝ) := by
  induction t with
  | nil=>simp only [population,labels_nil,List.length_nil,Nat.cast_zero,sum_empty]
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    rw [labels_node,sum_insert (by simp only [mem_union,not_or]; exact ⟨hli,hri⟩),sum_union hd]
    simp only [population,List.length_append,Nat.cast_add,hl htl,hr htr]
    ring

omit [DecidableEq I] in
lemma compatible_complement (R : A→B→Prop) (V : Domains A B) (xs : List (A×B))
    (hR : ∀ x∈xs,R x.1 x.2) :
    (xs.map (fun x=>if x.1∈V.1 ∧ x.2∈V.2 then (0:ℝ) else 1)).sum=
      (xs.length:ℝ)-compatible R V xs := by
  induction xs with
  | nil=>simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.cast_zero,
      compatible,List.filter_nil,sub_self]
  | cons x xs ih=>
    have hx : R x.1 x.2 := hR x (List.mem_cons_self ..)
    have ht : ∀ y∈xs,R y.1 y.2 := fun y hy=>hR y (List.mem_cons_of_mem _ hy)
    have hm : x∈flagDomain R V ↔ x.1∈V.1 ∧ x.2∈V.2 := by
      simp only [flagDomain,mem_filter,mem_product,hx,and_true]
    by_cases hc : x.1∈V.1 ∧ x.2∈V.2
    · have hxV : x∈flagDomain R V := hm.mpr hc
      simp only [List.map_cons,List.sum_cons,ite_eq_left hc,zero_add,ih ht,
        List.length_cons,Nat.cast_add,Nat.cast_one,compatible,List.filter_cons_of_pos (p:=fun z=>decide (z∈flagDomain R V)) (a:=x) (l:=xs) (by simpa only [decide_eq_true_eq] using hxV),
        List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
    · have hxV : x∉flagDomain R V := fun h=>hc (hm.mp h)
      simp only [List.map_cons,List.sum_cons,ite_eq_right hc,ih ht,
        List.length_cons,Nat.cast_add,Nat.cast_one,compatible,List.filter_cons_of_neg (p:=fun z=>decide (z∈flagDomain R V)) (a:=x) (l:=xs) (by simpa only [decide_eq_true_eq] using hxV)]
      ring

lemma pivot_count_complement (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (i : I) (t : BinaryTree I) (U : Domains A B)
    (hR : ∀ x∈targets i,R x.1 x.2) :
    ((targets i).map (fun x=>targetFailure choose read x.1 x.2 i t U z)).sum=
      ((targets i).length:ℝ)-produced choose read i (keptCount R choose read targets i) t U z := by
  have hones (xs : List (A×B)) : (xs.map (fun _=>(1:ℝ))).sum=(xs.length:ℝ) := by
    induction xs with
    | nil=>simp
    | cons x xs ih=>simp only [List.map_cons,List.sum_cons,ih,List.length_cons,
        Nat.cast_add,Nat.cast_one]; ring
  cases ha : arrive choose read z i t U with
  | none=>simpa only [targetFailure,ha,produced,sub_zero] using hones (targets i)
  | some V=>
    cases hc : choose i (z i) V with
    | none=>simpa only [targetFailure,ha,hc,produced,keptCount,sub_zero] using hones (targets i)
    | some c=>
      simp only [targetFailure,ha,hc,produced,keptCount]
      exact compatible_complement R (read i (z i) V c) (targets i) hR

theorem output_loss_eq_targets (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hR : ∀ i∈labels t,∀ x∈targets i,R x.1 x.2) :
    ((population targets t).length:ℝ)-(fullOutput R choose read targets z t U).length=
      ∑ i∈labels t,((targets i).map (fun x=>targetFailure choose read x.1 x.2 i t U z)).sum := by
  rw [population_length_sum targets t ht,fullOutput_length_accrued,
    accrued_eq_sum choose read _ z t U ht,←sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  exact (pivot_count_complement R choose read targets z i t U (hR i hi)).symm

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_CanonicalAuxiliaryLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B Ω Θ : Type*} [Fintype A] [Fintype B] [Fintype Ω] [Fintype Θ]

namespace AuxiliarySupport
variable {p : Law A} {good : Finset A} {M κ : ℝ}

lemma setLaw_sum (X : AuxiliarySupport p good M κ) (f : Finset A → ℝ) :
    (∑ S, X.setLaw.mass S * f S) =
      ∑ b, X.law.mass b * f (levelSet p b ∩ good) :=
  X.law.sum_map _ f

lemma setLaw_density (X : AuxiliarySupport p good M κ) (a : A) :
    (∑ S, X.setLaw.mass S * kernel S a) ≤
      4 * exp 1 * (if a ∈ good then p.mass a else 0) := by
  rw [X.setLaw_sum]
  by_cases ha : a ∈ good
  · simpa only [ite_eq_left ha, kernel] using X.density a
  · simp only [kernel, mem_inter, ha, and_false, ite_false, mul_zero, sum_const_zero,
      le_refl]

end AuxiliarySupport

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_AuxiliaryFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B I J Ω Θ : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
  [Fintype Ω] [Fintype Θ]

lemma Law.pi_coordinate_sum (p : I → Law A) (i : I) (f : A → ℝ) :
    (∑ z, (Law.pi p).mass z * f (z i)) = ∑ a, (p i).mass a * f a := by
  let ρ := Law.pi (fun j : {j : I // j ≠ i} => p j)
  have hm (z : I → A) : (Law.pi p).mass z = (p i).mass (z i) *
      ρ.mass (fun j => z j) := by
    change (∏ j, (p j).mass (z j)) = (p i).mass (z i) *
      (∏ j : {j : I // j ≠ i}, (p j).mass (z j))
    have he : (∏ j ∈ (univ : Finset I).erase i, (p j).mass (z j)) =
        ∏ j : {j : I // j ≠ i}, (p j).mass (z j) :=
      prod_subtype _ (by simp) _
    rw [← he]
    exact (mul_prod_erase univ (fun j => (p j).mass (z j)) (mem_univ i)).symm
  calc
    _ = ∑ z, (p i).mass (z i) * ρ.mass (fun j => z j) * f (z i) := by
      simp_rw [hm]
    _ = ∑ z : A × ({j : I // j ≠ i} → A), (p i).mass z.1 * ρ.mass z.2 * f z.1 :=
      Fintype.sum_equiv (Equiv.piSplitAt i (fun _ : I => A)) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro a _
      simp only [← sum_mul, ← mul_sum, ρ.total, mul_one]

lemma Law.independent_coordinates_sum (p : I → Law A) (q : J → Law B)
    (i : I) (j : J) (f : A → B → ℝ) :
    (∑ z, ((Law.pi p).prod (Law.pi q)).mass z * f (z.1 i) (z.2 j)) =
      ∑ a, ∑ b, (p i).mass a * (q j).mass b * f a b := by
  change (∑ z : (I → A) × (J → B), (Law.pi p).mass z.1 * (Law.pi q).mass z.2 * f (z.1 i) (z.2 j)) = _
  rw [Fintype.sum_prod_type]
  simp only [mul_assoc, ← mul_sum]
  simp_rw [Law.pi_coordinate_sum q j]
  exact Law.pi_coordinate_sum p i (fun a => ∑ b, (q j).mass b * f a b)

namespace AuxiliarySupport
variable {p : I → Law A} {q : J → Law B} {goodA : I → Finset A}
  {goodB : J → Finset B} {MA κA : I → ℝ} {MB κB : J → ℝ}

theorem familyLaw_incidence
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (i : I) (j : J) (R : A → B → Prop) :
    (∑ z, (familyLaw X Y).mass z * pairing (kernel (z.1 i)) (kernel (z.2 j))
      (fun a b => if R a b then 1 else 0)) ≤
      (4 * exp 1) * (4 * exp 1) * ((p i).prod (q j)).event
        (univ.filter (fun z => z.1 ∈ goodA i ∧ z.2 ∈ goodB j ∧ R z.1 z.2)) := by
  rw [familyLaw, Law.independent_coordinates_sum
    (fun i => (X i).setLaw) (fun j => (Y j).setLaw) i j
    (fun S T => pairing (kernel S) (kernel T) (fun a b => if R a b then 1 else 0))]
  have h := independent_pairing_le (X i).setLaw.mass (Y j).setLaw.mass id id
    (fun a b => if R a b then (1 : ℝ) else 0)
    (fun a => if a ∈ goodA i then (p i).mass a else 0)
    (fun b => if b ∈ goodB j then (q j).mass b else 0)
    (4 * exp 1) (4 * exp 1) (X i).setLaw.nonneg (Y j).setLaw.nonneg
    (by intros; split_ifs <;> norm_num) (X i).setLaw_density (Y j).setLaw_density
  simpa only [id_eq, good_pairing_eq_event] using h

end AuxiliarySupport

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_ReadyTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation SupportMixtures Selection
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma kernel_eq_uniform (S : Finset (Projectivization K V)) :
    kernel S = uniformMass S := by
  funext x
  simp only [kernel, uniformMass, one_div]

lemma Call.loss_bound {S : Finset (Projectivization K V)} (c : Call S)
    {n : ℕ} (hdim : Module.finrank K V = n+3)
    (y : Projectivization K (Module.Dual K V)) :
    c.loss n y ≤ 12*(Nat.card K:ℝ) *
      (∑ x, kernel S x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  have h := (scheduled_from_original hdim S c.source c.proposal
    (c.source_nonempty.mono c.source_original) c.source_nonempty
    c.source_original c.source_proposal c.targetOriginal c.target c.domain
    c.target_nonempty c.target_original c.target_domain c.target_fraction
    2 c.overhead (by norm_num) c.source_fraction c.proposal_ratio
    (by convert c.sparse using 1; ring)).2.2 y
  norm_num only [show (1000:ℝ)*2=2000 by norm_num,
    show (6:ℝ)*2=12 by norm_num] at h
  simpa only [Call.loss, sum_filter, kernel_eq_uniform, mul_ite, mul_one, mul_zero] using h

end
end SharpLogRamsey.ReadyTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation Selection PivotGeometry GeometricCover ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

lemma Call.failure_bound {S : Finset (Projectivization K V)} (c : Call S)
    {n : ℕ} (hdim : Module.finrank K V = n+3) :
    1-c.production n ≤ exp (-(Nat.card K:ℝ)) := by
  have h := (scheduled_from_original hdim S c.source c.proposal
    (c.source_nonempty.mono c.source_original) c.source_nonempty
    c.source_original c.source_proposal c.targetOriginal c.target c.domain
    c.target_nonempty c.target_original c.target_domain c.target_fraction
    2 c.overhead (by norm_num) c.source_fraction c.proposal_ratio
    (by convert c.sparse using 1; ring)).2.1
  norm_num only [show (1000:ℝ)*2=2000 by norm_num] at h
  exact h

end
end SharpLogRamsey.ReadyTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_ScheduledBanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ScheduledBanks
open Finset Real Validation PublicTables
open scoped Classical BigOperators
noncomputable section
variable (P Q : Type*) [Fintype P] [Fintype Q]

variable {P Q}

theorem integral (q b : ℝ) (a : Address P Q)
    (A : (Fin (length q a) → P) → Prop) (f : (Fin (length q a) → P) → ℝ) :
    (∑ z, (bankLaw q b).mass z * outcome A f (cutoff q b a) (z a)) =
      PublicTables.integral (rowLaw a.1.1 a.1.2 (length q a)) A f (cutoff q b a) := by
  rw [show bankLaw (P:=P) (Q:=Q) q b = piLaw (atLaw q b) from rfl]
  rw [family_integral (atLaw q b) a (fun _ z => outcome A f (cutoff q b a) z)]
  change (∑ s, (outsideLaw (atLaw q b) a).mass s *
    PublicTables.integral (rowLaw a.1.1 a.1.2 (length q a)) A f (cutoff q b a)) = _
  rw [←sum_mul, (outsideLaw (atLaw q b) a).total, one_mul]

end
end SharpLogRamsey.ScheduledBanks

namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
theorem Call.bank_loss_eq {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (hb : c.overhead = b) (n : ℕ)
    (y : Projectivization K (Module.Dual K V)) :
    (∑ z, (bankLaw (Nat.card K) b).mass z *
      (c.bankRow b n z).elim 0 (fun row => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) row y then 1 else 0)) =
    c.loss n y := by
  have h := ScheduledBanks.integral (Nat.card K) b c.address (c.accept n)
    (fun row => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) row y then 1 else 0)
  convert h using 1
  · rfl
  · simp only [Call.loss, Call.accept, Call.address, length, cutoff, hb]
    rfl

omit [Finite K] [FiniteDimensional K V] in
 theorem Call.bank_production_eq {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (hb : c.overhead = b) (n : ℕ) :
    (∑ z, (bankLaw (Nat.card K) b).mass z * (c.bankRow b n z).elim 0 (fun _ => 1)) =
      c.production n := by
  have h := ScheduledBanks.integral (Nat.card K) b c.address (c.accept n) (fun _ => 1)
  convert h using 1
  · rfl
  · simp only [Call.production, Call.accept, Call.address, length, cutoff, hb]
    rfl

 theorem Call.bank_loss_bound {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (hb : c.overhead=b) {n : ℕ} (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K V)) :
    (∑ z, (bankLaw (Nat.card K) b).mass z *
      (c.bankRow b n z).elim 0 (fun row => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) row y then 1 else 0)) ≤
    12*(Nat.card K:ℝ)*(∑ x, SupportMixtures.kernel S x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  rw [c.bank_loss_eq b hb n y]
  exact c.loss_bound hdim y

 theorem Call.bank_failure_bound {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (hb : c.overhead=b) {n : ℕ} (hdim : Module.finrank K V=n+3) :
    (∑ z, (bankLaw (Nat.card K) b).mass z * (if c.bankRow b n z = none then 1 else 0)) ≤
      exp (-(Nat.card K:ℝ)) := by
  have he (z) : (if c.bankRow b n z = none then (1:ℝ) else 0) =
      1-(c.bankRow b n z).elim 0 (fun _=>1) := by cases c.bankRow b n z <;> simp
  simp_rw [he, mul_sub, mul_one]
  rw [sum_sub_distrib, (bankLaw (P:=Projectivization K V)
    (Q:=Projectivization K (Module.Dual K V)) (Nat.card K) b).total,
    c.bank_production_eq b hb n]
  exact c.failure_bound hdim

end
end SharpLogRamsey.ReadyTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotBanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

lemma Input.next_none (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) :
    d.next hdim z=none ↔ d.firstCall.bankRow (b+log 1000000) n z=none := by
  unfold Input.next
  split <;> simp_all

lemma Input.next_overhead (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (c : Call B) (hc : d.next hdim z=some c) :
    c.overhead=b+log 1000000 := by
  unfold Input.next at hc
  split at hc
  · cases hc
  · cases Option.some.inj hc
    rfl

theorem Input.failure_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.failure hdim z w) ≤
      2*exp (-(Nat.card K:ℝ)) := by
  let e := exp (-(Nat.card K:ℝ))
  have he : 0≤e := (exp_pos _).le
  have hf := d.firstCall.bank_failure_bound (b+log 1000000) rfl hdim
  have hlocal (z : FirstBank (K:=K) (V:=V) b) :
      (∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.failure hdim z w) ≤
      (if d.firstCall.bankRow (b+log 1000000) n z=none then 1 else 0)+e := by
    unfold Input.failure
    cases hc : d.next hdim z with
    | none =>
      have hr := (d.next_none hdim z).mp hc
      simp only [Option.elim_none, mul_one, ite_eq_left hr, PublicTables.Law.total]
      linarith
    | some c =>
      have hr : d.firstCall.bankRow (b+log 1000000) n z≠none := by
        intro hr
        rw [(d.next_none hdim z).mpr hr] at hc
        cases hc
      simp only [Option.elim_some, ite_eq_right hr, zero_add]
      exact c.bank_failure_bound (b+log 1000000) (d.next_overhead hdim z c hc)
        (Subspace.dual_finrank_eq.trans hdim)
  calc
    _ ≤ ∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ((if d.firstCall.bankRow (b+log 1000000) n z=none then 1 else 0)+e) := by
        apply sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (hlocal z) ((bankLaw _ _).nonneg z)
    _ = (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      (if d.firstCall.bankRow (b+log 1000000) n z=none then 1 else 0))+e := by
        simp only [mul_add, sum_add_distrib, ←sum_mul, PublicTables.Law.total, one_mul]
    _ ≤ _ := by dsimp only [e]; linarith

 theorem Input.second_loss_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K (Module.Dual K V))) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.secondLoss hdim y z w) ≤
      12*(Nat.card K:ℝ)*(∑ x, SupportMixtures.kernel B x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  let E := 12*(Nat.card K:ℝ)*(∑ x, SupportMixtures.kernel B x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0))
  have hE : 0≤E := by
    dsimp only [E]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun x _ => mul_nonneg (SupportMixtures.kernel_nonneg _ _) (by split_ifs <;> norm_num))
  have hlocal (z : FirstBank (K:=K) (V:=V) b) :
      (∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.secondLoss hdim y z w) ≤ E := by
    unfold Input.secondLoss
    cases hc : d.next hdim z with
    | none => simpa only [Option.elim_none, mul_zero, sum_const_zero] using hE
    | some c =>
      simp only [Option.elim_some]
      exact c.bank_loss_bound (b+log 1000000) (d.next_overhead hdim z c hc)
        (Subspace.dual_finrank_eq.trans hdim) y
  calc
    _ ≤ ∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z * E := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (hlocal z) ((bankLaw _ _).nonneg z)
    _ = E := by rw [←sum_mul, PublicTables.Law.total, one_mul]

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma Input.firstRow_eq (d : Input n A B b) (z : FirstBank (K:=K) (V:=V) b) :
    d.firstCall.bankRow (b+log 1000000) n z =
      (d.firstCall.bankIndex (b+log 1000000) n z).map (rowAt _ (z d.firstCall.address)) := by
  exact (reconstruct_first _ _ _).symm

lemma Input.next_of_index (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b)
    (i : Fin (cutoff (Nat.card K) (b+log 1000000) d.firstCall.address))
    (hi : d.firstCall.bankIndex (b+log 1000000) n z=some i) :
    d.next hdim z=some (d.secondCall hdim (rowAt _ (z d.firstCall.address) i)
      (index_valid _ _ _ i hi)) := by
  have hr : d.firstCall.bankRow (b+log 1000000) n z=some (rowAt _ (z d.firstCall.address) i) := by
    rw [d.firstRow_eq,hi,Option.map_some]
  unfold Input.next
  split
  · rename_i he
    rw [he] at hr
    cases hr
  · rename_i r he
    have hrow := Option.some.inj (he.symm.trans hr)
    subst r
    rfl

lemma Input.choose_of_index (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (i : Fin (cutoff (Nat.card K) (b+log 1000000) d.firstCall.address))
    (hi : d.firstCall.bankIndex (b+log 1000000) n z=some i) :
    d.choose hdim z w =
      let c := d.secondCall hdim (rowAt _ (z d.firstCall.address) i) (index_valid _ _ _ i hi)
      (c.bankIndex (b+log 1000000) n w).map (fun j=>(⟨d.firstCall.address,i⟩,⟨c.address,j⟩)) := by
  unfold Input.choose
  split
  · rename_i he
    rw [he] at hi
    cases hi
  · rename_i j he
    have hij := Option.some.inj (he.symm.trans hi)
    subst j
    rfl

lemma Input.choose_first_fail (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (hi : d.firstCall.bankIndex (b+log 1000000) n z=none) : d.choose hdim z w=none := by
  unfold Input.choose
  split
  · rfl
  · rename_i j he
    rw [hi] at he
    cases he

lemma Input.choose_failure (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    (if d.choose hdim z w=none then (1:ℝ) else 0)=d.failure hdim z w := by
  cases hi : d.firstCall.bankIndex (b+log 1000000) n z with
  | none =>
    have hr : d.firstCall.bankRow (b+log 1000000) n z=none := by
      rw [d.firstRow_eq,hi,Option.map_none]
    have hn := (d.next_none hdim z).mpr hr
    rw [d.choose_first_fail hdim z w hi]
    simp only [Input.failure,hn,Option.elim_none,ite_true]
  | some i =>
    let c := d.secondCall hdim (rowAt _ (z d.firstCall.address) i) (index_valid _ _ _ i hi)
    have hn : d.next hdim z=some c := d.next_of_index hdim z i hi
    have hr : c.bankRow (b+log 1000000) n w =
        (c.bankIndex (b+log 1000000) n w).map (rowAt _ (w c.address)) :=
      (reconstruct_first _ _ _).symm
    rw [d.choose_of_index hdim z w i hi]
    simp only [Input.failure,hn,Option.elim_some]
    change (if (c.bankIndex (b+log 1000000) n w).map _=none then (1:ℝ) else 0)=_
    rw [hr]
    cases c.bankIndex (b+log 1000000) n w <;> simp

theorem Input.choose_failure_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w *
        (if d.choose hdim z w=none then 1 else 0)) ≤ 2*exp (-(Nat.card K:ℝ)) := by
  simp_rw [d.choose_failure hdim]
  exact d.failure_bound hdim

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotLosses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Finite K] in
lemma read_mask_first (b : ℝ) (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (c : Code (K:=K) (V:=V) b) :
    (read b z w U c).1=U.1∩(mask b z w U c).1 := by
  ext x
  simp [read,mask,primalCap]

omit [Finite K] in
lemma read_mask_second (b : ℝ) (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (c : Code (K:=K) (V:=V) b) :
    (read b z w U c).2=U.2∩(mask b z w U c).2 := by
  ext x
  simp [read,mask,cap]

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

lemma Input.dual_loss_le (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K V))
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    d.dualLoss hdim y z w ≤ (d.firstCall.bankRow (b+log 1000000) n z).elim 0
      (fun r=>if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) r y then 1 else 0) := by
  unfold Input.dualLoss
  rw [d.firstRow_eq]
  cases hi : d.firstCall.bankIndex (b+log 1000000) n z with
  | none => rw [d.choose_first_fail hdim z w hi]; simp
  | some i =>
    rw [d.choose_of_index hdim z w i hi]
    let c := d.secondCall hdim (rowAt _ (z d.firstCall.address) i) (index_valid _ _ _ i hi)
    change ((c.bankIndex (b+log 1000000) n w).map _).elim _ _ ≤ _
    cases c.bankIndex (b+log 1000000) n w <;> simp [mask,read,cap]
    split_ifs <;> norm_num

lemma Input.primal_loss_eq (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (x : Projectivization K V)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    d.primalLoss hdim x z w=d.secondLoss hdim (bidual x) z w := by
  unfold Input.primalLoss Input.secondLoss
  cases hi : d.firstCall.bankIndex (b+log 1000000) n z with
  | none =>
    have hr : d.firstCall.bankRow (b+log 1000000) n z=none := by
      rw [d.firstRow_eq,hi,Option.map_none]
    rw [d.choose_first_fail hdim z w hi,(d.next_none hdim z).mpr hr]
    rfl
  | some i =>
    rw [d.choose_of_index hdim z w i hi,d.next_of_index hdim z i hi]
    let c := d.secondCall hdim (rowAt _ (z d.firstCall.address) i) (index_valid _ _ _ i hi)
    change ((c.bankIndex (b+log 1000000) n w).map _).elim _ _ =
      (c.bankRow (b+log 1000000) n w).elim _ _
    have hr : c.bankRow (b+log 1000000) n w =
        (c.bankIndex (b+log 1000000) n w).map (rowAt _ (w c.address)) :=
      (reconstruct_first _ _ _).symm
    rw [hr]
    cases c.bankIndex (b+log 1000000) n w <;> simp [mask,read,primalCap]
    rfl

theorem Input.dual_loss_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K V)) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.dualLoss hdim y z w) ≤
      12*(Nat.card K:ℝ)*(∑ x, SupportMixtures.kernel A x *
        (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  apply le_trans _ (d.firstCall.bank_loss_bound (b+log 1000000) rfl hdim y)
  apply sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ ((bankLaw _ _).nonneg z)
  calc
    _ ≤ ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w *
      (d.firstCall.bankRow (b+log 1000000) n z).elim 0
        (fun r=>if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) r y then 1 else 0) := by
      apply sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (d.dual_loss_le hdim y z w) ((bankLaw _ _).nonneg w)
    _ = _ := by rw [←sum_mul,PublicTables.Law.total,one_mul]

theorem Input.primal_loss_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (x : Projectivization K V) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.primalLoss hdim x z w) ≤
      12*(Nat.card K:ℝ)*(∑ y, SupportMixtures.kernel B y *
        (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  simp_rw [d.primal_loss_eq hdim]
  simpa only [ProjectiveDuality.incident_bidual] using d.second_loss_bound hdim (bidual x)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Finite K] [FiniteDimensional K V] in
lemma banks_integral (b : ℝ) (f : Banks (K:=K) (V:=V) b→ℝ) :
    (∑ x,(banksLaw b).mass x*f x) =
      ∑ z,(bankLaw (Nat.card K) (b+log 1000000)).mass z *
        ∑ w,(bankLaw (Nat.card K) (b+log 1000000)).mass w*f (z,w) := by
  simp only [banksLaw,Fintype.sum_prod_type,mul_assoc,mul_sum]

variable {n : ℕ} {b τ P H : ℝ}

variable (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

theorem Book.ready_failure (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (hr : s.Ready τ U) :
    (∑ z,(banksLaw b).mass z*(if book.choose hdim hτ hτsmall s z U=none then 1 else 0)) ≤
      2*exp (-(Nat.card K:ℝ)) := by
  simp only [Book.choose,dite_eq_left hr]
  rw [banks_integral]
  exact (book.prepare hdim hτ hτsmall s U hr).choose_failure_bound hdim

theorem Book.dual_exclusion (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (y : Projectivization K (Module.Dual K V)) :
    (∑ z,(banksLaw b).mass z*(book.choose hdim hτ hτsmall s z U).elim 0
      (fun c=>if y∉(mask b z.1 z.2 U c).2 then 1 else 0)) ≤
      12*(Nat.card K:ℝ)*(∑ x,SupportMixtures.kernel s.A x *
        (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  by_cases hr : s.Ready τ U
  · simp only [Book.choose,dite_eq_left hr]
    rw [banks_integral]
    exact (book.prepare hdim hτ hτsmall s U hr).dual_loss_bound hdim y
  · simp only [Book.choose,dite_eq_right hr,Option.elim_none,mul_zero,sum_const_zero]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun x _=>mul_nonneg (SupportMixtures.kernel_nonneg _ _) (by split_ifs <;> norm_num))

theorem Book.primal_exclusion (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (x : Projectivization K V) :
    (∑ z,(banksLaw b).mass z*(book.choose hdim hτ hτsmall s z U).elim 0
      (fun c=>if x∉(mask b z.1 z.2 U c).1 then 1 else 0)) ≤
      12*(Nat.card K:ℝ)*(∑ y,SupportMixtures.kernel s.B y *
        (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  by_cases hr : s.Ready τ U
  · simp only [Book.choose,dite_eq_left hr]
    rw [banks_integral]
    exact (book.prepare hdim hτ hτsmall s U hr).primal_loss_bound hdim x
  · simp only [Book.choose,dite_eq_right hr,Option.elim_none,mul_zero,sum_const_zero]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun y _=>mul_nonneg (SupportMixtures.kernel_nonneg _ _) (by split_ifs <;> norm_num))

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_ChronologicalExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset PublicTables SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B C Ξ I : Type*} [Fintype A] [Fintype B] [Fintype Ξ]
  [DecidableEq I] {α : I→Type*}

lemma card_mul_kernel_sum (Y : Finset A) (f : A→ℝ) :
    (Y.card:ℝ)*(∑ y,kernel Y y*f y)=∑ y∈Y,f y := by
  by_cases h : Y.Nonempty
  · have hc : (Y.card:ℝ)≠0 := by exact_mod_cast card_ne_zero.mpr h
    calc
      _ = ∑ y,if y∈Y then f y else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro y _
        by_cases hy : y∈Y <;> simp [kernel,hy,hc]
      _ = _ := by simp
  · have he : Y=∅ := not_nonempty_iff_eq_empty.mp h
    simp [he]

omit [Fintype A] in
lemma sdiff_card_eq_sum (Y T : Finset A) :
    ((Y\T).card:ℝ) = ∑ y∈Y,if y∉T then (1:ℝ) else 0 := by
  rw [←sum_filter]
  have hf : Y.filter (fun y=>y∉T)=Y\T := by ext y; simp
  rw [hf]
  simp only [sum_const,nsmul_eq_mul,mul_one]

omit [Fintype A] [Fintype B] [DecidableEq I] in
lemma firstLoss_points (choose : ∀ i,α i→TreeDecoder.Domains A B→Option C)
    (mask : ∀ i,α i→TreeDecoder.CapReader A B C) (Y : Finset A)
    (i : I) (U : TreeDecoder.Domains A B) (z : α i) :
    firstLoss choose mask Y i U z = ∑ y∈Y,(choose i z U).elim 0
      (fun c=>if y∉(mask i z U c).1 then 1 else 0) := by
  cases h : choose i z U with
  | none=>simp [firstLoss,h]
  | some c=>simp only [firstLoss,h,Option.elim_some]; exact sdiff_card_eq_sum _ _

omit [Fintype A] [Fintype B] [DecidableEq I] in
lemma secondLoss_points (choose : ∀ i,α i→TreeDecoder.Domains A B→Option C)
    (mask : ∀ i,α i→TreeDecoder.CapReader A B C) (Y : Finset B)
    (i : I) (U : TreeDecoder.Domains A B) (z : α i) :
    secondLoss choose mask Y i U z = ∑ y∈Y,(choose i z U).elim 0
      (fun c=>if y∉(mask i z U c).2 then 1 else 0) := by
  cases h : choose i z U with
  | none=>simp [secondLoss,h]
  | some c=>simp only [secondLoss,h,Option.elim_some]; exact sdiff_card_eq_sum _ _

end
end SharpLogRamsey.FreshExecution

namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder FreshExecution SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Finite K] in
lemma chronoRead_first (b : ℝ) (z : Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) (c : Code (K:=K) (V:=V) b) :
    (chronoRead b z U c).1=U.1∩(chronoMask b z U c).1 :=
  read_mask_second b z.1 z.2 U.swap c

omit [Finite K] in
lemma chronoRead_second (b : ℝ) (z : Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) (c : Code (K:=K) (V:=V) b) :
    (chronoRead b z U c).2=U.2∩(chronoMask b z U c).2 :=
  read_mask_first b z.1 z.2 U.swap c

variable {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

theorem Book.first_loss_bound {I : Type*} [DecidableEq I]
    (s : I→Original (K:=K) (V:=V) n b) (i : I)
    (Y : Finset (Projectivization K (Module.Dual K V)))
    (U : ChronoDomains (K:=K) (V:=V)) :
    (∑ z,(banksLaw b).mass z*firstLoss (fun i=>book.chronoChoose hdim hτ hτsmall (s i))
      (fun _=>chronoMask b) Y i U z) ≤
      12*(Nat.card K:ℝ)*Y.card*pairing (kernel Y) (kernel (s i).A)
        (fun y x=>if y.rep x.rep=0 then 1 else 0) := by
  simp_rw [firstLoss_points,mul_sum]
  rw [sum_comm]
  calc
    _ ≤ ∑ y∈Y,12*(Nat.card K:ℝ)*∑ x,kernel (s i).A x *
        (if y.rep x.rep=0 then 1 else 0) := by
      apply sum_le_sum
      intro y hy
      exact book.dual_exclusion hdim hτ hτsmall (s i) U.swap y
    _ = 12*(Nat.card K:ℝ)*(∑ y∈Y,∑ x,kernel (s i).A x *
        (if y.rep x.rep=0 then 1 else 0)) := by rw [mul_sum]
    _ = 12*(Nat.card K:ℝ)*(Y.card*pairing (kernel Y) (kernel (s i).A)
        (fun y x=>if y.rep x.rep=0 then 1 else 0)) := by
      congr 1
      have he : pairing (kernel Y) (kernel (s i).A) (fun y x=>if y.rep x.rep=0 then 1 else 0) =
          ∑ y,kernel Y y*(∑ x,kernel (s i).A x*(if y.rep x.rep=0 then 1 else 0)) := by
        simp only [pairing,mul_sum,mul_assoc]
      rw [he,card_mul_kernel_sum]
    _ = _ := by ring

theorem Book.second_loss_bound {I : Type*} [DecidableEq I]
    (s : I→Original (K:=K) (V:=V) n b) (i : I)
    (Y : Finset (Projectivization K V))
    (U : ChronoDomains (K:=K) (V:=V)) :
    (∑ z,(banksLaw b).mass z*secondLoss (fun i=>book.chronoChoose hdim hτ hτsmall (s i))
      (fun _=>chronoMask b) Y i U z) ≤
      12*(Nat.card K:ℝ)*Y.card*pairing (kernel (s i).B) (kernel Y)
        (fun y x=>if y.rep x.rep=0 then 1 else 0) := by
  simp_rw [secondLoss_points,mul_sum]
  rw [sum_comm]
  calc
    _ ≤ ∑ x∈Y,12*(Nat.card K:ℝ)*∑ y,kernel (s i).B y *
        (if y.rep x.rep=0 then 1 else 0) := by
      apply sum_le_sum
      intro x hx
      exact book.primal_exclusion hdim hτ hτsmall (s i) U.swap x
    _ = 12*(Nat.card K:ℝ)*(∑ x∈Y,∑ y,kernel (s i).B y *
        (if y.rep x.rep=0 then 1 else 0)) := by rw [mul_sum]
    _ = 12*(Nat.card K:ℝ)*(Y.card*pairing (kernel (s i).B) (kernel Y)
        (fun y x=>if y.rep x.rep=0 then 1 else 0)) := by
      congr 1
      rw [pairing_reverse]
      have he : pairing (kernel Y) (kernel (s i).B) (fun x y=>if y.rep x.rep=0 then 1 else 0) =
          ∑ x,kernel Y x*(∑ y,kernel (s i).B y*(if y.rep x.rep=0 then 1 else 0)) := by
        simp only [pairing,mul_sum,mul_assoc]
      rw [he,card_mul_kernel_sum]
    _ = _ := by ring
end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_OriginalTreeLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence PublicTables FreshExecution TreeDecoder SupportMixtures BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

omit [Finite K] [FiniteDimensional K V] in
lemma banks_nonempty (b : ℝ) : Nonempty (Banks (K:=K) (V:=V) b) := by
  by_contra h
  have : IsEmpty (Banks (K:=K) (V:=V) b) := not_nonempty_iff.mp h
  have hh := (banksLaw (K:=K) (V:=V) b).total
  simp at hh

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma density_nonneg (S : Finset (Projectivization K (Module.Dual K V)))
    (T : Finset (Projectivization K V)) : 0≤density S T := by
  unfold density pairing
  exact sum_nonneg (fun y _=>sum_nonneg (fun x _=>
    mul_nonneg (mul_nonneg (kernel_nonneg _ _) (kernel_nonneg _ _)) (by dsimp only; split_ifs <;> norm_num)))

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma density_eq_count (S : Finset (Projectivization K (Module.Dual K V)))
    (T : Finset (Projectivization K V)) :
    density S T=(incidenceCount T S:ℝ)/((T.card:ℝ)*S.card) := by
  unfold density
  rw [Selection.pairing_reverse,kernel_incidence,incidenceCount_eq_card]
  rfl

variable {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.banksFintype
omit [Fintype I] [DecidableEq I] in
lemma Book.ready_failure_chrono (s : I→Original (K:=K) (V:=V) n b) (i : I)
    (U : ChronoDomains (K:=K) (V:=V)) :
    (∑ z,(banksLaw (K:=K) (V:=V) b).mass z*readyFailure
      (fun i=>book.chronoChoose hdim hτ hτsmall (s i)) (s i).B (s i).A
      ((incidenceCount (s i).A (s i).B:ℝ)>τ*((s i).A.card:ℝ)*(s i).B.card/Nat.card K) i U z) ≤
        2*exp (-(Nat.card K:ℝ)) := by
  by_cases hr : (s i).Ready τ U.swap
  · have hh := book.ready_failure hdim hτ hτsmall (s i) U.swap hr
    have hB : ¬((s i).B∩U.1).card<(9/10:ℝ)*(s i).B.card := not_lt.mpr hr.2.1
    have hA : ¬((s i).A∩U.2).card<(9/10:ℝ)*(s i).A.card := not_lt.mpr hr.1
    have hD : ¬τ*((s i).A.card:ℝ)*(s i).B.card/Nat.card K<
        (incidenceCount (s i).A (s i).B:ℝ) := not_lt.mpr hr.2.2
    simp only [readyFailure,hB,hA,hD,not_false_eq_true,and_self,ite_true,
      trialFailure,Book.chronoChoose]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  · have hn : ¬(¬((s i).B∩U.1).card<(9/10:ℝ)*(s i).B.card ∧
        ¬((s i).A∩U.2).card<(9/10:ℝ)*(s i).A.card ∧
        ¬τ*((s i).A.card:ℝ)*(s i).B.card/Nat.card K<(incidenceCount (s i).A (s i).B:ℝ)) := by
      intro hh
      apply hr
      exact ⟨not_lt.mp hh.2.1,not_lt.mp hh.1,not_lt.mp hh.2.2⟩
    simp only [readyFailure,ite_eq_right hn,mul_zero,sum_const_zero]
    positivity

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem original_density_rejection (μ : Law Ω) (s : Ω→Original (K:=K) (V:=V) n b)
    (hτpos : 0<τ) (E : ℝ)
    (hmean : (∑ ω,μ.mass ω*density (s ω).B (s ω).A)≤E) :
    (∑ ω,μ.mass ω*(if τ*((s ω).A.card:ℝ)*(s ω).B.card/Nat.card K<
      (incidenceCount (s ω).A (s ω).B:ℝ) then 1 else 0))≤(Nat.card K:ℝ)*E/τ := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  have hpoint (ω : Ω) : (if τ*((s ω).A.card:ℝ)*(s ω).B.card/Nat.card K<
      (incidenceCount (s ω).A (s ω).B:ℝ) then (1:ℝ) else 0)≤(Nat.card K:ℝ)*density (s ω).B (s ω).A/τ := by
    split_ifs with hh
    · have ha : (0:ℝ)<(s ω).A.card := by exact_mod_cast card_pos.mpr (s ω).nonemptyA
      have hb : (0:ℝ)<(s ω).B.card := by exact_mod_cast card_pos.mpr (s ω).nonemptyB
      rw [density_eq_count]
      apply le_of_lt
      apply (lt_div_iff₀ hτpos).mpr
      have hp := (div_lt_iff₀ hq).mp hh
      rw [←mul_div_assoc]
      apply (lt_div_iff₀ (mul_pos ha hb)).mpr
      convert hp using 1 <;> ring
    · exact div_nonneg (mul_nonneg hq.le (density_nonneg _ _)) hτpos.le
  calc
    _ ≤ ∑ ω,μ.mass ω*((Nat.card K:ℝ)*density (s ω).B (s ω).A/τ) :=
      sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (hpoint ω) (μ.nonneg ω))
    _ = (Nat.card K:ℝ)*(∑ ω,μ.mass ω*density (s ω).B (s ω).A)/τ := by
      simp only [mul_sum,sum_div]
      apply sum_congr rfl
      intros
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmean hq.le) hτpos.le

theorem Book.first_trim (μ : Law Ω) (s : Ω→I→Original (K:=K) (V:=V) n b)
    (target : I) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (ht : Separated t) (hmem : target∈labels t) (hU : ∀ ω,(s ω target).B⊆U.1)
    (E : ℝ) (hE : 0≤E)
    (hmean : ∀ i∈leftPath target t,(∑ ω,μ.mass ω*density (s ω target).B (s ω i).A)≤E) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      (if firstTrim (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) (s ω target).B target t U z then (1:ℝ) else 0)))≤
      10*t.height*(12*(Nat.card K:ℝ)*E) := by
  apply original_first_trim μ (fun _=>banksLaw (K:=K) (V:=V) b) (fun _=>(banks_nonempty (K:=K) (V:=V) b).some)
    (fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)) (fun _ _=>chronoRead b)
    (fun _ _=>chronoMask b) (fun _ _=>chronoRead_first b)
    target (fun ω=>(s ω target).B) (fun ω=>(s ω target).nonemptyB) t U ht hmem hU
    (fun ω i=>12*(Nat.card K:ℝ)*(s ω target).B.card*density (s ω target).B (s ω i).A)
    (fun ω i _=>mul_nonneg (by positivity) (density_nonneg _ _))
    (fun ω i _=>book.first_loss_bound hdim hτ hτsmall (s ω) i (s ω target).B)
    (12*(Nat.card K:ℝ)*E) (by positivity)
  intro i hi
  have hc (ω : Ω) : ((s ω target).B.card:ℝ)≠0 := by
    exact_mod_cast card_ne_zero.mpr (s ω target).nonemptyB
  have he (ω : Ω) : (12*(Nat.card K:ℝ)*(s ω target).B.card*density (s ω target).B (s ω i).A)/
      (s ω target).B.card = 12*(Nat.card K:ℝ)*density (s ω target).B (s ω i).A := by
    field_simp [hc ω]
  simp only [he]
  calc
    _ = 12*(Nat.card K:ℝ)*(∑ ω,μ.mass ω*density (s ω target).B (s ω i).A) := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmean i hi) (by positivity)

theorem Book.second_trim (μ : Law Ω) (s : Ω→I→Original (K:=K) (V:=V) n b)
    (target : I) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (ht : Separated t) (hmem : target∈labels t) (hU : ∀ ω,(s ω target).A⊆U.2)
    (E : ℝ) (hE : 0≤E)
    (hmean : ∀ i∈rightPath target t,(∑ ω,μ.mass ω*density (s ω i).B (s ω target).A)≤E) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      (if secondTrim (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) (s ω target).A target t U z then (1:ℝ) else 0)))≤
      10*t.height*(12*(Nat.card K:ℝ)*E) := by
  apply original_second_trim μ (fun _=>banksLaw (K:=K) (V:=V) b) (fun _=>(banks_nonempty (K:=K) (V:=V) b).some)
    (fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)) (fun _ _=>chronoRead b)
    (fun _ _=>chronoMask b) (fun _ _=>chronoRead_second b)
    target (fun ω=>(s ω target).A) (fun ω=>(s ω target).nonemptyA) t U ht hmem hU
    (fun ω i=>12*(Nat.card K:ℝ)*(s ω target).A.card*density (s ω i).B (s ω target).A)
    (fun ω i _=>mul_nonneg (by positivity) (density_nonneg _ _))
    (fun ω i _=>book.second_loss_bound hdim hτ hτsmall (s ω) i (s ω target).A)
    (12*(Nat.card K:ℝ)*E) (by positivity)
  intro i hi
  have hc (ω : Ω) : ((s ω target).A.card:ℝ)≠0 := by
    exact_mod_cast card_ne_zero.mpr (s ω target).nonemptyA
  have he (ω : Ω) : (12*(Nat.card K:ℝ)*(s ω target).A.card*density (s ω i).B (s ω target).A)/
      (s ω target).A.card = 12*(Nat.card K:ℝ)*density (s ω i).B (s ω target).A := by
    field_simp [hc ω]
  simp only [he]
  calc
    _ = 12*(Nat.card K:ℝ)*(∑ ω,μ.mass ω*density (s ω i).B (s ω target).A) := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmean i hi) (by positivity)

theorem Book.deletion_loss (μ : Law Ω) (s : Ω→I→Original (K:=K) (V:=V) n b)
    (target : I) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (ht : Separated t) (hmem : target∈labels t)
    (hU : ∀ ω,∀ i∈labels t,(s ω i).B⊆U.1 ∧ (s ω i).A⊆U.2)
    (hτpos : 0<τ) (E : ℝ) (hE : 0≤E)
    (hfirst : ∀ i∈plannedPath target t,∀ j∈leftPath i t,
      (∑ ω,μ.mass ω*density (s ω i).B (s ω j).A)≤E)
    (hsecond : ∀ i∈plannedPath target t,∀ j∈rightPath i t,
      (∑ ω,μ.mass ω*density (s ω j).B (s ω i).A)≤E)
    (hself : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*density (s ω i).B (s ω i).A)≤E) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      (1-pivotSuccess (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) target t U z)))≤
      20*(12*(Nat.card K:ℝ)*E)*t.height^2+
        ((Nat.card K:ℝ)*E/τ+2*exp (-(Nat.card K:ℝ)))*t.height := by
  apply original_deletion_quadratic μ (fun _=>banksLaw (K:=K) (V:=V) b)
    (fun _=>(banks_nonempty (K:=K) (V:=V) b).some)
    (fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)) (fun _ _=>chronoRead b)
    (fun ω i=>(s ω i).B) (fun ω i=>(s ω i).A)
    (fun ω i=>τ*((s ω i).A.card:ℝ)*(s ω i).B.card/Nat.card K<
      (incidenceCount (s ω i).A (s ω i).B:ℝ)) target t U ht hmem
    (12*(Nat.card K:ℝ)*E) ((Nat.card K:ℝ)*E/τ) (2*exp (-(Nat.card K:ℝ)))
    (by positivity) (by positivity) (by positivity)
  · intro i hi
    exact book.first_trim hdim hτ hτsmall μ s i t U ht (plannedPath_subset target t hi)
      (fun ω=>(hU ω i (plannedPath_subset target t hi)).1) E hE (hfirst i hi)
  · intro i hi
    exact book.second_trim hdim hτ hτsmall μ s i t U ht (plannedPath_subset target t hi)
      (fun ω=>(hU ω i (plannedPath_subset target t hi)).2) E hE (hsecond i hi)
  · intro i hi
    exact original_density_rejection μ (fun ω=>s ω i) hτpos E (hself i hi)
  · intro i hi ω V
    exact book.ready_failure_chrono hdim hτ hτsmall (s ω) i V

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_OriginalTargetLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence PublicTables FreshExecution TreeDecoder SupportMixtures BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma firstTargetDensity_nonneg (good : Prop) (y : Projectivization K (Module.Dual K V))
    (T : Finset (Projectivization K V)) : 0≤firstTargetDensity good y T := by
  unfold firstTargetDensity
  split_ifs
  · exact sum_nonneg (fun x _=>mul_nonneg (kernel_nonneg _ _) (by split_ifs <;> norm_num))
  · exact le_rfl

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma secondTargetDensity_nonneg (good : Prop) (x : Projectivization K V)
    (S : Finset (Projectivization K (Module.Dual K V))) : 0 ≤ secondTargetDensity good x S := by
  unfold secondTargetDensity
  split_ifs
  · exact sum_nonneg (fun y _=>mul_nonneg (kernel_nonneg _ _) (by split_ifs <;> norm_num))
  · exact le_rfl

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma firstTargetDensity_eq (good : Prop) (y : Projectivization K (Module.Dual K V))
    (T : Finset (Projectivization K V)) :
    ((goodSingleton good y).card:ℝ)*density (goodSingleton good y) T=firstTargetDensity good y T := by
  have he : density (goodSingleton good y) T =
      ∑ y',kernel (goodSingleton good y) y' * (∑ x,kernel T x*(if y'.rep x.rep=0 then 1 else 0)) := by
    simp only [density,pairing,mul_sum,mul_assoc]
  rw [he,card_mul_kernel_sum]
  by_cases hg : good <;> simp [goodSingleton,hg,firstTargetDensity]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma secondTargetDensity_eq (good : Prop) (x : Projectivization K V)
    (S : Finset (Projectivization K (Module.Dual K V))) :
    ((goodSingleton good x).card:ℝ)*density S (goodSingleton good x)=secondTargetDensity good x S := by
  have he : density S (goodSingleton good x) =
      ∑ x',kernel (goodSingleton good x) x' * (∑ y,kernel S y*(if y.rep x'.rep=0 then 1 else 0)) := by
    unfold density
    rw [Selection.pairing_reverse]
    simp only [pairing,mul_sum,mul_assoc]
  rw [he,card_mul_kernel_sum]
  by_cases hg : good <;> simp [goodSingleton,hg,secondTargetDensity]

variable {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.targetBanksFintype
theorem Book.target_loss (μ : Law Ω) (s : Ω→I→Original (K:=K) (V:=V) n b)
    (target : I) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (ht : Separated t) (hmem : target∈labels t)
    (hU : ∀ ω,∀ i∈labels t,(s ω i).B⊆U.1 ∧ (s ω i).A⊆U.2)
    (goodA goodB : Ω→Prop) (a : Ω→Projectivization K (Module.Dual K V))
    (c : Ω→Projectivization K V) (haU : ∀ ω,a ω∈U.1) (hcU : ∀ ω,c ω∈U.2)
    (hτpos : 0<τ) (E EA EB δA δB : ℝ) (hE : 0≤E) (hEA : 0≤EA) (hEB : 0≤EB)
    (hfirst : ∀ i∈plannedPath target t,∀ j∈leftPath i t,
      (∑ ω,μ.mass ω*density (s ω i).B (s ω j).A)≤E)
    (hsecond : ∀ i∈plannedPath target t,∀ j∈rightPath i t,
      (∑ ω,μ.mass ω*density (s ω j).B (s ω i).A)≤E)
    (hself : ∀ i∈plannedPath target t,(∑ ω,μ.mass ω*density (s ω i).B (s ω i).A)≤E)
    (hmeanA : ∀ i∈insert target (leftPath target t),
      (∑ ω,μ.mass ω*firstTargetDensity (goodA ω) (a ω) (s ω i).A)≤EA)
    (hmeanB : ∀ i∈insert target (rightPath target t),
      (∑ ω,μ.mass ω*secondTargetDensity (goodB ω) (c ω) (s ω i).B)≤EB)
    (hbadA : (∑ ω,μ.mass ω*(if goodA ω then (0:ℝ) else 1))≤δA)
    (hbadB : (∑ ω,μ.mass ω*(if goodB ω then (0:ℝ) else 1))≤δB) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      targetFailure (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) (a ω) (c ω) target t U z))≤
      20*(12*(Nat.card K:ℝ)*E)*t.height^2+
        ((Nat.card K:ℝ)*E/τ+2*exp (-(Nat.card K:ℝ)))*t.height+
        δA+δB+((t.height:ℝ)+1)*(12*(Nat.card K:ℝ)*EA+12*(Nat.card K:ℝ)*EB) := by
  apply original_good_target_loss μ (fun _=>banksLaw (K:=K) (V:=V) b)
    (fun _=>(banks_nonempty (K:=K) (V:=V) b).some)
    (fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)) (fun _ _=>chronoRead b)
    (fun _ _=>chronoMask b) (fun _ _=>chronoRead_first b) (fun _ _=>chronoRead_second b)
    goodA goodB a c target t U ht hmem haU hcU
    (fun ω i=>12*(Nat.card K:ℝ)*firstTargetDensity (goodA ω) (a ω) (s ω i).A)
    (fun ω i=>12*(Nat.card K:ℝ)*secondTargetDensity (goodB ω) (c ω) (s ω i).B)
    (12*(Nat.card K:ℝ)*EA) (12*(Nat.card K:ℝ)*EB) _ δA δB (by positivity) (by positivity)
  · intros; exact mul_nonneg (by positivity) (firstTargetDensity_nonneg _ _ _)
  · intros; exact mul_nonneg (by positivity) (secondTargetDensity_nonneg _ _ _)
  · intro ω i hi U
    have hh := book.first_loss_bound hdim hτ hτsmall (s ω) i (goodSingleton (goodA ω) (a ω)) U
    change _≤12*(Nat.card K:ℝ)*_ * density _ _ at hh
    rw [mul_assoc,firstTargetDensity_eq] at hh
    exact hh
  · intro ω i hi U
    have hh := book.second_loss_bound hdim hτ hτsmall (s ω) i (goodSingleton (goodB ω) (c ω)) U
    change _≤12*(Nat.card K:ℝ)*_ * density _ _ at hh
    rw [mul_assoc,secondTargetDensity_eq] at hh
    exact hh
  · intro i hi
    calc
      _ = 12*(Nat.card K:ℝ)*(∑ ω,μ.mass ω*firstTargetDensity (goodA ω) (a ω) (s ω i).A) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmeanA i hi) (by positivity)
  · intro i hi
    calc
      _ = 12*(Nat.card K:ℝ)*(∑ ω,μ.mass ω*secondTargetDensity (goodB ω) (c ω) (s ω i).B) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmeanB i hi) (by positivity)
  · exact hbadA
  · exact hbadB
  · exact book.deletion_loss hdim hτ hτsmall μ s target t U ht hmem hU hτpos E hE hfirst hsecond hself

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FamilyAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

lemma Law.prod_left_sum (p : Law A) (q : Law B) (f : A → ℝ) :
    (∑ z, (p.prod q).mass z * f z.1) = ∑ a, p.mass a * f a := by
  simp only [Law.prod, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  simp only [←sum_mul, ←mul_sum, q.total, mul_one]

lemma Law.prod_right_sum (p : Law A) (q : Law B) (f : B → ℝ) :
    (∑ z, (p.prod q).mass z * f z.2) = ∑ b, q.mass b * f b := by
  simp only [Law.prod, Fintype.sum_prod_type, mul_assoc, ←mul_sum,
    ←sum_mul, p.total, one_mul]

namespace AuxiliarySupport
variable {p : I → Law A} {q : J → Law B} {goodA : I → Finset A}
  {goodB : J → Finset B} {MA κA : I → ℝ} {MB κB : J → ℝ}

lemma familyLaw_first_sum
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (i : I) (f : Finset A → ℝ) :
    (∑ z, (familyLaw X Y).mass z * f (z.1 i)) = ∑ S, (X i).setLaw.mass S * f S := by
  rw [familyLaw, Law.prod_left_sum (Law.pi (fun i => (X i).setLaw))
    (Law.pi (fun j => (Y j).setLaw)) (fun z : I → Finset A => f (z i))]
  exact Law.pi_coordinate_sum _ i f

lemma familyLaw_second_sum
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (j : J) (f : Finset B → ℝ) :
    (∑ z, (familyLaw X Y).mass z * f (z.2 j)) = ∑ S, (Y j).setLaw.mass S * f S := by
  rw [familyLaw, Law.prod_right_sum (Law.pi (fun i => (X i).setLaw))
    (Law.pi (fun j => (Y j).setLaw)) (fun z : J → Finset B => f (z j))]
  exact Law.pi_coordinate_sum _ j f

lemma familyLaw_first_density
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j)) (i : I) (a : A) :
    (∑ z, (familyLaw X Y).mass z * kernel (z.1 i) a) ≤
      (4*exp 1) * (if a ∈ goodA i then (p i).mass a else 0) := by
  rw [familyLaw_first_sum X Y i (fun S => kernel S a)]
  exact (X i).setLaw_density a

lemma familyLaw_second_density
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j)) (j : J) (b : B) :
    (∑ z, (familyLaw X Y).mass z * kernel (z.2 j) b) ≤
      (4*exp 1) * (if b ∈ goodB j then (q j).mass b else 0) := by
  rw [familyLaw_second_sum X Y j (fun S => kernel S b)]
  exact (Y j).setLaw_density b

lemma familyLaw_first_target
    {T : Type*} [Fintype T] (r : Law T) (goodT : Finset T)
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (i : I) (R : A → T → Prop) :
    (∑ z, (familyLaw X Y).mass z * pairing (kernel (z.1 i))
      (fun b => if b ∈ goodT then r.mass b else 0) (fun a b => if R a b then 1 else 0)) ≤
      (4*exp 1) * ((p i).prod r).event
        (univ.filter (fun z => z.1 ∈ goodA i ∧ z.2 ∈ goodT ∧ R z.1 z.2)) := by
  have h := one_sided_pairing_le (familyLaw X Y).mass (fun z => z.1 i)
    (fun a => if a ∈ goodA i then (p i).mass a else 0)
    (fun b => if b ∈ goodT then r.mass b else 0)
    (fun a b => if R a b then (1:ℝ) else 0) (4*exp 1)
    (familyLaw X Y).nonneg (by intro b; split_ifs <;> simp [r.nonneg])
    (by intros; split_ifs <;> norm_num) (familyLaw_first_density X Y i)
  simpa only [good_pairing_eq_event] using h

lemma familyLaw_second_target
    {T : Type*} [Fintype T] (r : Law T) (goodT : Finset T)
    (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (j : J) (R : B → T → Prop) :
    (∑ z, (familyLaw X Y).mass z * pairing (kernel (z.2 j))
      (fun b => if b ∈ goodT then r.mass b else 0) (fun a b => if R a b then 1 else 0)) ≤
      (4*exp 1) * ((q j).prod r).event
        (univ.filter (fun z => z.1 ∈ goodB j ∧ z.2 ∈ goodT ∧ R z.1 z.2)) := by
  have h := one_sided_pairing_le (familyLaw X Y).mass (fun z => z.2 j)
    (fun a => if a ∈ goodB j then (q j).mass a else 0)
    (fun b => if b ∈ goodT then r.mass b else 0)
    (fun a b => if R a b then (1:ℝ) else 0) (4*exp 1)
    (familyLaw X Y).nonneg (by intro b; split_ifs <;> simp [r.nonneg])
    (by intros; split_ifs <;> norm_num) (familyLaw_second_density X Y j)
  simpa only [good_pairing_eq_event] using h

end AuxiliarySupport
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_NullFreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω : Type*} [Fintype Ω]

lemma Law.prod_sum_swap {A : Type*} [Fintype A] (μ : Law Ω) (ρ : Law A)
    (f : Ω→A→ℝ) :
    (∑ z,(μ.prod ρ).mass z*f z.1 z.2)=∑ a,ρ.mass a*(∑ ω,μ.mass ω*f ω a) := by
  simp only [Law.prod,Fintype.sum_prod_type,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intros
  ring

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_VariableOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] [Fintype Ω] {α : I→Type*}

theorem expected_variable_loss (μ : Law Ω) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C) (z : Ω→∀ i,α i)
    (n : I→ℕ) (target : Ω→∀ i,Fin (n i)→A×B) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t)
    (hR : ∀ ω,∀ i∈labels t,∀ j,R (target ω i j).1 (target ω i j).2)
    (δ : ℝ)
    (hpoint : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*
      targetFailure (choose ω) (read ω) (target ω i j).1 (target ω i j).2 i t U (z ω))≤δ) :
    (∑ ω,μ.mass ω*((∑ i∈labels t,(n i:ℝ))-
      (fullOutput R (choose ω) (read ω) (fun i=>List.ofFn (target ω i)) (z ω) t U).length))≤
        (∑ i∈labels t,(n i:ℝ))*δ := by
  have hsize (ω : Ω) :
      ((population (fun i=>List.ofFn (target ω i)) t).length:ℝ)=∑ i∈labels t,(n i:ℝ) := by
    rw [population_length_sum _ t ht]
    simp only [List.length_ofFn]
  have he (ω : Ω) : (∑ i∈labels t,(n i:ℝ))-
      (fullOutput R (choose ω) (read ω) (fun i=>List.ofFn (target ω i)) (z ω) t U).length=
      ∑ i∈labels t,∑ j : Fin (n i),targetFailure (choose ω) (read ω)
        (target ω i j).1 (target ω i j).2 i t U (z ω) := by
    rw [←hsize ω,output_loss_eq_targets R (choose ω) (read ω) _ (z ω) t U ht]
    · simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    · intro i hi x hx
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx
      exact hR ω i hi j
  simp_rw [he,mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ i∈labels t,∑ j : Fin (n i),∑ ω,μ.mass ω*
        targetFailure (choose ω) (read ω) (target ω i j).1 (target ω i j).2 i t U (z ω) := by
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ ≤ ∑ i∈labels t,∑ _j : Fin (n i),δ := by
      apply sum_le_sum
      intro i hi
      exact sum_le_sum (fun j _=>hpoint i hi j)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,sum_mul]

variable [Fintype I] [∀ i,Fintype (α i)]

theorem original_variable_loss (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C)
    (n : I→ℕ) (target : Ω→∀ i,Fin (n i)→A×B) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t)
    (hR : ∀ ω,∀ i∈labels t,∀ j,R (target ω i j).1 (target ω i j).2)
    (δ : ℝ)
    (hpoint : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*∑ z,(piLaw p).mass z*
      targetFailure (choose ω) read (target ω i j).1 (target ω i j).2 i t U z)≤δ) :
    (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((∑ i∈labels t,(n i:ℝ))-
      (fullOutput R (choose ω) read (fun i=>List.ofFn (target ω i)) z t U).length))≤
        (∑ i∈labels t,(n i:ℝ))*δ := by
  have hh:=expected_variable_loss (sourcePublicLaw μ p) R (fun x=>choose x.1)
    (fun _=>read) (fun x=>x.2) n (fun x=>target x.1) t U ht (fun x=>hR x.1) δ
    (by
      intro i hi j
      have hp:=hpoint i hi j
      simpa only [sourcePublicLaw,Fintype.sum_prod_type,mul_assoc,←mul_sum] using hp)
  simp only [sourcePublicLaw,Fintype.sum_prod_type,mul_assoc,←mul_sum] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  apply sum_congr rfl
  intro z _
  ring

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

lemma Law.prod_map_left (p : Law X) (s : Law Y) (f : X→Z) :
    (p.prod s).map (fun z=>f z.1)=p.map f := by
  ext a
  simp only [Law.map,Law.prod,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  by_cases h : f x=a
  · simp only [h,ite_true,←mul_sum,s.total,mul_one]
  · simp only [h,ite_false,sum_const_zero]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_OriginalFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence SupportMixtures Selection Selection.AuxiliarySupport
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I : Type*} [Fintype I]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}

variable (X : ∀ i,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem originalFamily_density {n : ℕ} {b : ℝ} (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2)) (i j : I) :
    (∑ z,(familyLaw X Y).nullFree.mass z *
      density (originalFamily X Y hMA hMB hprod z i).B
        (originalFamily X Y hMA hMB hprod z j).A)≤
      (4*exp 1)*(4*exp 1)*((p i).prod (r j)).event
        (univ.filter (fun ay=>ay.1∈goodA i ∧ ay.2∈goodB j ∧ ay.1.rep ay.2.rep=0)) := by
  change (∑ z,(familyLaw X Y).nullFree.mass z * density (z.val.1 i) (z.val.2 j))≤_
  rw [(familyLaw X Y).nullFree_integral (fun z=>density (z.1 i) (z.2 j))]
  exact familyLaw_incidence X Y i j (fun a y=>a.rep y.rep=0)

variable {Ω : Type*} [Fintype Ω]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma firstTargetDensity_mean (μ : Law Ω) (a : Ω→Projectivization K (Module.Dual K V))
    (G : Finset (Projectivization K (Module.Dual K V))) (T : Finset (Projectivization K V)) :
    (∑ ω,μ.mass ω*firstTargetDensity (a ω∈G) (a ω) T)=
      pairing (fun y=>if y∈G then (μ.map a).mass y else 0) (kernel T)
        (fun y x=>if y.rep x.rep=0 then 1 else 0) := by
  rw [←μ.sum_map a (fun y=>firstTargetDensity (y∈G) y T)]
  unfold pairing firstTargetDensity
  apply sum_congr rfl
  intro y _
  by_cases hy : y∈G <;> simp [hy,mul_sum]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma secondTargetDensity_mean (μ : Law Ω) (c : Ω→Projectivization K V)
    (G : Finset (Projectivization K V)) (S : Finset (Projectivization K (Module.Dual K V))) :
    (∑ ω,μ.mass ω*secondTargetDensity (c ω∈G) (c ω) S)=
      pairing (kernel S) (fun x=>if x∈G then (μ.map c).mass x else 0)
        (fun y x=>if y.rep x.rep=0 then 1 else 0) := by
  rw [←μ.sum_map c (fun x=>secondTargetDensity (x∈G) x S),pairing_reverse]
  unfold pairing secondTargetDensity
  apply sum_congr rfl
  intro x _
  by_cases hx : x∈G <;> simp [hx,mul_sum]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem originalFamily_first_target {n : ℕ} {b : ℝ} (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (μ : Law Ω) (a : Ω→Projectivization K (Module.Dual K V))
    (G : Finset (Projectivization K (Module.Dual K V))) (j : I) :
    (∑ z,(μ.prod (familyLaw X Y).nullFree).mass z *
      firstTargetDensity (a z.1∈G) (a z.1) (originalFamily X Y hMA hMB hprod z.2 j).A)≤
      (4*exp 1)*((μ.map a).prod (r j)).event
        (univ.filter (fun ay=>ay.1∈G ∧ ay.2∈goodB j ∧ ay.1.rep ay.2.rep=0)) := by
  change (∑ z,(μ.prod (familyLaw X Y).nullFree).mass z *
    firstTargetDensity (a z.1∈G) (a z.1) (z.2.val.2 j))≤_
  rw [μ.prod_sum_swap (familyLaw X Y).nullFree
    (fun ω z=>firstTargetDensity (a ω∈G) (a ω) (z.val.2 j))]
  simp_rw [firstTargetDensity_mean]
  rw [(familyLaw X Y).nullFree_integral (fun z=>pairing
    (fun y=>if y∈G then (μ.map a).mass y else 0) (kernel (z.2 j))
    (fun y x=>if y.rep x.rep=0 then 1 else 0))]
  simp_rw [pairing_reverse (fun y=>if y∈G then (μ.map a).mass y else 0)]
  have hh := familyLaw_second_target (μ.map a) G X Y j (fun y x=>x.rep y.rep=0)
  have he : ((r j).prod (μ.map a)).event
      (univ.filter (fun yx=>yx.1∈goodB j ∧ yx.2∈G ∧ yx.2.rep yx.1.rep=0))=
      ((μ.map a).prod (r j)).event
      (univ.filter (fun xy=>xy.1∈G ∧ xy.2∈goodB j ∧ xy.1.rep xy.2.rep=0)) := by
    rw [←good_pairing_eq_event (r j) (μ.map a) (goodB j) G (fun y x=>x.rep y.rep=0),
      ←good_pairing_eq_event (μ.map a) (r j) G (goodB j) (fun x y=>x.rep y.rep=0)]
    exact pairing_reverse _ _ _
  rw [he] at hh
  exact hh

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem originalFamily_second_target {n : ℕ} {b : ℝ} (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (μ : Law Ω) (c : Ω→Projectivization K V) (G : Finset (Projectivization K V)) (i : I) :
    (∑ z,(μ.prod (familyLaw X Y).nullFree).mass z *
      secondTargetDensity (c z.1∈G) (c z.1) (originalFamily X Y hMA hMB hprod z.2 i).B)≤
      (4*exp 1)*((p i).prod (μ.map c)).event
        (univ.filter (fun ay=>ay.1∈goodA i ∧ ay.2∈G ∧ ay.1.rep ay.2.rep=0)) := by
  change (∑ z,(μ.prod (familyLaw X Y).nullFree).mass z *
    secondTargetDensity (c z.1∈G) (c z.1) (z.2.val.1 i))≤_
  rw [μ.prod_sum_swap (familyLaw X Y).nullFree
    (fun ω z=>secondTargetDensity (c ω∈G) (c ω) (z.val.1 i))]
  simp_rw [secondTargetDensity_mean]
  rw [(familyLaw X Y).nullFree_integral (fun z=>pairing (kernel (z.1 i))
    (fun x=>if x∈G then (μ.map c).mass x else 0)
    (fun y x=>if y.rep x.rep=0 then 1 else 0))]
  exact familyLaw_first_target (μ.map c) G X Y i (fun y x=>y.rep x.rep=0)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence SupportMixtures Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [Fintype Ω]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}

variable (X : ∀ i,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))
  {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
  (hτ : 0<τ) (hτsmall : τ≤1/40000)
  (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
  (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
    (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.reciprocalBanksFintype
theorem Book.original_tree_target_loss
    (μ : Law Ω) (target : I) (t : BinaryTree I) (ht : Separated t) (hmem : target∈labels t)
    (a : Ω→Projectivization K (Module.Dual K V)) (c : Ω→Projectivization K V)
    (GA : Finset (Projectivization K (Module.Dual K V))) (GB : Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈plannedPath target t,∀ j∈leftPath i t,
      goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hsecond : ∀ i∈plannedPath target t,∀ j∈rightPath i t,
      goodIncidence (p j) (r i) (goodA j) (goodB i)≤ε)
    (hself : ∀ i∈plannedPath target t,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈insert target (leftPath target t),
      goodIncidence (μ.map a) (r i) GA (goodB i)≤εA)
    (hmeanB : ∀ i∈insert target (rightPath target t),
      goodIncidence (p i) (μ.map c) (goodA i) GB≤εB)
    (hbadA : (∑ ω,μ.mass ω*(if a ω∈GA then (0:ℝ) else 1))≤δA)
    (hbadB : (∑ ω,μ.mass ω*(if c ω∈GB then (0:ℝ) else 1))≤δB) :
    (∑ ω,(μ.prod (familyLaw X Y).nullFree).mass ω *
      (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z *
        targetFailure
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (originalFamily X Y hMA hMB hprod ω.2 i))
          (fun _=>chronoRead b) (a ω.1) (c ω.1) target t (univ,univ) z))≤
      20*(12*(Nat.card K:ℝ)*((4*exp 1)*(4*exp 1)*ε))*t.height^2+
        ((Nat.card K:ℝ)*((4*exp 1)*(4*exp 1)*ε)/τ+2*exp (-(Nat.card K:ℝ)))*t.height+
        δA+δB+((t.height:ℝ)+1)*
          (12*(Nat.card K:ℝ)*((4*exp 1)*εA)+12*(Nat.card K:ℝ)*((4*exp 1)*εB)) := by
  let ν := μ.prod (familyLaw X Y).nullFree
  have hdc (i j : I) :
      (∑ ω,ν.mass ω * density (originalFamily X Y hMA hMB hprod ω.2 i).B
        (originalFamily X Y hMA hMB hprod ω.2 j).A)≤
      (4*exp 1)*(4*exp 1)*goodIncidence (p i) (r j) (goodA i) (goodB j) := by
    rw [show (∑ ω,ν.mass ω * density (originalFamily X Y hMA hMB hprod ω.2 i).B
        (originalFamily X Y hMA hMB hprod ω.2 j).A)=
      ∑ z,(familyLaw X Y).nullFree.mass z * density (originalFamily X Y hMA hMB hprod z i).B
        (originalFamily X Y hMA hMB hprod z j).A from
      μ.prod_right_sum (familyLaw X Y).nullFree
        (fun z=>density (originalFamily X Y hMA hMB hprod z i).B
          (originalFamily X Y hMA hMB hprod z j).A)]
    exact originalFamily_density X Y hMA hMB hprod i j
  exact book.target_loss hdim hτ.le hτsmall ν.asPublic
    (fun ω i=>originalFamily X Y hMA hMB hprod ω.2 i) target t (univ,univ) ht hmem
    (by intros; exact ⟨subset_univ _,subset_univ _⟩)
    (fun ω=>a ω.1∈GA) (fun ω=>c ω.1∈GB) (fun ω=>a ω.1) (fun ω=>c ω.1)
    (by simp) (by simp) hτ ((4*exp 1)*(4*exp 1)*ε) ((4*exp 1)*εA) ((4*exp 1)*εB)
    δA δB (by positivity) (by positivity) (by positivity)
    (fun i hi j hj=>(hdc i j).trans (mul_le_mul_of_nonneg_left (hfirst i hi j hj) (by positivity)))
    (fun i hi j hj=>(hdc j i).trans (mul_le_mul_of_nonneg_left (hsecond i hi j hj) (by positivity)))
    (fun i hi=>(hdc i i).trans (mul_le_mul_of_nonneg_left (hself i hi) (by positivity)))
    (fun i hi=>(originalFamily_first_target X Y hMA hMB hprod μ a GA i).trans
      (mul_le_mul_of_nonneg_left (hmeanA i hi) (by positivity)))
    (fun i hi=>(originalFamily_second_target X Y hMA hMB hprod μ c GB i).trans
      (mul_le_mul_of_nonneg_left (hmeanB i hi) (by positivity)))
    (by
      have hh := (μ.prod_left_sum (familyLaw X Y).nullFree
        (fun ω=>if a ω∈GA then (0:ℝ) else 1)).le.trans hbadA
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext outcome
      congr 1
      by_cases hgood : a outcome.1∈GA <;> simp only [hgood,ite_true,ite_false])
    (by
      have hh := (μ.prod_left_sum (familyLaw X Y).nullFree
        (fun ω=>if c ω∈GB then (0:ℝ) else 1)).le.trans hbadB
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext outcome
      congr 1
      by_cases hgood : c outcome.1∈GB <;> simp only [hgood,ite_true,ite_false])

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence SupportMixtures Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [Fintype Ω]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.flat_ActualReciprocalPopulation_1
variable (X : ∀ i,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))
  {d : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=d+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
  (hτ : 0<τ) (hτsmall : τ≤1/40000)
  (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
  (hprod : ∀ i,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
    (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.populationBanksFintype
theorem Book.original_population_loss
    (μ : Law Ω) (n : I→ℕ)
    (target : Ω→∀ i,Fin (n i)→Projectivization K (Module.Dual K V)×Projectivization K V)
    (t : BinaryTree I) (ht : Separated t)
    (hR : ∀ ω,∀ i∈labels t,∀ j,SharpLogRamsey.Incidence.Incident (target ω i j).2 (target ω i j).1)
    (GA : ∀ i,Fin (n i)→Finset (Projectivization K (Module.Dual K V)))
    (GB : ∀ i,Fin (n i)→Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈labels t,∀ j∈leftPath i t,
      goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hsecond : ∀ i∈labels t,∀ j∈rightPath i t,
      goodIncidence (p j) (r i) (goodA j) (goodB i)≤ε)
    (hself : ∀ i∈labels t,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈labels t,∀ j,∀ k∈insert i (leftPath i t),
      goodIncidence (μ.map (fun ω=>(target ω i j).1)) (r k) (GA i j) (goodB k)≤εA)
    (hmeanB : ∀ i∈labels t,∀ j,∀ k∈insert i (rightPath i t),
      goodIncidence (p k) (μ.map (fun ω=>(target ω i j).2)) (goodA k) (GB i j)≤εB)
    (hbadA : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*(if (target ω i j).1∈GA i j then (0:ℝ) else 1))≤δA)
    (hbadB : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*(if (target ω i j).2∈GB i j then (0:ℝ) else 1))≤δB) :
    (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z *
      ∑ ω,(μ.prod (familyLaw X Y).nullFree).mass ω*((∑ i∈labels t,(n i:ℝ))-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ.le hτsmall (originalFamily X Y hMA hMB hprod ω.2 i))
        (fun _=>chronoRead b) (fun i=>List.ofFn (target ω.1 i)) z t (univ,univ)).length))≤
        (∑ i∈labels t,(n i:ℝ))*treeError (Nat.card K) τ t.height ε εA εB δA δB := by
  apply original_variable_loss (μ.prod (familyLaw X Y).nullFree).asPublic
    (fun _ : I=>banksLaw (K:=K) (V:=V) b) (fun y x=>SharpLogRamsey.Incidence.Incident x y)
    (fun ω i=>book.chronoChoose hdim hτ.le hτsmall (originalFamily X Y hMA hMB hprod ω.2 i))
    (fun _=>chronoRead b) n (fun ω=>target ω.1) t (univ,univ) ht (fun ω=>hR ω.1)
  intro i hi j
  apply book.original_tree_target_loss X Y hdim hτ hτsmall hMA hMB hprod
    μ i t ht hi (fun ω=>(target ω i j).1) (fun ω=>(target ω i j).2)
    (GA i j) (GB i j) ε εA εB δA δB hε hεA hεB
  · intro k hk l hl
    exact hfirst k (plannedPath_subset i t hk) l hl
  · intro k hk l hl
    exact hsecond k (plannedPath_subset i t hk) l hl
  · intro k hk
    exact hself k (plannedPath_subset i t hk)
  · exact hmeanA i hi j
  · exact hmeanB i hi j
  · exact hbadA i hi j
  · exact hbadB i hi j

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_BalancedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree
open BinaryTree Finset FreshExecution
open scoped Classical
noncomputable section

lemma balanced_inorder (lo n : ℕ) : inorder (balanced lo n)=List.range' lo n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rw [balanced]
    split_ifs with hn
    · simp [hn,inorder]
    · simp only [inorder]
      rw [ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)),
        ih (n-n/2-1) (by omega)]
      rw [←List.range'_succ, List.range'_append_1]
      congr 1
      have : n/2<n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      omega

lemma inorder_map {A B : Type*} (f : A→B) (t : BinaryTree A) :
    inorder (t.map f)=(inorder t).map f := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [BinaryTree.map,inorder,hl,hr]

lemma map_range_getD {A : Type*} (l : List A) (a : A) :
    (List.range l.length).map (fun i=>l.getD i a)=l := by
  apply List.ext_getElem
  · simp
  · intro i hi ho
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem l a ho

variable {I : Type*} [LinearOrder I]

attribute [local instance] OAI.SharpLogRamsey.ChronologicalTree.liveEq
lemma liveTree_inorder (S : Finset I) (fallback : I) :
    inorder (liveTree S fallback)=S.sort (·≤·) := by
  rw [liveTree,inorder_map,balanced_inorder,←List.range_eq_range']
  simpa only [length_sort] using map_range_getD (S.sort (·≤·)) fallback

lemma liveTree_labels (S : Finset I) (fallback : I) : labels (liveTree S fallback)=S := by
  rw [labels,liveTree_inorder]
  exact sort_toFinset _ _

lemma liveTree_nodup (S : Finset I) (fallback : I) :
    (inorder (liveTree S fallback)).Nodup := by
  rw [liveTree_inorder]
  exact sort_nodup _ _

lemma liveTree_separated (S : Finset I) (fallback : I) : Separated (liveTree S fallback) :=
  separated_of_nodup _ (liveTree_nodup S fallback)

lemma ordered_leftPath (t : BinaryTree I) (ht : (inorder t).Pairwise (·<·))
    (target i : I) (hi : i∈leftPath target t) : target < i := by
  induction t with
  | nil => simp [leftPath] at hi
  | node a l r hl hr =>
    simp only [inorder,List.pairwise_append,List.pairwise_cons] at ht
    rw [leftPath] at hi
    split_ifs at hi with ha hL
    · simp at hi
    · rcases mem_insert.mp hi with rfl|hi
      · exact ht.2.2 target (by simpa only [labels,List.mem_toFinset] using hL) i (List.mem_cons_self ..)
      · exact hl ht.1 hi
    · exact hr ht.2.1.2 hi

lemma ordered_rightPath (t : BinaryTree I) (ht : (inorder t).Pairwise (·<·))
    (target i : I) (hi : i∈rightPath target t) : i < target := by
  induction t with
  | nil => simp [rightPath] at hi
  | node a l r hl hr =>
    simp only [inorder,List.pairwise_append,List.pairwise_cons] at ht
    rw [rightPath] at hi
    split_ifs at hi with ha hR
    · simp at hi
    · rcases mem_insert.mp hi with rfl|hi
      · exact ht.2.1.1 target (by simpa only [labels,List.mem_toFinset] using hR)
      · exact hr ht.2.1.2 hi
    · exact hl ht.1 hi

lemma liveTree_ordered (S : Finset I) (fallback : I) :
    (inorder (liveTree S fallback)).Pairwise (·<·) := by
  rw [liveTree_inorder]
  exact S.sortedLT_sort.pairwise

lemma liveTree_left (S : Finset I) (fallback target i : I)
    (hi : i∈leftPath target (liveTree S fallback)) : target < i :=
  ordered_leftPath _ (liveTree_ordered S fallback) target i hi

lemma liveTree_right (S : Finset I) (fallback target i : I)
    (hi : i∈rightPath target (liveTree S fallback)) : i < target :=
  ordered_rightPath _ (liveTree_ordered S fallback) target i hi

end
end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_LiveFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {I : Type*} [Fintype I] [LinearOrder I]

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.liveDecEq
omit [Fintype I] [LinearOrder I] in
lemma liveRetraction_mem (S : Finset I) (h : S.Nonempty) (i : I) (hi : i∈S) :
    (liveRetraction S h i).val=i := by simp [liveRetraction,hi]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {Ω : Type*} [Fintype Ω]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}

variable (S : Finset I) (hS : S.Nonempty)
  (X : ∀ i : S,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i : S,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))

variable {d : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=d+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
  (hτ : 0<τ) (hτsmall : τ≤1/40000)
  (hMA : ∀ i∈S,0<MA i) (hMB : ∀ i∈S,0<MB i)
  (hprod : ∀ i∈S,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
    (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.liveBanksFintype
theorem Book.live_population_loss
    (μ : Law Ω) (counts : I→ℕ)
    (target : Ω→∀ i,Fin (counts i)→Projectivization K (Module.Dual K V)×Projectivization K V)
    (fallback : I)
    (hR : ∀ ω,∀ i∈S,∀ j,SharpLogRamsey.Incidence.Incident (target ω i j).2 (target ω i j).1)
    (GA : ∀ i,Fin (counts i)→Finset (Projectivization K (Module.Dual K V)))
    (GB : ∀ i,Fin (counts i)→Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈S,∀ j∈S,i < j → goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hself : ∀ i∈S,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈S,∀ j,∀ k∈S,i ≤ k →
      goodIncidence (μ.map (fun ω=>(target ω i j).1)) (r k) (GA i j) (goodB k)≤εA)
    (hmeanB : ∀ i∈S,∀ j,∀ k∈S,k ≤ i →
      goodIncidence (p k) (μ.map (fun ω=>(target ω i j).2)) (goodA k) (GB i j)≤εB)
    (hbadA : ∀ i∈S,∀ j,(∑ ω,μ.mass ω*(if (target ω i j).1∈GA i j then (0:ℝ) else 1))≤δA)
    (hbadB : ∀ i∈S,∀ j,(∑ ω,μ.mass ω*(if (target ω i j).2∈GB i j then (0:ℝ) else 1))≤δB) :
    (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z *
      ∑ ω,(μ.prod (familyLaw (liveX S hS X) (liveY S hS Y)).nullFree).mass ω*
      ((∑ i∈S,(counts i:ℝ))-
       (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ.le hτsmall (liveOriginal S hS X Y hMA hMB hprod ω.2 i))
        (fun _=>chronoRead b) (fun i=>List.ofFn (target ω.1 i)) z (liveTree S fallback) (univ,univ)).length))≤
      (∑ i∈S,(counts i:ℝ))*treeError (Nat.card K) τ (liveTree S fallback).height ε εA εB δA δB := by
  have hsubL (i j : I) (hj : j∈leftPath i (liveTree S fallback)) : j∈S := by
    rw [←liveTree_labels S fallback]
    exact leftPath_subset i _ hj
  have hsubR (i j : I) (hj : j∈rightPath i (liveTree S fallback)) : j∈S := by
    rw [←liveTree_labels S fallback]
    exact rightPath_subset i _ hj
  have hh := book.original_population_loss (liveX S hS X) (liveY S hS Y) hdim hτ hτsmall
    (fun i=>hMA _ (liveRetraction S hS i).property)
    (fun i=>hMB _ (liveRetraction S hS i).property)
    (fun i=>hprod _ (liveRetraction S hS i).property) μ counts target (liveTree S fallback)
    (liveTree_separated S fallback)
  simp only [liveTree_labels] at hh
  apply hh (fun ω=>hR ω) GA GB ε εA εB δA δB hε hεA hεB
  · intro i hi j hj
    simpa only [liveRetraction_mem S hS i hi,liveRetraction_mem S hS j (hsubL i j hj)] using
      hfirst i hi j (hsubL i j hj) (liveTree_left S fallback i j hj)
  · intro i hi j hj
    simpa only [liveRetraction_mem S hS i hi,liveRetraction_mem S hS j (hsubR i j hj)] using
      hfirst j (hsubR i j hj) i hi (liveTree_right S fallback i j hj)
  · intro i hi
    simpa only [liveRetraction_mem S hS i hi] using hself i hi
  · intro i hi j k hk
    rcases mem_insert.mp hk with hki|hk
    · subst k
      simpa only [liveRetraction_mem S hS i hi] using hmeanA i hi j i hi le_rfl
    · simpa only [liveRetraction_mem S hS k (hsubL i k hk)] using
        hmeanA i hi j k (hsubL i k hk) (liveTree_left S fallback i k hk).le
  · intro i hi j k hk
    rcases mem_insert.mp hk with hki|hk
    · subst k
      simpa only [liveRetraction_mem S hS i hi] using hmeanB i hi j i hi le_rfl
    · simpa only [liveRetraction_mem S hS k (hsubR i k hk)] using
        hmeanB i hi j k (hsubR i k hk) (liveTree_right S fallback i k hk).le
  · exact hbadA
  · exact hbadB

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_LiveRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.ChronologicalTree
open BinaryTree Finset
open scoped Classical
variable {I : Type*} [LinearOrder I]
lemma liveTree_empty (fallback : I) : liveTree ∅ fallback=nil := by
  simp [liveTree,balanced,BinaryTree.map]
end SharpLogRamsey.ChronologicalTree

namespace SharpLogRamsey.ActualPivot
open Finset Real Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {K V I Y₀ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype I] [LinearOrder I] [Fintype Y₀] {d : ℕ} {b τ P H : ℝ}

attribute [instance] Realization.inst

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.realDecEq
variable (hdim : Module.finrank K V=d+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
  (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)

include hb

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.realizationBanksFintype
theorem Book.live_realization_oai
    (q : Law Y₀) (S : Finset I) (fallback : I)
    (p : I→Law (Projectivization K (Module.Dual K V)))
    (r : I→Law (Projectivization K V))
    (goodA : I→Finset (Projectivization K (Module.Dual K V)))
    (goodB : I→Finset (Projectivization K V)) (MA MB κA κB : I→ℝ)
    (X : ∀ i : S,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ i : S,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))
    (hMA : ∀ i∈S,0<MA i) (hMB : ∀ i∈S,0<MB i)
    (hprod : ∀ i∈S,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (counts : I→ℕ)
    (target : Y₀→∀ i,Fin (counts i)→Projectivization K (Module.Dual K V)×Projectivization K V)
    (hR : ∀ y,q.mass y≠0→∀ i∈S,∀ j,SharpLogRamsey.Incidence.Incident (target y i j).2 (target y i j).1)
    (GA : ∀ i,Fin (counts i)→Finset (Projectivization K (Module.Dual K V)))
    (GB : ∀ i,Fin (counts i)→Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈S,∀ j∈S,i < j → goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hself : ∀ i∈S,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈S,∀ j,∀ k∈S,i ≤ k →
      goodIncidence (q.map (fun y=>(target y i j).1)) (r k) (GA i j) (goodB k)≤εA)
    (hmeanB : ∀ i∈S,∀ j,∀ k∈S,k ≤ i →
      goodIncidence (p k) (q.map (fun y=>(target y i j).2)) (goodA k) (GB i j)≤εB)
    (hbadA : ∀ i∈S,∀ j,(∑ y,q.mass y*(if (target y i j).1∈GA i j then (0:ℝ) else 1))≤δA)
    (hbadB : ∀ i∈S,∀ j,(∑ y,q.mass y*(if (target y i j).2∈GB i j then (0:ℝ) else 1))≤δB) :
    ∃ e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q,
      (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
        ∑ ω,e.μ.mass ω*((∑ i∈S,(counts i:ℝ))-
        (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
          (fun _=>chronoRead b) (fun i=>List.ofFn (target (e.source ω) i)) z
          (liveTree S fallback) (univ,univ)).length))≤
        (∑ i∈S,(counts i:ℝ))*treeError (Nat.card K) τ (liveTree S fallback).height ε εA εB δA δB := by
  by_cases hS : S.Nonempty
  · let e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q :=
      { Ω := {y // q.mass y≠0} × OriginalChoice (liveX S hS X) (liveY S hS Y)
        inst := inferInstance
        μ := q.nullFree.prod (familyLaw (liveX S hS X) (liveY S hS Y)).nullFree
        source := fun ω=>ω.1.val
        supports := fun ω=>liveOriginal S hS X Y hMA hMB hprod ω.2
        marginal := by
          rw [Law.prod_map_left]
          exact (q.nullFree_map id).trans (Law.map_id q) }
    refine ⟨e,?_⟩
    apply book.live_population_loss S hS X Y hdim hτ hτsmall hMA hMB hprod q.nullFree counts
      (fun y=>target y.val) fallback (fun y=>hR y.val y.property) GA GB ε εA εB δA δB hε hεA hεB
      hfirst hself
    · intro i hi j k hk hik
      rw [q.nullFree_map (fun y=>(target y i j).1)]
      exact hmeanA i hi j k hk hik
    · intro i hi j k hk hki
      rw [q.nullFree_map (fun y=>(target y i j).2)]
      exact hmeanB i hi j k hk hki
    · intro i hi j
      rw [q.nullFree_integral (fun y=>if (target y i j).1∈GA i j then (0:ℝ) else 1)]
      exact hbadA i hi j
    · intro i hi j
      rw [q.nullFree_integral (fun y=>if (target y i j).2∈GB i j then (0:ℝ) else 1)]
      exact hbadB i hi j
  · have hS' : S=∅ := not_nonempty_iff_eq_empty.mp hS
    let e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q :=
      { Ω := Y₀
        inst := inferInstance
        μ := q
        source := id
        supports := fun _ _=>emptyOriginal hdim hb
        marginal := Law.map_id q }
    refine ⟨e,?_⟩
    simp [hS',liveTree_empty,fullOutput_nil]
end
end SharpLogRamsey.ActualPivot

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.ActualPivot.Book.live_realization_oai := @OAI.SharpLogRamsey.ActualPivot.Book.live_realization_oai
