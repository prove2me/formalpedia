-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.MachineCode.output_certificate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:35:32.47409+00:00
-- url     : https://prove2.me/submissions/44d7d885-f0ba-4e0b-a5f9-4a1f0af32be5

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_OAIQ2Mt000

section
-- module Solutions.OAIQ2_Mat.MatroidCounting_CommonBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

open Set

section PairedReduction
variable {α β : Type*}

lemma sum_eRank (M : Matroid α) (N : Matroid β) :
    (M.sum N).eRank = M.eRank + N.eRank := by
  obtain ⟨B,hB⟩ := M.exists_isBase
  obtain ⟨C,hC⟩ := N.exists_isBase
  have hBC : (M.sum N).IsBase (Sum.inl '' B ∪ Sum.inr '' C) := by
    rw [Matroid.sum_isBase_iff]
    simpa [Set.preimage_image_eq _ Sum.inl_injective,
      Set.preimage_image_eq _ Sum.inr_injective] using And.intro hB hC
  rw [← hBC.encard_eq_eRank, Set.encard_union_eq,
    Set.InjOn.encard_image, Set.InjOn.encard_image,
    hB.encard_eq_eRank, hC.encard_eq_eRank]
  · exact Sum.inr_injective.injOn
  · exact Sum.inl_injective.injOn
  · exact Set.disjoint_image_inl_image_inr

lemma transversal_isBase_iff (M₁ M₂ : Matroid α) (h₂ : M₂.E = Set.univ)
    (A : Set α) :
    (pairedMatroid M₁ M₂).IsBase (transversal A) ↔ M₁.IsBase A ∧ M₂.IsBase A := by
  simp only [pairedMatroid, Matroid.sum_isBase_iff, preimage_inl_transversal,
    preimage_inr_transversal, Matroid.dual_isBase_iff', h₂,
    ← Set.compl_eq_univ_sdiff, compl_compl, Set.subset_univ, and_true]

lemma paired_eRank [Fintype α] (M₁ M₂ : Matroid α) (h₂ : M₂.E = Set.univ)
    (hr : M₁.eRank = M₂.eRank) :
    (pairedMatroid M₁ M₂).eRank = (Fintype.card α : ℕ∞) := by
  rw [pairedMatroid, sum_eRank,hr, M₂.eRank_add_eRank_dual,h₂,
    Set.encard_univ, ENat.card_eq_coe_fintype_card]

lemma transversal_encard [Fintype α] (A : Set α) :
    (transversal A).encard = (Fintype.card α : ℕ∞) := by
  rw [transversal, Set.encard_union_eq,
    Set.InjOn.encard_image, Set.InjOn.encard_image,
    ← Set.encard_union_eq disjoint_compl_right, union_compl_self, Set.encard_univ,
    ENat.card_eq_coe_fintype_card]
  · exact Sum.inr_injective.injOn
  · exact Sum.inl_injective.injOn
  · exact Set.disjoint_image_inl_image_inr

end PairedReduction

open scoped BigOperators Classical

open scoped BigOperators Classical
lemma subsetDeficiency_zero {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (A : Set (Fin n)) :
    subsetDeficiency M₁ M₂ A=0 ↔ M₁.IsBase A ∧ M₂.IsBase A := by
  have hR : (pairedMatroid M₁ M₂).eRank=(n:ℕ∞) := by simpa using paired_eRank M₁ M₂ hE₂ hr
  have hk : ((pairedMatroid M₁ M₂).eRk (transversal A)).toNat≤n :=
    ENat.toNat_le_of_le_natCast (by rw [← hR]; exact Matroid.eRk_le_eRank _ _)
  rw [← transversal_isBase_iff M₁ M₂ hE₂ A]
  constructor
  · intro hd
    have hn : ((pairedMatroid M₁ M₂).eRk (transversal A)).toNat=n := by unfold subsetDeficiency at hd; omega
    have he : (pairedMatroid M₁ M₂).eRk (transversal A)=(n:ℕ∞) := by
      calc
        _ = (((pairedMatroid M₁ M₂).eRk (transversal A)).toNat:ℕ∞) :=
          (ENat.natCast_toNat (Matroid.isRkFinite_set _ _).eRk_lt_top.ne).symm
        _ = _ := congrArg (fun k : ℕ => (k:ℕ∞)) hn
    have hi : (pairedMatroid M₁ M₂).Indep (transversal A) := by
      apply (Matroid.indep_iff_eRk_eq_encard_of_finite (Set.toFinite _)).mpr
      rw [he,transversal_encard,Fintype.card_fin]
    exact hi.isBase_of_eRk_ge (Set.toFinite _) (by rw [he,hR])
  · intro h
    unfold subsetDeficiency
    rw [h.eRk_eq_eRank,hR,ENat.toNat_natCast,Nat.sub_self]

open scoped BigOperators Classical
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance101 : Fintype X]
universe u

omit sectionInstance101 in
lemma Sample.toList_length [Fintype X] {k : ℕ} (v : Sample X k) : v.toList.length=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ (ih v.2)
end FiniteChain
section ActualHistoryEstimate
open scoped BigOperators Classical
variable (n : ℕ) (N L : ℕ) (M : Matroid (Fin n ⊕ Fin n))
lemma empirical_nonneg {Γ : Type*} (H : Set Γ → ℝ) (hH : ∀ S,0 ≤ H S) (l : List (Set Γ)) :
    0 ≤ empirical H l := by
  unfold empirical
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact List.sum_nonneg (fun x hx => by obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hx; exact hH S)
lemma empiricalRatio_nonneg {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (gs : List (Γ × Γ)) (g : Set Γ → ℝ) (hg : ∀ S,0 ≤ g S) (l : List (Set Γ)) :
    0 ≤ empiricalRatio gs g l := by
  unfold empiricalRatio
  apply div_nonneg
  · apply empirical_nonneg; intro S; unfold plainObservable; split_ifs; exact hg S; rfl
  · apply empirical_nonneg; intro S; unfold plainObservable; split_ifs <;> norm_num
lemma historyEstimate_nonneg (hn : 0<n) (h : List (PhaseSample n N)) :
    0 ≤ historyEstimate n N L M h := by
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j _
  exact empiricalRatio_nonneg _ _ (fun S => pow_nonneg (le_trans (by norm_num) (annealRho_bounds n hn).1) _) _
end ActualHistoryEstimate
section WitnessRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n))
local notation "GS" => pairedSlots n
lemma witnessed_iff_common_base (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (x : PlainIndex GS) :
    Witnessed n M₁ M₂ x ↔ M₁.IsBase (Sum.inl ⁻¹' x.val.val) ∧ M₂.IsBase (Sum.inl ⁻¹' x.val.val) := by
  unfold Witnessed
  rw [plain_eq_transversal n x.val.val x.property]
  simpa only [preimage_inl_transversal,subsetDeficiency] using subsetDeficiency_zero M₁ M₂ hE₂ hr (Sum.inl ⁻¹' x.val.val)
lemma witnessed_count_pos (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank) (x : PlainIndex GS)
    (hx : Witnessed n M₁ M₂ x) : 0<commonBaseCount M₁ M₂ := by
  obtain ⟨h₁,h₂⟩ := (witnessed_iff_common_base n M₁ M₂ hE₂ hr x).mp hx
  unfold commonBaseCount
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨(Sum.inl ⁻¹' x.val.val).toFinset,by simpa using And.intro h₁ h₂⟩⟩
end WitnessRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
include hn in
lemma guardedEstimate_nonneg (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    0 ≤ guardedEstimate n M₁ M₂ N L h x := by
  unfold guardedEstimate
  split_ifs
  · exact historyEstimate_nonneg n N L K hn h
  · rfl
lemma guardedEstimate_zero (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (hZ : commonBaseCount M₁ M₂=0) (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    guardedEstimate n M₁ M₂ N L h x=0 := by
  unfold guardedEstimate
  apply ite_eq_right
  intro hx
  have hp := witnessed_count_pos n M₁ M₂ hE₂ hr x hx
  omega

end

section

open scoped BigOperators Classical
lemma uniformAverage_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformAverage (fun x => f (e x))=uniformAverage f := by
  rw [uniformAverage,uniformAverage,e.sum_comp,Fintype.card_congr e]
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
lemma uniformAverage_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    uniformAverage (fun x => f x+g x)=uniformAverage f+uniformAverage g := by
  simp [uniformAverage,Finset.sum_add_distrib,add_div]
lemma uniformAverage_mul_left {X : Type*} [Fintype X] (r : ℝ) (f : X → ℝ) :
    uniformAverage (fun x => r*f x)=r*uniformAverage f := by
  simp [uniformAverage,← Finset.mul_sum,mul_div_assoc]
lemma uniformAverage_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun y => f (x,y))) := by
  simp only [uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← Finset.sum_div]
  ring
lemma uniformAverage_fin_succ {X : Type*} [Fintype X] (D : ℕ)
    (f : (Fin (D+1) → X) → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun rest => f (Fin.cons x rest))) := by
  rw [← uniformAverage_equiv (Fin.consEquiv (fun _ : Fin (D+1) => X)) f,uniformAverage_prod]
  rfl

lemma acceptedCard (v T : ℕ) (hv : v≤T) :
    Fintype.card {x : Fin T // x.val < v}=v := by
  let e : {x : Fin T // x.val < v} ≃ Fin v :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hv⟩,x.isLt⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  simpa using Fintype.card_congr e
lemma rejectedCard (v T : ℕ) (hv : v≤T) :
    Fintype.card {x : Fin T // ¬x.val < v}=T-v := by
  rw [Fintype.card_subtype_compl,acceptedCard v T hv,Fintype.card_fin]
lemma sum_ite_count {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] (r : ℝ) :
    (∑ x,if p x then r else 0)=(Fintype.card {x // p x}:ℝ)*r := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  congr 1
  exact_mod_cast (Fintype.card_subtype p).symm
lemma one_trial_none (v h : ℕ) (hv : v≤2^h) (r : ℝ) :
    uniformAverage (fun bits : BitWord h => if (wordEquiv h bits).val < v then 0 else r)=
      rejectionRate v h*r := by
  rw [uniformAverage_equiv (wordEquiv h) (fun x => if x.val<v then 0 else r)]
  unfold uniformAverage rejectionRate
  have he : (∑ x : Fin (2^h),if x.val<v then (0:ℝ) else r)=(2^h-v:ℕ)*r := by
    calc
      _ = ∑ x : Fin (2^h),if ¬x.val<v then r else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x.val<v <;> simp [hx]
      _ = _ := by rw [sum_ite_count,rejectedCard _ _ hv]
  rw [he,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  ring
lemma one_trial_some (v h : ℕ) (hv : v≤2^h) (a : Fin v) (r : ℝ) :
    uniformAverage (fun bits : BitWord h =>
      if hx : (wordEquiv h bits).val<v then
        (if (⟨(wordEquiv h bits).val,hx⟩ : Fin v)=a then (1:ℝ) else 0)
      else r) = 1/(2:ℝ)^h+rejectionRate v h*r := by
  let aT : Fin (2^h) := ⟨a.val,lt_of_lt_of_le a.isLt hv⟩
  have he : (fun bits : BitWord h =>
      if hx : (wordEquiv h bits).val<v then
        (if (⟨(wordEquiv h bits).val,hx⟩ : Fin v)=a then (1:ℝ) else 0)
      else r) = fun bits => (if wordEquiv h bits=aT then 1 else 0)+
        (if (wordEquiv h bits).val<v then 0 else r) := by
    funext bits
    by_cases hx : (wordEquiv h bits).val<v
    · have he : (⟨(wordEquiv h bits).val,hx⟩ : Fin v)=a ↔ wordEquiv h bits=aT := by
        simp only [Fin.ext_iff,aT]
      simp [hx,he]
    · have he : wordEquiv h bits≠aT := by
        intro hh
        have ht : (wordEquiv h bits).val=a.val := congrArg Fin.val hh
        exact hx (ht ▸ a.isLt)
      simp [hx,he]
  rw [he,uniformAverage_add,one_trial_none v h hv r]
  congr 1
  rw [uniformAverage_equiv (wordEquiv h) (fun x => if x=aT then 1 else 0)]
  simp [uniformAverage,aT]
lemma boundedUniform_failure (v h D : ℕ) (hv : v≤2^h) :
    uniformAverage (fun bits => if boundedUniform v h D bits=none then (1:ℝ) else 0)=
      rejectionRate v h^D := by
  induction D with
  | zero => simp [boundedUniform,uniformAverage_const]
  | succ D ih =>
    rw [uniformAverage_fin_succ]
    have he : (fun x : BitWord h => uniformAverage (fun rest : Fin D → BitWord h =>
        if boundedUniform v h (D+1) (Fin.cons x rest)=none then (1:ℝ) else 0)) =
        fun x => if (wordEquiv h x).val<v then 0 else rejectionRate v h^D := by
      funext x
      by_cases hx : (wordEquiv h x).val<v
      · simp only [boundedUniform,Fin.cons_zero,dite_eq_left hx,Option.some_ne_none,ite_false,ite_eq_left hx]
        try simp only [Fin.ext_iff]
        apply uniformAverage_const
      · simpa [boundedUniform,hx] using ih
    rw [he,one_trial_none v h hv,pow_succ']
lemma clog_trial_size (v : ℕ) (hv : 0<v) : v≤2^Nat.clog 2 v ∧ 2^Nat.clog 2 v≤2*v := by
  refine ⟨Nat.le_pow_clog (by norm_num) v,?_⟩
  by_cases h : v=1
  · subst v; norm_num
  have hv' : 1<v := by omega
  have hh := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hv'
  have hc := Nat.clog_pos (by norm_num : 1<2) hv'
  have hp : Nat.clog 2 v=(Nat.clog 2 v).pred+1 := by exact (Nat.succ_pred_eq_of_pos hc).symm
  rw [hp,pow_succ]
  omega
lemma boundedUniform_probability (v h D : ℕ) (hv : v ≤ 2^h) (hv0 : 0 < v) (a : Fin v) :
    uniformAverage (fun bits => if boundedUniform v h D bits=some a then (1:ℝ) else 0)=
      (1-rejectionRate v h^D)/(v:ℝ) := by
  have hv' : (v:ℝ)≠0 := by exact_mod_cast ne_of_gt hv0
  have hT : (2:ℝ)^h≠0 := by positivity
  induction D with
  | zero => simp [boundedUniform,uniformAverage_const]
  | succ D ih =>
    rw [uniformAverage_fin_succ]
    have he : (fun x : BitWord h => uniformAverage (fun rest : Fin D → BitWord h =>
        if boundedUniform v h (D+1) (Fin.cons x rest)=some a then (1:ℝ) else 0)) =
        fun x => if hx : (wordEquiv h x).val<v then
          (if (⟨(wordEquiv h x).val,hx⟩ : Fin v)=a then 1 else 0)
          else (1-rejectionRate v h^D)/(v:ℝ) := by
      funext x
      by_cases hx : (wordEquiv h x).val<v
      · simp only [boundedUniform,Fin.cons_zero,dite_eq_left hx,Option.some.injEq,]
        try simp only [Fin.ext_iff]
        apply uniformAverage_const
      · simpa [boundedUniform,hx] using ih
    rw [he,one_trial_some v h hv]
    have hr : rejectionRate v h=1-(v:ℝ)/(2:ℝ)^h := by
      unfold rejectionRate
      rw [Nat.cast_sub hv,Nat.cast_pow,Nat.cast_ofNat]
      field_simp
    rw [pow_succ]
    calc
      _ = ((v:ℝ)/(2:ℝ)^h+rejectionRate v h-rejectionRate v h^D*rejectionRate v h)/v := by
        field_simp ; ring
      _ = _ := by rw [hr]; ring
lemma uniformAverage_sum {X J : Type*} [Fintype X] [Fintype J] (f : J → X → ℝ) :
    uniformAverage (fun x => ∑ j,f j x)=∑ j,uniformAverage (f j) := by
  unfold uniformAverage
  rw [Finset.sum_comm,Finset.sum_div]

lemma boundedUniform_law (v h D : ℕ) (hv : v ≤ 2^h) (hv0 : 0 < v) (φ : Option (Fin v) → ℝ) :
    uniformAverage (fun bits => φ (boundedUniform v h D bits)) =
      rejectionRate v h^D*φ none + (1-rejectionRate v h^D)*uniformAverage (fun a => φ (some a)) := by
  have he : (fun bits => φ (boundedUniform v h D bits)) = fun bits =>
      φ none*(if boundedUniform v h D bits=none then 1 else 0) +
        ∑ a : Fin v,φ (some a)*(if boundedUniform v h D bits=some a then 1 else 0) := by
    funext bits
    cases e : boundedUniform v h D bits with
    | none => simp
    | some a => simp
  rw [he,uniformAverage_add,uniformAverage_mul_left,boundedUniform_failure v h D hv,
    uniformAverage_sum]
  simp_rw [uniformAverage_mul_left,boundedUniform_probability v h D hv hv0]
  rw [← Finset.sum_mul]
  unfold uniformAverage
  rw [Fintype.card_fin]
  ring

lemma uniformAverage_bitPrefix (h H : ℕ) (hh : h≤H) (φ : BitWord h → ℝ) :
    uniformAverage (fun w => φ (bitPrefix h H hh w))=uniformAverage φ := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hh
  rw [← uniformAverage_equiv (Fin.appendEquiv h t) (fun w => φ (bitPrefix h (h+t) hh w)),uniformAverage_prod]
  have he : ∀ a : BitWord h,∀ b : BitWord t,bitPrefix h (h+t) hh ((Fin.appendEquiv h t) (a,b))=a := by
    intro a b
    funext i
    change Fin.append a b (Fin.castAdd t i)=a i
    simp
  simp_rw [he,uniformAverage_const]
lemma uniformAverage_prefixTrials (h H D : ℕ) (hh : h≤H)
    (φ : (Fin D → BitWord h) → ℝ) :
    uniformAverage (fun w : Fin D → BitWord H => φ (fun d => bitPrefix h H hh (w d)))=uniformAverage φ := by
  induction D with
  | zero =>
    have he : ∀ w : Fin 0 → BitWord H,(fun d => bitPrefix h H hh (w d))=(fun d : Fin 0 => Fin.elim0 d) := by
      intro w; funext d; exact Fin.elim0 d
    have hf : ∀ w : Fin 0 → BitWord h,w=(fun d : Fin 0 => Fin.elim0 d) := by
      intro w; funext d; exact Fin.elim0 d
    simp_rw [he]
    rw [uniformAverage_const]
    conv_rhs => arg 1; ext w; rw [hf w]
    rw [uniformAverage_const]
  | succ D ih =>
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    have he : ∀ x : BitWord H,∀ xs : Fin D → BitWord H,
        (fun d : Fin (D+1) => bitPrefix h H hh ((Fin.cons x xs : Fin (D+1) → BitWord H) d))=
        Fin.cons (bitPrefix h H hh x) (fun d => bitPrefix h H hh (xs d)) := by
      intro x xs; funext d; refine Fin.cases ?_ (fun i => ?_) d <;> rfl
    simp_rw [he]
    have hhφ : ∀ x : BitWord H,
        uniformAverage (fun xs : Fin D → BitWord H => φ (Fin.cons (bitPrefix h H hh x) (fun d => bitPrefix h H hh (xs d))))=
        uniformAverage (fun xs : Fin D → BitWord h => φ (Fin.cons (bitPrefix h H hh x) xs)) := by
      intro x
      exact ih (fun xs => φ (Fin.cons (bitPrefix h H hh x) xs))
    simp_rw [hhφ]
    exact uniformAverage_bitPrefix h H hh (fun x => uniformAverage (fun xs => φ (Fin.cons x xs)))

namespace DrawTree

section
open scoped BigOperators Classical
variable {A : Type*}
lemma run_draw_average (H D M v : ℕ) (k : Fin (v+1) → DrawTree A)
    (hh : Nat.clog 2 (v+1)≤H) (φ : A → ℝ) :
    uniformAverage (fun bits => optionValue φ (run H D (M+1) (.draw v k) bits))=
      (1-rejectionRate (v+1) (Nat.clog 2 (v+1))^D)*
        uniformAverage (fun a : Fin (v+1) => uniformAverage
          (fun rest => optionValue φ (run H D M (k a) rest))) := by
  rw [uniformAverage_fin_succ]
  simp only [run,dite_eq_left hh,Fin.cons_zero,Fin.tail_cons]
  let ψ : Option (Fin (v+1)) → ℝ := fun z => match z with
    | none => 0
    | some a => uniformAverage (fun rest => optionValue φ (run H D M (k a) rest))
  have he : (fun x : Fin D → BitWord H => uniformAverage
      (fun rest : Fin M → Fin D → BitWord H => optionValue φ
        (match boundedUniform (v+1) (Nat.clog 2 (v+1)) D
          (fun d => bitPrefix _ H hh (x d)) with
         | none => none
         | some a => run H D M (k a) rest))) =
      fun x => ψ (boundedUniform (v+1) (Nat.clog 2 (v+1)) D
          (fun d => bitPrefix _ H hh (x d))) := by
    funext x
    cases hz : boundedUniform (v+1) (Nat.clog 2 (v+1)) D
      (fun d => bitPrefix _ H hh (x d)) with
    | none => exact uniformAverage_const 0
    | some a => rfl
  erw [he,uniformAverage_prefixTrials _ _ D hh (fun w => ψ (boundedUniform (v+1) (Nat.clog 2 (v+1)) D w))]
  rw [boundedUniform_law _ _ _ (clog_trial_size _ (by omega)).1 (by omega)]
  simp only [ψ,mul_zero,zero_add]

end
open scoped BigOperators Classical
variable {A B : Type*}
lemma fits_mono_steps (H M M' : ℕ) (hM : M≤M') (t : DrawTree A) (ht : Fits H M t) :
    Fits H M' t := by
  induction M generalizing M' t with
  | zero => cases t <;> simp_all [Fits]
  | succ M ih =>
    cases t with
    | leaf a => simp [Fits]
    | draw v f =>
      cases M' with
      | zero => omega
      | succ M' => exact ⟨ht.1,fun i => ih M' (by omega) (f i) (ht.2 i)⟩
lemma fits_bind (H M N : ℕ) (t : DrawTree A) (k : A → DrawTree B)
    (ht : Fits H M t) (hk : ∀ a,Fits H N (k a)) : Fits H (M+N) (t.bind k) := by
  induction M generalizing t with
  | zero => cases t with
    | leaf a => simpa only [bind,Nat.zero_add] using hk a
    | draw v f => exact False.elim ht
  | succ M ih =>
    cases t with
    | leaf a => exact fits_mono_steps H N (M+1+N) (by omega) (k a) (hk a)
    | draw v f =>
      have he : M+1+N=(M+N)+1 := by omega
      rw [he]
      exact ⟨ht.1,fun i => ih (f i) (ht.2 i)⟩

lemma rationalCoin_fits (a v H : ℕ) (hh : Nat.clog 2 (v+1)≤H) :
    Fits H 1 (rationalCoin a v) := ⟨hh,fun _ => trivial⟩
lemma bernoulli_fits (p : ℚ) (H : ℕ) (hh : Nat.clog 2 p.den≤H) :
    Fits H 1 (bernoulli p) := by
  unfold bernoulli
  apply rationalCoin_fits
  have hd : p.den-1+1=p.den := by have h := p.den_pos; omega
  simpa only [hd] using hh
end DrawTree

section RationalSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance112 : Fintype Γ] [sectionInstance113 : DecidableEq Γ]
omit sectionInstance112 sectionInstance113 in
lemma rationalEmpirical_cast [Fintype Γ] [DecidableEq Γ] (H : Set Γ → ℚ) (l : List (Set Γ)) :
    (rationalEmpirical H l:ℝ)=empirical (fun S => (H S:ℝ)) l := by
  simp [rationalEmpirical,empirical,Rat.cast_list_sum,List.map_map,Function.comp_def]
omit sectionInstance112 sectionInstance113 in
lemma rationalPlain_cast [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (S : Set Γ) :
    (rationalPlain gs g S:ℝ)=plainObservable gs (fun S => (g S:ℝ)) S := by
  unfold rationalPlain plainObservable; split_ifs <;> simp
omit sectionInstance112 sectionInstance113 in
lemma rationalDefect_cast [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) :
    (rationalDefect gs p r S:ℝ)=defectIndicator gs p r S := by
  unfold rationalDefect defectIndicator; split_ifs <;> simp
lemma rationalLearn_cast (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (l : List (Set Γ)) (p r : Γ × Γ) :
    (rationalLearn gs w l p r:ℝ)=learnedMultipliers gs (fun p r => (w p r:ℝ)) l p r := by
  unfold rationalLearn learnedMultipliers
  split_ifs <;> simp [rationalEmpirical_cast,rationalPlain_cast,rationalDefect_cast]
lemma rationalHistory_cast {X : Type*} (gs : List (Γ × Γ))
    (sample : X → List (Set Γ)) (h : List X) (p r : Γ × Γ) :
    (rationalHistory gs sample h p r:ℝ)=historyWeights gs sample h p r := by
  induction h using List.reverseRecOn generalizing p r with
  | nil => norm_num [rationalHistory,historyWeights]
  | append_singleton h x ih =>
    simp only [rationalHistory,List.foldl_append,List.foldl_cons,List.foldl_nil,historyWeights_snoc]
    rw [rationalLearn_cast]
    have he : (fun p r => ((h.foldl (fun w x => rationalLearn gs w (sample x)) (fun _ _ => 4)) p r:ℝ))=
        historyWeights gs sample h := by funext p r; exact ih p r
    rw [he]

lemma rationalRho_cast (n : ℕ) : (rationalRho n:ℝ)=annealRho n := by simp [rationalRho,annealRho]
lemma rationalRatio_cast (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (l : List (Set Γ)) :
    (rationalRatio gs g l:ℝ)=empiricalRatio gs (fun S => (g S:ℝ)) l := by
  simp [rationalRatio,empiricalRatio,rationalEmpirical_cast,rationalPlain_cast]
end RationalSampling

namespace DrawTree
open scoped BigOperators Classical
lemma uniformChoice_fits (A : Type*) [Fintype A] [Nonempty A] (H : ℕ)
    (h : Nat.clog 2 (Fintype.card A)≤H) : Fits H 1 (uniformChoice A) := by
  unfold uniformChoice
  refine ⟨?_,fun _ => trivial⟩
  have he : Fintype.card A-1+1=Fintype.card A := by have hh := Fintype.card_pos (α := A); omega
  simpa only [he] using h
end DrawTree

namespace DrawTree
open scoped BigOperators Classical
variable {A B D : Type*}
lemma optionBind_fits (t : DrawTree (Option A)) (k : A → DrawTree (Option B))
    (H M N : ℕ) (ht : Fits H M t) (hk : ∀ a,Fits H N (k a)) :
    Fits H (M+N) (t.optionBind k) := by
  apply fits_bind H M N t _ ht
  intro a; cases a with
  | none => cases N <;> trivial
  | some a => exact hk a

lemma iterate_fits (t : A → DrawTree (Option A)) (H M k : ℕ)
    (ht : ∀ a,Fits H M (t a)) : ∀ a,Fits H (M*k) (iterate t k a) := by
  induction k with
  | zero => intro a; trivial
  | succ k ih =>
    intro a
    have h := optionBind_fits (iterate t k a) t H (M*k) M (ih a) ht
    simpa only [iterate,Nat.mul_succ] using h
end DrawTree

section DrawHitting
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance116 : Fintype X]
variable (step : X → DrawTree X) (A : X → Prop)
omit sectionInstance116 in
lemma hittingTree_fits [Fintype X] (H M k : ℕ) (hs : ∀ x,DrawTree.Fits H M (step x)) :
    ∀ x,DrawTree.Fits H (M*k) (hittingTree step A k x) := by
  induction k with
  | zero => intro x; trivial
  | succ k ih =>
    intro x
    unfold hittingTree
    have h := DrawTree.fits_bind H M (M*k) (step x)
      (fun y => if hy : A y then DrawTree.leaf (some (⟨y,hy⟩ : FiniteChain.Inside A)) else hittingTree step A k y)
      (hs x) (by intro y; split_ifs; exacts [by cases M*k <;> trivial,ih y])
    simpa only [Nat.mul_succ,Nat.add_comm] using h
end DrawHitting
namespace DrawTree
open scoped BigOperators Classical
variable {X Y : Type*} [sectionInstance117 : Fintype X]
omit sectionInstance117 in
lemma map_fits [Fintype X] (t : DrawTree X) (f : X → Y) (H M : ℕ) (ht : Fits H M t) :
    Fits H M (t.map f) := by
  have h := fits_bind H M 0 t (fun x => .leaf (f x)) ht (fun _ => trivial)
  simpa only [map,Nat.add_zero] using h
lemma sample_fits (step : X → DrawTree X) (H M k : ℕ)
    (hs : ∀ x,Fits H M (step x)) (x : X) : Fits H (M*k) (sample step k x) := by
  induction k generalizing x with
  | zero => trivial
  | succ k ih =>
    unfold sample
    have h := fits_bind H M (M*k) (step x)
      (fun y => (sample step k y).map (fun v : FiniteChain.Sample X k => (x,v)))
      (hs x) (by intro y; exact map_fits _ _ H (M*k) (ih y))
    simpa only [FiniteChain.Sample,sample,Nat.mul_succ,Nat.add_comm] using h

end DrawTree
section DrawActual
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n)) (N L : ℕ)
local notation "GS" => pairedSlots n
lemma rationalStored_cast (h : List (PhaseSample n N)) (j : ℕ) (p r) :
    (rationalStored n N h j p r:ℝ)=storedWeights n N h j p r := by
  exact rationalHistory_cast GS (observedSets n N) (h.take j) p r
end DrawActual
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
lemma rationalEstimate_cast (h : List (PhaseSample n N)) :
    (rationalEstimate n M₁ M₂ N L h:ℝ)=historyEstimate n N L K h := by
  simp only [rationalEstimate,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_prod,rationalRatio_cast,
    rationalRho_cast,historyEstimate]
lemma rationalGuard_cast (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    (rationalGuard n M₁ M₂ N L h x:ℝ)=guardedEstimate n M₁ M₂ N L h x := by
  unfold rationalGuard guardedEstimate
  split_ifs <;> simp [rationalEstimate_cast]
include hn in
lemma rationalGuard_nonneg (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    0≤rationalGuard n M₁ M₂ N L h x := by
  have hh := guardedEstimate_nonneg n hn M₁ M₂ N L h x
  rw [←rationalGuard_cast] at hh
  exact_mod_cast hh
lemma rationalGuard_zero (hE₂ : M₂.E=Set.univ) (hr : M₁.eRank=M₂.eRank)
    (hZ : commonBaseCount M₁ M₂=0) (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    rationalGuard n M₁ M₂ N L h x=0 := by
  have hh := guardedEstimate_zero n M₁ M₂ N L hE₂ hr hZ h x
  rw [←rationalGuard_cast] at hh
  exact_mod_cast hh

end

open scoped BigOperators Classical

namespace RatBound
variable {q r : ℚ} {B D : ℕ}
lemma one_le (h : RatBound q B) : 1≤B := by
  obtain ⟨a,b,ha,hb,hpos,he⟩ := h; omega
lemma mono (h : RatBound q B) (hBD : B≤D) : RatBound q D := by
  obtain ⟨a,b,ha,hb,hpos,he⟩ := h
  exact ⟨a,b,ha.trans hBD,hb.trans hBD,hpos,he⟩
lemma nat (a B : ℕ) (ha : a≤B) (hB : 0<B) : RatBound (a:ℚ) B :=
  ⟨a,1,ha,hB,by omega,by simp⟩
lemma zero (B : ℕ) (hB : 0<B) : RatBound 0 B := by exact_mod_cast nat 0 B (by omega) hB
lemma one (B : ℕ) (hB : 0<B) : RatBound 1 B := by exact_mod_cast nat 1 B hB hB
lemma mul (hq : RatBound q B) (hr : RatBound r D) : RatBound (q*r) (B*D) := by
  obtain ⟨a,b,ha,hb,hpos,rfl⟩ := hq
  obtain ⟨c,d,hc,hd,hdpos,rfl⟩ := hr
  exact ⟨a*c,b*d,Nat.mul_le_mul ha hc,Nat.mul_le_mul hb hd,Nat.mul_pos hpos hdpos,by push_cast; ring⟩
lemma inv (hq : RatBound q B) : RatBound q⁻¹ B := by
  obtain ⟨a,b,ha,hb,hpos,rfl⟩ := hq
  by_cases hz : a=0
  · subst a; simpa using zero B (by omega)
  · exact ⟨b,a,hb,ha,Nat.pos_of_ne_zero hz,by simp [inv_div]⟩
lemma div (hq : RatBound q B) (hr : RatBound r D) : RatBound (q/r) (B*D) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv
lemma pow (hq : RatBound q B) (k : ℕ) : RatBound (q^k) (B^k) := by
  induction k with
  | zero => simpa using one 1 (by decide)
  | succ k ih => simpa only [pow_succ] using ih.mul hq
lemma min_one (hq : RatBound q B) : RatBound (min 1 q) B := by
  by_cases h : 1≤q
  · rw [min_eq_left h]; exact one B hq.one_le
  · rw [min_eq_right (le_of_not_ge h)]; exact hq
lemma den_le (hq : RatBound q B) : q.den≤B := by
  obtain ⟨a,b,ha,hb,hpos,rfl⟩ := hq
  have he : ((a:ℚ)/(b:ℚ))=Rat.divInt (a:ℤ) (b:ℤ) := by simp [Rat.divInt_eq_div]
  rw [he]
  have hd := Rat.den_dvd (a:ℤ) (b:ℤ)
  exact (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.mp hd)).trans hb
end RatBound

section ActualSize
open scoped BigOperators Classical
lemma RatBound.nat_div (a b B : ℕ) (ha : a≤B) (hb : b≤B) (hB : 0<B) : RatBound ((a:ℚ)/b) B := by
  by_cases hz : b=0
  · subst b; simpa using RatBound.zero B hB
  · exact ⟨a,b,ha,hb,Nat.pos_of_ne_zero hz,rfl⟩
lemma indicator_list_sum {X : Type*} (P : X → Prop) (l : List X) :
    (l.map (fun x => if P x then (1:ℚ) else 0)).sum=(l.countP (fun x => decide (P x)):ℚ) := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases hx : P x <;> simp [hx,ih,add_comm]
variable {Γ : Type*} [sectionInstance118 : Fintype Γ] [sectionInstance119 : DecidableEq Γ]
omit sectionInstance118 sectionInstance119 in
lemma rationalTypeRatio [Fintype Γ] [DecidableEq Γ] (gs : List (Γ × Γ)) (l : List (Set Γ)) (p r : Γ × Γ) :
    rationalEmpirical (rationalPlain gs (fun _ => 1)) l /
      rationalEmpirical (rationalDefect gs p r) l =
      (l.countP (fun S => decide (PlainState gs S)):ℚ)/
        (l.countP (fun S => decide (DefectState gs p r S)):ℚ) := by
  unfold rationalEmpirical rationalPlain rationalDefect
  rw [indicator_list_sum,indicator_list_sum]
  by_cases hz : l.length=0
  · have he : l=[] := List.length_eq_zero_iff.mp hz
    simp [he]
  · exact div_div_div_cancel_right₀ (by exact_mod_cast hz : (l.length:ℚ)≠0) _ _
lemma rationalLearn_bound (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℚ)
    (l : List (Set Γ)) (B N : ℕ) (hN : 0<N) (hlen : l.length≤N)
    (hw : ∀ p r,RatBound (w p r) B) (p r : Γ × Γ) :
    RatBound (rationalLearn gs w l p r) (B*N) := by
  unfold rationalLearn
  split_ifs
  · apply (hw p r).mul
    rw [rationalTypeRatio]
    exact RatBound.nat_div _ _ N ((List.countP_le_length).trans hlen)
      ((List.countP_le_length).trans hlen) hN
  · exact (hw p r).mono (Nat.le_mul_of_pos_right _ hN)
lemma rationalHistory_bound {X : Type*} (gs : List (Γ × Γ)) (sample : X → List (Set Γ))
    (N : ℕ) (hN : 0<N) (hs : ∀ x,(sample x).length≤N) (h : List X) (p r : Γ × Γ) :
    RatBound (rationalHistory gs sample h p r) (4*N^h.length) := by
  induction h using List.reverseRecOn generalizing p r with
  | nil => simpa [rationalHistory] using RatBound.nat 4 4 (by omega) (by omega)
  | append_singleton h x ih =>
    have he : rationalHistory gs sample (h++[x])=rationalLearn gs (rationalHistory gs sample h) (sample x) := by
      funext p r; simp [rationalHistory,List.foldl_append]
    rw [he]
    have hh := rationalLearn_bound gs (rationalHistory gs sample h) (sample x) (4*N^h.length) N hN (hs x) ih p r
    simpa only [List.length_append,List.length_singleton,pow_succ,Nat.mul_assoc] using hh
omit sectionInstance119 in
lemma rationalMultiplier_bound [DecidableEq Γ] (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℚ)
    (B : ℕ) (hB : 0<B) (hw : ∀ p r,RatBound (w p r) B) (S : Set Γ) :
    RatBound (rationalMultiplier gs w S) B := by
  unfold rationalMultiplier
  split_ifs
  · exact hw _ _
  · exact RatBound.one B hB
lemma rationalRho_bound (n : ℕ) (hn : 0<n) : RatBound (rationalRho n) (2*n) := by
  refine ⟨2*n-1,2*n,by omega,le_rfl,by omega,?_⟩
  have hnn : (n:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : ((2*n-1:ℕ):ℚ)=2*(n:ℚ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  rw [he,rationalRho]
  push_cast
  field_simp
omit sectionInstance118 sectionInstance119 in
lemma rationalAnneal_bound [Fintype Γ] [DecidableEq Γ] (M : Matroid Γ) (n j : ℕ) (hn : 0<n) (S : Set Γ) :
    RatBound (rationalAnneal M n j S) ((2*n)^(n*j)) := by
  have hh := ((rationalRho_bound n hn).pow j).pow (n-(M.eRk S).toNat)
  unfold rationalAnneal
  apply hh.mono
  rw [←pow_mul]
  apply Nat.pow_le_pow_right (by omega : 0<2*n)
  nlinarith [Nat.sub_le n (M.eRk S).toNat]
end ActualSize

section StoredSize
open scoped BigOperators Classical
variable (n N L : ℕ) (hN : 0<N)
include hN
lemma observedSets_length (x : PhaseSample n N) : (observedSets n N x).length=N := by
  rw [observedSets,List.length_map,FiniteChain.Sample.toList_length]
  omega
lemma rationalStored_bound (h : List (PhaseSample n N)) (hlen : h.length≤L) (j : ℕ) (p r) :
    RatBound (rationalStored n N h j p r) (4*N^L) := by
  have hd := rationalHistory_bound (pairedSlots n) (observedSets n N) N hN
    (fun x => (observedSets_length n N hN x).le) (h.take j) p r
  apply hd.mono
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right hN
  rw [List.length_take]
  exact (Nat.min_le_right _ _).trans hlen
lemma rationalWeight_bound (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
    (h : List (PhaseSample n N)) (hlen : h.length≤L) (j : ℕ) (hj : j≤L) (S : Set (Fin n ⊕ Fin n)) :
    RatBound (rationalWeight (pairedSlots n) (rationalStored n N h j) (rationalAnneal M n j) S)
      (4*N^L*(2*n)^(n*L)) := by
  unfold rationalWeight
  apply RatBound.mul
  · exact rationalMultiplier_bound _ _ _ (by positivity) (rationalStored_bound n N L hN h hlen j) S
  · apply (rationalAnneal_bound M n j hn S).mono
    apply Nat.pow_le_pow_right (by omega : 0<2*n)
    exact Nat.mul_le_mul_left n hj
lemma rationalAcceptance_bound (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
    (h : List (PhaseSample n N)) (hlen : h.length≤L) (j : ℕ) (hj : j≤L)
    (S T : ChainIndex (pairedSlots n)) :
    RatBound (rationalAcceptance (pairedSlots n) (rationalStored n N h j) (rationalAnneal M n j) S T)
      ((4*N^L*(2*n)^(n*L))^2) := by
  unfold rationalAcceptance
  have ha := (rationalWeight_bound n N L hN hn M h hlen j hj T.val).div
    (rationalWeight_bound n N L hN hn M h hlen j hj S.val)
  simpa only [pow_two] using ha.min_one
end StoredSize

open scoped BigOperators Classical
lemma acceptance_word_bound (n N L : ℕ) :
    (4*N^L*(2*n)^(n*L))^2 ≤ 2^(drawWordBound n N L) := by
  have hN := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=N)).le L
  have hn := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=2*n)).le (n*L)
  have hw : 4*N^L*(2*n)^(n*L)≤2^(2+N*L+(2*n)*(n*L)) := by
    calc
      _ ≤ 4*(2^N)^L*(2^(2*n))^(n*L) := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hN) hn
      _ = _ := by rw [←pow_mul,←pow_mul]; rw [show (4:ℕ)=2^2 by norm_num,←pow_add,←pow_add]
  calc
    _ ≤ (2^(2+N*L+(2*n)*(n*L)))^2 := Nat.pow_le_pow_left hw 2
    _ = 2^(2*(2+N*L+(2*n)*(n*L))) := by rw [←pow_mul]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by unfold drawWordBound; omega)
lemma drawWordBound_ge_one (n N L : ℕ) : 1≤drawWordBound n N L := by unfold drawWordBound; omega
lemma drawWordBound_ge_n (n N L : ℕ) : n≤drawWordBound n N L := by unfold drawWordBound; omega
lemma drawWordBound_exchange (n N L : ℕ) : Nat.clog 2 (n^2)≤drawWordBound n N L := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_two_pow_self (n:=n^2)).le.trans (Nat.pow_le_pow_right (by omega) (by unfold drawWordBound; omega))

section ActualFits
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n)) (N L : ℕ) (hN : 0<N)
local notation "GS" => pairedSlots n
local notation "H" => drawWordBound n N L
include hN in
lemma actualStepTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) (j : ℕ) (hj : j≤L)
    (x : ChainIndex GS) : DrawTree.Fits H 3 (actualStepTree n hn M N h j x) := by
  let : Nonempty (ExchangeChoice x.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]; positivity)
  unfold actualStepTree rationalMetropolis
  apply DrawTree.fits_bind H 1 2 _ _
  · apply DrawTree.bernoulli_fits
    norm_num
    exact drawWordBound_ge_one n N L
  · intro lazy
    cases lazy with
    | true => trivial
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      apply DrawTree.fits_bind H 1 1 _ _
      · apply DrawTree.uniformChoice_fits
        rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]
        exact drawWordBound_exchange n N L
      · intro a
        unfold rationalExchange
        split_ifs
        · apply DrawTree.map_fits
          apply DrawTree.bernoulli_fits
          apply Nat.clog_le_of_le_pow
          exact (rationalAcceptance_bound n N L hN hn M h hlen j hj x _).den_le.trans
            (acceptance_word_bound n N L)
        · trivial
include hN in
lemma actualTraceTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) (j cap : ℕ) (hj : j≤L)
    (x : PlainIndex GS) : DrawTree.Fits H (3*(cap+1)) (actualTraceTree n hn M N h j cap x) := by
  exact hittingTree_fits _ _ H 3 (cap+1) (actualStepTree_fits n hn M N L hN h hlen j hj) x.val
include hN in
lemma actualRestartTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) (cap j : ℕ) (hj : j≤L) :
    DrawTree.Fits H (1+3*j*(cap+1)*(20*n^4*(n*(L+1)+2))) (actualRestartTree n hn M N L h cap j) := by
  let := plainIndex_nonempty GS (pairedSlots_fresh n) (pairedSlots_cover n)
  induction j with
  | zero =>
    rw [actualRestartTree]
    simp only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero]
    apply DrawTree.map_fits
    apply DrawTree.uniformChoice_fits
    rw [plainIndex_card,Nat.clog_pow 2 n (by omega)]
    exact drawWordBound_ge_n n N L
  | succ j ih =>
    rw [actualRestartTree]
    have hh := DrawTree.optionBind_fits (actualRestartTree n hn M N L h cap j)
      (DrawTree.iterate (actualTraceTree n hn M N h (j+1) cap) (20*n^4*(n*(L+1)+2))) H
      (1+3*j*(cap+1)*(20*n^4*(n*(L+1)+2))) (3*(cap+1)*(20*n^4*(n*(L+1)+2)))
      (ih (by omega))
      (DrawTree.iterate_fits _ H (3*(cap+1)) _ (actualTraceTree_fits n hn M N L hN h hlen (j+1) cap hj))
    convert hh using 1 <;> first | rfl | ring

include hN in
lemma actualPhaseTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) :
    DrawTree.Fits H (phaseDrawBound n N L) (actualPhaseTree n hn M N L h) := by
  unfold actualPhaseTree
  split_ifs
  · have hstart : DrawTree.Fits H (1+3*L*(restartCap n L+1)*(20*n^4*(n*(L+1)+2))) (actualStartTree n hn M N L h) := by
      apply DrawTree.map_fits
      apply DrawTree.fits_mono_steps H _ _ _ _
        (actualRestartTree_fits n hn M N L hN h hlen (restartCap n L) h.length hlen)
      gcongr
    apply DrawTree.optionBind_fits _ _ H _ (3*N) hstart
    intro x
    apply DrawTree.map_fits
    apply DrawTree.fits_mono_steps H (3*(N-1)) (3*N) (by omega)
    exact DrawTree.sample_fits _ H 3 (N-1) (actualStepTree_fits n hn M N L hN h hlen h.length hlen) x
  · cases phaseDrawBound n N L <;> trivial
end ActualFits

namespace DrawTree
variable {A B C : Type*}
lemma bind_assoc (t : DrawTree A) (f : A → DrawTree B) (g : B → DrawTree C) :
    (t.bind f).bind g=t.bind (fun a => (f a).bind g) := by
  induction t with
  | leaf a => rfl
  | draw v k ih => simp only [bind,ih]
lemma optionBind_assoc (t : DrawTree (Option A)) (f : A → DrawTree (Option B)) (g : B → DrawTree (Option C)) :
    (t.optionBind f).optionBind g=t.optionBind (fun a => (f a).optionBind g) := by
  simp only [optionBind,bind_assoc]
  congr 1; funext a; cases a <;> rfl
lemma leaf_fits (H M : ℕ) (a : A) : Fits H M (.leaf a) := by cases M <;> trivial
end DrawTree
section AlgorithmFits
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (hN : 0<N)
local notation "K" => pairedMatroid M₁ M₂
local notation "H" => drawWordBound n N L
local notation "B" => phaseDrawBound n N L
include hN in
lemma rationalWitnessTree_fits (h : List (PhaseSample n N)) (hlen : h.length≤L) :
    DrawTree.Fits H B (rationalWitnessTree n hn M₁ M₂ N L h) := by
  unfold rationalWitnessTree
  split_ifs
  · apply DrawTree.fits_mono_steps H _ B _ _
      (actualRestartTree_fits n hn K N L hN h hlen (restartCap n L) h.length hlen)
    unfold phaseDrawBound
    have hh : 3*h.length*(restartCap n L+1)*(20*n^4*(n*(L+1)+2))≤
        3*L*(restartCap n L+1)*(20*n^4*(n*(L+1)+2)) := by gcongr
    omega
  · exact DrawTree.leaf_fits H B none
include hN in
lemma rational_history_finish_fits (h : List (PhaseSample n N)) (k : ℕ) (hlen : h.length+k≤L) :
    DrawTree.Fits H (B*(k+1))
      ((DrawTree.history (actualPhaseTree n hn K N L) k h).optionBind (fun h =>
        (rationalWitnessTree n hn M₁ M₂ N L h).map (Option.map (rationalGuard n M₁ M₂ N L h)))) := by
  induction k generalizing h with
  | zero =>
    simp only [DrawTree.history,DrawTree.pureSome,DrawTree.optionBind,DrawTree.bind,Nat.zero_add,Nat.mul_one]
    exact DrawTree.map_fits _ _ H B (rationalWitnessTree_fits n hn M₁ M₂ N L hN h (by omega))
  | succ k ih =>
    rw [DrawTree.history,DrawTree.optionBind_assoc]
    have hh := DrawTree.optionBind_fits
      (actualPhaseTree n hn K N L h)
      (fun x => (DrawTree.history (actualPhaseTree n hn K N L) k (h++[x])).optionBind (fun h =>
        (rationalWitnessTree n hn M₁ M₂ N L h).map (Option.map (rationalGuard n M₁ M₂ N L h))))
      H B (B*(k+1)) (actualPhaseTree_fits n hn K N L hN h (by omega)) (by
        intro x; apply ih; simp only [List.length_append,List.length_singleton]; omega)
    convert hh using 1 <;> first | rfl | ring
include hN in
lemma rationalAlgorithmTree_fits : DrawTree.Fits H (algorithmDrawBound n N L) (rationalAlgorithmTree n hn M₁ M₂ N L) :=
  rational_history_finish_fits n hn M₁ M₂ N L hN [] L (by simp)
end AlgorithmFits

namespace DrawTree
variable {A B : Type*}
lemma all_bind (t : DrawTree A) (f : A → DrawTree B) (p : B → Prop)
    (hf : ∀ a,All p (f a)) : All p (t.bind f) := by
  induction t with
  | leaf a => exact hf a
  | draw v k ih => exact ih
lemma all_map (t : DrawTree A) (f : A → B) (p : B → Prop) (hf : ∀ a,p (f a)) : All p (t.map f) :=
  all_bind t _ p hf
end DrawTree
section AlgorithmAll
open scoped Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
include hn in
lemma rationalAlgorithmTree_all : DrawTree.All
    (fun a : Option ℚ => ∀ z,a=some z → 0≤z ∧
      (M₂.E=Set.univ → M₁.eRank=M₂.eRank → commonBaseCount M₁ M₂=0 → z=0))
    (rationalAlgorithmTree n hn M₁ M₂ N L) := by
  unfold rationalAlgorithmTree DrawTree.optionBind
  apply DrawTree.all_bind
  intro a
  cases a with
  | none => intro z; simp
  | some h =>
    apply DrawTree.all_map
    intro a
    cases a with
    | none => intro z; simp
    | some x =>
      intro z hz
      simp only [Option.map_some,Option.some.injEq] at hz
      subst z
      exact ⟨rationalGuard_nonneg n hn M₁ M₂ N L h x,
        fun hE hr hZ => rationalGuard_zero n M₁ M₂ N L hE hr hZ h x⟩
end AlgorithmAll
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical
lemma rationalMedian_all (p : ℚ → Prop) (l : List ℚ) (h0 : p 0) (hl : ∀ z∈l,p z) : p (rationalMedian l) := by
  unfold rationalMedian
  by_cases h : l.length/2<(l.mergeSort (· ≤ ·)).length
  · rw [List.getD_eq_getElem _ _ h]
    apply hl
    exact (List.mem_mergeSort).mp (List.getElem_mem h)
  · have hl0 : l.length=0 := by simp only [List.length_mergeSort] at h; omega
    have he : l=[] := List.length_eq_zero_iff.mp hl0
    simpa [he] using h0

section GreedyOracle
variable {α : Type*} [sectionInstance120 : DecidableEq α]

lemma greedyOracle_correct (M : Matroid α) (O : Finset α → Bool)
    (hO : ∀ I,O I = true ↔ M.Indep (I : Set α)) (l : List α)
    (hE : ∀ a ∈ l,a ∈ M.E) : M.IsBasis (greedyOracle O l : Set α) (l.toFinset : Set α) := by
  induction l with
  | nil => simp [greedyOracle]
  | cons a l ih =>
    have hi := ih (fun x hx => hE x (by simp [hx]))
    have ha := hE a (by simp)
    simp only [greedyOracle]
    split_ifs with h
    · have hind := (hO _).mp h
      apply hind.isBasis_of_subset_of_subset_closure
      · simpa only [List.toFinset_cons,Finset.coe_insert] using Set.insert_subset_insert hi.subset
      · simp only [List.toFinset_cons,Finset.coe_insert]
        apply Set.insert_subset
        · simpa only [Finset.coe_insert] using M.subset_closure _ hind.subset_ground (Finset.mem_insert_self a _)
        · exact hi.subset_closure.trans (M.closure_mono (by simp))
    · apply hi.indep.isBasis_of_subset_of_subset_closure
      · exact hi.subset.trans (by simp)
      · simp only [List.toFinset_cons,Finset.coe_insert]
        apply Set.insert_subset
        · apply hi.indep.mem_closure_iff'.mpr
          refine ⟨ha,?_⟩
          intro hind
          exfalso
          exact h ((hO _).mpr (by simpa using hind))
        · exact hi.subset_closure

lemma greedyOracle_rank (M : Matroid α) (O : Finset α → Bool)
    (hO : ∀ I,O I = true ↔ M.Indep (I : Set α)) (l : List α)
    (hE : ∀ a ∈ l,a ∈ M.E) :
    (greedyOracle O l).card = (M.eRk (l.toFinset : Set α)).toNat := by
  have h := (greedyOracle_correct M O hO l hE).encard_eq_eRk
  simpa using congrArg ENat.toNat h
end GreedyOracle

open scoped Classical

lemma queryFinset_exact {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (which : Bool) (I : Finset (Fin n)) :
    queryFinset O which I = true ↔ (if which then M₂ else M₁).Indep (I : Set (Fin n)) := by
  have h := hO which (fun i => decide (i ∈ I))
  have he : {i : Fin n | decide (i ∈ I) = true} = (I : Set (Fin n)) := by ext i; simp
  rw [he] at h
  exact h
lemma rankOracle_correct {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (which : Bool) (S : Finset (Fin n)) :
    rankOracle O which S = ((if which then M₂ else M₁).eRk (S : Set (Fin n))).toNat := by
  have hE : (if which then M₂ else M₁).E = Set.univ := by cases which <;> simpa
  have h := greedyOracle_rank (if which then M₂ else M₁) (queryFinset O which)
    (queryFinset_exact M₁ M₂ O hO which) ((List.finRange n).filter (fun i => decide (i ∈ S)))
    (by intro i _; simp [hE])
  have hs : (((List.finRange n).filter (fun i => decide (i ∈ S))).toFinset : Set (Fin n)) = S := by
    ext i; simp
  rw [hs] at h
  exact h

section SumRank
open Set
variable {α β : Type*} [sectionInstance121 : Fintype α] [sectionInstance122 : Fintype β]
omit sectionInstance121 sectionInstance122 in
lemma sum_eRk [Fintype α] [Fintype β] (M : Matroid α) (N : Matroid β) (S : Set (α ⊕ β)) :
    (M.sum N).eRk S = M.eRk (Sum.inl ⁻¹' S) + N.eRk (Sum.inr ⁻¹' S) := by
  obtain ⟨I,hI⟩ := M.exists_isBasis' (Sum.inl ⁻¹' S)
  obtain ⟨J,hJ⟩ := N.exists_isBasis' (Sum.inr ⁻¹' S)
  have hb : (M.sum N).IsBasis' (Sum.inl '' I ∪ Sum.inr '' J) S := by
    rw [Matroid.isBasis'_iff_isBasis_inter_ground,Matroid.sum_isBasis_iff]
    constructor
    · simpa [Set.preimage_image_eq _ Sum.inl_injective,Set.preimage_image_eq _ Sum.inr_injective]
        using hI.isBasis_inter_ground
    · simpa [Set.preimage_image_eq _ Sum.inl_injective,Set.preimage_image_eq _ Sum.inr_injective]
        using hJ.isBasis_inter_ground
  rw [hb.eRk_eq_encard,Set.encard_union_eq (Set.disjoint_image_inl_image_inr),
    Set.InjOn.encard_image Sum.inl_injective.injOn,
    Set.InjOn.encard_image Sum.inr_injective.injOn,hI.encard_eq_eRk,hJ.encard_eq_eRk]

lemma dual_rank_nat (M : Matroid α) (hE : M.E=Set.univ) (S : Set α) :
    (M✶.eRk S).toNat+M.eRank.toNat = S.ncard+(M.eRk Sᶜ).toNat := by
  have h := M.eRk_dual_add_eRank S (by simp [hE])
  rw [hE,← Set.compl_eq_univ_sdiff] at h
  have hh := congrArg ENat.toNat h
  rw [ENat.toNat_add (M✶.isRkFinite_set S).eRk_lt_top.ne
      ((M.eRank_ne_top_iff).mpr inferInstance),
    ENat.toNat_add (M.isRkFinite_set Sᶜ).eRk_lt_top.ne
      (Set.encard_ne_top_iff.mpr (Set.toFinite S))] at hh
  simpa only [Set.ncard,add_comm] using hh
end SumRank

open scoped Classical

lemma paired_rank_nat {n r : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₂ : M₂.E=Set.univ) (hr₂ : M₂.eRank=(r:ℕ∞)) (S : Set (Fin n ⊕ Fin n)) :
    ((pairedMatroid M₁ M₂).eRk S).toNat+r =
      (M₁.eRk (Sum.inl ⁻¹' S)).toNat+(Sum.inr ⁻¹' S).ncard+
        (M₂.eRk (Sum.inr ⁻¹' S)ᶜ).toNat := by
  rw [pairedMatroid,sum_eRk,ENat.toNat_add
    (M₁.isRkFinite_set _).eRk_lt_top.ne (M₂✶.isRkFinite_set _).eRk_lt_top.ne]
  have h := dual_rank_nat M₂ hE₂ (Sum.inr ⁻¹' S)
  rw [hr₂,ENat.toNat_natCast] at h
  omega
lemma pairedDeficiencyOracle_correct {n r : ℕ} (M₁ M₂ : Matroid (Fin n))
    (O : IndependenceOracle n) (hO : ExactOracles M₁ M₂ O)
    (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (_ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞)) (S : Set (Fin n ⊕ Fin n)) :
    pairedDeficiencyOracle r O (Sum.inl ⁻¹' S).toFinset (Sum.inr ⁻¹' S).toFinset =
      n-((pairedMatroid M₁ M₂).eRk S).toNat := by
  have h := paired_rank_nat M₁ M₂ hE₂ hr₂ S
  unfold pairedDeficiencyOracle
  rw [rankOracle_correct M₁ M₂ O hO hE₁ hE₂,rankOracle_correct M₁ M₂ O hO hE₁ hE₂]
  simp only [Bool.false_eq_true,ite_false,ite_true,Set.coe_toFinset,Finset.coe_compl,
    Set.toFinset_card,Set.fintypeCard_eq_ncard]
  omega

section

open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
lemma rationalHistoryPositive_iff (h : List (PhaseSample n N)) :
    rationalHistoryPositive n N h ↔ HistoryPositive n N h := by
  unfold rationalHistoryPositive HistoryPositive
  constructor <;> intro hh j hj p q
  · have hs := hh j hj p q
    rw [←rationalStored_cast]
    exact_mod_cast hs
  · have hs := hh j hj p q
    rw [←rationalStored_cast] at hs
    exact_mod_cast hs
variable (M₁ M₂ : Matroid (Fin n)) (hO : ExactOracles M₁ M₂ O)
variable (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
variable (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞))
include hO hE₁ hE₂ hr₁ hr₂
lemma oracleDeficiency_eq (S : Set (Fin n ⊕ Fin n)) :
    oracleDeficiency n r O S=n-((pairedMatroid M₁ M₂).eRk S).toNat :=
  pairedDeficiencyOracle_correct M₁ M₂ O hO hE₁ hE₂ hr₁ hr₂ S
lemma oracleAnneal_eq (j : ℕ) : oracleAnneal n r O j = rationalAnneal (pairedMatroid M₁ M₂) n j := by
  funext S
  simp only [oracleAnneal,rationalAnneal,oracleDeficiency_eq n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleStepTree_eq (h : List (PhaseSample n N)) (j : ℕ) :
    oracleStepTree n hn r O N h j=actualStepTree n hn (pairedMatroid M₁ M₂) N h j := by
  unfold oracleStepTree actualStepTree
  rw [oracleAnneal_eq n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleTraceTree_eq (h : List (PhaseSample n N)) (j cap : ℕ) :
    oracleTraceTree n hn r O N h j cap=actualTraceTree n hn (pairedMatroid M₁ M₂) N h j cap := by
  unfold oracleTraceTree actualTraceTree
  rw [oracleStepTree_eq n hn r O N M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleRestartTree_eq (h : List (PhaseSample n N)) (cap j : ℕ) :
    oracleRestartTree n hn r O N L h cap j = actualRestartTree n hn (pairedMatroid M₁ M₂) N L h cap j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [oracleRestartTree,actualRestartTree,ih,
      oracleTraceTree_eq n hn r O N M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleStartTree_eq (h : List (PhaseSample n N)) :
    oracleStartTree n hn r O N L h=actualStartTree n hn (pairedMatroid M₁ M₂) N L h := by
  unfold oracleStartTree actualStartTree
  rw [oracleRestartTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oraclePhaseTree_eq : oraclePhaseTree n hn r O N L=actualPhaseTree n hn (pairedMatroid M₁ M₂) N L := by
  funext h
  simp only [oraclePhaseTree,actualPhaseTree,rationalHistoryPositive_iff,
    oracleStartTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂,
    oracleStepTree_eq n hn r O N M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleEstimate_eq (h : List (PhaseSample n N)) :
    oracleEstimate n r O N L h=rationalEstimate n M₁ M₂ N L h := by
  simp only [oracleEstimate,rationalEstimate,
    oracleDeficiency_eq n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
lemma oracleGuard_eq (h : List (PhaseSample n N)) :
    oracleGuard n r O N L h=rationalGuard n M₁ M₂ N L h := by
  funext x
  simp only [oracleGuard,rationalGuard,Witnessed,
    oracleDeficiency_eq n r O M₁ M₂ hO hE₁ hE₂ hr₁ hr₂,
    oracleEstimate_eq n r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
  split_ifs <;> simp_all
lemma oracleWitnessTree_eq (h : List (PhaseSample n N)) :
    oracleWitnessTree n hn r O N L h=rationalWitnessTree n hn M₁ M₂ N L h := by
  simp only [oracleWitnessTree,rationalWitnessTree,rationalHistoryPositive_iff,
    oracleRestartTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
theorem oracleAlgorithmTree_eq : oracleAlgorithmTree n hn r O N L=rationalAlgorithmTree n hn M₁ M₂ N L := by
  simp only [oracleAlgorithmTree,rationalAlgorithmTree,
    oraclePhaseTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂,
    oracleWitnessTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂,
    oracleGuard_eq n r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]

end

open scoped BigOperators Classical
lemma commonBaseCount_empty (M₁ M₂ : Matroid (Fin 0)) : commonBaseCount M₁ M₂=1 := by
  have base (M : Matroid (Fin 0)) : M.IsBase ∅ := by
    obtain ⟨B,hB⟩ := M.exists_isBase
    have he : B=∅ := Set.eq_empty_of_isEmpty B
    simpa only [he] using hB
  let : Nonempty {A : Finset (Fin 0) // M₁.IsBase (A:Set (Fin 0)) ∧ M₂.IsBase (A:Set (Fin 0))} :=
    ⟨⟨∅,by simpa using And.intro (base M₁) (base M₂)⟩⟩
  unfold commonBaseCount
  exact Nat.card_unique

open scoped BigOperators Classical

section
namespace DrawTree
open scoped BigOperators Classical
variable {A B : Type*}

lemma Reindexed.refl (t : DrawTree A) : Reindexed t t := by
  induction t with
  | leaf a => exact .leaf a
  | draw v k ih => exact .draw v k k (Equiv.refl _) ih
lemma Reindexed.symm {t u : DrawTree A} (h : Reindexed t u) : Reindexed u t := by
  induction h with
  | leaf a => exact .leaf a
  | draw v k l e h ih =>
    apply Reindexed.draw v l k e.symm
    intro i
    simpa using ih (e.symm i)
lemma Reindexed.bind {t u : DrawTree A} {k l : A → DrawTree B}
    (ht : Reindexed t u) (hk : ∀ a,Reindexed (k a) (l a)) :
    Reindexed (t.bind k) (u.bind l) := by
  induction ht with
  | leaf a => exact hk a
  | draw v a b e h ih => exact .draw v _ _ e ih
lemma Reindexed.map {t u : DrawTree A} (h : Reindexed t u) (f : A → B) :
    Reindexed (t.map f) (u.map f) := h.bind (fun a => .leaf (f a))
lemma uniformVia_reindexed (A : Type*) [Fintype A] [Nonempty A]
    (e : Fin (Fintype.card A) ≃ A) : Reindexed (uniformVia A e) (uniformChoice A) := by
  let h : Fintype.card A-1+1=Fintype.card A := by have hh := Fintype.card_pos (α := A); omega
  let c := finCongr h
  let p := c.trans (e.trans ((Fintype.equivFin A).trans c.symm))
  apply Reindexed.draw _ _ _ p
  intro i
  have he : (Fintype.equivFin A).symm (Fin.cast h (p i))=e (Fin.cast h i) := by simp [p,c]
  simpa only [he] using Reindexed.leaf (e (Fin.cast h i))
lemma Reindexed.fits {t u : DrawTree A} (h : Reindexed t u) (H M : ℕ)
    (ht : Fits H M t) : Fits H M u := by
  induction h generalizing M with
  | leaf a => trivial
  | draw v k l e h ih =>
    cases M with
    | zero => exact False.elim ht
    | succ M =>
      refine ⟨ht.1,fun i => ?_⟩
      simpa using ih (e.symm i) M (ht.2 (e.symm i))
lemma Reindexed.all {t u : DrawTree A} (h : Reindexed t u) (P : A → Prop)
    (ht : All P t) : All P u := by
  induction h with
  | leaf a => exact ht
  | draw v k l e h ih =>
    intro i
    simpa using ih (e.symm i) (ht (e.symm i))
lemma Reindexed.run_expectation {t u : DrawTree A} (h : Reindexed t u) (H D M : ℕ)
    (ht : Fits H M t) (φ : A → ℝ) :
    uniformAverage (fun bits => optionValue φ (run H D M t bits))=
      uniformAverage (fun bits => optionValue φ (run H D M u bits)) := by
  induction h generalizing M with
  | leaf a => rfl
  | draw v k l e h ih =>
    cases M with
    | zero => exact False.elim ht
    | succ M =>
      rw [run_draw_average H D M v k ht.1 φ,run_draw_average H D M v l ht.1 φ]
      congr 1
      have he : ∀ i,uniformAverage (fun bits => optionValue φ (run H D M (k i) bits))=
          uniformAverage (fun bits => optionValue φ (run H D M (l (e i)) bits)) :=
        fun i => ih i M (ht.2 i)
      simp_rw [he]
      exact uniformAverage_equiv e (fun i => uniformAverage (fun bits => optionValue φ (run H D M (l i) bits)))
lemma Reindexed.run_observable {t u : DrawTree A} (h : Reindexed t u) (H D M : ℕ)
    (ht : Fits H M t) (φ : Option A → ℝ) :
    uniformAverage (fun bits => φ (run H D M t bits))=
      uniformAverage (fun bits => φ (run H D M u bits)) := by
  have hf : ∀ x : Option A,φ x=optionValue (fun a => φ (some a)-φ none) x+φ none := by
    intro x; cases x <;> simp [optionValue]
  have he (v : DrawTree A) :
      (fun bits => φ (run H D M v bits))=
        (fun bits => optionValue (fun a => φ (some a)-φ none) (run H D M v bits)+φ none) :=
    funext (fun bits => hf _)
  rw [he t,he u,uniformAverage_add,uniformAverage_add,h.run_expectation H D M ht]
lemma Reindexed.optionBind {t u : DrawTree (Option A)} {k l : A → DrawTree (Option B)}
    (ht : Reindexed t u) (hk : ∀ a,Reindexed (k a) (l a)) :
    Reindexed (t.optionBind k) (u.optionBind l) := by
  apply ht.bind
  intro a; cases a with
  | none => exact .leaf none
  | some a => exact hk a
lemma Reindexed.iterate {t u : A → DrawTree (Option A)} (h : ∀ a,Reindexed (t a) (u a))
    (k : ℕ) (a : A) : Reindexed (iterate t k a) (iterate u k a) := by
  induction k with
  | zero => exact .leaf (some a)
  | succ k ih => exact ih.optionBind h
lemma Reindexed.sample [Fintype A] {t u : A → DrawTree A} (h : ∀ a,Reindexed (t a) (u a))
    (k : ℕ) (a : A) : Reindexed (sample t k a) (sample u k a) := by
  induction k generalizing a with
  | zero => exact .leaf a
  | succ k ih => exact (h a).bind (fun x => (ih x).map (fun v => (a,v)))
lemma Reindexed.history {K L : List A → DrawTree (Option A)}
    (h : ∀ a,Reindexed (K a) (L a)) (k : ℕ) (a : List A) :
    Reindexed (history K k a) (history L k a) := by
  induction k generalizing a with
  | zero => exact .leaf (some a)
  | succ k ih => exact (h a).optionBind (fun x => ih (a++[x]))
end DrawTree
lemma hittingTree_reindexed {X : Type*} [Fintype X] {t u : X → DrawTree X}
    (h : ∀ x,DrawTree.Reindexed (t x) (u x)) (A : X → Prop) (k : ℕ) (x : X) :
    DrawTree.Reindexed (hittingTree t A k x) (hittingTree u A k x) := by
  classical
  induction k generalizing x with
  | zero => exact .leaf none
  | succ k ih =>
    apply (h x).bind
    intro y
    by_cases hy : A y
    · simp only [dite_eq_left hy]; exact .leaf _
    · simp only [dite_eq_right hy]; exact ih y

open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
local notation "GS" => pairedSlots n
lemma canonicalMetropolis_reindexed (w : ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) →
    ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℚ) (f : Set (Fin n ⊕ Fin n) → ℚ)
    (S : ChainIndex GS) : DrawTree.Reindexed (canonicalMetropolis n hn w f S)
      (rationalMetropolis GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n) w f S) := by
  let : Nonempty (ExchangeChoice S.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]; positivity)
  apply (DrawTree.Reindexed.refl (DrawTree.bernoulli (1/2))).bind
  intro lazy
  cases lazy with
  | true => exact .leaf S
  | false =>
    apply (DrawTree.uniformVia_reindexed _ (canonicalExchangeEnumeration n S.val)).bind
    intro a; exact .refl _
lemma canonicalStepTree_reindexed (h : List (PhaseSample n N)) (j : ℕ) (S : ChainIndex GS) :
    DrawTree.Reindexed (canonicalStepTree n hn r O N h j S) (oracleStepTree n hn r O N h j S) :=
  canonicalMetropolis_reindexed n hn _ _ S
lemma canonicalTraceTree_reindexed (h : List (PhaseSample n N)) (j cap : ℕ) (S : PlainIndex GS) :
    DrawTree.Reindexed (canonicalTraceTree n hn r O N h j cap S) (oracleTraceTree n hn r O N h j cap S) :=
  hittingTree_reindexed (canonicalStepTree_reindexed n hn r O N h j) _ _ _
lemma canonicalRestartTree_reindexed (h : List (PhaseSample n N)) (cap j : ℕ) :
    DrawTree.Reindexed (canonicalRestartTree n hn r O N L h cap j) (oracleRestartTree n hn r O N L h cap j) := by
  let := plainIndex_nonempty GS (pairedSlots_fresh n) (pairedSlots_cover n)
  induction j with
  | zero => exact (DrawTree.uniformVia_reindexed _ (canonicalPlainEnumeration n)).map some
  | succ j ih => exact ih.optionBind (fun S => DrawTree.Reindexed.iterate (canonicalTraceTree_reindexed n hn r O N h (j+1) cap) _ S)
lemma canonicalStartTree_reindexed (h : List (PhaseSample n N)) :
    DrawTree.Reindexed (canonicalStartTree n hn r O N L h) (oracleStartTree n hn r O N L h) :=
  (canonicalRestartTree_reindexed n hn r O N L h _ _).map _
lemma canonicalPhaseTree_reindexed (h : List (PhaseSample n N)) :
    DrawTree.Reindexed (canonicalPhaseTree n hn r O N L h) (oraclePhaseTree n hn r O N L h) := by
  unfold canonicalPhaseTree oraclePhaseTree
  split_ifs
  · exact (canonicalStartTree_reindexed n hn r O N L h).optionBind (fun S =>
      (DrawTree.Reindexed.sample (canonicalStepTree_reindexed n hn r O N h h.length) _ S).map some)
  · exact .leaf none
lemma canonicalWitnessTree_reindexed (h : List (PhaseSample n N)) :
    DrawTree.Reindexed (canonicalWitnessTree n hn r O N L h) (oracleWitnessTree n hn r O N L h) := by
  unfold canonicalWitnessTree oracleWitnessTree
  split_ifs
  · exact canonicalRestartTree_reindexed n hn r O N L h _ _
  · exact .leaf none
lemma canonicalAlgorithmTree_reindexed :
    DrawTree.Reindexed (canonicalAlgorithmTree n hn r O N L) (oracleAlgorithmTree n hn r O N L) :=
  (DrawTree.Reindexed.history (canonicalPhaseTree_reindexed n hn r O N L) L []).optionBind
    (fun h => (canonicalWitnessTree_reindexed n hn r O N L h).map _)

end

section CanonicalFair
open scoped BigOperators Classical
lemma uniformAverage_independent_eq {X Y Z : Type*} [Fintype X] [Fintype Y]
    (f : X → Z) (g : Y → Z)
    (h : ∀ φ : Z → ℝ,uniformAverage (fun x => φ (f x))=uniformAverage (fun y => φ (g y)))
    (k : ℕ) (F : (Fin k → Z) → ℝ) :
    uniformAverage (fun xs : Fin k → X => F (fun i => f (xs i)))=
      uniformAverage (fun ys : Fin k → Y => F (fun i => g (ys i))) := by
  induction k with
  | zero =>
    have hf : ∀ xs : Fin 0 → X,(fun i => f (xs i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro xs; funext i; exact Fin.elim0 i
    have hg : ∀ ys : Fin 0 → Y,(fun i => g (ys i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro ys; funext i; exact Fin.elim0 i
    simp_rw [hf,hg,uniformAverage_const]
  | succ k ih =>
    have hf (x : X) (xs : Fin k → X) :
        (fun i : Fin (k+1) => f ((Fin.cons x xs : Fin (k+1) → X) i))=Fin.cons (f x) (fun i => f (xs i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hg (y : Y) (ys : Fin k → Y) :
        (fun i : Fin (k+1) => g ((Fin.cons y ys : Fin (k+1) → Y) i))=Fin.cons (g y) (fun i => g (ys i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp_rw [hf,hg]
    have hi (x : X) := ih (fun zs => F (Fin.cons (f x) zs))
    simp_rw [hi]
    exact h (fun z => uniformAverage (fun ys : Fin k → Y => F (Fin.cons z (fun i => g (ys i)))))
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
variable (M₁ M₂ : Matroid (Fin n)) (hO : ExactOracles M₁ M₂ O)
variable (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
variable (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞))
include hO hE₁ hE₂ hr₁ hr₂ in
lemma canonicalAlgorithmTree_to_rational :
    DrawTree.Reindexed (canonicalAlgorithmTree n hn r O N L) (rationalAlgorithmTree n hn M₁ M₂ N L) := by
  rw [←oracleAlgorithmTree_eq n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂]
  exact canonicalAlgorithmTree_reindexed n hn r O N L
include hO hE₁ hE₂ hr₁ hr₂ in
lemma canonicalAlgorithmTree_fits (hN : 0<N) :
    DrawTree.Fits (drawWordBound n N L) (algorithmDrawBound n N L) (canonicalAlgorithmTree n hn r O N L) :=
  (canonicalAlgorithmTree_to_rational n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂).symm.fits _ _
    (rationalAlgorithmTree_fits n hn M₁ M₂ N L hN)
end CanonicalFair

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

section

variable {k n : ℕ}
lemma incrementBits_correct (xs : List Bool) : binaryValue (incrementBits xs)=binaryValue xs+1 := by
  induction xs with
  | nil => simp [incrementBits,leadingOnes,carryTail,binaryValue]
  | cons x xs ih =>
    cases x with
    | false => simp [incrementBits,leadingOnes,carryTail,binaryValue,Nat.add_comm]
    | true =>
      have he : incrementBits (true::xs)=false::incrementBits xs := by simp [incrementBits,leadingOnes,carryTail,List.replicate_succ]
      rw [he,binaryValue,binaryValue,ih]
      simp; omega

end

open scoped Classical

section

variable {k n : ℕ}
lemma wordGreedy_length (W : List Bool → Bool) (xs ps : List Bool) :
    (wordGreedy W xs ps).length=xs.length+ps.length := by
  induction xs generalizing ps with
  | nil => simp [wordGreedy]
  | cons b xs ih => simp [wordGreedy,ih,Nat.add_comm,Nat.add_left_comm]

end

section

variable {n : ℕ}
lemma wordSet_zero_succ (m : ℕ) (ps : List Bool) :
    wordSet n (List.replicate (m+1) false++ps)=wordSet n (List.replicate m false++false::ps) := by
  congr 1
  rw [List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]
lemma wordSet_bit (as ps : List Bool) (h : as.length<n) :
    wordSet n (as++true::ps)=insert (⟨as.length,h⟩ : Fin n) (wordSet n (as++false::ps)) := by
  ext i
  simp only [wordSet,Set.mem_ofPred_eq,Set.mem_insert_iff,Fin.ext_iff]
  by_cases hi : i.val<as.length
  · rw [List.getElem?_append_left hi,List.getElem?_append_left hi]
    have hh : ¬i.val=as.length := by omega
    simp [hh]
  · have hle : as.length≤ i.val := by omega
    rw [List.getElem?_append_right hle,List.getElem?_append_right hle]
    by_cases he : i.val=as.length
    · simp [he]
    · obtain ⟨j,hj⟩ : ∃j,i.val-as.length=j+1 := ⟨i.val-as.length-1,by omega⟩
      simp [he,hj]
lemma wordSet_zero_subset (xs ps : List Bool) :
    wordSet n (List.replicate xs.length false++ps) ⊆ wordSet n (xs++ps) := by
  intro i hi
  simp only [wordSet,Set.mem_ofPred_eq] at *
  by_cases h : i.val<xs.length
  · rw [List.getElem?_append_left (by simpa using h),List.getElem?_replicate] at hi
    simp [h] at hi
  · have hle : xs.length≤ i.val := by omega
    rw [List.getElem?_append_right (by simpa using hle)] at hi
    rw [List.getElem?_append_right hle]
    simpa using hi
lemma wordSet_ofFn (f : Fin n → Bool) : wordSet n (List.ofFn f)={i | f i=true} := by
  ext i
  simp [wordSet]
lemma wordSet_zeros (m : ℕ) : wordSet n (List.replicate m false)=∅ := by
  ext i
  simp only [wordSet,Set.mem_ofPred_eq,List.getElem?_replicate,Set.mem_empty_iff_false,iff_false]
  split_ifs <;> simp

theorem wordGreedy_basis (M : Matroid (Fin n)) (hE : M.E=Set.univ)
    (W : List Bool → Bool) (hW : ∀l,l.length=n → (W l=true ↔ M.Indep (wordSet n l)))
    (xs ps : List Bool) (hn : xs.length+ps.length=n)
    (hI : M.Indep (wordSet n (List.replicate xs.length false++ps))) :
    M.IsBasis (wordSet n (wordGreedy W xs ps)) (wordSet n (xs.reverse++ps)) := by
  induction xs generalizing ps with
  | nil => simpa [wordGreedy] using hI.isBasis_self
  | cons b xs ih =>
    have hlen : xs.length+(b::ps).length=n := by simp only [List.length_cons] at *; omega
    have ha : xs.length<n := by simp only [List.length_cons] at hn; omega
    let a : Fin n := ⟨xs.length,ha⟩
    have hI' : M.Indep (wordSet n (List.replicate xs.length false++false::ps)) := by
      simpa only [List.length_cons,wordSet_zero_succ] using hI
    have hbit : wordSet n (List.replicate xs.length false++true::ps)=
        insert a (wordSet n (List.replicate xs.length false++false::ps)) := by
      simpa [a] using wordSet_bit (n:=n) (List.replicate xs.length false) ps (by simpa using ha)
    have hbit' : wordSet n (xs.reverse++true::ps)=insert a (wordSet n (xs.reverse++false::ps)) := by
      simpa [a] using wordSet_bit (n:=n) xs.reverse ps (by simpa using ha)
    have hqueryLen : (List.replicate xs.length false++true::ps).length=n := by
      simp only [List.length_append,List.length_replicate,List.length_cons]
      simp only [List.length_cons] at hn
      omega
    cases b with
    | false => simpa [wordGreedy,List.reverse_cons,List.append_assoc] using ih (false::ps) hlen hI'
    | true =>
      cases hq : W (List.replicate xs.length false++true::ps) with
      | true =>
        have hJ := (hW _ hqueryLen).mp hq
        simpa [wordGreedy,hq,List.reverse_cons,List.append_assoc] using ih (true::ps) hlen hJ
      | false =>
        have hJ := ih (false::ps) (by simpa using hlen) hI'
        have han : ¬M.Indep (insert a (wordSet n (List.replicate xs.length false++false::ps))) := by
          rw [←hbit]
          intro h
          have := (hW _ hqueryLen).mpr h
          simp [hq] at this
        have hac : a ∈ M.closure (wordSet n (List.replicate xs.length false++false::ps)) :=
          hI'.mem_closure_iff'.mpr ⟨by simp [hE],fun h => (han h).elim⟩
        have hsub : wordSet n (List.replicate xs.length false++false::ps) ⊆ wordSet n (xs.reverse++false::ps) := by
          simpa using wordSet_zero_subset (n:=n) xs.reverse (false::ps)
        have hac' : a ∈ M.closure (wordSet n (wordGreedy W xs (false::ps))) := by
          rw [hJ.closure_eq_closure]
          exact M.closure_mono hsub hac
        have hB := hJ.indep.isBasis_of_subset_of_subset_closure
          (hJ.subset.trans (Set.subset_insert a _)) (Set.insert_subset hac' hJ.subset_closure)
        simpa [wordGreedy,hq,List.reverse_cons,List.append_assoc,hbit'] using hB

end

section

variable {k n : ℕ}
lemma popcount_value (xs ys : List Bool) :
    binaryValue (popcountBits xs ys)=binaryValue ys+xs.count true := by
  induction xs generalizing ys with
  | nil => simp [popcountBits]
  | cons b xs ih => cases b <;> simp [popcountBits,ih,incrementBits_correct,_root_.Nat.add_comm,_root_.Nat.add_assoc]

end

section
open scoped BigOperators Classical
variable {k n : ℕ}
lemma count_ofFn (n : ℕ) (f : Fin n → Bool) :
    (List.ofFn f).count true=∑i,if f i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,Fin.sum_univ_succ]
    cases hf : f 0 <;> simp [ih,Nat.add_comm]
lemma wordSet_card (xs : List Bool) (hn : xs.length=n) :
    Fintype.card (wordSet n xs)=xs.count true := by
  subst n
  let f : Fin xs.length → Bool := fun i => xs[i.val]
  have hf : List.ofFn f=xs := List.ofFn_getElem
  have hs : wordSet xs.length xs=wordSet xs.length (List.ofFn f) := congrArg (wordSet xs.length) hf.symm
  rw [hs,wordSet_ofFn,Fintype.card_subtype,Finset.card_filter]
  have hc := count_ofFn xs.length f
  rw [hf] at hc
  exact hc.symm
lemma wordGreedy_rank (M : Matroid (Fin n)) (hE : M.E=Set.univ)
    (W : List Bool → Bool) (hW : ∀l,l.length=n → (W l=true ↔ M.Indep (wordSet n l)))
    (xs : List Bool) (hn : xs.length=n) :
    (wordGreedy W xs []).count true=(M.eRk (wordSet n xs.reverse)).toNat := by
  have h := wordGreedy_basis M hE W hW xs [] (by simpa using hn)
    (by simp [wordSet_zeros])
  simp only [List.append_nil] at h
  have hh := h.encard_eq_eRk
  rw [Set.encard_eq_coe_toFinset_card] at hh
  have hc : (wordSet n (wordGreedy W xs [])).toFinset.card=(wordGreedy W xs []).count true := by
    rw [Set.toFinset_card]
    exact wordSet_card _ (by simpa [wordGreedy_length] using hn)
  rw [hc] at hh
  simpa using congrArg ENat.toNat hh

end

section

variable {k n : ℕ}

lemma binaryValue_append (xs ys : List Bool) :
    binaryValue (xs++ys)=binaryValue xs+2^xs.length*binaryValue ys := by
  induction xs with
  | nil => simp [binaryValue]
  | cons x xs ih =>
    simp only [List.cons_append,binaryValue,ih,List.length_cons,pow_succ]
    ring

end

end

namespace MachineCode

lemma binaryValue_bits (n : ℕ) : binaryValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [binaryValue,ih,Nat.bit]
    omega

lemma rankWord_correct {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (which : Bool) (x : Word) (hx : x.length=n) :
    rankWord O which x=((if which then M₂ else M₁).eRk (wordSet n x)).toNat := by
  simp only [rankWord,rankBits,popcount_value,binaryValue,Nat.zero_add]
  have hr := wordGreedy_rank (if which then M₂ else M₁) (by cases which <;> assumption)
    (wordOracle which O) (fun l _ => hO which (fun i => l[i.val]?.getD false)) x.reverse
    (by simpa only [List.length_reverse] using hx)
  simpa only [List.reverse_reverse] using hr
open scoped Classical in
lemma rankWord_eq_rankOracle {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (which : Bool) (x : Word) (hx : x.length=n) :
    rankWord O which x=rankOracle O which (wordSet n x).toFinset := by
  classical
  rw [rankWord_correct M₁ M₂ O hO hE₁ hE₂ which x hx,
    rankOracle_correct M₁ M₂ O hO hE₁ hE₂ which,Set.coe_toFinset]


lemma foldValue_eq_foldl {a b : DataType} (f : Value (.prod a b) → Option (Value b))
    (g : Value b → Value a → Value b) (hf : ∀ x z, f (x,z)=some (g z x))
    (xs : List (Value a)) (z : Value b) : foldValue f xs z=some (xs.foldl g z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih => simp [foldValue,hf,ih]

namespace Expression
variable {n : ℕ} (O : IndependenceOracle n)
lemma run_listReverse {a : DataType} (xs : List (Value a)) :
    run O listReverse xs=some xs.reverse := by
  simp only [listReverse,run]
  have h := foldValue_eq_foldl (fun p : Value (.prod a (.list a)) => some (p.1::p.2))
    (fun zs x => x::zs) (fun _ _ => rfl) xs []
  simpa using h
lemma run_mapStep {a b c : DataType} (p : Expression (.prod a c) b)
    (f : Value a → Value c → Value b) (hp : ∀ x z, run O p (x,z)=some (f x z))
    (x : Value a) (xs : List (Value b)) (z : Value c) :
    run O (mapStep p) (x,(xs,z))=some (f x z::xs,z) := by
  simp [mapStep,run,hp]
lemma run_mapWith {a b c : DataType} (p : Expression (.prod a c) b)
    (f : Value a → Value c → Value b) (hp : ∀ x z, run O p (x,z)=some (f x z))
    (xs : List (Value a)) (z : Value c) :
    run O (mapWith p) (xs,z)=some (xs.map (fun x => f x z)) := by
  have hf : ∀ (ys : List (Value a)) (acc : List (Value b)),
      foldValue (run O (mapStep p)) ys (acc,z)=some ((ys.map (fun x => f x z)).reverse++acc,z) := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons x ys ih => intro acc; simp [foldValue,run_mapStep O p f hp,ih,List.append_assoc]
  simp [mapWith,run,hf,run_listReverse]
lemma run_listLength {a : DataType} (xs : List (Value a)) :
    run O listLength xs=some xs.length := by
  have hf : ∀ (ys : List (Value a)) (z : ℕ),
      foldValue (fun p : Value (.prod a .nat) => some (p.2+1)) ys z=some (z+ys.length) := by
    intro ys
    induction ys with
    | nil => intro z; simp [foldValue]
    | cons x ys ih => intro z; simpa [foldValue,ih] using congrArg some (by omega : z+1+ys.length=z+(ys.length+1))
  simp [listLength,run,hf]
lemma run_wordLength (xs : Word) : run O wordLength xs=some xs.length := by
  simp [wordLength,run,run_listLength]
lemma run_wordRepeatStep (b : Bool) (w : Word) :
    run O wordRepeatStep (b,w)=some (if b then false::(w++w) else w++w) := by
  cases b <;> rfl
lemma unary_value (xs : List Bool) (w : Word) :
    ∃ out, foldValue (run O wordRepeatStep) xs.reverse w=some out ∧
      out.length=2^xs.length*w.length+binaryValue xs := by
  induction xs generalizing w with
  | nil => exact ⟨w,rfl,by simp [binaryValue]⟩
  | cons b xs ih =>
    obtain ⟨u,hu,hl⟩ := ih w
    have happ : ∀ (ys zs : List Bool) v,
        foldValue (run O wordRepeatStep) (ys++zs) v=
          (foldValue (run O wordRepeatStep) ys v).bind (foldValue (run O wordRepeatStep) zs) := by
      intro ys
      induction ys with
      | nil => intros; rfl
      | cons y ys ih => intros; simp [foldValue,ih,Option.bind_assoc]
    refine ⟨(if b then false::(u++u) else u++u),?_,?_⟩
    · rw [List.reverse_cons,happ,hu]
      simp only [Option.bind_some,foldValue]
      rw [run_wordRepeatStep]; rfl
    · cases b <;> simp [List.length_append,hl,binaryValue,Nat.pow_succ] <;> ring
lemma run_unary (m : ℕ) : ∃ w,run O unary m=some w ∧ w.length=m := by
  obtain ⟨w,hw,hlen⟩ := unary_value O m.bits []
  refine ⟨w,?_,?_⟩
  · simpa [unary,run] using hw
  · simpa [binaryValue_bits] using hlen
end Expression

lemma mod_double_lt (a b : ℕ) (hb : 0<b) (hba : b≤a) : 2*(a%b)<a := by
  have hr := Nat.mod_lt a hb
  have hd := Nat.div_pos hba hb
  have hm := Nat.mul_le_mul_left b hd
  have he := Nat.mod_add_div a b
  omega
lemma mod_size_lt (a b : ℕ) (hb : 0<b) (hba : b≤a) : (a%b).size<a.size := by
  have ha : 0<a := lt_of_lt_of_le hb hba
  by_cases hz : a%b=0
  · simpa [hz] using Nat.size_pos.mpr ha
  · have h := Nat.size_le_size (Nat.le_of_lt (mod_double_lt a b hb hba))
    have hs : (2*(a%b)).size=(a%b).size+1 := by
      have he : 2*(a%b)=Nat.bit false (a%b) := by simp [Nat.bit_val]
      rw [he,Nat.size_bit (by simpa [Nat.bit_val] using hz)]
    rw [hs] at h
    omega

lemma gcdSteps_zero (k a : ℕ) : gcdSteps k (a,0)=(a,0) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [gcdSteps,gcdStep] using ih
lemma gcdSteps_done (k a b : ℕ) (hba : b≤a) (hk : a.size+b.size≤k) :
    gcdSteps k (a,b)=(Nat.gcd a b,0) := by
  induction k generalizing a b with
  | zero =>
    have ha : a=0 := Nat.size_eq_zero.mp (by omega)
    have hb : b=0 := Nat.size_eq_zero.mp (by omega)
    simp [ha,hb,gcdSteps]
  | succ k ih =>
    by_cases hb : b=0
    · subst b; simp [gcdSteps_zero]
    · have hb' := Nat.pos_of_ne_zero hb
      have hl := mod_size_lt a b hb' hba
      have hs := Nat.size_le_size hba
      have hh := ih b (a%b) (Nat.le_of_lt (Nat.mod_lt a hb')) (by omega)
      simp only [gcdSteps,gcdStep,hb,ite_false]
      rw [hh,Nat.gcd_comm b (a%b),←Nat.gcd_rec,Nat.gcd_comm b a]

namespace Expression
lemma run_sortPair {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O sortPair (a,b)=some (if a<b then (b,a) else (a,b)) := by
  simp only [sortPair,applyIf,swap,run]
  by_cases h : a<b <;> simp [h]
lemma run_gcdStepCode {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O gcdStepCode (a,b)=some (gcdStep (a,b)) := by
  by_cases hb : b=0 <;>
    simp [gcdStepCode,applyIf,run,swap,natEqZero,natMod,natDivRem,gcdStep,hb]
lemma fold_gcdStepCode {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (p : ℕ × ℕ) :
    foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) xs p=some (gcdSteps xs.length p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons b xs ih =>
    rcases p with ⟨a,c⟩
    change ((run O gcdStepCode (a,c)).bind fun p =>
      foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) xs p)=_
    rw [run_gcdStepCode,Option.bind_some,ih]
    rfl
lemma run_gcdCode {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O gcdCode (a,b)=some (Nat.gcd a b) := by
  unfold gcdCode
  have hs := run_sortPair O a b
  simp only [run]
  rw [hs]
  simp only [Option.bind_some]
  by_cases hab : a<b
  · simp only [hab,ite_true]
    change ((foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) (b.bits++a.bits) (b,a)).bind
      fun p => some p.1)=some (Nat.gcd a b)
    rw [fold_gcdStepCode]
    simp only [List.length_append,Nat.size_eq_bits_len]
    rw [gcdSteps_done _ _ _ (Nat.le_of_lt hab) (by rfl)]
    simp [Nat.gcd_comm]
  · simp only [hab,ite_false]
    change ((foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) (a.bits++b.bits) (a,b)).bind
      fun p => some p.1)=some (Nat.gcd a b)
    rw [fold_gcdStepCode]
    simp only [List.length_append,Nat.size_eq_bits_len]
    rw [gcdSteps_done _ _ _ (Nat.le_of_not_gt hab) (by rfl)]
    rfl
end Expression

open Expression

open Expression

lemma rationalPair_div (a b : ℕ) : rationalPair ((a:ℚ)/(b:ℚ))=normalizePair a b := by
  have he : (a:ℚ)/(b:ℚ)=mkRat (a:ℤ) b := by
    simp only [Rat.mkRat_eq_divInt,Rat.divInt_eq_div,Int.cast_natCast]
  rw [he]
  by_cases hb : b=0 <;>
    simp [rationalPair,normalizePair,Rat.num_mkRat,Rat.den_mkRat,hb,Nat.gcd_comm,Int.natAbs_ediv_of_nonneg]
lemma rationalPair_value {q : ℚ} (hq : 0≤q) :
    ((rationalPair q).1:ℚ)/((rationalPair q).2:ℚ)=q := by
  dsimp [rationalPair]
  have hnum : 0≤q.num := Rat.num_nonneg.mpr hq
  have he : (q.num.natAbs:ℚ)=(q.num:ℚ) := by
    have hnat : (q.num.natAbs:ℤ)=q.num := Int.natAbs_of_nonneg hnum
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnat
  rw [he]
  exact Rat.num_div_den q
lemma rationalPair_den (q : ℚ) : 0<(rationalPair q).2 := q.den_pos

namespace Expression
lemma run_applyIf {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a .bool) (q r : Expression a b) (x : Value a) :
    run O (applyIf p q r) x=(run O p x).bind (fun t => if t then run O r x else run O q x) := by
  simp [applyIf,run,Option.bind_assoc]
lemma run_letIn {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression (.prod a b) c) (x : Value a) :
    run O (letIn p q) x=(run O p x).bind (fun y => run O q (x,y)) := by
  simp [letIn,run,Option.bind_assoc]

lemma run_normalizeRat {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O normalizeRat (a,b)=some (normalizePair a b) := by
  rw [normalizeRat,run_applyIf]
  change ((run O natEqZero b).bind fun t => if t then some (0,1) else _)=_
  rw [run_natEqZero]
  by_cases hb : b=0
  · simp [hb,normalizePair]
  · simp only [hb,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    rw [run_letIn,run_gcdCode]
    change (do
      let x ← run O natDiv (Nat.gcd a b,a)
      let y ← run O natDiv (Nat.gcd a b,b)
      pure (x,y))=some (normalizePair a b)
    rw [run_natDiv O _ _,run_natDiv O _ _]
    simp [normalizePair,hb]
lemma run_normalizeRat_pair {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O normalizeRat (a,b)=some (rationalPair ((a:ℚ)/(b:ℚ))) := by
  rw [rationalPair_div]
  exact run_normalizeRat O a b
lemma run_ratAdd_raw {n : ℕ} (O : IndependenceOracle n) (a b c d : ℕ) :
    run O ratAdd ((a,b),(c,d))=some (normalizePair (a*d+c*b) (b*d)) := by
  change run O normalizeRat (a*d+c*b,b*d)=_
  exact run_normalizeRat O _ _
lemma run_ratMul_raw {n : ℕ} (O : IndependenceOracle n) (a b c d : ℕ) :
    run O ratMul ((a,b),(c,d))=some (normalizePair (a*c) (b*d)) := by
  change run O normalizeRat (a*c,b*d)=_
  exact run_normalizeRat O _ _
lemma run_ratDiv_raw {n : ℕ} (O : IndependenceOracle n) (a b c d : ℕ) :
    run O ratDiv ((a,b),(c,d))=some (normalizePair (a*d) (c*b)) := by
  change run O normalizeRat (a*d,c*b)=_
  exact run_normalizeRat O _ _
lemma run_ratAdd {n : ℕ} (O : IndependenceOracle n) (q r : ℚ) (hq : 0≤q) (hr : 0≤r) :
    run O ratAdd (rationalPair q,rationalPair r)=some (rationalPair (q+r)) := by
  rw [run_ratAdd_raw,←rationalPair_div]
  congr 2
  conv_rhs => rw [←rationalPair_value hq,←rationalPair_value hr]
  push_cast
  have hb : (rationalPair q).2 ≠ 0 := (rationalPair_den q).ne'
  have hd : (rationalPair r).2 ≠ 0 := (rationalPair_den r).ne'
  field_simp
lemma run_ratMul {n : ℕ} (O : IndependenceOracle n) (q r : ℚ) (hq : 0≤q) (hr : 0≤r) :
    run O ratMul (rationalPair q,rationalPair r)=some (rationalPair (q*r)) := by
  rw [run_ratMul_raw,←rationalPair_div]
  congr 2
  conv_rhs => rw [←rationalPair_value hq,←rationalPair_value hr]
  push_cast
  ring
lemma run_ratDiv {n : ℕ} (O : IndependenceOracle n) (q r : ℚ) (hq : 0≤q) (hr : 0≤r) :
    run O ratDiv (rationalPair q,rationalPair r)=some (rationalPair (q/r)) := by
  rw [run_ratDiv_raw,←rationalPair_div]
  congr 2
  conv_rhs => rw [←rationalPair_value hq,←rationalPair_value hr]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring
lemma run_ratLess {n : ℕ} (O : IndependenceOracle n) (q r : ℚ) (hq : 0≤q) (hr : 0≤r) :
    run O ratLess (rationalPair q,rationalPair r)=some (decide (q<r)) := by
  change some (decide ((rationalPair q).1*(rationalPair r).2 <
    (rationalPair r).1*(rationalPair q).2))=some (decide (q<r))
  congr 2
  conv_rhs => rw [←rationalPair_value hq,←rationalPair_value hr]
  have hb : (0:ℚ)<(rationalPair q).2 := by exact_mod_cast rationalPair_den q
  have hd : (0:ℚ)<(rationalPair r).2 := by exact_mod_cast rationalPair_den r
  rw [div_lt_div_iff₀ hb hd]
  norm_cast
lemma run_ratMinOne {n : ℕ} (O : IndependenceOracle n) (q : ℚ) (hq : 0≤q) :
    run O ratMinOne (rationalPair q)=some (rationalPair (min 1 q)) := by
  have hv := rationalPair_value hq
  have hd : (0:ℚ)<(rationalPair q).2 := by exact_mod_cast rationalPair_den q
  have hcmp : (rationalPair q).2<(rationalPair q).1 ↔ (1:ℚ)<q := by
    conv_rhs => rw [←hv,lt_div_iff₀ hd,one_mul]
    norm_cast
  by_cases h : 1<q
  · have he := hcmp.mpr h
    simp only [ratMinOne,run_applyIf]
    change (if decide ((rationalPair q).2 < (rationalPair q).1) then some (1,1) else some (rationalPair q))=_
    rw [ite_eq_left (by simpa using he),min_eq_left (le_of_lt h)]
    rfl
  · have he : ¬(rationalPair q).2<(rationalPair q).1 := mt hcmp.mp h
    simp only [ratMinOne,run_applyIf]
    change (if decide ((rationalPair q).2 < (rationalPair q).1) then some (1,1) else some (rationalPair q))=_
    rw [ite_eq_right (by simpa using he),min_eq_right (le_of_not_gt h)]

lemma foldValue_iterate {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (xs : List Bool) (z : Value a) :
    foldValue (run O (Expression.snd (a:=.bool) >>> p)) xs z=some ((f^[xs.length]) z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons b xs ih =>
    change ((run O p z).bind fun y => foldValue (run O (Expression.snd (a:=.bool) >>> p)) xs y)=_
    rw [hp,Option.bind_some,ih]
    rfl
lemma run_iterateWord {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (w : Word) (z : Value a) :
    run O (iterateWord p) (w,z)=some ((f^[w.length]) z) := by
  change foldValue (run O (Expression.snd (a:=.bool) >>> p)) w z=_
  exact foldValue_iterate O p f hp w z
lemma run_iterateNat {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (k : ℕ) (z : Value a) :
    run O (iterateNat p) (k,z)=some ((f^[k]) z) := by
  obtain ⟨w,hw,hlen⟩ := run_unary O k
  simp only [iterateNat,onLeft,run,Option.bind_some]
  rw [hw]
  change run O (iterateWord p) (w,z)=_
  rw [run_iterateWord O p f hp,hlen]
lemma run_fromList {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) :
    run O fromList xs=some xs := by
  simp only [fromList,run]
  rw [run_listReverse]
  change foldValue (run O consBit) xs.reverse []=some xs
  have hh := foldValue_eq_foldl (run O consBit) (fun z x => x::z) (fun _ _ => rfl) xs.reverse []
  simpa using hh

lemma rangeStep_iterate (k : ℕ) : (rangeStep^[k]) (0,[])=(k,(List.range k).reverse) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; simp [rangeStep,List.range_succ]
lemma run_rangeCode {n : ℕ} (O : IndependenceOracle n) (k : ℕ) :
    run O rangeCode k=some (List.range k) := by
  have hh := run_iterateNat O rangeStepCode rangeStep (fun _ => rfl) k (0,[])
  change ((run O (iterateNat rangeStepCode) (k,(0,[]))).bind fun p => run O listReverse p.2)=_
  rw [hh,rangeStep_iterate,Option.bind_some,run_listReverse,List.reverse_reverse]

lemma run_splitStep {n : ℕ} (O : IndependenceOracle n) {a : DataType} (x : Value a)
    (k : ℕ) (u v : List (Value a)) : run O splitStep (x,(k,(u,v)))=some (splitStepValue (x,(k,(u,v)))) := by
  rw [splitStep,run_applyIf]
  change ((run O natEqZero k).bind fun t => if t then _ else _)=_
  rw [run_natEqZero]
  by_cases hk : k=0
  · subst k; rfl
  · simp only [hk,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    change ((run O natSub (k,1)).bind fun j => some (j,(x::u,v)))=_
    rw [run_natSub]
    simp [splitStepValue,hk]
lemma fold_splitStep {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a))
    (k : ℕ) (u v : List (Value a)) :
    foldValue (run O splitStep) xs (k,(u,v))=
      some (k-xs.length,((xs.take k).reverse++u,(xs.drop k).reverse++v)) := by
  induction xs generalizing k u v with
  | nil => simp [foldValue]
  | cons x xs ih =>
    rw [foldValue,run_splitStep]
    cases k with
    | zero => simpa [splitStepValue,List.append_assoc] using ih 0 u (x::v)
    | succ k => simpa [splitStepValue,List.append_assoc] using ih k (x::u) v
lemma run_splitAtCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O splitAtCode (xs,k)=some (xs.take k,xs.drop k) := by
  change ((foldValue (run O splitStep) xs (k,([],[]))).bind fun p => do
    let x ← run O listReverse p.2.1
    let y ← run O listReverse p.2.2
    pure (x,y))=_
  rw [fold_splitStep]
  simp only [List.append_nil,Option.bind_some]
  rw [run_listReverse,run_listReverse]
  simp
lemma run_takeCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O takeCode (xs,k)=some (xs.take k) := by
  change ((run O splitAtCode (xs,k)).bind fun p => some p.1)=_
  rw [run_splitAtCode]; rfl
lemma run_dropCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O dropCode (xs,k)=some (xs.drop k) := by
  change ((run O splitAtCode (xs,k)).bind fun p => some p.2)=_
  rw [run_splitAtCode]; rfl

lemma run_compose {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression b c) (x : Value a) :
    run O (p >>> q) x=(run O p x).bind (run O q) := rfl
lemma run_both {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression a c) (x : Value a) :
    run O (both p q) x=(run O p x).bind (fun y => (run O q x).map (fun z => (y,z))) := by
  simp only [run]
  congr 1
  funext y
  cases run O q x <;> rfl

lemma foldLast_append {A : Type*} (xs ys : List A) (d : A) :
    foldLast (xs++ys) d=foldLast ys (foldLast xs d) := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih => exact ih x
lemma foldLast_reverse {A : Type*} (xs : List A) (d : A) :
    foldLast xs.reverse d=xs.headD d := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [List.reverse_cons,foldLast_append,foldLast]
lemma run_headD {n : ℕ} (O : IndependenceOracle n) {a} (xs : List (Value a)) (d : Value a) :
    run O headD (xs,d)=some (xs.headD d) := by
  have hf : ∀ (ys : List (Value a)) (z : Value a),
      foldValue (run O (fst (b:=a))) ys z=some (foldLast ys z) := by
    intro ys
    induction ys with
    | nil => intro z; rfl
    | cons y ys ih => intro z; exact ih y
  simp only [headD,onLeft,run,run_listReverse]
  change foldValue (run O (fst (b:=a))) xs.reverse d=_
  rw [hf,foldLast_reverse]
lemma run_getDCode {n : ℕ} (O : IndependenceOracle n) {a} (xs : List (Value a)) (k : ℕ) (d : Value a) :
    run O getDCode ((xs,k),d)=some (xs.getD k d) := by
  simp [getDCode,run]
  rw [run_dropCode O xs k]
  change run O headD (xs.drop k,d)=_
  rw [run_headD]
  congr 1
  induction k generalizing xs with
  | zero => cases xs <;> rfl
  | succ k ih => cases xs with
    | nil => rfl
    | cons x xs => exact ih xs
lemma run_boolOr {n : ℕ} (O : IndependenceOracle n) (x y : Bool) :
    run O boolOr (x,y)=some (x||y) := by cases x <;> rfl
lemma run_natEqual {n : ℕ} (O : IndependenceOracle n) (x y : ℕ) :
    run O natEqual (x,y)=some (decide (x=y)) := by
  simp [natEqual,run,swap]
  rw [run_boolOr]
  simp only [Option.bind_some]
  congr 1
  by_cases h : x=y
  · subst y; simp
  · have hn : x<y ∨ y<x := by omega
    rcases hn with hh|hh <;> simp [h,hh]
lemma run_listAll {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) :
    run O listAll xs=some (xs.all id) := by
  have hf : ∀ (ys : List Bool) (z : Bool),
      foldValue (run O boolAnd) ys z=some (z && ys.all id) := by
    intro ys
    induction ys with
    | nil => intro z; cases z <;> rfl
    | cons y ys ih =>
      intro z
      change ((run O boolAnd (y,z)).bind (foldValue (run O boolAnd) ys))=_
      rw [run_boolAnd,Option.bind_some,ih]
      cases z <;> cases y <;> simp
  change foldValue (run O boolAnd) xs true=_
  simpa using hf xs true
lemma run_filterStep {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression (.prod a b) .bool)
    (f : Value a → Value b → Bool) (hp : ∀ x z,run O p (x,z)=some (f x z))
    (x : Value a) (ys : List (Value a)) (z : Value b) :
    run O (filterStep p) (x,(ys,z))=some ((if f x z then x::ys else ys),z) := by
  simp only [filterStep,run_both,run_applyIf]
  change ((run O p (x,z)).bind fun t => if t then some (x::ys) else some ys).bind
    (fun v => (some z).map (fun w => (v,w)))=_
  rw [hp]
  cases f x z <;> rfl
lemma run_filterWith {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression (.prod a b) .bool)
    (f : Value a → Value b → Bool) (hp : ∀ x z,run O p (x,z)=some (f x z))
    (xs : List (Value a)) (z : Value b) :
    run O (filterWith p) (xs,z)=some (xs.filter (fun x => f x z)) := by
  have hf : ∀ (ys acc : List (Value a)),
      foldValue (run O (filterStep p)) ys (acc,z)=some ((ys.filter (fun x => f x z)).reverse++acc,z) := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons y ys ih =>
      intro acc
      rw [foldValue,run_filterStep O p f hp,Option.bind_some]
      cases h : f y z <;> simp [h,ih,List.append_assoc]
  change ((foldValue (run O (filterStep p)) xs ([],z)).bind fun yz => run O listReverse yz.1)=_
  rw [hf]
  change run O listReverse ((xs.filter (fun x => f x z)).reverse++[])=_
  rw [List.append_nil,run_listReverse,List.reverse_reverse]

lemma run_powCode {n : ℕ} (O : IndependenceOracle n) (a k : ℕ) :
    run O powCode (a,k)=some (a^k) := by
  let f : ℕ×ℕ → ℕ×ℕ := fun z => (z.1,z.1*z.2)
  have hi : ∀ j v,(f^[j]) (a,v)=(a,a^j*v) := by
    intro j
    induction j with
    | zero => intro v; simp [f]
    | succ j ih => intro v; rw [Function.iterate_succ_apply',ih]; simp [f,pow_succ]; ring
  have hh := run_iterateNat O powStepCode f (fun _ => rfl) k (a,1)
  simp [powCode,run,hh,hi]

lemma run_ratPowCode {n : ℕ} (O : IndependenceOracle n) (q : ℚ) (hq : 0≤q) (k : ℕ) :
    run O ratPowCode (rationalPair q,k)=some (rationalPair (q^k)) := by
  simp [ratPowCode,run]
  rw [run_powCode O _ _,run_powCode O _ _]
  change run O normalizeRat ((rationalPair q).1^k,(rationalPair q).2^k)=_
  rw [run_normalizeRat_pair]
  congr 2
  conv_rhs => rw [←rationalPair_value hq]
  push_cast
  rw [div_pow]
end Expression

open Expression

open Expression
lemma wordSet_not {n : ℕ} (x : Word) (hx : x.length=n) :
    wordSet n (x.map Bool.not)=(wordSet n x)ᶜ := by
  ext i
  simp only [wordSet,Set.mem_ofPred_eq,Set.mem_compl_iff]
  have hi : i.val<x.length := by omega
  rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem (by simpa using hi),List.getElem_map]
  cases x[i.val] <;> simp

namespace Expression

lemma run_wordGet {n : ℕ} (O : IndependenceOracle n) (x : Word) (j : ℕ) :
    run O wordGet (x,j)=some (x[j]?.getD false) := by
  change run O (getDCode (a:=.bool)) ((x,j),false)=_
  exact run_getDCode O (a:=.bool) x j false
lemma run_wordNot {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    run O wordNot x=some (x.map Bool.not) := by
  change ((run O (mapWith (c:=.unit) (fst >>> boolNot)) (x,())).bind (run O fromList))=_
  rw [run_mapWith O _ (fun b (_ : Unit) => !b) (by intro b z; exact run_boolNot O b)]
  change run O fromList (x.map Bool.not)=_
  exact run_fromList O _
lemma run_wordCount {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    run O wordCount x=some (x.count true) := by
  have hf : ∀ (xs : Word) k,foldValue (run O wordCountStep) xs k=some (k+xs.count true) := by
    intro xs
    induction xs with
    | nil => intro k; simp [foldValue]
    | cons b xs ih =>
      intro k
      cases b with
      | false =>
        change foldValue (run O wordCountStep) xs k=some (k+(false::xs).count true)
        rw [ih]; simp
      | true =>
        change foldValue (run O wordCountStep) xs (k+1)=some (k+(true::xs).count true)
        rw [ih]; simp [Nat.add_comm,Nat.add_left_comm]
  change foldValue (run O wordCountStep) x 0=_
  simpa using hf x 0

lemma run_deficiencyCode {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (x y : Word)
    (hx : x.length=n) (hy : y.length=n) :
    run O deficiencyCode (r,(x,y))=
      some (n+r-(rankWord O false x+y.count true+rankWord O true (y.map Bool.not))) := by
  simp only [deficiencyCode,run_compose,run_both]
  simp [run,run_wordLength,run_wordCount,run_wordNot,hx,hy]
  rw [run_natSub]
end Expression

open scoped Classical in
lemma deficiencyCode_source {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r : ℕ) (x y : Word) (hx : x.length=n) (hy : y.length=n) :
    run O Expression.deficiencyCode (r,(x,y))=some (oracleDeficiency n r O (representedState n (x,y))) := by
  rw [Expression.run_deficiencyCode O r x y hx hy]
  unfold oracleDeficiency pairedDeficiencyOracle
  rw [representedState_preinl,representedState_preinr,
    rankWord_eq_rankOracle M₁ M₂ O hO hE₁ hE₂ false x hx,
    rankWord_eq_rankOracle M₁ M₂ O hO hE₁ hE₂ true (y.map Bool.not) (by simpa using hy),
    wordSet_not y hy]
  rw [Set.toFinset_compl]
  have hc : (wordSet n y).toFinset.card=y.count true := by
    simpa using wordSet_card y hy
  simp only [hc]

lemma foldValue_append {A B : Type*} (f : A×B → Option B) (xs ys : List A) (z : B) :
    foldValue f (xs++ys) z=(foldValue f xs z).bind (foldValue f ys) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,foldValue,ih,Option.bind_assoc]

namespace Expression
lemma run_wordTake {n : ℕ} (O : IndependenceOracle n) (x : Word) (k : ℕ) :
    run O wordTake (x,k)=some (x.take k) := by
  change ((run O (takeCode (a:=.bool)) (x,k)).bind (run O fromList))=_
  rw [run_takeCode]; exact run_fromList O _
lemma run_rejectStep {n : ℕ} (O : IndependenceOracle n) (x : Word) (v k : ℕ) (z : Bool×ℕ) :
    run O rejectStep (x,((v,k),z))=some ((v,k),
      if binaryValue (x.take k).reverse<v then (true,binaryValue (x.take k).reverse) else z) := by
  simp only [rejectStep,run_both,run_letIn,run_compose,run_fst,run_snd,run_constant,
    run_reverse,run_toNat,run_applyIf,Option.bind_some,Option.map_some]
  rw [run_wordTake O x k]
  by_cases h : binaryValue (x.take k).reverse<v <;> simp [run,h]
lemma fold_reject {n : ℕ} (O : IndependenceOracle n) (v k : ℕ) (xs : List Word) (z : Bool×ℕ) :
    foldValue (run O rejectStep) xs.reverse ((v,k),z)=
      some ((v,k),match rejectValue v k xs with | none => z | some y => (true,y)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons,foldValue_append,ih]
    simp only [Option.bind_some,foldValue]
    rw [run_rejectStep]
    simp only [Option.bind_some]
    change _=some ((v,k),match rejectValue v k (x::xs) with | none => z | some y => (true,y))
    simp only [rejectValue]
    split_ifs <;> rfl
lemma run_rejectCode {n : ℕ} (O : IndependenceOracle n) (xs : List Word) (v k : ℕ) :
    run O rejectCode (xs,(v,k))=some (optionData 0 (rejectValue v k xs)) := by
  simp only [rejectCode,run_compose,run_both,run_fst,run_snd,run_constant,Option.bind_some,
    run_listReverse,Option.map_some]
  change ((foldValue (run O rejectStep) xs.reverse ((v,k),(false,0))).bind fun z => some z.2)=_
  rw [fold_reject]
  cases rejectValue v k xs <;> rfl
end Expression

lemma binaryValue_ofFn_reverse (h : ℕ) (bits : BitWord h) :
    binaryValue (List.ofFn bits).reverse=(wordEquiv h bits).val := by
  induction h with
  | zero => simp [wordEquiv,binaryValue]
  | succ h ih =>
    rw [List.ofFn_succ,List.reverse_cons,binaryValue_append]
    simp only [List.length_reverse,List.length_ofFn,ih,binaryValue]
    simp [wordEquiv,Equiv.trans_apply,Fin.consEquiv,finProdFinEquiv,finTwoEquiv]
    cases bits 0 <;> simp <;> rfl

lemma ofFn_bitPrefix (h H : ℕ) (hh : h≤H) (bits : BitWord H) :
    List.ofFn (bitPrefix h H hh bits)=(List.ofFn bits).take h := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    simp [bitPrefix]

lemma rejectValue_prefix (v h H D : ℕ) (hh : h≤H) (bits : Fin D → BitWord H) :
    Expression.rejectValue v h (List.ofFn (fun i => List.ofFn (bits i)))=
      (boundedUniform v h D (fun i => bitPrefix h H hh (bits i))).map Fin.val := by
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [List.ofFn_succ]
    simp only [Expression.rejectValue,←ofFn_bitPrefix h H hh,binaryValue_ofFn_reverse,boundedUniform]
    split_ifs <;> first | rfl | exact ih (Fin.tail bits)

lemma bankEval_bind {A B : Type*} (t : DrawTree A) (f : A → DrawTree B) (bank : Bank) :
    bankEval (t.bind f) bank=
      match bankEval t bank with
      | (none,rest) => (none,rest)
      | (some a,rest) => bankEval (f a) rest := by
  induction t generalizing bank with
  | leaf a => rfl
  | draw v k ih =>
    cases bank with
    | nil => rfl
    | cons rows bank =>
      simp only [DrawTree.bind,bankEval]
      split <;> first | rfl | exact ih _ bank
lemma bankEval_map {A B : Type*} (t : DrawTree A) (f : A → B) (bank : Bank) :
    bankEval (t.map f) bank=((bankEval t bank).1.map f,(bankEval t bank).2) := by
  rw [DrawTree.map,bankEval_bind]
  cases bankEval t bank with
  | mk o rest => cases o <;> rfl

lemma bankEncode_succ {H D M : ℕ} (bits : Fin (M+1) → Fin D → BitWord H) :
    bankEncode bits=List.ofFn (fun d => List.ofFn (bits 0 d))::bankEncode (Fin.tail bits) := by
  exact List.ofFn_succ
lemma bankEval_run {A : Type*} (H D M : ℕ) (t : DrawTree A) (ht : DrawTree.Fits H M t)
    (bits : Fin M → Fin D → BitWord H) :
    (bankEval t (bankEncode bits)).1=DrawTree.run H D M t bits := by
  induction t generalizing M with
  | leaf a => cases M <;> rfl
  | draw v k ih =>
    cases M with
    | zero => exact False.elim ht
    | succ M =>
      rw [bankEncode_succ]
      simp only [bankEval,DrawTree.run,dite_eq_left ht.1]
      have he := rejectValue_prefix (v+1) (Nat.clog 2 (v+1)) H D ht.1 (bits 0)
      cases hu : boundedUniform (v+1) (Nat.clog 2 (v+1)) D
          (fun i => bitPrefix _ H ht.1 (bits 0 i)) with
      | none =>
        simp only [hu,Option.map_none] at he
        split
        · rfl
        · rename_i i hi
          have hh := he.symm.trans hi
          cases hh
      | some i =>
        simp only [hu,Option.map_some] at he
        split
        · rename_i hi
          have hh := he.symm.trans hi
          cases hh
        · rename_i j hj
          have hh := Option.some.inj (he.symm.trans hj)
          subst j
          exact ih i M (ht.2 i) (Fin.tail bits)

open Expression

namespace Expression
lemma clog_two_size_pred (v : ℕ) : Nat.clog 2 v=(v-1).size := by
  apply Nat.le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by norm_num)).mpr
    have h := Nat.lt_size_self (v-1)
    omega
  · apply Nat.size_le.mpr
    have h := Nat.le_pow_clog (by norm_num : 1<2) v
    have hp : 0<2^(Nat.clog 2 v) := by positivity
    omega

lemma run_clogCode {n : ℕ} (O : IndependenceOracle n) (v : ℕ) :
    run O clogCode v=some (Nat.clog 2 v) := by
  simp only [clogCode,run_compose,run_both,run_ident,run_constant,Option.bind_some,Option.map_some]
  rw [run_natSub]
  change run O wordLength (v-1).bits=_
  rw [run_wordLength,Nat.size_eq_bits_len,clog_two_size_pred]

end Expression
open Expression
namespace Effect

lemma run_pure {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression a b)
    (x : Value a) (y : Value b) (bank : Bank) (hp : run O p x=some y) :
    run O (pure p) (x,bank)=some (optionalValue b (some y),bank) := by
  simp only [pure,run_both,run_compose,run_fst,run_snd,run_constant,
    Option.bind_some,hp,Option.map_some]
  rfl
lemma run_bind {n : ℕ} (O : IndependenceOracle n) {a b c} (p : Effect a b) (q : Effect b c)
    (x : Value a) (bank rest : Bank) (y : Option (Value b))
    (hp : run O p (x,bank)=some (optionalValue b y,rest)) :
    run O (bind p q) (x,bank)=
      match y with
      | none => some (optionalValue c none,rest)
      | some z => run O q (z,rest) := by
  cases y <;> dsimp only <;> rw [bind,run_compose,hp,Option.bind_some,run_applyIf] <;> rfl
lemma run_keep {n : ℕ} (O : IndependenceOracle n) {a b} (p : Effect a b)
    (x : Value a) (bank rest : Bank) (y : Value b)
    (hp : run O p (x,bank)=some (optionalValue b (some y),rest)) :
    run O (keep p) (x,bank)=some (optionalValue (.prod a b) (some (x,y)),rest) := by
  rw [keep,run_letIn,hp]
  rfl
lemma run_draw {n : ℕ} (O : IndependenceOracle n) (v : ℕ) (bank : Bank) :
    run O draw (v,bank)=some (optionData 0
      (Expression.rejectValue v (Nat.clog 2 v) (bank.headD [])),bank.drop 1) := by
  simp only [draw,run_both,run_compose,run_fst,run_snd,run_ident,run_constant,Option.bind_some,Option.map_some]
  rw [run_headD,run_clogCode,run_dropCode]
  simp only [Option.bind_some,Option.map_some]
  rw [run_rejectCode]
  rfl

lemma realizes_pure {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b : DataType}
    (p : Expression a b) (encode : A → Value b) (x : Value a) (y : A)
    (hp : run O p x=some (encode y)) : Realizes O (pure p) encode x (.leaf y) := by
  intro bank
  exact run_pure O p x (encode y) bank hp

lemma realizes_bind {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c : DataType}
    (p : Effect a b) (q : Effect b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : Realizes O p ea x t) (hq : ∀ y,Realizes O q eb (ea y) (f y)) :
    Realizes O (bind p q) eb x (t.bind f) := by
  intro bank
  rw [bankEval_bind]
  cases ht : bankEval t bank with
  | mk out rest =>
    have hh := hp bank
    rw [ht] at hh
    cases out with
    | none => exact run_bind O p q x bank rest none hh
    | some y =>
      rw [run_bind O p q x bank rest (some (ea y)) hh]
      exact hq y rest

lemma realizes_keep {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b : DataType}
    (p : Effect a b) (ea : A → Value b) (x : Value a) (t : DrawTree A)
    (hp : Realizes O p ea x t) :
    Realizes O (keep p) (fun y => (x,ea y)) x t := by
  intro bank
  have hh := hp bank
  cases ht : bankEval t bank with
  | mk out rest =>
    rw [ht] at hh
    cases out with
    | none => rw [keep,run_letIn,hh]; rfl
    | some y => exact run_keep O p x bank rest (ea y) hh

lemma realizes_letIn {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c : DataType}
    (p : Effect a b) (q : Effect (.prod a b) c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : Realizes O p ea x t) (hq : ∀ y,Realizes O q eb (x,ea y) (f y)) :
    Realizes O (letIn p q) eb x (t.bind f) :=
  realizes_bind O (keep p) q _ eb x t f (realizes_keep O p ea x t hp) hq

lemma realizes_draw {n : ℕ} (O : IndependenceOracle n) (v : ℕ) :
    Realizes O draw Fin.val (v+1) (.draw v DrawTree.leaf) := by
  intro bank
  rw [run_draw]
  cases bank with
  | nil => rfl
  | cons rows bank =>
    simp only [bankEval]
    split
    · rename_i hi
      simp only [List.headD_cons,List.drop_succ_cons,List.drop_zero,hi,Option.map_none]
      rfl
    · rename_i i hi
      simp only [List.headD_cons,List.drop_succ_cons,List.drop_zero,hi,Option.map_some]
      rfl

lemma run_precompose {n : ℕ} (O : IndependenceOracle n) {a b c} (p : Expression a b)
    (q : Effect b c) (x : Value a) (y : Value b) (bank : Bank)
    (hp : run O p x=some y) : run O (precompose p q) (x,bank)=run O q (y,bank) := by
  simp only [precompose,onLeft,run_compose,run_both,run_fst,run_snd,Option.bind_some,hp,Option.map_some]

lemma realizes_precompose {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Expression a b) (q : Effect b c) (ea : A → Value c) (x : Value a) (y : Value b)
    (t : DrawTree A) (hp : run O p x=some y) (hq : Realizes O q ea y t) :
    Realizes O (precompose p q) ea x t := by
  intro bank
  rw [run_precompose O p q x y bank hp]
  exact hq bank

lemma run_choose {n : ℕ} (O : IndependenceOracle n) {a b} (test : Expression a .bool)
    (p q : Effect a b) (x : Value a) (bank : Bank) (v : Bool)
    (ht : run O test x=some v) :
    run O (choose test p q) (x,bank)=if v then run O q (x,bank) else run O p (x,bank) := by
  rw [choose,run_applyIf]
  change ((run O test x).bind fun v => if v then _ else _)=_
  rw [ht,Option.bind_some]

lemma realizes_map {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a b) (q : Expression b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → B)
    (hp : Realizes O p ea x t) (hq : ∀ y,run O q (ea y)=some (eb (f y))) :
    Realizes O (map p q) eb x (t.map f) :=
  realizes_bind O p (pure q) ea eb x t (fun y => .leaf (f y)) hp
    (fun y => realizes_pure O q eb (ea y) (f y) (hq y))
end Effect

lemma iterateM_some {A : Type*} (f : A → Option A) (x : A) (h : f x=some x) (k : ℕ) :
    iterateM f k x=some x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterateM,h,Option.bind_some,ih]
namespace Expression
lemma run_iterateNatM {n : ℕ} (O : IndependenceOracle n) {a : DataType}
    (p : Expression a a) (k : ℕ) (x : Value a) :
    run O (iterateNat p) (k,x)=iterateM (run O p) k x := by
  have hf : ∀ (w : Word) (z : Value a),
      foldValue (run O (Expression.snd (a:=.bool) >>> p)) w z=iterateM (run O p) w.length z := by
    intro w
    induction w with
    | nil => intro z; rfl
    | cons b w ih =>
      intro z
      change ((run O p z).bind (foldValue (run O (Expression.snd (a:=.bool) >>> p)) w))=_
      simp only [List.length_cons,iterateM]
      congr 1
      funext v
      exact ih v
  obtain ⟨w,hw,hlen⟩ := run_unary O k
  simp only [iterateNat,onLeft,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [hw]
  change foldValue (run O (Expression.snd (a:=.bool) >>> p)) w x=_
  rw [hf,hlen]
end Expression
namespace Effect

lemma run_loopStep_none {n : ℕ} (O : IndependenceOracle n) {a} (p : Effect a a) (bank : Bank) :
    run O (loopStep p) (optionalValue a none,bank)=some (optionalValue a none,bank) := rfl
lemma run_loopStep_some {n : ℕ} (O : IndependenceOracle n) {a} (p : Effect a a)
    (x : Value a) (bank : Bank) :
    run O (loopStep p) (optionalValue a (some x),bank)=run O p (x,bank) := rfl
lemma run_repeat {n : ℕ} (O : IndependenceOracle n) {a} (p : Effect a a)
    (k : ℕ) (x : Value a) (bank : Bank) :
    run O (repeatCode p) ((k,x),bank)=iterateM (run O (loopStep p)) k (optionalValue a (some x),bank) := by
  change run O (iterateNat (loopStep p)) (k,(optionalValue a (some x),bank))=_
  exact run_iterateNatM O _ _ _

lemma realizes_repeat {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a}
    (p : Effect a a) (ea : A → Value a) (f : A → DrawTree A)
    (hp : ∀ x,Realizes O p ea (ea x) (f x)) (k : ℕ) (x : A) :
    Realizes O (repeatCode p) ea (k,ea x) (treeRepeat f k x) := by
  intro bank
  rw [run_repeat]
  induction k generalizing x bank with
  | zero => rfl
  | succ k ih =>
    rw [iterateM,run_loopStep_some,hp x bank,Option.bind_some,treeRepeat,bankEval_bind]
    cases ht : bankEval (f x) bank with
    | mk out rest =>
      cases out with
      | none =>
        simpa only [Option.map_none] using iterateM_some (run O (loopStep p))
          (optionalValue a none,rest) (run_loopStep_none O p rest) k
      | some y => exact ih y rest

end Effect
end MachineCode

namespace DrawTree
variable {A B : Type*}
lemma Reindexed.trans {t u v : DrawTree A} (h : Reindexed t u) (g : Reindexed u v) :
    Reindexed t v := by
  induction h generalizing v with
  | leaf a => cases g; exact .leaf a
  | draw m k l e h ih =>
    cases g with
    | draw _ _ z f gz =>
      exact .draw m k z (e.trans f) (fun i => ih i (gz (e i)))
end DrawTree
namespace MachineCode
open Expression
namespace Effect

lemma Realizes.law {n : ℕ} {O : IndependenceOracle n} {A : Type*} {a b} {p : Effect a b}
    {e : A → Value b} {x : Value a} {t : DrawTree A} (h : Realizes O p e x t) :
    RealizesLaw O p e x t := ⟨t,.refl t,h⟩
lemma RealizesLaw.reindex {n : ℕ} {O : IndependenceOracle n} {A : Type*} {a b}
    {p : Effect a b} {e : A → Value b} {x : Value a} {t u : DrawTree A}
    (h : RealizesLaw O p e x u) (ht : DrawTree.Reindexed t u) : RealizesLaw O p e x t := by
  rcases h with ⟨v,hv,hp⟩
  exact ⟨v,ht.trans hv,hp⟩
lemma law_bind {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a b) (q : Effect b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : RealizesLaw O p ea x t) (hq : ∀ y,RealizesLaw O q eb (ea y) (f y)) :
    RealizesLaw O (bind p q) eb x (t.bind f) := by
  classical
  rcases hp with ⟨u,hu,hp⟩
  choose g hg hq using hq
  exact ⟨u.bind g,hu.bind hg,realizes_bind O p q ea eb x u g hp hq⟩
lemma law_letIn {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a b) (q : Effect (.prod a b) c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : RealizesLaw O p ea x t) (hq : ∀ y,RealizesLaw O q eb (x,ea y) (f y)) :
    RealizesLaw O (letIn p q) eb x (t.bind f) := by
  classical
  rcases hp with ⟨u,hu,hp⟩
  choose g hg hq using hq
  exact ⟨u.bind g,hu.bind hg,realizes_letIn O p q ea eb x u g hp hq⟩
lemma law_precompose {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Expression a b) (q : Effect b c) (ea : A → Value c) (x : Value a) (y : Value b)
    (t : DrawTree A) (hp : run O p x=some y) (hq : RealizesLaw O q ea y t) :
    RealizesLaw O (precompose p q) ea x t := by
  rcases hq with ⟨u,hu,hq⟩
  exact ⟨u,hu,realizes_precompose O p q ea x y u hp hq⟩
lemma law_map {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a b) (q : Expression b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → B)
    (hp : RealizesLaw O p ea x t) (hq : ∀ y,run O q (ea y)=some (eb (f y))) :
    RealizesLaw O (map p q) eb x (t.map f) := by
  rcases hp with ⟨u,hu,hp⟩
  exact ⟨u.map f,hu.map f,realizes_map O p q ea eb x u f hp hq⟩
lemma law_choose {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b}
    (test : Expression a .bool) (p q : Effect a b) (ea : A → Value b)
    (x : Value a) (t : DrawTree A) (v : Bool) (ht : run O test x=some v)
    (h : RealizesLaw O (if v then q else p) ea x t) :
    RealizesLaw O (choose test p q) ea x t := by
  rcases h with ⟨u,hu,hp⟩
  refine ⟨u,hu,fun bank => ?_⟩
  rw [run_choose O test p q x bank v ht]
  cases v <;> exact hp bank
end Effect
end MachineCode

namespace DrawTree
variable {A B C : Type*}
lemma bind_leaf (t : DrawTree A) : t.bind leaf=t := by
  induction t with
  | leaf a => rfl
  | draw v f ih => simp only [bind,ih]
lemma map_bind (t : DrawTree A) (f : A → B) (g : B → DrawTree C) :
    (t.map f).bind g=t.bind (fun a => g (f a)) := by
  rw [DrawTree.map,bind_assoc]
  rfl
lemma bind_map (t : DrawTree A) (f : A → DrawTree B) (g : B → C) :
    (t.bind f).map g=t.bind (fun a => (f a).map g) := bind_assoc t f _
lemma map_map (t : DrawTree A) (f : A → B) (g : B → C) :
    (t.map f).map g=t.map (g ∘ f) := map_bind t f _
end DrawTree
namespace MachineCode

open Expression

namespace Effect

lemma law_some {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b} (p : Effect a b)
    (ea : A → Value b) (x : Value a) (t : DrawTree A) (h : RealizesLaw O p ea x t) :
    RealizesLaw O (someCode p) (optionEncode ea) x (t.map some) :=
  law_map O p _ ea (optionEncode ea) x t some h (fun _ => rfl)
lemma law_none {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b} (ea : A → Value b) (x : Value a) :
    RealizesLaw O (noneCode (a:=a) (b:=b)) (optionEncode ea) x (.leaf none) :=
  (realizes_pure O _ _ _ none rfl).law
lemma law_optionContinue {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b}
    (q : Effect a (Optional b)) (ea : A → Value a) (eb : B → Value b)
    (f : A → DrawTree (Option B)) (x : Option A)
    (hq : ∀ y,RealizesLaw O q (optionEncode eb) (ea y) (f y)) :
    RealizesLaw O (optionContinue q) (optionEncode eb) (optionEncode ea x)
      (match x with | none => .leaf none | some y => f y) := by
  unfold optionContinue
  cases x with
  | none => exact law_choose O _ _ _ _ _ _ false rfl (law_none O eb _)
  | some y =>
    exact law_choose O _ _ _ _ _ _ true rfl
      (law_precompose O snd q _ _ _ _ rfl (hq y))
lemma law_optionBind {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a (Optional b)) (q : Effect b (Optional c))
    (ea : A → Value b) (eb : B → Value c) (x : Value a)
    (t : DrawTree (Option A)) (f : A → DrawTree (Option B))
    (hp : RealizesLaw O p (optionEncode ea) x t)
    (hq : ∀ y,RealizesLaw O q (optionEncode eb) (ea y) (f y)) :
    RealizesLaw O (optionBind p q) (optionEncode eb) x (t.optionBind f) :=
  law_bind O p (optionContinue q) (optionEncode ea) (optionEncode eb) x t _ hp
    (fun y => law_optionContinue O q ea eb f y hq)

lemma law_repeat {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a}
    (p : Effect a a) (ea : A → Value a) (f : A → DrawTree A)
    (hp : ∀ x,RealizesLaw O p ea (ea x) (f x)) (k : ℕ) (x : A) :
    RealizesLaw O (repeatCode p) ea (k,ea x) (treeRepeat f k x) := by
  classical
  choose g hg hp using hp
  have hh : ∀ k x, DrawTree.Reindexed (treeRepeat f k x) (treeRepeat g k x) := by
    intro k
    induction k with
    | zero => intro x; exact .leaf x
    | succ k ih => intro x; exact (hg x).bind ih
  exact ⟨treeRepeat g k x,hh k x,realizes_repeat O p ea g hp k x⟩
lemma treeRepeat_succ_last {A : Type*} (f : A → DrawTree A) (k : ℕ) (x : A) :
    treeRepeat f (k+1) x=(treeRepeat f k x).bind f := by
  induction k generalizing x with
  | zero => exact DrawTree.bind_leaf (f x)
  | succ k ih =>
    change (f x).bind (treeRepeat f (k+1))=((f x).bind (treeRepeat f k)).bind f
    rw [DrawTree.bind_assoc]
    congr 1
    funext y
    exact ih y
lemma treeRepeat_option {A : Type*} (f : A → DrawTree (Option A)) (k : ℕ) (x : A) :
    treeRepeat (fun u => match u with | none => .leaf none | some a => f a) k (some x)=
      DrawTree.iterate f k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [treeRepeat_succ_last,ih]; rfl

lemma law_iterate {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a}
    (p : Effect a (Optional a)) (ea : A → Value a) (f : A → DrawTree (Option A))
    (hp : ∀ x,RealizesLaw O p (optionEncode ea) (ea x) (f x)) (k : ℕ) (x : A) :
    RealizesLaw O (iterateCode p) (optionEncode ea) (k,ea x) (DrawTree.iterate f k x) := by
  unfold iterateCode
  apply law_precompose O _ _ _ _ (k,optionEncode ea (some x)) _ rfl
  rw [←treeRepeat_option]
  apply law_repeat
  intro u
  exact law_optionContinue O p ea ea f u hp
end Effect

open scoped Classical
lemma stateEncode_get_right {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    (stateEncode S).2[i.val]?.getD false=decide (Sum.inr i∈S) := by simp [stateEncode]

namespace Expression

lemma run_boolXor {n : ℕ} (O : IndependenceOracle n) (a b : Bool) :
    run O boolXor (a,b)=some (xor a b) := by cases a <;> cases b <;> rfl

lemma run_singleAt {n : ℕ} (O : IndependenceOracle n) (i : ℕ) (S : Word×Word) :
    run O singleAt (i,S)=some (singleValue i S) := by
  simp only [singleAt,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_wordGet,run_wordGet]
  exact run_boolXor O _ _
lemma run_fullAt {n : ℕ} (O : IndependenceOracle n) (i : ℕ) (S : Word×Word) :
    run O fullAt (i,S)=some (fullValue i S) := by
  simp only [fullAt,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_wordGet,run_wordGet]
  exact run_boolAnd O _ _
lemma run_emptyAt {n : ℕ} (O : IndependenceOracle n) (i : ℕ) (S : Word×Word) :
    run O emptyAt (i,S)=some (emptyValue i S) := by
  simp only [emptyAt,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_wordGet,run_wordGet]
  change ((run O boolOr _).bind (run O boolNot))=_
  rw [run_boolOr]; exact run_boolNot O _

lemma run_plainCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O plainCode S=some (plainValue S) := by
  simp only [plainCode,run_compose,run_both,run_fst,run_ident,Option.bind_some,Option.map_some]
  rw [run_wordLength,Option.bind_some,run_rangeCode]
  change ((run O (mapWith singleAt) (List.range S.1.length,S)).bind (run O listAll))=_
  rw [run_mapWith O singleAt singleValue (run_singleAt O)]
  exact run_listAll O _
end Expression

lemma singleValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    Expression.singleValue i.val (stateEncode S)=decide (PairSingle (slotPair i) S) := by
  rw [Expression.singleValue,stateEncode_get_left,stateEncode_get_right]
  unfold PairSingle slotPair
  by_cases ha : Sum.inl i∈S <;> by_cases hb : Sum.inr i∈S <;> simp [ha,hb]
lemma fullValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    Expression.fullValue i.val (stateEncode S)=decide (PairFull (slotPair i) S) := by
  rw [Expression.fullValue,stateEncode_get_left,stateEncode_get_right]
  unfold PairFull slotPair
  by_cases ha : Sum.inl i∈S <;> by_cases hb : Sum.inr i∈S <;> simp [ha,hb]
lemma emptyValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    Expression.emptyValue i.val (stateEncode S)=decide (PairEmpty (slotPair i) S) := by
  rw [Expression.emptyValue,stateEncode_get_left,stateEncode_get_right]
  unfold PairEmpty slotPair
  by_cases ha : Sum.inl i∈S <;> by_cases hb : Sum.inr i∈S <;> simp [ha,hb]

lemma plainValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    Expression.plainValue (stateEncode S)=decide (PlainState (pairedSlots n) S) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Expression.plainValue,List.all_map,List.all_eq_true,Function.comp_apply,id_eq,
    stateEncode_left_length,List.mem_range,decide_eq_true_eq]
  constructor
  · intro h p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hh := h i.val i.isLt
    rw [singleValue_source] at hh
    exact of_decide_eq_true hh
  · intro h i hi
    rw [singleValue_source S ⟨i,hi⟩]
    exact decide_eq_true (h _ (by simp [pairedSlots]))

lemma plainCode_source {n : ℕ} (O : IndependenceOracle n) (S : Set (Fin n⊕Fin n)) :
    run O Expression.plainCode (stateEncode S)=some (decide (PlainState (pairedSlots n) S)) := by
  rw [Expression.run_plainCode,plainValue_source]

namespace Expression

lemma run_defectAt {n : ℕ} (O : IndependenceOracle n) (i p r : ℕ) (S : Word×Word) :
    run O defectAt (i,((p,r),S))=some (defectAtValue i ((p,r),S)) := by
  simp only [defectAt,run_applyIf,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_natEqual]
  by_cases hi : i=p
  · subst i; simp only [decide_true,Option.bind_some,ite_true]; simpa only [defectAtValue,ite_true] using run_emptyAt O p S
  · simp only [hi,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    rw [run_natEqual]
    by_cases hr : i=r
    · subst i; simp only [decide_true,Option.bind_some,ite_true]
      simpa only [defectAtValue,hi,ite_false,ite_true] using run_fullAt O r S
    · simp only [hr,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
      simpa only [defectAtValue,hi,hr,ite_false] using run_singleAt O i S

lemma run_defectCode {n : ℕ} (O : IndependenceOracle n) (p r : ℕ) (S : Word×Word) :
    run O defectCode ((p,r),S)=some (defectValue p r S) := by
  simp only [defectCode,run_compose,run_both,run_fst,run_snd,run_ident,Option.bind_some,Option.map_some]
  rw [run_natEqual,run_wordLength]
  simp only [Option.bind_some]
  rw [run_rangeCode]
  simp only [Option.bind_some,run_boolNot,run_compose]
  rw [run_mapWith O defectAt defectAtValue (by intro i v; rcases v with ⟨⟨p,r⟩,S⟩; exact run_defectAt O i p r S)]
  simp only [Option.bind_some,run_listAll,Option.map_some]
  rw [run_boolAnd]
  congr 1
  simp only [defectValue,decide_not]
end Expression

lemma slotPair_inj {α : Type*} (i j : α) : slotPair i=slotPair j ↔ i=j := by simp [slotPair]
lemma slotPair_mem {n : ℕ} (i : Fin n) : slotPair i∈pairedSlots n := by simp [pairedSlots]
lemma defect_paired_iff {n : ℕ} (p r : Fin n) (S : Set (Fin n⊕Fin n)) :
    DefectState (pairedSlots n) (slotPair p) (slotPair r) S ↔
      p≠r ∧ PairEmpty (slotPair p) S ∧ PairFull (slotPair r) S ∧
      ∀ i, i≠p → i≠r → PairSingle (slotPair i) S := by
  constructor
  · intro h
    refine ⟨fun hp => h.2.2.1 (congrArg slotPair hp),h.2.2.2.1,h.2.2.2.2.1,?_⟩
    intro i hip hir
    exact h.2.2.2.2.2 (slotPair i) (slotPair_mem i) (fun he => hip ((slotPair_inj i p).mp he)) (fun he => hir ((slotPair_inj i r).mp he))
  · rintro ⟨hpr,hp,hr,h⟩
    refine ⟨slotPair_mem p,slotPair_mem r,fun he => hpr ((slotPair_inj p r).mp he),hp,hr,?_⟩
    intro t ht htp htr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact h i (fun he => htp (congrArg slotPair he)) (fun he => htr (congrArg slotPair he))

lemma defectValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (p r : Fin n) :
    Expression.defectValue p.val r.val (stateEncode S)=
      decide (DefectState (pairedSlots n) (slotPair p) (slotPair r) S) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Expression.defectValue,Bool.and_eq_true,decide_eq_true_eq,List.all_map,List.all_eq_true,
    Function.comp_apply,id_eq,stateEncode_left_length,List.mem_range]
  rw [defect_paired_iff]
  constructor
  · rintro ⟨hne,h⟩
    have hpr : p≠r := fun he => hne (congrArg Fin.val he)
    refine ⟨hpr,?_,?_,?_⟩
    · have hh := h p.val p.isLt
      simpa only [Expression.defectAtValue,ite_true,emptyValue_source,decide_eq_true_eq] using hh
    · have hh := h r.val r.isLt
      have hrp : r.val≠p.val := Ne.symm hne
      simpa only [Expression.defectAtValue,hrp,ite_false,ite_true,fullValue_source,decide_eq_true_eq] using hh
    · intro i hip hir
      have hh := h i.val i.isLt
      have hip' : i.val≠p.val := fun he => hip (Fin.ext he)
      have hir' : i.val≠r.val := fun he => hir (Fin.ext he)
      simpa only [Expression.defectAtValue,hip',hir',ite_false,singleValue_source,decide_eq_true_eq] using hh
  · rintro ⟨hpr,hp,hr,h⟩
    refine ⟨fun he => hpr (Fin.ext he),?_⟩
    intro i hi
    let j : Fin n := ⟨i,hi⟩
    change Expression.defectAtValue j.val ((p.val,r.val),stateEncode S)=true
    by_cases hjp : j=p
    · subst p
      simpa only [Expression.defectAtValue,ite_true,emptyValue_source,decide_eq_true_eq] using hp
    · by_cases hjr : j=r
      · subst r
        have hne : j.val≠p.val := fun he => hjp (Fin.ext he)
        simpa only [Expression.defectAtValue,hne,ite_false,ite_true,fullValue_source,decide_eq_true_eq] using hr
      · have hip : j.val≠p.val := fun he => hjp (Fin.ext he)
        have hir : j.val≠r.val := fun he => hjr (Fin.ext he)
        simpa only [Expression.defectAtValue,hip,hir,ite_false,singleValue_source,decide_eq_true_eq] using h j hjp hjr

namespace Expression

lemma run_countWith {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression (.prod a b) .bool)
    (f : Value a → Value b → Bool) (hp : ∀ x z,run O p (x,z)=some (f x z))
    (xs : List (Value a)) (z : Value b) :
    run O (countWith p) (xs,z)=some (xs.countP (fun x => f x z)) := by
  rw [countWith,run_compose,run_filterWith O p f hp,Option.bind_some,run_listLength]
  simp only [List.countP_eq_length_filter]

lemma run_countPlainCode {n : ℕ} (O : IndependenceOracle n) (xs : List (Word×Word)) :
    run O countPlainCode xs=some (countPlainValue xs) := by
  change run O (countWith (fst (b:=.unit) >>> plainCode)) (xs,())=_
  exact run_countWith (a:=StateData) (b:=.unit) O _ (fun x (_ : Unit) => plainValue x) (fun x _ => run_plainCode O x) xs ()
lemma run_countDefectCode {n : ℕ} (O : IndependenceOracle n) (xs : List (Word×Word)) (p r : ℕ) :
    run O countDefectCode (xs,(p,r))=some (countDefectValue xs p r) := by
  exact run_countWith (a:=StateData) (b:=NN) O _ (fun S u => defectValue u.1 u.2 S)
    (fun S u => run_defectCode O u.1 u.2 S) xs (p,r)

lemma learningRatio_nonneg (xs : List (Word×Word)) (p r : ℕ) : 0≤learningRatio xs p r := by
  unfold learningRatio; positivity
lemma run_learningRatio {n : ℕ} (O : IndependenceOracle n) (xs : List (Word×Word)) (p r : ℕ) :
    run O learningRatioCode (xs,(p,r))=some (rationalPair (learningRatio xs p r)) := by
  simp only [learningRatioCode,run_compose,run_both,run_fst,Option.bind_some]
  rw [run_countPlainCode,run_countDefectCode]
  exact run_normalizeRat_pair O _ _

lemma weightUpdate_nonneg (p r : ℕ) (xs : List (Word×Word)) (q : ℚ) (hq : 0≤q) :
    0≤weightUpdate p r xs q := by
  unfold weightUpdate
  split_ifs
  · exact hq
  · exact mul_nonneg hq (learningRatio_nonneg xs p r)
lemma run_weightStep {n : ℕ} (O : IndependenceOracle n) (p r : ℕ) (xs : List (Word×Word)) (q : ℚ) (hq : 0≤q) :
    run O weightStep (xs,((p,r),rationalPair q))=some ((p,r),rationalPair (weightUpdate p r xs q)) := by
  simp only [weightStep,run_both,run_compose,run_fst,run_snd,Option.bind_some,run_applyIf]
  rw [run_natEqual]
  by_cases hpr : p=r
  · subst p; simp only [decide_true,Option.bind_some,ite_true,Option.map_some,weightUpdate]
  · simp only [hpr,decide_false,Option.bind_some,Option.map_some,Bool.false_eq_true,ite_false]
    rw [run_learningRatio]
    simp only [Option.bind_some,Option.map_some]
    rw [run_ratMul O q _ hq (learningRatio_nonneg xs p r)]
    simp only [Option.map_some,weightUpdate,hpr,ite_false]

lemma fold_weightStep {n : ℕ} (O : IndependenceOracle n) (p r : ℕ) (h : List (List (Word×Word)))
    (q : ℚ) (hq : 0≤q) :
    foldValue (run O weightStep) h ((p,r),rationalPair q)=some
      ((p,r),rationalPair (h.foldl (fun q xs => weightUpdate p r xs q) q)) := by
  induction h generalizing q with
  | nil => rfl
  | cons xs h ih =>
    rw [foldValue,run_weightStep O p r xs q hq,Option.bind_some]
    exact ih _ (weightUpdate_nonneg p r xs q hq)
lemma run_historyWeightCode {n : ℕ} (O : IndependenceOracle n) (p r : ℕ) (h : List (List (Word×Word))) :
    run O historyWeightCode (h,(p,r))=some (rationalPair (historyWeightValue p r h)) := by
  change ((foldValue (run O weightStep) h ((p,r),rationalPair 4)).bind fun z => some z.2)=_
  rw [fold_weightStep O p r h 4 (by norm_num)]
  rfl
end Expression

lemma countPlainValue_source {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) :
    Expression.countPlainValue (sampleEncode xs)=xs.countP (fun S => decide (PlainState (pairedSlots n) S)) := by
  simp only [Expression.countPlainValue,sampleEncode,List.countP_map,plainValue_source,Function.comp_def]
lemma countDefectValue_source {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) (p r : Fin n) :
    Expression.countDefectValue (sampleEncode xs) p.val r.val=
      xs.countP (fun S => decide (DefectState (pairedSlots n) (slotPair p) (slotPair r) S)) := by
  simp only [Expression.countDefectValue,sampleEncode,List.countP_map,defectValue_source,Function.comp_def]

lemma weightUpdate_source {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) (p r : Fin n)
    (w : ((Fin n⊕Fin n)×(Fin n⊕Fin n)) → ((Fin n⊕Fin n)×(Fin n⊕Fin n)) → ℚ) :
    Expression.weightUpdate p.val r.val (sampleEncode xs) (w (slotPair p) (slotPair r))=
      rationalLearn (pairedSlots n) w xs (slotPair p) (slotPair r) := by
  unfold Expression.weightUpdate rationalLearn
  by_cases hpr : p=r
  · subst p; simp
  · have hv : p.val≠r.val := fun he => hpr (Fin.ext he)
    have hs : slotPair p≠slotPair r := fun he => hpr ((slotPair_inj p r).mp he)
    rw [ite_eq_right hv,ite_eq_left ⟨slotPair_mem p,slotPair_mem r,hs⟩,rationalTypeRatio]
    rw [Expression.learningRatio,countPlainValue_source,countDefectValue_source]

lemma historyWeight_source {n : ℕ} (h : List (List (Set (Fin n⊕Fin n)))) (p r : Fin n) :
    Expression.historyWeightValue p.val r.val (historyEncode h)=
      rationalHistory (pairedSlots n) id h (slotPair p) (slotPair r) := by
  have hf : ∀ (l : List (List (Set (Fin n⊕Fin n))))
      (w : ((Fin n⊕Fin n)×(Fin n⊕Fin n)) → ((Fin n⊕Fin n)×(Fin n⊕Fin n)) → ℚ),
      (historyEncode l).foldl (fun q xs => Expression.weightUpdate p.val r.val xs q) (w (slotPair p) (slotPair r))=
        (l.foldl (fun w xs => rationalLearn (pairedSlots n) w xs) w) (slotPair p) (slotPair r) := by
    intro l
    induction l with
    | nil => intro w; rfl
    | cons xs l ih =>
      intro w
      change (historyEncode l).foldl _ (Expression.weightUpdate p.val r.val (sampleEncode xs) (w (slotPair p) (slotPair r)))=_
      rw [weightUpdate_source]
      exact ih _
  exact hf h (fun _ _ => 4)

namespace Expression

lemma run_listAppend {n : ℕ} (O : IndependenceOracle n) {a} (xs ys : List (Value a)) :
    run O listAppend (xs,ys)=some (xs++ys) := by
  have hf : ∀ (us vs : List (Value a)),foldValue (run O cons) us vs=some (us.reverse++vs) := by
    intro us
    induction us with
    | nil => intro vs; rfl
    | cons u us ih => intro vs; simpa [foldValue,run,List.reverse_cons,List.append_assoc] using ih (u::vs)
  simp only [listAppend,onLeft,run_compose,run_both,run_fst,run_snd,Option.bind_some]
  rw [run_listReverse]
  simp only [Option.bind_some,Option.map_some]
  change foldValue (run O cons) xs.reverse ys=_
  rw [hf,List.reverse_reverse]

lemma run_productStep {n : ℕ} (O : IndependenceOracle n) {a b}
    (x : Value a) (zs : List (Value a × Value b)) (ys : List (Value b)) :
    run O productStep (x,(zs,ys))=some (zs++ys.map (fun y => (x,y)),ys) := by
  simp only [productStep,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_mapWith O swap (fun y x => (x,y)) (fun _ _ => rfl)]
  simp only [Option.map_some,Option.bind_some]
  rw [run_listAppend]
  rfl
lemma run_productCode {n : ℕ} (O : IndependenceOracle n) {a b}
    (xs : List (Value a)) (ys : List (Value b)) :
    run O productCode (xs,ys)=some ((xs ×ˢ ys)) := by
  have hf : ∀ (us : List (Value a)) (acc : List (Value a × Value b)),
      foldValue (run O productStep) us (acc,ys)=some (acc++(us ×ˢ ys),ys) := by
    intro us
    induction us with
    | nil => intro acc; simp [foldValue]
    | cons u us ih =>
      intro acc
      rw [foldValue,run_productStep,Option.bind_some,ih]
      simp [List.product_cons,List.append_assoc]
  change ((foldValue (run O productStep) xs ([],ys)).bind fun z => some z.1)=_
  rw [hf]
  rfl

lemma run_indexPairs {n : ℕ} (O : IndependenceOracle n) (k : ℕ) :
    run O indexPairs k=some ((List.range k) ×ˢ (List.range k)) := by
  simp only [indexPairs,run_compose,run_both]
  rw [run_rangeCode]
  simp only [Option.bind_some,Option.map_some]
  exact run_productCode O _ _
end Expression

open Expression

open Expression

lemma iterateM_succ_last {A : Type*} (f : A → Option A) (k : ℕ) (x : A) :
    iterateM f (k+1) x=(iterateM f k x).bind f := by
  induction k generalizing x with
  | zero => simp [iterateM]
  | succ k ih =>
    simp only [iterateM,Option.bind_assoc]
    congr 1
    funext y
    exact ih y
open Expression
open scoped Classical
namespace Effect
lemma realizes_repeat_succ_last {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a}
    (p : Effect a a) (ea : A → Value a) (eb : B → Value a) (k : ℕ) (x : Value a)
    (t : DrawTree A) (f : A → DrawTree B)
    (hp : Realizes O (repeatCode p) ea (k,x) t)
    (hq : ∀ y,Realizes O p eb (ea y) (f y)) :
    Realizes O (repeatCode p) eb (k+1,x) (t.bind f) := by
  intro bank
  rw [run_repeat,iterateM_succ_last,←run_repeat,hp,Option.bind_some,bankEval_bind]
  cases ht : bankEval t bank with
  | mk out rest =>
    cases out with
    | none => rfl
    | some y => exact hq y rest
lemma law_repeat_succ_last {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a}
    (p : Effect a a) (ea : A → Value a) (eb : B → Value a) (k : ℕ) (x : Value a)
    (t : DrawTree A) (f : A → DrawTree B)
    (hp : RealizesLaw O (repeatCode p) ea (k,x) t)
    (hq : ∀ y,RealizesLaw O p eb (ea y) (f y)) :
    RealizesLaw O (repeatCode p) eb (k+1,x) (t.bind f) := by
  classical
  rcases hp with ⟨u,hu,hp⟩
  choose g hg hq using hq
  exact ⟨u.bind g,hu.bind hg,realizes_repeat_succ_last O p ea eb k x u g hp hq⟩

lemma phaseRepeat_bind {A B : Type*} (f : ℕ → A → DrawTree (Option A)) (t : DrawTree B)
    (g : B → A) (k : ℕ) :
    (t.bind (fun x => phaseRepeat f (k+1) (g x)))=
      (t.bind (fun x => phaseRepeat f k (g x))).optionBind (f (k+1)) := by
  simp only [phaseRepeat,DrawTree.optionBind,DrawTree.bind_assoc]
lemma law_phaseRepeat {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a}
    (p : Effect a (Optional a)) (e : ℕ → A → Value a)
    (f : ℕ → A → DrawTree (Option A))
    (hp : ∀ j x,RealizesLaw O p (optionEncode (e (j+1))) (e j x) (f (j+1) x))
    (k : ℕ) (x : A) :
    RealizesLaw O (repeatCode (optionContinue p)) (optionEncode (e k))
      (k,optionEncode (e 0) (some x)) (phaseRepeat f k x) := by
  induction k with
  | zero => exact ⟨.leaf (some x),.leaf (some x),fun _ => rfl⟩
  | succ k ih =>
    apply law_repeat_succ_last O (optionContinue p) (optionEncode (e k)) _ k _ _ _ ih
    intro y
    exact law_optionContinue O p (e k) (e (k+1)) (f (k+1)) y (hp k)

lemma searchRepeat_done {X : Type*} (step : X → DrawTree X) (P : X → Prop) (k : ℕ) (y : FiniteChain.Inside P) :
    treeRepeat (searchStep step P) k (.inr y)=.leaf (.inr y) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih
lemma searchRepeat_finish {X : Type*} [Fintype X] (step : X → DrawTree X) (P : X → Prop) (k : ℕ) (x : X) :
    (treeRepeat (searchStep step P) k (.inl x)).map searchFinish=hittingTree step P k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [treeRepeat,searchStep,DrawTree.map_bind,DrawTree.bind_map,hittingTree]
    congr 1
    funext y
    by_cases hy : P y
    · rw [dite_eq_left hy,searchRepeat_done,dite_eq_left hy]; rfl
    · rw [dite_eq_right hy,ih,dite_eq_right hy]

lemma law_hitStep {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a}
    (step : Effect a a) (test : Expression a .bool) (e : X → Value a)
    (f : X → DrawTree X) (P : X → Prop)
    (hs : ∀ x,RealizesLaw O step e (e x) (f x))
    (ht : ∀ x,run O test (e x)=some (decide (P x))) (u : SearchState X P) :
    RealizesLaw O (hitStepCode step test) (searchEncode e) (searchEncode e u) (searchStep f P u) := by
  unfold hitStepCode
  cases u with
  | inl x =>
    apply law_choose O _ _ _ _ _ _ false rfl
    change RealizesLaw O (map (precompose fst step) (both ident test)) _ _ _
    apply law_map O _ _ e _ _ _ _
    · exact law_precompose O fst step _ _ _ _ rfl (hs x)
    · intro y
      rw [run_both,run_ident,Option.bind_some,ht]
      by_cases hy : P y
      · simp only [hy,dite_eq_left,decide_true,Option.map_some]; rfl
      · simp only [hy,decide_false,Option.map_some]; rfl
  | inr y =>
    apply law_choose O _ _ _ _ _ _ true rfl
    change RealizesLaw O (pure ident) (searchEncode e) _ (.leaf (.inr y))
    exact (realizes_pure O ident (searchEncode e) _ (Sum.inr y) rfl).law

lemma law_hitting {n : ℕ} (O : IndependenceOracle n) {X : Type*} [Fintype X] {a}
    (step : Effect a a) (test : Expression a .bool) (e : X → Value a)
    (f : X → DrawTree X) (P : X → Prop)
    (hs : ∀ x,RealizesLaw O step e (e x) (f x))
    (ht : ∀ x,run O test (e x)=some (decide (P x))) (k : ℕ) (x : X) :
    RealizesLaw O (hittingCode step test) (optionEncode (fun y : FiniteChain.Inside P => e y.val))
      (k,e x) (hittingTree f P k x) := by
  unfold hittingCode
  apply law_precompose O _ _ _ _ (k,searchEncode e (.inl x : SearchState X P)) _ rfl
  rw [←searchRepeat_finish]
  apply law_map O _ _ (searchEncode e) _ _ _ searchFinish
  · exact law_repeat O _ _ _ (law_hitStep O step test e f P hs ht) k (.inl x)
  · intro u
    cases u <;> rfl
end Effect

open Expression
namespace Effect
lemma law_recode {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Effect a b) (q : Expression b c) (ea : A → Value b) (eb : A → Value c)
    (x : Value a) (t : DrawTree A) (hp : RealizesLaw O p ea x t)
    (hq : ∀ y,run O q (ea y)=some (eb y)) : RealizesLaw O (map p q) eb x t := by
  have hh := law_map O p q ea eb x t id hp hq
  simpa only [DrawTree.map,id_eq,DrawTree.bind_leaf] using hh

lemma law_withContext {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Effect (.prod c a) b) (e : A → Value b) (ctx : Value c) (x : Value a)
    (t : DrawTree A) (hp : RealizesLaw O p e (ctx,x) t) :
    RealizesLaw O (withContext p) (fun y => (ctx,e y)) (ctx,x) t := by
  unfold withContext
  rw [←DrawTree.bind_leaf t]
  apply law_letIn O p _ e _ _ t DrawTree.leaf hp
  intro y
  exact (realizes_pure O _ _ _ y rfl).law

lemma law_optionMap {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c}
    (p : Effect a (Optional b)) (q : Expression b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree (Option A)) (f : A → B)
    (hp : RealizesLaw O p (optionEncode ea) x t)
    (hq : ∀ y,run O q (ea y)=some (eb (f y))) :
    RealizesLaw O (map p (optionMapCode q)) (optionEncode eb) x (t.map (Option.map f)) := by
  apply law_map O p _ (optionEncode ea) (optionEncode eb) x t _ hp
  intro y
  cases y with
  | none => rfl
  | some y =>
    change ((run O q (ea y)).bind fun z => some (true,z))=_
    rw [hq]; rfl

lemma law_optionRecode {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Effect a (Optional b)) (q : Expression b c) (ea : A → Value b) (eb : A → Value c)
    (x : Value a) (t : DrawTree (Option A))
    (hp : RealizesLaw O p (optionEncode ea) x t)
    (hq : ∀ y,run O q (ea y)=some (eb y)) :
    RealizesLaw O (map p (optionMapCode q)) (optionEncode eb) x t := by
  apply law_recode O p _ (optionEncode ea) (optionEncode eb) x t hp
  intro y
  cases y with
  | none => rfl
  | some y =>
    change ((run O q (ea y)).bind fun z => some (true,z))=_
    rw [hq]; rfl
end Effect

open scoped Classical
namespace Expression

lemma run_defectPairsCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O defectPairsCode S=some (defectPairsValue S) := by
  simp only [defectPairsCode,run_compose,run_both,run_fst,run_ident,Option.bind_some]
  rw [run_wordLength,Option.bind_some,run_indexPairs]
  simp only [Option.bind_some,Option.map_some]
  exact run_filterWith (a:=NN) (b:=StateData) O defectCode (fun pr S => defectValue pr.1 pr.2 S)
    (fun pr S => run_defectCode O pr.1 pr.2 S) _ S

lemma run_chainCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O chainCode S=some (chainValue S) := by
  simp only [chainCode,run_compose,run_both]
  rw [run_plainCode,run_defectPairsCode]
  simp only [Option.bind_some,run_compose,run_listLength,run_natEqZero,run_boolNot,Option.map_some]
  rw [run_boolOr]
  simp only [chainValue,decide_not]

lemma run_multiplierCode {n : ℕ} (O : IndependenceOracle n) (h : List (List (Word×Word))) (S : Word×Word) :
    run O multiplierCode (h,S)=some (rationalPair (multiplierValue h S)) := by
  simp only [multiplierCode,run_letIn,run_compose,run_snd,Option.bind_some]
  rw [run_defectPairsCode]
  simp only [Option.bind_some,run_applyIf,run_compose,run_snd,run_listLength,run_natEqZero]
  by_cases he : (defectPairsValue S).length=0
  · simp only [he,decide_true,ite_true,multiplierValue,run_constant]
    rfl
  · simp only [he,decide_false,Option.bind_some,Bool.false_eq_true,ite_false,multiplierValue,
      run_compose,run_both,run_fst,run_snd,run_constant,Option.map_some]
    rw [run_headD]
    simp only [Option.map_some,Option.bind_some]
    exact run_historyWeightCode O _ _ h
end Expression

lemma mem_defectPairsValue {n : ℕ} (S : Set (Fin n⊕Fin n)) (p r : ℕ) :
    (p,r)∈Expression.defectPairsValue (stateEncode S) ↔
      ∃ (hp : p<n) (hr : r<n),DefectState (pairedSlots n) (slotPair ⟨p,hp⟩) (slotPair ⟨r,hr⟩) S := by
  simp only [Expression.defectPairsValue,List.mem_filter,List.mem_product,List.mem_range,stateEncode_left_length]
  constructor
  · rintro ⟨⟨hp,hr⟩,h⟩
    exact ⟨hp,hr,of_decide_eq_true (by simpa only [defectValue_source S ⟨p,hp⟩ ⟨r,hr⟩] using h)⟩
  · rintro ⟨hp,hr,h⟩
    exact ⟨⟨hp,hr⟩,by simpa only [defectValue_source S ⟨p,hp⟩ ⟨r,hr⟩] using decide_eq_true h⟩

lemma defectPairs_nonempty_source {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    (Expression.defectPairsValue (stateEncode S)).length≠0 ↔
      ∃ p r,DefectState (pairedSlots n) p r S := by
  rw [Ne, List.length_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨⟨p,r⟩,hm⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨hp,hr,hd⟩ := (mem_defectPairsValue S p r).mp hm
    exact ⟨_,_,hd⟩
  · rintro ⟨p,r,h⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h.1
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h.2.1
    exact List.ne_nil_of_mem ((mem_defectPairsValue S i.val j.val).mpr ⟨i.isLt,j.isLt,h⟩)

lemma chainValue_source {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    Expression.chainValue (stateEncode S)=decide (ChainState (pairedSlots n) S) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hh
    apply decide_eq_true
    have ho : Expression.plainValue (stateEncode S)=true ∨
        decide ((Expression.defectPairsValue (stateEncode S)).length≠0)=true := by
      simpa only [Expression.chainValue,Bool.or_eq_true] using hh
    rcases ho with hp|hd
    · exact Or.inl (of_decide_eq_true (by simpa only [plainValue_source] using hp))
    · exact Or.inr ((defectPairs_nonempty_source S).mp (of_decide_eq_true hd))
  · intro hh
    rw [Expression.chainValue,Bool.or_eq_true]
    rcases of_decide_eq_true hh with hp|hd
    · exact Or.inl (by rw [plainValue_source]; exact decide_eq_true hp)
    · exact Or.inr (decide_eq_true ((defectPairs_nonempty_source S).mpr hd))

lemma multiplierValue_source {n : ℕ} (h : List (List (Set (Fin n⊕Fin n)))) (S : Set (Fin n⊕Fin n)) :
    Expression.multiplierValue (historyEncode h) (stateEncode S)=
      rationalMultiplier (pairedSlots n) (rationalHistory (pairedSlots n) id h) S := by
  unfold Expression.multiplierValue rationalMultiplier
  by_cases he : (Expression.defectPairsValue (stateEncode S)).length=0
  · have hn : ¬∃ p r,DefectState (pairedSlots n) p r S := by
      intro hh
      exact ((defectPairs_nonempty_source S).mpr hh) he
    rw [ite_eq_left he,dite_eq_right hn]
  · let l := Expression.defectPairsValue (stateEncode S)
    have hl : l≠[] := by simpa only [List.length_eq_zero_iff] using he
    have hm : l.headD (0,0)∈l := by
      cases hh : l with
      | nil => exact False.elim (hl hh)
      | cons a l => simp
    obtain ⟨hp,hr,hd⟩ := (mem_defectPairsValue S (l.headD (0,0)).1 (l.headD (0,0)).2).mp hm
    have hex : ∃ p r,DefectState (pairedSlots n) p r S := ⟨_,_,hd⟩
    rw [ite_eq_right he,dite_eq_left hex,historyWeight_source h ⟨_,hp⟩ ⟨_,hr⟩]
    have hh := hex.choose_spec.choose_spec.unique hd
    exact congrArg₂ (rationalHistory (pairedSlots n) id h) hh.1.symm hh.2.symm

namespace Expression

lemma run_updateAt {n : ℕ} (O : IndependenceOracle n) (i : ℕ) (w : Word) (j : ℕ) (b : Bool) :
    run O updateAt (i,(w,(j,b)))=some (if i=j then b else w[i]?.getD false) := by
  simp only [updateAt,run_applyIf,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_natEqual,run_wordGet]
  by_cases h : i=j <;> simp [h]
lemma run_updateWord {n : ℕ} (O : IndependenceOracle n) (w : Word) (j : ℕ) (b : Bool) :
    run O updateWord (w,(j,b))=some (w.set j b) := by
  simp only [updateWord,run_compose,run_both,run_fst,run_ident,Option.bind_some]
  rw [run_wordLength,Option.bind_some,run_rangeCode]
  simp only [Option.bind_some,Option.map_some,run_compose]
  rw [run_mapWith (a:=.nat) (b:=.bool) (c:=.prod .word (.prod .nat .bool)) O updateAt
    (fun i z => if i=z.2.1 then z.2.2 else z.1[i]?.getD false)
    (fun i z => run_updateAt O i z.1 z.2.1 z.2.2)]
  simp only [Option.bind_some]
  rw [run_fromList]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_set]
    rw [List.getElem?_eq_getElem (by simpa using hi)]
    simp only [Option.getD_some]
    by_cases he : i=j
    · simp [he]
    · simp [he,Ne.symm he]

lemma run_splitWord {n : ℕ} (O : IndependenceOracle n) (w : Word) (k : ℕ) :
    run O splitWord (w,k)=some (w.take k,w.drop k) := by
  change ((run O (splitAtCode (a:=.bool)) (w,k)).bind (run O (both (fst >>> fromList) (snd >>> fromList))))=_
  rw [run_splitAtCode]
  simp only [Option.bind_some,run_both,run_compose,run_fst,run_snd]
  rw [run_fromList,run_fromList]
  rfl

lemma run_exchangeWord {n : ℕ} (O : IndependenceOracle n) (w : Word) (a b : ℕ) :
    run O exchangeWord (w,(a,b))=some ((w.set a false).set b true) := by
  simp only [exchangeWord,run_letIn,run_compose,run_both,run_fst,run_snd,run_constant,
    Option.bind_some,Option.map_some]
  rw [run_updateWord]
  simp only [Option.bind_some]
  exact run_updateWord O _ _ _

lemma run_exchangeSetCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) (a b : ℕ) :
    run O exchangeSetCode (S,(a,b))=some
      ((((S.1++S.2).set a false).set b true).take S.1.length,
       (((S.1++S.2).set a false).set b true).drop S.1.length) := by
  simp only [exchangeSetCode,run_compose,run_both,run_fst,run_snd,run_append,Option.bind_some,Option.map_some]
  rw [run_exchangeWord,run_wordLength]
  simp only [Option.bind_some,Option.map_some]
  exact run_splitWord O _ _
end Expression

open scoped Classical
lemma position_inj {n : ℕ} (i j : Fin n⊕Fin n) : position i=position j ↔ i=j := by
  exact ⟨fun h => finSumFinEquiv.injective (Fin.ext h),fun h => congrArg position h⟩

lemma combinedEncode_update {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n⊕Fin n) (b : Bool) :
    (combinedEncode S).set (position i) b=combinedEncode (if b then insert i S else S\{i}) := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    let j : Fin n⊕Fin n := finSumFinEquiv.symm ⟨k,by simpa using hk'⟩
    have hj : position j=k := by simp [position,j]
    have ha := combinedEncode_get S j
    have hb := combinedEncode_get (if b then insert i S else S\{i}) j
    rw [hj,List.getElem?_eq_getElem (by simpa using hk),Option.getD_some] at ha
    rw [hj,List.getElem?_eq_getElem hk',Option.getD_some] at hb
    rw [List.getElem_set,ha,hb]
    have he : position i=k ↔ i=j := by rw [←hj,position_inj]
    simp only [he]
    cases b <;> by_cases hij : i=j <;> simp [hij,eq_comm]

lemma exchangeSetCode_source {n : ℕ} (O : IndependenceOracle n) (S : Set (Fin n⊕Fin n)) (a : ExchangeChoice S) :
    run O Expression.exchangeSetCode (stateEncode S,(position a.1.val,position a.2.val))=
      some (stateEncode (exchangedSet S a)) := by
  rw [Expression.run_exchangeSetCode,stateEncode_left_length]
  change some (((combinedEncode S).set (position a.1.val) false |>.set (position a.2.val) true).take n,
    ((combinedEncode S).set (position a.1.val) false |>.set (position a.2.val) true).drop n)=_
  rw [combinedEncode_update]
  simp only [Bool.false_eq_true,ite_false]
  rw [combinedEncode_update]
  simp only [ite_true]
  change some ((combinedEncode (exchangedSet S a)).take n,(combinedEncode (exchangedSet S a)).drop n)=_
  have hh (x y : Word) : some ((x++y).take x.length,(x++y).drop x.length)=some (x,y) := by simp
  simpa only [combinedEncode, stateEncode_left_length, Prod.eta] using hh (stateEncode (exchangedSet S a)).1 (stateEncode (exchangedSet S a)).2

open scoped Classical
namespace Expression
lemma historyWeightValue_nonneg (p r : ℕ) (h : List (List (Word×Word))) :
    0≤historyWeightValue p r h := by
  have hf : ∀ (l : List (List (Word×Word))) (q : ℚ),0≤q →
      0≤l.foldl (fun q xs => weightUpdate p r xs q) q := by
    intro l
    induction l with
    | nil => intro q hq; exact hq
    | cons xs l ih => intro q hq; exact ih _ (weightUpdate_nonneg p r xs q hq)
  exact hf h 4 (by norm_num)
lemma multiplierValue_nonneg (h : List (List (Word×Word))) (S : Word×Word) :
    0 ≤ multiplierValue h S := by
  unfold multiplierValue
  split_ifs
  · norm_num
  · exact historyWeightValue_nonneg _ _ h

lemma rationalRho_nonneg (n : ℕ) : 0≤rationalRho n := by
  cases n with
  | zero => norm_num [rationalRho]
  | succ n =>
    unfold rationalRho
    have hh : (1:ℚ) ≤ 2*((n+1:ℕ):ℚ) := by push_cast; linarith [Nat.cast_nonneg (α:=ℚ) n]
    exact sub_nonneg.mpr ((div_le_one (by positivity : (0:ℚ)<2*((n+1:ℕ):ℚ))).mpr hh)
lemma run_rhoCode {n : ℕ} (O : IndependenceOracle n) (m : ℕ) :
    run O rhoCode m=some (rationalPair (rationalRho m)) := by
  simp only [rhoCode,run_applyIf,run_natEqZero]
  by_cases hm : m=0
  · subst m; simp only [decide_true,Option.bind_some,ite_true,run_constant]
    norm_num [rationalPair,rationalRho]
  · simp only [hm,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    change run O (both (both (snd (a:=.nat) (b:=.nat)) (constant 1) >>> natSub) snd >>> normalizeRat) (m,m*2)=_
    simp only [run_compose,run_both,run_snd,run_constant,Option.bind_some,Option.map_some]
    rw [run_natSub]
    simp only [Option.bind_some]
    rw [run_normalizeRat_pair]
    congr 2
    have hp : 1 ≤ m*2 := by omega
    have hz : (m:ℚ)≠0 := by exact_mod_cast hm
    rw [Nat.cast_sub hp,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    unfold rationalRho
    field_simp

end Expression

lemma annealCode_source {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r j : ℕ) (h : List (List (Set (Fin n⊕Fin n)))) (S : Set (Fin n⊕Fin n)) :
    run O Expression.annealCode (((r,j),historyEncode h),stateEncode S)=
      some (rationalPair ((rationalRho n^j)^(oracleDeficiency n r O S))) := by
  simp only [Expression.annealCode,Expression.run_compose,Expression.run_both,
    Expression.run_fst,Expression.run_snd,Option.bind_some,Option.map_some]
  rw [Expression.run_wordLength,stateEncode_left_length]
  simp only [Option.bind_some]
  rw [Expression.run_rhoCode]
  simp only [Option.bind_some]
  rw [Expression.run_ratPowCode O _ (Expression.rationalRho_nonneg n)]
  simp only [Option.bind_some]
  rw [deficiencyCode_source M₁ M₂ O hO hE₁ hE₂ r _ _ (stateEncode_left_length S) (stateEncode_right_length S),stateEncode_repr]
  simp only [Option.bind_some,Option.map_some]
  exact Expression.run_ratPowCode O _ (pow_nonneg (Expression.rationalRho_nonneg n) _) _

lemma weightCode_source {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r j : ℕ) (h : List (List (Set (Fin n⊕Fin n)))) (S : Set (Fin n⊕Fin n)) :
    run O Expression.weightCode (((r,j),historyEncode h),stateEncode S)=some
      (rationalPair (rationalMultiplier (pairedSlots n) (rationalHistory (pairedSlots n) id h) S*
        (rationalRho n^j)^(oracleDeficiency n r O S))) := by
  simp only [Expression.weightCode,Expression.run_compose,Expression.run_both,
    Expression.run_fst,Expression.run_snd,Option.bind_some,Option.map_some]
  rw [Expression.run_multiplierCode,multiplierValue_source,annealCode_source M₁ M₂ O hO hE₁ hE₂]
  simp only [Option.bind_some,Option.map_some]
  apply Expression.run_ratMul
  · rw [←multiplierValue_source]
    exact Expression.multiplierValue_nonneg _ _
  · exact pow_nonneg (pow_nonneg (Expression.rationalRho_nonneg n) j) _

open Expression
namespace Effect

lemma bernoulliCode_source {n : ℕ} (O : IndependenceOracle n) (q : ℚ) :
    Realizes O bernoulliCode id (rationalPair q) (DrawTree.bernoulli q) := by
  have hd : q.den-1+1=q.den := by have hh := q.den_pos; omega
  have hh : Realizes O draw Fin.val q.den (.draw (q.den-1) DrawTree.leaf) := by
    simpa only [hd] using realizes_draw O (q.den-1)
  have hp : Realizes O (precompose (snd (a:=.nat)) draw) Fin.val (rationalPair q)
      (.draw (q.den-1) DrawTree.leaf) :=
    realizes_precompose (a:=NN) (b:=.nat) (c:=.nat) O snd draw Fin.val (rationalPair q) q.den _ rfl hh
  change Realizes O (letIn (precompose snd draw) (pure (both snd (fst >>> fst) >>> less))) id
    (rationalPair q) _
  have hr := realizes_letIn O (precompose (snd (a:=.nat)) draw)
    (pure (both snd (fst >>> fst) >>> less)) Fin.val id (rationalPair q)
    (.draw (q.den-1) DrawTree.leaf) (fun (i : Fin (q.den-1+1)) => .leaf (decide (i.val<q.num.natAbs))) hp
    (fun i => realizes_pure O _ id _ _ rfl)
  exact hr
end Effect

open Expression
open scoped Classical

lemma acceptanceCode_source {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r j : ℕ) (h : List (List (Set (Fin n⊕Fin n)))) (S T : ChainIndex (pairedSlots n)) :
    run O acceptanceCode (((r,j),historyEncode h),(stateEncode S.val,stateEncode T.val))=some
      (rationalPair (rationalAcceptance (pairedSlots n) (rationalHistory (pairedSlots n) id h)
        (oracleAnneal n r O j) S T)) := by
  have hn (U : Set (Fin n⊕Fin n)) : 0 ≤ rationalWeight (pairedSlots n)
      (rationalHistory (pairedSlots n) id h) (oracleAnneal n r O j) U := by
    unfold rationalWeight
    apply mul_nonneg
    · rw [←multiplierValue_source]; exact multiplierValue_nonneg _ _
    · exact pow_nonneg (pow_nonneg (rationalRho_nonneg n) j) _
  simp only [acceptanceCode,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [weightCode_source M₁ M₂ O hO hE₁ hE₂,weightCode_source M₁ M₂ O hO hE₁ hE₂]
  simp only [Option.bind_some,Option.map_some]
  change ((run O ratDiv (rationalPair (rationalWeight (pairedSlots n) (rationalHistory (pairedSlots n) id h)
    (oracleAnneal n r O j) T.val),rationalPair (rationalWeight (pairedSlots n) (rationalHistory (pairedSlots n) id h)
    (oracleAnneal n r O j) S.val))).bind (run O ratMinOne))=_
  rw [run_ratDiv O _ _ (hn _) (hn _),Option.bind_some]
  exact run_ratMinOne O _ (div_nonneg (hn _) (hn _))

open scoped Classical
namespace Expression

lemma run_membersCode {n : ℕ} (O : IndependenceOracle n) (w : Word) :
    run O membersCode w=some (memberPositions w) := by
  simp only [membersCode,run_compose,run_both,run_ident,run_wordLength,Option.bind_some,Option.map_some]
  rw [run_rangeCode]
  simp only [Option.bind_some]
  apply run_filterWith
  intro i w
  exact run_wordGet O w i
end Expression

open Expression
namespace Effect

lemma uniformVia_size {A : Type*} [Fintype A] [Nonempty A] (m : ℕ) (e : Fin m ≃ A)
    (h : m=Fintype.card A) (hc : m-1+1=m) :
    (DrawTree.draw (m-1) (fun i => .leaf (e (Fin.cast hc i))))=
      DrawTree.uniformVia A ((finCongr h.symm).trans e) := by
  subst m
  rfl

lemma realizes_uniformList {n : ℕ} (O : IndependenceOracle n) {A : Type*} [Fintype A] [Nonempty A]
    {a} (encode : A → Value a) (l : List (Value a)) (e : Fin l.length ≃ A)
    (he : ∀ i,l.get i=encode (e i)) :
    RealizesLaw O uniformList encode l (DrawTree.uniformChoice A) := by
  have hlen : l.length=Fintype.card A := by simpa using Fintype.card_congr e
  have hp : 0<l.length := by rw [hlen]; exact Fintype.card_pos
  let hc : l.length-1+1=l.length := by omega
  let ee : Fin (Fintype.card A) ≃ A := (finCongr hlen.symm).trans e
  let t : DrawTree A := .draw (l.length-1) (fun i => .leaf (e (Fin.cast hc i)))
  have ht : t=DrawTree.uniformVia A ee := uniformVia_size l.length e hlen hc
  apply RealizesLaw.reindex (u:=t)
  · apply Realizes.law
    change Realizes O (letIn (precompose listLength draw) (pure _)) encode l
      ((DrawTree.draw (l.length-1) DrawTree.leaf).bind (fun i => .leaf (e (Fin.cast hc i))))
    apply realizes_letIn O (a:=.list a) (b:=.nat) (c:=a) _ _
      (fun i : Fin (l.length-1+1) => i.val) encode l _ _
    · apply realizes_precompose O (a:=.list a) (b:=.nat) (c:=.nat) listLength draw
        (fun i : Fin (l.length-1+1) => i.val) l l.length _ (run_listLength O l)
      simpa only [hc] using realizes_draw O (l.length-1)
    · intro i
      apply realizes_pure
      simp only [run_compose,run_both,run_fst,run_snd,run_constant,Option.bind_some,Option.map_some]
      rw [run_getDCode]
      rw [List.getD_eq_getElem (l:=l) (d:=zeroValue a) (n:=i.val) (by omega)]
      exact congrArg some (he (Fin.cast hc i))
  · rw [ht]
    exact (DrawTree.uniformVia_reindexed A ee).symm
end Effect

open scoped Classical
open Expression
lemma run_exchangePositionsCode {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O exchangePositionsCode S=some (exchangePositions S) := by
  simp only [exchangePositionsCode,run_compose,run_both,run_append,Option.bind_some,run_membersCode,
    run_wordNot,Option.map_some]
  exact run_productCode O (a:=.nat) (b:=.nat) _ _
lemma exchangeListEquiv_val {n : ℕ} (S : Set (Fin n⊕Fin n))
    (i : Fin (exchangePositions (stateEncode S)).length) :
    (position (exchangeListEquiv S i).1.val,position (exchangeListEquiv S i).2.val)=
      (exchangePositions (stateEncode S)).get i := by
  simp [exchangeListEquiv,exchangePositionEquiv,memberPositionEquiv_val,List.Nodup.getEquiv]

namespace Effect

lemma proposal_source {n : ℕ} (O : IndependenceOracle n) (S : Set (Fin n⊕Fin n))
    [Nonempty (ExchangeChoice S)] :
    RealizesLaw O proposal (fun a : ExchangeChoice S => (position a.1.val,position a.2.val))
      (stateEncode S) (DrawTree.uniformChoice (ExchangeChoice S)) := by
  apply law_precompose O _ _ _ _ _ _ (run_exchangePositionsCode O _)
  exact realizes_uniformList O _ _ (exchangeListEquiv S) (fun i => (exchangeListEquiv_val S i).symm)
end Effect

section
open Expression
open scoped Classical

variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r j : ℕ) (h : List (List (Set (Fin n⊕Fin n))))
local notation "GS" => pairedSlots n
local notation "ctx" => (((r,j),historyEncode h) : Value WeightContext)
local notation "W" => rationalHistory GS id h
local notation "F" => oracleAnneal n r O j
open Effect
include M₁ M₂ hO hE₁ hE₂

lemma offerCore_source (S : ChainIndex GS) (U : Set (Fin n⊕Fin n)) :
    RealizesLaw O offerCore (fun T : ChainIndex GS => stateEncode T.val)
      ((ctx,stateEncode S.val),stateEncode U)
      (if hu : ChainState GS U then
        (DrawTree.bernoulli (rationalAcceptance GS W F S ⟨U,hu⟩)).map
          (fun b => if b then ⟨U,hu⟩ else S)
      else .leaf S) := by
  have ht : run O ((snd (a:=WeightInput) (b:=StateData)) >>> chainCode) ((ctx,stateEncode S.val),stateEncode U)=some (decide (ChainState GS U)) := by
    change run O chainCode (stateEncode U)=_
    rw [run_chainCode,chainValue_source]
  unfold offerCore
  apply law_choose O _ _ _ _ _ _ _ ht
  by_cases hu : ChainState GS U
  · simp only [hu,decide_true,ite_true,dite_eq_left]
    change RealizesLaw O (letIn (precompose _ bernoulliCode) (pure _)) _ _
      ((DrawTree.bernoulli (rationalAcceptance GS W F S ⟨U,hu⟩)).bind (fun b => .leaf (if b then ⟨U,hu⟩ else S)))
    apply law_letIn O (a:=OfferInput) (b:=.bool) (c:=StateData) _ _ id _ _ _ _
    · apply Realizes.law
      apply realizes_precompose O _ _ _ _ (rationalPair (rationalAcceptance GS W F S ⟨U,hu⟩))
      · exact acceptanceCode_source M₁ M₂ O hO hE₁ hE₂ r j h S ⟨U,hu⟩
      · exact bernoulliCode_source O _
    · intro b
      apply Realizes.law
      apply realizes_pure
      cases b <;> rfl
  · simp only [hu,decide_false,Bool.false_eq_true,ite_false]
    exact (realizes_pure O _ _ _ S rfl).law

lemma offerCode_source (S : ChainIndex GS) (a : ExchangeChoice S.val) :
    RealizesLaw O offerCode (fun T : ChainIndex GS => stateEncode T.val)
      ((ctx,stateEncode S.val),(position a.1.val,position a.2.val))
      (rationalExchange GS W F S a) := by
  unfold offerCode
  apply law_precompose O _ _ _ _ ((ctx,stateEncode S.val),stateEncode (exchangedSet S.val a))
  · simp only [run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [exchangeSetCode_source]
    rfl
  · exact offerCore_source M₁ M₂ O hO hE₁ hE₂ r j h S _

lemma activeStepCode_source (S : ChainIndex GS) [Nonempty (ExchangeChoice S.val)] :
    RealizesLaw O activeStepCode (fun T : ChainIndex GS => stateEncode T.val) (ctx,stateEncode S.val)
      ((DrawTree.uniformChoice (ExchangeChoice S.val)).bind (rationalExchange GS W F S)) := by
  unfold activeStepCode
  apply law_letIn O (a:=WeightInput) (b:=NN) (c:=StateData) _ _
    (fun a : ExchangeChoice S.val => (position a.1.val,position a.2.val)) _ _ _ _
  · exact law_precompose O snd proposal _ _ _ _ rfl (proposal_source O S.val)
  · exact offerCode_source M₁ M₂ O hO hE₁ hE₂ r j h S

lemma stepCode_source (hn : 0<n) (S : ChainIndex GS) :
    RealizesLaw O stepCode (fun T : ChainIndex GS => stateEncode T.val) (ctx,stateEncode S.val)
      (rationalMetropolis GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n) W F S) := by
  let : Nonempty (ExchangeChoice S.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]; positivity)
  unfold stepCode rationalMetropolis
  apply law_letIn O (a:=WeightInput) (b:=.bool) (c:=StateData) _ _ id _ _ _ _
  · apply Realizes.law
    exact realizes_precompose O _ bernoulliCode id _ (rationalPair (1/2)) _ (by norm_num [run_constant,rationalPair]) (bernoulliCode_source O _)
  · intro b
    apply law_choose O _ _ _ _ _ _ b rfl
    cases b with
    | false =>
      exact law_precompose O fst activeStepCode _ _ _ _ rfl (activeStepCode_source M₁ M₂ O hO hE₁ hE₂ r j h S)
    | true => exact (realizes_pure O _ _ _ S rfl).law
end

section
open Expression
open scoped Classical

lemma binaryValue_injective_length (x y : Word) (hlen : x.length=y.length)
    (hv : binaryValue x=binaryValue y) : x=y := by
  induction x generalizing y with
  | nil => cases y <;> simp_all
  | cons b x ih =>
    cases y with
    | nil => simp at hlen
    | cons c y =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      have hbc : b=c := by cases b <;> cases c <;> simp_all [binaryValue] <;> omega
      subst c
      have hxy : binaryValue x=binaryValue y := by cases b <;> simp_all [binaryValue]
      rw [ih y hlen hxy]

lemma binaryValue_replicate_false (k : ℕ) : binaryValue (List.replicate k false)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,binaryValue,ih]

lemma padded_range (w : Word) (k : ℕ) (hk : w.length≤k) :
    (List.range k).map (fun i => w[i]?.getD false)=w++List.replicate (k-w.length) false := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    by_cases h : i<w.length
    · rw [List.getElem?_eq_getElem h,List.getElem_append_left h]; rfl
    · rw [List.getElem?_eq_none (by omega),List.getElem_append_right (by omega)]
      simp
namespace Expression

lemma run_paddedBitsCode {n : ℕ} (O : IndependenceOracle n) (k v : ℕ) (hv : v<2^k) :
    run O paddedBitsCode (k,v)=some (List.ofFn ((wordEquiv k).symm ⟨v,hv⟩)) := by
  have hk : v.bits.length≤k := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr hv
  have hr : (List.range k).map (fun i => v.bits[i]?.getD false)=v.bits++List.replicate (k-v.bits.length) false := padded_range _ _ hk
  have he : ((List.range k).map (fun i => v.bits[i]?.getD false)).reverse=
      List.ofFn ((wordEquiv k).symm ⟨v,hv⟩) := by
    apply List.reverse_inj.mp
    simp only [List.reverse_reverse]
    apply binaryValue_injective_length
    · simp
    · rw [hr,binaryValue_append,binaryValue_replicate_false,binaryValue_bits,binaryValue_ofFn_reverse]
      simp
  simp only [paddedBitsCode,run_compose,run_both,run_fst,run_snd,Option.bind_some]
  rw [run_rangeCode]
  change ((run O (mapWith (c:=.word) (Expression.swap >>> wordGet)) (List.range k,v.bits)).bind fun l =>
    (run O fromList l).bind (run O reverse))=_
  rw [run_mapWith O (c:=.word) (Expression.swap >>> wordGet) (fun i w => w[i]?.getD false) (fun i w => run_wordGet O w i)]
  simp only [Option.bind_some]
  rw [run_fromList]
  exact congrArg some he

lemma plainDecodeCode_source {n : ℕ} (O : IndependenceOracle n) (v : Fin (2^n)) :
    run O plainDecodeCode (n,v.val)=some (stateEncode (wordPlainEquiv n ((wordEquiv n).symm v)).val.val) := by
  rw [plainDecodeCode,run_compose,run_paddedBitsCode O n v.val v.isLt,Option.bind_some,run_both,run_ident,Option.bind_some,run_wordNot]
  simp only [Option.map_some]
  congr 1
  change (List.ofFn _,(List.ofFn _).map Bool.not)=_
  unfold stateEncode wordPlainEquiv
  simp only []
  apply Prod.ext
  · apply List.ext_getElem <;> simp [transversal]
  · apply List.ext_getElem <;> simp [transversal]
end Expression
namespace Effect
attribute [local instance] OAI.CommonBasesFPRAS.MachineCode.Effect.instNonemptyPlainIndexSumFinPairedSlots
lemma plainCode_source {n : ℕ} (O : IndependenceOracle n) :
    RealizesLaw O plainCode (fun S : PlainIndex (pairedSlots n) => stateEncode S.val.val) n
      (DrawTree.uniformVia _ (canonicalPlainEnumeration n)) := by
  have hp : 0<2^n := by positivity
  let hc : 2^n-1+1=2^n := by omega
  let e : Fin (2^n) ≃ PlainIndex (pairedSlots n) := (wordEquiv n).symm.trans (wordPlainEquiv n)
  let t : DrawTree (PlainIndex (pairedSlots n)) := .draw (2^n-1) (fun i => .leaf (e (Fin.cast hc i)))
  have ht : t=DrawTree.uniformVia _ (canonicalPlainEnumeration n) := by
    exact uniformVia_size (2^n) e (plainIndex_card n).symm hc
  rw [←ht]
  apply Realizes.law
  change Realizes O (letIn (a:=.nat) (b:=.nat) (c:=StateData) _ _) _ n
    ((DrawTree.draw (2^n-1) DrawTree.leaf).bind (fun i => .leaf (e (Fin.cast hc i))))
  apply realizes_letIn O (a:=.nat) (b:=.nat) (c:=StateData) _ _
    (fun i : Fin (2^n-1+1) => i.val) _ n _ _
  · apply realizes_precompose O _ draw _ _ (2^n)
    · change run O powCode (2,n)=_; exact run_powCode O 2 n
    · simpa only [hc] using realizes_draw O (2^n-1)
  · intro i
    apply realizes_pure
    exact plainDecodeCode_source O (Fin.cast hc i)

end Effect

lemma rationalHistory_map {X : Type*} {n : ℕ} (f : X → List (Set (Fin n⊕Fin n))) (h : List X) :
    rationalHistory (pairedSlots n) id (h.map f)=rationalHistory (pairedSlots n) f h := by
  simp only [rationalHistory,List.foldl_map,id_eq]
lemma historyEncode_take {n : ℕ} (h : List (List (Set (Fin n⊕Fin n)))) (j : ℕ) :
    (historyEncode h).take j=historyEncode (h.take j) := by simp only [historyEncode,List.map_take]

variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N : ℕ) (h : List (PhaseSample n N)) (j : ℕ) (hn : 0<n)
local notation "GS" => pairedSlots n
local notation "ctx" => (((r,j),historyEncode (h.map (observedSets n N))) : Value WeightContext)
open Effect
include M₁ M₂ hO hE₁ hE₂

lemma storedStepCode_source (S : ChainIndex GS) :
    RealizesLaw O storedStepCode (fun T : ChainIndex GS => stateEncode T.val) (ctx,stateEncode S.val)
      (canonicalStepTree n hn r O N h j S) := by
  unfold storedStepCode
  apply law_precompose O storedStepPrep stepCode _ _
    (((r,j),historyEncode ((h.map (observedSets n N)).take j)),stateEncode S.val)
  · simp only [storedStepPrep,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [run_takeCode,historyEncode_take]; rfl
  · have hp := stepCode_source M₁ M₂ O hO hE₁ hE₂ r j
      ((h.map (observedSets n N)).take j) hn S
    have he : rationalHistory GS id ((h.map (observedSets n N)).take j)=rationalStored n N h j := by
      rw [←List.map_take,rationalHistory_map]; rfl
    rw [he] at hp
    exact hp.reindex (canonicalMetropolis_reindexed n hn _ _ S)

lemma traceCode_source (cap : ℕ) (S : PlainIndex GS) :
    RealizesLaw O traceCode (optionEncode (fun T : PlainIndex GS => stateEncode T.val.val))
      (cap+1,(ctx,stateEncode S.val.val)) (canonicalTraceTree n hn r O N h j cap S) := by
  unfold traceCode canonicalTraceTree
  apply law_optionRecode O _ snd
    (fun y : PlainIndex GS => (ctx,stateEncode y.val.val)) _ _ _
  · exact law_hitting O (withContext storedStepCode) (snd >>> Expression.plainCode)
      (fun T : ChainIndex GS => (ctx,stateEncode T.val)) (canonicalStepTree n hn r O N h j)
      (plainPredicate GS)
      (fun T => law_withContext O storedStepCode _ ctx _ _
        (storedStepCode_source M₁ M₂ O hO hE₁ hE₂ r N h j hn T))
      (fun T => plainCode_source O T.val) (cap+1) S.val
  · intro T; rfl
end

section
open Expression
namespace Effect

lemma law_withOptionContext {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Effect (.prod c a) (Optional b)) (e : A → Value b) (ctx : Value c) (x : Value a)
    (t : DrawTree (Option A)) (hp : RealizesLaw O p (optionEncode e) (ctx,x) t) :
    RealizesLaw O (withOptionContext p) (optionEncode (fun y => (ctx,e y))) (ctx,x) t := by
  unfold withOptionContext
  rw [←DrawTree.bind_leaf t]
  apply law_letIn O p _ (optionEncode e) _ _ t DrawTree.leaf hp
  intro y
  apply Realizes.law
  apply realizes_pure
  cases y <;> rfl
end Effect

open Expression
open scoped Classical
section Correct
variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N L : ℕ) (h : List (PhaseSample n N)) (hn : 0<n) (cap : ℕ)
local notation "GS" => pairedSlots n
local notation "tau" => 20*n^4*(n*(L+1)+2)
local notation "ctx" => (((r,historyEncode (h.map (observedSets n N))),(cap,tau)) : Value RestartContext)
local notation "enc" => (fun j (x : PlainIndex GS) => ((ctx,j),stateEncode (Subtype.val (Subtype.val x))))
open Effect
include M₁ M₂ hO hE₁ hE₂
lemma traceAtCode_source (j : ℕ) (x : PlainIndex GS) :
    RealizesLaw O traceAtCode (optionEncode (fun y : PlainIndex GS => stateEncode y.val.val))
      (enc j x) (canonicalTraceTree n hn r O N h j cap x) := by
  apply law_precompose O traceAtPrep traceCode _ _ _ _
  · rfl
  · exact traceCode_source M₁ M₂ O hO hE₁ hE₂ r N h j hn cap x
lemma restartTick_source (j : ℕ) (x : PlainIndex GS) :
    RealizesLaw O restartTick (optionEncode (enc (j+1))) (enc j x)
      (DrawTree.iterate (canonicalTraceTree n hn r O N h (j+1) cap) tau x) := by
  apply law_precompose O restartTickPrep _ _ _ _ _
  · rfl
  · apply law_iterate O (withOptionContext traceAtCode) (enc (j+1)) _ _ tau x
    intro y
    apply law_withOptionContext
    exact traceAtCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn cap (j+1) y
end Correct

open Effect
lemma canonicalRestart_phaseRepeat {n : ℕ} (hn : 0<n) (r : ℕ) (O : IndependenceOracle n)
    (N L : ℕ) (h : List (PhaseSample n N)) (cap k : ℕ) :
    canonicalRestartTree n hn r O N L h cap k =
      ((@DrawTree.uniformVia (PlainIndex (pairedSlots n)) _ (plainIndex_nonempty (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_cover n)) (canonicalPlainEnumeration n)).bind
        (fun x => phaseRepeat (fun j => DrawTree.iterate (canonicalTraceTree n hn r O N h j cap)
          (20*n^4*(n*(L+1)+2))) k x)) := by
  let := plainIndex_nonempty (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_cover n)
  induction k with
  | zero => rfl
  | succ k ih => rw [canonicalRestartTree,ih,Effect.phaseRepeat_bind]

variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N L : ℕ) (h : List (PhaseSample n N)) (hn : 0<n) (cap k : ℕ)
local notation "GS" => pairedSlots n
local notation "tau" => 20*n^4*(n*(L+1)+2)
local notation "ctx" => (((r,historyEncode (h.map (observedSets n N))),(cap,tau)) : Value RestartContext)
local notation "enc" => (fun j (x : PlainIndex GS) => ((ctx,j),stateEncode (Subtype.val (Subtype.val x))))
open Effect
include M₁ M₂ hO hE₁ hE₂
lemma restartCode_source :
    RealizesLaw O restartCode (optionEncode (fun x : PlainIndex GS => stateEncode x.val.val))
      (n,(k,ctx)) (canonicalRestartTree n hn r O N L h cap k) := by
  rw [canonicalRestart_phaseRepeat]
  unfold restartCode
  apply law_optionRecode O _ snd (enc k) _ _ _
  · apply law_letIn O _ _ (fun x : PlainIndex GS => stateEncode x.val.val) _ _ _ _
    · exact law_precompose O fst plainCode _ _ n _ rfl (Effect.plainCode_source O)
    · intro x
      apply law_precompose O restartPrep _ _ _ _ _
      · rfl
      · exact law_phaseRepeat O restartTick enc _
          (restartTick_source M₁ M₂ O hO hE₁ hE₂ r N L h hn cap) k x
  · intro x; rfl
end

open Expression
open scoped Classical
namespace Expression

lemma run_allRange {n : ℕ} (O : IndependenceOracle n) {a} (p : Expression (.prod .nat a) .bool)
    (f : ℕ → Value a → Bool) (hp : ∀ i x,run O p (i,x)=some (f i x)) (m : ℕ) (x : Value a) :
    run O (allRange p) (m,x)=some (decide (∀ i < m,f i x=true)) := by
  simp only [allRange,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_rangeCode]
  simp only [Option.bind_some,run_compose]
  rw [run_mapWith O p f hp,Option.bind_some,run_listAll]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp
end Expression
lemma rationalPair_pos {q : ℚ} (hq : 0 ≤ q) : 0 < (rationalPair q).1 ↔ 0 < q := by
  have hd : (0:ℚ) < (rationalPair q).2 := by exact_mod_cast rationalPair_den q
  conv_rhs => rw [←rationalPair_value hq]
  rw [div_pos_iff_of_pos_right hd]
  exact_mod_cast (Iff.rfl : 0 < (rationalPair q).1 ↔ 0 < (rationalPair q).1)
namespace Expression

lemma run_pairPositiveCode {n : ℕ} (O : IndependenceOracle n) (h : List (List (Word×Word))) (p q : ℕ) :
    run O pairPositiveCode (h,(p,q))=some (decide (0 < historyWeightValue p q h)) := by
  simp only [pairPositiveCode,run_compose]
  rw [run_historyWeightCode]
  simp only [Option.bind_some,run_compose,run_fst]
  rw [run_natEqZero]
  simp only [Option.bind_some,run_boolNot]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
  exact (Nat.pos_iff_ne_zero.symm).trans (rationalPair_pos (historyWeightValue_nonneg p q h))

lemma run_slotRowCode {n : ℕ} (O : IndependenceOracle n) (p m : ℕ) (h : List (List (Word×Word))) :
    run O slotRowCode (p,(m,h))=some (decide (∀ q < m,0 < historyWeightValue p q h)) := by
  change run O (allRange (a:=.prod .nat HistoryData) _) (m,(p,h))=_
  rw [run_allRange (a:=.prod .nat HistoryData) O _ (fun q u => decide (0 < historyWeightValue u.1 q u.2))]
  · simp
  · intro q u; exact run_pairPositiveCode O u.2 u.1 q
lemma run_slotsPositiveCode {n : ℕ} (O : IndependenceOracle n) (m : ℕ) (h : List (List (Word×Word))) :
    run O slotsPositiveCode (m,h)=some (decide (∀ p < m,∀ q < m,0 < historyWeightValue p q h)) := by
  change run O (allRange slotRowCode) (m,(m,h))=_
  rw [run_allRange (a:=.prod .nat HistoryData) O _ (fun p u => decide (∀ q < u.1,0 < historyWeightValue p q u.2))
    (fun p u => run_slotRowCode O p u.1 u.2)]
  simp
lemma run_prefixPositiveCode {n : ℕ} (O : IndependenceOracle n) (j m : ℕ) (h : List (List (Word×Word))) :
    run O prefixPositiveCode (j,(m,h))=some (decide (∀ p < m,∀ q < m,0 < historyWeightValue p q (h.take j))) := by
  simp only [prefixPositiveCode,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_takeCode]
  exact run_slotsPositiveCode O m (h.take j)
lemma run_historyPositiveCode {n : ℕ} (O : IndependenceOracle n) (m : ℕ) (h : List (List (Word×Word))) :
    run O historyPositiveCode (m,h)=some (decide (∀ j ≤ h.length,∀ p < m,∀ q < m,0 < historyWeightValue p q (h.take j))) := by
  simp only [historyPositiveCode,run_compose,run_both,run_snd,run_ident,run_constant,Option.bind_some,Option.map_some]
  rw [run_listLength]
  change run O (allRange prefixPositiveCode) (h.length+1,(m,h))=_
  rw [run_allRange (a:=.prod .nat HistoryData) O _ (fun j u => decide (∀ p < u.1,∀ q < u.1,0 < historyWeightValue p q (u.2.take j)))
    (fun j u => run_prefixPositiveCode O j u.1 u.2)]
  simp only [decide_eq_true_eq,Nat.lt_add_one_iff]
end Expression

lemma rationalHistory_inactive {Γ X : Type*} [DecidableEq Γ] (gs : List (Γ×Γ)) (s : X → List (Set Γ))
    (h : List X) (p q : Γ×Γ) (hp : ¬(p∈gs ∧ q∈gs ∧ p≠q)) : rationalHistory gs s h p q=4 := by
  have hh : ∀ (l : List X) (w : (Γ×Γ) → (Γ×Γ) → ℚ),
      (l.foldl (fun w x => rationalLearn gs w (s x)) w) p q=w p q := by
    intro l
    induction l with
    | nil => intro w; rfl
    | cons x l ih => intro w; rw [List.foldl_cons,ih]; simp [rationalLearn,hp]
  exact hh h _
lemma rationalHistoryPositive_slots {n N : ℕ} (h : List (PhaseSample n N)) :
    rationalHistoryPositive n N h ↔ ∀ j ≤ h.length,∀ p q : Fin n,0 < rationalStored n N h j (slotPair p) (slotPair q) := by
  constructor
  · intro hh j hj p q; exact hh j hj _ _
  · intro hh j hj p q
    by_cases hpq : p∈pairedSlots n ∧ q∈pairedSlots n ∧ p≠q
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hpq.1
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hpq.2.1
      exact hh j hj a b
    · change 0 < rationalHistory _ _ _ p q
      have hz := rationalHistory_inactive (pairedSlots n) (observedSets n N) (h.take j) p q hpq
      rw [hz]; norm_num
lemma historyPositiveCode_source {n N : ℕ} (O : IndependenceOracle n) (h : List (PhaseSample n N)) :
    run O Expression.historyPositiveCode (n,historyEncode (h.map (observedSets n N)))=
      some (decide (rationalHistoryPositive n N h)) := by
  rw [Expression.run_historyPositiveCode]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [rationalHistoryPositive_slots]
  have hlen : (historyEncode (h.map (observedSets n N))).length=h.length := by simp [historyEncode]
  rw [hlen]
  constructor
  · intro hp j hj p q
    have hh := hp j hj p.val p.isLt q.val q.isLt
    rw [historyEncode_take,historyWeight_source,←List.map_take,rationalHistory_map] at hh
    exact hh
  · intro hp j hj p hp' q hq'
    rw [historyEncode_take,historyWeight_source (p:=⟨p,hp'⟩) (r:=⟨q,hq'⟩),←List.map_take,rationalHistory_map]
    exact hp j hj ⟨p,hp'⟩ ⟨q,hq'⟩
end MachineCode

namespace DrawTree
lemma Reindexed.lift_map {A B : Type*} (f : A → B) (t : DrawTree A) (u : DrawTree B)
    (h : Reindexed (t.map f) u) : ∃ v, Reindexed t v ∧ v.map f=u := by
  classical
  induction t generalizing u with
  | leaf a =>
    cases h
    exact ⟨.leaf a,.leaf a,rfl⟩
  | draw w k ih =>
    cases h with
    | draw _ _ l e hh =>
      choose v hv he using fun i => ih i (l (e i)) (hh i)
      refine ⟨.draw w (fun i => v (e.symm i)),.draw w k _ e (by intro i; simpa using hv i),?_⟩
      simp only [DrawTree.map,DrawTree.bind] at he ⊢
      congr 1
      funext i
      simpa using he (e.symm i)
end DrawTree
namespace MachineCode

open Expression
namespace Effect
lemma law_unmap {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b}
    (p : Effect a b) (e : B → Value b) (x : Value a) (t : DrawTree A) (f : A → B)
    (h : RealizesLaw O p e x (t.map f)) : RealizesLaw O p (e ∘ f) x t := by
  rcases h with ⟨u,hu,hp⟩
  obtain ⟨v,hv,rfl⟩ := hu.lift_map f t u
  refine ⟨v,hv,fun bank => ?_⟩
  simpa only [bankEval_map,Option.map_map,Function.comp_def] using hp bank

lemma sampleRepeat_finish {X : Type*} (f : X → DrawTree X) (k : ℕ) (acc : List X) (x : X) :
    (treeRepeat (sampleTickTree f) k (acc,x)).map (fun s => s.1.reverse++[s.2])=
      (DrawTree.sample f k x).map (fun v => acc.reverse++v.toList) := by
  induction k generalizing acc x with
  | zero => rfl
  | succ k ih =>
    simp only [treeRepeat,sampleTickTree,DrawTree.map_bind,DrawTree.bind_map,DrawTree.sample]
    congr 1
    funext y
    rw [ih]
    change (DrawTree.sample f k y).map (fun v => (x::acc).reverse++v.toList)=
      ((DrawTree.sample f k y).map (fun v => (x,v))).map (fun v : X × FiniteChain.Sample X k => acc.reverse++v.1::v.2.toList)
    rw [DrawTree.map_map]
    congr 1
    funext v
    simp [List.reverse_cons,List.append_assoc]

lemma law_sampleTick {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a}
    (p : Effect a a) (e : X → Value a) (f : X → DrawTree X)
    (hp : ∀ x,RealizesLaw O p e (e x) (f x)) (s : List X × X) :
    RealizesLaw O (sampleTick p) (fun u => (u.1.map e,e u.2)) (s.1.map e,e s.2) (sampleTickTree f s) := by
  unfold sampleTick sampleTickTree DrawTree.map
  apply law_letIn O (a:=.prod (.list a) a) (b:=a) (c:=.prod (.list a) a) _ _ e _ _ _ _
  · exact law_precompose O snd p _ _ _ _ rfl (hp s.2)
  · intro y
    exact (realizes_pure O _ _ _ (s.2::s.1,y) rfl).law

lemma law_sample {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a}
    (p : Effect a a) (e : X → Value a) (f : X → DrawTree X)
    (hp : ∀ x,RealizesLaw O p e (e x) (f x)) (k : ℕ) (x : X) :
    RealizesLaw O (sampleCode p) (fun v => v.toList.map e) (k,e x) (DrawTree.sample f k x) := by
  apply law_unmap O (a:=.prod .nat a) (b:=.list a) (sampleCode p)
    (fun l : List X => l.map e) (k,e x) (DrawTree.sample f k x) (fun v => v.toList)
  unfold sampleCode
  apply law_precompose O _ _ _ _ (k,(([] : List (Value a)),e x)) _ rfl
  have he := sampleRepeat_finish f k [] x
  simp only [List.reverse_nil,List.nil_append] at he
  rw [←he]
  apply law_map O _ _ (fun u : List X × X => (u.1.map e,e u.2)) _ _ _ _
  · exact law_repeat O (sampleTick p) _ _ (law_sampleTick O p e f hp) k ([],x)
  · intro u
    simp only [sampleFinish,run_compose,run_both,run_fst,run_snd,run_constant,Option.bind_some,Option.map_some]
    rw [run_listReverse]
    change run O listAppend ((u.1.map e).reverse,[e u.2])=_
    rw [run_listAppend]
    simp
end Effect

section
open Expression
open scoped Classical
namespace Expression
lemma run_mapEach {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression a b)
    (f : Value a → Value b) (hp : ∀ x,run O p x=some (f x)) (xs : List (Value a)) :
    run O (mapEach p) xs=some (xs.map f) := by
  change run O (mapWith (c:=.unit) (fst >>> p)) (xs,())=_
  exact run_mapWith (c:=.unit) O _ (fun x _ => f x) (fun x _ => hp x) xs ()
end Expression
namespace Effect
lemma law_retainOption {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b}
    (p : Effect a (Optional b)) (e : A → Value b) (x : Value a)
    (t : DrawTree (Option A)) (hp : RealizesLaw O p (optionEncode e) x t) :
    RealizesLaw O (retainOption p) (optionEncode (fun y => (x,e y))) x t := by
  unfold retainOption
  rw [←DrawTree.bind_leaf t]
  apply law_letIn O p _ (optionEncode e) _ _ t DrawTree.leaf hp
  intro y
  apply Realizes.law
  apply realizes_pure
  cases y <;> rfl

end Effect
variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N L : ℕ) (h : List (PhaseSample n N)) (hn : 0<n)
local notation "GS" => pairedSlots n
local notation "ctx" => ((params n r N L,historyEncode (h.map (observedSets n N))) : Value PhaseInput)
open Effect
include M₁ M₂ hO hE₁ hE₂
lemma phaseRestartCode_source :
    RealizesLaw O phaseRestartCode (optionEncode (fun x : PlainIndex GS => stateEncode x.val.val)) ctx
      (canonicalRestartTree n hn r O N L h (restartCap n L) h.length) := by
  apply law_precompose O phaseRestartPrep restartCode _ ctx _ _
  · simp only [phaseRestartPrep,params,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [run_listLength]
    simp only [historyEncode,List.length_map]
    rfl
  · exact restartCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn _ _
lemma startCode_source :
    RealizesLaw O startCode (optionEncode (fun x : ChainIndex GS => stateEncode x.val)) ctx
      (canonicalStartTree n hn r O N L h) := by
  apply law_optionMap O phaseRestartCode ident (fun x : PlainIndex GS => stateEncode x.val.val) _ ctx _ Subtype.val
  · exact phaseRestartCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn
  · intro x; rfl
lemma phaseStepCode_source (x : ChainIndex GS) :
    RealizesLaw O phaseStepCode (fun y : ChainIndex GS => stateEncode y.val) (ctx,stateEncode x.val)
      (canonicalStepTree n hn r O N h h.length x) := by
  apply law_precompose O phaseStepPrep storedStepCode _ _ _ _
  · simp only [phaseStepPrep,params,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [run_listLength]
    simp only [historyEncode,List.length_map]
    rfl
  · exact storedStepCode_source M₁ M₂ O hO hE₁ hE₂ r N h h.length hn x
lemma phaseSampleCode_source (x : ChainIndex GS) :
    RealizesLaw O phaseSampleCode (fun v : PhaseSample n N => sampleEncode (observedSets n N v))
      (ctx,stateEncode x.val) (DrawTree.sample (canonicalStepTree n hn r O N h h.length) (N-1) x) := by
  apply law_precompose O phaseSamplePrep _ _ _ _ _
  · simp only [phaseSamplePrep,params,run_both,run_compose,run_fst,run_snd,run_ident,run_constant,Option.bind_some,Option.map_some]
    rw [run_natSub]
    rfl
  · apply law_recode O _ (mapEach snd) (fun v : PhaseSample n N => v.toList.map (fun y => (ctx,stateEncode y.val))) _ _ _
    · exact law_sample O (withContext phaseStepCode) (fun y : ChainIndex GS => (ctx,stateEncode y.val)) _
        (fun y => law_withContext O phaseStepCode _ ctx _ _
          (phaseStepCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn y)) (N-1) x
    · intro v
      rw [run_mapEach O snd Prod.snd (fun _ => rfl)]
      simp only [sampleEncode,observedSets,List.map_map]
      rfl
omit M₁ M₂ hO hE₁ hE₂ in
lemma positiveTest_source : run O positiveTest ctx=some (decide (rationalHistoryPositive n N h)) :=
  historyPositiveCode_source O h
lemma phaseCode_source :
    RealizesLaw O phaseCode (optionEncode (fun v : PhaseSample n N => sampleEncode (observedSets n N v))) ctx
      (canonicalPhaseTree n hn r O N L h) := by
  unfold phaseCode canonicalPhaseTree
  apply law_choose O positiveTest _ _ _ ctx _ (decide (rationalHistoryPositive n N h)) (positiveTest_source O r N L h)
  by_cases hh : rationalHistoryPositive n N h
  · simp only [hh,decide_true,ite_true]
    apply law_optionBind O (retainOption startCode) (someCode phaseSampleCode)
      (fun x : ChainIndex GS => (ctx,stateEncode x.val)) _ ctx _ _
    · exact law_retainOption O startCode _ ctx _ (startCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn)
    · intro x
      exact law_some O phaseSampleCode _ _ _ (phaseSampleCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn x)
  · simp only [hh,decide_false,Bool.false_eq_true,ite_false]
    exact law_none (a:=PhaseInput) O _ ctx
lemma witnessCode_source :
    RealizesLaw O witnessCode (optionEncode (fun x : PlainIndex GS => stateEncode x.val.val)) ctx
      (canonicalWitnessTree n hn r O N L h) := by
  unfold witnessCode canonicalWitnessTree
  apply law_choose O positiveTest _ _ _ ctx _ (decide (rationalHistoryPositive n N h)) (positiveTest_source O r N L h)
  by_cases hh : rationalHistoryPositive n N h
  · simp only [hh,decide_true,ite_true]
    exact phaseRestartCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn
  · simp only [hh,decide_false,Bool.false_eq_true,ite_false]
    exact law_none (a:=PhaseInput) O _ ctx
end

open Expression
namespace Expression
lemma run_mapWith_source {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a b c}
    (p : Expression (.prod a c) b) (e : X → Value a) (f : X → Value b) (ctx : Value c)
    (hp : ∀ x,run O p (e x,ctx)=some (f x)) (xs : List X) :
    run O (mapWith p) (xs.map e,ctx)=some (xs.map f) := by
  have hs : ∀ x (acc : List (Value b)),run O (mapStep p) (e x,(acc,ctx))=some (f x::acc,ctx) := by
    intro x acc
    simp only [mapStep,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
    rw [hp]
    rfl
  have hf : ∀ (ys : List X) (acc : List (Value b)),
      foldValue (run O (mapStep p)) (ys.map e) (acc,ctx)=some ((ys.map f).reverse++acc,ctx) := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons x ys ih => intro acc; simp [foldValue,hs,ih,List.append_assoc]
  simp only [mapWith,run_both,run_compose,run_fst,run_snd,run_constant,Option.bind_some,Option.map_some]
  change (foldValue (run O (mapStep p)) (xs.map e) ([],ctx)).bind (fun z => run O listReverse z.1)=_
  rw [hf,Option.bind_some,run_listReverse]
  simp

lemma run_ratSumCode {n : ℕ} (O : IndependenceOracle n) (xs : List ℚ) (hx : ∀ q∈xs,0≤q) :
    run O ratSumCode (xs.map rationalPair)=some (rationalPair xs.sum) := by
  have hf : ∀ (ys : List ℚ), (∀ q∈ys,0≤q) → ∀ q,0≤q →
      foldValue (run O ratAdd) (ys.map rationalPair) (rationalPair q)=some (rationalPair (q+ys.sum)) := by
    intro ys
    induction ys with
    | nil => intro hy q hq; simp [foldValue]
    | cons y ys ih =>
      intro hy q hq
      rw [List.map_cons,foldValue,run_ratAdd O y q (hy y (by simp)) hq,Option.bind_some]
      rw [ih (fun z hz => hy z (by simp [hz])) (y+q) (add_nonneg (hy y (by simp)) hq)]
      simp [add_left_comm,add_assoc]
  change foldValue (run O ratAdd) (xs.map rationalPair) (rationalPair 0)=_
  simpa using hf xs hx 0 (le_refl 0)
lemma run_ratProductCode {n : ℕ} (O : IndependenceOracle n) (xs : List ℚ) (hx : ∀ q∈xs,0≤q) :
    run O ratProductCode (xs.map rationalPair)=some (rationalPair xs.prod) := by
  have hf : ∀ (ys : List ℚ), (∀ q∈ys,0≤q) → ∀ q,0≤q →
      foldValue (run O ratMul) (ys.map rationalPair) (rationalPair q)=some (rationalPair (q*ys.prod)) := by
    intro ys
    induction ys with
    | nil => intro hy q hq; simp [foldValue]
    | cons y ys ih =>
      intro hy q hq
      rw [List.map_cons,foldValue,run_ratMul O y q (hy y (by simp)) hq,Option.bind_some]
      rw [ih (fun z hz => hy z (by simp [hz])) (y*q) (mul_nonneg (hy y (by simp)) hq)]
      simp [mul_left_comm,mul_assoc]
  change foldValue (run O ratMul) (xs.map rationalPair) (rationalPair 1)=_
  simpa using hf xs hx 1 (by norm_num)

lemma run_natRatCode {n : ℕ} (O : IndependenceOracle n) (k : ℕ) :
    run O natRatCode k=some (rationalPair (k:ℚ)) := by
  change run O normalizeRat (k,1)=_
  simpa using run_normalizeRat_pair O k 1
end Expression

open Expression

open Expression
end MachineCode

namespace DrawTree
lemma All.mono {A : Type*} {t : DrawTree A} {P Q : A → Prop}
    (h : All P t) (hq : ∀ x,P x → Q x) : All Q t := by
  induction t with
  | leaf x => exact hq x h
  | draw v k ih => exact fun i => ih i (h i)
end DrawTree
namespace MachineCode

lemma bankEval_all {A : Type*} (t : DrawTree A) (P : A → Prop)
    (ht : DrawTree.All P t) (bank : Bank) (x : A)
    (hx : (bankEval t bank).1=some x) : P x := by
  induction t generalizing bank with
  | leaf a =>
    have he : a=x := Option.some.inj hx
    exact he ▸ ht
  | draw v k ih =>
    cases bank with
    | nil => cases hx
    | cons row bank =>
      simp only [bankEval] at hx
      split at hx
      · cases hx
      · exact ih _ (ht _) bank hx
open Expression

open Expression

open scoped Classical

open Expression
open Effect
open scoped Classical

end MachineCode

namespace MachineCode

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

section
open Expression
open scoped Classical
variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ) (r : ℕ)
local notation "GS" => pairedSlots n
local notation "f" => (fun S => rationalPlain GS (fun S => rationalRho n^oracleDeficiency n r O S) S)
lemma weightedPlain_nonneg (S : Set (Fin n⊕Fin n)) : 0≤f S := by
  change 0 ≤ if PlainState GS S then rationalRho n ^ oracleDeficiency n r O S else 0
  split_ifs
  · exact pow_nonneg (Expression.rationalRho_nonneg n) _
  · rfl
include M₁ M₂ hO hE₁ hE₂
lemma weightedPlainCode_source (S : Set (Fin n⊕Fin n)) :
    run O weightedPlainCode (r,stateEncode S)=some (rationalPair (f S)) := by
  rw [weightedPlainCode,run_applyIf]
  change ((run O Expression.plainCode (stateEncode S)).bind fun b => _)=_
  rw [plainCode_source]
  by_cases hs : PlainState GS S
  · simp only [hs,decide_true,Option.bind_some,ite_true]
    change run O annealCode (((r,1),historyEncode ([] : List (List (Set (Fin n⊕Fin n))))),stateEncode S)=_
    rw [annealCode_source M₁ M₂ O hO hE₁ hE₂]
    simp only [rationalPlain,hs,ite_true,pow_one]
  · simp only [hs,decide_false,Option.bind_some,Bool.false_eq_true,ite_false,run_constant,rationalPlain]
    rfl
lemma weightedListCode_source (xs : List (Set (Fin n⊕Fin n))) :
    run O weightedListCode (r,sampleEncode xs)=some ((xs.map f).map rationalPair) := by
  change run O (mapWith (Expression.swap >>> weightedPlainCode)) (xs.map stateEncode,r)=_
  rw [run_mapWith_source O (Expression.swap >>> weightedPlainCode) stateEncode (fun S => rationalPair (f S)) r
    (weightedPlainCode_source M₁ M₂ O hO hE₁ hE₂ r) xs]
  simp only [List.map_map,Function.comp_def]
lemma weightedMeanCode_source (xs : List (Set (Fin n⊕Fin n))) :
    run O weightedMeanCode (r,sampleEncode xs)=some (rationalPair (rationalEmpirical f xs)) := by
  rw [weightedMeanCode,run_letIn,weightedListCode_source M₁ M₂ O hO hE₁ hE₂ r xs,Option.bind_some]
  simp only [run_compose,run_both,run_fst,run_snd,Option.bind_some]
  rw [run_ratSumCode O (xs.map f) (by intro q hq; obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hq; exact weightedPlain_nonneg O r S)]
  simp only [Option.bind_some]
  rw [run_listLength]
  simp only [sampleEncode,List.length_map,Option.bind_some]
  rw [run_natRatCode]
  simp only [Option.bind_some,Option.map_some]
  apply run_ratDiv
  · exact List.sum_nonneg (by intro q hq; obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hq; exact weightedPlain_nonneg O r S)
  · positivity
omit M₁ M₂ hO hE₁ hE₂ in
lemma plainMeanCode_source (xs : List (Set (Fin n⊕Fin n))) :
    run O plainMeanCode (r,sampleEncode xs)=some (rationalPair (rationalEmpirical (rationalPlain GS (fun _ => 1)) xs)) := by
  simp only [plainMeanCode,run_compose,run_both,run_snd,Option.bind_some]
  rw [run_countPlainCode,run_listLength]
  simp only [Option.bind_some,Option.map_some]
  rw [run_normalizeRat_pair,countPlainValue_source]
  unfold rationalEmpirical rationalPlain
  dsimp only
  rw [indicator_list_sum]
  simp only [sampleEncode,List.length_map]
lemma ratioCode_source (xs : List (Set (Fin n⊕Fin n))) :
    run O ratioCode (r,sampleEncode xs)=some (rationalPair (rationalRatio GS (fun S => rationalRho n^oracleDeficiency n r O S) xs)) := by
  simp only [ratioCode,run_compose,run_both]
  rw [weightedMeanCode_source M₁ M₂ O hO hE₁ hE₂ r xs,plainMeanCode_source O r xs]
  simp only [Option.bind_some,Option.map_some]
  apply run_ratDiv
  · unfold rationalEmpirical
    apply div_nonneg
    · apply List.sum_nonneg
      intro q hq
      obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hq
      exact weightedPlain_nonneg O r S
    · positivity
  · unfold rationalEmpirical rationalPlain
    rw [indicator_list_sum]
    positivity
end

section
open Expression
namespace Effect

lemma optionRepeat_none {X : Type*} (f : X → DrawTree (Option X)) (k : ℕ) :
    treeRepeat (fun x => match x with | none => .leaf none | some y => f y) k none=.leaf none := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih
lemma iterate_history {X : Type*} (K : List X → DrawTree (Option X)) (k : ℕ) (h : List X) :
    DrawTree.iterate (historyTickTree K) k h=DrawTree.history K k h := by
  rw [←treeRepeat_option]
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    simp only [treeRepeat,historyTickTree,DrawTree.map_bind,DrawTree.history,DrawTree.optionBind]
    congr 1
    funext u
    cases u with
    | none => exact optionRepeat_none _ k
    | some x => exact ih (h++[x])
lemma law_historyTickCode {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a c}
    (p : Effect (.prod c (.list a)) (Optional a)) (e : X → Value a) (ctx : Value c)
    (K : List X → DrawTree (Option X)) (h : List X)
    (hp : RealizesLaw O p (optionEncode e) (ctx,h.map e) (K h)) :
    RealizesLaw O (historyTickCode p) (optionEncode (fun h => (ctx,h.map e))) (ctx,h.map e) (historyTickTree K h) := by
  apply law_optionMap O (retainOption p) _ (fun y => ((ctx,h.map e),e y)) _ _ _ (fun x => h++[x])
  · exact law_retainOption O p e (ctx,h.map e) (K h) hp
  · intro x
    simp only [run_both,run_compose,run_fst,run_snd,run_constant,Option.bind_some,Option.map_some]
    change ((run O listAppend (h.map e,[e x])).map fun l => (ctx,l))=_
    rw [run_listAppend]
    simp

lemma law_historyCode {n : ℕ} (O : IndependenceOracle n) {X : Type*} {a c}
    (p : Effect (.prod c (.list a)) (Optional a)) (e : X → Value a) (ctx : Value c)
    (K : List X → DrawTree (Option X))
    (hp : ∀ h,RealizesLaw O p (optionEncode e) (ctx,h.map e) (K h)) (k : ℕ) (h : List X) :
    RealizesLaw O (historyCode p) (optionEncode (fun h => (ctx,h.map e))) (k,(ctx,h.map e)) (DrawTree.history K k h) := by
  rw [←iterate_history]
  exact law_iterate O (historyTickCode p) _ _ (fun h => law_historyTickCode O p e ctx K h (hp h)) k h
end Effect

open Expression
open scoped BigOperators Classical

lemma historyAtCode_source {n N : ℕ} (O : IndependenceOracle n) (h : List (PhaseSample n N)) (j : ℕ) :
    run O historyAtCode (historyEncode (h.map (observedSets n N)),j)=
      some (sampleEncode (historySample (observedSets n N) h j)) := by
  change run O getDCode ((historyEncode (h.map (observedSets n N)),j),[])=_
  rw [run_getDCode]
  unfold historyEncode historySample
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h[j]? <;> rfl
lemma ratio_nonnegative {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (xs : List (Set (Fin n⊕Fin n))) :
    0≤rationalRatio (pairedSlots n) (fun S => rationalRho n^oracleDeficiency n r O S) xs := by
  unfold rationalRatio rationalEmpirical
  apply div_nonneg
  · apply div_nonneg
    · apply List.sum_nonneg
      intro q hq
      obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hq
      exact weightedPlain_nonneg O r S
    · positivity
  · apply div_nonneg
    · unfold rationalPlain
      rw [indicator_list_sum]
      positivity
    · positivity
variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ) (r N L : ℕ)
local notation "GS" => pairedSlots n
include M₁ M₂ hO hE₁ hE₂
lemma ratioAtCode_source (h : List (PhaseSample n N)) (j : ℕ) :
    run O ratioAtCode (j,(params n r N L,historyEncode (h.map (observedSets n N))))=
      some (rationalPair (rationalRatio GS (fun S => rationalRho n^oracleDeficiency n r O S)
        (historySample (observedSets n N) h j))) := by
  simp only [ratioAtCode,run_compose,run_both,run_fst,run_snd,params,Option.bind_some,Option.map_some]
  rw [historyAtCode_source]
  simp only [Option.bind_some,Option.map_some]
  exact ratioCode_source M₁ M₂ O hO hE₁ hE₂ r _
lemma estimateCode_source (h : List (PhaseSample n N)) :
    run O estimateCode (params n r N L,historyEncode (h.map (observedSets n N)))=
      some (rationalPair (oracleEstimate n r O N L h)) := by
  simp only [estimateCode,run_compose,run_both,run_fst,run_snd,run_ident,run_constant,params,Option.bind_some,Option.map_some]
  rw [run_powCode,Option.bind_some,run_natRatCode,Option.bind_some,run_rangeCode]
  simp only [Option.bind_some]
  let f : ℕ → ℚ := fun j => rationalRatio GS (fun S => rationalRho n^oracleDeficiency n r O S)
    (historySample (observedSets n N) h j)
  have hm := run_mapWith_source O ratioAtCode id (fun j => rationalPair (f j))
    (params n r N L,historyEncode (h.map (observedSets n N)))
    (ratioAtCode_source M₁ M₂ O hO hE₁ hE₂ r N L h) (List.range L)
  simp only [List.map_id,params] at hm
  rw [run_compose,hm]
  simp only [Option.bind_some]
  have he : (List.range L).map (fun j => rationalPair (f j))=((List.range L).map f).map rationalPair := by
    simp only [List.map_map,Function.comp_def]
  rw [he,run_ratProductCode O _ (by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    exact ratio_nonnegative O r _)]
  simp only [Option.bind_some,Option.map_some]
  rw [run_ratMul O _ _ (by positivity) (by
    apply List.prod_nonneg
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    exact ratio_nonnegative O r _)]
  congr 2
  unfold oracleEstimate
  rw [Nat.cast_pow,Nat.cast_ofNat]
  congr 1
lemma guardCode_source (h : List (PhaseSample n N)) (x : PlainIndex GS) :
    run O guardCode ((params n r N L,historyEncode (h.map (observedSets n N))),stateEncode x.val.val)=
      some (rationalPair (oracleGuard n r O N L h x)) := by
  rw [guardCode,run_applyIf]
  simp only [run_compose,run_both,run_fst,run_snd,params,Option.bind_some,Option.map_some]
  rw [deficiencyCode_source M₁ M₂ O hO hE₁ hE₂ r _ _ (stateEncode_left_length _) (stateEncode_right_length _),
    stateEncode_repr,Option.bind_some,run_natEqZero]
  by_cases hz : oracleDeficiency n r O x.val.val=0
  · simp only [hz,decide_true,Option.bind_some,ite_true]
    simpa only [params,oracleGuard,hz,ite_true] using estimateCode_source M₁ M₂ O hO hE₁ hE₂ r N L h
  · simp only [hz,decide_false,Option.bind_some,Bool.false_eq_true,ite_false,run_constant,oracleGuard]
    rfl
end

section
open Expression
open Effect
open scoped Classical
variable {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (r N L : ℕ) (hn : 0<n)
local notation "GS" => pairedSlots n
include M₁ M₂ hO hE₁ hE₂
lemma algorithmHistoryCode_source :
    RealizesLaw O algorithmHistoryCode
      (optionEncode (fun h : List (PhaseSample n N) => (params n r N L,historyEncode (h.map (observedSets n N)))))
      (params n r N L) (DrawTree.history (canonicalPhaseTree n hn r O N L) L []) := by
  apply law_precompose O _ _ _ _ _ _ rfl
  have hh := law_historyCode O phaseCode (fun v : PhaseSample n N => sampleEncode (observedSets n N v))
    (params n r N L) (canonicalPhaseTree n hn r O N L)
    (fun h => by
      simpa only [historyEncode,List.map_map,Function.comp_def] using
        phaseCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn) L []
  simpa only [historyEncode,List.map_map,Function.comp_def,List.map_nil] using hh
lemma finalGuardCode_source (h : List (PhaseSample n N)) :
    RealizesLaw O finalGuardCode (optionEncode rationalPair)
      (params n r N L,historyEncode (h.map (observedSets n N)))
      ((canonicalWitnessTree n hn r O N L h).map (Option.map (oracleGuard n r O N L h))) := by
  apply law_optionMap O (retainOption witnessCode) guardCode
    (fun x : PlainIndex GS => ((params n r N L,historyEncode (h.map (observedSets n N))),stateEncode x.val.val))
    rationalPair _ _ (oracleGuard n r O N L h)
  · exact law_retainOption O witnessCode _ _ _ (witnessCode_source M₁ M₂ O hO hE₁ hE₂ r N L h hn)
  · exact guardCode_source M₁ M₂ O hO hE₁ hE₂ r N L h

lemma algorithmCode_source :
    RealizesLaw O algorithmCode (optionEncode rationalPair) (params n r N L)
      (canonicalAlgorithmTree n hn r O N L) := by
  exact law_optionBind O algorithmHistoryCode finalGuardCode
    (fun h : List (PhaseSample n N) => (params n r N L,historyEncode (h.map (observedSets n N))))
    rationalPair (params n r N L) _ _
    (algorithmHistoryCode_source M₁ M₂ O hO hE₁ hE₂ r N L hn)
    (fun h => finalGuardCode_source M₁ M₂ O hO hE₁ hE₂ r N L hn h)
end

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open scoped Classical

open Expression

namespace Expression

lemma run_insertStep {n : ℕ} (O : IndependenceOracle n) (q x : ℚ) (hq : 0≤q) (hx : 0≤x)
    (xs ys : List ℚ) :
    run O insertStep (rationalPair x,(rationalPair q,(xs.map rationalPair,ys.map rationalPair)))=
      some (rationalPair q,((x::xs).map rationalPair,
        (if x<q then x::ys else q::x::xs).map rationalPair)) := by
  simp only [insertStep,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some,run_applyIf]
  rw [run_ratLess O x q hx hq]
  by_cases h : x<q <;> simp [h,run]
lemma run_insertRatCode {n : ℕ} (O : IndependenceOracle n) (q : ℚ) (hq : 0≤q)
    (xs : List ℚ) (hx : ∀ x∈xs,0≤x) :
    run O insertRatCode (rationalPair q,xs.map rationalPair)=
      some ((xs.orderedInsert (·≤·) q).map rationalPair) := by
  have hf : ∀ xs : List ℚ,(∀x∈xs,0≤x) →
      foldValue (run O insertStep) (xs.map rationalPair).reverse
        (rationalPair q,([], [rationalPair q]))=
      some (rationalPair q,(xs.map rationalPair,(xs.orderedInsert (·≤·) q).map rationalPair)) := by
    intro xs
    induction xs with
    | nil => intro hx; rfl
    | cons x xs ih =>
      intro hx
      simp only [List.map_cons,List.reverse_cons,foldValue_append]
      rw [ih (fun y hy => hx y (by simp [hy])),Option.bind_some,foldValue]
      rw [run_insertStep O q x hq (hx x (by simp)),Option.bind_some]
      simp only [foldValue,List.orderedInsert_cons]
      by_cases h : x<q
      · simp [h,not_le.mpr h]
      · simp [h,le_of_not_gt h]
  simp only [insertRatCode,insertInit,run_compose,run_both,run_fst,run_snd,run_constant,Option.bind_some,Option.map_some]
  rw [run_listReverse]
  change ((foldValue (run O insertStep) (xs.map rationalPair).reverse
    (rationalPair q,([],[rationalPair q]))).bind fun z => some z.2.2)=_
  rw [hf xs hx]
  rfl
lemma run_sortRatCode {n : ℕ} (O : IndependenceOracle n) (xs : List ℚ) (hx : ∀ x∈xs,0≤x) :
    run O sortRatCode (xs.map rationalPair)=some ((xs.mergeSort (·≤·)).map rationalPair) := by
  have hf : ∀ xs : List ℚ,(∀x∈xs,0≤x) →
      foldValue (run O insertRatCode) (xs.map rationalPair).reverse []=
      some ((xs.insertionSort (·≤·)).map rationalPair) := by
    intro xs
    induction xs with
    | nil => intro hx; rfl
    | cons x xs ih =>
      intro hx
      simp only [List.map_cons,List.reverse_cons,foldValue_append]
      rw [ih (fun y hy => hx y (by simp [hy])),Option.bind_some,foldValue]
      rw [run_insertRatCode O x (hx x (by simp)) _ (by
        intro y hy
        exact hx y (by simpa using Or.inr ((List.perm_insertionSort _ _).mem_iff.mp hy)))]
      rfl
  simp only [sortRatCode,run_compose,run_both,run_constant,run_listReverse,Option.bind_some,Option.map_some]
  change foldValue (run O insertRatCode) (xs.map rationalPair).reverse []=_
  rw [hf xs hx,List.mergeSort_eq_insertionSort]
lemma run_medianCode {n : ℕ} (O : IndependenceOracle n) (xs : List ℚ) (hx : ∀ x∈xs,0≤x) :
    run O medianCode (xs.map rationalPair)=some (rationalPair (rationalMedian xs)) := by
  simp only [medianCode,run_compose,run_both,run_ident,run_constant]
  rw [run_sortRatCode O xs hx]
  simp only [Option.bind_some,Option.map_some]
  rw [run_listLength]
  simp only [Option.bind_some,List.length_map]
  simp only [run_compose,run_both,run_constant,run_ident,Option.bind_some,Option.map_some]
  rw [run_natDiv]
  simp only [Option.bind_some,Option.map_some]
  rw [run_getDCode]
  unfold rationalMedian
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (xs.mergeSort (·≤·))[xs.length/2]? <;> rfl
end Expression

namespace Expression

lemma run_singleCode {n : ℕ} (O : IndependenceOracle n) (x : Value AlgorithmParams)
    (t : DrawTree (Option ℚ))
    (ht : Effect.Realizes O Effect.algorithmCode (optionEncode rationalPair) x t)
    (bank : Bank) :
    run O singleCode (x,bank)=some (rationalPair ((bankEval t bank).1.join.getD 0)) := by
  rw [singleCode,run_compose,ht,Option.bind_some]
  cases h : (bankEval t bank).1 with
  | none => rfl
  | some v =>
    cases v <;> rfl
lemma run_amplifiedCode {n : ℕ} (O : IndependenceOracle n) (x : Value AlgorithmParams)
    (t : DrawTree (Option ℚ))
    (ht : Effect.Realizes O Effect.algorithmCode (optionEncode rationalPair) x t)
    (banks : List Bank) (hz : ∀ bank∈banks,0≤(bankEval t bank).1.join.getD 0) :
    run O amplifiedCode (x,banks)=
      some (rationalPair (rationalMedian (banks.map (fun bank => (bankEval t bank).1.join.getD 0)))) := by
  simp only [amplifiedCode,run_compose]
  change ((run O (mapWith (swap >>> singleCode)) (banks,x)).bind (run O medianCode))=_
  have hm := run_mapWith_source O (swap >>> singleCode) (fun bank : Bank => bank)
    (fun bank => rationalPair ((bankEval t bank).1.join.getD 0)) x
    (fun bank => by change run O singleCode (x,bank)=_; exact run_singleCode O x t ht bank) banks
  simp only [List.map_id_fun',id_eq] at hm
  rw [hm]
  simp only [Option.bind_some]
  rw [show banks.map (fun bank => rationalPair ((bankEval t bank).1.join.getD 0))=
    (banks.map (fun bank => (bankEval t bank).1.join.getD 0)).map rationalPair by simp only [List.map_map]; rfl]
  apply run_medianCode
  intro q hq
  obtain ⟨bank,hbank,rfl⟩ := List.mem_map.mp hq
  exact hz bank hbank
end Expression

open Expression Effect

open Expression
namespace Expression

lemma run_chunkStep {n : ℕ} (O : IndependenceOracle n) {a : DataType}
    (i h : ℕ) (xs : List (Value a)) :
    run O chunkStep (i,(xs,h))=some ((xs.drop (i*h)).take h) := by
  simp only [chunkStep,prodE,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  simp only [run,Option.map_some,Option.bind_some]
  rw [run_dropCode,Option.bind_some,Option.bind_some,run_takeCode]
lemma run_chunksCode {n : ℕ} (O : IndependenceOracle n) {a : DataType}
    (xs : List (Value a)) (m h : ℕ) :
    run O chunksCode (xs,(m,h))=some (chunkValues m h xs) := by
  simp only [chunksCode,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_rangeCode,Option.bind_some,Option.bind_some]
  exact run_mapWith O chunkStep (fun i ctx => (ctx.1.drop (i*ctx.2)).take ctx.2)
    (fun i ctx => run_chunkStep O i ctx.2 ctx.1) _ _
lemma chunkValues_succ {α : Type*} (m h : ℕ) (xs : List α) :
    chunkValues (m+1) h xs=xs.take h::chunkValues m h (xs.drop h) := by
  simp only [chunkValues,List.range_succ_eq_map,List.map_cons,List.map_map,Nat.zero_mul,List.drop_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply,Nat.succ_eq_add_one,List.drop_drop,Nat.add_mul,Nat.one_mul,Nat.add_comm h]
lemma chunkValues_flatten {α : Type*} (h : ℕ) (xs : List (List α))
    (hx : ∀ x∈xs,x.length=h) : chunkValues xs.length h xs.flatten=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    rw [List.length_cons,chunkValues_succ,List.flatten_cons,←hh,List.take_left,List.drop_left,hh,ht]
lemma chunkValues_ofFn {α : Type*} (m h : ℕ) (f : Fin m → Fin h → α) :
    chunkValues m h ((List.ofFn (fun i => List.ofFn (f i))).flatten)=
      List.ofFn (fun i => List.ofFn (f i)) := by
  convert chunkValues_flatten h (List.ofFn (fun i => List.ofFn (f i))) (by
    intro xs hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact List.length_ofFn) using 1 ; simp
end Expression
open Expression Effect
namespace Expression
lemma run_rowsCode {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (D H : ℕ) :
    run O rowsCode (xs,(D,H))=some (chunkValues D H xs) := by
  rw [rowsCode,run_compose,run_chunksCode,Option.bind_some]
  simpa using run_mapEach O fromList (fun x => x) (run_fromList O) (chunkValues D H xs)
lemma run_bankCode {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (M D H : ℕ) :
    run O bankCode (xs,(M,(D,H)))=
      some ((chunkValues M (D*H) xs).map (chunkValues D H)) := by
  simp only [bankCode,prodE,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  simp only [run,Option.map_some,Option.bind_some,Option.bind_assoc]
  change ((run O chunksCode (xs,(M,D*H))).bind fun ys => run O (mapWith rowsCode) (ys,(D,H)))=_
  rw [run_chunksCode,Option.bind_some]
  exact run_mapWith O rowsCode (fun ys ctx => chunkValues ctx.1 ctx.2 ys)
    (fun ys ctx => run_rowsCode O ys ctx.1 ctx.2) _ _
lemma run_banksCode {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (R M D H : ℕ) :
    run O banksCode (xs,(R,(M,(D,H))))=
      some ((chunkValues R (M*(D*H)) xs).map (fun ys =>
        (chunkValues M (D*H) ys).map (chunkValues D H))) := by
  simp only [banksCode,prodE,run_compose,run_both,run_fst,run_snd,Option.bind_some,Option.map_some]
  simp only [run,Option.map_some,Option.bind_some,Option.bind_assoc]
  change ((run O chunksCode (xs,(R,M*(D*H)))).bind fun ys => run O (mapWith bankCode) (ys,(M,(D,H))))=_
  rw [run_chunksCode,Option.bind_some]
  exact run_mapWith O bankCode (fun ys ctx =>
    (chunkValues ctx.1 (ctx.2.1*ctx.2.2) ys).map (chunkValues ctx.2.1 ctx.2.2))
    (fun ys ctx => run_bankCode O ys ctx.1 ctx.2.1 ctx.2.2) _ _
end Expression

open Expression

open Expression

open Expression Effect

open Expression

open Expression

open Expression Effect
open scoped Classical
lemma treeBankOutput_all (t : DrawTree (Option ℚ)) (Z : ℕ)
    (ht : DrawTree.All (fun a : Option ℚ => ∀ z,a=some z → 0≤z ∧ (Z=0 → z=0)) t)
    (bank : Bank) : 0≤treeBankOutput t bank ∧ (Z=0 → treeBankOutput t bank=0) := by
  unfold treeBankOutput
  cases h : (bankEval t bank).1 with
  | none => simp
  | some a =>
    cases a with
    | none => simp
    | some z =>
      simpa only [Option.join_some,Option.getD_some] using bankEval_all t _ ht bank (some z) h z rfl
lemma treeBanksOutput_all (t : DrawTree (Option ℚ)) (Z : ℕ)
    (ht : DrawTree.All (fun a : Option ℚ => ∀ z,a=some z → 0≤z ∧ (Z=0 → z=0)) t)
    (banks : List Bank) : 0≤treeBanksOutput t banks ∧ (Z=0 → treeBanksOutput t banks=0) := by
  constructor
  · apply rationalMedian_all (fun z => 0≤z) _ (by norm_num)
    intro z hz
    obtain ⟨bank,hbank,rfl⟩ := List.mem_map.mp hz
    exact (treeBankOutput_all t Z ht bank).1
  · intro hZ
    apply rationalMedian_all (fun z => z=0) _ rfl
    intro z hz
    obtain ⟨bank,hbank,rfl⟩ := List.mem_map.mp hz
    exact (treeBankOutput_all t Z ht bank).2 hZ
lemma reindexed_bank_law {t u : DrawTree (Option ℚ)} (h : DrawTree.Reindexed t u)
    (H D M : ℕ) (ht : DrawTree.Fits H M t) (φ : ℚ → ℝ) :
    uniformAverage (fun bits : Fin M → Fin D → BitWord H => φ (treeBankOutput u (bankEncode bits)))=
      uniformAverage (fun bits : Fin M → Fin D → BitWord H => φ ((DrawTree.run H D M t bits).join.getD 0)) := by
  unfold treeBankOutput
  simp only [bankEval_run H D M u (h.fits H M ht)]
  exact (h.run_observable H D M ht (fun a : Option (Option ℚ) => φ (a.join.getD 0))).symm
lemma reindexed_banks_law {t u : DrawTree (Option ℚ)} (h : DrawTree.Reindexed t u)
    (H D M R : ℕ) (ht : DrawTree.Fits H M t) (φ : ℚ → ℝ) :
    uniformAverage (fun bits : Fin R → Fin M → Fin D → BitWord H =>
      φ (treeBanksOutput u (List.ofFn (fun i => bankEncode (bits i)))))=
      uniformAverage (fun bits : Fin R → Fin M → Fin D → BitWord H =>
        φ (rationalMedian (List.ofFn (fun i => (DrawTree.run H D M t (bits i)).join.getD 0)))) := by
  simp only [treeBanksOutput,List.map_ofFn,Function.comp_def]
  exact uniformAverage_independent_eq (fun bits => treeBankOutput u (bankEncode bits))
    (fun bits => (DrawTree.run H D M t bits).join.getD 0) (reindexed_bank_law h H D M ht) R
    (fun z => φ (rationalMedian (List.ofFn z)))
lemma canonicalTree_all {n : ℕ} (hn : 0<n) (r N L : ℕ) (M₁ M₂ : Matroid (Fin n))
    (O : IndependenceOracle n) (hO : ExactOracles M₁ M₂ O)
    (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞)) :
    DrawTree.All (fun a : Option ℚ => ∀ z,a=some z → 0≤z ∧ (commonBaseCount M₁ M₂=0 → z=0))
      (canonicalAlgorithmTree n hn r O N L) := by
  apply DrawTree.All.mono
    ((canonicalAlgorithmTree_to_rational n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂).symm.all _
      (rationalAlgorithmTree_all n hn M₁ M₂ N L))
  intro a ha z hz
  exact ⟨(ha z hz).1,(ha z hz).2 hE₂ (hr₁.trans hr₂.symm)⟩

open Expression
lemma bitMatrix_apply (a b : ℕ) (w : BitWord (a*b)) (i : Fin a) (j : Fin b) :
    bitMatrixEquiv a b w i j=w (finProdFinEquiv (i,j)) := rfl
lemma ofFn_bitMatrix (a b : ℕ) (w : BitWord (a*b)) :
    List.ofFn w=(List.ofFn (fun i => List.ofFn (bitMatrixEquiv a b w i))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [bitMatrix_apply]
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
lemma chunks_bitMatrix (a b : ℕ) (w : BitWord (a*b)) :
    chunkValues a b (List.ofFn w)=List.ofFn (fun i => List.ofFn (bitMatrixEquiv a b w i)) := by
  rw [ofFn_bitMatrix,chunkValues_ofFn]
lemma run_banksCode_four {n : ℕ} (O : IndependenceOracle n) (R M D H : ℕ)
    (w : BitWord (R*(M*(D*H)))) :
    run O banksCode (List.ofFn w,(R,(M,(D,H))))=
      some (List.ofFn (fun i => bankEncode (fourBitEquiv R M D H w i))) := by
  rw [run_banksCode]
  simp only [chunks_bitMatrix,List.map_ofFn,Function.comp_def]
  rfl
lemma run_reshapeCode_four {n : ℕ} (O : IndependenceOracle n) (R M H : ℕ)
    (w : BitWord (R*(M*((M+6)*H)))) :
    run O reshapeCode (List.ofFn w,(R,(M,H)))=
      some (List.ofFn (fun i => bankEncode (fourBitEquiv R M (M+6) H w i))) := by
  change run O banksCode (List.ofFn w,(R,(M,(M+6,H))))=_
  exact run_banksCode_four O R M (M+6) H w
lemma run_reshapeCode_cast {n a : ℕ} (O : IndependenceOracle n) (R M H : ℕ)
    (h : a=R*(M*((M+6)*H))) (w : BitWord a) :
    run O reshapeCode (List.ofFn w,(R,(M,H)))=
      some (List.ofFn (fun i => bankEncode (fourBitEquiv R M (M+6) H
        ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) w) i))) := by
  subst a
  exact run_reshapeCode_four O R M H w

lemma run_reshapeCode_equiv {n a : ℕ} (O : IndependenceOracle n) (R M H : ℕ)
    (h : a=R*(M*((M+6)*H))) (w : BitWord a) :
    run O reshapeCode (List.ofFn w,(R,(M,H)))=
      some (List.ofFn (fun i => bankEncode (bankReshapeEquiv R M H h w i))) := by
  exact run_reshapeCode_cast O R M H h w
lemma run_reshapeCode_source {n : ℕ} (O : IndependenceOracle n) (ε δ : ℚ)
    (w : BitWord (fairBitCount n ε δ)) :
    let L := annealLength n (accuracyExponent ε)
    let N := sampleCount n L ε
    run O reshapeCode (List.ofFn w,(repetitionCount δ,(algorithmDrawBound n N L,drawWordBound n N L)))=
      some (List.ofFn (fun i => bankEncode (reshapeWordEquiv n ε δ w i))) := by
  exact run_reshapeCode_equiv O _ _ _ (reshape_count n ε δ) w

open Expression
open scoped Classical

lemma run_reshapePrepared_generic {n : ℕ} (O : IndependenceOracle n) (w : Word)
    (p : Value AlgorithmParams) (shape : Value BankShape) (banks : Value (.list BankData))
    (h : run O reshapeCode (w,shape)=some banks) :
    run O reshapePrepared (w,(p,shape))=some (p,banks) := by
  simp only [reshapePrepared,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some,h]
lemma run_reshapePrepared {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ)
    (w : BitWord (fairBitCount n ε δ)) :
    let L := annealLength n (accuracyExponent ε)
    let N := sampleCount n L ε
    run O reshapePrepared (rawValue n r ε δ w)=
      some (params n r N L,List.ofFn (fun i => bankEncode (reshapeWordEquiv n ε δ w i))) := by
  exact run_reshapePrepared_generic O _ _ _ _ (run_reshapeCode_source O ε δ w)

lemma output_certificate_oai {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞))
    (ε δ : ℚ) : ∃ v,OutputCertificate r M₁ M₂ O ε δ v := by
  let L := annealLength n (accuracyExponent ε)
  let N := sampleCount n L ε
  by_cases hn : 0<n
  · obtain ⟨u,hu,he⟩ := algorithmCode_source M₁ M₂ O hO hE₁ hE₂ r N L hn
    have ht := canonicalTree_all hn r N L M₁ M₂ O hO hE₁ hE₂ hr₁ hr₂
    have huall := hu.all _ ht
    let v : BitWord (fairBitCount n ε δ) → ℚ := fun w =>
      treeBanksOutput u (List.ofFn (fun i => bankEncode (reshapeWordEquiv n ε δ w i)))
    refine ⟨v,?_,?_,?_⟩
    · intro w
      rw [postambleCode,run_compose,run_reshapePrepared,Option.bind_some]
      have hz : ∀ bank∈List.ofFn (fun i => bankEncode (reshapeWordEquiv n ε δ w i)),
          0≤(bankEval u bank).1.join.getD 0 := fun bank _ => (treeBankOutput_all u _ huall bank).1
      have hh := run_amplifiedCode O (params n r N L) u he _ hz
      have hc : run O (Expression.compose fst (Expression.compose fst (Expression.compose fst natEqZero)) : Expression AmplifyInput .bool)
          (params n r N L,List.ofFn (fun i => bankEncode (reshapeWordEquiv n ε δ w i)))=some false := by
        simp [params,run_natEqZero,run_compose,run_fst,ne_of_gt hn]
      rw [finishCode,run_applyIf,hc,Option.bind_some]
      simp only [Bool.false_eq_true,ite_false]
      exact hh
    · intro w; exact treeBanksOutput_all u _ huall _
    · intro φ
      have hfit := canonicalAlgorithmTree_fits n hn r O N L M₁ M₂ hO hE₁ hE₂ hr₁ hr₂
        (by dsimp [N,sampleCount]; omega)
      have hb := reindexed_banks_law hu (drawWordBound n N L) (algorithmDrawBound n N L+6)
        (algorithmDrawBound n N L) (repetitionCount δ) hfit φ
      calc
        _ = uniformAverage (fun banks : FPRASBank n ε δ =>
            φ (treeBanksOutput u (List.ofFn (fun i => bankEncode (banks i))))) :=
          uniformAverage_equiv (reshapeWordEquiv n ε δ) _
        _ = _ := by simpa only [canonicalBoundedOutput,dite_eq_left hn,
          canonicalAmplifiedOutput,canonicalFairOutput] using hb
  · refine ⟨fun _ => 1,?_,?_,?_⟩
    · intro w
      rw [postambleCode,run_compose,run_reshapePrepared,Option.bind_some]
      have hc : run O (Expression.compose fst (Expression.compose fst (Expression.compose fst natEqZero)) : Expression AmplifyInput .bool)
          (params n r N L,List.ofFn (fun i => bankEncode (reshapeWordEquiv n ε δ w i)))=some true := by
        simp [params,run_natEqZero,run_compose,run_fst,show n=0 by omega]
      rw [finishCode,run_applyIf,hc,Option.bind_some,ite_eq_left rfl]
      rfl
    · intro w
      have hn0 : n=0 := by omega
      subst n
      simp [commonBaseCount_empty]
    · intro φ
      simp only [canonicalBoundedOutput,dite_eq_right hn,uniformAverage_const]

open Expression

open scoped Classical

end MachineCode
end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end

theorem solution : type_of% @OAI.CommonBasesFPRAS.MachineCode.output_certificate_oai := @OAI.CommonBasesFPRAS.MachineCode.output_certificate_oai
