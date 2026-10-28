-- Prove2me | solution 1 for OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:48:52.880197+00:00
-- url     : https://prove2.me/submissions/de4a4e30-76d5-443b-b681-af694dc79a5b

import Mathlib
import Definitions.Def_OAIQ045S002

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem Law.le_map (p : Law α) (f : α → β) (a : α) :
    p.mass a ≤ (p.map f).mass (f a) := by
  apply single_le_sum (fun b hb => p.nonneg b)
  simp

theorem entropy_map_le (p : Law α) (f : α → β) : entropy (p.map f) ≤ entropy p := by
  rw [entropy_map,entropy]
  apply neg_le_neg
  apply sum_le_sum
  intro a ha
  by_cases hz : p.mass a = 0
  · simp [hz]
  apply mul_le_mul_of_nonneg_left _ (p.nonneg a)
  exact Real.log_le_log (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz)) (p.le_map f a)

theorem Law.snd_mul_condFst (p : Law (α × β)) (a : α) (b : β) :
    p.snd.mass b*(p.condFst b).mass a = p.mass (a,b) := by
  by_cases h : p.snd.mass b = 0
  · rw [h,zero_mul]
    exact (le_antisymm (by simpa [h] using p.le_snd a b) (p.nonneg _)).symm
  · rw [p.condFst_mass b h a]
    field_simp

theorem entropy_chain (p : Law (α × β)) :
    entropy p = entropy p.snd+∑ b, p.snd.mass b*entropy (p.condFst b) := by
  have pointwise (a : α) (b : β) :
      p.mass (a,b)*Real.log (p.mass (a,b)) =
      p.mass (a,b)*Real.log (p.snd.mass b)+
      p.snd.mass b*((p.condFst b).mass a*Real.log ((p.condFst b).mass a)) := by
    by_cases hp : p.mass (a,b) = 0
    · have hh := p.snd_mul_condFst a b
      rw [hp] at hh
      simp only [hp,zero_mul,zero_add]
      rw [← mul_assoc,hh,zero_mul]
    have hs : 0 < p.snd.mass b := (lt_of_le_of_ne (p.nonneg (a,b)) (Ne.symm hp)).trans_le (p.le_snd a b)
    rw [p.condFst_mass b hs.ne', Real.log_div hp hs.ne']
    field_simp
    ring
  unfold entropy
  rw [Fintype.sum_prod_type, sum_comm]
  simp_rw [pointwise, sum_add_distrib, ← mul_sum, ← sum_mul]
  change -((∑ b, p.snd.mass b*Real.log (p.snd.mass b))+
    ∑ b, p.snd.mass b*∑ a, (p.condFst b).mass a*Real.log ((p.condFst b).mass a)) = _
  simp only [mul_neg, sum_neg_distrib]
  ring

end SharpLogRamsey.Selection
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_DivergenceMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem entropy_map_eq_of_leftInverse (p : Law α) (f : α → β) (g : β → α)
    (h : Function.LeftInverse g f) : entropy (p.map f) = entropy p := by
  apply le_antisymm (entropy_map_le p f)
  have hh := entropy_map_le (p.map f) g
  have he : g ∘ f = id := funext h
  simpa only [Law.map_map, he, Law.map_id] using hh

theorem entropy_pair_self (p : Law α) (f : α → β) :
    entropy (p.map (fun a => (a,f a))) = entropy p :=
  entropy_map_eq_of_leftInverse p _ Prod.fst (fun _a => rfl)

theorem entropy_cond_chain (p : Law α) (f : α → β) (g : α → γ) :
    entropy (p.map (fun a => (g a,f a))) = entropy (p.map f)+
      ∑ b, (p.map f).mass b*entropy ((p.cond f b).map g) := by
  let q := p.map (fun a => (g a,f a))
  have he : q.snd = p.map f := by rw [← Law.map_snd, Law.map_map]; rfl
  have hm (b : β) : (p.map f).mass b*entropy (q.condFst b) =
      (p.map f).mass b*entropy ((p.cond f b).map g) := by
    by_cases hb : (p.map f).mass b = 0
    · simp [hb]
    congr 1
    congr 1
    ext c
    apply (mul_left_cancel₀ hb)
    rw [← he, q.snd_mul_condFst, he, p.cond_map_weight]
  rw [entropy_chain, he]
  congr 1
  exact sum_congr rfl fun b hb => hm b

theorem entropy_cond_self (p : Law α) (f : α → β) :
    entropy p = entropy (p.map f)+∑ b, (p.map f).mass b*entropy (p.cond f b) := by
  simpa only [id_eq, Law.map_id, entropy_pair_self] using entropy_cond_chain p f id

end SharpLogRamsey.Selection

end

end OAI
end

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
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem mixing_cell_scale {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) {B z : ℝ}
    (hB : 1≤B) (hz : 0≤z) (hz1 : z≤1)
    (hcap : (S.card:ℝ)*T.card ≤ B*(Nat.card K:ℝ)^(n+3)*z^2) :
    (incidenceCount S T:ℝ) ≤ 2*B*(Nat.card K:ℝ)^(n+2)*z := by
  let q : ℝ := Nat.card K
  let p : ℝ := (∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i)
  let a : ℝ := (S.card:ℝ)*T.card
  have hq : 0<q := by
    dsimp [q]
    exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hv : 0<∑ i∈range (n+3),q^i :=
    sum_pos' (fun i _ => pow_nonneg hq.le _) ⟨0,by simp,by simp⟩
  have hp : p≤1/q := by
    apply (div_le_div_iff₀ hv hq).mpr
    have he : (∑ i∈range (n+3),q^i)=q*(∑ i∈range (n+2),q^i)+1 := geom_sum_succ
    linarith
  have ha : 0≤a := by dsimp [a]; positivity
  have hzz : z^2≤z := by nlinarith
  have hmean : p*a≤B*q^(n+2)*z := by
    have H := mul_le_mul_of_nonneg_right hp ha
    have H' : a/q≤B*q^(n+2)*z^2 := by
      apply (div_le_iff₀ hq).mpr
      change a≤B*q^(n+3)*z^2 at hcap
      calc
        a ≤ B*q^(n+3)*z^2 := hcap
        _ = _ := by rw [show n+3=(n+2)+1 by omega,pow_succ]; ring
    have H'' := mul_le_mul_of_nonneg_left hzz (show 0≤B*q^(n+2) by positivity)
    calc
      p*a ≤ a/q := by simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using H
      _ ≤ B*q^(n+2)*z^2 := H'
      _ ≤ _ := H''
  have hs := projective_mixing_sq hdim S T
  change ((incidenceCount S T:ℝ)-p*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hs
  simp only [mul_assoc] at hs
  change ((incidenceCount S T:ℝ)-p*a)^2 ≤ q^(n+1)*a at hs
  have hscale : q^(n+1)*a ≤ (B*q^(n+2)*z)^2 := by
    have H := mul_le_mul_of_nonneg_left hcap (pow_nonneg hq.le (n+1))
    have he : q^(n+1)*(B*q^(n+3)*z^2)=B*(q^(n+2)*z)^2 := by
      rw [mul_pow,←pow_mul]
      have he : q^(n+1)*q^(n+3)=q^((n+2)*2) := by rw [←pow_add]; congr 1; omega
      calc
        _ = B*(q^(n+1)*q^(n+3))*z^2 := by ring
        _ = _ := by rw [he]; ring
    change q^(n+1)*a ≤ q^(n+1)*(B*q^(n+3)*z^2) at H
    rw [he] at H
    have hBB : B≤B^2 := by nlinarith
    have H' := mul_le_mul_of_nonneg_right hBB (sq_nonneg (q^(n+2)*z))
    exact H.trans (by nlinarith [H'])
  have hpos : 0≤B*q^(n+2)*z := by positivity
  have hdev := (sq_le_sq₀ (abs_nonneg ((incidenceCount S T:ℝ)-p*a)) hpos).mp
    (by simpa using hs.trans hscale)
  have hh := le_abs_self ((incidenceCount S T:ℝ)-p*a)
  linarith

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreeDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeDecoder
open BinaryTree List
open scoped Classical
noncomputable section
variable {A B I C : Type*}

lemma retained_sublist (R : A → B → Prop) (U : Domains A B) (xs : List (A×B)) (n : ℕ) :
    retained R U xs n <+ xs :=
  (List.take_sublist n _).trans List.filter_sublist

lemma retained_mem (R : A → B → Prop) (U : Domains A B) (xs : List (A×B)) (n : ℕ)
    {x : A×B} (hx : x∈retained R U xs n) : x∈flagDomain R U := by
  exact of_decide_eq_true (List.mem_filter.mp (List.mem_of_mem_take hx)).2

lemma forall₂_replicate_membership {α : Type*} (xs : List α) (S : Finset α)
    (h : ∀ x∈xs,x∈S) : List.Forall₂ (fun x D => x∈D) xs (List.replicate xs.length S) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons,List.replicate_succ]
    exact List.Forall₂.cons (h a (by simp))
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem decoder_correct (R : A → B → Prop) (read : CapReader A B C)
    (targets : I → List (A×B)) (counts : I → ℕ) (t : BinaryTree (I×C)) (U : Domains A B) :
    List.Forall₂ (fun x D => x∈D) (output R read targets counts t U)
      (decode R read (message R read targets counts t U) U) := by
  induction t generalizing U with
  | nil => exact List.Forall₂.nil
  | node z l r hl hr =>
    rcases z with ⟨i,c⟩
    simp only [output,message,decode]
    apply List.rel_append
    · apply List.rel_append
      · exact hl _
      · apply forall₂_replicate_membership
        intro x hx
        exact retained_mem R _ _ _ hx
    · exact hr _

theorem output_sublist (R : A → B → Prop) (read : CapReader A B C)
    (choose : I → Domains A B → Option C) (targets : I → List (A×B)) (counts : I → ℕ)
    (t : BinaryTree I) (U : Domains A B) :
    output R read targets counts (execute read choose t U) U <+ population targets t := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [execute]
    split
    · exact List.nil_sublist _
    · simp only [output,population]
      exact ((hl _).append (retained_sublist R _ _ _)).append (hr _)

end
end SharpLogRamsey.TreeDecoder

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TreeCodeEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeCodeEntropy
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B C : Type*}

lemma weight_node (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (c : C) (l r : BinaryTree C) (U : Domains A B) :
    exp (-cost allowed read (.node c l r) U)=
      exp (-log (allowed U).card)*exp (-cost allowed read l ((read U c).1,U.2))*
        exp (-cost allowed read r (U.1,(read U c).2)) := by
  simp only [cost,neg_add,exp_add]

theorem kraft (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (shape : BinaryTree Unit) (U : Domains A B) :
    (∑ t∈codes allowed read shape U,exp (-cost allowed read t U))≤1 := by
  induction shape generalizing U with
  | nil => simp [codes,cost]
  | node v l r hl hr =>
    rw [codes]
    rw [sum_biUnion]
    rotate_left
    · intro c hc c' hc' hne
      apply disjoint_left.mpr
      intro t ht ht'
      obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
      obtain ⟨z',hz',he⟩ := mem_image.mp ht'
      exact hne (BinaryTree.node.inj he).1.symm
    have hone (c : C) :
        ∑ t∈(((codes allowed read l ((read U c).1,U.2)) ×ˢ
          (codes allowed read r (U.1,(read U c).2))).image
          (fun z=>BinaryTree.node c z.1 z.2)),exp (-cost allowed read t U) ≤
          exp (-log (allowed U).card) := by
      rw [sum_image]
      · simp_rw [weight_node]
        rw [sum_product]
        simp_rw [←mul_sum]
        rw [←sum_mul,←mul_sum]
        have hL := hl ((read U c).1,U.2)
        have hR := hr (U.1,(read U c).2)
        have hLn : 0≤∑ t∈codes allowed read l ((read U c).1,U.2),
            exp (-cost allowed read t ((read U c).1,U.2)) := sum_nonneg (fun _ _=>(exp_pos _).le)
        have hRn : 0≤∑ t∈codes allowed read r (U.1,(read U c).2),
            exp (-cost allowed read t (U.1,(read U c).2)) := sum_nonneg (fun _ _=>(exp_pos _).le)
        nlinarith [exp_pos (-log (allowed U).card),mul_le_mul hL hR hRn (by norm_num : (0:ℝ)≤1)]
      · intro z hz z' hz' he
        exact Prod.ext (BinaryTree.node.inj he).2.1 (BinaryTree.node.inj he).2.2
    apply (sum_le_sum (fun c _=>hone c)).trans
    by_cases he : (allowed U).card=0
    · simp [card_eq_zero.mp he]
    · have hp : (0:ℝ)<(allowed U).card := by exact_mod_cast Nat.pos_of_ne_zero he
      simp only [sum_const,nsmul_eq_mul]
      rw [exp_neg,exp_log hp]
      exact le_of_eq (mul_inv_cancel₀ hp.ne')

theorem card_subset_le_exp (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (shape : BinaryTree Unit) (U : Domains A B) (S : Finset (BinaryTree C)) (K : ℝ)
    (hS : S⊆codes allowed read shape U)
    (hK : ∀ t∈S,cost allowed read t U≤K) : (S.card:ℝ)≤exp K := by
  have hh : (S.card:ℝ)*exp (-K)≤1 := by
    calc
      _ = ∑ _t∈S,exp (-K) := by simp
      _ ≤ ∑ t∈S,exp (-cost allowed read t U) :=
        sum_le_sum (fun t ht=>exp_le_exp.mpr (neg_le_neg (hK t ht)))
      _ ≤ ∑ t∈codes allowed read shape U,exp (-cost allowed read t U) :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _=>(exp_pos _).le)
      _ ≤ 1 := kraft allowed read shape U
  have hm := mul_le_mul_of_nonneg_right hh (exp_pos K).le
  rw [mul_assoc,←exp_add,neg_add_cancel,exp_zero,mul_one,one_mul] at hm
  exact hm

end
end SharpLogRamsey.TreeCodeEntropy

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreeShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeShapes
open BinaryTree Finset
open scoped Classical

lemma prefix_free (t t' : BinaryTree Unit) (u v : List Bool)
    (h : bits t++u=bits t'++v) : t=t' ∧ u=v := by
  induction t generalizing t' u v with
  | nil =>
    cases t' with
    | nil => simpa [bits] using h
    | node _ _ _ => simp [bits] at h
  | node a l r hl hr =>
    cases t' with
    | nil => simp [bits] at h
    | node a' l' r' =>
      have he : bits l++(bits r++u)=bits l'++(bits r'++v) := by
        simpa only [bits,List.cons_append,List.cons.injEq,true_and,List.append_assoc] using h
      obtain ⟨hl',hh⟩ := hl l' (bits r++u) (bits r'++v) he
      obtain ⟨hr',hu⟩ := hr r' u v hh
      exact ⟨by cases a;cases a';simp [hl',hr'],hu⟩

lemma boundedEncode_injective (N : ℕ) (S : Finset (BinaryTree Unit))
    (hS : ∀ t∈S,t.numNodes≤N) : Function.Injective (boundedEncode N S hS) := by
  intro s t he
  have hh := congrArg Subtype.val he
  exact Subtype.ext (prefix_free s.val t.val _ _ hh).1

theorem card_le (N : ℕ) (S : Finset (BinaryTree Unit))
    (hS : ∀ t∈S,t.numNodes≤N) : S.card≤2^(2*N+1) := by
  have h := Fintype.card_le_of_injective _ (boundedEncode_injective N S hS)
  simpa only [Fintype.card_coe,card_vector,Fintype.card_bool] using h

end SharpLogRamsey.TreeShapes

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_TreeMessageEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeCodeEntropy
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B C Γ : Type*} [Fintype Γ]

omit [Fintype Γ] in
lemma shape_numNodes (t : BinaryTree C) : (shape t).numNodes=t.numNodes := by
  induction t with
  | nil => rfl
  | node _ l r hl hr => simpa only [shape,BinaryTree.map,numNodes] using congrArg₂ (fun x y=>x+y+1) hl hr

theorem tree_message_entropy (p : Selection.Law Γ)
    (allowed : Domains A B→Finset C) (read : CapReader A B C) (U : Domains A B)
    (m : Γ→BinaryTree C) (hinj : Function.Injective m) (N : ℕ) (K : ℝ)
    (hN : ∀ g,(m g).numNodes≤N)
    (hmem : ∀ g,m g∈codes allowed read (shape (m g)) U)
    (hK : ∀ g,cost allowed read (m g) U≤K) :
    Selection.entropy p≤((2*N+1:ℕ):ℝ)*log 2+K := by
  let R := univ.image (fun g=>shape (m g))
  let ctx : Γ→R := fun g=>⟨shape (m g),mem_image.mpr ⟨g,mem_univ _,rfl⟩⟩
  have hc (c : R) (hc : (p.map ctx).mass c≠0) : Selection.entropy (p.cond ctx c)≤K := by
    let S := univ.filter (fun g=>shape (m g)=c.val)
    let T := S.image m
    have hT : T⊆codes allowed read c.val U := by
      intro t ht
      obtain ⟨g,hg,rfl⟩ := mem_image.mp ht
      have he := (mem_filter.mp hg).2
      simpa only [he] using hmem g
    have hTK : ∀ t∈T,cost allowed read t U≤K := by
      intro t ht
      obtain ⟨g,hg,rfl⟩ := mem_image.mp ht
      exact hK g
    have hcard : (S.card:ℝ)≤exp K := by
      have h := card_subset_le_exp allowed read c.val U T K hT hTK
      simpa only [T,card_image_of_injective S hinj] using h
    have hp : S.Nonempty := by
      obtain ⟨g,hg,he⟩ := mem_image.mp c.property
      exact ⟨g,mem_filter.mpr ⟨mem_univ _,he⟩⟩
    have hb := Selection.entropy_le_log_card (p.cond ctx c) S (by
      intro g hg
      by_contra hn
      obtain ⟨hg',he⟩ := p.cond_support ctx c hc g hn
      have hv := congrArg Subtype.val he
      exact hg (mem_filter.mpr ⟨mem_univ _,hv⟩))
    exact hb.trans ((log_le_iff_le_exp (by exact_mod_cast card_pos.mpr hp)).mpr hcard)
  have hhead : Selection.entropy (p.map ctx)≤((2*N+1:ℕ):ℝ)*log 2 := by
    have h := Selection.entropy_le_log_card (p.map ctx) univ
      (fun c hc=>False.elim (hc (mem_univ c)))
    simp only [card_univ,Fintype.card_coe] at h
    have hR : R.Nonempty := by
      have hn : (univ:Finset Γ).Nonempty := by
        by_contra hn
        have hz : (univ:Finset Γ)=∅ := not_nonempty_iff_eq_empty.mp hn
        have ht := p.total
        rw [hz,sum_empty] at ht
        norm_num at ht
      exact hn.image _
    have hs : R.card≤2^(2*N+1) := TreeShapes.card_le N R (by
      intro t ht
      obtain ⟨g,hg,rfl⟩ := mem_image.mp ht
      simpa only [shape_numNodes] using hN g)
    apply h.trans
    have hpow : (R.card:ℝ)≤(2:ℝ)^(2*N+1) := by exact_mod_cast hs
    have hh := log_le_log (show (0:ℝ)<R.card by exact_mod_cast card_pos.mpr hR) hpow
    simpa only [log_pow] using hh
  rw [Selection.entropy_cond_self p ctx]
  apply add_le_add hhead
  calc
    _ ≤ ∑ c,(p.map ctx).mass c*K := by
      apply sum_le_sum
      intro c _
      by_cases hz : (p.map ctx).mass c=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hc c hz) ((p.map ctx).nonneg c)
    _ = K := by rw [←sum_mul,(p.map ctx).total,one_mul]

end
end SharpLogRamsey.TreeCodeEntropy

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReciprocalPotential
open Real

lemma gap_nonneg {a s : ℝ} (hs : 0 < s) (hsa : s≤a) : 0≤log (a/s) := by
  exact log_nonneg ((one_le_div hs).mpr hsa)

theorem gap_identity {a b s t Q : ℝ} (ha : 0<a) (hb : 0<b)
    (hs : 0 < s) (ht : 0<t) (hQ : 0<Q) :
    log (a/s)+log (b/t)=log (a*b/Q)+log (Q/(s*t)) := by
  simp only [log_div (mul_ne_zero ha.ne' hb.ne') hQ.ne',
    log_div ha.ne' hs.ne',log_div hb.ne' ht.ne',
    log_div hQ.ne' (mul_ne_zero hs.ne' ht.ne'),
    log_mul ha.ne' hb.ne',log_mul hs.ne' ht.ne']
  ring

theorem gap_sum {a b s t Q K : ℝ} (ha : 0<a) (hb : 0<b)
    (hs : 0 < s) (ht : 0<t) (hQ : 0<Q) (hprod : Q*exp (-K)≤ s*t) :
    log (a/s)+log (b/t)≤log (a*b/Q)+K := by
  rw [gap_identity ha hb hs ht hQ]
  apply add_le_add le_rfl
  apply (log_le_iff_le_exp (div_pos hQ (mul_pos hs ht))).mpr
  apply (div_le_iff₀ (mul_pos hs ht)).mpr
  have H := mul_le_mul_of_nonneg_right hprod (exp_nonneg K)
  have he : exp (-K)*exp K=1 := by rw [←exp_add]; simp
  nlinarith [show Q*exp (-K)*exp K=Q by rw [mul_assoc,he,mul_one]]

theorem cap_potential {b t Q C a' : ℝ} (hb : 0<b) (ht : 0<t)
    (hQ : 0<Q) (hC : 1≤C) (htb : t≤b) (ha' : 0<a')
    (hcap : a'≤C*Q/t) :
    max (log (a'*b/Q)) 0≤log (b/t)+log C := by
  have hc : 0<C := lt_of_lt_of_le zero_lt_one hC
  apply max_le
  · have hle : a'*b/Q≤C*(b/t) := by
      apply (div_le_iff₀ hQ).mpr
      have H := mul_le_mul_of_nonneg_right hcap hb.le
      have he : (C*Q/t)*b=C*(b/t)*Q := by ring
      exact H.trans_eq he
    have hp : 0<a'*b/Q := div_pos (mul_pos ha' hb) hQ
    have H := log_le_log hp hle
    rw [log_mul hc.ne' (div_pos hb ht).ne'] at H
    linarith
  · exact add_nonneg (gap_nonneg ht htb) (log_nonneg hC)

end SharpLogRamsey.ReciprocalPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreePotential
open BinaryTree
variable {α : Type*}

lemma root_nonneg (f : α → ℝ) (K : ℝ) {t : BinaryTree α} (h : Admissible f K t) :
    0 ≤ root f t := by
  cases t with
  | nil => rfl
  | node a l r => exact h.1

theorem total_le_height (f : α → ℝ) (K : ℝ) (hK : 0≤K)
    (t : BinaryTree α) (h : Admissible f K t) :
    total f t≤(t.height:ℝ)*(root f t+(t.numNodes:ℝ)*K) := by
  induction t with
  | nil => simp [total,root]
  | node a l r hl hr =>
    rcases h with ⟨ha,hbranch,hleft,hright⟩
    have hln := root_nonneg f K hleft
    have hrn := root_nonneg f K hright
    have ihl := hl hleft
    have ihr := hr hright
    have hhl : (l.height:ℝ)≤(max l.height r.height:ℝ) := by exact_mod_cast le_max_left _ _
    have hhr : (r.height:ℝ)≤(max l.height r.height:ℝ) := by exact_mod_cast le_max_right _ _
    have hL := mul_le_mul_of_nonneg_right hhl (add_nonneg hln (by positivity : 0≤(l.numNodes:ℝ)*K))
    have hR := mul_le_mul_of_nonneg_right hhr (add_nonneg hrn (by positivity : 0≤(r.numNodes:ℝ)*K))
    have hB := mul_le_mul_of_nonneg_left hbranch (show 0≤(max l.height r.height:ℝ) by positivity)
    simp only [total,root,height,numNodes,Nat.cast_add,Nat.cast_one,Nat.cast_max]
    have hN : 0≤((l.numNodes:ℝ)+(r.numNodes:ℝ)+1)*K := by positivity
    nlinarith

end SharpLogRamsey.TreePotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B I C : Type*}

lemma potential_nonneg (Q : ℝ) (U : Domains A B) : 0≤potential Q U := le_max_right _ _

lemma cap_potential_zero_allowed {b t Q C a' : ℝ} (hb : 0<b) (ht : 0<t)
    (hQ : 0<Q) (hC : 1≤C) (htb : t≤b) (ha' : 0≤a') (hcap : a'≤C*Q/t) :
    max (log (a'*b/Q)) 0≤log (b/t)+log C := by
  rcases ha'.eq_or_lt with hz | hp
  · rw [←hz]
    simp only [zero_mul,zero_div,log_zero,max_self]
    exact add_nonneg (ReciprocalPotential.gap_nonneg ht htb) (log_nonneg hC)
  · exact ReciprocalPotential.cap_potential hb ht hQ hC htb hp hcap

theorem branch (Q C b : ℝ) (hQ : 0<Q) (hC : 1≤C)
    (U V : Domains A B) (S : Finset A) (T : Finset B)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (htrimS : (9/10:ℝ)*S.card≤(S∩U.1).card)
    (htrimT : (9/10:ℝ)*T.card≤(T∩U.2).card)
    (hprod : Q*exp (-b)≤(S.card:ℝ)*T.card)
    (hcapA : (V.1.card:ℝ)≤C*Q/T.card)
    (hcapB : (V.2.card:ℝ)≤C*Q/S.card) :
    potential Q (V.1,U.2)+potential Q (U.1,V.2)≤
      potential Q U+(b+log 4+2*log C) := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have ht : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
  have hs' : (0:ℝ)<(S∩U.1).card := by linarith
  have ht' : (0:ℝ)<(T∩U.2).card := by linarith
  have hsu : ((S∩U.1).card:ℝ)≤U.1.card := by exact_mod_cast card_le_card inter_subset_right
  have htu : ((T∩U.2).card:ℝ)≤U.2.card := by exact_mod_cast card_le_card inter_subset_right
  have hsa : ((S∩U.1).card:ℝ)≤S.card := by exact_mod_cast card_le_card inter_subset_left
  have hta : ((T∩U.2).card:ℝ)≤T.card := by exact_mod_cast card_le_card inter_subset_left
  have hp' : Q*exp (-(b+log 4))≤((S∩U.1).card:ℝ)*(T∩U.2).card := by
    have he : exp (-(b+log 4))=exp (-b)/4 := by
      rw [neg_add,exp_add,exp_neg (log 4),exp_log (by norm_num : (0:ℝ)<4)]
      ring
    rw [he]
    have hh := mul_le_mul htrimS htrimT (by positivity) hs'.le
    nlinarith [mul_pos hs ht]
  have hca : (V.1.card:ℝ)≤C*Q/(T∩U.2).card :=
    hcapA.trans (div_le_div_of_nonneg_left (by positivity) ht' hta)
  have hcb : (V.2.card:ℝ)≤C*Q/(S∩U.1).card :=
    hcapB.trans (div_le_div_of_nonneg_left (by positivity) hs' hsa)
  have hl := cap_potential_zero_allowed (ht'.trans_le htu) ht' hQ hC htu
    (Nat.cast_nonneg V.1.card) hca
  have hr := cap_potential_zero_allowed (hs'.trans_le hsu) hs' hQ hC hsu
    (Nat.cast_nonneg V.2.card) hcb
  have hg := ReciprocalPotential.gap_sum (hs'.trans_le hsu) (ht'.trans_le htu) hs' ht' hQ hp'
  rw [mul_comm (V.2.card:ℝ) (U.1.card:ℝ)] at hr
  have hm : log ((U.1.card:ℝ)*U.2.card/Q)≤potential Q U := le_max_left _ _
  dsimp only [potential] at *
  linarith

lemma annotate_height (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) :
    (annotate read choose t U).height≤t.height := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [annotate]
    split
    · simp
    · simp only [height]
      exact Nat.add_le_add_right (max_le_max (hl _) (hr _)) 1

lemma annotate_numNodes (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) :
    (annotate read choose t U).numNodes≤t.numNodes := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [annotate]
    split
    · simp
    · simp only [numNodes]
      exact Nat.add_le_add_right (Nat.add_le_add (hl _) (hr _)) 1

lemma root_le (Q : ℝ) (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) :
    TreePotential.root (fun z : I×Domains A B×C => potential Q z.2.1)
      (annotate read choose t U)≤potential Q U := by
  cases t with
  | nil => exact potential_nonneg Q U
  | node i l r =>
    simp only [annotate]
    split
    · exact potential_nonneg Q U
    · exact le_rfl

theorem admissible (Q C₀ b : ℝ) (hQ : 0<Q) (hC : 1≤C₀)
    (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (hvalid : ∀ i U c, choose i U=some c →
      ∃ S : Finset A, ∃ T : Finset B, S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U c).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U c).2.card:ℝ)≤C₀*Q/S.card)
    (t : BinaryTree I) (U : Domains A B) :
    TreePotential.Admissible (fun z : I×Domains A B×C => potential Q z.2.1)
      (b+log 4+2*log C₀) (annotate read choose t U) := by
  induction t generalizing U with
  | nil => trivial
  | node i l r hl hr =>
    simp only [annotate]
    split
    · trivial
    · rename_i c hc
      obtain ⟨S,T,hS,hT,htrS,htrT,hp,hca,hcb⟩ := hvalid i U c hc
      refine ⟨potential_nonneg Q U,?_,hl _,hr _⟩
      apply (add_le_add (root_le Q read choose l _) (root_le Q read choose r _)).trans
      exact branch Q C₀ b hQ hC U (read U c) S T hS hT htrS htrT hp hca hcb

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_ChronologicalTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree

open BinaryTree

lemma balanced_height (lo n : ℕ) : (balanced lo n).height≤Nat.log 2 n+1 := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rw [balanced]
    split_ifs with h
    · simp
    · simp only [height]
      by_cases hn : n=1
      · subst n
        simp [balanced]
      have hn2 : 2≤n := by omega
      have hl : n/2<n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      have hr : n-n/2-1<n := by omega
      have hrle : n-n/2-1≤n/2 := by omega
      have h1 := ih (n/2) hl (lo:=lo)
      have h2 := ih (n-n/2-1) hr (lo:=lo+n/2+1)
      have hlog := Nat.log_monotone (b:=2) hrle
      have he := Nat.log_div_base 2 n
      have hp : 0<Nat.log 2 n := Nat.log_pos (by decide) hn2
      omega

end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B I C : Type*}

lemma total_cost_local (Q c P : ℝ) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (cost : I→Domains A B→C→ℝ)
    (hcost : ∀ i U x,choose i U=some x → cost i U x ≤ c*(potential Q U+P))
    (t : BinaryTree I) (U : Domains A B) :
    TreePotential.total (fun z : I×Domains A B×C => cost z.1 z.2.1 z.2.2)
      (annotate read choose t U)≤
      c*(TreePotential.total (fun z : I×Domains A B×C => potential Q z.2.1)
        (annotate read choose t U)+((annotate read choose t U).numNodes:ℝ)*P) := by
  induction t generalizing U with
  | nil => simp [annotate,TreePotential.total]
  | node i l r hl hr =>
    simp only [annotate]
    split
    · simp [TreePotential.total]
    · rename_i x hx
      have h := hcost i U x hx
      have hl' := hl ((read U x).1,U.2)
      have hr' := hr (U.1,(read U x).2)
      simp only [TreePotential.total,numNodes,Nat.cast_add,Nat.cast_one]
      linarith

theorem maximum_cost (Q C₀ b c P : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b)
    (hc : 0 ≤ c) (hP : 0≤P)
    (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (hvalid : ∀ i U x, choose i U=some x →
      ∃ S : Finset A, ∃ T : Finset B, S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (cost : I→Domains A B→C→ℝ)
    (hcost : ∀ i U x,choose i U=some x → cost i U x ≤ c*(potential Q U+P))
    (t : BinaryTree I) (U : Domains A B) :
    TreePotential.total (fun z : I×Domains A B×C => cost z.1 z.2.1 z.2.2)
      (annotate read choose t U)≤
      c*((t.height:ℝ)*(potential Q U+(t.numNodes:ℝ)*(b+log 4+2*log C₀))+
        (t.numNodes:ℝ)*P) := by
  let K := b+log 4+2*log C₀
  have hK : 0≤K := add_nonneg (add_nonneg hb (log_nonneg (by norm_num)))
    (mul_nonneg (by norm_num) (log_nonneg hC))
  have ha := admissible Q C₀ b hQ hC read choose hvalid t U
  have ht := TreePotential.total_le_height _ K hK _ ha
  have hr := root_le Q read choose t U
  have hh : ((annotate read choose t U).height:ℝ)≤t.height := by
    exact_mod_cast annotate_height read choose t U
  have hn : ((annotate read choose t U).numNodes:ℝ)≤t.numNodes := by
    exact_mod_cast annotate_numNodes read choose t U
  apply (total_cost_local Q c P read choose cost hcost t U).trans
  apply mul_le_mul_of_nonneg_left _ hc
  apply add_le_add _ (mul_le_mul_of_nonneg_right hn hP)
  apply ht.trans
  apply mul_le_mul hh (add_le_add hr (mul_le_mul_of_nonneg_right hn hK))
  · exact add_nonneg (TreePotential.root_nonneg _ K ha) (mul_nonneg (by positivity) hK)
  · positivity

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder TreeCodeEntropy
open scoped Classical
noncomputable section
variable {A B C I Ω : Type*}

lemma codeTree_numNodes (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) : (codeTree read choose t U).numNodes≤t.numNodes := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [codeTree,execute]
    split
    · simp only [BinaryTree.map,numNodes]; omega
    · simp only [BinaryTree.map,numNodes]
      exact Nat.add_le_add_right (Nat.add_le_add (hl _) (hr _)) 1

lemma codeTree_mem (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : I→Domains A B→Option C)
    (hallowed : ∀ i U c,choose i U=some c→c∈allowed U)
    (t : BinaryTree I) (U : Domains A B) :
    codeTree read choose t U∈codes allowed read (shape (codeTree read choose t U)) U := by
  induction t generalizing U with
  | nil => simp [codeTree,execute,shape,BinaryTree.map,codes]
  | node i l r hl hr =>
    simp only [codeTree,execute]
    split
    · simp [shape,BinaryTree.map,codes]
    · rename_i c hc
      simp only [BinaryTree.map,shape,codes]
      apply mem_biUnion.mpr
      refine ⟨c,hallowed i U c hc,mem_image.mpr ?_⟩
      exact ⟨(_, _),mem_product.mpr ⟨hl _,hr _⟩,rfl⟩

lemma codeTree_cost (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (t : BinaryTree I) (U : Domains A B) :
    TreeCodeEntropy.cost allowed read (codeTree read choose t U) U=
      TreePotential.total (fun z : I×Domains A B×C=>log (allowed z.2.1).card)
        (annotate read choose t U) := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    cases hj : choose i U with
    | none => simp only [codeTree,execute,annotate,hj,BinaryTree.map,TreeCodeEntropy.cost,
        TreePotential.total]
    | some c =>
      simp only [codeTree,execute,annotate,hj,BinaryTree.map,TreeCodeEntropy.cost,
        TreePotential.total]
      exact congrArg₂ (fun x y=>log (allowed U).card+x+y) (hl _) (hr _)

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedFullMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder TreeCodeEntropy
open scoped Classical
noncomputable section
variable {A B C I Ω : Type*}

lemma fullMessage_eq_codeTree (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ)
    (t : BinaryTree I) (U : Domains A B) :
    message R read targets counts (execute read choose t U) U=
      codeTree (countReader read) (countChoose R read choose targets counts) t U := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    cases he : choose i U with
    | none => simp only [execute,he,message,codeTree,countChoose,Option.map_none,BinaryTree.map]
    | some c =>
      simp only [execute,he,message,codeTree,countChoose,Option.map_some,countReader,BinaryTree.map]
      exact congrArg₂ (fun x y=>BinaryTree.node _ x y) (hl _) (hr _)

lemma countChoose_mem (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ)
    (allowed : Domains A B→Finset C) (n : ℕ)
    (hc : ∀ i,counts i≤n) (ha : ∀ i U c,choose i U=some c→c∈allowed U)
    (i : I) (U : Domains A B) (x : C×ℕ)
    (hx : countChoose R read choose targets counts i U=some x) : x∈countAlphabet allowed n U := by
  obtain ⟨c,he,rfl⟩:=Option.map_eq_some_iff.mp hx
  apply mem_product.mpr
  refine ⟨ha i U c he,mem_range.mpr ?_⟩
  have hh : (retained R (read U c) (targets i) (counts i)).length ≤ counts i :=
    List.length_take_le _ _
  have hn:=hc i
  omega

lemma countAlphabet_log (allowed : Domains A B→Finset C) (n : ℕ) (U : Domains A B) (h : (allowed U).Nonempty) :
    log (countAlphabet allowed n U).card=log (allowed U).card+log (n+1:ℕ) := by
  rw [countAlphabet,card_product,card_range,Nat.cast_mul]
  exact log_mul (by exact_mod_cast (card_pos.mpr h).ne') (by positivity)

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedOverhead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreePotential
open BinaryTree
lemma total_sub_const {α : Type*} (f : α→ℝ) (D : ℝ) (t : BinaryTree α) :
    total (fun a=>f a-D) t=total f t-(t.numNodes:ℝ)*D := by
  induction t with
  | nil=>simp [total]
  | node a l r hl hr=>simp only [total,numNodes,Nat.cast_add,Nat.cast_one,hl,hr]; ring
end SharpLogRamsey.TreePotential

namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder TreeCodeEntropy
open scoped Classical
noncomputable section
variable {A B C I Ω : Type*}

theorem codeTree_cost_overhead (Q C₀ b c P D : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b)
    (hc : 0 ≤ c) (hP : 0≤P) (hD : 0≤D) (N H : ℕ)
    (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : I→Domains A B→Option C)
    (hvalid : ∀ i U x,choose i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (hcost : ∀ i U x,choose i U=some x→log (allowed U).card≤D+c*(potential Q U+P))
    (t : BinaryTree I) (hN : t.numNodes≤N) (hH : t.height≤H) (U : Domains A B) :
    TreeCodeEntropy.cost allowed read (codeTree read choose t U) U≤
      (N:ℝ)*D+c*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+(N:ℝ)*P) := by
  have hx := maximum_cost Q C₀ b c P hQ hC hb hc hP read choose hvalid
    (fun _ V _=>log (allowed V).card-D) (by intro i V x hx; linarith [hcost i V x hx]) t U
  rw [TreePotential.total_sub_const] at hx
  have hn₀ : ((annotate read choose t U).numNodes:ℝ)≤N := by
    exact_mod_cast (annotate_numNodes read choose t U).trans hN
  have hn : (t.numNodes:ℝ)≤N := by exact_mod_cast hN
  have hh : (t.height:ℝ)≤H := by exact_mod_cast hH
  have hK : 0≤b+log 4+2*log C₀ := add_nonneg
    (add_nonneg hb (log_nonneg (by norm_num))) (mul_nonneg (by norm_num) (log_nonneg hC))
  have hupper : c*((t.height:ℝ)*(potential Q U+(t.numNodes:ℝ)*(b+log 4+2*log C₀))+(t.numNodes:ℝ)*P)≤
      c*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+(N:ℝ)*P) := by
    apply mul_le_mul_of_nonneg_left _ hc
    apply add_le_add _ (mul_le_mul_of_nonneg_right hn hP)
    exact mul_le_mul hh (add_le_add le_rfl (mul_le_mul_of_nonneg_right hn hK))
      (add_nonneg (potential_nonneg _ _) (mul_nonneg (by positivity) hK)) (by positivity)
  rw [codeTree_cost]
  linarith [mul_le_mul_of_nonneg_right hn₀ hD]

variable [Fintype Ω]

theorem full_execution_entropy_overhead (p : Selection.Law Ω)
    (Q C₀ b c P D : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b)
    (hc : 0 ≤ c) (hP : 0≤P) (hD : 0≤D)
    (N H n : ℕ) (R : A→B→Prop)
    (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : Ω→I→Domains A B→Option C) (t : Ω→BinaryTree I) (U : Domains A B)
    (targets : Ω→I→List (A×B)) (counts : Ω→I→ℕ)
    (hcounts : ∀ ω i,counts ω i≤n)
    (hN : ∀ ω,(t ω).numNodes≤N) (hH : ∀ ω,(t ω).height≤H)
    (hallowed : ∀ ω i U x,choose ω i U=some x→x∈allowed U)
    (hvalid : ∀ ω i U x,choose ω i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (hcost : ∀ ω i U x,choose ω i U=some x→log (allowed U).card≤D+c*(potential Q U+P)) :
    let M := fun ω=>codeTree (countReader read)
      (countChoose R read (choose ω) (targets ω) (counts ω)) (t ω) U
    let S := univ.image M
    let msg : Ω→S := fun ω=>⟨M ω,mem_image.mpr ⟨ω,mem_univ _,rfl⟩⟩
    Selection.entropy (p.map msg)≤((2*N+1:ℕ):ℝ)*log 2+(N:ℝ)*(D+log (n+1:ℕ))+
      c*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+(N:ℝ)*P) := by
  have hn : 0≤log (n+1:ℕ) := log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
  have hV (ω : Ω) : ∀ i U x,countChoose R read (choose ω) (targets ω) (counts ω) i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      (((countReader read) U x).1.card:ℝ)≤C₀*Q/T.card ∧
      (((countReader read) U x).2.card:ℝ)≤C₀*Q/S.card := by
    intro i V x hx
    obtain ⟨y,hy,rfl⟩:=Option.map_eq_some_iff.mp hx
    exact hvalid ω i V y hy
  have hC' (ω : Ω) : ∀ i U x,countChoose R read (choose ω) (targets ω) (counts ω) i U=some x→
      log (countAlphabet allowed n U).card≤D+log (n+1:ℕ)+c*(potential Q U+P) := by
    intro i V x hx
    obtain ⟨y,hy,rfl⟩:=Option.map_eq_some_iff.mp hx
    rw [countAlphabet_log allowed n V ⟨y,hallowed ω i V y hy⟩]
    linarith [hcost ω i V y hy]
  dsimp only
  rw [add_assoc]
  apply tree_message_entropy _ (countAlphabet allowed n) (countReader read) U
    Subtype.val Subtype.val_injective N
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact (codeTree_numNodes _ _ _ _).trans (hN ω)
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact codeTree_mem _ _ _
      (countChoose_mem R read (choose ω) (targets ω) (counts ω) allowed n
        (hcounts ω) (hallowed ω)) (t ω) U
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact codeTree_cost_overhead Q C₀ b c P (D+log (n+1:ℕ)) hQ hC hb hc hP
      (add_nonneg hD hn) N H _ _ _ (hV ω) (hC' ω) (t ω) (hN ω) (hH ω) U

end
end SharpLogRamsey.ExecutedPotential

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

theorem exists_fixed_family {Ω : Type*} [Fintype Ω] (μ : Law Ω)
    (p : ∀ i,Law (α i)) (success : Ω→(∀i,α i)→Prop) (c : ℝ)
    (h : c≤∑ z,(piLaw p).mass z*(∑ ω,μ.mass ω*(if success ω z then 1 else 0))) :
    ∃ z,c≤∑ ω,μ.mass ω*(if success ω z then 1 else 0) := by
  by_contra! hn
  have hlt : (∑ z,(piLaw p).mass z*(∑ ω,μ.mass ω*(if success ω z then 1 else 0))) < c := by
    have hnzero : ∃ z,(piLaw p).mass z≠0 := by
      by_contra! hz
      have ht := (piLaw p).total
      simp_rw [hz,sum_const_zero] at ht
      norm_num at ht
    obtain ⟨z,hz⟩ := hnzero
    have hh := sum_lt_sum (fun y (_hy : y∈univ)=>
      mul_le_mul_of_nonneg_left (hn y).le ((piLaw p).nonneg y))
      ⟨z,mem_univ _,mul_lt_mul_of_pos_left (hn z) (lt_of_le_of_ne ((piLaw p).nonneg z) (Ne.symm hz))⟩
    simpa only [←sum_mul,(piLaw p).total,one_mul] using hh
  linarith

end
end SharpLogRamsey.PublicTables

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

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PivotGeometry
open Finset Real Incidence Validation ProjectiveDuality PublicTables TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma primalCap_image {h : ℕ} (U : Finset (Projectivization K V))
    (u : Fin h→Projectivization K (Module.Dual K V)) :
    (primalCap U u).image (bidual (K:=K) (V:=V))=
      cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V))) u := by
  ext y
  simp only [primalCap,cap,mem_image,mem_filter]
  constructor
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,hp⟩
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩
    exact ⟨x,⟨hx,hp⟩,rfl⟩

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma primalCap_card {h : ℕ} (U : Finset (Projectivization K V))
    (u : Fin h→Projectivization K (Module.Dual K V)) :
    (primalCap U u).card=
      (cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V))) u).card := by
  rw [←primalCap_image,card_image_of_injective _ (bidual (K:=K) (V:=V)).injective]

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma primalCap_capture {h : ℕ} (U S : Finset (Projectivization K V))
    (u : Fin h→Projectivization K (Module.Dual K V)) (M : ℝ)
    (hS : S⊆U)
    (hg : GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V)))
      (S.image (bidual (K:=K) (V:=V))) M u) :
    (99:ℝ)*S.card≤100*(S∩primalCap U u).card := by
  have hh := cap_capture (image_subset_image hS) hg
  have he : (S∩primalCap U u).image (bidual (K:=K) (V:=V))=
      (S.image (bidual (K:=K) (V:=V)))∩
        cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V))) u := by
    rw [image_inter _ _ (bidual (K:=K) (V:=V)).injective,primalCap_image]
  rw [←he,card_image_of_injective _ (bidual (K:=K) (V:=V)).injective,
    card_image_of_injective _ (bidual (K:=K) (V:=V)).injective] at hh
  exact hh

omit [Finite K] [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in

theorem accepted_caps {n h h' : ℕ}
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (z : Fin h→Projectivization K V) (u : Fin h'→Projectivization K (Module.Dual K V))
    (hz : implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (B∩UT) (2000*(Nat.card K:ℝ)^(n+3)/A.card)) z)
    (hu : implementAccept ((B∩UT)∩cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V)))
        ((A∩U).image (bidual (K:=K) (V:=V))) (2000*(Nat.card K:ℝ)^(n+3)/B.card)) u) :
    primalCap U u⊆U ∧ cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z⊆UT ∧
    ((primalCap U u).card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/B.card ∧
    ((cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z).card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/A.card ∧
    (99:ℝ)*(A∩U).card≤100*((A∩U)∩primalCap U u).card ∧
    (99:ℝ)*(B∩UT).card≤100*((B∩UT)∩cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z).card := by
  refine ⟨filter_subset _ _,filter_subset _ _,?_,hz.2.1,?_,cap_capture inter_subset_right hz.2⟩
  · rw [primalCap_card]
    exact hu.2.1
  · exact primalCap_capture U (A∩U) u _ inter_subset_right hu.2

end
end SharpLogRamsey.PivotGeometry

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

theorem Input.choose_valid (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (c : Code (K:=K) (V:=V) b) (hc : d.choose hdim z w=some c) :
    let D := read b z w (d.U,d.UT) c
    D.1⊆d.U ∧ D.2⊆d.UT ∧
    (D.1.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/B.card ∧
    (D.2.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/A.card ∧
    (99:ℝ)*(A∩d.U).card≤100*((A∩d.U)∩D.1).card ∧
    (99:ℝ)*(B∩d.UT).card≤100*((B∩d.UT)∩D.2).card := by
  unfold Input.choose at hc
  split at hc
  · cases hc
  · rename_i i hi
    let r := rowAt _ (z d.firstCall.address) i
    have hv : d.firstCall.accept n r := index_valid _ _ _ i hi
    let c' := d.secondCall hdim r hv
    change (c'.bankIndex (b+log 1000000) n w).map _=some c at hc
    obtain ⟨j,hj,he⟩ := Option.map_eq_some_iff.mp hc
    subst c
    have hu := index_valid (c'.accept n) _ (w c'.address) j hj
    exact accepted_caps A d.U d.W B d.UT r (rowAt _ (w c'.address) j) hv hu

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

variable {n : ℕ} {b τ P H : ℝ}

variable (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma Book.prepare_spec (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (hr : s.Ready τ U) :
    let d := book.prepare hdim hτ hτsmall s U hr
    (d.U,d.UT)=U ∧ d.W∈book.library U (s.A∩U.1).card (s.B∩U.2).card ∧ d.W⊆U.1 := by
  exact (book.input hdim s.A s.B U s.nonemptyA s.nonemptyB hτ hr.1 hr.2.1 s.product hr.2.2
    (s.sparse U hr hτsmall)).choose_spec

theorem Book.choose_caps (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (z : Banks (K:=K) (V:=V) b) (c : Code (K:=K) (V:=V) b)
    (hc : book.choose hdim hτ hτsmall s z U=some c) :
    (9/10:ℝ)*s.A.card≤(s.A∩U.1).card ∧ (9/10:ℝ)*s.B.card≤(s.B∩U.2).card ∧
      (read b z.1 z.2 U c).1⊆U.1 ∧ (read b z.1 z.2 U c).2⊆U.2 ∧
      ((read b z.1 z.2 U c).1.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/s.B.card ∧
      ((read b z.1 z.2 U c).2.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/s.A.card := by
  unfold Book.choose at hc
  split at hc
  · rename_i hr
    let d := book.prepare hdim hτ hτsmall s U hr
    have hdom := (book.prepare_spec hdim hτ hτsmall s U hr).1
    have hcap := d.choose_valid hdim z.1 z.2 c hc
    have hu : d.U=U.1 := congrArg Prod.fst hdom
    have hv : d.UT=U.2 := congrArg Prod.snd hdom
    dsimp only at hcap
    rw [hdom,hu,hv] at hcap
    exact ⟨hr.1,hr.2.1,hcap.1,hcap.2.1,hcap.2.2.1,hcap.2.2.2.1⟩
  · cases hc

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

variable {n : ℕ} {b τ P H : ℝ}
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))

omit [Finite K] in
lemma Book.mem_allowed (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (v : book.LocalRaw U) (c : Code (K:=K) (V:=V) b) (hc : book.decodeRaw z U v=some c) :
    c∈book.allowed z U := by
  refine mem_biUnion.mpr ⟨v,mem_univ _,?_⟩
  rw [hc]
  exact mem_singleton_self c

omit [Finite K] in
lemma Book.allowed_card (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    (book.allowed z U).card≤
      ∑ s : FirstSize (K:=K) (V:=V),∑ t : SecondSize (K:=K) (V:=V),
        (book.library U s t).card*firstBound b U t*secondBound b U s := by
  have hh : (book.allowed z U).card≤Fintype.card (book.LocalRaw U) := by
    apply (card_biUnion_le).trans
    calc
      _ ≤ ∑ _v : book.LocalRaw U,1 := by
        apply sum_le_sum
        intro v _
        cases book.decodeRaw z U v <;> simp
      _ = _ := by simp
  simpa only [Book.LocalRaw,Fintype.card_sigma,Fintype.card_prod,
    Fintype.card_coe,Fintype.card_fin,←Nat.mul_assoc] using hh

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotAlphabetMembership
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {n : ℕ} {b τ P H : ℝ}

theorem Input.choose_allowed
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
    {A : Finset (Projectivization K V)} {B : Finset (Projectivization K (Module.Dual K V))}
    (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (hW : d.W∈book.library (d.U,d.UT) (A∩d.U).card (B∩d.UT).card)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (c : Code (K:=K) (V:=V) b) (hc : d.choose hdim z w=some c) :
    c∈book.allowed z (d.U,d.UT) := by
  unfold Input.choose at hc
  split at hc
  · cases hc
  · rename_i i hi
    let row := rowAt _ (z d.firstCall.address) i
    let call := d.secondCall hdim row (index_valid _ _ _ i hi)
    change (call.bankIndex (b+log 1000000) n w).map
      (fun j=>(⟨d.firstCall.address,i⟩,⟨call.address,j⟩))=some c at hc
    obtain ⟨j,hj,he⟩ := Option.map_eq_some_iff.mp hc
    cases he
    have hW' : d.W∈book.library (d.U,d.UT) call.address.2.2 d.firstCall.address.2.2 := by
      change d.W∈book.library (d.U,d.UT)
        ((A∩d.U).image (bidual (K:=K) (V:=V))).card (B∩d.UT).card
      simpa only [card_image_of_injective _ (bidual (K:=K) (V:=V)).injective] using hW
    let v : book.LocalRaw (d.U,d.UT) :=
      ⟨call.address.2.2,d.firstCall.address.2.2,⟨d.W,hW'⟩,i,j⟩
    apply book.mem_allowed z (d.U,d.UT) v
    have hWn : d.W.Nonempty := d.source_nonempty.mono inter_subset_right
    have hBn : (cap SharpLogRamsey.Incidence.Incident (Nat.card K) d.UT row).Nonempty :=
      call.source_nonempty.mono call.source_proposal
    dsimp only [Book.decodeRaw,v]
    rw [dite_eq_left hWn]
    change (if hc : (cap SharpLogRamsey.Incidence.Incident (Nat.card K) d.UT row).Nonempty then _ else _)=_
    rw [dite_eq_left hBn]
    rfl

theorem Book.choose_allowed (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
    (hτ : 0≤τ) (hτsmall : τ≤1/40000)
    (s : Original (K:=K) (V:=V) n b) (z : Banks (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (c : Code (K:=K) (V:=V) b) (hc : book.choose hdim hτ hτsmall s z U=some c) :
    c∈book.allowed z.1 U := by
  unfold Book.choose at hc
  split at hc
  · rename_i hr
    let d := book.prepare hdim hτ hτsmall s U hr
    have hs := book.prepare_spec hdim hτ hτsmall s U hr
    dsimp only at hs
    have hW : d.W∈book.library (d.U,d.UT) (s.A∩d.U).card (s.B∩d.UT).card := by
      have hu : d.U=U.1 := congrArg Prod.fst hs.1
      have hv : d.UT=U.2 := congrArg Prod.snd hs.1
      simpa only [hu,hv] using hs.2.1
    have hh := d.choose_allowed book hdim hW z.1 z.2 c hc
    rw [hs.1] at hh
    exact hh
  · cases hc

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotIndexCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Real
noncomputable section

lemma index_scheduleLength_le {q u t : ℝ} (hq : 1≤q) (ht : 0<t) (htu : t≤u) :
    (scheduleLength q u t:ℝ)≤21*q*(log (u/t)+2) := by
  have hd : 0≤log (u/t) := log_nonneg ((le_div_iff₀ ht).mpr (by simpa using htu))
  have hx : 0≤20*q*(log (u/t)+2) := by positivity
  have hc := Nat.ceil_lt_add_one hx
  change (⌈20*q*(log (u/t)+2)⌉₊:ℝ)≤_
  have hqd : 2≤q*(log (u/t)+2) := by nlinarith
  nlinarith

lemma scheduleCutoff_log {q a : ℝ} (hq : 1≤q) (ha : 0≤a) (h : ℕ) :
    log ((scheduleCutoff q a h:ℝ)+1)≤(h:ℝ)*a+log (4*q) := by
  have he : 1≤exp ((h:ℝ)*a) := one_le_exp (by positivity)
  have hx : 0≤2*q*exp ((h:ℝ)*a) := by positivity
  have hc := Nat.ceil_lt_add_one hx
  have hq0 : 0<q := by linarith
  have hb : (scheduleCutoff q a h:ℝ)+1≤4*q*exp ((h:ℝ)*a) := by
    dsimp only [scheduleCutoff]
    have hp : 1≤q*exp ((h:ℝ)*a) := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr he)]
    nlinarith
  calc
    _ ≤ log (4*q*exp ((h:ℝ)*a)) := log_le_log (by positivity) hb
    _ = _ := by rw [log_mul (by positivity) (exp_ne_zero _),log_exp]; ring

theorem reciprocal_index_cost {q a u v s t : ℝ}
    (hq : 1≤q) (ha : 0≤a) (hs : 0 < s) (ht : 0<t) (hsu : s≤u) (htv : t≤v) :
    log ((scheduleCutoff q a (scheduleLength q v t):ℝ)+1)+
      log ((scheduleCutoff q a (scheduleLength q u s):ℝ)+1)≤
      21*q*a*(log (u/s)+log (v/t)+4)+2*log (4*q) := by
  have h1 := scheduleCutoff_log hq ha (scheduleLength q v t)
  have h2 := scheduleCutoff_log hq ha (scheduleLength q u s)
  have h3 := mul_le_mul_of_nonneg_right (index_scheduleLength_le hq ht htv) ha
  have h4 := mul_le_mul_of_nonneg_right (index_scheduleLength_le hq hs hsu) ha
  linarith

theorem local_index_budget {q a u v s t Q b P J L : ℝ}
    (hq : 1 ≤ q) (ha : 0 ≤ a) (haP : a ≤ P) (hP : 4 ≤ P) (hJ : 0 ≤ J)
    (hs : 0 < s) (ht : 0<t) (hsu : s ≤ u) (htv : t ≤ v) (hQ : 0<Q)
    (_hb : 0 ≤ b) (hbP : b ≤ P) (hprod : Q*exp (-b) ≤ s*t)
    (hlib : L ≤ J*q*P*(log (u/s)+log (v/t)+P)) :
    L+log ((scheduleCutoff q a (scheduleLength q v t):ℝ)+1)+
      log ((scheduleCutoff q a (scheduleLength q u s):ℝ)+1) ≤
      (2*(J+22)*q*P)*(max (log (u*v/Q)) 0+P) := by
  let d := log (u/s)+log (v/t)
  have hd : 0 ≤ d := add_nonneg (ReciprocalPotential.gap_nonneg hs hsu)
    (ReciprocalPotential.gap_nonneg ht htv)
  have hq0 : 0<q := by linarith
  have hP0 : 0<P := by linarith
  have hv := reciprocal_index_cost hq ha hs ht hsu htv
  have hval : 21*q*a*(d+4) ≤ 21*q*P*(d+P) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left haP (by positivity))
      (by linarith) (by linarith) (by positivity)
  have hlog : log (4*q) ≤ 4*q := (log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hbase : 8*q ≤ q*P*(d+P) := by
    have hmul := mul_le_mul_of_nonneg_left (show 8 ≤ P*(d+P) by nlinarith) hq0.le
    nlinarith only [hmul]
  have hloc : L+log ((scheduleCutoff q a (scheduleLength q v t):ℝ)+1)+
      log ((scheduleCutoff q a (scheduleLength q u s):ℝ)+1) ≤
      (J+22)*q*P*(d+P) := by
    dsimp only [d] at hval hbase
    nlinarith only [hlib,hv,hval,hlog,hbase]
  have hgap := ReciprocalPotential.gap_sum (hs.trans_le hsu) (ht.trans_le htv) hs ht hQ hprod
  have hm : log (u*v/Q) ≤ max (log (u*v/Q)) 0 := le_max_left _ _
  have hm0 : 0 ≤ max (log (u*v/Q)) 0 := le_max_right _ _
  have hd' : d+P ≤ 2*(max (log (u*v/Q)) 0+P) := by
    dsimp only [d]
    linarith
  apply hloc.trans
  have hcoef : 0 ≤ (J+22)*q*P := by positivity
  convert mul_le_mul_of_nonneg_left hd' hcoef using 1 <;> first | rfl | ring

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotAlphabetCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {n : ℕ} {b τ P H : ℝ}

lemma three_card_le_exp (l m n : ℕ) (L : ℝ)
    (h : log ((l:ℝ)+1)+log ((m:ℝ)+1)+log ((n:ℝ)+1)≤L) :
    (l:ℝ)*m*n≤exp L := by
  calc
    _ ≤ ((l:ℝ)+1)*((m:ℝ)+1)*((n:ℝ)+1) := by gcongr <;> linarith
    _ = exp (log ((l:ℝ)+1)+log ((m:ℝ)+1)+log ((n:ℝ)+1)) := by
      rw [exp_add,exp_add,exp_log (by positivity),exp_log (by positivity),exp_log (by positivity)]
    _ ≤ _ := exp_le_exp.mpr h

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma headerCost_nonneg : 0≤headerCost (K:=K) (V:=V) := by
  exact add_nonneg (log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V)))); linarith))
    (log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card (Projectivization K (Module.Dual K V))); linarith))

variable (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
  (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
include hb hH hP haP

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem Book.header_index_cost
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (s t : ℕ)
    (hh : Header (Nat.card K) b (n+3) U s t) :
    log (((book.library U s t).card:ℝ)+1)+log ((firstBound b U t:ℝ)+1)+
      log ((secondBound b U s:ℝ)+1)≤
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P) := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hlib := (book.valid U s t hh).2.2
  rcases hh with ⟨hs,ht,hsu,htv,hprod,_⟩
  have hb' : 0≤b+log 4 := add_nonneg hb (log_nonneg (by norm_num))
  have hbP : b+log 4≤P := (add_le_add_right (log_le_log (by norm_num) (by norm_num : (4:ℝ)≤1000000)) b).trans haP
  have he := local_index_budget hq (add_nonneg hb (log_nonneg (by norm_num))) haP hP hH
    (by exact_mod_cast hs) (by exact_mod_cast ht) (by exact_mod_cast hsu) (by exact_mod_cast htv)
    (show 0<(Nat.card K:ℝ)^(n+3) by positivity) hb' hbP hprod hlib
  simpa only [firstBound,secondBound,card_image_of_injective _ (bidual (K:=K) (V:=V)).injective,
    potential] using he

theorem Book.allowed_card_exp (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    ((book.allowed z U).card:ℝ)≤exp (headerCost (K:=K) (V:=V)+
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P)) := by
  let L := (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P)
  have hh (s t : ℕ) : ((book.library U s t).card:ℝ)*firstBound b U t*secondBound b U s≤exp L := by
    by_cases hh : Header (Nat.card K) b (n+3) U s t
    · exact three_card_le_exp _ _ _ L (book.header_index_cost hb hH hP haP U s t hh)
    · simp only [book.invalid U s t hh,card_empty,Nat.cast_zero,zero_mul]
      exact (exp_pos L).le
  calc
    _ ≤ ∑ s : FirstSize (K:=K) (V:=V),∑ t : SecondSize (K:=K) (V:=V),
        ((book.library U s t).card:ℝ)*firstBound b U t*secondBound b U s := by
      exact_mod_cast book.allowed_card z U
    _ ≤ ∑ _s : FirstSize (K:=K) (V:=V),∑ _t : SecondSize (K:=K) (V:=V),exp L := by
      exact sum_le_sum (fun s _=>sum_le_sum (fun t _=>hh s t))
    _ = (((Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))):ℝ)+1)*
        ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1))*exp L := by
      simp only [sum_const,card_univ,nsmul_eq_mul,FirstSize,SecondSize,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
      ring
    _ = _ := by
      rw [exp_add]
      congr 1
      dsimp only [headerCost]
      rw [exp_add,exp_log (by positivity),exp_log (by positivity)]

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ReciprocalEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder FreshExecution ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [Fintype Ω]
  {n : ℕ} {b τ P H : ℝ}

variable (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))

omit [Finite K] in
lemma Book.mem_publicAlphabet (z : I→Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) (i : I) (c : Code (K:=K) (V:=V) b)
    (hc : c∈book.allowed (z i).1 U.swap) : (i,c)∈book.publicAlphabet z U := by
  exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨c,hc,rfl⟩⟩

omit [Finite K] in
lemma Book.publicAlphabet_card (z : I→Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) :
    (book.publicAlphabet z U).card≤∑ i,(book.allowed (z i).1 U.swap).card := by
  apply (card_biUnion_le).trans
  exact sum_le_sum (fun i _=>card_image_le)

variable (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
include hb hH hP haP

lemma Book.publicAlphabet_log (z : I→Banks (K:=K) (V:=V) b)
    (U : ChronoDomains (K:=K) (V:=V)) :
    log ((book.publicAlphabet z U).card:ℝ)≤
      log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V)+
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P) := by
  let L := headerCost (K:=K) (V:=V)+
      (2*(H+22)*(Nat.card K:ℝ)*P)*(potential ((Nat.card K:ℝ)^(n+3)) U+P)
  have hL : 0≤L := add_nonneg headerCost_nonneg
    (mul_nonneg (by positivity) (add_nonneg (potential_nonneg _ _) (by linarith)))
  have hs : potential ((Nat.card K:ℝ)^(n+3)) U.swap=potential ((Nat.card K:ℝ)^(n+3)) U := by
    dsimp only [potential,Prod.swap]; rw [mul_comm]
  have hc : ((book.publicAlphabet z U).card:ℝ)≤((Fintype.card I:ℝ)+1)*exp L := by
    calc
      _ ≤ ∑ i,((book.allowed (z i).1 U.swap).card:ℝ) := by exact_mod_cast book.publicAlphabet_card z U
      _ ≤ ∑ _i : I,exp L := by
        apply sum_le_sum
        intro i _
        simpa only [hs] using book.allowed_card_exp hb hH hP haP (z i).1 U.swap
      _ = (Fintype.card I:ℝ)*exp L := by simp only [sum_const,card_univ,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (exp_pos L).le
  by_cases hz : (book.publicAlphabet z U).card=0
  · rw [hz,Nat.cast_zero,log_zero,add_assoc]
    exact add_nonneg (log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card I); linarith)) hL
  · apply (log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hz)).mpr
    rw [add_assoc,exp_add,exp_log (by positivity)]
    exact hc

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.publicCodeDecidableEq
variable (hdim : Module.finrank K V=n+3) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

theorem Book.actual_full_entropy (p : Selection.Law Ω)
    (s : Ω→I→Original (K:=K) (V:=V) n b) (z : I→Banks (K:=K) (V:=V) b)
    (t : Ω→BinaryTree I) (U : ChronoDomains (K:=K) (V:=V))
    (N ht m : ℕ) (targets : Ω→I→List (Projectivization K (Module.Dual K V)×Projectivization K V))
    (counts : Ω→I→ℕ) (hcounts : ∀ ω i,counts ω i ≤ m)
    (hN : ∀ ω,(t ω).numNodes≤N) (hht : ∀ ω,(t ω).height≤ht) :
    let rd := fixedRead (fun _i : I=>chronoRead (K:=K) (V:=V) b) z
    let ch := fun ω=>fixedChoose (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i)) z
    let M := fun ω=>codeTree (countReader rd)
      (countChoose (fun y x=>SharpLogRamsey.Incidence.Incident x y) rd (ch ω) (targets ω) (counts ω)) (t ω) U
    let S := univ.image M
    let msg : Ω→S := fun ω=>⟨M ω,mem_image.mpr ⟨ω,mem_univ _,rfl⟩⟩
    Selection.entropy (p.map msg)≤((2*N+1:ℕ):ℝ)*log 2+
      (N:ℝ)*(log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V)+log (m+1:ℕ))+
      (2*(H+22)*(Nat.card K:ℝ)*P)*
      ((ht:ℝ)*(potential ((Nat.card K:ℝ)^(n+3)) U+(N:ℝ)*(b+log 4+2*log 2000))+(N:ℝ)*P) := by
  apply full_execution_entropy_overhead p ((Nat.card K:ℝ)^(n+3)) 2000 b
    (2*(H+22)*(Nat.card K:ℝ)*P) P (log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V))
    (by have : 0<Nat.card K:=Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K)); positivity)
    (by norm_num) hb (by positivity) (by linarith)
    (add_nonneg (log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card I); linarith)) headerCost_nonneg)
    N ht m _ (book.publicAlphabet z) _ _ t U targets counts hcounts hN hht
  · intro ω i U c hc
    obtain ⟨x,hx,rfl⟩:=Option.map_eq_some_iff.mp hc
    apply book.mem_publicAlphabet
    exact book.choose_allowed hdim hτ hτsmall (s ω i) (z i) U.swap x hx
  · intro ω i U c hc
    obtain ⟨x,hx,rfl⟩:=Option.map_eq_some_iff.mp hc
    have hh:=book.choose_caps hdim hτ hτsmall (s ω i) U.swap (z i) x hx
    refine ⟨(s ω i).B,(s ω i).A,(s ω i).nonemptyB,(s ω i).nonemptyA,hh.2.1,hh.1,?_,hh.2.2.2.2.2,hh.2.2.2.2.1⟩
    simpa only [mul_comm] using (s ω i).product
  · intro ω i U c hc
    exact book.publicAlphabet_log hb hH hP haP z U

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SourceCoupling
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
variable {X Ω B : Type*} [Fintype X] [Fintype Ω] [Fintype B]

lemma Law.attach_support (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (h : q.map f=μ.map g) (x : Σ _x : X,Ω)
    (hx : (q.attach μ f g).mass x≠0) :
    q.mass x.1≠0 ∧ μ.mass x.2≠0 ∧ g x.2=f x.1 := by
  have hx' : q.mass x.1≠0 ∧ (μ.cond g (f x.1)).mass x.2≠0 := mul_ne_zero_iff.mp hx
  have hf : (μ.map g).mass (f x.1)≠0 := by
    rw [←h]
    exact ne_of_gt ((lt_of_le_of_ne (q.nonneg x.1) (Ne.symm hx'.1)).trans_le (q.le_map f x.1))
  exact ⟨hx'.1,μ.cond_support g (f x.1) hf x.2 hx'.2⟩

end
end SharpLogRamsey.Selection

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

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedRetention
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

omit [DecidableEq I] in
lemma fullOutput_sublist (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) :
    List.Sublist (fullOutput R choose read targets z t U) (population targets t) :=
  output_sublist R (fixedRead read z) (fixedChoose choose z) targets _ t U

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedConditioning
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
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma conditionSuccess_support (p : Law Ω) (E : Ω→Prop) (h : 0<acceptProb p E)
    (x : Ω) (hx : (conditionSuccess p E h).mass x≠0) : p.mass x≠0 ∧ E x := by
  by_cases he : E x
  · refine ⟨?_,he⟩
    intro hp
    exact hx (by simp only [conditionSuccess,he,ite_true,hp,zero_div])
  · exact False.elim (hx (by simp only [conditionSuccess,he,ite_false]))

omit [Fintype Ξ] in

theorem conditionSuccess_fiber (p : Law Ω) (E : Ω→Prop) (h : 0<acceptProb p E)
    (stream : Ω→Ξ) (base : Ξ→ℝ) (L c : ℝ) (hc : 0 < c) (hprob : c≤acceptProb p E)
    (hb : ∀ x,0≤base x) (hL : 0≤L)
    (hdom : ∀ x,(∑ ω∈univ.filter (fun ω=>stream ω=x),p.mass ω)≤L*base x) :
    ∀ x,(∑ ω∈univ.filter (fun ω=>stream ω=x),(conditionSuccess p E h).mass ω)≤
      (L/c)*base x := by
  intro x
  calc
    _ ≤ ∑ ω∈univ.filter (fun ω=>stream ω=x),p.mass ω/acceptProb p E := by
      apply sum_le_sum
      intro ω _
      dsimp only [conditionSuccess]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (p.nonneg ω) h.le
    _ = (∑ ω∈univ.filter (fun ω=>stream ω=x),p.mass ω)/acceptProb p E := (sum_div ..).symm
    _ ≤ (L*base x)/acceptProb p E := div_le_div_of_nonneg_right (hdom x) h.le
    _ ≤ (L*base x)/c := div_le_div_of_nonneg_left (mul_nonneg hL (hb x)) hc hprob
    _ = _ := by ring

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedExtraction
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

omit [DecidableEq I] in
lemma prefix_decoder_correct (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) (m : ℕ) :
    List.Forall₂ (fun x D=>x∈D)
      ((fullOutput R choose read targets z t U).take m)
      ((decode R (fixedRead read z) (fullMessage R choose read targets z t U) U).take m) := by
  exact List.forall₂_take m (decoder_correct R (fixedRead read z) targets
    (fun i=>(targets i).length) (execute (fixedRead read z) (fixedChoose choose z) t U) U)

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_VariableRetention
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
variable [Fintype Ω] [Fintype I] [∀ i,Fintype (α i)]

theorem fixed_output_half_le (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C) (targets : Ω→I→List (A×B))
    (t : Ω→BinaryTree I) (U : Domains A B) (N : ℕ) (hN : 0<N)
    (hsize : ∀ ω,(population (targets ω) (t ω)).length≤N)
    (hmean : (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((N:ℝ)-
      (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length))≤(N:ℝ)/4) :
    ∃ z,(1/2:ℝ)≤∑ ω,μ.mass ω*(if (N:ℝ)/2≤
      (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length then 1 else 0) := by
  let out := fun ω z => (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length
  have hbound (ω : Ω) (z : ∀ i,α i) : out ω z≤N := by
    exact (fullOutput_sublist R (choose ω) (read ω) (targets ω) z (t ω) U).length_le.trans (hsize ω)
  have hp (ω : Ω) (z : ∀ i,α i) :
      (N:ℝ)/2-((N:ℝ)-out ω z)≤(N:ℝ)/2*(if (N:ℝ)/2≤out ω z then 1 else 0) := by
    split_ifs with hh
    · have hb : (out ω z:ℝ)≤N := by exact_mod_cast hbound ω z
      linarith
    · linarith
  have hz (z : ∀ i,α i) :
      (N:ℝ)/2-(∑ ω,μ.mass ω*((N:ℝ)-out ω z))≤
        (N:ℝ)/2*(∑ ω,μ.mass ω*(if (N:ℝ)/2≤out ω z then 1 else 0)) := by
    have hh:=sum_le_sum (fun ω (_ : ω∈univ)=>mul_le_mul_of_nonneg_left (hp ω z) (μ.nonneg ω))
    simpa only [mul_sub,sum_sub_distrib,←sum_mul,μ.total,one_mul,mul_left_comm,mul_sum] using hh
  have hall:=sum_le_sum (fun z (_ : z∈univ)=>mul_le_mul_of_nonneg_left (hz z) ((piLaw p).nonneg z))
  have hall' : (N:ℝ)/2-(∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((N:ℝ)-out ω z))≤
      (N:ℝ)/2*(∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*(if (N:ℝ)/2≤out ω z then 1 else 0)) := by
    simpa only [mul_sub,sum_sub_distrib,←sum_mul,(piLaw p).total,one_mul,mul_left_comm,mul_sum] using hall
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hs : (1/2:ℝ)≤∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*(if (N:ℝ)/2≤out ω z then 1 else 0) := by
    change (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((N:ℝ)-out ω z))≤(N:ℝ)/4 at hmean
    nlinarith
  exact exists_fixed_family μ p (fun ω z=>(N:ℝ)/2≤out ω z) (1/2) hs

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_VariableExtraction
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
variable [Fintype Ω] [Fintype I] [∀ i,Fintype (α i)]

theorem fixed_extraction_le (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : Ω→I→List (A×B))
    (t : Ω→BinaryTree I) (U : Domains A B) (N : ℕ) (hN : 0<N)
    (hsize : ∀ ω,(population (targets ω) (t ω)).length≤N)
    (Q : (A×B)→(A×B)→Prop)
    (hcons : ∀ ω,μ.mass ω≠0→(population (targets ω) (t ω)).Pairwise Q)
    (hmean : (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((N:ℝ)-
      (fullOutput R (choose ω) read (targets ω) z (t ω) U).length))≤(N:ℝ)/4) :
    ∃ z,let E:=fun ω=>(N:ℝ)/2≤(fullOutput R (choose ω) read (targets ω) z (t ω) U).length
      ∃ hE : 0<acceptProb μ E,
        (1/2:ℝ)≤acceptProb μ E ∧
        ∀ ω,(conditionSuccess μ E hE).mass ω≠0→
          let out:=(fullOutput R (choose ω) read (targets ω) z (t ω) U).take (N/2)
          out.length=N/2 ∧ List.Sublist out (population (targets ω) (t ω)) ∧ out.Pairwise Q ∧
          List.Forall₂ (fun x D=>x∈D) out
            ((decode R (fixedRead read z) (fullMessage R (choose ω) read (targets ω) z (t ω) U) U).take (N/2)) := by
  obtain ⟨z,hz⟩:=fixed_output_half_le μ p R choose (fun _=>read) targets t U N hN hsize hmean
  let E:=fun ω=>(N:ℝ)/2≤(fullOutput R (choose ω) read (targets ω) z (t ω) U).length
  have he : (1/2:ℝ)≤acceptProb μ E := by
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    simp only [acceptProb,accepted]
    apply sum_congr rfl
    intro ω _
    split_ifs <;> simp only [mul_zero,mul_one]
  have hp : 0<acceptProb μ E := lt_of_lt_of_le (by norm_num) he
  refine ⟨z,hp,he,?_⟩
  intro ω hω
  obtain ⟨hμ,hE⟩:=conditionSuccess_support μ E hp ω hω
  have hlen : N/2≤(fullOutput R (choose ω) read (targets ω) z (t ω) U).length := by
    have hh : (N:ℝ)≤2*(fullOutput R (choose ω) read (targets ω) z (t ω) U).length := by
      dsimp only [E] at hE
      simpa only [mul_comm] using (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mp hE
    have hh' : N≤2*(fullOutput R (choose ω) read (targets ω) z (t ω) U).length := by exact_mod_cast hh
    omega
  have hsub:= (List.take_sublist (N/2) (fullOutput R (choose ω) read (targets ω) z (t ω) U)).trans
    (fullOutput_sublist R (choose ω) read (targets ω) z (t ω) U)
  exact ⟨List.length_take_of_le hlen,hsub,List.Pairwise.sublist hsub (hcons ω hμ),
    prefix_decoder_correct R (choose ω) read (targets ω) z (t ω) U (N/2)⟩

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedDecodedSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset BinaryTree TreeDecoder Real
open scoped Classical
noncomputable section
variable {A B C I : Type*}

lemma flagDomain_size (R : A→B→Prop) (V : Domains A B)
    (S : Finset A) (T : Finset B) (hS : S.Nonempty) (hT : T.Nonempty)
    (Q C₀ b : ℝ) (hQ : 0<Q) (hC : 0≤C₀)
    (hprod : Q*exp (-b)≤(S.card:ℝ)*T.card)
    (hA : (V.1.card:ℝ)≤C₀*Q/T.card) (hB : (V.2.card:ℝ)≤C₀*Q/S.card) :
    ((flagDomain R V).card:ℝ)≤C₀^2*Q*exp b := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have ht : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
  have he : exp (-b)*exp b=1 := by rw [←exp_add]; simp only [neg_add_cancel,exp_zero]
  have hq : Q≤((S.card:ℝ)*T.card)*exp b := by
    have hh:=mul_le_mul_of_nonneg_right hprod (exp_nonneg b)
    simpa only [mul_assoc,he,mul_one] using hh
  have hd : Q/((S.card:ℝ)*T.card)≤exp b := (div_le_iff₀ (mul_pos hs ht)).mpr (by
    simpa only [mul_comm] using hq)
  have hm : (V.1.card:ℝ)*V.2.card≤(C₀*Q/T.card)*(C₀*Q/S.card) :=
    mul_le_mul hA hB (by positivity) (div_nonneg (mul_nonneg hC hQ.le) ht.le)
  have hid : (C₀*Q/T.card)*(C₀*Q/S.card)=C₀^2*Q*(Q/((S.card:ℝ)*T.card)) := by
    field_simp
  have hcard : (flagDomain R V).card≤V.1.card*V.2.card := by
    dsimp only [flagDomain]
    exact (card_filter_le _ _).trans_eq (card_product _ _)
  calc
    _ ≤ (V.1.card:ℝ)*V.2.card := by exact_mod_cast hcard
    _ ≤ C₀^2*Q*exp b := (hm.trans_eq hid).trans
      (mul_le_mul_of_nonneg_left hd (mul_nonneg (sq_nonneg C₀) hQ.le))

theorem decoded_domains_size (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ)
    (K : ℝ)
    (hcap : ∀ i U c,choose i U=some c→((flagDomain R (read U c)).card:ℝ)≤K)
    (t : BinaryTree I) (U : Domains A B) :
    ∀ D∈decode R read (message R read targets counts (execute read choose t U) U) U,
      (D.card:ℝ)≤K := by
  induction t generalizing U with
  | nil => simp only [execute,message,decode,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | node i l r hl hr =>
    cases he : choose i U with
    | none => simp only [execute,he,message,decode,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    | some c =>
      simp only [execute,he,message,decode,List.mem_append]
      intro D hD
      rcases hD with (hD | hD) | hD
      · exact hl _ D hD
      · obtain ⟨_,rfl⟩:=List.mem_replicate.mp hD
        exact hcap i U c he
      · exact hr _ D hD

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder FreshExecution ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I : Type*} {n : ℕ} {b τ P H : ℝ}

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma chronoFlagDomain_card (U : ChronoDomains (K:=K) (V:=V)) :
    (flagDomain (fun y x=>SharpLogRamsey.Incidence.Incident x y) U).card=
      incidenceCount U.2 U.1 := by
  simp only [flagDomain,incidenceCount,card_eq_sum_ones,sum_filter,sum_product]

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem reciprocal_flagDomain_size (hdim : Module.finrank K V=n+3) (hb : 0≤b)
    (U : ChronoDomains (K:=K) (V:=V))
    (S : Finset (Projectivization K (Module.Dual K V))) (T : Finset (Projectivization K V))
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(S.card:ℝ)*T.card)
    (hA : (U.1.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/T.card)
    (hB : (U.2.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/S.card) :
    ((flagDomain (fun y x=>SharpLogRamsey.Incidence.Incident x y) U).card:ℝ)≤
      8000000*(Nat.card K:ℝ)^(n+2)*exp b := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hp := flagDomain_size (fun _ _=>True) U S T hS hT
    ((Nat.card K:ℝ)^(n+3)) 2000 b (by positivity) (by norm_num) hprod hA hB
  have hcap : (U.2.card:ℝ)*U.1.card≤(2000^2*exp b)*(Nat.card K:ℝ)^(n+3)*(1:ℝ)^2 := by
    have hp' : (U.1.card:ℝ)*U.2.card≤2000^2*(Nat.card K:ℝ)^(n+3)*exp b := by
      simpa only [flagDomain,filter_true,card_product,Nat.cast_mul] using hp
    calc
      _ = (U.1.card:ℝ)*U.2.card := by ring
      _ ≤ _ := hp'
      _ = _ := by ring
  have hB' : 1≤(2000:ℝ)^2*exp b := by nlinarith [one_le_exp hb]
  have hm := mixing_cell_scale hdim U.2 U.1 hB' (by norm_num : (0:ℝ)≤1) le_rfl hcap
  rw [chronoFlagDomain_card]
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

variable (hdim : Module.finrank K V=n+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
  (hb : 0≤b) (hτ : 0≤τ) (hτsmall : τ≤1/40000)
include hb

theorem Book.actual_decoded_size (s : I→Original (K:=K) (V:=V) n b)
    (z : I→Banks (K:=K) (V:=V) b)
    (targets : I→List (Projectivization K (Module.Dual K V)×Projectivization K V))
    (counts : I→ℕ) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V)) :
    let rd := fixedRead (fun _i : I=>chronoRead (K:=K) (V:=V) b) z
    let ch := fixedChoose (fun i=>book.chronoChoose hdim hτ hτsmall (s i)) z
    ∀ D∈decode (fun y x=>SharpLogRamsey.Incidence.Incident x y) rd
      (message (fun y x=>SharpLogRamsey.Incidence.Incident x y) rd targets counts (execute rd ch t U) U) U,
      (D.card:ℝ)≤8000000*(Nat.card K:ℝ)^(n+2)*exp b := by
  apply decoded_domains_size
  intro i U c hc
  obtain ⟨x,hx,rfl⟩:=Option.map_eq_some_iff.mp hc
  have hh:=book.choose_caps hdim hτ hτsmall (s i) U.swap (z i) x hx
  apply reciprocal_flagDomain_size hdim hb _ (s i).B (s i).A (s i).nonemptyB (s i).nonemptyA
  · simpa only [mul_comm] using (s i).product
  · exact hh.2.2.2.2.2
  · exact hh.2.2.2.2.1

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.ActualPivot
open Finset Real TreeDecoder FreshExecution BinaryTree ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω Ξ : Type*} [Fintype I] [Fintype Ω]
  {n : ℕ} {b τ P H : ℝ}

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.flat_ActualExecutedReplacement_1
variable (hdim : Module.finrank K V=n+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
  (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
  (hτ : 0≤τ) (hτsmall : τ≤1/40000)

include hb hH hP haP

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.replacementBanksFintype
theorem Book.actual_replacement (μ : Selection.Law Ω)
    (s : Ω→I→Original (K:=K) (V:=V) n b)
    (targets : Ω→I→List (Flag (K:=K) (V:=V))) (t : Ω→BinaryTree I)
    (U : ChronoDomains (K:=K) (V:=V)) (N W ht m : ℕ) (hN : 0<N)
    (hsize : ∀ ω,(population (targets ω) (t ω)).length≤N)
    (hnodes : ∀ ω,(t ω).numNodes≤W) (hheight : ∀ ω,(t ω).height≤ht)
    (hcounts : ∀ ω i,(targets ω i).length≤ m)
    (Q : Flag (K:=K) (V:=V)→Flag (K:=K) (V:=V)→Prop)
    (hcons : ∀ ω,μ.mass ω≠0→(population (targets ω) (t ω)).Pairwise Q)
    (stream : Ω→Ξ) (base : Ξ→ℝ) (L : ℝ) (hb0 : ∀ x,0≤base x) (hL : 0≤L)
    (hdom : ∀ x,(∑ ω∈univ.filter (fun ω=>stream ω=x),μ.mass ω)≤L*base x)
    (hmean : (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      ∑ ω,μ.mass ω*((N:ℝ)-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) (targets ω) z (t ω) U).length))≤(N:ℝ)/4) :
    ∃ z : I→Banks (K:=K) (V:=V) b,
      let R:=fun (y : Projectivization K (Module.Dual K V)) (x : Projectivization K V)=>SharpLogRamsey.Incidence.Incident x y
      let choose:=fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)
      let read:=fun _ : I=>chronoRead (K:=K) (V:=V) b
      let E:=fun ω=>(N:ℝ)/2≤(fullOutput R (choose ω) read (targets ω) z (t ω) U).length
      ∃ hE : 0<PublicTables.acceptProb μ.asPublic E,
        let ν:=Selection.Law.ofPublic (PublicTables.conditionSuccess μ.asPublic E hE)
        let M:=fun ω=>fullMessage R (choose ω) read (targets ω) z (t ω) U
        let S:=univ.image M
        let msg : Ω→S:=fun ω=>⟨M ω,mem_image.mpr ⟨ω,mem_univ _,rfl⟩⟩
        let domains:=fun c : S=>(decode R (fixedRead read z) c.val U).take (N/2)
        (1/2:ℝ)≤PublicTables.acceptProb μ.asPublic E ∧
        (∀ x,(∑ ω∈univ.filter (fun ω=>stream ω=x),ν.mass ω)≤(2*L)*base x) ∧
        (∀ ω,ν.mass ω≠0→
          let out:=(fullOutput R (choose ω) read (targets ω) z (t ω) U).take (N/2)
          out.length=N/2 ∧ out.Sublist (population (targets ω) (t ω)) ∧
          out.Pairwise Q ∧ List.Forall₂ (fun x D=>x∈D) out (domains (msg ω))) ∧
        (∀ c D,D∈domains c→(D.card:ℝ)≤8000000*(Nat.card K:ℝ)^(n+2)*exp b) ∧
        Selection.entropy (ν.map msg)≤((2*W+1:ℕ):ℝ)*log 2+
          (W:ℝ)*(log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V)+log (m+1:ℕ))+
          (2*(H+22)*(Nat.card K:ℝ)*P)*
          ((ht:ℝ)*(potential ((Nat.card K:ℝ)^(n+3)) U+(W:ℝ)*(b+log 4+2*log 2000))+(W:ℝ)*P) := by
  let R:=fun (y : Projectivization K (Module.Dual K V)) (x : Projectivization K V)=>SharpLogRamsey.Incidence.Incident x y
  let choose:=fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)
  let read:=fun _ : I=>chronoRead (K:=K) (V:=V) b
  obtain ⟨z,hE,hprob,hextract⟩:=fixed_extraction_le μ.asPublic
    (fun _ : I=>banksLaw (K:=K) (V:=V) b) R choose read targets t U N hN hsize Q hcons hmean
  refine ⟨z,hE,hprob,?_,hextract,?_,?_⟩
  · have hh:=PublicTables.conditionSuccess_fiber μ.asPublic _ hE stream base L (1/2)
      (by norm_num) hprob hb0 hL hdom
    simpa only [Selection.Law.ofPublic, R, choose, read, div_div,div_one,one_div,div_inv_eq_mul,mul_comm] using hh
  · intro c D hD
    obtain ⟨ω,_,he⟩:=mem_image.mp c.property
    have hm : D∈decode R (fixedRead read z) (fullMessage R (choose ω) read (targets ω) z (t ω) U) U := by
      change D∈(decode R (fixedRead read z) c.val U).take (N/2) at hD
      rw [←he] at hD
      exact List.mem_of_mem_take hD
    exact book.actual_decoded_size hdim hb hτ hτsmall (s ω) z (targets ω)
      (fun i=>(targets ω i).length) (t ω) U D hm
  · have hh:=book.actual_full_entropy hb hH hP haP hdim hτ hτsmall
      (Selection.Law.ofPublic (PublicTables.conditionSuccess μ.asPublic _ hE)) s z t U
      W ht m targets (fun ω i=>(targets ω i).length) hcounts hnodes hheight
    simp only [Selection.entropy_map] at hh ⊢
    simpa only [R, choose, read, Selection.Law.map,
      Subtype.mk.injEq, fullMessage, fullMessage_eq_codeTree] using hh

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

lemma liveTree_nodes (S : Finset I) (fallback : I) : (liveTree S fallback).numNodes=S.card := by
  rw [←inorder_length,liveTree_inorder,length_sort]

lemma map_height {A B : Type*} (f : A→B) (t : BinaryTree A) : (t.map f).height=t.height := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [BinaryTree.map,height,hl,hr]

lemma liveTree_height (S : Finset I) (fallback : I) :
    (liveTree S fallback).height≤Nat.log 2 S.card+1 := by
  rw [liveTree,map_height]
  exact balanced_height _ _

lemma liveTree_nodup (S : Finset I) (fallback : I) :
    (inorder (liveTree S fallback)).Nodup := by
  rw [liveTree_inorder]
  exact sort_nodup _ _

lemma liveTree_separated (S : Finset I) (fallback : I) : Separated (liveTree S fallback) :=
  separated_of_nodup _ (liveTree_nodup S fallback)

lemma liveTree_ordered (S : Finset I) (fallback : I) :
    (inorder (liveTree S fallback)).Pairwise (·<·) := by
  rw [liveTree_inorder]
  exact S.sortedLT_sort.pairwise

end
end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_ExposureWindows
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
variable {ι β C X : Type} [Fintype β]
namespace ExposureModel

lemma lift_origin (M : ExposureModel ι β C) (z : M.History) (e : X↪ι)
    (h : ∀ x,∃ i,M.origin z i=e x) (x : X) : M.origin z (M.lift z e h x)=e x :=
  (h x).choose_spec

end ExposureModel

namespace Windows
variable [Fintype C]

lemma owner_before_next {w n : ℕ} (i j : Fin w) (hij : i<j)
    (a b : Slot w n) (ha : a.1=i) (hb : b.1=j) : position a<position b := by
  change a.1.val*(4*n)+a.2.val< b.1.val*(4*n)+b.2.val
  rw [ha,hb]
  have hi : i.val+1≤ j.val := hij
  have hA:=a.2.isLt
  nlinarith

end Windows
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_PreparedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]

variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualPreparedWindows_1
lemma target_origin (z : (model w n k p θ G t).History) (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).origin z (target w n k p θ G t z (i,x))=middle w (n+k) (i,x) :=
  lift_origin _ _ _ _ _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_GoodPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open TreeDecoder BinaryTree ChronologicalTree
lemma population_flatMap {I A B : Type*} (f : I→List (A×B)) (t : BinaryTree I) :
    population f t=(inorder t).flatMap f := by
  induction t with
  | nil => rfl
  | node i l r hl hr => simp [population,inorder,hl,hr]
end SharpLogRamsey.FreshExecution

namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.finDecC
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.indexDecC
lemma goodTarget_eq (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w)
    (j : Fin (goodMiddle w n k p θ G t z bad i).card) :
    goodTarget w n k p θ G t z bad i j=target w n k p θ G t z.1
      (i,(goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl j) := rfl

lemma goodTarget_before (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w)
    (a b : Fin (goodMiddle w n k p θ G t z bad i).card) (hab : a<b) :
    position ((model w n k p θ G t).origin z.1 (goodTarget w n k p θ G t z bad i a)) <
      position ((model w n k p θ G t).origin z.1 (goodTarget w n k p θ G t z bad i b)) := by
  simp only [goodTarget_eq,target_origin]
  have h:=((goodMiddle w n k p θ G t z bad i).orderEmbOfFin rfl).strictMono hab
  change i.val*(4*(n+k))+((n+k)+_) < i.val*(4*(n+k))+((n+k)+_)
  exact Nat.add_lt_add_left (Nat.add_lt_add_left h (n+k)) _

lemma goodTarget_before_next (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i j : Fin w) (hij : i<j)
    (a : Fin (goodMiddle w n k p θ G t z bad i).card)
    (b : Fin (goodMiddle w n k p θ G t z bad j).card) :
    position ((model w n k p θ G t).origin z.1 (goodTarget w n k p θ G t z bad i a)) <
      position ((model w n k p θ G t).origin z.1 (goodTarget w n k p θ G t z bad j b)) := by
  simp only [goodTarget_eq,target_origin]
  exact owner_before_next i j hij _ _ rfl rfl

theorem goodPopulation_pairwise {A B : Type*} (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (live : Finset (Fin w)) (fallback : Fin w)
    (F : (model w n k p θ G t).Index z.1→A×B) (Q : A×B→A×B→Prop)
    (hQ : ∀ i j,position ((model w n k p θ G t).origin z.1 i) <
      position ((model w n k p θ G t).origin z.1 j)→Q (F i) (F j)) :
    (population (fun i=>List.ofFn (fun j=>F (goodTarget w n k p θ G t z bad i j)))
      (liveTree live fallback)).Pairwise Q := by
  rw [population_flatMap,List.pairwise_flatMap]
  constructor
  · intro i hi
    rw [List.pairwise_ofFn]
    exact fun a b hab=>hQ _ _ (goodTarget_before w n k p θ G t z bad i a b hab)
  · apply (liveTree_ordered live fallback).imp
    intro i j hij x hx y hy
    obtain ⟨a,rfl⟩:=List.mem_ofFn.mp hx
    obtain ⟨b,rfl⟩:=List.mem_ofFn.mp hy
    exact hQ _ _ (goodTarget_before_next w n k p θ G t z bad i j hij a b)

lemma goodPopulation_length {A B : Type*} (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (live : Finset (Fin w)) (fallback : Fin w)
    (F : (model w n k p θ G t).Index z.1→A×B) :
    (population (fun i=>List.ofFn (fun j=>F (goodTarget w n k p θ G t z bad i j)))
      (liveTree live fallback)).length=∑ i∈live,(goodMiddle w n k p θ G t z bad i).card := by
  have hh:=population_length_sum (fun i=>List.ofFn (fun j=>F (goodTarget w n k p θ G t z bad i j)))
    _ (liveTree_separated live fallback)
  rw [liveTree_labels] at hh
  simp only [List.length_ofFn] at hh
  exact_mod_cast hh

lemma goodPopulation_size (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (live : Finset (Fin w)) :
    (∑ i∈live,(goodMiddle w n k p θ G t z bad i).card)≤w*(2*(n+k)) := by
  calc
    _ ≤ ∑ _i∈live,2*(n+k) := by
      apply sum_le_sum
      intro i hi
      simpa using card_le_univ (goodMiddle w n k p θ G t z bad i)
    _ = live.card*(2*(n+k)) := by simp
    _ ≤ w*(2*(n+k)) := Nat.mul_le_mul_right _ (by simpa using card_le_univ live)

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_MixtureRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.ActualPivot
open Finset Selection
open scoped Classical BigOperators
noncomputable section
variable {K V I Y₀ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  {d : ℕ} {b : ℝ} [Fintype Y₀]

variable {Θ : Type} [Fintype Θ] {Y : Θ→Type} [∀ θ,Fintype (Y θ)]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma Realization.attach_agrees {Ω B : Type} [Fintype Ω] [Fintype B]
    {q : Law Y₀} (e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q)
    (p : Law Ω) (tag : Y₀→B) (g : Ω→B) (h : q.map tag=p.map g)
    (ω : (e.attach p tag g h).Ω) (hω : (e.attach p tag g h).μ.mass ω≠0) :
    e.μ.mass ω.1≠0 ∧ p.mass ω.2≠0 ∧ g ω.2=tag (e.source ω.1) := by
  apply Law.attach_support e.μ p (tag∘e.source) g _ ω hω
  rw [←Law.map_map,e.marginal,h]
end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ContextOutput
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

attribute [instance] ContextOutput.finiteX ContextOutput.finiteΓ

variable {Ω F X Γ : Type} [Fintype Ω] [Fintype F] [Fintype X] [Fintype Γ]
  {ℓ m : ℕ} {B C L : ℝ}

theorem contextOutput_of_lists (p : Law Ω) (G : Ω→Fin ℓ→F) (μ : Law X)
    (source : X→Ω) (msg : X→Γ) (out : X→List F) (domains : Γ→List (Finset F))
    (hB : 0≤B)
    (hlen : ∀ x,μ.mass x≠0→(out x).length=m)
    (hsub : ∀ x,μ.mass x≠0→(out x).Sublist (List.ofFn (G (source x))))
    (hhit : ∀ x,μ.mass x≠0→List.Forall₂ (fun f D=>f∈D) (out x) (domains (msg x)))
    (hsize : ∀ c D,D∈domains c→(D.card:ℝ)≤B)
    (hdom : ∀ a,(μ.map source).mass a≤L*p.mass a)
    (hcost : entropy (μ.map msg)≤C) : Nonempty (ContextOutput p G m B C L) := by
  let Y:={x // μ.mass x≠0}
  have he : ∀ x : Y,∃ e : Fin m↪o Fin ℓ,∀ i,
      G (source x.val) (e i)=(out x.val).get ⟨i.val,by rw [hlen x.val x.property];exact i.isLt⟩ := by
    intro x
    obtain ⟨e,he⟩:=List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (hsub x.val x.property)
    let f : Fin m↪o Fin ℓ:=
      (Fin.castOrderIso (hlen x.val x.property).symm).toOrderEmbedding.trans
        (e.trans (Fin.castOrderIso (List.length_ofFn (f:=G (source x.val)))).toOrderEmbedding)
    refine ⟨f,?_⟩
    intro i
    have hh:=he ((Fin.castOrderIso (hlen x.val x.property).symm) i)
    rw [List.get_ofFn] at hh
    exact hh.symm
  choose e he using he
  refine ⟨⟨Y,Γ,inferInstance,inferInstance,μ.nullFree,(fun x=>source x.val),
    (fun x=>msg x.val),e,(fun c i=>(domains c).getD i.val ∅),?_,?_,?_,?_,?_⟩⟩
  · intro x hz
    have ha:=hdom (source x.val)
    rw [hz,mul_zero] at ha
    have hh:=(μ.le_map source x.val).trans ha
    exact x.property (le_antisymm hh (μ.nonneg x.val))
  · intro x i
    rw [he]
    have hdlen : (domains (msg x.val)).length=m := by
      rw [←(hhit x.val x.property).length_eq,hlen x.val x.property]
    rw [List.getD_eq_getElem _ _ (by rw [hdlen];exact i.isLt)]
    exact (hhit x.val x.property).get (by rw [hlen x.val x.property];exact i.isLt)
      (by rw [hdlen];exact i.isLt)
  · intro c i
    by_cases hi : i.val<(domains c).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hsize c _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      simpa using hB
  · intro a
    rw [Law.nullFree_map]
    exact hdom a
  · rw [Law.nullFree_map]
    exact hcost
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_PreparedMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b : ℝ}
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.mixBlockDec
variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
local notation "M" => model w n k p θ G t

variable (e : ∀ z : PositiveHistory w n k p θ G t hp,
  Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))

omit [Finite K] [FiniteDimensional K V] in
lemma attachedPrepared_tuple (ω : (attachedPrepared w n k p θ G t hp e).Ω)
    (hω : (attachedPrepared w n k p θ G t hp e).μ.mass ω≠0) :
    p.mass ω.2≠0 ∧ θ ω.2=ω.1.1.val.1.1 ∧
      ∀ i,G ω.2 ((M).origin ω.1.1.val.1 i)=(e ω.1.1).source ω.1.2 i := by
  have hh:=(mixedPrepared w n k p θ G t hp e).attach_agrees p
    (fun x=>(x.1.1.1,(M).restore x.1.1 x.2)) (fun ω=>(θ ω,G ω))
    (afterDraw_tagged_map n k p θ G (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp) ω hω
  refine ⟨hh.2.1,congrArg Prod.fst hh.2.2,?_⟩
  intro i
  have he:=congrFun (congrArg Prod.snd hh.2.2) ((M).origin ω.1.1.val.1 i)
  exact he.trans ((M).restore_origin ω.1.1.val.1 ((e ω.1.1).source ω.1.2) i)

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Selection TreeDecoder FreshExecution BinaryTree ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) ]
  {I X Ω : Type} [Fintype I] [Fintype X] [Fintype Ω]
  {d ℓ : ℕ} {b τ P H : ℝ}

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.outEqI
attribute [local instance] OAI.SharpLogRamsey.ActualPivot.outBanks
theorem Book.context_output (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
    (hτ : 0≤τ) (hτsmall : τ≤1/40000)
    (p : Law Ω) (G : Ω→Fin ℓ→Flag (K:=K) (V:=V)) (μ : Law X) (source : X→Ω)
    (hmarginal : μ.map source=p)
    (s : X→I→Original (K:=K) (V:=V) d b)
    (targets : X→I→List (Flag (K:=K) (V:=V))) (t : X→BinaryTree I)
    (N W ht m : ℕ) (hN : 0<N)
    (hsize : ∀ x,(population (targets x) (t x)).length≤N)
    (hnodes : ∀ x,(t x).numNodes≤W) (hheight : ∀ x,(t x).height≤ht)
    (hcounts : ∀ x i,(targets x i).length≤ m)
    (hsub : ∀ x,μ.mass x≠0→(population (targets x) (t x)).Sublist (List.ofFn (G (source x))))
    (hmean : (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      ∑ x,μ.mass x*((N:ℝ)-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ hτsmall (s x i))
        (fun _=>chronoRead b) (targets x) z (t x) (univ,univ)).length))≤(N:ℝ)/4) :
    Nonempty (ContextOutput p G (N/2) (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
      (reciprocalOutputCost (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) (P:=P) (H:=H) W ht m) 2) := by
  obtain ⟨z,hE,hprob,hdom,hextract,hdomains,hcost⟩:=book.actual_replacement hdim hb hH hP haP hτ hτsmall
    μ s targets t (univ,univ) N W ht m hN hsize hnodes hheight hcounts
    (fun _ _=>True) (by intro x hx;exact List.pairwise_of_forall (fun _ _=>trivial))
    source p.mass 1 p.nonneg (by norm_num)
    (by intro a;change (μ.map source).mass a≤1*p.mass a;rw [hmarginal,one_mul]) hmean
  let R:=fun (y : Projectivization K (Module.Dual K V)) (x : Projectivization K V)=>SharpLogRamsey.Incidence.Incident x y
  let choose:=fun x i=>book.chronoChoose hdim hτ hτsmall (s x i)
  let read:=fun _ : I=>chronoRead (K:=K) (V:=V) b
  let E:=fun x=>(N:ℝ)/2≤(fullOutput R (choose x) read (targets x) z (t x) (univ,univ)).length
  let ν:=Selection.Law.ofPublic (PublicTables.conditionSuccess μ.asPublic E hE)
  let M:=fun x=>fullMessage R (choose x) read (targets x) z (t x) (univ,univ)
  let S:=univ.image M
  let msg : X→S:=fun x=>⟨M x,mem_image.mpr ⟨x,mem_univ _,rfl⟩⟩
  let DD:=fun c : S=>(decode R (fixedRead read z) c.val (univ,univ)).take (N/2)
  let out:=fun x=>(fullOutput R (choose x) read (targets x) z (t x) (univ,univ)).take (N/2)
  apply contextOutput_of_lists p G ν source msg out DD (by positivity)
  · intro x hx
    exact (hextract x hx).1
  · intro x hx
    have hμ : μ.mass x≠0:=(PublicTables.conditionSuccess_support μ.asPublic E hE x hx).1
    exact (hextract x hx).2.1.trans (hsub x hμ)
  · intro x hx
    exact (hextract x hx).2.2.2
  · exact hdomains
  · intro a
    have hh:=hdom a
    simpa only [mul_one,Law.map] using hh
  · exact hcost
end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_PopulationSublist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section

lemma finProd_position {w n : ℕ} (i : Slot w n) :
    (finProdFinEquiv i).val=position i := by
  simp [finProdFinEquiv,position,Nat.mul_comm,Nat.add_comm]

variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

local instance sublistFinDec_r429528_1 (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance sublistIndexDec_r429528_1 (z : (model w n k p θ G t).FreshHistory) :
    DecidableEq ((model w n k p θ G t).Index z.1) := Classical.decEq _
theorem goodPopulation_sublist {A B : Type*} (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1))
    (live : Finset (Fin w)) (fallback : Fin w)
    (F : (model w n k p θ G t).Index z.1→A×B) (F0 : Slot w (n+k)→A×B)
    (hF : ∀ i,F i=F0 ((model w n k p θ G t).origin z.1 i)) :
    (population (fun i=>List.ofFn (fun j=>F (goodTarget w n k p θ G t z bad i j)))
      (liveTree live fallback)).Sublist (List.ofFn (flattenTuple F0)) := by
  let l:=population (fun i=>List.ofFn (fun j=>(model w n k p θ G t).origin z.1
    (goodTarget w n k p θ G t z bad i j))) (liveTree live fallback)
  have hl : l.Pairwise (fun i j=>position i<position j) :=
    goodPopulation_pairwise w n k p θ G t z bad live fallback
      ((model w n k p θ G t).origin z.1) (fun i j=>position i<position j) (fun _ _ h=>h)
  have hl' : (l.map finProdFinEquiv).Pairwise (·<·) := by
    rw [List.pairwise_map]
    apply hl.imp
    intro i j hij
    change (finProdFinEquiv i).val<(finProdFinEquiv j).val
    simpa only [finProd_position] using hij
  have hs : (l.map finProdFinEquiv).Sublist (List.finRange (w*(4*(n+k)))) :=
    List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset hl'.nodup (by intro i hi;exact List.mem_finRange i))
      hl' (List.sortedLT_finRange _).pairwise
  have hm:=hs.map (flattenTuple F0)
  rw [←List.ofFn_eq_map] at hm
  simpa [l,population_flatMap,List.map_flatMap,List.map_ofFn,Function.comp_def,
    flattenTuple,←hF] using hm
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_PreparedOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.prepOutFinDec
local instance prepOutBlockDec_r429528_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→ActualPivot.Flag (K:=K) (V:=V)) (t : Fin k)
  (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))
  (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1))
  (live : (model w n k p θ G t).FreshHistory→Finset (Fin w)) (fallback : Fin w)

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.prepOutBanks
theorem prepared_context_of_mean_oai (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
    (hτ : 0≤τ) (hτsmall : τ≤1/40000) (hn : 0<n)
    (hmean : (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
      ∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*((w*(2*(n+k)):ℝ)-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ hτsmall ((e ω.1.1).supports ω.1.2 i))
        (fun _=>chronoRead b) (preparedTargets w n k p θ G t hp e bad ω.1) tab
        (preparedTree w n k p θ G t hp e live fallback ω.1) (univ,univ)).length))≤
      (w*(2*(n+k)):ℝ)/4) :
    Nonempty (ContextOutput p (fun ω=>flattenTuple (G ω)) (w*(n+k))
      (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
      (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
        w (Nat.log 2 w+1) (2*(n+k))) 2) := by
  have hw : 0<w:=Nat.zero_lt_of_lt fallback.isLt
  have hN : 0<w*(2*(n+k)) :=
    Nat.mul_pos hw (Nat.mul_pos (by decide) (by omega))
  have hmarg : (attachedPrepared w n k p θ G t hp e).μ.map (fun ω=>ω.2)=p :=
    (attachedPrepared w n k p θ G t hp e).marginal
  have hres:=book.context_output hdim hb hH hP haP hτ hτsmall p (fun ω=>flattenTuple (G ω))
    (attachedPrepared w n k p θ G t hp e).μ (fun ω=>ω.2) hmarg
    (fun ω=>(e ω.1.1).supports ω.1.2)
    (fun ω=>preparedTargets w n k p θ G t hp e bad ω.1)
    (fun ω=>preparedTree w n k p θ G t hp e live fallback ω.1)
    (w*(2*(n+k))) w (Nat.log 2 w+1) (2*(n+k)) hN
    (fun ω=>by rw [goodPopulation_length];exact goodPopulation_size w n k p θ G t _ _ _)
    (fun ω=>by rw [liveTree_nodes];simpa using card_le_univ (live ω.1.1.val))
    (fun ω=>by
      apply (liveTree_height _ _).trans
      exact Nat.add_le_add_right (Nat.log_mono_right (by simpa using card_le_univ (live ω.1.1.val))) 1)
    (fun ω i=>by rw [List.length_ofFn];simpa using card_le_univ (goodMiddle w n k p θ G t ω.1.1.val (bad ω.1.1.val) i))
    (fun ω hω=>goodPopulation_sublist w n k p θ G t ω.1.1.val (bad ω.1.1.val)
      (live ω.1.1.val) fallback ((e ω.1.1).source ω.1.2) (G ω.2)
      (fun i=>((attachedPrepared_tuple w n k p θ G t hp e ω hω).2.2 i).symm))
    (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hmean)
  have heq : w*(2*(n+k))/2=w*(n+k) := by
    have : w*(2*(n+k))=2*(w*(n+k)) := by ring
    omega
  simpa only [heq] using hres
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean_oai := @OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean_oai
