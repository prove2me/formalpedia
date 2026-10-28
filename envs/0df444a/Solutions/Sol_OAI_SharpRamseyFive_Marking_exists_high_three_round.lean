-- Prove2me | solution 1 for OAI.SharpRamseyFive.Marking.exists_high_three_round
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:28:53.070953+00:00
-- url     : https://prove2.me/submissions/1753d294-65a8-4bb9-8f45-7a24cca007cc

import Mathlib
import Definitions.Def_OAIQ060R004

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem conditional_deficit_le (p : Law (α × β)) (capA capB : ℝ)
    (hcap : entropy (first p) ≤ capA) :
    (∑ a,first p a*(capB-entropy (fiber p a))) ≤ capA+capB-entropy p := by
  have he : (∑ a,first p a*(capB-entropy (fiber p a))) =
      capB-∑ a,first p a*entropy (fiber p a) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,(first p).sum_one,one_mul]
  rw [he,entropy_chain]
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FinitePiLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι→Type*} [∀i,Fintype (β i)]

lemma piLaw_prod (p : ∀i,Law (β i)) (f : ∀i,β i→ℝ) :
    (∑x,piLaw p x*(∏i,f i (x i)))=∏i,∑a,p i a*f i a := by
  simp only [piLaw,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a=>p i a*f i a)).symm

lemma piLaw_eval_expectation (p : ∀i,Law (β i)) (i : ι) (f : β i→ℝ) :
    (∑x,piLaw p x*f (x i))=∑a,p i a*f a := by
  let g : ∀j,β j→ℝ := fun j a=>if h : j=i then f (h ▸ a) else 1
  have hx (x : ∀j,β j) : (∏j,g j (x j))=f (x i) := by
    have he : (fun j=>g j (x j))=Function.update (fun _=>1) i (f (x i)) := by
      funext j
      by_cases hj : j=i
      · subst j;simp [g]
      · simp [g,hj]
    rw [he,Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hs : (fun j=>∑a,p j a*g j a)=Function.update (fun _=>1) i (∑a,p i a*f a) := by
    funext j
    by_cases hj : j=i
    · subst j;simp [g]
    · simp [g,hj,(p j).sum_one]
  have hh := piLaw_prod p g
  simp_rw [hx] at hh
  rw [hs,Finset.prod_update_of_mem (Finset.mem_univ i)] at hh
  simpa using hh

end

open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ProductHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A : Type} [Fintype B] [Fintype A]

lemma piLaw_update_balance (μ : B → Law A) (s : B → A) (b : B) (a : A) :
    piLaw μ s * μ b a = piLaw μ (Function.update s b a) * μ b (s b) := by
  classical
  have h₁ := Finset.mul_prod_erase Finset.univ (fun c => μ c (s c)) (Finset.mem_univ b)
  have h₂ := Finset.mul_prod_erase Finset.univ
    (fun c => μ c (Function.update s b a c)) (Finset.mem_univ b)
  have hprod : (∏ c ∈ Finset.univ.erase b, μ c (Function.update s b a c)) =
      ∏ c ∈ Finset.univ.erase b, μ c (s c) := by
    apply Finset.prod_congr rfl
    intro c hc
    rw [Function.update_of_ne (Finset.mem_erase.mp hc).1]
  simp only [Function.update_self, hprod] at h₂
  change (∏ c, μ c (s c)) * μ b a = (∏ c, μ c (Function.update s b a c)) * μ b (s b)
  rw [←h₁, ←h₂]
  ring

theorem independent_selected_identity (μ : B → Law A)
    (f : (B → A) → B → A → ℝ)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (∑ s, piLaw μ s * f s b (s b)) =
      ∑ s, piLaw μ s * (∑ a, μ b a * f s b a) := by
  classical
  have hh := Fintype.sum_equiv (RepresentativeAverage.swapAt (A := A) b)
    (fun z => piLaw μ z.1 * μ b z.2 * f z.1 b (z.1 b))
    (fun z => piLaw μ z.1 * μ b z.2 * f z.1 b z.2) (by
      intro z
      simp only [RepresentativeAverage.swapAt, Function.Involutive.toPerm, Equiv.coe_fn_mk]
      rw [hown]
      rw [←piLaw_update_balance]
      )
  simp only [Fintype.sum_prod_type] at hh
  calc
    _ = ∑ s, ∑ a, piLaw μ s * μ b a * f s b (s b) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [←Finset.sum_mul, ←Finset.mul_sum, (μ b).sum_one, mul_one]
    _ = ∑ s, ∑ a, piLaw μ s * μ b a * f s b a := hh
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LogSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

theorem log_sum (f g : α → ℝ) (hf : ∀ a,0≤f a) (hg : ∀ a,0≤g a)
    (hac : ∀ a,0<f a → 0<g a) :
    (∑ a,f a)*Real.log ((∑ a,f a)/(∑ a,g a)) ≤ ∑ a,f a*Real.log (f a/g a) := by
  let F := ∑ a,f a
  let G := ∑ a,g a
  have hF0 : 0≤F := Finset.sum_nonneg fun a _ => hf a
  by_cases hFz : F=0
  · have hzero (a : α) : f a=0 := by
      have hle : f a≤F := Finset.single_le_sum (fun b _ => hf b) (Finset.mem_univ a)
      exact le_antisymm (hle.trans_eq hFz) (hf a)
    simp only [hzero,Finset.sum_const_zero,zero_mul]
    exact le_rfl
  have hF : 0<F := lt_of_le_of_ne hF0 (Ne.symm hFz)
  have hG : 0<G := by
    have hex : ∃ a,0<f a := by
      by_contra! hn
      have hnon : F≤0 := Finset.sum_nonpos fun a _ => hn a
      exact (not_le_of_gt hF) hnon
    obtain ⟨a,ha⟩ := hex
    exact (hac a ha).trans_le (Finset.single_le_sum (fun b _ => hg b) (Finset.mem_univ a))
  let p : Law α :=
    { mass := fun a => f a/F
      nonneg := fun a => div_nonneg (hf a) hF.le
      sum_one := by rw [←Finset.sum_div]; exact div_self hFz }
  let q : Law α :=
    { mass := fun a => g a/G
      nonneg := fun a => div_nonneg (hg a) hG.le
      sum_one := by rw [←Finset.sum_div]; exact div_self (ne_of_gt hG) }
  have hD : 0≤divergence p q := by
    apply divergence_nonneg p q
    intro a ha
    exact div_pos (hac a ((div_pos_iff_of_pos_right hF).mp ha)) hG
  have he (a : α) : f a*Real.log (f a/g a) =
      f a*Real.log (F/G)+F*(p a*Real.log (p a/q a)) := by
    by_cases hz : f a=0
    · simp [p,hz]
    · have hfp : 0<f a := lt_of_le_of_ne (hf a) (Ne.symm hz)
      have hgp := hac a hfp
      dsimp [p,q]
      rw [Real.log_div hz (ne_of_gt hgp),Real.log_div hFz (ne_of_gt hG),
        Real.log_div (ne_of_gt (div_pos hfp hF)) (ne_of_gt (div_pos hgp hG)),
        Real.log_div hz hFz,Real.log_div (ne_of_gt hgp) (ne_of_gt hG)]
      field_simp
      ring
  calc
    _ ≤ F*Real.log (F/G)+F*divergence p q := le_add_of_nonneg_right (mul_nonneg hF.le hD)
    _ = _ := by
      simp only [he,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,divergence,F]

theorem divergence_map_le (p q : Law α) (hac : ∀ a,0<p a → 0<q a) (f : α → β) :
    divergence (map p f) (map q f) ≤ divergence p q := by
  have hpoint (b : β) := log_sum
    (fun a => if f a=b then p a else 0)
    (fun a => if f a=b then q a else 0)
    (fun a => by split_ifs; exact p.nonneg a; exact le_rfl)
    (fun a => by split_ifs; exact q.nonneg a; exact le_rfl)
    (fun a ha => by
      split_ifs at ha ⊢ with h
      · exact hac a ha
      · exact (lt_irrefl _ ha).elim)
  have hs := Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => hpoint b)
  change divergence (map p f) (map q f) ≤ _ at hs
  apply hs.trans_eq
  rw [Finset.sum_comm]
  unfold divergence
  apply Finset.sum_congr rfl
  intro a _
  have hterm (b : β) : (if f a=b then p a else 0)*Real.log
      ((if f a=b then p a else 0)/(if f a=b then q a else 0)) =
      if f a=b then p a*Real.log (p a/q a) else 0 := by
    split_ifs <;> simp
  simp only [hterm]
  classical
  simp

lemma map_product {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law α) (q : Law β) (f : α → γ) (g : β → δ) :
    map (product p q) (fun z => (f z.1,g z.2)) = product (map p f) (map q g) := by
  apply Law.ext
  funext z
  simp only [map,product,Fintype.sum_prod_type]
  have he (a : α) (b : β) :
      (if (f a,g b)=z then p a*q b else 0) =
        (if f a=z.1 then p a else 0)*(if g b=z.2 then q b else 0) := by
    rcases z with ⟨c,d⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [he,←Finset.mul_sum,←Finset.sum_mul]

theorem mutual_information_map_le {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    entropy (map (first p) f)+entropy (map (second p) g)-
      entropy (map p (fun z => (f z.1,g z.2))) ≤
    entropy (first p)+entropy (second p)-entropy p := by
  have h := divergence_map_le p (product (first p) (second p)) (ac_product p)
    (fun z => (f z.1,g z.2))
  rw [map_product] at h
  have h1 : first (map p (fun z => (f z.1,g z.2)))=map (first p) f := by
    change first (pair p (f ∘ Prod.fst) (g ∘ Prod.snd))=_
    rw [first_pair,←map_comp,map_first]
  have h2 : second (map p (fun z => (f z.1,g z.2)))=map (second p) g := by
    change second (pair p (f ∘ Prod.fst) (g ∘ Prod.snd))=_
    rw [second_pair,←map_comp,map_second]
  rw [←h1,←h2,mutual_information,mutual_information] at h
  rw [h1,h2] at h
  exact h

end

open scoped BigOperators Classical
variable {α β γ ι : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

lemma information_conditional (p : Law (α × β)) :
    information p = entropy (second p)-∑ a,first p a*entropy (fiber p a) := by
  dsimp [information]
  rw [entropy_chain]
  ring

theorem total_correlation_drop (p : Law (α × (ι → β))) :
    (entropy (first p)+(∑ i,entropy (map (second p) (fun x => x i)))-entropy p)-
      (∑ a,first p a*totalCorrelation (fiber p a)) =
      ∑ i,information (mapSnd p (fun x => x i)) := by
  have hI (i : ι) : information (mapSnd p (fun x => x i)) =
      entropy (map (second p) (fun x => x i))-
      ∑ a,first p a*entropy (map (fiber p a) (fun x => x i)) := by
    rw [information_conditional,second_mapSnd,first_mapSnd]
    simp only [fiber_mapSnd]
  simp only [hI,totalCorrelation,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a i => first p a*entropy (map (fiber p a) (fun x => x i)))]
  rw [entropy_chain]
  ring

lemma information_observation_le (p : Law (α × β)) (f : α → γ) :
    information (map p (fun z => (f z.1,z.2))) ≤ information p := by
  have hh := mutual_information_map_le p f id
  have h1 : first (map p (fun z => (f z.1,z.2)))=map (first p) f := by
    change first (pair p (f ∘ Prod.fst) (id ∘ Prod.snd))=_
    rw [first_pair]
    rw [←map_comp,map_first]
  have h2 : second (map p (fun z => (f z.1,z.2)))=second p := by
    change second (pair p (f ∘ Prod.fst) Prod.snd)=_
    rw [second_pair,map_second]
  simpa only [information,h1,h2,map_id,id_eq] using hh

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SplitLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {ι β : Type*} [Fintype ι] [Fintype β]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSubtypeMemFinset_solutions
lemma first_reveal (p : Law (ι → β)) (E : Finset ι) :
    first (reveal p E) = map p (fun x (i : E) => x i.val) := first_pair _ _ _

lemma entropy_reveal (p : Law (ι → β)) (E : Finset ι) :
    entropy (reveal p E) = entropy p := by
  apply entropy_map_injective
  intro x y he
  exact congrArg Prod.snd he

lemma information_reveal_selected (p : Law (ι → β)) (E : Finset ι) (i : ι) (hi : i∈E) :
    information (mapSnd (reveal p E) (fun x => x i)) = entropy (map p (fun x => x i)) := by
  let e : E := ⟨i,hi⟩
  have he : mapSnd (reveal p E) (fun x => x i)=
      map (first (reveal p E)) (fun y => (y,y e)) := by
    rw [first_reveal]
    simp only [reveal,mapSnd,pair,map_comp,Function.comp_def,id_eq]
    rfl
  have hH : entropy (mapSnd (reveal p E) (fun x => x i))=
      entropy (first (reveal p E)) := by
    rw [he]
    apply entropy_map_injective
    intro x y h
    exact congrArg Prod.fst h
  simp only [information,first_mapSnd,second_mapSnd,second_reveal,hH]
  ring

lemma entropy_reveal_le_coordinate_sum (p : Law (ι → β)) (E : Finset ι) :
    entropy (first (reveal p E)) ≤ ∑ i∈E,entropy (map p (fun x => x i)) := by
  have hh := totalCorrelation_nonneg (first (reveal p E))
  simp only [totalCorrelation,first_reveal,map_comp,Function.comp_def] at hh
  rw [Finset.sum_coe_sort E (fun i : ι => entropy (map p (fun x => x i)))] at hh
  simpa only [first_reveal] using (sub_nonneg.mp hh)

theorem reveal_information_budget (p : Law (ι → β)) (E : Finset ι) :
    (∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i)))+
      (∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a)) ≤
        totalCorrelation p := by
  have hh := total_correlation_drop (reveal p E)
  simp only [second_reveal,entropy_reveal] at hh
  have hb := entropy_reveal_le_coordinate_sum p E
  have hs := Finset.sum_add_sum_compl E
    (fun i => information (mapSnd (reveal p E) (fun x => x i)))
  have hsel : (∑ i∈E,information (mapSnd (reveal p E) (fun x => x i)))=
      ∑ i∈E,entropy (map p (fun x => x i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact information_reveal_selected p E i hi
  rw [hsel] at hs
  change (∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i)))+
      (∑ a,first (reveal p E) a*totalCorrelation (fiber (reveal p E) a)) ≤
        (∑ i,entropy (map p (fun x => x i)))-entropy p
  linarith

theorem reveal_coordinate_information_le (p : Law (ι → β)) (E : Finset ι)
    (j : E) (i : ι) :
    information (pair p (fun x => x j.val) (fun x => x i)) ≤
      information (mapSnd (reveal p E) (fun x => x i)) := by
  have hh := information_observation_le (mapSnd (reveal p E) (fun x => x i))
    (fun y => y j)
  simpa only [reveal,mapSnd,pair,map_comp,Function.comp_def,id_eq] using hh

end

open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RepresentativeSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical NNReal
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions
noncomputable local instance instDecidableEqSubtypeSumProdMemFinset_solutions_r11b48c_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
omit [Fintype A] [Fintype T] in
lemma mem_representativeSet_left (s : B → A) (b : B) (a : A) :
    Sum.inl (b,a) ∈ representativeSet (T := T) s ↔ a=s b := by
  simp [representativeSet,eq_comm]

omit [Fintype A] [Fintype T] in
lemma not_mem_representativeSet_right (s : B → A) (t : T) :
    Sum.inr t ∉ representativeSet s := by simp [representativeSet]

lemma blockInformation_own_independent (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a i : A) :
    blockInformation p (Function.update s b a) b i=blockInformation p s b i := by
  apply Finset.sup_congr rfl
  intro c hc
  rw [Function.update_of_ne (Finset.mem_erase.mp hc).1]

lemma blockInformation_le_reveal (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a : A) :
    (blockInformation p s b a:ℝ) ≤ information
      (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inl (b,a)))) := by
  let z : ℝ≥0 := ⟨information (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inl (b,a)))),information_nonneg _⟩
  change (blockInformation p s b a:ℝ) ≤ (z:ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro c _
  exact reveal_coordinate_information_le p (representativeSet s)
    ⟨Sum.inl (c,s c),(mem_representativeSet_left s c (s c)).mpr rfl⟩ (Sum.inl (b,a))

lemma middleInformation_le_reveal (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (t : T) :
    (middleInformation p s t:ℝ) ≤ information
      (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inr t))) := by
  let z : ℝ≥0 := ⟨information (mapSnd (reveal p (representativeSet s)) (fun x => x (Sum.inr t))),information_nonneg _⟩
  change (middleInformation p s t:ℝ) ≤ (z:ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro c _
  exact reveal_coordinate_information_le p (representativeSet s)
    ⟨Sum.inl (c,s c),(mem_representativeSet_left s c (s c)).mpr rfl⟩ (Sum.inr t)

theorem representative_unselected_le_cost (p : Law (((B × A) ⊕ T) → β)) (s : B → A) :
    (∑ b,∑ a∈Finset.univ.erase (s b),(blockInformation p s b a:ℝ))+
      (∑ t,(middleInformation p s t:ℝ)) ≤ revealCost p (representativeSet s) := by
  classical
  let f : ((B × A) ⊕ T) → ℝ := fun i =>
    information (mapSnd (reveal p (representativeSet s)) (fun x => x i))
  have he : revealCost p (representativeSet s)=
      (∑ b,∑ a∈Finset.univ.erase (s b),f (Sum.inl (b,a)))+∑ t,f (Sum.inr t) := by
    unfold revealCost
    change (∑ i∈(representativeSet s)ᶜ,f i)=_
    have hfilt : (representativeSet (T := T) s)ᶜ=Finset.univ.filter (fun i => i∉representativeSet s) := by ext i; simp
    rw [hfilt,Finset.sum_filter,Fintype.sum_sum_type]
    simp only [mem_representativeSet_left,not_mem_representativeSet_right,
      not_false_eq_true,ite_true,Fintype.sum_prod_type]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [←Finset.sum_filter]
    rw [Finset.filter_ne']
  rw [he]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    exact blockInformation_le_reveal p s b a
  · exact Finset.sum_le_sum fun t _ => middleInformation_le_reveal p s t

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UnusedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions_1
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_1_r11b48c_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
lemma uniformOn_expectation (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    (∑ a, uniformOn S hS a * f a) = (S.card : ℝ)⁻¹ * ∑ a ∈ S, f a := by
  simp only [uniformOn]
  calc
    _ = ∑ a, if a ∈ S then (S.card : ℝ)⁻¹ * f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by rw [←Finset.sum_filter, Finset.filter_univ_mem, Finset.mul_sum]

lemma piLaw_uniformOn_zero (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (s : B → A) {b : B} (h : s b ∉ S b) :
    piLaw (fun b => uniformOn (S b) (hS b)) s = 0 := by
  classical
  change (∏ b, uniformOn (S b) (hS b) (s b)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [uniformOn,h])

theorem unused_selected_identity (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (f : (B → A) → B → A → ℝ)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (S b).card * (∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * f s b (s b)) =
      ∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * (∑ a ∈ S b, f s b a) := by
  classical
  rw [independent_selected_identity _ f hown]
  simp_rw [uniformOn_expectation]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hc : ((S b).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hS b))
  field_simp

theorem unused_all_le_twice_unselected (S : B → Finset A)
    (hS : ∀ b, (S b).Nonempty) (hsize : ∀ b, 2 ≤ (S b).card)
    (f : (B → A) → B → A → ℝ) (hf : ∀ s b a, 0 ≤ f s b a)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s * (∑ a ∈ S b, f s b a)) ≤
      2*(∑ s, piLaw (fun b => uniformOn (S b) (hS b)) s *
        (∑ a ∈ (S b).erase (s b), f s b a)) := by
  classical
  let w := piLaw (fun b => uniformOn (S b) (hS b))
  have hi := unused_selected_identity S hS f hown b
  have hs : (∑ s, w s * (∑ a ∈ S b, f s b a)) =
      (∑ s, w s * f s b (s b)) +
      (∑ s, w s * (∑ a ∈ (S b).erase (s b), f s b a)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : s b ∈ S b
    · rw [←mul_add, Finset.add_sum_erase _ _ h]
    · have hz : w s = 0 := piLaw_uniformOn_zero S hS s h
      simp [hz]
  have hn : 0 ≤ ∑ s, w s * f s b (s b) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (w.nonneg s) (hf s b (s b))
  have hc : (2 : ℝ) ≤ (S b).card := by exact_mod_cast hsize b
  change (S b).card * (∑ s, w s * f s b (s b)) = _ at hi
  change (∑ s, w s * (∑ a ∈ S b, f s b a)) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hc hn]

theorem unused_information_le_twice_cost
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (hS : ∀ b, (S b).Nonempty) (hsize : ∀ b, 2 ≤ (S b).card) :
    (∑ s : B → A, piLaw (fun b => uniformOn (S b) (hS b)) s *
      ((∑ b : B, ∑ a ∈ S b, (blockInformation p s b a : ℝ)) +
        ∑ t : T, (middleInformation p s t : ℝ))) ≤
      2 * (∑ s : B → A, piLaw (fun b => uniformOn (S b) (hS b)) s *
        revealCost p (representativeSet s)) := by
  classical
  let w := piLaw (fun b => uniformOn (S b) (hS b))
  have hb := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset B)) =>
    unused_all_le_twice_unselected S hS hsize
      (fun s b a => (blockInformation p s b a : ℝ))
      (fun _ _ _ => NNReal.coe_nonneg _) (fun s b a i =>
        congrArg NNReal.toReal (blockInformation_own_independent p s b a i)) b)
  have hc (s : B → A) :
      (∑ b : B, ∑ a ∈ (S b).erase (s b), (blockInformation p s b a : ℝ)) +
      (∑ t : T, (middleInformation p s t : ℝ)) ≤ revealCost p (representativeSet s) := by
    apply le_trans _ (representative_unselected_le_cost p s)
    apply add_le_add _ le_rfl
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.erase_subset_erase (s b) (Finset.subset_univ _)
    · intro a _ _
      exact NNReal.coe_nonneg _
  have hh := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (B → A))) =>
    mul_le_mul_of_nonneg_left (hc s) (w.nonneg s))
  have hm : 0 ≤ ∑ s : B → A, w s * ∑ t : T, (middleInformation p s t : ℝ) := by
    exact Finset.sum_nonneg fun s _ => mul_nonneg (w.nonneg s)
      (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)
  have hb' :
      (∑ s : B → A, w s * (∑ b : B, ∑ a ∈ S b, (blockInformation p s b a : ℝ))) ≤
      2 * (∑ s : B → A, w s * (∑ b : B, ∑ a ∈ (S b).erase (s b),
        (blockInformation p s b a : ℝ))) := by
    calc
      _ = ∑ b : B, ∑ s : B → A, w s * (∑ a ∈ S b, (blockInformation p s b a : ℝ)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ b : B, 2 * (∑ s : B → A, w s * (∑ a ∈ (S b).erase (s b),
        (blockInformation p s b a : ℝ))) := hb
      _ = _ := by
        rw [←Finset.mul_sum]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
  change (∑ s : B → A, w s * _) ≤ 2 * (∑ s : B → A, w s * _)
  simp only [mul_add, Finset.sum_add_distrib] at hh ⊢
  linarith only [hb',hh,hm]

end

open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_nonneg (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ mean p f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (hf a)
lemma mean_mono (p : Law α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : mean p f ≤ mean p g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a)
lemma mean_add (p : Law α) (f g : α → ℝ) : mean p (fun a => f a + g a) = mean p f + mean p g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]
lemma mean_smul (p : Law α) (c : ℝ) (f : α → ℝ) : mean p (fun a => c * f a) = c * mean p f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]
lemma mean_finset_sum {ι : Type*} (p : Law α) (s : Finset ι) (f : ι → α → ℝ) :
    mean p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean p (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm
lemma mean_sum {ι : Type*} [Fintype ι] (p : Law α) (f : ι → α → ℝ) :
    mean p (fun a => ∑ i, f i a) = ∑ i, mean p (f i) := mean_finset_sum p Finset.univ f
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BlockReveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions_2
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_2_r11b48c_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
lemma freshBlockLaw_eq (S : B → Finset A) (hS : ∀ b, (S b).Nonempty) :
    freshBlockLaw S = piLaw (fun b => uniformOn (S b) (hS b)) := by
  simp only [freshBlockLaw, dite_eq_left (hS _)]

omit [Fintype B] [Fintype A] [Nonempty A] in
lemma eraseBlock_card (S : B → Finset A) (s : B → A) (n : ℕ)
    (hS : ∀ b, n+1 ≤ (S b).card) : ∀ b, n ≤ (eraseBlock S s b).card := by
  intro b
  have := hS b
  simp only [eraseBlock, Finset.card_erase_eq_ite]
  split_ifs <;> omega

lemma blockAllInformation_mean_le (p : Law (((B × A) ⊕ T) → β))
    (S : B → Finset A) (hS : ∀ b, 2 ≤ (S b).card) :
    mean (freshBlockLaw S) (blockAllInformation p S) ≤
      2 * mean (freshBlockLaw S) (fun s => revealCost p (representativeSet s)) := by
  have hn : ∀ b, (S b).Nonempty := fun b => Finset.card_pos.mp (by have := hS b; omega)
  rw [freshBlockLaw_eq S hn]
  exact unused_information_le_twice_cost p S hn hS

omit [Nonempty A] in
lemma mean_reveal_budget (p : Law (((B × A) ⊕ T) → β)) (μ : Law (B → A)) :
    mean μ (fun s => revealCost p (representativeSet s)) +
      mean μ (fun s => mean (first (reveal p (representativeSet s)))
        (fun a => totalCorrelation (fiber (reveal p (representativeSet s)) a))) ≤
          totalCorrelation p := by
  rw [←mean_add]
  apply le_trans (mean_mono μ (fun s => reveal_information_budget p (representativeSet s)))
  exact (mean_const μ (totalCorrelation p)).le

theorem block_information_telescope
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (n : ℕ) (hS : ∀ b, n+1 ≤ (S b).card) :
    (∑ i : Fin n, blockRoundMean blockAllInformation p S n i) ≤ 2 * totalCorrelation p := by
  induction n generalizing p S with
  | zero => simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (totalCorrelation_nonneg p)
  | succ n ih =>
    have hsize : ∀ b, 2 ≤ (S b).card := fun b => by have := hS b; omega
    have hn (s : B → A) : ∀ b, n+1 ≤ (eraseBlock S s b).card :=
      eraseBlock_card S s (n+1) hS
    have hcost := blockAllInformation_mean_le p S hsize
    have hbudget := mean_reveal_budget p (freshBlockLaw S)
    simp only [blockRoundMean, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    have htail :
        (∑ i : Fin n, mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => blockRoundMean blockAllInformation (fiber (reveal p (representativeSet s)) a)
            (eraseBlock S s) n i))) ≤
        2 * mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => totalCorrelation (fiber (reveal p (representativeSet s)) a))) := by
      rw [←mean_sum]
      simp_rw [←mean_sum]
      calc
        _ ≤ mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
          (fun a => 2 * totalCorrelation (fiber (reveal p (representativeSet s)) a))) := by
            apply mean_mono
            intro s
            apply mean_mono
            intro a
            exact ih _ _ (hn s)
        _ = _ := by simp_rw [mean_smul]
    linarith only [htail,hcost,hbudget]

end
end

open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GoodEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma goodFirst_positive (p : Law (α × β)) (NA N K : ℝ) (hNA : 0<NA)
    (a : α) (ha : a ∈ goodFirstEndpoints p NA N K) : 0 < first p a := by
  exact (div_pos (Real.exp_pos _) hNA).trans_le (Finset.mem_filter.mp ha).2.1

lemma goodFirst_conditional_cap (p : Law (α × β)) (NA N K : ℝ)
    (hNA : 0<NA) (hN : 0<N) (a : α) (ha : a∈goodFirstEndpoints p NA N K)
    (b : β) (hb : b ∉ heavyRow p N K a) :
    fiber p a b ≤ Real.exp (2*K)*NA/N := by
  have hlo := (Finset.mem_filter.mp ha).2.1
  have hfp := goodFirst_positive p NA N K hNA a ha
  have hj : N*p (a,b) ≤ Real.exp K := by
    simpa only [heavyRow,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hb
  have hscale : (Real.exp (-K)/NA) * (Real.exp (2*K)*NA/N) = Real.exp K/N := by
    have hexp : Real.exp (-K) * Real.exp (2*K) = Real.exp K := by rw [←Real.exp_add]; congr 1; ring
    rw [div_mul_div_comm]
    calc
      _ = (Real.exp (-K)*Real.exp (2*K))/N := by field_simp
      _ = _ := by rw [hexp]
  have hprod := mul_le_mul_of_nonneg_right hlo (show 0 ≤ Real.exp (2*K)*NA/N by positivity)
  rw [hscale] at hprod
  have hmass : first p a * fiber p a b ≤ Real.exp K/N := by
    rw [←mass_eq_first_mul_fiber]
    exact (le_div_iff₀ hN).mpr (by simpa [mul_comm] using hj)
  exact (mul_le_mul_iff_right₀ hfp).mp (hmass.trans hprod)
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Failure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {α β : Type*} [Fintype α] [Fintype β]

lemma failure_nonneg (p : Law α) (v : α → V) (f : Module.Dual K V) : 0≤failure p v f := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact p.nonneg a
  · exact le_rfl

lemma mem_core (p : Law α) (v : α → V) (ρ : ℝ) (x : V) :
    x∈core (K := K) p v ρ ↔ ∀ f : Module.Dual K V,failure p v f≤ρ → f x=0 := by
  simp only [core,Submodule.mem_iInf,LinearMap.mem_ker]
  exact ⟨fun h f hf => h ⟨f,hf⟩,fun h f => h f.val f.property⟩

theorem core_failure [FiniteDimensional K V] (p : Law α) (v : α → V) (ρ : ℝ) (hρ : 0≤ρ) :
    (∑ a,if v a∉core (K := K) p v ρ then p a else 0)≤finrank K V*ρ := by
  let S : Set (Module.Dual K V) := {f | failure p v f≤ρ}
  obtain ⟨T,hTS,hcard,hspan,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn K S
  have hT : T.card≤finrank K V := by
    rw [hcard]
    exact (Submodule.finrank_le (Submodule.span K S)).trans_eq Subspace.dual_finrank_eq
  have hex (x : V) (hx : x∉core (K := K) p v ρ) : ∃ f∈T,f x≠0 := by
    by_contra hn
    have hz : ∀ f∈T,f x=0 := by simpa only [not_exists,not_and,not_not] using hn
    have hle : Submodule.span K (T:Set (Module.Dual K V))≤LinearMap.ker (Module.Dual.eval K V x) := by
      apply Submodule.span_le.mpr
      intro f hf
      exact hz f hf
    rw [hspan] at hle
    apply hx
    apply (mem_core (K := K) p v ρ x).mpr
    intro f hf
    exact hle (Submodule.subset_span (show f∈S from hf))
  have hpoint (a : α) :
      (if v a∉core (K := K) p v ρ then p a else 0)≤∑ f∈T,if f (v a)≠0 then p a else 0 := by
    by_cases h : v a∈core (K := K) p v ρ
    · simp only [h,not_true_eq_false,ite_false]
      exact Finset.sum_nonneg fun _ _ => by split_ifs; exact p.nonneg a; exact le_rfl
    · obtain ⟨f,hf,hfa⟩ := hex (v a) h
      simp only [h,not_false_eq_true,ite_true]
      have hh := Finset.single_le_sum (s := T) (f := fun f => if f (v a)≠0 then p a else 0)
        (fun _ _ => by split_ifs; exact p.nonneg a; exact le_rfl) hf
      simpa only [ite_eq_left hfa] using hh
  calc
    _ ≤ ∑ a,∑ f∈T,if f (v a)≠0 then p a else 0 := Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ f∈T,failure p v f := by rw [Finset.sum_comm]; rfl
    _ ≤ ∑ _f∈T,ρ := Finset.sum_le_sum fun f hf => hTS hf
    _ = (T.card:ℝ)*ρ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hρ

theorem core_orthogonal (p : Law α) (v : α → Module.Dual K V)
    (q : Law β) (w : β → V) (ρ : ℝ) (hρ : 0<ρ)
    (hmiss : (∑ b,q b*failure p v (Module.Dual.eval K V (w b)))≤ρ^2)
    (x : Module.Dual K V) (hx : x∈core (K := K) p v ρ)
    (y : V) (hy : y∈core (K := K) q w ρ) : x y=0 := by
  let B := Finset.univ.filter fun b => ρ<failure p v (Module.Dual.eval K V (w b))
  have hmass : ρ*(∑ b∈B,q b)≤ρ^2 := by
    calc
      _ ≤ ∑ b∈B,q b*failure p v (Module.Dual.eval K V (w b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro b hb
        have hh := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hb).2.le (q.nonneg b)
        simpa only [mul_comm ρ] using hh
      _ ≤ ∑ b,q b*failure p v (Module.Dual.eval K V (w b)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun b _ _ => mul_nonneg (q.nonneg b) (failure_nonneg p v _))
      _ ≤ _ := hmiss
  have hB : (∑ b∈B,q b)≤ρ := by nlinarith
  have hf : failure q w x≤ρ := by
    apply le_trans _ hB
    rw [failure]
    have hh : (∑ b∈B,q b)=(∑ b,if b∈B then q b else 0) := by
      rw [←Finset.sum_filter]
      simp only [Finset.filter_univ_mem]
    rw [hh]
    apply Finset.sum_le_sum
    intro b _
    by_cases h : x (w b)=0
    · simp only [h,ne_eq,not_true_eq_false,ite_false]
      split_ifs; exact q.nonneg b; exact le_rfl
    · have hb : b∈B := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        by_contra hn
        have he := (mem_core (K := K) p v ρ x).mp hx (Module.Dual.eval K V (w b)) (le_of_not_gt hn)
        exact h he
      simp only [h,ne_eq,not_false_eq_true,ite_true,hb,le_refl]
  exact (mem_core (K := K) q w ρ y).mp hy x hf

end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CoreGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry

section
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem subspace_mass_cap [Finite K] [Fintype (ℙ K V)]
    (p : Law (ℙ K V)) (W : Submodule K V) (B : Finset (ℙ K V))
    (c δ ε : ℝ) (hc : 0 ≤ c)
    (hlight : ∀ a,a∉B → p a ≤ c)
    (hbad : (∑ a∈B,p a)≤δ)
    (hout : (∑ a,if a.rep∉W then p a else 0)≤ε) :
    1-ε-δ ≤ c*(∑ i∈Finset.range (finrank K W),(Nat.card K:ℝ)^i) := by
  have hp (a : ℙ K V) : p a≤(if a.rep∈W then c else 0)+
      (if a.rep∉W then p a else 0)+(if a∈B then p a else 0) := by
    by_cases hW : a.rep∈W <;> by_cases hB : a∈B <;> simp only [hW,hB,
      not_true_eq_false,not_false_eq_true,ite_true,ite_false]
    · linarith [p.nonneg a]
    · simpa using hlight a hB
    · linarith [p.nonneg a]
    · simp
  have hs := Finset.sum_le_sum (fun a (_ha : a∈(Finset.univ : Finset (ℙ K V))) => hp a)
  rw [p.sum_one,Finset.sum_add_distrib,Finset.sum_add_distrib] at hs
  have hb : (∑ a,if a∈B then p a else 0)=∑ a∈B,p a := by
    rw [←Finset.sum_filter]; simp only [Finset.filter_univ_mem]
  have hw : (∑ a : ℙ K V,if a.rep∈W then c else 0)=
      c*(∑ i∈Finset.range (finrank K W),(Nat.card K:ℝ)^i) := by
    have hn : (Finset.univ.filter fun a : ℙ K V => a.rep∈W).card=
        ∑ i∈Finset.range (finrank K W),Nat.card K^i := by
      rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card]
      rw [Nat.card_congr (Equiv.subtypeEquivRight fun a => rep_mem_iff a W)]
      exact SharpRamseyFive.ProjectiveIncidence.card_subspacePoints W
    rw [←Finset.sum_filter,Finset.sum_const, nsmul_eq_mul,hn,mul_comm]
    norm_cast
  rw [hb,hw] at hs
  linarith

lemma geometric_card_bound (q : ℝ) (hq : 2≤q) (r : ℕ) :
    (∑ i∈Finset.range r,q^i)≤2*q^(r-1) := by
  cases r with
  | zero => simp
  | succ r =>
    simp only [Nat.add_sub_cancel]
    have h := geom_sum_mul q (r+1)
    rw [pow_succ] at h
    have hp : 0≤q^r := pow_nonneg (by linarith) _
    have hh : q*q^r≤2*q^r*(q-1) := by nlinarith
    have hq' : 0<q-1 := by linarith
    nlinarith

theorem core_dimension_mass [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
    (p : Law (ℙ K V)) (ρ c δ : ℝ) (hρ : 0≤ρ) (hc : 0 ≤ c)
    (B : Finset (ℙ K V)) (hlight : ∀ a,a∉B → p a ≤ c)
    (hbad : (∑ a∈B,p a)≤δ) :
    1-(finrank K V:ℝ)*ρ-δ ≤ c*(∑ i∈Finset.range
      (finrank K (core (K := K) p Projectivization.rep ρ)),(Nat.card K:ℝ)^i) := by
  exact subspace_mass_cap p _ B c δ _ hc hlight hbad (core_failure p _ ρ hρ)

end

section
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical

lemma rank_from_light_mass {q A s : ℝ} {r : ℕ} (hq : 2≤q) (hA : 0<A)
    (hs : 2 ≤ s)
    (hmass : (191/200:ℝ)≤(Real.exp (2*s)*A/q^4)*(∑ i∈Finset.range r,q^i)) :
    ⌈5-(Real.log A+3*s)/Real.log q⌉₊ ≤ r := by
  have hq0 : 0<q := by linarith
  have hlogq : 0<Real.log q := Real.log_pos (by linarith)
  have hr : 1 ≤ r := by
    by_contra hn
    have hz : r=0 := by omega
    norm_num [hz] at hmass
  have hc : 0<Real.exp (2*s)*A/q^4 := by positivity
  have he : (191/200:ℝ)≤2*(Real.exp (2*s)*A/q^4)*q^(r-1) := by
    have h := mul_le_mul_of_nonneg_left (geometric_card_bound q hq r) hc.le
    exact hmass.trans (by convert h using 1; ring)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<191/200) he
  have hr0 : q^(r-1)≠0 := ne_of_gt (pow_pos hq0 _)
  rw [Real.log_mul (by positivity : (2:ℝ)*(Real.exp (2*s)*A/q^4)≠0) hr0,
    Real.log_mul (by norm_num : (2:ℝ)≠0) hc.ne',Real.log_div (by positivity)
      (by positivity : q^4≠0),Real.log_mul (Real.exp_ne_zero _) hA.ne',
    Real.log_exp,Real.log_pow,Real.log_pow] at hl
  rw [Nat.cast_sub hr] at hl
  norm_num only [Nat.cast_one,Nat.cast_ofNat] at hl
  have hconstant : Real.log 2-Real.log (191/200:ℝ)≤ s := by
    rw [←Real.log_div (by norm_num : (2:ℝ)≠0) (by norm_num : (191/200:ℝ)≠0)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2/(191/200))
    linarith
  apply Nat.ceil_le.mpr
  apply (mul_le_mul_iff_left₀ hlogq).mp

  have heq : (5-(Real.log A+3*s)/Real.log q)*Real.log q=
      5*Real.log q-(Real.log A+3*s) := by field_simp
  rw [heq]
  nlinarith

theorem core_dimension_lower {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] (hdim : finrank K V=5)
    (p : Law (ℙ K V)) (A s : ℝ) (hA : 0<A) (hs : 2 ≤ s)
    (B : Finset (ℙ K V))
    (hlight : ∀ a,a∉B → p a≤Real.exp (2*s)*A/(Nat.card K:ℝ)^4)
    (hbad : (∑ a∈B,p a)≤1/50) :
    ⌈5-(Real.log A+3*s)/Real.log (Nat.card K)⌉₊≤
      finrank K (core (K := K) p Projectivization.rep (1/200)) := by
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K))
  apply rank_from_light_mass hq hA hs
  have h := core_dimension_mass p (1/200) (Real.exp (2*s)*A/(Nat.card K:ℝ)^4)
    (1/50) (by norm_num) (by positivity) B hlight hbad
  rw [hdim] at h
  norm_num at h ⊢
  exact h
end

section
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem high_band_rectangles (hdim : finrank K V=5)
    (U : Submodule K (Module.Dual K V)) (W : Submodule K V)
    (hU : 2≤finrank K U) (hW : 2≤finrank K W)
    (horth : U≤W.dualAnnihilator) (a c : V) (b y : Module.Dual K V)
    (ha : a∈U.dualCoannihilator) (hb : b∈U) (hc : c∈W)
    (hy : y∈W.dualAnnihilator) (hay : y a=0) :
    (InRectangle U a b ∧ InRectangle U c y) ∨
      (InRectangle W.dualAnnihilator a b ∧ InRectangle W.dualAnnihilator c y) := by
  by_cases hyU : y∈U
  · left
    refine ⟨⟨ha,hb⟩,?_,hyU⟩
    apply (Submodule.mem_dualCoannihilator c).mpr
    intro f hf
    exact (Submodule.mem_dualAnnihilator f).mp (horth hf) c hc
  · right
    let S := U⊔Submodule.span K {y}
    have hUS : U<S := by
      apply lt_of_le_of_ne le_sup_left
      intro he
      apply hyU
      rw [he]
      exact (show Submodule.span K {y}≤S from le_sup_right)
        (Submodule.subset_span (Set.mem_singleton y))
    have hSV : S≤W.dualAnnihilator := by
      apply sup_le horth
      rw [Submodule.span_singleton_le_iff_mem]; exact hy
    have hS : S=W.dualAnnihilator := by
      apply Submodule.eq_of_le_of_finrank_eq hSV
      have ht := Submodule.finrank_lt_finrank_of_lt hUS
      have hm := Submodule.finrank_mono hSV
      have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
      omega
    have haS : a∈S.dualCoannihilator := by
      apply (Submodule.mem_dualCoannihilator a).mpr
      have hle : S≤LinearMap.ker (Module.Dual.eval K V a) := by
        apply sup_le
        · intro f hf
          exact (Submodule.mem_dualCoannihilator a).mp ha f hf
        · rw [Submodule.span_singleton_le_iff_mem]; exact hay
      intro f hf
      exact hle hf
    refine ⟨⟨?_,horth hb⟩,?_,hy⟩
    · rwa [hS] at haS
    · apply (Submodule.mem_dualCoannihilator c).mpr
      intro f hf
      exact (Submodule.mem_dualAnnihilator f).mp hf c hc
end

open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}

theorem rectangle_charge_count (U W : Fin n → Submodule K (Module.Dual K V))
    (x : Fin n → V × Module.Dual K V) (M : ℝ)
    (hocc : ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (x i).1 (x i).2 then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,if RectangleCharge U W x i j then (1:ℝ) else 0)≤2*n*M := by
  have ht (i j : Fin n) : (if RectangleCharge U W x i j then (1:ℝ) else 0)≤
      (if InRectangle (U i) (x j).1 (x j).2 then 1 else 0)+
      (if InRectangle (W j) (x i).1 (x i).2 then 1 else 0) := by
    by_cases h : RectangleCharge U W x i j
    · simp only [h,ite_true]
      rcases h.2 with h|h
      · simp only [h.2,ite_true]; split_ifs <;> norm_num
      · simp only [h.1,ite_true]; split_ifs <;> norm_num
    · simp only [h,ite_false]; split_ifs <;> norm_num
  calc
    _ ≤ ∑ i,∑ j,((if InRectangle (U i) (x j).1 (x j).2 then (1:ℝ) else 0)+
        (if InRectangle (W j) (x i).1 (x i).2 then 1 else 0)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = (∑ i,∑ j,if InRectangle (U i) (x j).1 (x j).2 then (1:ℝ) else 0)+
        ∑ j,∑ i,if InRectangle (W j) (x i).1 (x i).2 then 1 else 0 := by
      simp only [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    _ ≤ (∑ _i : Fin n,M)+(∑ _j : Fin n,M) := add_le_add
      (Finset.sum_le_sum fun i _ => hocc (U i)) (Finset.sum_le_sum fun j _ => hocc (W j))
    _ = _ := by simp; ring

theorem expected_rectangle_charge {Ω : Type*} [Fintype Ω] (p : Law Ω)
    (U W : Ω → Fin n → Submodule K (Module.Dual K V))
    (x : Ω → Fin n → V × Module.Dual K V) (M : ℝ)
    (hocc : ∀ ω,0<p ω → ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (x ω i).1 (x ω i).2 then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,∑ ω,p ω*(if RectangleCharge (U ω) (W ω) (x ω) i j then (1:ℝ) else 0))≤
      2*n*M := by
  have ht (ω : Ω) : p ω*(∑ i,∑ j,if RectangleCharge (U ω) (W ω) (x ω) i j then (1:ℝ) else 0)≤
      p ω*(2*n*M) := by
    by_cases hp : p ω=0
    · simp only [hp,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (rectangle_charge_count _ _ _ M
        (hocc ω (lt_of_le_of_ne (p.nonneg ω) (Ne.symm hp)))) (p.nonneg ω)
  calc
    _ = ∑ ω,p ω*(∑ i,∑ j,if RectangleCharge (U ω) (W ω) (x ω) i j then (1:ℝ) else 0) := by
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset Ω))]
    _ ≤ ∑ ω,p ω*(2*n*M) := Finset.sum_le_sum fun ω _ => ht ω
    _ = _ := by rw [←Finset.sum_mul,p.sum_one,one_mul]
end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Swap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mass_eq_second_mul_fiber (p : Law (α × β)) (a : α) (b : β) :
    p (a,b)=second p b*fiber (swap p) b a := by
  simpa only [first_swap,swap_mass] using mass_eq_first_mul_fiber (swap p) b a

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReverseMiss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

omit [FiniteDimensional K V] in
lemma reverseMiss_eq (p : Law β) (q : Law γ)
    (v : β → Module.Dual K V) (w : γ → V) :
    reverseMiss p q v w = ∑ c,q c*failure p v (Module.Dual.eval K V (w c)) := by
  rw [reverseMiss,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [CoreGeometry.failure,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (if v b (w c)≠0 then _ else _) = q c*(if v b (w c)≠0 then _ else _)
  split_ifs <;> simp [mul_comm]

omit [FiniteDimensional K V] in
lemma captured_orthogonal (p : Law (α × β)) (q : Law (γ × δ))
    (v : β → Module.Dual K V) (w : γ → V) (good : α → δ → Prop)
    (a : α) (b : β) (c : γ) (y : δ) (h : capturedEvent p q v w good a b c y) :
    core (K := K) (fiber p a) v (1/200) ≤
      (core (K := K) (fiber (swap q) y) w (1/200)).dualAnnihilator := by
  intro f hf
  apply (Submodule.mem_dualAnnihilator f).mpr
  intro z hz
  apply core_orthogonal (fiber p a) v (fiber (swap q) y) w (1/200) (by norm_num) _ f hf z hz
  rw [←reverseMiss_eq]
  convert h.2.1 using 1; norm_num

end SharpRamseyFive.LowConflict

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Cores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.LowConflict
open scoped BigOperators Classical
noncomputable section
variable {K V α β : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype α] [Fintype β]

lemma conditional_flag_annihilation (p : Law (α × β)) (v : α → V)
    (w : β → Module.Dual K V) (hflag : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (a : α) (ha : 0<first p a) :
    failure (fiber p a) w (Module.Dual.eval K V (v a)) = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  change (if w b (v a) ≠ 0 then fiber p a b else 0)=0
  split_ifs with h
  · by_contra hz
    have hp : 0 < p (a,b) := by
      rw [mass_eq_first_mul_fiber]
      exact mul_pos ha (lt_of_le_of_ne ((fiber p a).nonneg b) (Ne.symm hz))
    exact h (hflag a b hp)
  · rfl

lemma firstCore_self (p : Law (α × β)) (v : α → V)
    (w : β → Module.Dual K V) (hflag : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (a : α) (ha : 0<first p a) : v a ∈ (firstCore p w a).dualCoannihilator := by
  apply (Submodule.mem_dualCoannihilator _).mpr
  intro f hf
  exact (mem_core _ _ _ f).mp hf (Module.Dual.eval K V (v a))
    (by rw [conditional_flag_annihilation p v w hflag a ha]; norm_num)

lemma secondCore_self (p : Law (α × β)) (v : α → V)
    (w : β → Module.Dual K V) (hflag : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (b : β) (hb : 0 < second p b) : w b ∈ (secondCore (K := K) p v b).dualAnnihilator := by
  have hz : failure (fiber (swap p) b) v (w b)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    change (if w b (v a)≠0 then fiber (swap p) b a else 0)=0
    split_ifs with h
    · by_contra hn
      have hp : 0 < p (a,b) := by
        rw [mass_eq_second_mul_fiber]
        exact mul_pos hb (lt_of_le_of_ne ((fiber (swap p) b).nonneg a) (Ne.symm hn))
      exact h (hflag a b hp)
    · rfl
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro z hz'
  exact (mem_core _ _ _ z).mp hz' (w b) (by rw [hz]; norm_num)

variable [FiniteDimensional K V]

theorem actual_high_rectangles (hdim : finrank K V=5)
    (p q : Law (α × β)) (v : α → V) (w : β → Module.Dual K V)
    (hp : ∀ a b, 0<p (a,b) → w b (v a)=0)
    (hq : ∀ a b, 0<q (a,b) → w b (v a)=0)
    (good : α → β → Prop)
    (hg : ∀ a y, good a y → 0<first p a ∧ 0 < second q y ∧ w y (v a)=0)
    (hU : ∀ a y, good a y → 2 ≤ finrank K (firstCore p w a))
    (hW : ∀ a y, good a y → 2 ≤ finrank K (secondCore (K := K) q v y))
    (a c : α) (b y : β) (h : capturedEvent p q w v good a b c y) :
    (InRectangle (firstCore p w a) (v a) (w b) ∧
      InRectangle (firstCore p w a) (v c) (w y)) ∨
    (InRectangle (secondCore (K := K) q v y).dualAnnihilator (v a) (w b) ∧
      InRectangle (secondCore (K := K) q v y).dualAnnihilator (v c) (w y)) := by
  exact high_band_rectangles hdim _ _ (hU a y h.1) (hW a y h.1)
    (captured_orthogonal p q w v good a b c y h) _ _ _ _
    (firstCore_self p v w hp a (hg a y h.1).1) h.2.2.1 h.2.2.2
    (secondCore_self q v w hq y (hg a y h.1).2.1) (hg a y h.1).2.2

end
end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GoodCoreRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem goodFirst_core_rank (hdim : finrank K V=5)
    (p : Law (ℙ K V × ℙ K (Module.Dual K V))) (A s : ℝ)
    (hA : 0 < A) (hs : 2 ≤ s) (a : ℙ K V)
    (ha : a∈goodFirstEndpoints p A ((Nat.card K:ℝ)^4) s) :
    ⌈5-(Real.log A+3*s)/Real.log (Nat.card K)⌉₊ ≤
      finrank K (firstCore p Projectivization.rep a) := by
  have hq : 0 < (Nat.card K : ℝ) := by
    exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  apply core_dimension_lower (by rw [Subspace.dual_finrank_eq,hdim])
    (fiber p a) A s hA hs (heavyRow p ((Nat.card K:ℝ)^4) s a)
  · intro b hb
    exact goodFirst_conditional_cap p A _ s hA (pow_pos hq 4) a ha b hb
  · exact (Finset.mem_filter.mp ha).2.2

theorem goodSecond_core_rank (hdim : finrank K V=5)
    (p : Law (ℙ K V × ℙ K (Module.Dual K V))) (B s : ℝ)
    (hB : 0 < B) (hs : 2 ≤ s) (b : ℙ K (Module.Dual K V))
    (hb : b∈goodFirstEndpoints (swap p) B ((Nat.card K:ℝ)^4) s) :
    ⌈5-(Real.log B+3*s)/Real.log (Nat.card K)⌉₊ ≤
      finrank K (secondCore (K := K) p Projectivization.rep b) := by
  have hq : 0 < (Nat.card K : ℝ) := by
    exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  apply core_dimension_lower hdim (fiber (swap p) b) B s hB hs
    (heavyRow (swap p) ((Nat.card K:ℝ)^4) s b)
  · intro a ha
    exact goodFirst_conditional_cap (swap p) B _ s hB (pow_pos hq 4) b hb a ha
  · exact (Finset.mem_filter.mp hb).2.2
end
end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BandCoreRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical
noncomputable section

lemma rank_of_logarithmic_slack {q A s : ℝ} {r n : ℕ}
    (hq : 1<q) (hslack : Real.log A+3*s < (6-(r:ℝ))*Real.log q)
    (hcore : ⌈5-(Real.log A+3*s)/Real.log q⌉₊ ≤ n) : r≤n := by
  have hl : 0<Real.log q := Real.log_pos hq
  have hd : (r:ℝ)-1 < 5-(Real.log A+3*s)/Real.log q := by
    have := (div_lt_iff₀ hl).mpr hslack
    linarith
  have hn : 5-(Real.log A+3*s)/Real.log q ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcore)
  by_contra h
  have hnr : n+1 ≤ r := by omega
  have hnr' : (n:ℝ)+1≤(r:ℝ) := by exact_mod_cast hnr
  linarith

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem goodFirst_integer_rank (hdim : finrank K V=5)
    (p : Law (ℙ K V × ℙ K (Module.Dual K V))) (A s : ℝ)
    (hA : 0<A) (hs : 2 ≤ s) (r : ℕ)
    (hcap : Real.log A+3*s < (6-(r:ℝ))*Real.log (Nat.card K))
    (a : ℙ K V) (ha : a∈goodFirstEndpoints p A ((Nat.card K:ℝ)^4) s) :
    r ≤ finrank K (firstCore p Projectivization.rep a) := by
  apply rank_of_logarithmic_slack (by exact_mod_cast (Finite.one_lt_card (α := K))) hcap
  exact goodFirst_core_rank hdim p A s hA hs a ha

theorem goodSecond_integer_rank (hdim : finrank K V=5)
    (p : Law (ℙ K V × ℙ K (Module.Dual K V))) (B s : ℝ)
    (hB : 0<B) (hs : 2 ≤ s) (r : ℕ)
    (hcap : Real.log B+3*s < (6-(r:ℝ))*Real.log (Nat.card K))
    (b : ℙ K (Module.Dual K V))
    (hb : b∈goodFirstEndpoints (swap p) B ((Nat.card K:ℝ)^4) s) :
    r ≤ finrank K (secondCore (K := K) p Projectivization.rep b) := by
  apply rank_of_logarithmic_slack (by exact_mod_cast (Finite.one_lt_card (α := K))) hcap
  exact goodSecond_core_rank hdim p B s hB hs b hb
end
end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RevealDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι β : Type*} [Fintype ι] [Fintype β]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEq_solutions
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSubtypeMemFinset_solutions_2
lemma fiber_reveal_agrees (p : Law (ι → β)) (E : Finset ι) (a : E → β)
    (ha : 0 < first (reveal p E) a) (x : ι → β)
    (hx : 0 < fiber (reveal p E) a x) : (fun i : E => x i.val) = a := by
  apply (reveal_positive p E a x _).2
  rw [mass_eq_first_mul_fiber]
  exact mul_pos ha hx

lemma InDomains.fiber {p : Law (ι → β)} {D : ι → Finset β} (h : InDomains p D)
    (E : Finset ι) (a : E → β) : InDomains (fiber (reveal p E) a) D := by
  intro x hx i
  exact h x (fiber_reveal_support p E a x hx) i

lemma FixedOutside.fiber {p : Law (ι → β)} {U : Finset ι} (h : FixedOutside p U)
    (E : Finset ι) (a : E → β) (ha : 0 < first (reveal p E) a) :
    FixedOutside (fiber (reveal p E) a) (U \ E) := by
  intro i hi
  by_cases he : i ∈ E
  · refine ⟨a ⟨i,he⟩,fun x hx => ?_⟩
    exact congrFun (fiber_reveal_agrees p E a ha x hx) ⟨i,he⟩
  · have hu : i ∉ U := fun hu => hi (Finset.mem_sdiff.mpr ⟨hu,he⟩)
    obtain ⟨b,hb⟩ := h i hu
    exact ⟨b,fun x hx => hb x (fiber_reveal_support p E a x hx)⟩

lemma marginalDeficit_le_active {p : Law (ι → β)} {U : Finset ι}
    (h : FixedOutside p U) (J : ℝ) : marginalDeficit p U J ≤ activeDeficit p U J := by
  have hh := h.entropy_le_sum
  simp only [marginalDeficit, activeDeficit, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

lemma activeDeficit_reveal (p : Law (ι → β)) (U E : Finset ι) (hEU : E ⊆ U)
    (J : ℝ) (hc : ∀ i ∈ E, entropy (map p (fun x => x i)) ≤ J) :
    mean (first (reveal p E)) (fun a => activeDeficit (fiber (reveal p E) a) (U \ E) J) ≤
      activeDeficit p U J := by
  have hcap : entropy (first (reveal p E)) ≤ (E.card : ℝ) * J := by
    apply (entropy_reveal_le_coordinate_sum p E).trans
    calc
      _ ≤ ∑ _i ∈ E,J := Finset.sum_le_sum hc
      _ = _ := by simp
  have hh := conditional_deficit_le (reveal p E) ((E.card : ℝ)*J) (((U \ E).card : ℝ)*J) hcap
  rw [entropy_reveal] at hh
  have hcard : ((E.card : ℝ) + (U \ E).card) = U.card := by
    simpa only [add_comm] using (show ((U \ E).card : ℝ) + E.card = U.card by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hEU)
  simpa only [activeDeficit, mean, ←add_mul, hcard] using hh
end

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.instDecidableEqSumProd_solutions_3
local instance instDecidableEqSubtypeSumProdMemFinset_solutions_3_r11b48c_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
omit [Nonempty A] in
lemma mem_blockActive_left (S : B → Finset A) (b : B) (a : A) :
    Sum.inl (b,a) ∈ blockActive (T := T) S ↔ a ∈ S b := by simp [blockActive]
omit [Nonempty A] in
lemma mem_blockActive_right (S : B → Finset A) (t : T) :
    Sum.inr t ∈ blockActive S := by simp [blockActive]

lemma freshBlockLaw_supported (S : B → Finset A) (hS : ∀ b, (S b).Nonempty)
    (s : B → A) (hs : 0 < freshBlockLaw S s) : ∀ b, s b ∈ S b := by
  intro b
  by_contra h
  rw [freshBlockLaw_eq S hS,piLaw_uniformOn_zero S hS s h] at hs
  exact lt_irrefl _ hs

omit [Nonempty A] in
lemma representativeSet_subset_active (S : B → Finset A) (s : B → A)
    (hs : ∀ b, s b ∈ S b) : representativeSet (T := T) s ⊆ blockActive S := by
  intro i hi
  simp only [representativeSet, Finset.mem_image, Finset.mem_univ, true_and] at hi
  obtain ⟨b,rfl⟩ := hi
  exact (mem_blockActive_left S b (s b)).mpr (hs b)

omit [Nonempty A] in
lemma blockActive_erase (S : B → Finset A) (s : B → A) :
    blockActive (T := T) (eraseBlock S s) = blockActive S \ representativeSet s := by
  ext i
  cases i with
  | inl x => rcases x with ⟨b,a⟩; simp [blockActive,eraseBlock,representativeSet, and_comm, eq_comm]
  | inr t => simp [blockActive,representativeSet]

theorem block_round_deficit (J : ℝ) (D : ((B × A) ⊕ T) → Finset β)
    (hJ : ∀ i, Real.log (D i).card ≤ J)
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (hp : InDomains p D) (hfix : FixedOutside p (blockActive S))
    (n : ℕ) (hS : ∀ b, n ≤ (S b).card) (i : Fin n) :
    blockRoundMean (blockAllDeficit J) p S n i ≤ activeDeficit p (blockActive S) J := by
  induction n generalizing p S with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hn : ∀ b, (S b).Nonempty := fun b => Finset.card_pos.mp (by have := hS b; omega)
    cases i using Fin.cases with
    | zero =>
      change mean (freshBlockLaw S) (fun _ => marginalDeficit p (blockActive S) J) ≤ _
      rw [mean_const]
      exact marginalDeficit_le_active hfix J
    | succ i =>
      change mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
        (fun a => blockRoundMean (blockAllDeficit J) (fiber (reveal p (representativeSet s)) a)
          (eraseBlock S s) n i)) ≤ _
      apply le_trans (mean_mono_pos (freshBlockLaw S) (fun s hs => ?_))
        (mean_const (freshBlockLaw S) (activeDeficit p (blockActive S) J)).le
      have he : representativeSet (T := T) s ⊆ blockActive S :=
        representativeSet_subset_active S s (freshBlockLaw_supported S hn s hs)
      calc
        _ ≤ mean (first (reveal p (representativeSet s)))
          (fun a => activeDeficit (fiber (reveal p (representativeSet s)) a)
            (blockActive (eraseBlock S s)) J) := by
            apply mean_mono_pos
            intro a ha
            apply ih _ _ (hp.fiber _ _)
            · rw [blockActive_erase]
              exact hfix.fiber _ _ ha
            · exact eraseBlock_card S s n hS
        _ ≤ activeDeficit p (blockActive S) J := by
          rw [blockActive_erase]
          exact activeDeficit_reveal p (blockActive S) (representativeSet s) he J
            (fun j _ => hp.entropy_cap J hJ j)

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CollisionSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T : Type} [Fintype B] [Fintype A] [Fintype T] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.collisionSamplingDecEq
lemma fresh_row_collision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (hc : ∀ i j,0 ≤ c i j) (S : B → Finset A) (r : ℕ) (hr : 0 < r)
    (hS : ∀ b,r≤(S b).card) (i : ((B × A) ⊕ T)) :
    r * mean (freshBlockLaw S) (fun s => ∑ b,c i (Sum.inl (b,s b))) ≤
      ∑ j∈blockActive S,c i j := by
  have hn : ∀ b,(S b).Nonempty := fun b => Finset.card_pos.mp (hr.trans_le (hS b))
  rw [freshBlockLaw_eq S hn,mean_sum,Finset.mul_sum]
  have hb (b : B) : (r:ℝ)*mean (piLaw fun d => uniformOn (S d) (hn d))
      (fun s => c i (Sum.inl (b,s b))) ≤ ∑ a∈S b,c i (Sum.inl (b,a)) := by
    have he : mean (piLaw fun d => uniformOn (S d) (hn d))
        (fun s => c i (Sum.inl (b,s b))) =
        ((S b).card:ℝ)⁻¹ * ∑ a∈S b,c i (Sum.inl (b,a)) := by
      change (∑ s,piLaw (fun d => uniformOn (S d) (hn d)) s *
        (fun a => c i (Sum.inl (b,a))) (s b)) = _
      rw [piLaw_eval_expectation (fun d => uniformOn (S d) (hn d)) b
        (fun a => c i (Sum.inl (b,a))),uniformOn_expectation]
    have hnn := mean_nonneg (piLaw fun d=>uniformOn (S d) (hn d))
      (fun s=>c i (Sum.inl (b,s b))) (fun s=>hc _ _)
    have hcp : ((S b).card:ℝ)≠0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hn b))
    calc
      _ ≤ (S b).card*mean (piLaw fun d=>uniformOn (S d) (hn d))
          (fun s=>c i (Sum.inl (b,s b))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hS b) hnn
      _ = _ := by rw [he]; field_simp
  apply (Finset.sum_le_sum fun b _=>hb b).trans
  have he : (∑ j∈blockActive S,c i j)=
      (∑ b,∑ a∈S b,c i (Sum.inl (b,a)))+∑ t,c i (Sum.inr t) := by
    calc
      _ = ∑ j,if j∈blockActive S then c i j else 0 := by
        rw [Finset.sum_ite_mem,Finset.univ_inter]
      _ = _ := by
        rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
        simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
          Finset.sum_ite_mem,Finset.univ_inter]
  rw [he]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun t _=>hc _ _)

theorem fresh_all_collision_bound (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (hc : ∀ i j,0 ≤ c i j) (S : B → Finset A) (r : ℕ) (hr : 0 < r)
    (hS : ∀ b,r≤(S b).card) :
    r * mean (freshBlockLaw S) (allCollision c S) ≤
      ∑ i∈blockActive S,∑ j∈blockActive S,c i j := by
  have hpoint (s : B → A) : allCollision c S s ≤
      ∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b)) := by
    have he : (∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b)))=
        (∑ b,∑ a∈S b,∑ d,c (Sum.inl (b,a)) (Sum.inl (d,s d)))+
        ∑ t,middleCollision c s t := by
      calc
        _ = ∑ i,if i∈blockActive S then ∑ b,c i (Sum.inl (b,s b)) else 0 := by
          rw [Finset.sum_ite_mem,Finset.univ_inter]
        _ = _ := by
          rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
          simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
            Finset.sum_ite_mem,Finset.univ_inter,middleCollision]
    rw [he]
    change _ + _ ≤ _ + _
    apply add_le_add _ le_rfl
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun d _ _=>hc _ _)
  calc
    _ ≤ r * mean (freshBlockLaw S)
        (fun s=>∑ i∈blockActive S,∑ b,c i (Sum.inl (b,s b))) :=
      mul_le_mul_of_nonneg_left (mean_mono _ hpoint) (Nat.cast_nonneg _)
    _ = ∑ i∈blockActive S,r * mean (freshBlockLaw S)
        (fun s=>∑ b,c i (Sum.inl (b,s b))) := by rw [mean_finset_sum,Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ => fresh_row_collision c hc S r hr hS i

end

open scoped Classical BigOperators

lemma badIndexIndicator_le {δ g d e : ℝ} (hδ : 0≤δ) (hg : 0≤g)
    (hd : 0<d) (he : 0<e) : badIndexIndicator δ g d e≤δ/d+g/e := by
  unfold badIndexIndicator
  split_ifs with h
  · rcases h with h|h
    · have hh : 1≤δ/d := (le_div_iff₀ hd).mpr (by linarith)
      exact hh.trans (le_add_of_nonneg_right (div_nonneg hg he.le))
    · have hh : 1≤g/e := (le_div_iff₀ he).mpr (by linarith)
      exact hh.trans (le_add_of_nonneg_left (div_nonneg hδ hd.le))
  · positivity

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.goodDeleteIndexDecEq
omit [Nonempty A] in
lemma blockActive_sum (S : B→Finset A) (f : ((B×A)⊕T)→ℝ) :
    (∑ i∈blockActive S,f i)=(∑ b,∑ a∈S b,f (Sum.inl (b,a)))+∑ t,f (Sum.inr t) := by
  calc
    _ = ∑ i,if i∈blockActive S then f i else 0 := by
      simp only [Finset.sum_ite_mem,Finset.univ_inter]
    _ = _ := by
      rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
      simp only [mem_blockActive_left,mem_blockActive_right,ite_true,
        Finset.sum_ite_mem,Finset.univ_inter]

lemma mean_div {X : Type*} [Fintype X] (p : Law X) (f : X→ℝ) (d : ℝ) :
    mean p (fun x=>f x/d)=mean p f/d := by
  simp only [mean,mul_div_assoc,Finset.sum_div]

omit [Nonempty A] in
lemma indexInformation_sum (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexInformation p s i)=blockAllInformation p S s := by
  rw [blockActive_sum]
  rfl

omit [Nonempty A] in
lemma indexCollision_sum (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexCollision c s i)=allCollision c S s := by
  rw [blockActive_sum]
  rfl

omit [Nonempty A] in
lemma indexBad_sum (J d e : ℝ) (hd : 0<d) (he : 0<e)
    (p : Law (((B×A)⊕T)→β)) (hJ : ∀ i,entropy (map p (fun x=>x i))≤J)
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0 ≤ c i j)
    (S : B→Finset A) (s : B→A) :
    (∑ i∈blockActive S,indexBad J d e p c s i)≤
      blockAllDeficit J p S s/d+(blockAllInformation p S s+allCollision c S s)/e := by
  have hscore (i : ((B×A)⊕T)) : 0 ≤ indexInformation p s i+indexCollision c s i := by
    cases i with
    | inl z => exact add_nonneg (NNReal.coe_nonneg _) (Finset.sum_nonneg fun _ _=>hc _ _)
    | inr t => exact add_nonneg (NNReal.coe_nonneg _) (Finset.sum_nonneg fun _ _=>hc _ _)
  calc
    _ ≤ ∑ i∈blockActive S,((J-entropy (map p (fun x=>x i)))/d+
        (indexInformation p s i+indexCollision c s i)/e) :=
      Finset.sum_le_sum fun i _=>badIndexIndicator_le (sub_nonneg.mpr (hJ i)) (hscore i) hd he
    _ = _ := by
      rw [Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_div,Finset.sum_add_distrib,
        indexInformation_sum,indexCollision_sum]
      rfl

theorem fresh_bad_bound (J d e : ℝ) (hd : 0<d) (he : 0<e)
    (p : Law (((B×A)⊕T)→β)) (hJ : ∀ i,entropy (map p (fun x=>x i))≤J)
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0 ≤ c i j)
    (S : B→Finset A) (r : ℕ) (hr : 0 < r) (hS : ∀ b,r≤(S b).card) :
    mean (freshBlockLaw S) (fun s=>∑ i∈blockActive S,indexBad J d e p c s i)≤
      mean (freshBlockLaw S) (blockAllDeficit J p S)/d+
      (mean (freshBlockLaw S) (blockAllInformation p S)+
        (∑ i∈blockActive S,∑ j∈blockActive S,c i j)/r)/e := by
  have hb:=mean_mono (freshBlockLaw S) (indexBad_sum J d e hd he p hJ c hc S)
  simp_rw [mean_add,mean_div] at hb
  apply hb.trans
  rw [mean_add]
  gcongr
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  apply (le_div_iff₀ hr').mpr
  simpa only [mul_comm] using fresh_all_collision_bound c hc S r hr hS

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FiniteKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.blockHistIndexDecEq
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.blockHistSubtypeDecEq
theorem history_round_mean
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ)
    (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n : ℕ) :
    blockRoundMean J p S (n+1) (Fin.last n)=
      mean (historyLaw p S n) (fun h=>mean (freshBlockLaw (historyUnused S h))
        (J (historyPosterior p h) (historyUnused S h))) := by
  induction n generalizing p S with
  | zero =>
    change mean (freshBlockLaw S) (J p S)=mean (uniformType Unit) (fun _=>mean (freshBlockLaw S) (J p S))
    exact (mean_const _ _).symm
  | succ n ih =>
    change mean (freshBlockLaw S) (fun s=>mean (first (reveal p (representativeSet s)))
      (fun a=>blockRoundMean J (fiber (reveal p (representativeSet s)) a)
        (eraseBlock S s) (n+1) (Fin.last n)))=_
    simp_rw [ih]
    change _=mean (sigmaLaw (freshBlockLaw S) fun s=>
      adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n)
      (fun h => mean (freshBlockLaw (historyUnused (eraseBlock S h.1) h.2.2))
        (J (historyPosterior (fiber (reveal p (representativeSet h.1)) h.2.1) h.2.2)
          (historyUnused (eraseBlock S h.1) h.2.2)))
    rw [mean_sigma]
    apply mean_congr
    intro s
    rw [mean_adaptive]

lemma blockRoundMean_total_irrel
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ)
    (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) (n m : ℕ)
    (i : Fin n) (j : Fin m) (hij : i.val=j.val) :
    blockRoundMean J p S n i=blockRoundMean J p S m j := by
  induction n generalizing p S m with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases m with
    | zero => exact Fin.elim0 j
    | succ m =>
      cases i using Fin.cases with
      | zero =>
        have hj : j=0 := Fin.ext (by simpa using hij.symm)
        subst j
        rfl
      | succ i =>
        have hj : j≠0 := by intro hz;subst j;simp at hij
        obtain ⟨j,rfl⟩:=Fin.exists_succ_eq.mpr hj
        simp only [blockRoundMean,Fin.cases_succ]
        apply mean_congr
        intro s
        apply mean_congr
        intro a
        apply ih _ _ _ i j
        simpa using hij

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_Collisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.LowConflict
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped BigOperators Classical
noncomputable section
variable {K V α β : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype α] [Fintype β] {n : ℕ}

omit [FiniteDimensional K V] in
lemma tuple_flag_marginal (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V)
    (hp : ∀ x,0<p x → ∀ i,w (x i).2 (v (x i).1)=0)
    (i : Fin n) (a : α) (b : β) (h : 0<tupleMarginal p i (a,b)) : w b (v a)=0 := by
  obtain ⟨x,hx,hxi⟩ := map_positive p (fun x => x i) (a,b) h
  simpa only [hxi] using hp x hx i

omit [FiniteDimensional K V] in
lemma tuple_collision_count (p : Law (Fin n → α × β)) (v : α → V)
    (w : β → Module.Dual K V) (good : Fin n → Fin n → α → β → Prop) (M : ℝ)
    (hc : ∀ x,0<p x → ∀ i j,tupleCapture p v w good i j x →
      RectangleCharge
        (fun t => firstCore (tupleMarginal p t) w (x t).1)
        (fun t => (secondCore (K := K) (tupleMarginal p t) v (x t).2).dualAnnihilator)
        (fun t => (v (x t).1,w (x t).2)) i j)
    (hocc : ∀ x,0<p x → ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (v (x i).1) (w (x i).2) then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,tupleCollision p v w good i j)≤2*n*M := by
  apply le_trans _ (expected_rectangle_charge p
    (fun x t => firstCore (tupleMarginal p t) w (x t).1)
    (fun x t => (secondCore (K := K) (tupleMarginal p t) v (x t).2).dualAnnihilator)
    (fun x t => (v (x t).1,w (x t).2)) M hocc)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : p x=0
  · simp [hp]
  · have hp' : 0<p x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hp)
    by_cases ht : tupleCapture p v w good i j x
    · simp only [ht,ite_true,hc x hp' i j ht,mul_one,le_refl]
    · simp only [ht,ite_false]
      exact mul_nonneg (p.nonneg x) (by split_ifs <;> norm_num)

theorem high_tuple_collision_bound (hdim : finrank K V=5)
    (p : Law (Fin n → α × β)) (v : α → V) (w : β → Module.Dual K V)
    (good : Fin n → Fin n → α → β → Prop) (M : ℝ)
    (hp : ∀ x,0<p x → ∀ i,w (x i).2 (v (x i).1)=0)
    (hg : ∀ i j a y,good i j a y →
      0<first (tupleMarginal p i) a ∧ 0 < second (tupleMarginal p j) y ∧ w y (v a)=0)
    (hU : ∀ i j a y, good i j a y → 2 ≤ finrank K (firstCore (tupleMarginal p i) w a))
    (hW : ∀ i j a y, good i j a y →
      2 ≤ finrank K (secondCore (K := K) (tupleMarginal p j) v y))
    (hocc : ∀ x,0<p x → ∀ S : Submodule K (Module.Dual K V),
      (∑ i,if InRectangle S (v (x i).1) (w (x i).2) then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,tupleCollision p v w good i j)≤2*n*M := by
  apply tuple_collision_count p v w good M ?_ hocc
  intro x hx i j ht
  refine ⟨ht.1,?_⟩
  exact actual_high_rectangles hdim _ _ v w
    (tuple_flag_marginal p v w hp i) (tuple_flag_marginal p v w hp j)
    (good i j) (hg i j) (hU i j) (hW i j) _ _ _ _ ht.2

end
end SharpRamseyFive.LowConflict

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedReciprocalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {I β : Type} [Fintype I] [Fintype β] {n : ℕ}

lemma orderedLaw_positive (p : Law (I→β)) (e : I≃Fin n)
    (x : Fin n→β) (hx : 0<orderedLaw p e x) :
    ∃ y,0<p y ∧ ∀ i,x (e i)=y i := by
  obtain ⟨y,hy,rfl⟩:=map_positive p (fun x i=>x (e.symm i)) x hx
  exact ⟨y,hy,fun i=>by simp only [Equiv.symm_apply_apply]⟩
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.uniformHistoryIndexDecEq
local instance uniformHistorySubtypeDecEq_r11b48c_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
theorem exists_uniform_pre_round (μ : Law κ)
    (p : κ→Law (((B×A)⊕T)→β)) (S : κ→B→Finset A)
    (n : ℕ) (hn : 0<n) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    ∃ i : Fin n, mean μ (fun c=>blockRoundMean blockAllInformation (p c) (S c) n i)≤
      2*mean μ (fun c=>totalCorrelation (p c))/n := by
  have hb : (∑ i : Fin n,mean μ (fun c=>blockRoundMean blockAllInformation (p c) (S c) n i))≤
      2*mean μ (fun c=>totalCorrelation (p c)) := by
    rw [←mean_sum,←mean_smul]
    exact mean_mono_pos μ (fun c hc=>block_information_telescope (p c) (S c) n (hS c hc))
  by_contra! hh
  have hs := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hn⟩⟩) (fun i _=>hh i)
  have he : (∑ _i : Fin n,2*mean μ (fun c=>totalCorrelation (p c))/n)=
      2*mean μ (fun c=>totalCorrelation (p c)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  rw [he] at hs
  exact (not_lt_of_ge hb) hs

lemma preRound_mean (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ)
    (J : Law (((B×A)⊕T)→β)→(B→Finset A)→(B→A)→ℝ) :
    mean (preRoundLaw μ p S n) (fun z=>J (historyPosterior (p z.1.1) z.1.2)
      (historyUnused (S z.1.1) z.1.2) z.2)=
      mean μ (fun c=>blockRoundMean J (p c) (S c) (n+1) (Fin.last n)) := by
  rw [preRoundLaw,mean_adaptive,mean_adaptive]
  apply mean_congr
  intro c
  exact (history_round_mean J (p c) (S c) n).symm

theorem exists_preRoundLaw_information (μ : Law κ)
    (p : κ→Law (((B×A)⊕T)→β)) (S : κ→B→Finset A)
    (n : ℕ) (hn : 0<n) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    ∃ i : Fin n, mean (preRoundLaw μ p S i.val)
      (fun z=>blockAllInformation (historyPosterior (p z.1.1) z.1.2)
        (historyUnused (S z.1.1) z.1.2) z.2)≤
      2*mean μ (fun c=>totalCorrelation (p c))/n := by
  obtain ⟨i,hi⟩:=exists_uniform_pre_round μ p S n hn hS
  refine ⟨i,?_⟩
  rw [preRound_mean]
  have he (c : κ) := blockRoundMean_total_irrel blockAllInformation (p c) (S c)
    (i.val+1) n (Fin.last i.val) i rfl
  simp_rw [he]
  exact hi

lemma preRoundLaw_deficit (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (J : ℝ) (D : κ→((B×A)⊕T)→Finset β)
    (hJ : ∀ c x,Real.log (D c x).card≤J) (hp : ∀ c,0<μ c→InDomains (p c) (D c))
    (hfix : ∀ c,0<μ c→FixedOutside (p c) (blockActive (S c)))
    (n : ℕ) (hS : ∀ c,0<μ c→∀ b,n+1≤(S c b).card) :
    mean (preRoundLaw μ p S n) (fun z=>blockAllDeficit J
      (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)≤
      mean μ (fun c=>activeDeficit (p c) (blockActive (S c)) J) := by
  rw [preRound_mean]
  exact mean_mono_pos μ (fun c hc=>block_round_deficit J (D c) (hJ c)
    (p c) (S c) (hp c hc) (hfix c hc) (n+1) (hS c hc) (Fin.last n))

end

open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.historyProducerIndexDecEq
local instance historyProducerSubtypeDecEq_r11b48c_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
omit [Fintype β] [Nonempty A] in
lemma history_unused_card (S : B→Finset A) (r n : ℕ)
    (hS : ∀ b,r+n≤(S b).card) (h : BlockHistory B A T β n) :
    ∀ b,r≤(historyUnused S h b).card := by
  induction n generalizing S with
  | zero => simpa only [historyUnused,Nat.add_zero] using hS
  | succ n ih =>
    apply ih (eraseBlock S h.1) _ h.2.2
    apply eraseBlock_card S h.1 (r+n)
    intro b
    have := hS b
    omega

omit [Nonempty A] in
lemma history_in_domains (p : Law (((B×A)⊕T)→β)) (D : ((B×A)⊕T)→Finset β)
    (hp : InDomains p D) (n : ℕ) (h : BlockHistory B A T β n) :
    InDomains (historyPosterior p h) D := by
  induction n generalizing p with
  | zero => exact hp
  | succ n ih => exact ih _ (hp.fiber _ _) h.2.2

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PreRoundDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.preRoundDeletionIndexDecEq
theorem preRound_bad_budget (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n r : ℕ) (hr : 0 < r)
    (hS : ∀ c,0<μ c→∀ b,r+n≤(S c b).card)
    (J d e : ℝ) (hd : 0<d) (he : 0<e) (D : κ→((B×A)⊕T)→Finset β)
    (hJ : ∀ c i,Real.log (D c i).card≤J)
    (hp : ∀ c,0<μ c→InDomains (p c) (D c))
    (hfix : ∀ c,0<μ c→FixedOutside (p c) (blockActive (S c)))
    (c : κ→BlockHistory B A T β n→((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (hc : ∀ a h i j,0 ≤ c a h i j) (C : ℝ)
    (hC : ∀ a,0<μ a→∀ h,0<historyLaw (p a) (S a) n h→
      (∑ i∈blockActive (historyUnused (S a) h),
        ∑ j∈blockActive (historyUnused (S a) h),c a h i j)≤C) :
    mean (preRoundLaw μ p S n) (fun z=>∑ i∈blockActive (historyUnused (S z.1.1) z.1.2),
      preRoundBad μ p S n J d e c z i)≤
      mean μ (fun a=>activeDeficit (p a) (blockActive (S a)) J)/d+
      (mean (preRoundLaw μ p S n) (fun z=>blockAllInformation
        (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)+C/r)/e := by
  have hlocal (a : κ) (ha : 0<μ a) (h : BlockHistory B A T β n)
      (hh : 0<historyLaw (p a) (S a) n h) :
      mean (freshBlockLaw (historyUnused (S a) h))
        (fun s=>∑ i∈blockActive (historyUnused (S a) h),
          indexBad J d e (historyPosterior (p a) h) (c a h) s i)≤
        mean (freshBlockLaw (historyUnused (S a) h))
          (blockAllDeficit J (historyPosterior (p a) h) (historyUnused (S a) h))/d+
        (mean (freshBlockLaw (historyUnused (S a) h))
          (blockAllInformation (historyPosterior (p a) h) (historyUnused (S a) h))+C/r)/e := by
    apply (fresh_bad_bound J d e hd he _ ((history_in_domains (p a) (D a) (hp a ha) n h).entropy_cap J (hJ a))
      _ (hc a h) _ r hr (history_unused_card (S a) r n (hS a ha) h)).trans
    gcongr
    exact hC a ha h hh
  have hb := mean_mono_pos μ (fun a ha=>mean_mono_pos (historyLaw (p a) (S a) n)
    (hlocal a ha))
  simp_rw [mean_add,mean_div,mean_add,mean_const] at hb
  have hdef := preRoundLaw_deficit μ p S J D hJ hp hfix n
    (fun a ha b=>by have := hS a ha b; omega)
  unfold preRoundLaw at hdef ⊢
  simp only [mean_adaptive,preRoundBad] at hdef ⊢
  exact hb.trans (by gcongr)

end

open scoped Classical BigOperators
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PreparedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {κ B A T β : Type} [Fintype κ] [Fintype B] [Fintype A] [Fintype T]
  [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.chosenRoundDE
lemma FixedOutside.totalCorrelation_le_active {ι : Type} [Fintype ι]
    (p : Law (ι→β)) (U : Finset ι) (J : ℝ) (hfix : FixedOutside p U)
    (hc : ∀i∈U,entropy (map p (fun x=>x i))≤J) :
    totalCorrelation p≤activeDeficit p U J := by
  unfold totalCorrelation activeDeficit
  apply sub_le_sub_right
  calc
    _ = ∑i∈U,entropy (map p (fun x=>x i)) := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi=>hfix.entropy_zero i hi)
    _ ≤ ∑_i∈U,J := Finset.sum_le_sum hc
    _ = _ := by simp

theorem exists_small_deletion_round (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (rounds rem : ℕ) (hrounds : 0 < rounds) (hrem : 0 < rem)
    (hS : ∀a,0<μ a→∀b,rem+rounds≤(S a b).card)
    (J d ε budget C : ℝ) (hd : 0<d) (hε : 0<ε)
    (D : κ→((B×A)⊕T)→Finset β) (hJ : ∀a i,Real.log (D a i).card≤J)
    (hp : ∀a,0<μ a→InDomains (p a) (D a))
    (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (S a)))
    (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (S a)) J)≤budget)
    (c : (i : Fin rounds)→κ→BlockHistory B A T β i.val→((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (hc : ∀i a h x y,0 ≤ c i a h x y)
    (hC : ∀i a,0<μ a→∀h,0<historyLaw (p a) (S a) i.val h→
      (∑x∈blockActive (historyUnused (S a) h),∑y∈blockActive (historyUnused (S a) h),c i a h x y)≤C) :
    ∃i : Fin rounds,mean (preRoundLaw μ p S i.val) (fun z=>
      ∑j∈blockActive (historyUnused (S z.1.1) z.1.2),preRoundBad μ p S i.val J d ε (c i) z j)≤
      budget/d+(2*budget/rounds+C/rem)/ε := by
  obtain ⟨i,hi⟩:=exists_preRoundLaw_information μ p S rounds hrounds
    (fun a ha b=>by have := hS a ha b;omega)
  refine ⟨i,?_⟩
  have htc : mean μ (fun a=>totalCorrelation (p a))≤budget := by
    apply (mean_mono_pos μ (fun a ha=>FixedOutside.totalCorrelation_le_active (p a) _ J
      (hfix a ha) (fun j _=>(hp a ha).entropy_cap J (hJ a) j))).trans hbudget
  have hi' : mean (preRoundLaw μ p S i.val) (fun z=>blockAllInformation
      (historyPosterior (p z.1.1) z.1.2) (historyUnused (S z.1.1) z.1.2) z.2)≤2*budget/rounds :=
    hi.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htc (by norm_num)) (by positivity))
  have h:=preRound_bad_budget μ p S i.val rem hrem
    (fun a ha b=>by have := hS a ha b;have:=i.isLt;omega) J d ε hd hε D hJ hp hfix
    (c i) (hc i) C (hC i)
  exact h.trans (add_le_add (div_le_div_of_nonneg_right hbudget hd.le)
    (div_le_div_of_nonneg_right (add_le_add hi' le_rfl) hε.le))
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighLowConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {n : ℕ}

omit [Finite K] [FiniteDimensional K V] in
lemma high_collision_nonneg (p : Law (Fin n→FlagPair K V)) (s : ℝ) (i j : Fin n) :
    0≤highCollision p s i j := tupleCollision_nonneg ..

lemma high_three_core_slack (s : ℝ) (hsmall : Real.log 32+3*s<Real.log (Nat.card K)) :
    Real.log (32*(Nat.card K:ℝ)^3)+3*s<(6-(2:ℝ))*Real.log (Nat.card K) := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hq 3)),Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem high_three_collisions (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (s M : ℝ) (hs : 2 ≤ s)
    (hsmall : Real.log 32+3*s<Real.log (Nat.card K))
    (hinc : ∀ x,0<p x→TupleIncident x)
    (hocc : ∀ x,0<p x→∀ S : Submodule K (Dual K V),
      (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,highCollision p s i j)≤2*n*M := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  apply high_tuple_collision_bound hdim p Projectivization.rep Projectivization.rep (highThreeGood p s) M
  · intro x hx i
    exact (incident_iff _ _).mp (hinc x hx i)
  · intro i j a y hg
    obtain ⟨ha,hb,hi⟩:=hg
    have ha':= (Finset.mem_filter.mp (show a∈highGoodFirst _ _ _ _ _ from ha)).1
    have hb':= (Finset.mem_filter.mp (show y∈highGoodFirst _ _ _ _ _ from hb)).1
    refine ⟨goodFirst_positive _ _ _ _ (by positivity) a ha',?_,(incident_iff _ _).mp hi⟩
    simpa only [first_swap] using (goodFirst_positive (swap (tupleMarginal p j)) _ _ _ (by positivity) y hb')
  · intro i j a y hg
    apply goodFirst_integer_rank hdim (tupleMarginal p i) _ s (by positivity) hs 2
      (high_three_core_slack s hsmall) a
    exact (Finset.mem_filter.mp (show a∈highGoodFirst _ _ _ _ _ from hg.1)).1
  · intro i j a y hg
    apply goodSecond_integer_rank hdim (tupleMarginal p j) _ s (by positivity) hs 2
      (high_three_core_slack s hsmall) y
    exact (Finset.mem_filter.mp (show y∈highGoodFirst _ _ _ _ _ from hg.2.1)).1
  · exact hocc

end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_OrderedHighConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {I : Type} [Fintype I] {n : ℕ}
lemma sum_symm_reindex (e : I≃Fin n) (c : Fin n→Fin n→ℝ) :
    (∑ i,∑ j,(c (e i) (e j)+c (e j) (e i)))=2*∑ i,∑ j,c i j := by
  have h1 : (∑ i,∑ j,c (e i) (e j))=∑ i,∑ j,c i j := by
    calc
      _ = ∑ i,∑ j,c (e i) j := Finset.sum_congr rfl (fun i _=>e.sum_comp (c (e i)))
      _ = _ := e.sum_comp (fun i=>∑ j,c i j)
  have h2 : (∑ i,∑ j,c (e j) (e i))=∑ i,∑ j,c i j := by
    rw [Finset.sum_comm]
    exact h1
  simp only [Finset.sum_add_distrib,h1,h2]
  ring
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

omit [Finite K] [FiniteDimensional K V] in
lemma orderedHighCollision_nonneg (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s : ℝ) (i j : I) :
    0≤orderedHighCollision p e s i j := add_nonneg (high_collision_nonneg ..) (high_collision_nonneg ..)

lemma orderedHigh_collision_budget (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (s M : ℝ)
    (hs : 2 ≤ s) (hsmall : Real.log 32+3*s<Real.log (Nat.card K))
    (hinc : ∀ x,0<p x→∀ i,Incident (x i).1 (x i).2)
    (hocc : ∀ x,0<p x→∀ S : Submodule K (Dual K V),
      (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,orderedHighCollision p e s i j)≤4*n*M := by
  have hi : ∀ x,0<orderedLaw p e x→TupleIncident x := by
    intro x hx i
    obtain ⟨y,hy,he⟩:=orderedLaw_positive p e x hx
    simpa only [←he,Equiv.apply_symm_apply] using hinc y hy (e.symm i)
  have ho : ∀ x,0<orderedLaw p e x→∀ S : Submodule K (Dual K V),
      (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M := by
    intro x hx S
    obtain ⟨y,hy,he⟩:=orderedLaw_positive p e x hx
    have heq : (∑ i,if InRectangle S (y i).1.rep (y i).2.rep then (1:ℝ) else 0)=
        (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0) := by
      simpa only [he] using e.sum_comp
        (fun i=>if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)
    rw [←heq]
    exact hocc y hy S
  have h:=high_three_collisions hdim (orderedLaw p e) s M hs hsmall hi ho
  simp only [orderedHighCollision]
  rw [sum_symm_reindex]
  linarith

end
end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighChosenRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype κ] {w n : ℕ} [Nonempty (Fin n)]
local instance hcrBDE_r11b48c_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance hcrTDE_r11b48c_1 : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.hcrIDE
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma orderedHigh_collision_subset (p : Law (Slots w n→FlagPair K V)) (s : ℝ)
    (U : Finset (Slots w n)) :
    (∑i∈U,∑j∈U,orderedHighCollision p (slotEquiv w n) s i j)≤
      ∑i,∑j,orderedHighCollision p (slotEquiv w n) s i j := by
  apply (Finset.sum_le_sum (fun i _=>Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ U) (fun j _ _=>orderedHighCollision_nonneg p _ s i j))).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
    (fun i _ _=>Finset.sum_nonneg (fun j _=>orderedHighCollision_nonneg p _ s i j))

theorem exists_high_three_round_oai (hd : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (elig : κ→Fin w×Bool→Finset (Fin n)) (rounds rem : ℕ)
    (hrounds : 0 < rounds) (hrem : 0 < rem)
    (hS : ∀a,0<μ a→∀b,rem+rounds≤(elig a b).card)
    (J d ε budget s M : ℝ) (hdpos : 0<d) (hε : 0<ε)
    (D : κ→Slots w n→Finset (FlagPair K V)) (hJ : ∀a i,Real.log (D a i).card≤J)
    (hp : ∀a,0<μ a→InDomains (p a) (D a))
    (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (elig a)))
    (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (elig a)) J)≤budget)
    (hs : 2 ≤ s) (hsmall : Real.log 32+3*s<Real.log (Nat.card K))
    (hinc : ∀a,0<μ a→∀x,0<p a x→∀i,Incident (x i).1 (x i).2)
    (hocc : ∀a,0<μ a→∀x,0<p a x→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    ∃i : Fin rounds,mean (preRoundLaw μ p elig i.val) (fun z=>
      ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
        preRoundBad μ p elig i.val J d ε
          (fun a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w n) s) z j)≤
      budget/d+(2*budget/rounds+(4*(w*(4*n):ℝ)*M)/rem)/ε := by
  apply exists_small_deletion_round μ p elig rounds rem hrounds hrem hS J d ε budget
    (4*(w*(4*n):ℝ)*M) hdpos hε D hJ hp hfix hbudget
    (fun i a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w n) s)
  · intro i a h x y
    exact orderedHighCollision_nonneg _ _ _ _ _
  · intro i a ha h hh
    apply (orderedHigh_collision_subset _ s _).trans
    have hn : ((w*(4*n):ℕ):ℝ)=w*(4*n) := by push_cast;rfl
    rw [←hn]
    apply orderedHigh_collision_budget hd _ _ s M hs hsmall
    · intro x hx j
      exact hinc a ha x (history_support (p a) i.val h x hx) j
    · intro x hx W
      exact hocc a ha x (history_support (p a) i.val h x hx) W
end
end SharpRamseyFive.Marking

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.Marking.exists_high_three_round_oai := @OAI.SharpRamseyFive.Marking.exists_high_three_round_oai
