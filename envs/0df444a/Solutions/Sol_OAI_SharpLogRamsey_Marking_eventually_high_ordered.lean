-- Prove2me | solution 1 for OAI.SharpLogRamsey.Marking.eventually_high_ordered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:35:54.405528+00:00
-- url     : https://prove2.me/submissions/51445f48-0d97-475c-a311-f480c5e91220

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_eventually_prepared_high

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
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
theorem divergence_map_le (p q : Law α) (hab : p.AbsolutelyContinuous q) (f : α → β) :
    divergence (p.map f) (q.map f) ≤ divergence p q := by
  unfold divergence
  calc
    _ ≤ ∑ b, ∑ a with f a = b, p.mass a*Real.log (p.mass a/q.mass a) := by
      apply sum_le_sum
      intro b hb
      exact log_sum (univ.filter (fun a => f a = b)) p.mass q.mass
        (fun a ha => p.nonneg a) (fun a ha => q.nonneg a) (fun a ha => hab a)
    _ = _ := sum_fiberwise univ f _

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem Law.prod_map (p : Law α) (q : Law β) (f : α → γ) (g : β → δ) :
    (p.prod q).map (fun z => (f z.1,g z.2)) = (p.map f).prod (q.map g) := by
  ext z
  rcases z with ⟨c,d⟩
  simp only [Law.map, Law.prod, Prod.mk.injEq, Fintype.sum_prod_type, sum_filter]
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  split_ifs <;> simp_all

theorem mutualInfo_map_le (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    mutualInfo (p.map (fun z => (f z.1,g z.2))) ≤ mutualInfo p := by
  rw [mutualInfo_eq_divergence, Law.fst_map_pair, Law.snd_map_pair,
    mutualInfo_eq_divergence, ← Law.prod_map]
  exact divergence_map_le _ _ p.absContinuous_prod _

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

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Law.absContinuous_pi (p : Law (ι → β)) :
    p.AbsolutelyContinuous (Law.pi p.marginal) := by
  intro x hz
  change (∏ i, (p.marginal i).mass (x i)) = 0 at hz
  obtain ⟨i,hi⟩ := (prod_eq_zero_iff).mp hz
  have hh : p.mass x ≤ (p.marginal i).mass (x i) := p.le_map (fun y => y i) x
  exact le_antisymm (hi.2 ▸ hh) (p.nonneg _)

theorem totalCorrelation_eq_divergence (p : Law (ι → β)) :
    totalCorrelation p = divergence p (Law.pi p.marginal) := by
  have pointwise (x : ι → β) :
      p.mass x*Real.log (p.mass x/(∏ i, (p.marginal i).mass (x i))) =
      p.mass x*Real.log (p.mass x)-∑ i, p.mass x*Real.log ((p.marginal i).mass (x i)) := by
    by_cases hz : p.mass x = 0
    · simp [hz]
    have hp : 0 < p.mass x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hz)
    have hm (i : ι) : 0 < (p.marginal i).mass (x i) := hp.trans_le (p.le_map _ x)
    rw [Real.log_div hz (prod_ne_zero_iff.mpr fun i hi => (hm i).ne'),
      Real.log_prod (fun i hi => (hm i).ne'),mul_sub,mul_sum]
  have hs : ∑ x, ∑ i, p.mass x*Real.log ((p.marginal i).mass (x i)) =
      ∑ i, ∑ b, (p.marginal i).mass b*Real.log ((p.marginal i).mass b) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    exact (p.sum_map (fun x => x i) (fun b => Real.log ((p.marginal i).mass b))).symm
  unfold divergence
  change _ = ∑ x, p.mass x*Real.log (p.mass x/(∏ i, (p.marginal i).mass (x i)))
  simp_rw [pointwise]
  rw [sum_sub_distrib,hs]
  unfold totalCorrelation entropy
  rw [sum_neg_distrib]
  ring

theorem totalCorrelation_nonneg (p : Law (ι → β)) : 0 ≤ totalCorrelation p := by
  rw [totalCorrelation_eq_divergence]
  exact divergence_nonneg _ _ p.absContinuous_pi

theorem entropy_subadditive_pi (p : Law (ι → β)) :
    entropy p ≤ ∑ i, entropy (p.marginal i) := by
  have h := totalCorrelation_nonneg p
  unfold totalCorrelation at h
  linarith

theorem entropy_restrict_chain (p : Law (ι → β)) (E : Finset ι) :
    entropy p = entropy (p.restrict E)+
      ∑ e, (p.restrict E).mass e*entropy ((p.cond (fun x (i:E) => x i) e).restrict Eᶜ) := by
  have hx : Function.Injective (fun x : ι → β =>
      ((fun i : ↥(Eᶜ) => x i),(fun i : E => x i))) := by
    intro x y h
    funext i
    by_cases hi : i ∈ E
    · exact congr_fun (congrArg Prod.snd h) ⟨i,hi⟩
    · exact congr_fun (congrArg Prod.fst h) ⟨i,by simpa using hi⟩
  have h := entropy_cond_chain p (fun x (i:E) => x i) (fun x (i:↥(Eᶜ)) => x i)
  rwa [entropy_map_eq_of_injective p _ hx] at h

theorem entropy_marginal_cond (p : Law (ι → β)) (E : Finset ι) (i : ι) :
    (∑ e, (p.restrict E).mass e*entropy ((p.cond (fun x (j:E) => x j) e).marginal i)) =
      entropy (p.marginal i)-mutualInfo (p.map (fun x => (x i,fun j:E => x j))) := by
  have he : (p.map (fun x => (x i,fun j:E => x j))).fst = p.marginal i := by
    rw [← Law.map_fst, Law.map_map]; rfl
  have hs : (p.map (fun x => (x i,fun j:E => x j))).snd = p.restrict E := by
    rw [← Law.map_snd, Law.map_map]; rfl
  have h := entropy_cond_chain p (fun x (j:E) => x j) (fun x => x i)
  unfold mutualInfo
  rw [he,hs,h]
  change _ = entropy (p.marginal i)-(entropy (p.marginal i)+entropy (p.restrict E)-
    (entropy (p.restrict E)+∑ e, (p.restrict E).mass e*entropy ((p.cond (fun x (j:E) => x j) e).marginal i)))
  ring

theorem totalCorrelation_drop (p : Law (ι → β)) (E : Finset ι) :
    totalCorrelation p-
      (∑ e, (p.restrict E).mass e*
        totalCorrelation ((p.cond (fun x (i:E) => x i) e).restrict Eᶜ)) =
    totalCorrelation (p.restrict E)+
      ∑ i ∈ Eᶜ, mutualInfo (p.map (fun x => (x i,fun j:E => x j))) := by
  have hc := entropy_restrict_chain p E
  have hm : ∑ e, (p.restrict E).mass e *
      (∑ i : ↥(Eᶜ), entropy (((p.cond (fun x (i:E) => x i) e).restrict Eᶜ).marginal i)) =
      ∑ i ∈ Eᶜ, (entropy (p.marginal i)-mutualInfo (p.map (fun x => (x i,fun j:E => x j)))) := by
    simp only [Law.marginal_restrict,mul_sum]
    rw [sum_comm]
    simp_rw [entropy_marginal_cond]
    exact (sum_subtype (Eᶜ) (fun _ => Iff.rfl) (fun i => entropy (p.marginal i)-mutualInfo (p.map (fun x => (x i,fun j:E => x j))))).symm
  unfold totalCorrelation
  simp only [mul_sub,sum_sub_distrib]
  rw [hm]
  have he : (∑ i : E, entropy ((p.restrict E).marginal i)) =
      ∑ i ∈ E, entropy (p.marginal i) := by
    simp only [Law.marginal_restrict]
    exact (sum_subtype E (fun _ => Iff.rfl) (fun i => entropy (p.marginal i))).symm
  rw [he,sum_sub_distrib]
  have hsum := sum_add_sum_compl E (fun i => entropy (p.marginal i))
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {B X : Type*} [Fintype B] [Fintype X] [DecidableEq B]

theorem fresh_draw_identity (b : B) (g : X→(B→X)→ℝ)
    (hdep : ∀ j f x, g j (Function.update f b x)=g j f) :
    (Fintype.card X:ℝ)*(∑ f : B→X, g (f b) f)=
      ∑ f : B→X, ∑ j, g j f := by
  classical
  let e := Equiv.funSplitAt b X
  have hi (x : X) (r : {z : B // z≠b}→X) : e.symm (x,r) b=x := by
    simp [e,Equiv.funSplitAt,Equiv.piSplitAt]
  have hu (x j : X) (r : {z : B // z≠b}→X) :
      Function.update (e.symm (x,r)) b j=e.symm (j,r) := by
    funext z
    by_cases hz : z=b
    · subst z
      simp [hi]
    · simp [e,Equiv.funSplitAt,Equiv.piSplitAt,hz]
  have hg (x j : X) (r : {z : B // z≠b}→X) : g j (e.symm (x,r))=g j (e.symm (j,r)) := by
    rw [←hu x j r]
    exact (hdep j (e.symm (x,r)) j).symm
  rw [←e.symm.sum_comp (fun f => g (f b) f),←e.symm.sum_comp (fun f => ∑ j, g j f)]
  simp only [Fintype.sum_prod_type,hi]
  trans (∑ _x : X, ∑ j : X, ∑ r : {z : B // z≠b}→X, g j (e.symm (j,r)))
  · simp only [sum_const,nsmul_eq_mul,card_univ]
  · apply sum_congr rfl
    intro x _
    rw [sum_comm]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro j _
    exact (hg x j r).symm

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

lemma pairInformation_le_exposed (p : Law (ι → β)) (i : ι) (E : Finset ι)
    {j : ι} (hj : j∈E) : pairInformation p i j ≤ exposedInformation p i E := by
  change mutualInfo (p.map (fun x => (x i,x j))) ≤
    mutualInfo (p.map (fun x => (x i,fun z : E => x z)))
  have H := mutualInfo_map_le (p.map (fun x => (x i,fun z : E => x z)))
    id (fun z : E → β => z ⟨j,hj⟩)
  simpa only [Law.map_map,Function.comp_def,id_eq] using H

lemma maximumInformation_le_exposed (p : Law (ι → β)) (i : ι) (E J : Finset ι)
    (hJ : J⊆E) : maximumInformation p i J ≤ exposedInformation p i E := by
  apply Finset.sup_le
  intro j hj
  exact pairInformation_le_exposed p i E (hJ hj)

theorem maximum_exposure_drop (p : Law (ι → β)) (E : Finset ι)
    (J : ι → Finset ι) (hJ : ∀ i, J i⊆E) :
    (∑ i, (maximumInformation p i (J i):ℝ)) ≤
      totalCorrelation p-
        (∑ e, (p.restrict E).mass e*
          totalCorrelation ((p.cond (fun x (j:E) => x j) e).restrict Eᶜ))+
      ∑ i∈E, (maximumInformation p i (J i):ℝ) := by
  have H := totalCorrelation_drop p E
  have hn := totalCorrelation_nonneg (p.restrict E)
  have hle : (∑ i∈Eᶜ, (maximumInformation p i (J i):ℝ)) ≤
      ∑ i∈Eᶜ, mutualInfo (p.map (fun x => (x i,fun j:E => x j))) := by
    apply sum_le_sum
    intro i _
    exact maximumInformation_le_exposed p i E (J i) (hJ i)
  have hs := sum_add_sum_compl E (fun i => (maximumInformation p i (J i):ℝ))
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {ι β B X : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
  [Fintype B] [Fintype X] [DecidableEq B]

omit [Fintype ι] [Fintype X] in
lemma otherRepresentatives_sub (e : B×X ↪ ι) (own : ι→Option B)
    (f : B→X) (i : ι) : otherRepresentatives e own f i⊆freshRepresentatives e f := by
  exact image_subset_image (filter_subset _ _)

omit [Fintype ι] [Fintype X] in
lemma otherRepresentatives_update (e : B×X ↪ ι) (own : ι→Option B)
    (hown : ∀ b x, own (e (b,x))=some b) (b : B) (x y : X) (f : B→X) :
    otherRepresentatives e own (Function.update f b y) (e (b,x))=
      otherRepresentatives e own f (e (b,x)) := by
  unfold otherRepresentatives
  rw [hown]
  apply image_congr
  intro c hc
  have hn : c≠b := by simpa using (mem_filter.mp hc).2
  simp only [Function.update_of_ne hn]

theorem selected_maximum_absorption (p : Law (ι→β)) (e : B×X ↪ ι)
    (own : ι→Option B) (hown : ∀ b x, own (e (b,x))=some b) :
    (Fintype.card X:ℝ)*
      (∑ f : B→X, ∑ i∈freshRepresentatives e f,
        (maximumInformation p i (otherRepresentatives e own f i):ℝ)) ≤
      ∑ f : B→X, ∑ i, (maximumInformation p i (otherRepresentatives e own f i):ℝ) := by
  let M (f : B→X) (i : ι) : ℝ := maximumInformation p i (otherRepresentatives e own f i)
  have hsel (f : B→X) : (∑ i∈freshRepresentatives e f,M f i)=∑ b,M f (e (b,f b)) := by
    apply sum_image
    intro b _ c _ he
    exact (Prod.mk.inj (e.injective he)).1
  change (Fintype.card X:ℝ)*(∑ f, ∑ i∈freshRepresentatives e f,M f i)≤∑ f,∑ i,M f i
  simp_rw [hsel]
  rw [sum_comm,mul_sum]
  have hb (b : B) : (Fintype.card X:ℝ)*(∑ f : B→X,M f (e (b,f b)))=
      ∑ f : B→X,∑ x : X, M f (e (b,x)) := by
    apply fresh_draw_identity b (fun x f => M f (e (b,x)))
    intro x f y
    dsimp [M]
    rw [otherRepresentatives_update e own hown]
  simp_rw [hb]
  rw [sum_comm]
  apply sum_le_sum
  intro f _
  have h : (∑ z∈univ.map e, M f z) ≤ ∑ i, M f i := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro i _ _
    exact (maximumInformation p i _).property
  simpa only [sum_map,Fintype.sum_prod_type] using h

theorem fresh_round_drop (p : Law (ι→β)) (e : B×X ↪ ι)
    (own : ι→Option B) (hown : ∀ b x, own (e (b,x))=some b)
    (hX : 0<Fintype.card X) :
    (1-1/(Fintype.card X:ℝ))*
      (∑ f : B→X, ∑ i, (maximumInformation p i (otherRepresentatives e own f i):ℝ)) ≤
      ∑ f : B→X, (totalCorrelation p-
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z*
          totalCorrelation ((p.cond (fun x (j:freshRepresentatives e f) => x j) z).restrict
            (freshRepresentatives e f)ᶜ)) := by
  have H := sum_le_sum (fun f (_ : f∈(univ : Finset (B→X))) =>
    maximum_exposure_drop p (freshRepresentatives e f) (otherRepresentatives e own f)
      (otherRepresentatives_sub e own f))
  rw [sum_add_distrib] at H
  have hs := selected_maximum_absorption p e own hown
  have hn : 0<(Fintype.card X:ℝ) := by exact_mod_cast hX
  let A : ℝ := ∑ f : B→X, ∑ i, (maximumInformation p i (otherRepresentatives e own f i):ℝ)
  let S : ℝ := ∑ f : B→X, ∑ i∈freshRepresentatives e f,
    (maximumInformation p i (otherRepresentatives e own f i):ℝ)
  have hh : S≤A/(Fintype.card X:ℝ) := by
    apply (le_div_iff₀ hn).mpr
    change S*(Fintype.card X:ℝ)≤A
    change (Fintype.card X:ℝ)*S≤A at hs
    nlinarith
  change A≤_+S at H
  change (1-1/(Fintype.card X:ℝ))*A≤_
  have he : (1-1/(Fintype.card X:ℝ))*A=A-A/(Fintype.card X:ℝ) := by ring
  rw [he]
  linarith

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RemainingEmbedding
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
open Finset
open scoped Classical
noncomputable section
variable {B β ι : Type*} [Fintype B] [Fintype β] [Fintype ι] [DecidableEq ι] [DecidableEq B]

theorem roundInformation_budget {m : ℕ} (hm : 2 ≤ m) (p : Law (ι → β))
    (e : B×Fin m  ↪  ι) (own : ι → Option B) (hown : ∀ b x,own (e (b,x))= some b) :
    roundInformation p e own+2*nextPotential p e ≤ 2*totalCorrelation p := by
  have hm0 : 0 < m := by omega
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by positivity
  let : Nonempty (Fin m) := ⟨⟨0,hm0⟩⟩
  have hc : (0:ℝ)<Fintype.card (B → Fin m) := by exact_mod_cast Fintype.card_pos
  have H := fresh_round_drop p e own hown (by simpa using hm0)
  simp only [Fintype.card_fin,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul] at H
  have hhalf : (1/2:ℝ) ≤ 1-1/(m:ℝ) := by
    have hdiv : (1:ℝ)/(m:ℝ) ≤ 1/2 := (div_le_iff₀ hmpos).mpr (by linarith)
    linarith
  have hmi : 0 ≤ ∑ f : B → Fin m,∑ i,(maximumInformation p i (otherRepresentatives e own f i):ℝ) := by positivity
  have HH := mul_le_mul_of_nonneg_right hhalf hmi
  unfold roundInformation nextPotential
  rw [← mul_div_assoc, ← add_div]
  apply (div_le_iff₀ hc).mpr
  have he : 2*totalCorrelation p*↑(Fintype.card (B → Fin m))=
      2*(↑(Fintype.card (B → Fin m))*totalCorrelation p) := by ring
  rw [he]
  linarith

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset
open scoped Classical
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

lemma exposureScores_zero {ι : Type u} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    (p : Law (ι → β)) (e : B × Fin (n+(k+1)) ↪ ι) (own : ι → Option B) :
    exposureScores n (k+1) p e own 0 = roundInformation p e own := rfl

lemma exposureScores_succ {ι : Type u} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    (p : Law (ι → β)) (e : B × Fin (n+(k+1)) ↪ ι) (own : ι → Option B) (j : Fin k) :
    exposureScores n (k+1) p e own j.succ =
      (∑ f : B → Fin (n+k+1), ∑ z,
        (p.restrict (freshRepresentatives e f)).mass z *
          exposureScores n k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) (fun i => own i) j) /
          Fintype.card (B → Fin (n+k+1)) := rfl

theorem exposureScores_sum_le (n k : ℕ) (hn : 2 ≤ n)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι → β)) (e : B × Fin (n+k) ↪ ι)
    (own : ι → Option B) (hown : ∀ b x, own (e (b,x)) = some b) :
    (∑ t, exposureScores n k p e own t) ≤ 2 * totalCorrelation p := by
  induction k generalizing ι with
  | zero =>
    simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (totalCorrelation_nonneg p)
  | succ k ih =>
    rw [Fin.sum_univ_succ, exposureScores_zero]
    have hs : (∑ t : Fin k, exposureScores n (k+1) p e own t.succ) ≤
        2 * nextPotential p e := by
      simp_rw [exposureScores_succ, ← sum_div]
      rw [sum_comm]
      simp_rw [sum_comm (s := (univ : Finset (Fin k))), ← mul_sum]
      unfold nextPotential
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [mul_sum]
      apply sum_le_sum
      intro f _
      rw [mul_sum]
      apply sum_le_sum
      intro z _
      rw [mul_left_comm (2:ℝ)]
      apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
      exact ih _ (remainingEmbedding e f) (fun i => own i)
        (fun b x => remaining_own e f own hown b x)
    have hb := roundInformation_budget (by omega : 2 ≤ n+(k+1)) p e own hown
    linarith only [hs,hb]

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

lemma marginal_deficit_sum (p : Law (ι → β)) (J : ℝ) :
    (∑ i, (J-entropy (p.marginal i))) ≤ tupleDeficit J p := by
  have h := entropy_subadditive_pi p
  simp only [tupleDeficit,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]
  linarith

lemma tupleDeficit_nonneg (p : Law (ι → β)) (J : ℝ)
    (h : ∀ i, entropy (p.marginal i) ≤ J) : 0 ≤ tupleDeficit J p := by
  exact (sum_nonneg (fun i _ => sub_nonneg.mpr (h i))).trans (marginal_deficit_sum p J)

theorem tupleDeficit_drop (p : Law (ι → β)) (E : Finset ι) (J : ℝ) :
    tupleDeficit J p - ∑ z, (p.restrict E).mass z *
      tupleDeficit J ((p.cond (fun x (i:E) => x i) z).restrict Eᶜ) =
        tupleDeficit J (p.restrict E) := by
  have hc := entropy_restrict_chain p E
  have hn : (Fintype.card ι:ℝ) = (Fintype.card E:ℝ)+Fintype.card ↥(Eᶜ) := by
    simp only [Fintype.card_coe]
    exact_mod_cast (card_add_card_compl E).symm
  simp only [tupleDeficit,mul_sub,sum_sub_distrib,← sum_mul,Law.total,one_mul]
  rw [hn]
  linarith

lemma tupleDeficit_expected_le (p : Law (ι → β)) (E : Finset ι) (J : ℝ)
    (h : ∀ i, entropy (p.marginal i) ≤ J) :
    (∑ z, (p.restrict E).mass z *
      tupleDeficit J ((p.cond (fun x (i:E) => x i) z).restrict Eᶜ)) ≤ tupleDeficit J p := by
  have he := tupleDeficit_nonneg (p.restrict E) J (fun i => by
    simpa only [Law.marginal_restrict] using h i)
  have hd := tupleDeficit_drop p E J
  linarith

lemma totalCorrelation_le_tupleDeficit (p : Law (ι → β)) (J : ℝ)
    (h : ∀ i, entropy (p.marginal i) ≤ J) : totalCorrelation p ≤ tupleDeficit J p := by
  have hs := sum_le_sum (fun i (_ : i ∈ univ) => h i)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  unfold totalCorrelation tupleDeficit
  linarith

end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
variable {Ω α Γ A : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype A]

lemma entropy_mapped_support (p : Law Ω) (F : Ω → α) (S : Finset α)
    (hS : ∀ x, p.mass x ≠ 0 → F x ∈ S) : entropy (p.map F) ≤ Real.log S.card := by
  apply entropy_le_log_card
  intro a ha
  by_contra hn
  obtain ⟨x,hx,rfl⟩ := p.map_support F a hn
  exact ha (hS x hx)

end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

lemma tupleSupported_marginal_cap (p : Law (ι → β)) (D : ι → Finset β)
    (hD : tupleSupported p D) (J : ℝ) (hJ : ∀ i, Real.log (D i).card ≤ J) (i : ι) :
    entropy (p.marginal i) ≤ J :=
  (entropy_mapped_support p (fun x => x i) (D i) (fun x hx => hD x hx i)).trans (hJ i)

lemma tupleSupported_cond_restrict (p : Law (ι → β)) (D : ι → Finset β)
    (hD : tupleSupported p D) (E : Finset ι) (z : E → β)
    (hz : (p.restrict E).mass z ≠ 0) :
    tupleSupported ((p.cond (fun x (i:E) => x i) z).restrict Eᶜ) (fun i => D i) := by
  intro x hx i
  obtain ⟨y,hy,rfl⟩ := (p.cond (fun x (i:E) => x i) z).map_support _ x hx
  exact hD y ((p.cond_support (fun x (i:E) => x i) z hz y hy).1) i

end
end SharpLogRamsey.Selection
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

lemma exposureDeficits_succ (n k : ℕ) (J : ℝ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : Law (ι → β)) (e : B × Fin (n+(k+1)) ↪ ι) (j : Fin k) :
    exposureDeficits n J (k+1) p e j.succ =
      (∑ f : B → Fin (n+k+1), ∑ z,
        (p.restrict (freshRepresentatives e f)).mass z *
          exposureDeficits n J k
            ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
              (freshRepresentatives e f)ᶜ)
            (remainingEmbedding e f) j) / Fintype.card (B → Fin (n+k+1)) := rfl

theorem exposureDeficits_le (n k : ℕ) (J : ℝ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (p : Law (ι → β)) (e : B × Fin (n+k) ↪ ι) (D : ι → Finset β)
    (hD : tupleSupported p D) (hJ : ∀ i, Real.log (D i).card ≤ J) (t : Fin k) :
    exposureDeficits n J k p e t ≤ tupleDeficit J p := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · exact le_rfl
    · rw [exposureDeficits_succ]
      have hn : (0:ℝ) < Fintype.card (B → Fin (n+k+1)) := by
        let : Nonempty (Fin (n+k+1)) := ⟨⟨0,by omega⟩⟩
        exact_mod_cast Fintype.card_pos
      apply (div_le_iff₀ hn).mpr
      calc
        _ ≤ ∑ f : B → Fin (n+k+1), ∑ z,
            (p.restrict (freshRepresentatives e f)).mass z *
              tupleDeficit J ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) := by
          apply sum_le_sum
          intro f _
          apply sum_le_sum
          intro z _
          by_cases hz : (p.restrict (freshRepresentatives e f)).mass z = 0
          · rw [hz,zero_mul,zero_mul]
          · apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
            exact ih _ (remainingEmbedding e f) (fun i => D i)
              (tupleSupported_cond_restrict p D hD _ z hz) (fun i => hJ i) j
        _ ≤ ∑ _f : B → Fin (n+k+1), tupleDeficit J p := by
          apply sum_le_sum
          intro f _
          exact tupleDeficit_expected_le p _ J (tupleSupported_marginal_cap p D hD J hJ)
        _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_FreshBlockBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {B X ι : Type*} [Fintype B] [Fintype X] [Fintype ι] [DecidableEq B] [DecidableEq ι]

theorem selected_absorption (e : B×X ↪ ι) (M : (B→X)→ι→ℝ)
    (hM : ∀ f i,0≤M f i)
    (hupdate : ∀ b x f y,M (Function.update f b y) (e (b,x))=M f (e (b,x))) :
    (Fintype.card X:ℝ)*(∑ f : B→X, ∑ i∈freshRepresentatives e f,M f i)≤
      ∑ f : B→X,∑ i,M f i := by
  have hsel (f : B→X) : (∑ i∈freshRepresentatives e f,M f i)=∑ b,M f (e (b,f b)) := by
    apply sum_image
    intro b _ c _ he
    exact (Prod.mk.inj (e.injective he)).1
  simp_rw [hsel]
  rw [sum_comm,mul_sum]
  have hb (b : B) : (Fintype.card X:ℝ)*(∑ f : B→X,M f (e (b,f b)))=
      ∑ f : B→X,∑ x : X,M f (e (b,x)) :=
    fresh_draw_identity b (fun x f => M f (e (b,x))) (hupdate b)
  simp_rw [hb]
  rw [sum_comm]
  apply sum_le_sum
  intro f _
  have hh := sum_le_sum_of_subset_of_nonneg (s:=univ.map e) (t:=univ)
    (f:=M f) (subset_univ _) (fun i _ _ => hM f i)
  simpa only [sum_map,Fintype.sum_prod_type] using hh

theorem selected_fixed_observable (e : B×X ↪ ι) (δ : ι→ℝ) (hδ : ∀ i,0≤δ i) :
    (Fintype.card X:ℝ)*(∑ f : B→X, ∑ i∈freshRepresentatives e f,δ i)≤
      (Fintype.card (B→X):ℝ)*∑ i,δ i := by
  simpa only [sum_const,card_univ,nsmul_eq_mul] using
    selected_absorption e (fun _=>δ) (fun _=>hδ) (by intros; rfl)

omit [Fintype ι] [DecidableEq ι] in
lemma maximumCharge_le_sum (c : ι→ι→ℝ≥0) (i : ι) (J : Finset ι) :
    (maximumCharge c i J:ℝ)≤∑ j∈J,(c i j:ℝ) := by
  have hh : maximumCharge c i J≤∑ j∈J,c i j := by
    apply Finset.sup_le
    intro j hj
    exact single_le_sum (fun j _ => (zero_le : (0:ℝ≥0) ≤ c i j)) hj
  exact_mod_cast hh

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_FreshBlockCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {B X ι : Type*} [Fintype B] [Fintype X] [Fintype ι] [DecidableEq B] [DecidableEq ι]

theorem collision_all_indices (e : B×X ↪ ι) (own : ι→Option B) (c : ι→ι→ℝ≥0) :
    (Fintype.card X:ℝ)*(∑ f : B→X,∑ i,
      (maximumCharge c i (otherRepresentatives e own f i):ℝ))≤
      (Fintype.card (B→X):ℝ)*∑ i,∑ j,(c i j:ℝ) := by
  calc
    _ ≤ (Fintype.card X:ℝ)*(∑ f : B→X,∑ i,
        ∑ j∈freshRepresentatives e f,(c i j:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro f _
      apply sum_le_sum
      intro i _
      exact (maximumCharge_le_sum c i _).trans
        (sum_le_sum_of_subset_of_nonneg (otherRepresentatives_sub e own f i)
          (fun j _ _ => NNReal.coe_nonneg (c i j)))
    _ = ∑ i,(Fintype.card X:ℝ)*(∑ f : B→X,
        ∑ j∈freshRepresentatives e f,(c i j:ℝ)) := by rw [sum_comm,mul_sum]
    _ ≤ ∑ i,(Fintype.card (B→X):ℝ)*∑ j,(c i j:ℝ) := by
      apply sum_le_sum
      intro i _
      exact selected_fixed_observable e (fun j => (c i j:ℝ)) (fun j => (c i j).coe_nonneg)
    _ = _ := by rw [mul_sum]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β B X ι : Type*} [Fintype β] [Fintype B] [Fintype X] [Fintype ι]
  [DecidableEq B] [DecidableEq ι]

omit [Fintype X] in
lemma badIndices_update_self (p : Law (ι→β)) (e : B×X ↪ ι)
    (own : ι→Option B) (hown : ∀ b x,own (e (b,x))=some b)
    (c : ι→ι→NNReal) (J D a : ℝ) (b : B) (x y : X) (f : B→X) :
    e (b,x)∈badIndices p e own c J D a (Function.update f b y) ↔
      e (b,x)∈badIndices p e own c J D a f := by
  simp only [badIndices,mem_filter]
  rw [otherRepresentatives_update e own hown]

theorem selected_bad_absorption (p : Law (ι→β)) (e : B×X ↪ ι)
    (own : ι→Option B) (hown : ∀ b x,own (e (b,x))=some b)
    (c : ι→ι→NNReal) (J D a : ℝ) :
    (Fintype.card X:ℝ)*(∑ f : B→X,
      ((freshRepresentatives e f∩badIndices p e own c J D a f).card:ℝ))≤
      ∑ f : B→X,((badIndices p e own c J D a f).card:ℝ) := by
  have hh := selected_absorption e
    (fun f i => if i∈badIndices p e own c J D a f then (1:ℝ) else 0)
    (by intros; split_ifs <;> norm_num) (by
      intro b x f y
      simp only [badIndices_update_self p e own hown c J D a b x y f])
  simpa only [sum_boole,filter_mem_eq_inter,univ_inter,Nat.cast_sum] using hh

omit [Fintype X] in

theorem badIndices_card (p : Law (ι→β)) (e : B×X ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) (hD : 0<D) (ha : 0<a)
    (hJ : ∀ i,entropy (p.marginal i)≤J) (f : B→X) :
    ((badIndices p e own c J D a f).card:ℝ)≤tupleDeficit J p/D+
      (∑ i,(maximumInformation p i (otherRepresentatives e own f i):ℝ))/a+
      (∑ i,(maximumCharge c i (otherRepresentatives e own f i):ℝ))/a := by
  let δ := fun i => J-entropy (p.marginal i)
  let I := fun i => (maximumInformation p i (otherRepresentatives e own f i):ℝ)
  let C := fun i => (maximumCharge c i (otherRepresentatives e own f i):ℝ)
  have hδ (i : ι) : 0≤δ i := sub_nonneg.mpr (hJ i)
  have hI (i : ι) : 0≤I i := NNReal.coe_nonneg _
  have hC (i : ι) : 0≤C i := NNReal.coe_nonneg _
  have hcost (i : ι) : 0≤δ i/D+I i/a+C i/a :=
    add_nonneg (add_nonneg (div_nonneg (hδ i) hD.le) (div_nonneg (hI i) ha.le))
      (div_nonneg (hC i) ha.le)
  have hib (i : ι) (hi : i∈badIndices p e own c J D a f) :
      1≤δ i/D+I i/a+C i/a := by
    rcases (mem_filter.mp hi).2 with hd | ⟨j,hj,hh⟩
    · have hh : 1≤δ i/D := (le_div_iff₀ hD).mpr (by simpa only [one_mul] using hd.le)
      linarith only [hh,div_nonneg (hI i) ha.le,div_nonneg (hC i) ha.le]
    · have hi' : (pairInformation p i j:ℝ)≤I i := by
        exact_mod_cast (Finset.le_sup (f:=pairInformation p i) hj)
      have hc' : (c i j:ℝ)≤C i := by
        exact_mod_cast (Finset.le_sup (f:=c i) hj)
      have hh' : 1≤(I i+C i)/a := (le_div_iff₀ ha).mpr (by linarith)
      rw [add_div] at hh'
      linarith only [hh',div_nonneg (hδ i) hD.le]
  calc
    _ = ∑ _i∈badIndices p e own c J D a f,(1:ℝ) := by simp
    _ ≤ ∑ i∈badIndices p e own c J D a f,(δ i/D+I i/a+C i/a) := sum_le_sum hib
    _ ≤ ∑ i,(δ i/D+I i/a+C i/a) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hcost i)
    _ = (∑ i,δ i)/D+(∑ i,I i)/a+(∑ i,C i)/a := by
      simp only [sum_add_distrib,←sum_div]
    _ ≤ _ := add_le_add (add_le_add
      (div_le_div_of_nonneg_right (marginal_deficit_sum p J) hD.le) le_rfl) le_rfl

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β B ι : Type*} [Fintype β] [Fintype B] [Fintype ι] [DecidableEq B] [DecidableEq ι]

theorem roundBad_le {m : ℕ} (hm : 0 < m) (p : Law (ι→β)) (e : B×Fin m ↪ ι)
    (own : ι→Option B) (c : ι→ι→NNReal) (J D a : ℝ) (hD : 0 < D) (ha : 0 < a)
    (hJ : ∀ i,entropy (p.marginal i)≤J) :
    roundBad p e own c J D a≤tupleDeficit J p/D+roundInformation p e own/a+
      (∑ i,∑ j,(c i j:ℝ))/((m:ℝ)*a) := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hm' : (0:ℝ) <  m := by exact_mod_cast hm
  have hN : (0:ℝ) <  Fintype.card (B→Fin m) := by exact_mod_cast Fintype.card_pos
  have HC : (∑ f : B→Fin m,∑ i,
        (maximumCharge c i (otherRepresentatives e own f i):ℝ))/Fintype.card (B→Fin m)≤
      (∑ i,∑ j,(c i j:ℝ))/(m:ℝ) := by
    apply (div_le_div_iff₀ hN hm').mpr
    have hh := collision_all_indices e own c
    simp only [Fintype.card_fin] at hh
    nlinarith only [hh]
  calc
    _ ≤ (∑ f : B→Fin m,(tupleDeficit J p/D+
        (∑ i,(maximumInformation p i (otherRepresentatives e own f i):ℝ))/a+
        (∑ i,(maximumCharge c i (otherRepresentatives e own f i):ℝ))/a))/
          Fintype.card (B→Fin m) := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact sum_le_sum (fun f _ => badIndices_card p e own c J D a hD ha hJ f)
    _ = tupleDeficit J p/D+roundInformation p e own/a+
        ((∑ f : B→Fin m,∑ i,
          (maximumCharge c i (otherRepresentatives e own f i):ℝ))/Fintype.card (B→Fin m))/a := by
      simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,←sum_div,roundInformation]
      field_simp
    _ ≤ tupleDeficit J p/D+roundInformation p e own/a+
        ((∑ i,∑ j,(c i j:ℝ))/(m:ℝ))/a :=
      add_le_add le_rfl (div_le_div_of_nonneg_right HC ha.le)
    _ = _ := by rw [div_div]

theorem roundSelectedBad_le {m : ℕ} (p : Law (ι→β)) (e : B×Fin m ↪ ι)
    (own : ι→Option B) (hown : ∀ b x,own (e (b,x))=some b)
    (c : ι→ι→NNReal) (J D a : ℝ) :
    (m:ℝ)*roundSelectedBad p e own c J D a ≤ roundBad p e own c J D a := by
  unfold roundSelectedBad roundBad
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [Fintype.card_fin] using selected_bad_absorption p e own hown c J D a

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
universe u v w
variable {B : Type v} {β : Type w} [Fintype B] [Fintype β]

lemma roundSelectedBad_nonneg {ι : Type u} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (p : Law (ι→β)) (e : B×Fin m ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) : 0 ≤ roundSelectedBad p e own c J D a := by
  unfold roundSelectedBad
  positivity

theorem exposureSelectedBad_le (n k : ℕ) (J D a : ℝ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→β))
    (e : B×Fin (n+k) ↪ ι) (own : ι→Option B)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k) :
    (n:ℝ)*exposureSelectedBad n J D a k p e own t≤exposureBad n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · change (n:ℝ)*roundSelectedBad p e own (fun _ _ => 0) J D a≤
        roundBad p e own (fun _ _ => 0) J D a
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (show n≤n+(k+1) by omega))
        (roundSelectedBad_nonneg p e own _ J D a)).trans (roundSelectedBad_le p e own hown _ J D a)
    · change (n:ℝ)*((∑ f : B→Fin (n+k+1),∑ z,
          (p.restrict (freshRepresentatives e f)).mass z *
            exposureSelectedBad n J D a k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ)
              (remainingEmbedding e f) (fun i => own i) j)/_)≤_
      rw [←mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [mul_sum]
      apply sum_le_sum
      intro f _
      rw [mul_sum]
      apply sum_le_sum
      intro z _
      rw [mul_left_comm]
      apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
      exact ih _ (remainingEmbedding e f) (fun i => own i)
        (fun b x => remaining_own e f own hown b x) j

theorem exposureBad_budget (n k : ℕ) (J D a : ℝ) (hD : 0<D) (ha : 0<a)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→β))
    (e : B×Fin (n+k) ↪ ι) (own : ι→Option B) (S : ι→Finset β)
    (hS : tupleSupported p S) (hJ : ∀ i,Real.log (S i).card≤J) (t : Fin k) :
    exposureBad n J D a k p e own t≤
      exposureDeficits n J k p e t/D+exposureScores n k p e own t/a := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · change roundBad p e own (fun _ _ => 0) J D a≤tupleDeficit J p/D+roundInformation p e own/a
      simpa only [NNReal.coe_zero,sum_const_zero,zero_div,add_zero] using
        roundBad_le (by omega : 0<n+(k+1)) p e own (fun _ _ => 0) J D a hD ha
          (tupleSupported_marginal_cap p S hS J hJ)
    · change (∑ f : B→Fin (n+k+1),∑ z,
          (p.restrict (freshRepresentatives e f)).mass z *
            exposureBad n J D a k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ)
              (remainingEmbedding e f) (fun i => own i) j)/_≤_
      calc
        _ ≤ (∑ f : B→Fin (n+k+1),∑ z,
            (p.restrict (freshRepresentatives e f)).mass z *
            (exposureDeficits n J k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) j/D+
             exposureScores n k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) (fun i => own i) j/a)) /
                Fintype.card (B→Fin (n+k+1)) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply sum_le_sum
          intro f _
          apply sum_le_sum
          intro z _
          by_cases hz : (p.restrict (freshRepresentatives e f)).mass z=0
          · rw [hz,zero_mul,zero_mul]
          · apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
            exact ih _ (remainingEmbedding e f) (fun i => own i) (fun i => S i)
              (tupleSupported_cond_restrict p S hS _ z hz) (fun i => hJ i) j
        _ = _ := by
          rw [exposureDeficits_succ,exposureScores_succ]
          simp only [mul_add,←mul_div_assoc,sum_add_distrib,←sum_div,add_div]
          ring

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureContexts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
universe u v w z
variable {Θ : Type z} {C : Type v} {β : Type w} {ι : Type u}
variable [Fintype Θ] [Fintype C] [Fintype β] [Fintype ι] [DecidableEq ι]

lemma contextAverage_mono (μ : Law Θ) {f g : Θ→ℝ}
    (h : ∀ θ,μ.mass θ≠0 → f θ≤g θ) : contextAverage μ f ≤ contextAverage μ g := by
  apply sum_le_sum
  intro θ _
  by_cases hθ : μ.mass θ=0
  · simp only [hθ,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h θ hθ) (μ.nonneg θ)

lemma contextAverage_add (μ : Law Θ) (f g : Θ→ℝ) :
    contextAverage μ (fun θ => f θ+g θ)=contextAverage μ f+contextAverage μ g := by
  simp only [contextAverage,mul_add,sum_add_distrib]

lemma contextAverage_div (μ : Law Θ) (f : Θ→ℝ) (a : ℝ) :
    contextAverage μ (fun θ => f θ/a)=contextAverage μ f/a := by
  simp only [contextAverage,←mul_div_assoc,←sum_div]

lemma contextAverage_mul (μ : Law Θ) (f : Θ→ℝ) (a : ℝ) :
    contextAverage μ (fun θ => a*f θ)=a*contextAverage μ f := by
  simp only [contextAverage,mul_left_comm,←mul_sum]

lemma contextScores_sum (n k : ℕ) (hn : 2≤n) (μ : Law Θ)
    (p : Θ→Law (ι→β)) (e : Θ→C×Fin (n+k) ↪ ι) (own : Θ→ι→Option C)
    (hown : ∀ θ b x,own θ (e θ (b,x))=some b) :
    ∑ t : Fin k,contextAverage μ (fun θ => exposureScores n k (p θ) (e θ) (own θ) t) ≤
      2*contextAverage μ (fun θ => totalCorrelation (p θ)) := by
  simp only [contextAverage]
  rw [sum_comm]
  simp only [←mul_sum]
  rw [mul_sum]
  apply sum_le_sum
  intro θ _
  calc
    _ ≤ μ.mass θ*(2*totalCorrelation (p θ)) :=
      mul_le_mul_of_nonneg_left (exposureScores_sum_le n k hn (p θ) (e θ) (own θ) (hown θ)) (μ.nonneg θ)
    _ = _ := by ring

lemma exists_context_round (n k : ℕ) (hn : 2≤n) (hk : 0<k) (μ : Law Θ)
    (p : Θ→Law (ι→β)) (e : Θ→C×Fin (n+k) ↪ ι) (own : Θ→ι→Option C)
    (hown : ∀ θ b x,own θ (e θ (b,x))=some b) :
    ∃ t : Fin k,
      contextAverage μ (fun θ => exposureScores n k (p θ) (e θ) (own θ) t) ≤
        2*contextAverage μ (fun θ => totalCorrelation (p θ))/(k:ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hconst : (∑ _t : Fin k,
      2*contextAverage μ (fun θ => totalCorrelation (p θ))/(k:ℝ)) =
      2*contextAverage μ (fun θ => totalCorrelation (p θ)) := by
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  obtain ⟨t,_,ht⟩ := exists_le_of_sum_le (univ_nonempty : (univ : Finset (Fin k)).Nonempty)
    ((contextScores_sum n k hn μ p e own hown).trans_eq hconst.symm)
  exact ⟨t,ht⟩

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_EndpointCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.event_mono (p : Law α) {E F : Finset α} (h : E ⊆ F) : p.event E ≤ p.event F :=
  sum_le_sum_of_subset_of_nonneg h (fun x _ _ => p.nonneg x)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_AuxiliaryLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped Classical BigOperators

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.onEvent_mean (p : Law α) (E : Finset α) (hE : 0<p.event E) (f : α→ℝ) :
    ∑ a : E, (p.onEvent E hE).mass a*f a = (∑ a∈E, p.mass a*f a)/p.event E := by
  simp only [Law.onEvent,div_mul_eq_mul_div,←sum_div]
  congr 1
  exact sum_coe_sort E (fun a => p.mass a*f a)

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection SharpLogRamsey.MomentBudgetBridge

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

end SharpLogRamsey.SourceScales
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TailSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.HighRankExcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K] in
lemma geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

end
end SharpLogRamsey.HighRankExcess
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_AtomEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.SimultaneousExtraction
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

lemma markov_complement (p : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (ht : ∑ z, p z=1)
    (f g : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    1-(∑ z, p z*f z)/A-(∑ z, p z*g z)/B ≤
      ∑ z ∈ univ.filter (fun z => f z ≤ A ∧ g z ≤ B), p z := by
  have H (z : Ω) : p z*(1-f z/A-g z/B) ≤
      if f z ≤ A ∧ g z ≤ B then p z else 0 := by
    by_cases h : f z ≤ A ∧ g z ≤ B
    · rw [ite_eq_left h]
      have h0 : 0 ≤ f z/A := div_nonneg (hf z) hA.le
      have h1 : 0 ≤ g z/B := div_nonneg (hg z) hB.le
      nlinarith [hp z]
    · rw [ite_eq_right h]
      have he : 1 ≤ f z/A+g z/B := by
        by_cases he : f z ≤ A
        · have hh : B < g z := lt_of_not_ge (fun hh => h ⟨he,hh⟩)
          have hh' : 1 ≤ g z/B := (one_le_div hB).mpr hh.le
          linarith [div_nonneg (hf z) hA.le]
        · have hh' : 1 ≤ f z/A := (one_le_div hA).mpr (le_of_not_ge he)
          linarith [div_nonneg (hg z) hB.le]
      exact mul_nonpos_of_nonneg_of_nonpos (hp z) (by linarith)
  have HH := sum_le_sum (fun z (_ : z∈univ) => H z)
  simpa only [sum_filter, mul_sub, mul_one, mul_div_assoc, sum_sub_distrib,
    sum_div, ht] using HH

theorem simultaneous_mass (p : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (ht : ∑ z, p z=1)
    (f g : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (E S A B : ℝ) (hA : 0<A) (hB : 0<B)
    (hE : ∑ z, p z*f z ≤ E) (hS : ∑ z, p z*g z ≤ S) :
    1-E/A-S/B ≤ ∑ z ∈ univ.filter (fun z => f z ≤ A ∧ g z ≤ B), p z := by
  have H := markov_complement p hp ht f g hf hg A B hA hB
  have H₁ := div_le_div_of_nonneg_right hE hA.le
  have H₂ := div_le_div_of_nonneg_right hS hB.le
  linarith

end
end SharpLogRamsey.SimultaneousExtraction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodRows
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

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]

lemma Law.onEvent_mean_le_two (p : Law X) (E : Finset X) (hE : (1:ℝ)/2≤p.event E)
    (f : X→ℝ) (hf : ∀ x,0≤f x) :
    ∑ x : E,(p.onEvent E (by linarith)).mass x*f x≤2*∑ x,p.mass x*f x := by
  rw [p.onEvent_mean]
  apply (div_le_iff₀ (by linarith : 0<p.event E)).mpr
  have hn : 0≤∑ x,p.mass x*f x := sum_nonneg (fun x _=>mul_nonneg (p.nonneg x) (hf x))
  calc
    _ ≤ ∑ x,p.mass x*f x := sum_le_univ_sum_of_nonneg (fun x=>mul_nonneg (p.nonneg x) (hf x))
    _ ≤ _ := by nlinarith

end
end SharpLogRamsey.Selection

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

lemma raw_rows_entropy {F Ω : Type*} [Fintype F] [Fintype Ω] (h : ℕ)
    (p : Law Ω) (code : Ω→(Fin h→F)×(Fin h→F)) :
    entropy (p.map code)≤2*(h:ℝ)*log (Fintype.card F) := by
  have hh:=entropy_le_log_card (p.map code) univ (by simp)
  simp only [card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Nat.cast_mul,Nat.cast_pow] at hh
  rw [←pow_two,log_pow,log_pow] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_HighRankEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section
variable {K V Ω : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype Ω]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_bound {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (Fintype.card (Projectivization K V):ℝ)≤2*(Nat.card K:ℝ)^d := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  simp only [Nat.cast_pow]
  exact HighRankExcess.geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)) d

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_positive {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (0:ℝ)<Fintype.card (Projectivization K V) := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  apply lt_of_lt_of_le (by norm_num : (0:ℝ)<(Nat.card K^0:ℕ))
  exact single_le_sum (fun i _=>Nat.cast_nonneg _) (mem_range.mpr (by omega))

omit [FiniteDimensional K V] in
lemma flag_card_log {d : ℕ} (hdim : Module.finrank K V=d+1) :
    log (Fintype.card (Projectivization K (Module.Dual K V)×Projectivization K V))≤
      2*(log 2+(d:ℝ)*log (Nat.card K)) := by
  have hdual : Module.finrank K (Module.Dual K V)=d+1 := by rw [Subspace.dual_finrank_eq,hdim]
  have ha:=projective_card_bound hdual
  have hb:=projective_card_bound hdim
  have hap:=projective_card_positive hdual
  have hbp:=projective_card_positive hdim
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  simp only [Fintype.card_prod,Nat.cast_mul]
  apply (log_le_log (mul_pos hap hbp)
    (mul_le_mul ha hb hbp.le (by positivity))).trans
  rw [←pow_two,log_pow,log_mul (by norm_num) (pow_ne_zero _ hq.ne'),log_pow]
  rfl

omit [FiniteDimensional K V] in
theorem raw_entropy {d h : ℕ} (hdim : Module.finrank K V=d+1)
    (p : Law Ω)
    (code : Ω→(Fin h→Projectivization K (Module.Dual K V)×Projectivization K V)×
      (Fin h→Projectivization K (Module.Dual K V)×Projectivization K V)) :
    entropy (p.map code)≤4*(h:ℝ)*(log 2+(d:ℝ)*log (Nat.card K)) := by
  apply (raw_rows_entropy h p code).trans
  have hh:=mul_le_mul_of_nonneg_left (flag_card_log hdim) (by positivity : 0≤2*(h:ℝ))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_ExposureScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma rpow_ratio (x : ℝ) (hx : 0<x) (a b : ℝ) : x^a/x^b=x^(a-b) := by
  rw [rpow_sub hx]

theorem eventually_integer_bad_small (η C c ε : ℝ)
    (hη : 0<η) (hC : 0≤C) (hc : 0 < c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D N budget M n k : ℝ,
      0<q → 0<D → 0≤N → budget≤C*N*D*σ^(-beta η) → M≤C*σ →
      c*q*D*σ^(3000*beta η)≤k → c*q*σ^(1+η/2)≤n →
      let a:=σ^(-2000*beta η)/q
      budget/(D*σ^beta η)+2*budget/(k*a)+4*N*M/(n*a)≤N*ε := by
  have hb:=beta_pos hη
  have hexp : 2000*beta η-η/2<0 := by dsimp [beta]; linarith
  have h1 : Tendsto (fun σ : ℝ=>C*σ^(-2*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (by positivity : 0<2*beta η)).const_mul C
  have h2 : Tendsto (fun σ : ℝ=>(2*C/c)*σ^(-1001*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (by positivity : 0<1001*beta η)).const_mul (2*C/c)
  have h3 : Tendsto (fun σ : ℝ=>(4*C/c)*σ^(2000*beta η-η/2)) atTop (𝓝 0) := by
    simpa only [mul_zero,neg_neg] using (tendsto_rpow_neg_atTop (neg_pos.mpr hexp)).const_mul (4*C/c)
  have ht := (h1.add h2).add h3
  simp only [add_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℝ)] with σ hsmall hσ
  intro q D N budget M n k hq hD hN hbudget hM hk hn
  dsimp only
  let a:=σ^(-2000*beta η)/q
  have ha : 0<a := div_pos (rpow_pos_of_pos hσ _) hq
  have hka : c*D*σ^(1000*beta η)≤k*a := by
    have hh:=mul_le_mul_of_nonneg_right hk ha.le
    have he : (c*q*D*σ^(3000*beta η))*a=c*D*σ^(1000*beta η) := by
      dsimp [a]
      have hr : σ^(3000*beta η)*σ^(-2000*beta η)=σ^(1000*beta η) := by
        rw [←rpow_add hσ]; congr 1; ring
      calc
        _ = c*D*(σ^(3000*beta η)*σ^(-2000*beta η)) := by field_simp
        _ = _ := by rw [hr]
    rwa [he] at hh
  have hna : c*σ^(1+η/2-2000*beta η)≤n*a := by
    have hh:=mul_le_mul_of_nonneg_right hn ha.le
    have he : (c*q*σ^(1+η/2))*a=c*σ^(1+η/2-2000*beta η) := by
      dsimp [a]
      have hr : σ^(1+η/2)*σ^(-2000*beta η)=σ^(1+η/2-2000*beta η) := by
        rw [←rpow_add hσ]; congr 1; ring
      calc
        _ = c*(σ^(1+η/2)*σ^(-2000*beta η)) := by field_simp
        _ = _ := by rw [hr]
    rwa [he] at hh
  have hb0 : 0≤C*N*D*σ^(-beta η) := by positivity
  have hd0 : 0<D*σ^beta η := by positivity
  have hk0 : 0 < c*D*σ^(1000*beta η) := by positivity
  have hn0 : 0 < c*σ^(1+η/2-2000*beta η) := by positivity
  have hbnd1 : budget/(D*σ^beta η)≤N*(C*σ^(-2*beta η)) := by
    calc
      _ ≤ (C*N*D*σ^(-beta η))/(D*σ^beta η) := div_le_div_of_nonneg_right hbudget hd0.le
      _ = C*N*(σ^(-beta η)/σ^beta η) := by field_simp
      _ = _ := by
        rw [rpow_ratio σ hσ, show -beta η-beta η = -2*beta η by ring]
        ring
  have hbnd2 : 2*budget/(k*a)≤N*((2*C/c)*σ^(-1001*beta η)) := by
    calc
      _ ≤ (2*(C*N*D*σ^(-beta η)))/(k*a) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget (by norm_num)) (hk0.le.trans hka)
      _ ≤ (2*(C*N*D*σ^(-beta η)))/(c*D*σ^(1000*beta η)) :=
        div_le_div_of_nonneg_left (by positivity) hk0 hka
      _ = N*(2*C/c)*(σ^(-beta η)/σ^(1000*beta η)) := by field_simp
      _ = _ := by
        rw [rpow_ratio σ hσ, show -beta η-1000*beta η = -1001*beta η by ring]
        ring
  have hbnd3 : 4*N*M/(n*a)≤N*((4*C/c)*σ^(2000*beta η-η/2)) := by
    calc
      _ ≤ (4*N*(C*σ))/(n*a) := by
        apply div_le_div_of_nonneg_right _ (hn0.le.trans hna)
        gcongr
      _ ≤ (4*N*(C*σ))/(c*σ^(1+η/2-2000*beta η)) :=
        div_le_div_of_nonneg_left (by positivity) hn0 hna
      _ = N*(4*C/c)*(σ^(1:ℝ)/σ^(1+η/2-2000*beta η)) := by rw [rpow_one]; field_simp
      _ = _ := by
        rw [rpow_ratio σ hσ, show (1:ℝ)-(1+η/2-2000*beta η) = 2000*beta η-η/2 by ring]
        ring
  calc
    _ ≤ N*(C*σ^(-2*beta η))+N*((2*C/c)*σ^(-1001*beta η))+
        N*((4*C/c)*σ^(2000*beta η-η/2)) := add_le_add (add_le_add hbnd1 hbnd2) hbnd3
    _ = N*(C*σ^(-2*beta η)+(2*C/c)*σ^(-1001*beta η)+(4*C/c)*σ^(2000*beta η-η/2)) := by ring
    _ ≤ N*ε := mul_le_mul_of_nonneg_left hsmall.le hN
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_InformationScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

theorem eventually_information_bad_small (η C c ε : ℝ)
    (hη : 0<η) (hC : 0≤C) (hc : 0 < c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D N budget k : ℝ,
      0<q → 0<D → 0≤N → budget≤C*N*D*σ^(-beta η) →
      c*q*D*σ^(3000*beta η)≤k →
      let a:=σ^(-2000*beta η)/q
      budget/(D*σ^beta η)+2*budget/(k*a)≤N*ε := by
  filter_upwards [eventually_integer_bad_small η C c ε hη hC hc hε,
    eventually_ge_atTop (0:ℝ)] with σ h hσ
  intro q D N budget k hq hD hN hb hk
  have hh:=h q D N budget 0 (c*q*σ^(1+η/2)) k hq hD hN hb
    (mul_nonneg hC hσ) hk le_rfl
  simpa only [mul_zero,zero_div,add_zero] using hh
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureAverages
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
variable {β C : Type} [Fintype β] [Fintype C]

namespace ExposureModel
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype C] in
lemma initial_mean (p : Law (ι→β)) {m : ℕ} (e : C×Fin m↪ι) (own : ι→Option C)
    (F : StateStatistic β C) : (initial p e own).mean F=F ι m p e own := by
  change (∑ _z : Unit,(1/(Fintype.card Unit:ℝ))*F ι m p e own)=_
  simp

lemma join_mean {m : ℕ} (p : Law (ι→β)) (e : C×Fin (m+1)↪ι)
    (child : ∀ f : C→Fin (m+1), (freshRepresentatives e f→β)→
      ExposureModel ↥((freshRepresentatives e f)ᶜ) β C)
    (F : StateStatistic β C) :
    (join p e child).mean F=(∑ f : C→Fin (m+1),∑ z,
      (p.restrict (freshRepresentatives e f)).mass z*(child f z).mean F)/
        Fintype.card (C→Fin (m+1)) := by
  unfold mean
  change (∑ h,((Law.equiprobable (C→Fin (m+1))).sigma (fun f=>
    (p.restrict (freshRepresentatives e f)).sigma (fun z=>(child f z).historyLaw))).mass h*
      F ((child h.1 h.2.1).Index h.2.2) ((child h.1 h.2.1).remaining h.2.2)
        ((child h.1 h.2.1).tupleLaw h.2.2) ((child h.1 h.2.1).embedding h.2.2)
          ((child h.1 h.2.1).owner h.2.2))=_
  rw [Law.sigma_sum]
  simp_rw [Law.sigma_sum]
  exact Law.equiprobable_sum _ _

end ExposureModel

theorem ExposureModel.atRound_mean (F : StateStatistic β C) (n k : ℕ)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    (atRound n k p e own t).mean F=exposureAverage F n k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · exact initial_mean p e own F
    · change (join p e _).mean F=_
      rw [join_mean]
      simp_rw [ih]
      rfl

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureMixture
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
variable {β C ι Θ : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ]
namespace ExposureModel

omit [Fintype C] [Fintype ι] [DecidableEq ι] in
lemma mix_expectation (ν : Law Θ) (M : Θ→ExposureModel ι β C) (φ : (ι→β)→ℝ) :
    (mix ν M).expectation φ=∑ z,ν.mass z*(M z).expectation φ := by
  exact ν.sigma_sum (fun z=>(M z).historyLaw) _

omit [Fintype C] [Fintype ι] [DecidableEq ι] in
lemma mix_mean (ν : Law Θ) (M : Θ→ExposureModel ι β C) (F : StateStatistic β C) :
    (mix ν M).mean F=∑ z,ν.mass z*(M z).mean F := by
  exact ν.sigma_sum (fun z=>(M z).historyLaw) _

omit [Fintype C] [Fintype ι] [DecidableEq ι] in
lemma joint_expectation (M : ExposureModel ι β C) (φ : (ι→β)→ℝ) :
    (∑ x,M.joint.mass x*φ (M.restore x.1 x.2))=M.expectation φ :=
  M.historyLaw.sigma_sum _ _

omit [Fintype C] in
lemma restored_map (M : ExposureModel ι β C) (p : Law (ι→β))
    (h : ∀ φ,M.expectation φ=∑ x,p.mass x*φ x) :
    M.joint.map (fun x=>M.restore x.1 x.2)=p := by
  ext y
  have he := (M.joint_expectation (fun x=>if x=y then 1 else 0)).trans
    (h (fun x=>if x=y then 1 else 0))
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',mem_univ,ite_true] using he

theorem contextual_preserves (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (φ : (ι→β)→ℝ) :
    (contextual n k p θ G e own t).expectation φ=∑ ω,p.mass ω*φ (G ω) := by
  rw [contextual,mix_expectation]
  simp_rw [atRound_preserves]
  have hm (z : Θ) : (∑ x,((p.cond θ z).map G).mass x*φ x)=
      ∑ ω,(p.cond θ z).mass ω*φ (G ω) := Law.sum_map _ _ _
  simp_rw [hm]
  exact p.history_sum θ _

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_DominatedCoupling
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

theorem Law.attach_source_le (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (c : ℝ) (h : ∀ b,(q.map f).mass b ≤ c*(μ.map g).mass b)
    (φ : Ω→ℝ) (hφ : ∀ ω,0≤φ ω) :
    (∑ x,(q.attach μ f g).mass x*φ x.2) ≤ c*∑ ω,μ.mass ω*φ ω := by
  rw [Law.attach,Law.sigma_sum]
  change (∑ x,q.mass x*(fun b=>∑ ω,(μ.cond g b).mass ω*φ ω) (f x))≤_
  rw [←q.sum_map f (fun b=>∑ ω,(μ.cond g b).mass ω*φ ω)]
  calc
    _ ≤ ∑ b,c*(μ.map g).mass b*∑ ω,(μ.cond g b).mass ω*φ ω := by
      apply sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_right (h b)
        (sum_nonneg (fun ω _=>mul_nonneg ((μ.cond g b).nonneg ω) (hφ ω)))
    _ = c*∑ ω,μ.mass ω*φ ω := by
      simp_rw [mul_assoc]
      rw [←mul_sum,μ.history_sum]

lemma Law.attach_support_of_dominated (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (c : ℝ) (h : ∀ b,(q.map f).mass b ≤ c*(μ.map g).mass b)
    (x : Σ _x : X,Ω) (hx : (q.attach μ f g).mass x≠0) :
    q.mass x.1≠0 ∧ μ.mass x.2≠0 ∧ g x.2=f x.1 := by
  have hx' : q.mass x.1≠0 ∧ (μ.cond g (f x.1)).mass x.2≠0 := mul_ne_zero_iff.mp hx
  have hf : (μ.map g).mass (f x.1)≠0 := by
    intro he
    have hh:=h (f x.1)
    rw [he,mul_zero] at hh
    have hp : 0<q.mass x.1 := lt_of_le_of_ne (q.nonneg x.1) (Ne.symm hx'.1)
    exact (not_lt_of_ge hh) (hp.trans_le (q.le_map f x.1))
  exact ⟨hx'.1,μ.cond_support g (f x.1) hf x.2 hx'.2⟩

lemma Law.attach_map_source_le (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (c : ℝ) (h : ∀ b,(q.map f).mass b ≤ c*(μ.map g).mass b) (ω : Ω) :
    ((q.attach μ f g).map (fun x=>x.2)).mass ω ≤ c*μ.mass ω := by
  have hh:=q.attach_source_le μ f g c h (fun x=>if x=ω then 1 else 0) (by intro x; positivity)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true] using hh
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_DominatedMixture
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
variable {Z B : Type} [Fintype Z] [Fintype B]

lemma Law.event_nonzero_filter (μ : Law Z) (H : Finset Z) :
    μ.event (H.filter (fun z=>μ.mass z≠0))=μ.event H := by
  unfold Law.event
  rw [sum_filter]
  apply sum_congr rfl
  intro z hz
  split_ifs with h
  · rfl
  · exact (not_not.mp h).symm

lemma Law.dominated_observable {X Y : Type} [Fintype X] [Fintype Y]
    (p : Law X) (q : Law Y) (f : X→Y) (c : ℝ)
    (h : ∀ y,(p.map f).mass y ≤ c*q.mass y) (g : Y→ℝ) (hg : ∀ y,0≤g y) :
    (∑ x,p.mass x*g (f x)) ≤ c*∑ y,q.mass y*g y := by
  rw [←p.sum_map f g,mul_sum]
  apply sum_le_sum
  intro y _
  exact (mul_le_mul_of_nonneg_right (h y) (hg y)).trans_eq (mul_assoc _ _ _)

omit [Fintype B] in

theorem Law.dominated_history_mixture (μ : Law Z) (H : Finset Z)
    (hH : (1:ℝ)/2≤μ.event H) (Q : Z→Type) [∀ z,Fintype (Q z)] (q : ∀ z,Law (Q z))
    (X : H→Type) [∀ z,Fintype (X z)] (ν : ∀ z,Law (X z))
    (f : ∀ z,X z→Q z.val) (c : ℝ) (hc : 0 ≤ c)
    (hd : ∀ z y,((ν z).map (f z)).mass y ≤ c*(q z.val).mass y)
    (restore : ∀ z,Q z→B) (φ : B→ℝ) (hφ : ∀ b,0≤φ b) :
    (∑ x,((μ.onEvent H (by linarith)).sigma ν).mass x*
      φ (restore x.1.val (f x.1 x.2)))≤(2*c)*
        ∑ y,(μ.sigma q).mass y*φ (restore y.1 y.2) := by
  rw [Law.sigma_sum,Law.sigma_sum]
  calc
    _ ≤ ∑ z : H,(μ.onEvent H (by linarith)).mass z*
        (c*∑ y,(q z.val).mass y*φ (restore z.val y)) := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ ((μ.onEvent H (by linarith)).nonneg z)
      exact (ν z).dominated_observable (q z.val) (f z) c (hd z)
        (fun y=>φ (restore z.val y)) (fun y=>hφ _)
    _ = c*∑ z : H,(μ.onEvent H (by linarith)).mass z*
        (∑ y,(q z.val).mass y*φ (restore z.val y)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z _
      ring
    _ ≤ c*(2*∑ z,μ.mass z*∑ y,(q z).mass y*φ (restore z y)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact μ.onEvent_mean_le_two H hH (fun z=>∑ y,(q z).mass y*φ (restore z y))
        (fun z=>sum_nonneg (fun y _=>mul_nonneg ((q z).nonneg y) (hφ _)))
    _ = _ := by ring

lemma Law.dominated_history_map (μ : Law Z) (H : Finset Z)
    (hH : (1:ℝ)/2≤μ.event H) (Q : Z→Type) [∀ z,Fintype (Q z)] (q : ∀ z,Law (Q z))
    (X : H→Type) [∀ z,Fintype (X z)] (ν : ∀ z,Law (X z))
    (f : ∀ z,X z→Q z.val) (c : ℝ) (hc : 0 ≤ c)
    (hd : ∀ z y,((ν z).map (f z)).mass y ≤ c*(q z.val).mass y)
    (restore : ∀ z,Q z→B) (b : B) :
    (((μ.onEvent H (by linarith)).sigma ν).map
      (fun x=>restore x.1.val (f x.1 x.2))).mass b≤
        (2*c)*((μ.sigma q).map (fun y=>restore y.1 y.2)).mass b := by
  have hh:=μ.dominated_history_mixture H hH Q q X ν f c hc hd restore
    (fun y=>if y=b then 1 else 0) (by intro y; positivity)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using hh
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FreshRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {β C ι : Type} [Fintype β] [Fintype C] [Fintype ι] [DecidableEq ι]
namespace ExposureModel

omit [Fintype ι] [DecidableEq ι] in
lemma afterDraw_preserves (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z)
    (φ : (ι→β)→ℝ) : (M.afterDraw h).expectation φ=M.expectation φ :=
  M.freshLaw_old h (fun z=>∑ x,(M.tupleLaw z).mass x*φ (M.restore z x))

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_WindowDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section
variable {W ι X : Type*} [Fintype W] [Fintype ι] [Fintype X]

omit [Fintype W] [Fintype ι] in
lemma goodTargets_card (target : W×X↪ι) (keep : Finset W) (bad : Finset ι) :
    (keep.card*Fintype.card X)≤(goodTargets target keep bad).card+bad.card := by
  have hsub : ((keep×ˢ(univ:Finset X)).map target) ⊆
      goodTargets target keep bad ∪ bad := by
    intro i hi
    by_cases hb : i∈bad
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hi,hb⟩)
  have h:=card_le_card hsub
  have hh : ((keep×ˢ(univ:Finset X)).map target).card≤
      (goodTargets target keep bad).card+bad.card := by
    simpa only [goodTargets,add_comm] using h.trans (card_union_le _ _)
  simpa only [card_map,card_product,card_univ] using hh

omit [Fintype ι] in
lemma goodTargets_loss (target : W×X↪ι) (lost : Finset W) (bad : Finset ι) :
    Fintype.card W*Fintype.card X≤
      (goodTargets target (univ\lost) bad).card+bad.card+lost.card*Fintype.card X := by
  have h:=goodTargets_card target (univ\lost) bad
  have hc : (univ\lost).card+lost.card=Fintype.card W := by
    simpa using card_sdiff_add_card_eq_card (subset_univ lost)
  nlinarith

end
end SharpLogRamsey.Selection.Windows

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

lemma representative_selected [Fintype C] (M : ExposureModel ι β C) (x : M.FreshHistory) :
    univ.map (M.representative x)=M.freshSelected x := by
  ext i
  simp only [mem_map,mem_univ,true_and,freshSelected,freshRepresentatives,mem_image]
  rfl

end ExposureModel

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

lemma goodMiddle_card (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (live : Finset (Fin w)) :
    (∑ i∈live,(goodMiddle w n k p θ G t z bad i).card)=
      (goodTargets (target w n k p θ G t z.1) live bad).card := by
  rw [←card_sigma]
  apply card_bij (fun a _=>target w n k p θ G t z.1 (a.1,a.2))
  · intro a ha
    obtain ⟨hi,hx⟩:=mem_sigma.mp ha
    exact mem_sdiff.mpr ⟨mem_map.mpr ⟨(a.1,a.2),mem_product.mpr ⟨hi,mem_univ _⟩,rfl⟩,
      (mem_filter.mp hx).2⟩
  · intro a ha b hb he
    have hh:=(target w n k p θ G t z.1).injective he
    exact Sigma.ext (congrArg Prod.fst hh) (heq_of_eq (congrArg Prod.snd hh))
  · intro a ha
    obtain ⟨ha,hb⟩:=mem_sdiff.mp ha
    obtain ⟨⟨i,x⟩,hx,rfl⟩:=mem_map.mp ha
    exact ⟨⟨i,x⟩,mem_sigma.mpr ⟨(mem_product.mp hx).1,mem_filter.mpr ⟨mem_univ _,hb⟩⟩,rfl⟩

lemma goodPopulation_predeletion (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (lost : Finset (Fin w)) :
    w*(2*(n+k))≤(∑ i∈univ\lost,(goodMiddle w n k p θ G t z bad i).card)+
      bad.card+lost.card*(2*(n+k)) := by
  rw [goodMiddle_card]
  simpa only [Fintype.card_fin] using goodTargets_loss (target w n k p θ G t z.1) lost bad

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_HighRankMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section

attribute [instance] StreamReplacement.finiteX

variable {Ω F ι Γ Z : Type} [Fintype Ω] [Fintype F] [Fintype ι] [Fintype Γ] [Fintype Z]

omit [Fintype ι] in

theorem mix_stream_replacement [Fintype (ι→F)]
    (p : Law Ω) (G : Ω→ι→F) (pos : ι→ℕ)
    (μ : Law Z) (Q : Z→Type) [∀ z,Fintype (Q z)] (q : ∀ z,Law (Q z))
    (restore : ∀ z,Q z→ι→F)
    (hrestore : (μ.sigma q).map (fun z=>restore z.1 z.2)=p.map G)
    (H : Finset Z) (hH : (1:ℝ)/2≤μ.event H)
    (ℓ : H→ℕ) (target : ∀ z,Q z.val→Fin (ℓ z)→F)
    (loc : ∀ z,Fin (ℓ z)→ι)
    (hloc : ∀ z,StrictMono (fun i=>pos (loc z i)))
    (hvalue : ∀ z y i,restore z.val y (loc z i)=target z y i)
    (m : ℕ) (hm : ∀ z,m≤ℓ z/2) (DD : Γ→Finset F) (B C : ℝ)
    (e : ∀ z,Replacement (q z.val) (target z) DD B C)
    (hcost : ∀ (Y : Type) [Fintype Y] (ν : Law Y) (msg : Y→Γ),entropy (ν.map msg)≤C) :
    Nonempty (StreamReplacement p G pos m DD B C) := by
  let X : H→Type:=fun z=>(e z).Ω
  let ν : ∀ z,Law (X z):=fun z=>(e z).μ
  let f : ∀ z,X z→Q z.val:=fun z=>(e z).source
  let ρ:=(μ.onEvent H (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hH)).sigma ν
  let F0:=fun x : Σ z : H,X z=>restore x.1.val (f x.1 x.2)
  have hd : ∀ y,(ρ.map F0).mass y≤4*(p.map G).mass y := by
    intro y
    have hh:=μ.dominated_history_map H hH Q q X ν f 2 (by norm_num)
      (fun z=>(e z).dominated) restore y
    rw [hrestore] at hh
    simpa only [show (2:ℝ)*2=4 by norm_num] using hh
  let τ:=ρ.attach p F0 G
  let msg:=fun x : Σ _x : (Σ z : H,X z),Ω=>(e x.1.1).msg x.1.2
  let idx:=fun x : Σ _x : (Σ z : H,X z),Ω=>fun i : Fin m=>
    loc x.1.1 ((e x.1.1).chosen x.1.2 (Fin.castLE (hm x.1.1) i))
  refine ⟨⟨_,inferInstance,τ,(fun x=>x.2),msg,idx,?_,?_,?_,?_,?_,hcost _ τ msg⟩⟩
  · intro x i j hij
    exact hloc x.1.1 ((e x.1.1).chosen x.1.2|>.strictMono hij)
  · intro x hx
    exact (ρ.attach_support_of_dominated p F0 G 4 hd x hx).2.1
  · intro x hx i
    have hh:=ρ.attach_support_of_dominated p F0 G 4 hd x hx
    have he:=congrFun hh.2.2 (idx x i)
    rw [he]
    change restore x.1.1.val (f x.1.1 x.1.2)
      (loc x.1.1 ((e x.1.1).chosen x.1.2 (Fin.castLE (hm x.1.1) i)))∈_
    rw [hvalue]
    exact (e x.1.1).hit x.1.2 _
  · intro x
    exact (e x.1.1).size x.1.2
  · intro x
    exact ρ.attach_map_source_le p F0 G 4 hd x
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SourceZero
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
variable {Θ Ω B ι β : Type*} [Fintype Θ] [Fintype Ω] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype β]

omit [Fintype Ω] in

theorem exists_context_good_zero (n k : ℕ) (hn : 2≤n) (hk : 0<k)
    (J D a budget : ℝ) (hD : 0<D) (ha : 0<a)
    (μ : Law Θ) (p : Θ→Law (ι→β)) (e : Θ→B×Fin (n+k) ↪ ι)
    (own : Θ→ι→Option B) (hown : ∀ θ b x,own θ (e θ (b,x))=some b)
    (S : Θ→ι→Finset β)
    (hS : ∀ θ,μ.mass θ≠0→tupleSupported (p θ) (S θ))
    (hJ : ∀ θ i,Real.log (S θ i).card≤J)
    (hbudget : contextAverage μ (fun θ=>tupleDeficit J (p θ))≤budget) :
    ∃ t : Fin k,
      contextAverage μ (fun θ=>exposureBad n J D a k (p θ) (e θ) (own θ) t)≤
        budget/D+2*budget/((k:ℝ)*a) ∧
      (n:ℝ)*contextAverage μ (fun θ=>exposureSelectedBad n J D a k (p θ) (e θ) (own θ) t)≤
        budget/D+2*budget/((k:ℝ)*a) := by
  have hTC : contextAverage μ (fun θ=>totalCorrelation (p θ))≤budget := by
    apply le_trans _ hbudget
    apply contextAverage_mono μ
    intro θ hθ
    exact totalCorrelation_le_tupleDeficit (p θ) J
      (tupleSupported_marginal_cap (p θ) (S θ) (hS θ hθ) J (hJ θ))
  obtain ⟨t,ht⟩:=exists_context_round n k hn hk μ p e own hown
  have hbθ (θ : Θ) (hθ : μ.mass θ≠0) :
      exposureBad n J D a k (p θ) (e θ) (own θ) t≤
        tupleDeficit J (p θ)/D+exposureScores n k (p θ) (e θ) (own θ) t/a := by
    exact (exposureBad_budget n k J D a hD ha (p θ) (e θ) (own θ)
      (S θ) (hS θ hθ) (hJ θ) t).trans (by
        have hd:=exposureDeficits_le n k J (p θ) (e θ) (S θ) (hS θ hθ) (hJ θ) t
        gcongr)
  have hb:=contextAverage_mono μ hbθ
  simp only [contextAverage_add,contextAverage_div] at hb
  have hb' : contextAverage μ (fun θ=>exposureBad n J D a k (p θ) (e θ) (own θ) t)≤
      budget/D+2*budget/((k:ℝ)*a) := by
    calc
      _ ≤ _ := hb
      _ ≤ budget/D+(2*budget/(k:ℝ))/a :=
        add_le_add (div_le_div_of_nonneg_right hbudget hD.le)
          (div_le_div_of_nonneg_right
            (ht.trans (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hTC (by norm_num)) (Nat.cast_nonneg k))) ha.le)
      _ = _ := by rw [div_div]
  refine ⟨t,hb',le_trans ?_ hb'⟩
  rw [←contextAverage_mul]
  apply contextAverage_mono μ
  intro θ _
  exact exposureSelectedBad_le n k J D a (p θ) (e θ) (own θ) (hown θ) t

lemma conditional_tupleSupported (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (S : Θ→ι→Finset β)
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (z : Θ) (hz : (p.map θ).mass z≠0) :
    tupleSupported ((p.cond θ z).map G) (S z) := by
  intro f hf i
  obtain ⟨x,hx,rfl⟩ := (p.cond θ z).map_support G f hf
  obtain ⟨hx,he⟩:=p.cond_support θ z hz x hx
  simpa only [he] using hS x hx i

theorem actual_source_exposure (n k : ℕ) (hn : 2≤n) (hk : 0<k)
    (J D a budget : ℝ) (hD : 0<D) (ha : 0<a)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→B×Fin (n+k) ↪ ι) (own : Θ→ι→Option B)
    (hown : ∀ z b x,own z (e z (b,x))=some b)
    (S : Θ→ι→Finset β)
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (hJ : ∀ z i,Real.log (S z i).card≤J)
    (hbudget : (∑ z,(p.map θ).mass z*((Fintype.card ι:ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget) :
    ∃ t : Fin k,
      (∑ z,(p.map θ).mass z*exposureBad n J D a k
        ((p.cond θ z).map G) (e z) (own z) t)≤budget/D+2*budget/((k:ℝ)*a) ∧
      (n:ℝ)*(∑ z,(p.map θ).mass z*exposureSelectedBad n J D a k
        ((p.cond θ z).map G) (e z) (own z) t)≤budget/D+2*budget/((k:ℝ)*a) := by
  exact exists_context_good_zero n k hn hk J D a budget hD ha (p.map θ)
    (fun z=>(p.cond θ z).map G) e own hown S
    (conditional_tupleSupported p θ G S hS) hJ hbudget

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_StreamTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical
noncomputable section
variable {α Ω : Type} [Fintype α] [Fintype Ω]

omit [Fintype α] in
lemma singleTuple_injective (n : ℕ) : Function.Injective (singleTuple (α:=α) (n:=n)) := by
  intro F G h
  funext i
  exact congrFun h (0,i)

lemma single_position {n : ℕ} (i : Slot 1 n) : position i=i.2.val := by
  have h : i.1.val=0 := Fin.eq_zero i.1 ▸ rfl
  simp only [position,h,zero_mul,zero_add]

lemma single_entropy {n : ℕ} (p : Law Ω) (F : Ω→Fin (4*n)→α) :
    entropy (p.map (fun x=>singleTuple (F x)))=entropy (p.map F) := by
  rw [show (fun x=>singleTuple (F x))=singleTuple ∘ F from rfl,←Law.map_map]
  exact entropy_map_eq_of_injective _ _ (singleTuple_injective n)
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ZeroExposure
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
variable {β C : Type} [Fintype β] [Fintype C]

lemma exposureAverage_zero_bad (n k : ℕ) (J D a : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (p : Law (ι→β))
    (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    exposureAverage (zeroBadStatistic J D a) n k p e own t=exposureBad n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · rfl
    · change (∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        exposureAverage _ n k _ _ _ j)/_=_
      simp_rw [ih]
      rfl

lemma exposureAverage_zero_selected (n k : ℕ) (J D a : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (p : Law (ι→β))
    (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    exposureAverage (zeroSelectedStatistic J D a) n k p e own t=
      exposureSelectedBad n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · rfl
    · change (∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        exposureAverage _ n k _ _ _ j)/_=_
      simp_rw [ih]
      rfl

namespace ExposureModel
variable {ι Θ Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Θ] [Fintype Ω]

omit [Fintype ι] [DecidableEq ι] in
lemma fresh_zero_bad_mean (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z) (J D a : ℝ) :
    (∑ x,(M.freshLaw h).mass x*((M.freshBad (fun _ _ _=>0) J D a x).card:ℝ))=
      M.mean (zeroBadStatistic J D a) := by
  rw [freshLaw_sum]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma fresh_zero_selected_mean (M : ExposureModel ι β C) (h : ∀ z,0<M.remaining z) (J D a : ℝ) :
    (∑ x,(M.freshLaw h).mass x*((M.freshSelected x∩M.freshBad (fun _ _ _=>0) J D a x).card:ℝ))=
      M.mean (zeroSelectedStatistic J D a) := by
  rw [freshLaw_sum]
  rfl

lemma contextual_zero_bad_mean (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) (J D a : ℝ) :
    (contextual n k p θ G e own t).mean (zeroBadStatistic J D a)=
      ∑ z,(p.map θ).mass z*exposureBad n J D a k ((p.cond θ z).map G) (e z) (own z) t := by
  rw [contextual,mix_mean]
  simp_rw [atRound_mean,exposureAverage_zero_bad]

lemma contextual_zero_selected_mean (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) (J D a : ℝ) :
    (contextual n k p θ G e own t).mean (zeroSelectedStatistic J D a)=
      ∑ z,(p.map θ).mass z*exposureSelectedBad n J D a k ((p.cond θ z).map G) (e z) (own z) t := by
  rw [contextual,mix_mean]
  simp_rw [atRound_mean,exposureAverage_zero_selected]
end ExposureModel
open ExposureModel

variable {ι Θ Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Θ] [Fintype Ω]

theorem actual_realized_zero (n k : ℕ) (hn : 2≤n) (hk : 0<k)
    (J D a budget : ℝ) (hD : 0<D) (ha : 0<a)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C)
    (hown : ∀ z b x,own z (e z (b,x))=some b)
    (S : Θ→ι→Finset β)
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (hJ : ∀ z i,Real.log (S z i).card≤J)
    (hbudget : (∑ z,(p.map θ).mass z*((Fintype.card ι:ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget) :
    ∃ t : Fin k,
      let E:=contextual n k p θ G e own t
      let hp:=contextual_positive_general n k (by omega : 0<n) p θ G e own t
      let bad:=E.freshBad (fun _ _ _=>0) J D a
      (∑ x,(E.freshLaw hp).mass x*((bad x).card:ℝ))≤budget/D+2*budget/((k:ℝ)*a) ∧
      (n:ℝ)*(∑ x,(E.freshLaw hp).mass x*((E.freshSelected x∩bad x).card:ℝ))≤
        budget/D+2*budget/((k:ℝ)*a) ∧
      (E.afterDraw hp).joint.map (fun x=>(E.afterDraw hp).restore x.1 x.2)=p.map G := by
  obtain ⟨t,hb,hs⟩:=actual_source_exposure n k hn hk J D a budget hD ha
    p θ G e own hown S hS hJ hbudget
  refine ⟨t,?_,?_,?_⟩
  · rw [fresh_zero_bad_mean,contextual_zero_bad_mean]
    exact hb
  · rw [fresh_zero_selected_mean,contextual_zero_selected_mean]
    exact hs
  · apply restored_map
    intro φ
    rw [afterDraw_preserves,contextual_preserves,Law.sum_map]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Marking
open Finset Selection ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma covectorDomain_mem (D : Finset (ProjectivePair (K:=K) (V:=V)))
    (f : ProjectivePair (K:=K) (V:=V)) : f.swap ∈covectorDomain D ↔ f∈D := by
  simp [covectorDomain]

lemma covectorDomain_card (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).card=D.card := card_map _

lemma covectorDomain_first (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).image Prod.fst=D.image Prod.snd := by
  ext a
  simp [covectorDomain]

lemma covectorDomain_second (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).image Prod.snd=D.image Prod.fst := by
  ext a
  simp [covectorDomain]

lemma covectorTuple_consistent {N : ℕ} (F : Fin N→ProjectivePair (K:=K) (V:=V))
    [FiniteDimensional K V]
    (h : ScanConsistent ((List.ofFn F).map toScan)) :
    ∀ (i j : Fin N),i<j→(covectorTuple F i).1.rep (covectorTuple F j).2.rep=0→
      (covectorTuple F j).1.rep (covectorTuple F i).2.rep=0 := by
  rw [List.map_ofFn] at h
  exact List.pairwise_ofFn.mp h

lemma covectorTuple_flag {ι : Type*} (F : ι→ProjectivePair (K:=K) (V:=V))
    (h : ∀ i,Incidence.Incident (F i).1 (F i).2) (i : ι) :
    (covectorTuple F i).1.rep (covectorTuple F i).2.rep=0 := h i

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma covectorTuple_entropy (p : Law Ω)
    (F : Ω→ι→ProjectivePair (K:=K) (V:=V)) :
    entropy (p.map (fun x=>covectorTuple (F x)))=entropy (p.map F) := by
  rw [show (fun x=>covectorTuple (F x))=covectorTuple∘F from rfl,←Law.map_map]
  apply entropy_map_eq_of_injective
  intro f g he
  funext i
  exact Prod.swap_injective (congrFun he i)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighGoodHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighGoodHistory_1
lemma one_goodMiddle_count (n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→Slot 1 (n+k)→β) (t : Fin k)
    (z : (model 1 n k p θ G t).FreshHistory)
    (bad : Finset ((model 1 n k p θ G t).Index z.1)) :
    2*(n+k)≤(goodMiddle 1 n k p θ G t z bad 0).card+bad.card := by
  have h:=goodPopulation_predeletion 1 n k p θ G t z bad ∅
  simpa using h

theorem high_good_history_half (n k : ℕ) (hn : 0<n) (hkn : k≤n)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot 1 (n+k)→β) (t : Fin k)
    (hp : ∀ z,0<(model 1 n k p θ G t).remaining z)
    (bad : ∀ z : (model 1 n k p θ G t).FreshHistory,
      Finset ((model 1 n k p θ G t).Index z.1)) (A : ℝ)
    (hb : (∑ z,((model 1 n k p θ G t).freshLaw hp).mass z*((bad z).card:ℝ))≤A)
    (hs : (n:ℝ)*(∑ z,((model 1 n k p θ G t).freshLaw hp).mass z*
      (((model 1 n k p θ G t).freshSelected z∩bad z).card:ℝ))≤A)
    (hA : A≤(2*(n+k):ℕ)/20) :
    (1:ℝ)/2≤((model 1 n k p θ G t).freshLaw hp).event
      (univ.filter (fun z=>(model 1 n k p θ G t).representative z (0,false)∉bad z ∧
        ((2*(n+k):ℕ):ℝ)/2≤(goodMiddle 1 n k p θ G t z (bad z) 0).card)) := by
  let M:=model 1 n k p θ G t
  let μ:=M.freshLaw hp
  let N : ℕ:=2*(n+k)
  let f:=fun z : M.FreshHistory=>((bad z).card:ℝ)
  let g:=fun z : M.FreshHistory=>((M.freshSelected z∩bad z).card:ℝ)
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hN : (0:ℝ)<N := by dsimp [N]; positivity
  have hNn : (N:ℝ)≤4*n := by
    exact_mod_cast (by dsimp [N]; omega : N≤4*n)
  have hs' : (∑ z,μ.mass z*g z)≤A/n := by
    apply (le_div_iff₀ hn0).mpr
    simpa only [mul_comm] using hs
  have hprob:=SimultaneousExtraction.simultaneous_mass μ.mass μ.nonneg μ.total f g
    (fun z=>Nat.cast_nonneg _) (fun z=>Nat.cast_nonneg _) A (A/n) ((N:ℝ)/2) (1/2)
    (by positivity) (by norm_num) hb hs'
  have hA0 : 0≤A := (sum_nonneg (fun z _=>mul_nonneg (μ.nonneg z) (by positivity))).trans hb
  have hleft : (1:ℝ)/2≤1-A/((N:ℝ)/2)-(A/n)/(1/2) := by
    have h1 : A/((N:ℝ)/2)≤1/10 := by
      apply (div_le_iff₀ (by positivity : 0<(N:ℝ)/2)).mpr
      change A≤(N:ℝ)/20 at hA
      linarith
    have h2 : (A/n)/(1/2)≤2/5 := by
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<1/2)).mpr
      apply (div_le_iff₀ hn0).mpr
      change A≤(N:ℝ)/20 at hA
      linarith
    linarith
  apply (hleft.trans hprob).trans
  apply Law.event_mono
  intro z hz
  obtain ⟨hf,hg⟩:=(mem_filter.mp hz).2
  have hg0 : (M.freshSelected z∩bad z).card=0 := by
    have hlt : ((M.freshSelected z∩bad z).card:ℝ)<1 := by dsimp [g] at hg; linarith
    have : (M.freshSelected z∩bad z).card<1 := by exact_mod_cast hlt
    omega
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_,?_⟩
  · intro hrep
    have hr : M.representative z (0,false)∈M.freshSelected z := by
      rw [←representative_selected]
      exact mem_map.mpr ⟨(0,false),mem_univ _,rfl⟩
    have hi:=mem_inter.mpr ⟨hr,hrep⟩
    rw [card_eq_zero.mp hg0] at hi
    simp at hi
  · have hc:=one_goodMiddle_count n k p θ G t z (bad z)
    have hc' : (N:ℝ)≤(goodMiddle 1 n k p θ G t z (bad z) 0).card+f z := by
      dsimp only [N, f]
      exact_mod_cast hc
    linarith
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real ActualHighRank
open scoped Classical BigOperators
noncomputable section

lemma card_first_fiber {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A×B)) (a : A) :
    (univ.filter (fun b=>(a,b)∈S)).card=(S.filter (fun z=>z.1=a)).card := by
  apply card_bij (fun b _=>(a,b))
  · intro b hb
    exact mem_filter.mpr ⟨(mem_filter.mp hb).2,rfl⟩
  · intro a ha b hb h
    exact Prod.mk.inj h|>.2
  · intro z hz
    have he : (a,z.2)=z := by ext <;> simp only [(mem_filter.mp hz).2]
    exact ⟨z.2,mem_filter.mpr ⟨mem_univ _,by rw [he]; exact (mem_filter.mp hz).1⟩,he⟩

lemma card_second_fiber {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A×B)) (b : B) :
    (univ.filter (fun a=>(a,b)∈S)).card=(S.filter (fun z=>z.2=b)).card := by
  apply card_bij (fun a _=>(a,b))
  · intro a ha
    exact mem_filter.mpr ⟨(mem_filter.mp ha).2,rfl⟩
  · intro a ha b hb h
    exact Prod.mk.inj h|>.1
  · intro z hz
    have he : (z.1,b)=z := by ext <;> simp only [(mem_filter.mp hz).2]
    exact ⟨z.1,mem_filter.mpr ⟨mem_univ _,by rw [he]; exact (mem_filter.mp hz).1⟩,he⟩

variable {K : Type} [Field K] [Fintype K] {d : ℕ}
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1)→K))
local notation "B" => Projectivization K (Fin (d+1)→K)

attribute [local instance] OAI.SharpLogRamsey.Marking.flat_ActualHighRankClass_3
attribute [local instance] OAI.SharpLogRamsey.Marking.flat_ActualHighRankClass_4
theorem covectorDomain_high {gap : ℝ} (S : Finset (B×A)) (r r' : Fin (d+1))
    (h : ValidSlotClass d gap S (.inr (r,r')))
    (hs : (S.card:ℝ)≤64*(Nat.card K:ℝ)^d) :
    2 ≤ r.val ∧ r.val≤d ∧ d+2 ≤ r.val+r'.val ∧
      Caps (log (Nat.card K)) r.val r'.val (covectorDomain S) := by
  obtain ⟨hr,hr',hsum,hA,hB,hfB,hfA⟩:=h
  have hrd : r.val≤d := Nat.le_of_lt_succ r.is_lt
  have hr'd : r'.val≤d := Nat.le_of_lt_succ r'.is_lt
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hexp (m : ℕ) (hm : m≤d) :
      (Nat.card K:ℝ)^(d-m)=exp (((d:ℝ)-m)*log (Nat.card K)) := by
    rw [←Nat.cast_sub hm,exp_nat_mul,exp_log hq]
  refine ⟨by omega,hrd,by omega,?_,?_,?_,?_,?_⟩
  · rw [covectorDomain_first]
    exact hB.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · rw [covectorDomain_second]
    exact hA.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · rwa [covectorDomain_card]
  · intro a
    have he : univ.filter (fun b=>(a,b)∈covectorDomain S)=univ.filter (fun b=>(b,a)∈S) := by
      ext b
      simp only [mem_filter,mem_univ,true_and]
      exact covectorDomain_mem S (b,a)
    rw [he,card_second_fiber,←hexp r'.val hr'd]
    exact hfA a
  · intro b
    have he : univ.filter (fun a=>(a,b)∈covectorDomain S)=univ.filter (fun a=>(b,a)∈S) := by
      ext a
      simp only [mem_filter,mem_univ,true_and]
      exact covectorDomain_mem S (b,a)
    rw [he,card_first_fiber,←hexp r.val hrd]
    exact hfB b

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankStream_1
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankStream_3
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankStream_4
local instance flat_ActualHighRankStream_5_rf12237_1 {K : Type} [Field K] {d : ℕ} : DecidableEq (Projectivization K (Module.Dual K (Fin (d+1)→K)) × Projectivization K (Fin (d+1)→K)) := Classical.decEq _
theorem eventually_high_stream {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (n k : ℕ), 0<n → k≤n → ∀ (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot 1 (n+k)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (S : Θ→Slot 1 (n+k)→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D J : ℝ) (r r' : ℕ), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      2 ≤ r → r≤d → d+2 ≤ r+r' →
      (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
      (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
        (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i,Caps σ r r' (S (θ ω) i)) →
      ∀ (t : Fin k) (hp : ∀ z,0<(model 1 n k p θ G t).remaining z),
      let M:=model 1 n k p θ G t
      let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
      let bad:=M.freshBad (fun _ _ _=>0) J (D*σ^beta η) a
      ∀ A : ℝ, A≤((2*(n+k):ℕ):ℝ)/20 →
      (∑ z,(M.freshLaw hp).mass z*((bad z).card:ℝ))≤A →
      (n:ℝ)*(∑ z,(M.freshLaw hp).mass z*((M.freshSelected z∩bad z).card:ℝ))≤A →
      Nonempty (StreamReplacement p G position ((n+k)/2)
        (fun code=>rawDomain (h:=rawRows σ η) code r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_prepared_high hη d hd] with σ he
  intro K Ω Θ _ _ _ _ hlog n k hn hkn p θ G S D J r r' hDl hDu hJ hr hrd hrr hS hf hcon hcap t hp
  dsimp only
  intro A hA hb hs
  let M:=model 1 n k p θ G t
  let μ:=M.freshLaw hp
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  let bad:=M.freshBad (fun _ _ _=>0) J (D*σ^beta η) a
  let E:=univ.filter (fun z=>M.representative z (0,false)∉bad z ∧
    ((2*(n+k):ℕ):ℝ)/2≤(goodMiddle 1 n k p θ G t z (bad z) 0).card)
  let H:=E.filter (fun z=>μ.mass z≠0)
  have hH : (1:ℝ)/2≤μ.event H := by
    rw [Law.event_nonzero_filter]
    exact high_good_history_half n k hn hkn p θ G t hp bad A hb hs hA
  have hzpos (z : H) : μ.mass z.val≠0 := (mem_filter.mp z.property).2
  have hrep (z : H) : M.representative z.val (0,false)∉bad z.val :=
    (mem_filter.mp (mem_filter.mp z.property).1).2.1
  let ℓ:=fun z : H=>(goodMiddle 1 n k p θ G t z.val (bad z.val) 0).card
  have hℓ (z : H) : n+k≤ℓ z := by
    have hh:=(mem_filter.mp (mem_filter.mp z.property).1).2.2
    have he : ((2*(n+k):ℕ):ℝ)/2=(n+k:ℕ) := by push_cast; ring
    rw [he] at hh
    exact_mod_cast hh
  let Q:=fun z : M.FreshHistory=>M.Index z.1→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)
  let q : ∀ z,Law (Q z):=fun z=>M.tupleLaw z.1
  let target:=fun (z : H) (y : Q z.val) (i : Fin (ℓ z))=>
    y (goodTarget 1 n k p θ G t z.val (bad z.val) 0 i)
  let DD:=fun code=>rawDomain (K:=K) (d:=d) (h:=rawRows σ η) code r (rawThreshold σ η)
  let B₀:=highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D)
  let C₀:=4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ)
  have hex (z : H) : Nonempty (Replacement (q z.val) (target z) DD B₀ C₀) := by
    apply he K Ω Θ hlog 1 n k p θ G S D J r r' hDl hDu hJ hr hrd hrr hS hf hcon hcap t hp z.val
      (hzpos z) 0 (hrep z)
    exact (by omega : 0<n+k).trans_le (hℓ z)
  let e :=fun z=>Classical.choice (hex z)
  have hrestore : (μ.sigma q).map (fun z=>M.restore z.1.1 z.2)=p.map G := by
    apply (M.afterDraw hp).restored_map
    intro φ
    rw [afterDraw_preserves,contextual_preserves,Law.sum_map]
  let loc:=fun (z : H) (i : Fin (ℓ z))=>M.origin z.val.1
    (goodTarget 1 n k p θ G t z.val (bad z.val) 0 i)
  have hloc : ∀ z,StrictMono (fun i=>position (loc z i)) := by
    intro z i j hij
    exact goodTarget_before 1 n k p θ G t z.val (bad z.val) 0 i j hij
  have hval : ∀ z y i,M.restore z.val.1 y (loc z i)=target z y i := by
    intro z y i
    exact M.restore_origin z.val.1 y _
  have hm : ∀ z,(n+k)/2≤ℓ z/2 := fun z=>Nat.div_le_div_right (hℓ z)
  have hcost : ∀ (Y : Type) [Fintype Y] (ν : Law Y)
      (msg : Y→((Fin (rawRows σ η)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))×
        (Fin (rawRows σ η)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))),
      entropy (ν.map msg)≤C₀ := by
    intro Y _ ν msg
    have hh:=raw_entropy (by simp : Module.finrank K (Fin (d+1)→K)=d+1) ν msg
    rwa [hlog] at hh
  have mix0 := mix_stream_replacement (Γ:=
      ((Fin (rawRows σ η)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))×
        (Fin (rawRows σ η)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))))
      p G position μ Q q
  have mix1 := mix0 (fun z=>M.restore z.1) hrestore H hH ℓ target loc hloc hval
  have mix2 := mix1 ((n+k)/2) hm DD B₀ C₀
  have hh:=mix2 e hcost
  exact hh

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

local instance flat_ActualHighRankExperiment_1_rf12237_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankExperiment_3
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankExperiment_4
theorem eventually_high_experiment {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d)
    (C c : ℝ) (hC : 0≤C) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (n k : ℕ), 2≤n → 0<k → k≤n → ∀ (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot 1 (n+k)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (S : Θ→Slot 1 (n+k)→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D J budget : ℝ) (r r' : ℕ), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      2 ≤ r → r≤d → d+2 ≤ r+r' →
      (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
      (∀ z i,log (S z i).card≤J) →
      (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
        (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i,Caps σ r r' (S (θ ω) i)) →
      (∑ z,(p.map θ).mass z*((Fintype.card (Slot 1 (n+k)):ℝ)*J-
          entropy ((p.cond θ z).map G)))≤budget →
      budget≤C*((2*(n+k):ℕ):ℝ)*D*σ^(-beta η) →
      c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
      Nonempty (StreamReplacement p G position ((n+k)/2)
        (fun code=>rawDomain (h:=rawRows σ η) code r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_high_stream hη d hd,
    SourceScales.eventually_information_bad_small η C c (1/20) hη hC hc (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ he hsmall hσ
  intro K Ω Θ _ _ _ _ hlog n k hn hk hkn p θ G S D J budget r r' hDl hDu hJ hr hrd hrr
    hS hSJ hf hcon hcap hbudget hb hk0
  have hσ0 : 0<σ := by linarith
  have hD : 0<D := (rpow_pos_of_pos hσ0 _).trans_le hDl
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have ha : 0<σ^(-2000*beta η)/(Nat.card K:ℝ) := div_pos (rpow_pos_of_pos hσ0 _) hq
  have hΔ : 0<D*σ^beta η := mul_pos hD (rpow_pos_of_pos hσ0 _)
  obtain ⟨t,hbad,hselected,hrestore⟩:=actual_realized_zero n k hn hk J (D*σ^beta η)
    (σ^(-2000*beta η)/(Nat.card K:ℝ)) budget hΔ ha p θ G
    (fun _=>embedding 1 (n+k)) (fun _=>owner 1 (n+k)) (fun _=>embedding_owner 1 (n+k)) S hS hSJ hbudget
  apply he K Ω Θ hlog n k (by omega) hkn p θ G S D J r r' hDl hDu hJ hr hrd hrr
    hS hf hcon hcap t (contextual_positive n k (by omega) p θ G
      (fun _=>embedding 1 (n+k)) (fun _=>owner 1 (n+k)) t)
    (budget/(D*σ^beta η)+2*budget/((k:ℝ)*(σ^(-2000*beta η)/(Nat.card K:ℝ))))
  · have hh:=hsmall (Nat.card K) D (2*(n+k):ℕ) budget k hq hD (by positivity) hb hk0
    simpa only [div_eq_mul_inv,one_div,one_mul,SourceScales.beta,HighRankBudgets.beta] using hh
  · exact hbad
  · exact hselected
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankOrdered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.flat_ActualHighRankOrdered_3
attribute [local instance] OAI.SharpLogRamsey.Marking.flat_ActualHighRankOrdered_4
theorem eventually_high_ordered_oai {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d)
    (C c : ℝ) (hC : 0≤C) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (n k : ℕ), 2≤n → 0<k → k≤n → ∀ (p : Law Ω) (θ : Ω→Θ)
        (F : Ω→Fin (4*(n+k))→ProjectivePair (K:=K) (V:=Fin (d+1)→K))
        (S : Θ→Fin (4*(n+k))→Finset (ProjectivePair (K:=K) (V:=Fin (d+1)→K)))
        (D J budget gap : ℝ) (r r' : Fin (d+1)), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      (∀ ω,p.mass ω≠0→∀ i,F ω i∈S (θ ω) i) →
      (∀ z i,log (S z i).card≤J) →
      (∀ ω,p.mass ω≠0→∀ i,Incidence.Incident (F ω i).1 (F ω i).2) →
      (∀ ω,p.mass ω≠0→ScanConsistent ((List.ofFn (F ω)).map toScan)) →
      (∀ ω,p.mass ω≠0→∀ i,ValidSlotClass d gap (S (θ ω) i) (.inr (r,r'))) →
      (∀ z i,((S z i).card:ℝ)≤64*(Nat.card K:ℝ)^d) →
      (∑ z : Θ,(p.map θ).mass z*(((4*(n+k):ℕ):ℝ)*J-
          entropy ((p.cond θ z).map F)))≤budget →
      budget≤C*((2*(n+k):ℕ):ℝ)*D*σ^(-beta η) →
      c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
      Nonempty (StreamReplacement p F Fin.val ((n+k)/2)
        (fun code=>(rawDomain (h:=rawRows σ η) code r.val (rawThreshold σ η)).map
          (Equiv.prodComm _ _).toEmbedding)
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  filter_upwards [eventually_high_experiment hη d hd C c hC hc] with σ he
  intro K Ω Θ _ _ _ _ hlog n k hn hk hkn p θ F S D J budget gap r r' hDl hDu hJ
    hS hSJ hf hcon hclass hsize hbudget hb hk0
  have hpos : ∃ ω,p.mass ω≠0 := by
    by_contra hh
    have hz : ∀ ω,p.mass ω=0 := by simpa only [not_exists,not_not] using hh
    have hh:=p.total
    simp only [hz,sum_const_zero] at hh
    norm_num at hh
  obtain ⟨ω,hω⟩:=hpos
  let i0 : Fin (4*(n+k)):=⟨0,by omega⟩
  obtain ⟨hr,hrd,hrr,_⟩:=covectorDomain_high (S (θ ω) i0) r r' (hclass ω hω i0) (hsize _ _)
  let G:=fun ω=>singleTuple (covectorTuple (F ω))
  let T:=fun z (i : Slot 1 (n+k))=>covectorDomain (S z i.2)
  have hG : ∀ ω,p.mass ω≠0→∀ i,G ω i∈T (θ ω) i := by
    intro ω hω i
    exact (covectorDomain_mem _ _).mpr (hS ω hω i.2)
  have hT : ∀ z i,log (T z i).card≤J := by
    intro z i
    simpa only [T,covectorDomain_card] using hSJ z i.2
  have hflag : ∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0 := by
    intro ω hω i
    exact covectorTuple_flag (F ω) (hf ω hω) i.2
  have hchron : ∀ ω,p.mass ω≠0→∀ i j,position i<position j→
      (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0 := by
    intro ω hω i j hij
    apply covectorTuple_consistent (F ω) (hcon ω hω)
    change i.2.val<j.2.val
    simpa only [single_position] using hij
  have hcap : ∀ ω,p.mass ω≠0→∀ i,Caps σ r.val r'.val (T (θ ω) i) := by
    intro ω hω i
    have hh:=(covectorDomain_high (S (θ ω) i.2) r r' (hclass ω hω i.2) (hsize _ _)).2.2.2
    rwa [hlog] at hh
  have hbud : (∑ z,(p.map θ).mass z*((Fintype.card (Slot 1 (n+k)):ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget := by
    apply le_trans (le_of_eq ?_) hbudget
    apply sum_congr rfl
    intro z _
    rw [single_entropy]
    simp only [Slot,Fintype.card_prod,Fintype.card_fin,Nat.one_mul]
    congr 2
    convert covectorTuple_entropy (K:=K) (V:=Fin (d+1)→K) (p.cond θ z) F using 1 <;> congr!
  obtain ⟨e⟩:=he K Ω Θ hlog n k hn hk hkn p θ G T D J budget r.val r'.val hDl hDu hJ
    hr hrd hrr hG hT hflag hchron hcap hbud hb hk0
  exact ⟨e.transport (Equiv.prodComm _ _) Prod.snd F Fin.val
    (fun i=>(single_position i).symm) (fun _ _=>rfl)⟩
end
end SharpLogRamsey.Marking

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Marking.eventually_high_ordered_oai := @OAI.SharpLogRamsey.Marking.eventually_high_ordered_oai
