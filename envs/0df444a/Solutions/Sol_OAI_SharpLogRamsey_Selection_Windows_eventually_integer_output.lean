-- Prove2me | solution 1 for OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:41:09.19748+00:00
-- url     : https://prove2.me/submissions/9260fc94-b7cc-4e71-abf7-c1448a660698

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_eventually_integer_decoder
import Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_prepared_context_of_mean

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

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Selection
variable {α : Type*} [Fintype α]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem Law.mem_core (p : Law α) (v : α → V) (ρ : ℝ) (x : V) :
    x ∈ p.core (K:=K) v ρ ↔ ∀ f ∈ p.tests (K:=K) v ρ, f x = 0 := by
  unfold Law.core
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h f hf
    exact h f (Submodule.subset_span hf)
  · intro h
    have hs : Submodule.span K (p.tests (K:=K) v ρ) ≤ LinearMap.ker (Module.Dual.eval K V x) := by
      rw [Submodule.span_le]
      exact h
    exact fun f hf => hs hf

omit [FiniteDimensional K V] in
theorem Law.core_le_test (p : Law α) (v : α → V) (ρ : ℝ)
    (f : Module.Dual K V) (hf : p.event (univ.filter (fun a => f (v a) ≠ 0)) ≤ ρ) :
    p.core (K:=K) v ρ ≤ LinearMap.ker f := by
  intro x hx
  exact (p.mem_core (K:=K) v ρ x).mp hx f hf

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma Law.fst_mul_condSnd (p : Law (A × B)) (a : A) (b : B) :
    p.fst.mass a*(p.condSnd a).mass b = p.mass (a,b) := by
  have h := p.cond_map_weight Prod.fst Prod.snd a b
  rw [Law.map_fst] at h
  change p.fst.mass a*((p.cond Prod.fst a).map Prod.snd).mass b = _
  rw [h]
  simp [Law.map, Fintype.sum_prod_type, sum_filter, Prod.mk.injEq, and_comm, ite_and]

lemma Law.condSnd_mass (p : Law (A × B)) (a : A) (ha : p.fst.mass a ≠ 0) (b : B) :
    (p.condSnd a).mass b = p.mass (a,b)/p.fst.mass a := by
  apply (eq_div_iff ha).mpr
  rw [mul_comm, p.fst_mul_condSnd]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ProdRectangleEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Selection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma complementary_of_rank_sum (W : Submodule K V) (U : Submodule K (Module.Dual K V))
    {r s : ℕ} (hW : r ≤ Module.finrank K W) (hU : s ≤ Module.finrank K U)
    (hsum : Module.finrank K V = r+s) (h : U ≤ W.dualAnnihilator) :
    Module.finrank K W = r ∧ U = W.dualAnnihilator := by
  have hle := Submodule.finrank_mono h
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  refine ⟨by omega, Submodule.eq_of_le_of_finrank_eq h ?_⟩
  omega

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B Ω : Type*} [Fintype A] [Fintype B] [Fintype Ω]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma firstCore_own (p : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hflag : ∀ ab, p.mass ab ≠ 0 → w ab.1 (v ab.2) = 0)
    (a : A) (ha : p.fst.mass a ≠ 0) :
    w a ∈ (firstCore (K := K) p v ρ a).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  apply (p.condSnd a).core_le_test v ρ (w a)
  have he : (p.condSnd a).event (univ.filter (fun b => w a (v b) ≠ 0)) = 0 := by
    apply sum_eq_zero
    intro b hb
    rw [p.condSnd_mass a ha]
    rw [show p.mass (a,b) = 0 from not_not.mp (fun hn => (mem_filter.mp hb).2 (hflag (a,b) hn))]
    exact zero_div _
  simpa only [he] using hρ

omit [Fintype Ω] [FiniteDimensional K V] in
lemma secondCore_own (p : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hflag : ∀ ab, p.mass ab ≠ 0 → w ab.1 (v ab.2) = 0)
    (y : B) (hy : p.snd.mass y ≠ 0) :
    v y ∈ (secondCore p w ρ y).dualCoannihilator := by
  rw [Submodule.mem_dualCoannihilator]
  apply (p.condFst y).core_le_test w ρ (Module.Dual.eval K V (v y))
  have he : (p.condFst y).event (univ.filter (fun a => (Module.Dual.eval K V (v y)) (w a) ≠ 0)) = 0 := by
    apply sum_eq_zero
    intro a ha
    rw [p.condFst_mass y hy]
    rw [show p.mass (a,y) = 0 from not_not.mp (fun hn => (mem_filter.mp ha).2 (hflag (a,y) hn))]
    exact zero_div _
  simpa only [he] using hρ

omit [Fintype Ω] in
lemma coreCollision_rectangle (p q : Law (A × B)) (v : B → V) (w : A → Module.Dual K V)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (goodA : A → Prop) (goodB : B → Prop)
    (hpflag : ∀ ab, p.mass ab ≠ 0 → w ab.1 (v ab.2) = 0)
    (hqflag : ∀ ab, q.mass ab ≠ 0 → w ab.1 (v ab.2) = 0)
    {r s : ℕ} (hsum : Module.finrank K V = r+s)
    (hW : ∀ a, goodA a → r ≤ Module.finrank K (firstCore (K := K) p v ρ a))
    (hU : ∀ y, goodB y → s ≤ Module.finrank K (secondCore q w ρ y))
    (ab cy : A × B) (hp : p.mass ab ≠ 0) (hq : q.mass cy ≠ 0)
    (hcol : coreCollision p q v w ρ goodA goodB (ab,cy)) :
    ab ∈ orthogonalRectangle v w (firstCore (K := K) p v ρ ab.1) ∧
    cy ∈ orthogonalRectangle v w (firstCore (K := K) p v ρ ab.1) := by
  obtain ⟨hga,hgy,_,hcont,hb,hc⟩ := hcol
  have hcomp := (complementary_of_rank_sum _ _ (hW _ hga) (hU _ hgy) hsum hcont).2
  have hpa : p.fst.mass ab.1 ≠ 0 := (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg _) (Ne.symm hp)) (p.le_fst _ _)).ne'
  have hqy : q.snd.mass cy.2 ≠ 0 := (lt_of_lt_of_le (lt_of_le_of_ne (q.nonneg _) (Ne.symm hq)) (q.le_snd _ _)).ne'
  have hy := secondCore_own q v w hρ hqflag cy.2 hqy
  rw [hcomp, Subspace.dualAnnihilator_dualCoannihilator_eq] at hy
  exact ⟨mem_filter.mpr ⟨mem_univ _, hb, firstCore_own p v w hρ hpflag ab.1 hpa⟩,
    mem_filter.mpr ⟨mem_univ _,hy,hcomp ▸ hc⟩⟩

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalActualCharges
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
variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma marginal_flag (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (hf : tupleFlags p v w) (i : ι) (ab : A×B) (ha : (p.marginal i).mass ab≠0) :
    w ab.1 (v ab.2)=0 := by
  obtain ⟨x,hx,rfl⟩ := p.map_support (fun x => x i) ab ha
  exact hf x hx i

lemma rankCollision_rectangle (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (hflag : tupleFlags p v w) (x : ι→A×B) (hx : p.mass x≠0) (i j : ι)
    (hc : rankCollision p v w ρ r s i j x) :
    x j∈orthogonalRectangle v w (firstCore (K:=K) (p.marginal i) v ρ (x i).1) := by
  have hpi : (p.marginal i).mass (x i)≠0 :=
    (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)) (p.le_map _ x)).ne'
  have hpj : (p.marginal j).mass (x j)≠0 :=
    (lt_of_lt_of_le (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)) (p.le_map _ x)).ne'
  exact (coreCollision_rectangle _ _ v w hρ _ _
    (marginal_flag p v w hflag i) (marginal_flag p v w hflag j) hsum
    (fun _ h => h) (fun _ h => h) (x i) (x j) hpi hpj hc).2

theorem directedCollision_sum (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {ρ M : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (hflag : tupleFlags p v w) (hocc : rectangleBound p v w M) :
    ∑ i,∑ j,(directedCollision p v w ρ r s i j:ℝ)≤Fintype.card ι*M := by
  let C := rankCollision p v w ρ r s
  have hpoint (x : ι→A×B) (hx : p.mass x≠0) (i : ι) :
      ∑ j,(if C i j x then (1:ℝ) else 0)≤M := by
    have hs : univ.filter (fun j => C i j x)⊆
        univ.filter (fun j => x j∈orthogonalRectangle v w
          (firstCore (K:=K) (p.marginal i) v ρ (x i).1)) := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _,rankCollision_rectangle p v w hρ hsum hflag x hx i j (mem_filter.mp hj).2⟩
    have hc := (Nat.cast_le.mpr (card_le_card hs) :
      ((univ.filter (fun j => C i j x)).card:ℝ)≤_)
    simpa only [sum_boole] using hc.trans (hocc x hx _)
  have he (i j : ι) : (directedCollision p v w ρ r s i j:ℝ)=
      ∑ x,p.mass x*(if C i j x then (1:ℝ) else 0) := by
    simp only [directedCollision,Law.event,sum_filter,mul_ite,mul_one,mul_zero]
    rfl
  simp_rw [he]
  have hswap : (∑ i,∑ j,∑ x,p.mass x*(if C i j x then (1:ℝ) else 0))=
      ∑ x,p.mass x*(∑ i,∑ j,(if C i j x then (1:ℝ) else 0)) := by
    conv_lhs => arg 2; ext i; rw [sum_comm]
    rw [sum_comm]
    simp_rw [mul_sum]
  rw [hswap]
  calc
    _ ≤ ∑ x,p.mass x*(Fintype.card ι*M) := by
      apply sum_le_sum
      intro x _
      by_cases hx : p.mass x=0
      · simp [hx]
      apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
      exact (sum_le_sum (fun i _ => hpoint x hx i)).trans_eq (by simp)
    _ = _ := by rw [←sum_mul,p.total,one_mul]

theorem reciprocalCharges_sum (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {ρ M : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (hflag : tupleFlags p v w) (hocc : rectangleBound p v w M) :
    ∑ i,∑ j,(reciprocalCharges p v w ρ r s i j:ℝ)≤2*Fintype.card ι*M := by
  simp only [reciprocalCharges,NNReal.coe_add,sum_add_distrib]
  rw [sum_comm (f:=fun i j => (directedCollision p v w ρ r s j i:ℝ))]
  linarith only [directedCollision_sum p v w hρ hsum hflag hocc]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalChargeHistories
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
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]

variable {A B : Type*} [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma tupleFlags_cond_restrict (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (hf : tupleFlags p v w) (E : Finset ι) (z : E→A×B)
    (hz : (p.restrict E).mass z≠0) :
    tupleFlags (A:=A) (B:=B) (ι := ↥(Eᶜ)) (p.revealRest E z) v w := by
  intro x hx i
  obtain ⟨y,hy,rfl⟩ := (p.cond (fun x (i:E) => x i) z).map_support _ x hx
  exact hf y (p.cond_support _ z hz y hy).1 i

omit [FiniteDimensional K V] in

lemma rectangleBound_cond_restrict (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    {M : ℝ} (ho : rectangleBound p v w M) (E : Finset ι) (z : E→A×B)
    (hz : (p.restrict E).mass z≠0) :
    rectangleBound (A:=A) (B:=B) (ι := ↥(Eᶜ)) (p.revealRest E z) v w M := by
  intro x hx W
  obtain ⟨y,hy,rfl⟩ := (p.cond (fun x (i:E) => x i) z).map_support _ x hx
  have ht := ho y (p.cond_support _ z hz y hy).1 W
  refine le_trans ?_ ht
  apply Nat.cast_le.mpr
  apply card_le_card_of_injOn (fun (i : (Eᶜ : Finset ι)) => (i:ι))
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  · exact Subtype.val_injective.injOn

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ExposureReciprocal
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
variable {C : Type v} {A B : Type w} [Fintype C] [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in

theorem chargedSelectedBad_le (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (n k : ℕ) (J D a : ℝ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→A×B))
    (e : C×Fin (n+k) ↪ ι) (own : ι→Option C)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k) :
    (n:ℝ)*chargedSelectedBad v w ρ r s n J D a k p e own t ≤ chargedBad v w ρ r s n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · change (n:ℝ)*roundSelectedBad p e own (reciprocalCharges p v w ρ r s) J D a≤
        roundBad p e own (reciprocalCharges p v w ρ r s) J D a
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (show n≤n+(k+1) by omega))
        (roundSelectedBad_nonneg p e own _ J D a)).trans (roundSelectedBad_le p e own hown _ J D a)
    · change (n:ℝ)*((∑ f : C→Fin (n+k+1),∑ z,
          (p.restrict (freshRepresentatives e f)).mass z *
            chargedSelectedBad v w ρ r s n J D a k
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

omit [FiniteDimensional K V] in
lemma history_average_const {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    {m : ℕ} (hm : 0 < m) (p : Law (ι→β)) (e : C×Fin m ↪ ι) (a : ℝ) :
    (∑ f : C→Fin m,∑ z,(p.restrict (freshRepresentatives e f)).mass z*a)/
      Fintype.card (C→Fin m)=a := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hc : (Fintype.card (C→Fin m):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hi (f : C→Fin m) : ∑ z, (p.restrict (freshRepresentatives e f)).mass z*a=a := by
    rw [←sum_mul,Law.total,one_mul]
  simp_rw [hi]
  simp only [sum_const,card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ a hc

theorem chargedBad_budget (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 0<n) (J D a N M : ℝ) (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (p : Law (ι→A×B))
    (e : C×Fin (n+k) ↪ ι) (own : ι→Option C) (S : ι→Finset (A×B))
    (hS : tupleSupported p S) (hJ : ∀ i,Real.log (S i).card≤J)
    (hN : (Fintype.card ι:ℝ)≤N) (hf : tupleFlags p v w) (ho : rectangleBound p v w M)
    (t : Fin k) :
    chargedBad v w ρ r s n J D a k p e own t≤
      exposureDeficits n J k p e t/D+exposureScores n k p e own t/a+2*N*M/((n:ℝ)*a) := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) t
    · change roundBad p e own (reciprocalCharges p v w ρ r s) J D a≤
        tupleDeficit J p/D+roundInformation p e own/a+2*N*M/((n:ℝ)*a)
      refine (roundBad_le (by omega : 0<n+(k+1)) p e own _ J D a hD ha
        (tupleSupported_marginal_cap p S hS J hJ)).trans ?_
      apply add_le_add_right
      have hc : (∑ i,∑ j,(reciprocalCharges p v w ρ r s i j:ℝ))≤2*N*M := by
        exact (reciprocalCharges_sum p v w hρ hsum hf ho).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hN (by norm_num)) hM)
      have hm : (0:ℝ)<n := by exact_mod_cast hn
      have hN0 : 0≤N := (Nat.cast_nonneg _).trans hN
      apply div_le_div₀ (by positivity) hc (by positivity)
      gcongr
      exact_mod_cast (show n≤n+(k+1) by omega)
    · change (∑ f : C→Fin (n+k+1),∑ z,
          (p.restrict (freshRepresentatives e f)).mass z *
            chargedBad v w ρ r s n J D a k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ)
              (remainingEmbedding e f) (fun i => own i) j)/_≤_
      calc
        _ ≤ (∑ f : C→Fin (n+k+1),∑ z,
            (p.restrict (freshRepresentatives e f)).mass z *
            (exposureDeficits n J k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) j/D+
             exposureScores n k
              ((p.cond (fun x (i : freshRepresentatives e f) => x i) z).restrict
                (freshRepresentatives e f)ᶜ) (remainingEmbedding e f) (fun i => own i) j/a+
              2*N*M/((n:ℝ)*a))) /Fintype.card (C→Fin (n+k+1)) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply sum_le_sum
          intro f _
          apply sum_le_sum
          intro z _
          by_cases hz : (p.restrict (freshRepresentatives e f)).mass z=0
          · rw [hz,zero_mul,zero_mul]
          · apply mul_le_mul_of_nonneg_left _ ((p.restrict _).nonneg z)
            exact ih _ (remainingEmbedding e f) (fun i => own i) (fun i => S i)
              (tupleSupported_cond_restrict p S hS _ z hz) (fun i => hJ i)
              ((Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hN)
              (tupleFlags_cond_restrict p v w hf _ z hz)
              (rectangleBound_cond_restrict p v w ho _ z hz) j
        _ = _ := by
          rw [exposureDeficits_succ,exposureScores_succ]
          simp only [mul_add,sum_add_distrib,add_div]
          rw [history_average_const (by omega : 0<n+k+1)]
          simp only [←mul_div_assoc,←sum_div]
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

lemma contextAverage_const (μ : Law Θ) (a : ℝ) : contextAverage μ (fun _ => a)=a := by
  unfold contextAverage
  rw [←sum_mul,μ.total,one_mul]

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

variable {A B : Type w} [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_context_good_reciprocal (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 2≤n) (hk : 0<k) (J D a M : ℝ) (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    (μ : Law Θ) (p : Θ→Law (ι→A×B)) (e : Θ→C×Fin (n+k) ↪ ι)
    (own : Θ→ι→Option C) (hown : ∀ θ b x,own θ (e θ (b,x))=some b)
    (S : Θ→ι→Finset (A×B))
    (hS : ∀ θ,μ.mass θ≠0 → tupleSupported (p θ) (S θ))
    (hJ : ∀ θ i,Real.log (S θ i).card≤J)
    (hf : ∀ θ,μ.mass θ≠0 → tupleFlags (p θ) v w)
    (ho : ∀ θ,μ.mass θ≠0 → rectangleBound (p θ) v w M) :
    ∃ t : Fin k,
      contextAverage μ (fun θ => chargedBad v w ρ r s n J D a k (p θ) (e θ) (own θ) t) ≤
        contextAverage μ (fun θ => tupleDeficit J (p θ))/D+
        2*contextAverage μ (fun θ => totalCorrelation (p θ))/((k:ℝ)*a)+
        2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (n:ℝ)*contextAverage μ (fun θ => chargedSelectedBad v w ρ r s n J D a k (p θ) (e θ) (own θ) t) ≤
        contextAverage μ (fun θ => tupleDeficit J (p θ))/D+
        2*contextAverage μ (fun θ => totalCorrelation (p θ))/((k:ℝ)*a)+
        2*Fintype.card ι*M/((n:ℝ)*a) := by
  obtain ⟨t,ht⟩ := exists_context_round n k hn hk μ p e own hown
  have hbθ (θ : Θ) (hθ : μ.mass θ≠0) :
      chargedBad v w ρ r s n J D a k (p θ) (e θ) (own θ) t ≤
        tupleDeficit J (p θ)/D+exposureScores n k (p θ) (e θ) (own θ) t/a+
        2*Fintype.card ι*M/((n:ℝ)*a) := by
    have hb := chargedBad_budget v w hρ hsum n k (by omega) J D a (Fintype.card ι) M hD ha hM
      (p θ) (e θ) (own θ) (S θ) (hS θ hθ) (hJ θ) le_rfl (hf θ hθ) (ho θ hθ) t
    have hd := exposureDeficits_le n k J (p θ) (e θ) (S θ) (hS θ hθ) (hJ θ) t
    exact hb.trans (by gcongr)
  have hb := contextAverage_mono μ hbθ
  simp only [contextAverage_add,contextAverage_div,contextAverage_const] at hb
  have hbound : contextAverage μ (fun θ => chargedBad v w ρ r s n J D a k (p θ) (e θ) (own θ) t) ≤
      contextAverage μ (fun θ => tupleDeficit J (p θ))/D+
        2*contextAverage μ (fun θ => totalCorrelation (p θ))/((k:ℝ)*a)+
        2*Fintype.card ι*M/((n:ℝ)*a) := by
    calc
      _ ≤ _ := hb
      _ ≤ contextAverage μ (fun θ => tupleDeficit J (p θ))/D+
          (2*contextAverage μ (fun θ => totalCorrelation (p θ))/(k:ℝ))/a+_ := by gcongr
      _ = _ := by rw [div_div]
  refine ⟨t,hbound,le_trans ?_ hbound⟩
  rw [←contextAverage_mul]
  apply contextAverage_mono μ
  intro θ _
  exact chargedSelectedBad_le v w ρ r s n k J D a (p θ) (e θ) (own θ) (hown θ) t

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_SourceReciprocalExposure
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
universe u
variable {Θ Ω C ι : Type*} {A B : Type u} [Fintype Θ] [Fintype Ω] [Fintype C]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma reciprocal_conditional_supported (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (S : Θ→ι→Finset (A×B))
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (z : Θ) (hz : (p.map θ).mass z≠0) :
    tupleSupported ((p.cond θ z).map G) (S z) := by
  intro f hf i
  obtain ⟨x,hx,rfl⟩ := (p.cond θ z).map_support G f hf
  obtain ⟨hx,he⟩:=p.cond_support θ z hz x hx
  simpa only [he] using hS x hx i

omit [FiniteDimensional K V] in
lemma conditional_tupleFlags (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (v : B→V) (w : A→Module.Dual K V)
    (hf : ∀ x,p.mass x≠0→∀ i,w (G x i).1 (v (G x i).2)=0)
    (z : Θ) (hz : (p.map θ).mass z≠0) :
    tupleFlags ((p.cond θ z).map G) v w := by
  intro f hf' i
  obtain ⟨x,hx,rfl⟩ := (p.cond θ z).map_support G f hf'
  exact hf x (p.cond_support θ z hz x hx).1 i

omit [FiniteDimensional K V] in
lemma conditional_rectangleBound (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (v : B→V) (w : A→Module.Dual K V) (M : ℝ)
    (ho : ∀ x,p.mass x≠0→∀ W : Submodule K V,
      ((univ.filter (fun i=>G x i∈orthogonalRectangle v w W)).card:ℝ)≤M)
    (z : Θ) (hz : (p.map θ).mass z≠0) :
    rectangleBound ((p.cond θ z).map G) v w M := by
  intro f hf W
  obtain ⟨x,hx,rfl⟩ := (p.cond θ z).map_support G f hf
  exact ho x (p.cond_support θ z hz x hx).1 W

theorem actual_source_reciprocal (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 2≤n) (hk : 0<k) (J D a M budget : ℝ)
    (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k) ↪ ι) (own : Θ→ι→Option C)
    (hown : ∀ z b x,own z (e z (b,x))=some b)
    (S : Θ→ι→Finset (A×B))
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (hJ : ∀ z i,Real.log (S z i).card≤J)
    (hf : ∀ x,p.mass x≠0→∀ i,w (G x i).1 (v (G x i).2)=0)
    (ho : ∀ x,p.mass x≠0→∀ W : Submodule K V,
      ((univ.filter (fun i=>G x i∈orthogonalRectangle v w W)).card:ℝ)≤M)
    (hbudget : (∑ z,(p.map θ).mass z*((Fintype.card ι:ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget) :
    ∃ t : Fin k,
      (∑ z,(p.map θ).mass z*chargedBad v w ρ r s n J D a k
        ((p.cond θ z).map G) (e z) (own z) t)≤
          budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (n:ℝ)*(∑ z,(p.map θ).mass z*chargedSelectedBad v w ρ r s n J D a k
        ((p.cond θ z).map G) (e z) (own z) t)≤
          budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) := by
  have hb : contextAverage (p.map θ) (fun z=>tupleDeficit J ((p.cond θ z).map G))≤budget := hbudget
  have hTC : contextAverage (p.map θ) (fun z=>totalCorrelation ((p.cond θ z).map G))≤budget := by
    apply le_trans _ hb
    apply contextAverage_mono
    intro z hz
    exact totalCorrelation_le_tupleDeficit _ J (tupleSupported_marginal_cap _ (S z)
      (reciprocal_conditional_supported p θ G S hS z hz) J (hJ z))
  obtain ⟨t,ht,ht'⟩ := exists_context_good_reciprocal v w hρ hsum n k hn hk J D a M hD ha hM
    (p.map θ) (fun z=>(p.cond θ z).map G) e own hown S
    (reciprocal_conditional_supported p θ G S hS) hJ
    (conditional_tupleFlags p θ G v w hf) (conditional_rectangleBound p θ G v w M ho)
  have hscale : contextAverage (p.map θ) (fun z=>tupleDeficit J ((p.cond θ z).map G))/D+
      2*contextAverage (p.map θ) (fun z=>totalCorrelation ((p.cond θ z).map G))/((k:ℝ)*a)+
      2*Fintype.card ι*M/((n:ℝ)*a)≤
        budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) := by
    have hdenom : 0 ≤ (k : ℝ) * a := mul_nonneg (Nat.cast_nonneg k) ha.le
    exact add_le_add
      (add_le_add (div_le_div_of_nonneg_right hb hD.le)
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTC (show (0 : ℝ) ≤ 2 by norm_num)) hdenom)) le_rfl
  exact ⟨t,ht.trans hscale,ht'.trans hscale⟩

end
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

variable {A B K V : Type} [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma exposureAverage_bad (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s n k : ℕ)
    (J D a : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→A×B)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    exposureAverage (reciprocalBadStatistic v w ρ r s J D a) n k p e own t=
      chargedBad v w ρ r s n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · rfl
    · change (∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        exposureAverage _ n k _ _ _ j)/_=_
      simp_rw [ih]
      rfl

omit [FiniteDimensional K V] in
lemma exposureAverage_selected (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s n k : ℕ)
    (J D a : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→A×B)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k) :
    exposureAverage (reciprocalSelectedStatistic v w ρ r s J D a) n k p e own t=
      chargedSelectedBad v w ρ r s n J D a k p e own t := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>?_) t
    · rfl
    · change (∑ f : C→Fin (n+k+1),∑ z,(p.restrict (freshRepresentatives e f)).mass z*
        exposureAverage _ n k _ _ _ j)/_=_
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

variable {A B K V : Type} [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional K V] in
lemma fresh_bad_mean (M : ExposureModel ι (A×B) C) (h : ∀ z,0<M.remaining z)
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (J D a : ℝ) :
    (∑ x,(M.freshLaw h).mass x*
      ((M.freshBad (fun z=>reciprocalCharges (M.tupleLaw z) v w ρ r s) J D a x).card:ℝ))=
      M.mean (reciprocalBadStatistic v w ρ r s J D a) := by
  rw [freshLaw_sum]
  rfl

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional K V] in
lemma fresh_selected_mean (M : ExposureModel ι (A×B) C) (h : ∀ z,0<M.remaining z)
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (J D a : ℝ) :
    (∑ x,(M.freshLaw h).mass x*((M.freshSelected x∩
      M.freshBad (fun z=>reciprocalCharges (M.tupleLaw z) v w ρ r s) J D a x).card:ℝ))=
      M.mean (reciprocalSelectedStatistic v w ρ r s J D a) := by
  rw [freshLaw_sum]
  rfl

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SourceExposure
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
variable {Θ Ω C ι A B K V : Type} [Fintype Θ] [Fintype Ω] [Fintype C]
  [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace ExposureModel

omit [FiniteDimensional K V] in
lemma contextual_bad_mean (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (J D a : ℝ) :
    (contextual n k p θ G e own t).mean (reciprocalBadStatistic v w ρ r s J D a)=
      ∑ z,(p.map θ).mass z*chargedBad v w ρ r s n J D a k ((p.cond θ z).map G)
        (e z) (own z) t := by
  rw [contextual,mix_mean]
  simp_rw [atRound_mean,exposureAverage_bad]

omit [FiniteDimensional K V] in
lemma contextual_selected_mean (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (v : B→V) (w : A→Module.Dual K V) (ρ : ℝ) (r s : ℕ) (J D a : ℝ) :
    (contextual n k p θ G e own t).mean (reciprocalSelectedStatistic v w ρ r s J D a)=
      ∑ z,(p.map θ).mass z*chargedSelectedBad v w ρ r s n J D a k ((p.cond θ z).map G)
        (e z) (own z) t := by
  rw [contextual,mix_mean]
  simp_rw [atRound_mean,exposureAverage_selected]

end ExposureModel
open ExposureModel

theorem actual_realized_reciprocal (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 2≤n) (hk : 0<k) (J D a M budget : ℝ)
    (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→A×B)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C)
    (hown : ∀ z b x,own z (e z (b,x))=some b)
    (S : Θ→ι→Finset (A×B))
    (hS : ∀ x,p.mass x≠0→∀ i,G x i∈S (θ x) i)
    (hJ : ∀ z i,Real.log (S z i).card≤J)
    (hf : ∀ x,p.mass x≠0→∀ i,w (G x i).1 (v (G x i).2)=0)
    (ho : ∀ x,p.mass x≠0→∀ W : Submodule K V,
      ((univ.filter (fun i=>G x i∈orthogonalRectangle v w W)).card:ℝ)≤M)
    (hbudget : (∑ z,(p.map θ).mass z*((Fintype.card ι:ℝ)*J-
      entropy ((p.cond θ z).map G)))≤budget) :
    ∃ t : Fin k,
      let E:=contextual n k p θ G e own t
      let hp:=contextual_positive n k (by omega : 0<n) p θ G e own t
      let bad:=E.freshBad (fun z=>reciprocalCharges (E.tupleLaw z) v w ρ r s) J D a
      (∑ x,(E.freshLaw hp).mass x*((bad x).card:ℝ))≤
        budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (n:ℝ)*(∑ x,(E.freshLaw hp).mass x*((E.freshSelected x∩bad x).card:ℝ))≤
        budget/D+2*budget/((k:ℝ)*a)+2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (E.afterDraw hp).joint.map (fun x=>(E.afterDraw hp).restore x.1 x.2)=p.map G := by
  obtain ⟨t,hb,hs⟩:=actual_source_reciprocal v w hρ hsum n k hn hk J D a M budget hD ha hM
    p θ G e own hown S hS hJ hf ho hbudget
  refine ⟨t,?_,?_,?_⟩
  ·
    rw [fresh_bad_mean,contextual_bad_mean]
    exact hb
  ·
    rw [fresh_selected_mean,contextual_selected_mean]
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

omit [Fintype ι] in
lemma badWindows_image (e : W×Bool↪ι) (bad : Finset ι) :
    badWindows e bad=(univ.filter (fun z:W×Bool=>e z∈bad)).image Prod.fst := by
  ext i
  simp only [badWindows,mem_filter,mem_univ,true_and,mem_image]
  constructor
  · rintro (h|h)
    · exact ⟨(i,false),h,rfl⟩
    · exact ⟨(i,true),h,rfl⟩
  · rintro ⟨⟨j,b⟩,h,rfl⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h

omit [Fintype ι] in
lemma badWindows_card (e : W×Bool↪ι) (bad : Finset ι) :
    (badWindows e bad).card≤((univ.map e)∩bad).card := by
  rw [badWindows_image]
  have he : (univ.filter (fun z:W×Bool=>e z∈bad)).map e=(univ.map e)∩bad := by
    ext i
    simp only [mem_map,mem_filter,mem_univ,true_and,mem_inter]
    constructor
    · rintro ⟨z,h,rfl⟩
      exact ⟨⟨z,rfl⟩,h⟩
    · rintro ⟨⟨z,rfl⟩,h⟩
      exact ⟨z,h,rfl⟩
  calc
    _ ≤ (univ.filter (fun z:W×Bool=>e z∈bad)).card := card_image_le
    _ = _ := by rw [←he,card_map]

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
theorem bad_windows_mean (hp : ∀ z,0<(model w n k p θ G t).remaining z)
    (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1)) :
    (∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      ((badWindows ((model w n k p θ G t).representative z) (bad z)).card:ℝ))≤
    ∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ) := by
  apply sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (((model w n k p θ G t).freshLaw hp).nonneg z)
  have hh := badWindows_card ((model w n k p θ G t).representative z) (bad z)
  rw [representative_selected] at hh
  apply (Nat.cast_le (α:=ℝ)).mpr
  convert! (preTransparency := .all) hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext index
  simp only [mem_inter]

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
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_MixedLoss
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
variable {X Ω B A Θ : Type*} [Fintype X] [Fintype Ω] [Fintype B] [Fintype A] [Fintype Θ]

lemma Law.attach_left (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B) (φ : X→ℝ) :
    (∑ x,(q.attach μ f g).mass x*φ x.1)=∑ x,q.mass x*φ x := by
  rw [Law.attach,Law.sigma_sum]
  apply sum_congr rfl
  intro x _
  change q.mass x*(∑ a,(μ.cond g (f x)).mass a*φ x)=q.mass x*φ x
  rw [←sum_mul,(μ.cond g (f x)).total,one_mul]

theorem Law.mixed_loss (ν : Law Θ) {Y : {θ // ν.mass θ≠0}→Type*}
    [∀ θ,Fintype (Y θ)] (μ : ∀ θ,Law (Y θ)) (p : Law A)
    (N : ℕ) (pop : Θ→ℕ) (out : A→(Σ θ,Y θ)→ℕ) (δ : ℝ) (hδ : 0≤δ)
    (hsize : ∀ θ,pop θ≤N)
    (hlocal : ∀ θ,(∑ a,p.mass a*∑ y,(μ θ).mass y*((pop θ.val:ℝ)-(out a ⟨θ,y⟩:ℝ)))≤
      (pop θ.val:ℝ)*δ) :
    (∑ a,p.mass a*∑ ω,(ν.nullFree.sigma μ).mass ω*((N:ℝ)-(out a ω:ℝ)))≤
      (∑ θ,ν.mass θ*((N:ℝ)-(pop θ:ℝ)))+(N:ℝ)*δ := by
  have hloc (θ : {θ // ν.mass θ≠0}) :
      (∑ a,p.mass a*∑ y,(μ θ).mass y*((N:ℝ)-(out a ⟨θ,y⟩:ℝ)))≤
        (N:ℝ)-(pop θ.val:ℝ)+(N:ℝ)*δ := by
    calc
      _ = (N:ℝ)-(pop θ.val:ℝ)+
          ∑ a,p.mass a*∑ y,(μ θ).mass y*((pop θ.val:ℝ)-(out a ⟨θ,y⟩:ℝ)) := by
        have he (a : A) (y : Y θ) : (N:ℝ)-(out a ⟨θ,y⟩:ℝ)=
            ((N:ℝ)-(pop θ.val:ℝ))+((pop θ.val:ℝ)-(out a ⟨θ,y⟩:ℝ)) := by ring
        simp_rw [he]
        simp only [mul_add,sum_add_distrib,←sum_mul,(μ θ).total,p.total,one_mul]
      _ ≤ _ := add_le_add le_rfl ((hlocal θ).trans
        (mul_le_mul_of_nonneg_right (show (pop θ.val:ℝ)≤(N:ℝ) by exact_mod_cast hsize θ.val) hδ))
  calc
    _ = ∑ θ,ν.nullFree.mass θ*(∑ a,p.mass a*
        ∑ y,(μ θ).mass y*((N:ℝ)-(out a ⟨θ,y⟩:ℝ))) := by
      simp_rw [Law.sigma_sum,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro θ _
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro y _
      ring
    _ ≤ ∑ θ,ν.nullFree.mass θ*((N:ℝ)-(pop θ.val:ℝ)+(N:ℝ)*δ) :=
      sum_le_sum (fun θ _=>mul_le_mul_of_nonneg_left (hloc θ) (ν.nullFree.nonneg θ))
    _ = _ := by
      rw [ν.nullFree_integral (fun θ=>(N:ℝ)-(pop θ:ℝ)+(N:ℝ)*δ)]
      simp only [mul_add,sum_add_distrib,←sum_mul,ν.total,one_mul]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_PredeletionMean
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

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.preFinDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.preBlockDec
lemma bad_predeletion_mean
    (hp : ∀ z,0<(model w n k p θ G t).remaining z)
    (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1)) :
    (∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      ((w*(2*(n+k)):ℝ)-(∑ i∈univ\badWindows ((model w n k p θ G t).representative z) (bad z),
        (goodMiddle w n k p θ G t z (bad z) i).card:ℕ)))≤
      (∑ z,((model w n k p θ G t).freshLaw hp).mass z*((bad z).card:ℝ))+
      (2*(n+k):ℕ)*(∑ z,((model w n k p θ G t).freshLaw hp).mass z*
        (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ)) := by
  let M:=model w n k p θ G t
  have hpnt (z : M.FreshHistory) :
      ((w*(2*(n+k)):ℝ)-(∑ i∈univ\badWindows (M.representative z) (bad z),
        (goodMiddle w n k p θ G t z (bad z) i).card:ℕ))≤
      ((bad z).card:ℝ)+((badWindows (M.representative z) (bad z)).card:ℝ)*(2*(n+k):ℕ) := by
    have hh:=goodPopulation_predeletion w n k p θ G t z (bad z) (badWindows (M.representative z) (bad z))
    have hh' := (Nat.cast_le (α:=ℝ)).mpr hh
    push_cast at hh'
    change (w:ℝ)*(2*((n:ℝ)+(k:ℝ)))≤
      (∑ i∈univ\badWindows (M.representative z) (bad z),
        ((goodMiddle w n k p θ G t z (bad z) i).card:ℝ))+
        ((bad z).card:ℝ)+((badWindows (M.representative z) (bad z)).card:ℝ)*(2*((n:ℝ)+(k:ℝ))) at hh'
    push_cast
    linarith

  calc
    _ ≤ ∑ z,(M.freshLaw hp).mass z*(((bad z).card:ℝ)+
        ((badWindows (M.representative z) (bad z)).card:ℝ)*(2*(n+k):ℕ)) :=
      sum_le_sum (fun z _=>mul_le_mul_of_nonneg_left (hpnt z) ((M.freshLaw hp).nonneg z))
    _ = (∑ z,(M.freshLaw hp).mass z*((bad z).card:ℝ))+
        (2*(n+k):ℕ)*(∑ z,(M.freshLaw hp).mass z*
          ((badWindows (M.representative z) (bad z)).card:ℝ)) := by
      simp only [mul_add,sum_add_distrib,mul_sum,mul_left_comm,mul_comm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (bad_windows_mean w n k p θ G t hp bad) (show (0:ℝ)≤((2*(n+k):ℕ):ℝ) by positivity))

theorem bad_predeletion_five (hkn : k≤n)
    (hp : ∀ z,0<(model w n k p θ G t).remaining z)
    (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1))
    (B : ℝ)
    (hbad : (∑ z,((model w n k p θ G t).freshLaw hp).mass z*((bad z).card:ℝ))≤B)
    (hrep : (n:ℝ)*(∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ))≤B) :
    (∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      ((w*(2*(n+k)):ℝ)-(∑ i∈univ\badWindows ((model w n k p θ G t).representative z) (bad z),
        (goodMiddle w n k p θ G t z (bad z) i).card:ℕ)))≤5*B := by
  have h:=bad_predeletion_mean w n k p θ G t hp bad
  have hh : (2*(n+k):ℕ)≤4*n := by omega
  have hh' : ((2*(n+k):ℕ):ℝ)≤4*(n:ℝ) := by exact_mod_cast hh
  have hn : 0≤∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ) :=
    sum_nonneg (fun z _=>mul_nonneg (((model w n k p θ G t).freshLaw hp).nonneg z) (by positivity))
  have hmul:=mul_le_mul_of_nonneg_right hh' hn
  nlinarith

end
end SharpLogRamsey.Selection.Windows

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
lemma attachedPrepared_left (f : (mixedPrepared w n k p θ G t hp e).Ω→ℝ) :
    (∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*f ω.1)=
      ∑ x,(mixedPrepared w n k p θ G t hp e).μ.mass x*f x :=
  Law.attach_left _ _ _ _ _

omit [Finite K] [FiniteDimensional K V] in
theorem attachedPrepared_loss {A : Type} [Fintype A] (ρ : Law A)
    (N : ℕ) (pop : (M).FreshHistory→ℕ)
    (out : A→(mixedPrepared w n k p θ G t hp e).Ω→ℕ) (δ B : ℝ) (hδ : 0≤δ)
    (hsize : ∀ z,pop z≤N)
    (hlocal : ∀ z,(∑ a,ρ.mass a*∑ y,(e z).μ.mass y*
      ((pop z.val:ℝ)-(out a ⟨z,y⟩:ℝ)))≤(pop z.val:ℝ)*δ)
    (hdelete : (∑ z,((M).freshLaw hp).mass z*((N:ℝ)-(pop z:ℝ)))≤B) :
    (∑ a,ρ.mass a*∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*
      ((N:ℝ)-(out a ω.1:ℝ)))≤B+(N:ℝ)*δ := by
  have heq : (∑ a,ρ.mass a*∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*
      ((N:ℝ)-(out a ω.1:ℝ)))=
      ∑ a,ρ.mass a*∑ y,(mixedPrepared w n k p θ G t hp e).μ.mass y*
        ((N:ℝ)-(out a y:ℝ)) := by
    apply sum_congr rfl
    intro a _
    congr 1
    exact attachedPrepared_left w n k p θ G t hp e (fun y=>(N:ℝ)-(out a y:ℝ))
  rw [heq]
  exact (Law.mixed_loss ((M).freshLaw hp) (fun z=>(e z).μ) ρ N pop out δ hδ hsize hlocal).trans
    (add_le_add hdelete le_rfl)
end
end SharpLogRamsey.Selection.Windows

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
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.experimentFinDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.experimentSlotDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.experimentBlockDec
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)

variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.experimentBanks
theorem eventually_integer_experiment (d : ℕ) (η C A loss : ℝ)
    (hη : 0<η) (hC : 0<C) (hloss : 0<loss) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      ∀ (hdim : Module.finrank K V=d+3), log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
        (hτ : 0≤τ) (hτsmall : τ≤1/40000)
        (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J M budget : ℝ),
        ∀ (hn : 2≤n), 0<k → k≤n → (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
        (∀ z i,log (S z i).card≤J) →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,IntegerBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        (∀ ω,p.mass ω≠0→∀ W : Submodule K V,
          ((univ.filter (fun i=>G ω i∈orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ)≤M) →
        (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
          entropy ((p.cond θ z).map G)))≤budget →
        ∀ fallback : Fin w, ∃ t : Fin k,
        let hp:=contextual_positive n k (by omega : 0<n) p θ G
          (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t
        ∃ e : ∀ z : PositiveHistory w n k p θ G t hp,
          Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
            (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))),
        let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
        let expmt:=attachedPrepared w n k p θ G t hp e
        (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
          ∑ ω,expmt.μ.mass ω*((w*(2*(n+k)):ℝ)-
            (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
              (fun i=>book.chronoChoose hdim hτ hτsmall ((e ω.1.1).supports ω.1.2 i))
              (fun _=>chronoRead b) (integerTargets w n k p θ G t hp e r J (D*σ^beta η) a ω.1) tab
              (integerTree w n k p θ G t hp e r J (D*σ^beta η) a fallback ω.1) (univ,univ)).length))≤
          5*(budget/(D*σ^beta η)+2*budget/((k:ℝ)*a)+
            2*Fintype.card (Slot w (n+k))*M/((n:ℝ)*a))+(w*(2*(n+k)):ℝ)*loss := by
  filter_upwards [eventually_integer_decoder d η C A loss hη hC hloss,
    eventually_ge_atTop (1:ℝ)] with σ hdec hσ
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hτ hτsmall Ω Θ _ _ w n k p θ G S u r J M budget hn hk hkn hw hr hJ hM hSJ hS hf hcon hcap hband ho hbudget fallback
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  have hσ0 : 0<σ := by linarith
  have hD : 0<D*σ^beta η := mul_pos ((rpow_pos_of_pos hσ0 _).trans_le hDl) (rpow_pos_of_pos hσ0 _)
  have ha : 0<a := by dsimp [a]; exact div_pos (rpow_pos_of_pos hσ0 _) (by exact_mod_cast Finite.card_pos)
  obtain ⟨t,hbad,hrep,_⟩:=actual_realized_reciprocal Projectivization.rep Projectivization.rep
    (show (0:ℝ)≤1/(100*((d:ℝ)+3)) by positivity)
    (show Module.finrank K V=r+(d+3-r) by omega)
    n k hn hk J (D*σ^beta η) a M budget hD ha hM p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) (fun _=>embedding_owner w (n+k))
    S hS hSJ hf ho hbudget
  let hp:=contextual_positive n k (by omega : 0<n) p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t
  have hh := hdec K V hdim hlog D P H hDl hDu book hτ hτsmall Ω Θ w n k p θ G S u r J
    hw hr hJ hS hf hcon hcap hband t hp
  choose e he using fun z : PositiveHistory w n k p θ G t hp=>hh z.val z.property fallback
  refine ⟨t,e,?_⟩
  let pop:=integerPop (d:=d) w n k p θ G t r J (D*σ^beta η) a
  let out:=fun tab (y : (mixedPrepared w n k p θ G t hp e).Ω)=>
    (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
      (fun i=>book.chronoChoose hdim hτ hτsmall ((e y.1).supports y.2 i))
      (fun _=>chronoRead (16*scaleKstar σ η D))
      (integerTargets w n k p θ G t hp e r J (D*σ^beta η) a y) tab
      (integerTree w n k p θ G t hp e r J (D*σ^beta η) a fallback y) (univ,univ)).length
  have hlocal : ∀ z,(∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) (16*scaleKstar σ η D))).mass tab*
      ∑ y,(e z).μ.mass y*((pop z.val:ℝ)-(out tab ⟨z,y⟩:ℝ)))≤(pop z.val:ℝ)*loss := by
    intro z
    dsimp only [pop,out,integerPop,integerTree,integerLive,integerBad]
    unfold integerTargets
    convert he z using 1 <;> simp only [integerBad,Nat.cast_sum] <;> rfl
  have hdelete := bad_predeletion_five w n k p θ G t hkn hp
    (integerBad (d:=d) w n k p θ G t r J (D*σ^beta η) a) _ hbad hrep
  have hres := attachedPrepared_loss w n k p θ G t hp e
    (Law.ofPublic (PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) (16*scaleKstar σ η D))))
    (w*(2*(n+k))) pop out loss _ hloss.le
    (fun z=>goodPopulation_size w n k p θ G t z _ _) hlocal
    (by simpa only [pop,integerPop,integerLive,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hdelete)
  simpa only [Law.ofPublic,out,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hres
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerQuarter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.quarterBanks
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.quarterFinDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.quarterSlotDec
local instance quarterBlockDec_r3d0606_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
theorem eventually_integer_quarter (d : ℕ) (η C A C0 c : ℝ)
    (hη : 0<η) (hC : 0<C) (hC0 : 0≤C0) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      ∀ (hdim : Module.finrank K V=d+3), log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
        (hτ : 0≤τ) (hτsmall : τ≤1/40000)
        (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J M budget : ℝ),
        ∀ (hn : 2≤n), 0<k → k≤n → (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
        (∀ z i,log (S z i).card≤J) →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,IntegerBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        (∀ ω,p.mass ω≠0→∀ W : Submodule K V,
          ((univ.filter (fun i=>G ω i∈orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ)≤M) →
        (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
          entropy ((p.cond θ z).map G)))≤budget →
        budget≤C0*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) → M≤C0*σ →
        c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
        c*(Nat.card K:ℝ)*σ^(1+η/2)≤n →
        ∀ fallback : Fin w, ∃ t : Fin k,
        let hp:=contextual_positive n k (by omega : 0<n) p θ G
          (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t
        ∃ e : ∀ z : PositiveHistory w n k p θ G t hp,
          Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
            (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))),
        let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
        let expmt:=attachedPrepared w n k p θ G t hp e
        (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
          ∑ ω,expmt.μ.mass ω*((w*(2*(n+k)):ℝ)-
            (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
              (fun i=>book.chronoChoose hdim hτ hτsmall ((e ω.1.1).supports ω.1.2 i))
              (fun _=>chronoRead b) (integerTargets w n k p θ G t hp e r J (D*σ^beta η) a ω.1) tab
              (integerTree w n k p θ G t hp e r J (D*σ^beta η) a fallback ω.1) (univ,univ)).length))≤
          (w*(2*(n+k)):ℝ)/4 := by
  filter_upwards [eventually_integer_experiment d η C A (1/8) hη hC (by norm_num),
    eventually_integer_bad_small η C0 c (1/40) hη hC0 hc (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ hex hsmall hσ
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hτ hτsmall Ω Θ _ _ w n k p θ G S u r J M budget hn hk hkn hw hr hJ hM hSJ hS hf hcon hcap hband ho hbudget hb hM0 hk0 hn0 fallback
  obtain ⟨t,e,he⟩:=hex K V hdim hlog D P H hDl hDu book hτ hτsmall Ω Θ w n k p θ G S u r J M budget
    hn hk hkn hw hr hJ hM hSJ hS hf hcon hcap hband ho hbudget fallback
  refine ⟨t,e,?_⟩
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  have hσ0 : 0<σ := by linarith
  have hD : 0<D := (rpow_pos_of_pos hσ0 _).trans_le hDl
  have hbad:=hsmall (Nat.card K) D (w*(2*(n+k)):ℝ) budget M n k hq hD (by positivity) hb hM0 hk0 hn0
  have hcard : (Fintype.card (Slot w (n+k)):ℝ)=2*(w*(2*(n+k)):ℝ) := by
    simp only [Slot,Fintype.card_prod,Fintype.card_fin,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  dsimp only at he hbad ⊢
  apply he.trans
  rw [hcard]
  have heq : 2*(2*(w*(2*(n+k)):ℝ))*M=4*(w*(2*(n+k)):ℝ)*M := by ring
  rw [heq]
  nlinarith
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}

local instance outputBanks_r3d0606_1 : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance outputFinDec_r3d0606_1 (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.outputSlotDec
local instance outputBlockDec_r3d0606_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
theorem eventually_integer_output_oai (d : ℕ) (η C A C0 c : ℝ)
    (hη : 0<η) (hC : 0<C) (hC0 : 0≤C0) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (_ : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
        (_ : 0≤b) (_ : 0≤H) (_ : 4≤P) (_ : b+log 1000000≤P)
        (_ : 0≤τ) (_ : τ≤1/40000)
        (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J M budget : ℝ),
        2≤n → 0<k → k≤n → (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
        (∀ z i,log (S z i).card≤J) →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,IntegerBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        (∀ ω,p.mass ω≠0→∀ W : Submodule K V,
          ((univ.filter (fun i=>G ω i∈orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ)≤M) →
        (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
          entropy ((p.cond θ z).map G)))≤budget →
        budget≤C0*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) → M≤C0*σ →
        c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
        c*(Nat.card K:ℝ)*σ^(1+η/2)≤n →
        Fin w →
        Nonempty (ContextOutput p (fun ω=>flattenTuple (G ω)) (w*(n+k))
          (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
          (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
            w (Nat.log 2 w+1) (2*(n+k))) 2) := by
  filter_upwards [eventually_integer_quarter d η C A C0 c hη hC hC0 hc] with σ hex
  intro K V _ _ _ _ _ _ _ _ hdim hlog D P H hDl hDu
  dsimp only
  intro book hb hH hP haP hτ hτsmall Ω Θ _ _ w n k p θ G S u r J M budget hn hk hkn hw hr hJ hM hSJ hS hf hcon hcap hband ho hbudget hbudget0 hM0 hk0 hn0 fallback
  obtain ⟨t,e,he⟩:=hex K V hdim hlog D P H hDl hDu book hτ hτsmall Ω Θ w n k p θ G S u r J M budget
    hn hk hkn hw hr hJ hM hSJ hS hf hcon hcap hband ho hbudget hbudget0 hM0 hk0 hn0 fallback
  let hp:=contextual_positive n k (by omega : 0<n) p θ G
    (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t
  exact prepared_context_of_mean w n k p θ G t hp e
    (integerBad (d:=d) w n k p θ G t r J (D*σ^beta η) (σ^(-2000*beta η)/(Nat.card K:ℝ)))
    (integerLive (d:=d) w n k p θ G t r J (D*σ^beta η) (σ^(-2000*beta η)/(Nat.card K:ℝ)))
    fallback hdim book hb hH hP haP hτ hτsmall (by omega) he
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output_oai := @OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output_oai
