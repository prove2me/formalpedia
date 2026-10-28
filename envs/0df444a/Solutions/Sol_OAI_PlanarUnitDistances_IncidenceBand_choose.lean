-- Prove2me | solution 1 for OAI.PlanarUnitDistances.IncidenceBand.choose
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T02:57:59.348465+00:00
-- url     : https://prove2.me/submissions/0fc10354-762b-4bb9-90b7-95620323db73

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceBook_constants
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceEstimates_upper
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceNoise_limit
import Theorems.Thm_OAI_PlanarUnitDistances_IncidenceScale_scale_limit

section
-- module Solutions.OAIQ2_Uni.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Cross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma avg_congr (μ : Law X) {f g : X → ℝ} (h : ∀ x, f x = g x) : avg μ f = avg μ g := by
  unfold avg
  exact sum_congr rfl (fun x _ => congrArg (μ.val x * ·) (h x))
lemma avg_ite (μ : Law X) (P : X → Prop) [DecidablePred P] :
    avg μ (fun x => if P x then 1 else 0) = event μ P := by
  unfold event
  apply avg_congr
  intro x
  split_ifs <;> rfl

lemma avg_const (μ : Law X) (c : ℝ) : avg μ (fun _ => c) = c := by
  simp [avg,← sum_mul,μ.total]
lemma avg_add (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x+g x)=avg μ f+avg μ g := by simp [avg,mul_add,sum_add_distrib]
lemma avg_sub (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x-g x)=avg μ f-avg μ g := by simp [avg,mul_sub,sum_sub_distrib]
lemma avg_smul (μ : Law X) (c : ℝ) (f : X  →  ℝ) :
    avg μ (fun x => c*f x)=c*avg μ f := by simp [avg,mul_left_comm, mul_sum]
lemma avg_mono (μ : Law X) {f g : X  →  ℝ} (h : ∀ x,f x ≤ g x) : avg μ f ≤ avg μ g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x)
lemma avg_le_const (μ : Law X) {f : X  →  ℝ} {c : ℝ} (h : ∀ x,f x ≤ c) : avg μ f ≤ c :=
  (avg_mono μ h).trans_eq (avg_const μ c)
lemma const_le_avg (μ : Law X) {f : X  →  ℝ} {c : ℝ} (h : ∀ x,c ≤ f x) : c ≤ avg μ f :=
  (avg_const μ c).symm.trans_le (avg_mono μ h)
lemma event_le_one (μ : Law X) (P : X  →  Prop) : event μ P ≤ 1 := by
  classical
  apply avg_le_const; intro x; split <;> norm_num
lemma event_compl (μ : Law X) (P : X  →  Prop) : event μ (fun x => ¬P x)=1-event μ P := by
  classical
  calc
    event μ (fun x => ¬P x) = avg μ (fun x => 1 - if P x then 1 else 0) := by
      apply avg_congr
      intro x
      split_ifs <;> simp_all
    _ = 1 - event μ P := by rw [avg_sub,avg_const,avg_ite]
lemma event_mono (μ : Law X) {P Q : X  →  Prop} (h : ∀ x,P x → Q x) : event μ P ≤ event μ Q := by
  classical
  apply avg_mono; intro x; split_ifs <;> simp_all
lemma event_union_le (μ : Law X) (P Q : X  →  Prop) :
    event μ (fun x => P x ∨ Q x) ≤ event μ P+event μ Q := by
  classical
  unfold event
  rw [← avg_add]
  apply avg_mono; intro x; split_ifs <;> simp_all

lemma pair_avg (μ : Law X) (ν : Law Y) (f : X×Y → ℝ) :
    avg (pair μ ν) f=avg μ (fun x => avg ν (fun y => f (x,y))) := by
  simp [avg,pair,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma pair_fst (μ : Law X) (ν : Law Y) (f : X → ℝ) :
    avg (pair μ ν) (fun x => f x.1)=avg μ f := by
  rw [pair_avg]; simp_rw [avg_const]
lemma pair_snd (μ : Law X) (ν : Law Y) (f : Y → ℝ) :
    avg (pair μ ν) (fun x => f x.2)=avg ν f := by
  rw [pair_avg]; dsimp only; rw [avg_const]
lemma pair_prod (μ : Law X) (ν : Law Y) (f : X → ℝ) (g : Y → ℝ) :
    avg (pair μ ν) (fun x => f x.1*g x.2)=avg μ f*avg ν g := by
  rw [pair_avg]; dsimp only; simp_rw [avg_smul];
  simp only [avg, ← mul_assoc, sum_mul]
lemma pair_union (μ : Law X) (P : X → Prop) :
    event (pair μ μ) (fun x => P x.1 ∨ P x.2)  ≤  2*event μ P := by
  classical
  have h := event_union_le (pair μ μ) (fun x => P x.1) (fun x => P x.2)
  have h₁ : event (pair μ μ) (fun x => P x.1) = event μ P := by
    rw [← avg_ite (pair μ μ) (fun x => P x.1), ← avg_ite μ P]
    exact pair_fst μ μ (fun x => if P x then 1 else 0)
  have h₂ : event (pair μ μ) (fun x => P x.2) = event μ P := by
    rw [← avg_ite (pair μ μ) (fun x => P x.2), ← avg_ite μ P]
    exact pair_snd μ μ (fun x => if P x then 1 else 0)
  rw [h₁,h₂] at h
  linarith
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.StrictCross
open Set
variable {A B : Type*}

lemma same_row {a : A} {b c : B} (hbc : b ≠ c) (x : A × B) :
    Adj x (a,b) ∧ Adj x (a,c) ↔ x.1=a ∧ x.2≠b ∧ x.2≠c := by
  simp only [Adj]
  constructor
  · rintro ⟨h,h'⟩
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rcases h' with ⟨_,hc⟩ | ⟨hc,_⟩
      · exact ⟨ha,hb,hc⟩
      · exact (hc ha).elim
    · rcases h' with ⟨hc,_⟩ | ⟨_,hc⟩
      · exact (ha hc).elim
      · exact (hbc (hb.symm.trans hc)).elim
  · rintro ⟨ha,hb,hc⟩; exact ⟨Or.inl ⟨ha,hb⟩,Or.inl ⟨ha,hc⟩⟩

lemma swap_iff (x y : A × B) : Adj x.swap y.swap ↔ Adj x y := by
  simp only [Adj,Prod.fst_swap,Prod.snd_swap]
  tauto

lemma same_column {a c : A} {b : B} (hac : a ≠ c) (x : A × B) :
    Adj x (a,b) ∧ Adj x (c,b) ↔ x.2=b ∧ x.1≠a ∧ x.1≠c := by
  have h := same_row (a := b) hac x.swap
  rw [show (b,a) = (a,b).swap from rfl, show (b,c) = (c,b).swap from rfl,
    swap_iff,swap_iff] at h
  exact h

lemma corners {a c : A} {b d : B} (hac : a ≠ c) (hbd : b ≠ d) (x : A × B) :
    Adj x (a,b) ∧ Adj x (c,d) ↔ x=(a,d) ∨ x=(c,b) := by
  constructor
  · rintro ⟨h,h'⟩
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases h' with ⟨hc,hd⟩ | ⟨hc,hd⟩
    · exact (hac (ha.symm.trans hc)).elim
    · exact Or.inl (Prod.ext ha hd)
    · exact Or.inr (Prod.ext hc hb)
    · exact (hbd (hb.symm.trans hd)).elim
  · rintro (rfl|rfl) <;> simp [Adj,hac,hbd,Ne.symm hac,Ne.symm hbd]

lemma third_off_row {a c : A} {b d e : B} (hbd : b ≠ d) (hac : a ≠ c)
    (x : A × B) (h₁ : Adj x (a,b)) (h₂ : Adj x (a,d)) (h₃ : Adj x (c,e)) :
    x=(a,e) := by
  have hx := (same_row hbd x).mp ⟨h₁,h₂⟩
  rcases h₃ with h | h
  · exact (hac (hx.1.symm.trans h.1)).elim
  · exact Prod.ext hx.1 h.2

lemma three_independent {a c e : A} {b d f : B}
    (hac : a ≠ c) (hae : a ≠ e) (hce : c ≠ e)
    (hbd : b ≠ d) (hbf : b ≠ f) (hdf : d ≠ f) (x : A × B) :
    ¬(Adj x (a,b) ∧ Adj x (c,d) ∧ Adj x (e,f)) := by
  rintro ⟨h₁,h₂,h₃⟩
  rcases (corners hac hbd x).mp ⟨h₁,h₂⟩ with h|h <;> rw [h] at h₃
  · simp [Adj,hae,hdf] at h₃
  · simp [Adj,hce,hbf] at h₃

theorem classification (Y : Finset (A × B)) :
    Y.card ≤ 1 ∨
    (∃ y∈Y, ∃ z∈Y, y≠z ∧ y.1=z.1 ∧
      ((∀ w∈Y,w.1=y.1) ∨ ∃ w∈Y,w.1≠y.1)) ∨
    (∃ y∈Y, ∃ z∈Y, y≠z ∧ y.2=z.2 ∧
      ((∀ w∈Y,w.2=y.2) ∨ ∃ w∈Y,w.2≠y.2)) ∨
    (∃ y∈Y, ∃ z∈Y, y.1≠z.1 ∧ y.2≠z.2 ∧
      ((∀ w∈Y,w=y ∨ w=z) ∨ ∃ w∈Y,
        y.1≠w.1 ∧ z.1≠w.1 ∧ y.2≠w.2 ∧ z.2≠w.2)) := by
  classical
  by_cases hs : Y.card ≤ 1
  · exact Or.inl hs
  have he : ∃ y∈Y,∃ z∈Y,y≠z := by
    by_contra! h
    exact hs (Finset.card_le_one.mpr h)
  rcases he with ⟨y,hy,z,hz,hyz⟩
  by_cases hr : ∃ y∈Y,∃ z∈Y,y≠z ∧ y.1=z.1
  · obtain ⟨y,hy,z,hz,hn,he⟩ := hr
    refine Or.inr (Or.inl ⟨y,hy,z,hz,hn,he,?_⟩)
    by_cases hw : ∀ w∈Y,w.1=y.1
    · exact Or.inl hw
    · exact Or.inr (by simpa only [not_forall,exists_prop] using hw)
  by_cases hc : ∃ y∈Y,∃ z∈Y,y≠z ∧ y.2=z.2
  · obtain ⟨y,hy,z,hz,hn,he⟩ := hc
    refine Or.inr (Or.inr (Or.inl ⟨y,hy,z,hz,hn,he,?_⟩))
    by_cases hw : ∀ w∈Y,w.2=y.2
    · exact Or.inl hw
    · exact Or.inr (by simpa only [not_forall,exists_prop] using hw)
  have h₁ : ∀ u∈Y,∀ v∈Y,u≠v → u.1≠v.1 := by
    intro u hu v hv hn he; exact hr ⟨u,hu,v,hv,hn,he⟩
  have h₂ : ∀ u∈Y,∀ v∈Y,u≠v → u.2≠v.2 := by
    intro u hu v hv hn he; exact hc ⟨u,hu,v,hv,hn,he⟩
  refine Or.inr (Or.inr (Or.inr ⟨y,hy,z,hz,h₁ y hy z hz hyz,h₂ y hy z hz hyz,?_⟩))
  by_cases hw : ∀ w∈Y,w=y ∨ w=z
  · exact Or.inl hw
  · obtain ⟨w,hw,hwy,hwz⟩ : ∃ w∈Y,w≠y ∧ w≠z := by
      simpa only [not_forall,not_or,exists_prop] using hw
    exact Or.inr ⟨w,hw,h₁ y hy w hw (Ne.symm hwy),h₁ z hz w hw (Ne.symm hwz),
      h₂ y hy w hw (Ne.symm hwy),h₂ z hz w hw (Ne.symm hwz)⟩

lemma coefficient_lower (r : ℝ) : 1-1/20000 ≤ coefficient r := by
  unfold coefficient; split <;> norm_num

lemma score_polynomial (r : ℝ) :
    coefficient r * (r^2+(1-r)^2)-2*r*(1-r) ≥ (1/40000:ℝ) := by
  unfold coefficient
  split_ifs with h
  · nlinarith [sq_nonneg (2*r-1)]
  · have hn : (1/100:ℝ) < |r-1/2| := lt_of_not_ge h
    have hh : (1/100:ℝ)^2 < |r-1/2|^2 := (sq_lt_sq₀ (by norm_num) (abs_nonneg _)).mpr hn
    rw [sq_abs] at hh
    nlinarith [sq_nonneg (2*r-1)]
end PlanarUnitDistances.StrictCross

namespace PlanarUnitDistances.StarScore
open FiniteLaw StrictCross
noncomputable section
variable {X A B : Type*} [Fintype X]

lemma frequency_nonneg (μ : Law X) (bit : X  →  Bool) : 0 ≤ frequency μ bit := event_nonneg _ _
lemma frequency_le_one (μ : Law X) (bit : X  →  Bool) : frequency μ bit ≤ 1 := event_le_one _ _
lemma variation_nonneg (μ : Law X) (bit : X  →  Bool) : 0 ≤ variation μ bit := by
  unfold variation
  exact mul_nonneg (mul_nonneg (by norm_num) (frequency_nonneg _ _))
    (sub_nonneg.mpr (frequency_le_one _ _))
lemma variation_le_half (μ : Law X) (bit : X  →  Bool) : variation μ bit ≤ 1/2 := by
  unfold variation; nlinarith [sq_nonneg (frequency μ bit-1/2)]

lemma coefficient_upper (r : ℝ) : coefficient r ≤ 2 := by
  unfold coefficient; split <;> norm_num
lemma coefficient_nonneg (r : ℝ) : 0 ≤ coefficient r := by
  linarith [coefficient_lower r]
omit [Fintype X] in
lemma slot_lower (r : ℝ) (bit : X → Bool) (state : X → A×B) (x y : X) :
    -1 ≤ slot r bit state x y := by
  unfold slot
  split_ifs <;> linarith [coefficient_nonneg r]

lemma mismatch (μ : Law X) (bit : X → Bool) :
    event (pair μ μ) (fun x => bit x.1≠bit x.2)=variation μ bit := by
  classical
  let f : X → ℝ := fun x => if bit x then 1 else 0
  have he (x : X×X) : (if bit x.1≠bit x.2 then (1:ℝ) else 0)=
      f x.1+f x.2-2*(f x.1*f x.2) := by
    dsimp [f]; cases h₁ : bit x.1 <;> cases h₂ : bit x.2 <;> norm_num
  rw [← avg_ite]
  have heq := avg_congr (pair μ μ) he
  rw [heq]
  rw [avg_sub,avg_add,avg_smul,pair_fst,pair_snd,pair_prod]
  have hf : avg μ f = frequency μ bit := by
    dsimp only [f,frequency]
    exact avg_ite _ _
  rw [hf]
  unfold variation; ring

lemma score_lower (μ : Law X) (bit : X → Bool) (state : X → A×B) :
    -variation μ bit ≤ score μ bit state := by
  classical
  have h (x : X×X) : -(if bit x.1≠bit x.2 then (1:ℝ) else 0)  ≤
      slot (frequency μ bit) bit state x.1 x.2 := by
    unfold slot; split_ifs <;> simp_all [coefficient_nonneg]
  have ha := avg_mono (pair μ μ) h
  have he : (fun x : X×X => -(if bit x.1 ≠ bit x.2 then (1:ℝ) else 0))=
      (fun x => (-1)*(if bit x.1≠bit x.2 then (1:ℝ) else 0)) := by funext; ring
  rw [he,avg_smul] at ha
  rw [avg_ite,mismatch,neg_one_mul] at ha
  exact ha

lemma score_ge_half_neg (μ : Law X) (bit : X → Bool) (state : X → A×B) :
    -(1/2:ℝ) ≤ score μ bit state := le_trans (by linarith [variation_le_half μ bit])
      (score_lower μ bit state)

theorem determined (μ : Law X) (bit : X → Bool) (state : X → A×B) (good : X → Prop)
    (h : ∀ x y,good x → good y → bit x=bit y → state x=state y) :
    (1/40000:ℝ)-6*event μ (fun x => ¬good x) ≤ score μ bit state := by
  classical
  let c := coefficient (frequency μ bit)
  have hpoint (x : X×X) :
      c-(c+1)*(if bit x.1≠bit x.2 then (1:ℝ) else 0)-
        3*(if ¬good x.1 ∨ ¬good x.2 then (1:ℝ) else 0)  ≤
      slot (frequency μ bit) bit state x.1 x.2 := by
    by_cases hg : good x.1 ∧ good x.2
    · have hg' : ¬(¬good x.1 ∨ ¬good x.2) := by tauto
      simp only [hg',ite_false,mul_zero,sub_zero]
      by_cases hb : bit x.1=bit x.2
      · have hs := h _ _ hg.1 hg.2 hb
        simp [slot,hb,hs,c]
      · simp [slot,hb]
    · have hbad : ¬good x.1 ∨ ¬good x.2 := by tauto
      simp only [hbad,ite_true,mul_one]
      have hc : c ≤ 2 := coefficient_upper _
      by_cases hb : bit x.1=bit x.2
      · simp only [hb,ne_eq,not_true_eq_false,ite_false,mul_zero,sub_zero]
        linarith [slot_lower (frequency μ bit) bit state x.1 x.2]
      · simp only [hb,ne_eq,not_false_eq_true,ite_true,mul_one]
        linarith [slot_lower (frequency μ bit) bit state x.1 x.2]
  have ha := avg_mono (pair μ μ) hpoint
  rw [avg_sub,avg_sub,avg_const,avg_smul,avg_smul] at ha
  rw [avg_ite,avg_ite] at ha
  rw [mismatch] at ha
  have hu := pair_union μ (fun x => ¬good x)
  have hn := score_polynomial (frequency μ bit)
  change c * _ - _  ≥  _ at hn
  unfold variation at ha
  unfold score
  nlinarith

theorem constant_good (μ : Law X) (bit : X → Bool) (state : X → A×B) (good : X → Prop)
    (h : ∀ x y,good x → good y → bit x=bit y ∧ state x=state y) :
    (1-1/20000:ℝ)-4*event μ (fun x => ¬good x) ≤ score μ bit state := by
  classical
  have hpoint (x : X×X) : (1-1/20000:ℝ)-
      2*(if ¬good x.1 ∨ ¬good x.2 then (1:ℝ) else 0)  ≤
      slot (frequency μ bit) bit state x.1 x.2 := by
    by_cases hg : good x.1 ∧ good x.2
    · have hg' : ¬(¬good x.1 ∨ ¬good x.2) := by tauto
      obtain ⟨hb,hs⟩ := h _ _ hg.1 hg.2
      simpa [slot,hg',hb,hs] using coefficient_lower (frequency μ bit)
    · have hbad : ¬good x.1 ∨ ¬good x.2 := by tauto
      simp only [hbad,ite_true,mul_one]
      linarith [slot_lower (frequency μ bit) bit state x.1 x.2]
  have ha := avg_mono (pair μ μ) hpoint
  rw [avg_sub,avg_const,avg_smul] at ha
  rw [avg_ite] at ha
  unfold score
  linarith [pair_union μ (fun x => ¬good x)]

theorem constant_bit (μ : Law X) (bit : X → Bool) (good : X → Prop)
    (h : ∀ x y,good x → good y → bit x=bit y) :
    variation μ bit ≤ 2*event μ (fun x => ¬good x) := by
  rw [← mismatch]
  apply le_trans (event_mono (pair μ μ) (fun x hx => ?_)) (pair_union μ (fun x => ¬good x))
  by_contra! he
  exact hx (h _ _ he.1 he.2)
end
end PlanarUnitDistances.StarScore

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
open scoped Classical
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma atom_le_fiber (μ : Law X) (φ : X → Y) (x : X) : μ.val x ≤ fiberMass μ φ (φ x) := by
  classical
  rw [fiberMass_eq]
  have h := single_le_sum (s := univ) (f := fun y => if φ y=φ x then μ.val y else 0)
    (fun y _ => by split_ifs <;> simp [μ.nonneg]) (mem_univ x)
  simpa using h

lemma push_avg (μ : Law X) (φ : X → Y) (g : Y → ℝ) :
    avg (push μ φ) g = avg μ (fun x => g (φ x)) := by
  classical
  unfold avg push
  simp only [fiberMass_eq,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp

omit [Fintype Y] in
lemma cond_weight (μ : Law X) (φ : X → Y) (y : Y) (x : X) :
    fiberMass μ φ y * (cond μ φ y).val x = if φ x=y then μ.val x else 0 := by
  classical
  by_cases hy : 0 < fiberMass μ φ y
  · simp only [cond,hy,↓reduceDIte]
    split_ifs
    · field_simp
    · ring
  · have hz := le_antisymm (le_of_not_gt hy) (fiberMass_nonneg μ φ y)
    simp only [hz,zero_mul]
    split_ifs with hxy
    · have h := atom_le_fiber μ φ x
      rw [hxy,hz] at h
      exact (le_antisymm h (μ.nonneg x)).symm
    · rfl

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.RestrictedTransfer
open Finset

section Mass
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {ν : X → ℝ}
omit [Fintype X] [DecidableEq X] in
lemma mass_nonneg (hν : ∀ x, 0 ≤ ν x) (s : Finset X) : 0 ≤ mass ν s :=
  sum_nonneg (fun x _ => hν x)
omit [Fintype X] [DecidableEq X] in
lemma mass_mono (hν : ∀ x, 0 ≤ ν x) {s t : Finset X} (h : s ⊆ t) :
    mass ν s ≤ mass ν t := sum_le_sum_of_subset_of_nonneg h (fun x _ _ => hν x)
lemma mass_compl (hν : ∑ x, ν x = 1) (s : Finset X) : mass ν sᶜ = 1 - mass ν s := by
  have h := sum_compl_add_sum s ν
  dsimp [mass]
  linarith
omit [Fintype X] in
lemma mass_union_le (hν : ∀ x, 0 ≤ ν x) (s t : Finset X) :
    mass ν (s ∪ t) ≤ mass ν s + mass ν t := by
  have he := sum_union_inter (s₁ := s) (s₂ := t) (f := ν)
  have hi : 0 ≤ ∑ x ∈ s ∩ t, ν x := sum_nonneg (fun x _ => hν x)
  dsimp [mass]
  linarith
omit [Fintype X] [DecidableEq X] in
lemma atom_le_mass (hν : ∀ x, 0 ≤ ν x) {s : Finset X} {x : X} (hx : x ∈ s) :
    ν x ≤ mass ν s := single_le_sum (fun y _ => hν y) hx
omit [DecidableEq X] in
lemma mass_le_one (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (s : Finset X) :
    mass ν s ≤ 1 := by simpa [mass, hs] using mass_mono hν (subset_univ s)
end Mass

section Supports
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma high_row_unique {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : η < 1/2) {a a' : A}
    (ha : 1-η ≤ mass ν (row a)) (ha' : 1-η ≤ mass ν (row a')) : a = a' := by
  by_contra hn
  have hd : Disjoint (row a : Finset (A × B)) (row a') := by
    simp only [disjoint_left, row, mem_filter, mem_univ, true_and]
    intro x hx hx'
    exact hn (hx.symm.trans hx')
  have hu := mass_le_one hν hs (row a ∪ row a')
  rw [mass, sum_union hd] at hu
  change mass ν (row a) + mass ν (row a') ≤ 1 at hu
  linarith

lemma high_col_unique {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : η < 1/2) {b b' : B}
    (hb : 1-η ≤ mass ν (col b)) (hb' : 1-η ≤ mass ν (col b')) : b = b' := by
  by_contra hn
  have hd : Disjoint (col b : Finset (A × B)) (col b') := by
    simp only [disjoint_left, col, mem_filter, mem_univ, true_and]
    intro x hx hx'
    exact hn (hx.symm.trans hx')
  have hu := mass_le_one hν hs (col b ∪ col b')
  rw [mass, sum_union hd] at hu
  change mass ν (col b) + mass ν (col b') ≤ 1 at hu
  linarith

lemma rowException_mass {ν : A × B → ℝ} (hs : ∑ x, ν x = 1)
    {η : ℝ} (hη : 0 ≤ η) : mass ν (rowException ν η) ≤ η := by
  unfold rowException
  split_ifs with h
  · rw [mass_compl hs]; linarith [h.choose_spec]
  · simpa [mass] using hη
lemma colException_mass {ν : A × B → ℝ} (hs : ∑ x, ν x = 1)
    {η : ℝ} (hη : 0 ≤ η) : mass ν (colException ν η) ≤ η := by
  unfold colException
  split_ifs with h
  · rw [mass_compl hs]; linarith [h.choose_spec]
  · simpa [mass] using hη

lemma smallException_mass {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : 0 ≤ η) :
    mass ν (smallException ν η) ≤ 3*η := by
  classical
  unfold smallException
  split_ifs with h
  · obtain ⟨U, hUcard, hU⟩ := h
    have hsub : univ.filter (fun x => ν x ≤ η) ⊆
        Uᶜ ∪ U.filter (fun x => ν x ≤ η) := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact mem_union_right _ (mem_filter.mpr ⟨hxU, (mem_filter.mp hx).2⟩)
      · exact mem_union_left _ (mem_compl.mpr hxU)
    have hsmall : mass ν (U.filter (fun x => ν x ≤ η)) ≤ 2*η := by
      calc
        _ ≤ ∑ _x ∈ U.filter (fun x => ν x ≤ η), η :=
          sum_le_sum (fun x hx => (mem_filter.mp hx).2)
        _ = ((U.filter (fun x => ν x ≤ η)).card : ℝ) * η := by simp
        _ ≤ 2*η := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (card_filter_le U _).trans hUcard) hη
    have huu := mass_union_le hν Uᶜ (U.filter (fun x => ν x ≤ η))
    have hmm := mass_mono hν hsub
    rw [mass_compl hs] at huu
    linarith
  · simp [mass]; positivity

lemma exception_mass {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : 0 ≤ η) :
    mass ν (exception ν η) ≤ 5*η := by
  have h₁ := mass_union_le hν (rowException ν η) (colException ν η)
  have h₂ := mass_union_le hν (rowException ν η ∪ colException ν η) (smallException ν η)
  have h₃ := rowException_mass hs hη
  have h₄ := colException_mass hs hη
  have h₅ := smallException_mass hν hs hη
  dsimp [exception]
  linarith

lemma outside_exception_mem {ν : A × B → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hs : ∑ x, ν x = 1) {η : ℝ} (hη : η < 1/2)
    {U : Finset (A × B)} (hU : Permitted U) (hm : 1-η ≤ mass ν U)
    {x : A × B} (hx : x ∉ exception ν η) : x ∈ U := by
  classical
  have hxR : x ∉ rowException ν η := fun h => hx (mem_union_left _ (mem_union_left _ h))
  have hxC : x ∉ colException ν η := fun h => hx (mem_union_left _ (mem_union_right _ h))
  have hxS : x ∉ smallException ν η := fun h => hx (mem_union_right _ h)
  rcases hU with ⟨a, rfl⟩ | ⟨b, rfl⟩ | hcard
  · have h : ∃ a', 1-η ≤ mass ν (row a') := ⟨a, hm⟩
    simp only [rowException, dite_eq_left h, mem_compl, not_not] at hxR
    have he := high_row_unique hν hs hη h.choose_spec hm
    simpa only [he] using hxR
  · have h : ∃ b', 1-η ≤ mass ν (col b') := ⟨b, hm⟩
    simp only [colException, dite_eq_left h, mem_compl, not_not] at hxC
    have he := high_col_unique hν hs hη h.choose_spec hm
    simpa only [he] using hxC
  · have h : ∃ U', U'.card ≤ 2 ∧ 1-η ≤ mass ν U' := ⟨U, hcard, hm⟩
    simp only [smallException, ite_eq_left h, mem_filter, mem_univ, true_and, not_le] at hxS
    by_contra hxn
    have ha := atom_le_mass hν (mem_compl.mpr hxn)
    rw [mass_compl hs] at ha
    linarith
end Supports

section Posterior
variable {P H A B : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]
  [DecidableEq H] [DecidableEq A] [DecidableEq B]

omit [Fintype H] in
lemma historyMass_nonneg (μ : P → ℝ) (hμ : ∀ p, 0 ≤ μ p) (h : P → H) (a : H) :
    0 ≤ historyMass μ h a := sum_nonneg fun p _ => by split; exact hμ p; exact le_rfl
omit [Fintype H] in
lemma historyMass_pos (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → H) (p : P) :
    0 < historyMass μ h (h p) := by
  apply lt_of_lt_of_le (hμ p)
  have hh := single_le_sum (f := fun x => if h x = h p then μ x else 0)
    (fun x _ => by split; exact (hμ x).le; exact le_rfl) (mem_univ p)
  simpa [historyMass] using hh
omit [Fintype H] in
lemma posterior_nonneg (μ : P → ℝ) (hμ : ∀ p, 0 ≤ μ p) (h : P → H) (a : H) (p : P) :
    0 ≤ posterior μ h a p := by
  unfold posterior
  exact div_nonneg (by split; exact hμ p; exact le_rfl) (historyMass_nonneg μ hμ h a)
omit [Fintype H] in
lemma posterior_stationary (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → H) (x : P) :
    ∑ p, μ p * posterior μ h (h p) x = μ x := by
  have he (p : P) : μ p * posterior μ h (h p) x =
      (if h p = h x then μ p else 0) * (μ x / historyMass μ h (h x)) := by
    by_cases hp : h p = h x
    · simp [posterior, hp]
    · simp [posterior, hp, Ne.symm hp]
  simp_rw [he]
  rw [← sum_mul]
  change historyMass μ h (h x) * (μ x / historyMass μ h (h x)) = μ x
  exact mul_div_cancel₀ _ (historyMass_pos μ hμ h x).ne'

omit [Fintype H] in
lemma posterior_function (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (h : P → H) (f : H → P → ℝ) :
    (∑ p, μ p * ∑ x, posterior μ h (h p) x * f (h p) x) =
      ∑ x, μ x * f (h x) x := by
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  have he (p : P) : μ p * (posterior μ h (h p) x * f (h p) x) =
      (μ p * posterior μ h (h p) x) * f (h x) x := by
    by_cases hp : h p = h x
    · rw [hp]; ring
    · simp [posterior, Ne.symm hp]
  simp_rw [he]
  rw [← sum_mul, posterior_stationary μ hμ h]

omit [Fintype H] [Fintype A] [Fintype B] in
lemma statePosterior_nonneg (μ : P → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    (h : P → H) (X : P → A × B) (a : H) (x : A × B) :
    0 ≤ statePosterior μ h X a x := by
  apply sum_nonneg
  intro p _
  split_ifs
  · exact posterior_nonneg μ hμ h a p
  · rfl
omit [Fintype H] in
lemma statePosterior_sum (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (h : P → H) (X : P → A × B) (p : P) : ∑ x, statePosterior μ h X (h p) x = 1 := by
  unfold statePosterior
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true, posterior, ← sum_div]
  exact div_self (historyMass_pos μ hμ h p).ne'
omit [Fintype H] [Fintype A] [Fintype B] in
lemma statePosterior_mass (μ : P → ℝ) (h : P → H) (X : P → A × B)
    (a : H) (U : Finset (A × B)) :
    mass (statePosterior μ h X a) U =
      ∑ p, posterior μ h a p * if X p ∈ U then 1 else 0 := by
  unfold mass statePosterior
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  by_cases hp : X p ∈ U <;> simp [hp]

omit [Fintype H] in

lemma actual_exception_mass (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (hsμ : ∑ p, μ p = 1) (h : P → H) (X : P → A × B)
    {η : ℝ} (hη : 0 ≤ η) :
    (∑ p, μ p * if X p ∈ exception (statePosterior μ h X (h p)) η then 1 else 0) ≤ 5*η := by
  classical
  let f : H → P → ℝ := fun a p =>
    if X p ∈ exception (statePosterior μ h X a) η then 1 else 0
  have he := posterior_function μ hμ h f
  change (∑ p, μ p * f (h p) p) ≤ 5*η
  rw [← he]
  calc
    _ ≤ ∑ p, μ p * (5*η) := by
      apply sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (hμ p).le
      change (∑ x, posterior μ h (h p) x *
        if X x ∈ exception (statePosterior μ h X (h p)) η then 1 else 0) ≤ 5*η
      rw [← statePosterior_mass]
      exact exception_mass (statePosterior_nonneg μ (fun p => (hμ p).le) h X (h p))
        (statePosterior_sum μ hμ h X p) hη
    _ = 5*η := by rw [← sum_mul, hsμ, one_mul]
end Posterior

section Transfer
variable {P H A B T : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]
  [Fintype T] [DecidableEq H] [DecidableEq A] [DecidableEq B]

omit [Fintype H] in

theorem restricted_transfer (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (hsμ : ∑ p, μ p = 1) (h : P → H) (X : P → A × B)
    (w : P → T → ℝ) (hw : ∀ p t, 0 ≤ w p t) (hwμ : ∀ p, ∑ t, w p t = μ p)
    (U : T → Finset (A × B)) (hU : ∀ t, Permitted (U t))
    (G : T → Prop) [DecidablePred G] {η : ℝ} (hη : 0 < η) (hη' : η < 1/2)
    (hG : ∀ t, G t →
      (∑ p, w p t * mass (statePosterior μ h X (h p)) (U t)ᶜ) ≤
        3*η^2 * ∑ p, w p t) :
    (∑ p, ∑ t, w p t * if G t ∧ X p ∉ U t then 1 else 0) ≤ 8*η := by
  classical
  let ν := statePosterior μ h X
  let exc (p : P) : ℝ := if X p ∈ exception (ν (h p)) η then 1 else 0
  have hexc0 (p : P) : 0 ≤ exc p := by dsimp [exc]; split <;> norm_num
  have hν (p : P) : ∀ x, 0 ≤ ν (h p) x :=
    statePosterior_nonneg μ (fun p => (hμ p).le) h X (h p)
  have hsν (p : P) : ∑ x, ν (h p) x = 1 := statePosterior_sum μ hμ h X p
  have hpt (p : P) (t : T) :
      w p t * (if G t ∧ X p ∉ U t then 1 else 0) ≤
        (if G t then w p t * mass (ν (h p)) (U t)ᶜ / η else 0) + w p t * exc p := by
    have hnn := mul_nonneg (hw p t) (mass_nonneg (hν p) (U t)ᶜ)
    by_cases hg : G t
    · simp only [hg, true_and, ite_true]
      by_cases hx : X p ∈ U t
      · simp only [hx, not_true_eq_false, ite_false, mul_zero]
        exact add_nonneg (div_nonneg hnn hη.le) (mul_nonneg (hw p t) (hexc0 p))
      by_cases hc : 1-η ≤ mass (ν (h p)) (U t)
      · have hxexc : X p ∈ exception (ν (h p)) η := by
          by_contra hn
          exact hx (outside_exception_mem (hν p) (hsν p) hη' (hU t) hc hn)
        simp only [hx, not_false_eq_true, ite_true, mul_one]
        have hex : exc p = 1 := ite_eq_left hxexc
        rw [hex, mul_one]
        linarith [div_nonneg hnn hη.le]
      · have hmc : η ≤ mass (ν (h p)) (U t)ᶜ := by
          rw [mass_compl (hsν p)]; linarith [lt_of_not_ge hc]
        have hmul := mul_le_mul_of_nonneg_left hmc (hw p t)
        have hd : w p t ≤ w p t * mass (ν (h p)) (U t)ᶜ / η :=
          (le_div_iff₀ hη).mpr hmul
        simp only [hx, not_false_eq_true, ite_true, mul_one]
        linarith [mul_nonneg (hw p t) (hexc0 p)]
    · simp only [hg, false_and, ite_false, mul_zero, zero_add]
      exact mul_nonneg (hw p t) (hexc0 p)
  have hlocal (t : T) :
      (∑ p, if G t then w p t * mass (ν (h p)) (U t)ᶜ / η else 0) ≤
        3*η * ∑ p, w p t := by
    by_cases hg : G t
    · simp only [hg, ite_true, ← sum_div]
      apply (div_le_iff₀ hη).mpr
      calc
        _ ≤ 3*η^2 * ∑ p, w p t := hG t hg
        _ = _ := by ring
    · simp only [hg, ite_false, sum_const_zero]
      exact mul_nonneg (by positivity) (sum_nonneg (fun p _ => hw p t))
  have htt : (∑ p, ∑ t, w p t) = 1 := by simp_rw [hwμ]; exact hsμ
  calc
    _ ≤ ∑ p, ∑ t,
          ((if G t then w p t * mass (ν (h p)) (U t)ᶜ / η else 0) + w p t * exc p) :=
      sum_le_sum (fun p _ => sum_le_sum (fun t _ => hpt p t))
    _ = (∑ t, ∑ p, if G t then w p t * mass (ν (h p)) (U t)ᶜ / η else 0) +
        ∑ p, μ p * exc p := by
      simp only [sum_add_distrib, ← sum_mul, hwμ]
      rw [sum_comm]
    _ ≤ (∑ t, 3*η * ∑ p, w p t) + 5*η := by
      apply add_le_add
      · exact sum_le_sum (fun t _ => hlocal t)
      · exact actual_exception_mass μ hμ hsμ h X hη.le
    _ = 8*η := by
      rw [← mul_sum, sum_comm, htt]
      ring
end Transfer

section EdgeTemplate
variable {P Q H A B Θ : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype Θ] [DecidableEq H] [DecidableEq A] [DecidableEq B]

omit [Fintype Q] [Fintype H] [Fintype A] [Fintype B] in
lemma centerMixture_mass (μ : P → ℝ) (h : P → H) (X : P → A × B)
    (edge : P → Q → ℝ) (q : Q) (U : Finset (A × B)) :
    mass (centerMixture μ h X edge q) U =
      (∑ p, edge p q * mass (statePosterior μ h X (h p)) U) / (∑ r, edge r q) := by
  unfold mass centerMixture
  rw [sum_comm]
  simp only [← mul_sum, div_mul_eq_mul_div, ← sum_div]

omit [Fintype H] in

theorem edge_template_transfer (μ : P → ℝ) (hμ : ∀ p, 0 < μ p)
    (hsμ : ∑ p, μ p = 1) (h : P → H) (X : P → A × B)
    (edge : P → Q → ℝ) (he : ∀ p q, 0 ≤ edge p q)
    (heμ : ∀ p, ∑ q, edge p q = μ p) (hκ : ∀ q, 0 < ∑ p, edge p q)
    (a : Q → Θ → ℝ) (ha : ∀ q θ, 0 ≤ a q θ) (has : ∀ q, ∑ θ, a q θ = 1)
    (U : Q → Θ → Finset (A × B)) (hU : ∀ q θ, Permitted (U q θ))
    (G : Q → Θ → Prop) [∀ q, DecidablePred (G q)]
    {η : ℝ} (hη : 0 < η) (hη' : η < 1/2)
    (hg : ∀ q θ, G q θ → 1-3*η^2 ≤ mass (centerMixture μ h X edge q) (U q θ)) :
    (∑ p, ∑ q, ∑ θ, edge p q * a q θ *
      if G q θ ∧ X p ∉ U q θ then 1 else 0) ≤ 8*η := by
  classical
  let w : P → Q × Θ → ℝ := fun p v => edge p v.1 * a v.1 v.2
  have hw : ∀ p v, 0 ≤ w p v := fun p v => mul_nonneg (he p v.1) (ha v.1 v.2)
  have hws (p : P) : ∑ v, w p v = μ p := by
    simp only [w, Fintype.sum_prod_type, ← mul_sum, has, mul_one, heμ]
  have hm (v : Q × Θ) (hv : G v.1 v.2) :
      (∑ p, w p v * mass (statePosterior μ h X (h p)) (U v.1 v.2)ᶜ) ≤
        3*η^2 * ∑ p, w p v := by
    have hg' := hg v.1 v.2 hv
    rw [centerMixture_mass] at hg'
    have hg'' := (le_div_iff₀ (hκ v.1)).mp hg'
    have heq : (∑ p, edge p v.1 * mass (statePosterior μ h X (h p)) (U v.1 v.2)ᶜ) =
        (∑ p, edge p v.1) - ∑ p, edge p v.1 * mass (statePosterior μ h X (h p)) (U v.1 v.2) := by
      simp only [mass_compl (statePosterior_sum μ hμ h X _), mul_sub,
        mul_one, sum_sub_distrib]
    have hh : (∑ p, edge p v.1 * mass (statePosterior μ h X (h p)) (U v.1 v.2)ᶜ) ≤
        3*η^2 * ∑ p, edge p v.1 := by rw [heq]; nlinarith
    have hmult := mul_le_mul_of_nonneg_right hh (ha v.1 v.2)
    calc
      _ = (∑ p, edge p v.1 * mass (statePosterior μ h X (h p)) (U v.1 v.2)ᶜ) *
          a v.1 v.2 := by
        rw [sum_mul]
        apply sum_congr rfl
        intro p _
        dsimp [w]
        ring
      _ ≤ (3*η^2 * ∑ p, edge p v.1) * a v.1 v.2 := hmult
      _ = _ := by simp only [w, ← sum_mul]; ring
  have hfinal := restricted_transfer μ hμ hsμ h X w hw hws
    (fun v => U v.1 v.2) (fun v => hU v.1 v.2)
    (fun v => G v.1 v.2) hη hη' hm
  simpa only [Fintype.sum_prod_type, w] using hfinal
end EdgeTemplate

end PlanarUnitDistances.RestrictedTransfer

namespace PlanarUnitDistances.CrossStructure
open Finset StrictCross RestrictedTransfer
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma consistent_adj {b : Bool} {x y : A×B} (h : Consistent b x y) : Adj x y := by
  cases b with
  | false => exact Or.inr h
  | true => exact Or.inl h
lemma consistent_symm {b : Bool} {x y : A×B} (h : Consistent b x y) : Consistent b y x := by
  cases b <;> dsimp [Consistent] at *
  · exact ⟨Ne.symm h.1,Eq.symm h.2⟩
  · exact ⟨Eq.symm h.1,Ne.symm h.2⟩
lemma bit_unique {b c : Bool} {x y : A×B} (h : Consistent b x y) (h' : Consistent c x y) : b=c := by
  cases b <;> cases c <;> simp_all [Consistent]
lemma bit_true {b : Bool} {x y : A×B} (h : Consistent b x y) (he : x.1=y.1) : b=true := by
  cases b <;> simp_all [Consistent]
lemma bit_false {b : Bool} {x y : A×B} (h : Consistent b x y) (he : x.2=y.2) : b=false := by
  cases b <;> simp_all [Consistent]

lemma card_pair_le (y z : A×B) : ({y,z} : Finset (A×B)).card≤3 := by
  have := card_insert_le y {z}
  simp only [card_singleton] at this
  omega
lemma card_triple_le (y z w : A×B) : ({y,z,w} : Finset (A×B)).card≤3 := by
  have h := card_insert_le y {z,w}
  have h' := card_insert_le z {w}
  simp only [card_singleton] at h'
  omega

lemma pair_coord_inj {S : Finset (A×B)} {y z : A×B} (h : ∀w∈S,w=y ∨ w=z)
    (h₁ : y.1≠z.1) (h₂ : y.2≠z.2) :
    (∀u∈S,∀v∈S,u.1=v.1 → u=v) ∧ (∀u∈S,∀v∈S,u.2=v.2 → u=v) := by
  constructor <;> intro u hu v hv he
  · rcases h u hu with rfl|rfl <;> rcases h v hv with rfl|rfl
    · rfl
    · exact (h₁ he).elim
    · exact (h₁ he.symm).elim
    · rfl
  · rcases h u hu with rfl|rfl <;> rcases h v hv with rfl|rfl
    · rfl
    · exact (h₂ he).elim
    · exact (h₂ he.symm).elim
    · rfl

lemma determined_of_inj {S : Finset (A×B)}
    (h : (∀u∈S,∀v∈S,u.1=v.1 → u=v) ∧ (∀u∈S,∀v∈S,u.2=v.2 → u=v))
    (x : A×B) (y : A×B) (hy : y∈S) (z : A×B) (hz : z∈S) (b : Bool)
    (hc : Consistent b x y) (hd : Consistent b x z) : y=z := by
  cases b with
  | false => exact h.2 y hy z hz (hc.2.symm.trans hd.2)
  | true => exact h.1 y hy z hz (hc.1.symm.trans hd.1)

variable [Fintype A] [Fintype B]

theorem witnesses (Y : Finset (A×B)) :
    ∃ W U : Finset (A×B), W⊆Y ∧ W.card≤3 ∧ (U=univ ∨ Permitted U) ∧
      (∀x,(∀w∈W,Adj x w) → x∈U) ∧ Shape Y U := by
  classical
  rcases classification Y with h|h|h|h
  · refine ⟨∅,univ,empty_subset _,by simp,Or.inl rfl,fun x _ => mem_univ x,Or.inl ?_⟩
    exact card_le_one.mp h
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := h
    have hn : y.2≠z.2 := by intro hh; exact hyz (Prod.ext he hh)
    rcases hw with hall|⟨w,hw,hwy⟩
    · refine ⟨{y,z},row y.1,?_,card_pair_le y z,Or.inr (Or.inl ⟨y.1,rfl⟩),?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · intro x hx
        have hx' := (same_row hn x).mp ⟨hx y (by simp),by simpa only [Adj,← he] using hx z (by simp)⟩
        simpa [row] using hx'.1
      · right; right; left
        refine ⟨true,?_⟩
        intro x hx v hv b hb
        have hx' : x.1=y.1 := by simpa [row] using hx
        exact bit_true hb (hx'.trans (hall v hv).symm)
    · refine ⟨{y,z,w},{(y.1,w.2)},?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        have hx' := third_off_row hn hwy.symm x (hx y (by simp))
          (by simpa only [Adj,← he] using hx z (by simp)) (hx w (by simp))
        exact mem_singleton.mpr hx'
      · intro x hx v hv
        exact (mem_singleton.mp hx).trans (mem_singleton.mp hv).symm
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := h
    have hn : y.1≠z.1 := by intro hh; exact hyz (Prod.ext hh he)
    rcases hw with hall|⟨w,hw,hwy⟩
    · refine ⟨{y,z},col y.2,?_,card_pair_le y z,Or.inr (Or.inr (Or.inl ⟨y.2,rfl⟩)),?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · intro x hx
        have hx' := (same_column hn x).mp ⟨hx y (by simp),by simpa only [Adj,← he] using hx z (by simp)⟩
        simpa [col] using hx'.1
      · right; right; left
        refine ⟨false,?_⟩
        intro x hx v hv b hb
        have hx' : x.2=y.2 := by simpa [col] using hx
        exact bit_false hb (hx'.trans (hall v hv).symm)
    · refine ⟨{y,z,w},{(w.1,y.2)},?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        have hxy := (swap_iff x y).mpr (hx y (by simp))
        have hxz := (swap_iff x z).mpr (hx z (by simp))
        have hxw := (swap_iff x w).mpr (hx w (by simp))
        have hx' := third_off_row hn hwy.symm x.swap hxy
          (by simpa only [Prod.swap,← he] using hxz) hxw
        apply mem_singleton.mpr
        exact Prod.ext (congrArg Prod.snd hx') (congrArg Prod.fst hx')
      · intro x hx v hv
        exact (mem_singleton.mp hx).trans (mem_singleton.mp hv).symm
  · obtain ⟨y,hy,z,hz,h₁,h₂,hw⟩ := h
    rcases hw with hall|⟨w,hw,hyw,hzw,hyw',hzw'⟩
    · refine ⟨{y,z},{(y.1,z.2),(z.1,y.2)},?_,card_pair_le y z,?_,?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · right; right; right
        exact (card_insert_le _ _).trans (by simp)
      · intro x hx
        simpa only [mem_insert,mem_singleton] using (corners h₁ h₂ x).mp ⟨hx y (by simp),hx z (by simp)⟩
      · right; right; right
        have hY := pair_coord_inj hall h₁ h₂
        have hU := pair_coord_inj (y := (y.1,z.2)) (z := (z.1,y.2)) (S := {(y.1,z.2),(z.1,y.2)})
          (by intro v hv; simpa only [mem_insert,mem_singleton] using hv) h₁ h₂.symm
        constructor
        · intro x _ u hu v hv b hc hd
          exact determined_of_inj hY x u hu v hv b hc hd
        · intro v _ x hx u hu b hc hd
          exact determined_of_inj hU v x hx u hu b (consistent_symm hc) (consistent_symm hd)
    · refine ⟨{y,z,w},∅,?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        exact (three_independent h₁ hyw hzw h₂ hyw' hzw' x
          ⟨hx y (by simp),hx z (by simp),hx w (by simp)⟩).elim
      · simp
end
end PlanarUnitDistances.CrossStructure

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma cond_tower_dep (μ : Law X) (φ : X → Y) (f : Y → X → ℝ) :
    avg (push μ φ) (fun y => avg (cond μ φ y) (f y)) = avg μ (fun x => f (φ x) x) := by
  classical
  unfold avg
  simp only [push,mul_sum,← mul_assoc,cond_weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw StarScore CrossStructure
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

lemma row_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (left π) (fun p => avg (row π p) (f p)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [row,push_avg]
  change avg (push π Prod.fst) _ = _
  exact cond_tower_dep π Prod.fst (fun p pq => f p pq.2)
lemma col_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (right π) (fun q => avg (col π q) (fun p => f p q)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [col,push_avg]
  change avg (push π Prod.snd) _ = _
  exact cond_tower_dep π Prod.snd (fun q pq => f pq.1 q)
lemma row_event (π : Law (P×Q)) (g : P → Q → Prop) :
    avg (left π) (fun p => event (row π p) (g p)) = event π (fun pq => g pq.1 pq.2) := by
  unfold event
  exact row_avg π _
lemma col_event (π : Law (P×Q)) (g : P → Q → Prop) :
    avg (right π) (fun q => event (col π q) (fun p => g p q)) = event π (fun pq => g pq.1 pq.2) := by
  unfold event
  exact col_avg π _

lemma vp_le (π : Law (P×Q)) (bit : P → Q → Bool) : VP π bit ≤ 1/2 :=
  avg_le_const _ (fun p => variation_le_half (row π p) (bit p))
lemma vq_le (π : Law (P×Q)) (bit : P → Q → Bool) : VQ π bit ≤ 1/2 :=
  avg_le_const _ (fun q => variation_le_half (col π q) (fun p => bit p q))
lemma dp_lower (π : Law (P×Q)) (bit : P → Q → Bool) (y : Q → A×B) : -VP π bit ≤ DP π bit y := by
  have h := avg_mono (left π) (fun p => score_lower (row π p) (bit p) y)
  have he : avg (left π) (fun p => -variation (row π p) (bit p)) = -VP π bit := by
    calc
      _ = avg (left π) (fun p => (-1)*variation (row π p) (bit p)) :=
        avg_congr _ (fun p => by ring)
      _ = _ := by rw [avg_smul]; simp only [neg_one_mul,VP]
  exact he ▸ h
lemma dq_lower (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) : -VQ π bit ≤ DQ π bit x := by
  have h := avg_mono (right π) (fun q => score_lower (col π q) (fun p => bit p q) x)
  have he : avg (right π) (fun q => -variation (col π q) (fun p => bit p q)) = -VQ π bit := by
    calc
      _ = avg (right π) (fun q => (-1)*variation (col π q) (fun p => bit p q)) :=
        avg_congr _ (fun q => by ring)
      _ = _ := by rw [avg_smul]; simp only [neg_one_mul,VQ]
  exact he ▸ h

theorem slice_score (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : P → Q → Prop) (Y U : Finset (A×B)) (hs : Shape Y U)
    (hg : ∀ p q,good p q → x p∈U ∧ y q∈Y ∧ Consistent (bit p q) (x p) (y q)) :
    (VP π bit+VQ π bit)/80000-12*bad π good ≤ DP π bit y+DQ π bit x := by
  have hbad : 0≤bad π good := event_nonneg _ _
  have hvp := vp_le π bit
  have hvq := vq_le π bit
  have hdp := dp_lower π bit y
  have hdq := dq_lower π bit x
  rcases hs with hs|hs|⟨b,hs⟩|⟨hsP,hsQ⟩
  · have h (p : P) := constant_good (row π p) (bit p) y (good p) (by
      intro q r hq hr
      have hy := hs (y q) (hg p q hq).2.1 (y r) (hg p r hr).2.1
      refine ⟨?_,hy⟩
      exact bit_unique (hg p q hq).2.2 (hy ▸ (hg p r hr).2.2))
    have ha := avg_mono (left π) h
    rw [avg_sub,avg_const,avg_smul,row_event] at ha
    change (1-1/20000:ℝ)-4*bad π good ≤ DP π bit y at ha
    linarith
  · have h (q : Q) := constant_good (col π q) (fun p => bit p q) x (fun p => good p q) (by
      intro p r hp hr
      have hx := hs (x p) (hg p q hp).1 (x r) (hg r q hr).1
      refine ⟨?_,hx⟩
      exact bit_unique (hg p q hp).2.2 (hx ▸ (hg r q hr).2.2))
    have ha := avg_mono (right π) h
    rw [avg_sub,avg_const,avg_smul,col_event] at ha
    change (1-1/20000:ℝ)-4*bad π good ≤ DQ π bit x at ha
    linarith
  · have hc : ∀p q,good p q → bit p q=b := by
      intro p q hp
      exact hs (x p) (hg p q hp).1 (y q) (hg p q hp).2.1 _ (hg p q hp).2.2
    have hp := avg_mono (left π) (fun p => constant_bit (row π p) (bit p) (good p)
      (by intro q r hq hr; exact (hc p q hq).trans (hc p r hr).symm))
    have hq := avg_mono (right π) (fun q => constant_bit (col π q) (fun p => bit p q) (fun p => good p q)
      (by intro p r hp hr; exact (hc p q hp).trans (hc r q hr).symm))
    rw [avg_smul,row_event] at hp
    rw [avg_smul,col_event] at hq
    change VP π bit ≤ 2*bad π good at hp
    change VQ π bit ≤ 2*bad π good at hq
    linarith
  · have hp := avg_mono (left π) (fun p => determined (row π p) (bit p) y (good p) (by
      intro q r hq hr hb
      apply hsP (x p) (hg p q hq).1 (y q) (hg p q hq).2.1 (y r) (hg p r hr).2.1 (bit p q)
      · exact (hg p q hq).2.2
      · exact hb ▸ (hg p r hr).2.2))
    have hq := avg_mono (right π) (fun q => determined (col π q) (fun p => bit p q) x (fun p => good p q) (by
      intro p r hp hr hb
      apply hsQ (y q) (hg p q hp).2.1 (x p) (hg p q hp).1 (x r) (hg r q hr).1 (bit p q)
      · exact (hg p q hp).2.2
      · exact hb ▸ (hg r q hr).2.2))
    rw [avg_sub,avg_const,avg_smul,row_event] at hp
    rw [avg_sub,avg_const,avg_smul,col_event] at hq
    change (1/40000:ℝ)-6*bad π good ≤ DP π bit y at hp
    change (1/40000:ℝ)-6*bad π good ≤ DQ π bit x at hq
    linarith
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.RareScore
open FiniteLaw CrossStructure
open scoped Classical
noncomputable section
variable {A B X : Type*}

lemma normal_bits {r b c : Bool} {l x y z : A×B}
    (hy : ¬exceptional r l y) (hz : ¬exceptional r l z)
    (hb : Consistent b x y) (hc : Consistent c x z) : b=c := by
  cases r <;> cases b <;> cases c <;>
    simp_all [exceptional,Consistent]

lemma exceptional_bits {r b c : Bool} {l x y z : A×B}
    (hx : exceptional r l x) (hy : ¬exceptional r l y) (hz : ¬exceptional r l z)
    (hb : Consistent b x y) (hc : Consistent c x z) :
    b=r ∧ c=r ∧ nonshared r y z := by
  cases r <;> cases b <;> cases c <;>
    simp_all [exceptional,Consistent,nonshared]

lemma ind_nonneg (h : Prop) : 0≤ ind h := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (h : Prop) : ind h≤1 := by unfold ind; split_ifs <;> norm_num

lemma slot_lower (r : Bool) (l x y z : A×B) (b c : Bool) :
    2*ind (exceptional r l x)-2*ind (exceptional r l x ∧ exceptional r l y)-
      2*ind (exceptional r l x ∧ exceptional r l z)-ind (exceptional r l y)-
      ind (exceptional r l z)-3*ind (¬Consistent b x y)-3*ind (¬Consistent c x z) ≤
    slot r l x y z b c := by
  have hp := exceptional_bits (r:=r) (b:=b) (c:=c) (l:=l) (x:=x) (y:=y) (z:=z)
  have hn := normal_bits (r:=r) (b:=b) (c:=c) (l:=l) (x:=x) (y:=y) (z:=z)
  have hpos : 2*ind (exceptional r l x)-
      2*ind (exceptional r l x ∧ exceptional r l y)-
      2*ind (exceptional r l x ∧ exceptional r l z)-
      2*ind (¬Consistent b x y)-2*ind (¬Consistent c x z) ≤
      2*ind (exceptional r l x ∧ b=r ∧ c=r ∧ nonshared r y z) := by
    unfold ind
    split_ifs <;> simp_all <;> norm_num
  have hneg : ind (b≠c)≤ ind (exceptional r l y)+ind (exceptional r l z)+
      ind (¬Consistent b x y)+ind (¬Consistent c x z) := by
    unfold ind
    split_ifs <;> simp_all <;> norm_num
  unfold slot
  linarith

variable [Fintype X]

theorem star_lower (μ : Law X) (r : Bool) (l base : A×B)
    (state : X → A×B) (bit : X → Bool) :
    2*ind (exceptional r l base)-
      4*event μ (fun y => exceptional r l base ∧ exceptional r l (state y))-
      2*event μ (fun y => exceptional r l (state y))-
      6*event μ (fun y => ¬Consistent (bit y) base (state y)) ≤
    avg (pair μ μ) (fun yz => slot r l base (state yz.1) (state yz.2) (bit yz.1) (bit yz.2)) := by
  have hs := avg_mono (pair μ μ) (fun yz =>
    slot_lower r l base (state yz.1) (state yz.2) (bit yz.1) (bit yz.2))
  simp only [avg_sub,avg_smul,avg_const] at hs
  have hf (g : X → Prop) : avg (pair μ μ) (fun yz => ind (g yz.1))=event μ g := by
    rw [pair_fst μ μ (fun x => ind (g x))]
    exact avg_ite μ g
  have hg (g : X → Prop) : avg (pair μ μ) (fun yz => ind (g yz.2))=event μ g := by
    rw [pair_snd μ μ (fun x => ind (g x))]
    exact avg_ite μ g
  rw [hf (fun y => exceptional r l base ∧ exceptional r l (state y)),
    hg (fun y => exceptional r l base ∧ exceptional r l (state y)),
    hf (fun y => exceptional r l (state y)),hg (fun y => exceptional r l (state y)),
    hf (fun y => ¬Consistent (bit y) base (state y)),
    hg (fun y => ¬Consistent (bit y) base (state y))] at hs
  linarith

end
end PlanarUnitDistances.RareScore

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma event_eq_sum (μ : Law X) (P : X → Prop) :
    event μ P = ∑ x, if P x then μ.val x else 0 := by
  unfold event avg
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma event_congr (μ : Law X) {P Q : X → Prop} (h : ∀ x,P x ↔ Q x) :
    event μ P=event μ Q := le_antisymm (event_mono μ (fun x => (h x).mp))
      (event_mono μ (fun x => (h x).mpr))

lemma event_true (μ : Law X) : event μ (fun _ => True)=1 := by
  simp [event,avg_const]
lemma event_false (μ : Law X) : event μ (fun _ => False)=0 := by
  simp [event,avg_const]

lemma event_exists_le (μ : Law X) (P : I → X → Prop) :
    event μ (fun x => ∃ i,P i x) ≤ ∑ i,event μ (P i) := by
  classical
  unfold event avg
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
  dsimp only
  split_ifs with hx
  · obtain ⟨i,hi⟩ := hx
    have := single_le_sum (s := univ) (f := fun i => if P i x then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa only [hi,ite_true] using this
  · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma sum_event_fibers (μ : Law X) (f : X → Y) : ∑ y,event μ (fun x => f x=y)=1 := by
  simp_rw [event_eq_sum]
  rw [sum_comm]
  simpa using μ.total

variable [DecidableEq I]

lemma independent_event (μ : Law X) (P : I → X → Prop) :
    event (independent μ I) (fun x => ∀ i,P i (x i)) = ∏ i,event μ (P i) := by
  classical
  simp only [event_eq_sum,independent]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x _
  by_cases h : ∀ i,P i (x i)
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    simp only [h,ite_false]
    symm
    apply prod_eq_zero (mem_univ i)
    simp [hi]

lemma independent_all (μ : Law X) (P : X → Prop) :
    event (independent μ I) (fun x => ∀ i,P (x i)) = (event μ P)^(Fintype.card I) := by
  rw [independent_event]
  simp

lemma equiv_avg {Y : Type*} [Fintype Y] (μ : Law X) (ν : Law Y) (e : X ≃ Y)
    (he : ∀ x,μ.val x=ν.val (e x)) (f : Y → ℝ) :
    avg μ (fun x => f (e x)) = avg ν f := by
  unfold avg
  simp_rw [he]
  exact e.sum_comp (fun y => ν.val y*f y)

lemma independent_split (μ : Law X) (i : I) (f : (I → X) → ℝ) :
    avg (independent μ I) f = avg μ (fun x =>
      avg (independent μ {j : I // j ≠ i}) (fun xs => f ((Equiv.piSplitAt i (fun _ => X)).symm (x,xs)))) := by
  classical
  let e := Equiv.piSplitAt i (fun _ => X)
  have he : ∀ xs : I → X, (independent μ I).val xs =
      (pair μ (independent μ {j : I // j ≠ i})).val (e xs) := by
    intro xs
    change (∏ j,μ.val (xs j)) = μ.val (xs i)* ∏ j : {j : I // j ≠ i},μ.val (xs j)
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    congr 1
    exact Finset.prod_subtype (univ.erase i) (fun j => by simp) (fun j => μ.val (xs j))
  have h := equiv_avg (independent μ I) (pair μ (independent μ {j : I // j ≠ i}))
    e he (fun z => f (e.symm z))
  simp only [Equiv.symm_apply_apply] at h
  rw [h,pair_avg]

lemma independent_two_split (μ : Law X) (i j : I) (hij : i≠j)
    (f : (I → X) → ℝ) :
    avg (independent μ I) f = avg μ (fun x => avg μ (fun y =>
      avg (independent μ {l : {l : I // l ≠ i} // l ≠ ⟨j,hij.symm⟩}) (fun xs =>
        f ((Equiv.piSplitAt i (fun _ => X)).symm (x,
          (Equiv.piSplitAt (⟨j,hij.symm⟩ : {l : I // l≠i}) (fun _ => X)).symm (y,xs)))))) := by
  classical
  rw [independent_split μ i]
  apply avg_congr
  intro x
  exact independent_split μ (⟨j,hij.symm⟩ : {l : I // l≠i}) _
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Wedges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

lemma dependent_avg (μ : Law X) (ν : X → Law Y) (f : X×Y → ℝ) :
    avg (dependent μ ν) f = avg μ (fun x => avg (ν x) (fun y => f (x,y))) := by
  simp [avg,dependent,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma tensor_event (μ : I → Law X) (P : I → X → Prop) :
    event (tensor μ) (fun x => ∀i,P i (x i)) = ∏ i,event (μ i) (P i) := by
  classical
  simp only [event_eq_sum,tensor]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x _
  by_cases h : ∀i,P i (x i)
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    simp only [h,ite_false]
    symm
    apply prod_eq_zero (mem_univ i)
    simp [hi]
lemma tensor_coordinate (μ : I → Law X) (i : I) (P : X → Prop) :
    event (tensor μ) (fun x => P (x i)) = event (μ i) P := by
  classical
  calc
    _ = event (tensor μ) (fun x => ∀j, j=i → P (x j)) :=
      event_congr _ (fun x => by simp)
    _ = ∏ j,event (μ j) (fun x => j=i → P x) := tensor_event μ (fun j x => j=i → P x)
    _ = event (μ i) P := by
      rw [prod_eq_single i]
      · apply event_congr; simp
      · intro j _ hji
        simp only [hji,false_implies]
        exact event_true _
      · simp
lemma tensor_union_le (μ : I → Law X) (P : I → X → Prop) :
    event (tensor μ) (fun x => ∃i,P i (x i)) ≤ ∑ i,event (μ i) (P i) := by
  have h := event_exists_le (tensor μ) (fun i x => P i (x i))
  simpa only [tensor_coordinate] using h

lemma tensor_dependent (μ : Law X) (ν : X → Law Y) (f : (I → X) → (I → Y) → ℝ) :
    avg (independent (dependent μ ν) I) (fun xy => f (fun i => (xy i).1) (fun i => (xy i).2)) =
    avg (independent μ I) (fun x => avg (tensor (fun i => ν (x i))) (f x)) := by
  classical
  let e : (I → X×Y) ≃ (I → X)×(I → Y) := Equiv.arrowProdEquivProdArrow I (fun _ => X) (fun _ => Y)
  have he : ∀ xy, (independent (dependent μ ν) I).val xy =
      (dependent (independent μ I) (fun x => tensor (fun i => ν (x i)))).val (e xy) := by
    intro xy
    change (∏i,μ.val (xy i).1*(ν (xy i).1).val (xy i).2) =
      (∏i,μ.val (xy i).1)*(∏i,(ν (xy i).1).val (xy i).2)
    exact prod_mul_distrib
  have h := equiv_avg (independent (dependent μ ν) I)
    (dependent (independent μ I) (fun x => tensor (fun i => ν (x i)))) e he
    (fun xy => f xy.1 xy.2)
  rw [dependent_avg] at h
  exact h

lemma independent_push (μ : Law X) (φ : X → Y) (f : (I → Y) → ℝ) :
    avg (independent μ I) (fun x => f (φ ∘ x)) = avg (independent (push μ φ) I) f := by
  classical
  have hw : ∀y : I → Y,(push (independent μ I) (fun x => φ ∘ x)).val y =
      (independent (push μ φ) I).val y := by
    intro y
    change event (independent μ I) (fun x => φ ∘ x=y) = ∏i,event μ (fun x => φ x=y i)
    rw [event_congr _ (fun x => funext_iff)]
    exact independent_event μ (fun i x => φ x=y i)
  calc
    _ = avg (push (independent μ I) (fun x => φ ∘ x)) f :=
      (push_avg _ _ _).symm
    _ = _ := by unfold avg; simp_rw [hw]

lemma law_ext {μ ν : Law X} (h : ∀x,μ.val x=ν.val x) : μ=ν := by
  cases μ with | mk a ha sa =>
    cases ν with | mk b hb sb =>
      have : a=b := funext h
      subst b
      rfl

lemma push_dependent_snd (μ : Law X) (ν : X → Law Y) :
    push (dependent μ ν) Prod.snd=mix μ ν := by
  apply law_ext
  intro y
  change event (dependent μ ν) (fun xy => xy.2=y)=avg μ (fun x => (ν x).val y)
  simp only [event_eq_sum,dependent,Fintype.sum_prod_type,avg]
  simp

lemma tensor_mixture (μ : Law X) (ν : X → Law Y) (f : (I → Y) → ℝ) :
    avg (independent μ I) (fun x => avg (tensor (fun i => ν (x i))) f) =
      avg (independent (mix μ ν) I) f := by
  rw [← tensor_dependent]
  have h := independent_push (I := I) (dependent μ ν) Prod.snd f
  rw [push_dependent_snd] at h
  exact h
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.WedgeLaw
open FiniteLaw FiniteStarCoupling WedgeProfiles
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma average (π : Law (P×Q)) (f : Q×(P×P) → ℝ) :
    avg (law π) f=avg (right π) (fun q => avg (pair (col π q) (col π q)) (fun pp => f (q,pp))) :=
  dependent_avg _ _ _

lemma first (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (law π) (fun a => f a.2.1 a.1)=avg π (fun pq => f pq.1 pq.2) := by
  rw [average]
  calc
    _ = avg (right π) (fun q => avg (col π q) (fun p => f p q)) := by
      apply avg_congr
      intro q
      exact FiniteLaw.pair_fst (col π q) (col π q) (fun p => f p q)
    _ = _ := col_avg π f

lemma second (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (law π) (fun a => f a.2.2 a.1)=avg π (fun pq => f pq.1 pq.2) := by
  rw [average]
  calc
    _ = avg (right π) (fun q => avg (col π q) (fun p => f p q)) := by
      apply avg_congr
      intro q
      exact FiniteLaw.pair_snd (col π q) (col π q) (fun p => f p q)
    _ = _ := col_avg π f

lemma first_point (π : Law (P×Q)) (f : P → ℝ) :
    avg (law π) (fun a => f a.2.1)=avg (left π) f := by
  rw [first π (fun p _ => f p)]
  exact (push_avg π Prod.fst f).symm

lemma second_point (π : Law (P×Q)) (f : P → ℝ) :
    avg (law π) (fun a => f a.2.2)=avg (left π) f := by
  rw [second π (fun p _ => f p)]
  exact (push_avg π Prod.fst f).symm

lemma mismatch (π : Law (P×Q)) (b : P → Q → Bool) :
    avg (law π) (fun a => |value (b a.2.1 a.1)-value (b a.2.2 a.1)|)=VQ π b := by
  rw [average]
  apply avg_congr
  intro q
  rw [←StarScore.mismatch]
  apply avg_congr
  intro pp
  cases h₁ : b pp.1 q <;> cases h₂ : b pp.2 q <;> norm_num [value,h₁,h₂]
end
end PlanarUnitDistances.WedgeLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]
lemma left_val (π : Law (P×Q)) (p : P) : (left π).val p = ∑q,π.val (p,q) := by
  simp only [left,push,fiberMass_eq,Fintype.sum_prod_type]
  rw [sum_comm]
  simp
lemma right_val (π : Law (P×Q)) (q : Q) : (right π).val q = ∑p,π.val (p,q) := by
  simp [right,push,fiberMass_eq,Fintype.sum_prod_type]
lemma row_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (left π).val p*(row π p).val q=π.val (p,q) := by
  simp only [row,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.2=q then fiberMass π Prod.fst p*(cond π Prod.fst p).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma col_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (right π).val q*(col π q).val p=π.val (p,q) := by
  simp only [col,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.1=p then fiberMass π Prod.snd q*(cond π Prod.snd q).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma row_val (π : Law (P×Q)) {p : P} (hp : 0<(left π).val p) (q : Q) :
    (row π p).val q=π.val (p,q)/(left π).val p := by
  apply (eq_div_iff hp.ne').mpr
  simpa only [mul_comm] using row_weight π p q
lemma col_val (π : Law (P×Q)) {q : Q} (hq : 0<(right π).val q) (p : P) :
    (col π q).val p=π.val (p,q)/(right π).val q := by
  apply (eq_div_iff hq.ne').mpr
  simpa only [mul_comm] using col_weight π p q
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.TemplateCoupling
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

lemma slice_weight (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (pq : P×Q) :
    (templates π a).val θ*(slice π a θ).val pq=π.val pq*(a pq.2).val θ := by
  exact col_weight (joint π a) pq θ
lemma slice_avg (π : Law (P×Q)) (a : Q → Law Θ) (f : Θ → P×Q → ℝ) :
    avg (templates π a) (fun θ => avg (slice π a θ) (f θ))=
      avg π (fun pq => avg (a pq.2) (fun θ => f θ pq)) := by
  simp only [slice,push_avg]
  change avg (push (joint π a) Prod.snd) _=_
  rw [cond_tower_dep]
  exact dependent_avg π _ _
lemma slice_event (π : Law (P×Q)) (a : Q → Law Θ) (f : Θ → P×Q → Prop) :
    avg (templates π a) (fun θ => event (slice π a θ) (f θ))=
      avg π (fun pq => event (a pq.2) (fun θ => f θ pq)) := by
  unfold event
  exact slice_avg π a _
lemma slice_right_weight (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (q : Q) :
    (templates π a).val θ*(right (slice π a θ)).val q = (right π).val q*(a q).val θ := by
  simp only [right_val,mul_sum,sum_mul,slice_weight]

lemma col_eq (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (q : Q)
    (ht : 0<(templates π a).val θ) (hq : 0<(right (slice π a θ)).val q) :
    col (slice π a θ) q=col π q := by
  have he := slice_right_weight π a θ q
  apply law_ext
  intro p
  apply (mul_right_inj' (mul_ne_zero ht.ne' hq.ne')).mp
  calc
    _ = (templates π a).val θ*(slice π a θ).val (p,q) := by rw [mul_assoc,col_weight]
    _ = π.val (p,q)*(a q).val θ := slice_weight π a θ (p,q)
    _ = ((templates π a).val θ*(right (slice π a θ)).val q)*(col π q).val p := by
      rw [he]
      calc
        _ = ((right π).val q*(col π q).val p)*(a q).val θ := by rw [col_weight]
        _ = _ := by ring

lemma center_statistic (π : Law (P×Q)) (a : Q → Law Θ) (F : Q → Law P → ℝ) :
    avg (templates π a) (fun θ => avg (right (slice π a θ)) (fun q => F q (col (slice π a θ) q)))=
      avg (right π) (fun q => F q (col π q)) := by
  have he (θ : Θ) (q : Q) :
      (templates π a).val θ*((right (slice π a θ)).val q*F q (col (slice π a θ) q))=
        (right π).val q*(a q).val θ*F q (col π q) := by
    rw [← mul_assoc]
    by_cases ht : 0<(templates π a).val θ
    · by_cases hq : 0<(right (slice π a θ)).val q
      · rw [col_eq π a θ q ht hq,slice_right_weight]
      · have hz := le_antisymm (le_of_not_gt hq) ((right (slice π a θ)).nonneg q)
        rw [← slice_right_weight,hz,mul_zero,zero_mul,zero_mul]
    · have hz := le_antisymm (le_of_not_gt ht) ((templates π a).nonneg θ)
      rw [← slice_right_weight,hz,zero_mul,zero_mul,zero_mul]
  simp only [avg,mul_sum,he]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← sum_mul,← mul_sum,(a q).total,mul_one]

lemma center_variation (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool) :
    avg (templates π a) (fun θ => VQ (slice π a θ) bit)=VQ π bit :=
  center_statistic π a (fun q ν => StarScore.variation ν (fun p => bit p q))
lemma center_score {A B : Type*} (π : Law (P×Q)) (a : Q → Law Θ)
    (bit : P → Q → Bool) (x : P → A×B) :
    avg (templates π a) (fun θ => DQ (slice π a θ) bit x)=DQ π bit x :=
  center_statistic π a (fun q ν => StarScore.score ν (fun p => bit p q) x)
end
end PlanarUnitDistances.TemplateCoupling

namespace PlanarUnitDistances.CrossSampling
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]

lemma atom_eq (ν : Law (A×B)) (y : A×B) : event ν (fun x => x=y)=ν.val y := by
  classical
  rw [event_eq_sum]
  exact sum_eq_single y (fun x _ hx => ite_eq_right hx) (by simp) |>.trans (ite_eq_left rfl)
lemma row_le_cross_add_atom (ν : Law (A×B)) (y : A×B) :
    rowMass ν y.1 ≤ crossMass ν y+ν.val y := by
  have h := event_mono ν (P := fun x => x.1=y.1) (Q := fun x => Adj x y ∨ x=y) (by
    intro x hx
    by_cases hy : x.2=y.2
    · exact Or.inr (Prod.ext hx hy)
    · exact Or.inl (Or.inl ⟨hx,hy⟩))
  exact h.trans ((event_union_le ν _ _).trans_eq (by rw [atom_eq]; rfl))
lemma col_le_cross_add_atom (ν : Law (A×B)) (y : A×B) :
    colMass ν y.2 ≤ crossMass ν y+ν.val y := by
  have h := event_mono ν (P := fun x => x.2=y.2) (Q := fun x => Adj x y ∨ x=y) (by
    intro x hy
    by_cases hx : x.1=y.1
    · exact Or.inr (Prod.ext hx hy)
    · exact Or.inl (Or.inr ⟨hx,hy⟩))
  exact h.trans ((event_union_le ν _ _).trans_eq (by rw [atom_eq]; rfl))

omit [DecidableEq I] in
lemma bad_decomposition (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) (h : Bad ν α xs) :
    (∃ ij : I×I,Corner ν α xs ij.1 ij.2) ∨ LowRow ν α xs ∨ LowCol ν α xs ∨
      HeavyAvoid ν α xs := by
  obtain ⟨y,hy,hall⟩ := h
  have hne : ∀ i,xs i ≠ y := by
    intro i eq
    have hi := hall i
    rw [eq] at hi
    simp [Adj] at hi
  by_cases hr : ∃ i,(xs i).1=y.1 ∧ (xs i).2≠y.2
  · obtain ⟨i,hi⟩ := hr
    by_cases hc : ∃ j,(xs j).1≠y.1 ∧ (xs j).2=y.2
    · obtain ⟨j,hj⟩ := hc
      have hij : i≠j := by intro he; subst j; exact hj.1 hi.1
      left
      refine ⟨(i,j),hij,?_,?_⟩
      · simpa only [hi.1,hj.2,Prod.mk.eta] using hy
      · simpa only [hi.1,hj.2,Prod.mk.eta] using hall
    · have har : ∀ j,(xs j).1=y.1 := by
        intro j
        rcases hall j with h|h
        · exact h.1
        · exact False.elim (hc ⟨j,h⟩)
      by_cases hlo : rowMass ν y.1 ≤ 1-α/2
      · exact Or.inr (Or.inl ⟨y.1,hlo,har⟩)
      · right; right; right
        refine ⟨y,?_,hne⟩
        have := row_le_cross_add_atom ν y
        linarith
  · have hac : ∀ j,(xs j).2=y.2 := by
      intro j
      rcases hall j with h|h
      · exact False.elim (hr ⟨j,h⟩)
      · exact h.2
    by_cases hlo : colMass ν y.2 ≤ 1-α/2
    · exact Or.inr (Or.inr (Or.inl ⟨y.2,hlo,hac⟩))
    · right; right; right
      refine ⟨y,?_,hne⟩
      have := col_le_cross_add_atom ν y
      linarith

lemma low_fiber_bound {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (f : X → Y)
    {r : ℝ} (hr : 0≤r) (hI : 0<Fintype.card I) :
    event (independent ν I) (fun xs => ∃ y,event ν (fun x => f x=y) ≤ r ∧ ∀ i,f (xs i)=y) ≤
      r^(Fintype.card I-1) := by
  refine (event_exists_le _ _).trans ?_
  have hb : ∀ y,event (independent ν I) (fun xs => event ν (fun x => f x=y) ≤ r ∧
      ∀ i,f (xs i)=y) ≤ event ν (fun x => f x=y)*r^(Fintype.card I-1) := by
    intro y
    by_cases hy : event ν (fun x => f x=y) ≤ r
    · have he : event (independent ν I) (fun xs => event ν (fun x => f x=y) ≤ r ∧
          ∀ i,f (xs i)=y) = event (independent ν I) (fun xs => ∀ i,f (xs i)=y) := by
        apply event_congr
        intro xs
        simp only [hy,true_and]
      rw [he,independent_all (I := I) ν (fun x => f x=y)]
      conv_lhs => rw [show Fintype.card I=1+(Fintype.card I-1) by omega,pow_add,pow_one]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (event_nonneg _ _) hy _) (event_nonneg _ _)
    · have he : event (independent ν I) (fun xs => event ν (fun x => f x=y) ≤ r ∧
          ∀ i,f (xs i)=y) = 0 := by
        calc
          _ = event (independent ν I) (fun _ => False) := event_congr _ (by intro xs; simp only [hy,false_and])
          _ = 0 := event_false _
      rw [he]
      exact mul_nonneg (event_nonneg _ _) (pow_nonneg hr _)
  calc
    _ ≤ ∑ y,event ν (fun x => f x=y)*r^(Fintype.card I-1) := sum_le_sum fun y _ => hb y
    _ = _ := by rw [← sum_mul,sum_event_fibers,one_mul]
lemma heavyavoid_bound (ν : Law (A×B)) {α : ℝ} (hα : 0<α) (hα1 : α<1) :
    event (independent ν I) (HeavyAvoid ν α) ≤ (2/α)*(1-α/2)^(Fintype.card I) := by
  have hr : 0 ≤ 1-α/2 := by linarith
  refine (event_exists_le _ _).trans ?_
  have hb : ∀ y,event (independent ν I) (fun xs => α/2<ν.val y ∧ ∀ i,xs i≠y) ≤
      ν.val y*((2/α)*(1-α/2)^(Fintype.card I)) := by
    intro y
    by_cases hy : α/2<ν.val y
    · have he : event (independent ν I) (fun xs => α/2<ν.val y ∧ ∀ i,xs i≠y) =
          event (independent ν I) (fun xs => ∀ i,xs i≠y) := by
        apply event_congr
        intro xs
        simp only [hy,true_and]
      rw [he,independent_all (I := I) ν (fun x => x≠y),event_compl,atom_eq]
      have hν : 0≤1-ν.val y := by
        have := event_le_one ν (fun x => x=y)
        rw [atom_eq] at this
        linarith
      have hpow := pow_le_pow_left₀ hν (show 1-ν.val y ≤ 1-α/2 by linarith) (Fintype.card I)
      have hfactor : 1≤ν.val y*(2/α) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hα).mpr
        linarith
      calc
        _ ≤ (1-α/2)^(Fintype.card I) := hpow
        _ ≤ (ν.val y*(2/α))*(1-α/2)^(Fintype.card I) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor (pow_nonneg hr _)
        _ = _ := by ring
    · have he : event (independent ν I) (fun xs => α/2<ν.val y ∧ ∀ i,xs i≠y)=0 := by
        calc
          _ = event (independent ν I) (fun _ => False) := event_congr _ (by intro xs; simp only [hy,false_and])
          _ = 0 := event_false _
      rw [he]
      exact mul_nonneg (ν.nonneg y) (mul_nonneg (div_nonneg (by norm_num) hα.le) (pow_nonneg hr _))
  calc
    _ ≤ ∑ y,ν.val y*((2/α)*(1-α/2)^(Fintype.card I)) := sum_le_sum fun y _ => hb y
    _ = _ := by rw [← sum_mul,ν.total,one_mul]

omit [Fintype I] in
lemma fillTwo_i {X : Type*} (i j : I) (hij : i≠j) (a b : X) (xs : Rest i j hij → X) :
    fillTwo i j hij a b xs i = a := by simp [fillTwo,Equiv.piSplitAt_symm_apply]
omit [Fintype I] in
lemma fillTwo_j {X : Type*} (i j : I) (hij : i≠j) (a b : X) (xs : Rest i j hij → X) :
    fillTwo i j hij a b xs j = b := by simp [fillTwo,Equiv.piSplitAt_symm_apply,hij.symm]
omit [Fintype I] in
lemma fillTwo_rest {X : Type*} (i j : I) (hij : i≠j) (a b : X) (xs : Rest i j hij → X)
    (l : Rest i j hij) : fillTwo i j hij a b xs l.val.val = xs l := by
  have hl := l.val.property
  simp [fillTwo,Equiv.piSplitAt_symm_apply,hl,l.property]

lemma card_neq (i : I) : Fintype.card {l : I //l≠i}=Fintype.card I-1 := by
  rw [Fintype.card_subtype_compl (fun l : I => l=i)]
  simp
lemma card_rest (i j : I) (hij : i≠j) : Fintype.card (Rest i j hij)=Fintype.card I-2 := by
  rw [card_neq,card_neq]
  omega

lemma corner_bound (ν : Law (A×B)) {α : ℝ} (hα : α<1) (i j : I) :
    event (independent ν I) (fun xs => Corner ν α xs i j) ≤ (1-α)^(Fintype.card I-2) := by
  classical
  by_cases hij : i=j
  · subst j
    have he : event (independent ν I) (fun xs => Corner ν α xs i i)=0 := by
      simp [event,Corner,avg_const]
    rw [he]
    exact pow_nonneg (by linarith) _
  · rw [← avg_ite (independent ν I) (fun xs => Corner ν α xs i j),independent_two_split ν i j hij]
    apply avg_le_const
    intro a
    apply avg_le_const
    intro b
    change avg (independent ν (Rest i j hij)) (fun xs =>
      if Corner ν α (fillTwo i j hij a b xs) i j then 1 else 0) ≤ _
    by_cases hm : crossMass ν (a.1,b.2)<1-α
    · have hm' : ∀ xs, Corner ν α (fillTwo i j hij a b xs) i j →
          ∀ l,Adj (xs l) (a.1,b.2) := by
        intro xs hx l
        have he := hx.2.2 l.val.val
        simpa only [fillTwo_i,fillTwo_j,fillTwo_rest] using he
      have hh := event_mono (independent ν (Rest i j hij)) hm'
      rw [avg_ite]
      refine hh.trans ?_
      rw [independent_all (I := Rest i j hij) ν (fun x => Adj x (a.1,b.2)),card_rest]
      exact pow_le_pow_left₀ (event_nonneg _ _) hm.le _
    · have he : ∀ xs,¬Corner ν α (fillTwo i j hij a b xs) i j := by
        intro xs hx
        apply hm
        simpa only [fillTwo_i,fillTwo_j] using hx.2.1
      simp only [he,ite_false,avg_const]
      exact pow_nonneg (by linarith) _

lemma sampling_bound (ν : Law (A×B)) {α : ℝ} (hα : 0<α) (hα1 : α<1)
    (hI : 0<Fintype.card I) : event (independent ν I) (Bad ν α) ≤
      (Fintype.card I : ℝ)^2*(1-α)^(Fintype.card I-2) +
      2*(1-α/2)^(Fintype.card I-1)+(2/α)*(1-α/2)^(Fintype.card I) := by
  have h := event_mono (independent ν I) (bad_decomposition ν α)
  have hu₁ := event_union_le (independent ν I) (fun xs => ∃ ij : I×I,Corner ν α xs ij.1 ij.2)
    (fun xs => LowRow ν α xs ∨ LowCol ν α xs ∨ HeavyAvoid ν α xs)
  have hu₂ := event_union_le (independent ν I) (LowRow ν α) (fun xs => LowCol ν α xs ∨ HeavyAvoid ν α xs)
  have hu₃ := event_union_le (independent ν I) (LowCol ν α) (HeavyAvoid ν α)
  have hc := event_exists_le (independent ν I) (fun ij : I×I => fun xs => Corner ν α xs ij.1 ij.2)
  have hcs : (∑ ij : I×I,event (independent ν I) (fun xs => Corner ν α xs ij.1 ij.2)) ≤
      (Fintype.card I : ℝ)^2*(1-α)^(Fintype.card I-2) := by
    calc
      _ ≤ ∑ _ : I×I,(1-α)^(Fintype.card I-2) := sum_le_sum fun ij _ => corner_bound ν hα1 ij.1 ij.2
      _ = _ := by simp [Fintype.card_prod,pow_two]
  have hr := low_fiber_bound (I := I) ν Prod.fst (r := 1-α/2) (by linarith) hI
  have hcol := low_fiber_bound (I := I) ν Prod.snd (r := 1-α/2) (by linarith) hI
  have hh := heavyavoid_bound (I := I) ν hα hα1
  change event (independent ν I) (LowRow ν α) ≤ _ at hr
  change event (independent ν I) (LowCol ν α) ≤ _ at hcol
  linarith
end
end PlanarUnitDistances.CrossSampling

namespace PlanarUnitDistances.CrossTemplates
open Finset FiniteLaw StrictCross CrossSampling
open scoped Classical
noncomputable section
variable {H A B I : Type*} [Fintype H] [Fintype A] [Fintype B] [Fintype I]

lemma all_cross_lower (ν : I → Law (A×B)) (y : A×B) {ε : ℝ}
    (h : ∀i,1-ε≤crossMass (ν i) y) :
    1-(Fintype.card I:ℝ)*ε ≤ event (tensor ν) (fun x => ∀i,Adj (x i) y) := by
  have hh := tensor_union_le ν (fun _ x => ¬Adj x y)
  simp_rw [event_compl] at hh
  have hc : (∑ i : I, (1 - event (ν i) (fun x => Adj x y))) ≤ (Fintype.card I:ℝ)*ε := by
    calc
      _ ≤ ∑ _ : I, ε := sum_le_sum fun i _ => by have := h i; change 1-ε≤event (ν i) _ at this; linarith
      _ = _ := by simp
  have he : event (tensor ν) (fun x => ∃i,¬Adj (x i) y) =
      1-event (tensor ν) (fun x => ∀i,Adj (x i) y) := by
    rw [← event_compl]
    apply event_congr
    intro x
    simp
  rw [he] at hh
  linarith

theorem failure_bound (μ : Law H) (ν : H → Law (A×B)) {ε α : ℝ}
    (hα : 0<α) (hα1 : α<1) (hI : 0<Fintype.card I) :
    (1-(Fintype.card I:ℝ)*ε)*event (independent μ I) (Failure μ ν ε α) ≤
      (Fintype.card I : ℝ)^2*(1-α)^(Fintype.card I-2) +
      2*(1-α/2)^(Fintype.card I-1)+(2/α)*(1-α/2)^(Fintype.card I) := by
  let G := Bad (I := I) (mix μ ν) α
  have hl (h : I → H) :
      (if Failure μ ν ε α h then 1-(Fintype.card I:ℝ)*ε else 0) ≤
        event (tensor (fun i => ν (h i))) G := by
    split_ifs with hh
    · obtain ⟨y,hy,hmy⟩ := hh
      have hy' : ∀i,1-ε≤crossMass (ν (h i)) y := (mem_filter.mp hy).2
      refine (all_cross_lower _ y hy').trans (event_mono _ ?_)
      intro x hx
      exact ⟨y,hmy,hx⟩
    · exact event_nonneg _ _
  have ha := avg_mono (independent μ I) hl
  have he : avg (independent μ I) (fun h => if Failure μ ν ε α h then 1-(Fintype.card I:ℝ)*ε else 0) =
      (1-(Fintype.card I:ℝ)*ε)*event (independent μ I) (Failure μ ν ε α) := by
    rw [← avg_ite]
    rw [← avg_smul]
    apply avg_congr
    intro h
    split_ifs <;> simp_all
  rw [he] at ha
  have hm : avg (independent μ I) (fun h => event (tensor (fun i => ν (h i))) G) =
      event (independent (mix μ ν) I) G := by
    unfold event
    exact tensor_mixture μ ν _
  rw [hm] at ha
  exact ha.trans (sampling_bound (mix μ ν) hα hα1 hI)

lemma miss_markov (μ : Law H) (ν : H → Law (A×B)) (y : A×B) {ε : ℝ} :
    ε*event μ (fun h => crossMass (ν h) y<1-ε) ≤
      avg μ (fun h => 1-crossMass (ν h) y) := by
  rw [← avg_ite]
  rw [← avg_smul]
  apply avg_mono
  intro h
  split_ifs with hh
  · simp only [mul_one]
    linarith
  · simp only [mul_zero]
    exact sub_nonneg.mpr (event_le_one _ _)

theorem candidate_miss (μ : Law H) (ν : H → Law (A×B)) (y : A×B) {ε : ℝ} (hε : 0≤ε) :
    ε*event (independent μ I) (fun h => y∉Candidates ν ε h) ≤
      (Fintype.card I:ℝ)*avg μ (fun h => 1-crossMass (ν h) y) := by
  have he : event (independent μ I) (fun h => y∉Candidates ν ε h) =
      event (independent μ I) (fun h => ∃i,crossMass (ν (h i)) y<1-ε) := by
    apply event_congr
    intro h
    simp only [Candidates,mem_filter,mem_univ,true_and,not_forall,not_le]
  rw [he]
  have hu := tensor_union_le (fun _ : I => μ) (fun _ h => crossMass (ν h) y<1-ε)
  have heq : tensor (fun _ : I => μ)=independent μ I := by apply law_ext; intro x; rfl
  rw [heq] at hu
  have hh := mul_le_mul_of_nonneg_left hu hε
  have hm := miss_markov μ ν y (ε := ε)
  calc
    _ ≤ ε*∑_ : I,event μ (fun h => crossMass (ν h) y<1-ε) := hh
    _ = (Fintype.card I:ℝ)*(ε*event μ (fun h => crossMass (ν h) y<1-ε)) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
end
end PlanarUnitDistances.CrossTemplates

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling StrictCross CrossSampling CrossTemplates CrossStructure
open scoped Classical
noncomputable section
variable {P Q H A B Θ : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype Θ]

omit [Fintype H] in
lemma posterior_val (π : Law (P×Q)) (h : P → H) (x : P → A×B)
    (hμ : ∀p,0<(left π).val p) (p : P) (s : A×B) :
    (posteriorState π h x (h p)).val s =
      RestrictedTransfer.statePosterior (left π).val h x (h p) s := by
  have hp : 0<fiberMass (left π) h (h p) := lt_of_lt_of_le (hμ p) (atom_le_fiber _ _ _)
  have he : fiberMass (left π) h (h p)=RestrictedTransfer.historyMass (left π).val h (h p) :=
    fiberMass_eq _ _ _
  simp only [posteriorState,push]
  simp only [FiniteLaw.cond,hp,↓reduceDIte]
  simp only [fiberMass_eq,RestrictedTransfer.statePosterior,RestrictedTransfer.posterior]
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp_all [RestrictedTransfer.historyMass]

lemma mixture_val (π : Law (P×Q)) (h : P → H) (x : P → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q) (q : Q) (s : A×B) :
    (mix (historyLaw π h q) (posteriorState π h x)).val s=
      RestrictedTransfer.centerMixture (left π).val h x (fun p q => π.val (p,q)) q s := by
  change avg (push (col π q) h) (fun v => (posteriorState π h x v).val s)=_
  rw [push_avg]
  simp only [avg,posterior_val π h x hμ,col_val π (hκ q),right_val,
    RestrictedTransfer.centerMixture]

lemma event_mem_mass {X : Type*} [Fintype X] (μ : Law X) (U : Finset X) :
    event μ (fun x => x∈U)=RestrictedTransfer.mass μ.val U := by
  rw [event_eq_sum]
  simp only [RestrictedTransfer.mass]
  calc
    _ = ∑x,if x∈U then μ.val x else 0 := by
      apply sum_congr rfl; intro x _; split_ifs <;> rfl
    _ = _ := by rw [sum_ite_mem]; simp

lemma witnesses_mass (μ : Law (A×B)) (W U : Finset (A×B)) {α : ℝ} (hα : 0≤α)
    (hw : W.card≤3) (hU : ∀x,(∀w∈W,Adj x w) → x∈U)
    (hm : ∀w∈W,1-α≤crossMass μ w) : 1-3*α≤event μ (fun x => x∈U) := by
  have hu := event_exists_le (I := W) μ (fun w x => ¬Adj x w.val)
  have hsum : (∑w : W,event μ (fun x => ¬Adj x w.val))≤3*α := by
    calc
      _ ≤ ∑_w : W,α := sum_le_sum fun w _ => by
        rw [event_compl]; have hh := hm w.val w.property
        change 1-α≤event μ (fun x => Adj x w.val) at hh
        linarith
      _ = (W.card:ℝ)*α := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hw) hα
  have hm' : event μ (fun x => x∉U)≤event μ (fun x => ∃w : W,¬Adj x w.val) := by
    apply event_mono
    intro x hx
    by_contra hn
    push Not at hn
    exact hx (hU x (fun w hw => hn ⟨w,hw⟩))
  rw [event_compl] at hm'
  linarith

theorem actual_transfer (π : Law (P×Q)) (h : P → H) (x : P → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    (a : Q → Law Θ) (U : Θ → Finset (A×B)) (hU : ∀θ,U θ=univ ∨ RestrictedTransfer.Permitted (U θ))
    (G : Q → Θ → Prop) {η : ℝ} (hη : 0<η) (hη' : η<1/2)
    (hg : ∀q θ,G q θ → 1-3*η^2≤event (mix (historyLaw π h q) (posteriorState π h x)) (fun s => s∈U θ)) :
    avg π (fun pq => event (a pq.2) (fun θ => G pq.2 θ ∧ x pq.1∉U θ))≤8*η := by
  let U' : Q → Θ → Finset (A×B) := fun _ θ => if U θ=univ then ∅ else U θ
  let G' : Q → Θ → Prop := fun q θ => G q θ ∧ U θ≠univ
  have hu : ∀q θ,RestrictedTransfer.Permitted (U' q θ) := by
    intro q θ
    by_cases he : U θ=univ
    · simp only [U',he,↓reduceIte]
      exact Or.inr (Or.inr (by simp))
    · simp only [U',he,↓reduceIte]
      exact (hU θ).resolve_left he
  have hh : ∀q θ,G' q θ → 1-3*η^2≤RestrictedTransfer.mass
      (RestrictedTransfer.centerMixture (left π).val h x (fun p q => π.val (p,q)) q) (U' q θ) := by
    intro q θ hqt
    have ht := hg q θ hqt.1
    rw [event_mem_mass] at ht
    change 1-3*η^2≤∑s∈U θ,(mix (historyLaw π h q) (posteriorState π h x)).val s at ht
    simp_rw [mixture_val π h x hμ hκ] at ht
    simpa only [U',hqt.2,↓reduceIte,RestrictedTransfer.mass] using ht
  have ht := RestrictedTransfer.edge_template_transfer (left π).val hμ (left π).total h x
    (fun p q => π.val (p,q)) (fun p q => π.nonneg (p,q))
    (fun p => (left_val π p).symm) (fun q => by simpa only [← right_val] using hκ q)
    (fun q θ => (a q).val θ) (fun q θ => (a q).nonneg θ) (fun q => (a q).total)
    U' hu G' hη hη' hh
  have heq : avg π (fun pq => event (a pq.2) (fun θ => G pq.2 θ ∧ x pq.1∉U θ))=
      ∑p,∑q,∑θ,π.val (p,q)*(a q).val θ*(if G' q θ ∧ x p∉U' q θ then 1 else 0) := by
    simp only [avg,event,Fintype.sum_prod_type,mul_sum,← mul_assoc]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro θ _
    by_cases he : U θ=univ <;> simp [U',G',he]
  exact heq ▸ ht

omit [Fintype A] [Fintype B] in

theorem aggregate_score (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (Y U : Θ → Finset (A×B))
    (good : Θ → P → Q → Prop) (hs : ∀θ,Shape (Y θ) (U θ))
    (hg : ∀θ p q,good θ p q → x p∈U θ ∧ y q∈Y θ ∧ Consistent (bit p q) (x p) (y q)) :
    (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/80000 -
      12*avg π (fun pq => event (a pq.2) (fun θ => ¬good θ pq.1 pq.2)) ≤
      avg (templates π a) (fun θ => DP (slice π a θ) bit y)+DQ π bit x := by
  have ht := avg_mono (templates π a) (fun θ => slice_score (slice π a θ) bit x y
    (good θ) (Y θ) (U θ) (hs θ) (hg θ))
  have he : avg (templates π a) (fun θ => (VP (slice π a θ) bit+VQ (slice π a θ) bit)/80000)=
      (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/80000 := by
    simp only [div_eq_mul_inv,mul_comm _ (80000:ℝ)⁻¹,avg_smul,avg_add,center_variation]
  rw [avg_sub,he,avg_smul,avg_add,center_score] at ht
  simp only [bad,slice_event] at ht
  exact ht
end
end PlanarUnitDistances.CommonTemplate

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteInformation
open scoped InnerProductSpace
open Finset Real

lemma hellinger_pointwise {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : p ≠ 0 → q ≠ 0) :
    (sqrt p - sqrt q)^2 ≤ p * log (p/q) - p + q := by
  by_cases hpz : p = 0
  · simp [hpz, sq_sqrt hq]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm (hac hpz))
  have hspp := sqrt_pos.mpr hpp
  have hsqp := sqrt_pos.mpr hqp
  have hsp := sq_sqrt hp
  have hsq := sq_sqrt hq
  have hl := log_le_sub_one_of_pos (div_pos hsqp hspp)
  rw [log_div (ne_of_gt hsqp) (ne_of_gt hspp), log_sqrt hq, log_sqrt hp] at hl
  have hm : p * (sqrt q / sqrt p) = sqrt p * sqrt q := by
    rw [← mul_div_assoc]
    apply (div_eq_iff (ne_of_gt hspp)).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*p by positivity)
  rw [log_div hpz (hac hpz)]
  nlinarith

theorem hellinger_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) :
    (∑ a, (sqrt (p a) - sqrt (q a))^2) ≤ KL p q := by
  have hh := sum_le_sum (s := univ) (fun a _ => hellinger_pointwise (hp a) (hq a) (hac a))
  simpa only [sum_add_distrib, sum_sub_distrib, hpsum, hqsum, sub_add_cancel, KL] using hh

theorem TV_sq_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : (TV p q)^2 ≤ KL p q := by
  have hH := hellinger_le_KL p q hp hq hpsum hqsum hac
  have hs : (∑ a, (sqrt (p a) + sqrt (q a))^2) ≤ 4 := by
    calc
      _ ≤ ∑ a, (2*p a + 2*q a) := by
        apply sum_le_sum
        intro a _
        nlinarith [sq_nonneg (sqrt (p a) - sqrt (q a)), sq_sqrt (hp a), sq_sqrt (hq a)]
      _ = 4 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hpsum, hqsum]; norm_num
  have hid (a : α) : |p a-q a| =
      |sqrt (p a)-sqrt (q a)| * (sqrt (p a)+sqrt (q a)) := by
    rw [← abs_of_nonneg (show 0 ≤ sqrt (p a)+sqrt (q a) by positivity), ← abs_mul]
    congr 1
    nlinarith [sq_sqrt (hp a), sq_sqrt (hq a)]
  have hcs := sum_mul_sq_le_sq_mul_sq univ
    (fun a => |sqrt (p a)-sqrt (q a)|) (fun a => sqrt (p a)+sqrt (q a))
  simp only [← hid, sq_abs] at hcs
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ∑ a, (sqrt (p a)-sqrt (q a))^2 by positivity)
  unfold TV
  nlinarith

theorem KL_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : 0 ≤ KL p q :=
  (sq_nonneg _).trans (TV_sq_le_KL p q hp hq hpsum hqsum hac)

universe u

end PlanarUnitDistances.FiniteInformation

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceEntropy
open Finset Real FiniteInformation
variable {P Q : Type*} [Fintype P] [Fintype Q]

omit [Fintype Q] in
lemma degree_nonneg (E : P → Q → Prop) (q : Q) : 0 ≤ degree E q :=
  sum_nonneg fun p _ => indicator_nonneg E p q

lemma edgeCount_nonneg (E : P → Q → Prop) : 0 ≤ edgeCount E :=
  sum_nonneg fun q _ => degree_nonneg E q

lemma wedge_nonneg (E : P → Q → Prop) (x : P × P) : 0 ≤ wedge E x := by
  unfold wedge
  exact sum_nonneg fun q _ => div_nonneg
    (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
    (mul_nonneg (edgeCount_nonneg E) (degree_nonneg E _))

lemma pointLaw_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) : ∑ p, pointLaw E p = 1 := by
  unfold pointLaw
  rw [← sum_div, sum_comm]
  exact div_self hE

lemma wedge_fst (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) (p : P) :
    ∑ r, wedge E (p,r) = pointLaw E p := by
  unfold wedge pointLaw
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro q _
  dsimp only
  rw [← sum_div, ← mul_sum]
  change indicator E p q * degree E q / (edgeCount E * degree E q) = _
  exact mul_div_mul_right _ _ (hd q)

lemma wedge_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) (hd : ∀ q, degree E q ≠ 0) :
    ∑ x, wedge E x = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [wedge_fst E hd]
  exact pointLaw_sum E hE

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.UnitCodegree
open Polynomial Complex
open scoped ComplexConjugate

lemma unit_distance_equation (p q : ℂ) (h : dist p q = 1) :
    (q-p)*(conj q-conj p) = 1 := by
  rw [← map_sub, mul_conj, normSq_eq_norm_sq, ← dist_eq_norm, dist_comm q p, h]
  norm_num

end PlanarUnitDistances.UnitCodegree

namespace PlanarUnitDistances.UniformGraphLaw
open Finset FiniteLaw FiniteStarCoupling IncidenceEntropy
open scoped Classical BigOperators
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma right_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (q : Q) :
    (right (law E hE)).val q=degree E q/edgeCount E := by
  rw [right_val]
  simp only [law,←sum_div,degree]
lemma left_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (p : P) :
    (left (law E hE)).val p=pointLaw E p := by
  rw [left_val]
  simp only [law,←sum_div,pointLaw]
lemma row_eq (E : P → Q → Prop) (hE : 0<edgeCount E) {p : P}
    (hp : 0<∑q,indicator E p q) (q : Q) :
    (row (law E hE) p).val q=indicator E p q/(∑q,indicator E p q) := by
  rw [row_val (law E hE) (by rw [left_eq]; exact div_pos hp hE),left_eq]
  change (indicator E p q/edgeCount E)/((∑q,indicator E p q)/edgeCount E)=_
  field_simp

end
end PlanarUnitDistances.UniformGraphLaw

namespace PlanarUnitDistances.GeometricLaw
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
lemma row_count (P Q : Finset Plane) (p : P) :
    (∑q,IncidenceEntropy.indicator (E P Q) p q)=CircleIncidence.degree Q p := by
  change (∑q : Q,if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)=_
  rw [CircleIncidence.degree_sum]
  exact (Finset.sum_coe_sort Q (fun q => if dist (p:Plane) q=1 then (1:ℝ) else 0)).trans
    (by simp only [dist_comm])
lemma left_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) :
    (left (graph P Q he)).val p=CircleIncidence.degree Q p/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.left_eq,IncidenceEntropy.pointLaw,edgeCount_eq,row_count]
lemma right_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (q : Q) :
    (right (graph P Q he)).val q=CircleIncidence.degree P q/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.right_eq,degree_eq,edgeCount_eq]
lemma row_le (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) (q : Q)
    (hp : 0<CircleIncidence.degree Q p) :
    (row (graph P Q he) p).val q ≤ 1/CircleIncidence.degree Q p := by
  rw [graph,UniformGraphLaw.row_eq _ _ (by rw [row_count]; exact hp),row_count]
  apply div_le_div_of_nonneg_right _ hp.le
  unfold IncidenceEntropy.indicator
  split_ifs <;> norm_num

lemma counting_event (P : Finset Plane) (hp : 0<P.card) (A : Finset P) :
    event (counting P hp) (fun p => p∈A)=(A.card:ℝ)/(P.card:ℝ) := by
  have hattach : P.attach ∩ A=A := by ext p; simp
  simp [event,avg,counting,mul_ite,Finset.sum_ite_mem,hattach,div_eq_mul_inv]

lemma image_sub {P : Finset Plane} (A : Finset P) : image A⊆P := by
  intro p hp
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
  exact a.property
lemma image_card {P : Finset Plane} (A : Finset P) : (image A).card=A.card :=
  Finset.card_image_of_injective _ Subtype.val_injective
lemma event_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    (A : Finset P) (B : Finset Q) :
    event (graph P Q he) (fun pq => pq.1∈A ∧ pq.2∈B)=
      CircleIncidence.incidences (image A) (image B)/CircleIncidence.incidences P Q := by
  simp only [event,avg,graph,UniformGraphLaw.law,edgeCount_eq,Fintype.sum_prod_type]
  simp_rw [mul_ite,mul_one,mul_zero,ite_and]
  have hattach : Q.attach ∩ B=B := by ext q; simp
  have hsum : ∀p : P,
      (∑q : Q,if p∈A then if q∈B then IncidenceEntropy.indicator (E P Q) p q/CircleIncidence.incidences P Q else 0 else 0)=
      if p∈A then ∑q∈B,IncidenceEntropy.indicator (E P Q) p q/CircleIncidence.incidences P Q else 0 := by
    intro p
    by_cases hp : p∈A
    · simp [hp,hattach]
    · simp [hp]
  simp_rw [hsum]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  simp_rw [←Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  unfold CircleIncidence.incidences image
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  apply Finset.sum_congr rfl
  intro q _
  rw [CircleIncidence.degree_sum,Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  rfl

theorem expansion (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    {ξ : ℝ}
    (hx : ∀A⊆P,∀B⊆Q,CircleIncidence.incidences A B/CircleIncidence.incidences P Q ≤
      Real.sqrt ((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))*
        (((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))^(1/25:ℝ)+ξ)) :
    ∀A : Finset P,∀B : Finset Q,event (graph P Q he) (fun pq => pq.1∈A ∧ pq.2∈B) ≤
      Real.sqrt (event (counting P (card_pos P Q he).1) (fun p => p∈A)*
        event (counting Q (card_pos P Q he).2) (fun q => q∈B))*
        ((event (counting P (card_pos P Q he).1) (fun p => p∈A)*
          event (counting Q (card_pos P Q he).2) (fun q => q∈B))^(1/25:ℝ)+ξ) := by
  intro A B
  rw [event_eq,counting_event,counting_event]
  simpa only [image_card] using hx (image A) (image_sub A) (image B) (image_sub B)

end
end PlanarUnitDistances.GeometricLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sequence
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceSequence
open Filter PowerGrowth CircleIncidence
open scoped Classical
noncomputable section
lemma Good.point_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (p : P) : 0 < degree Q p := by
  have hm : (0:ℝ) < P.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).1
  have hh := (le_div_iff₀ h.positive).mp (h.atomP p p.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hm) h.positive).trans_le hh

lemma Good.center_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (q : Q) : 0 < degree P q := by
  have hn : (0:ℝ) < Q.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).2
  have hh := (le_div_iff₀ h.positive).mp (h.atomQ q q.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hn) h.positive).trans_le hh

lemma Good.information_nonneg {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) : 0 ≤ information P Q := by
  have he : IncidenceEntropy.edgeCount (GeometricLaw.E P Q) ≠ 0 := by
    rw [GeometricLaw.edgeCount_eq]; exact h.positive.ne'
  have hd : ∀q : Q,IncidenceEntropy.degree (GeometricLaw.E P Q) q ≠ 0 := by
    intro q; rw [GeometricLaw.degree_eq]; exact (h.center_degree_pos q).ne'
  have hp : ∀p : P,0 < IncidenceEntropy.pointLaw (GeometricLaw.E P Q) p := by
    intro p
    rw [IncidenceEntropy.pointLaw,GeometricLaw.row_count,GeometricLaw.edgeCount_eq]
    exact div_pos (h.point_degree_pos p) h.positive
  exact FiniteInformation.KL_nonneg _ _ (IncidenceEntropy.wedge_nonneg _)
    (fun pr => (mul_pos (hp pr.1) (hp pr.2)).le) (IncidenceEntropy.wedge_sum _ he hd)
    (by rw [Fintype.sum_prod_type,←Finset.sum_mul_sum,IncidenceEntropy.pointLaw_sum _ he,one_mul])
    (fun pr _ => (mul_pos (hp pr.1) (hp pr.2)).ne')

lemma Sequence.accuracy_limit : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma Sequence.error_limit (s : Sequence) : Tendsto s.ξ atTop (nhds 0) :=
  squeeze_zero (fun i => (s.good i).error_nonneg) (fun i => (s.good i).error_le)
    Sequence.accuracy_limit

end
end PlanarUnitDistances.IncidenceSequence

namespace PlanarUnitDistances.CommonFieldModel
open scoped Classical
noncomputable section
variable (P Q : Finset Plane)

variable {P Q}

namespace Model
variable (M : Model P Q)
lemma center_injective : Function.Injective (M.z ∘ Sum.inr) := by
  intro q r h
  apply Subtype.val_injective
  apply UnitCodegree.zCoordinate.injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inr] using hh
lemma unit_identity (p : P) (q : Q) (h : dist (p:Plane) (q:Plane)=1) :
    (M.z (.inl p)-M.z (.inr q))*(M.w (.inl p)-M.w (.inr q))=1 := by
  apply Subtype.val_injective
  change ((M.z (.inl p):ℂ)-(M.z (.inr q):ℂ))*((M.w (.inl p):ℂ)-(M.w (.inr q):ℂ))=1
  simp only [M.z_eq,M.w_eq,location,Sum.elim_inl,Sum.elim_inr]
  exact UnitCodegree.unit_distance_equation _ _ (by
    rw [UnitCodegree.zCoordinate.dist_map,dist_comm]; exact h)

lemma sub_mem (v r : P⊕Q) : M.z v-M.z r ∈ M.support :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(v,r),Finset.mem_univ _,rfl⟩))
lemma difference_mem (v r s : P⊕Q) :
    ((M.z v-M.z r)-(M.z v-M.z s))*((M.z v-M.z r)⁻¹-(M.z v-M.z s)⁻¹) ∈ M.support :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v,r,s),Finset.mem_univ _,rfl⟩)
end Model
end
end PlanarUnitDistances.CommonFieldModel

namespace PlanarUnitDistances.ExpansionConsequences
open Finset Real

section FiniteLaw
variable {P Q : Type*} [Fintype P] [Fintype Q]
variable (w : P → Q → ℝ)

lemma threshold_markov {Q : Type*} [Fintype Q] (κ g : Q → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hg : ∀ q, 0 ≤ g q) {d : ℝ} (_hd : 0 ≤ d) :
    d * mass κ (univ.filter (fun q => d < g q)) ≤ ∑ q, κ q * g q := by
  classical
  rw [mass, mul_sum]
  calc
    _ ≤ ∑ q ∈ univ.filter (fun q => d < g q), κ q * g q := by
      apply sum_le_sum
      intro q hq
      calc
        d * κ q = κ q * d := mul_comm _ _
        _ ≤ κ q * g q := mul_le_mul_of_nonneg_left (le_of_lt (mem_filter.mp hq).2) (hκ q)
    _ ≤ ∑ q, κ q * g q :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => mul_nonneg (hκ q) (hg q))

theorem height_tail_mass {A : Type*} [Fintype A] (μ a : A → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (ha : ∀ p, 0 ≤ a p)
    {C S R : ℝ} (hS : 0 < S) (hR : 0 < R)
    (hm : ∑ p, μ p * a p ≤ C*S) :
    mass μ (univ.filter (fun p => R*S < a p)) ≤ C/R := by
  classical
  have h := threshold_markov μ a hμ ha (mul_pos hR hS).le
  have hh : R * mass μ (univ.filter (fun p => R*S < a p)) ≤ C := by
    nlinarith
  exact (le_div_iff₀ hR).mpr (by nlinarith)
end FiniteLaw

universe u

end PlanarUnitDistances.ExpansionConsequences

namespace PlanarUnitDistances.LawExpansion
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q A : Type*} [Fintype P] [Fintype Q] [Fintype A]

lemma mass_event (μ : Law P) (F : Finset P) :
    ExpansionConsequences.mass μ.val F=event μ (fun p => p∈F) := by
  unfold ExpansionConsequences.mass event avg
  simp only [mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_of_subset (subset_univ _)]

lemma rect_event (π : Law (P×Q)) (F : Finset P) (G : Finset Q) :
    ExpansionConsequences.rect (fun p q => π.val (p,q)) F G=
      event π (fun pq => pq.1∈F ∧ pq.2∈G) := by
  simp only [ExpansionConsequences.rect,event,avg,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]
  symm
  calc
    _ = ∑p,if p∈F then ∑q∈G,π.val (p,q) else 0 := by
      apply sum_congr rfl
      intro p _
      by_cases hp : p∈F
      · simp only [hp,true_and,↓reduceIte,←sum_filter,filter_mem_eq_of_subset (subset_univ _)]
      · simp [hp]
    _ = _ := by rw [←sum_filter,filter_mem_eq_of_subset (subset_univ _)]

end
end PlanarUnitDistances.LawExpansion

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_AbsoluteValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset
noncomputable section

section Entries
variable (K : Type*) [Field K] [NumberField K]

lemma infiniteEntry_count : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K :=
  AlgHom.card ℚ K ℂ

end Entries

end
end PlanarUnitDistances.WeightedAbsoluteValues

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_HeightTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x-y| < 1 := by
  have hx₁ := Int.floor_le x
  have hx₂ := Int.lt_floor_add_one x
  have hy₁ := Int.floor_le y
  have hy₂ := Int.lt_floor_add_one y
  rw [← h] at hy₁ hy₂
  rw [abs_lt]
  constructor <;> linarith

lemma norm_le_of_same_grid {r : ℝ} (hr : 0 < r) {z w : ℂ} {u : ℝ × ℝ}
    (h : gridLabel r z u = gridLabel r w u) : ‖z-w‖ ≤ 2*r := by
  have hx := abs_sub_lt_one_of_floor_eq (congrArg Prod.fst h)
  have hy := abs_sub_lt_one_of_floor_eq (congrArg Prod.snd h)
  rw [add_sub_add_right_eq_sub,← sub_div,abs_div,abs_of_pos hr,div_lt_one hr] at hx hy
  calc
    _ ≤ |(z-w).re|+|(z-w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ r+r := add_le_add hx.le hy.le
    _ = 2*r := by ring

end
end PlanarUnitDistances.GridShift

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_States
attribute [-instance] _root_.OAI.PlanarUnitDistances.LevelScale.instIsFiniteMeasureProdPlaceRealMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteStates
open MeasureTheory Set Real
open scoped Classical
noncomputable section
variable {V : Type*}

lemma label_eq_iff (r : Setoid V) (x y : V) : label r x=label r y ↔ r.r x y := by
  constructor
  · intro he
    have hh := congrFun he y
    simpa only [label,r.refl y,decide_true,decide_eq_true_eq] using hh
  · intro h
    funext z
    apply Bool.decide_congr
    exact ⟨fun hx => r.trans (r.symm h) hx,fun hy => r.trans h hy⟩

end
end PlanarUnitDistances.FiniteStates

namespace PlanarUnitDistances.FiniteLevels
open MeasureTheory Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSingletonClass J] in
lemma integral_eq (weight : ℝ≥0) (l u : J → ℝ) (f : J × ℝ → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀x, |f x| ≤ M) :
    (∫x, f x ∂measure weight l u) =
      (weight : ℝ) * ∑ j, ∫ s in Icc (l j) (u j), f (j,s) := by
  have hm (j : J) : Measurable (fun s : ℝ => (j,s)) :=
    measurable_const.prodMk measurable_id
  have hi (j : J) : Integrable f
      (Measure.map (fun s : ℝ => (j,s)) (volume.restrict (Icc (l j) (u j)))) := by
    apply Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x
  unfold measure
  rw [integral_finsetSum_measure (fun j _ => (hi j).smul_measure_nnreal (c := weight))]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact integral_map (hm j).aemeasurable hf.aestronglyMeasurable

end
end PlanarUnitDistances.FiniteLevels

namespace PlanarUnitDistances.BudgetPlaces
open Real Finset
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]

lemma differenceProduct_ne_zero {d d' : K} (h : d ≠ d') :
    differenceProduct d d' ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr h) (sub_ne_zero.mpr (inv_injective.ne h))

lemma inv_difference_abs (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d ≠ 0) (hd' : d' ≠ 0) :
    v (d⁻¹-d'⁻¹) = v (d-d')/(v d*v d') := by
  have he : d⁻¹-d'⁻¹ = -(d-d')/(d*d') := by field_simp; ring
  rw [he,map_div₀,v.map_neg,v.map_mul]

theorem place_identity (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    -log (v (differenceProduct d d')) =
      2*alpha v d d'-(max (threshold v d) (threshold v d')-
        min (threshold v d) (threshold v d')) := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have hdv := v.pos hd
  have hdv' := v.pos hd'
  have hI := v.pos (sub_ne_zero.mpr (inv_injective.ne hdd))
  rw [differenceProduct,v.map_mul,log_mul hD.ne' hI.ne',inv_difference_abs v hd hd',
    log_div hD.ne' (mul_ne_zero hdv.ne' hdv'.ne'),log_mul hdv.ne' hdv'.ne']
  unfold alpha threshold
  have hm := min_add_max (-log (v d)) (-log (v d'))
  linarith

lemma alpha_nonneg_nonarch (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {d d' : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    0 ≤ alpha v d d' := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have htri : v (d-d') ≤ max (v d) (v d') := by
    simpa only [sub_eq_add_neg,v.map_neg] using hv d (-d')
  unfold alpha threshold
  by_cases hh : v d ≤ v d'
  · rw [max_eq_right hh] at htri
    have hlog := log_le_log (v.pos hd) hh
    rw [min_eq_right (by linarith)]
    linarith [log_le_log hD htri]
  · have hh' := (le_of_not_ge hh)
    rw [max_eq_left hh'] at htri
    have hlog := log_le_log (v.pos hd') hh'
    rw [min_eq_left (by linarith)]
    linarith [log_le_log hD htri]

lemma alpha_add_log_two_nonneg (v : AbsoluteValue K ℝ)
    {d d' : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    0 ≤ alpha v d d'+log 2 := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have htri : v (d-d') ≤ v d+v d' := by
    simpa only [sub_eq_add_neg,v.map_neg] using v.add_le d (-d')
  unfold alpha threshold
  by_cases hh : v d ≤ v d'
  · have hlog := log_le_log (v.pos hd) hh
    have ht : v (d-d') ≤ 2*v d' := by linarith
    have hLt := log_le_log hD ht
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (v.pos hd').ne'] at hLt
    rw [min_eq_right (by linarith)]
    linarith
  · have hh' := (le_of_not_ge hh)
    have hlog := log_le_log (v.pos hd') hh'
    have ht : v (d-d') ≤ 2*v d := by linarith
    have hLt := log_le_log hD ht
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (v.pos hd).ne'] at hLt
    rw [min_eq_left (by linarith)]
    linarith

section Global
open PlanarUnitDistances.WeightedAbsoluteValues
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in

theorem arch_allowance :
    (∑ _σ : K →ₐ[ℚ] ℂ, 2*log 2)/(Module.finrank ℚ K : ℝ) = 2*log 2 := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  simp only [sum_const,card_univ,nsmul_eq_mul,infiniteEntry_count]
  field_simp

end Global
end
end PlanarUnitDistances.BudgetPlaces

namespace PlanarUnitDistances.PlaceLevels
open Finset Real WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

lemma log_off_support {S : Finset K} {x : K} (hx : x∈S)
    {v : Nat.Primes × Gal(K/ℚ)} (hv : v∉finiteSupport K S) :
    log (finiteEntry K v.1 v.2 x)=0 := by
  by_cases h0 : x=0
  · simp [h0]
  have hp : v.1.val ∉ rootDenominators K x ∪ rootDenominators K x⁻¹ := by
    intro hh
    apply hv
    exact mem_biUnion.mpr ⟨x,hx,mem_product.mpr ⟨mem_subtype.mpr hh,mem_univ _⟩⟩
  rw [finiteEntry_eq_one_off_support K h0 _ _ hp,log_one]

lemma log_le_radius {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    |log (av K v x)|≤radius K S v := by
  exact single_le_sum (fun y _ => abs_nonneg (log (av K v y))) hx
lemma threshold_in_range {S : Finset K} {x : K} (hx : x∈S) (v : Place K S) :
    -radius K S v ≤ -log (av K v x) ∧ -log (av K v x) ≤ radius K S v := by
  have h := abs_le.mp (log_le_radius K hx v)
  constructor <;> linarith

lemma sum_logs {S : Finset K} {x : K} (hx : x∈S) :
    (∑v : Place K S,log (av K v x)) =
      (∑σ : K →ₐ[ℚ] ℂ,log (infiniteEntry K σ x))+
      ∑ᶠv : Nat.Primes × Gal(K/ℚ), log (finiteEntry K v.1 v.2 x) := by
  change (∑v : (K →ₐ[ℚ] ℂ) ⊕ ↥(finiteSupport K S),log (av K v x))=_
  rw [Fintype.sum_sum_type]
  congr 1
  change (∑v : ↥(finiteSupport K S), log (finiteEntry K v.val.1 v.val.2 x))=_
  rw [Finset.sum_coe_sort (finiteSupport K S) (fun v => log (finiteEntry K v.1 v.2 x))]
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  by_contra hs
  exact hv (log_off_support K hx hs)

lemma sum_log_product_formula [IsGalois ℚ K] {S : Finset K} {x : K}
    (hx : x∈S) (h0 : x≠0) :
    (∑v : Place K S,log (av K v x))/(Module.finrank ℚ K:ℝ)=0 := by
  rw [sum_logs K hx]
  exact weighted_log_product_formula K h0
end
end PlanarUnitDistances.PlaceLevels

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma abs_bit_sub_eq (a b s : ℝ) :
    |bit a s - bit b s| = (Ico (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) s := by
  by_cases ha : s < a <;> by_cases hb : s < b <;>
    simp [bit,ha,hb,Set.indicator,mem_Ico]

lemma bit_sub_integral {l u a b : ℝ} (hla : l ≤ a) (hua : a ≤ u)
    (hlb : l ≤ b) (hub : b ≤ u) :
    ∫ s in Icc l u, |bit a s - bit b s| = |a-b| := by
  simp_rw [abs_bit_sub_eq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  rw [measureReal_restrict_apply measurableSet_Ico]
  have hsub : Ico (min a b) (max a b) ⊆ Icc l u := by
    intro s hs
    exact ⟨(le_min hla hlb).trans hs.1, hs.2.le.trans (max_le hua hub)⟩
  rw [inter_eq_left.mpr hsub,Real.volume_real_Ico]
  simp [smul_eq_mul,max_sub_min_eq_abs,abs_sub_comm]

end
end PlanarUnitDistances.ThresholdProfiles

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Predictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]
lemma event_and_lower (μ : Law X) (P Q : X → Prop) :
    event μ P+event μ Q-1 ≤ event μ (fun x => P x∧Q x) := by
  have h := avg_mono μ (f := fun x => (if P x then (1:ℝ) else 0)+(if Q x then (1:ℝ) else 0)-1)
    (g := fun x => if P x∧Q x then (1:ℝ) else 0) (fun x => by split_ifs <;> simp_all)
  simpa only [avg_sub,avg_add,avg_const,avg_ite] using h
lemma event_disjoint_union (μ : Law X) (P Q : X → Prop) (h : ∀x,¬(P x∧Q x)) :
    event μ (fun x => P x∨Q x)=event μ P+event μ Q := by
  unfold event
  rw [← avg_add]
  apply avg_congr
  intro x
  have := h x
  split_ifs <;> simp_all
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteMarginalScore
open Finset FiniteLaw StrictCross CrossStructure CrossSampling StarScore
open scoped Classical
noncomputable section
variable {A B Q : Type*} [Fintype A] [Fintype B] [Fintype Q]

lemma collision_nonneg {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) :
    0≤collision ν φ := sum_nonneg fun _ _ => sq_nonneg _
lemma collision_atom {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) (a : Y) :
    event ν (fun x => φ x=a)^2 ≤ collision ν φ := by
  unfold collision
  exact single_le_sum (f := fun y => (event ν (fun x => φ x=y))^2) (fun _ _ => sq_nonneg _) (mem_univ a)
lemma collision_two {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y)
    {a b : Y} (hab : a≠b) :
    event ν (fun x => φ x=a)^2+event ν (fun x => φ x=b)^2 ≤ collision ν φ := by
  have h := sum_le_sum_of_subset_of_nonneg (show ({a,b}:Finset Y)⊆univ from subset_univ _)
    (f := fun y => event ν (fun x => φ x=y)^2) (fun _ _ _ => sq_nonneg _)
  simpa [collision,hab] using h
lemma collision_one_linear {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) (a : Y) :
    2*event ν (fun x => φ x=a)-1≤collision ν φ := by
  have h := collision_atom ν φ a
  nlinarith [sq_nonneg (event ν (fun x => φ x=a)-1)]
lemma collision_two_linear {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y)
    {a b : Y} (hab : a≠b) :
    event ν (fun x => φ x=a)+event ν (fun x => φ x=b)-1/2≤collision ν φ := by
  have h := collision_two ν φ hab
  nlinarith [sq_nonneg (event ν (fun x => φ x=a)+event ν (fun x => φ x=b)-1),
    sq_nonneg (event ν (fun x => φ x=a)-event ν (fun x => φ x=b))]

lemma tau_lower (ν : Law (A×B)) : -1≤tau ν := by
  unfold tau
  linarith [collision_nonneg ν Prod.fst,collision_nonneg ν Prod.snd]
lemma tau_row (ν : Law (A×B)) (a : A) : 2*rowMass ν a-2≤tau ν := by
  have h := collision_one_linear ν Prod.fst a
  have h' := collision_nonneg ν Prod.snd
  change 2*rowMass ν a-1≤collision ν Prod.fst at h
  unfold tau
  linarith
lemma tau_col (ν : Law (A×B)) (b : B) : 2*colMass ν b-2≤tau ν := by
  have h := collision_one_linear ν Prod.snd b
  have h' := collision_nonneg ν Prod.fst
  change 2*colMass ν b-1≤collision ν Prod.snd at h
  unfold tau
  linarith
lemma tau_cross (ν : Law (A×B)) (y : A×B) : crossMass ν y-3/2≤tau ν := by
  have hA := collision_atom ν Prod.fst y.1
  have hB := collision_atom ν Prod.snd y.2
  have hm : crossMass ν y ≤ rowMass ν y.1+colMass ν y.2 :=
    (event_mono ν (fun x hx => hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2))).trans
      (event_union_le ν (fun x => x.1=y.1) (fun x => x.2=y.2))
  change rowMass ν y.1 ^ 2 ≤ _ at hA
  change colMass ν y.2 ^ 2 ≤ _ at hB
  unfold tau
  nlinarith [sq_nonneg (rowMass ν y.1+colMass ν y.2-1),sq_nonneg (rowMass ν y.1-colMass ν y.2)]
lemma tau_atom (ν : Law (A×B)) (y : A×B) :
    4*event ν (fun x => x=y)-3≤tau ν := by
  have hA := collision_one_linear ν Prod.fst y.1
  have hB := collision_one_linear ν Prod.snd y.2
  have hmA := event_mono ν (fun x (hx : x=y) => congrArg Prod.fst hx)
  have hmB := event_mono ν (fun x (hx : x=y) => congrArg Prod.snd hx)
  unfold tau
  linarith
lemma tau_two (ν : Law (A×B)) {y z : A×B} (hA : y.1≠z.1) (hB : y.2≠z.2) :
    2*event ν (fun x => x=y∨x=z)-2≤tau ν := by
  have ha := collision_two_linear ν Prod.fst hA
  have hb := collision_two_linear ν Prod.snd hB
  have hmA := event_mono ν (fun x (hx : x=y∨x=z) => hx.elim
    (fun h => Or.inl (congrArg Prod.fst h)) (fun h => Or.inr (congrArg Prod.fst h)))
  have hmB := event_mono ν (fun x (hx : x=y∨x=z) => hx.elim
    (fun h => Or.inl (congrArg Prod.snd h)) (fun h => Or.inr (congrArg Prod.snd h)))
  rw [event_disjoint_union ν (fun x => x.1=y.1) (fun x => x.1=z.1)
    (fun x h => hA (h.1.symm.trans h.2))] at hmA
  rw [event_disjoint_union ν (fun x => x.2=y.2) (fun x => x.2=z.2)
    (fun x h => hB (h.1.symm.trans h.2))] at hmB
  unfold tau
  linarith

lemma two_cross_mass (ν : Law (A×B)) {ε : ℝ} {y z : A×B}
    (hy : 1-ε≤crossMass ν y) (hz : 1-ε≤crossMass ν z) :
    1-2*ε≤event ν (fun x => Adj x y∧Adj x z) := by
  have h := event_and_lower ν (fun x => Adj x y) (fun x => Adj x z)
  change crossMass ν y+crossMass ν z-1≤_ at h
  linarith
lemma three_cross_mass (ν : Law (A×B)) {ε : ℝ} {y z w : A×B}
    (hy : 1-ε≤crossMass ν y) (hz : 1-ε≤crossMass ν z) (hw : 1-ε≤crossMass ν w) :
    1-3*ε≤event ν (fun x => Adj x y∧Adj x z∧Adj x w) := by
  have h₁ := two_cross_mass ν hz hw
  have h₂ := event_and_lower ν (fun x => Adj x y) (fun x => Adj x z∧Adj x w)
  change crossMass ν y+event ν (fun x => Adj x z∧Adj x w)-1≤_ at h₂
  linarith

theorem second_slice (μ : Law Q) (bit : Q → Bool) (state : Q → A×B)
    (ν : Law (A×B)) (x : A×B) (good : Q → Prop) {ε : ℝ} (hε : 0≤ε)
    (hcons : ∀q,good q → Consistent (bit q) x (state q))
    (hprob : ∀q,good q → 1-ε≤crossMass ν (state q)) :
    variation μ bit/80000-20*(event μ (fun q => ¬good q)+ε) ≤ score μ bit state+tau ν := by
  let b := event μ (fun q => ¬good q)
  let v := variation μ bit
  let d := score μ bit state
  have hb : 0≤b := event_nonneg _ _
  have hv : v≤1/2 := variation_le_half _ _
  have hd : -v≤d := score_lower _ _ _
  have hd' : -1/2≤d := by simpa only [neg_div] using score_ge_half_neg μ bit state
  have ht := tau_lower ν
  change v/80000-20*(b+ε)≤d+tau ν
  by_cases hg : ∃q,good q
  swap
  · have he : b=1 := by
      dsimp [b]
      calc
        _ = event μ (fun _ => True) := event_congr _ (fun q => by simp only [not_exists] at hg; simp [hg q])
        _ = 1 := event_true _
    rw [he]
    linarith
  obtain ⟨q₀,hq₀⟩ := hg
  let Y := (univ.filter good).image state
  have memY {y : A×B} : y∈Y ↔ ∃q,good q ∧ state q=y := by simp only [Y,mem_image,mem_filter,mem_univ,true_and]
  have hmem (q : Q) (hq : good q) : state q∈Y := memY.mpr ⟨q,hq,rfl⟩
  have hx (y : A×B) (hy : y∈Y) : Adj x y := by
    obtain ⟨q,hq,rfl⟩ := memY.mp hy
    exact consistent_adj (hcons q hq)
  have hm (y : A×B) (hy : y∈Y) : 1-ε≤crossMass ν y := by
    obtain ⟨q,hq,rfl⟩ := memY.mp hy
    exact hprob q hq
  rcases classification Y with hs|hs|hs|hs
  · have hd₁ := constant_good μ bit state good (by
      intro q r hq hr
      have he := card_le_one.mp hs _ (hmem q hq) _ (hmem r hr)
      exact ⟨bit_unique (hcons q hq) (he ▸ hcons r hr),he⟩)
    have ht₁ := tau_cross ν (state q₀)
    have ht₂ := hprob q₀ hq₀
    change (1-1/20000:ℝ)-4*b≤d at hd₁
    linarith
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := hs
    have hn : y.2≠z.2 := by intro hh; exact hyz (Prod.ext he hh)
    have hzx : Adj x (y.1,z.2) := by simpa only [Adj,←he] using hx z hz
    have hxr : x.1=y.1 := ((same_row hn x).mp ⟨hx y hy,hzx⟩).1
    have hr : 1-2*ε≤rowMass ν y.1 := by
      refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
      intro u hu
      exact ((same_row hn u).mp ⟨hu.1,by simpa only [Adj,←he] using hu.2⟩).1
    rcases hw with hall|⟨w,hw,hwy⟩
    · have hc : ∀q,good q → bit q=true := by
        intro q hq
        exact bit_true (hcons q hq) (hxr.trans (hall _ (hmem q hq)).symm)
      have hcv := constant_bit μ bit good (fun q r hq hr => (hc q hq).trans (hc r hr).symm)
      have ht₁ := tau_row ν y.1
      change v≤2*b at hcv
      linarith
    · have ha : 1-3*ε≤event ν (fun u => u=(y.1,w.2)) := by
        refine (three_cross_mass ν (hm y hy) (hm z hz) (hm w hw)).trans (event_mono ν ?_)
        intro u hu
        exact third_off_row hn hwy.symm u hu.1 (by simpa only [Adj,←he] using hu.2.1) hu.2.2
      have ht₁ := tau_atom ν (y.1,w.2)
      linarith
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := hs
    have hn : y.1≠z.1 := by intro hh; exact hyz (Prod.ext hh he)
    have hzx : Adj x (z.1,y.2) := by simpa only [Adj,←he] using hx z hz
    have hxc : x.2=y.2 := ((same_column hn x).mp ⟨hx y hy,hzx⟩).1
    have hr : 1-2*ε≤colMass ν y.2 := by
      refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
      intro u hu
      exact ((same_column hn u).mp ⟨hu.1,by simpa only [Adj,←he] using hu.2⟩).1
    rcases hw with hall|⟨w,hw,hwy⟩
    · have hc : ∀q,good q → bit q=false := by
        intro q hq
        exact bit_false (hcons q hq) (hxc.trans (hall _ (hmem q hq)).symm)
      have hcv := constant_bit μ bit good (fun q r hq hr => (hc q hq).trans (hc r hr).symm)
      have ht₁ := tau_col ν y.2
      change v≤2*b at hcv
      linarith
    · have ha : 1-3*ε≤event ν (fun u => u=(w.1,y.2)) := by
        refine (three_cross_mass ν (hm y hy) (hm z hz) (hm w hw)).trans (event_mono ν ?_)
        intro u hu
        have huy := (swap_iff u y).mpr hu.1
        have huz := (swap_iff u z).mpr hu.2.1
        have huw := (swap_iff u w).mpr hu.2.2
        have he' := third_off_row hn hwy.symm u.swap huy
          (by simpa only [Prod.swap,←he] using huz) huw
        exact Prod.ext (congrArg Prod.snd he') (congrArg Prod.fst he')
      have ht₁ := tau_atom ν (w.1,y.2)
      linarith
  · obtain ⟨y,hy,z,hz,h₁,h₂,hw⟩ := hs
    rcases hw with hall|⟨w,hw,hyw,hzw,hyw',hzw'⟩
    · have ha : 1-2*ε≤event ν (fun u => u=(y.1,z.2)∨u=(z.1,y.2)) := by
        refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
        intro u hu
        exact (corners h₁ h₂ u).mp hu
      have ht₁ := tau_two ν (y := (y.1,z.2)) (z := (z.1,y.2)) h₁ h₂.symm
      have hinj := pair_coord_inj hall h₁ h₂
      have hdet := determined μ bit state good (by
        intro q r hq hr hbit
        exact determined_of_inj hinj x (state q) (hmem q hq) (state r) (hmem r hr)
          (bit q) (hcons q hq) (hbit ▸ hcons r hr))
      change (1/40000:ℝ)-6*b≤d at hdet
      linarith
    · exact (three_independent h₁ hyw hzw h₂ hyw' hzw' x ⟨hx y hy,hx z hz,hx w hw⟩).elim
end
end PlanarUnitDistances.FiniteMarginalScore

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma avg_comm (μ : Law X) (ν : Law Y) (f : X → Y → ℝ) :
    avg μ (fun x => avg ν (f x)) = avg ν (fun y => avg μ (fun x => f x y)) := by
  simp only [avg,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteLaw
open MeasureTheory Finset Set
open scoped Classical
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma fromMeasure_avg (μ : Measure S) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ) (f : S → ℝ) :
    avg (fromMeasure μ hμ) f=(∫s,f s ∂μ)/μ.real Set.univ := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [avg,fromMeasure,smul_eq_mul]
  rw [Finset.sum_div]
  apply sum_congr rfl; intro s _; ring

variable {Ω : Type*} [MeasurableSpace Ω]

lemma compress_avg (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ)
    (c : Ω → S) (hc : Measurable c) (f : S → ℝ) :
    avg (compress μ hμ c hc) f=(∫s,f (c s) ∂μ)/μ.real Set.univ := by
  rw [compress,fromMeasure_avg,map_real_univ μ c hc,
    integral_map hc.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scale
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceScale
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence
open scoped Classical
noncomputable section
variable (s : Sequence)
lemma positive (n : ℕ) (p : s.P n) : 0<(left (graph s n)).val p := by
  rw [graph,GeometricLaw.left_eq]
  exact div_pos ((s.good n).point_degree_pos p) (s.good n).positive
lemma positiveQ (n : ℕ) (q : s.Q n) : 0<(right (graph s n)).val q := by
  rw [graph,GeometricLaw.right_eq]
  exact div_pos ((s.good n).center_degree_pos q) (s.good n).positive
lemma support (n : ℕ) (p : s.P n) (q : s.Q n) (h : 0<(graph s n).val (p,q)) :
    GeometricLaw.E (s.P n) (s.Q n) p q := by
  change 0<IncidenceEntropy.indicator (GeometricLaw.E (s.P n) (s.Q n)) p q/_ at h
  by_contra hn
  simp [IncidenceEntropy.indicator,hn] at h
lemma row_bound (n : ℕ) (p : s.P n) (q : s.Q n) :
    (row (graph s n) p).val q≤1/(s.t n^(1/2:ℝ)) := by
  have hp := (s.good n).point_degree_pos p
  have he := (s.good n).positive
  have hb := (le_div_iff₀ he).mp ((s.good n).atomP p p.property)
  have hd : s.t n^(1/2:ℝ)≤CircleIncidence.degree (s.Q n) p :=
    (s.good n).degreeP.trans (by simpa only [div_mul_eq_mul_div] using hb)
  exact (GeometricLaw.row_le _ _ he p q hp).trans
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by linarith [s.large n,Nat.cast_nonneg (α:=ℝ) n]) _) hd)
end
end PlanarUnitDistances.IncidenceScale

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling StrictCross CrossSampling CrossTemplates CrossStructure
open scoped Classical
noncomputable section
variable {P Q H A B I : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype I]

lemma bad_good_indicator (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s] :
    (if ¬(p ∧ q ∧ r ∧ s) then (1:ℝ) else 0) ≤
      (if ¬p then 1 else 0)+(if ¬q then 1 else 0)+(if ¬r then 1 else 0)+
        (if r ∧ ¬s then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;>
    simp [hp,hq,hr,hs]

lemma candidate_miss_mean (π : Law (P×Q)) (h : P → H) (x : P → A×B) (y : Q → A×B)
    {ε : ℝ} (hε : 0<ε) :
    avg π (fun pq => event (templateLaw (I := I) π h pq.2)
      (fun θ => y pq.2∉Candidates (posteriorState π h x) ε θ))≤
      ((Fintype.card I:ℝ)/ε)*predictionError π h x y := by
  have hc := avg_mono (right π) (fun q => candidate_miss (I := I) (historyLaw π h q)
    (posteriorState π h x) (y q) hε.le)
  rw [avg_smul,avg_smul] at hc
  have he : avg (right π) (fun q => avg (historyLaw π h q)
      (fun v => 1-crossMass (posteriorState π h x v) (y q)))=predictionError π h x y := by
    simp only [historyLaw,push_avg]
    exact col_avg π _
  rw [he] at hc
  have he' : avg (right π) (fun q => event (templateLaw (I := I) π h q)
      (fun θ => y q∉Candidates (posteriorState π h x) ε θ))=
      avg π (fun pq => event (templateLaw (I := I) π h pq.2)
        (fun θ => y pq.2∉Candidates (posteriorState π h x) ε θ)) := push_avg π Prod.snd _
  change ε*avg (right π) (fun q => event (templateLaw (I := I) π h q)
      (fun θ => y q∉Candidates (posteriorState π h x) ε θ))≤_ at hc
  rw [he'] at hc
  rw [mul_comm ε] at hc
  have hd := (le_div_iff₀ hε).mpr hc
  simpa only [div_mul_eq_mul_div] using hd

lemma failure_mean (π : Law (P×Q)) (h : P → H) (x : P → A×B)
    {ε α : ℝ} (hα : 0<α) (hα1 : α<1) (hI : 0<Fintype.card I) (hk : (Fintype.card I:ℝ)*ε<1) :
    avg π (fun pq => event (templateLaw (I := I) π h pq.2)
      (Failure (historyLaw π h pq.2) (posteriorState π h x) ε α))≤
      samplingError (Fintype.card I) α/(1-(Fintype.card I:ℝ)*ε) := by
  apply avg_le_const
  intro pq
  have hs := failure_bound (I := I) (historyLaw π h pq.2) (posteriorState π h x)
    (ε := ε) hα hα1 hI
  apply (le_div_iff₀ (by linarith : 0<1-(Fintype.card I:ℝ)*ε)).mpr
  simpa only [mul_comm,templateLaw,samplingError] using hs

theorem common_score (π : Law (P×Q)) (h : P → H) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    {ε η : ℝ} (hε : 0<ε) (hk : (Fintype.card I:ℝ)*ε<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2) :
    (avg (templates π (templateLaw (I := I) π h))
      (fun θ => VP (slice π (templateLaw π h) θ) bit)+VQ π bit)/80000 ≤
    avg (templates π (templateLaw (I := I) π h))
      (fun θ => DP (slice π (templateLaw π h) θ) bit y)+DQ π bit x+
    12*(event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
      ((Fintype.card I:ℝ)/ε)*predictionError π h x y+
      samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ε)+8*η) := by
  let ν := posteriorState π h x
  let Y : (I → H) → Finset (A×B) := Candidates ν ε
  choose W U hw hW hU hi hs using fun θ => witnesses (Y θ)
  let G : Q → (I → H) → Prop := fun q θ => ¬Failure (historyLaw π h q) ν ε (η^2) θ
  have hm (q : Q) (θ : I → H) (hg : G q θ) :
      1-3*η^2≤event (mix (historyLaw π h q) ν) (fun s => s∈U θ) := by
    apply witnesses_mass _ (W θ) (U θ) (sq_nonneg η) (hW θ) (hi θ)
    intro w hww
    by_contra hn
    exact hg ⟨w,hw θ hww,lt_of_not_ge hn⟩
  have ht := actual_transfer π h x hμ hκ (templateLaw (I := I) π h) U hU G hη hη' hm
  let good : (I → H) → P → Q → Prop := fun θ p q =>
    Consistent (bit p q) (x p) (y q) ∧ y q∈Y θ ∧ G q θ ∧ x p∈U θ
  have hc := aggregate_score π (templateLaw (I := I) π h) bit x y Y U good hs (by
    intro θ p q hpq
    exact ⟨hpq.2.2.2,hpq.2.1,hpq.1⟩)
  have hb : avg π (fun pq => event (templateLaw (I := I) π h pq.2) (fun θ => ¬good θ pq.1 pq.2))≤
      event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
      ((Fintype.card I:ℝ)/ε)*predictionError π h x y+
      samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ε)+8*η := by
    have hu : ∀pq : P×Q,event (templateLaw (I := I) π h pq.2) (fun θ => ¬good θ pq.1 pq.2)≤
        (if ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2) then 1 else 0)+
        event (templateLaw (I := I) π h pq.2) (fun θ => y pq.2∉Y θ)+
        event (templateLaw (I := I) π h pq.2) (fun θ => ¬G pq.2 θ)+
        event (templateLaw (I := I) π h pq.2) (fun θ => G pq.2 θ ∧ x pq.1∉U θ) := by
      intro pq
      rw [← avg_ite,← avg_ite,← avg_ite,← avg_ite,← avg_const (templateLaw (I := I) π h pq.2)
        (if ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2) then 1 else 0),← avg_add,← avg_add,← avg_add]
      apply avg_mono
      intro θ
      simpa only [good] using bad_good_indicator (Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))
        (y pq.2∈Y θ) (G pq.2 θ) (x pq.1∈U θ)
    have ha := avg_mono π hu
    rw [avg_add,avg_add,avg_add,avg_ite] at ha
    have hmiss := candidate_miss_mean (I := I) π h x y hε
    have hfail := failure_mean (I := I) π h x (ε := ε)
      (sq_pos_of_pos hη) (by nlinarith) hI hk
    have hf : avg π (fun pq => event (templateLaw (I := I) π h pq.2) (fun θ => ¬G pq.2 θ))=
        avg π (fun pq => event (templateLaw (I := I) π h pq.2)
          (Failure (historyLaw π h pq.2) ν ε (η^2))) := by
      apply avg_congr; intro pq
      apply event_congr; intro θ; simp [G]
    rw [hf] at ha
    change avg π (fun pq => event (templateLaw (I := I) π h pq.2) (fun θ => y pq.2∉Y θ))≤_ at hmiss
    linarith
  linarith
end
end PlanarUnitDistances.CommonTemplate

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Slots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LevelGeometry
open MeasureTheory Set Real FiniteStates PlaceLevels LevelStates BudgetPlaces
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [NumberField K]

lemma first_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (h : (state S z w u (v,s) x).1=(state S z w u (v,s) y).1) :
    av K v (z x-z y) ≤ exp (allowance v-s) := by
  cases v with
  | inl σ =>
    have hg : GridShift.gridLabel (exp (-s)) (σ (z x)) (u σ).1=
        GridShift.gridLabel (exp (-s)) (σ (z y)) (u σ).1 :=
      (label_eq_iff _ _ _).mp h
    have hb := GridShift.norm_le_of_same_grid (exp_pos (-s)) hg
    simpa only [av,WeightedAbsoluteValues.infiniteEntry_apply,map_sub,allowance,
      sub_eq_add_neg,map_add,map_neg,exp_add,exp_log (by norm_num : (0:ℝ)<2)] using hb
  | inr v =>
    have hb : WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2 (z x-z y) ≤ exp (-s) :=
      (label_eq_iff _ _ _).mp h
    simpa only [av,allowance,zero_sub] using hb

lemma second_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (h : (state S z w u (v,s) x).2=(state S z w u (v,s) y).2) :
    av K v (w x-w y) ≤ exp (allowance v+s) := by
  cases v with
  | inl σ =>
    have hg : GridShift.gridLabel (exp s) (σ (w x)) (u σ).2=
        GridShift.gridLabel (exp s) (σ (w y)) (u σ).2 :=
      (label_eq_iff _ _ _).mp h
    have hb := GridShift.norm_le_of_same_grid (exp_pos s) hg
    simpa only [av,WeightedAbsoluteValues.infiniteEntry_apply,map_sub,allowance,
      exp_add,exp_log (by norm_num : (0:ℝ)<2)] using hb
  | inr v =>
    have hb : WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2 (w x-w y) ≤ exp s :=
      (label_eq_iff _ _ _).mp h
    simpa only [av,allowance,zero_add] using hb

lemma first_log_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (hxy : z x≠z y) (h : (state S z w u (v,s) x).1=(state S z w u (v,s) y).1) :
    log (av K v (z x-z y)) ≤ allowance v-s := by
  have hb := log_le_log ((av K v).pos (sub_ne_zero.mpr hxy)) (first_bound S z w u v s x y h)
  simpa only [log_exp] using hb
lemma second_log_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (hxy : w x≠w y) (h : (state S z w u (v,s) x).2=(state S z w u (v,s) y).2) :
    log (av K v (w x-w y)) ≤ allowance v+s := by
  have hb := log_le_log ((av K v).pos (sub_ne_zero.mpr hxy)) (second_bound S z w u v s x y h)
  simpa only [log_exp] using hb

omit [NumberField K] in
lemma opposite_log {d d' : K} (v : AbsoluteValue K ℝ)
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') :
    log (v (d⁻¹-d'⁻¹)) = max (threshold v d) (threshold v d')-alpha v d d' := by
  rw [inv_difference_abs v hd hd']
  rw [log_div ((v.pos (sub_ne_zero.mpr hdd)).ne') (mul_ne_zero ((v.pos hd).ne') ((v.pos hd').ne')),
    log_mul ((v.pos hd).ne') ((v.pos hd').ne')]
  unfold alpha threshold
  have hm := min_add_max (-log (v d)) (-log (v d'))
  linarith

theorem positive_flanks (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y y' : V)
    (hu : (z x-z y)*(w x-w y)=1) (hu' : (z x-z y')*(w x-w y')=1)
    (hyy : z y≠z y') :
    let d := z x-z y
    let d' := z x-z y'
    let b := min (threshold (av K v) d) (threshold (av K v) d')
    let b' := max (threshold (av K v) d) (threshold (av K v) d')
    let T := alpha (av K v) d d'+allowance v
    ((s<threshold (av K v) d ∧ s<threshold (av K v) d' ∧
        (state S z w u (v,s) y).2=(state S z w u (v,s) y').2) → s∈Icc (b-T) b) ∧
    ((threshold (av K v) d ≤ s ∧ threshold (av K v) d' ≤ s ∧
        (state S z w u (v,s) y).1=(state S z w u (v,s) y').1) → s∈Icc b' (b'+T)) := by
  dsimp only
  have hd : z x-z y≠0 := left_ne_zero_of_mul_eq_one hu
  have hd' : z x-z y'≠0 := left_ne_zero_of_mul_eq_one hu'
  have hdd : z x-z y≠z x-z y' := by exact sub_right_injective.ne hyy
  have hw : w x-w y=(z x-z y)⁻¹ := eq_inv_of_mul_eq_one_right hu
  have hw' : w x-w y'=(z x-z y')⁻¹ := eq_inv_of_mul_eq_one_right hu'
  have he : w y-w y'=-((z x-z y)⁻¹-(z x-z y')⁻¹) := by rw [←hw,←hw']; ring
  have hz : z y-z y'=-((z x-z y)-(z x-z y')) := by ring
  have hwyy : w y≠w y' := by
    intro hh
    have hi : (z x-z y)⁻¹=(z x-z y')⁻¹ := by rw [←hw,←hw',hh]
    exact hdd (inv_injective hi)
  have hm : min (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')) ≤
      max (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')) := min_le_max
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    have hb := second_log_bound S z w u v s y y' hwyy h₃
    rw [he,AbsoluteValue.map_neg,opposite_log (av K v) hd hd' hdd] at hb
    refine ⟨by linarith,(le_min h₁.le h₂.le)⟩
  · rintro ⟨h₁,h₂,h₃⟩
    have hb := first_log_bound S z w u v s y y' hyy h₃
    rw [hz,AbsoluteValue.map_neg] at hb
    refine ⟨max_le h₁ h₂,?_⟩
    unfold alpha threshold at *
    linarith

end
end PlanarUnitDistances.LevelGeometry

namespace PlanarUnitDistances.PlaceScore
open MeasureTheory Set Real BudgetIntervals StrictCross
open scoped Classical
noncomputable section

lemma coefficient_bounds (ρ : ℝ) : 0 ≤ coefficient ρ ∧ coefficient ρ ≤ 2 := by
  unfold coefficient
  split_ifs <;> norm_num
lemma reward_bounds (ε p ρ : ℝ) (one : Bool) : 0≤reward ε p ρ one ∧ reward ε p ρ one ≤ 2 := by
  unfold reward
  split_ifs <;> try norm_num
  exact coefficient_bounds ρ
lemma ind_nonneg (A : Set ℝ) (s : ℝ) : 0 ≤ ind A s := by
  unfold ind Set.indicator; split_ifs <;> norm_num
lemma ind_Icc_integrable (a b : ℝ) : Integrable (ind (Icc a b)) := by
  exact (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc a b)).integrable_indicator measurableSet_Icc
lemma ind_Icc_integral (a b : ℝ) : ∫s,ind (Icc a b) s = max 0 (b-a) := by
  change (∫s,(Icc a b).indicator (fun _ => (1:ℝ)) s)=_
  rw [integral_indicator_const (1:ℝ) measurableSet_Icc]
  simp only [smul_eq_mul,mul_one,Real.volume_real_Icc,max_comm]
end
end PlanarUnitDistances.PlaceScore

namespace PlanarUnitDistances.LevelScores
open FiniteLaw StrictCross CrossStructure RareScore PlaceScore
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma positive_bounds (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) :
    0 ≤ positive ε p ρ good l base y z b c ∧ positive ε p ρ good l base y z b c ≤ 2 := by
  unfold positive
  split_ifs
  · exact ⟨mul_nonneg (coefficient_bounds ρ).1 (RareScore.ind_nonneg _),
      (mul_le_mul_of_nonneg_left (RareScore.ind_le_one _) (coefficient_bounds ρ).1).trans
        (by simpa using (coefficient_bounds ρ).2)⟩
  · constructor
    · exact mul_nonneg (by norm_num) (RareScore.ind_nonneg _)
    · nlinarith [RareScore.ind_le_one (exceptional (minority p) l base ∧
        b=minority p ∧ c=minority p ∧ nonshared (minority p) y z)]
  · norm_num
lemma score_bounds (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) :
    -1 ≤ score ε p ρ good l base y z b c ∧ score ε p ρ good l base y z b c ≤ 2 := by
  have h := positive_bounds ε p ρ good l base y z b c
  have hn := RareScore.ind_nonneg (b≠c)
  have hm := RareScore.ind_le_one (b≠c)
  unfold score
  constructor <;> linarith

lemma minority_reward {ε p ρ : ℝ} (hε : ε<1/2) (h : ¬common ε p) :
    reward ε p ρ (minority p)=2 := by
  unfold reward
  rw [ite_eq_right h]
  unfold minority
  by_cases hp : p<1/2
  · have hl : p<ε := by unfold common at h; push Not at h; by_contra! hh; have := h hh; linarith
    rw [show decide (p<1/2)=true from decide_eq_true hp]
    simp [hl]
  · have hr : 1-ε<p := by unfold common at h; push Not at h; apply h; linarith
    rw [show decide (p<1/2)=false from decide_eq_false hp]
    simp [hr]

lemma positive_le_rewards {ε p ρ : ℝ} (hε : ε<1/2) (good : Prop)
    (l base y z : A×B) (b c : Bool) :
    positive ε p ρ good l base y z b c ≤
      reward ε p ρ true*RareScore.ind (b=true ∧ c=true ∧ nonshared true y z)+
      reward ε p ρ false*RareScore.ind (b=false ∧ c=false ∧ nonshared false y z) := by
  have hn₀ := (reward_bounds ε p ρ false).1
  have hn₁ := (reward_bounds ε p ρ true).1
  by_cases hc : common ε p
  · unfold positive reward
    rw [ite_eq_left hc,ite_eq_left hc,ite_eq_left hc]
    cases b <;> cases c <;> simp only [RareScore.ind,nonshared,Bool.false_eq_true,
      Bool.true_eq_false,↓reduceIte,true_and,false_and,and_false]
    all_goals try split_ifs
    all_goals nlinarith [(coefficient_bounds ρ).1]
  · have hm := minority_reward (ρ:=ρ) hε hc
    unfold positive
    rw [ite_eq_right hc]
    by_cases hg : good
    · rw [ite_eq_left hg]
      unfold RareScore.ind
      by_cases hp : exceptional (minority p) l base ∧
          b=minority p ∧ c=minority p ∧ nonshared (minority p) y z
      · rw [ite_eq_left hp]
        obtain ⟨_,hb,hc',hns⟩ := hp
        rw [hb,hc']
        cases hr : minority p
        · rw [hr] at hm hns
          simp [hm,hns]
        · rw [hr] at hm hns
          simp [hm,hns]
      · rw [ite_eq_right hp]
        split_ifs <;> nlinarith
    · rw [ite_eq_right hg]
      exact add_nonneg (mul_nonneg hn₁ (RareScore.ind_nonneg _))
        (mul_nonneg hn₀ (RareScore.ind_nonneg _))

lemma rare_score {ε p ρ : ℝ} (good : Prop) (l base y z : A×B) (b c : Bool)
    (hc : ¬common ε p) (hg : good) :
    score ε p ρ good l base y z b c=RareScore.slot (minority p) l base y z b c := by
  simp [score,positive,RareScore.slot,hc,hg]

end
end PlanarUnitDistances.LevelScores

namespace PlanarUnitDistances.LevelSlotGeometry
open MeasureTheory Set Real FiniteStates PlaceLevels LevelStates LevelGeometry BudgetPlaces LevelScores
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [NumberField K]

theorem positive_le_cap (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s ε : ℝ)
    (g ρ : ℝ → ℝ) (hε : ε<1/2) (good : Prop) (l : (V → Bool)×(V → Bool)) (x y y' : V)
    (hu : (z x-z y)*(w x-w y)=1) (hu' : (z x-z y')*(w x-w y')=1)
    (hyy : z y≠z y') :
    positive ε (g s) (ρ s) good l (state S z w u (v,s) x)
      (state S z w u (v,s) y) (state S z w u (v,s) y')
      (decide (s<threshold (av K v) (z x-z y))) (decide (s<threshold (av K v) (z x-z y'))) ≤
    PlaceScore.cap ε g ρ
      (min (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')))
      (max (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')))
      (alpha (av K v) (z x-z y) (z x-z y')+allowance v) s := by
  have hp := positive_le_rewards hε good l (state S z w u (v,s) x)
    (state S z w u (v,s) y) (state S z w u (v,s) y')
    (decide (s<threshold (av K v) (z x-z y))) (decide (s<threshold (av K v) (z x-z y')))
    (p:=g s) (ρ:=ρ s)
  have hf := positive_flanks S z w u v s x y y' hu hu' hyy
  dsimp only at hf
  refine hp.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ (PlaceScore.reward_bounds ε (g s) (ρ s) true).1)
    (mul_le_mul_of_nonneg_left ?_ (PlaceScore.reward_bounds ε (g s) (ρ s) false).1))
  · unfold RareScore.ind
    split_ifs with h
    · have he₁ : s<threshold (av K v) (z x-z y) := of_decide_eq_true h.1
      have he₂ : s<threshold (av K v) (z x-z y') := of_decide_eq_true h.2.1
      have hi := hf.1 ⟨he₁,he₂,h.2.2⟩
      have hi' := lt_min he₁ he₂
      change 1 ≤ PlaceScore.ind _ s
      rw [PlaceScore.ind,Set.indicator_of_mem (show s∈Icc _ _ ∩ Iio _ from ⟨hi,hi'⟩)]
    · exact PlaceScore.ind_nonneg _ _
  · unfold RareScore.ind
    split_ifs with h
    · have he₁ : threshold (av K v) (z x-z y) ≤ s := le_of_not_gt (of_decide_eq_false h.1)
      have he₂ : threshold (av K v) (z x-z y') ≤ s := le_of_not_gt (of_decide_eq_false h.2.1)
      have hi := hf.2 ⟨he₁,he₂,h.2.2⟩
      simp only [PlaceScore.ind,Set.indicator_of_mem hi,le_refl]
    · exact PlaceScore.ind_nonneg _ _
end
end PlanarUnitDistances.LevelSlotGeometry

namespace PlanarUnitDistances.RareRows
open FiniteLaw FiniteStarCoupling RareScore LevelScores
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

lemma common_slot {X : Type*} {ε p ρ : ℝ} (hc : PlaceScore.common ε p)
    (good : Prop) (l base : A×B) (s : X → A×B) (b : X → Bool) (i j : X) :
    LevelScores.score ε p ρ good l base (s i) (s j) (b i) (b j)=StarScore.slot ρ b s i j := by
  simp only [LevelScores.score,LevelScores.positive,hc,↓reduceIte,StarScore.slot]
  cases b i <;> cases b j <;> simp [nonshared,ind,mul_ite]

lemma common_P {ε f : ℝ} (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) (hc : PlaceScore.common ε f) :
    scoreP ε f π bit x y good l=DP π bit y := by
  unfold scoreP DP StarScore.score StarScore.frequency
  apply avg_congr
  intro p
  apply avg_congr
  intro qq
  exact common_slot hc good l (x p) y (bit p) qq.1 qq.2
lemma common_Q {ε f : ℝ} (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) (hc : PlaceScore.common ε f) :
    scoreQ ε f π bit x y good l=DQ π bit x := by
  unfold scoreQ DQ StarScore.score StarScore.frequency
  apply avg_congr
  intro q
  apply avg_congr
  intro pp
  exact common_slot hc good l (y q) x (fun p => bit p q) pp.1 pp.2

lemma consistency_symm (b : Bool) (x y : A×B) : CrossStructure.Consistent b x y ↔ CrossStructure.Consistent b y x := by
  cases b <;> simp [CrossStructure.Consistent,eq_comm]

theorem rare_P {ε f : ℝ} (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) (hc : ¬PlaceScore.common ε f) (hg : good) :
    let r := minority f
    2*event (left π) (fun p => exceptional r l (x p))-
      2*event (right π) (fun q => exceptional r l (y q))-
      4*event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2))-
      6*event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))≤
      scoreP ε f π bit x y good l := by
  dsimp only
  let r := minority f
  have h := avg_mono (left π) (fun p => star_lower (row π p) r l (x p) y (bit p))
  simp only [avg_sub,avg_smul,row_event] at h
  have hleft : avg (left π) (fun p => ind (exceptional r l (x p)))=event (left π) (fun p => exceptional r l (x p)) := rfl
  rw [hleft] at h
  have hright : event π (fun pq => exceptional r l (y pq.2))=event (right π) (fun q => exceptional r l (y q)) := by
    simp only [right,event,push_avg]
  rw [hright] at h
  have hs : scoreP ε f π bit x y good l=avg (left π) (fun p => avg (pair (row π p) (row π p))
      (fun qq => slot r l (x p) (y qq.1) (y qq.2) (bit p qq.1) (bit p qq.2))) := by
    unfold scoreP
    apply avg_congr
    intro p
    apply avg_congr
    intro qq
    exact rare_score good l (x p) (y qq.1) (y qq.2) (bit p qq.1) (bit p qq.2) hc hg
  rw [hs]
  linarith

theorem rare_Q {ε f : ℝ} (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) (hc : ¬PlaceScore.common ε f) (hg : good) :
    let r := minority f
    2*event (right π) (fun q => exceptional r l (y q))-
      2*event (left π) (fun p => exceptional r l (x p))-
      4*event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2))-
      6*event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))≤
      scoreQ ε f π bit x y good l := by
  dsimp only
  let r := minority f
  have h := avg_mono (right π) (fun q => star_lower (col π q) r l (y q) x (fun p => bit p q))
  simp only [avg_sub,avg_smul,col_event] at h
  have hright : avg (right π) (fun q => ind (exceptional r l (y q)))=event (right π) (fun q => exceptional r l (y q)) := rfl
  rw [hright] at h
  have hleft : event π (fun pq => exceptional r l (x pq.1))=event (left π) (fun p => exceptional r l (x p)) := by
    simp only [left,event,push_avg]
  rw [hleft] at h
  have hj : event π (fun pq => exceptional r l (y pq.2) ∧ exceptional r l (x pq.1))=
      event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2)) := by simp only [and_comm]
  rw [hj] at h
  have hi : event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (y pq.2) (x pq.1))=
      event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2)) := by
    congr 1
    funext pq
    exact propext (not_congr (consistency_symm (bit pq.1 pq.2) (y pq.2) (x pq.1)))
  rw [hi] at h
  have hs : scoreQ ε f π bit x y good l=avg (right π) (fun q => avg (pair (col π q) (col π q))
      (fun pp => slot r l (y q) (x pp.1) (x pp.2) (bit pp.1 q) (bit pp.2 q))) := by
    unfold scoreQ
    apply avg_congr
    intro q
    apply avg_congr
    intro pp
    exact rare_score good l (y q) (x pp.1) (x pp.2) (bit pp.1 q) (bit pp.2 q) hc hg
  rw [hs]
  linarith

lemma scoreP_lower (ε f : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) : -1≤ scoreP ε f π bit x y good l := by
  apply const_le_avg
  intro p
  apply const_le_avg
  intro qq
  exact (LevelScores.score_bounds _ _ _ _ _ _ _ _ _ _).1
lemma scoreQ_lower (ε f : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) : -1≤ scoreQ ε f π bit x y good l := by
  apply const_le_avg
  intro q
  apply const_le_avg
  intro pp
  exact (LevelScores.score_bounds _ _ _ _ _ _ _ _ _ _).1
end
end PlanarUnitDistances.RareRows

namespace PlanarUnitDistances.TemplateCoupling
open FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]
lemma slice_avg_original (π : Law (P×Q)) (a : Q → Law Θ) (f : P×Q → ℝ) :
    avg (templates π a) (fun θ => avg (slice π a θ) f)=avg π f := by
  rw [slice_avg]
  simp only [avg_const]
lemma slice_event_original (π : Law (P×Q)) (a : Q → Law Θ) (f : P×Q → Prop) :
    avg (templates π a) (fun θ => event (slice π a θ) f)=event π f :=
  slice_avg_original π a _
lemma slice_left_event (π : Law (P×Q)) (a : Q → Law Θ) (f : P → Prop) :
    avg (templates π a) (fun θ => event (left (slice π a θ)) f)=event (left π) f := by
  simp only [left,event,push_avg]
  exact slice_avg_original π a _
lemma slice_right_event (π : Law (P×Q)) (a : Q → Law Θ) (f : Q → Prop) :
    avg (templates π a) (fun θ => event (right (slice π a θ)) f)=event (right π) f := by
  simp only [right,event,push_avg]
  exact slice_avg_original π a _
end
end PlanarUnitDistances.TemplateCoupling

namespace PlanarUnitDistances.RareRows
open FiniteLaw FiniteStarCoupling TemplateCoupling LevelScores RareScore
open scoped Classical
noncomputable section
variable {P Q Θ A B : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

theorem rare_T {ε f : ℝ} (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (good : Prop) (l : A×B)
    (hc : ¬PlaceScore.common ε f) (hg : good) :
    let r := minority f
    2*event (left π) (fun p => exceptional r l (x p))-
      2*event (right π) (fun q => exceptional r l (y q))-
      4*event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2))-
      6*event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))≤
      scoreT ε f π a bit x y good l := by
  have h := avg_mono (templates π a) (fun θ => rare_P (slice π a θ) bit x y good l hc hg)
  simpa only [avg_sub,avg_smul,slice_left_event,slice_right_event,slice_event_original,scoreT] using h

lemma common_T {ε f : ℝ} (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (good : Prop) (l : A×B) (hc : PlaceScore.common ε f) :
    scoreT ε f π a bit x y good l=avg (templates π a) (fun θ => DP (slice π a θ) bit y) := by
  unfold scoreT
  apply avg_congr
  intro θ
  exact common_P (slice π a θ) bit x y good l hc

lemma scoreT_lower (ε f : ℝ) (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (good : Prop) (l : A×B) :
    -1≤ scoreT ε f π a bit x y good l :=
  const_le_avg _ (fun θ => scoreP_lower ε f (slice π a θ) bit x y good l)
end
end PlanarUnitDistances.RareRows

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_RareEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.CommonRareScore
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows LevelScores RareScore
open scoped Classical
noncomputable section
variable {P Q H A B I L : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype I] [Fintype L]

theorem balanced (π : Law (P×Q)) (h : P → H) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    {ζ η : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2)
    (ε : ℝ) (good : Prop) (l : A×B) :
    let f := event π (fun pq => bit pq.1 pq.2=true)
    let a := templateLaw (I := I) π h
    let m := event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))
    let J := event π (fun pq => exceptional (minority f) l (x pq.1) ∧ exceptional (minority f) l (y pq.2))
    (if PlaceScore.common ε f then (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/80000 else 0)≤
      scoreT ε f π a bit x y good l+scoreQ ε f π bit x y good l+
      (if PlaceScore.common ε f then
        12*(m+((Fintype.card I:ℝ)/ζ)*predictionError π h x y+
          samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η)
       else if good then 8*J+12*m else 2) := by
  dsimp only
  by_cases hc : PlaceScore.common ε (event π (fun pq => bit pq.1 pq.2=true))
  · rw [ite_eq_left hc,ite_eq_left hc,common_T π _ bit x y good l hc,common_Q π bit x y good l hc]
    exact common_score π h bit x y hμ hκ hζ hk hI hη hη'
  · rw [ite_eq_right hc,ite_eq_right hc]
    by_cases hg : good
    · rw [ite_eq_left hg]
      have hp := rare_T π (templateLaw (I := I) π h) bit x y good l hc hg
      have hq := rare_Q π bit x y good l hc hg
      dsimp only at hp hq
      linarith
    · rw [ite_eq_right hg]
      linarith [scoreT_lower ε (event π (fun pq => bit pq.1 pq.2=true)) π
        (templateLaw (I := I) π h) bit x y good l,
        scoreQ_lower ε (event π (fun pq => bit pq.1 pq.2=true)) π bit x y good l]

theorem balanced_average (σ : Law L) (π : Law (P×Q)) (h : P → H)
    (bit : L → P → Q → Bool) (x : L → P → A×B) (y : L → Q → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    {ζ η : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2)
    (ε : ℝ) (good : L → Prop) (l : L → A×B) :
    let f := fun s => event π (fun pq => bit s pq.1 pq.2=true)
    let a := templateLaw (I := I) π h
    let m := fun s => event π (fun pq => ¬CrossStructure.Consistent (bit s pq.1 pq.2) (x s pq.1) (y s pq.2))
    let J := fun s => event π (fun pq => exceptional (minority (f s)) (l s) (x s pq.1) ∧
      exceptional (minority (f s)) (l s) (y s pq.2))
    avg σ (fun s => if PlaceScore.common ε (f s) then
      (avg (templates π a) (fun θ => VP (slice π a θ) (bit s))+VQ π (bit s))/80000 else 0)≤
      avg σ (fun s => scoreT ε (f s) π a (bit s) (x s) (y s) (good s) (l s))+
      avg σ (fun s => scoreQ ε (f s) π (bit s) (x s) (y s) (good s) (l s))+
      avg σ (fun s => if PlaceScore.common ε (f s) then
        12*(m s+((Fintype.card I:ℝ)/ζ)*predictionError π h (x s) (y s)+
          samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η)
       else if good s then 8*J s+12*m s else 2) := by
  have hh := avg_mono σ (fun s => balanced π h (bit s) (x s) (y s) hμ hκ hζ hk hI hη hη' ε (good s) (l s))
  simpa only [avg_add] using hh
end
end PlanarUnitDistances.CommonRareScore

namespace PlanarUnitDistances.LawRare
open Finset FiniteLaw LawExpansion FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma event_domination (μ ν : Law P) {γ : ℝ} (h : ∀p,γ*μ.val p≤ν.val p) (F : P → Prop) :
    γ*event μ F≤event ν F := by
  unfold event avg
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  by_cases hp : F p <;> simp [hp,h p]

theorem small_rect (π : Law (P×Q)) (U : Law P) (W : Law Q) {γ η ξ a : ℝ}
    (hγ : 0<γ) (hη : 0≤η) (hξ : 0≤ξ)
    (hl : ∀p,γ*U.val p≤(left π).val p) (hr : ∀q,γ*W.val q≤(right π).val q)
    (hexp : ∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ))
    (F : Finset P) (G : Finset Q) (hF : event (left π) (fun p => p∈F)≤a) :
    event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      (((a/γ)^η+ξ)/γ)*Real.sqrt (event (left π) (fun p => p∈F)*event (right π) (fun q => q∈G)) := by
  let u := event U (fun p => p∈F)
  let v := event W (fun q => q∈G)
  let h := event (left π) (fun p => p∈F)
  let k := event (right π) (fun q => q∈G)
  have hu : 0≤u := event_nonneg _ _
  have hv : 0≤v := event_nonneg _ _
  have hh : 0≤h := event_nonneg _ _
  have hk : 0≤k := event_nonneg _ _
  have hul : γ*u≤h := event_domination U (left π) hl _
  have hvr : γ*v≤k := event_domination W (right π) hr _
  have hp := mul_le_mul hul hvr (mul_nonneg hγ.le hv) hh
  have hs : γ*Real.sqrt (u*v)≤Real.sqrt (h*k) := by
    apply (sq_le_sq₀ (mul_nonneg hγ.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hu hv),Real.sq_sqrt (mul_nonneg hh hk)]
    nlinarith
  have huv : u*v≤a/γ := by
    have ha : u≤a/γ := (le_div_iff₀ hγ).mpr (by linarith)
    exact (mul_le_of_le_one_right hu (event_le_one W _)).trans ha
  have he := Real.rpow_le_rpow (mul_nonneg hu hv) huv hη
  have han : 0≤(a/γ)^η+ξ := add_nonneg (Real.rpow_nonneg (div_nonneg (hh.trans hF) hγ.le) _) hξ
  have hs' : Real.sqrt (u*v)≤Real.sqrt (h*k)/γ := (le_div_iff₀ hγ).mpr (by nlinarith)
  calc
    _ ≤ Real.sqrt (u*v)*((u*v)^η+ξ) := hexp F G
    _ ≤ Real.sqrt (u*v)*((a/γ)^η+ξ) := mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ ≤ (Real.sqrt (h*k)/γ)*((a/γ)^η+ξ) := mul_le_mul_of_nonneg_right hs' han
    _ = _ := by ring

end
end PlanarUnitDistances.LawRare

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]
lemma event_markov (μ : Law X) (f : X → ℝ) (hf : ∀x,0≤f x) {ε : ℝ} (hε : 0<ε) :
    event μ (fun x => ε<f x)≤avg μ f/ε := by
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]; unfold event; rw [←avg_smul]
  apply avg_mono
  intro x
  split_ifs with h
  · simpa using h.le
  · simpa using hf x
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling StrictCross CrossSampling CrossStructure FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P Q H A B : Type*} [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype B]
omit [Fintype H] in

theorem marginal_score (π : Law (P×Q)) (h : P → H) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) {ε : ℝ} (hε : 0<ε) :
    VP π bit/80000≤DP π bit y+avg (left π) (fun p => tau (posteriorState π h x (h p)))+
      20*(event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
        predictionError π h x y/ε+ε) := by
  let good : P → Q → Prop := fun p q => Consistent (bit p q) (x p) (y q) ∧
    1-ε≤crossMass (posteriorState π h x (h p)) (y q)
  have hs := avg_mono (left π) (fun p => second_slice (row π p) (bit p) y
    (posteriorState π h x (h p)) (x p) (good p) hε.le
    (fun _ hg => hg.1) (fun _ hg => hg.2))
  simp only [avg_sub,div_eq_mul_inv,avg_add,avg_smul,avg_const] at hs
  have hv : avg (left π) (fun p => StarScore.variation (row π p) (bit p)*80000⁻¹)=VP π bit*80000⁻¹ := by
    simp [VP,avg,Finset.sum_mul,mul_assoc]
  rw [hv,row_event] at hs
  have hb : event π (fun pq => ¬good pq.1 pq.2)≤
      event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
      predictionError π h x y/ε := by
    refine (event_mono π ?_).trans ((event_union_le π _ _).trans (add_le_add_right
      (event_markov π (fun pq => 1-crossMass (posteriorState π h x (h pq.1)) (y pq.2))
        (fun pq => sub_nonneg.mpr (event_le_one _ _)) hε) _))
    intro pq hg
    by_cases hc : Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2)
    · right
      have hn : ¬1-ε≤crossMass (posteriorState π h x (h pq.1)) (y pq.2) := fun hp => hg ⟨hc,hp⟩
      linarith
    · exact Or.inl hc
  change _≤DP π bit y+_ at hs
  linarith
end
end PlanarUnitDistances.CommonTemplate

namespace PlanarUnitDistances.LevelBookkeeping
open Finset FiniteLaw FiniteStarCoupling RareLabels RareMoments RareScore
open scoped Classical
noncomputable section
variable {D P Q A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype A]

omit [Fintype D] [Fintype A] in
lemma minority_nonneg (π : Law (P×Q)) (b : P → Q → Bool) : 0 ≤ minorityMass π b :=
  le_min (event_nonneg _ _) (sub_nonneg.mpr (event_le_one _ _))
omit [Fintype D] [Fintype A] in
lemma minority_le_half (π : Law (P×Q)) (b : P → Q → Bool) : minorityMass π b ≤ 1/2 := by
  unfold minorityMass
  have := min_le_left (event π (fun pq => b pq.1 pq.2=true)) (1-event π (fun pq => b pq.1 pq.2=true))
  have := min_le_right (event π (fun pq => b pq.1 pq.2=true)) (1-event π (fun pq => b pq.1 pq.2=true))
  linarith
end
end PlanarUnitDistances.LevelBookkeeping

namespace PlanarUnitDistances.FiniteLaw
open scoped Classical
noncomputable section
variable {D : Type*} [Fintype D]
lemma avg_neg (σ : Law D) (f : D → ℝ) : avg σ (fun s => -f s) = -avg σ f := by
  simp only [avg,mul_neg,Finset.sum_neg_distrib]
lemma cut_add (σ : Law D) (c : D → Prop) (f g : D → ℝ) :
    cut σ c (fun s => f s+g s)=cut σ c f+cut σ c g := by
  unfold cut; rw [←avg_add]; apply avg_congr; intro s; split_ifs <;> simp
lemma cut_smul (σ : Law D) (c : D → Prop) (a : ℝ) (f : D → ℝ) :
    cut σ c (fun s => a*f s)=a*cut σ c f := by
  unfold cut; rw [←avg_smul]; apply avg_congr; intro s; split_ifs <;> simp
lemma cut_nonneg (σ : Law D) (c : D → Prop) (f : D → ℝ) (hf : ∀s,0 ≤ f s) : 0 ≤ cut σ c f :=
  avg_nonneg σ (fun s => by split_ifs <;> first | exact hf s | exact le_rfl)
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GlobalScores
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows LevelScores RareScore RareMoments
open scoped Classical
noncomputable section
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype I]

theorem common_lower (σ : Law D) (π : Law (P×Q)) (h : P → H)
    (b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    {ζ η : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2)
    (ε : ℝ) (g : D → Prop) (l : D → A×A) :
    let c := common ε π b
    let R := fun s => ¬c s ∧ g s
    let a := templateLaw (I := I) π h
    let CT := cut σ c (fun s => avg (templates π a) (fun θ => VP (slice π a θ) (b s)))
    let CQ := cut σ c (fun s => VQ π (b s))
    (CT+CQ)/80000 ≤
      avg σ (fun s => scoreT ε (frequency π (b s)) π a (b s) (x s) (y s) (g s) (l s))+
      avg σ (fun s => scoreQ ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s))+
      12*avg σ (fun s => RareLabels.error π (b s) (x s) (y s))+
      (12*(Fintype.card I:ℝ)/ζ)*cut σ c (fun s => predictionError π h (x s) (y s))+
      (12*(samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η))*event σ c+
      8*cut σ R (fun s => RareMoments.joint π (b s) (x s) (y s) (l s))+2*event σ (bad c g) := by
  dsimp only
  let c := common ε π b
  let R := fun s => ¬c s ∧ g s
  let m := fun s => RareLabels.error π (b s) (x s) (y s)
  let J := fun s => RareMoments.joint π (b s) (x s) (y s) (l s)
  let pe := fun s => predictionError π h (x s) (y s)
  let e := samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η
  have he : avg σ (fun s => if c s then 12*(m s+((Fintype.card I:ℝ)/ζ)*pe s+e)
      else if g s then 8*J s+12*m s else 2) ≤
      12*avg σ m+(12*(Fintype.card I:ℝ)/ζ)*cut σ c pe+12*e*event σ c+
      8*cut σ R J+2*event σ (bad c g) := by
    have hh := avg_mono σ (f := fun s => if c s then 12*(m s+((Fintype.card I:ℝ)/ζ)*pe s+e)
      else if g s then 8*J s+12*m s else 2)
      (g := fun s => 12*m s+(12*(Fintype.card I:ℝ)/ζ)*(if c s then pe s else 0)+
        12*e*(if c s then 1 else 0)+8*(if R s then J s else 0)+2*(if bad c g s then 1 else 0)) (by
        intro s
        have hm : 0 ≤ m s := event_nonneg _ _
        by_cases hc : c s <;> by_cases hg : g s <;>
          simp only [hc,hg,R,bad,not_true_eq_false,not_false_eq_true,and_self,and_false,and_true,ite_true,ite_false,div_eq_mul_inv] <;> nlinarith)
    simp only [avg_add,avg_smul] at hh
    unfold cut event
    convert hh using 1; congr!
  have hbal := CommonRareScore.balanced_average (I := I) σ π h b x y hμ hκ hζ hk hI hη hη' ε g l
  have hl : avg σ (fun s => if c s then
      (avg (templates π (templateLaw (I := I) π h)) (fun θ => VP (slice π (templateLaw (I := I) π h) θ) (b s))+VQ π (b s))/80000 else 0)=
      (cut σ c (fun s => avg (templates π (templateLaw (I := I) π h)) (fun θ => VP (slice π (templateLaw (I := I) π h) θ) (b s)))+
      cut σ c (fun s => VQ π (b s)))/80000 := by
    change cut σ c (fun s => _/80000)=_
    simp_rw [div_eq_mul_inv,mul_comm _ (80000:ℝ)⁻¹]
    rw [cut_smul,cut_add]
  dsimp [c,common] at hl
  change _ ≤ _ at hbal
  change _ ≤ _ at he
  erw [hl] at hbal
  dsimp [c,R,m,J,pe,e,frequency,common,RareLabels.error,RareMoments.joint] at he ⊢
  simp only [add_assoc] at he hbal ⊢
  linarith

omit [Fintype A] in
lemma center_score_lower (π : Law (P×Q)) (b : P → Q → Bool) (x : P → A×A) :
    -VQ π b ≤ DQ π b x := by
  have h := avg_mono (right π) (fun q => StarScore.score_lower (col π q) (fun p => b p q) x)
  simpa only [avg_neg,VQ,DQ] using h

omit [Fintype A] in

theorem center_lower (σ : Law D) (π : Law (P×Q)) (b : D → P → Q → Bool)
    (x : D → P → A×A) (y : D → Q → A×A) (ε : ℝ) (g : D → Prop) (l : D → A×A) :
    let c := common ε π b
    let R := fun s => ¬c s ∧ g s
    2*cut σ R (fun s => hq π (b s) (y s) (l s))-2*cut σ R (fun s => hp π (b s) (x s) (l s))-
      4*cut σ R (fun s => RareMoments.joint π (b s) (x s) (y s) (l s))-
      6*avg σ (fun s => RareLabels.error π (b s) (x s) (y s))-
      cut σ c (fun s => VQ π (b s))-event σ (bad c g) ≤
      avg σ (fun s => scoreQ ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)) := by
  dsimp only
  let c := common ε π b
  let R := fun s => ¬c s ∧ g s
  have hh := avg_mono σ (f := fun s => 2*(if R s then hq π (b s) (y s) (l s) else 0)-
    2*(if R s then hp π (b s) (x s) (l s) else 0)-4*(if R s then RareMoments.joint π (b s) (x s) (y s) (l s) else 0)-
    6*RareLabels.error π (b s) (x s) (y s)-(if c s then VQ π (b s) else 0)-(if bad c g s then 1 else 0))
    (g := fun s => scoreQ ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)) (by
      intro s
      have hm := event_nonneg π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))
      by_cases hc : c s
      · have hs := center_score_lower π (b s) (x s)
        rw [common_Q π (b s) (x s) (y s) (g s) (l s) (show PlaceScore.common ε (frequency π (b s)) from hc)]
        simp only [R,bad,hc,not_true_eq_false,false_and,ite_false,ite_true]
        dsimp [RareLabels.error] at *; linarith
      · by_cases hg : g s
        · have hs := rare_Q π (b s) (x s) (y s) (g s) (l s) hc hg
          simpa only [R,bad,hc,hg,not_false_eq_true,not_true_eq_false,and_self,and_false,ite_true,ite_false,sub_zero,hq,hp,RareMoments.joint,RareLabels.error,frequency] using hs
        · have hs := scoreQ_lower ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)
          simp only [R,bad,hc,hg,not_false_eq_true,true_and,ite_true,ite_false] at hs ⊢
          dsimp [RareLabels.error] at *; linarith)
  simpa only [avg_sub,avg_smul,cut,event] using hh
end
end PlanarUnitDistances.GlobalScores

namespace PlanarUnitDistances.GlobalMarginal
open FiniteLaw FiniteStarCoupling CommonTemplate RareRows LevelScores RareScore RareMoments GlobalScores
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A]

omit [Fintype H] in

theorem point_lower (σ : Law D) (π : Law (P×Q)) (h : P → H)
    (b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A)
    {δ : ℝ} (hδ : 0<δ) (ε : ℝ) (g : D → Prop) (l : D → A×A) :
    let c := common ε π b
    let R := fun s => ¬c s ∧ g s
    cut σ c (fun s => VP π (b s))/80000 ≤
      avg σ (fun s => scoreP ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s))+
      cut σ c (fun s => avg (left π) (fun p => FiniteMarginalScore.tau (posteriorState π h (x s) (h p))))+
      2*cut σ R (fun s => hq π (b s) (y s) (l s))+
      4*cut σ R (fun s => RareMoments.joint π (b s) (x s) (y s) (l s))+
      26*avg σ (fun s => RareLabels.error π (b s) (x s) (y s))+
      (20/δ)*cut σ c (fun s => predictionError π h (x s) (y s))+
      (20*δ)*event σ c+event σ (GlobalScores.bad c g) := by
  dsimp only
  let c := common ε π b
  let R := fun s => ¬c s ∧ g s
  have hh := avg_mono σ (f := fun s => if c s then VP π (b s)/80000 else 0)
    (g := fun s => scoreP ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)+
      (if c s then avg (left π) (fun p => FiniteMarginalScore.tau (posteriorState π h (x s) (h p))) else 0)+
      2*(if R s then hq π (b s) (y s) (l s) else 0)+
      4*(if R s then RareMoments.joint π (b s) (x s) (y s) (l s) else 0)+
      26*RareLabels.error π (b s) (x s) (y s)+
      (20/δ)*(if c s then predictionError π h (x s) (y s) else 0)+
      (20*δ)*(if c s then 1 else 0)+(if GlobalScores.bad c g s then 1 else 0)) (by
      intro s
      have hm := event_nonneg π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))
      by_cases hc : c s
      · have hs := marginal_score π h (b s) (x s) (y s) hδ
        rw [common_P π (b s) (x s) (y s) (g s) (l s) (show PlaceScore.common ε (frequency π (b s)) from hc)]
        simp only [R,GlobalScores.bad,hc,not_true_eq_false,false_and,ite_false,ite_true]
        dsimp only [RareLabels.error]
        simp only [div_eq_mul_inv] at hs ⊢
        nlinarith
      · by_cases hg : g s
        · have hs := rare_P π (b s) (x s) (y s) (g s) (l s) hc hg
          have hpt : 0 ≤ hp π (b s) (x s) (l s) := event_nonneg _ _
          simp only [R,GlobalScores.bad,hc,hg,not_false_eq_true,not_true_eq_false,and_self,and_false,ite_true,ite_false] at hs ⊢
          dsimp only [RareLabels.error,RareMoments.joint,hq,hp,frequency] at hs hpt ⊢
          linarith
        · have hs := scoreP_lower ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)
          simp only [R,GlobalScores.bad,hc,hg,not_false_eq_true,true_and,ite_true,ite_false] at hs ⊢
          dsimp only [RareLabels.error] at *
          linarith)
  have hl : avg σ (fun s => if c s then VP π (b s)/80000 else 0)=
      cut σ c (fun s => VP π (b s))/80000 := by
    change cut σ c (fun s => VP π (b s)/80000)=_
    simp_rw [div_eq_mul_inv,mul_comm _ (80000:ℝ)⁻¹]
    rw [cut_smul]
  rw [hl] at hh
  simp only [avg_add,avg_smul] at hh
  dsimp only [c,R] at hh
  simp only [cut,event] at hh ⊢
  convert hh using 1

omit [Fintype A] in

theorem scale_lower (σ : Law D) (π : Law (P×Q))
    (b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A)
    (ε C : ℝ) (g : D → Prop) (l : D → A×A)
    (hstable : ∀s,common ε π b s → RareLabels.minorityMass π (b s) ≤ C*(VP π (b s)+VQ π (b s)))
    (hrare : ∀s,¬common ε π b s → g s → RareLabels.minorityMass π (b s) ≤
      hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)+RareLabels.error π (b s) (x s) (y s)) :
    let c := common ε π b
    let R := fun s => ¬c s ∧ g s
    avg σ (fun s => RareLabels.minorityMass π (b s)) ≤
      C*(cut σ c (fun s => VP π (b s))+cut σ c (fun s => VQ π (b s)))+
      cut σ R (fun s => hp π (b s) (x s) (l s))+cut σ R (fun s => hq π (b s) (y s) (l s))+
      avg σ (fun s => RareLabels.error π (b s) (x s) (y s))+event σ (GlobalScores.bad c g)/2 := by
  dsimp only
  let c := common ε π b
  let R := fun s => ¬c s ∧ g s
  have hh := avg_mono σ (f := fun s => RareLabels.minorityMass π (b s))
    (g := fun s => C*((if c s then VP π (b s) else 0)+(if c s then VQ π (b s) else 0))+
      (if R s then hp π (b s) (x s) (l s) else 0)+(if R s then hq π (b s) (y s) (l s) else 0)+
      RareLabels.error π (b s) (x s) (y s)+(1/2)*(if GlobalScores.bad c g s then 1 else 0)) (by
      intro s
      have hm : 0 ≤ RareLabels.error π (b s) (x s) (y s) := event_nonneg _ _
      by_cases hc : c s <;> by_cases hg : g s <;>
        simp only [R,GlobalScores.bad,hc,hg,not_true_eq_false,not_false_eq_true,and_self,and_false,and_true,ite_true,ite_false]
      · linarith [hstable s hc]
      · linarith [hstable s hc]
      · simpa using hrare s hc hg
      · linarith [LevelBookkeeping.minority_le_half π (b s)])
  simp only [avg_add,avg_smul] at hh
  dsimp only [c,R] at hh
  simp only [cut,event,div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,mul_one] at hh ⊢
  convert hh using 1
end
end PlanarUnitDistances.GlobalMarginal

namespace PlanarUnitDistances.ScoreBook
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows RareMoments GlobalScores
open scoped Classical
noncomputable section

namespace Book
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype I]

omit [Fintype A] [Fintype H] [Fintype I] in
lemma nonneg (B : Book D P Q H A) : 0 ≤ B.S ∧ 0 ≤ B.M ∧ 0 ≤ B.HP ∧ 0 ≤ B.HQ ∧
    0 ≤ B.CP ∧ 0 ≤ B.CQ ∧ 0 ≤ B.J ∧ 0 ≤ B.WC ∧ 0 ≤ B.WB := by
  refine ⟨avg_nonneg _ (fun _ => LevelBookkeeping.minority_nonneg _ _),avg_nonneg _ (fun _ => event_nonneg _ _),
    cut_nonneg _ _ _ (fun _ => event_nonneg _ _),cut_nonneg _ _ _ (fun _ => event_nonneg _ _),
    cut_nonneg _ _ _ (fun _ => avg_nonneg _ (fun _ => StarScore.variation_nonneg _ _)),
    cut_nonneg _ _ _ (fun _ => avg_nonneg _ (fun _ => StarScore.variation_nonneg _ _)),
    cut_nonneg _ _ _ (fun _ => event_nonneg _ _),event_nonneg _ _,event_nonneg _ _⟩
omit [Fintype A] in
lemma CT_nonneg (B : Book D P Q H A) : 0 ≤ CT (I := I) B :=
  cut_nonneg _ _ _ (fun _ => avg_nonneg _ (fun _ => avg_nonneg _ (fun _ => StarScore.variation_nonneg _ _)))

theorem common_lower (B : Book D P Q H A)
    (hμ : ∀p,0<(left B.graph).val p) (hκ : ∀q,0<(right B.graph).val q)
    {ζ η : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2) :
    (CT (I := I) B+B.CQ)/80000 ≤ DT (I := I) B+B.DQ+12*B.M+
      (12*(Fintype.card I:ℝ)/ζ)*B.EP+
      (12*(CommonTemplate.samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η))*B.WC+
      8*B.J+2*B.WB := by
  exact GlobalScores.common_lower B.levels B.graph B.history B.bit B.point B.center hμ hκ hζ hk hI hη hη'
    B.epsilon B.good B.label

omit [Fintype A] [Fintype H] [Fintype I] in
lemma center_lower (B : Book D P Q H A) :
    2*B.HQ-2*B.HP-4*B.J-6*B.M-B.CQ-B.WB ≤ B.DQ :=
  GlobalScores.center_lower B.levels B.graph B.bit B.point B.center B.epsilon B.good B.label

omit [Fintype H] [Fintype I] in
lemma point_lower (B : Book D P Q H A) {δ : ℝ} (hδ : 0<δ) :
    B.CP/80000 ≤ B.DP+B.T+2*B.HQ+4*B.J+26*B.M+(20/δ)*B.EP+(20*δ)*B.WC+B.WB :=
  GlobalMarginal.point_lower B.levels B.graph B.history B.bit B.point B.center hδ B.epsilon B.good B.label

omit [Fintype A] [Fintype H] [Fintype I] in
lemma scale_lower (B : Book D P Q H A) (L : ℝ)
    (hstable : ∀s,B.C s → RareLabels.minorityMass B.graph (B.bit s) ≤ L*(VP B.graph (B.bit s)+VQ B.graph (B.bit s)))
    (hrare : ∀s,¬B.C s → B.good s → RareLabels.minorityMass B.graph (B.bit s) ≤
      hp B.graph (B.bit s) (B.point s) (B.label s)+hq B.graph (B.bit s) (B.center s) (B.label s)+
        RareLabels.error B.graph (B.bit s) (B.point s) (B.center s)) :
    B.S ≤ L*(B.CP+B.CQ)+B.HP+B.HQ+B.M+B.WB/2 :=
  GlobalMarginal.scale_lower B.levels B.graph B.bit B.point B.center B.epsilon L B.good B.label hstable hrare
end Book
end
end PlanarUnitDistances.ScoreBook

namespace PlanarUnitDistances.ScoreCoercivity
noncomputable section

theorem from_scores {S HP HQ CP CQ CT DP DQ DT T E L : ℝ}
    (hE : 0 ≤ E) (hHP : 0 ≤ HP) (hCT : 0 ≤ CT) (hL : 0 ≤ L)
    (hcommon : (CT+CQ)/80000 ≤ DT+DQ+E)
    (hDT : DT ≤ CT/20000000+E) (hDQ : DQ ≤ CQ/20000000+E)
    (hcenter : 2*HQ-2*HP-CQ-E ≤ DQ)
    (hpoint : CP/80000 ≤ DP+T+2*HQ+E)
    (hDP : DP ≤ CP/20000000+E) (hT : T ≤ 2*HP+E)
    (hscale : S ≤ L*(CP+CQ)+HP+HQ+E) :
    CQ ≤ 250000*E ∧ HQ ≤ HP+130000*E ∧
      S ≤ (400000*L+2)*HP+(23000000000*L+130001)*E := by
  have hc : CT+CQ ≤ 250000*E := by linarith
  have hq : CQ ≤ 250000*E := by linarith
  have hQ : HQ ≤ HP+130000*E := by linarith
  have hp : CP ≤ 400000*HP+22000000000*E := by linarith
  refine ⟨hq,hQ,?_⟩
  have hsum : CP+CQ ≤ 400000*HP+23000000000*E := by linarith
  have hh := mul_le_mul_of_nonneg_left hsum hL
  nlinarith

end
end PlanarUnitDistances.ScoreCoercivity

namespace PlanarUnitDistances.BookCoercivity
open FiniteLaw ScoreBook FiniteStarCoupling RareMoments
open scoped Classical
noncomputable section
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q]
  [Fintype H] [Fintype A] [Fintype I]

omit [Fintype H] in
lemma loss_bounds (B : Book D P Q H A) (ζ η δ eP eQ eT ePred : ℝ) :
    let E := loss (I := I) B ζ η δ eP eQ eT ePred
    0 ≤ E ∧ commonLoss (I := I) B ζ η ≤ E ∧ centerLoss B ≤ E ∧
      pointLoss B δ ≤ E ∧ scaleLoss B ≤ E ∧ eP ≤ E ∧ eQ ≤ E ∧ eT ≤ E ∧ ePred ≤ E := by
  dsimp only [loss]
  have h0 := abs_nonneg (commonLoss (I := I) B ζ η)
  have h1 := abs_nonneg (centerLoss B)
  have h2 := abs_nonneg (pointLoss B δ)
  have h3 := abs_nonneg (scaleLoss B)
  have h4 := abs_nonneg eP
  have h5 := abs_nonneg eQ
  have h6 := abs_nonneg eT
  have h7 := abs_nonneg ePred
  have l0 := le_abs_self (commonLoss (I := I) B ζ η)
  have l1 := le_abs_self (centerLoss B)
  have l2 := le_abs_self (pointLoss B δ)
  have l3 := le_abs_self (scaleLoss B)
  have l4 := le_abs_self eP
  have l5 := le_abs_self eQ
  have l6 := le_abs_self eT
  have l7 := le_abs_self ePred
  refine ⟨by positivity,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    linarith only [h0,h1,h2,h3,h4,h5,h6,h7,l0,l1,l2,l3,l4,l5,l6,l7]

end
end PlanarUnitDistances.BookCoercivity

namespace PlanarUnitDistances.LevelSnapshot
open MeasureTheory Set Finset FiniteLaw LevelStates PlaceLevels
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

lemma measurable_value {Y : Type*} [MeasurableSpace Y] (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → Y) :
    Measurable (fun a => F (snapshot S z w src tgt u a)) :=
  (measurable_of_finite F).comp (measurable_snapshot S z w src tgt u)

lemma integrable_value (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → ℝ)
    {ν : Measure (Place K S×ℝ)} [IsFiniteMeasure ν] :
    Integrable (fun a => F (snapshot S z w src tgt u a)) ν := by
  apply Integrable.mono' (integrable_const (∑d : Data V E, |F d|))
    (measurable_value S z w src tgt u F).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using
      (single_le_sum (s:=univ) (fun d _ => abs_nonneg (F d)) (mem_univ (snapshot S z w src tgt u a)))

lemma integrable_piece (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → ℝ)
    (v : Place K S) (l r : ℝ) : IntegrableOn (fun s => F (snapshot S z w src tgt u (v,s))) (Icc l r) := by
  apply Integrable.mono' (integrable_const (∑d : Data V E, |F d|))
    ((measurable_value S z w src tgt u F).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using
      (single_le_sum (s:=univ) (fun d _ => abs_nonneg (F d)) (mem_univ (snapshot S z w src tgt u (v,s))))

end
end PlanarUnitDistances.LevelSnapshot

namespace PlanarUnitDistances.ActualSlots
open MeasureTheory Set Finset FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot LevelScores RareScore
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E] [Fintype F]

lemma negative_integral {l r b c : ℝ} (hlb : l ≤ b) (hbr : b ≤ r) (hlc : l ≤ c) (hcr : c ≤ r) :
    (∫s in Icc l r, ind (decide (s<b)≠decide (s<c)))=|b-c| := by
  have he (s : ℝ) : ind (decide (s<b)≠decide (s<c))=|ThresholdProfiles.bit b s-ThresholdProfiles.bit c s| := by
    by_cases hb : s<b <;> by_cases hc : s<c <;> simp [ind,ThresholdProfiles.bit,hb,hc]
  simp_rw [he]
  exact ThresholdProfiles.bit_sub_integral hlb hbr hlc hcr

end
end PlanarUnitDistances.ActualSlots

namespace PlanarUnitDistances.GlobalPairBudget
open MeasureTheory Set Finset Real PlaceLevels BudgetPlaces LevelGeometry PlaceScore
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

lemma total_allowance (S : Finset K) :
    (∑v : Place K S,2*allowance v)/(Module.finrank ℚ K:ℝ)=2*log 2 := by
  rw [Fintype.sum_sum_type]
  simp only [allowance,mul_zero,sum_const_zero,add_zero]
  exact arch_allowance K

lemma thickness_nonneg {S : Finset K} (v : Place K S) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') :
    0 ≤ alpha (av K v) d d'+allowance v := by
  cases v with
  | inl σ => exact alpha_add_log_two_nonneg _ hd hd' hdd
  | inr v =>
    simpa only [av,allowance,add_zero] using alpha_nonneg_nonarch
      (WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2)
      (WeightedAbsoluteValues.finiteEntry_nonarch K v.val.1 v.val.2) hd hd' hdd

lemma cancellation [IsGalois ℚ K] {S : Finset K} {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') (hmem : differenceProduct d d'∈S) :
    (∑v : Place K S,(2*(alpha (av K v) d d'+allowance v)-
      |threshold (av K v) d-threshold (av K v) d'|))/(Module.finrank ℚ K:ℝ)=2*log 2 := by
  have he (v : Place K S) :
      2*(alpha (av K v) d d'+allowance v)-|threshold (av K v) d-threshold (av K v) d'| =
      -log (av K v (differenceProduct d d'))+2*allowance v := by
    rw [place_identity _ hd hd' hdd,max_sub_min_eq_abs,abs_sub_comm (threshold (av K v) d')]
    ring
  simp_rw [he]
  rw [sum_add_distrib,sum_neg_distrib,add_div,neg_div,
    sum_log_product_formula K hmem (differenceProduct_ne_zero hdd),neg_zero,zero_add]
  exact total_allowance S

end
end PlanarUnitDistances.GlobalPairBudget

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Integration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.TailWindows
open Finset Set FiniteLaw
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E]

lemma tail_antitone (μ : Law E) (x : E → ℝ) : Antitone (tail μ x) := by
  intro s t hst
  exact event_mono μ (fun e he => lt_of_le_of_lt hst he)

end
end PlanarUnitDistances.TailWindows

namespace PlanarUnitDistances.ActualBudget
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots SlotIntegration TailWindows
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype V] [Fintype E] [Fintype F]

omit [IsGalois ℚ K] [Fintype V] in
lemma snapshot_frequency (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E) (v : Place K S) (s : ℝ) :
    frequency μ (snapshot S z w src tgt u (v,s))=
      tail μ (fun e => threshold (av K v) (z (src e)-z (tgt e))) s := by
  simp only [frequency,snapshot,LevelStates.bit,TailWindows.tail,threshold,decide_eq_true_eq]
end
end PlanarUnitDistances.ActualBudget

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ActualScoreBook
open MeasureTheory FiniteLaw LevelSnapshot ActualSlots ScoreBook FiniteStarCoupling RareRows RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

lemma average (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) (F : Data V (P×Q) → ℝ) :
    (∫a,F (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u a) ∂LevelScale.measure S)=
      mass S*avg (make S z w x y u π h ε good label hm).levels F := by
  have he := compress_avg (LevelScale.measure S) hm
    (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u)
    (measurable_snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u) F
  exact (mul_comm _ _).trans ((eq_div_iff hm.ne').mp he) |>.symm

end
end PlanarUnitDistances.ActualScoreBook

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LocalProfiles
open FiniteLaw FiniteStarCoupling WedgeProfiles RareScore RareMoments ScoreBook LevelScores
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q]

lemma X_nonneg (B : Book D P Q H A) (s : D) (p : P) : 0 ≤ X B s p := by
  unfold X ind
  positivity
lemma error1_nonneg (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : 0 ≤ error1 B s a := by
  unfold error1 jfirst jsecond ifirst isecond ind
  positivity
lemma error2_nonneg (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : 0 ≤ error2 B s a := by
  unfold error2 jpoints jfirst jsecond ifirst isecond ind
  positivity

end
end PlanarUnitDistances.LocalProfiles

namespace PlanarUnitDistances.WedgeSummary
open FiniteLaw FiniteStarCoupling WedgeProfiles RareScore ScoreBook LevelScores LocalProfiles
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q]

lemma first_joint (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (jfirst B s)=RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s) := by
  rw [show jfirst B s=(fun a => ind (exceptional B s (B.point s a.2.1) ∧ exceptional B s (B.center s a.1))) from rfl,
    WedgeLaw.first B.graph (fun p q => ind (exceptional B s (B.point s p) ∧ exceptional B s (B.center s q)))]
  rfl
lemma second_joint (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (jsecond B s)=RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s) := by
  rw [show jsecond B s=(fun a => ind (exceptional B s (B.point s a.2.2) ∧ exceptional B s (B.center s a.1))) from rfl,
    WedgeLaw.second B.graph (fun p q => ind (exceptional B s (B.point s p) ∧ exceptional B s (B.center s q)))]
  rfl
lemma point_joint (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (jpoints B s)=RareMoments.wedge B.graph (B.bit s) (B.point s) (B.label s) := by
  rw [WedgeLaw.average]
  rfl
lemma first_error (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (ifirst B s)=RareLabels.error B.graph (B.bit s) (B.point s) (B.center s) := by
  rw [show ifirst B s=(fun a => ind (¬CrossStructure.Consistent (B.bit s a.2.1 a.1) (B.point s a.2.1) (B.center s a.1))) from rfl,
    WedgeLaw.first B.graph (fun p q => ind (¬CrossStructure.Consistent (B.bit s p q) (B.point s p) (B.center s q)))]
  rfl
lemma second_error (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (isecond B s)=RareLabels.error B.graph (B.bit s) (B.point s) (B.center s) := by
  rw [show isecond B s=(fun a => ind (¬CrossStructure.Consistent (B.bit s a.2.2 a.1) (B.point s a.2.2) (B.center s a.1))) from rfl,
    WedgeLaw.second B.graph (fun p q => ind (¬CrossStructure.Consistent (B.bit s p q) (B.point s p) (B.center s q)))]
  rfl

lemma X_average (B : Book D P Q H A) :
    avg B.levels (fun s => avg (left B.graph) (X B s))=B.HP := by
  apply avg_congr
  intro s
  unfold LocalProfiles.X
  by_cases h : B.R s
  · simp only [h,ite_true]
    rfl
  · simp only [h,ite_false,avg_const]

lemma err1_at (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (error1 B s)=
      (if B.C s then VQ B.graph (B.bit s) else 0)+ind (¬B.C s ∧ ¬B.good s)+
      (if B.R s then 4*RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s)+
        4*RareLabels.error B.graph (B.bit s) (B.point s) (B.center s) else 0) := by
  unfold error1
  simp only [avg_add,avg_const]
  have hc : avg (WedgeLaw.law B.graph) (fun a => if B.C s then |bits B s a| else 0)=
      if B.C s then VQ B.graph (B.bit s) else 0 := by
    by_cases h : B.C s
    · simp only [h,ite_true,bits]
      exact WedgeLaw.mismatch B.graph (B.bit s)
    · simp [h,avg_const]
  rw [hc]
  congr 1
  by_cases h : B.R s
  · simp only [h,ite_true,avg_smul,avg_add,first_joint,second_joint,first_error,second_error]
    ring
  · simp [h,avg_const]

lemma err2_at (B : Book D P Q H A) (s : D) :
    avg (WedgeLaw.law B.graph) (error2 B s)=
      if B.R s then 2*RareMoments.wedge B.graph (B.bit s) (B.point s) (B.label s)+
        4*RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s)+
        4*RareLabels.error B.graph (B.bit s) (B.point s) (B.center s) else 0 := by
  unfold error2
  by_cases h : B.R s
  · simp only [h,ite_true,avg_smul,avg_add,point_joint,first_joint,second_joint,first_error,second_error]
    ring
  · simp [h,avg_const]

lemma cut_error (B : Book D P Q H A) :
    cut B.levels B.R (fun s => RareLabels.error B.graph (B.bit s) (B.point s) (B.center s)) ≤ B.M := by
  apply avg_mono
  intro s
  by_cases h : B.R s
  · simp only [h,ite_true]
    exact le_rfl
  · simp only [h,ite_false]
    exact event_nonneg _ _

theorem residual_budget (B : Book D P Q H A) :
    avg B.levels (fun s => avg (WedgeLaw.law B.graph) (error1 B s)) ≤ B.CQ+B.WB+4*B.J+4*B.M := by
  simp_rw [err1_at]
  rw [avg_add,avg_add]
  change B.CQ+B.WB+cut B.levels B.R (fun s => _+_) ≤ _
  rw [cut_add,cut_smul,cut_smul]
  have h := cut_error B
  change _ ≤ B.M at h
  dsimp only [Book.J]
  linarith

theorem size_budget (B : Book D P Q H A) :
    avg B.levels (fun s => avg (WedgeLaw.law B.graph) (error2 B s)) ≤ 2*JW B+4*B.J+4*B.M := by
  simp_rw [err2_at]
  change cut B.levels B.R (fun s => _+_+_) ≤ _
  rw [cut_add,cut_add,cut_smul,cut_smul,cut_smul]
  have h := cut_error B
  dsimp only [JW,Book.J]
  linarith
end
end PlanarUnitDistances.WedgeSummary

namespace PlanarUnitDistances.ActualProfiles
open MeasureTheory Set FiniteLaw LevelSnapshot ScoreBook ActualScoreBook PlaceLevels
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

namespace Input
variable (G : Input K V P Q H)

lemma height_nonneg (p : P) (v : Place K G.support) : 0 ≤ G.heightAt p v :=
  integral_nonneg (fun _ => LocalProfiles.X_nonneg _ _ _)
lemma error_nonneg (i : Bool) (a : Q×(P×P)) (v : Place K G.support) : 0 ≤ G.errorAt i a v := by
  apply integral_nonneg
  intro s
  cases i
  · exact LocalProfiles.error2_nonneg _ _ _
  · exact LocalProfiles.error1_nonneg _ _ _

end Input
end
end PlanarUnitDistances.ActualProfiles

namespace PlanarUnitDistances.SamplingDecay
open Filter CommonTemplate
noncomputable section
lemma limit {α : ℝ} (ha : 0 < α) (ha' : α < 1) :
    Tendsto (fun n => samplingError n α) atTop (nhds 0) := by
  have hr : 0 < 1-α := by linarith
  have hr' : 1-α < 1 := by linarith
  have hs : 0 < 1-α/2 := by linarith
  have hs' : 1-α/2 < 1 := by linarith
  have h0 : Tendsto (fun n : ℕ => (n:ℝ)^2*(1-α)^(n-2)) atTop (nhds 0) := by
    have hh := (tendsto_pow_const_mul_const_pow_of_lt_one 2 hr.le hr').div_const ((1-α)^2)
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [div_eq_iff (pow_ne_zero 2 hr.ne')]
    rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn]
  have h1 : Tendsto (fun n : ℕ => (1-α/2)^(n-1)) atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hs.le hs').div_const (1-α/2)
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [div_eq_iff hs.ne',←pow_succ,Nat.sub_add_cancel hn]
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hs.le hs'
  simpa only [samplingError,mul_zero,add_zero] using (h0.add (h1.const_mul 2)).add (h2.const_mul (2/α))
end
end PlanarUnitDistances.SamplingDecay

namespace PlanarUnitDistances.BudgetParameters
open Filter CommonTemplate
noncomputable section

lemma vanishing_pos (n : ℕ) : 0 < vanishing n := by unfold vanishing; positivity
lemma vanishing_limit : Tendsto vanishing atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R:=ℝ)))

lemma Params.zeta_pos (a : Params) : 0 < a.zeta := by
  have hk : (0:ℝ) < a.k := by exact_mod_cast a.k_pos
  unfold Params.zeta
  positivity
lemma Params.k_zeta (a : Params) : (a.k:ℝ)*a.zeta=1/2 := by
  have hk : (a.k:ℝ)≠0 := by exact_mod_cast a.k_pos.ne'
  unfold Params.zeta
  field_simp

theorem exists_small {C γ η s₀ ρ : ℝ} (_hC : 0 < C) (_hγ : 0 < γ)
    (hη : 0 < η) (hs : 0 < s₀) (hρ : 0 < ρ) :
    ∃a : Params, a.epsilon+a.epsilon ≤ s₀ ∧ leading a C γ η < ρ ∧ wedge a C γ η < ρ := by
  have hdlim : Tendsto (fun n => vanishing n*C) atTop (nhds 0) := by
    simpa only [zero_mul] using vanishing_limit.mul_const C
  obtain ⟨nd,hnd⟩ := (hdlim.eventually_lt_const (by linarith : (0:ℝ) < ρ/4)).exists
  let d := vanishing nd
  have hd : 0 < d := vanishing_pos nd
  have hq : Tendsto (fun n => joint C γ η (vanishing n) 0) atTop (nhds 0) := by
    have hh : Tendsto (fun n => C*(vanishing n+vanishing n)/γ) atTop (nhds 0) := by
      simpa only [add_zero,mul_zero,zero_div] using (vanishing_limit.add vanishing_limit).const_mul C |>.div_const γ
    simpa only [joint,add_zero,zero_div] using (hh.rpow_const_nhds_zero hη).div_const γ
  have hjlim : Tendsto (fun n => 8*joint C γ η (vanishing n) 0*C) atTop (nhds 0) := by
    simpa only [zero_mul,mul_zero] using (hq.const_mul 8).mul_const C
  have hwlim : Tendsto (fun n => joint C γ η (vanishing n) 0/Real.sqrt d*C) atTop (nhds 0) := by
    simpa only [zero_mul,zero_div] using (hq.div_const (Real.sqrt d)).mul_const C
  have helim : Tendsto (fun n => vanishing n+vanishing n) atTop (nhds 0) := by
    simpa only [zero_add] using vanishing_limit.add vanishing_limit
  obtain ⟨ne,hne0,hne1,hne2,hne3⟩ :=
    ((vanishing_limit.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).and
      ((helim.eventually_le_const hs).and
        ((hjlim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8)).and
          (hwlim.eventually_lt_const (by linarith : (0:ℝ)<ρ/4))))).exists
  let ε := vanishing ne
  have he : 0 < ε := vanishing_pos ne
  have halim : Tendsto (fun n => 96*vanishing n/ε) atTop (nhds 0) := by
    simpa only [mul_zero,zero_div] using (vanishing_limit.const_mul 96).div_const ε
  obtain ⟨na,hna0,hna1⟩ := ((vanishing_limit.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).and
    (halim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8))).exists
  let a := vanishing na
  have ha : 0 < a := vanishing_pos na
  have hblim : Tendsto (fun n => 20*vanishing n/ε) atTop (nhds 0) := by
    simpa only [mul_zero,zero_div] using (vanishing_limit.const_mul 20).div_const ε
  obtain ⟨nb,hnb⟩ := (hblim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8)).exists
  let b := vanishing nb
  have hb : 0 < b := vanishing_pos nb
  have hklim : Tendsto (fun n => 24*samplingError n (a^2)/ε) atTop (nhds 0) := by
    simpa only [mul_zero,zero_div] using ((SamplingDecay.limit (sq_pos_of_pos ha)
      (by dsimp [a] at *; nlinarith [vanishing_pos na])).const_mul 24).div_const ε
  obtain ⟨k,hk,hke⟩ := ((eventually_gt_atTop 0).and
    (hklim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8))).exists
  let ζ : ℝ := 1/(2*k)
  have hmlim : Tendsto (fun m : ℕ => (12*(k:ℝ)/ζ+20/b)*4/(m:ℝ)/ε) atTop (nhds 0) := by
    simpa only [zero_div] using (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R:=ℝ))).div_const ε
  obtain ⟨m,hm,hme⟩ := ((eventually_gt_atTop 0).and
    (hmlim.eventually_lt_const (by linarith : (0:ℝ)<ρ/8))).exists
  let p : Params := ⟨ε,b,a,d,k,m,he,hne0,hb,ha,hna0,hd,hk,hm⟩
  refine ⟨p,hne1,?_,?_⟩
  · change 8*joint C γ η ε 0*C+
      (96*a+20*b+24*samplingError k (a^2)+(12*(k:ℝ)/ζ+20/b)*4/(m:ℝ))/ε < ρ
    rw [add_div,add_div,add_div]
    linarith
  · change (d+joint C γ η ε 0/Real.sqrt d)*C < ρ
    rw [add_mul]
    linarith
end
end PlanarUnitDistances.BudgetParameters

namespace PlanarUnitDistances.IncidenceBook
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale ActualScoreBook LevelSnapshot BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params) (i : ℕ)
lemma capacity_pos : 0 < capacity a := pow_pos a.m_pos _
end
end PlanarUnitDistances.IncidenceBook

namespace PlanarUnitDistances.BookEnvelope
open Filter FiniteLaw ScoreBook BookCoercivity BudgetParameters
open scoped Classical
noncomputable section

variable (a : Params) (C γ η ξ r : ℝ)

theorem total_limit (ξ r : ℕ → ℝ) (hξ : Tendsto ξ atTop (nhds 0))
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto (fun n => total a C γ η (ξ n) (r n)) atTop (nhds (leading a C γ η)) := by
  have hheight : Tendsto (fun n => height C (r n)) atTop (nhds (height C 0)) := by
    exact (tendsto_const_nhds.add hr).const_mul C
  have hjoint : Tendsto (fun n => joint C γ η a.epsilon (ξ n)) atTop
      (nhds (joint C γ η a.epsilon 0)) := by
    exact (tendsto_const_nhds.add hξ).div_const γ
  have hj : Tendsto (fun n => j a C γ η (ξ n) (r n)) atTop (nhds (j a C γ η 0 0)) :=
    (hjoint.div_const 2).mul hheight
  have hp : Tendsto (fun n => pred a (r n)) atTop (nhds (pred a 0)) :=
    hr.add ((tendsto_const_nhds.add (hr.const_mul 18)).div_const a.epsilon)
  have hs : Tendsto (fun n => star a C (r n)) atTop (nhds (star a C 0)) :=
    hr.add ((hr.const_mul 2).mul (tendsto_const_nhds.add hheight))
  have hpr : Tendsto (fun n => prediction a (r n)) atTop (nhds (prediction a 0)) :=
    (hr.add (hr.div_const a.epsilon)).add (hr.div_const a.epsilon)
  have hc : Tendsto (fun n => common a C γ η (ξ n) (r n)) atTop
      (nhds (common a C γ η 0 0)) :=
    ((((hr.const_mul 12).add (hp.const_mul (12*(a.k:ℝ)/a.zeta))).add
      tendsto_const_nhds).add (hj.const_mul 8)).add ((hr.div_const a.epsilon).const_mul 2)
  have hq : Tendsto (fun n => center a C γ η (ξ n) (r n)) atTop
      (nhds (center a C γ η 0 0)) :=
    ((hj.const_mul 4).add (hr.const_mul 6)).add (hr.div_const a.epsilon)
  have hpoint : Tendsto (fun n => point a C γ η (ξ n) (r n)) atTop
      (nhds (point a C γ η 0 0)) :=
    ((((hj.const_mul 4).add (hr.const_mul 26)).add (hp.const_mul (20/a.delta))).add
      tendsto_const_nhds).add (hr.div_const a.epsilon)
  have hsc : Tendsto (fun n => sc a (r n)) atTop (nhds (sc a 0)) :=
    hr.add ((hr.div_const a.epsilon).div_const 2)
  have hh : Tendsto (fun n => total a C γ η (ξ n) (r n)) atTop (nhds (total a C γ η 0 0)) :=
    ((((hc.add hq).add hpoint).add hsc).add (hs.const_mul 3)).add hpr
  convert hh using 1
  unfold total common center point sc star prediction pred j height leading joint
  rw [a.k_zeta]
  ring_nf

lemma sampling_nonneg : 0 ≤ CommonTemplate.samplingError a.k (a.eta^2) := by
  have h0 : 0 ≤ 1-a.eta^2 := by nlinarith [a.eta_pos,a.eta_lt]
  have h1 : 0 ≤ 1-a.eta^2/2 := by nlinarith [a.eta_pos,a.eta_lt]
  unfold CommonTemplate.samplingError
  positivity

variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A]

omit [Fintype H] in
theorem bounds (B : Book D P Q H A) (hC : 0 ≤ C) (_hγ : 0 < γ) (_hξ : 0 ≤ ξ) (hr : 0 ≤ r)
    (hM : B.M ≤ r*B.S) (hWC : B.WC ≤ (1/a.epsilon)*B.S)
    (hWB : B.WB ≤ (r/a.epsilon)*B.S) (hJ : B.J ≤ j a C γ η ξ r*B.S)
    (hEP : B.EP ≤ pred a r*B.S) :
    loss (I:=Fin a.k) B a.zeta a.eta a.delta
      (star a C r*B.S) (star a C r*B.S) (star a C r*B.S) (prediction a r*B.S) ≤
        total a C γ η ξ r*B.S := by
  obtain ⟨hS,hM0,hP,hQ,hCP,hCQ,hJ0,hWC0,hWB0⟩ := B.nonneg
  have hEP0 : 0 ≤ B.EP := by
    unfold Book.EP
    apply cut_nonneg
    intro s
    unfold CommonTemplate.predictionError
    apply avg_nonneg
    intro pq
    exact sub_nonneg.mpr (event_le_one _ _)
  have hz := a.zeta_pos
  have he := a.epsilon_pos
  have hd := a.delta_pos
  have ha := a.eta_pos
  have hsample := sampling_nonneg a
  have hk : 0 < 1-(a.k:ℝ)*a.zeta := by rw [a.k_zeta]; norm_num
  have hc0 : 0 ≤ commonLoss (I:=Fin a.k) B a.zeta a.eta := by
    unfold commonLoss
    simp only [Fintype.card_fin]
    positivity
  have hq0 : 0 ≤ centerLoss B := by unfold centerLoss; positivity
  have hp0 : 0 ≤ pointLoss B a.delta := by unfold pointLoss; positivity
  have hs0 : 0 ≤ scaleLoss B := by unfold scaleLoss; positivity
  have hst : 0 ≤ star a C r := by unfold star height; positivity
  have hpr : 0 ≤ prediction a r := by unfold prediction; positivity
  have hc : commonLoss (I:=Fin a.k) B a.zeta a.eta ≤ common a C γ η ξ r*B.S := by
    unfold commonLoss common
    simp only [Fintype.card_fin]
    calc
      _ ≤ 12*(r*B.S)+(12*(a.k:ℝ)/a.zeta)*(pred a r*B.S)+
          (12*(CommonTemplate.samplingError a.k (a.eta^2)/(1-(a.k:ℝ)*a.zeta)+8*a.eta))*((1/a.epsilon)*B.S)+
          8*(j a C γ η ξ r*B.S)+2*((r/a.epsilon)*B.S) := by gcongr
      _ = _ := by ring
  have hq : centerLoss B ≤ center a C γ η ξ r*B.S := by
    unfold centerLoss center
    calc
      _ ≤ 4*(j a C γ η ξ r*B.S)+6*(r*B.S)+(r/a.epsilon)*B.S := by gcongr
      _ = _ := by ring
  have hp : pointLoss B a.delta ≤ point a C γ η ξ r*B.S := by
    unfold pointLoss point
    calc
      _ ≤ 4*(j a C γ η ξ r*B.S)+26*(r*B.S)+(20/a.delta)*(pred a r*B.S)+
        (20*a.delta)*((1/a.epsilon)*B.S)+(r/a.epsilon)*B.S := by gcongr
      _ = _ := by ring
  have hs : scaleLoss B ≤ sc a r*B.S := by
    unfold scaleLoss sc
    calc
      _ ≤ r*B.S+((r/a.epsilon)*B.S)/2 := by gcongr
      _ = _ := by ring
  unfold loss total
  rw [abs_of_nonneg hc0,abs_of_nonneg hq0,abs_of_nonneg hp0,abs_of_nonneg hs0,
    abs_of_nonneg (mul_nonneg hst hS),abs_of_nonneg (mul_nonneg hpr hS)]
  linarith
end
end PlanarUnitDistances.BookEnvelope

namespace PlanarUnitDistances.CoercivityAll
open FiniteLaw ScoreBook FiniteStarCoupling RareMoments BookCoercivity
open scoped Classical
noncomputable section
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q]
  [Fintype H] [Fintype A] [Fintype I]
theorem all (B : Book D P Q H A)
    (hμ : ∀p,0<(left B.graph).val p) (hκ : ∀q,0<(right B.graph).val q)
    {ζ η δ L eP eQ eT ePred : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2) (hδ : 0<δ) (hL : 0 ≤ L)
    (hstable : ∀s,B.C s → RareLabels.minorityMass B.graph (B.bit s) ≤ L*(VP B.graph (B.bit s)+VQ B.graph (B.bit s)))
    (hrare : ∀s,¬B.C s → B.good s → RareLabels.minorityMass B.graph (B.bit s) ≤
      hp B.graph (B.bit s) (B.point s) (B.label s)+hq B.graph (B.bit s) (B.center s) (B.label s)+
        RareLabels.error B.graph (B.bit s) (B.point s) (B.center s))
    (hDP : B.DP ≤ B.CP/20000000+eP) (hDQ : B.DQ ≤ B.CQ/20000000+eQ)
    (hDT : Book.DT (I := I) B ≤ Book.CT (I := I) B/20000000+eT)
    (hT : B.T ≤ 2*B.HP+ePred) :
    B.CQ ≤ 250000*loss (I := I) B ζ η δ eP eQ eT ePred ∧
    B.HQ ≤ B.HP+130000*loss (I := I) B ζ η δ eP eQ eT ePred ∧
    B.S ≤ (400000*L+2)*B.HP+(23000000000*L+130001)*loss (I := I) B ζ η δ eP eQ eT ePred := by
  obtain ⟨hE,h0,h1,h2,h3,h4,h5,h6,h7⟩ := loss_bounds (I := I) B ζ η δ eP eQ eT ePred
  have hc := B.common_lower (I := I) hμ hκ hζ hk hI hη hη'
  have hq := B.center_lower
  have hp := B.point_lower hδ
  have hs := B.scale_lower L hstable hrare
  have hnn := B.nonneg
  have hct := B.CT_nonneg (I := I)
  dsimp only [commonLoss,centerLoss,pointLoss,scaleLoss] at h0 h1 h2 h3
  exact ScoreCoercivity.from_scores (S := B.S) (HP := B.HP) (HQ := B.HQ)
    (CP := B.CP) (CQ := B.CQ) (CT := Book.CT (I := I) B)
    (DP := B.DP) (DQ := B.DQ) (DT := Book.DT (I := I) B) (T := B.T) hE hnn.2.2.1 hct hL
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
end
end PlanarUnitDistances.CoercivityAll

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_RareBudget
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceNoise
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params)
lemma tpos (i : ℕ) : 0 < s.t i := by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]
lemma dp_nonneg (i : ℕ) : 0 ≤ dp s i := Real.rpow_nonneg (tpos s i).le _
lemma collision_nonneg (i : ℕ) : 0 ≤ collision s a i := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (dp_nonneg s i)
lemma root_nonneg (i : ℕ) : 0 ≤ rootInfo s a i := Real.rpow_nonneg
  (div_nonneg (s.good i).information_nonneg (Nat.cast_nonneg _)) _
lemma nonneg (i : ℕ) : 0 ≤ noise s a i := by
  unfold noise
  have h₁ := collision_nonneg s a i
  have h₂ := root_nonneg s a i
  have h₃ := vanishing_pos i
  positivity
lemma components (i : ℕ) :
    |(2*Real.log 2+4)/scale s i| ≤ noise s a i ∧ collision s a i ≤ noise s a i ∧
      vanishing i ≤ noise s a i ∧ rootInfo s a i ≤ noise s a i := by
  have h₀ := abs_nonneg ((2*Real.log 2+4)/scale s i)
  have h₁ := collision_nonneg s a i
  have h₂ := (vanishing_pos i).le
  have h₃ := root_nonneg s a i
  unfold noise
  constructor; linarith
  constructor; linarith
  constructor <;> linarith
lemma dp_le_collision (i : ℕ) : dp s i ≤ collision s a i := by
  have hc : (1:ℝ) ≤ capacity a := by exact_mod_cast capacity_pos a
  have hh := one_le_pow₀ (n:=length s a i) hc
  exact (one_mul (dp s i)).symm.le.trans (mul_le_mul_of_nonneg_right hh (dp_nonneg s i))
lemma row_atom (i : ℕ) (p : s.P i) (q : s.Q i) :
    (FiniteStarCoupling.row (graph s i) p).val q ≤ dp s i := by
  have hr := row_bound s i p q
  rw [one_div,←Real.rpow_neg (tpos s i).le] at hr
  simpa only [dp,neg_div] using hr
end
end PlanarUnitDistances.IncidenceNoise

namespace PlanarUnitDistances.EnvelopeCoercivity
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook BudgetParameters
  BookEnvelope BookCoercivity
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A]
variable (B : Book D P Q H A) (a : Params) {C L ξ r : ℝ}

theorem bounds (hC : 0<C) (hL : 0≤L) (hξ : 0≤ξ) (hr : 0≤r)
    (hμ : ∀p,0<(left B.graph).val p) (hκ : ∀q,0<(right B.graph).val q)
    (hst : ∀d,minorityMass B.graph (B.bit d) ≤ L*(VP B.graph (B.bit d)+VQ B.graph (B.bit d)))
    (hra : ∀d,B.R d → minorityMass B.graph (B.bit d) ≤ hp B.graph (B.bit d) (B.point d) (B.label d)+
      hq B.graph (B.bit d) (B.center d) (B.label d)+RareLabels.error B.graph (B.bit d) (B.point d) (B.center d))
    (hM : B.M ≤ r*B.S) (hWC : B.WC ≤ (1/a.epsilon)*B.S) (hWB : B.WB ≤ (r/a.epsilon)*B.S)
    (hJ : B.J ≤ j a C (27/50) (1/25) ξ r*B.S) (hEP : B.EP ≤ pred a r*B.S)
    (hDP : B.DP ≤ B.CP/20000000+star a C r*B.S)
    (hDQ : B.DQ ≤ B.CQ/20000000+star a C r*B.S)
    (hDT : Book.DT (I:=Fin a.k) B ≤ Book.CT (I:=Fin a.k) B/20000000+star a C r*B.S)
    (hT : B.T ≤ 2*B.HP+prediction a r*B.S) :
    B.CQ ≤ 250000*total a C (27/50) (1/25) ξ r*B.S ∧
    B.HQ ≤ B.HP+130000*total a C (27/50) (1/25) ξ r*B.S ∧
    B.S ≤ pointConstant L*B.HP+lossConstant L*total a C (27/50) (1/25) ξ r*B.S := by
  have hk : (Fintype.card (Fin a.k):ℝ)*a.zeta<1 := by
    rw [Fintype.card_fin,a.k_zeta]; norm_num
  have hh := CoercivityAll.all (I:=Fin a.k) B hμ hκ a.zeta_pos hk
    (by simpa only [Fintype.card_fin] using a.k_pos) a.eta_pos a.eta_lt a.delta_pos hL
    (fun d _ => hst d) (fun d h₁ h₂ => hra d ⟨h₁,h₂⟩) hDP hDQ hDT hT
  have he := BookEnvelope.bounds a C (27/50) (1/25) ξ r B hC.le (by norm_num) hξ hr hM hWC hWB hJ hEP
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ 250000*loss (I:=Fin a.k) B a.zeta a.eta a.delta
          (star a C r*B.S) (star a C r*B.S) (star a C r*B.S) (prediction a r*B.S) := hh.1
      _ ≤ _ := by linarith
  · linarith [mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤130000)]
  · have hc : 0≤lossConstant L := by unfold lossConstant; positivity
    have ht := mul_le_mul_of_nonneg_left he hc
    dsimp only [pointConstant,lossConstant] at ht ⊢
    linarith [hh.2.2]

omit [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] in
lemma positive_fraction {S HP L E : ℝ} (hL : 0≤L) (hS : 0≤S)
    (h : S≤pointConstant L*HP+lossConstant L*E*S) (hE : lossConstant L*E≤1/2) :
    S/(2*pointConstant L)≤HP := by
  have hp : 0<pointConstant L := by unfold pointConstant; positivity
  have ht := mul_le_mul_of_nonneg_right hE hS
  apply (div_le_iff₀ (by positivity : 0<2*pointConstant L)).mpr
  nlinarith
end
end PlanarUnitDistances.EnvelopeCoercivity

namespace PlanarUnitDistances.ProfileBudget
open MeasureTheory Set Finset FiniteLaw FiniteStarCoupling LevelSnapshot
  ScoreBook ActualScoreBook PlaceLevels ActualProfiles
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)

lemma weighted_nonneg {f : Place K G.support → ℝ} (hf : ∀v,0≤f v) : 0 ≤ weighted G f :=
  mul_nonneg (NNReal.coe_nonneg _) (sum_nonneg fun v _ => hf v)

lemma integrate (F : Data V (P×Q) → ℝ) :
    weighted G (fun v => ∫s in Icc (-radius K G.support v) (radius K G.support v), F (G.snap (v,s)))=
      mass G.support*avg G.book.levels F := by
  have hh := ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts
    G.graph G.history G.epsilon G.good G.label G.mass_pos F
  have hi := FiniteLevels.integral_eq (LevelScale.weight K)
    (fun v => -radius K G.support v) (radius K G.support)
    (fun a => F (G.snap a))
    (measurable_value G.support G.z G.w (fun pq : P×Q => G.point pq.1)
      (fun pq : P×Q => G.center pq.2) G.shifts F)
    (∑d : Data V (P×Q), |F d|) (fun a =>
      single_le_sum (s := univ) (fun d _ => abs_nonneg (F d)) (mem_univ (G.snap a)))
  exact hi.symm.trans hh

lemma height_eq (p : P) : height G p=mass G.support*avg G.book.levels (fun s => LocalProfiles.X G.book s p) :=
  integrate G (fun s => LocalProfiles.X G.book s p)
lemma error_eq (i : Bool) (a : Q×(P×P)) : error G i a=mass G.support*
    avg G.book.levels (fun s => (if i then LocalProfiles.error1 else LocalProfiles.error2) G.book s a) :=
  integrate G (fun s => (if i then LocalProfiles.error1 else LocalProfiles.error2) G.book s a)
lemma height_nonneg (p : P) : 0 ≤ height G p := weighted_nonneg G (G.height_nonneg p)
lemma error_nonneg (i : Bool) (a : Q×(P×P)) : 0 ≤ error G i a := weighted_nonneg G (G.error_nonneg i a)

lemma height_average : avg (left G.graph) (height G)=mass G.support*G.book.HP := by
  rw [show height G=(fun p => mass G.support*avg G.book.levels (fun s => LocalProfiles.X G.book s p)) from funext (height_eq G)]
  rw [avg_smul,avg_comm]
  congr 1
  exact WedgeSummary.X_average G.book

theorem residual_budget : avg (WedgeLaw.law G.graph) (error G true) ≤
    mass G.support*(G.book.CQ+G.book.WB+4*G.book.J+4*G.book.M) := by
  rw [show error G true=(fun a => mass G.support*avg G.book.levels (fun s => LocalProfiles.error1 G.book s a)) from funext (error_eq G true)]
  rw [avg_smul,avg_comm]
  apply mul_le_mul_of_nonneg_left _ G.mass_pos.le
  exact WedgeSummary.residual_budget G.book

theorem size_budget : avg (WedgeLaw.law G.graph) (error G false) ≤
    mass G.support*(2*WedgeSummary.JW G.book+4*G.book.J+4*G.book.M) := by
  rw [show error G false=(fun a => mass G.support*avg G.book.levels (fun s => LocalProfiles.error2 G.book s a)) from funext (error_eq G false)]
  rw [avg_smul,avg_comm]
  apply mul_le_mul_of_nonneg_left _ G.mass_pos.le
  exact WedgeSummary.size_budget G.book

end
end PlanarUnitDistances.ProfileBudget

namespace PlanarUnitDistances.RarePairBudget
open MeasureTheory Set Real FiniteLaw PlaceScore RareScore
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma slot_pointwise (r : Bool) (l x y z : A×B) (b c : Bool) :
    2*RareScore.ind (exceptional r l x)-3*(RareScore.ind (exceptional r l y)+
      RareScore.ind (exceptional r l z)+RareScore.ind (¬CrossStructure.Consistent b x y)+
      RareScore.ind (¬CrossStructure.Consistent c x z)) ≤ slot r l x y z b c := by
  have h := slot_lower r l x y z b c
  have h₁ : RareScore.ind (exceptional r l x ∧ exceptional r l y) ≤ RareScore.ind (exceptional r l y) := by
    unfold RareScore.ind; split_ifs <;> simp_all
  have h₂ : RareScore.ind (exceptional r l x ∧ exceptional r l z) ≤ RareScore.ind (exceptional r l z) := by
    unfold RareScore.ind; split_ifs <;> simp_all
  linarith

lemma cap_left {ε b b' T : ℝ} {g : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (hlo : g b<ε) (s : ℝ) :
    cap ε g b b' T s ≤ 2*PlaceScore.ind (Icc (b-T) b) s := by
  have hright : (if 1-ε<g s then (2:ℝ) else 0)*PlaceScore.ind (Icc b' (b'+T)) s=0 := by
    by_cases hs : s∈Icc b' (b'+T)
    · have hm := hg (hbb.trans hs.1)
      have hn : ¬1-ε<g s := by linarith
      simp [hn]
    · simp [PlaceScore.ind,hs]
  unfold cap
  rw [hright,add_zero]
  have hi : PlaceScore.ind (Icc (b-T) b ∩ Iio b) s ≤ PlaceScore.ind (Icc (b-T) b) s := by
    unfold PlaceScore.ind
    by_cases hs : s∈Icc (b-T) b ∩ Iio b
    · simp [hs,hs.1]
    · simp [hs,Set.indicator]; split_ifs <;> norm_num
  split_ifs <;> nlinarith [PlaceScore.ind_nonneg (Icc (b-T) b) s]

lemma cap_right {ε b b' T : ℝ} {g : ℝ → ℝ}
    (hg : Antitone g) (hlo : ε ≤ g b) (s : ℝ) :
    cap ε g b b' T s ≤ 2*PlaceScore.ind (Icc b' (b'+T)) s := by
  have hleft : (if g s<ε then (2:ℝ) else 0)*PlaceScore.ind (Icc (b-T) b ∩ Iio b) s=0 := by
    by_cases hs : s∈Icc (b-T) b ∩ Iio b
    · have hn : ¬g s<ε := not_lt.mpr (hlo.trans (hg hs.1.2))
      simp [hn]
    · simp [PlaceScore.ind,hs]
  unfold cap
  rw [hleft,zero_add]
  split_ifs <;> nlinarith [PlaceScore.ind_nonneg (Icc b' (b'+T)) s]

theorem positive_budget {ε b b' T : ℝ} {g f : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (hT : 0 ≤ T)
    (hf : Integrable f) (hcap : ∀s,f s ≤ cap ε g b b' T s) : (∫s,f s) ≤ 2*T := by
  by_cases hl : g b<ε
  · have h := integral_mono hf ((ind_Icc_integrable (b-T) b).const_mul 2)
      (fun s => (hcap s).trans (cap_left hε hg hbb hl s))
    rw [integral_const_mul,ind_Icc_integral,show b-(b-T)=T by ring,max_eq_right hT] at h
    exact h
  · have h := integral_mono hf ((ind_Icc_integrable b' (b'+T)).const_mul 2)
      (fun s => (hcap s).trans (cap_right hg (le_of_not_gt hl) s))
    rw [integral_const_mul,ind_Icc_integral,show b'+T-b'=T by ring,max_eq_right hT] at h
    exact h
end
end PlanarUnitDistances.RarePairBudget

namespace PlanarUnitDistances.RareGlobalBudget
open MeasureTheory Set Finset Real PlaceLevels BudgetPlaces LevelGeometry GlobalPairBudget
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

theorem weighted_pair (S : Finset K) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') (hmem : differenceProduct d d'∈S)
    {ε : ℝ} (hε : ε<1/2) (g f : Place K S → ℝ → ℝ)
    (hg : ∀v,Antitone (g v)) (hf : ∀v,Integrable (f v))
    (hcap : ∀v s,f v s ≤ RarePairBudget.cap ε (g v)
      (min (threshold (av K v) d) (threshold (av K v) d'))
      (max (threshold (av K v) d) (threshold (av K v) d'))
      (alpha (av K v) d d'+allowance v) s) :
    (∑v : Place K S,((∫s,f v s)-|threshold (av K v) d-threshold (av K v) d'|)) /
      (Module.finrank ℚ K:ℝ) ≤ 2*log 2 := by
  have hb (v : Place K S) := RarePairBudget.positive_budget hε (hg v)
    (min_le_max (a:=threshold (av K v) d) (b:=threshold (av K v) d'))
    (GlobalPairBudget.thickness_nonneg v hd hd' hdd) (hf v) (hcap v)
  have hs := sum_le_sum (s:=univ) (fun v _ => sub_le_sub_right (hb v)
    |threshold (av K v) d-threshold (av K v) d'|)
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Module.finrank ℚ K))
  rw [cancellation hd hd' hdd hmem] at hh
  exact hh
end
end PlanarUnitDistances.RareGlobalBudget

namespace PlanarUnitDistances.ActualRarePair
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
open scoped Classical BigOperators
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

omit [Fintype V] in
lemma positive_bounds (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x y y' : V) (e f : E) (a : Data V E) :
    0≤positive ε μ good label x y y' e f a ∧ positive ε μ good label x y y' e f a≤2 := by
  unfold positive
  split_ifs
  · norm_num
  · exact LevelScores.positive_bounds _ _ _ _ _ _ _ _ _ _

lemma cap_nonneg (ε : ℝ) (g : ℝ → ℝ) (b b' T s : ℝ) :
    0≤RarePairBudget.cap ε g b b' T s := by
  unfold RarePairBudget.cap
  split_ifs <;> nlinarith [PlaceScore.ind_nonneg (Icc (b-T) b ∩ Iio b) s,
    PlaceScore.ind_nonneg (Icc b' (b'+T)) s]

lemma cap_eq {ε : ℝ} {g ρ : ℝ → ℝ} {b b' T s : ℝ}
    (hc : ¬PlaceScore.common ε (g s)) :
    PlaceScore.cap ε g ρ b b' T s=RarePairBudget.cap ε g b b' T s := by
  simp [PlaceScore.cap,PlaceScore.reward,hc,RarePairBudget.cap]

omit [Fintype V] in

theorem positive_cap (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : ε<1/2) (e f : E) (he : src e=src f)
    (hu : (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1)
    (hu' : (z (src f)-z (tgt f))*(w (src f)-w (tgt f))=1)
    (hy : z (tgt e)≠z (tgt f)) (v : Place K S) (s : ℝ) :
    positive ε μ good label (src e) (tgt e) (tgt f) e f (snapshot S z w src tgt u (v,s))≤
      RarePairBudget.cap ε (TailWindows.tail μ (fun j => threshold (av K v) (z (src j)-z (tgt j))))
        (min (threshold (av K v) (z (src e)-z (tgt e))) (threshold (av K v) (z (src f)-z (tgt f))))
        (max (threshold (av K v) (z (src e)-z (tgt e))) (threshold (av K v) (z (src f)-z (tgt f))))
        (alpha (av K v) (z (src e)-z (tgt e)) (z (src f)-z (tgt f))+LevelGeometry.allowance v) s := by
  let a := snapshot S z w src tgt u (v,s)
  by_cases hc : PlaceScore.common ε (frequency μ a)
  · unfold positive
    rw [ite_eq_left hc]
    exact cap_nonneg _ _ _ _ _ _
  · have hu'' := hu'
    rw [←he] at hu''
    have hh := LevelSlotGeometry.positive_le_cap S z w u v s ε
      (TailWindows.tail μ (fun j => threshold (av K v) (z (src j)-z (tgt j))))
      (fun _ => 0) hε (good a) (label a) (src e) (tgt e) (tgt f) hu hu'' hy
    have hcf : ¬PlaceScore.common ε (TailWindows.tail μ (fun j => threshold (av K v) (z (src j)-z (tgt j))) s) := by
      simpa only [a,ActualBudget.snapshot_frequency] using hc
    rw [cap_eq hcf] at hh
    unfold positive
    rw [ite_eq_right hc,ActualBudget.snapshot_frequency]
    convert hh using 1 <;> simp only [a,snapshot,LevelStates.bit,threshold,←he]
    rfl

theorem upper [IsGalois ℚ K] (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : ε<1/2) (e f : E) (he : src e=src f)
    (hu : (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1)
    (hu' : (z (src f)-z (tgt f))*(w (src f)-w (tgt f))=1)
    (hy : z (tgt e)≠z (tgt f))
    (hm : z (src e)-z (tgt e)∈S) (hm' : z (src f)-z (tgt f)∈S)
    (hΔ : differenceProduct (z (src e)-z (tgt e)) (z (src f)-z (tgt f))∈S) :
    (∫a,score ε μ good label (src e) (tgt e) (tgt f) e f (snapshot S z w src tgt u a)
      ∂LevelScale.measure S)≤2*log 2 := by
  let d := z (src e)-z (tgt e)
  let d' := z (src f)-z (tgt f)
  have hd : d≠0 := left_ne_zero_of_mul_eq_one hu
  have hd' : d'≠0 := left_ne_zero_of_mul_eq_one hu'
  have hdd : d≠d' := by
    dsimp only [d,d']
    rw [←he]
    exact fun h => hy (sub_right_injective h)
  let a := snapshot S z w src tgt u
  let pos := positive ε μ good label (src e) (tgt e) (tgt f) e f
  let neg : Data V E → ℝ := fun a => RareScore.ind (a.1 e≠a.1 f)
  let F : Place K S → ℝ → ℝ := fun v => (Icc (-radius K S v) (radius K S v)).indicator (fun s => pos (a (v,s)))
  have hF (v : Place K S) : Integrable (F v) :=
    (integrable_piece S z w src tgt u pos v _ _).integrable_indicator measurableSet_Icc
  have hcap (v : Place K S) (s : ℝ) : F v s≤RarePairBudget.cap ε
      (TailWindows.tail μ (fun j => threshold (av K v) (z (src j)-z (tgt j))))
      (min (threshold (av K v) d) (threshold (av K v) d'))
      (max (threshold (av K v) d) (threshold (av K v) d'))
      (alpha (av K v) d d'+LevelGeometry.allowance v) s := by
    by_cases hs : s∈Icc (-radius K S v) (radius K S v)
    · dsimp only [F]
      rw [Set.indicator_of_mem hs]
      exact positive_cap S z w src tgt u μ good label hε e f he hu hu' hy v s
    · dsimp only [F]
      rw [Set.indicator_of_notMem hs]
      exact cap_nonneg _ _ _ _ _ _
  have hb := RareGlobalBudget.weighted_pair S hd hd' hdd hΔ hε _ F
    (fun v => TailWindows.tail_antitone μ _) hF hcap
  have hbound (a : Place K S×ℝ) : |score ε μ good label (src e) (tgt e) (tgt f) e f
      (snapshot S z w src tgt u a)|≤2 := by
    have hp := positive_bounds ε μ good label (src e) (tgt e) (tgt f) e f (snapshot S z w src tgt u a)
    have hn := RareScore.ind_nonneg ((snapshot S z w src tgt u a).1 e≠(snapshot S z w src tgt u a).1 f)
    have hn' := RareScore.ind_le_one ((snapshot S z w src tgt u a).1 e≠(snapshot S z w src tgt u a).1 f)
    unfold score
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  rw [LevelScale.measure,FiniteLevels.integral_eq _ _ _ _ (measurable_value S z w src tgt u _) 2 hbound]
  have hp (v : Place K S) : (∫s in Icc (-radius K S v) (radius K S v),
      score ε μ good label (src e) (tgt e) (tgt f) e f (snapshot S z w src tgt u (v,s)))=
      (∫s,F v s)-|threshold (av K v) d-threshold (av K v) d'| := by
    change (∫s in Icc (-radius K S v) (radius K S v),pos (a (v,s))-neg (a (v,s)))=_
    rw [integral_sub (integrable_piece S z w src tgt u pos v _ _) (integrable_piece S z w src tgt u neg v _ _)]
    dsimp only [F]
    rw [integral_indicator measurableSet_Icc]
    congr 1
    exact ActualSlots.negative_integral (threshold_in_range K hm v).1 (threshold_in_range K hm v).2
      (threshold_in_range K hm' v).1 (threshold_in_range K hm' v).2
  simp_rw [hp]
  convert hb using 1
  simp only [LevelScale.weight,div_eq_mul_inv,mul_comm]
  rfl

omit [Fintype V] in
lemma lower_slot (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x y y' : V) (e f : E) (a : Data V E) :
    2*RareScore.ind (rareException ε μ good label x a)-
      3*(RareScore.ind (rareException ε μ good label y a)+RareScore.ind (rareException ε μ good label y' a)+
        RareScore.ind (¬CrossStructure.Consistent (a.1 e) (a.2 x) (a.2 y))+
        RareScore.ind (¬CrossStructure.Consistent (a.1 f) (a.2 x) (a.2 y')))-
      RareScore.ind (PlaceScore.common ε (frequency μ a))-
      RareScore.ind (¬PlaceScore.common ε (frequency μ a) ∧ ¬good a) ≤
    score ε μ good label x y y' e f a := by
  have hi := RareScore.ind_nonneg (¬CrossStructure.Consistent (a.1 e) (a.2 x) (a.2 y))
  have hi' := RareScore.ind_nonneg (¬CrossStructure.Consistent (a.1 f) (a.2 x) (a.2 y'))
  have hn := RareScore.ind_le_one (a.1 e≠a.1 f)
  by_cases hc : PlaceScore.common ε (frequency μ a)
  · simp only [score,positive,rareException,hc,not_true_eq_false,false_and,
      ite_eq_left]
    norm_num [RareScore.ind] at *
    linarith
  · by_cases hg : good a
    · have h := RarePairBudget.slot_pointwise (LevelScores.minority (frequency μ a)) (label a)
        (a.2 x) (a.2 y) (a.2 y') (a.1 e) (a.1 f)
      simpa [score,positive,LevelScores.positive,rareException,hc,hg,RareScore.slot,RareScore.ind] using h
    · simp only [score,positive,rareException,hc,hg,not_false_eq_true,true_and,false_and,and_false,
        ite_eq_right,LevelScores.positive]
      norm_num [RareScore.ind] at *
      linarith

theorem pointwise [IsGalois ℚ K] (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : ε<1/2) (e f : E) (he : src e=src f)
    (hu : (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1)
    (hu' : (z (src f)-z (tgt f))*(w (src f)-w (tgt f))=1)
    (hy : z (tgt e)≠z (tgt f))
    (hm : z (src e)-z (tgt e)∈S) (hm' : z (src f)-z (tgt f)∈S)
    (hΔ : differenceProduct (z (src e)-z (tgt e)) (z (src f)-z (tgt f))∈S) :
    let a := snapshot S z w src tgt u
    let X := fun x b => RareScore.ind (rareException ε μ good label x (a b))
    let I := fun j b => RareScore.ind (¬CrossStructure.Consistent ((a b).1 j) ((a b).2 (src j)) ((a b).2 (tgt j)))
    let C := fun b => RareScore.ind (PlaceScore.common ε (frequency μ (a b)))
    let B := fun b => RareScore.ind (¬PlaceScore.common ε (frequency μ (a b)) ∧ ¬good (a b))
    2*(∫b,X (src e) b ∂LevelScale.measure S) ≤
      3*((∫b,X (tgt e) b ∂LevelScale.measure S)+(∫b,X (tgt f) b ∂LevelScale.measure S)+
        (∫b,I e b ∂LevelScale.measure S)+(∫b,I f b ∂LevelScale.measure S))+
      (∫b,C b ∂LevelScale.measure S)+(∫b,B b ∂LevelScale.measure S)+2*log 2 := by
  dsimp only
  let a := snapshot S z w src tgt u
  let X := fun x b => RareScore.ind (rareException ε μ good label x (a b))
  let I := fun j b => RareScore.ind (¬CrossStructure.Consistent ((a b).1 j) ((a b).2 (src j)) ((a b).2 (tgt j)))
  let C := fun b => RareScore.ind (PlaceScore.common ε (frequency μ (a b)))
  let B := fun b => RareScore.ind (¬PlaceScore.common ε (frequency μ (a b)) ∧ ¬good (a b))
  have hX (x) : Integrable (X x) (LevelScale.measure S) :=
    integrable_value S z w src tgt u (fun b => RareScore.ind (rareException ε μ good label x b))
  have hI (j) : Integrable (I j) (LevelScale.measure S) :=
    integrable_value S z w src tgt u (fun b => RareScore.ind (¬CrossStructure.Consistent (b.1 j) (b.2 (src j)) (b.2 (tgt j))))
  have hC : Integrable C (LevelScale.measure S) :=
    integrable_value S z w src tgt u (fun b => RareScore.ind (PlaceScore.common ε (frequency μ b)))
  have hB : Integrable B (LevelScale.measure S) :=
    integrable_value S z w src tgt u (fun b => RareScore.ind (¬PlaceScore.common ε (frequency μ b) ∧ ¬good b))
  have hsum := (((hX (tgt e)).add (hX (tgt f))).add (hI e)).add (hI f)
  have hlow := ((((hX (src e)).const_mul 2).sub (hsum.const_mul 3)).sub hC).sub hB
  have hlo := integral_mono hlow
    (integrable_value S z w src tgt u (score ε μ good label (src e) (tgt e) (tgt f) e f))
    (fun b => by simpa only [Pi.sub_apply,Pi.add_apply,X,I,C,B,←he] using lower_slot ε μ good label (src e) (tgt e) (tgt f) e f (a b))
  simp only [Pi.sub_apply,Pi.add_apply] at hlo
  rw [integral_sub _ hB,integral_sub _ hC,integral_sub,integral_const_mul,integral_const_mul,
    integral_add,integral_add,integral_add] at hlo
  · have hup := upper S z w src tgt u μ good label hε e f he hu hu' hy hm hm' hΔ
    change 2*(∫b,X (src e) b ∂LevelScale.measure S) ≤
      3*((∫b,X (tgt e) b ∂LevelScale.measure S)+(∫b,X (tgt f) b ∂LevelScale.measure S)+
        (∫b,I e b ∂LevelScale.measure S)+(∫b,I f b ∂LevelScale.measure S))+
      (∫b,C b ∂LevelScale.measure S)+(∫b,B b ∂LevelScale.measure S)+2*log 2
    linarith
  all_goals fun_prop
end
end PlanarUnitDistances.ActualRarePair

namespace PlanarUnitDistances.ActualHeights
open MeasureTheory FiniteLaw FiniteStarCoupling ActualProfiles ActualScoreBook LevelSnapshot
  ProfileBudget ScoreBook RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)
lemma center_nonneg (q : Q) : 0 ≤ center G q := by
  apply mul_nonneg G.mass_pos.le
  apply avg_nonneg
  intro d
  unfold ind
  split_ifs <;> norm_num
lemma mistake_nonneg (p : P) (q : Q) : 0 ≤ mistake G p q := by
  apply mul_nonneg G.mass_pos.le
  apply avg_nonneg
  intro d
  unfold ind
  split_ifs <;> norm_num
lemma center_average : avg (right G.graph) (center G)=mass G.support*G.book.HQ := by
  unfold center
  rw [avg_smul,avg_comm]
  congr 1
  unfold Book.HQ cut
  apply avg_congr
  intro d
  by_cases hd : G.book.R d
  · simp only [hd,↓reduceIte]
    rfl
  · simp only [hd,↓reduceIte,avg_const]
lemma mistake_average : avg G.graph (fun pq => mistake G pq.1 pq.2)=mass G.support*G.book.M := by
  unfold mistake
  rw [avg_smul,avg_comm]
  rfl
lemma point_integral (p : P) :
    (∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.point p) (G.snap b))
      ∂LevelScale.measure G.support)=height G p := by
  rw [height_eq]
  have hh := ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.point p) d))
  unfold Input.snap
  rw [hh]
  congr 1
  apply avg_congr
  intro d
  simp only [ActualSlots.rareException,LocalProfiles.X,LocalProfiles.exceptional,LocalProfiles.rareBit,
    ActualSlots.frequency,Input.book,make,Book.R,Book.C,GlobalScores.common,RareRows.frequency]
  unfold ind
  split_ifs <;> simp_all
lemma center_integral (q : Q) :
    (∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.center q) (G.snap b))
      ∂LevelScale.measure G.support)=center G q := by
  have hh := ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.center q) d))
  unfold Input.snap
  rw [hh]
  unfold center
  congr 1
  apply avg_congr
  intro d
  simp only [ActualSlots.rareException,LocalProfiles.exceptional,LocalProfiles.rareBit,
    ActualSlots.frequency,Input.book,make,Book.R,Book.C,GlobalScores.common,RareRows.frequency]
  unfold ind
  split_ifs <;> simp_all
lemma inconsistent_integral (p : P) (q : Q) :
    (∫b,ind (¬CrossStructure.Consistent ((G.snap b).1 (p,q)) ((G.snap b).2 (G.point p))
      ((G.snap b).2 (G.center q))) ∂LevelScale.measure G.support)=mistake G p q :=
  ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (¬CrossStructure.Consistent (d.1 (p,q)) (d.2 (G.point p)) (d.2 (G.center q))))
lemma common_integral :
    (∫b,ind (PlaceScore.common G.epsilon (ActualSlots.frequency G.graph (G.snap b)))
      ∂LevelScale.measure G.support)=mass G.support*G.book.WC :=
  ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (PlaceScore.common G.epsilon (ActualSlots.frequency G.graph d)))
lemma bad_integral :
    (∫b,ind (¬PlaceScore.common G.epsilon (ActualSlots.frequency G.graph (G.snap b)) ∧ ¬G.good (G.snap b))
      ∂LevelScale.measure G.support)=mass G.support*G.book.WB :=
  ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (¬PlaceScore.common G.epsilon (ActualSlots.frequency G.graph d) ∧ ¬G.good d))
theorem pointwise [IsGalois ℚ K] (hε : G.epsilon<1/2) (p : P) (q r : Q)
    (hu : (G.z (G.point p)-G.z (G.center q))*(G.w (G.point p)-G.w (G.center q))=1)
    (hur : (G.z (G.point p)-G.z (G.center r))*(G.w (G.point p)-G.w (G.center r))=1)
    (hy : G.z (G.center q)≠G.z (G.center r))
    (hm : G.z (G.point p)-G.z (G.center q)∈G.support)
    (hmr : G.z (G.point p)-G.z (G.center r)∈G.support)
    (hΔ : BudgetPlaces.differenceProduct (G.z (G.point p)-G.z (G.center q))
      (G.z (G.point p)-G.z (G.center r))∈G.support) :
    2*height G p≤3*(center G q+center G r+mistake G p q+mistake G p r)+
      mass G.support*(G.book.WC+G.book.WB)+2*Real.log 2 := by
  have hh := ActualRarePair.pointwise G.support G.z G.w (fun pq : P×Q => G.point pq.1)
    (fun pq : P×Q => G.center pq.2) G.shifts G.graph G.good G.label hε (p,q) (p,r)
    rfl hu hur hy hm hmr hΔ
  dsimp only at hh
  change 2*(∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.point p) (G.snap b))
      ∂LevelScale.measure G.support) ≤
    3*((∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.center q) (G.snap b)) ∂LevelScale.measure G.support)+
       (∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.center r) (G.snap b)) ∂LevelScale.measure G.support)+
       (∫b,ind (¬CrossStructure.Consistent ((G.snap b).1 (p,q)) ((G.snap b).2 (G.point p)) ((G.snap b).2 (G.center q))) ∂LevelScale.measure G.support)+
       (∫b,ind (¬CrossStructure.Consistent ((G.snap b).1 (p,r)) ((G.snap b).2 (G.point p)) ((G.snap b).2 (G.center r))) ∂LevelScale.measure G.support))+
    (∫b,ind (PlaceScore.common G.epsilon (ActualSlots.frequency G.graph (G.snap b))) ∂LevelScale.measure G.support)+
    (∫b,ind (¬PlaceScore.common G.epsilon (ActualSlots.frequency G.graph (G.snap b)) ∧ ¬G.good (G.snap b)) ∂LevelScale.measure G.support)+2*Real.log 2 at hh
  rw [point_integral,center_integral,center_integral,inconsistent_integral,inconsistent_integral,
    common_integral,bad_integral] at hh
  linarith
end
end PlanarUnitDistances.ActualHeights

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Tails
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceCoercivity
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters
  EnvelopeCoercivity
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
variable (R : Realization s a i)

attribute [local instance] OAI.PlanarUnitDistances.IncidenceCoercivity.instFintypeSumSubtypePlaneMemFinsetPQ
local instance instFintypeProdSubtypePlaneMemFinsetPQ_rc2410d_1 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
attribute [local instance] OAI.PlanarUnitDistances.IncidenceCoercivity.instFintypeForallSumSubtypePlaneMemFinsetPQBool
theorem bounds {C L : ℝ} (hC : 0<C) (hL : 0<L) (hv : R.Valid C L) (hscale : 0<scale s i) :
    R.book.CQ ≤ 250000*BookEnvelope.total a C (27/50) (1/25) (s.ξ i) (noise s a i)*R.book.S ∧
    R.book.S ≤ pointConstant L*R.book.HP+
      lossConstant L*BookEnvelope.total a C (27/50) (1/25) (s.ξ i) (noise s a i)*R.book.S ∧
    R.book.CQ+R.book.WB+8*R.book.J+8*R.book.M+2*WedgeSummary.JW R.book ≤
      errorCoefficient a C (s.ξ i) (noise s a i)*R.book.S := by
  obtain ⟨hM,hWC,hWB,hH,hJ,hEP,hDP,hDQ,hDT,hT⟩ := IncidenceEstimates.upper R hC hv hscale
  have hh := EnvelopeCoercivity.bounds R.book a hC hL.le (s.good i).error_nonneg
    (IncidenceNoise.nonneg s a i) (positive s i) (positiveQ s i)
    hv.2.2.2.2.1 hv.2.2.2.2.2.1 hM hWC hWB hJ hEP hDP hDQ hDT hT
  refine ⟨hh.1,hh.2.2,?_⟩
  have hw := hv.2.2.2.2.2.2.2.2.2.2.1
  have hc : 0 ≤ a.d+BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i)/Real.sqrt a.d := by
    have hd := a.d_pos
    have he := a.epsilon_pos
    have hx := (s.good i).error_nonneg
    unfold BudgetParameters.joint
    positivity
  have hn := R.book.nonneg
  have hp : R.book.HP ≤ BookEnvelope.height C (noise s a i)*R.book.S := by linarith [hn.2.2.2.1]
  have hw' := hw.trans (mul_le_mul_of_nonneg_left hp hc)
  unfold errorCoefficient
  nlinarith

omit R in
theorem error_limit (s : Sequence) (a : Params) (C : ℝ) :
    Tendsto (fun i => errorCoefficient a C (s.ξ i) (noise s a i)) atTop
      (nhds (250000*leading a C (27/50) (1/25)+
        4*BudgetParameters.joint C (27/50) (1/25) a.epsilon 0*C+2*BudgetParameters.wedge a C (27/50) (1/25))) := by
  have hr := IncidenceNoise.limit s a
  have ht := BookEnvelope.total_limit a C (27/50) (1/25) (s.ξ) (noise s a) s.error_limit hr
  have hj : Tendsto (fun i => BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i)) atTop
      (nhds (BudgetParameters.joint C (27/50) (1/25) a.epsilon 0)) :=
    (tendsto_const_nhds.add s.error_limit).div_const _
  have hh : Tendsto (fun i => BookEnvelope.height C (noise s a i)) atTop (nhds C) := by
    simpa only [BookEnvelope.height,add_zero,mul_one] using ((tendsto_const_nhds (x:=1)).add hr).const_mul C
  have h := ((((ht.const_mul 250000).add (hr.div_const a.epsilon)).add
    (((hj.div_const 2).mul hh).const_mul 8)).add (hr.const_mul 8)).add
      (((((tendsto_const_nhds (x:=a.d)).add (hj.div_const (Real.sqrt a.d))).mul hh)).const_mul 2)
  convert h using 1
  · funext i
    unfold errorCoefficient BookEnvelope.j
    ring
  · unfold BudgetParameters.wedge
    ring_nf

omit R in
lemma leading_joint (a : Params) {C : ℝ} (hC : 0<C) :
    4*BudgetParameters.joint C (27/50) (1/25) a.epsilon 0*C ≤ leading a C (27/50) (1/25) := by
  have he := a.epsilon_pos
  have hd := a.delta_pos
  have ha := a.eta_pos
  have hz := a.zeta_pos
  have hs := BookEnvelope.sampling_nonneg a
  have hj : 0≤BudgetParameters.joint C (27/50) (1/25) a.epsilon 0 := by unfold BudgetParameters.joint; positivity
  unfold leading
  have hq : 0≤(96*a.eta+20*a.delta+24*CommonTemplate.samplingError a.k (a.eta^2)+
    (12*(a.k:ℝ)/a.zeta+20/a.delta)*4/(a.m:ℝ))/a.epsilon := by positivity
  nlinarith
end
end PlanarUnitDistances.IncidenceCoercivity

namespace PlanarUnitDistances.IncidenceRare
open Filter FiniteLaw FiniteStarCoupling ScoreBook IncidenceSequence IncidenceScale
  IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters EnvelopeCoercivity
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}

local instance instFintypeSumSubtypePlaneMemFinsetPQ_rc2410d_1 : Fintype (s.P i⊕s.Q i) := inferInstance
local instance instFintypeProdSubtypePlaneMemFinsetPQ_rc2410d_2 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
local instance instFintypeForallSumSubtypePlaneMemFinsetPQBool_rc2410d_1 : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
theorem prepare (s : Sequence) : ∃c C : ℝ,0<c ∧ 0<C ∧
    ∀τ : ℝ,0<τ → ∃a : Params,∀ᶠi in atTop,∃R : Realization s a i,Ready R c C τ := by
  obtain ⟨s₀,C,L,hs,hC,hL,hbook⟩ := IncidenceBook.constants s
  let pc := pointConstant L
  let lc := lossConstant L
  have hpc : 0<pc := by dsimp [pc,pointConstant]; positivity
  have hlc : 0<lc := by dsimp [lc,lossConstant]; positivity
  refine ⟨1/(2*pc),2*C,by positivity,by positivity,?_⟩
  intro τ hτ
  let ρ := min (1/(4*lc)) (τ/500010)
  have hρ : 0<ρ := lt_min (by positivity) (by positivity)
  obtain ⟨a,ha,hlead,hwedge⟩ := BudgetParameters.exists_small hC
    (by norm_num : (0:ℝ)<27/50) (by norm_num : (0:ℝ)<1/25) hs hρ
  have ha' : 2*a.epsilon ≤ s₀ := by linarith
  have ht := BookEnvelope.total_limit a C (27/50) (1/25) (s.ξ) (noise s a) s.error_limit (IncidenceNoise.limit s a)
  have herrlim := IncidenceCoercivity.error_limit s a C
  have herror : 250000*leading a C (27/50) (1/25)+
      4*BudgetParameters.joint C (27/50) (1/25) a.epsilon 0*C+2*BudgetParameters.wedge a C (27/50) (1/25)<τ := by
    have hj := IncidenceCoercivity.leading_joint a hC
    have hr : ρ≤τ/500010 := min_le_right _ _
    have hh : 500010*ρ≤τ := by have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<500010)).mp hr; linarith
    linarith
  refine ⟨a,?_⟩
  filter_upwards [hbook a ha',(scale_limit s).eventually_gt_atTop 0,
    ht.eventually_lt_const (show leading a C (27/50) (1/25)<2*ρ by linarith),
    herrlim.eventually_le_const herror,(IncidenceNoise.limit s a).eventually_le_const (by norm_num : (0:ℝ)<1)]
      with i hi hscale htotal herr hnoise
  obtain ⟨R,hR⟩ := hi
  have hu := IncidenceEstimates.upper R hC hR hscale
  have hc := IncidenceCoercivity.bounds R hC hL hR hscale
  have hS := R.book.nonneg.1
  have hE : lc*BookEnvelope.total a C (27/50) (1/25) (s.ξ i) (noise s a i)≤1/2 := by
    have hr : ρ≤1/(4*lc) := min_le_left _ _
    have hh : ρ*(4*lc)≤1 := (le_div_iff₀ (by positivity : 0<4*lc)).mp hr
    nlinarith [mul_le_mul_of_nonneg_left htotal.le hlc.le]
  have hp := EnvelopeCoercivity.positive_fraction hL.le hS hc.2.1 hE
  have hm := R.mass_pos.le
  have heq := hR.2.1
  refine ⟨R,hR.1,heq,hR.2.2.1,hR.2.2.2.2.2.2.1,hR.2.2.2.2.2.2.2.1,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hp hm
    calc
      1/(2*pc)*scale s i=mass (model s i).support*(R.book.S/(2*pc)) := by rw [←heq]; ring
      _ ≤ _ := hh
  · have hh := mul_le_mul_of_nonneg_left hu.2.2.2.1 hm
    have hc' : BookEnvelope.height C (noise s a i)≤2*C := by unfold BookEnvelope.height; nlinarith
    calc
      _ ≤ mass (model s i).support*(BookEnvelope.height C (noise s a i)*R.book.S) := hh
      _ = BookEnvelope.height C (noise s a i)*scale s i := by rw [←heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc' hscale.le
  · calc
      _ ≤ mass (model s i).support*(IncidenceCoercivity.errorCoefficient a C (s.ξ i) (noise s a i)*R.book.S) := mul_le_mul_of_nonneg_left hc.2.2 hm
      _ = IncidenceCoercivity.errorCoefficient a C (s.ξ i) (noise s a i)*scale s i := by rw [←heq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right herr hscale.le
end
end PlanarUnitDistances.IncidenceRare

namespace PlanarUnitDistances.IncidenceHeights
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceRare ActualScoreBook ActualProfiles ProfileBudget
open scoped Classical
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}
variable (R : Realization s a i)

local instance instFintypeSumSubtypePlaneMemFinsetPQ_rc2410d_2 : Fintype (s.P i⊕s.Q i) := inferInstance
lemma Z_nonneg (x) : 0≤Z R x := add_nonneg (error_nonneg R.input true x) (error_nonneg R.input false x)

local instance instFintypeProdSubtypePlaneMemFinsetPQ_rc2410d_3 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
theorem averages {c C τ : ℝ} (hR : Ready R c C τ) :
    c*scale s i≤avg (left (graph s i)) (height R.input) ∧
    avg (left (graph s i)) (height R.input)≤C*scale s i ∧
    avg (right (graph s i)) (ActualHeights.center R.input)≤C*scale s i ∧
    avg (graph s i) (fun pq => ActualHeights.mistake R.input pq.1 pq.2)≤2*Real.log 2+4 ∧
    avg (WedgeLaw.law (graph s i)) (Z R)≤τ*scale s i := by
  obtain ⟨_,_,hm,_,_,hp,hH,he⟩ := hR
  have hn := R.book.nonneg
  have hmass := R.mass_pos.le
  have hPa := height_average R.input
  have hQa := ActualHeights.center_average R.input
  have hMa := ActualHeights.mistake_average R.input
  have hE₁ := residual_budget R.input
  have hE₂ := size_budget R.input
  change avg (left (graph s i)) (height R.input)=mass (model s i).support*R.book.HP at hPa
  change avg (right (graph s i)) (ActualHeights.center R.input)=mass (model s i).support*R.book.HQ at hQa
  change avg (graph s i) (fun pq => ActualHeights.mistake R.input pq.1 pq.2)=mass (model s i).support*R.book.M at hMa
  change avg (WedgeLaw.law (graph s i)) (error R.input true)≤ mass (model s i).support*(R.book.CQ+R.book.WB+4*R.book.J+4*R.book.M) at hE₁
  change avg (WedgeLaw.law (graph s i)) (error R.input false)≤ mass (model s i).support*(2*WedgeSummary.JW R.book+4*R.book.J+4*R.book.M) at hE₂
  refine ⟨?_,?_,?_,?_,?_⟩
  · rwa [hPa]
  · rw [hPa]
    nlinarith [mul_nonneg hmass hn.2.2.2.1]
  · rw [hQa]
    nlinarith [mul_nonneg hmass hn.2.2.1]
  · rwa [hMa]
  · change avg (WedgeLaw.law (graph s i)) (fun x => error R.input true x+error R.input false x)≤_
    rw [avg_add]
    nlinarith

lemma row_support (p : s.P i) (q : s.Q i) (h : (row (graph s i) p).val q≠0) :
    GeometricLaw.E (s.P i) (s.Q i) p q := by
  apply support s i p q
  rw [←row_weight]
  exact mul_pos (positive s i p) (lt_of_le_of_ne ((row (graph s i) p).nonneg q) (Ne.symm h))

theorem pointwise (p : s.P i) (q r : s.Q i) (hqr : q≠r)
    (hq : (row (graph s i) p).val q≠0) (hr : (row (graph s i) p).val r≠0) :
    2*height R.input p≤3*(ActualHeights.center R.input q+ActualHeights.center R.input r+
      ActualHeights.mistake R.input p q+ActualHeights.mistake R.input p r)+
      mass (model s i).support*(R.book.WC+R.book.WB)+2*Real.log 2 := by
  let M := model s i
  exact ActualHeights.pointwise R.input a.epsilon_lt p q r
    (M.unit_identity p q (row_support p q hq)) (M.unit_identity p r (row_support p r hr))
    (M.center_injective.ne hqr) (M.sub_mem (.inl p) (.inr q)) (M.sub_mem (.inl p) (.inr r))
    (M.difference_mem (.inl p) (.inr q) (.inr r))

theorem baseline {c C τ : ℝ} (hR : Ready R c C τ) :
    mass (model s i).support*(R.book.WC+R.book.WB)+2*Real.log 2≤
      scale s i/a.epsilon+(2*Real.log 2+4)/a.epsilon+2*Real.log 2 := by
  obtain ⟨_,hs,hm,hc,hb,_⟩ := hR
  have hmass := R.mass_pos.le
  have hc' := mul_le_mul_of_nonneg_left hc hmass
  have hb' := mul_le_mul_of_nonneg_left hb hmass
  have hm' := div_le_div_of_nonneg_right hm a.epsilon_pos.le
  dsimp only [Realization.common_bound,Realization.bad_bound,Realization.mistake_bound] at *
  rw [←mul_div_assoc,hs] at hc'
  rw [←mul_div_assoc] at hb'
  nlinarith
end
end PlanarUnitDistances.IncidenceHeights

namespace PlanarUnitDistances.TailControl
open Finset MeasureTheory Set
open scoped BigOperators

lemma layer_apply (a t : ℝ) : layer a t = if 0 < t ∧ t ≤ a then 1 else 0 := by
  classical
  simp [layer, Set.indicator_apply]

lemma layer_integrable (a : ℝ) : Integrable (layer a) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma integral_layer {a : ℝ} (ha : 0 ≤ a) : ∫ t, layer a t = a := by
  change (∫ t, (Ioc 0 a).indicator (fun _ : ℝ => (1 : ℝ)) t) = a
  rw [integral_indicator measurableSet_Ioc, integral_const]
  simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal ha]

lemma layer_nonneg (a t : ℝ) : 0 ≤ layer a t := by
  simp only [layer_apply]; split_ifs <;> norm_num

section Finite
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma tails_integrable (μ a : P → ℝ) : Integrable (tails μ a) := by
  exact integrable_finsetSum _ (fun p _ => (layer_integrable (a p)).const_mul (μ p))

lemma integral_tails (μ a : P → ℝ) (ha : ∀ p, 0 ≤ a p) :
    ∫ t, tails μ a t = ∑ p, μ p * a p := by
  unfold tails
  rw [integral_finsetSum _ (fun p _ => (layer_integrable (a p)).const_mul (μ p))]
  simp only [integral_const_mul, integral_layer (ha _)]

lemma tails_nonneg (μ a : P → ℝ) (hμ : ∀ p, 0 ≤ μ p) (t : ℝ) : 0 ≤ tails μ a t :=
  sum_nonneg (fun p _ => mul_nonneg (hμ p) (layer_nonneg _ _))

lemma tails_eq_mass (μ a : P → ℝ) {t : ℝ} (ht : 0 < t) :
    tails μ a t = mass μ (univ.filter (fun p => t ≤ a p)) := by
  classical
  simp only [tails, mass, sum_filter, layer_apply, ht, true_and]
  apply sum_congr rfl
  intro p _
  split_ifs <;> simp

lemma tails_eq_zero (μ a : P → ℝ) {t : ℝ} (ht : ¬0 < t) : tails μ a t = 0 := by
  simp [tails, layer_apply, ht]

lemma pairTails_integrable (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ) :
    Integrable (pairTails w a b) := by
  exact integrable_finsetSum _ (fun p _ => integrable_finsetSum _
    (fun q _ => (layer_integrable _).const_mul _))

lemma integral_pairTails (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ)
    (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q) :
    ∫ t, pairTails w a b t = ∑ p, ∑ q, w p q * min (a p) (b q) := by
  unfold pairTails
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _
    (fun q _ => (layer_integrable _).const_mul _))]
  apply sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => (layer_integrable _).const_mul _)]
  simp only [integral_const_mul, integral_layer (le_min (ha _) (hb _))]

lemma pairTails_eq_rectangle (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ)
    {t : ℝ} (ht : 0 < t) :
    pairTails w a b t =
      ∑ p ∈ univ.filter (fun p => t ≤ a p), ∑ q ∈ univ.filter (fun q => t ≤ b q), w p q := by
  classical
  simp only [pairTails, sum_filter, layer_apply, ht, true_and, le_min_iff]
  apply sum_congr rfl
  intro p _
  by_cases hp : t ≤ a p
  · simp only [hp, true_and, ↓reduceIte]
    apply sum_congr rfl
    intro q _
    split_ifs <;> simp
  · simp [hp]

lemma pairTails_eq_zero (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ)
    {t : ℝ} (ht : ¬0 < t) : pairTails w a b t = 0 := by
  simp [pairTails, layer_apply, ht]

lemma layer_young {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    θ * Real.sqrt (x*y) ≤ x/24 + 6*θ^2*y := by
  rw [Real.sqrt_mul hx]
  nlinarith [sq_nonneg (Real.sqrt x - 12*θ*Real.sqrt y),
    Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem capped_expectation (w : P → Q → ℝ) (μ : P → ℝ) (κ : Q → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hκ : ∀ q, 0 ≤ κ q)
    (a : P → ℝ) (b : Q → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q)
    (T : Finset P) (hzero : ∀ p, p ∉ T → a p = 0) (θ : ℝ)
    (hexp : ∀ F : Finset P, F ⊆ T → ∀ G : Finset Q,
      (∑ p ∈ F, ∑ q ∈ G, w p q) ≤ θ * Real.sqrt (mass μ F * mass κ G)) :
    (∑ p, ∑ q, w p q * min (a p) (b q)) ≤
      (∑ p, μ p * a p)/24 + 6*θ^2*(∑ q, κ q * b q) := by
  classical
  have hpoint (t : ℝ) : pairTails w a b t ≤ tails μ a t / 24 + 6*θ^2*tails κ b t := by
    by_cases ht : 0 < t
    · have hsub : univ.filter (fun p => t ≤ a p) ⊆ T := by
        intro p hp
        by_contra hn
        have hp' := (mem_filter.mp hp).2
        rw [hzero p hn] at hp'
        exact (not_le_of_gt ht) hp'
      have he := hexp _ hsub (univ.filter (fun q => t ≤ b q))
      rw [← pairTails_eq_rectangle w a b ht, ← tails_eq_mass μ a ht,
        ← tails_eq_mass κ b ht] at he
      exact he.trans (layer_young (tails_nonneg μ a hμ t) (tails_nonneg κ b hκ t))
    · simp only [pairTails_eq_zero _ _ _ ht, tails_eq_zero _ _ ht]
      norm_num
  have hint := integral_mono (pairTails_integrable w a b)
    ((tails_integrable μ a).div_const 24 |>.add ((tails_integrable κ b).const_mul (6*θ^2))) hpoint
  change (∫ t, pairTails w a b t) ≤ (∫ t, tails μ a t / 24 + 6*θ^2*tails κ b t) at hint
  rw [integral_pairTails w a b ha hb, integral_add
    ((tails_integrable μ a).div_const 24) ((tails_integrable κ b).const_mul _),
    integral_div, integral_const_mul, integral_tails μ a ha, integral_tails κ b hb] at hint
  exact hint

lemma average_distinct (π c : Q → ℝ) (hπ : ∀ q, 0 ≤ π q)
    (hs : ∑ q, π q = 1) (hmax : ∀ q, π q ≤ 1/2) (hc : ∀ q, 0 ≤ c q)
    {a : ℝ} (ha : 0 ≤ a)
    (hcap : ∀ q r, q ≠ r → π q ≠ 0 → π r ≠ 0 → a ≤ 3*(c q+c r)) :
    a/2 ≤ 6 * ∑ q, π q*c q := by
  classical
  have hcoll : ∑ q, π q*π q ≤ 1/2 := by
    calc
      _ ≤ ∑ q, π q*(1/2) := sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hmax q) (hπ q))
      _ = 1/2 := by rw [← sum_mul, hs]; norm_num
  have hp (q r : Q) : π q*π r*a ≤
      3*(π q*π r*c q+π q*π r*c r) + if q=r then π q*π r*a else 0 := by
    by_cases hqr : q = r
    · simp only [hqr, ↓reduceIte]
      nlinarith [mul_nonneg (mul_nonneg (hπ r) (hπ r)) (hc r)]
    · simp only [hqr, ↓reduceIte, add_zero]
      by_cases hq : π q = 0
      · simp [hq]
      by_cases hr : π r = 0
      · simp [hr]
      have hh := mul_le_mul_of_nonneg_left (hcap q r hqr hq hr) (mul_nonneg (hπ q) (hπ r))
      nlinarith
  have hh := sum_le_sum (s := univ) (fun q _ => sum_le_sum (s := univ) (fun r _ => hp q r))
  have he (q : Q) : (∑ r, π q*π r*a) = π q*a := by
    calc
      _ = π q*a * ∑ r, π r := by rw [mul_sum]; apply sum_congr rfl; intro r _; ring
      _ = _ := by rw [hs, mul_one]
  have he₁ (q : Q) : (∑ r, π q*π r*c q) = π q*c q := by
    calc
      _ = π q*c q * ∑ r, π r := by rw [mul_sum]; apply sum_congr rfl; intro r _; ring
      _ = _ := by rw [hs, mul_one]
  have he₂ (q : Q) : (∑ r, π q*π r*c r) = π q*(∑ r, π r*c r) := by
    rw [mul_sum]; apply sum_congr rfl; intro r _; ring
  simp only [sum_add_distrib, ← mul_sum, he, he₁, he₂, sum_ite_eq] at hh
  rw [← sum_mul, hs, one_mul, ← sum_mul, hs, one_mul] at hh
  simp only [Finset.mem_univ, ite_true] at hh
  rw [← sum_mul] at hh
  nlinarith [mul_le_mul_of_nonneg_right hcoll ha]

theorem finite_tail_bound (μ : P → ℝ) (κ : Q → ℝ) (π m : P → Q → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hκ : ∀ q, 0 ≤ κ q)
    (hπ : ∀ p q, 0 ≤ π p q) (hsπ : ∀ p, ∑ q, π p q = 1)
    (hmπ : ∀ p q, π p q ≤ 1/2) (hm : ∀ p q, 0 ≤ m p q)
    (a : P → ℝ) (b : Q → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ q, 0 ≤ b q)
    (T : Finset P) (θ : ℝ)
    (hcap : ∀ p ∈ T, ∀ q r, q ≠ r → π p q ≠ 0 → π p r ≠ 0 →
      a p ≤ 3*(min (a p) (b q)+min (a p) (b r)+m p q+m p r))
    (hexp : ∀ F : Finset P, F ⊆ T → ∀ G : Finset Q,
      (∑ p ∈ F, ∑ q ∈ G, μ p*π p q) ≤ θ * Real.sqrt (mass μ F * mass κ G)) :
    (∑ p, μ p * capped a T p) ≤ 144*θ^2*(∑ q, κ q*b q) +
      24*(∑ p, ∑ q, μ p*π p q*m p q) := by
  classical
  have hz (p : P) : 0 ≤ capped a T p := by simp only [capped]; split_ifs; exact ha p; positivity
  have hrow (p : P) : capped a T p / 2 ≤
      6 * ∑ q, π p q * (min (capped a T p) (b q) + m p q) := by
    apply average_distinct (π p) (fun q => min (capped a T p) (b q)+m p q)
      (hπ p) (hsπ p) (hmπ p) (fun q => add_nonneg (le_min (hz p) (hb q)) (hm p q)) (hz p)
    intro q r hqr hq hr
    by_cases hp : p ∈ T
    · simp only [capped, hp, ↓reduceIte]
      linarith [hcap p hp q r hqr hq hr]
    · simp only [capped, hp, ↓reduceIte, min_eq_left (hb q), min_eq_left (hb r), zero_add]
      exact mul_nonneg (by norm_num) (add_nonneg (hm p q) (hm p r))
  have havg := sum_le_sum (s := univ) (fun p _ => mul_le_mul_of_nonneg_left (hrow p) (hμ p))
  have havg' : (∑ p, μ p*capped a T p)/2 ≤
      6*(∑ p, ∑ q, μ p*π p q*min (capped a T p) (b q)) +
      6*(∑ p, ∑ q, μ p*π p q*m p q) := by
    have heq : (∑ p, μ p * (6 * ∑ q, π p q * (min (capped a T p) (b q) + m p q))) =
        6*(∑ p, ∑ q, μ p*π p q*min (capped a T p) (b q)) +
          6*(∑ p, ∑ q, μ p*π p q*m p q) := by
      calc
        _ = ∑ p, ∑ q, (6*(μ p*π p q*min (capped a T p) (b q)) +
            6*(μ p*π p q*m p q)) := by
          apply sum_congr rfl
          intro p _
          rw [← mul_assoc, mul_sum]
          apply sum_congr rfl
          intro q _
          ring
        _ = _ := by simp only [sum_add_distrib, ← mul_sum]
    rw [heq] at havg
    simpa only [mul_div_assoc, sum_div] using havg
  have hmin := capped_expectation (fun p q => μ p*π p q) μ κ hμ hκ (capped a T) b hz hb
    T (fun p hp => by simp [capped, hp]) θ hexp
  linarith

end Finite
end PlanarUnitDistances.TailControl

namespace PlanarUnitDistances.LawTail
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
lemma capped_pointwise {a b c e f B : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (he : 0≤e) (hf : 0≤f) (hB : B≤a) (h : 2*a≤3*(b+c+e+f)+B) :
    a≤3*(min a b+min a c+e+f) := by
  by_cases h₁ : a≤b
  · rw [min_eq_left h₁]
    have hv : 0≤ min a c := le_min ha hc
    linarith
  · by_cases h₂ : a≤c
    · rw [min_eq_left h₂]
      have hv : 0≤ min a b := le_min ha hb
      linarith
    · rw [min_eq_right (le_of_not_ge h₁),min_eq_right (le_of_not_ge h₂)]
      linarith

theorem estimate (π : Law (P×Q)) (U : Law P) (V : Law Q) (a : P → ℝ) (b : Q → ℝ)
    (m : P → Q → ℝ) {γ η ξ C S R B M : ℝ}
    (hγ : 0<γ) (hη : 0≤η) (hξ : 0≤ξ) (_hC : 0≤C) (hS : 0<S) (hR : 0<R)
    (hμ : ∀p,γ*U.val p≤(left π).val p) (hκ : ∀q,γ*V.val q≤(right π).val q)
    (hexp : ∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event V (fun q => q∈G))*
        ((event U (fun p => p∈F)*event V (fun q => q∈G))^η+ξ))
    (ha : ∀p,0≤a p) (hb : ∀q,0≤b q) (hm : ∀p q,0≤ m p q)
    (hrow : ∀p q,(row π p).val q≤1/2)
    (hmean : avg (left π) a≤C*S) (hmeanQ : avg (right π) b≤C*S)
    (hmmean : avg π (fun pq => m pq.1 pq.2)≤M) (hbase : B≤R*S)
    (hp : ∀p q r,q≠r → (row π p).val q≠0 → (row π p).val r≠0 →
      2*a p≤3*(b q+b r+m p q+m p r)+B) :
    avg (left π) (fun p => if R*S<a p then a p else 0)≤
      144*((((C/R)/γ)^η+ξ)/γ)^2*(C*S)+24*M := by
  let T := univ.filter (fun p => R*S<a p)
  have hT : event (left π) (fun p => p∈T)≤C/R := by
    rw [←LawExpansion.mass_event]
    exact ExpansionConsequences.height_tail_mass (left π).val a (left π).nonneg ha hS hR hmean
  have he (F : Finset P) (hF : F⊆T) (G : Finset Q) :
      (∑p∈F,∑q∈G,(left π).val p*(row π p).val q)≤
        ((((C/R)/γ)^η+ξ)/γ)*Real.sqrt
          (TailControl.mass (left π).val F*TailControl.mass (right π).val G) := by
    simp_rw [row_weight]
    change ExpansionConsequences.rect (fun p q => π.val (p,q)) F G≤_
    rw [LawExpansion.rect_event]
    change _≤((((C/R)/γ)^η+ξ)/γ)*Real.sqrt
      (ExpansionConsequences.mass (left π).val F*ExpansionConsequences.mass (right π).val G)
    rw [LawExpansion.mass_event,LawExpansion.mass_event]
    exact LawRare.small_rect π U V hγ hη hξ hμ hκ hexp F G
      ((event_mono (left π) (fun _ h => hF h)).trans hT)
  have ht := TailControl.finite_tail_bound (left π).val (right π).val
    (fun p q => (row π p).val q) m (left π).nonneg (right π).nonneg
    (fun p => (row π p).nonneg) (fun p => (row π p).total) hrow hm a b ha hb T
    ((((C/R)/γ)^η+ξ)/γ) (fun p hpT q r hqr hq hr =>
      capped_pointwise (ha p) (hb q) (hb r) (hm p q) (hm p r)
        (hbase.trans (mem_filter.mp hpT).2.le) (hp p q r hqr hq hr)) he
  have hM : (∑p,∑q,(left π).val p*(row π p).val q*m p q)=avg π (fun pq => m pq.1 pq.2) := by
    simp only [row_weight,avg,Fintype.sum_prod_type]
  rw [hM] at ht
  have heq : (∑p,(left π).val p*TailControl.capped a T p)=
      avg (left π) (fun p => if R*S<a p then a p else 0) := by
    simp only [avg,TailControl.capped,T,mem_filter,mem_univ,true_and]
  rw [heq] at ht
  have h₁ := mul_le_mul_of_nonneg_left hmeanQ (by positivity : 0≤144*((((C/R)/γ)^η+ξ)/γ)^2)
  simp only [avg] at ht h₁ hmmean ⊢
  linarith
end
end PlanarUnitDistances.LawTail

namespace PlanarUnitDistances.AccurateBand
open FiniteLaw Finset
open scoped Classical BigOperators
noncomputable section
variable {X : Type*} [Fintype X]

lemma weighted_kept (μ : Law X) (W Z : X → ℝ) {L U δ : ℝ}
    (hW : ∀x,0≤W x) (hZ : ∀x,0≤Z x) (hL : 0≤L) (hδ : 0<δ) :
    avg μ W-avg μ Z/δ-L-avg μ (fun x => if U<W x then W x else 0) ≤
      avg μ (fun x => if kept W Z L U δ x then W x else 0) := by
  have h := avg_mono μ (f := fun x => W x-Z x/δ-L-(if U<W x then W x else 0))
    (g := fun x => if kept W Z L U δ x then W x else 0) (fun x => by
      have hz := div_nonneg (hZ x) hδ.le
      by_cases ha : kept W Z L U δ x
      · simp only [ha,↓reduceIte]
        split_ifs <;> linarith [hW x]
      · simp only [ha,↓reduceIte]
        by_cases ht : U<W x
        · simp only [ht,↓reduceIte]; linarith
        · simp only [ht,↓reduceIte,sub_zero]
          have hu := le_of_not_gt ht
          by_cases hl : L≤W x
          · have he : δ*W x<Z x := lt_of_not_ge (fun he => ha ⟨hl,hu,he⟩)
            have hw : W x<Z x/δ := (lt_div_iff₀ hδ).mpr (by nlinarith)
            linarith
          · linarith)
  simpa only [avg_sub,avg_const,div_eq_mul_inv,←avg_smul,mul_comm] using h

lemma kept_probability (μ : Law X) (W Z : X → ℝ) {L U δ : ℝ} (_hU : 0≤U) :
    avg μ (fun x => if kept W Z L U δ x then W x else 0) ≤
      U*event μ (kept W Z L U δ) := by
  unfold event
  rw [←avg_smul]
  apply avg_mono
  intro x
  by_cases h : kept W Z L U δ x
  · simpa only [h,ite_eq_left,mul_one] using h.2.1
  · simp [h]

lemma dyadic_cover {L U W : ℝ} {N : ℕ} (hL : 0<L) (hLW : L≤W)
    (hWU : W≤U) (hU : U<L*2^N) :
    ∃j : Fin N, L*2^(j:ℕ)≤W ∧ W≤2*(L*2^(j:ℕ)) := by
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near ((one_le_div hL).mpr hLW) (by norm_num : (1:ℝ)<2)
  have hjN : j<N := by
    by_contra hn
    have hm := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (le_of_not_gt hn)
    have ht : L*2^j≤W := by have ht := (le_div_iff₀ hL).mp hj; nlinarith
    nlinarith
  refine ⟨⟨j,hjN⟩,?_,?_⟩
  · have ht := (le_div_iff₀ hL).mp hj
    nlinarith
  · have ht := (div_lt_iff₀ hL).mp hj'
    rw [pow_succ] at ht
    nlinarith

lemma exists_cover_piece (μ : Law X) {Y : Type*} [Fintype Y] [Nonempty Y]
    (A : X → Prop) (B : Y → X → Prop) (hcover : ∀x,A x → ∃y,B y x) :
    ∃y,event μ A/(Fintype.card Y:ℝ) ≤ event μ (B y) := by
  have h : event μ A ≤ ∑y,event μ (B y) := by
    calc
      _ ≤ avg μ (fun x => ∑y,if B y x then 1 else 0) := by
        apply avg_mono
        intro x
        by_cases ha : A x
        · obtain ⟨y,hy⟩ := hcover x ha
          simp only [ha,↓reduceIte]
          have hh := single_le_sum (s := univ) (f := fun y => if B y x then (1:ℝ) else 0)
            (fun y _ => by split_ifs <;> norm_num) (mem_univ y)
          simpa only [hy,ite_eq_left] using hh
        · simp only [ha,↓reduceIte]
          exact sum_nonneg fun y _ => by split_ifs <;> norm_num
      _ = _ := by simp only [avg,event,mul_sum]; rw [sum_comm]
  by_contra hn
  have ht : ∀y,event μ (B y)<event μ A/(Fintype.card Y:ℝ) := by
    simpa only [not_exists,not_le] using hn
  have hh := sum_lt_sum_of_nonempty (s := univ) univ_nonempty (fun y _ => ht y)
  have hc : (Fintype.card Y:ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Y≠0)
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_div_cancel₀ _ hc] at hh
  linarith

theorem select (μ : Law X) (W Z : X → ℝ) {L U δ m : ℝ} {N : ℕ}
    (hW : ∀x,0≤W x) (hZ : ∀x,0≤Z x) (hL : 0<L) (hU : 0<U)
    (hδ : 0<δ) (hLU : L≤U) (hN : 0<N) (hUN : U<L*2^N)
    (hm : m≤avg μ W-avg μ Z/δ-L-avg μ (fun x => if U<W x then W x else 0)) :
    ∃J,L≤J ∧ J≤U ∧ m/(U*N)≤event μ (fun x => J≤W x ∧ W x≤2*J ∧ Z x≤δ*W x) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let A := kept W Z L U δ
  let B (j : Fin N) (x : X) := A x ∧ L*2^(j:ℕ)≤W x ∧ W x≤2*(L*2^(j:ℕ))
  obtain ⟨j,hj⟩ := exists_cover_piece μ A B (fun x hx => by
    obtain ⟨j,hj⟩ := dyadic_cover hL hx.1 hx.2.1 hUN
    exact ⟨j,hx,hj⟩)
  have hmass : m≤U*event μ A := (hm.trans (weighted_kept μ W Z hW hZ hL.le hδ)).trans
    (kept_probability μ W Z hU.le)
  have hc : (0:ℝ)<N := by exact_mod_cast hN
  have hp : m/(U*N)≤event μ (B j) := by
    simp only [Fintype.card_fin] at hj
    apply le_trans _ hj
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right ((div_le_iff₀ hU).mpr (by nlinarith [hmass])) hc.le
  by_cases hJU : L*2^(j:ℕ)≤U
  · refine ⟨L*2^(j:ℕ),?_,hJU,?_⟩
    · nlinarith [(one_le_pow₀ (n := (j:ℕ)) (by norm_num : (1:ℝ)≤2))]
    · exact hp.trans (event_mono μ (fun x hx => ⟨hx.2.1,hx.2.2,hx.1.2.2⟩))
  · have hz : event μ (B j)=0 := by
      unfold event
      calc
        _ = avg μ (fun _ => 0) := avg_congr μ (fun x => ite_eq_right (fun hx => hJU (hx.2.1.trans hx.1.2.1)))
        _ = 0 := avg_const μ 0

    have hm0 : m/(U*N)≤0 := hp.trans_eq hz
    exact ⟨L,le_rfl,hLU,hm0.trans (event_nonneg μ _)⟩
end
end PlanarUnitDistances.AccurateBand

namespace PlanarUnitDistances.RareBand
open FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
lemma pair_tail {a b T : ℝ} (ha : 0≤a) (hb : 0≤b) :
    (if 2*T<a+b then a+b else 0)≤2*(if T<a then a else 0)+2*(if T<b then b else 0) := by
  split_ifs <;> linarith
lemma wedge_tail (π : Law (P×Q)) (h : P → ℝ) (hh : ∀p,0≤h p) (T : ℝ) :
    avg (WedgeLaw.law π) (fun a => if 2*T<h a.2.1+h a.2.2 then h a.2.1+h a.2.2 else 0) ≤
      4*avg (left π) (fun p => if T<h p then h p else 0) := by
  calc
    _ ≤ avg (WedgeLaw.law π) (fun a => 2*(if T<h a.2.1 then h a.2.1 else 0)+
      2*(if T<h a.2.2 then h a.2.2 else 0)) := avg_mono _ (fun a => pair_tail (hh _) (hh _))
    _ = _ := by rw [avg_add,avg_smul,avg_smul,WedgeLaw.first_point π (fun p=>if T<h p then h p else 0),WedgeLaw.second_point π (fun p=>if T<h p then h p else 0)]; ring

theorem select (π : Law (P×Q)) (h : P → ℝ) (Z : Q×(P×P) → ℝ)
    {c S R δ : ℝ} {N : ℕ} (hc : 0<c) (hS : 0<S) (hR : 0<R) (hδ : 0<δ)
    (hN : 0<N) (hRc : c≤4*R) (hRN : 4*R<c*2^N)
    (hh : ∀p,0≤h p) (hZ : ∀a,0≤Z a)
    (hmean : c*S≤avg (left π) h)
    (herr : avg (WedgeLaw.law π) Z≤δ*c*S/2)
    (htail : avg (left π) (fun p => if R*S<h p then h p else 0)≤c*S/8) :
    ∃J,c*S/2≤J ∧ J≤2*R*S ∧
      c/(4*R*N)≤event (WedgeLaw.law π)
        (fun a => J≤h a.2.1+h a.2.2 ∧ h a.2.1+h a.2.2≤2*J ∧ Z a≤δ*(h a.2.1+h a.2.2)) := by
  have hwmean : 2*c*S≤avg (WedgeLaw.law π) (fun a => h a.2.1+h a.2.2) := by
    rw [avg_add,WedgeLaw.first_point,WedgeLaw.second_point]
    linarith
  have hzt : avg (WedgeLaw.law π) Z/δ≤c*S/2 := by
    apply (div_le_iff₀ hδ).mpr
    nlinarith
  have hwt := (wedge_tail π h hh (R*S)).trans (mul_le_mul_of_nonneg_left htail (by norm_num : (0:ℝ)≤4))
  obtain ⟨J,hJ,hJU,hprob⟩ := AccurateBand.select (WedgeLaw.law π)
    (fun a => h a.2.1+h a.2.2) Z (L:=c*S/2) (U:=2*(R*S)) (δ:=δ) (m:=c*S/2)
    (N:=N) (fun a => add_nonneg (hh _) (hh _)) hZ (by positivity) (by positivity) hδ
    (by nlinarith [mul_le_mul_of_nonneg_right hRc hS.le]) hN
    (by nlinarith [mul_lt_mul_of_pos_right hRN hS]) (by linarith)
  refine ⟨J,hJ,by nlinarith,?_⟩
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have heq : (c*S/2)/(2*(R*S)*(N:ℝ))=c/(4*R*N) := by field_simp; ring
  rwa [heq] at hprob
end
end PlanarUnitDistances.RareBand

namespace PlanarUnitDistances.TailParameters
open Filter
noncomputable section

lemma noise_limit (C R : ℝ) {ξ : ℕ → ℝ} (hξ : Tendsto ξ atTop (nhds 0)) :
    Tendsto (fun n => coefficient C R (ξ n)) atTop (nhds (coefficient C R 0)) :=
  ((((tendsto_const_nhds.add hξ).div_const _).pow 2).const_mul 144).mul_const C
lemma radius_limit (C : ℝ) : Tendsto (fun R : ℝ => coefficient C R 0) atTop (nhds 0) := by
  have h : Tendsto (fun R : ℝ => (C/R)/(27/50:ℝ)) atTop (nhds 0) := by
    simpa only [zero_div,id_eq] using (tendsto_const_nhds.div_atTop tendsto_id).div_const (27/50:ℝ)
  have hp := h.rpow_const_nhds_zero (by norm_num : (0:ℝ)<1/25)
  simpa only [coefficient,add_zero,zero_div,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_mul]
    using (((hp.div_const (27/50:ℝ)).pow 2).const_mul 144).mul_const C
lemma exists_radius {c : ℝ} (hc : 0<c) (C B : ℝ) :
    ∃R : ℝ,0<R ∧ B≤R ∧ c≤4*R ∧ coefficient C R 0<c/16 := by
  obtain ⟨R,hR,hB,hcR,h⟩ := ((eventually_gt_atTop (0:ℝ)).and
    ((eventually_ge_atTop B).and ((eventually_ge_atTop (c/4)).and
      ((radius_limit C).eventually_lt_const (by positivity : (0:ℝ)<c/16))))).exists
  exact ⟨R,hR,hB,by linarith,h⟩
lemma exists_band {c R : ℝ} (hc : 0<c) : ∃N : ℕ,0<N ∧ 4*R<c*2^N := by
  have ht : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨N,hN,h⟩ := ((eventually_gt_atTop 0).and (ht.eventually_gt_atTop (4*R/c))).exists
  exact ⟨N,hN,by have hh := (div_lt_iff₀ hc).mp h; nlinarith⟩
end
end PlanarUnitDistances.TailParameters

namespace PlanarUnitDistances.IncidenceBand
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceRare IncidenceHeights ActualProfiles ProfileBudget BudgetParameters
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}

local instance instFintypeSumSubtypePlaneMemFinsetPQ_rc2410d_3 : Fintype (s.P i⊕s.Q i) := inferInstance
local instance instFintypeProdSubtypePlaneMemFinsetPQ_rc2410d_4 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
lemma tail {c C τ R₀ : ℝ} (R : Realization s a i) (hR : Ready R c C τ)
    (_hc : 0<c) (hC : 0<C) (hscale : 1≤ scale s i) (hR₀ : 0<R₀)
    (hb : 1/a.epsilon+(2*Real.log 2+4)/a.epsilon+2*Real.log 2≤R₀)
    (hrow : IncidenceNoise.noise s a i≤1/2)
    (hcoeff : TailParameters.coefficient C R₀ (s.ξ i)≤c/16)
    (hconst : 24*(2*Real.log 2+4)≤c*scale s i/16) :
    avg (left (graph s i)) (fun p => if R₀*scale s i<height R.input p then height R.input p else 0)≤c*scale s i/8 := by
  have hS : 0<scale s i := lt_of_lt_of_le zero_lt_one hscale
  have hm := IncidenceHeights.averages R hR
  let U := GeometricLaw.counting (s.P i) (GeometricLaw.card_pos _ _ (s.good i).positive).1
  let V := GeometricLaw.counting (s.Q i) (GeometricLaw.card_pos _ _ (s.good i).positive).2
  have hμ (p : s.P i) : (27/50:ℝ)*U.val p≤(left (graph s i)).val p := by
    rw [graph,GeometricLaw.left_eq]
    simpa only [U,GeometricLaw.counting,mul_one_div] using (s.good i).atomP p p.property
  have hκ (q : s.Q i) : (27/50:ℝ)*V.val q≤(right (graph s i)).val q := by
    rw [graph,GeometricLaw.right_eq]
    simpa only [V,GeometricLaw.counting,mul_one_div] using (s.good i).atomQ q q.property
  have hbase := IncidenceHeights.baseline R hR
  have hbase' : ActualScoreBook.mass (model s i).support*(R.book.WC+R.book.WB)+2*Real.log 2≤R₀*scale s i := by
    have he := a.epsilon_pos
    have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    have h₁ := mul_le_mul_of_nonneg_left hscale (show 0≤(2*Real.log 2+4)/a.epsilon+2*Real.log 2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hb hS.le
    simp only [div_eq_mul_inv,mul_one,one_mul] at hbase h₁ h₂ ⊢
    nlinarith
  have ht := LawTail.estimate (graph s i) U V (height R.input) (ActualHeights.center R.input)
    (ActualHeights.mistake R.input) (γ:=27/50) (η:=1/25) (ξ:=s.ξ i) (C:=C)
    (S:=scale s i) (R:=R₀) (M:=2*Real.log 2+4)
    (by norm_num) (by norm_num) (s.good i).error_nonneg hC.le hS hR₀ hμ hκ
    (GeometricLaw.expansion _ _ (s.good i).positive (s.good i).expansion)
    (height_nonneg R.input) (ActualHeights.center_nonneg R.input) (ActualHeights.mistake_nonneg R.input)
    (fun p q => ((IncidenceNoise.row_atom s i p q).trans
      ((IncidenceNoise.dp_le_collision s a i).trans (IncidenceNoise.components s a i).2.1)).trans hrow)
    hm.2.1 hm.2.2.1 hm.2.2.2.1 hbase' (fun p q r hqr hq hr => by
      simpa only [add_assoc] using IncidenceHeights.pointwise R p q r hqr hq hr)
  have hh := mul_le_mul_of_nonneg_right hcoeff hS.le
  dsimp only [TailParameters.coefficient] at hh
  nlinarith

theorem choose_oai (s : Sequence) : ∃c : ℝ,0<c ∧ ∀δ : ℝ,0<δ →
    ∃a : Params,∃b : ℝ,0<b ∧ ∀ᶠi in atTop,∃R : Realization s a i,∃J : ℝ,
      c*scale s i/2≤J ∧ b≤event (WedgeLaw.law (graph s i)) (band R J δ) := by
  obtain ⟨c,C,hc,hC,hprep⟩ := IncidenceRare.prepare s
  refine ⟨c,hc,?_⟩
  intro δ hδ
  obtain ⟨a,ha⟩ := hprep (δ*c/2) (by positivity)
  obtain ⟨R₀,hR₀,hb,hcR,hcoef⟩ := TailParameters.exists_radius hc C
    (1/a.epsilon+(2*Real.log 2+4)/a.epsilon+2*Real.log 2)
  obtain ⟨N,hN,hRN⟩ := TailParameters.exists_band (R:=R₀) hc
  refine ⟨a,c/(4*R₀*N),by positivity,?_⟩
  have hconst : ∀ᶠi in atTop,24*(2*Real.log 2+4)≤c*scale s i/16 := by
    filter_upwards [(scale_limit s).eventually_ge_atTop (384*(2*Real.log 2+4)/c)] with i hi
    have hh := (div_le_iff₀ hc).mp hi
    nlinarith
  filter_upwards [ha,(scale_limit s).eventually_ge_atTop 1,
    (IncidenceNoise.limit s a).eventually_le_const (by norm_num : (0:ℝ)<1/2),
    (TailParameters.noise_limit C R₀ s.error_limit).eventually_le_const hcoef,hconst]
      with i hi hscale hrow hcoeff hco
  obtain ⟨R,hR⟩ := hi
  have ht := tail R hR hc hC hscale hR₀ hb hrow hcoeff hco
  have hm := IncidenceHeights.averages R hR
  obtain ⟨J,hJ,_,hprob⟩ := RareBand.select (graph s i) (height R.input) (Z R)
    hc (lt_of_lt_of_le zero_lt_one hscale) hR₀ hδ hN hcR hRN
    (height_nonneg R.input) (Z_nonneg R) hm.1 (by convert hm.2.2.2.2 using 1; ring) ht
  exact ⟨R,J,hJ,hprob⟩
end
end PlanarUnitDistances.IncidenceBand

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.IncidenceBand.choose_oai := @OAI.PlanarUnitDistances.IncidenceBand.choose_oai
