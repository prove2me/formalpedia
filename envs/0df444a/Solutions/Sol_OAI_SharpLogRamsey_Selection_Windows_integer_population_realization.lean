-- Prove2me | solution 1 for OAI.SharpLogRamsey.Selection.Windows.integer_population_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:46:41.669733+00:00
-- url     : https://prove2.me/submissions/f6e63aee-a708-4271-bd96-a59bf23a747f

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_ActualPivot_Book_live_realization

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

theorem event_transfer (p q : Law α) (hab : p.AbsolutelyContinuous q) (E : Finset α) :
    q.event E ≤ 2*(divergence p q+p.event E) := by
  have hlog2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have pointwise (a : α) : p.mass a-q.mass a + (if a ∈ E then q.mass a/2 else 0) ≤
      p.mass a*Real.log (p.mass a/q.mass a)+(if a ∈ E then p.mass a*Real.log 2 else 0) := by
    by_cases ha : a ∈ E
    · simp only [ite_eq_left ha]
      have h := mul_log_div_ge (p.nonneg a) (div_nonneg (q.nonneg a) (by norm_num : (0:ℝ) ≤ 2))
        (fun h => hab a (by linarith))
      by_cases hp : p.mass a = 0
      · simp only [hp,zero_mul,zero_sub] at h ⊢; linarith
      have hp0 := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      have hq : q.mass a ≠ 0 := fun h => hp (hab a h)
      have he : Real.log (p.mass a/(q.mass a/2)) =
          Real.log (p.mass a/q.mass a)+Real.log 2 := by
        rw [div_div_eq_mul_div, mul_div_right_comm,
          Real.log_mul (div_ne_zero hp hq) (by norm_num)]
      rw [he] at h
      nlinarith
    · simpa only [ite_eq_right ha,add_zero] using mul_log_div_ge (p.nonneg a) (q.nonneg a) (hab a)
  have h := sum_le_sum (fun a (_ : a ∈ univ) => pointwise a)
  simp only [sum_add_distrib, sum_sub_distrib, p.total, q.total, sub_self, zero_add,
    ← sum_filter, filter_mem_eq_inter, univ_inter] at h
  rw [← sum_div, ← sum_mul] at h
  change q.event E/2 ≤ divergence p q+p.event E*Real.log 2 at h
  have hh := mul_le_mul_of_nonneg_left hlog2 (p.event_nonneg E)
  nlinarith

theorem mutualInfo_event_transfer (p : Law (α × β)) (E : Finset (α × β)) :
    (p.fst.prod p.snd).event E ≤ 2*(mutualInfo p+p.event E) := by
  rw [mutualInfo_eq_divergence]
  exact event_transfer p _ p.absContinuous_prod E

end SharpLogRamsey.Selection

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
lemma not_badIndices (p : Law (ι→β)) (e : B×X ↪ ι) (own : ι→Option B)
    (c : ι→ι→NNReal) (J D a : ℝ) (f : B→X) (i : ι) :
    i∉badIndices p e own c J D a f ↔
      J-entropy (p.marginal i)≤D ∧
      ∀ j∈otherRepresentatives e own f i,(pairInformation p i j:ℝ)+(c i j:ℝ)≤a := by
  simp [badIndices]

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

theorem Law.core_failure_le (p : Law α) (v : α → V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    p.event (univ.filter (fun a => v a ∉ p.core (K:=K) v ρ)) ≤
      (Module.finrank K V : ℝ)*ρ := by
  obtain ⟨b,hb,hspan,hli⟩ := exists_linearIndependent K (p.tests (K:=K) v ρ)
  let : Finite b := hli.finite
  let : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b ≤ Module.finrank K V := by
    have h := hli.fintype_card_le_finrank
    simpa only [Subspace.dual_finrank_eq] using h
  have hsome (a : α) (ha : v a ∉ p.core (K:=K) v ρ) : ∃ f : b, f.val (v a) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply ha
    rw [p.mem_core (K:=K)]
    have hs : Submodule.span K b ≤ LinearMap.ker (Module.Dual.eval K V (v a)) := by
      rw [Submodule.span_le]
      intro f hf
      exact hn ⟨f,hf⟩
    rw [hspan] at hs
    intro f hf
    exact hs (Submodule.subset_span hf)
  have hpoint (a : α) :
      (if v a ∉ p.core (K:=K) v ρ then p.mass a else 0) ≤
        ∑ f : b, if f.val (v a) ≠ 0 then p.mass a else 0 := by
    by_cases ha : v a ∉ p.core (K:=K) v ρ
    · obtain ⟨f,hf⟩ := hsome a ha
      rw [ite_eq_left ha]
      calc
        _ = (if f.val (v a) ≠ 0 then p.mass a else 0) := (ite_eq_left hf).symm
        _ ≤ ∑ g : b, if g.val (v a) ≠ 0 then p.mass a else 0 :=
          single_le_sum (f := fun g : b => if g.val (v a) ≠ 0 then p.mass a else 0)
            (fun g hg => by split_ifs <;> first | exact p.nonneg _ | positivity) (mem_univ f)
    · rw [ite_eq_right ha]
      exact sum_nonneg fun f hf => by split_ifs <;> first | exact p.nonneg _ | positivity
  calc
    p.event (univ.filter (fun a => v a ∉ p.core (K:=K) v ρ))
      = ∑ a, if v a ∉ p.core (K:=K) v ρ then p.mass a else 0 := by simp only [Law.event,sum_filter]
    _ ≤ ∑ a, ∑ f : b, if f.val (v a) ≠ 0 then p.mass a else 0 := sum_le_sum fun a ha => hpoint a
    _ = ∑ f : b, p.event (univ.filter (fun a => f.val (v a) ≠ 0)) := by
      rw [sum_comm]; simp only [Law.event,sum_filter]
    _ ≤ ∑ _ : b, ρ := sum_le_sum fun f hf => hb f.property
    _ = (Fintype.card b : ℝ)*ρ := by simp
    _ ≤ (Module.finrank K V : ℝ)*ρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hρ

theorem Law.event_complement (p : Law α) (E : Finset α) :
    p.event E + p.event Eᶜ = 1 := by
  exact (sum_add_sum_compl E p.mass).trans p.total

theorem Law.core_capture (p : Law α) (v : α → V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1-(Module.finrank K V : ℝ)*ρ ≤
      p.event (univ.filter (fun a => v a ∈ p.core (K:=K) v ρ)) := by
  have h := p.core_failure_le (K:=K) v hρ
  have hc := p.event_complement (univ.filter (fun a => v a ∈ p.core (K:=K) v ρ))
  have he : (univ.filter (fun a => v a ∈ p.core (K:=K) v ρ))ᶜ =
      univ.filter (fun a => v a ∉ p.core (K:=K) v ρ) := by ext a; simp
  rw [he] at hc
  linarith

variable {β : Type*} [Fintype β]

theorem Law.event_gt_le (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    {ρ : ℝ} (_hρ : 0 < ρ) :
    p.event (univ.filter (fun a => ρ < f a))*ρ ≤ ∑ a, p.mass a*f a := by
  rw [Law.event,sum_filter,sum_mul]
  apply sum_le_sum
  intro a ha
  by_cases he : ρ < f a
  · rw [ite_eq_left he]
    exact mul_le_mul_of_nonneg_left he.le (p.nonneg a)
  · rw [ite_eq_right he,zero_mul]
    exact mul_nonneg (p.nonneg a) (hf a)

omit [FiniteDimensional K V] in

theorem Law.cores_orthogonal (p : Law α) (q : Law β) (v : α → V)
    (w : β → Module.Dual K V) {ρ : ℝ} (hρ : 0 < ρ)
    (herror : (p.prod q).event (univ.filter (fun z : α × β => w z.2 (v z.1) ≠ 0)) ≤ ρ^2) :
    (q.core (K:=K) w ρ) ≤ (p.core (K:=K) v ρ).dualAnnihilator := by
  let err : α → ℝ := fun a => q.event (univ.filter (fun b => w b (v a) ≠ 0))
  have hmean : (∑ a, p.mass a*err a) =
      (p.prod q).event (univ.filter (fun z : α × β => w z.2 (v z.1) ≠ 0)) := by
    simp only [err,Law.event,Law.prod,sum_filter,Fintype.sum_prod_type,mul_sum,mul_ite,mul_zero]
  have hbad : p.event (univ.filter (fun a => ρ < err a)) ≤ ρ := by
    have h := p.event_gt_le err (fun a => q.event_nonneg _) hρ
    rw [hmean] at h
    apply (mul_le_mul_iff_left₀ hρ).mp
    nlinarith
  intro f hf
  rw [Submodule.mem_dualAnnihilator]
  have ht : f ∈ p.tests (K:=K) v ρ := by
    change p.event (univ.filter (fun a => f (v a) ≠ 0)) ≤ ρ
    apply le_trans _ hbad
    apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [mem_filter,mem_univ,true_and] at ha ⊢
      by_contra hn
      have he : Module.Dual.eval K V (v a) ∈ q.tests (K:=K) w ρ := by
        exact le_of_not_gt hn
      exact ha ((q.mem_core (K:=K) w ρ f).mp hf _ he)
    · intro a ha hb
      exact p.nonneg a
  intro x hx
  exact (p.mem_core (K:=K) v ρ x).mp hx f ht

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] in

theorem card_projective_subspace (W : Submodule K V) :
    Fintype.card {a : Projectivization K V // a.submodule ≤ W} =
      ∑ i ∈ Finset.range (Module.finrank K W), Nat.card K ^ i := by
  rw [← Nat.card_eq_fintype_card,
    ← Nat.card_congr (_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

omit [FiniteDimensional K V] in

theorem Law.subspace_mass_bound (p : Law (Projectivization K V))
    (W : Submodule K V) (E : Finset (Projectivization K V)) {c : ℝ}
    (hc : 0 ≤ c) (hE : ∀ a ∈ E, a.submodule ≤ W)
    (hcap : ∀ a ∈ E, p.mass a ≤ c) :
    p.event E ≤ c * ∑ i ∈ Finset.range (Module.finrank K W), (Nat.card K : ℝ)^i := by
  have hcard : E.card ≤ Fintype.card {a : Projectivization K V // a.submodule ≤ W} := by
    rw [Fintype.card_subtype]
    apply card_le_card
    intro a ha
    exact mem_filter.mpr ⟨mem_univ _,hE a ha⟩
  calc
    p.event E ≤ ∑ _a ∈ E, c := sum_le_sum hcap
    _ = c*E.card := by simp [mul_comm]
    _ ≤ c * (Fintype.card {a : Projectivization K V // a.submodule ≤ W} : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hc
    _ = _ := by rw [card_projective_subspace]; simp

theorem sum_powers_le_twice {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, q^i ≤ 2*q^(n-1) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one]
  clear hn
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hp : 0 ≤ q^m := pow_nonneg (by linarith) _
    have hmul : 2*q^m ≤ q^(m+1) := by
      rw [pow_succ]
      nlinarith
    calc
      _ ≤ 2*q^m+q^(m+1) := by
        simp only [Nat.succ_eq_add_one] at ih
        linarith
      _ ≤ 2*q^(m+1) := by linarith

omit [FiniteDimensional K V] in

theorem Law.subspace_rank_pos (p : Law (Projectivization K V))
    (W : Submodule K V) (E : Finset (Projectivization K V)) {c γ : ℝ}
    (hc : 0 ≤ c) (hγ : 0 < γ) (hmass : γ ≤ p.event E)
    (hE : ∀ a ∈ E, a.submodule ≤ W)
    (hcap : ∀ a ∈ E, p.mass a ≤ c) : 0 < Module.finrank K W := by
  have h := p.subspace_mass_bound W E hc hE hcap
  by_contra hn
  have hz : Module.finrank K W = 0 := by omega
  simp only [hz,range_zero,sum_empty,mul_zero] at h
  linarith

omit [FiniteDimensional K V] in

theorem Law.subspace_mass_le_pow (p : Law (Projectivization K V))
    (W : Submodule K V) (E : Finset (Projectivization K V)) {c γ : ℝ}
    (hc : 0 ≤ c) (hγ : 0 < γ) (hmass : γ ≤ p.event E)
    (hE : ∀ a ∈ E, a.submodule ≤ W)
    (hcap : ∀ a ∈ E, p.mass a ≤ c) :
    γ ≤ 2*c*(Nat.card K : ℝ)^(Module.finrank K W-1) := by
  have hr := p.subspace_rank_pos W E hc hγ hmass hE hcap
  have hq : (2 : ℝ) ≤ Nat.card K := by
    exact_mod_cast (Finite.one_lt_card (α:=K))
  calc
    γ ≤ p.event E := hmass
    _ ≤ c * ∑ i ∈ range (Module.finrank K W), (Nat.card K : ℝ)^i :=
      p.subspace_mass_bound W E hc hE hcap
    _ ≤ c*(2*(Nat.card K : ℝ)^(Module.finrank K W-1)) :=
      mul_le_mul_of_nonneg_left (sum_powers_le_twice hq hr) hc
    _ = _ := by ring

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

lemma Law.paired_cond_mass (p : Law (A × B)) (q : Law (C × D))
    (a : A) (b : B) (c : C) (y : D) (v : ℝ) :
    (p.fst.mass a*q.snd.mass y)*
      (((p.condSnd a).mass b*(q.condFst y).mass c)*v) =
    (p.mass (a,b)*q.mass (c,y))*v := by
  calc
    _ = (p.fst.mass a*(p.condSnd a).mass b)*
      (q.snd.mass y*(q.condFst y).mass c)*v := by ring
    _ = _ := by rw [p.fst_mul_condSnd,q.snd_mul_condFst]

lemma Law.product_disintegration (p : Law (A × B)) (q : Law (C × D))
    (F : (A × B) → (C × D) → ℝ) :
    (∑ z : (A × B) × (C × D), (p.prod q).mass z * F z.1 z.2) =
    ∑ ay : A × D, (p.fst.prod q.snd).mass ay *
      ∑ bc : B × C, ((p.condSnd ay.1).prod (q.condFst ay.2)).mass bc *
        F (ay.1,bc.1) (bc.2,ay.2) := by
  simp only [Law.prod, Fintype.sum_prod_type, mul_sum]
  simp_rw [p.paired_cond_mass q]
  apply sum_congr rfl
  intro a _
  calc
    _ = ∑ b : B, ∑ y : D, ∑ c : C, p.mass (a,b)*q.mass (c,y)*F (a,b) (c,y) := by
      apply sum_congr rfl
      intro b _
      exact sum_comm
    _ = _ := sum_comm

lemma Law.product_event_disintegration (p : Law (A × B)) (q : Law (C × D))
    (E : (A × B) → (C × D) → Prop) :
    (p.prod q).event (univ.filter (fun z => E z.1 z.2)) =
    ∑ ay : A × D, (p.fst.prod q.snd).mass ay *
      ((p.condSnd ay.1).prod (q.condFst ay.2)).event
        (univ.filter (fun bc : B × C => E (ay.1,bc.1) (bc.2,ay.2))) := by
  simpa only [Law.event, sum_filter, mul_ite, mul_one, mul_zero] using
    p.product_disintegration q (fun ab cy => if E ab cy then 1 else 0)

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
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]
lemma Law.prod_rectangle_event (p : Law A) (q : Law B) (S : Finset A) (T : Finset B) :
    (p.prod q).event (S ×ˢ T) = p.event S*q.event T := by
  simp only [Law.event, Law.prod, sum_product, sum_mul, mul_sum]
  exact sum_comm

lemma Law.event_filter_le_add (p : Law A) (P Q : A → Prop) :
    p.event (univ.filter P) ≤ p.event (univ.filter (fun a => P a ∧ ¬Q a)) +
      p.event (univ.filter (fun a => P a ∧ Q a)) := by
  simp only [Law.event, sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp,hq]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma core_capture_product (p q : Law (A × B)) (v : B → V)
    (w : A → Module.Dual K V) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hd : c ≤ 1-(Module.finrank K V:ℝ)*ρ) (a : A) (y : B) :
    c^2 ≤ ((p.condSnd a).prod (q.condFst y)).event
      (univ.filter (fun bc : B × A => v bc.1 ∈ firstCore (K := K) p v ρ a ∧
        w bc.2 ∈ secondCore q w ρ y)) := by
  have h₁ := (p.condSnd a).core_capture (K := K) v hρ
  have h₂ := (q.condFst y).core_capture (K := K) w hρ
  rw [Subspace.dual_finrank_eq] at h₂
  have he : (univ.filter (fun bc : B × A => v bc.1 ∈ firstCore (K := K) p v ρ a ∧
      w bc.2 ∈ secondCore q w ρ y)) =
      (univ.filter (fun b => v b ∈ firstCore (K := K) p v ρ a)) ×ˢ
      (univ.filter (fun a => w a ∈ secondCore q w ρ y)) := by ext bc; simp
  rw [he, Law.prod_rectangle_event, pow_two]
  exact mul_le_mul (hd.trans h₁) (hd.trans h₂) hc
    ((p.condSnd a).event_nonneg _)

lemma core_collision_capture (p q : Law (A × B)) (v : B → V)
    (w : A → Module.Dual K V) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hd : c ≤ 1-(Module.finrank K V:ℝ)*ρ) (goodA : A → Prop) (goodB : B → Prop) :
    c^2*(p.fst.prod q.snd).event (univ.filter (fun ay : A × B =>
      goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0 ∧ coreContained p q v w ρ ay.1 ay.2)) ≤
    (p.prod q).event (univ.filter (coreCollision p q v w ρ goodA goodB)) := by
  rw [show (p.prod q).event (univ.filter (coreCollision p q v w ρ goodA goodB)) =
    (p.prod q).event (univ.filter (fun z => coreCollision p q v w ρ goodA goodB (z.1,z.2))) by rfl,
    p.product_event_disintegration q (fun ab cy => coreCollision p q v w ρ goodA goodB (ab,cy))]
  simp only [Law.event, sum_filter, mul_sum]
  apply sum_le_sum
  intro ay _
  rw [←mul_sum]
  by_cases h : goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0 ∧ coreContained p q v w ρ ay.1 ay.2
  · rw [ite_eq_left h]
    have he : (∑ bc : B × A, if coreCollision p q v w ρ goodA goodB ((ay.1,bc.1), (bc.2,ay.2))
        then ((p.condSnd ay.1).prod (q.condFst ay.2)).mass bc else 0) =
        ((p.condSnd ay.1).prod (q.condFst ay.2)).event (univ.filter (fun bc : B × A =>
          v bc.1 ∈ firstCore (K := K) p v ρ ay.1 ∧ w bc.2 ∈ secondCore q w ρ ay.2)) := by
      simp [Law.event, sum_filter, coreCollision, h.1,h.2.1,h.2.2.1,h.2.2.2]
    rw [he, mul_comm (c^2)]
    exact mul_le_mul_of_nonneg_left (core_capture_product p q v w hρ hc hd ay.1 ay.2)
      ((p.fst.prod q.snd).nonneg ay)
  · rw [ite_eq_right h, mul_zero]
    exact mul_nonneg ((p.fst.prod q.snd).nonneg ay) (sum_nonneg (fun bc _ => by
      split_ifs; exact ((p.condSnd ay.1).prod (q.condFst ay.2)).nonneg bc; rfl))
omit [FiniteDimensional K V] in

lemma exceptional_core_mass (p q : Law (A × B)) (v : B → V)
    (w : A → Module.Dual K V) {ρ : ℝ} (hρ : 0 < ρ)
    (goodA : A → Prop) (goodB : B → Prop) :
    ρ^2*(p.fst.prod q.snd).event (univ.filter (fun ay : A × B =>
      (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
        ¬coreContained p q v w ρ ay.1 ay.2)) ≤
    (p.prod q).event (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0)) := by
  calc
    _ ≤ ∑ ay : A × B, (p.fst.prod q.snd).mass ay *
      ((p.condSnd ay.1).prod (q.condFst ay.2)).event
        (univ.filter (fun bc : B × A =>
          w ay.1 (v ay.2) = 0 ∧ w bc.2 (v bc.1) ≠ 0)) := by
      change ρ^2*(∑ ay with (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
        ¬coreContained p q v w ρ ay.1 ay.2, (p.fst.prod q.snd).mass ay) ≤ _
      rw [sum_filter,mul_sum]
      apply sum_le_sum
      intro ay _
      by_cases h : (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
          ¬coreContained p q v w ρ ay.1 ay.2
      · rw [ite_eq_left h, mul_comm (ρ^2)]
        apply mul_le_mul_of_nonneg_left _ ((p.fst.prod q.snd).nonneg ay)
        simp only [h.1.2.2, true_and]
        apply le_of_not_gt
        intro he
        exact h.2 ((p.condSnd ay.1).cores_orthogonal (q.condFst ay.2) v w hρ he.le)
      · rw [ite_eq_right h,mul_zero]
        exact mul_nonneg ((p.fst.prod q.snd).nonneg ay)
          (((p.condSnd ay.1).prod (q.condFst ay.2)).event_nonneg _)
    _ = _ := by
      convert (p.product_event_disintegration q
        (fun ab cy => w ab.1 (v cy.2) = 0 ∧ w cy.1 (v ab.2) ≠ 0)).symm using 1 <;> congr!

theorem reciprocal_incidence_collision (p : Law ((A × B) × (A × B)))
    (v : B → V) (w : A → Module.Dual K V)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (hd : c ≤ 1-(Module.finrank K V:ℝ)*ρ)
    (goodA : A → Prop) (goodB : B → Prop)
    (hconsistent : ∀ z, p.mass z ≠ 0 →
      w z.1.1 (v z.2.2) = 0 → w z.2.1 (v z.1.2) = 0) :
    (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0)) ≤
    2*mutualInfo p/ρ^2 +
      2*(mutualInfo p+p.event (univ.filter (coreCollision p.fst p.snd v w ρ goodA goodB)))/c^2 := by
  have hconf : p.event (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0)) = 0 := by
    apply sum_eq_zero
    intro z hz
    by_contra hn
    have hz' := (mem_filter.mp hz).2
    exact hz'.2 (hconsistent z hn hz'.1)
  have herr := mutualInfo_event_transfer p (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0))
  rw [hconf,add_zero] at herr
  have he := (exceptional_core_mass p.fst p.snd v w hρ goodA goodB).trans herr
  have hex : (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
        ¬coreContained p.fst p.snd v w ρ ay.1 ay.2)) ≤ 2*mutualInfo p/ρ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    simpa only [mul_comm] using he
  have hcap := (core_collision_capture p.fst p.snd v w hρ.le hc.le hd goodA goodB).trans
    (mutualInfo_event_transfer p (univ.filter (coreCollision p.fst p.snd v w ρ goodA goodB)))
  have hcm : (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0 ∧
        coreContained p.fst p.snd v w ρ ay.1 ay.2)) ≤
      2*(mutualInfo p+p.event (univ.filter (coreCollision p.fst p.snd v w ρ goodA goodB)))/c^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    simpa only [mul_comm] using hcap
  have hs := (p.fst.fst.prod p.snd.snd).event_filter_le_add
    (fun ay : A × B => goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0)
    (fun ay => coreContained p.fst p.snd v w ρ ay.1 ay.2)
  have hcm' : (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
      coreContained p.fst p.snd v w ρ ay.1 ay.2)) ≤
      2*(mutualInfo p+p.event (univ.filter (coreCollision p.fst p.snd v w ρ goodA goodB)))/c^2 := by
    simpa only [and_assoc] using hcm
  have HF := hs.trans (by
    convert add_le_add hex hcm' using 1
    all_goals try with_reducible_and_instances rfl
    congr!)
  convert HF using 1
  all_goals try with_reducible_and_instances rfl
  congr!

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

lemma Law.event_union_le (p : Law α) (E F : Finset α) :
    p.event (E ∪ F) ≤ p.event E+p.event F := by
  unfold Law.event
  have h : ∀ x, (if x ∈ E ∪ F then p.mass x else 0) ≤
      (if x ∈ E then p.mass x else 0)+(if x ∈ F then p.mass x else 0) := by
    intro x
    by_cases he : x ∈ E <;> by_cases hf : x ∈ F <;> simp [he,hf,p.nonneg]
  simpa only [sum_add_distrib, sum_ite_mem_eq] using
    (sum_le_sum (fun x (_ : x ∈ (univ : Finset α)) => h x))

lemma Law.event_mono (p : Law α) {E F : Finset α} (h : E ⊆ F) : p.event E ≤ p.event F :=
  sum_le_sum_of_subset_of_nonneg h (fun x _ _ => p.nonneg x)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_CoreDimensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open scoped BigOperators Classical
open Finset
noncomputable section
variable {α : Type*} [Fintype α]

lemma Law.event_sdiff_lower (p : Law α) (S T : Finset α) :
    p.event S-p.event T ≤ p.event (S\T) := by
  have hsubset : S ⊆ (S \ T) ∪ T := by
    intro atom hmem
    by_cases hremoved : atom ∈ T
    · exact mem_union_right _ hremoved
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hmem, hremoved⟩)
  exact sub_le_iff_le_add.mpr ((p.event_mono hsubset).trans (p.event_union_le _ _))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [Finite K] in

lemma Law.core_nonheavy_mass (p : Law (Projectivization K V))
    {ρ ε : ℝ} (hρ : 0 ≤ ρ) (bad : Finset (Projectivization K V))
    (hbad : p.event bad ≤ ε) :
    1-(Module.finrank K V:ℝ)*ρ-ε ≤
      p.event ((univ.filter (fun b => b.rep ∈ p.core (K := K) Projectivization.rep ρ))\bad) := by
  have h := p.core_capture (K := K) Projectivization.rep hρ
  have hh := p.event_sdiff_lower (univ.filter (fun b => b.rep ∈ p.core (K := K) Projectivization.rep ρ)) bad
  linarith

omit [FiniteDimensional K V] in

theorem Law.subspace_log_dimension (p : Law (Projectivization K V))
    (W : Submodule K V) (E : Finset (Projectivization K V)) {A κ γ : ℝ}
    (hA : 0 < A) (hγ : 0 < γ) (hκ : Real.log (2/γ) ≤ κ) (d : ℕ)
    (hmass : γ ≤ p.event E) (hE : ∀ a ∈ E, a.submodule ≤ W)
    (hcap : ∀ a ∈ E, p.mass a ≤ A*Real.exp (2*κ)/(Nat.card K:ℝ)^d) :
    (d:ℝ)+1-(Real.log A+3*κ)/Real.log (Nat.card K) ≤ Module.finrank K W := by
  have hq : (1:ℝ) < Nat.card K := by exact_mod_cast Finite.one_lt_card (α := K)
  have hq0 := lt_trans zero_lt_one hq
  have hc : 0 < A*Real.exp (2*κ)/(Nat.card K:ℝ)^d := by positivity
  have h := p.subspace_mass_le_pow W E hc.le hγ hmass hE hcap
  have hr := p.subspace_rank_pos W E hc.le hγ hmass hE hcap
  have hl := Real.log_le_log hγ h
  rw [Real.log_mul (mul_pos (by norm_num) hc).ne' (pow_ne_zero _ hq0.ne'),
    Real.log_mul (by norm_num) hc.ne', Real.log_div (by positivity) (pow_ne_zero _ hq0.ne'),
    Real.log_mul hA.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_pow, Real.log_pow] at hl
  have hcast : ((Module.finrank K W-1:ℕ):ℝ) = (Module.finrank K W:ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast] at hl
  rw [Real.log_div (by norm_num) hγ.ne'] at hκ
  have hlog : 0 < Real.log (Nat.card K) := Real.log_pos hq
  have hh : (d:ℝ)+1-(Module.finrank K W:ℝ) ≤ (Real.log A+3*κ)/Real.log (Nat.card K) := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith
  linarith

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] [Fintype A]

lemma conditional_atom_cap {m z M κ L : ℝ} (hM : 0 < M)
    (hm : exp (-κ)/M ≤ m) (hz : z≤exp (κ-L)) :
    z/m≤M*exp (2*κ-L) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hl : exp (-κ)≤ m*M := (div_le_iff₀ hM).mp hm
  apply (div_le_iff₀ hm0).mpr
  calc
    z ≤ exp (κ-L) := hz
    _ = exp (2*κ-L)*exp (-κ) := by rw [← exp_add]; congr 1; ring
    _ ≤ exp (2*κ-L)*(m*M) := mul_le_mul_of_nonneg_left hl (exp_pos _).le
    _ = _ := by ring

theorem conditional_core_dimension (p : Law (Projectivization K V))
    (z : Projectivization K V→ℝ) (m M κ ρ ε : ℝ) (d : ℕ)
    (hM : 0 < M) (hm : exp (-κ)/M ≤ m)
    (hp : ∀ b,p.mass b=z b/m) (hρ : 0≤ρ)
    (hheavy : p.event (univ.filter (fun b => exp (κ-(d:ℝ)*log (Nat.card K))<z b))≤ε)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ) :
    (d:ℝ)+1-(log M+3*κ)/log (Nat.card K)≤
      Module.finrank K (p.core (K:=K) Projectivization.rep ρ) := by
  let bad := univ.filter (fun b : Projectivization K V => exp (κ-(d:ℝ)*log (Nat.card K))<z b)
  let E := (univ.filter (fun b => b.rep∈p.core (K:=K) Projectivization.rep ρ))\bad
  have hmass := p.core_nonheavy_mass hρ bad hheavy
  apply p.subspace_log_dimension (p.core (K:=K) Projectivization.rep ρ) E hM hγ hκ d hmass
  · intro b hb
    rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
    exact (mem_filter.mp (mem_sdiff.mp hb).1).2
  · intro b hb
    have hz : z b≤exp (κ-(d:ℝ)*log (Nat.card K)) := by
      have hn := (mem_sdiff.mp hb).2
      simpa only [bad,mem_filter,mem_univ,true_and,not_lt] using hn
    rw [hp b]
    have hh := conditional_atom_cap hM hm hz
    have he : exp (2*κ-(d:ℝ)*log (Nat.card K))=exp (2*κ)/(Nat.card K:ℝ)^d := by
      rw [exp_sub,exp_nat_mul,exp_log]
      exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
    rw [he] at hh
    simpa only [mul_div_assoc] using hh

theorem goodSecond_core_dimension (p : Law (Projectivization K V×A))
    (M κ ρ ε : ℝ) (d : ℕ) (a : A) (hM : 0 < M) (hρ : 0≤ρ)
    (hgood : goodSecond p M ((d:ℝ)*log (Nat.card K)) κ ε a)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ) :
    (d:ℝ)+1-(log M+3*κ)/log (Nat.card K)≤
      Module.finrank K ((p.condFst a).core (K:=K) Projectivization.rep ρ) := by
  have hm : p.snd.mass a≠0 := (lt_of_lt_of_le (by positivity) hgood.1).ne'
  exact conditional_core_dimension (p.condFst a) (fun b => p.mass (b,a))
    (p.snd.mass a) M κ ρ ε d hM hgood.1 (p.condFst_mass a hm) hρ hgood.2 hγ hκ

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_Reciprocal
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
variable {A B : Type*} [Fintype A] [Fintype B]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]

theorem goodFirst_core_dimension (p : Law (A×Projectivization K V))
    (M κ ρ ε : ℝ) (d : ℕ) (a : A) (hM : 0 < M) (hρ : 0≤ρ)
    (hgood : goodFirst p M ((d:ℝ)*log (Nat.card K)) κ ε a)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ) :
    (d:ℝ)+1-(log M+3*κ)/log (Nat.card K)≤
      Module.finrank K (firstCore (K:=K) p Projectivization.rep ρ a) := by
  have hm : p.fst.mass a≠0 :=
    (lt_of_lt_of_le (div_pos (exp_pos (-κ)) hM) hgood.1).ne'
  exact conditional_core_dimension (p.condSnd a) (fun b => p.mass (a,b))
    (p.fst.mass a) M κ ρ ε d hM hgood.1 (p.condSnd_mass a hm) hρ hgood.2 hγ hκ

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

private lemma round_core_rank {r a : ℕ} {x : ℝ}
    (hx : (r:ℝ)-1<x) (ha : x≤a) : r≤a := by
  by_contra hn
  have hn' : (a:ℝ)+1 ≤ r := by exact_mod_cast (show a+1 ≤ r by omega)
  linarith

theorem projective_integer_ranks
    (p q : Law (Projectivization K (Module.Dual K V)×Projectivization K V))
    (MA MB κ ρ ε : ℝ) (d r : ℕ) (hMA : 0<MA) (hMB : 0<MB) (hρ : 0≤ρ)
    (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (a : Projectivization K (Module.Dual K V)) (y : Projectivization K V)
    (ha : goodFirst p MA ((d:ℝ)*log (Nat.card K)) κ ε a)
    (hy : goodSecond q MB ((d:ℝ)*log (Nat.card K)) κ ε y) :
    r≤Module.finrank K (firstCore (K:=K) p Projectivization.rep ρ a) ∧
    d+1-r≤Module.finrank K (secondCore q Projectivization.rep ρ y) := by
  constructor
  · exact round_core_rank hu (goodFirst_core_dimension p MA κ ρ ε d a hMA hρ ha hγ hκ)
  · have hh := goodSecond_core_dimension q MB κ ρ ε d y hMB hρ hy
      (by simpa only [Subspace.dual_finrank_eq] using hγ)
      (by simpa only [Subspace.dual_finrank_eq] using hκ)
    apply round_core_rank (x:=(d:ℝ)+1-(log MB+3*κ)/log (Nat.card K)) _ hh
    have hc : ((d+1-r:ℕ):ℝ)=(d:ℝ)+1-r := by
      rw [Nat.cast_sub hr,Nat.cast_add,Nat.cast_one]
    rw [hc]
    linarith

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

theorem projective_integer_incidence
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (MA MB κ ρ ε c : ℝ) (d r : ℕ)
    (hMA : 0<MA) (hMB : 0<MB) (hρ : 0<ρ) (hc : 0 < c)
    (hcap : c≤1-(Module.finrank K V:ℝ)*ρ) (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) MA ((d:ℝ)*log (Nat.card K)) κ ε ay.1 ∧
      goodSecond (p.marginal j) MB ((d:ℝ)*log (Nat.card K)) κ ε ay.2 ∧
      ay.1.rep ay.2.rep=0))≤
      2*(pairInformation p i j:ℝ)/ρ^2+
        2*((pairInformation p i j:ℝ)+
          (directedCollision p Projectivization.rep Projectivization.rep ρ r (d+1-r) i j:ℝ))/c^2 := by
  classical
  let : DecidableEq (Projectivization K (Module.Dual K V)×Projectivization K V) := Classical.decEq _
  let : DecidableEq ((Projectivization K (Module.Dual K V)×Projectivization K V)×
      (Projectivization K (Module.Dual K V)×Projectivization K V)) := Classical.decEq _
  let p₂ := p.map (fun x => (x i,x j))
  have hi : p₂.fst=p.marginal i := by
    rw [←Law.map_fst,Law.map_map]; rfl
  have hj : p₂.snd=p.marginal j := by
    rw [←Law.map_snd,Law.map_map]; rfl
  let ga := goodFirst (p.marginal i) MA ((d:ℝ)*log (Nat.card K)) κ ε
  let gb := goodSecond (p.marginal j) MB ((d:ℝ)*log (Nat.card K)) κ ε
  have hcon : ∀ z,p₂.mass z≠0 →
      z.1.1.rep z.2.2.rep=0 → z.2.1.rep z.1.2.rep=0 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := p.map_support (fun x => (x i,x j)) z hz
    exact hconsistent x hx
  have hb := reciprocal_incidence_collision p₂ Projectivization.rep Projectivization.rep
    hρ hc hcap ga gb hcon
  have he : p₂.event (univ.filter (coreCollision p₂.fst p₂.snd
      Projectivization.rep Projectivization.rep ρ ga gb))≤
      (directedCollision p Projectivization.rep Projectivization.rep ρ r (d+1-r) i j:ℝ) := by
    rw [hi,hj]
    have hm := p.event_map (fun x => (x i,x j))
      (univ.filter (coreCollision (p.marginal i) (p.marginal j)
        Projectivization.rep Projectivization.rep ρ ga gb))
    refine hm.le.trans ?_
    apply p.event_mono
    intro x hx
    have hh := (mem_filter.mp hx).2
    simp only [mem_filter,mem_univ,true_and] at hh
    have hranks := projective_integer_ranks (p.marginal i) (p.marginal j)
      MA MB κ ρ ε d r hMA hMB hρ.le hr hγ hκ hu hv (x i).1 (x j).2 hh.1 hh.2.1
    exact mem_filter.mpr ⟨mem_univ _,hranks.1,hranks.2,hh.2.2⟩
  rw [hi,hj] at hb he
  change _≤2*mutualInfo p₂/ρ^2+2*(mutualInfo p₂+_)/c^2
  exact hb.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl he)
        (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg c)))

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

lemma Law.map_comp {γ : Type*} [Fintype γ] (p : Law α) (f : α→β) (g : β→γ) :
    (p.map f).map g=p.map (g∘f) := by
  exact p.map_map f g

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_EndpointSupports
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
variable {A B : Type*} [Fintype A] [Fintype B]

lemma Law.swap_eq_map (p : Law (A × B)) : p.swap = p.map Prod.swap := by
  ext ⟨b,a⟩
  exact (p.map_mass_injective Prod.swap Prod.swap_injective (a,b)).symm

@[simp] lemma entropy_swap (p : Law (A × B)) : entropy p.swap = entropy p := by
  rw [Law.swap_eq_map]
  exact entropy_map_eq_of_injective p Prod.swap Prod.swap_injective

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureRealization
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

theorem atRound_owner (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C) (t : Fin k)
    (z : (atRound n k p e own t).History) (i : (atRound n k p e own t).Index z) :
    (atRound n k p e own t).owner z i=own ((atRound n k p e own t).origin z i) := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => rfl
    | succ j => exact ih _ (remainingEmbedding e z.1) (fun i=>own i) j z.2.2 i

theorem atRound_embedding_owner (n k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Law (ι→β)) (e : C×Fin (n+k)↪ι) (own : ι→Option C)
    (hown : ∀ b x,own (e (b,x))=some b) (t : Fin k)
    (z : (atRound n k p e own t).History) (b : C)
    (x : Fin ((atRound n k p e own t).remaining z)) :
    (atRound n k p e own t).owner z ((atRound n k p e own t).embedding z (b,x))=some b := by
  induction k generalizing ι with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    induction t using Fin.cases with
    | zero => exact hown b x
    | succ j =>
      exact ih _ (remainingEmbedding e z.1) (fun i=>own i)
        (remaining_own e z.1 own hown) j z.2.2 x

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureSupport
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

lemma Law.common_source_support (q : Law X) (p : Law Ω) (f : X→B) (g : Ω→B)
    (h : q.map f=p.map g) (x : X) (hx : q.mass x≠0) :
    ∃ ω,p.mass ω≠0 ∧ g ω=f x := by
  have hf : (p.map g).mass (f x)≠0 := by
    rw [←h]
    exact ne_of_gt ((lt_of_le_of_ne (q.nonneg x) (Ne.symm hx)).trans_le (q.le_map f x))
  exact p.map_support g (f x) hf

namespace ExposureModel
variable {β C ι Θ : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ]

omit [Fintype Θ] [Fintype ι] [DecidableEq ι] in
lemma afterDraw_tagged (M : ExposureModel ι β C) (hp : ∀ z,0<M.remaining z)
    (tag : M.History→Θ) (φ : Θ×(ι→β)→ℝ) :
    (∑ x,(M.afterDraw hp).joint.mass x*φ (tag x.1.1,(M.afterDraw hp).restore x.1 x.2))=
      ∑ x,M.joint.mass x*φ (tag x.1,M.restore x.1 x.2) := by
  rw [joint,Law.sigma_sum,joint,Law.sigma_sum]
  exact M.freshLaw_old hp (fun z=>∑ y,(M.tupleLaw z).mass y*φ (tag z,M.restore z y))

theorem contextual_afterDraw_tagged_map (n k : ℕ) {Ω : Type} [Fintype Ω]
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z) :
    ((contextual n k p θ G e own t).afterDraw hp).joint.map
      (fun x=>(x.1.1.1,((contextual n k p θ G e own t).afterDraw hp).restore x.1 x.2))=
        p.map (fun ω=>(θ ω,G ω)) := by
  ext y
  have he:=afterDraw_tagged (contextual n k p θ G e own t) hp (fun z=>z.1)
    (fun x=>if x=y then 1 else 0)
  have he' := he.trans (contextual_tagged n k p θ G e own t (fun x=>if x=y then 1 else 0))
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using he'

theorem contextual_fresh_source (n k : ℕ) {Ω : Type} [Fintype Ω]
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
    (z : (contextual n k p θ G e own t).FreshHistory)
    (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)
    (y : (contextual n k p θ G e own t).Index z.1→β)
    (hy : ((contextual n k p θ G e own t).tupleLaw z.1).mass y≠0) :
    ∃ ω,p.mass ω≠0 ∧ θ ω=z.1.1 ∧
      ∀ i,G ω ((contextual n k p θ G e own t).origin z.1 i)=y i := by
  let M:=contextual n k p θ G e own t
  obtain ⟨ω,hω,he⟩:=Law.common_source_support (M.afterDraw hp).joint p
    (fun x=>(x.1.1.1,(M.afterDraw hp).restore x.1 x.2)) (fun ω=>(θ ω,G ω))
    (contextual_afterDraw_tagged_map n k p θ G e own t hp) ⟨z,y⟩ (mul_ne_zero hz hy)
  refine ⟨ω,hω,congrArg Prod.fst he,fun i=>?_⟩
  have hh:=congrFun (congrArg Prod.snd he) (M.origin z.1 i)
  exact hh.trans (M.restore_origin z.1 y i)

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_AuxiliaryCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

omit [Finite K] [FiniteDimensional K V] in
lemma directedCollision_le_reciprocal
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (ρ : ℝ) (r s : ℕ) (i j : ι) :
    (directedCollision p Projectivization.rep Projectivization.rep ρ r s i j : ℝ) ≤
      (reciprocalCharges p Projectivization.rep Projectivization.rep ρ r s i j : ℝ) := by
  unfold reciprocalCharges
  exact_mod_cast (le_add_right (le_refl _) :
    directedCollision p Projectivization.rep Projectivization.rep ρ r s i j ≤ _)

theorem integer_good_event_le
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (MA MB κ ρ ε c a : ℝ) (d r : ℕ)
    (hMA : 0<MA) (hMB : 0<MB) (hρ : 0<ρ) (hc : 0 < c)
    (hcap : c≤1-(Module.finrank K V:ℝ)*ρ) (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0)
    (hcharge : (pairInformation p i j:ℝ)+
      (reciprocalCharges p Projectivization.rep Projectivization.rep ρ r (d+1-r) i j:ℝ)≤a) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) MA ((d:ℝ)*log (Nat.card K)) κ ε ay.1 ∧
      goodSecond (p.marginal j) MB ((d:ℝ)*log (Nat.card K)) κ ε ay.2 ∧
      ay.1.rep ay.2.rep=0)) ≤ 2*a/ρ^2 + 2*a/c^2 := by
  apply (projective_integer_incidence p i j MA MB κ ρ ε c d r
    hMA hMB hρ hc hcap hr hγ hκ hu hv hconsistent).trans
  have hdir := directedCollision_le_reciprocal p ρ r (d+1-r) i j
  have hn : (0:ℝ)≤(reciprocalCharges p Projectivization.rep Projectivization.rep
      ρ r (d+1-r) i j:ℝ) := NNReal.coe_nonneg _
  apply add_le_add <;> apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  · linarith only [hcharge, hn]
  · linarith only [hcharge, hdir]

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_BandCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real ReciprocalBands
open scoped Classical BigOperators
noncomputable section

lemma integer_band_rank_bounds {d r : ℕ} {σ C κ gap u v : ℝ}
    (hσ : 0<σ) (hC : 0<C)
    (hu : IntegerBand r σ gap u) (hv : IntegerBand r σ gap v)
    (hsmall : log C+3*κ+gap<σ) :
    (r:ℝ)-1 < (d:ℝ)+1-(log (C*exp (((d:ℝ)+1)*σ-u))+3*κ)/σ ∧
    (d:ℝ)-r < (d:ℝ)+1-(log (C*exp v)+3*κ)/σ := by
  rw [IntegerBand,abs_le] at hu hv
  rw [log_mul hC.ne' (exp_ne_zero _),log_exp,
    log_mul hC.ne' (exp_ne_zero _),log_exp]
  constructor
  · have hh : (log C+(((d:ℝ)+1)*σ-u)+3*κ)/σ < (d:ℝ)+1-((r:ℝ)-1) := by
      apply (div_lt_iff₀ hσ).mpr
      nlinarith [hu.1]
    linarith
  · have hh : (log C+v+3*κ)/σ < (d:ℝ)+1-((d:ℝ)-r) := by
      apply (div_lt_iff₀ hσ).mpr
      nlinarith [hv.2]
    linarith

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

theorem integer_band_event_le
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (C κ gap u v a : ℝ) (d r : ℕ)
    (hdim : Module.finrank K V=d+1) (hC : 0<C) (hr : r≤d+1)
    (hu : IntegerBand r (log (Nat.card K)) gap u)
    (hv : IntegerBand r (log (Nat.card K)) gap v)
    (hsmall : log C+3*κ+gap<log (Nat.card K))
    (hκ : log (200/97)≤κ)
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0)
    (hcharge : (pairInformation p i j:ℝ)+
      (reciprocalCharges p Projectivization.rep Projectivization.rep
        (1/(100*((d:ℝ)+1))) r (d+1-r) i j:ℝ)≤a) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) (C*exp (((d:ℝ)+1)*log (Nat.card K)-u))
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.1 ∧
      goodSecond (p.marginal j) (C*exp v)
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.2 ∧
      ay.1.rep ay.2.rep=0)) ≤ (20000*((d:ℝ)+1)^2+8)*a := by
  have hσ : 0<log (Nat.card K:ℝ) := log_pos (by exact_mod_cast Finite.one_lt_card (α:=K))
  have hd : (0:ℝ)<(d:ℝ)+1 := by positivity
  have he : (Module.finrank K V:ℝ)*(1/(100*((d:ℝ)+1)))=1/100 := by
    rw [hdim,Nat.cast_add,Nat.cast_one]
    field_simp
  obtain ⟨hrA,hrB⟩ := integer_band_rank_bounds (d:=d) hσ hC hu hv hsmall
  have hh := integer_good_event_le p i j
    (C*exp (((d:ℝ)+1)*log (Nat.card K)-u)) (C*exp v) κ
    (1/(100*((d:ℝ)+1))) (1/50) (1/2) a d r
    (by positivity) (by positivity) (by positivity) (by norm_num)
    (by rw [he]; norm_num) hr (by rw [he]; norm_num)
    (by simpa only [he,show (1:ℝ)-1/100-1/50=97/100 by norm_num,
      show (2:ℝ)/(97/100)=200/97 by norm_num] using hκ) hrA hrB hconsistent hcharge
  apply hh.trans_eq
  field_simp
  ring

end
end SharpLogRamsey.Selection

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

lemma owner_early {w n : ℕ} (j : Slot w n) (i : Fin w)
    (h : owner w n j=some (i,false)) : j.1=i ∧ j.2.val<n := by
  unfold owner at h
  split_ifs at h with he hl
  · have hh:=Option.some.inj h
    exact ⟨congrArg Prod.fst hh,he⟩
  · have hh:=congrArg Prod.snd (Option.some.inj h)
    cases hh

lemma owner_late {w n : ℕ} (j : Slot w n) (i : Fin w)
    (h : owner w n j=some (i,true)) : j.1=i ∧ 3*n≤ j.2.val := by
  unfold owner at h
  split_ifs at h with he hl
  · have hh:=congrArg Prod.snd (Option.some.inj h)
    cases hh
  · have hh:=Option.some.inj h
    exact ⟨congrArg Prod.fst hh,hl⟩

lemma owner_between {w n : ℕ} (i : Fin w) (a b : Slot w n)
    (ha : owner w n a=some (i,false)) (hb : owner w n b=some (i,true))
    (x : Fin (2*n)) : position a<position (middle w n (i,x)) ∧
      position (middle w n (i,x))<position b := by
  obtain ⟨ha₁,ha₂⟩:=owner_early a i ha
  obtain ⟨hb₁,hb₂⟩:=owner_late b i hb
  change a.1.val*(4*n)+a.2.val< i.val*(4*n)+(n+x.val) ∧
    i.val*(4*n)+(n+x.val)< b.1.val*(4*n)+b.2.val
  rw [ha₁,hb₁]
  constructor <;> omega

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
lemma model_owner (z : (model w n k p θ G t).History) (i : (model w n k p θ G t).Index z) :
    (model w n k p θ G t).owner z i=owner w (n+k) ((model w n k p θ G t).origin z i) :=
  atRound_owner n k ((p.cond θ z.1).map G) (embedding w (n+k)) (owner w (n+k)) t z.2 i

lemma model_embedding_owner (z : (model w n k p θ G t).History) (b : Block w)
    (x : Fin ((model w n k p θ G t).remaining z)) :
    (model w n k p θ G t).owner z ((model w n k p θ G t).embedding z (b,x))=some b :=
  atRound_embedding_owner n k ((p.cond θ z.1).map G) (embedding w (n+k)) (owner w (n+k))
    (embedding_owner w (n+k)) t z.2 b x

lemma target_origin (z : (model w n k p θ G t).History) (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).origin z (target w n k p θ G t z (i,x))=middle w (n+k) (i,x) :=
  lift_origin _ _ _ _ _

lemma target_owner (z : (model w n k p θ G t).History) (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).owner z (target w n k p θ G t z (i,x))=none := by
  rw [model_owner,target_origin,middle_unowned]

lemma representative_owner (z : (model w n k p θ G t).FreshHistory) (b : Block w) :
    (model w n k p θ G t).owner z.1 ((model w n k p θ G t).representative z b)=some b :=
  model_embedding_owner w n k p θ G t z.1 b (z.2 b)

lemma representative_origin_owner (z : (model w n k p θ G t).FreshHistory) (b : Block w) :
    owner w (n+k) ((model w n k p θ G t).origin z.1
      ((model w n k p θ G t).representative z b))=some b := by
  rw [←model_owner,representative_owner]

lemma target_between (z : (model w n k p θ G t).FreshHistory) (i : Fin w) (x : Fin (2*(n+k))) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false))) <
      position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (i,x))) ∧
    position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (i,x))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,true))) := by
  rw [target_origin]
  exact owner_between i _ _ (representative_origin_owner w n k p θ G t z (i,false))
    (representative_origin_owner w n k p θ G t z (i,true)) x

lemma representative_other (z : (model w n k p θ G t).FreshHistory) (b c : Block w) (hbc : b≠c) :
    (model w n k p θ G t).representative z b∈otherRepresentatives
      ((model w n k p θ G t).embedding z.1) ((model w n k p θ G t).owner z.1) z.2
      ((model w n k p θ G t).representative z c) := by
  apply mem_image.mpr
  refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
  rw [representative_owner]
  exact fun h=>hbc (Option.some.inj h)

lemma target_other (z : (model w n k p θ G t).FreshHistory) (b : Block w)
    (i : Fin w) (x : Fin (2*(n+k))) :
    (model w n k p θ G t).representative z b∈otherRepresentatives
      ((model w n k p θ G t).embedding z.1) ((model w n k p θ G t).owner z.1) z.2
      (target w n k p θ G t z.1 (i,x)) := by
  apply mem_image.mpr
  refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
  rw [target_owner]
  exact Option.some_ne_none _

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_GoodChronology
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
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β]

lemma pairInformation_symm (p : Law (ι→β)) (i j : ι) :
    pairInformation p i j=pairInformation p j i := by
  apply Subtype.ext
  change mutualInfo (p.map (fun x=>(x i,x j)))=mutualInfo (p.map (fun x=>(x j,x i)))
  have he : p.map (fun x=>(x j,x i))=(p.map (fun x=>(x i,x j))).swap := by
    rw [Law.swap_eq_map,Law.map_map]
    rfl
  rw [he]
  simp only [mutualInfo,Law.swap_fst,Law.swap_snd,entropy_swap,add_comm]

variable {A B K V : Type} [Fintype A] [Fintype B] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma reciprocalCharges_symm (p : Law (ι→A×B)) (v : B→V) (w : A→Module.Dual K V)
    (ρ : ℝ) (r s : ℕ) (i j : ι) :
    reciprocalCharges p v w ρ r s i j=reciprocalCharges p v w ρ r s j i :=
  add_comm _ _

variable {C X : Type} [Fintype C]

lemma good_charge_reversed (p : Law (ι→β)) (e : C×X↪ι) (own : ι→Option C)
    (c : ι→ι→NNReal) (hc : ∀ i j,c i j=c j i) (J D a : ℝ) (f : C→X)
    (i j : ι) (hi : i∉badIndices p e own c J D a f)
    (hj : j∈otherRepresentatives e own f i) :
    (pairInformation p j i:ℝ)+(c j i:ℝ)≤a := by
  rw [pairInformation_symm p j i,hc j i]
  exact ((not_badIndices p e own c J D a f i).mp hi).2 j hj

lemma good_charge_either (p : Law (ι→β)) (e : C×X↪ι) (own : ι→Option C)
    (c : ι→ι→NNReal) (hc : ∀ i j,c i j=c j i) (J D a : ℝ) (f : C→X)
    (i j : ι)
    (h : (i∉badIndices p e own c J D a f ∧ j∈otherRepresentatives e own f i) ∨
      (j∉badIndices p e own c J D a f ∧ i∈otherRepresentatives e own f j)) :
    (pairInformation p i j:ℝ)+(c i j:ℝ)≤a := by
  rcases h with h|h
  · exact ((not_badIndices p e own c J D a f i).mp h.1).2 j h.2
  · exact good_charge_reversed p e own c hc J D a f j i h.1 h.2

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.ExposureModel
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ ι β C : Type} [Fintype Ω] [Fintype Θ] [Fintype ι]
  [DecidableEq ι] [Fintype β] [Fintype C]
variable (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
  (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
  (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
  (z : (contextual n k p θ G e own t).FreshHistory)
  (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)

include hp hz

lemma prepared_pair_property (P : Θ→ι→ι→β→β→Prop)
    (hP : ∀ ω,p.mass ω≠0→∀ i j,P (θ ω) i j (G ω i) (G ω j))
    (i j : (contextual n k p θ G e own t).Index z.1) :
    ∀ y,((contextual n k p θ G e own t).tupleLaw z.1).mass y≠0→
      P z.1.1 ((contextual n k p θ G e own t).origin z.1 i)
        ((contextual n k p θ G e own t).origin z.1 j) (y i) (y j) := by
  intro y hy
  obtain ⟨ω,hω,hθ,hG⟩:=contextual_fresh_source n k p θ G e own t hp z hz y hy
  simpa only [hθ,hG i,hG j] using hP ω hω ((contextual n k p θ G e own t).origin z.1 i)
    ((contextual n k p θ G e own t).origin z.1 j)

end
end SharpLogRamsey.Selection.ExposureModel

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.ExposureModel
open Finset Real ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ ι C : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype Ω] [Fintype Θ]
  [Fintype ι] [DecidableEq ι] [Fintype C]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
variable (n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→ι→Projectivization K (Module.Dual K V)×Projectivization K V)
  (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
  (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
  (z : (contextual n k p θ G e own t).FreshHistory)
  (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)
  (pos : ι→ℕ)
  (hcon : ∀ ω,p.mass ω≠0→∀ i j,pos i<pos j→
    (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0)
include hp hz hcon

omit [Finite K] [FiniteDimensional K V] in
lemma prepared_consistency
    (i j : (contextual n k p θ G e own t).Index z.1)
    (hij : pos ((contextual n k p θ G e own t).origin z.1 i)<
      pos ((contextual n k p θ G e own t).origin z.1 j)) :
    ∀ y,((contextual n k p θ G e own t).tupleLaw z.1).mass y≠0→
      (y i).1.rep (y j).2.rep=0→(y j).1.rep (y i).2.rep=0 := by
  intro y hy
  exact prepared_pair_property n k p θ G e own t hp z hz
    (fun _ i j a b=>pos i<pos j→a.1.rep b.2.rep=0→b.1.rep a.2.rep=0)
    hcon i j y hy hij

theorem prepared_integer_event
    (i j : (contextual n k p θ G e own t).Index z.1)
    (hij : pos ((contextual n k p θ G e own t).origin z.1 i)<
      pos ((contextual n k p θ G e own t).origin z.1 j))
    (P κ gap u v J D a : ℝ) (d r : ℕ)
    (hdim : Module.finrank K V=d+1) (hP : 0<P) (hr : r≤d+1)
    (hu : IntegerBand r (log (Nat.card K)) gap u)
    (hv : IntegerBand r (log (Nat.card K)) gap v)
    (hsmall : log P+3*κ+gap<log (Nat.card K)) (hκ : log (200/97)≤κ)
    (hgood :
      let M:=contextual n k p θ G e own t
      let c:=reciprocalCharges (M.tupleLaw z.1) Projectivization.rep Projectivization.rep
        (1/(100*((d:ℝ)+1))) r (d+1-r)
      (i∉badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1) c J D a z.2 ∧
        j∈otherRepresentatives (M.embedding z.1) (M.owner z.1) z.2 i) ∨
      (j∉badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1) c J D a z.2 ∧
        i∈otherRepresentatives (M.embedding z.1) (M.owner z.1) z.2 j)) :
    let q:=(contextual n k p θ G e own t).tupleLaw z.1
    ((q.marginal i).fst.prod (q.marginal j).snd).event (univ.filter (fun ay=>
      goodFirst (q.marginal i) (P*exp (((d:ℝ)+1)*log (Nat.card K)-u))
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.1 ∧
      goodSecond (q.marginal j) (P*exp v) ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.2 ∧
      ay.1.rep ay.2.rep=0))≤(20000*((d:ℝ)+1)^2+8)*a := by
  let M:=contextual n k p θ G e own t
  apply integer_band_event_le (M.tupleLaw z.1) i j P κ gap u v a d r hdim hP hr
    hu hv hsmall hκ
    (prepared_consistency n k p θ G e own t hp z hz pos hcon i j hij)
  exact good_charge_either (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
    _ (reciprocalCharges_symm _ _ _ _ _ _) J D a z.2 i j hgood

end
end SharpLogRamsey.Selection.ExposureModel

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PreparedChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution
open scoped Classical
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

lemma representative_window (z : (model w n k p θ G t).FreshHistory) (i : Fin w) (b : Bool) :
    ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,b))).1=i := by
  have hh:=representative_origin_owner w n k p θ G t z (i,b)
  cases b
  · exact (owner_early _ i hh).1
  · exact (owner_late _ i hh).1

lemma representative_before (z : (model w n k p θ G t).FreshHistory)
    (i j : Fin w) (hij : i<j) (b c : Bool) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,b))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (j,c))) :=
  owner_before_next i j hij _ _ (representative_window w n k p θ G t z i b)
    (representative_window w n k p θ G t z j c)

lemma representatives_straddle (z : (model w n k p θ G t).FreshHistory) (i : Fin w) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,true))) := by
  have he:=owner_early _ i (representative_origin_owner w n k p θ G t z (i,false))
  have hl:=owner_late _ i (representative_origin_owner w n k p θ G t z (i,true))
  unfold position
  rw [he.1,hl.1]
  exact Nat.add_lt_add_left
    (he.2.trans_le ((Nat.le_mul_of_pos_left _ (by decide : 0<3)).trans hl.2)) _

lemma target_before_later (z : (model w n k p θ G t).FreshHistory)
    (i j : Fin w) (hij : i≤j) (x : Fin (2*(n+k))) :
    position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (i,x))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (j,true))) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · rw [target_origin]
    exact owner_before_next i j h _ _ rfl (representative_window w n k p θ G t z j true)
  · exact (target_between w n k p θ G t z i x).2

lemma earlier_before_target (z : (model w n k p θ G t).FreshHistory)
    (i j : Fin w) (hij : i≤j) (x : Fin (2*(n+k))) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false))) <
      position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (j,x))) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · rw [target_origin]
    exact owner_before_next i j h _ _ (representative_window w n k p θ G t z i false) rfl
  · exact (target_between w n k p θ G t z i x).1

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
lemma goodTarget_not_bad (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1)) (i : Fin w)
    (j : Fin (goodMiddle w n k p θ G t z bad i).card) :
    goodTarget w n k p θ G t z bad i j∉bad := by
  exact (mem_filter.mp ((goodMiddle w n k p θ G t z bad i).orderEmbOfFin_mem rfl j)).2

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_GoodRealization
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
variable {A B J : Type*} [Fintype A] [Fintype B] [Fintype J] [DecidableEq J]
lemma Law.marginal_fst_map (q : Law (J→A×B)) (i : J) :
    (q.marginal i).fst=q.map (fun y=>(y i).1) := by
  rw [←Law.map_fst,Law.marginal,Law.map_comp]
  rfl
lemma Law.marginal_snd_map (q : Law (J→A×B)) (i : J) :
    (q.marginal i).snd=q.map (fun y=>(y i).2) := by
  rw [←Law.map_snd,Law.marginal,Law.map_comp]
  rfl
lemma Law.map_bad_sum (q : Law A) (f : A→B) (S : Finset B) :
    (∑ y,q.mass y*(if f y∈S then (0:ℝ) else 1))=(q.map f).event (univ\S) := by
  rw [←q.sum_map f (fun b=>if b∈S then (0:ℝ) else 1)]
  have hs : univ\S=univ.filter (fun b=>b∉S) := by ext b; simp
  rw [Law.event,hs]
  simp only [sum_filter,ite_not,mul_ite,mul_zero,mul_one]
end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.goodDec
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
  (z : (model w n k p θ G t).FreshHistory)

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.goodBanks
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.goodBlockDec
theorem good_population_realization
    (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)
    (bad : Finset ((model w n k p θ G t).Index z.1))
    (live : Finset (Fin w)) (fallback : Fin w)
    (hgood : ∀ i∈live,∀ c,((model w n k p θ G t).representative z (i,c))∉bad)
    (GA : (model w n k p θ G t).Index z.1→Finset (Projectivization K (Module.Dual K V)))
    (GB : (model w n k p θ G t).Index z.1→Finset (Projectivization K V))
    (MA MB κA κB : (model w n k p θ G t).Index z.1→ℝ)
    (X : ∀ i,i∉bad→AuxiliarySupport (((model w n k p θ G t).tupleLaw z.1).marginal i).fst
      (GA i) (MA i) (κA i))
    (Y : ∀ i,i∉bad→AuxiliarySupport (((model w n k p θ G t).tupleLaw z.1).marginal i).snd
      (GB i) (MB i) (κB i))
    (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i∈live,
      let a:=(model w n k p θ G t).representative z (i,false)
      let c:=(model w n k p θ G t).representative z (i,true)
      (Nat.card K:ℝ)^(d+3)*exp (-b)≤(MA a*exp (-κA a)/2)*(MB c*exp (-κB c)/2))
    (hR : ∀ y,((model w n k p θ G t).tupleLaw z.1).mass y≠0→∀ i,
      SharpLogRamsey.Incidence.Incident (y i).2 (y i).1)
    (ε δA δB : ℝ) (hε : 0≤ε)
    (hinc : ∀ i j,
      position ((model w n k p θ G t).origin z.1 i)<position ((model w n k p θ G t).origin z.1 j)→
      ((i∉bad ∧ j∈otherRepresentatives ((model w n k p θ G t).embedding z.1)
        ((model w n k p θ G t).owner z.1) z.2 i) ∨
       (j∉bad ∧ i∈otherRepresentatives ((model w n k p θ G t).embedding z.1)
        ((model w n k p θ G t).owner z.1) z.2 j))→
      goodIncidence (((model w n k p θ G t).tupleLaw z.1).marginal i).fst
        (((model w n k p θ G t).tupleLaw z.1).marginal j).snd (GA i) (GB j)≤ε)
    (hbadA : ∀ i,i∉bad→(((model w n k p θ G t).tupleLaw z.1).marginal i).fst.event (univ\GA i)≤δA)
    (hbadB : ∀ i,i∉bad→(((model w n k p θ G t).tupleLaw z.1).marginal i).snd.event (univ\GB i)≤δB) :
    ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) ((model w n k p θ G t).tupleLaw z.1),
      (∑ a,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass a*
        ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
        (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
          (fun _=>chronoRead b)
          (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) a
          (liveTree live fallback) (univ,univ)).length))≤
        (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*
          treeError (Nat.card K) τ (liveTree live fallback).height ε ε ε δA δB := by
  let M:=model w n k p θ G t
  let early:=fun i=>M.representative z (i,false)
  let late:=fun i=>M.representative z (i,true)
  apply book.live_realization hdim hb hτ hτsmall (M.tupleLaw z.1) live fallback
    (fun i=>(M.tupleLaw z.1|>.marginal (early i)).fst)
    (fun i=>(M.tupleLaw z.1|>.marginal (late i)).snd)
    (fun i=>GA (early i)) (fun i=>GB (late i))
    (fun i=>MA (early i)) (fun i=>MB (late i)) (fun i=>κA (early i)) (fun i=>κB (late i))
    (fun i=>X (early i) (hgood i i.property false))
    (fun i=>Y (late i) (hgood i i.property true))
    (fun i _=>hMA (early i)) (fun i _=>hMB (late i)) hprod
    (fun i=>(goodMiddle w n k p θ G t z bad i).card)
    (fun y i j=>y (goodTarget w n k p θ G t z bad i j))
    (fun y hy i _ j=>hR y hy _) (fun i j=>GA (goodTarget w n k p θ G t z bad i j))
    (fun i j=>GB (goodTarget w n k p θ G t z bad i j)) ε ε ε δA δB hε hε hε
  · intro i hi j hj hij
    apply hinc _ _ (representative_before w n k p θ G t z i j hij false true)
    exact Or.inl ⟨hgood i hi false,representative_other w n k p θ G t z (j,true) (i,false) (by simp)⟩
  · intro i hi
    apply hinc _ _ (representatives_straddle w n k p θ G t z i)
    exact Or.inl ⟨hgood i hi false,representative_other w n k p θ G t z (i,true) (i,false) (by simp)⟩
  · intro i _ j m _ him
    rw [←Law.marginal_fst_map (M.tupleLaw z.1) (goodTarget w n k p θ G t z bad i j)]
    apply hinc
    · exact target_before_later w n k p θ G t z i m him _
    · exact Or.inl ⟨goodTarget_not_bad w n k p θ G t z bad i j,target_other w n k p θ G t z (m,true) i _⟩
  · intro i _ j m _ hmi
    rw [←Law.marginal_snd_map (M.tupleLaw z.1) (goodTarget w n k p θ G t z bad i j)]
    apply hinc
    · exact earlier_before_target w n k p θ G t z m i hmi _
    · exact Or.inr ⟨goodTarget_not_bad w n k p θ G t z bad i j,target_other w n k p θ G t z (m,false) i _⟩
  · intro i _ j
    rw [Law.map_bad_sum,←Law.marginal_fst_map]
    exact hbadA _ (goodTarget_not_bad w n k p θ G t z bad i j)
  · intro i _ j
    rw [Law.map_bad_sum,←Law.marginal_snd_map]
    exact hbadB _ (goodTarget_not_bad w n k p θ G t z bad i j)
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real ReciprocalBands
open scoped Classical BigOperators
noncomputable section

lemma reciprocal_window_product (q : ℝ) (r : ℕ) (hq : 0<q)
    (P κ u v gap b : ℝ) (hP : 1≤P) (huv : u-v≤gap)
    (hb : gap+2*κ+log 4≤b) :
    q^r*exp (-b)≤(P*exp ((r:ℝ)*log q-u)*exp (-κ)/2)*
      (P*exp v*exp (-κ)/2) := by
  have he : (P*exp ((r:ℝ)*log q-u)*exp (-κ)/2)*
      (P*exp v*exp (-κ)/2)=P^2*q^r*exp (v-u-2*κ-log 4) := by
    rw [exp_sub (v-u-2*κ) (log 4),exp_log (by norm_num : (0:ℝ)<4)]
    have hx : exp (v-u-2*κ)=exp (v-u)*exp (-κ)*exp (-κ) := by
      rw [←exp_add,←exp_add]
      congr 1
      ring
    rw [hx,exp_sub,exp_sub,exp_nat_mul,exp_log hq]
    ring
  rw [he]
  have hb' : -b≤v-u-2*κ-log 4 := by linarith
  have hp : (1:ℝ)≤P^2 := by nlinarith
  calc
    _ ≤ q^r*exp (v-u-2*κ-log 4) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hb') (pow_nonneg hq.le _)
    _ = (1:ℝ)*q^r*exp (v-u-2*κ-log 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (pow_nonneg hq.le _)) (exp_pos _).le

lemma integer_window_difference {r : ℕ} {σ gap u v : ℝ}
    (hu : IntegerBand r σ gap u) (hv : IntegerBand r σ gap v) : u-v≤2*gap := by
  rw [IntegerBand,abs_le] at hu hv
  linarith

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_IntegerRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.intDec
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
local instance intSlotDec_r433873_1 : DecidableEq (Slot w (n+k)) :=
  @instDecidableEqProd (Fin w) (Fin (4*(n+k))) (@instDecidableEqFin w) (@instDecidableEqFin (4*(n+k)))
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.intBlockDec
variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (z : (model w n k p θ G t).FreshHistory)
  (hz : ((model w n k p θ G t).freshLaw hp).mass z≠0)
local notation "M" => model w n k p θ G t
local notation "q" => ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst z)

include hp hz

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.intBanks
theorem integer_population_realization_oai
    (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)
    (r : ℕ) (hr : r≤d+3) (κ gap J D a δ : ℝ)
    (u : (M).Index z.1→ℝ)
    (hband : ∀ i,IntegerBand r (log (Nat.card K)) gap (u i))
    (hsmall : log 1024+3*κ+gap<log (Nat.card K)) (hκ : log (200/97)≤κ)
    (hbudget : 2*gap+2*κ+log 4≤b) (ha : 0≤a)
    (hcon : ∀ ω,p.mass ω≠0→∀ i j,position i<position j→
      (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0)
    (hf : ∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0)
    (fallback : Fin w)
    (hsupp :
      let c:=reciprocalCharges q Projectivization.rep Projectivization.rep
        (1/(100*((d:ℝ)+3))) r (d+3-r)
      let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
      ∀ i,i∉bad→
      let qi:=(q).marginal i
      let MA:=1024*exp (((d+3:ℕ):ℝ)*log (Nat.card K)-u i)
      let MB:=1024*exp (u i)
      let L:=((d+2:ℕ):ℝ)*log (Nat.card K)
      Nonempty (AuxiliarySupport qi.fst (univ.filter (goodFirst qi MA L κ (1/50))) MA κ) ∧
      Nonempty (AuxiliarySupport qi.snd (univ.filter (goodSecond qi MB L κ (1/50))) MB κ) ∧
      qi.fst.event (univ.filter (fun x=>¬goodFirst qi MA L κ (1/50) x))≤δ ∧
      qi.snd.event (univ.filter (fun x=>¬goodSecond qi MB L κ (1/50) x))≤δ) :
    let c:=reciprocalCharges q Projectivization.rep Projectivization.rep
      (1/(100*((d:ℝ)+3))) r (d+3-r)
    let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
    let live:=univ\badWindows ((M).representative z) bad
    ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) q,
      (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
        ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
        (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
          (fun _=>chronoRead b)
          (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) tab
          (liveTree live fallback) (univ,univ)).length))≤
        (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*
          treeError (Nat.card K) τ (liveTree live fallback).height
            ((20000*((d:ℝ)+3)^2+8)*a) ((20000*((d:ℝ)+3)^2+8)*a)
            ((20000*((d:ℝ)+3)^2+8)*a) δ δ := by
  dsimp only
  let c:=reciprocalCharges q Projectivization.rep Projectivization.rep
      (1/(100*((d:ℝ)+3))) r (d+3-r)
  let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
  let live:=univ\badWindows ((M).representative z) bad
  let MA:=fun i=>1024*exp (((d+3:ℕ):ℝ)*log (Nat.card K)-u i)
  let MB:=fun i=>1024*exp (u i)
  let L:=((d+2:ℕ):ℝ)*log (Nat.card K)
  let GA:=fun i=>univ.filter (goodFirst ((q).marginal i) (MA i) L κ (1/50))
  let GB:=fun i=>univ.filter (goodSecond ((q).marginal i) (MB i) L κ (1/50))
  have hgood : ∀ i∈live,∀ c,(M).representative z (i,c)∉bad := by
    intro i hi v
    have hh:¬((M).representative z (i,false)∈bad ∨ (M).representative z (i,true)∈bad) := by
      simpa only [live,mem_sdiff,mem_univ,true_and,badWindows,mem_filter,true_and] using hi
    cases v
    · exact fun h=>hh (Or.inl h)
    · exact fun h=>hh (Or.inr h)
  apply good_population_realization w n k p θ G t z hdim book hb hτ hτsmall bad live fallback hgood
    GA GB MA MB (fun _=>κ) (fun _=>κ)
    (fun i hi=>(hsupp i hi).1.some) (fun i hi=>(hsupp i hi).2.1.some)
    (fun i=>by dsimp [MA]; positivity) (fun i=>by dsimp [MB]; positivity)
  · intro i hi
    exact reciprocal_window_product (Nat.card K) (d+3) (by exact_mod_cast Finite.card_pos)
      1024 κ _ _ (2*gap) b (by norm_num)
      (integer_window_difference (hband _) (hband _)) hbudget
  · intro y hy i
    exact prepared_pair_property n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz (fun _ _ _ x _=>x.1.rep x.2.rep=0)
      (fun ω h i _=>hf ω h i) i i y hy
  · exact mul_nonneg (by positivity) ha
  · intro i j hij hgood
    have hh:=prepared_integer_event n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz position hcon i j hij 1024 κ gap (u i) (u j) J D a
      (d+2) r (by simpa [Nat.add_assoc] using hdim) (by norm_num) (by omega)
      (hband i) (hband j) hsmall hκ
    specialize hh (by simpa only [Nat.add_assoc,Nat.cast_add,Nat.cast_ofNat,
      show (d:ℝ)+2+1=(d:ℝ)+3 by ring] using hgood)
    simpa only [goodIncidence,GA,GB,MA,MB,L,mem_filter,mem_univ,true_and,
      Nat.cast_add,Nat.cast_ofNat,show (d:ℝ)+2+1=(d:ℝ)+3 by ring] using hh
  · intro i hi
    have he : univ\GA i=univ.filter (fun x=>¬goodFirst ((q).marginal i) (MA i) L κ (1/50) x) := by
      ext x
      simp only [GA,mem_sdiff,mem_univ,true_and,mem_filter]
    rw [he]
    exact (hsupp i hi).2.2.1
  · intro i hi
    have he : univ\GB i=univ.filter (fun x=>¬goodSecond ((q).marginal i) (MB i) L κ (1/50) x) := by
      ext x
      simp only [GB,mem_sdiff,mem_univ,true_and,mem_filter]
    rw [he]
    exact (hsupp i hi).2.2.2
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Selection.Windows.integer_population_realization_oai := @OAI.SharpLogRamsey.Selection.Windows.integer_population_realization_oai
