-- Prove2me | solution 1 for OAI.SharpLogRamsey.Selection.Windows.eventually_open_movement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:43:44.297249+00:00
-- url     : https://prove2.me/submissions/d7e1f34d-e852-47ff-8eda-73e039c9fb49

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

theorem Law.mass_le_one (p : Law α) (a : α) : p.mass a ≤ 1 := by
  rw [← p.total]
  exact single_le_sum (fun b hb => p.nonneg b) (mem_univ a)

theorem entropy_nonneg (p : Law α) : 0 ≤ entropy p := by
  apply neg_nonneg.mpr
  exact sum_nonpos fun a ha => mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
    (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))

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

theorem entropy_subadditive (p : Law (α × β)) : entropy p ≤ entropy p.fst+entropy p.snd := by
  have h := mutualInfo_nonneg p
  unfold mutualInfo at h
  linarith

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
variable {α β : Type*} [Fintype α] [Fintype β]

theorem Law.small_atoms (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) {c : ℝ} (hc : 0 ≤ c) :
    p.event (univ.filter (fun a => p.mass a < c)) ≤ S.card*c := by
  have h (a : α) : (if p.mass a < c then p.mass a else 0) ≤
      if a ∈ S then c else 0 := by
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha]; split_ifs <;> linarith
    · rw [ite_eq_right ha,hs a ha]; split_ifs <;> rfl
  have hh := sum_le_sum fun a (_ : a ∈ univ) => h a
  simpa [Law.event, sum_filter] using hh

theorem negative_log_part (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) :
    (∑ a, p.mass a*max (-(Real.log (p.mass a)+L)) 0) ≤ S.card*Real.exp (-L) := by
  have pointwise (a : α) : p.mass a*max (-(Real.log (p.mass a)+L)) 0 ≤
      if a ∈ S then Real.exp (-L) else 0 := by
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha]
      by_cases hp : p.mass a = 0
      · simp [hp,Real.exp_nonneg]
      have hp0 : 0 < p.mass a := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      by_cases hz : 0 ≤ -(Real.log (p.mass a)+L)
      · rw [max_eq_left hz]
        have hh := mul_log_div_ge (p.nonneg a) (Real.exp_nonneg (-L))
          (fun h => False.elim ((Real.exp_ne_zero _) h))
        rw [Real.log_div hp (Real.exp_ne_zero _),Real.log_exp] at hh
        nlinarith
      · rw [max_eq_right (le_of_not_ge hz),mul_zero]
        exact Real.exp_nonneg _
    · rw [ite_eq_right ha,hs a ha,zero_mul]
  have h := sum_le_sum fun a (_ : a ∈ univ) => pointwise a
  simpa using h

theorem positive_log_part (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) :
    (∑ a, p.mass a*max (Real.log (p.mass a)+L) 0) ≤
      L-entropy p+S.card*Real.exp (-L) := by
  have pointwise (a : α) : p.mass a*max (Real.log (p.mass a)+L) 0 =
      p.mass a*(Real.log (p.mass a)+L)+
      p.mass a*max (-(Real.log (p.mass a)+L)) 0 := by
    by_cases h : 0 ≤ Real.log (p.mass a)+L
    · rw [max_eq_left h,max_eq_right (by linarith)]; ring
    · rw [max_eq_right (le_of_not_ge h),max_eq_left (by linarith)]; ring
  simp_rw [pointwise,sum_add_distrib,mul_add,sum_add_distrib,← sum_mul,p.total,one_mul]
  have h := negative_log_part p S hs L
  unfold entropy
  linarith

theorem Law.heavy_atoms (p : Law α) (S : Finset α)
    (hs : ∀ a, a ∉ S → p.mass a = 0) (L : ℝ) {K : ℝ} (hK : 0 < K) :
    p.event (univ.filter (fun a => Real.exp (K-L) < p.mass a)) ≤
      (L-entropy p+S.card*Real.exp (-L))/K := by
  apply (le_div_iff₀ hK).mpr
  have h (a : α) : (if Real.exp (K-L) < p.mass a then p.mass a else 0)*K ≤
      p.mass a*max (Real.log (p.mass a)+L) 0 := by
    by_cases ha : Real.exp (K-L) < p.mass a
    · rw [ite_eq_left ha]
      have hp : 0 < p.mass a := (Real.exp_pos _).trans ha
      have hh := Real.log_lt_log (Real.exp_pos (K-L)) ha
      rw [Real.log_exp] at hh
      have hle : K ≤ max (Real.log (p.mass a)+L) 0 :=
        (by linarith : K ≤ Real.log (p.mass a)+L).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left hle (p.nonneg a)
    · rw [ite_eq_right ha,zero_mul]
      exact mul_nonneg (p.nonneg _) (le_max_right _ _)
  have hh := (sum_le_sum fun a (_ : a ∈ univ) => h a).trans (positive_log_part p S hs L)
  simpa only [Law.event,sum_filter,sum_mul] using hh

theorem Law.bad_conditional_mass (p : Law (α × β)) (E : Finset (α × β))
    {ρ : ℝ} (hρ : 0 < ρ) :
    p.snd.event (univ.filter (fun b =>
      ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E)))) ≤ p.event E/ρ := by
  apply (le_div_iff₀ hρ).mpr
  have hh (b : β) :
      (if ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E))
        then p.snd.mass b else 0)*ρ ≤ ∑ a, if (a,b) ∈ E then p.mass (a,b) else 0 := by
    have he : p.snd.mass b*((p.condFst b).event (univ.filter (fun a => (a,b) ∈ E))) =
        ∑ a, if (a,b) ∈ E then p.mass (a,b) else 0 := by
      simp only [Law.event,sum_filter,mul_sum,mul_ite,mul_zero,p.snd_mul_condFst]
    rw [← he]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left h.le (p.snd.nonneg b)
    · rw [zero_mul]
      exact mul_nonneg (p.snd.nonneg b) ((p.condFst b).event_nonneg _)
  have h := sum_le_sum fun b (_ : b ∈ univ) => hh b
  have he : (∑ z, if z ∈ E then p.mass z else 0) = p.event E := by
    rw [← sum_filter]
    simp [Law.event]
  change (∑ b with ρ < (p.condFst b).event (univ.filter (fun a => (a,b) ∈ E)), p.snd.mass b)*ρ ≤ _
  rw [sum_filter,sum_mul,← he,Fintype.sum_prod_type,sum_comm]
  exact h

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

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

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

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma not_contained_of_rank_sum (W : Submodule K V) (U : Submodule K (Module.Dual K V))
    {r s : ℕ} (hW : r ≤ Module.finrank K W) (hU : s ≤ Module.finrank K U)
    (hsum : Module.finrank K V < r+s) : ¬U ≤ W.dualAnnihilator := by
  intro h
  have hle := Submodule.finrank_mono h
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

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

theorem badSecond_mass (p : Law (α × β)) (S : Finset (α × β))
    (hs : ∀ x, x ∉ S → p.mass x = 0) (D : Finset β)
    (hD : ∀ b, b ∉ D → p.snd.mass b = 0)
    (M L K ρ : ℝ) (hM : 0 < M) (hcard : (D.card:ℝ) ≤ M)
    (hK : 0 < K) (hρ : 0 < ρ) :
    p.snd.event (univ.filter (fun b => ¬goodSecond p M L K ρ b)) ≤
      Real.exp (-K)+(L-entropy p+S.card*Real.exp (-L))/(K*ρ) := by
  have hsub : univ.filter (fun b => ¬goodSecond p M L K ρ b) ⊆
      univ.filter (fun b => p.snd.mass b < Real.exp (-K)/M) ∪
      univ.filter (fun b => ρ < conditionalHeavy p L K b) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and,goodSecond,not_and_or,not_le,mem_union] at hb ⊢
    exact hb
  have hsmall := p.snd.small_atoms D hD (c := Real.exp (-K)/M) (by positivity)
  have hs2 : D.card*(Real.exp (-K)/M) ≤ Real.exp (-K) := by
    calc
      _ ≤ M*(Real.exp (-K)/M) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp
  have hheavy := p.bad_conditional_mass (univ.filter (fun x => Real.exp (K-L) < p.mass x)) hρ
  have hheavy' : p.snd.event (univ.filter (fun b => ρ < conditionalHeavy p L K b)) ≤
      (L-entropy p+S.card*Real.exp (-L))/(K*ρ) := by
    have he := p.heavy_atoms S hs L hK
    have hh := hheavy.trans (div_le_div_of_nonneg_right he hρ.le)
    convert hh using 1 <;> try rfl
    · simp only [conditionalHeavy,mem_filter,mem_univ,true_and]
      with_unfolding_all rfl
    · rw [div_div]
  exact (p.snd.event_mono hsub).trans ((p.snd.event_union_le _ _).trans
    (add_le_add (hsmall.trans hs2) hheavy'))

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
open scoped BigOperators Classical
open Finset
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem reciprocal_open_incidence (p : Law ((A × B) × (A × B)))
    (v : B → V) (w : A → Module.Dual K V) {ρ : ℝ} (hρ : 0 < ρ)
    (goodA : A → Prop) (goodB : B → Prop)
    {r s : ℕ} (hsum : Module.finrank K V < r+s)
    (hW : ∀ a, goodA a → r ≤ Module.finrank K (firstCore (K := K) p.fst v ρ a))
    (hU : ∀ y, goodB y → s ≤ Module.finrank K (secondCore p.snd w ρ y))
    (hconsistent : ∀ z, p.mass z ≠ 0 →
      w z.1.1 (v z.2.2) = 0 → w z.2.1 (v z.1.2) = 0) :
    (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay : A × B =>
      goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0)) ≤ 2*mutualInfo p/ρ^2 := by
  have he := exceptional_core_mass p.fst p.snd v w hρ goodA goodB
  have heq : (univ.filter (fun ay : A × B =>
      (goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) ∧
      ¬coreContained p.fst p.snd v w ρ ay.1 ay.2)) =
      univ.filter (fun ay : A × B => goodA ay.1 ∧ goodB ay.2 ∧ w ay.1 (v ay.2) = 0) := by
    ext ay
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨And.left, fun h => ⟨h,?_⟩⟩
    exact not_contained_of_rank_sum _ _ (hW _ h.1) (hU _ h.2.1) hsum
  rw [heq] at he
  have hz : p.event (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0)) = 0 := by
    apply sum_eq_zero
    intro z hz
    by_contra hn
    exact (mem_filter.mp hz).2.2 (hconsistent z hn (mem_filter.mp hz).2.1)
  have ht := mutualInfo_event_transfer p (univ.filter (fun z : (A × B) × (A × B) =>
      w z.1.1 (v z.2.2) = 0 ∧ w z.2.1 (v z.1.2) ≠ 0))
  rw [hz,add_zero] at ht
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  simpa only [mul_comm] using he.trans ht

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

theorem projective_open_incidence
    (p : Law ((Projectivization K (Module.Dual K V)×Projectivization K V)×
      (Projectivization K (Module.Dual K V)×Projectivization K V)))
    (MA MB κ ρ ε : ℝ) (d r : ℕ) (hMA : 0<MA) (hMB : 0<MB) (hρ : 0<ρ)
    (hd : Module.finrank K V=d+1) (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)+1-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (hconsistent : ∀ z,p.mass z≠0 →
      z.1.1.rep z.2.2.rep=0 → z.2.1.rep z.1.2.rep=0) :
    (p.fst.fst.prod p.snd.snd).event (univ.filter (fun ay =>
      goodFirst p.fst MA ((d:ℝ)*log (Nat.card K)) κ ε ay.1 ∧
      goodSecond p.snd MB ((d:ℝ)*log (Nat.card K)) κ ε ay.2 ∧
      ay.1.rep ay.2.rep=0))≤2*mutualInfo p/ρ^2 := by
  apply reciprocal_open_incidence p Projectivization.rep Projectivization.rep hρ _ _
    (r:=r) (s:=d+2-r) (by omega) _ _ hconsistent
  · intro a ha
    exact round_core_rank hu (goodFirst_core_dimension p.fst MA κ ρ ε d a hMA hρ.le ha hγ hκ)
  · intro y hy
    have hh := goodSecond_core_dimension p.snd MB κ ρ ε d y hMB hρ.le hy
      (by simpa only [Subspace.dual_finrank_eq] using hγ)
      (by simpa only [Subspace.dual_finrank_eq] using hκ)
    apply round_core_rank (x:=(d:ℝ)+1-(log MB+3*κ)/log (Nat.card K)) _ hh
    have hc : ((d+2-r:ℕ):ℝ)=(d:ℝ)+2-r := by
      rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_ofNat]
    rw [hc]
    linarith

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

theorem entropy_le_cross (p : Law α) (q : α → ℝ) (hq : ∀ a, 0<q a)
    (hqt : ∑ a, q a ≤ 1) : entropy p ≤ -∑ a, p.mass a*Real.log (q a) := by
  have h (a : α) : p.mass a-q a ≤
      p.mass a*Real.log (p.mass a)-p.mass a*Real.log (q a) := by
    have H := mul_log_div_ge (p.nonneg a) (hq a).le (by intro hh; exact ((hq a).ne' hh).elim)
    by_cases ha : p.mass a=0
    · simpa [ha] using H
    · rw [Real.log_div ha (hq a).ne', mul_sub] at H
      exact H
  have HH := sum_le_sum (fun a (_ : a∈univ) => h a)
  simp only [sum_sub_distrib, p.total] at HH
  unfold entropy
  linarith

lemma geometric_subprob (l : α → ℕ) (hl : Function.Injective l) {r : ℝ}
    (hr : 0 < r) (hr1 : r<1) : ∑ a, (1-r)*r^(l a) ≤ 1 := by
  have hs : (∑ n ∈ univ.image l, r^n) ≤ ∑' n : ℕ, r^n := by
    exact (summable_geometric_of_lt_one hr.le hr1).sum_le_tsum _ (fun _ _ => pow_nonneg hr.le _)
  rw [sum_image (fun _ _ _ _ he => hl he), tsum_geometric_of_lt_one hr.le hr1] at hs
  rw [← mul_sum]
  have H := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hr1.le)
  simpa only [mul_inv_cancel₀ (sub_pos.mpr hr1).ne'] using H

theorem integer_entropy (p : Law α) (l : α → ℕ) (hl : Function.Injective l)
    (M : ℝ) (hM : 0<M) (hm : ∑ a, p.mass a*(l a:ℝ) ≤ M) :
    entropy p ≤ Real.log (M+1)+1 := by
  let r := M/(M+1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hc : 1-r=1/(M+1) := by dsimp [r]; field_simp; ring
  have H := entropy_le_cross p (fun a => (1-r)*r^(l a))
    (fun a => mul_pos (sub_pos.mpr hr1) (pow_pos hr _))
    (geometric_subprob l hl hr hr1)
  have he : -∑ a, p.mass a*Real.log ((1-r)*r^(l a)) =
      Real.log (M+1) + (∑ a, p.mass a*(l a:ℝ))*Real.log (1+1/M) := by
    have her : Real.log r = -Real.log (1+1/M) := by
      have heq : r=(1+1/M)⁻¹ := by dsimp [r]; field_simp
      rw [heq,Real.log_inv]
    have hlogc : Real.log (1-r) = -Real.log (M+1) := by
      rw [hc, Real.log_div one_ne_zero (by positivity : M+1≠0), Real.log_one, zero_sub]
    simp_rw [Real.log_mul (sub_pos.mpr hr1).ne' (pow_pos hr _).ne',
      Real.log_pow, hlogc,her]
    simp only [mul_add, mul_neg, sum_add_distrib, sum_neg_distrib,
      ← mul_assoc, ← sum_mul,p.total,one_mul]
    ring
  rw [he] at H
  have hlog0 : 0≤Real.log (1+1/M) := Real.log_nonneg (by
    have h : (0:ℝ)≤1/M := by positivity
    linarith)
  have hlog := Real.log_le_sub_one_of_pos (show 0<1+1/M by positivity)
  have hh := mul_le_mul_of_nonneg_left hlog hM.le
  have hx : M*(1+1/M-1)=1 := by field_simp; ring
  rw [hx] at hh
  have hm' := mul_le_mul_of_nonneg_right hm hlog0
  linarith

lemma massLevel_mean (p : Law α) :
    (∑ a, p.mass a*(massLevel p a:ℝ)) ≤ entropy p := by
  unfold entropy
  rw [←sum_neg_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : p.mass a=0
  · simp [hp]
  have hlog : 0 ≤ -Real.log (p.mass a) :=
    neg_nonneg.mpr (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))
  have H := mul_le_mul_of_nonneg_left (Nat.floor_le hlog) (p.nonneg a)
  simpa only [massLevel, mul_neg] using H

lemma level_entropy (p : Law α) :
    entropy (p.map (levelIndex p)) ≤ Real.log (entropy p+2)+1 := by
  have hh := integer_entropy (p.map (levelIndex p)) Subtype.val Subtype.val_injective
    (entropy p+1) (by linarith [entropy_nonneg p])
  have hm : ∑ n : Levels p, (p.map (levelIndex p)).mass n*(n.val:ℝ) ≤ entropy p+1 := by
    rw [p.sum_map]
    exact (massLevel_mean p).trans (by linarith)
  simpa only [show entropy p+1+1=entropy p+2 by ring] using hh hm

lemma same_level_weight (p : Law α) {a b : α} (ha : 0<p.mass a) (hb : 0<p.mass b)
    (he : massLevel p a=massLevel p b) : p.mass a ≤ Real.exp 1*p.mass b := by
  have ha0 : 0 ≤ -Real.log (p.mass a) :=
    neg_nonneg.mpr (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))
  have h₁ := Nat.floor_le ha0
  have h₂ := Nat.lt_floor_add_one (-Real.log (p.mass b))
  change -(Real.log (p.mass b)) < (massLevel p b:ℝ)+1 at h₂
  have hle : Real.log (p.mass a) ≤ 1+Real.log (p.mass b) := by
    change (massLevel p a:ℝ) ≤ -Real.log (p.mass a) at h₁
    rw [he] at h₁
    linarith
  calc
    _ = Real.exp (Real.log (p.mass a)) := (Real.exp_log ha).symm
    _ ≤ Real.exp (1+Real.log (p.mass b)) := Real.exp_le_exp.mpr hle
    _ = _ := by rw [Real.exp_add,Real.exp_log hb]

lemma Law.onEvent_mean (p : Law α) (E : Finset α) (hE : 0<p.event E) (f : α→ℝ) :
    ∑ a : E, (p.onEvent E hE).mass a*f a = (∑ a∈E, p.mass a*f a)/p.event E := by
  simp only [Law.onEvent,div_mul_eq_mul_div,←sum_div]
  congr 1
  exact sum_coe_sort E (fun a => p.mass a*f a)

theorem support_average (p : Law α) (l : α→β) (G : β→Finset α)
    (R : Finset β) (hR : (1:ℝ)/2 ≤ (p.map l).event R)
    (hG : ∀ b∈R, 0<(G b).card)
    (hfiber : ∀ b∈R, ∀ a∈G b, l a=b)
    (hcharge : ∀ b∈R, ∀ a∈G b,
      (p.map l).mass b ≤ Real.exp 1*2*(G b).card*p.mass a) (a : α) :
    ∑ b : R, ((p.map l).onEvent R (by linarith)).mass b *
      (if a∈G b then 1/((G b).card:ℝ) else 0) ≤ 4*Real.exp 1*p.mass a := by
  have hp := p.nonneg a
  have hR0 : 0<(p.map l).event R := by linarith
  have he := (p.map l).onEvent_mean R hR0
    (fun b => if a∈G b then 1/((G b).card:ℝ) else 0)
  rw [he]
  have hsum : (∑ b∈R, (p.map l).mass b*(if a∈G b then 1/((G b).card:ℝ) else 0)) ≤
      2*Real.exp 1*p.mass a := by
    by_cases ha : l a∈R
    · rw [sum_eq_single_of_mem (l a) ha]
      · by_cases hg : a∈G (l a)
        · simp only [ite_eq_left hg,one_div]
          have H := hcharge (l a) ha a hg
          have hc : (0:ℝ)<(G (l a)).card := by exact_mod_cast hG (l a) ha
          have H' : (p.map l).mass (l a)/((G (l a)).card:ℝ) ≤
              2*Real.exp 1*p.mass a := (div_le_iff₀ hc).mpr (by nlinarith [H])
          simpa only [div_eq_mul_inv] using H'
        · simp only [ite_eq_right hg,mul_zero]
          positivity
      · intro b hb hba
        have hab : a∉G b := by intro hh; exact hba (hfiber b hb a hh).symm
        simp [hab]
    · have hz : ∀ b∈R, a∉G b := by
        intro b hb hh
        exact ha ((hfiber b hb a hh) ▸ hb)
      have : (∑ b∈R, (p.map l).mass b*(if a∈G b then 1/((G b).card:ℝ) else 0))=0 := by
        apply sum_eq_zero
        intro b hb
        simp [hz b hb]
      rw [this]
      positivity
  apply (div_le_iff₀ hR0).mpr
  calc
    _ ≤ 2*Real.exp 1*p.mass a := hsum
    _ = (4*Real.exp 1*p.mass a)*(1/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)

theorem partition_entropy (p : Law α) (l : α→β) (S : Finset α)
    (hs : ∀ a, a∉S → p.mass a=0) :
    entropy p ≤ entropy (p.map l)+
      ∑ b, (p.map l).mass b*Real.log (S.filter (fun a => l a=b)).card := by
  let T (b : β) := S.filter (fun a => l a=b)
  have hm (b : β) : ∑ a∈T b, p.mass a=(p.map l).mass b := by
    apply sum_subset (by
      intro a ha
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩)
    intro a ha hna
    apply hs
    intro haS
    apply hna
    exact mem_filter.mpr ⟨haS,(mem_filter.mp ha).2⟩
  have hlog (b : β) :
      (p.map l).mass b*Real.log ((p.map l).mass b)-
      (p.map l).mass b*Real.log (T b).card ≤ ∑ a∈T b, p.mass a*Real.log (p.mass a) := by
    have H := log_sum (T b) p.mass (fun _ => 1) (fun a _ => p.nonneg a)
      (by intros; norm_num) (by intro i hi hf; norm_num at hf)
    simp only [div_one,sum_const,nsmul_eq_mul,mul_one,hm] at H
    by_cases hb : (p.map l).mass b=0
    · simpa [hb] using H
    have hc : (T b).card≠0 := by
      intro he
      have hz : T b=∅ := card_eq_zero.mp he
      exact hb (by simpa [hz] using (hm b).symm)
    rw [Real.log_div hb (by exact_mod_cast hc),mul_sub] at H
    exact H
  have H := sum_le_sum (fun b (_ : b∈univ) => hlog b)
  have he : (∑ b, ∑ a∈T b, p.mass a*Real.log (p.mass a))=
      ∑ a, p.mass a*Real.log (p.mass a) := by
    rw [show (∑ b, ∑ a∈T b, p.mass a*Real.log (p.mass a))=
      ∑ a∈S, p.mass a*Real.log (p.mass a) from sum_fiberwise S l _]
    exact sum_subset (subset_univ S) (fun a _ hna => by rw [hs a hna,zero_mul])
  rw [sum_sub_distrib,he] at H
  unfold entropy
  dsimp only [T] at H
  linarith

theorem partition_loss (p : Law α) (l : α→β) (S : Finset α)
    (hs : ∀ a, a∉S → p.mass a=0) (loss : β→ℝ) (J : ℝ)
    (hc : ∀ b, 0<(p.map l).mass b →
      Real.log (S.filter (fun a => l a=b)).card ≤ J-loss b/2) :
    ∑ b, (p.map l).mass b*loss b ≤ 2*(J-entropy p+entropy (p.map l)) := by
  have hh (b : β) : (p.map l).mass b*Real.log (S.filter (fun a => l a=b)).card ≤
      (p.map l).mass b*(J-loss b/2) := by
    by_cases hz : (p.map l).mass b=0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (hc b (lt_of_le_of_ne ((p.map l).nonneg b) (Ne.symm hz)))
        ((p.map l).nonneg b)
  have H := (partition_entropy p l S hs).trans (add_le_add_right (sum_le_sum (fun b _ => hh b)) _)
  simp only [mul_sub,←mul_div_assoc,sum_sub_distrib,←sum_mul,←sum_div,(p.map l).total,one_mul] at H
  linarith

lemma levelSet_mass (p : Law α) (b : Levels p) :
    ∑ a∈levelSet p b, p.mass a=(p.map (levelIndex p)).mass b := by
  simp only [Law.map,levelSet,sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : 0<p.mass a
  · simp [ha]
  · have hz : p.mass a=0 := le_antisymm (le_of_not_gt ha) (p.nonneg a)
    simp [hz]

lemma levelSet_charge (p : Law α) (b : Levels p) {a : α} (ha : a∈levelSet p b) :
    (p.map (levelIndex p)).mass b ≤ Real.exp 1*(levelSet p b).card*p.mass a := by
  rw [←levelSet_mass p b]
  have ha' := (mem_filter.mp ha).2
  calc
    _ ≤ ∑ _x∈levelSet p b, Real.exp 1*p.mass a := by
      apply sum_le_sum
      intro x hx
      have hx' := (mem_filter.mp hx).2
      apply same_level_weight p hx'.1 ha'.1
      exact congrArg Subtype.val (hx'.2.trans ha'.2.symm)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

lemma bad_level_charge (p : Law α) (b : Levels p) (good : Finset α)
    (hhalf : 2*((levelSet p b)∩good).card < (levelSet p b).card) :
    (p.map (levelIndex p)).mass b ≤
      2*Real.exp 1*(∑ a∈levelSet p b\good, p.mass a) := by
  let S := levelSet p b
  let B := S\good
  have hS : 0<S.card := by dsimp [S]; omega
  have hc : S.card ≤ 2*B.card := by
    have he := card_sdiff_add_card_inter S good
    dsimp [S,B] at *
    omega
  have hrow (b' : α) (hb' : b'∈B) :
      (p.map (levelIndex p)).mass b ≤ Real.exp 1*S.card*p.mass b' :=
    levelSet_charge p b (mem_sdiff.mp hb').1
  have H := sum_le_sum (fun a (ha : a∈B) => hrow a ha)
  simp only [sum_const,nsmul_eq_mul,←mul_sum] at H
  have hm := (p.map (levelIndex p)).nonneg b
  have Hc : (S.card:ℝ) ≤ 2*(B.card:ℝ) := by exact_mod_cast hc
  have Hm := mul_le_mul_of_nonneg_right Hc hm
  have H₂ : (S.card:ℝ)*(p.map (levelIndex p)).mass b ≤
      (S.card:ℝ)*(2*Real.exp 1*(∑ a∈B,p.mass a)) := by nlinarith
  exact (mul_le_mul_iff_right₀ (show (0:ℝ)<S.card by exact_mod_cast hS)).mp H₂

lemma good_level_charge (p : Law α) (b : Levels p) (good : Finset α)
    (hhalf : (levelSet p b).card ≤ 2*((levelSet p b)∩good).card)
    {a : α} (ha : a∈(levelSet p b)∩good) :
    (p.map (levelIndex p)).mass b ≤
      Real.exp 1*2*((levelSet p b)∩good).card*p.mass a := by
  have hc : ((levelSet p b).card:ℝ) ≤ 2*(((levelSet p b)∩good).card:ℝ) := by exact_mod_cast hhalf
  have hpa := p.nonneg a
  have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Real.exp_nonneg 1)) hpa
  exact (levelSet_charge p b (mem_inter.mp ha).1).trans (by nlinarith [H])

lemma Law.map_comp {γ : Type*} [Fintype γ] (p : Law α) (f : α→β) (g : β→γ) :
    (p.map f).map g=p.map (g∘f) := by
  exact p.map_map f g

lemma Law.map_prod_marginals {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law (α×β)) (f : α→γ) (g : β→δ) :
    (p.map (fun z => (f z.1,g z.2))).fst=p.fst.map f ∧
    (p.map (fun z => (f z.1,g z.2))).snd=p.snd.map g := by
  constructor
  · rw [←Law.map_fst,Law.map_comp,←Law.map_fst,Law.map_comp]
    rfl
  · rw [←Law.map_snd,Law.map_comp,←Law.map_snd,Law.map_comp]
    rfl

lemma endpoint_levels_entropy (p : Law (α×β)) :
    entropy (p.map (fun z => (levelIndex p.fst z.1,levelIndex p.snd z.2))) ≤
      Real.log (entropy p.fst+2)+Real.log (entropy p.snd+2)+2 := by
  have H := entropy_subadditive (p.map (fun z => (levelIndex p.fst z.1,levelIndex p.snd z.2)))
  have hm := p.map_prod_marginals (levelIndex p.fst) (levelIndex p.snd)
  rw [hm.1,hm.2] at H
  linarith [level_entropy p.fst,level_entropy p.snd]

lemma levelLoss_nonneg (p : Law α) {A : ℝ} (b : Levels p)
    (hcap : ((levelSet p b).card:ℝ) ≤ A) : 0≤levelLoss p A b := by
  unfold levelLoss
  by_cases hz : (levelSet p b).card=0
  · simp [hz]
  · have hc : (0:ℝ)<(levelSet p b).card := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    exact Real.log_nonneg ((le_div_iff₀ hc).mpr (by simpa using hcap))

lemma levelLoss_size (p : Law α) {A K : ℝ} (hA : 0<A) (b : Levels p)
    (hc : 0<(levelSet p b).card) (hl : levelLoss p A b≤K) :
    A*Real.exp (-K) ≤ (levelSet p b).card := by
  have hc' : (0:ℝ)<(levelSet p b).card := by exact_mod_cast hc
  have H := Real.exp_le_exp.mpr hl
  rw [levelLoss,Real.exp_log (div_pos hA hc')] at H
  have H' := (div_le_iff₀ hc').mp H
  calc
    _ ≤ (Real.exp K*(levelSet p b).card)*Real.exp (-K) :=
      mul_le_mul_of_nonneg_right H' (Real.exp_nonneg _)
    _ = _ := by rw [mul_right_comm,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

lemma level_bad_total (p : Law α) (good : Finset α) :
    (∑ b : Levels p, ∑ a∈levelSet p b\good, p.mass a)=p.event (univ\good) := by
  have he (b : Levels p) : levelSet p b\good =
      univ.filter (fun a => 0<p.mass a ∧ levelIndex p a=b ∧ a∉good) := by
    ext a
    simp [levelSet,and_assoc]
  have he' : univ\good=univ.filter (fun a : α => a∉good) := by ext; simp
  change (∑ b : Levels p, ∑ a∈levelSet p b\good,p.mass a)=∑ a∈univ\good,p.mass a
  simp_rw [he,he',sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases ha : 0<p.mass a
  · by_cases hg : a∈good <;> simp [ha,hg]
  · have hz := le_antisymm (le_of_not_gt ha) (p.nonneg a)
    simp [hz]

lemma retained_mass (p : Law α) (good : Finset α) {A K : ℝ} (hK : 0<K)
    (hcap : ∀ b, ((levelSet p b).card:ℝ)≤A) :
    1-(∑ b, (p.map (levelIndex p)).mass b*levelLoss p A b)/K-
      2*Real.exp 1*p.event (univ\good) ≤
      (p.map (levelIndex p)).event (retainedLevels p good A K) := by
  let q := p.map (levelIndex p)
  let R := retainedLevels p good A K
  have hpoint (b : Levels p) : q.mass b ≤
      (if b∈R then q.mass b else 0)+q.mass b*levelLoss p A b/K+
      2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by
    have hm := q.nonneg b
    have hl := levelLoss_nonneg p b (hcap b)
    have hb0 : 0≤∑ a∈levelSet p b\good,p.mass a := sum_nonneg (fun a _ => p.nonneg a)
    by_cases hb : b∈R
    · rw [ite_eq_left hb]
      have hh : 0≤q.mass b*levelLoss p A b/K := by positivity
      have hh' : 0≤2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by positivity
      linarith
    rw [ite_eq_right hb,zero_add]
    by_cases hc : (levelSet p b).card=0
    · have h0 : q.mass b=0 := by
        rw [show q.mass b=(∑ a∈levelSet p b,p.mass a) from (levelSet_mass p b).symm]
        simp [card_eq_zero.mp hc]
      simp only [h0,zero_mul,zero_div,zero_add]
      positivity
    by_cases hlow : levelLoss p A b≤K
    · have hf : 2*((levelSet p b)∩good).card < (levelSet p b).card := by
        by_contra! hn
        apply hb
        exact mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero hc,hlow,hn⟩
      have H := bad_level_charge p b good hf
      have hh : 0≤q.mass b*levelLoss p A b/K := by positivity
      exact H.trans (by linarith)
    · have H : q.mass b ≤ q.mass b*levelLoss p A b/K := by
        apply (le_div_iff₀ hK).mpr
        exact mul_le_mul_of_nonneg_left (le_of_not_ge hlow) hm
      have hh : 0≤2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by positivity
      linarith
  have H := sum_le_sum (fun b (_ : b∈univ) => hpoint b)
  simp only [sum_add_distrib,←sum_div,←mul_sum,q.total,←sum_filter] at H
  rw [level_bad_total p good] at H
  have heR : univ.filter (fun b => b∈R)=R := by ext; simp
  rw [heR] at H
  change 1≤q.event R+(∑ b,q.mass b*levelLoss p A b)/K+2*Real.exp 1*p.event (univ\good) at H
  change 1-_/_-_≤q.event R
  linarith

theorem auxiliary_supports (p : Law α) (good : Finset α) {A K : ℝ}
    (hA : 0<A) (hK : 0<K) (hcap : ∀ b, ((levelSet p b).card:ℝ)≤A)
    (hbudget : (∑ b, (p.map (levelIndex p)).mass b*levelLoss p A b)/K+
      2*Real.exp 1*p.event (univ\good) ≤ 1/2) :
    ∃ ρ : Law (retainedLevels p good A K),
      (∀ b : retainedLevels p good A K,
        A*Real.exp (-K)/2 ≤ (((levelSet p b)∩good).card:ℝ) ∧
        (((levelSet p b)∩good).card:ℝ)≤A) ∧
      ∀ a, (∑ b : retainedLevels p good A K, ρ.mass b*
        (if a∈(levelSet p b)∩good then 1/((((levelSet p b)∩good).card):ℝ) else 0))
        ≤ 4*Real.exp 1*p.mass a := by
  let R := retainedLevels p good A K
  have hR : (1:ℝ)/2 ≤ (p.map (levelIndex p)).event R := by
    have H := retained_mass p good hK hcap
    change 1-_/_-_≤(p.map (levelIndex p)).event R at H
    linarith
  let ρ := (p.map (levelIndex p)).onEvent R (by linarith)
  refine ⟨ρ, ?_, ?_⟩
  · intro b
    have hb := (mem_filter.mp b.property).2
    have hh : ((levelSet p b).card:ℝ) ≤ 2*(((levelSet p b)∩good).card:ℝ) := by
      exact_mod_cast hb.2.2
    have hl := levelLoss_size p hA b hb.1 hb.2.1
    have hc : (((levelSet p b)∩good).card:ℝ) ≤ (levelSet p b).card := by
      exact_mod_cast card_le_card inter_subset_left
    exact ⟨by linarith, hc.trans (hcap b)⟩
  · intro a
    apply support_average p (levelIndex p) (fun b => levelSet p b∩good) R hR
    · intro b hb
      have hh := (mem_filter.mp hb).2
      have hp := hh.1
      have hs := hh.2.2
      omega
    · intro b hb a ha
      exact (mem_filter.mp (mem_inter.mp ha).1).2.2
    · intro b hb a ha
      exact good_level_charge p b good ((mem_filter.mp hb).2.2.2) ha

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

theorem mixing_loss_log {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    {A B C : ℝ} (hA : 0<A) (hB : 0<B) (hC : 1≤C)
    (hc : A*B≤C*(Nat.card K:ℝ)^(n+3))
    (hS : 0<S.card) (hT : 0<T.card)
    (hSA : (S.card:ℝ)≤A) (hTB : (T.card:ℝ)≤B)
    (he : 0 < incidenceCount S T) :
    Real.log (incidenceCount S T) ≤
      Real.log (2*C*(Nat.card K:ℝ)^(n+2))-
        (Real.log (A/S.card)+Real.log (B/T.card))/2 := by
  let x := Real.log (A/S.card)
  let y := Real.log (B/T.card)
  let z := Real.exp (-(x+y)/2)
  have hS' : (0:ℝ)<S.card := by exact_mod_cast hS
  have hT' : (0:ℝ)<T.card := by exact_mod_cast hT
  have hx : 0≤x := Real.log_nonneg ((one_le_div hS').mpr hSA)
  have hy : 0≤y := Real.log_nonneg ((one_le_div hT').mpr hTB)
  have hz : 0<z := Real.exp_pos _
  have hz1 : z≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hrS : Real.exp (-x)=(S.card:ℝ)/A := by
    rw [Real.exp_neg,Real.exp_log (div_pos hA hS')]
    simp
  have hrT : Real.exp (-y)=(T.card:ℝ)/B := by
    rw [Real.exp_neg,Real.exp_log (div_pos hB hT')]
    simp
  have hez : z^2=Real.exp (-x)*Real.exp (-y) := by
    rw [sq,←Real.exp_add,show -(x+y)/2+(-(x+y)/2)=(-x)+(-y) by ring,Real.exp_add]
  have hprod : (S.card:ℝ)*T.card=A*B*z^2 := by
    rw [hez,hrS,hrT]
    field_simp
  have H := mixing_cell_scale hdim S T hC hz.le hz1
    (show (S.card:ℝ)*T.card≤C*(Nat.card K:ℝ)^(n+3)*z^2 by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg z))
  have Hlog := Real.log_le_log (show (0:ℝ)< incidenceCount S T by exact_mod_cast he) H
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  rw [Real.log_mul (by positivity : 2*C*(Nat.card K:ℝ)^(n+2)≠0) hz.ne',
    show Real.log z=-(x+y)/2 from Real.log_exp _] at Hlog
  exact Hlog.trans_eq (by dsimp [x,y]; ring)

end SharpLogRamsey.Incidence

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

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

lemma positiveSupport_zero (p : Law α) (a : α) (ha : a∉positiveSupport p) : p.mass a=0 := by
  simp only [positiveSupport,mem_filter,mem_univ,true_and,not_lt] at ha
  exact le_antisymm ha (p.nonneg a)

lemma positiveSupport_cell_mass (p : Law α) (f : α→β) (b : β) :
    ∑ a∈(positiveSupport p).filter (fun a => f a=b),p.mass a=(p.map f).mass b := by
  apply sum_subset (by
    intro a ha
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩)
  intro a ha hna
  apply positiveSupport_zero
  intro hs
  exact hna (mem_filter.mpr ⟨hs,(mem_filter.mp ha).2⟩)

lemma positive_cell_nonempty (p : Law α) (f : α→β) (b : β) (hb : 0<(p.map f).mass b) :
    ((positiveSupport p).filter (fun a => f a=b)).Nonempty := by
  by_contra hn
  have he := not_nonempty_iff_eq_empty.mp hn
  have H := positiveSupport_cell_mass p f b
  rw [he,sum_empty] at H
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Incidence
open SharpLogRamsey.Selection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma endpoint_cell_subset
    (p : Law (Projectivization K V × Projectivization K (Module.Dual K V)))
    (hs : ∀ z, 0<p.mass z → Incident z.1 z.2)
    (b : Levels p.fst × Levels p.snd) :
    (positiveSupport p).filter (fun z => endpointLabels p z=b) ⊆
      (((levelSet p.fst b.1).product (levelSet p.snd b.2)).filter (fun z => Incident z.1 z.2)) := by
  intro z hz
  have hp := (mem_filter.mp (mem_filter.mp hz).1).2
  have hl := (mem_filter.mp hz).2
  have ha : (levelIndex p.fst z.1)=b.1 := congrArg Prod.fst hl
  have hb : (levelIndex p.snd z.2)=b.2 := congrArg Prod.snd hl
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,hp.trans_le (p.le_fst z.1 z.2),ha⟩,
      mem_filter.mpr ⟨mem_univ _,hp.trans_le (p.le_snd z.1 z.2),hb⟩⟩,hs z hp⟩

theorem reciprocal_level_losses {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K V × Projectivization K (Module.Dual K V)))
    (hs : ∀ z, 0<p.mass z → Incident z.1 z.2)
    {A B C : ℝ} (hA : 0<A) (hB : 0<B) (hC : 1≤C)
    (hc : A*B≤C*(Nat.card K:ℝ)^(n+3))
    (hSA : ∀ b, ((levelSet p.fst b).card:ℝ)≤A)
    (hTB : ∀ b, ((levelSet p.snd b).card:ℝ)≤B) :
    (∑ b, (p.fst.map (levelIndex p.fst)).mass b*levelLoss p.fst A b)+
      (∑ b, (p.snd.map (levelIndex p.snd)).mass b*levelLoss p.snd B b) ≤
        2*(Real.log (2*C*(Nat.card K:ℝ)^(n+2))-entropy p+
          Real.log (entropy p.fst+2)+Real.log (entropy p.snd+2)+2) := by
  classical
  let l := endpointLabels p
  let loss := fun b : Levels p.fst × Levels p.snd => levelLoss p.fst A b.1+levelLoss p.snd B b.2
  have hcell (b : Levels p.fst × Levels p.snd) (hb : 0<(p.map l).mass b) :
      Real.log ((positiveSupport p).filter (fun z => l z=b)).card ≤
        Real.log (2*C*(Nat.card K:ℝ)^(n+2))-loss b/2 := by
    let S := (positiveSupport p).filter (fun z => l z=b)
    have hn := positive_cell_nonempty p l b hb
    obtain ⟨z,hz⟩ := hn
    have hsub := endpoint_cell_subset p hs b
    have hz' := mem_product.mp (mem_filter.mp (hsub (by simpa only [l] using hz))).1
    have hAS : 0<(levelSet p.fst b.1).card := card_pos.mpr ⟨z.1,hz'.1⟩
    have hBT : 0<(levelSet p.snd b.2).card := card_pos.mpr ⟨z.2,hz'.2⟩
    have hcount : S.card≤ incidenceCount (levelSet p.fst b.1) (levelSet p.snd b.2) := by
      rw [incidenceCount_eq_card]
      exact card_le_card hsub
    have hSn : 0<S.card := card_pos.mpr ⟨z,by simpa only [S,mem_filter] using hz⟩
    have HD := mixing_loss_log hdim (levelSet p.fst b.1) (levelSet p.snd b.2)
      hA hB hC hc hAS hBT (hSA b.1) (hTB b.2) (hSn.trans_le hcount)
    have Hlog : Real.log S.card≤Real.log (incidenceCount (levelSet p.fst b.1) (levelSet p.snd b.2)) :=
      Real.log_le_log (by exact_mod_cast hSn) (by exact_mod_cast hcount)
    exact Hlog.trans HD
  have H := partition_loss p l (positiveSupport p) (positiveSupport_zero p) loss
    (Real.log (2*C*(Nat.card K:ℝ)^(n+2))) (by
      intro b hb
      simpa only [l] using hcell b hb)
  have he : (∑ b, (p.map l).mass b*loss b)=
      (∑ b, (p.fst.map (levelIndex p.fst)).mass b*levelLoss p.fst A b)+
      (∑ b, (p.snd.map (levelIndex p.snd)).mass b*levelLoss p.snd B b) := by
    rw [p.sum_map l loss]
    simp only [loss,l,endpointLabels,mul_add,sum_add_distrib]
    rw [p.fst.sum_map (levelIndex p.fst) (levelLoss p.fst A),
      p.snd.sum_map (levelIndex p.snd) (levelLoss p.snd B)]
    apply congrArg₂ (·+·)
    · simp only [Law.fst,Fintype.sum_prod_type,sum_mul]
    · simp only [Law.snd,Fintype.sum_prod_type,sum_mul]
      rw [sum_comm]
  rw [he] at H
  have HH := endpoint_levels_entropy p
  change entropy (p.map l)≤_ at HH
  linarith

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

lemma auxiliary_good_mixture (p : Law A) (good : Finset A) (M K : ℝ)
    (ρ : Law (retainedLevels p good M K))
    (hρ : ∀ a, (∑ b : retainedLevels p good M K, ρ.mass b *
      (if a ∈ levelSet p b ∩ good then 1 / ((levelSet p b ∩ good).card : ℝ) else 0))
      ≤ 4 * exp 1 * p.mass a) :
    ∀ a, SupportMixtures.mixture ρ.mass (fun b => levelSet p b ∩ good) a ≤
      (4 * exp 1) * (if a ∈ good then p.mass a else 0) := by
  intro a
  by_cases ha : a ∈ good
  · simpa only [ite_eq_left ha, SupportMixtures.mixture, SupportMixtures.kernel] using hρ a
  · simp [SupportMixtures.mixture, SupportMixtures.kernel, ha]

theorem actual_auxiliary_incidence (p : Law A) (q : Law B)
    (goodA : Finset A) (goodB : Finset B) (MA MB K : ℝ)
    (ρ : Law (retainedLevels p goodA MA K))
    (τ : Law (retainedLevels q goodB MB K))
    (hρ : ∀ a, (∑ b : retainedLevels p goodA MA K, ρ.mass b *
      (if a ∈ levelSet p b ∩ goodA then 1 / ((levelSet p b ∩ goodA).card : ℝ) else 0))
      ≤ 4 * exp 1 * p.mass a)
    (hτ : ∀ a, (∑ b : retainedLevels q goodB MB K, τ.mass b *
      (if a ∈ levelSet q b ∩ goodB then 1 / ((levelSet q b ∩ goodB).card : ℝ) else 0))
      ≤ 4 * exp 1 * q.mass a)
    (R : A → B → Prop) :
    (∑ a, ∑ b, ρ.mass a * τ.mass b *
      (((((levelSet p a ∩ goodA) ×ˢ (levelSet q b ∩ goodB)).filter
        (fun z => R z.1 z.2)).card : ℝ) /
        (((levelSet p a ∩ goodA).card : ℝ) * (levelSet q b ∩ goodB).card))) ≤
      (4 * exp 1)^2 * (p.prod q).event
        (univ.filter (fun z => z.1 ∈ goodA ∧ z.2 ∈ goodB ∧ R z.1 z.2)) := by
  have H := SupportMixtures.independent_pairing_le ρ.mass τ.mass
    (fun b => levelSet p b ∩ goodA) (fun b => levelSet q b ∩ goodB)
    (fun a b => if R a b then (1:ℝ) else 0)
    (fun a => if a ∈ goodA then p.mass a else 0)
    (fun b => if b ∈ goodB then q.mass b else 0)
    (4 * exp 1) (4 * exp 1) ρ.nonneg τ.nonneg (by intros; split_ifs <;> norm_num)
    (auxiliary_good_mixture p goodA MA K ρ hρ)
    (auxiliary_good_mixture q goodB MB K τ hτ)
  simpa only [SupportMixtures.kernel_incidence, good_pairing_eq_event, pow_two] using H

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

theorem actual_auxiliary_target_left (p : Law A) (q : Law B)
    (goodA : Finset A) (goodB : Finset B) (MA K : ℝ)
    (ρ : Law (retainedLevels p goodA MA K))
    (hρ : ∀ a, (∑ b : retainedLevels p goodA MA K, ρ.mass b *
      (if a ∈ levelSet p b ∩ goodA then 1 / ((levelSet p b ∩ goodA).card : ℝ) else 0))
      ≤ 4 * exp 1 * p.mass a)
    (R : A → B → Prop) :
    (∑ b, ρ.mass b * SupportMixtures.pairing
      (SupportMixtures.kernel (levelSet p b ∩ goodA))
      (fun y => if y ∈ goodB then q.mass y else 0)
      (fun a y => if R a y then 1 else 0)) ≤
      (4 * exp 1) * (p.prod q).event
        (univ.filter (fun z => z.1 ∈ goodA ∧ z.2 ∈ goodB ∧ R z.1 z.2)) := by
  have H := SupportMixtures.one_sided_pairing_le ρ.mass
    (fun b => levelSet p b ∩ goodA)
    (fun a => if a ∈ goodA then p.mass a else 0)
    (fun y => if y ∈ goodB then q.mass y else 0)
    (fun a y => if R a y then (1:ℝ) else 0) (4 * exp 1) ρ.nonneg
    (by intro y; split_ifs <;> simp [q.nonneg])
    (by intros; split_ifs <;> norm_num)
    (auxiliary_good_mixture p goodA MA K ρ hρ)
  simpa only [good_pairing_eq_event] using H

theorem actual_auxiliary_target_right (p : Law A) (q : Law B)
    (goodA : Finset A) (goodB : Finset B) (MB K : ℝ)
    (τ : Law (retainedLevels q goodB MB K))
    (hτ : ∀ a, (∑ b : retainedLevels q goodB MB K, τ.mass b *
      (if a ∈ levelSet q b ∩ goodB then 1 / ((levelSet q b ∩ goodB).card : ℝ) else 0))
      ≤ 4 * exp 1 * q.mass a)
    (R : A → B → Prop) :
    (∑ b, τ.mass b * SupportMixtures.pairing
      (fun a => if a ∈ goodA then p.mass a else 0)
      (SupportMixtures.kernel (levelSet q b ∩ goodB))
      (fun a y => if R a y then 1 else 0)) ≤
      (4 * exp 1) * (p.prod q).event
        (univ.filter (fun z => z.1 ∈ goodA ∧ z.2 ∈ goodB ∧ R z.1 z.2)) := by
  have H := actual_auxiliary_target_left q p goodB goodA MB K τ hτ (fun b a => R a b)
  rw [← good_pairing_eq_event q p goodB goodA (fun b a => R a b)] at H
  rw [pairing_reverse (fun b => if b ∈ goodB then q.mass b else 0)] at H
  have he (b : retainedLevels q goodB MB K) :
      SupportMixtures.pairing (SupportMixtures.kernel (levelSet q b ∩ goodB))
        (fun a => if a ∈ goodA then p.mass a else 0)
        (fun y a => if R a y then (1:ℝ) else 0) =
      SupportMixtures.pairing (fun a => if a ∈ goodA then p.mass a else 0)
        (SupportMixtures.kernel (levelSet q b ∩ goodB))
        (fun a y => if R a y then (1:ℝ) else 0) := pairing_reverse _ _ _
  simpa only [he, good_pairing_eq_event] using H

end
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

lemma Law.swap_condFst (p : Law (A × B)) (a : A) (ha : p.fst.mass a ≠ 0) :
    p.swap.condFst a = p.condSnd a := by
  ext endpoint
  exact (p.swap.condFst_mass a ha endpoint).trans (p.condSnd_mass a ha endpoint).symm

lemma goodSecond_swap (p : Law (A × B)) {M : ℝ} (hM : 0 < M)
    (L κ ε : ℝ) (a : A) : goodSecond p.swap M L κ ε a ↔ goodFirst p M L κ ε a := by
  unfold goodSecond goodFirst conditionalHeavy
  simp only [Law.swap_snd]
  constructor <;> intro h
  · have ha : p.fst.mass a ≠ 0 := (lt_of_lt_of_le (by positivity) h.1).ne'
    rw [Law.swap_condFst p a ha] at h
    exact h
  · have ha : p.fst.mass a ≠ 0 := (lt_of_lt_of_le (by positivity) h.1).ne'
    rw [Law.swap_condFst p a ha]
    exact h

theorem badFirst_mass (p : Law (A × B)) (S : Finset (A × B))
    (hs : ∀ x, x ∉ S → p.mass x = 0) (D : Finset A)
    (hD : ∀ a, a ∉ D → p.fst.mass a = 0)
    (M L κ ε : ℝ) (hM : 0 < M) (hcard : (D.card:ℝ) ≤ M)
    (hκ : 0 < κ) (hε : 0 < ε) :
    p.fst.event (univ.filter (fun a => ¬goodFirst p M L κ ε a)) ≤
      exp (-κ) + (L - entropy p + S.card * exp (-L)) / (κ * ε) := by
  have hs' : ∀ x, x ∉ S.image Prod.swap → p.swap.mass x = 0 := by
    rintro ⟨b,a⟩ hx
    rw [Law.swap_mass]
    apply hs
    intro h
    exact hx (mem_image.mpr ⟨(a,b),h,rfl⟩)
  have H := badSecond_mass p.swap (S.image Prod.swap) hs' D
    hD M L κ ε hM hcard hκ hε
  have he : (S.image Prod.swap).card = S.card := card_image_of_injective S Prod.swap_injective
  simpa only [Law.swap_snd, goodSecond_swap p hM L κ ε, entropy_swap, he] using H

lemma levelSet_card_le_domain (p : Law A) (S : Finset A)
    (hS : ∀ a, a ∉ S → p.mass a = 0) (b : Levels p) :
    (levelSet p b).card ≤ S.card := by
  apply card_le_card
  intro a ha
  by_contra hnot
  have hp := (mem_filter.mp ha).2.1
  rw [hS a hnot] at hp
  exact lt_irrefl _ hp

lemma auxiliarySupport_exists (p : Law A) (good : Finset A) {M κ : ℝ}
    (hM : 0 < M) (hκ : 0 < κ)
    (hcap : ∀ b, ((levelSet p b).card : ℝ) ≤ M)
    (hbudget : (∑ b, (p.map (levelIndex p)).mass b * levelLoss p M b) / κ +
      2 * exp 1 * p.event (univ \ good) ≤ 1/2) :
    Nonempty (AuxiliarySupport p good M κ) := by
  obtain ⟨ρ,hsize,hρ⟩ := auxiliary_supports p good hM hκ hcap hbudget
  exact ⟨⟨ρ,hsize,hρ⟩⟩

lemma mean_levelLoss_nonneg (p : Law A) (M : ℝ)
    (hcap : ∀ b, ((levelSet p b).card : ℝ) ≤ M) :
    0 ≤ ∑ b, (p.map (levelIndex p)).mass b * levelLoss p M b :=
  sum_nonneg (fun b _ => mul_nonneg ((p.map (levelIndex p)).nonneg b)
    (levelLoss_nonneg p b (hcap b)))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem reciprocal_auxiliary_choices {n : ℕ} (hdim : Module.finrank K V = n+3)
    (p : Law (Projectivization K (Module.Dual K V) × Projectivization K V))
    (S : Finset (Projectivization K (Module.Dual K V) × Projectivization K V))
    (DA : Finset (Projectivization K (Module.Dual K V)))
    (DB : Finset (Projectivization K V))
    (hs : ∀ z, z ∉ S → p.mass z = 0)
    (hf : ∀ z, 0 < p.mass z → z.1.rep z.2.rep = 0)
    (hDA : ∀ a, a ∉ DA → p.fst.mass a = 0)
    (hDB : ∀ b, b ∉ DB → p.snd.mass b = 0)
    (MA MB C L κ ε : ℝ) (hMA : 0 < MA) (hMB : 0 < MB) (hC : 1 ≤ C)
    (hA : (DA.card : ℝ) ≤ MA) (hB : (DB.card : ℝ) ≤ MB)
    (hcap : MA * MB ≤ C * (Nat.card K : ℝ)^(n+3))
    (hκ : 0 < κ) (hε : 0 < ε)
    (hsmall :
      (2 * (log (2*C*(Nat.card K:ℝ)^(n+2)) - entropy p +
        log (entropy p.fst+2) + log (entropy p.snd+2) + 2)) / κ +
      2 * exp 1 * (exp (-κ) + (L - entropy p + S.card * exp (-L)) / (κ*ε)) ≤ 1/2) :
    Nonempty (AuxiliarySupport p.fst (univ.filter (goodFirst p MA L κ ε)) MA κ) ∧
    Nonempty (AuxiliarySupport p.snd (univ.filter (goodSecond p MB L κ ε)) MB κ) := by
  have hLA (b : Levels p.fst) : ((levelSet p.fst b).card : ℝ) ≤ MA :=
    (show ((levelSet p.fst b).card : ℝ) ≤ DA.card by
      exact_mod_cast levelSet_card_le_domain p.fst DA hDA b).trans hA
  have hLB (b : Levels p.snd) : ((levelSet p.snd b).card : ℝ) ≤ MB :=
    (show ((levelSet p.snd b).card : ℝ) ≤ DB.card by
      exact_mod_cast levelSet_card_le_domain p.snd DB hDB b).trans hB
  have hloss := Incidence.reciprocal_level_losses hdim p.swap
    (by rintro ⟨a,b⟩ h; exact hf (b,a) (by exact h))
    hMB hMA hC (by simpa only [mul_comm MA] using hcap)
    hLB hLA
  rw [entropy_swap] at hloss
  change (∑ b, (p.snd.map (levelIndex p.snd)).mass b * levelLoss p.snd MB b) +
    (∑ b, (p.fst.map (levelIndex p.fst)).mass b * levelLoss p.fst MA b) ≤
    2 * (log (2*C*(Nat.card K:ℝ)^(n+2)) - entropy p +
      log (entropy p.snd+2) + log (entropy p.fst+2) + 2) at hloss
  have hna := mean_levelLoss_nonneg p.fst MA hLA
  have hnb := mean_levelLoss_nonneg p.snd MB hLB
  have hbadA := badFirst_mass p S hs DA hDA MA L κ ε hMA hA hκ hε
  have hbadB := badSecond_mass p S hs DB hDB MB L κ ε hMB hB hκ hε
  have heA : univ \ univ.filter (goodFirst p MA L κ ε) =
      univ.filter (fun a => ¬goodFirst p MA L κ ε a) := by ext; simp
  have heB : univ \ univ.filter (goodSecond p MB L κ ε) =
      univ.filter (fun a => ¬goodSecond p MB L κ ε a) := by ext; simp
  constructor
  · apply auxiliarySupport_exists p.fst _ hMA hκ hLA
    rw [heA]
    apply le_trans _ hsmall
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ hκ.le
      linarith
    · exact mul_le_mul_of_nonneg_left hbadA (by positivity)
  · apply auxiliarySupport_exists p.snd _ hMB hκ hLB
    rw [heB]
    apply le_trans _ hsmall
    apply add_le_add
    · apply div_le_div_of_nonneg_right _ hκ.le
      linarith
    · exact mul_le_mul_of_nonneg_left hbadB (by positivity)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_SupportThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

lemma log_entropy_envelope {x A h : ℝ} (hx : 1≤x) (hA : 0≤A)
    (hh : 0≤h) (hcap : h≤A*x) :
    log (h+2) ≤ log (A+2)+log x := by
  have hx0 : 0<x := by linarith
  have hA0 : 0<A+2 := by linarith
  rw [←log_mul hA0.ne' hx0.ne']
  apply log_le_log (by linarith)
  nlinarith

lemma supportErrorEnvelope_tendsto (b C C₀ A : ℝ) (hb : 0<b) :
    Tendsto (supportErrorEnvelope b C C₀ A) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun x : ℝ => (2+100*exp 1)*x^(-2*b)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<2*b by positivity)).const_mul (2+100*exp 1)
  have h₂ : Tendsto (fun x : ℝ =>
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)/x^(4*b)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0<4*b by positivity)).const_mul
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)
    simp only [mul_zero] at h
    apply (h.congr' ?_)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simp only [Real.rpow_neg hx, div_eq_mul_inv]
  have h₃ : Tendsto (fun x : ℝ => 4*log x/x^(4*b)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      ((isLittleO_log_rpow_atTop (show 0<4*b by positivity)).tendsto_div_nhds_zero).const_mul 4
  have h₄ : Tendsto (fun x : ℝ => 2*exp 1*exp (-(x^(4*b)))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop (show 0<4*b by positivity)))
    simpa only [Function.comp_def, mul_zero] using h.const_mul (2*exp 1)
  unfold supportErrorEnvelope
  simpa only [add_zero] using ((h₁.add h₂).add h₃).add h₄

theorem eventually_support_small (b C C₀ A : ℝ) (hb : 0<b)
    (hC : 1≤C) (hC₀ : 0≤C₀) (hA : 0≤A) :
    ∀ᶠ x : ℝ in atTop, ∀ κ δ H HA HB L S : ℝ,
      x^(4*b)≤κ → δ≤κ*x^(-2*b) → L-H≤δ → S*exp (-L)≤C₀ →
      0≤HA → HA≤A*x → 0≤HB → HB≤A*x →
      (2*(log (2*C)+L-H+log (HA+2)+log (HB+2)+2))/κ+
        2*exp 1*(exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))) ≤ 1/2 := by
  filter_upwards [(supportErrorEnvelope_tendsto b C C₀ A hb).eventually
      (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), eventually_ge_atTop (1:ℝ)] with x he hx
  intro κ δ H HA HB L S hκ hδ hH hS hHA0 hHA hHB0 hHB
  have hx0 : 0<x := by linarith
  have hxpow : 0<x^(4*b) := rpow_pos_of_pos hx0 _
  have hκ0 : 0<κ := hxpow.trans_le hκ
  have hlA := log_entropy_envelope hx hA hHA0 hHA
  have hlB := log_entropy_envelope hx hA hHB0 hHB
  have hlogx : 0≤log x := log_nonneg hx
  have hlogC : 0≤log (2*C) := log_nonneg (by linarith)
  have hlogA : 0≤log (A+2) := log_nonneg (by linarith)
  have hdiv : δ/κ≤x^(-2*b) := (div_le_iff₀ hκ0).mpr (by simpa only [mul_comm κ] using hδ)
  have hconst0 : 0≤2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀ := by positivity
  have hconst := div_le_div_of_nonneg_left hconst0 hxpow hκ
  have hlog := div_le_div_of_nonneg_left (show 0≤4*log x by positivity) hxpow hκ
  have hexp : exp (-κ)≤exp (-(x^(4*b))) := exp_le_exp.mpr (neg_le_neg hκ)
  have hfirst : (2*(log (2*C)+L-H+log (HA+2)+log (HB+2)+2))/κ ≤
      (2*(log (2*C)+δ+2*(log (A+2)+log x)+2))/κ := by
    apply div_le_div_of_nonneg_right _ hκ0.le
    linarith
  have hsecond : 2*exp 1*(exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))) ≤
      2*exp 1*(exp (-κ)+(δ+C₀)/(κ*(1/50))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hsplit : (2*(log (2*C)+δ+2*(log (A+2)+log x)+2))/κ+
      2*exp 1*(exp (-κ)+(δ+C₀)/(κ*(1/50))) =
      (2+100*exp 1)*(δ/κ)+
      (2*(log (2*C)+2*log (A+2)+2)+100*exp 1*C₀)/κ+
      4*log x/κ+2*exp 1*exp (-κ) := by ring
  apply (add_le_add hfirst hsecond).trans
  rw [hsplit]
  apply le_trans _ he.le
  unfold supportErrorEnvelope
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hdiv (by positivity)) hconst) hlog)
      (mul_le_mul_of_nonneg_left hexp (by positivity))

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_UniformSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)]

lemma projective_entropy_le {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K V)) :
    entropy p ≤ (n+3:ℕ)*log (Nat.card K) := by
  have hq : (2:ℝ)≤Nat.card K := by
    exact_mod_cast (show 2≤Nat.card K from Finite.one_lt_card)
  have hc : (Fintype.card (Projectivization K V):ℝ) ≤ (Nat.card K:ℝ)^(n+3) := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,
      Nat.cast_sum]
    simp only [Nat.cast_pow]
    apply (sum_powers_le_twice hq (by omega : 0<n+3)).trans
    simp only [show n+3-1=n+2 by omega]
    calc
      _ ≤ (Nat.card K:ℝ)*(Nat.card K:ℝ)^(n+2) :=
        mul_le_mul_of_nonneg_right hq (pow_nonneg (by linarith) _)
      _ = (Nat.card K:ℝ)^(n+3) := by
        simpa only [mul_comm] using (pow_succ (Nat.card K:ℝ) (n+2)).symm
  have hp : (0:ℝ)<Fintype.card (Projectivization K V) := by
    have : Nontrivial V := (Module.finrank_pos_iff (R := K)).mp (by omega)
    exact_mod_cast Fintype.card_pos (α := Projectivization K V)
  apply (entropy_le_log_card p univ (by simp)).trans
  simp only [card_univ]
  apply (log_le_log hp hc).trans
  rw [log_pow]

variable [Fintype (Projectivization K (Module.Dual K V))]

theorem eventually_reciprocal_auxiliary_choices (n : ℕ) (b C C₀ : ℝ)
    (hb : 0<b) (hC : 1≤C) (hC₀ : 0≤C₀) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=n+3 → log (Nat.card K)=σ →
      ∀ (p : Law (Projectivization K (Module.Dual K V) × Projectivization K V))
        (S : Finset (Projectivization K (Module.Dual K V) × Projectivization K V))
        (DA : Finset (Projectivization K (Module.Dual K V)))
        (DB : Finset (Projectivization K V)) (MA MB κ δ : ℝ),
        (∀ z,z∉S→p.mass z=0) →
        (∀ z,0<p.mass z→z.1.rep z.2.rep=0) →
        (∀ a,a∉DA→p.fst.mass a=0) →
        (∀ a,a∉DB→p.snd.mass a=0) →
        0<MA → 0<MB → (DA.card:ℝ)≤MA → (DB.card:ℝ)≤MB →
        MA*MB≤C*(Nat.card K:ℝ)^(n+3) →
        (S.card:ℝ)≤C₀*(Nat.card K:ℝ)^(n+2) →
        σ^(4*b)≤κ → δ≤κ*σ^(-2*b) → (n+2:ℕ)*σ-entropy p≤δ →
        Nonempty (AuxiliarySupport p.fst
          (univ.filter (goodFirst p MA ((n+2:ℕ)*σ) κ (1/50))) MA κ) ∧
        Nonempty (AuxiliarySupport p.snd
          (univ.filter (goodSecond p MB ((n+2:ℕ)*σ) κ (1/50))) MB κ) := by
  filter_upwards [eventually_support_small b C C₀ (n+3) hb hC hC₀ (by positivity),
      eventually_ge_atTop (1:ℝ)] with σ he hσ
  intro K V _ _ _ _ _ _ _ hdim hlog p S DA DB MA MB κ δ hs hf hDA hDB
    hMA hMB hA hB hcap hS hκ hδ hdef
  have hσ0 : 0<σ := by linarith
  have hκ0 : 0<κ := (rpow_pos_of_pos hσ0 (4*b)).trans_le hκ
  have hq : (0:ℝ)<Nat.card K := by
    exact_mod_cast (show 0<Nat.card K from Nat.zero_lt_one.trans Finite.one_lt_card)
  have hn : exp ((n+2:ℕ)*σ)=(Nat.card K:ℝ)^(n+2) := by
    rw [←hlog,exp_nat_mul,exp_log hq]
  have hSn : (S.card:ℝ)*exp (-((n+2:ℕ)*σ))≤C₀ := by
    have h := mul_le_mul_of_nonneg_right hS (le_of_lt (exp_pos (-((n+2:ℕ)*σ))))
    rw [←hn,mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one] at h
    exact h
  have hHA := projective_entropy_le (V:=Module.Dual K V)
    (by simpa only [Subspace.dual_finrank_eq] using hdim) p.fst
  have hHB := projective_entropy_le hdim p.snd
  rw [hlog] at hHA hHB
  have hnlog : log (2*C*(Nat.card K:ℝ)^(n+2)) = log (2*C)+(n+2:ℕ)*σ := by
    rw [log_mul (by positivity : 2*C≠0) (pow_ne_zero _ hq.ne'),log_pow,hlog]
  apply reciprocal_auxiliary_choices hdim p S DA DB hs hf hDA hDB
    MA MB C ((n+2:ℕ)*σ) κ (1/50) hMA hMB hC hA hB hcap hκ0 (by norm_num)
  rw [hnlog]
  exact he κ δ (entropy p) (entropy p.fst) (entropy p.snd) ((n+2:ℕ)*σ)
    S.card hκ hδ hdef hSn (entropy_nonneg _)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hHA) (entropy_nonneg _)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hHB)

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

theorem open_good_event_le
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (MA MB κ ρ ε a : ℝ) (d r : ℕ)
    (hMA : 0<MA) (hMB : 0<MB) (hρ : 0<ρ)
    (hd : Module.finrank K V=d+1) (hr : r≤d+1)
    (hγ : 0<1-(Module.finrank K V:ℝ)*ρ-ε)
    (hκ : log (2/(1-(Module.finrank K V:ℝ)*ρ-ε))≤κ)
    (hu : (r:ℝ)-1 < (d:ℝ)+1-(log MA+3*κ)/log (Nat.card K))
    (hv : (d:ℝ)+1-r < (d:ℝ)+1-(log MB+3*κ)/log (Nat.card K))
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0)
    (hinfo : (pairInformation p i j:ℝ)≤a) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) MA ((d:ℝ)*log (Nat.card K)) κ ε ay.1 ∧
      goodSecond (p.marginal j) MB ((d:ℝ)*log (Nat.card K)) κ ε ay.2 ∧
      ay.1.rep ay.2.rep=0)) ≤ 2*a/ρ^2 := by
  let p₂ := p.map (fun x => (x i,x j))
  have hi : p₂.fst=p.marginal i := by
    exact (Law.map_fst p₂).symm.trans (p.map_map (fun x => (x i,x j)) Prod.fst)
  have hj : p₂.snd=p.marginal j := by
    exact (Law.map_snd p₂).symm.trans (p.map_map (fun x => (x i,x j)) Prod.snd)
  have hcon : ∀ z,p₂.mass z≠0 →
      z.1.1.rep z.2.2.rep=0 → z.2.1.rep z.1.2.rep=0 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := p.map_support (fun x => (x i,x j)) z hz
    exact hconsistent x hx
  have h := projective_open_incidence p₂ MA MB κ ρ ε d r hMA hMB hρ
    hd hr hγ hκ hu hv hcon
  rw [hi,hj] at h
  apply h.trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinfo (by norm_num))
    (sq_nonneg ρ)

omit [Finite K] [FiniteDimensional K V] in
theorem auxiliary_three_estimates
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (MA MB L κ ε z : ℝ)
    (A : AuxiliarySupport (p.marginal i).fst
      (univ.filter (goodFirst (p.marginal i) MA L κ ε)) MA κ)
    (B : AuxiliarySupport (p.marginal j).snd
      (univ.filter (goodSecond (p.marginal j) MB L κ ε)) MB κ)
    (hz : ((p.marginal i).fst.prod (p.marginal j).snd).event
      (univ.filter (fun ay => goodFirst (p.marginal i) MA L κ ε ay.1 ∧
        goodSecond (p.marginal j) MB L κ ε ay.2 ∧ ay.1.rep ay.2.rep=0)) ≤ z) :
    let SA := fun b => levelSet (p.marginal i).fst b ∩
      univ.filter (goodFirst (p.marginal i) MA L κ ε)
    let SB := fun b => levelSet (p.marginal j).snd b ∩
      univ.filter (goodSecond (p.marginal j) MB L κ ε)
    (∑ a, ∑ b, A.law.mass a * B.law.mass b *
      ((((SA a ×ˢ SB b).filter (fun ay => ay.1.rep ay.2.rep=0)).card:ℝ) /
        ((SA a).card * (SB b).card))) ≤ (4*exp 1)^2*z ∧
    (∑ a, A.law.mass a * SupportMixtures.pairing (SupportMixtures.kernel (SA a))
      (fun y => if goodSecond (p.marginal j) MB L κ ε y then (p.marginal j).snd.mass y else 0)
      (fun x y => if x.rep y.rep=0 then 1 else 0)) ≤ (4*exp 1)*z ∧
    (∑ b, B.law.mass b * SupportMixtures.pairing
      (fun x => if goodFirst (p.marginal i) MA L κ ε x then (p.marginal i).fst.mass x else 0)
      (SupportMixtures.kernel (SB b))
      (fun x y => if x.rep y.rep=0 then 1 else 0)) ≤ (4*exp 1)*z := by
  dsimp only
  have h₂ := actual_auxiliary_incidence (p.marginal i).fst (p.marginal j).snd
    (univ.filter (goodFirst (p.marginal i) MA L κ ε))
    (univ.filter (goodSecond (p.marginal j) MB L κ ε)) MA MB κ
    A.law B.law A.density B.density (fun x y => x.rep y.rep=0)
  have h₁A := actual_auxiliary_target_left (p.marginal i).fst (p.marginal j).snd
    (univ.filter (goodFirst (p.marginal i) MA L κ ε))
    (univ.filter (goodSecond (p.marginal j) MB L κ ε)) MA κ
    A.law A.density (fun x y => x.rep y.rep=0)
  have h₁B := actual_auxiliary_target_right (p.marginal i).fst (p.marginal j).snd
    (univ.filter (goodFirst (p.marginal i) MA L κ ε))
    (univ.filter (goodSecond (p.marginal j) MB L κ ε)) MB κ
    B.law B.density (fun x y => x.rep y.rep=0)
  simp only [mem_filter, mem_univ, true_and] at h₂ h₁A h₁B
  exact ⟨h₂.trans (mul_le_mul_of_nonneg_left hz (sq_nonneg _)),
    h₁A.trans (mul_le_mul_of_nonneg_left hz (by positivity)),
    h₁B.trans (mul_le_mul_of_nonneg_left hz (by positivity))⟩

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

lemma open_band_rank_bounds {d r : ℕ} {σ C κ gap u v : ℝ}
    (hσ : 0<σ) (hC : 0<C)
    (hu : OpenBand r σ gap u) (hv : OpenBand r σ gap v)
    (hsmall : log C+3*κ<gap) :
    (r:ℝ)-1 < (d:ℝ)+1-(log (C*exp (((d:ℝ)+1)*σ-u))+3*κ)/σ ∧
    (d:ℝ)+1-r < (d:ℝ)+1-(log (C*exp v)+3*κ)/σ := by
  rw [log_mul hC.ne' (exp_ne_zero _),log_exp,
    log_mul hC.ne' (exp_ne_zero _),log_exp]
  constructor
  · have hh : (log C+(((d:ℝ)+1)*σ-u)+3*κ)/σ < (d:ℝ)+1-((r:ℝ)-1) := by
      apply (div_lt_iff₀ hσ).mpr
      nlinarith [hu.1]
    linarith
  · have hh : (log C+v+3*κ)/σ < (r:ℝ) := by
      apply (div_lt_iff₀ hσ).mpr
      linarith [hv.2]
    linarith

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

theorem open_band_event_le
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (C κ gap u v a : ℝ) (d r : ℕ)
    (hdim : Module.finrank K V=d+1) (hC : 0<C) (hr : r≤d+1)
    (hu : OpenBand r (log (Nat.card K)) gap u)
    (hv : OpenBand r (log (Nat.card K)) gap v)
    (hsmall : log C+3*κ<gap)
    (hκ : log (200/97)≤κ)
    (hconsistent : ∀ x,p.mass x≠0 →
      (x i).1.rep (x j).2.rep=0 → (x j).1.rep (x i).2.rep=0)
    (hinfo : (pairInformation p i j:ℝ)≤a) :
    ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay =>
      goodFirst (p.marginal i) (C*exp (((d:ℝ)+1)*log (Nat.card K)-u))
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.1 ∧
      goodSecond (p.marginal j) (C*exp v)
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.2 ∧
      ay.1.rep ay.2.rep=0)) ≤ (20000*((d:ℝ)+1)^2)*a := by
  have hσ : 0<log (Nat.card K:ℝ) := log_pos (by exact_mod_cast Finite.one_lt_card (α:=K))
  have hd : (0:ℝ)<(d:ℝ)+1 := by positivity
  have he : (Module.finrank K V:ℝ)*(1/(100*((d:ℝ)+1)))=1/100 := by
    rw [hdim,Nat.cast_add,Nat.cast_one]
    field_simp
  obtain ⟨hrA,hrB⟩ := open_band_rank_bounds (d:=d) hσ hC hu hv hsmall
  have hh := open_good_event_le p i j
    (C*exp (((d:ℝ)+1)*log (Nat.card K)-u)) (C*exp v) κ
    (1/(100*((d:ℝ)+1))) (1/50) a d r
    (by positivity) (by positivity) (by positivity) hdim hr
    (by rw [he]; norm_num)
    (by simpa only [he,show (1:ℝ)-1/100-1/50=97/100 by norm_num,
      show (2:ℝ)/(97/100)=200/97 by norm_num] using hκ) hrA hrB hconsistent hinfo
  apply hh.trans_eq
  field_simp
  ring

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

omit [Fintype W] in
theorem downward_sum [LinearOrder W] (S : Finset W) (early late : W→ℝ)
    (lo hi R : ℝ) (hlohi : lo≤hi) (hR : 0≤R)
    (hl : ∀ i∈S,lo≤late i) (hh : ∀ i∈S,early i≤hi)
    (hcross : ∀ i∈S,∀ j∈S,i<j→early j≤late i+R) :
    (∑ i∈S,(early i-late i))≤hi-lo+R*S.card := by
  induction S using Finset.induction_on_min generalizing hi with
  | empty => simpa using sub_nonneg.mpr hlohi
  | @insert i S hmin ih =>
    have hin : i∉S := by intro h; exact (lt_irrefl i) (hmin i h)
    have hli := hl i (mem_insert_self _ _)
    have hhi := hh i (mem_insert_self _ _)
    have hs := ih (late i+R) (by linarith)
      (fun j hj=>hl j (mem_insert_of_mem hj))
      (fun j hj=>hcross i (mem_insert_self _ _) j (mem_insert_of_mem hj) (hmin j hj))
      (fun j hj k hk h=>hcross j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) h)
    rw [sum_insert hin,card_insert_of_notMem hin,Nat.cast_add,Nat.cast_one]
    linarith

theorem downward_deleted [LinearOrder W] (S : Finset W) (early late : W→ℝ)
    (lo hi R D : ℝ) (hlohi : lo≤hi) (hR : 0≤R)
    (hl : ∀ i∈S,lo≤late i) (hh : ∀ i∈S,early i≤hi)
    (hcross : ∀ i∈S,∀ j∈S,i<j→early j≤late i+R) :
    D*((S.filter (fun i=>D<early i-late i)).card:ℝ)≤hi-lo+R*(Fintype.card W:ℝ) := by
  let T:=S.filter (fun i=>D<early i-late i)
  have hlow : D*(T.card:ℝ)≤∑ i∈T,(early i-late i) := by
    calc
      _ = ∑ _i∈T,D := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun i hi=>(mem_filter.mp hi).2.le)
  have hsum:=downward_sum T early late lo hi R hlohi hR
    (fun i hi=>hl i (mem_filter.mp hi).1) (fun i hi=>hh i (mem_filter.mp hi).1)
    (fun i hi j hj hij=>hcross i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij)
  have hc : (T.card:ℝ) ≤ (Fintype.card W:ℝ) := by exact_mod_cast card_le_univ T
  exact hlow.trans (hsum.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hc hR)))

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

lemma representative_owner (z : (model w n k p θ G t).FreshHistory) (b : Block w) :
    (model w n k p θ G t).owner z.1 ((model w n k p θ G t).representative z b)=some b :=
  model_embedding_owner w n k p θ G t z.1 b (z.2 b)

lemma representative_origin_owner (z : (model w n k p θ G t).FreshHistory) (b : Block w) :
    owner w (n+k) ((model w n k p θ G t).origin z.1
      ((model w n k p θ G t).representative z b))=some b := by
  rw [←model_owner,representative_owner]

lemma representative_other (z : (model w n k p θ G t).FreshHistory) (b c : Block w) (hbc : b≠c) :
    (model w n k p θ G t).representative z b∈otherRepresentatives
      ((model w n k p θ G t).embedding z.1) ((model w n k p θ G t).owner z.1) z.2
      ((model w n k p θ G t).representative z c) := by
  apply mem_image.mpr
  refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
  rw [representative_owner]
  exact fun h=>hbc (Option.some.inj h)

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

lemma prepared_marginal_source
    (i : (contextual n k p θ G e own t).Index z.1) (a : β)
    (ha : (((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a≠0) :
    ∃ ω,p.mass ω≠0 ∧ θ ω=z.1.1 ∧
      G ω ((contextual n k p θ G e own t).origin z.1 i)=a := by
  obtain ⟨y,hy,he⟩:=((contextual n k p θ G e own t).tupleLaw z.1).map_support
    (fun y=>y i) a ha
  obtain ⟨ω,hω,hθ,hG⟩:=contextual_fresh_source n k p θ G e own t hp z hz y hy
  exact ⟨ω,hω,hθ,(hG i).trans he⟩

lemma prepared_marginal_domain (S : Θ→ι→Finset β)
    (hS : ∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i)
    (i : (contextual n k p θ G e own t).Index z.1) :
    ∀ a,a∉S z.1.1 ((contextual n k p θ G e own t).origin z.1 i)→
      (((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a=0 := by
  intro a ha
  by_contra h
  obtain ⟨ω,hω,hθ,hG⟩:=prepared_marginal_source n k p θ G e own t hp z hz i a h
  have hh:=hS ω hω ((contextual n k p θ G e own t).origin z.1 i)
  rw [hθ,hG] at hh
  exact ha hh

lemma prepared_marginal_property (P : Θ→ι→β→Prop)
    (hP : ∀ ω,p.mass ω≠0→∀ i,P (θ ω) i (G ω i))
    (i : (contextual n k p θ G e own t).Index z.1) :
    ∀ a,(((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a≠0→
      P z.1.1 ((contextual n k p θ G e own t).origin z.1 i) a := by
  intro a ha
  obtain ⟨ω,hω,hθ,hG⟩:=prepared_marginal_source n k p θ G e own t hp z hz i a ha
  simpa only [hθ,hG] using hP ω hω ((contextual n k p θ G e own t).origin z.1 i)

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

theorem prepared_open_event
    (i j : (contextual n k p θ G e own t).Index z.1)
    (hij : pos ((contextual n k p θ G e own t).origin z.1 i)<
      pos ((contextual n k p θ G e own t).origin z.1 j))
    (P κ gap u v J D a : ℝ) (d r : ℕ)
    (hdim : Module.finrank K V=d+1) (hP : 0<P) (hr : r≤d+1)
    (hu : OpenBand r (log (Nat.card K)) gap u)
    (hv : OpenBand r (log (Nat.card K)) gap v)
    (hsmall : log P+3*κ<gap) (hκ : log (200/97)≤κ)
    (hgood :
      let M:=contextual n k p θ G e own t
      (i∉badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J D a z.2 ∧
        j∈otherRepresentatives (M.embedding z.1) (M.owner z.1) z.2 i) ∨
      (j∉badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J D a z.2 ∧
        i∈otherRepresentatives (M.embedding z.1) (M.owner z.1) z.2 j)) :
    let q:=(contextual n k p θ G e own t).tupleLaw z.1
    ((q.marginal i).fst.prod (q.marginal j).snd).event (univ.filter (fun ay=>
      goodFirst (q.marginal i) (P*exp (((d:ℝ)+1)*log (Nat.card K)-u))
        ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.1 ∧
      goodSecond (q.marginal j) (P*exp v) ((d:ℝ)*log (Nat.card K)) κ (1/50) ay.2 ∧
      ay.1.rep ay.2.rep=0))≤(20000*((d:ℝ)+1)^2)*a := by
  let M:=contextual n k p θ G e own t
  apply open_band_event_le (M.tupleLaw z.1) i j P κ gap u v a d r hdim hP hr
    hu hv hsmall hκ
    (prepared_consistency n k p θ G e own t hp z hz pos hcon i j hij)
  have hh:=good_charge_either (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
    (fun _ _=>0) (by intros; rfl) J D a z.2 i j hgood
  simpa only [NNReal.coe_zero,add_zero] using hh

end
end SharpLogRamsey.Selection.ExposureModel

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_EndpointScales
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

lemma endpoint_error_scale {x b κ δ H L S C₀ : ℝ}
    (hx : 1≤x) (hb : 0≤b) (hC₀ : 0≤C₀)
    (hκ : x^(4*b)≤κ) (hδ : δ≤κ*x^(-2*b))
    (hH : L-H≤δ) (hS : S*exp (-L)≤C₀) :
    exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))≤
      (51+50*C₀)*x^(-2*b) := by
  have hx0 : 0<x := by linarith
  have hp : 0<x^(2*b) := rpow_pos_of_pos hx0 _
  have hk : x^(2*b)≤κ := (rpow_le_rpow_of_exponent_le hx (by linarith)).trans hκ
  have hk0 : 0<κ := hp.trans_le hk
  have hi : 1/κ≤x^(-2*b) := by
    have hh:=one_div_le_one_div_of_le hp hk
    simpa only [neg_mul,rpow_neg hx0.le,one_div] using hh
  have he : exp (-κ)≤1/κ := by
    rw [exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le hk0
      (show κ≤exp κ by linarith [add_one_le_exp κ]))
  have hd : δ/κ≤x^(-2*b) := (div_le_iff₀ hk0).mpr (by simpa only [mul_comm κ] using hδ)
  have hsn : (L-H+S*exp (-L))/(κ*(1/50))≤50*(δ/κ)+50*C₀*(1/κ) := by
    calc
      _ ≤ (δ+C₀)/(κ*(1/50)) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ x^(-2*b)+(50*(δ/κ)+50*C₀*(1/κ)) := add_le_add (he.trans hi) hsn
    _ ≤ x^(-2*b)+(50*x^(-2*b)+50*C₀*x^(-2*b)) := by gcongr
    _ = _ := by ring

variable {A B : Type*} [Fintype A] [Fintype B]

theorem actual_endpoint_errors (p : Law (A×B)) (S : Finset (A×B))
    (DA : Finset A) (DB : Finset B)
    (hs : ∀ z,z∉S→p.mass z=0)
    (ha : ∀ a,a∉DA→p.fst.mass a=0) (hb : ∀ b,b∉DB→p.snd.mass b=0)
    (MA MB L κ x β δ C₀ : ℝ) (hMA : 0<MA) (hMB : 0<MB)
    (hA : (DA.card:ℝ)≤MA) (hB : (DB.card:ℝ)≤MB)
    (hx : 1≤x) (hβ : 0≤β) (hC₀ : 0≤C₀)
    (hκ : x^(4*β)≤κ) (hδ : δ≤κ*x^(-2*β))
    (hdef : L-entropy p≤δ) (hS : (S.card:ℝ)*exp (-L)≤C₀) :
    p.fst.event (univ.filter (fun a=>¬goodFirst p MA L κ (1/50) a))≤(51+50*C₀)*x^(-2*β) ∧
    p.snd.event (univ.filter (fun b=>¬goodSecond p MB L κ (1/50) b))≤(51+50*C₀)*x^(-2*β) := by
  have hκ0 : 0<κ := (rpow_pos_of_pos (by linarith : 0<x) (4*β)).trans_le hκ
  have he:=endpoint_error_scale hx hβ hC₀ hκ hδ hdef hS
  exact ⟨(badFirst_mass p S hs DA ha MA L κ (1/50) hMA hA hκ0 (by norm_num)).trans he,
    (badSecond_mass p S hs DB hb MB L κ (1/50) hMB hB hκ0 (by norm_num)).trans he⟩

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_IntegerScales
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

lemma K_le_Kstar {σ η D : ℝ} (hσ : 1≤σ) (hη : 0<η) (hD : 0≤D) :
    scaleK σ η D≤ scaleKstar σ η D := by
  unfold scaleK scaleKstar
  apply mul_le_mul_of_nonneg_left _ hD
  exact rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη; linarith)

theorem eventually_integer_regime (η : ℝ) (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ,σ^beta η≤D → D≤σ^(1-η/2) →
      log 1024+3*scaleK σ η D+scaleKstar σ η D<σ ∧
      log (200/97)≤ scaleK σ η D ∧
      2*scaleKstar σ η D+2*scaleK σ η D+log 4≤16*scaleKstar σ η D ∧
      0<σ^(-100*beta η) ∧ σ^(-100*beta η)≤1/40000 := by
  have hb:=beta_pos hη
  have hneg : 0<η/2-6*beta η := by unfold beta; linarith
  have ha : Tendsto (fun σ : ℝ=>σ^(-η/2+6*beta η)) atTop (𝓝 0) := by
    rw [show -η/2+6*beta η = -(η/2-6*beta η) by ring]
    exact tendsto_rpow_neg_atTop hneg
  have ht : Tendsto (fun σ : ℝ=>log 1024*σ^(-1:ℝ)+4*σ^(-η/2+6*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).const_mul (log 1024)).add (ha.const_mul 4)
  have hg : Tendsto (fun σ : ℝ=>σ^(4*beta η)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hτ : Tendsto (fun σ : ℝ=>σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using
      tendsto_rpow_neg_atTop (show 0<100*beta η by positivity)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hg.eventually (eventually_ge_atTop (log (200/97))),
    hτ.eventually (gt_mem_nhds (show (0:ℝ)<1/40000 by norm_num))] with σ hσ hs hg hτ D hDl hDu
  have hσ0 : 0<σ := by linarith
  have hD : 1≤D := (one_le_rpow hσ hb.le).trans hDl
  have hKK:=K_le_Kstar hσ hη (by linarith : 0≤D)
  have hK : σ^(4*beta η)≤ scaleK σ η D := by
    calc
      _ = σ^beta η*σ^(3*beta η) := by rw [←rpow_add hσ0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hDl (by positivity)
  have hKu : scaleKstar σ η D≤σ^(1-η/2+6*beta η) := by
    unfold scaleKstar
    rw [rpow_add hσ0]
    exact mul_le_mul_of_nonneg_right hDu (by positivity)
  have hK1 : 1≤ scaleKstar σ η D :=
    one_le_mul_of_one_le_of_one_le hD (one_le_rpow hσ (by positivity))
  refine ⟨?_,hg.trans hK,?_,rpow_pos_of_pos hσ0 _,hτ.le⟩
  · have hh : log 1024+4*σ^(1-η/2+6*beta η)<σ := by
      have he : log 1024*σ^(-1:ℝ)+4*σ^(-η/2+6*beta η)=
          (log 1024+4*σ^(1-η/2+6*beta η))/σ := by
        have hep : σ^(1-η/2+6*beta η)/σ=σ^(-η/2+6*beta η) := by
          calc
            _ = σ^(1-η/2+6*beta η)/σ^(1:ℝ) := by rw [rpow_one]
            _ = _ := by rw [←rpow_sub hσ0]; congr 1; ring
        rw [rpow_neg_one,add_div,mul_div_assoc,hep]
        ring
      rw [he] at hs
      simpa only [one_mul] using (div_lt_iff₀ hσ0).mp hs
    linarith
  · have hlog : log (4:ℝ)≤3 := by
      have hh:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      linarith
    linarith
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_OpenScales
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

lemma Kstar_lower {σ η D : ℝ} (hσ : 0<σ) (hDl : σ^beta η≤D) :
    σ^(7*beta η)≤ scaleKstar σ η D := by
  calc
    _ = σ^beta η*σ^(6*beta η) := by rw [←rpow_add hσ]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hDl (by positivity)

lemma K_ratio {σ η D : ℝ} (hσ : 0<σ) :
    scaleK σ η D=σ^(-3*beta η)*scaleKstar σ η D := by
  unfold scaleK scaleKstar
  rw [mul_left_comm,←rpow_add hσ]
  congr 2
  ring

lemma Kstar_inv_bound {σ η D : ℝ} (hσ : 0<σ) (hDl : σ^beta η≤D) :
    1≤σ^(-7*beta η)*scaleKstar σ η D := by
  have hh:=mul_le_mul_of_nonneg_left (Kstar_lower hσ hDl)
    (rpow_pos_of_pos hσ (-7*beta η)).le
  rw [←rpow_add hσ] at hh
  simpa only [show -7*beta η+7*beta η=0 by ring,rpow_zero] using hh

theorem eventually_open_regime (η : ℝ) (d : ℕ) (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop, ∀ D q : ℝ, σ^beta η≤D → 0<q →
      log 1024+3*scaleK σ η D < scaleKstar σ η D ∧
      (4*exp 1)^2*(20000*((d:ℝ)+3)^2*(σ^(-2000*beta η)/q))≤1/(4*q) := by
  have hb:=beta_pos hη
  have ht : Tendsto (fun σ : ℝ=>log 1024*σ^(-7*beta η)+3*σ^(-3*beta η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ=>σ^(-7*beta η)) atTop (𝓝 0) := by
      simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<7*beta η by positivity)
    have h2 : Tendsto (fun σ : ℝ=>σ^(-3*beta η)) atTop (𝓝 0) := by
      simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<3*beta η by positivity)
    simpa only [mul_zero,add_zero] using (h1.const_mul (log 1024)).add (h2.const_mul 3)
  have hs : Tendsto (fun σ : ℝ=>(4*exp 1)^2*(20000*((d:ℝ)+3)^2)*σ^(-2000*beta η)) atTop (𝓝 0) := by
    have he : Tendsto (fun σ : ℝ=>σ^(-2000*beta η)) atTop (𝓝 0) := by
      simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<2000*beta η by positivity)
    simpa only [mul_zero] using he.const_mul ((4*exp 1)^2*(20000*((d:ℝ)+3)^2))
  filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hs.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num))] with σ hσ ht hs D q hDl hq
  have hD : 0<D := (rpow_pos_of_pos hσ _).trans_le hDl
  have hg : 0 < scaleKstar σ η D := by unfold scaleKstar; positivity
  constructor
  · have hl : log 1024≤log 1024*(σ^(-7*beta η)*scaleKstar σ η D) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Kstar_inv_bound hσ hDl)
        (log_nonneg (show (1:ℝ)≤1024 by norm_num))
    rw [K_ratio hσ]
    have hh:=mul_lt_mul_of_pos_right ht hg
    nlinarith
  · have hh:=div_le_div_of_nonneg_right hs.le hq.le
    convert hh using 1 <;> first | rfl | ring

theorem eventually_open_deletion_small (η c ε : ℝ) (hη : 0<η) (hc : 0 < c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ D w : ℝ,σ^beta η≤D → 0≤w →
      c*σ^(1+η/2)≤w*D →
      σ+(2*scaleK σ η D+log 64)*w≤ε*w*scaleKstar σ η D := by
  have hb:=beta_pos hη
  have he1 : Tendsto (fun σ : ℝ=>σ^(-η/2-6*beta η)) atTop (𝓝 0) := by
    simpa only [neg_add, neg_div, sub_eq_add_neg] using
      tendsto_rpow_neg_atTop (show 0<η/2+6*beta η by positivity)
  have he2 : Tendsto (fun σ : ℝ=>σ^(-3*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<3*beta η by positivity)
  have he3 : Tendsto (fun σ : ℝ=>σ^(-7*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<7*beta η by positivity)
  have ht : Tendsto (fun σ : ℝ=>c⁻¹*σ^(-η/2-6*beta η)+2*σ^(-3*beta η)+log 64*σ^(-7*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using ((he1.const_mul c⁻¹).add (he2.const_mul 2)).add (he3.const_mul (log 64))
  filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds hε)] with σ hσ ht D w hDl hw hwD
  have hD : 0<D := (rpow_pos_of_pos hσ _).trans_le hDl
  have hg : 0≤ scaleKstar σ η D := by unfold scaleKstar; positivity
  have hfirst : σ ≤ c⁻¹*σ^(-η/2-6*beta η)*w*scaleKstar σ η D := by
    have hh:=mul_le_mul_of_nonneg_left hwD (show 0 ≤ c⁻¹*σ^(-η/2) by positivity)
    have heq : c⁻¹*σ^(-η/2)*(c*σ^(1+η/2))=σ := by
      rw [mul_mul_mul_comm,inv_mul_cancel₀ (ne_of_gt hc),one_mul,←rpow_add hσ]
      simp only [show -η/2+(1+η/2)=1 by ring,rpow_one]
    rw [heq] at hh
    have heq2 : c⁻¹*σ^(-η/2)*(w*D)=c⁻¹*σ^(-η/2-6*beta η)*w*scaleKstar σ η D := by
      unfold scaleKstar
      have hrpow : σ^(-η/2-6*beta η)*σ^(6*beta η)=σ^(-η/2) := by
        rw [←rpow_add hσ]; congr 1; ring
      calc
        _ = c⁻¹*(σ^(-η/2-6*beta η)*σ^(6*beta η))*(w*D) := by rw [hrpow]
        _ = _ := by ring
    rwa [heq2] at hh
  have hlog : log 64*w≤log 64*σ^(-7*beta η)*w*scaleKstar σ η D := by
    have hh:=mul_le_mul_of_nonneg_left (Kstar_inv_bound hσ hDl)
      (show 0≤log 64*w from mul_nonneg (log_nonneg (show (1:ℝ)≤64 by norm_num)) hw)
    nlinarith
  have hh:=mul_le_mul_of_nonneg_right ht.le (mul_nonneg hw hg)
  rw [K_ratio hσ]
  nlinarith
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

lemma Law.map_image_support {A B : Type*} [Fintype A] [Fintype B]
    (p : Law A) (S : Finset A) (f : A→B)
    (hS : ∀ a,a∉S→p.mass a=0) :
    ∀ b,b∉S.image f→(p.map f).mass b=0 := by
  intro b hb
  by_contra he
  obtain ⟨a,ha,rfl⟩:=p.map_support f b he
  exact hb (mem_image.mpr ⟨a,by by_contra h; exact ha (hS a h),rfl⟩)

lemma reciprocal_source_scales {σ β D : ℝ} (hσ : 0<σ) (hD : σ^β≤D) :
    σ^(4*β)≤D*σ^(3*β) ∧ D*σ^β≤(D*σ^(3*β))*σ^(-2*β) := by
  constructor
  · calc
      _ = σ^β*σ^(3*β) := by rw [←rpow_add hσ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (rpow_nonneg hσ.le _)
  · rw [mul_assoc,←rpow_add hσ,show 3*β+-2*β=β by ring]

theorem eventually_actual_reciprocal (n : ℕ) (β : ℝ) (hβ : 0<β) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=n+3 → log (Nat.card K)=σ →
      ∀ (p : Law (Projectivization K (Module.Dual K V)×Projectivization K V))
        (S : Finset (Projectivization K (Module.Dual K V)×Projectivization K V)) (D u : ℝ),
        (∀ a,a∉S→p.mass a=0) →
        (∀ a,0<p.mass a→a.1.rep a.2.rep=0) →
        ((S.image Prod.fst).card:ℝ)≤1024*exp (((n+3:ℕ):ℝ)*σ-u) →
        ((S.image Prod.snd).card:ℝ)≤1024*exp u →
        (S.card:ℝ)≤64*(Nat.card K:ℝ)^(n+2) → σ^β≤D →
        ((n+2:ℕ):ℝ)*σ-entropy p≤D*σ^β →
        let MA:=1024*exp (((n+3:ℕ):ℝ)*σ-u)
        let MB:=1024*exp u
        let L:=((n+2:ℕ):ℝ)*σ
        let κ:=D*σ^(3*β)
        Nonempty (AuxiliarySupport p.fst (univ.filter (goodFirst p MA L κ (1/50))) MA κ) ∧
        Nonempty (AuxiliarySupport p.snd (univ.filter (goodSecond p MB L κ (1/50))) MB κ) ∧
        p.fst.event (univ.filter (fun a=>¬goodFirst p MA L κ (1/50) a))≤3251*σ^(-2*β) ∧
        p.snd.event (univ.filter (fun b=>¬goodSecond p MB L κ (1/50) b))≤3251*σ^(-2*β) := by
  filter_upwards [eventually_reciprocal_auxiliary_choices n β (1024^2) 64 hβ
      (by norm_num) (by norm_num),eventually_ge_atTop (1:ℝ)] with σ he hσ
  intro K V _ _ _ _ _ _ _ hdim hlog p S D u hs hf hA hB hS hD hdef
  have hσ0 : 0<σ := by linarith
  have hq : (0:ℝ)<Nat.card K := by
    exact_mod_cast (show 0<Nat.card K from Nat.zero_lt_one.trans Finite.one_lt_card)
  have hA0 : 0<1024*exp (((n+3:ℕ):ℝ)*σ-u) := by positivity
  have hB0 : 0<1024*exp u := by positivity
  have ha := p.map_image_support S Prod.fst hs
  have hb := p.map_image_support S Prod.snd hs
  rw [Law.map_fst] at ha
  rw [Law.map_snd] at hb
  have hcap : (1024*exp (((n+3:ℕ):ℝ)*σ-u))*(1024*exp u)≤
      1024^2*(Nat.card K:ℝ)^(n+3) := by
    rw [show (1024*exp (((n+3:ℕ):ℝ)*σ-u))*(1024*exp u)=
      1024^2*exp (((n+3:ℕ):ℝ)*σ) by rw [show ((n+3:ℕ):ℝ)*σ=(((n+3:ℕ):ℝ)*σ-u)+u by ring,exp_add]; ring_nf]
    rw [←hlog,exp_nat_mul,exp_log hq]
  have hsc:=reciprocal_source_scales hσ0 hD
  have hch:=he K V hdim hlog p S (S.image Prod.fst) (S.image Prod.snd) _ _ _ _
    hs hf ha hb hA0 hB0 hA hB hcap hS hsc.1 hsc.2 hdef
  have hp : (S.card:ℝ)*exp (-(((n+2:ℕ):ℝ)*σ))≤64 := by
    have hh:=mul_le_mul_of_nonneg_right hS (le_of_lt (exp_pos (-(((n+2:ℕ):ℝ)*σ))))
    have hn : exp (((n+2:ℕ):ℝ)*σ)=(Nat.card K:ℝ)^(n+2) := by
      rw [←hlog,exp_nat_mul,exp_log hq]
    rw [←hn,mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one] at hh
    exact hh
  have herr:=actual_endpoint_errors p S (S.image Prod.fst) (S.image Prod.snd) hs ha hb
    _ _ _ _ σ β (D*σ^β) 64 hA0 hB0 hA hB hσ hβ.le (by norm_num) hsc.1 hsc.2 hdef hp
  exact ⟨hch.1,hch.2,by norm_num only at herr ⊢; exact herr⟩

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_PreparedReciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section
variable {Ω : Type*} [Fintype Ω]
lemma Law.exists_mass_ne_zero (p : Law Ω) : ∃ ω,p.mass ω≠0 := by
  by_contra h
  push Not at h
  have hh:=p.total
  simp only [h,sum_const_zero] at hh
  norm_num at hh

namespace ExposureModel
variable {Ω Θ ι C β : Type} [Fintype Ω] [Fintype Θ] [Fintype ι] [DecidableEq ι]
  [Fintype C] [Fintype β]
lemma prepared_context_property (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
    (z : (contextual n k p θ G e own t).FreshHistory)
    (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)
    (P : Θ→Prop) (hP : ∀ ω,p.mass ω≠0→P (θ ω)) : P z.1.1 := by
  obtain ⟨y,hy⟩:=((contextual n k p θ G e own t).tupleLaw z.1).exists_mass_ne_zero
  obtain ⟨ω,hω,hθ,_⟩:=contextual_fresh_source n k p θ G e own t hp z hz y hy
  simpa only [hθ] using hP ω hω
end ExposureModel

open ExposureModel

theorem eventually_prepared_reciprocal (d : ℕ) (β : ℝ) (hβ : 0<β) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ (Ω Θ ι C : Type) [Fintype Ω] [Fintype Θ] [Fintype ι] [DecidableEq ι] [Fintype C]
        (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→ι→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→ι→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→ι→ℝ) (n k : ℕ) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C)
        (t : Fin k) (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
        (D J a : ℝ),
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        σ^β≤D → ((d+2:ℕ):ℝ)*σ≤J →
        ∀ (z : (contextual n k p θ G e own t).FreshHistory)
          (c : (contextual n k p θ G e own t).Index z.1→
            (contextual n k p θ G e own t).Index z.1→NNReal),
          ((contextual n k p θ G e own t).freshLaw hp).mass z≠0 →
          ∀ i,i∉badIndices ((contextual n k p θ G e own t).tupleLaw z.1)
            ((contextual n k p θ G e own t).embedding z.1)
            ((contextual n k p θ G e own t).owner z.1) c J (D*σ^β) a z.2 →
          let q:=((contextual n k p θ G e own t).tupleLaw z.1).marginal i
          let ui:=u z.1.1 ((contextual n k p θ G e own t).origin z.1 i)
          let MA:=1024*exp (((d+3:ℕ):ℝ)*σ-ui)
          let MB:=1024*exp ui
          let L:=((d+2:ℕ):ℝ)*σ
          let κ:=D*σ^(3*β)
          Nonempty (AuxiliarySupport q.fst (univ.filter (goodFirst q MA L κ (1/50))) MA κ) ∧
          Nonempty (AuxiliarySupport q.snd (univ.filter (goodSecond q MB L κ (1/50))) MB κ) ∧
          q.fst.event (univ.filter (fun x=>¬goodFirst q MA L κ (1/50) x))≤3251*σ^(-2*β) ∧
          q.snd.event (univ.filter (fun x=>¬goodSecond q MB L κ (1/50) x))≤3251*σ^(-2*β) := by
  filter_upwards [eventually_actual_reciprocal d β hβ] with σ he
  intro K V _ _ _ _ _ _ _ hdim hlog Ω Θ ι C _ _ _ _ _ p θ G S u n k e own t hp D J a
    hS hf hcap hD hJ z c hz i hi
  let M:=contextual n k p θ G e own t
  have hd:=((not_badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
    c J (D*σ^β) a z.2 i).mp hi).1
  have hcaps:=prepared_context_property n k p θ G e own t hp z hz
    (fun θ=>∀ i,(((S θ i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u θ i) ∧
      (((S θ i).image Prod.snd).card:ℝ)≤1024*exp (u θ i) ∧
      ((S θ i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) hcap
  apply he K V hdim hlog (M.tupleLaw z.1|>.marginal i) (S z.1.1 (M.origin z.1 i)) D
    (u z.1.1 (M.origin z.1 i))
  · exact prepared_marginal_domain n k p θ G e own t hp z hz S hS i
  · intro x hx
    exact prepared_marginal_property n k p θ G e own t hp z hz
      (fun _ _ x=>x.1.rep x.2.rep=0) hf i x (ne_of_gt hx)
  · exact (hcaps _).1
  · exact (hcaps _).2.1
  · exact (hcaps _).2.2
  · exact hD
  · exact (sub_le_sub_right hJ _).trans hd
end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_ChronologicalOrder
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
variable {A : Type*} [Fintype A]

lemma Law.exists_mass_pos_le_of_mean_le (p : Law A) (f : A → ℝ) (c : ℝ)
    (h : (∑ a, p.mass a * f a) ≤ c) :
    ∃ a, 0 < p.mass a ∧ f a ≤ c := by
  have hp : ∃ a, 0 < p.mass a := by
    by_contra! he
    have hz : ∑ a, p.mass a = 0 := sum_eq_zero (fun a _ => (he a).antisymm (p.nonneg a))
    linarith [p.total]
  by_contra! hh
  obtain ⟨a,ha⟩ := hp
  have hle (b : A) : p.mass b * c ≤ p.mass b * f b := by
    by_cases hb : p.mass b = 0
    · simp [hb]
    · exact mul_le_mul_of_nonneg_left (hh b (lt_of_le_of_ne (p.nonneg b) (Ne.symm hb))).le (p.nonneg b)
  have hlt : (∑ b, p.mass b*c) < ∑ b, p.mass b*f b :=
    sum_lt_sum (fun b _ => hle b) ⟨a,mem_univ _,mul_lt_mul_of_pos_left (hh a ha) ha⟩
  rw [←sum_mul,p.total,one_mul] at hlt
  exact (not_lt_of_ge h) hlt

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma reverse_incidence_count (S : Finset (Projectivization K (Module.Dual K V)))
    (T : Finset (Projectivization K V)) :
    Incidence.incidenceCount T S = ((S ×ˢ T).filter (fun z => z.1.rep z.2.rep=0)).card := by
  simp only [Incidence.incidenceCount, Incidence.Incident, card_filter, sum_product]
  apply sum_congr rfl
  intro dualPoint _
  exact card_filter _ _

theorem auxiliary_cap_product {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K (Module.Dual K V)))
    (q : Law (Projectivization K V))
    (goodA : Finset (Projectivization K (Module.Dual K V)))
    (goodB : Finset (Projectivization K V))
    (MA MB κ : ℝ) (hMA : 0<MA) (hMB : 0<MB)
    (A : AuxiliarySupport p goodA MA κ) (B : AuxiliarySupport q goodB MB κ)
    (hsparse :
      (∑ a, ∑ b, A.law.mass a * B.law.mass b *
        (((((levelSet p a ∩ goodA) ×ˢ (levelSet q b ∩ goodB)).filter
          (fun z => z.1.rep z.2.rep=0)).card : ℝ) /
          (((levelSet p a ∩ goodA).card : ℝ) * (levelSet q b ∩ goodB).card)))
        ≤ 1/(4*(Nat.card K:ℝ))) :
    MA*MB ≤ 64*(Nat.card K:ℝ)^(n+3)*exp (2*κ) := by
  let SA := fun a : retainedLevels p goodA MA κ => levelSet p a ∩ goodA
  let SB := fun b : retainedLevels q goodB MB κ => levelSet q b ∩ goodB
  have hmean : (∑ ab, (A.law.prod B.law).mass ab *
      ((((SA ab.1 ×ˢ SB ab.2).filter (fun z => z.1.rep z.2.rep=0)).card:ℝ)/
        ((SA ab.1).card*(SB ab.2).card))) ≤ 1/(4*(Nat.card K:ℝ)) := by
    simpa only [Law.prod,Fintype.sum_prod_type] using hsparse
  obtain ⟨⟨a,b⟩,_,hs⟩ := (A.law.prod B.law).exists_mass_pos_le_of_mean_le _ _ hmean
  have ha := (A.size a).1
  have hb := (B.size b).1
  have hapos : (0:ℝ)<(SA a).card := (by positivity : 0<MA*exp (-κ)/2).trans_le ha
  have hbpos : (0:ℝ)<(SB b).card := (by positivity : 0<MB*exp (-κ)/2).trans_le hb
  have hsp : (Incidence.incidenceCount (SB b) (SA a):ℝ) ≤
      ((SB b).card:ℝ)*(SA a).card/(4*(Nat.card K:ℝ)) := by
    rw [reverse_incidence_count]
    have hh := (div_le_iff₀ (mul_pos hapos hbpos)).mp hs
    calc
      _ ≤ (1/(4*(Nat.card K:ℝ)))*((SA a).card*(SB b).card) := hh
      _ = _ := by ring
  have hm := Incidence.sparse_product_bound hdim (SB b) (SA a) hsp
  have hl : (MA*exp (-κ)/2)*(MB*exp (-κ)/2)≤
      ((SA a).card:ℝ)*(SB b).card :=
    mul_le_mul ha hb (by positivity) hapos.le
  have hex : exp (-κ)*exp (-κ)*exp (2*κ)=1 := by
    rw [←exp_add,←exp_add,show -κ + -κ + 2*κ = 0 by ring,exp_zero]
  have hh := mul_le_mul_of_nonneg_right (hl.trans (by simpa only [mul_comm] using hm))
    (exp_pos (2*κ)).le
  have he : (MA*exp (-κ)/2)*(MB*exp (-κ)/2)*exp (2*κ)=MA*MB/4 := by
    calc
      _ = MA*MB/4*(exp (-κ)*exp (-κ)*exp (2*κ)) := by ring
      _ = _ := by rw [hex,mul_one]
  rw [he] at hh
  linarith

theorem auxiliary_chronological_order {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K (Module.Dual K V)))
    (q : Law (Projectivization K V))
    (goodA : Finset (Projectivization K (Module.Dual K V)))
    (goodB : Finset (Projectivization K V))
    (MA MB κ u v : ℝ) (hMA : 0<MA) (hMB : 0<MB)
    (hA : exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)≤MA)
    (hB : exp v≤MB)
    (A : AuxiliarySupport p goodA MA κ) (B : AuxiliarySupport q goodB MB κ)
    (hsparse :
      (∑ a, ∑ b, A.law.mass a * B.law.mass b *
        (((((levelSet p a ∩ goodA) ×ˢ (levelSet q b ∩ goodB)).filter
          (fun z => z.1.rep z.2.rep=0)).card : ℝ) /
          (((levelSet p a ∩ goodA).card : ℝ) * (levelSet q b ∩ goodB).card)))
        ≤ 1/(4*(Nat.card K:ℝ))) :
    v≤u+2*κ+log 64 := by
  have hq : (0:ℝ)<Nat.card K := by
    exact_mod_cast (show 0<Nat.card K from Nat.zero_lt_one.trans (Finite.one_lt_card : 1<Nat.card K))
  have hp := auxiliary_cap_product hdim p q goodA goodB MA MB κ hMA hMB A B hsparse
  have hlow := mul_le_mul hA hB (exp_pos v).le hMA.le
  have he : exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)*exp v=
      (Nat.card K:ℝ)^(n+3)*exp (v-u) := by
    rw [←exp_add,show ((n+3:ℕ):ℝ)*log (Nat.card K)-u+v=
      ((n+3:ℕ):ℝ)*log (Nat.card K)+(v-u) by ring,exp_add]
    congr 1
    rw [exp_nat_mul,exp_log hq]
  rw [he] at hlow
  have hcan : exp (v-u)≤64*exp (2*κ) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hq _)).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hlow.trans hp
  have hex : exp (v-u)≤exp (2*κ+log 64) := by
    rw [exp_add,exp_log (by norm_num : (0:ℝ)<64)]
    simpa only [mul_comm] using hcan
  have := exp_le_exp.mp hex
  linarith

end
end SharpLogRamsey.Selection

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

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

theorem chronological_order_of_good_event {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (P κ u v L ε z : ℝ) (hP : 1≤P)
    (A : AuxiliarySupport (p.marginal i).fst
      (univ.filter (goodFirst (p.marginal i) (P*exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)) L κ ε))
      (P*exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)) κ)
    (B : AuxiliarySupport (p.marginal j).snd
      (univ.filter (goodSecond (p.marginal j) (P*exp v) L κ ε)) (P*exp v) κ)
    (hevent : ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay=>
      goodFirst (p.marginal i) (P*exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)) L κ ε ay.1 ∧
      goodSecond (p.marginal j) (P*exp v) L κ ε ay.2 ∧ ay.1.rep ay.2.rep=0))≤z)
    (hz : (4*exp 1)^2*z≤1/(4*(Nat.card K:ℝ))) :
    v≤u+2*κ+log 64 := by
  apply auxiliary_chronological_order hdim (p.marginal i).fst (p.marginal j).snd _ _
    _ _ κ u v (mul_pos (by linarith) (exp_pos _))
    (mul_pos (by linarith) (exp_pos _))
    (by simpa using mul_le_mul_of_nonneg_right hP (exp_pos (((n+3:ℕ):ℝ)*log (Nat.card K)-u)).le)
    (by simpa using mul_le_mul_of_nonneg_right hP (exp_pos v).le) A B
  exact (auxiliary_three_estimates p i j _ _ L κ ε z A B hevent).1.trans hz

end
end SharpLogRamsey.Selection

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

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_OpenMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype Ω] [Fintype Θ] {d : ℕ}
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.moveDec
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
local instance moveSlotDec_r0c722e_1 : DecidableEq (Slot w (n+k)) :=
  @instDecidableEqProd (Fin w) (Fin (4*(n+k))) (@instDecidableEqFin w) (@instDecidableEqFin (4*(n+k)))
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.moveBlockDec
variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (z : (model w n k p θ G t).FreshHistory)
  (hz : ((model w n k p θ G t).freshLaw hp).mass z≠0)
local notation "M" => model w n k p θ G t
local notation "q" => ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst z)

include hp hz

theorem open_window_deletion
    (hdim : Module.finrank K V=d+3)
    (r : ℕ) (hr : r≤d+3) (κ gap J D a : ℝ) (hgap : 0≤gap)
    (u : (M).Index z.1→ℝ)
    (hband : ∀ i,OpenBand r (log (Nat.card K)) gap (u i))
    (hsmall : log 1024+3*κ<gap) (hκ : log (200/97)≤κ)
    (hsparse : (4*exp 1)^2*(20000*((d:ℝ)+3)^2*a)≤1/(4*(Nat.card K:ℝ)))
    (hcon : ∀ ω,p.mass ω≠0→∀ i j,position i<position j→
      (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0)
    (hsupp :
      let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) (fun _ _=>0) J D a z.2
      ∀ i,i∉bad→
      let qi:=(q).marginal i
      let MA:=1024*exp (((d+3:ℕ):ℝ)*log (Nat.card K)-u i)
      let MB:=1024*exp (u i)
      let L:=((d+2:ℕ):ℝ)*log (Nat.card K)
      Nonempty (AuxiliarySupport qi.fst (univ.filter (goodFirst qi MA L κ (1/50))) MA κ) ∧
      Nonempty (AuxiliarySupport qi.snd (univ.filter (goodSecond qi MB L κ (1/50))) MB κ)) :
    let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) (fun _ _=>0) J D a z.2
    let live:=univ\badWindows ((M).representative z) bad
    gap*((live.filter (fun i=>gap<u ((M).representative z (i,false))-
      u ((M).representative z (i,true)))).card:ℝ)≤
      log (Nat.card K)+(2*κ+log 64)*w := by
  dsimp only
  let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) (fun _ _=>0) J D a z.2
  let live:=univ\badWindows ((M).representative z) bad
  have hgood : ∀ i∈live,∀ c,(M).representative z (i,c)∉bad := by
    intro i hi v
    have hh:¬((M).representative z (i,false)∈bad ∨ (M).representative z (i,true)∈bad) := by
      simpa only [live,mem_sdiff,mem_univ,true_and,badWindows,mem_filter,true_and] using hi
    cases v
    · exact fun h=>hh (Or.inl h)
    · exact fun h=>hh (Or.inr h)
  have hcross : ∀ i∈live,∀ j∈live,i<j→
      u ((M).representative z (j,false))≤u ((M).representative z (i,true))+(2*κ+log 64) := by
    intro i hi j hj hij
    let ii:=(M).representative z (i,true)
    let jj:=(M).representative z (j,false)
    have he:=prepared_open_event n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz position hcon ii jj
      (representative_before w n k p θ G t z i j hij true false)
      1024 κ gap (u ii) (u jj) J D a (d+2) r
      (by simpa [Nat.add_assoc] using hdim) (by norm_num) (by omega)
      (hband ii) (hband jj) hsmall hκ
      (Or.inl ⟨hgood i hi true,representative_other w n k p θ G t z (j,false) (i,true) (by simp)⟩)
    have hh:=chronological_order_of_good_event hdim q ii jj 1024 κ (u ii) (u jj)
      (((d+2:ℕ):ℝ)*log (Nat.card K)) (1/50) (20000*((d:ℝ)+3)^2*a) (by norm_num)
      (hsupp ii (hgood i hi true)).1.some (hsupp jj (hgood j hj false)).2.some
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,show (d:ℝ)+2+1=(d:ℝ)+3 by ring] using he)
      hsparse
    simpa only [add_assoc] using hh
  have hlog : 0≤log (Nat.card K:ℝ) := by
    apply log_nonneg
    exact_mod_cast (show 1≤Nat.card K from Finite.card_pos)
  have hκ0 : 0≤κ := (log_nonneg (by norm_num : (1:ℝ)≤200/97)).trans hκ
  have hh:=downward_deleted live
    (fun i=>u ((M).representative z (i,false)))
    (fun i=>u ((M).representative z (i,true)))
    (((r:ℝ)-1)*log (Nat.card K)) ((r:ℝ)*log (Nat.card K)) (2*κ+log 64) gap
    (by nlinarith) (by have hl:=log_nonneg (show (1:ℝ)≤64 by norm_num); linarith)
    (by intro i hi; have hb:=(hband ((M).representative z (i,true))).1; linarith)
    (by intro i hi; have hb:=(hband ((M).representative z (i,false))).2; linarith)
    hcross
  simp only [Fintype.card_fin] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_UniformMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.movementFinDec
local instance movementSlotDec_r0c722e_1 (w L : ℕ) : DecidableEq (Slot w L) :=
  @instDecidableEqProd (Fin w) (Fin (4*L)) (@instDecidableEqFin w) (@instDecidableEqFin (4*L))
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.movementBlockDec
theorem eventually_open_movement_oai (d : ℕ) (η c ε : ℝ)
    (hη : 0<η) (hc : 0 < c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ (D : ℝ), σ^beta η≤D → D≤σ^(1-η/2) →
      ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J : ℝ),
        c*σ^(1+η/2)≤(w:ℝ)*D → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,OpenBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
          (z : (model w n k p θ G t).FreshHistory),
          ((model w n k p θ G t).freshLaw hp).mass z≠0 →
          let M:=model w n k p θ G t
          let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
          let bad:=badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
            (fun _ _=>0) J (D*σ^beta η) a z.2
          let live:=univ\badWindows (M.representative z) bad
          ((live.filter (fun i=>scaleKstar σ η D<
            u z.1.1 (M.origin z.1 (M.representative z (i,false)))-
              u z.1.1 (M.origin z.1 (M.representative z (i,true))))).card:ℝ)≤ε*w := by
  filter_upwards [eventually_prepared_reciprocal d (beta η) (beta_pos hη),
    eventually_integer_regime η hη,eventually_open_regime η d hη,
    eventually_open_deletion_small η c ε hη hc hε,eventually_ge_atTop (1:ℝ)]
    with σ hsupp hreg hopen hdelete hσ
  intro K V _ _ _ _ _ _ _ hdim hlog D hDl hDu Ω Θ _ _ w n k p θ G S u r J hw hr hJ hS hf hcon hcap hband t hp z hz
  let M:=model w n k p θ G t
  let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
  let κ:=scaleK σ η D
  let gap:=scaleKstar σ η D
  have hσ0 : 0<σ := lt_of_lt_of_le zero_lt_one hσ
  have hD : 0<D := (rpow_pos_of_pos hσ0 _).trans_le hDl
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  have hg : 0<gap := by dsimp [gap,scaleKstar]; positivity
  have hpb : ∀ i,OpenBand r (log (Nat.card K)) gap (u z.1.1 (M.origin z.1 i)) := by
    have hh:=prepared_context_property n k p θ G (fun _=>embedding w (n+k))
      (fun _=>owner w (n+k)) t hp z hz (fun θ=>∀ i,OpenBand r σ gap (u θ i)) hband
    intro i
    rw [hlog]
    exact hh _
  have hh:=open_window_deletion w n k p θ G t hp z hz hdim r hr κ gap J (D*σ^beta η) a hg.le
    (fun i=>u z.1.1 (M.origin z.1 i)) hpb (hopen D (Nat.card K) hDl hq).1
    (hreg D hDl hDu).2.1 (hopen D (Nat.card K) hDl hq).2 hcon (by
      dsimp only
      intro i hi
      have hh:=hsupp K V hdim hlog Ω Θ (Slot w (n+k)) (Block w) p θ G S u n k
        (fun _=>embedding w (n+k)) (fun _=>owner w (n+k)) t hp D J a hS hf hcap hDl hJ z (fun _ _=>0) hz i hi
      simpa only [hlog,κ,scaleK] using And.intro hh.1 hh.2.1)
  rw [hlog] at hh
  have hb:=hdelete D (w:ℝ) hDl (by positivity) hw
  dsimp only [gap,κ] at hh hg
  dsimp only
  nlinarith
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.Selection.Windows.eventually_open_movement_oai := @OAI.SharpLogRamsey.Selection.Windows.eventually_open_movement_oai
