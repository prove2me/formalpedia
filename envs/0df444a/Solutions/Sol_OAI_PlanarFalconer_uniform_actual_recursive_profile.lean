-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_recursive_profile
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:16:00.92123+00:00
-- url     : https://prove2.me/submissions/9326a671-72bb-42db-8b0c-bb77cbc5b19b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_recursive_energy_rules

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem finiteMin_le {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteMin s f ≤ f i := by
  rw [finiteMin, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le f hi

theorem le_finiteMin {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) {c : ℝ} (h : ∀ i ∈ s, c ≤ f i) : c ≤ finiteMin s f := by
  rw [finiteMin, dite_eq_left hs]
  exact Finset.le_inf' hs f h

theorem depthPairs_nonempty {a t Q : ℕ} (hQ : 0 < Q) (hw : a + Q ≤ t) :
    (depthPairs a t Q).Nonempty := by
  refine ⟨(a,a+Q), mem_depthPairs.mpr ?_⟩
  omega

theorem potential_le (A : ℕ → ℝ) {a t Q i j : ℕ}
    (hi : a ≤ i) (hij : i < j) (hjt : j ≤ t) (hgap : i + Q ≤ j) :
    potential A a t Q ≤ A i + A j :=
  finiteMin_le _ (mem_depthPairs.mpr ⟨hi,hij,hjt,hgap⟩)

theorem le_potential (A : ℕ → ℝ) {a t Q : ℕ} (hQ : 0 < Q)
    (hw : a+Q ≤ t) {c : ℝ}
    (h : ∀ i j, a ≤ i → i < j → j ≤ t → i+Q ≤ j → c ≤ A i + A j) :
    c ≤ potential A a t Q := by
  apply le_finiteMin (depthPairs_nonempty hQ hw)
  rintro ⟨i,j⟩ hij
  obtain ⟨hi, hij, hjt, hgap⟩ := mem_depthPairs.mp hij
  exact h i j hi hij hjt hgap

theorem potential_mono (A : ℕ → ℝ) {a b u t Q : ℕ}
    (hQ : 0 < Q) (hw : b+Q ≤ u) (hab : a ≤ b) (hut : u ≤ t) :
    potential A a t Q ≤ potential A b u Q := by
  apply le_potential A hQ hw
  intro i j hbi hij hju hgap
  exact potential_le A (hab.trans hbi) hij (hju.trans hut) hgap

theorem prefix_payment (A : ℕ → ℝ) {a p v t Q i₀ : ℕ}
    (hQ : 0 < Q) (hw : p+Q ≤ v) (hai : a ≤ i₀) (hip : i₀ ≤ p)
    (hvt : v ≤ t) (hcontrolled : ∀ i, p ≤ i → i+Q ≤ v → A p ≤ A i) :
    potential A a t Q + (A p - A i₀) ≤ potential A p v Q := by
  apply le_potential A hQ hw
  intro i j hpi hij hjv hgap
  have hparent := potential_le A hai (by omega : i₀ < j) (by omega : j ≤ t)
    (by omega : i₀+Q ≤ j)
  have hAi := hcontrolled i hpi (by omega)
  linarith

theorem suffix_payment (A : ℕ → ℝ) {a p t Q j₀ : ℕ}
    (hQ : 0 < Q) (hw : a+Q ≤ p) (hpj : p ≤ j₀) (hjt : j₀ ≤ t)
    (hcontrolled : ∀ j, a+Q ≤ j → j ≤ p → A p ≤ A j) :
    potential A a t Q + (A p - A j₀) ≤ potential A a p Q := by
  apply le_potential A hQ hw
  intro i j hai hij hjp hgap
  have hparent := potential_le A hai (by omega : i < j₀) hjt
    (by omega : i+Q ≤ j₀)
  have hAj := hcontrolled j (by omega) hjp
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Ledger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem intervalMin_attained (A : ℕ → ℝ) {a t : ℕ} (hat : a ≤ t) :
    ∃ i, a ≤ i ∧ i ≤ t ∧ intervalMin A a t = A i := by
  have hn : (Finset.Icc a t).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl,hat⟩⟩
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hn A
  exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
    by simpa only [intervalMin, finiteMin, dite_eq_left hn] using he⟩

theorem policy_prefix_payment (A : ℕ → ℝ) {a p v t l r q : ℕ}
    (hq : 0 < q) (hw : p+10*q ≤ v) (hap : a ≤ p) (hvt : v ≤ t)
    (hlp : l ≤ p) (htr : t ≤ r+2*q)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a t (10*q) + height A a p ≤ potential A p v (10*q) := by
  obtain ⟨i,hai,hip,hmin⟩ := intervalMin_attained A hap
  unfold height
  rw [hmin]
  apply prefix_payment A (by omega) hw hai hip hvt
  intro n hpn hnv
  exact hinner n (by omega) (by omega)

theorem policy_suffix_payment (A : ℕ → ℝ) {a p t l r q : ℕ}
    (hq : 0 < q) (hw : a+10*q ≤ p) (hpt : p ≤ t)
    (hla : l ≤ a+2*q) (hpr : p ≤ r)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a t (10*q) + (A p - intervalMin A p t) ≤
      potential A a p (10*q) := by
  obtain ⟨j,hpj,hjt,hmin⟩ := intervalMin_attained A hpt
  rw [hmin]
  apply suffix_payment A (by omega) hw hpj hjt
  intro n han hnp
  exact hinner n (by omega) (by omega)

theorem branch_cost_bound (V C : ℕ → ℝ) (n : ℕ)
    (hpay : ∀ k < n, V k + C k ≤ V (k+1)) :
    ∑ k ∈ Finset.range n, C k ≤ V n - V 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hs := ih (fun k hk => hpay k (by omega))
    have hn := hpay n (by omega)
    linarith

theorem profile_increments_telescope (A : ℕ → ℝ) (start : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ Finset.range n, -2 * (A (start (k+1)) - A (start k)) =
      2*A (start 0) - 2*A (start n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem nearby_pair {a t f Q : ℕ} (hQ : 0 < Q) (hw : a+Q ≤ t)
    (haf : a ≤ f) (hft : f ≤ t) :
    ∃ i j, a ≤ i ∧ i < j ∧ j ≤ t ∧ i+Q = j ∧
      i ≤ f ∧ f ≤ j ∧ f ≤ i+Q ∧ j ≤ f+Q := by
  refine ⟨max a (f-Q), max a (f-Q)+Q, ?_⟩
  omega

theorem potential_near_final (A : ℕ → ℝ) {a t f Q : ℕ} {e : ℝ}
    (hQ : 0 < Q) (hw : a+Q ≤ t) (haf : a ≤ f) (hft : f ≤ t)
    (hlocal : ∀ i, a ≤ i → i ≤ t → i ≤ f+Q → f ≤ i+Q → A i ≤ A f+e) :
    potential A a t Q ≤ 2*A f+2*e := by
  obtain ⟨i,j,hai,hij,hjt,hgap,hif,hfj,hfi,hjf⟩ := nearby_pair hQ hw haf hft
  have hp := potential_le A (Q := Q) hai hij hjt (by omega)
  have hi := hlocal i hai (by omega) (by omega) hfi
  have hj := hlocal j (by omega) hjt hjf (by omega)
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RegularizationSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Filter
open scoped Topology ENNReal

theorem fixed_polynomial_subpower (k : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ((4*(N:ℝ)+1)^k) ≤ ((2:ℝ)^N)^e := by
  have hb : 1 < (2:ℝ)^e := Real.one_lt_rpow (by norm_num) he
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hb).const_mul ((5:ℝ)^k)
  have hevent : ∀ᶠ N : ℕ in atTop, (5:ℝ)^k*((N:ℝ)^k/((2:ℝ)^e)^N) < 1 := by
    exact ht.eventually (gt_mem_nhds (by simp : (5:ℝ)^k*0 < (1:ℝ)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 N₀,?_⟩
  intro N hN
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast ((le_max_left 1 N₀).trans hN)
  have hh := hN₀ N ((le_max_right 1 N₀).trans hN)
  rw [← mul_div_assoc] at hh
  have hp : 0 < ((2:ℝ)^e)^N := by positivity
  have hpol : (4*(N:ℝ)+1)^k ≤ (5:ℝ)^k*(N:ℝ)^k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hbound := hpol.trans ((div_lt_one hp).mp hh).le
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm e (N:ℝ),
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hbound
  exact hbound

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policy_right_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, t-2*q ≤ (k+1)*q-1 := by
  let j := (t-q+1)/q
  have hj : 0 < j := Nat.div_pos (by omega) hq
  have hlo := Nat.div_mul_le_self (t-q+1) q
  have hhi := Nat.lt_mul_div_succ (t-q+1) hq
  change j*q ≤ t-q+1 at hlo
  rw [Nat.mul_comm q] at hhi
  change t-q+1 < (j+1)*q at hhi
  have hmul : (j+1)*q = j*q+q := by ring
  have he : (j-1+1)*q = j*q := by rw [Nat.sub_add_cancel hj]
  have he' : (j-1)*q+q = j*q := by simpa only [Nat.add_mul,one_mul] using he
  have hleft : a+q ≤ (j-1)*q := by omega
  have hkn : (j-1)*q ≤ N := by omega
  refine ⟨j-1,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hleft,by omega⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_minimizes (A : ℕ → ℝ) {N q a t n : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) (hn : n ≤ N)
    (hblock : n/q ∈ policyBlocks N q a t) : A (policyDepth A N q a t) ≤ A n := by
  have hkey := finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))
  have hcell : n ∈ policyBlock N q (n/q) := by
    apply Finset.mem_Ico.mpr
    have hlo := Nat.div_mul_le_self n q
    have hhi := Nat.lt_mul_div_succ n hq
    rw [Nat.mul_comm q] at hhi
    exact ⟨hlo,lt_min hhi (Nat.lt_succ_of_le hn)⟩
  exact (hkey.2 _ hblock).trans
    ((policyRepresentative_spec A hq ((Nat.div_mul_le_self n q).trans hn)).2.2.2 n hcell)

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyInteriorInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policy_blocks_order_convex {N q a t j k l : ℕ}
    (hj : j ∈ policyBlocks N q a t) (hl : l ∈ policyBlocks N q a t)
    (hjk : j ≤ k) (hkl : k ≤ l) : k ∈ policyBlocks N q a t := by
  have hj' := policyBlocks_mem hj
  have hl' := policyBlocks_mem hl
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_,?_⟩
  · exact hj'.2.1.trans (Nat.mul_le_mul_right q hjk)
  · exact (Nat.mul_le_mul_right q (Nat.add_le_add_right hkl 1)).trans hl'.2.2

theorem policy_interior_interval (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ l u : ℕ, l ≤ a+2*q ∧ t ≤ u+2*q ∧
      l ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ u ∧
      ∀ n, l ≤ n → n ≤ u → A (policyDepth A N q a t) ≤ A n := by
  let S := policyBlocks N q a t
  have hS : S.Nonempty := policyBlocks_nonempty hq ht hwide
  let j := S.min' hS
  let k := S.max' hS
  have hj : j ∈ S := S.min'_mem hS
  have hk : k ∈ S := S.max'_mem hS
  have hj' := policyBlocks_mem hj
  have hk' := policyBlocks_mem hk
  have hkpos : 0 < (k+1)*q := Nat.mul_pos (by omega) hq
  have huN : (k+1)*q-1 ≤ N := by omega
  obtain ⟨j₀,hj₀,hleft⟩ := policy_left_block hq ht hwide
  obtain ⟨k₀,hk₀,hright⟩ := policy_right_block hq ht hwide
  have hjj₀ : j ≤ j₀ := S.min'_le j₀ hj₀
  have hk₀k : k₀ ≤ k := S.le_max' k₀ hk₀
  have hlower : j*q ≤ a+2*q := (Nat.mul_le_mul_right q hjj₀).trans hleft
  have hupper : t ≤ ((k+1)*q-1)+2*q := by
    have hh := Nat.mul_le_mul_right q (Nat.add_le_add_right hk₀k 1)
    omega
  let key := policyKey A N q a t
  have hkey : key ∈ S := (finiteArgmin_spec hS (fun j => A (policyRepresentative A N q j))).1
  have hkeylo : j ≤ key := S.min'_le key hkey
  have hkeyhi : key ≤ k := S.le_max' key hkey
  have hrep := policyRepresentative_spec A hq
    ((Nat.le_div_iff_mul_le hq).mp (policyBlocks_mem hkey).1)
  have hplo : j*q ≤ policyDepth A N q a t := (Nat.mul_le_mul_right q hkeylo).trans hrep.1
  have hphi : policyDepth A N q a t ≤ (k+1)*q-1 := by
    have hh := hrep.2.1.trans_le (Nat.mul_le_mul_right q (Nat.add_le_add_right hkeyhi 1))
    exact Nat.le_sub_one_of_lt hh
  refine ⟨j*q,(k+1)*q-1,hlower,hupper,hplo,hphi,?_⟩
  intro n hnlo hnhi
  have hnN : n ≤ N := hnhi.trans huN
  have hjn : j ≤ n/q := (Nat.le_div_iff_mul_le hq).mpr hnlo
  have hnk : n/q ≤ k := by
    have hh : n < (k+1)*q := by omega
    have hd := (Nat.div_lt_iff_lt_mul hq).mpr hh
    omega
  exact policyDepth_minimizes A hq hS hnN (policy_blocks_order_convex hj hk hjn hnk)

theorem policy_representatives_card (A : ℕ → ℝ) (N q : ℕ) :
    (policyRepresentatives A N q).card ≤ N/q+1 :=
  Finset.card_image_le.trans (by simp)

theorem policyDepth_mem_representatives (A : ℕ → ℝ) {N q a t : ℕ}
    (hne : (policyBlocks N q a t).Nonempty) :
    policyDepth A N q a t ∈ policyRepresentatives A N q := by
  have hk := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  exact Finset.mem_image.mpr ⟨policyKey A N q a t,(Finset.mem_filter.mp hk).1,rfl⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_anchor (A : ℕ → ℝ) {N q b u : ℕ} {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) : descriptorAnchor d = policyDepth A N q b u := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    rfl
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d; rfl
    · simp at hd

theorem policyDescriptor_anchor_mem (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) :
    descriptorAnchor d ∈ policyRepresentatives A N q := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  rw [originDescriptor_anchor A hd]
  exact policyDepth_mem_representatives A (policyBlocks_nonempty hq huN hwide)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualFarBuffer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem sourceFarBuffer_ge_length (N L : ℕ) (sig : ℝ) : L ≤ sourceFarBuffer N L sig :=
  le_max_left _ _

theorem sourceFarBuffer_ge_slack (N L : ℕ) (sig : ℝ) :
    10*sig*(N:ℝ) ≤ (sourceFarBuffer N L sig:ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

theorem uniform_source_far_buffer {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L v a : ℕ,
      let L₀ := sourceFarBuffer N L sig
      let h := v-2*L₀
      a < h →
      let d := h-a
      a+d = h ∧ a+d+5 < v ∧
      (v:ℝ)-(a+d:ℕ) = 2*(L₀:ℝ) ∧ (L:ℝ) ≤ (L₀:ℝ) ∧
      10*sig*(N:ℝ) ≤ (L₀:ℝ) := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (1/sig)
  refine ⟨N₀,?_⟩
  intro N hN L v a
  dsimp only
  intro hah
  have hNs : 1/sig < (N:ℝ) := h₀.trans_le (Nat.cast_le.mpr hN)
  have hsigN : 1 < sig*(N:ℝ) := by
    have ht := (div_lt_iff₀ hsig).mp hNs
    linarith
  have hslack := sourceFarBuffer_ge_slack N L sig
  have hbuf : 5 < 2*sourceFarBuffer N L sig := by
    have hb : (5:ℝ) < 2*(sourceFarBuffer N L sig:ℝ) := by linarith
    exact_mod_cast hb
  have h2 : 2*sourceFarBuffer N L sig ≤ v := by omega
  have he : a+(v-2*sourceFarBuffer N L sig-a) = v-2*sourceFarBuffer N L sig := by omega
  refine ⟨he,by omega,?_,Nat.cast_le.mpr (sourceFarBuffer_ge_length N L sig),hslack⟩
  rw [he,Nat.cast_sub h2,Nat.cast_mul,Nat.cast_ofNat]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualOuterMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourcePolicyBlock_pos {N : ℕ} (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) :
    0 < sourcePolicyBlock N kap := by
  unfold sourcePolicyBlock
  exact Nat.ceil_pos.mpr (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixPolicyGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem prefix_policy_geometry (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t) :
    let p := policyDepth A N q a t
    a < p ∧ p ≤ t ∧ q ≤ p-a ∧ 2*(p-a) ≤ t-a ∧
      PolicyDescriptor.parallel a p ∈ policyDescriptorList A N q a t := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq htN hw)
  dsimp only
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · change PolicyDescriptor.parallel a (policyDepth A N q a t) ∈ originDescriptors A N q a t
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_Ico.mpr ⟨?_,by omega⟩,rfl⟩
    have he : min (policyDepth A N q a t-a) (t-policyDepth A N q a t) =
        policyDepth A N q a t-a := min_eq_left (by omega)
    rw [he]
    omega

theorem source_policy_block_lower (N : ℕ) (kap : ℝ) :
    kap*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := Nat.le_ceil _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualDirectBuffer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem uniform_source_ceiling_slack {sig kap : ℝ}
    (hsig : 0 < sig) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap ∧
      10*sig*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) ∧
      sig*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (1/sig)
  refine ⟨max 1 N₀,by omega,?_⟩
  intro N hN
  have hNs : 1/sig < (N:ℝ) := h₀.trans_le (Nat.cast_le.mpr (by omega))
  have hsigN : 1 < sig*(N:ℝ) := by
    have := (div_lt_iff₀ hsig).mp hNs
    linarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 10*sig*(N:ℝ) by positivity)
  have hblock := source_policy_block_lower N kap
  have hgapN : 1000*sig*(N:ℝ) ≤ kap*N :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hlt : (⌈10*sig*(N:ℝ)⌉₊:ℝ) < (sourcePolicyBlock N kap:ℝ) := by linarith
  exact ⟨Nat.cast_lt.mp hlt,by linarith,by linarith⟩

theorem direct_buffer_eq_length {N L q a v : ℕ} {sig : ℝ}
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q) (hw : a+100*q < v)
    (hdirect : v-2*sourceFarBuffer N L sig ≤ a) :
    sourceFarBuffer N L sig = L ∧ v ≤ a+2*L ∧ 0 < L := by
  have hv : v ≤ a+2*sourceFarBuffer N L sig := by omega
  have hL : ⌈10*sig*(N:ℝ)⌉₊ ≤ L := by
    by_contra h
    have he : sourceFarBuffer N L sig = ⌈10*sig*(N:ℝ)⌉₊ := max_eq_right (by omega)
    rw [he] at hv
    omega
  have he : sourceFarBuffer N L sig = L := max_eq_left hL
  rw [he] at hv
  exact ⟨he,hv,by omega⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ActualPolicyPayments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem actual_prefix_policy_payment (A : ℕ → ℝ) {N q a t v : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t) (hvt : v ≤ t) (hhigh : t-v ≤ q) :
    let p := policyDepth A N q a t
    p+10*q ≤ v ∧
      potential A a t (10*q)+height A a p ≤ potential A p v (10*q) := by
  have hg := prefix_policy_geometry A hq htN hw hpref
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq htN hw
  have hwidth : policyDepth A N q a t+10*q ≤ v := by omega
  exact ⟨hwidth,policy_prefix_payment A hq hwidth hg.1.le hvt hlp hr hinner⟩

theorem actual_suffix_policy_payment (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hsuffix : a+t < 2*policyDepth A N q a t) :
    let p := policyDepth A N q a t
    a+10*q ≤ p ∧
      potential A a t (10*q)+(A p-intervalMin A p t) ≤ potential A a p (10*q) := by
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq htN hw)
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq htN hw
  have hwidth : a+10*q ≤ policyDepth A N q a t := by omega
  exact ⟨hwidth,policy_suffix_payment A hq hwidth (by omega) hl hpr hinner⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InheritedPolicyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem remainingPolicyDescriptors_mono (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    remainingPolicyDescriptors A N q a₀ t₀ p ⊆ remainingPolicyDescriptors A N q a₀ t₀ a := by
  intro d hd
  obtain ⟨hd,hp⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd,hap.trans_lt hp⟩

 theorem reached_anchor_strictly_reduces_list (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ}
    (hap : a ≤ p) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a) (hp : descriptorAnchor d ≤ p) :
    (remainingPolicyDescriptors A N q a₀ t₀ p).card <
      (remainingPolicyDescriptors A N q a₀ t₀ a).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨remainingPolicyDescriptors_mono A N q a₀ t₀ hap,?_⟩
  intro he
  rw [← he] at hd
  have hh := (Finset.mem_filter.mp hd).2
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNearProgress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem remaining_maximum_preserved (A : ℕ → ℝ) {N q a₀ t₀ a p : ℕ}
    (hap : a ≤ p) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a)
    (hm : descriptorLength d = (remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength)
    (hanchor : p < descriptorAnchor d) :
    (remainingPolicyDescriptors A N q a₀ t₀ p).sup descriptorLength =
      (remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength := by
  apply le_antisymm
  · exact Finset.sup_mono (remainingPolicyDescriptors_mono A N q a₀ t₀ hap)
  · rw [← hm]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,hanchor⟩)

theorem actual_near_progress (A : ℕ → ℝ) {N q a₀ t₀ a v : ℕ} {sig : ℝ}
    (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    (hnear : a < v-2*sourceFarBuffer N
      ((remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength) sig) :
    let S := remainingPolicyDescriptors A N q a₀ t₀ a
    let L := S.sup descriptorLength
    let b := v-2*sourceFarBuffer N L sig
    v ≤ b+100*q ∨
      (∃ d ∈ S, descriptorLength d = L ∧ a < descriptorAnchor d ∧ descriptorAnchor d ≤ b ∧
        descriptorAnchor d ∈ policyRepresentatives A N q ∧
        (remainingPolicyDescriptors A N q a₀ t₀ b).card < S.card) ∨
      ((remainingPolicyDescriptors A N q a₀ t₀ b).sup descriptorLength = L ∧
        v-2*sourceFarBuffer N
          ((remainingPolicyDescriptors A N q a₀ t₀ b).sup descriptorLength) sig = b) := by
  classical
  dsimp only
  let S := remainingPolicyDescriptors A N q a₀ t₀ a
  let L := S.sup descriptorLength
  let b := v-2*sourceFarBuffer N L sig
  by_cases hterm : v ≤ b+100*q
  · exact Or.inl hterm
  apply Or.inr
  have hb := direct_buffer_eq_length hceil (by omega : b+100*q < v) (le_refl b)
  have hLpos : 0 < L := hb.2.2
  have hS : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : L = 0 := by simp [L,he]
    omega
  by_cases hpassed : ∃ d ∈ S, descriptorLength d = L ∧ descriptorAnchor d ≤ b
  · obtain ⟨d,hd,hm,hdb⟩ := hpassed
    have hap := (Finset.mem_filter.mp hd).2
    exact Or.inl ⟨d,hd,hm,hap,hdb,
      policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp hd).1,
      reached_anchor_strictly_reduces_list A N q a₀ t₀ hnear.le hd hdb⟩
  · obtain ⟨d,hd,hm⟩ := Finset.exists_mem_eq_sup S hS descriptorLength
    have hdb : b < descriptorAnchor d := by
      by_contra h
      exact hpassed ⟨d,hd,hm.symm,by omega⟩
    have he := remaining_maximum_preserved A hnear.le hd hm.symm hdb
    exact Or.inr ⟨he,by rw [he]⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchRepresentativeCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem branch_charges_injective {n : ℕ} (start charge : ℕ → ℕ)
    (C : Finset ℕ) (hC : C ⊆ Finset.range n)
    (hstart : MonotoneOn start (Set.Icc 0 n))
    (hcharge : ∀ j ∈ C, start j < charge j ∧ charge j ≤ start (j+1)) :
    Set.InjOn charge C := by
  intro i hi j hj he
  have hiN := Finset.mem_range.mp (hC hi)
  have hjN := Finset.mem_range.mp (hC hj)
  have hci := hcharge i hi
  have hcj := hcharge j hj
  rcases lt_trichotomy i j with hij | hij | hji
  · have hm := hstart (show i+1 ∈ Set.Icc 0 n by constructor <;> omega)
      (show j ∈ Set.Icc 0 n by constructor <;> omega) (by omega : i+1 ≤ j)
    omega
  · exact hij
  · have hm := hstart (show j+1 ∈ Set.Icc 0 n by constructor <;> omega)
      (show i ∈ Set.Icc 0 n by constructor <;> omega) (by omega : j+1 ≤ i)
    omega

theorem branch_representative_charges_bound (A : ℕ → ℝ) (N q n : ℕ)
    (start charge : ℕ → ℕ) (C : Finset ℕ) (hC : C ⊆ Finset.range n)
    (hstart : MonotoneOn start (Set.Icc 0 n))
    (hcharge : ∀ j ∈ C, start j < charge j ∧ charge j ≤ start (j+1))
    (hrep : ∀ j ∈ C, charge j ∈ policyRepresentatives A N q) :
    C.card ≤ (policyRepresentatives A N q).card ∧ C.card ≤ N/q+1 := by
  have hi := branch_charges_injective start charge C hC hstart hcharge
  have hc : C.card ≤ (policyRepresentatives A N q).card := by
    calc
      _ = (C.image charge).card := (Finset.card_image_of_injOn hi).symm
      _ ≤ _ := Finset.card_le_card (by
        intro p hp
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
        exact hrep j hj)
  exact ⟨hc,hc.trans (policy_representatives_card A N q)⟩

theorem source_representatives_real_bound (A : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) (hkap1 : kap ≤ 1) :
    ((policyRepresentatives A N (sourcePolicyBlock N kap)).card:ℝ) ≤ 2/kap := by
  let q := sourcePolicyBlock N kap
  have hq : 0 < q := sourcePolicyBlock_pos hN hkap
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hc : ((policyRepresentatives A N q).card:ℝ) ≤ ((N/q:ℕ):ℝ)+1 := by
    exact_mod_cast policy_representatives_card A N q
  have hmul : ((N/q:ℕ):ℝ)*(q:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N q
  have hdiv : ((N/q:ℕ):ℝ) ≤ (N:ℝ)/(q:ℝ) := (le_div_iff₀ hqR).mpr hmul
  have hblock := source_policy_block_lower N kap
  have hrat : (N:ℝ)/(q:ℝ) ≤ 1/kap := (div_le_div_iff₀ hqR hkap).mpr (by
    change (N:ℝ)*kap ≤ 1*(sourcePolicyBlock N kap:ℝ)
    nlinarith)
  have hone : 1 ≤ 1/kap := (le_div_iff₀ hkap).mpr (by simpa using hkap1)
  change ((policyRepresentatives A N q).card:ℝ) ≤ 2/kap
  have he : 2/kap = 1/kap+1/kap := by ring
  rw [he]
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchTransitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

namespace BranchState

theorem valid_depths {N : ℕ} {sig : ℝ} {s : BranchState} (h : s.Valid N sig) :
    s.start ≤ s.finish ∧ s.finish ≤ N := by
  cases s <;> simp only [Valid,start,finish] at *
  · exact h
  · omega

end BranchState

namespace BranchStep
variable {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
variable {s u : BranchState} {label : BranchLabel}

theorem nonterminal (h : BranchStep A N q sig s label u) : s.start+100*q < s.finish := by
  cases h <;> assumption

theorem nested (h : BranchStep A N q sig s label u) (hq : 0 < q)
    (hv : s.Valid N sig) : s.start ≤ u.start ∧ u.finish ≤ s.finish := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    simp only [BranchState.start,BranchState.finish]
    omega
  | low _ hm _ =>
    have hm := Finset.mem_Ioc.mp hm
    exact ⟨le_rfl,hm.2⟩
  | high hw _ hm _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    have hm := Finset.mem_Ioc.mp hm
    exact ⟨by dsimp [BranchState.start]; omega,hm.2⟩
  | near _ hs => exact ⟨hs.le,le_rfl⟩
  | far _ _ hm =>
    have hm := Finset.mem_Icc.mp hm
    exact ⟨by dsimp [BranchState.start]; omega,le_rfl⟩
  | direct _ hw => exact ⟨hw.anchor_gt.le,le_rfl⟩

theorem index_change (h : BranchStep A N q sig s label u) :
    u.index = s.index + (if label = .suffix ∨ label = .low ∨ label = .far then 1 else 0) := by
  cases h <;> simp [BranchState.index]

theorem episode_balance (h : BranchStep A N q sig s label u) :
    u.angular + (if label = .far then 1 else 0) =
      s.angular + (if label = .high then 1 else 0) := by
  cases h <;> simp [BranchState.angular]

theorem suffix_decrease (h : BranchStep A N q sig s .suffix u) (hq : 0 < q)
    (hv : s.Valid N sig) : u.finish+q ≤ s.finish := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    dsimp only [BranchState.finish]
    omega

theorem low_decrease (h : BranchStep A N q sig s .low u) :
    (u.finish:ℝ)+sig*N ≤ s.finish := by
  cases h with
  | low _ _ hg => dsimp only [BranchState.finish]; linarith

theorem graph_charge (h : BranchStep A N q sig s label u) (hq : 0 < q)
    (hv : s.Valid N sig) (hg : label = .high ∨ label = .direct) :
    s.start < u.start ∧ u.start ∈ policyRepresentatives A N q := by
  cases h with
  | high hw _ _ _ =>
    have hn := policyBlocks_nonempty hq hv.2 hw
    have hp := policyDepth_interior A hq hn
    exact ⟨by dsimp [BranchState.start]; omega,policyDepth_mem_representatives A hn⟩
  | direct _ hw =>
    exact ⟨hw.anchor_gt,policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp hw.mem).1⟩
  | _ => simp at hg

end BranchStep

theorem near_uncharged_next_direct {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    {s u w : BranchState} {label : BranchLabel}
    (h : BranchStep A N q sig s .near u) (hn : ¬ ChargedNear A N q s u)
    (hnext : BranchStep A N q sig u label w) : label = .direct := by
  have hw := hnext.nonterminal
  cases h with
  | near hwide hnear =>
    obtain ht | hp | he := actual_near_progress A hq hceil hnear
    · exact (not_lt_of_ge ht hw).elim
    · obtain ⟨e,hm,hL,ha,hb,_⟩ := hp
      exact (hn ⟨hw,e,hm,hL,ha,hb⟩).elim
    · simp only [BranchState.finish] at he
      cases hnext with
      | near _ hs =>
        simp only [BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at hs
        rw [he.2] at hs
        exact (Nat.lt_irrefl _ hs).elim
      | far _ hs _ =>
        simp only [BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at hs
        rw [he.2] at hs
        exact (Nat.lt_irrefl _ hs).elim
      | direct _ _ => rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem branchCount_card (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) :
    branchCount label n kind = ((Finset.range n).filter fun j => label j = kind).card := by
  simp [branchCount]

theorem branchCount_succ (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) :
    branchCount label (n+1) kind = branchCount label n kind + if label n = kind then 1 else 0 := by
  simp only [branchCount,Finset.sum_range_succ]

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

theorem nested (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    MonotoneOn (fun j => (b.state j).start) (Set.Icc 0 n) ∧
    AntitoneOn (fun j => (b.state j).finish) (Set.Icc 0 n) := by
  have hpair : ∀ j k, j ≤ k → k ≤ n →
      (b.state j).start ≤ (b.state k).start ∧ (b.state k).finish ≤ (b.state j).finish := by
    intro j k hjk hkn
    induction k, hjk using Nat.le_induction with
    | base => exact ⟨le_rfl,le_rfl⟩
    | succ k hjk ih =>
      have hp := ih (by omega)
      have hs := (b.step k (by omega)).nested hq (b.valid k (by omega))
      exact ⟨hp.1.trans hs.1,hs.2.trans hp.2⟩
  exact ⟨fun _ _ _ hk hjk => (hpair _ _ hjk hk.2).1,
    fun _ _ _ hk hjk => (hpair _ _ hjk hk.2).2⟩

theorem charges_card (b : PolicyBranch A N q sig n) :
    b.charges.card = branchCount b.label n .high + branchCount b.label n .direct + b.chargedNear.card := by
  classical
  simp only [charges,chargedNear,Finset.card_filter,branchCount,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases b.label j <;> simp

theorem charges_have_representatives (b : PolicyBranch A N q sig n) (hq : 0 < q)
    {j : ℕ} (hj : j ∈ b.charges) :
    ∃ p ∈ policyRepresentatives A N q, (b.state j).start < p ∧ p ≤ (b.state (j+1)).start := by
  classical
  obtain ⟨hj,hlabel⟩ := Finset.mem_filter.mp hj
  have hjn := Finset.mem_range.mp hj
  rcases hlabel with hh | hd | ⟨hn,he⟩
  · have hg := (b.step j hjn).graph_charge hq (b.valid j hjn.le) (Or.inl hh)
    exact ⟨_,hg.2,hg.1,le_rfl⟩
  · have hg := (b.step j hjn).graph_charge hq (b.valid j hjn.le) (Or.inr hd)
    exact ⟨_,hg.2,hg.1,le_rfl⟩
  · obtain ⟨_,e,he,_,ha,hp⟩ := he
    have hr : descriptorAnchor e ∈ policyRepresentatives A N q := by
      cases hs : b.state j <;> rw [hs] at he
      · exact policyDescriptor_anchor_mem A hq he
      · exact policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp he).1
    exact ⟨descriptorAnchor e,hr,ha,hp⟩

theorem representative_counts (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    branchCount b.label n .high + branchCount b.label n .direct + b.chargedNear.card ≤
        (policyRepresentatives A N q).card ∧
      (policyRepresentatives A N q).card ≤ N/q+1 := by
  classical
  let charge := fun j => if hj : j ∈ b.charges then
    Classical.choose (b.charges_have_representatives hq hj) else 0
  have hspec (j : ℕ) (hj : j ∈ b.charges) :
      charge j ∈ policyRepresentatives A N q ∧
      (b.state j).start < charge j ∧ charge j ≤ (b.state (j+1)).start := by
    simpa only [charge,dite_eq_left hj] using Classical.choose_spec (b.charges_have_representatives hq hj)
  have hb := branch_representative_charges_bound A N q n (fun j => (b.state j).start)
    charge b.charges (Finset.filter_subset _ _) (b.nested hq).1
    (fun j hj => (hspec j hj).2) (fun j hj => (hspec j hj).1)
  exact ⟨by rw [← b.charges_card]; exact hb.1,policy_representatives_card A N q⟩

theorem near_count (b : PolicyBranch A N q sig n) (hq : 0 < q)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q) :
    branchCount b.label n .near ≤ b.chargedNear.card + branchCount b.label n .direct + 1 := by
  classical
  let U := (Finset.range n).filter fun j => b.label j = .near ∧
    ¬ ChargedNear A N q (b.state j) (b.state (j+1))
  have hpartition : branchCount b.label n .near = b.chargedNear.card+U.card := by
    simp only [chargedNear,U,Finset.card_filter,branchCount,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hl : b.label j = .near <;>
      by_cases hc : ChargedNear A N q (b.state j) (b.state (j+1)) <;> simp [hl,hc]
  have hu : U.card ≤ branchCount b.label n .direct+1 := by
    rw [branchCount_card]
    let D := ((Finset.range n).filter fun j => b.label j = .direct)
    have hmap : U.image Nat.succ ⊆ insert n D := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hjn,hn,hc⟩ := Finset.mem_filter.mp hj
      have hjn := Finset.mem_range.mp hjn
      by_cases he : j+1 = n
      · exact Finset.mem_insert.mpr (Or.inl he)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        have hnext := near_uncharged_next_direct hq hceil
          (by simpa only [hn] using b.step j hjn) hc (b.step (j+1) (by omega))
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hnext⟩
    calc
      U.card = (U.image Nat.succ).card := (Finset.card_image_of_injective _ Nat.succ_injective).symm
      _ ≤ (insert n D).card := Finset.card_le_card hmap
      _ ≤ D.card+1 := Finset.card_insert_le _ _
  omega

theorem episode_identity (b : PolicyBranch A N q sig n) :
    (b.state n).angular + branchCount b.label n .far =
      (b.state 0).angular + branchCount b.label n .high := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    have hs := (b.step n (by omega)).episode_balance
    dsimp only [initialSegment] at hp
    rw [branchCount_succ,branchCount_succ]
    omega

theorem far_count (b : PolicyBranch A N q sig n) :
    branchCount b.label n .far ≤ branchCount b.label n .high+1 := by
  have hi := b.episode_identity
  have hzero : (b.state 0).angular ≤ 1 := by cases b.state 0 <;> simp [BranchState.angular]
  omega

theorem suffix_total_decrease (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    (b.state n).finish + branchCount b.label n .suffix*q ≤ (b.state 0).finish := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).nested hq (b.valid n (by omega))
    rw [branchCount_succ,Nat.add_mul]
    by_cases hl : b.label n = .suffix
    · have hd := BranchStep.suffix_decrease (by simpa only [hl] using b.step n (by omega)) hq
        (b.valid n (by omega))
      simp only [hl,ite_true,one_mul]
      omega
    · simp only [hl,ite_false,zero_mul]
      omega

theorem low_total_decrease (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    ((b.state n).finish:ℝ) + (branchCount b.label n .low:ℝ)*(sig*N) ≤ (b.state 0).finish := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).nested hq (b.valid n (by omega))
    have hsR : ((b.state (n+1)).finish:ℝ) ≤ (b.state n).finish := Nat.cast_le.mpr hs.2
    rw [branchCount_succ]
    by_cases hl : b.label n = .low
    · have hd := BranchStep.low_decrease (by simpa only [hl] using b.step n (by omega))
      simp only [hl,ite_true,Nat.cast_add,Nat.cast_one]
      nlinarith
    · simp only [hl,ite_false,add_zero]
      linarith

theorem index_identity (b : PolicyBranch A N q sig n) :
    (b.state n).index = (b.state 0).index + branchCount b.label n .suffix +
      branchCount b.label n .low + branchCount b.label n .far := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).index_change
    rw [branchCount_succ,branchCount_succ,branchCount_succ,hs,hp]
    cases b.label n <;> simp <;> omega

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem high_depth_gap {N q t v : ℕ} {sig : ℝ} (hv : v ≤ t)
    (hgap : (t:ℝ)-v < sig*N) (hslack : sig*(N:ℝ) ≤ q) : t-v ≤ q := by
  have hcast : ((t-v:ℕ):ℝ) = (t:ℝ)-v := Nat.cast_sub hv
  exact Nat.cast_le.mp (by rw [hcast]; exact hgap.le.trans hslack)

theorem BranchStep.valid_successor {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hq : 0 < q) (hslack : sig*(N:ℝ) ≤ q)
    (hbuffer : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+5 < t)
    {s u : BranchState} {label : BranchLabel}
    (h : BranchStep A N q sig s label u) (hv : s.Valid N sig) : u.Valid N sig := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    dsimp only [BranchState.Valid] at *
    omega
  | low _ hm _ =>
    have hm := Finset.mem_Ioc.mp hm
    dsimp only [BranchState.Valid] at *
    omega
  | high hw hs hm hg =>
    have hm := Finset.mem_Ioc.mp hm
    have hgap := high_depth_gap hm.2 hg hslack
    have hp := actual_prefix_policy_payment A hq hv.2 hw hs hm.2 hgap
    have hi := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    exact ⟨by omega,by omega,hm.2,hv.2,by linarith⟩
  | near _ hs =>
    dsimp only [BranchState.Valid,BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at *
    exact ⟨by omega,Nat.sub_le _ _,hv.2.2⟩
  | far _ hs hm =>
    have hb := hbuffer _ _ _ hs
    have hm := Finset.mem_Icc.mp hm
    dsimp only [BranchState.Valid,BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at *
    exact ⟨by omega,by omega⟩
  | direct _ hw =>
    exact ⟨hv.1.trans hw.anchor_gt.le,hw.anchor_lt.le,hv.2.2⟩

theorem uniform_branch_successor_validity {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      ∀ s u : BranchState, ∀ label : BranchLabel,
      s.Valid N sig → BranchStep A N (sourcePolicyBlock N kap) sig s label u →
      u.Valid N sig ∧ s.start ≤ u.start ∧ u.finish ≤ s.finish := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,h₂⟩ := uniform_source_far_buffer hsig
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A s u label hv h
  have hq := sourcePolicyBlock_pos (by omega : 0 < N) hkap
  have hb : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+5 < t := by
    intro L t a ha
    have hh := h₂ N (by omega) L t a ha
    omega
  exact ⟨h.valid_successor hq (h₁ N (by omega)).2.2 hb hv,h.nested hq hv⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem BranchStep.paid_width {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hc : label = .suffix ∨ label = .high ∨ label = .direct) : u.start+10*q ≤ u.finish := by
  cases h with
  | suffix hw hs => exact (actual_suffix_policy_payment A hq hv.2 hw hs).1
  | high hw hs hm hg =>
    have hm := Finset.mem_Ioc.mp hm
    exact (actual_prefix_policy_payment A hq hv.2 hw hs hm.2 (high_depth_gap hm.2 hg hslack)).1
  | direct _ he => exact he.width
  | _ => simp at hc

theorem BranchStep.potential_payment {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hu : u.start+10*q ≤ u.finish) :
    potential A s.start s.finish (10*q)+branchCost A s label u ≤
      potential A u.start u.finish (10*q) := by
  have hn := h.nested hq hv
  have hm := potential_mono A (by omega : 0 < 10*q) hu hn.1 hn.2
  cases h with
  | suffix hw hs => exact (actual_suffix_policy_payment A hq hv.2 hw hs).2
  | high hw hs hmem hg =>
    have hmem := Finset.mem_Ioc.mp hmem
    exact (actual_prefix_policy_payment A hq hv.2 hw hs hmem.2 (high_depth_gap hmem.2 hg hslack)).2
  | direct _ he => exact he.payment
  | _ => simpa only [branchCost,add_zero] using hm

theorem BranchStep.short_cost_zero {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hu : u.finish < u.start+10*q) : branchCost A s label u = 0 := by
  have hc : ¬ (label = .suffix ∨ label = .high ∨ label = .direct) := by
    intro hl
    exact (not_le_of_gt hu) (h.paid_width hq hv hslack hl)
  cases label <;> simp_all [branchCost]

theorem potential_le_final_start {A : ℕ → ℝ} {N a t f Q : ℕ}
    (hN : 0 < N) (hA : DiscreteProfileLipschitz A N)
    (hQ : 0 < Q) (hw : a+Q ≤ t) (ht : t ≤ N) (haf : a ≤ f) (hft : f ≤ t) :
    potential A a t Q ≤ 2*A f+2*(Q:ℝ)/N := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hb := potential_near_final A hQ hw haf hft (e := (Q:ℝ)/N) ?_
  · simpa only [mul_div_assoc] using hb
  intro j _ hjt hjf hfj
  have hd : |(j:ℝ)-f| ≤ (Q:ℝ) := by
    have hjR : (j:ℝ) ≤ (f:ℝ)+Q := by exact_mod_cast hjf
    have hfR : (f:ℝ) ≤ (j:ℝ)+Q := by exact_mod_cast hfj
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (hA j (hjt.trans ht) f (hft.trans ht)).trans (div_le_div_of_nonneg_right hd hNR.le)
  have hh' := (le_abs_self (A j-A f)).trans hh
  linarith

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

theorem costs_le_potential (b : PolicyBranch A N q sig n) (hq : 0 < q)
    (hslack : sig*(N:ℝ) ≤ q) (hfinal : (b.state n).start+10*q ≤ (b.state n).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      potential A (b.state n).start (b.state n).finish (10*q)-
        potential A (b.state 0).start (b.state 0).finish (10*q) := by
  apply branch_cost_bound (fun j => potential A (b.state j).start (b.state j).finish (10*q))
    (fun j => branchCost A (b.state j) (b.label j) (b.state (j+1))) n
  intro j hj
  apply (b.step j hj).potential_payment hq (b.valid j hj.le) hslack
  by_cases he : j+1 = n
  · simpa only [he] using hfinal
  · have hw := (b.step (j+1) (by omega)).nonterminal
    omega

theorem costs_le_final_start (b : PolicyBranch A N q sig n) (hN : 0 < N) (hq : 0 < q)
    (hslack : sig*(N:ℝ) ≤ q) (hA : DiscreteProfileLipschitz A N)
    (hinit : (b.state 0).start+10*q ≤ (b.state 0).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      2*A (b.state n).start+20*(q:ℝ)/N-potential A (b.state 0).start (b.state 0).finish (10*q) := by
  have hQ : 0 < 10*q := by omega
  have hfinal := BranchState.valid_depths (b.valid n le_rfl)
  by_cases hw : (b.state n).start+10*q ≤ (b.state n).finish
  · have hc := b.costs_le_potential hq hslack hw
    have hf := potential_le_final_start hN hA hQ hw hfinal.2 (le_refl _) hfinal.1
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
    linear_combination hc+hf
  · cases n with
    | zero => exact (hw hinit).elim
    | succ n =>
      have hs := b.step n (by omega)
      have hn := hs.nested hq (b.valid n (by omega))
      have hp := hs.nonterminal
      have hpwide : (b.state n).start+10*q ≤ (b.state n).finish := by omega
      have hd := BranchState.valid_depths (b.valid n (by omega))
      have hc := (b.initialSegment n (by omega)).costs_le_potential hq hslack hpwide
      dsimp only [initialSegment] at hc
      have hz := hs.short_cost_zero hq (b.valid n (by omega)) hslack (by omega)
      have hf := potential_le_final_start hN hA hQ hpwide hd.2 hn.1 (hfinal.1.trans hn.2)
      norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
      rw [Finset.sum_range_succ,hz,add_zero]
      linear_combination hc+hf

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SourceBranchDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem branch_count_total (label : ℕ → BranchLabel) (n : ℕ) :
    branchNonlowCount label n + branchCount label n .low = n := by
  induction n with
  | zero => simp [branchNonlowCount,branchCount]
  | succ n ih =>
    simp only [branchNonlowCount] at *
    simp only [branchCount_succ]
    cases h : label n <;> simp <;> omega

theorem source_branch_count_bounds {A : ℕ → ℝ} {N n : ℕ} {sig kap : ℝ}
    (hN : 0 < N) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n) :
    (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
      (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig := by
  have hq := sourcePolicyBlock_pos hN hkap
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hstart := BranchState.valid_depths (b.valid 0 (Nat.zero_le _))
  have hS := b.suffix_total_decrease hq
  have hSR : (branchCount b.label n .suffix:ℝ)*(sourcePolicyBlock N kap:ℝ) ≤ N := by
    exact_mod_cast (show branchCount b.label n .suffix*sourcePolicyBlock N kap ≤ N by omega)
  have hblock := source_policy_block_lower N kap
  have hSb := mul_le_mul_of_nonneg_left hblock (Nat.cast_nonneg (branchCount b.label n .suffix))
  have hSbound : (branchCount b.label n .suffix:ℝ) ≤ 1/kap := by
    apply (le_div_iff₀ hkap).mpr
    apply (mul_le_mul_iff_left₀ hNR).mp
    nlinarith [hSb.trans hSR]
  have hL := b.low_total_decrease hq
  have hLR : ((b.state 0).finish:ℝ) ≤ N := Nat.cast_le.mpr hstart.2
  have hLbound : (branchCount b.label n .low:ℝ) ≤ 1/sig := by
    apply (le_div_iff₀ hsig).mpr
    apply (mul_le_mul_iff_left₀ hNR).mp
    nlinarith [show (0:ℝ) ≤ (b.state n).finish from Nat.cast_nonneg _]
  have hG := (b.representative_counts hq).1
  have hK := b.near_count hq hceil
  have hF := b.far_count
  have hB := source_representatives_real_bound A hN hkap hkap1
  have hnonlow : branchNonlowCount b.label n ≤
      2*(policyRepresentatives A N (sourcePolicyBlock N kap)).card + branchCount b.label n .suffix+2 := by
    dsimp only [branchNonlowCount]
    omega
  have hnonlowR : (branchNonlowCount b.label n:ℝ) ≤
      2*((policyRepresentatives A N (sourcePolicyBlock N kap)).card:ℝ) +
        (branchCount b.label n .suffix:ℝ)+2 := by exact_mod_cast hnonlow
  have hone : 1 ≤ 1/kap := (le_div_iff₀ hkap).mpr (by simpa using hkap1)
  have hbound : (branchNonlowCount b.label n:ℝ) ≤ 20/kap := by
    have he : 20/kap = 20*(1/kap) := by ring
    have he2 : 2/kap = 2*(1/kap) := by ring
    rw [he2] at hB
    rw [he]
    linarith
  refine ⟨hbound,hLbound,?_⟩
  have ht : (branchNonlowCount b.label n:ℝ)+(branchCount b.label n .low:ℝ) = n := by
    exact_mod_cast branch_count_total b.label n
  linarith

theorem source_smoothing_reserve {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    1+20/kap+1/sig < (sourceSmoothingLevels sig kap:ℝ) := by
  have hceil : 100*(1/sig+1/kap)+100 ≤ (sourceSmoothingLevels sig kap:ℝ) := Nat.le_ceil _
  have he : 20/kap = 20*(1/kap) := by ring
  rw [he]
  have hk : 0 < 1/kap := by positivity
  have hs : 0 < 1/sig := by positivity
  linarith

theorem source_branch_index_bound {A : ℕ → ℝ} {N n : ℕ} {sig kap : ℝ}
    (hN : 0 < N) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n) (hi : (b.state 0).index = 0)
    {j : ℕ} (hj : j ≤ n) :
    ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig ∧ (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  let c := b.initialSegment j hj
  have hc := source_branch_count_bounds hN hsig hkap hkap1 hceil c
  have hind := c.index_identity
  change (b.state j).index = (b.state 0).index + branchCount b.label j .suffix +
    branchCount b.label j .low + branchCount b.label j .far at hind
  rw [hi] at hind
  have hn : (b.state j).index ≤ branchNonlowCount b.label j + branchCount b.label j .low := by
    dsimp only [branchNonlowCount]
    omega
  have hnR : ((b.state j).index:ℝ) ≤ (branchNonlowCount b.label j:ℝ)+(branchCount b.label j .low:ℝ) := by
    exact_mod_cast hn
  change (branchNonlowCount b.label j:ℝ) ≤ _ ∧ (branchCount b.label j .low:ℝ) ≤ _ ∧ _ at hc
  have hb : ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig := by linarith [hc.1,hc.2.1]
  refine ⟨hb,?_⟩
  have hh := hb.trans_lt (source_smoothing_reserve hsig hkap)
  exact_mod_cast hh

theorem uniform_source_branch_depth {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ, ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
      (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig ∧
      ∀ j ≤ n, ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig ∧
        (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_ceiling_slack hsig hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A n b hi
  have hNp : 0 < N := hN₀.trans_le hN
  have hc := source_branch_count_bounds hNp hsig hkap hkap1 (h₀ N hN).1 b
  exact ⟨hc.1,hc.2.1,hc.2.2,fun j hj => source_branch_index_bound
    hNp hsig hkap hkap1 (h₀ N hN).1 b hi hj⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchExponentAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem branch_nonlow_indicator_sum (label : ℕ → BranchLabel) (n : ℕ) :
    (∑ j ∈ Finset.range n, if label j = .low then 0 else 1) = branchNonlowCount label n := by
  have htot := branch_count_total label n
  have hsum : branchCount label n .low +
      (∑ j ∈ Finset.range n, if label j = .low then 0 else 1) = n := by
    simp only [branchCount,← Finset.sum_add_distrib]
    calc
      _ = ∑ _j ∈ Finset.range n, (1:ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : label j = .low <;> simp [hj]
      _ = n := by simp
  omega

theorem branch_nonlow_loss_sum (label : ℕ → BranchLabel) (n : ℕ) (loss : ℝ) :
    (∑ j ∈ Finset.range n, if label j = .low then 0 else loss) =
      (branchNonlowCount label n:ℝ)*loss := by
  have hcast := congrArg (fun k : ℕ => (k:ℝ)) (branch_nonlow_indicator_sum label n)
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] at hcast
  calc
    _ = ∑ j ∈ Finset.range n, (if label j = .low then (0:ℝ) else 1)*loss := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : label j = .low <;> simp [hj]
    _ = _ := by rw [← Finset.sum_mul,hcast]

theorem branch_exponent_sum (A : ℕ → ℝ) (lam sig eps : ℝ)
    (state : ℕ → BranchState) (label : ℕ → BranchLabel) (n : ℕ) :
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (state j) (label j) (state (j+1))) =
      2*A (state 0).start-2*A (state n).start+
      (∑ j ∈ Finset.range n, branchCost A (state j) (label j) (state (j+1)))+
      (branchNonlowCount label n:ℝ)*(4000*(lam+sig))+(n:ℝ)*eps := by
  simp only [branchExponent,Finset.sum_add_distrib]
  rw [profile_increments_telescope A (fun j => (state j).start) n,branch_nonlow_loss_sum]
  simp

theorem source_branch_exponent {A : ℕ → ℝ} {N n : ℕ} {lam sig kap eta : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (heta : 0 < eta) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (hslack : sig*(N:ℝ) ≤ sourcePolicyBlock N kap)
    (hqratio : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap)
    (hA : DiscreteProfileLipschitz A N)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n)
    (hinit : (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish) :
    let eps := eta/(2*(1+20/kap+1/sig))
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) +
      (200*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*kap+10^6*(lam+sig)/kap+eta := by
  dsimp only
  have hq := sourcePolicyBlock_pos hN hkap
  have hc := b.costs_le_final_start hN hq hslack hA hinit
  have hb := source_branch_count_bounds hN hsig hkap hkap1 hceil b
  let D : ℝ := 1+20/kap+1/sig
  have hD : 0 < D := by dsimp [D]; positivity
  have heps : 0 ≤ eta/(2*D) := by positivity
  have htime : (n:ℝ)*(eta/(2*D)) ≤ eta/2 := by
    have hn : (n:ℝ) ≤ D := by dsimp [D]; linarith [hb.2.2]
    calc
      _ ≤ D*(eta/(2*D)) := mul_le_mul_of_nonneg_right hn heps
      _ = eta/2 := by field_simp
  have hloss : (branchNonlowCount b.label n:ℝ)*(4000*(lam+sig)) ≤ 80000*(lam+sig)/kap := by
    calc
      _ ≤ (20/kap)*(4000*(lam+sig)) := mul_le_mul_of_nonneg_right hb.1 (by positivity)
      _ = _ := by ring
  have hlamK : lam ≤ (lam+sig)/kap := by
    apply (le_div_iff₀ hkap).mpr
    have hh := mul_le_mul_of_nonneg_left hkap1 hlam
    linarith
  have hbudget : 0 ≤ (lam+sig)/kap := by positivity
  rw [branch_exponent_sum]
  dsimp only [D] at htime
  simp only [mul_div_assoc] at hc hloss ⊢
  nlinarith

theorem uniform_source_branch_exponent {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DiscreteProfileLipschitz A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      (∑ j ∈ Finset.range n, branchExponent A lam sig (eta/(2*(1+20/kap+1/sig)))
        (b.state j) (b.label j) (b.state (j+1))) +
        (200*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*kap+10^6*(lam+sig)/kap+eta := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (1/kap)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := by omega
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hNp
  have hkn : 1 < kap*(N:ℝ) := by
    have hh := (div_lt_iff₀ hkap).mp (hN₂.trans_le (Nat.cast_le.mpr (show N₂ ≤ N by omega)))
    linarith
  have hq : (sourcePolicyBlock N kap:ℝ) < kap*N+1 :=
    Nat.ceil_lt_add_one (mul_nonneg hkap.le hNR.le)
  have hqr : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap :=
    (div_le_iff₀ hNR).mpr (by linarith)
  exact source_branch_exponent hNp hlam hsig hkap hkap1 heta
    (h₁ N (by omega)).1 (h₁ N (by omega)).2.2 hqr hA b hi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchExponent
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem RegularizedProfileData.discrete_lipschitz {Q : DyadicSquare}
    {ρ : MeasureTheory.Measure Plane} {N B : ℕ} {δ lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N B δ lam m) :
    DiscreteProfileLipschitz (fun n => m n-(n:ℝ)/N) N := by
  intro i hi j hj
  exact h.adjusted j i (Nat.cast_nonneg _) (Nat.cast_le.mpr hj)
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hi)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchRecursionOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem BranchStep.width_decreases {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) :
    u.finish-u.start < s.finish-s.start := by
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  have hstrict : s.start < u.start ∨ u.finish < s.finish := by
    cases h with
    | suffix hw _ =>
      have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hs.2 hw)
      exact Or.inr (by dsimp only [BranchState.finish]; omega)
    | low _ _ hg =>
      have hpos : 0 < sig*(N:ℝ) := mul_pos hsig (Nat.cast_pos.mpr hN)
      apply Or.inr
      apply (Nat.cast_lt (α := ℝ)).mp
      dsimp only [BranchState.finish]
      linarith
    | high hw _ _ _ =>
      have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hs.2 hw)
      exact Or.inl (by dsimp only [BranchState.start]; omega)
    | near _ hp => exact Or.inl hp
    | far _ _ hm =>
      have hm := Finset.mem_Icc.mp hm
      exact Or.inl (by dsimp only [BranchState.start]; omega)
    | direct _ he => exact Or.inl he.anchor_gt
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ReachedStateRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

@[simp] theorem extend_last_state (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).state (n+1) = u := ite_eq_right (by omega)

@[simp] theorem extend_last_label (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).label n = l := ite_eq_right (Nat.lt_irrefl n)

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchErrorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem DiscreteProfileLipschitz.increment_le_one {A : ℕ → ℝ} {N i j : ℕ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hi : i ≤ N) (hj : j ≤ N) :
    |A i-A j| ≤ 1 := by
  apply (hA i hi j hj).trans
  apply (div_le_one (Nat.cast_pos.mpr hN)).mpr
  apply abs_le.mpr
  have hi' : (i:ℝ) ≤ N := Nat.cast_le.mpr hi
  have hj' : (j:ℝ) ≤ N := Nat.cast_le.mpr hj
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i,Nat.cast_nonneg (α := ℝ) j]

theorem DiscreteProfileLipschitz.abs_le_one {A : ℕ → ℝ} {N i : ℕ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hzero : A 0 = 0) (hi : i ≤ N) :
    |A i| ≤ 1 := by
  simpa only [hzero,sub_zero] using hA.increment_le_one hN hi (Nat.zero_le N)

theorem DiscreteProfileLipschitz.minimum_cost_le_one {A : ℕ → ℝ} {N a t i : ℕ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N)
    (hat : a ≤ t) (ht : t ≤ N) (hi : i ≤ N) :
    A i-intervalMin A a t ≤ 1 := by
  obtain ⟨j,_,hjt,hmin⟩ := intervalMin_attained A hat
  rw [hmin]
  exact (le_abs_self _).trans (hA.increment_le_one hN hi (hjt.trans ht))

theorem BranchStep.cost_le_one {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hq : 0 < q)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) : branchCost A s l u ≤ 1 := by
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  cases h <;> simp only [branchCost]
  · exact hA.minimum_cost_le_one hN hn.2 hsd.2 (hud.2.trans (le_refl _))
  · norm_num
  · exact hA.minimum_cost_le_one hN hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)
  · norm_num
  · norm_num
  · exact hA.minimum_cost_le_one hN hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)

theorem BranchStep.exponent_le_four {A : ℕ → ℝ} {N q : ℕ} {lam sig eps : ℝ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hq : 0 < q)
    (hloss : 4000*(lam+sig) ≤ 1)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) :
    branchExponent A lam sig eps s l u ≤ 4+eps := by
  have hc := h.cost_le_one hA hN hq hs hu
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  have hi := abs_le.mp (hA.increment_le_one hN (hud.1.trans hud.2) (hsd.1.trans hsd.2))
  unfold branchExponent
  split_ifs <;> linarith

theorem PolicyBranch.ancestor_exponent_bound {A : ℕ → ℝ} {N q n : ℕ} {lam sig eps : ℝ}
    (b : PolicyBranch A N q sig n) (hA : DiscreteProfileLipschitz A N)
    (hN : 0 < N) (hq : 0 < q) (hloss : 4000*(lam+sig) ≤ 1) :
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) ≤
      (n:ℝ)*(4+eps) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (4+eps) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj := Finset.mem_range.mp hj
      exact (b.step j hj).exponent_le_four hA hN hq hloss (b.valid j hj.le)
        (b.valid (j+1) (by omega))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem source_error_exponent {sig kap T eps n : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hn : 0 ≤ n)
    (hdepth : n ≤ 20/kap+1/sig) (heps : eps ≤ 1)
    (hT : 1000*(1/sig+1/kap)+1000 < T) : -T+n*(4+eps) < -10 := by
  have hstep : n*(4+eps) ≤ 5*n := by nlinarith
  have hk : 0 < 1/kap := by positivity
  have hs : 0 < 1/sig := by positivity
  have he : 20/kap = 20*(1/kap) := by ring
  rw [he] at hdepth
  linarith

theorem uniform_source_error_branch {lam sig kap T eps : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : 1000*(1/sig+1/kap)+1000 < T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DiscreteProfileLipschitz A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      ((2:ℝ)^N)^(-T+(∑ j ∈ Finset.range n,
        branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1)))) ≤
      ((2:ℝ)^N)^(-10:ℝ) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_branch_depth hsig hkap hkap1 hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := hN₀.trans_le hN
  have hc := b.ancestor_exponent_bound (eps := eps) hA hNp (sourcePolicyBlock_pos hNp hkap) hloss
  have hd := (h₀ N hN A n b hi).2.2.1
  have he := source_error_exponent hsig hkap (Nat.cast_nonneg n) hd heps hT
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  linarith

theorem source_profile_exponent_lower {A : ℕ → ℝ} {N a t Q : ℕ}
    (hA : DiscreteProfileLipschitz A N) (hN : 0 < N) (hzero : A 0 = 0)
    (hQ : 0 < Q) (hw : a+Q ≤ t) (ht : t ≤ N) :
    -4 ≤ 2*A a-potential A a t Q := by
  have ha := abs_le.mp (hA.abs_le_one hN hzero (show a ≤ N by omega))
  have hb := abs_le.mp (hA.abs_le_one hN hzero (show a+Q ≤ N by omega))
  have hp := potential_le A (Q := Q) (le_refl a) (by omega : a < a+Q) hw (le_refl _)
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ReachedBranchWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

theorem weight_pos (b : PolicyBranch A N q sig n) (lam eps : ℝ) : 0 < b.weight lam eps := by
  unfold weight
  positivity

theorem exponentSum_extend (b : PolicyBranch A N q sig n) (lam eps : ℝ)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).exponentSum lam eps = b.exponentSum lam eps+
      branchExponent A lam sig eps (b.state n) l u := by
  unfold exponentSum
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_range.mp hj
    rw [b.extend_state_le hu hstep hj.le,b.extend_label_lt hu hstep hj,
      b.extend_state_le hu hstep (by omega : j+1 ≤ n)]
  · rw [b.extend_state_le hu hstep le_rfl,b.extend_last_label,b.extend_last_state]

theorem weight_extend (b : PolicyBranch A N q sig n) (lam eps : ℝ)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).weight lam eps = b.weight lam eps*
      ((2:ℝ)^N)^(branchExponent A lam sig eps (b.state n) l u) := by
  unfold weight
  rw [exponentSum_extend,Real.rpow_add (by positivity)]

theorem weight_zero (b : PolicyBranch A N q sig 0) (lam eps : ℝ) : b.weight lam eps = 1 := by
  simp [weight,exponentSum]

end PolicyBranch

theorem uniform_source_weighted_terminal {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DiscreteProfileLipschitz A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      b.weight lam (eta/(2*(1+20/kap+1/sig))) *
        ((2:ℝ)^N)^(200*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      ((2:ℝ)^N)^(2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*kap+10^6*(lam+sig)/kap+eta) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_branch_exponent hlam hsig hkap hkap1 hgap heta
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (h₀ N hN A hA n b hi)

theorem uniform_source_weighted_error {lam sig kap T eps : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : 1000*(1/sig+1/kap)+1000 < T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DiscreteProfileLipschitz A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      b.weight lam eps*((2:ℝ)^N)^(-T) ≤ ((2:ℝ)^N)^(-10:ℝ) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_error_branch hsig hkap hkap1 hgap hloss heps hT
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N),add_comm]
  exact h₀ N hN A hA n b hi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_WeightedBranchInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem weighted_branch_energy_induction (A : ℕ → ℝ) (N q D : ℕ)
    (sig lam eps C terminal floor error L E : ℝ) (root : BranchState)
    (energies : BranchState → ℝ → Prop)
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    (hC : 1 ≤ C) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hvalid : ∀ s u l, s.Valid N sig → BranchStep A N q sig s l u → u.Valid N sig)
    (hdepth : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root → n ≤ D)
    (hterminal : ∀ s, s.Valid N sig → s.finish ≤ s.start+100*q →
      ∀ x, energies s x → x ≤ terminal)
    (hreduction : ∀ s, s.Valid N sig →
      (∃ n, ∃ b : PolicyBranch A N q sig n, b.state 0 = root ∧ b.state n = s) →
      s.start+100*q < s.finish →
      ∀ M : ℝ, 0 ≤ M → floor ≤ M →
      (∀ u l, BranchStep A N q sig s l u → ∀ x, energies u x →
        ((2:ℝ)^N)^(branchExponent A lam sig eps s l u)*x ≤ M) →
      ∀ x, energies s x → x ≤ C*M+error)
    (htermWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*terminal ≤ L)
    (hfloorWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*floor ≤ L)
    (herrorWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*error ≤ E) :
    ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      ∀ x, energies (b.state n) x →
      b.weight lam eps*x ≤ (C+1)^(D-n+1)*(L+E) := by
  have haux : ∀ s : BranchState, ∀ n, ∀ b : PolicyBranch A N q sig n,
      b.state 0 = root → b.state n = s → ∀ x, energies s x →
      b.weight lam eps*x ≤ (C+1)^(D-n+1)*(L+E) := by
    intro s
    induction s using (measure (fun s : BranchState => s.finish-s.start)).wf.induction with
    | h s ih =>
      intro n b hroot hlast x hx
      have hs : s.Valid N sig := hlast ▸ b.valid n le_rfl
      have hW := b.weight_pos lam eps
      have hsum : 0 ≤ L+E := add_nonneg hL hE
      have hpow : 1 ≤ (C+1)^(D-n) := one_le_pow₀ (by linarith)
      let H := (C+1)^(D-n)*(L+E)
      have hLH : L ≤ H := by dsimp only [H]; nlinarith
      have hEH : E ≤ H := by dsimp only [H]; nlinarith
      have hH : 0 ≤ H := hL.trans hLH
      have hHlast : H ≤ (C+1)^(D-n+1)*(L+E) := by
        rw [pow_succ]
        change H ≤ (C+1)^(D-n)*(C+1)*(L+E)
        nlinarith
      by_cases hw : s.finish ≤ s.start+100*q
      · have ht := hterminal s hs hw x hx
        exact ((mul_le_mul_of_nonneg_left ht hW.le).trans (htermWeight n b hroot)).trans
          (hLH.trans hHlast)
      · have hfloor : floor ≤ H/b.weight lam eps := by
          apply (le_div_iff₀ hW).mpr
          simpa only [mul_comm] using (hfloorWeight n b hroot).trans hLH
        have hchildren : ∀ u l, BranchStep A N q sig s l u → ∀ y, energies u y →
            ((2:ℝ)^N)^(branchExponent A lam sig eps s l u)*y ≤ H/b.weight lam eps := by
          intro u l hstep y hy
          have hu := hvalid s u l hs hstep
          have hstep' : BranchStep A N q sig (b.state n) l u := hlast ▸ hstep
          let b' := b.extend hu hstep'
          have hroot' : b'.state 0 = root := by
            change (b.extend hu hstep').state 0 = root
            rw [b.extend_state_le hu hstep' (Nat.zero_le n),hroot]
          have hlast' : b'.state (n+1) = u := b.extend_last_state hu hstep'
          have hnd := hdepth (n+1) b' hroot'
          have hi := ih u (hstep.width_decreases hN hq hsig hs hu) (n+1) b' hroot' hlast' y hy
          have harith : D-(n+1)+1 = D-n := by omega
          rw [harith] at hi
          change b'.weight lam eps*y ≤ H at hi
          dsimp only [b'] at hi
          rw [b.weight_extend,hlast] at hi
          apply (le_div_iff₀ hW).mpr
          nlinarith only [hi]
        have hred := hreduction s hs ⟨n,b,hroot,hlast⟩ (by omega) (H/b.weight lam eps)
          (div_nonneg hH hW.le) hfloor hchildren x hx
        have hh := mul_le_mul_of_nonneg_left hred hW.le
        have herr := herrorWeight n b hroot
        have hid : b.weight lam eps*(C*(H/b.weight lam eps)+error) =
            C*H+b.weight lam eps*error := by field_simp
        rw [hid] at hh
        calc
          b.weight lam eps*x ≤ C*H+E := by linarith
          _ ≤ (C+1)*H := by linarith
          _ = (C+1)^(D-n+1)*(L+E) := by dsimp only [H]; rw [pow_succ]; ring
  intro n b hr x hx
  exact haux (b.state n) n b hr rfl x hx

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ActualRecursiveProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem RecursiveEnvironment.energies_mono (e : RecursiveEnvironment) {K L : ℕ}
    (hKL : K ≤ L) (Ψ : ℝ → ℝ) {s : BranchState} {x : ℝ}
    (hx : e.energies K Ψ s x) : e.energies L Ψ s x := by
  cases s with
  | D a t i => exact hx
  | H a₀ t₀ a v i =>
    obtain ⟨X,Y,hX,hY,k,hk,h,hh,hhb,hx⟩ := hx
    exact ⟨X,Y,hX,hY,k,fun l => (hk l).trans hKL,h,hh,hhb,hx⟩

theorem uniform_actual_profile_with_overhead {lam sig kap theta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
      e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
      e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
      ∀ root : BranchState, root.Valid e.N e.sig → root.index = 0 →
      root.start+10*e.q ≤ root.finish → ∀ x, e.energies K₀ Ψ root x →
      x ≤ ((e.N:ℝ)+4)^(⌈20/kap+1/sig⌉₊+1) *
        (((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
          +500*kap+10^6*(lam+sig)/kap+theta)+((2:ℝ)^e.N)^(-10:ℝ)) := by
  let Dstar : ℝ := 1+20/kap+1/sig
  have hDstar : 1 ≤ Dstar := by
    have hk : 0 ≤ 20/kap := by positivity
    have hs : 0 ≤ 1/sig := by positivity
    dsimp only [Dstar]
    linarith
  have hDpos : 0 < Dstar := by linarith
  let eps := theta/(2*Dstar)
  have heps : 0 < eps := div_pos htheta (by positivity)
  have hepstau : eps ≤ theta/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Dstar)).mpr
    nlinarith
  have heps1 : eps ≤ 1 := by linarith
  let T : ℝ := 1000*(1/sig+1/kap)+1001
  have hT : 0 < T := by dsimp [T]; positivity
  have hTlarge : 1000*(1/sig+1/kap)+1000 < T := by dsimp [T]; linarith
  obtain ⟨K,hK,N₁,hN₁,h₁⟩ := uniform_recursive_energy_rules hlam hsig hkap hgap heps
    (half_pos htheta) hT K₀ hΨ hpos hs hone
  obtain ⟨N₂,_,h₂⟩ := uniform_branch_successor_validity hsig hkap hgap
  obtain ⟨N₃,_,h₃⟩ := uniform_source_branch_depth hsig hkap hkap1 hgap
  obtain ⟨N₄,_,h₄⟩ := uniform_source_weighted_terminal hlam hsig hkap hkap1 hgap htheta
  obtain ⟨N₅,_,h₅⟩ := uniform_source_weighted_error hsig hkap hkap1 hgap hloss heps1 hTlarge
  refine ⟨max N₁ (max N₂ (max N₃ (max N₄ N₅))),by omega,?_⟩
  intro e hdlam hdsig hdq hdJ hN hQ hcarry B δ hprof root hroot hi hwide x hx
  have hNp : 0 < e.N := by omega
  have hqp := sourcePolicyBlock_pos hNp hkap
  have hA := hprof.discrete_lipschitz
  have hrules := h₁ e hdlam hdsig hdq hdJ (by omega) hQ hcarry B δ hprof
  let D : ℕ := ⌈20/kap+1/sig⌉₊
  let L := ((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
    +500*kap+10^6*(lam+sig)/kap+theta)
  let terminal := ((2:ℝ)^e.N)^(200*(e.q:ℝ)/e.N+12*lam+theta/2)
  let floor := ((2:ℝ)^e.N)^(12*lam+eps)
  have hfloor : floor ≤ terminal := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hnonneg : 0 ≤ 200*(e.q:ℝ)/e.N := by positivity
    linarith
  have hdepth : ∀ n, ∀ b : PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) sig n,
      b.state 0 = root → n ≤ D := by
    intro n b hb
    have hidx : (b.state 0).index = 0 := by rw [hb]; exact hi
    have hn := (h₃ e.N (by omega) e.profile n b hidx).2.2.1
    exact Nat.cast_le.mp (hn.trans (Nat.le_ceil _))
  have htermWeight : ∀ n, ∀ b : PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) sig n,
      b.state 0 = root → b.weight lam eps*terminal ≤ L := by
    intro n b hb
    have hw : (b.state 0).start+10*sourcePolicyBlock e.N kap ≤ (b.state 0).finish := by
      simpa only [hb,hdq] using hwide
    have hh := h₄ e.N (by omega) e.profile hA n b hw
    simpa only [hb,← hdq] using hh
  have hind := weighted_branch_energy_induction e.profile e.N (sourcePolicyBlock e.N kap) D
    sig lam eps ((e.N:ℝ)+3) terminal floor (((2:ℝ)^e.N)^(-T)) L (((2:ℝ)^e.N)^(-10:ℝ))
    root (e.energies K Ψ) hNp hqp hsig
    (by linarith [Nat.cast_nonneg (α := ℝ) e.N]) (by positivity) (by positivity)
    (fun s u l hv hstep => (h₂ e.N (by omega) e.profile s u l hv hstep).1)
    hdepth
    (by
      intro s hv ht y hy
      exact hrules.1 s (by simpa only [hdsig] using hv) (by simpa only [hdq] using ht) y hy)
    (by
      intro s hv hr hw M hM hfloorM hchildren y hy
      obtain ⟨n,b,hb,hbs⟩ := hr
      have hidx : (b.state 0).index = 0 := by rw [hb]; exact hi
      have hindex := ((h₃ e.N (by omega) e.profile n b hidx).2.2.2 n le_rfl).2
      rw [hbs,← hdJ] at hindex
      apply hrules.2 s (by simpa only [hdsig] using hv) hindex.le
        (by simpa only [hdq] using hw) M hM hfloorM _ y hy
      intro u l hstep z hz
      exact hchildren u l (by simpa only [hdq,hdsig] using hstep) z hz)
    htermWeight
    (fun n b hb => (mul_le_mul_of_nonneg_left hfloor (b.weight_pos lam eps).le).trans (htermWeight n b hb))
    (by
      intro n b hb
      have hidx : (b.state 0).index = 0 := by rw [hb]; exact hi
      exact h₅ e.N (by omega) e.profile hA n b hidx)
  let b : PolicyBranch e.profile e.N (sourcePolicyBlock e.N kap) sig 0 :=
    ⟨fun _ => root,fun _ => .low,fun _ _ => by simpa only [hdsig] using hroot,by omega⟩
  have hh := hind 0 b rfl x (e.energies_mono hK Ψ hx)
  simpa only [PolicyBranch.weight_zero,one_mul,Nat.sub_zero,show (e.N:ℝ)+3+1 = (e.N:ℝ)+4 by ring] using hh

theorem recursion_overhead_absorption (D : ℕ) {eta theta : ℝ}
    (heta : 0 < eta) (htheta : theta ≤ eta/4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g : ℝ, -4 ≤ g →
      ((N:ℝ)+4)^(D+1)*(((2:ℝ)^N)^g+((2:ℝ)^N)^(-10:ℝ)) ≤
        ((2:ℝ)^N)^(g+eta-theta) := by
  have he : 0 < eta-theta := by linarith
  obtain ⟨N₁,h₁⟩ := fixed_polynomial_subpower (D+2) he
  refine ⟨max 2 N₁,?_⟩
  intro N hN g hg
  have hNR : 2 ≤ (N:ℝ) := by exact_mod_cast (show 2 ≤ N by omega)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have herr : ((2:ℝ)^N)^(-10:ℝ) ≤ ((2:ℝ)^N)^g :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  have hpol : 2*((N:ℝ)+4)^(D+1) ≤ (4*(N:ℝ)+1)^(D+2) := by
    calc
      _ ≤ 2*(4*(N:ℝ)+1)^(D+1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by linarith) (D+1)) (by norm_num)
      _ ≤ (4*(N:ℝ)+1)^(D+1)*(4*(N:ℝ)+1) := by nlinarith [pow_nonneg (by linarith : 0 ≤ 4*(N:ℝ)+1) (D+1)]
      _ = _ := (pow_succ _ (D+1)).symm
  calc
    _ ≤ (2*((N:ℝ)+4)^(D+1))*((2:ℝ)^N)^g := by nlinarith [pow_nonneg (by linarith : 0 ≤ (N:ℝ)+4) (D+1)]
    _ ≤ ((2:ℝ)^N)^(eta-theta)*((2:ℝ)^N)^g :=
      mul_le_mul_of_nonneg_right (hpol.trans (h₁ N (by omega))) (by positivity)
    _ = _ := by rw [← Real.rpow_add hRp]; congr 1; ring

theorem uniform_actual_recursive_profile_oai {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1) (heta : 0 < eta) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
      e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
      e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
      ∀ root : BranchState, root.Valid e.N e.sig → root.index = 0 →
      root.start+10*e.q ≤ root.finish → ∀ x, e.energies K₀ Ψ root x →
      x ≤ ((2:ℝ)^e.N)^(2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
        +500*kap+10^6*(lam+sig)/kap+eta) := by
  let theta := min (eta/4) 1
  have htheta : 0 < theta := lt_min (by positivity) (by norm_num)
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_actual_profile_with_overhead hlam hsig hkap hkap1 hgap hloss
    htheta (min_le_right _ _) K₀ hΨ hpos hs hone
  obtain ⟨N₂,h₂⟩ := recursion_overhead_absorption ⌈20/kap+1/sig⌉₊ heta (min_le_left (eta/4) 1)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro e hdlam hdsig hdq hdJ hN hQ hcarry B δ hprof root hv hi hw x hx
  have hNp : 0 < e.N := by omega
  have hq : 0 < e.q := by rw [hdq]; exact sourcePolicyBlock_pos hNp hkap
  have hA := hprof.discrete_lipschitz
  have hzero : e.profile 0 = 0 := by simp only [RecursiveEnvironment.profile,Nat.cast_zero,hprof.zero,zero_div,sub_zero]
  have hrootdepth := BranchState.valid_depths hv
  have hbase := source_profile_exponent_lower hA hNp hzero (by omega : 0 < 10*e.q) hw hrootdepth.2
  change -4 ≤ 2*e.profile root.start-potential e.profile root.start root.finish (10*e.q) at hbase
  have hg : -4 ≤ 2*e.profile root.start-potential e.profile root.start root.finish (10*e.q)
      +500*kap+10^6*(lam+sig)/kap+theta := by
    have hloss0 : 0 ≤ 10^6*(lam+sig)/kap := by positivity
    linarith
  have hh := h₁ e hdlam hdsig hdq hdJ (by omega) hQ hcarry B δ hprof root hv hi hw x hx
  have habs := h₂ e.N (by omega) _ hg
  have hh := hh.trans habs
  apply hh.trans_eq
  congr 1
  dsimp only [theta]
  ring

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_recursive_profile_oai := @OAI.PlanarFalconer.uniform_actual_recursive_profile_oai
