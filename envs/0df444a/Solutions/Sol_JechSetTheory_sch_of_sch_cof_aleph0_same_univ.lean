-- Prove2me | solution 1 for JechSetTheory.sch_of_sch_cof_aleph0_same_univ
-- status  : ACCEPTED   (prove)
-- author  : @teargosling
-- created : 2026-11-26T03:24:41.148153+00:00
-- url     : https://prove2.me/submissions/73fa9d3e-a30c-4a98-8346-16a447402da0

import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.FundamentalSequence
import Mathlib.Tactic.NormNum
import Definitions.Def_JechStationary
import Theorems.Thm_JechSetTheory_pow_cof_eq_succ_of_isStationary

universe u

open Cardinal Order Set JechSetTheory

private lemma noMaxOrder_below_of_aleph0_le {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) :
    NoMaxOrder (Below c) := by
  refine ⟨fun a => ?_⟩
  have hlim_ord : IsSuccLimit c.ord := Cardinal.isSuccLimit_ord hc
  have hsucc_lt : Order.succ a.toOrd.1 < c.ord := hlim_ord.succ_lt a.toOrd.2
  refine ⟨Ordinal.ToType.mk ⟨Order.succ a.toOrd.1, hsucc_lt⟩, ?_⟩
  rw [← Ordinal.ToType.mk.symm.lt_iff_lt, Ordinal.ToType.mk.symm_apply_apply]
  exact Subtype.mk_lt_mk.mpr (Order.lt_succ a.toOrd.1)

private lemma nonempty_below_of_aleph0_le {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) :
    Nonempty (Below c) := by
  have hc_pos : 0 < c.ord := Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hc)
  exact ⟨Ordinal.ToType.mk ⟨0, hc_pos⟩⟩

private lemma pow_le_mul_iSup_of_lt_cof {μ δ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hδ_lt : δ < μ.ord.cof) :
    μ ^ δ ≤ μ * (⨆ α : Below μ, (#(Set.Iio α)) ^ δ) := by
  have : NoMaxOrder (Below μ) := noMaxOrder_below_of_aleph0_le hμ
  have hsurj : Function.Surjective
      (fun p : Σ α : Below μ, (Below δ → Set.Iio α) => fun i : Below δ => (p.2 i).1) := by
    intro g
    have hbdd : BddAbove (Set.range g) := by
      refine BddAbove.of_not_isCofinal fun hcof => (Order.cof_le hcof).not_gt ?_
      rw [Ordinal.cof_toType]
      have h1 : #(Set.range g) ≤ #(Below δ) := Cardinal.mk_range_le
      simpa [Below] using h1.trans_lt (by simpa [Below] using hδ_lt)
    obtain ⟨u, hu⟩ := hbdd
    obtain ⟨α, hα⟩ := exists_gt u
    exact ⟨⟨α, fun i => ⟨g i, (hu ⟨i, rfl⟩).trans_lt hα⟩⟩, rfl⟩
  have h1 : #(Below δ → Below μ) ≤ #(Σ α : Below μ, (Below δ → Set.Iio α)) :=
    Cardinal.mk_le_of_surjective hsurj
  have h2 : #(Below δ → Below μ) = μ ^ δ := by
    simp [Below]
  have h3 : #(Σ α : Below μ, (Below δ → Set.Iio α)) =
      Cardinal.sum (fun α : Below μ => (#(Set.Iio α)) ^ δ) := by
    simp [Below, Cardinal.mk_sigma]
  rw [h2, h3] at h1
  calc
    μ ^ δ ≤ Cardinal.sum (fun α : Below μ => (#(Set.Iio α)) ^ δ) := h1
    _ ≤ Cardinal.sum (fun _ : Below μ => ⨆ α : Below μ, (#(Set.Iio α)) ^ δ) :=
      Cardinal.sum_le_sum _ _ fun α => le_ciSup Cardinal.bddAbove_of_small α
    _ = #(Below μ) * (⨆ α : Below μ, (#(Set.Iio α)) ^ δ) := Cardinal.sum_const' _ _
    _ = μ * (⨆ α : Below μ, (#(Set.Iio α)) ^ δ) := by simp [Below]

private lemma pow_le_pow_cof_of_forall_lt_le {μ δ : Cardinal.{u}}
    (hμ : μ.IsSingular) (hbound : ∀ ρ < μ, ρ ^ δ ≤ μ) :
    μ ^ δ ≤ μ ^ μ.ord.cof := by
  have : NoMaxOrder (Below μ) := noMaxOrder_below_of_aleph0_le hμ.aleph0_le
  obtain ⟨f₀, hf₀⟩ := Ordinal.exists_isFundamentalSeq (o := μ.ord) rfl
  let E : Below μ.ord.cof → Below μ := fun ξ => Ordinal.ToType.mk (f₀ ξ.toOrd)
  have hE_cof : ∀ b : Below μ, ∃ ξ : Below μ.ord.cof, b < E ξ := by
    intro b
    obtain ⟨b', hb'⟩ := exists_gt b
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hf₀.isCofinal_range b'.toOrd
    refine ⟨Ordinal.ToType.mk i, hb'.trans_le ?_⟩
    rw [← Ordinal.ToType.mk.symm.le_iff_le]
    simpa [E, Ordinal.ToType.toOrd] using hi
  let Φ : (Below δ → Below μ) → ∀ ξ : Below μ.ord.cof, (Below δ → Option (Set.Iio (E ξ))) :=
    fun g ξ i => if h : g i < E ξ then some ⟨g i, h⟩ else none
  have hΦ_inj : Function.Injective Φ := by
    intro g₁ g₂ hΦ
    funext i
    obtain ⟨ξ, hξ⟩ := hE_cof (max (g₁ i) (g₂ i))
    have h₁ : g₁ i < E ξ := (le_max_left _ _).trans_lt hξ
    have h₂ : g₂ i < E ξ := (le_max_right _ _).trans_lt hξ
    have heq := congr_fun (congr_fun hΦ ξ) i
    simp only [Φ, dif_pos h₁, dif_pos h₂, Option.some.injEq] at heq
    exact congrArg Subtype.val heq
  have hle := Cardinal.mk_le_of_injective hΦ_inj
  have hlhs : #(Below δ → Below μ) = μ ^ δ := by simp [Below]
  have hrhs : #(∀ ξ : Below μ.ord.cof, (Below δ → Option (Set.Iio (E ξ)))) =
      Cardinal.prod (fun ξ : Below μ.ord.cof => (#(Option (Set.Iio (E ξ)))) ^ δ) := by
    simp [Below, Cardinal.mk_pi]
  rw [hlhs, hrhs] at hle
  have hfactor : ∀ ξ : Below μ.ord.cof, (#(Option (Set.Iio (E ξ)))) ^ δ ≤ μ := by
    intro ξ
    have hlt_iio : #(Set.Iio (E ξ)) < μ := by
      simpa [Below] using Cardinal.mk_Iio_lt (E ξ) (by simp [Below])
    have hlt_opt : #(Option (Set.Iio (E ξ))) < μ := by
      rw [Cardinal.mk_option]
      exact Cardinal.add_lt_of_lt hμ.aleph0_le hlt_iio
        (Cardinal.one_lt_aleph0.trans_le hμ.aleph0_le)
    exact hbound _ hlt_opt
  calc
    μ ^ δ ≤ Cardinal.prod (fun ξ : Below μ.ord.cof => (#(Option (Set.Iio (E ξ)))) ^ δ) := hle
    _ ≤ Cardinal.prod (fun _ : Below μ.ord.cof => μ) := Cardinal.prod_le_prod _ _ hfactor
    _ = μ ^ #(Below μ.ord.cof) := Cardinal.prod_const' _ _
    _ = μ ^ μ.ord.cof := by simp [Below]

private lemma pow_le_max_two_pow_succ {k δ : Cardinal.{u}}
    (hδ : ℵ₀ ≤ δ) (ih_sch : ∀ μ < k, SCHAt.{u} μ) :
    ∀ μ < k, μ ^ δ ≤ max (2 ^ δ) (Order.succ μ) := by
  intro μ hμ_lt
  induction μ using WellFoundedLT.induction with
  | ind μ ih =>
    by_cases hsmall : μ ≤ 2 ^ δ
    · have h1 : μ ^ δ ≤ ((2 : Cardinal.{u}) ^ δ) ^ δ := Cardinal.power_le_power_right hsmall
      have h2 : ((2 : Cardinal.{u}) ^ δ) ^ δ = (2 : Cardinal.{u}) ^ δ := by
        rw [← Cardinal.power_mul, Cardinal.mul_eq_self hδ]
      exact (h1.trans_eq h2).trans (le_max_left _ _)
    · push Not at hsmall
      have hδ_lt_μ : δ < μ := (Cardinal.cantor δ).trans hsmall
      have hℵ₀_le_μ : ℵ₀ ≤ μ := hδ.trans hδ_lt_μ.le
      have hsub : ∀ ρ < μ, ρ ^ δ ≤ μ := by
        intro ρ hρ
        have h1 := ih ρ hρ (hρ.trans hμ_lt)
        exact h1.trans (max_le hsmall.le (Order.succ_le_of_lt hρ))
      by_cases hcof : δ < μ.ord.cof
      · have h1 := pow_le_mul_iSup_of_lt_cof hℵ₀_le_μ hcof
        have h2 : (⨆ α : Below μ, (#(Set.Iio α)) ^ δ) ≤ μ := by
          have : Nonempty (Below μ) := nonempty_below_of_aleph0_le hℵ₀_le_μ
          refine ciSup_le fun α => hsub _ ?_
          simpa [Below] using Cardinal.mk_Iio_lt α (by simp [Below])
        have h3 : μ * (⨆ α : Below μ, (#(Set.Iio α)) ^ δ) ≤ μ * μ :=
          mul_le_mul' le_rfl h2
        have h4 : μ * μ = μ := Cardinal.mul_eq_self hℵ₀_le_μ
        exact ((h1.trans h3).trans_eq h4).trans
          ((Order.le_succ μ).trans (le_max_right _ _))
      · push Not at hcof
        have hμ_sing : μ.IsSingular :=
          ⟨hℵ₀_le_μ, (hcof.trans_lt hδ_lt_μ).ne⟩
        have h2cof : 2 ^ μ.ord.cof < μ :=
          (Cardinal.power_le_power_left (by norm_num : (2 : Cardinal.{u}) ≠ 0) hcof).trans_lt hsmall
        have h1 : μ ^ δ ≤ μ ^ μ.ord.cof := pow_le_pow_cof_of_forall_lt_le hμ_sing hsub
        have h2 : μ ^ μ.ord.cof = Order.succ μ := ih_sch μ hμ_lt hμ_sing h2cof
        exact (h1.trans_eq h2).trans (le_max_right _ _)

private lemma isStationary_omega_limits {c : Cardinal.{u}}
    (hcf : ℵ₀ < c) (hreg : c.ord.cof = c) :
    IsStationary {x : Below c | ∃ seq : ℕ → Below c, StrictMono seq ∧ IsLUB (Set.range seq) x} := by
  have : Nonempty (Below c) := nonempty_below_of_aleph0_le hcf.le
  have : NoMaxOrder (Below c) := noMaxOrder_below_of_aleph0_le hcf.le
  let : OrderBot (Below c) := WellFoundedLT.toOrderBot (Below c)
  let : ConditionallyCompleteLinearOrderBot (Below c) :=
    WellFoundedLT.conditionallyCompleteLinearOrderBot (Below c)
  intro C hC
  have hnext_ex : ∀ a : Below c, ∃ b ∈ C, a < b := by
    intro a
    obtain ⟨a', ha'⟩ := exists_gt a
    obtain ⟨b, hbC, hba'⟩ := hC.isCofinal a'
    exact ⟨b, hbC, ha'.trans_le hba'⟩
  choose next hnext_mem hnext_gt using hnext_ex
  obtain ⟨c₀, hc₀⟩ := hC.nonempty
  let seq : ℕ → Below c := fun n => next^[n] c₀
  have hseq_mem : ∀ n, seq n ∈ C := by
    intro n
    induction n with
    | zero => exact hc₀
    | succ n _ =>
      show next^[n + 1] c₀ ∈ C
      rw [Function.iterate_succ_apply']
      exact hnext_mem _
  have hseq_strict : StrictMono seq := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    show next^[n] c₀ < next^[n + 1] c₀
    rw [Function.iterate_succ_apply']
    exact hnext_gt _
  have hseq_bdd : BddAbove (Set.range seq) := by
    refine BddAbove.of_not_isCofinal fun hcof => (Order.cof_le hcof).not_gt ?_
    rw [Ordinal.cof_toType, hreg]
    have hcard : #(Set.range seq) ≤ ℵ₀ := by
      have h1 := Cardinal.mk_range_le_lift (f := seq)
      simpa using h1
    exact hcard.trans_lt hcf
  let x : Below c := sSup (Set.range seq)
  have hlub : IsLUB (Set.range seq) x := isLUB_csSup (Set.range_nonempty seq) hseq_bdd
  have hxC : x ∈ C := hC.isLUB_mem (Set.range_subset_iff.2 hseq_mem) (Set.range_nonempty seq) hlub
  exact ⟨x, ⟨seq, hseq_strict, hlub⟩, hxC⟩

private lemma exists_normal_seq_above {k : Cardinal.{u}}
    (hk : k.IsSingular) (hcf_gt : ℵ₀ < k.ord.cof) (h2 : 2 ^ k.ord.cof < k) :
    ∃ f : Below k.ord.cof → Cardinal.{u},
      IsNormalCardinalSeq f ∧
      (⨆ x, f x) = k ∧
      (∀ x, (2 : Cardinal.{u}) ^ ℵ₀ ≤ f x) := by
  classical
  set c := k.ord.cof
  have : Nonempty (Below c) := nonempty_below_of_aleph0_le hcf_gt.le
  have : NoMaxOrder (Below c) := noMaxOrder_below_of_aleph0_le hcf_gt.le
  have h2ℵ₀_lt_k : (2 : Cardinal.{u}) ^ ℵ₀ < k :=
    (Cardinal.power_le_power_left (by norm_num : (2 : Cardinal.{u}) ≠ 0) hcf_gt.le).trans_lt h2
  obtain ⟨f₀, hf₀⟩ := Ordinal.exists_isFundamentalSeq (o := k.ord) rfl
  let g : Below c → Cardinal.{u} := fun x => (f₀ x.toOrd).1.card
  have hg_mono : Monotone g := by
    intro x y hxy
    exact Ordinal.card_le_card (hf₀.strictMono.monotone (Ordinal.ToType.mk.symm.monotone hxy))
  have hg_lt : ∀ x, g x < k := fun x => Cardinal.lt_ord.mp (f₀ x.toOrd).2
  have hg_sup : (⨆ x, g x) = k := by
    apply le_antisymm
    · exact ciSup_le fun x => (hg_lt x).le
    · refine le_of_forall_lt fun μ hμ => ?_
      have hμ_succ : Order.succ μ < k := hk.isSuccLimit.succ_lt hμ
      have hord : (Order.succ μ).ord < k.ord := Cardinal.ord_lt_ord.2 hμ_succ
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hf₀.isCofinal_range ⟨(Order.succ μ).ord, hord⟩
      let x : Below c := Ordinal.ToType.mk i
      have hx_toOrd : x.toOrd = i := Ordinal.ToType.mk.symm_apply_apply i
      have hle : Order.succ μ ≤ g x := by
        calc
          Order.succ μ = (Order.succ μ).ord.card := (Cardinal.card_ord _).symm
          _ ≤ (f₀ i).1.card := Ordinal.card_le_card hi
          _ = g x := by simp [g, hx_toOrd]
      exact (Order.lt_succ μ).trans_le (hle.trans (le_ciSup Cardinal.bddAbove_of_small x))
  let f : Below c → Cardinal.{u} := WellFoundedLT.fix fun x ih =>
    if IsSuccLimit x then
      ⨆ y : Set.Iio x, ih y.1 y.2
    else
      max (max ((2 : Cardinal.{u}) ^ ℵ₀) (g x)) (⨆ y : Set.Iio x, Order.succ (ih y.1 y.2))
  have hf_lim : ∀ x, IsSuccLimit x → f x = ⨆ y : Set.Iio x, f y := by
    intro x hx
    change WellFoundedLT.fix _ x = _
    rw [WellFoundedLT.fix_eq]
    simp [hx, f]
  have hf_nonlim : ∀ x, ¬ IsSuccLimit x →
      f x = max (max ((2 : Cardinal.{u}) ^ ℵ₀) (g x)) (⨆ y : Set.Iio x, Order.succ (f y)) := by
    intro x hx
    change WellFoundedLT.fix _ x = _
    rw [WellFoundedLT.fix_eq]
    simp [hx, f]
  have hf_lt : ∀ x, f x < k := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x ih =>
      have hcard_lt : #(Set.Iio x) < c := by
        simpa [c] using Cardinal.mk_Iio_lt x (by simp)
      by_cases hx : IsSuccLimit x
      · rw [hf_lim x hx]
        exact Cardinal.iSup_lt_of_lt_cof_ord hcard_lt fun y => ih y.1 y.2
      · rw [hf_nonlim x hx]
        refine max_lt (max_lt h2ℵ₀_lt_k (hg_lt x)) ?_
        exact Cardinal.iSup_lt_of_lt_cof_ord hcard_lt fun y => hk.isSuccLimit.succ_lt (ih y.1 y.2)
  have hf_succ_le_nonlim : ∀ {y x : Below c}, y < x → ¬ IsSuccLimit x →
      Order.succ (f y) ≤ f x := by
    intro y x hyx hx
    rw [hf_nonlim x hx]
    have hle : Order.succ (f y) ≤ ⨆ z : Set.Iio x, Order.succ (f z.1) :=
      le_ciSup (f := fun z : Set.Iio x => Order.succ (f z.1))
        Cardinal.bddAbove_of_small ⟨y, hyx⟩
    exact hle.trans (le_max_right _ _)
  have hf_strict : StrictMono f := by
    intro y x hyx
    by_cases hx : IsSuccLimit x
    · have hsy_lt : Order.succ y < x := hx.succ_lt hyx
      have hy_lt_sy : y < Order.succ y := Order.lt_succ y
      have hsy_not_lim : ¬ IsSuccLimit (Order.succ y) := fun h => not_isMax y h.isMax
      have h1 : f y < f (Order.succ y) :=
        (Order.lt_succ (f y)).trans_le (hf_succ_le_nonlim hy_lt_sy hsy_not_lim)
      have h2 : f (Order.succ y) ≤ f x := by
        rw [hf_lim x hx]
        exact le_ciSup (f := fun z : Set.Iio x => f z.1)
          Cardinal.bddAbove_of_small ⟨Order.succ y, hsy_lt⟩
      exact h1.trans_le h2
    · exact (Order.lt_succ (f y)).trans_le (hf_succ_le_nonlim hyx hx)
  have hf_ge : ∀ x, (2 : Cardinal.{u}) ^ ℵ₀ ≤ f x := by
    intro x
    by_cases hx : IsSuccLimit x
    · have hc_pos : 0 < c.ord := Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans hcf_gt)
      let b : Below c := Ordinal.ToType.mk ⟨0, hc_pos⟩
      have hb_le_all : ∀ z : Below c, b ≤ z := by
        intro z
        rw [← Ordinal.ToType.mk.symm.le_iff_le, Ordinal.ToType.mk.symm_apply_apply]
        exact Subtype.mk_le_mk.mpr bot_le
      have hb_min : IsMin b := fun z _ => hb_le_all z
      have hb_not_lim : ¬ IsSuccLimit b := fun h => h.not_isMin hb_min
      have hb_lt_x : b < x :=
        (hb_le_all x).lt_of_ne (fun h => hx.not_isMin (h ▸ hb_min))
      have hb_ge : (2 : Cardinal.{u}) ^ ℵ₀ ≤ f b := by
        rw [hf_nonlim b hb_not_lim]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      exact hb_ge.trans (hf_strict hb_lt_x).le
    · rw [hf_nonlim x hx]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hf_sup : (⨆ x, f x) = k := by
    apply le_antisymm
    · exact ciSup_le fun x => (hf_lt x).le
    · rw [← hg_sup]
      refine ciSup_le fun x => ?_
      have hsx_not_lim : ¬ IsSuccLimit (Order.succ x) := fun h => not_isMax x h.isMax
      have h1 : g x ≤ g (Order.succ x) := hg_mono (Order.le_succ x)
      have h2 : g (Order.succ x) ≤ f (Order.succ x) := by
        rw [hf_nonlim (Order.succ x) hsx_not_lim]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      exact (h1.trans h2).trans (le_ciSup Cardinal.bddAbove_of_small (Order.succ x))
  exact ⟨f, ⟨hf_strict, hf_lim⟩, hf_sup, hf_ge⟩

theorem solution (h : ∀ l : Cardinal.{u}, l.ord.cof = ℵ₀ → SCHAt.{u} l) :
    ∀ k : Cardinal.{u}, SCHAt.{u} k := by
  intro k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    intro hk h2
    by_cases hcf_eq : k.ord.cof = ℵ₀
    · exact h k hcf_eq hk h2
    · have hcf_ge : ℵ₀ ≤ k.ord.cof :=
        Ordinal.aleph0_le_cof_iff.mpr
          (Ordinal.one_lt_cof_iff.mpr (Cardinal.isSuccLimit_ord hk.aleph0_le))
      have hcf_gt : ℵ₀ < k.ord.cof := hcf_ge.lt_of_ne' hcf_eq
      have hsmall : ∀ l < k, l ^ k.ord.cof < k := by
        intro l hl
        have hbound := pow_le_max_two_pow_succ hcf_ge ih l hl
        exact hbound.trans_lt (max_lt h2 (hk.isSuccLimit.succ_lt hl))
      obtain ⟨f, hf_normal, hf_sup, hf_ge⟩ := exists_normal_seq_above hk hcf_gt h2
      have hS_stat : IsStationary
          {x : Below k.ord.cof | ∃ seq : ℕ → Below k.ord.cof, StrictMono seq ∧ IsLUB (Set.range seq) x} :=
        isStationary_omega_limits hcf_gt (Ordinal.cof_ord_cof k.ord)
      have hgood_stat : IsStationary
          {x : Below k.ord.cof | (f x) ^ (f x).ord.cof = Order.succ (f x)} := by
        refine hS_stat.mono ?_
        rintro x ⟨seq, hstrict, hlub⟩
        have hseq_lt : ∀ n, seq n < x := fun n =>
          (hstrict (Nat.lt_succ_self n)).trans_le (hlub.1 ⟨n + 1, rfl⟩)
        have hx_lim : IsSuccLimit x := by
          refine ⟨fun hmin => (hseq_lt 0).not_ge (hmin (hseq_lt 0).le), fun y hcov => ?_⟩
          have hnot_ub : ¬ y ∈ upperBounds (Set.range seq) :=
            fun hub => hcov.1.not_ge (hlub.2 hub)
          rw [mem_upperBounds] at hnot_ub
          push Not at hnot_ub
          obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hnot_ub
          exact hcov.2 hn (hseq_lt n)
        have hfx_gt_2ℵ₀ : (2 : Cardinal.{u}) ^ ℵ₀ < f x :=
          (hf_ge (seq 0)).trans_lt (hf_normal.1 (hseq_lt 0))
        have hfx_gt_ℵ₀ : ℵ₀ < f x := (Cardinal.cantor ℵ₀).trans hfx_gt_2ℵ₀
        have hfx_sup_seq : (⨆ n : ℕ, f (seq n)) = f x := by
          have : Nonempty (Set.Iio x) := ⟨⟨seq 0, hseq_lt 0⟩⟩
          apply le_antisymm
          · exact ciSup_le fun n => (hf_normal.1 (hseq_lt n)).le
          · rw [hf_normal.2 x hx_lim]
            refine ciSup_le fun y => ?_
            have hnot_ub : ¬ y.1 ∈ upperBounds (Set.range seq) :=
              fun hub => y.2.not_ge (hlub.2 hub)
            rw [mem_upperBounds] at hnot_ub
            push Not at hnot_ub
            obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hnot_ub
            exact (hf_normal.1 hn).le.trans (le_ciSup Cardinal.bddAbove_of_small n)
        have hfx_cof_le : (f x).ord.cof ≤ ℵ₀ := by
          by_contra! hgt
          have hlt := Cardinal.lift_iSup_lt_of_lt_cof_ord (f := fun n : ℕ => f (seq n)) (a := f x)
            (by simpa using hgt) (fun n => hf_normal.1 (hseq_lt n))
          exact hlt.ne hfx_sup_seq
        have hfx_cof_ge : ℵ₀ ≤ (f x).ord.cof :=
          Ordinal.aleph0_le_cof_iff.mpr
            (Ordinal.one_lt_cof_iff.mpr (Cardinal.isSuccLimit_ord hfx_gt_ℵ₀.le))
        have hfx_cof : (f x).ord.cof = ℵ₀ := le_antisymm hfx_cof_le hfx_cof_ge
        have hfx_sing : (f x).IsSingular :=
          ⟨hfx_gt_ℵ₀.le, (hfx_cof.trans_lt hfx_gt_ℵ₀).ne⟩
        have hfx_two_pow : (2 : Cardinal.{u}) ^ (f x).ord.cof < f x := by
          rw [hfx_cof]
          exact hfx_gt_2ℵ₀
        exact h (f x) hfx_cof hfx_sing hfx_two_pow
      exact JechSetTheory.pow_cof_eq_succ_of_isStationary k hk hcf_gt hsmall f hf_normal hf_sup hgood_stat
