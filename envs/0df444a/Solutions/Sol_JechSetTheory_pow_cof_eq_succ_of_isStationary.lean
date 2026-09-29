-- Prove2me | solution 1 for JechSetTheory.pow_cof_eq_succ_of_isStationary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T06:50:05.601506+00:00
-- url     : https://prove2.me/submissions/54b931f6-437d-4de2-886b-7eea84837856

import Mathlib
import Definitions.Def_JechStationary

/-! 16beeb29 JechSetTheory.pow_cof_eq_succ_of_isStationary (Jech, Lemma 8.14).

Library (namespace `JechLib`): `isClub_diag` + `fodor`, `lemmaA` (Jech 8.15), `lemmaB`
(Jech 8.16, relative to a stationary set), `decomp` (partial maps into `μ` number at most
`μ ^ cf μ` when `μ` is `#A`-strong), and `core` (the coding `h ↦ (α ↦ h ↾ α truncated to D α)`).
-/

set_option autoImplicit false

universe u

open Cardinal Order Set

namespace JechLib

section Club

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

omit [WellFoundedLT I] in
theorem nonempty_of_cof (hI : ℵ₀ < cof I) : Nonempty I := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  rw [cof_eq_zero] at hI
  simp at hI

omit [WellFoundedLT I] in
theorem noMaxOrder_of_cof (hI : ℵ₀ < cof I) : NoMaxOrder I := by
  have := nonempty_of_cof hI
  rw [← noTopOrder_iff_noMaxOrder]
  exact one_lt_cof_iff.1 (one_lt_aleph0.trans hI)

omit [WellFoundedLT I] in
theorem isClub_Ici (a : I) : IsClub (Ici a) :=
  ⟨fun _d hd hne _ _b hb => by
    obtain ⟨y, hy⟩ := hne
    exact (hd hy).trans (hb.1 hy), fun x => ⟨max x a, le_max_right _ _, le_max_left _ _⟩⟩

omit [WellFoundedLT I] in
theorem isClub_Ioi [NoMaxOrder I] (a : I) : IsClub (Ioi a) :=
  ⟨fun _d hd hne _ _b hb => by
    obtain ⟨y, hy⟩ := hne
    exact (hd hy).trans_le (hb.1 hy), fun x => by
      obtain ⟨c, hc⟩ := exists_gt (max x a)
      exact ⟨c, (le_max_right _ _).trans_lt hc, (le_max_left _ _).trans hc.le⟩⟩

omit [WellFoundedLT I] in
theorem IsStationary.isCofinal' {T : Set I} (hT : IsStationary T) : IsCofinal T := fun a => by
  obtain ⟨b, hbT, hb⟩ := hT (isClub_Ici a)
  exact ⟨b, hbT, hb⟩

theorem IsStationary.inter_Ioi (hI : ℵ₀ < cof I) {T : Set I} (hT : IsStationary T) (a : I) :
    IsStationary (T ∩ Ioi a) := by
  have := noMaxOrder_of_cof hI
  intro C hC
  obtain ⟨b, hbT, hbC, hba⟩ := hT (hC.inter hI.ne' (isClub_Ioi a))
  exact ⟨b, ⟨hbT, hba⟩, hbC⟩

theorem isClub_diag (hI : ℵ₀ < cof I) (hIio : ∀ x : I, #(Iio x) < cof I) (C : I → Set I)
    (hC : ∀ β, IsClub (C β)) : IsClub {α | ∀ β < α, α ∈ C β} := by
  have := noMaxOrder_of_cof hI
  refine ⟨fun d hd _ _ a ha β hβa => ?_, fun a => ?_⟩
  · obtain ⟨y, hyd, hβy⟩ : ∃ y ∈ d, β < y := by
      by_contra h
      push Not at h
      exact (ha.2 fun z hz => h z hz).not_gt hβa
    apply (hC β).isLUB_mem (t := {z | z ∈ d ∧ β < z}) (fun z hz => hd hz.1 β hz.2)
      ⟨y, hyd, hβy⟩
    refine ⟨fun z hz => ha.1 hz.1, fun b hb => ha.2 fun z hz => ?_⟩
    by_cases hz' : β < z
    · exact hb ⟨hz, hz'⟩
    · exact (not_lt.1 hz').trans (hβy.le.trans (hb ⟨hyd, hβy⟩))
  · have hQ : ∀ x : I, IsClub (⋂ β : Iio x, C β) := fun x =>
      IsClub.iInter hI.ne' (by simpa using hIio x) (fun β => hC β)
    have hnext : ∀ x : I, ∃ y, x < y ∧ ∀ β < x, y ∈ C β := fun x => by
      obtain ⟨z, hz⟩ := exists_gt x
      obtain ⟨y, hy, hzy⟩ := (hQ x).isCofinal z
      exact ⟨y, hz.trans_le hzy, fun β hβ => mem_iInter.1 hy ⟨β, hβ⟩⟩
    choose nx hnx1 hnx2 using hnext
    have : Nonempty I := ⟨a⟩
    let := WellFoundedLT.toOrderBot (α := I)
    let := WellFoundedLT.conditionallyCompleteLinearOrderBot I
    let g : ℕ → I := fun n => nx^[n] a
    have gsucc : ∀ n, g (n + 1) = nx (g n) := fun n => Function.iterate_succ_apply' nx n a
    have gmono : StrictMono g := strictMono_nat_of_lt_succ fun n => by
      rw [gsucc]; exact hnx1 _
    have hbdd : BddAbove (range g) := by
      refine .of_not_isCofinal fun hg => (cof_le hg).not_gt (hI.trans_le' ?_)
      simpa using mk_range_le_lift (f := g)
    refine ⟨sSup (range g), fun β hβ => ?_, le_csSup hbdd ⟨0, rfl⟩⟩
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := exists_lt_of_lt_csSup (range_nonempty g) hβ
    apply (hC β).isLUB_mem (t := range fun n => g (m + n + 1)) ?_ (range_nonempty _)
    · refine ⟨?_, fun b hb => csSup_le (range_nonempty g) ?_⟩
      · rintro _ ⟨n, rfl⟩
        exact le_csSup hbdd ⟨_, rfl⟩
      · rintro _ ⟨n, rfl⟩
        exact (gmono.monotone (by omega : n ≤ m + n + 1)).trans (hb ⟨n, rfl⟩)
    · rintro _ ⟨n, rfl⟩
      simp only
      rw [gsucc]
      exact hnx2 _ β (hm.trans_le (gmono.monotone (Nat.le_add_right m n)))

theorem fodor (hI : ℵ₀ < cof I) (hIio : ∀ x : I, #(Iio x) < cof I) {T : Set I}
    (hT : IsStationary T) (r : I → I) (hr : ∀ α ∈ T, r α < α) :
    ∃ β, IsStationary {α | α ∈ T ∧ r α = β} := by
  by_contra h
  push Not at h
  simp only [not_isStationary_iff] at h
  choose C hC hdisj using h
  obtain ⟨α, hαT, hαC⟩ := hT (isClub_diag hI hIio C hC)
  exact Set.disjoint_left.1 (hdisj (r α)) ⟨hαT, rfl⟩ (hαC (r α) (hr α hαT))

end Club

section LemmaA

variable {I J : Type u} [LinearOrder I] [WellFoundedLT I] [LinearOrder J]

/-- Jech 8.15 in coded form: an almost-disjoint family of functions that are regressive into
the approximations `D α = {x | ∃ β < α, x < E β}` on a stationary set has at most `k` members. -/
theorem lemmaA (hI : ℵ₀ < cof I) (hIio : ∀ x : I, #(Iio x) < cof I) {k : Cardinal.{u}}
    (hk : ℵ₀ ≤ k) (hIk : #I ≤ k) (hpow : ∀ ν < k, ν ^ #I < k) (E : I → J)
    (hE : ∀ β, #(Iio (E β)) < k) {ι : Type u} (T : Set I) (hT : IsStationary T)
    (Ψ : ι → I → J) (hΨ : ∀ i, ∀ α ∈ T, ∃ β < α, Ψ i α < E β)
    (had : ∀ i j, i ≠ j → ¬ IsCofinal {α | α ∈ T ∧ Ψ i α = Ψ j α}) : #ι ≤ k := by
  classical
  have h' : ∀ i α, ∃ β, α ∈ T → β < α ∧ Ψ i α < E β := fun i α => by
    by_cases hα : α ∈ T
    · obtain ⟨β, hβ, h⟩ := hΨ i α hα
      exact ⟨β, fun _ => ⟨hβ, h⟩⟩
    · exact ⟨α, fun h => absurd h hα⟩
  choose r hr using h'
  have hfod : ∀ i, ∃ β, IsStationary {α | α ∈ T ∧ r i α = β} := fun i =>
    fodor hI hIio hT (r i) (fun α hα => (hr i α hα).1)
  choose b hb using hfod
  let code : ι → Σ β : I, (I → Option (Iio (E β))) := fun i =>
    ⟨b i, fun α => if h : α ∈ T ∧ r i α = b i then
      some ⟨Ψ i α, by have := (hr i α h.1).2; rw [h.2] at this; exact this⟩ else none⟩
  let ev : (Σ β : I, (I → Option (Iio (E β)))) → I → Option J :=
    fun p α => (p.2 α).map Subtype.val
  have hev : ∀ i α, ev (code i) α = if α ∈ T ∧ r i α = b i then some (Ψ i α) else none := by
    intro i α
    simp only [ev, code]
    split_ifs <;> rfl
  have hinj : Function.Injective code := by
    intro i j hij
    by_contra hne
    apply had i j hne
    refine (IsStationary.isCofinal' (hb i)).mono ?_
    intro α hα
    have h1 := congrFun (congrArg ev hij) α
    rw [hev, hev, if_pos (show α ∈ T ∧ r i α = b i from hα)] at h1
    split_ifs at h1 with h2
    exact ⟨hα.1, Option.some_injective _ h1⟩
  calc #ι ≤ #(Σ β : I, (I → Option (Iio (E β)))) := mk_le_of_injective hinj
    _ = sum fun β => #(I → Option (Iio (E β))) := mk_sigma _
    _ ≤ sum fun _ : I => k := sum_le_sum _ _ fun β => by
        rw [mk_arrow, mk_option, lift_id, lift_id]
        exact (hpow _ (add_lt_of_lt hk (hE β) (one_lt_aleph0.trans_le hk))).le
    _ = #I * k := sum_const' _ _
    _ ≤ k * k := by gcongr
    _ = k := mul_eq_self hk

end LemmaA

section LemmaB

variable {I J : Type u} [LinearOrder I] [WellFoundedLT I] [LinearOrder J]

theorem IsStationary.inter_club (hI : ℵ₀ < cof I) {T C : Set I} (hT : IsStationary T)
    (hC : IsClub C) : IsStationary (T ∩ C) := by
  intro D hD
  obtain ⟨b, hbT, hbC, hbD⟩ := hT (hC.inter hI.ne' hD)
  exact ⟨b, ⟨hbT, hbC⟩, hbD⟩

/-- Jech 8.16 relative to a stationary set `S`: an family of functions `Φ i α ∈ W α` that is
almost disjoint on `S`, where on `S` every initial segment of `W α` injects into `D α`, has at
most `k⁺` members. -/
theorem lemmaB (hI : ℵ₀ < cof I) (hIio : ∀ x : I, #(Iio x) < cof I) {k : Cardinal.{u}}
    (hk : ℵ₀ ≤ k) (hIk : #I ≤ k) (hpow : ∀ ν < k, ν ^ #I < k) (E : I → J)
    (hE : ∀ β, #(Iio (E β)) < k) (S : Set I) (hS : IsStationary S)
    (W : I → Type u) [∀ α, LinearOrder (W α)]
    (hW : ∀ α ∈ S, ∀ w : W α, #(Iic w) ≤ #{x : J | ∃ β < α, x < E β})
    {ι : Type u} (Φ : ι → ∀ α, W α)
    (had : ∀ i j, i ≠ j → ¬ IsCofinal {α | α ∈ S ∧ Φ i α = Φ j α}) : #ι ≤ succ k := by
  classical
  have h2I : #(Set I) * k ≤ k := by
    rw [mk_set]
    calc 2 ^ #I * k ≤ k * k := by
          gcongr; exact (hpow 2 ((natCast_lt_aleph0 (n := 2)).trans_le hk)).le
      _ = k := mul_eq_self hk
  have hF : ∀ g : ι, #{i | IsStationary {α | α ∈ S ∧ Φ i α ≤ Φ g α}} ≤ k := by
    intro g
    have hT : ∀ T : {T : Set I // IsStationary T ∧ T ⊆ S},
        #{i | ∀ α ∈ T.1, Φ i α ≤ Φ g α} ≤ k := by
      rintro ⟨T, hT, hTS⟩
      have hemb : ∀ α, ∃ e : W α → J, α ∈ S →
          (Set.InjOn e (Iic (Φ g α)) ∧ ∀ w ∈ Iic (Φ g α), ∃ β < α, e w < E β) := by
        intro α
        by_cases hα : α ∈ S
        · obtain ⟨emb⟩ := (Cardinal.le_def _ _).1 (hW α hα (Φ g α))
          refine ⟨fun w => if h : w ∈ Iic (Φ g α) then (emb ⟨w, h⟩).1 else E α,
            fun _ => ⟨?_, ?_⟩⟩
          · intro w hw w' hw' hww'
            simp only [dif_pos hw, dif_pos hw'] at hww'
            exact congrArg Subtype.val (emb.injective (Subtype.ext hww'))
          · intro w hw
            simp only [dif_pos hw]
            exact (emb ⟨w, hw⟩).2
        · exact ⟨fun _ => E α, fun h => absurd h hα⟩
      choose e he using hemb
      refine lemmaA hI hIio hk hIk hpow E hE T hT
        (fun (i : {i | ∀ α ∈ T, Φ i α ≤ Φ g α}) α => e α (Φ i.1 α)) ?_ ?_
      · rintro ⟨i, hi⟩ α hαT
        exact (he α (hTS hαT)).2 _ (hi α hαT)
      · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij hcof
        apply had i j (fun h => hij (Subtype.ext h))
        refine hcof.mono ?_
        rintro α ⟨hαT, heq⟩
        exact ⟨hTS hαT, (he α (hTS hαT)).1 (hi α hαT) (hj α hαT) heq⟩
    calc #{i | IsStationary {α | α ∈ S ∧ Φ i α ≤ Φ g α}}
        ≤ #(⋃ T : {T : Set I // IsStationary T ∧ T ⊆ S}, {i | ∀ α ∈ T.1, Φ i α ≤ Φ g α}) :=
          mk_le_mk_of_subset fun i hi =>
            mem_iUnion.2 ⟨⟨_, hi, fun α hα => hα.1⟩, fun α hα => hα.2⟩
      _ ≤ sum fun T : {T : Set I // IsStationary T ∧ T ⊆ S} =>
            #{i | ∀ α ∈ T.1, Φ i α ≤ Φ g α} := mk_iUnion_le_sum_mk
      _ ≤ sum fun _ : {T : Set I // IsStationary T ∧ T ⊆ S} => k := sum_le_sum _ _ hT
      _ = #{T : Set I // IsStationary T ∧ T ⊆ S} * k := sum_const' _ _
      _ ≤ #(Set I) * k := by gcongr; exact mk_subtype_le _
      _ ≤ k := h2I
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨G, -, hG⟩ := le_mk_iff_exists_subset.1
    (show succ k ≤ #(univ : Set ι) by rw [mk_univ]; exact hlt.le)
  have hU : #(⋃ g : G, {i | IsStationary {α | α ∈ S ∧ Φ i α ≤ Φ g.1 α}}) < #ι := by
    calc _ ≤ sum fun g : G => #{i | IsStationary {α | α ∈ S ∧ Φ i α ≤ Φ g.1 α}} :=
          mk_iUnion_le_sum_mk
      _ ≤ sum fun _ : G => k := sum_le_sum _ _ fun g => hF g.1
      _ = #G * k := sum_const' _ _
      _ = succ k := by
          rw [hG]
          exact mul_eq_left (hk.trans (le_succ k)) (le_succ k)
            (ne_of_gt (aleph0_pos.trans_le hk))
      _ < #ι := hlt
  obtain ⟨f, hf⟩ : ∃ f, f ∉ ⋃ g : G, {i | IsStationary {α | α ∈ S ∧ Φ i α ≤ Φ g.1 α}} := by
    by_contra h
    push Not at h
    exact hU.not_ge (by rw [← mk_univ]; exact mk_le_mk_of_subset fun x _ => h x)
  have hGF : G ⊆ {i | IsStationary {α | α ∈ S ∧ Φ i α ≤ Φ f α}} := fun g hg => by
    have hnot : ¬ IsStationary {α | α ∈ S ∧ Φ f α ≤ Φ g α} := fun h =>
      hf (mem_iUnion.2 ⟨⟨g, hg⟩, h⟩)
    obtain ⟨C, hC, hdisj⟩ := not_isStationary_iff.1 hnot
    refine (IsStationary.inter_club hI hS hC).mono fun α hα => ⟨hα.1, ?_⟩
    exact le_of_lt (not_le.1 fun h => Set.disjoint_left.1 hdisj ⟨hα.1, h⟩ hα.2)
  have := (mk_le_mk_of_subset hGF).trans (hF f)
  rw [hG] at this
  exact (lt_succ k).not_ge this

end LemmaB

section Decomp

/-- If every `ρ < μ` has `(ρ + 1) ^ #A ≤ μ`, then partial maps `A → μ` number at most
`μ ^ cf μ` (split along a cofinal subset of `μ` of size `cf μ`). -/
theorem decomp {A X : Type u} {μ : Cardinal.{u}} (hX : #X = μ) (hμ : ℵ₀ ≤ μ)
    (hpow : ∀ ρ < μ, (ρ + 1) ^ #A ≤ μ) : #(A → Option X) ≤ μ ^ μ.ord.cof := by
  classical
  have hT : #(μ.ord.ToType) = μ := by rw [mk_toType, card_ord]
  obtain ⟨eX⟩ : Nonempty (X ≃ μ.ord.ToType) := Cardinal.eq.1 (hX.trans hT.symm)
  have := Cardinal.noMaxOrder hμ
  obtain ⟨s, hs, hsc⟩ := Order.exists_cof_eq (μ.ord.ToType)
  have hcT : Order.cof (μ.ord.ToType) = μ.ord.cof := Ordinal.cof_toType _
  have hup : ∀ z : μ.ord.ToType, ∃ t : s, z < t.1 := fun z => by
    obtain ⟨z', hz'⟩ := exists_gt z
    obtain ⟨t, ht, hzt⟩ := hs z'
    exact ⟨⟨t, ht⟩, hz'.trans_le hzt⟩
  let F : (A → Option X) → (∀ t : s, A → Option (Iio t.1)) := fun p t a =>
    (p a).elim none fun x => if h : eX x < t.1 then some ⟨eX x, h⟩ else none
  have hF : Function.Injective F := by
    intro p q hpq
    funext a
    have key : ∀ t : s, F p t a = F q t a := fun t => congrFun (congrFun hpq t) a
    rcases hp : p a with _ | x <;> rcases hq : q a with _ | y
    · rfl
    · obtain ⟨t, ht⟩ := hup (eX y)
      have := key t
      simp only [F, hp, hq, Option.elim_none, Option.elim_some, dif_pos ht] at this
      cases this
    · obtain ⟨t, ht⟩ := hup (eX x)
      have := key t
      simp only [F, hp, hq, Option.elim_none, Option.elim_some, dif_pos ht] at this
      cases this
    · obtain ⟨t, ht⟩ := hup (max (eX x) (eX y))
      have := key t
      simp only [F, hp, hq, Option.elim_some, dif_pos ((le_max_left _ _).trans_lt ht),
        dif_pos ((le_max_right _ _).trans_lt ht), Option.some.injEq] at this
      rw [eX.injective (congrArg Subtype.val this)]
  calc #(A → Option X) ≤ #(∀ t : s, A → Option (Iio t.1)) := mk_le_of_injective hF
    _ = prod fun t : s => #(A → Option (Iio t.1)) := mk_pi _
    _ ≤ prod fun _ : s => μ := prod_le_prod _ _ fun t => by
        rw [mk_arrow, mk_option, lift_id, lift_id]
        exact hpow _ (mk_Iio_toType_ord_lt t.1)
    _ = μ ^ #s := prod_const' _ _
    _ = μ ^ μ.ord.cof := by rw [hsc, hcT]

end Decomp

section Core

variable {I J : Type u} [LinearOrder I] [WellFoundedLT I] [LinearOrder J]

/-- The coding step behind Jech 8.14: if on a stationary set `S` the restrictions `h ↾ α`
(truncated to `D α`) number at most `(#D α)⁺`, then `#(I → J) ≤ k⁺`. -/
theorem core (hI : ℵ₀ < cof I) (hIio : ∀ x : I, #(Iio x) < cof I) {k : Cardinal.{u}}
    (hk : ℵ₀ ≤ k) (hIk : #I ≤ k) (hpow : ∀ ν < k, ν ^ #I < k) (E : I → J)
    (hE : ∀ β, #(Iio (E β)) < k) (hEcof : ∀ x : J, ∃ β, x < E β)
    (S : Set I) (hS : IsStationary S)
    (hSD : ∀ α ∈ S, ℵ₀ ≤ #{x : J | ∃ β < α, x < E β} ∧
      #(Iio α → Option {x : J | ∃ β < α, x < E β}) ≤ succ #{x : J | ∃ β < α, x < E β}) :
    #(I → J) ≤ succ k := by
  classical
  have := noMaxOrder_of_cof hI
  have hWne : ∀ α : I, Nonempty (succ #{x : J | ∃ β < α, x < E β}).ord.ToType := fun α =>
    Ordinal.nonempty_toType_iff.2 (by
      rw [Ne, ord_eq_zero]
      exact (succ_pos _).ne')
  have hemb : ∀ α, ∃ e : (Iio α → Option {x : J | ∃ β < α, x < E β}) →
      (succ #{x : J | ∃ β < α, x < E β}).ord.ToType, α ∈ S → Function.Injective e := by
    intro α
    by_cases hα : α ∈ S
    · have h1 : #(Iio α → Option {x : J | ∃ β < α, x < E β}) ≤
          #((succ #{x : J | ∃ β < α, x < E β}).ord.ToType) := by
        rw [mk_toType, card_ord]; exact (hSD α hα).2
      obtain ⟨emb⟩ := (Cardinal.le_def _ _).1 h1
      exact ⟨emb, fun _ => emb.injective⟩
    · exact ⟨fun _ => (hWne α).some, fun h => absurd h hα⟩
  choose e he using hemb
  let code : (I → J) → ∀ α, (Iio α → Option {x : J | ∃ β < α, x < E β}) := fun h α b =>
    if hb : h b.1 ∈ {x : J | ∃ β < α, x < E β} then some ⟨h b.1, hb⟩ else none
  let Φ : (I → J) → ∀ α, (succ #{x : J | ∃ β < α, x < E β}).ord.ToType :=
    fun h α => e α (code h α)
  have hW : ∀ α ∈ S, ∀ w : (succ #{x : J | ∃ β < α, x < E β}).ord.ToType,
      #(Iic w) ≤ #{x : J | ∃ β < α, x < E β} := by
    intro α hα w
    have h2 : #(Iio w) ≤ #{x : J | ∃ β < α, x < E β} := le_of_lt_succ (mk_Iio_toType_ord_lt w)
    rw [← Iio_insert]
    calc #(insert w (Iio w) : Set _) ≤ #(Iio w) + 1 := mk_insert_le
      _ ≤ #{x : J | ∃ β < α, x < E β} + 1 := by gcongr
      _ = #{x : J | ∃ β < α, x < E β} := add_one_eq (hSD α hα).1
  have had : ∀ h h' : I → J, h ≠ h' → ¬ IsCofinal {α | α ∈ S ∧ Φ h α = Φ h' α} := by
    intro h h' hne hcof
    obtain ⟨b, hb⟩ : ∃ b, h b ≠ h' b := by
      by_contra hc
      push Not at hc
      exact hne (funext hc)
    obtain ⟨β1, hβ1⟩ := hEcof (h b)
    obtain ⟨β2, hβ2⟩ := hEcof (h' b)
    obtain ⟨m, hm⟩ := exists_gt (max (max b β1) β2)
    obtain ⟨α, ⟨hαS, hαeq⟩, hmα⟩ := hcof m
    have hlt : max (max b β1) β2 < α := hm.trans_le hmα
    have hbα : b < α := ((le_max_left _ _).trans (le_max_left _ _)).trans_lt hlt
    have h1 : h b ∈ {x : J | ∃ β < α, x < E β} :=
      ⟨β1, ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hlt, hβ1⟩
    have h2 : h' b ∈ {x : J | ∃ β < α, x < E β} :=
      ⟨β2, (le_max_right _ _).trans_lt hlt, hβ2⟩
    have hc := congrFun (he α hαS hαeq) ⟨b, hbα⟩
    simp only [code, dif_pos h1, dif_pos h2, Option.some.injEq, Subtype.mk.injEq] at hc
    exact hb hc
  exact lemmaB hI hIio hk hIk hpow E hE S hS
    (fun α => (succ #{x : J | ∃ β < α, x < E β}).ord.ToType) hW Φ had

end Core

theorem mk_Iio_mk {o o' : Ordinal.{u}} (h : o < o') :
    #(Iio (Ordinal.ToType.mk ⟨o, h⟩ : o'.ToType)) = o.card := by
  have h1 : Ordinal.typein (α := o'.ToType) (· < ·) (Ordinal.ToType.mk ⟨o, h⟩) = o :=
    congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨o, h⟩)
  have h2 := Ordinal.card_typein (r := fun a b : o'.ToType => a < b) (Ordinal.ToType.mk ⟨o, h⟩)
  rw [h1] at h2
  exact h2.symm

end JechLib

open JechLib

set_option maxHeartbeats 4000000 in
open Cardinal Order Set JechSetTheory in
theorem solution (k : Cardinal) (hk : k.IsSingular)
    (hcf : ℵ₀ < k.ord.cof) (hsmall : ∀ l < k, l ^ k.ord.cof < k)
    (f : Below k.ord.cof → Cardinal) (hf : IsNormalCardinalSeq f)
    (hlim : ⨆ x, f x = k)
    (hstat : IsStationary {x : Below k.ord.cof | (f x) ^ (f x).ord.cof = Order.succ (f x)}) :
    k ^ k.ord.cof = Order.succ k := by
  classical
  have hk0 : ℵ₀ ≤ k := hk.aleph0_le
  have hck : k.ord.cof < k := hk.cof_ord_lt
  have hk1 : ℵ₀ < k := hcf.trans hck
  have hcI : Order.cof (k.ord.cof.ord.ToType) = k.ord.cof := by
    rw [Ordinal.cof_toType, Ordinal.cof_ord_cof]
  have hmkI : #(k.ord.cof.ord.ToType) = k.ord.cof := by rw [mk_toType, card_ord]
  have hI : ℵ₀ < Order.cof (k.ord.cof.ord.ToType) := by rw [hcI]; exact hcf
  have hIio : ∀ x : k.ord.cof.ord.ToType, #(Iio x) < Order.cof (k.ord.cof.ord.ToType) :=
    fun x => by rw [hcI]; exact mk_Iio_toType_ord_lt x
  have hIk : #(k.ord.cof.ord.ToType) ≤ k := by rw [hmkI]; exact hck.le
  have hpow : ∀ ν < k, ν ^ #(k.ord.cof.ord.ToType) < k := fun ν hν => by
    rw [hmkI]; exact hsmall ν hν
  have hImax : NoMaxOrder (k.ord.cof.ord.ToType) := noMaxOrder_of_cof hI
  have hIne : Nonempty (Below k.ord.cof) := nonempty_of_cof hI
  obtain ⟨hmono, hcont⟩ := hf
  have hbdd : BddAbove (range f) := Cardinal.bddAbove_range f
  have hfk : ∀ β, f β < k := fun β => by
    obtain ⟨y, hy⟩ := exists_gt β
    exact (hmono hy).trans_le (hlim ▸ le_ciSup hbdd y)
  have hord : ∀ β, (f β).ord < k.ord := fun β => ord_lt_ord.2 (hfk β)
  let E : k.ord.cof.ord.ToType → k.ord.ToType := fun β => Ordinal.ToType.mk ⟨(f β).ord, hord β⟩
  have hEmk : ∀ β, #(Iio (E β)) = f β := fun β => by
    simp only [E]; rw [mk_Iio_mk, card_ord]
  have hEmono : ∀ β β', β < β' → E β < E β' := fun β β' h => by
    simp only [E]
    rw [OrderIso.lt_iff_lt]
    exact (ord_lt_ord.2 (hmono h) : _)
  have hE : ∀ β, #(Iio (E β)) < k := fun β => mk_Iio_toType_ord_lt _
  have hEcof : ∀ x : k.ord.ToType, ∃ β, x < E β := fun x => by
    have hx : #(Iio x) < ⨆ y, f y := by rw [hlim]; exact mk_Iio_toType_ord_lt x
    obtain ⟨β, hβ⟩ := (lt_ciSup_iff hbdd).1 hx
    refine ⟨β, not_le.1 fun hle => ?_⟩
    have := mk_le_mk_of_subset (Iio_subset_Iio hle)
    rw [hEmk] at this
    exact hβ.not_ge this
  obtain ⟨a0, ha0⟩ := (lt_ciSup_iff hbdd).1 (hlim.symm ▸ hk1)
  have hγ : ∀ β, ∃ γ, (f β) ^ k.ord.cof < f γ := fun β =>
    (lt_ciSup_iff hbdd).1 (hlim.symm ▸ hsmall _ (hfk β))
  choose γ hγ using hγ
  have hC : IsClub {α | ∀ β < α, α ∈ Ioi (γ β)} :=
    isClub_diag hI hIio (fun β => Ioi (γ β)) (fun β => isClub_Ioi _)
  let S := {x : Below k.ord.cof | (f x) ^ (f x).ord.cof = Order.succ (f x)} ∩
    ({α | ∀ β < α, α ∈ Ioi (γ β)} ∩ Ioi a0)
  have hS : IsStationary S :=
    IsStationary.inter_club hI hstat (hC.inter hI.ne' (isClub_Ioi a0))
  have hSlim : ∀ α ∈ S, IsSuccLimit α := by
    rintro α ⟨-, hαC, hαa⟩
    refine ⟨fun hmin => hmin.not_lt hαa, fun b hb => ?_⟩
    have h1 : γ b < α := hαC b hb.lt
    have h2 : γ b ≤ b := not_lt.1 fun h => hb.2 h h1
    have h4 : f (γ b) ≤ f b := hmono.monotone h2
    have h5 : f b ≤ (f b) ^ k.ord.cof := self_le_power _ (one_le_aleph0.trans hcf.le)
    exact absurd ((hγ b).trans_le h4) (not_lt.2 h5)
  have hDeq : ∀ α ∈ S, #{x : k.ord.ToType | ∃ β < α, x < E β} = f α := by
    intro α hα
    apply le_antisymm
    · calc #{x : k.ord.ToType | ∃ β < α, x < E β} ≤ #(Iio (E α)) :=
            mk_le_mk_of_subset fun x ⟨β, hβ, hx⟩ => hx.trans (hEmono β α hβ)
        _ = f α := hEmk α
    · have hne : Nonempty (Iio α) := ⟨⟨a0, hα.2.2⟩⟩
      rw [hcont α (hSlim α hα)]
      refine ciSup_le fun y => ?_
      rw [← hEmk]
      exact mk_le_mk_of_subset fun x hx => ⟨y.1, y.2, hx⟩
  refine le_antisymm ?_ (Order.succ_le_of_lt (lt_power_cof_ord hk0))
  have hmain := core hI hIio hk0 hIk hpow E hE hEcof S hS (fun α hα => by
    rw [hDeq α hα]
    have hαa : a0 < α := hα.2.2
    refine ⟨ha0.le.trans (hmono hαa).le, ?_⟩
    rw [← hα.1]
    apply decomp (hDeq α hα) (ha0.le.trans (hmono hαa).le)
    intro ρ hρ
    have hbddα : BddAbove (range fun y : Iio α => f y) := Cardinal.bddAbove_range _
    have : Nonempty (Iio α) := ⟨⟨a0, hαa⟩⟩
    rw [hcont α (hSlim α hα)] at hρ
    obtain ⟨y, hy⟩ := (lt_ciSup_iff hbddα).1 hρ
    have hfy0 : f y ≠ 0 := (pos_of_gt hy).ne'
    calc (ρ + 1) ^ #(Iio α) ≤ (f y) ^ #(Iio α) :=
          power_le_power_right ((add_one_le_succ ρ).trans (Order.succ_le_of_lt hy))
      _ ≤ (f y) ^ k.ord.cof := by
          apply power_le_power_left hfy0
          exact (mk_set_le _).trans hmkI.le
      _ ≤ f (γ y) := (hγ y).le
      _ ≤ f α := hmono.monotone (hα.2.1 y y.2).le)
  rw [mk_arrow, lift_id, lift_id, mk_toType, card_ord, hmkI] at hmain
  exact hmain
